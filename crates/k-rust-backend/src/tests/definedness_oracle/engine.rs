//! The oracle's evaluator: the relation `->E` of the design's section 1.2 on hash-consed ground
//! terms, written against the oracle's own language and sharing no code with the backend.
//!
//! A ground term is interned with its injections composed and `\bottom` propagated through every
//! constructor (strictness, rule 4). [`Universe::normalize`] returns every normal form a term
//! has under `->E`, with whether every evaluation ended within the bounds: innermost (a root
//! step only on normal-form arguments), the first priority group with an applicable equation
//! (rule 2; an equation applies when its left-hand side matches modulo the injection and
//! overload axioms and its `requires` normalizes to `true`), hooks on literals (rule 1), a stuck
//! partial function to `\bottom` and a stuck total symbol or equation head to itself (rule 3 as
//! corrected in the design's 3.13 (k)).
//!
//! Matching modulo the axioms reads a subject's lesser overload application as the greater
//! production the pattern names, by lifting the subject (its arguments injected into the greater
//! production's argument sorts), and a subject injection from a lesser sort as the injection from
//! the pattern's sort of the inner injection.

use std::{
    collections::{BTreeMap, HashMap, HashSet},
    rc::Rc,
};

use super::language::{Definition, Kind, Pat};

pub(super) type Id = u32;

/// `\bottom`, interned first.
pub(super) const BOTTOM: Id = 0;

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(super) enum Node {
    Bottom,
    Int(i64),
    Bool(bool),
    /// A symbol (an index into the definition's symbols) and its arguments.
    App(u32, Vec<Id>),
    /// `inj{from, to}` (sort indexes) of a term of sort `from` other than an injection.
    Inj(u32, u32, Id),
    /// A list of `Int` elements.
    List(Vec<Id>),
}

/// What evaluating a term found.
#[derive(Clone, Debug, Default)]
pub(super) struct Normal {
    /// Its normal forms, sorted; [`BOTTOM`] when an evaluation is undefined.
    pub(super) forms: Vec<Id>,
    /// Whether every evaluation ended within the bounds.
    pub(super) complete: bool,
    /// The equations (bit `i` for equation `i`) some evaluation applied, at any position.
    pub(super) applied: u128,
    /// Whether some evaluation reached an application of a total symbol to normal forms with no
    /// value: a violation of precondition P2.
    pub(super) total_undefined: bool,
}

impl Normal {
    fn of(form: Id) -> Self {
        Self {
            forms: vec![form],
            complete: true,
            ..Self::default()
        }
    }

    fn incomplete() -> Self {
        Self::default()
    }

    fn merge(&mut self, other: &Self) {
        self.forms.extend(&other.forms);
        self.complete &= other.complete;
        self.applied |= other.applied;
        self.total_undefined |= other.total_undefined;
    }

    fn finish(mut self) -> Self {
        self.forms.sort_unstable();
        self.forms.dedup();
        self
    }

    /// The one normal form, when evaluation ended and found exactly one.
    pub(super) fn unique(&self) -> Option<Id> {
        (self.complete && self.forms.len() == 1).then(|| self.forms[0])
    }
}

/// An equation that applies at a term, with its matching valuation.
pub(super) type Applying = (usize, HashMap<String, Id>);

thread_local! {
    /// Test switch (V7): every universe built on this thread also takes outermost steps.
    pub(super) static OUTERMOST: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Bounds of one universe.
const MAX_SIZE: u32 = 40;
const MAX_WORK: usize = 60_000;
const MAX_COMBINATIONS: usize = 64;

pub(super) struct Universe<'d> {
    pub(super) definition: &'d Definition,
    symbol_ids: HashMap<String, u32>,
    sort_ids: HashMap<String, u32>,
    sort_names: Vec<String>,
    /// `below[a][b]`: `a` is a subsort of `b` (reflexive).
    below: Vec<Vec<bool>>,
    /// `(greater, lesser)` overload pairs, transitively closed.
    overloads: HashSet<(u32, u32)>,
    /// Per symbol, its equations by priority group, groups ascending.
    groups: Vec<Vec<Vec<usize>>>,
    nodes: Vec<Node>,
    ids: HashMap<Node, Id>,
    sizes: Vec<u32>,
    normal: HashMap<Id, Rc<Normal>>,
    in_progress: HashSet<Id>,
    work: usize,
    /// Test switch (V7): also take root steps on arguments that are not normal forms.
    pub(super) outermost_too: bool,
}

impl<'d> Universe<'d> {
    pub(super) fn new(definition: &'d Definition) -> Self {
        let order = definition.sort_order();
        let sort_names = order.keys().cloned().collect::<Vec<_>>();
        let sort_ids = sort_names
            .iter()
            .enumerate()
            .map(|(index, name)| (name.clone(), u32::try_from(index).unwrap()))
            .collect::<HashMap<_, _>>();
        let mut below = vec![vec![false; sort_names.len()]; sort_names.len()];
        for (sup, subs) in &order {
            for sub in subs {
                below[sort_ids[sub] as usize][sort_ids[sup] as usize] = true;
            }
        }
        let symbol_ids = definition
            .symbols
            .iter()
            .enumerate()
            .map(|(index, symbol)| (symbol.name.clone(), u32::try_from(index).unwrap()))
            .collect::<HashMap<_, _>>();
        let overloads = definition
            .overloads()
            .into_iter()
            .map(|(greater, lesser)| (symbol_ids[&greater], symbol_ids[&lesser]))
            .collect();
        let mut groups = vec![BTreeMap::<u8, Vec<usize>>::new(); definition.symbols.len()];
        for (index, equation) in definition.equations.iter().enumerate() {
            // A `symbolic` equation is no step of `->E` on ground terms.
            if equation.symbolic {
                continue;
            }
            groups[symbol_ids[equation.root()] as usize]
                .entry(equation.priority)
                .or_default()
                .push(index);
        }
        let mut universe = Self {
            definition,
            symbol_ids,
            sort_ids,
            sort_names,
            below,
            overloads,
            groups: groups
                .into_iter()
                .map(|groups| groups.into_values().collect())
                .collect(),
            nodes: Vec::new(),
            ids: HashMap::new(),
            sizes: Vec::new(),
            normal: HashMap::new(),
            in_progress: HashSet::new(),
            work: 0,
            outermost_too: OUTERMOST.get(),
        };
        universe.intern(Node::Bottom);
        universe
    }

    pub(super) fn symbol_id(&self, name: &str) -> u32 {
        self.symbol_ids[name]
    }

    pub(super) fn sort_id(&self, name: &str) -> u32 {
        self.sort_ids[name]
    }

    pub(super) fn sort_name(&self, sort: u32) -> &str {
        &self.sort_names[sort as usize]
    }

    pub(super) fn is_subsort(&self, sub: u32, sup: u32) -> bool {
        self.below[sub as usize][sup as usize]
    }

    pub(super) fn node_of(&self, id: Id) -> &Node {
        &self.nodes[id as usize]
    }

    pub(super) fn size(&self, id: Id) -> u32 {
        self.sizes[id as usize]
    }

    fn intern(&mut self, node: Node) -> Id {
        if let Some(id) = self.ids.get(&node) {
            return *id;
        }
        let size = 1 + self
            .children_of(&node)
            .iter()
            .map(|child| self.sizes[*child as usize])
            .sum::<u32>();
        let id = Id::try_from(self.nodes.len()).unwrap();
        self.nodes.push(node.clone());
        self.sizes.push(size);
        self.ids.insert(node, id);
        id
    }

    fn children_of(&self, node: &Node) -> Vec<Id> {
        match node {
            Node::App(_, children) | Node::List(children) => children.clone(),
            Node::Inj(_, _, child) => vec![*child],
            Node::Bottom | Node::Int(_) | Node::Bool(_) => Vec::new(),
        }
    }

    pub(super) fn children(&self, id: Id) -> Vec<Id> {
        self.children_of(&self.nodes[id as usize])
    }

    /// A term, `\bottom` when a child is, injections composed.
    pub(super) fn node(&mut self, node: Node) -> Id {
        match node {
            Node::App(_, ref children) | Node::List(ref children) if children.contains(&BOTTOM) => {
                BOTTOM
            }
            Node::Inj(_, _, BOTTOM) => BOTTOM,
            Node::Inj(from, to, argument) if from == to => argument,
            Node::Inj(from, to, argument) => match self.nodes[argument as usize] {
                Node::Inj(inner, _, operand) => self.node(Node::Inj(inner, to, operand)),
                _ => {
                    let _ = from;
                    self.intern(node)
                }
            },
            node => self.intern(node),
        }
    }

    pub(super) fn int(&mut self, value: i64) -> Id {
        self.node(Node::Int(value))
    }

    pub(super) fn boolean(&mut self, value: bool) -> Id {
        self.node(Node::Bool(value))
    }

    /// The sort of a term other than `\bottom`.
    pub(super) fn sort_of(&self, id: Id) -> u32 {
        match &self.nodes[id as usize] {
            Node::Bottom => panic!("\\bottom has no sort"),
            Node::Int(_) => self.sort_ids["Int"],
            Node::Bool(_) => self.sort_ids["Bool"],
            Node::App(symbol, _) => {
                self.sort_ids[&self.definition.symbols[*symbol as usize].result]
            }
            Node::Inj(_, to, _) => *to,
            Node::List(_) => self.sort_ids["List"],
        }
    }

    fn argument_sort(&self, symbol: u32, index: usize) -> u32 {
        self.sort_ids[&self.definition.symbols[symbol as usize].arguments[index]]
    }

    fn result_sort(&self, symbol: u32) -> u32 {
        self.sort_ids[&self.definition.symbols[symbol as usize].result]
    }

    /// The application of the greater production `greater` that the overload axioms equate with
    /// the lesser application `lesser(arguments)`: its arguments injected into `greater`'s.
    fn lifted(&mut self, greater: u32, lesser: u32, arguments: &[Id]) -> Vec<Id> {
        arguments
            .iter()
            .enumerate()
            .map(|(index, argument)| {
                let (from, to) = (
                    self.argument_sort(lesser, index),
                    self.argument_sort(greater, index),
                );
                self.node(Node::Inj(from, to, *argument))
            })
            .collect()
    }

    /// Matches `pattern` against the ground `subject` modulo the injection and overload axioms,
    /// extending `valuation`.
    pub(super) fn matches(
        &mut self,
        pattern: &Pat,
        subject: Id,
        valuation: &mut HashMap<String, Id>,
    ) -> bool {
        if subject == BOTTOM {
            return false;
        }
        match pattern {
            Pat::Var(name, sort) => {
                if self.sort_of(subject) != self.sort_ids[sort] {
                    return false;
                }
                match valuation.get(name) {
                    Some(bound) => *bound == subject,
                    None => {
                        valuation.insert(name.clone(), subject);
                        true
                    }
                }
            }
            Pat::Int(value) => self.nodes[subject as usize] == Node::Int(*value),
            Pat::As(inner, name, _) => {
                self.matches(inner, subject, valuation)
                    && match valuation.get(name) {
                        Some(bound) => *bound == subject,
                        None => {
                            valuation.insert(name.clone(), subject);
                            true
                        }
                    }
            }
            Pat::App(name, arguments) => {
                let symbol = self.symbol_ids[name];
                let children = match self.nodes[subject as usize].clone() {
                    Node::App(head, children) if head == symbol => children,
                    Node::App(head, children)
                        if self.overloads.contains(&(symbol, head))
                            && self.result_sort(head) == self.result_sort(symbol) =>
                    {
                        self.lifted(symbol, head, &children)
                    }
                    Node::Inj(from, to, inner) => match self.nodes[inner as usize].clone() {
                        Node::App(head, children)
                            if self.overloads.contains(&(symbol, head))
                                && self.result_sort(head) == from
                                && self.result_sort(symbol) == to =>
                        {
                            self.lifted(symbol, head, &children)
                        }
                        _ => return false,
                    },
                    _ => return false,
                };
                arguments.len() == children.len()
                    && arguments
                        .iter()
                        .zip(children)
                        .all(|(argument, child)| self.matches(argument, child, valuation))
            }
            Pat::Inj(from, to, inner) => {
                let Node::Inj(source, target, operand) = self.nodes[subject as usize].clone()
                else {
                    return false;
                };
                let (from, to) = (self.sort_ids[from], self.sort_ids[to]);
                if target != to {
                    false
                } else if source == from {
                    self.matches(inner, operand, valuation)
                } else if self.below[source as usize][from as usize] {
                    let lifted = self.node(Node::Inj(source, from, operand));
                    self.matches(inner, lifted, valuation)
                } else {
                    false
                }
            }
            Pat::List(prefix, rest, suffix) => {
                let Node::List(elements) = self.nodes[subject as usize].clone() else {
                    return false;
                };
                let fixed = prefix.len() + suffix.len();
                if elements.len() < fixed || (rest.is_none() && elements.len() != fixed) {
                    return false;
                }
                let middle = elements[prefix.len()..elements.len() - suffix.len()].to_vec();
                let tail = &elements[elements.len() - suffix.len()..];
                if !prefix
                    .iter()
                    .zip(&elements)
                    .chain(suffix.iter().zip(tail))
                    .all(|(element, value)| self.matches(element, *value, valuation))
                {
                    return false;
                }
                match rest {
                    None => true,
                    Some(rest) => {
                        let middle = self.node(Node::List(middle));
                        match valuation.get(rest) {
                            Some(bound) => *bound == middle,
                            None => {
                                valuation.insert(rest.clone(), middle);
                                true
                            }
                        }
                    }
                }
            }
        }
    }

    /// The ground instance of `pattern` under `valuation` (every variable bound).
    pub(super) fn instantiate(&mut self, pattern: &Pat, valuation: &HashMap<String, Id>) -> Id {
        match pattern {
            Pat::Var(name, _) => valuation[name],
            Pat::Int(value) => self.int(*value),
            Pat::As(_, name, _) => valuation[name],
            Pat::App(name, arguments) => {
                let children = arguments
                    .iter()
                    .map(|argument| self.instantiate(argument, valuation))
                    .collect();
                let symbol = self.symbol_ids[name];
                self.node(Node::App(symbol, children))
            }
            Pat::Inj(from, to, inner) => {
                let operand = self.instantiate(inner, valuation);
                let (from, to) = (self.sort_ids[from], self.sort_ids[to]);
                self.node(Node::Inj(from, to, operand))
            }
            Pat::List(prefix, rest, suffix) => {
                let mut elements = prefix
                    .iter()
                    .map(|element| self.instantiate(element, valuation))
                    .collect::<Vec<_>>();
                if let Some(rest) = rest {
                    match self.nodes[valuation[rest] as usize].clone() {
                        Node::List(middle) => elements.extend(middle),
                        _ => elements.push(BOTTOM),
                    }
                }
                elements.extend(
                    suffix
                        .iter()
                        .map(|element| self.instantiate(element, valuation))
                        .collect::<Vec<_>>(),
                );
                self.node(Node::List(elements))
            }
        }
    }

    /// The ground term of a ground pattern.
    pub(super) fn ground(&mut self, pattern: &Pat) -> Id {
        self.instantiate(pattern, &HashMap::new())
    }

    /// Every normal form of `id` under `->E`.
    pub(super) fn normalize(&mut self, id: Id) -> Rc<Normal> {
        if let Some(normal) = self.normal.get(&id) {
            return Rc::clone(normal);
        }
        if !self.in_progress.insert(id) {
            // A term that reaches itself: its evaluation need not end.
            return Rc::new(Normal::incomplete());
        }
        self.work += 1;
        let normal = if self.work > MAX_WORK || self.sizes[id as usize] > MAX_SIZE {
            Normal::incomplete()
        } else {
            self.evaluate(id).finish()
        };
        self.in_progress.remove(&id);
        let normal = Rc::new(normal);
        self.normal.insert(id, Rc::clone(&normal));
        normal
    }

    /// Whether `id` is a normal form other than `\bottom`: it evaluates to itself only.
    pub(super) fn is_normal_form(&mut self, id: Id) -> bool {
        id != BOTTOM && self.normalize(id).unique() == Some(id)
    }

    fn evaluate(&mut self, id: Id) -> Normal {
        match self.nodes[id as usize].clone() {
            Node::Bottom | Node::Int(_) | Node::Bool(_) => Normal::of(id),
            Node::Inj(from, to, argument) => {
                let inner = self.normalize(argument);
                let mut normal = Normal {
                    forms: Vec::new(),
                    ..(*inner).clone()
                };
                for form in &inner.forms {
                    let form = self.node(Node::Inj(from, to, *form));
                    normal.forms.push(form);
                }
                normal
            }
            Node::List(elements) => self.combinations(&elements, |universe, elements| {
                let list = universe.node(Node::List(elements));
                Normal::of(list)
            }),
            Node::App(symbol, arguments) => {
                let mut normal = Normal::of(BOTTOM);
                normal.forms.clear();
                if self.outermost_too && self.definition.symbols[symbol as usize].kind != Kind::Hook
                {
                    // The switched-off discipline: a root step before the arguments are
                    // evaluated.
                    let root = self.root(id, symbol, false);
                    if !root.forms.is_empty() && root.forms != [id] {
                        normal.merge(&root);
                    }
                }
                let evaluated = self.combinations(&arguments, |universe, arguments| {
                    let application = universe.node(Node::App(symbol, arguments));
                    if application == id {
                        universe.root(id, symbol, true)
                    } else {
                        (*universe.normalize(application)).clone()
                    }
                });
                normal.merge(&evaluated);
                normal
            }
        }
    }

    /// Evaluates every combination of the normal forms of `children` with `then`; `\bottom` when
    /// a child's normal form is.
    fn combinations(
        &mut self,
        children: &[Id],
        mut then: impl FnMut(&mut Self, Vec<Id>) -> Normal,
    ) -> Normal {
        let mut normal = Normal::of(BOTTOM);
        normal.forms.clear();
        let mut choices = vec![Vec::new()];
        for child in children {
            let child = self.normalize(*child);
            normal.complete &= child.complete;
            normal.applied |= child.applied;
            normal.total_undefined |= child.total_undefined;
            if child.forms.is_empty() {
                normal.complete = false;
                return normal;
            }
            let mut next = Vec::new();
            for choice in &choices {
                for form in &child.forms {
                    let mut extended: Vec<Id> = choice.clone();
                    extended.push(*form);
                    next.push(extended);
                }
            }
            if next.len() > MAX_COMBINATIONS {
                normal.complete = false;
                next.truncate(MAX_COMBINATIONS);
            }
            choices = next;
        }
        for choice in choices {
            if choice.contains(&BOTTOM) {
                normal.forms.push(BOTTOM);
            } else {
                let result = then(self, choice);
                normal.merge(&result);
            }
        }
        normal
    }

    /// The root steps of the application `id` of `symbol`, whose arguments are normal forms when
    /// `innermost`; with `innermost` off, only the reducts (no stuck reading).
    fn root(&mut self, id: Id, symbol: u32, innermost: bool) -> Normal {
        let declared = self.definition.symbols[symbol as usize].clone();
        if declared.kind == Kind::Hook {
            return self.hook(&declared.name, &self.children(id));
        }
        let mut normal = Normal::of(BOTTOM);
        normal.forms.clear();
        let groups = self.groups[symbol as usize].clone();
        let definition = self.definition;
        for group in groups {
            let mut fired = false;
            for index in group {
                let equation = &definition.equations[index];
                let mut valuation = HashMap::new();
                if !self.matches(&equation.lhs, id, &mut valuation) {
                    continue;
                }
                if let Some(requires) = &equation.requires {
                    let condition = self.instantiate(requires, &valuation);
                    let condition = self.normalize(condition);
                    normal.complete &= condition.complete;
                    normal.applied |= condition.applied;
                    let truth = self.boolean(true);
                    if !condition.forms.contains(&truth) {
                        continue;
                    }
                }
                fired = true;
                normal.applied |= 1u128 << index;
                if let Some(ensures) = &equation.ensures {
                    let condition = self.instantiate(ensures, &valuation);
                    let condition = self.normalize(condition);
                    normal.complete &= condition.complete;
                    normal.applied |= condition.applied;
                    let truth = self.boolean(true);
                    if condition.forms.iter().any(|form| *form != truth) {
                        normal.forms.push(BOTTOM);
                    }
                    if !condition.forms.contains(&truth) {
                        continue;
                    }
                }
                let reduct = self.instantiate(&equation.rhs, &valuation);
                if reduct == id {
                    normal.complete = false;
                    continue;
                }
                let reduct = self.normalize(reduct);
                normal.merge(&reduct);
            }
            if fired {
                return normal;
            }
        }
        if !innermost {
            return normal;
        }
        match declared.kind {
            Kind::Function { total: false } => normal.forms.push(BOTTOM),
            _ => normal.forms.push(id),
        }
        normal
    }

    /// The equations of the first priority group that has an equation applying at the
    /// application `id`, whose arguments are normal forms, each with its matching valuation; and
    /// whether every `requires` they evaluated ended.
    pub(super) fn applicable(&mut self, id: Id) -> (Vec<Applying>, bool) {
        let Node::App(symbol, _) = self.nodes[id as usize].clone() else {
            return (Vec::new(), true);
        };
        let definition = self.definition;
        let mut complete = true;
        for group in self.groups[symbol as usize].clone() {
            let mut applying = Vec::new();
            for index in group {
                let equation = &definition.equations[index];
                let mut valuation = HashMap::new();
                if !self.matches(&equation.lhs, id, &mut valuation) {
                    continue;
                }
                if let Some(requires) = &equation.requires {
                    let condition = self.instantiate(requires, &valuation);
                    let condition = self.normalize(condition);
                    complete &= condition.complete;
                    let truth = self.boolean(true);
                    if !condition.forms.contains(&truth) {
                        continue;
                    }
                }
                applying.push((index, valuation));
            }
            if !applying.is_empty() {
                return (applying, complete);
            }
        }
        (Vec::new(), complete)
    }

    /// A hooked operation on normal-form arguments.
    fn hook(&mut self, name: &str, arguments: &[Id]) -> Normal {
        let values = arguments
            .iter()
            .map(|argument| self.nodes[*argument as usize].clone())
            .collect::<Vec<_>>();
        let result = match (name, values.as_slice()) {
            ("divInt", [Node::Int(_), Node::Int(0)]) => Some(BOTTOM),
            ("divInt", [Node::Int(left), Node::Int(right)]) => {
                left.checked_div(*right).map(|value| self.int(value))
            }
            ("addInt", [Node::Int(left), Node::Int(right)]) => {
                left.checked_add(*right).map(|value| self.int(value))
            }
            ("eqInt", [Node::Int(left), Node::Int(right)]) => Some(self.boolean(left == right)),
            ("ltInt", [Node::Int(left), Node::Int(right)]) => Some(self.boolean(left < right)),
            ("notBool", [Node::Bool(value)]) => Some(self.boolean(!value)),
            // `KEQUAL.eq` on normal forms: distinct normal forms are distinct elements of `M_NF`.
            ("eqA", [_, _]) => Some(self.boolean(arguments[0] == arguments[1])),
            _ => None,
        };
        match result {
            Some(result) => Normal::of(result),
            // A hook on a term that is not a literal: outside the oracle's model.
            None => Normal::incomplete(),
        }
    }

    /// Whether `id` applies a total symbol (a constructor, or a symbol declared `total`) whose
    /// arguments have defined normal forms, while `id` has `\bottom` among its normal forms: a
    /// violation of P2 at `id`.
    pub(super) fn violates_totality(&mut self, id: Id) -> bool {
        let Node::App(symbol, arguments) = self.nodes[id as usize].clone() else {
            return false;
        };
        if !self.definition.symbols[symbol as usize].total() {
            return false;
        }
        let defined = arguments.iter().all(|argument| {
            let normal = self.normalize(*argument);
            normal.complete && !normal.forms.contains(&BOTTOM)
        });
        defined && self.normalize(id).forms.contains(&BOTTOM)
    }

    /// The KORE text of `id`, with the subterm `hole` (if any) written as `variable`.
    pub(super) fn kore(&self, id: Id, hole: Option<(Id, &str)>) -> String {
        if let Some((target, variable)) = hole
            && target == id
        {
            return variable.to_owned();
        }
        match &self.nodes[id as usize] {
            Node::Bottom => panic!("no query holds \\bottom"),
            Node::Int(value) => format!(r#"\dv{{SortInt{{}}}}("{value}")"#),
            Node::Bool(value) => format!(r#"\dv{{SortBool{{}}}}("{value}")"#),
            Node::App(symbol, children) => format!(
                "{}{{}}({})",
                self.definition.symbols[*symbol as usize].name,
                children
                    .iter()
                    .map(|child| self.kore(*child, hole))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Node::Inj(from, to, child) => format!(
                "inj{{Sort{}{{}}, Sort{}{{}}}}({})",
                self.sort_names[*from as usize],
                self.sort_names[*to as usize],
                self.kore(*child, hole)
            ),
            Node::List(elements) => super::language::list_kore(
                elements
                    .iter()
                    .map(|element| format!("listItem{{}}({})", self.kore(*element, hole)))
                    .collect(),
            ),
        }
    }

    /// A readable rendering of `id`.
    pub(super) fn show(&self, id: Id) -> String {
        match &self.nodes[id as usize] {
            Node::Bottom => "⊥".to_owned(),
            Node::Int(value) => value.to_string(),
            Node::Bool(value) => value.to_string(),
            Node::App(symbol, children) => {
                let name = &self.definition.symbols[*symbol as usize].name;
                if children.is_empty() {
                    name.clone()
                } else {
                    format!(
                        "{name}({})",
                        children
                            .iter()
                            .map(|child| self.show(*child))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                }
            }
            Node::Inj(from, to, child) => format!(
                "inj{{{}, {}}}({})",
                self.sort_names[*from as usize],
                self.sort_names[*to as usize],
                self.show(*child)
            ),
            Node::List(elements) => format!(
                "[{}]",
                elements
                    .iter()
                    .map(|element| self.show(*element))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }
    }

    /// The symbols applied in `id`.
    pub(super) fn symbols_in(&self, id: Id, into: &mut HashSet<u32>) {
        if let Node::App(symbol, _) = &self.nodes[id as usize] {
            into.insert(*symbol);
        }
        for child in self.children(id) {
            self.symbols_in(child, into);
        }
    }
}
