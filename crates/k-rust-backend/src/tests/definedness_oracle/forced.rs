//! V6 (d): what every model of a definition must satisfy, derived from its axioms alone, with
//! no use of the backend's taint closure, of `SortReach` or of `M_NF` (the design's "Revision
//! after review 1", R1.7). The contract's property (B) says that the claims on untainted terms
//! hold together in one model whenever the definition has one; a claim on a term that every
//! model makes undefined refutes it.
//!
//! The models are those of the contract: sorts may be empty, `\bottom` is the undefined term,
//! symbols are strict, and an axiom's variables range over elements. On the explored ground
//! terms the derivation computes
//!
//! - `FD`, defined in every model: literals, and applications of constructors and of symbols
//!   declared total (hooks where the hook is defined) to `FD` arguments, injections and lists of
//!   `FD` terms (the functional axioms and precondition P2);
//! - equal in every model: `l rho = r rho` for an equation of its root's highest priority group,
//!   not `symbolic`, whose `requires` is absent or holds by the hooks alone, and whose `ensures`
//!   is absent or decided by the hooks alone (`r rho` is `\bottom` where it is false),
//!   whose left-hand side matches the term, and all of whose bindings (the term's arguments and
//!   the pattern variables) are `FD` (the axiom instance holds because its bindings are
//!   elements); a union-find over these instances;
//! - `FU`, undefined in every model: a hook on literals where it is undefined, a term with an
//!   `FU` subterm (strictness), a term equal to an `FU` term, the remaining argument of an `FU`
//!   application of a total symbol whose other arguments are `FD`, the operand of an `FU`
//!   injection, and the single binding not in `FD` of two matching equation instances at one
//!   term whose right-hand sides are apart when that binding is defined (if it were defined,
//!   both instances would hold and identify two different elements, or an element with an
//!   undefined term).
//!
//! When an `FD` term is `FU`, or two `FD` terms apart by no-confusion are equal, the definition
//! has no model at all, (B) holds vacuously, and nothing is checked.

use std::collections::{BTreeSet, HashMap, HashSet};

use super::{
    engine::{BOTTOM, Id, Node, Universe},
    language::{Kind, Pat},
};

/// Bounds of one derivation.
const MAX_TERMS: usize = 4_000;
const MAX_TERM_SIZE: u32 = 30;
const MAX_ROUNDS: usize = 64;

/// What every model makes undefined, on the explored terms.
#[derive(Debug, Default)]
pub(super) struct Forced {
    undefined: HashSet<Id>,
    defined: HashSet<Id>,
    /// Why the definition has no model, when the derivation shows it.
    pub(super) inconsistent: Option<String>,
}

impl Forced {
    /// Whether every model makes `id` undefined.
    pub(super) fn undefined(&self, id: Id) -> bool {
        self.undefined.contains(&id)
    }

    /// Whether every model makes the explored term `id` defined.
    pub(super) fn defined(&self, id: Id) -> bool {
        self.defined.contains(&id)
    }
}

/// An axiom instance at `term`: `term = rhs` holds in every model where every term of `guard`
/// (the bindings not in `FD`) is defined.
struct Instance {
    term: Id,
    rhs: Id,
    guard: Vec<Id>,
}

struct Derivation<'u, 'd> {
    universe: &'u mut Universe<'d>,
    terms: Vec<Id>,
    instances: Vec<Instance>,
    parent: HashMap<Id, Id>,
    undefined: HashSet<Id>,
    defined: HashMap<Id, bool>,
    /// The classes of the equalities, by root, refreshed after each round's unions.
    classes: HashMap<Id, Vec<Id>>,
    /// The roots of the classes with an undefined member.
    undefined_roots: HashSet<Id>,
}

/// The derivation over `roots`, their subterms and the right-hand sides of the instances found.
pub(super) fn derive(universe: &mut Universe<'_>, roots: &[Id]) -> Forced {
    let mut derivation = Derivation {
        universe,
        terms: Vec::new(),
        instances: Vec::new(),
        parent: HashMap::new(),
        undefined: HashSet::new(),
        defined: HashMap::new(),
        classes: HashMap::new(),
        undefined_roots: HashSet::new(),
    };
    derivation.explore(roots);
    let inconsistent = derivation.saturate();
    let defined = derivation
        .defined
        .iter()
        .filter(|(_, defined)| **defined)
        .map(|(id, _)| *id)
        .collect();
    Forced {
        undefined: derivation.undefined,
        defined,
        inconsistent,
    }
}

impl Derivation<'_, '_> {
    fn explore(&mut self, roots: &[Id]) {
        let definition = self.universe.definition;
        let mut seen = HashSet::new();
        let mut queue = roots.to_vec();
        while let Some(id) = queue.pop() {
            if id == BOTTOM
                || !seen.insert(id)
                || self.terms.len() >= MAX_TERMS
                || self.universe.size(id) > MAX_TERM_SIZE
            {
                continue;
            }
            self.terms.push(id);
            queue.extend(self.universe.children(id));
            let Node::App(symbol, _) = self.universe.node_of(id).clone() else {
                continue;
            };
            for index in self.universe.first_group(symbol) {
                let equation = &definition.equations[index];
                if equation.symbolic {
                    continue;
                }
                let mut valuation = HashMap::new();
                if !self.universe.matches(&equation.lhs, id, &mut valuation) {
                    continue;
                }
                if let Some(requires) = &equation.requires
                    && self.truth_by_hooks(requires, &valuation) != Some(true)
                {
                    continue;
                }
                // Where the `ensures` is false the instance's right-hand side is `\bottom`.
                let rhs = match &equation.ensures {
                    None => self.universe.instantiate(&equation.rhs, &valuation),
                    Some(ensures) => match self.truth_by_hooks(ensures, &valuation) {
                        Some(true) => self.universe.instantiate(&equation.rhs, &valuation),
                        Some(false) => BOTTOM,
                        None => continue,
                    },
                };
                // The axiom binds each argument of the term by membership in its argument
                // pattern, and each pattern variable inside it: an instance states something
                // only where all of these are defined.
                let mut guard = valuation
                    .values()
                    .copied()
                    .chain(self.universe.children(id))
                    .filter(|value| !self.fd(*value))
                    .collect::<Vec<_>>();
                guard.sort_unstable();
                guard.dedup();
                self.instances.push(Instance {
                    term: id,
                    rhs,
                    guard,
                });
                queue.push(rhs);
            }
        }
    }

    /// The truth of `condition` under `valuation` by the hooks alone, when it mentions only
    /// hooked symbols and its variables are bound to literals.
    fn truth_by_hooks(&mut self, condition: &Pat, valuation: &HashMap<String, Id>) -> Option<bool> {
        fn hooks_only(pattern: &Pat, hooks: &BTreeSet<&str>) -> bool {
            match pattern {
                Pat::App(name, arguments) => {
                    hooks.contains(name.as_str())
                        && arguments.iter().all(|argument| hooks_only(argument, hooks))
                }
                Pat::Var(..) | Pat::Int(_) => true,
                Pat::Inj(..) | Pat::As(..) | Pat::List(..) => false,
            }
        }
        let definition = self.universe.definition;
        let hooks = definition
            .symbols
            .iter()
            .filter(|symbol| symbol.kind == Kind::Hook)
            .map(|symbol| symbol.name.as_str())
            .chain(["true", "false"])
            .collect::<BTreeSet<_>>();
        if !hooks_only(condition, &hooks) {
            return None;
        }
        let mut variables = std::collections::BTreeMap::new();
        super::language::pattern_variables(condition, &mut variables);
        if !variables.keys().all(|name| {
            valuation.get(name).is_some_and(|value| {
                matches!(self.universe.node_of(*value), Node::Int(_) | Node::Bool(_))
            })
        }) {
            return None;
        }
        let condition = self.universe.instantiate(condition, valuation);
        let normal = self.universe.normalize(condition);
        let (truth, falsity) = (self.universe.boolean(true), self.universe.boolean(false));
        if !normal.complete {
            None
        } else if normal.forms == [truth] {
            Some(true)
        } else if normal.forms == [falsity] {
            Some(false)
        } else {
            None
        }
    }

    /// Defined in every model.
    fn fd(&mut self, id: Id) -> bool {
        if let Some(known) = self.defined.get(&id) {
            return *known;
        }
        let definition = self.universe.definition;
        let result = match self.universe.node_of(id).clone() {
            Node::Bottom => false,
            Node::Int(_) | Node::Bool(_) => true,
            Node::Inj(_, _, operand) => self.fd(operand),
            Node::List(elements) => elements.iter().all(|element| self.fd(*element)),
            Node::App(symbol, arguments) => {
                let declared = &definition.symbols[symbol as usize];
                let arguments_defined = arguments.iter().all(|argument| self.fd(*argument));
                if declared.kind == Kind::Hook {
                    arguments_defined && self.hook_value(id) == Some(true)
                } else {
                    declared.total() && arguments_defined
                }
            }
        };
        self.defined.insert(id, result);
        result
    }

    /// For a hooked application of literals: whether the hook is defined there.
    fn hook_value(&mut self, id: Id) -> Option<bool> {
        let Node::App(symbol, arguments) = self.universe.node_of(id).clone() else {
            return None;
        };
        if self.universe.definition.symbols[symbol as usize].kind != Kind::Hook {
            return None;
        }
        if !arguments.iter().all(|argument| {
            matches!(
                self.universe.node_of(*argument),
                Node::Int(_) | Node::Bool(_)
            )
        }) {
            return None;
        }
        let normal = self.universe.normalize(id);
        if !normal.complete || normal.forms.len() != 1 {
            return None;
        }
        Some(normal.forms[0] != BOTTOM)
    }

    fn find(&mut self, id: Id) -> Id {
        let mut root = id;
        while let Some(&next) = self.parent.get(&root) {
            if next == root {
                break;
            }
            root = next;
        }
        self.parent.insert(id, root);
        root
    }

    fn union(&mut self, left: Id, right: Id) -> bool {
        let (left, right) = (self.find(left), self.find(right));
        if left == right {
            return false;
        }
        self.parent.insert(left, right);
        true
    }

    fn members(&mut self, id: Id) -> Vec<Id> {
        let root = self.find(id);
        self.classes.get(&root).cloned().unwrap_or_else(|| vec![id])
    }

    fn refresh_classes(&mut self) {
        let mut classes = HashMap::<Id, Vec<Id>>::new();
        for term in self.terms.clone() {
            let root = self.find(term);
            classes.entry(root).or_default().push(term);
        }
        self.classes = classes;
        let undefined = self.undefined.iter().copied().collect::<Vec<_>>();
        self.undefined_roots = undefined.into_iter().map(|id| self.find(id)).collect();
    }

    fn class_undefined(&mut self, id: Id) -> bool {
        let root = self.find(id);
        self.undefined_roots.contains(&root)
    }

    /// Defined in every model in which every term of `assumed` is.
    fn defined_assuming(&mut self, id: Id, assumed: &[Id]) -> bool {
        if assumed.contains(&id) || self.fd(id) {
            return true;
        }
        let definition = self.universe.definition;
        match self.universe.node_of(id).clone() {
            Node::Inj(_, _, operand) => self.defined_assuming(operand, assumed),
            Node::List(elements) => elements
                .iter()
                .all(|element| self.defined_assuming(*element, assumed)),
            Node::App(symbol, arguments) => {
                let declared = &definition.symbols[symbol as usize];
                declared.kind != Kind::Hook
                    && declared.total()
                    && arguments
                        .iter()
                        .all(|argument| self.defined_assuming(*argument, assumed))
            }
            Node::Bottom | Node::Int(_) | Node::Bool(_) => false,
        }
    }

    /// Whether `left` and `right` differ in every model in which every term of `assumed` is
    /// defined: one is undefined and the other defined, or both are defined and apart by
    /// no-confusion (different literals, constructors, list lengths, or apart arguments).
    fn apart(&mut self, left: Id, right: Id, assumed: &[Id], depth: usize) -> bool {
        if depth == 0 || self.find(left) == self.find(right) {
            return false;
        }
        let (left_undefined, right_undefined) =
            (self.class_undefined(left), self.class_undefined(right));
        if (left_undefined && self.defined_assuming(right, assumed))
            || (right_undefined && self.defined_assuming(left, assumed))
        {
            return true;
        }
        for x in self.members(left) {
            for y in self.members(right) {
                if self.structurally_apart(x, y, assumed, depth) {
                    return true;
                }
            }
        }
        false
    }

    fn structurally_apart(&mut self, x: Id, y: Id, assumed: &[Id], depth: usize) -> bool {
        if !(self.defined_assuming(x, assumed) && self.defined_assuming(y, assumed)) {
            return false;
        }
        let definition = self.universe.definition;
        match (
            self.universe.node_of(x).clone(),
            self.universe.node_of(y).clone(),
        ) {
            (Node::Int(a), Node::Int(b)) => a != b,
            (Node::Bool(a), Node::Bool(b)) => a != b,
            (Node::App(f, left), Node::App(g, right)) => {
                let constructors = definition.symbols[f as usize].kind == Kind::Constructor
                    && definition.symbols[g as usize].kind == Kind::Constructor;
                if !constructors {
                    return false;
                }
                f != g
                    || left
                        .iter()
                        .zip(&right)
                        .any(|(a, b)| self.apart(*a, *b, assumed, depth - 1))
            }
            (Node::Inj(from, to, a), Node::Inj(other_from, other_to, b)) => {
                from == other_from && to == other_to && self.apart(a, b, assumed, depth - 1)
            }
            (Node::List(left), Node::List(right)) => {
                left.len() != right.len()
                    || left
                        .iter()
                        .zip(&right)
                        .any(|(a, b)| self.apart(*a, *b, assumed, depth - 1))
            }
            _ => false,
        }
    }

    fn mark(&mut self, id: Id) -> bool {
        let root = self.find(id);
        self.undefined_roots.insert(root);
        self.undefined.insert(id)
    }

    /// Saturates `FU` and the equalities; the reason the definition has no model, if found.
    #[allow(
        clippy::too_many_lines,
        reason = "one fixpoint over the derivation rules"
    )]
    fn saturate(&mut self) -> Option<String> {
        let definition = self.universe.definition;
        let terms = self.terms.clone();
        self.undefined.insert(BOTTOM);
        for round in 0..MAX_ROUNDS {
            let mut changed = false;
            for index in 0..self.instances.len() {
                if self.instances[index].guard.is_empty() {
                    let (term, rhs) = (self.instances[index].term, self.instances[index].rhs);
                    changed |= self.union(term, rhs);
                }
            }
            self.refresh_classes();
            for &id in &terms {
                if self.undefined.contains(&id) {
                    continue;
                }
                let base = self.hook_value(id) == Some(false)
                    || self
                        .universe
                        .children(id)
                        .iter()
                        .any(|child| self.undefined.contains(child));
                if base || self.class_undefined(id) {
                    changed |= self.mark(id);
                }
            }
            for &id in &terms {
                if !self.undefined.contains(&id) {
                    continue;
                }
                match self.universe.node_of(id).clone() {
                    Node::Inj(_, _, operand) => changed |= self.mark(operand),
                    Node::App(symbol, arguments)
                        if definition.symbols[symbol as usize].total()
                            && definition.symbols[symbol as usize].kind != Kind::Hook =>
                    {
                        let open = arguments
                            .iter()
                            .copied()
                            .filter(|argument| !self.fd(*argument))
                            .collect::<Vec<_>>();
                        if let [only] = open.as_slice() {
                            changed |= self.mark(*only);
                        }
                    }
                    _ => {}
                }
            }
            // Two instances at one term whose right-hand sides are apart when their bindings
            // are defined: one of the bindings is undefined.
            let mut by_term = HashMap::<Id, Vec<usize>>::new();
            for (index, instance) in self.instances.iter().enumerate() {
                by_term.entry(instance.term).or_default().push(index);
            }
            for indexes in by_term.values() {
                for (position, &first) in indexes.iter().enumerate() {
                    for &second in &indexes[position + 1..] {
                        let mut guard = self.instances[first].guard.clone();
                        guard.extend(self.instances[second].guard.iter().copied());
                        guard.sort_unstable();
                        guard.dedup();
                        if guard.len() != 1 || self.undefined.contains(&guard[0]) {
                            continue;
                        }
                        let (left, right) = (self.instances[first].rhs, self.instances[second].rhs);
                        if self.apart(left, right, &guard, 4) {
                            changed |= self.mark(guard[0]);
                        }
                    }
                }
            }
            // No model: an `FD` term undefined, or two `FD` terms apart and equal.
            for &id in &terms {
                if self.undefined.contains(&id) && self.fd(id) {
                    return Some(format!(
                        "a term defined in every model is undefined (round {round})"
                    ));
                }
            }
            let classes = self.classes.values().cloned().collect::<Vec<_>>();
            for members in classes {
                for (position, &x) in members.iter().enumerate() {
                    for &y in &members[position + 1..] {
                        if self.structurally_apart(x, y, &[], 4) {
                            return Some(format!(
                                "two terms apart in every model are equal (round {round})"
                            ));
                        }
                    }
                }
            }
            if !changed {
                return None;
            }
        }
        None
    }
}
