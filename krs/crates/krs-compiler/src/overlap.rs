//! Sort-aware overlap checking of transitions (decisions.md, F2 and its amendment).
//!
//! Every transition is checked: readable tables, `#[k::rule]` term rules
//! completed to the computation-cell head, and `cells!` rules. Equations,
//! simplifications, aliases, claims, anywhere rules, and heat and cool rules
//! (K orders those by the result-sort condition it adds) are not. Rules at
//! different priorities never overlap; rules of one `nondet` group may, and
//! the group is validated instead; and complementary guard conjuncts (the
//! catalog's [`GuardMeaning`] of each Bool-valued builtin), or a guard
//! conjunct that unification makes false on literal operands, separate two
//! rules after unification. Members of one `overload` family are one
//! head: K's overload axioms identify `expDot(inj(L), F)` with
//! `inj(lValDot(L, F))`, so their applications unify when their arguments do
//! (clause 7c). An `A | B` or-pattern contributes the cross product of its
//! alternatives (clause 7b), and in any sentence two of its alternatives
//! that bind variables must not match one term with different bindings
//! (clause 8, KF-030). A rule's footprint includes the cells read by the
//! function contexts of the equations reachable from its requires and result
//! (clause 5, KF-025); such a cell is unified as an unconstrained variable.
//! List, Set and K-sequence patterns are unified modulo their collection
//! axioms by an over-approximation that answers "disjoint" only when no
//! collection matches both sides (clause 7e).

use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    ApplicationRef, BuiltinOperation, BuiltinSort, GuardMeaning, ItemKind, ListOperation,
    MapOperation, ProductionAttribute, SemanticId, SetOperation, StableItemId,
};
use krs_ir_levels::{
    IrCondition, RuleBodyRef, SemanticApplicationRef, SemanticModule, SemanticRule,
    SemanticSortRef, SemanticTerm, SemanticTermKind,
};

use crate::int_facts::{IntFact, IntFacts, evaluate_int};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct VariableKey {
    rule: usize,
    ordinal: usize,
}

#[derive(Clone, Debug)]
enum Pattern {
    Variable {
        key: VariableKey,
        sort: SemanticSortRef,
    },
    Application {
        sort: SemanticSortRef,
        application: SemanticApplicationRef,
        arguments: Vec<Self>,
        /// A parametric application's instance: with the symbol, its
        /// identity (X10.7d, KF-027).
        instance: Vec<SemanticSortRef>,
    },
    Token {
        sort: SemanticSortRef,
        value: String,
    },
    KSequence {
        sort: SemanticSortRef,
        items: Vec<Self>,
    },
    Map {
        sort: SemanticSortRef,
        operation: MapOperation,
        arguments: Vec<Self>,
    },
    List {
        sort: SemanticSortRef,
        operation: ListOperation,
        arguments: Vec<Self>,
    },
    Set {
        sort: SemanticSortRef,
        operation: SetOperation,
        arguments: Vec<Self>,
    },
    Cell {
        sort: SemanticSortRef,
        cell: SemanticId,
        children: Vec<Self>,
    },
    /// `k::matches!(subject, pattern)` in a guard (KF-031): the subject, and
    /// the pattern's shape with its local binders and wildcards renamed
    /// canonically, so two guards testing one subject against one shape are
    /// the same guard.
    Matches {
        sort: SemanticSortRef,
        subject: Box<Self>,
        shape: String,
    },
    /// A `let` block (KF-032) in a guard: opaque, the same as no other
    /// term, so no guard is complementary to it (conservative).
    Opaque { sort: SemanticSortRef },
}

impl Pattern {
    fn sort(&self) -> &SemanticSortRef {
        match self {
            Self::Variable { sort, .. }
            | Self::Application { sort, .. }
            | Self::Token { sort, .. }
            | Self::KSequence { sort, .. }
            | Self::Map { sort, .. }
            | Self::List { sort, .. }
            | Self::Set { sort, .. }
            | Self::Cell { sort, .. }
            | Self::Matches { sort, .. }
            | Self::Opaque { sort } => sort,
        }
    }
}

#[derive(Default)]
struct VariableCatalog {
    by_rule: [BTreeMap<SemanticId, VariableKey>; 2],
    /// Variables standing for cells read only through a function context.
    unconstrained: [usize; 2],
    /// Each `alias @ pattern` met so far: the alias denotes the term its
    /// pattern matches (clause 7b), so it is unified with that pattern.
    aliases: Vec<(VariableKey, SemanticSortRef, Pattern)>,
    /// The alternative each `A | B` node of each side stands for in this
    /// unification, keyed by the node's address (clause 7b).
    choices: [Choice; 2],
}

/// The alternative chosen at each or-pattern node, keyed by its address.
type Choice = BTreeMap<usize, usize>;

fn node_address(term: &SemanticTerm) -> usize {
    std::ptr::from_ref(term) as usize
}

/// The direct subterms of `term`.
fn subterms(term: &SemanticTerm) -> Vec<&SemanticTerm> {
    match term.kind() {
        SemanticTermKind::Variable { .. } | SemanticTermKind::Token { .. } => Vec::new(),
        SemanticTermKind::Application { arguments, .. } => arguments.iter().collect(),
        SemanticTermKind::KSequence { items, .. } => items.iter().collect(),
        SemanticTermKind::Map(operands) => operands.operands().collect(),
        SemanticTermKind::List(operands) => operands.operands().collect(),
        SemanticTermKind::Set(operands) => operands.operands().collect(),
        SemanticTermKind::Cell { children, .. } => children.iter().collect(),
        SemanticTermKind::Rewrite { from, to } => vec![from.as_ref(), to.as_ref()],
        SemanticTermKind::As { pattern, .. } => vec![pattern.as_ref()],
        SemanticTermKind::Or { alternatives } => alternatives.iter().collect(),
        // A `k::matches!` pattern binds its own names and is never unified
        // with a rule's patterns.
        SemanticTermKind::Matches { subject, .. } => vec![subject.as_ref()],
        // Likewise a `let` pattern; its value and body are ordinary terms.
        SemanticTermKind::Let { value, body, .. } => vec![value.as_ref(), body.as_ref()],
    }
}

/// The direct subterms of a pre-pattern's left image: a local rewrite
/// (KF-011) contributes only its left side.
fn pattern_subterms(term: &SemanticTerm) -> Vec<&SemanticTerm> {
    match term.kind() {
        SemanticTermKind::Rewrite { from, .. } => vec![from.as_ref()],
        _ => subterms(term),
    }
}

/// The canonical shape of a `k::matches!` pattern: its structure with each
/// local binder renamed by first occurrence and each wildcard written `_`.
fn matches_shape(term: &SemanticTerm, names: &mut BTreeMap<SemanticId, usize>) -> String {
    let list = |terms: Vec<&SemanticTerm>, names: &mut BTreeMap<SemanticId, usize>| {
        terms
            .into_iter()
            .map(|term| matches_shape(term, names))
            .collect::<Vec<_>>()
            .join(",")
    };
    let sort = term.sort();
    match term.kind() {
        SemanticTermKind::Variable { variable } => {
            if variable.kind() == krs_ir::SemanticIdKind::Wildcard {
                format!("_:{sort}")
            } else {
                let next = names.len();
                let index = *names.entry(variable.clone()).or_insert(next);
                format!("${index}:{sort}")
            }
        }
        SemanticTermKind::Token { value } => format!("{value:?}:{sort}"),
        SemanticTermKind::Application {
            application,
            arguments,
            instance,
            ..
        } => format!(
            "{application:?}{instance:?}({})",
            list(arguments.iter().collect(), names)
        ),
        SemanticTermKind::As { alias, pattern } => {
            let next = names.len();
            let index = *names.entry(alias.clone()).or_insert(next);
            format!("(${index}@{})", matches_shape(pattern, names))
        }
        SemanticTermKind::Or { alternatives } => {
            format!(
                "({})",
                list(alternatives.iter().collect(), names).replace(',', "|")
            )
        }
        _ => format!("{:?}", term.kind()),
    }
}

/// Every or-pattern node in `term`, in preorder, with its alternative count.
fn or_nodes<'a>(term: &'a SemanticTerm, output: &mut Vec<(&'a SemanticTerm, usize)>) {
    if let SemanticTermKind::Or { alternatives } = term.kind() {
        output.push((term, alternatives.len()));
    }
    for child in pattern_subterms(term) {
        or_nodes(child, output);
    }
}

/// The cross product of the alternatives of `nodes`: one choice per
/// combination. A choice at a node inside an unchosen alternative is unused,
/// so some combinations repeat; the product is bounded by the authored size.
fn choices(nodes: &[(&SemanticTerm, usize)]) -> Vec<Choice> {
    let mut output = vec![Choice::new()];
    for (node, count) in nodes {
        output = output
            .into_iter()
            .flat_map(|choice| {
                (0..*count).map(move |index| {
                    let mut choice = choice.clone();
                    choice.insert(node_address(node), index);
                    choice
                })
            })
            .collect();
    }
    output
}

/// Every occurrence of a named (authored) variable in `term`, counted.
fn named_occurrences(term: &SemanticTerm, output: &mut BTreeMap<SemanticId, usize>) {
    let named = |variable: &SemanticId| matches!(variable.kind(), krs_ir::SemanticIdKind::Named);
    match term.kind() {
        SemanticTermKind::Variable { variable } if named(variable) => {
            *output.entry(variable.clone()).or_default() += 1;
        }
        SemanticTermKind::As { alias, .. } if named(alias) => {
            *output.entry(alias.clone()).or_default() += 1;
        }
        _ => {}
    }
    for child in pattern_subterms(term) {
        named_occurrences(child, output);
    }
}

impl VariableCatalog {
    /// A variable no named binder shares: a cell in a footprint only
    /// through a function context (clause 5, KF-025).
    fn unconstrained(&mut self, rule: usize) -> VariableKey {
        self.unconstrained[rule] += 1;
        VariableKey {
            rule,
            ordinal: usize::MAX - self.unconstrained[rule],
        }
    }

    fn key(&mut self, rule: usize, id: &SemanticId) -> VariableKey {
        if let Some(key) = self.by_rule[rule].get(id) {
            return *key;
        }
        let key = VariableKey {
            rule,
            ordinal: self.by_rule[rule].len(),
        };
        self.by_rule[rule].insert(id.clone(), key);
        key
    }
}

#[derive(Default)]
struct SortGraph {
    candidates: BTreeSet<SemanticSortRef>,
    parents: BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
    ancestors: BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
    compatible: BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
    /// Every cell below each group cell (KF-016).
    descendants: BTreeMap<SemanticId, BTreeSet<SemanticId>>,
    /// The root of each `overload` family member's chain of targets (clause 7c).
    overload_roots: BTreeMap<StableItemId, StableItemId>,
    /// Constructors whose applications are free terms: no function, hook,
    /// alias, desugar or bracket production, and no anywhere rule's head.
    /// Only these decide a ground `==K` guard (clause 4).
    free_constructors: BTreeSet<StableItemId>,
}

impl SortGraph {
    fn from_modules(modules: &[SemanticModule]) -> Self {
        let mut graph = Self::default();
        graph
            .candidates
            .extend(BuiltinSort::ALL.into_iter().map(SemanticSortRef::Builtin));
        for module in modules {
            graph.candidates.extend(
                module
                    .sorts()
                    .iter()
                    .map(|sort| SemanticSortRef::Declared(sort.id().clone())),
            );
            for production in module.productions() {
                if production.id().item_kind() == ItemKind::Constructor
                    && !production.attributes().iter().any(|attribute| {
                        matches!(
                            attribute,
                            ProductionAttribute::Function { .. }
                                | ProductionAttribute::Hook { .. }
                                | ProductionAttribute::RawHook { .. }
                                | ProductionAttribute::Memo { .. }
                                | ProductionAttribute::FreshGenerator { .. }
                                | ProductionAttribute::Alias { .. }
                                | ProductionAttribute::Desugar { .. }
                                | ProductionAttribute::Bracket { .. }
                        )
                    })
                {
                    graph.free_constructors.insert(production.id().clone());
                }
                if let Some(target) =
                    production
                        .attributes()
                        .iter()
                        .find_map(|attribute| match attribute {
                            ProductionAttribute::Overload { target, .. } => Some(target),
                            _ => None,
                        })
                {
                    graph
                        .overload_roots
                        .insert(production.id().clone(), target.clone());
                }
            }
            for edge in module.subsorts() {
                graph.candidates.insert(edge.subsort().clone());
                graph.candidates.insert(edge.supersort().clone());
                graph
                    .parents
                    .entry(edge.subsort().clone())
                    .or_default()
                    .insert(edge.supersort().clone());
            }
        }
        for module in modules {
            let mut groups = Vec::new();
            if let Some(configuration) = module.configuration() {
                group_cells(configuration.cells(), &mut groups);
            }
            for (cell, sort, descendants) in groups {
                graph.descendants.insert(cell, descendants);
                graph.candidates.insert(sort);
            }
        }
        graph.complete_k_item();
        // An anywhere rule rewrites its head wherever it occurs, so that
        // head's applications are not free terms; a head the check cannot
        // name leaves no constructor free.
        for rule in modules.iter().flat_map(SemanticModule::rules) {
            if rule.anywhere().is_none() {
                continue;
            }
            match rule.relational_body() {
                RuleBodyRef::Term(body) => match head_application(body.from(), true) {
                    Some(ApplicationRef::Declared(head)) => {
                        graph.free_constructors.remove(head);
                    }
                    Some(ApplicationRef::Builtin(_) | ApplicationRef::Generated(_)) => {}
                    None => graph.free_constructors.clear(),
                },
                _ => graph.free_constructors.clear(),
            }
        }
        // A strict list's value list joins its families as K's overload
        // axioms make it (KF-020).
        graph
            .overload_roots
            .extend(crate::semantic::value_list_overloads(modules));
        graph.build_closure();
        graph.resolve_overload_roots();
        graph
    }

    /// Makes every candidate sort but `K` a subsort of `KItem`, as in the
    /// emitted K: each declared and builtin sort and every generated
    /// group-cell sort (KF-016), whether or not a subsort sentence says so.
    fn complete_k_item(&mut self) {
        let k_item = self
            .candidates
            .iter()
            .find(|sort| {
                matches!(sort, SemanticSortRef::Declared(id)
                    if id.item_name() == "KItem" && id.package().k_namespace() == "KRS-FRAMEWORK")
            })
            .cloned();
        let Some(k_item) = k_item else {
            return;
        };
        for sort in &self.candidates {
            if *sort != k_item
                && !matches!(
                    sort,
                    SemanticSortRef::Builtin(BuiltinSort::KSequence)
                        | SemanticSortRef::Parameter(_)
                )
            {
                self.parents
                    .entry(sort.clone())
                    .or_default()
                    .insert(k_item.clone());
            }
        }
    }

    /// Replaces each member's authored target by the root of its chain.
    /// Semantic lowering has rejected cycles; a cycle stops at the first
    /// repeated production all the same.
    fn resolve_overload_roots(&mut self) {
        let targets = self.overload_roots.clone();
        for root in self.overload_roots.values_mut() {
            let mut visited = BTreeSet::new();
            while visited.insert(root.clone()) {
                let Some(next) = targets.get(root) else {
                    break;
                };
                root.clone_from(next);
            }
        }
    }

    /// Whether two application heads are one head for unification: the same
    /// symbol, or members of one `overload` family (clause 7c), whose
    /// argument sorts the unifier then checks argument by argument.
    fn same_head(&self, left: &SemanticApplicationRef, right: &SemanticApplicationRef) -> bool {
        left == right
            || matches!(
                (left, right),
                (ApplicationRef::Declared(left), ApplicationRef::Declared(right))
                    if self.overload_root(left) == self.overload_root(right)
            )
    }

    fn free_constructor(&self, production: &StableItemId) -> bool {
        self.free_constructors.contains(production)
    }

    fn overload_root<'id>(&'id self, production: &'id StableItemId) -> &'id StableItemId {
        self.overload_roots.get(production).unwrap_or(production)
    }

    fn build_closure(&mut self) {
        for candidate in &self.candidates {
            let mut pending = vec![candidate.clone()];
            let mut ancestors = BTreeSet::new();
            while let Some(sort) = pending.pop() {
                if !ancestors.insert(sort.clone()) {
                    continue;
                }
                if let Some(parents) = self.parents.get(&sort) {
                    pending.extend(parents.iter().cloned());
                }
            }
            for left in &ancestors {
                self.compatible
                    .entry(left.clone())
                    .or_default()
                    .extend(ancestors.iter().cloned());
            }
            self.ancestors.insert(candidate.clone(), ancestors);
        }
    }

    fn is_subsort(&self, candidate: &SemanticSortRef, expected: &SemanticSortRef) -> bool {
        candidate == expected
            || self
                .ancestors
                .get(candidate)
                .is_some_and(|ancestors| ancestors.contains(expected))
    }

    fn compatible(&self, left: &SemanticSortRef, right: &SemanticSortRef) -> bool {
        self.compatible
            .get(left)
            .is_some_and(|compatible| compatible.contains(right))
    }

    /// Whether one of two distinct cells is a group cell containing the
    /// other: their clauses then constrain the same leaves (KF-016).
    fn nested(&self, left: &SemanticId, right: &SemanticId) -> bool {
        self.descendants
            .get(left)
            .is_some_and(|below| below.contains(right))
            || self
                .descendants
                .get(right)
                .is_some_and(|below| below.contains(left))
    }
}

struct Unifier<'graph> {
    graph: &'graph SortGraph,
    substitutions: BTreeMap<VariableKey, Pattern>,
    requirements: BTreeMap<VariableKey, BTreeSet<SemanticSortRef>>,
}

impl<'graph> Unifier<'graph> {
    fn new(graph: &'graph SortGraph) -> Self {
        Self {
            graph,
            substitutions: BTreeMap::new(),
            requirements: BTreeMap::new(),
        }
    }

    #[expect(
        clippy::too_many_lines,
        reason = "Keeps the symmetric unification cases in one exhaustive match."
    )]
    fn unify(&mut self, left: Pattern, right: Pattern) -> bool {
        let left = self.resolve(left);
        let right = self.resolve(right);
        // A variable is bound to the other side whatever its theory; any
        // other side built by a collection constructor is unified modulo
        // that collection's axioms (clause 7e).
        if !matches!(left, Pattern::Variable { .. })
            && !matches!(right, Pattern::Variable { .. })
            && let Some(theory) = Collection::of(&left).or_else(|| Collection::of(&right))
        {
            return self.unify_collection(theory, &left, false, &right, false);
        }
        match (left, right) {
            (
                Pattern::Variable {
                    key: left,
                    sort: left_sort,
                },
                Pattern::Variable {
                    key: right,
                    sort: right_sort,
                },
            ) => self.unify_variables(left, left_sort, right, right_sort),
            (Pattern::Variable { key, sort }, term) | (term, Pattern::Variable { key, sort }) => {
                self.bind(key, sort, term)
            }
            (
                Pattern::Application {
                    sort: left_sort,
                    application: left_application,
                    arguments: left_arguments,
                    instance: left_instance,
                },
                Pattern::Application {
                    sort: right_sort,
                    application: right_application,
                    arguments: right_arguments,
                    instance: right_instance,
                },
            ) => {
                left_instance == right_instance
                    && self.graph.same_head(&left_application, &right_application)
                    && self.graph.compatible(&left_sort, &right_sort)
                    && self.unify_arguments(left_arguments, right_arguments)
            }
            (
                Pattern::Token {
                    sort: left_sort,
                    value: left_value,
                },
                Pattern::Token {
                    sort: right_sort,
                    value: right_value,
                },
            ) => left_value == right_value && self.graph.compatible(&left_sort, &right_sort),
            (
                Pattern::Map {
                    sort: left_sort,
                    operation: left_operation,
                    arguments: left_arguments,
                },
                Pattern::Map {
                    sort: right_sort,
                    operation: right_operation,
                    arguments: right_arguments,
                },
            ) => {
                if !self.graph.compatible(&left_sort, &right_sort) {
                    return false;
                }
                match (left_operation, right_operation) {
                    // Framed item requirements may be satisfied by distinct
                    // entries, so key/value terms cannot prove disjointness.
                    (MapOperation::Item, MapOperation::Item) => true,
                    (left, right) if left == right => {
                        self.unify_arguments(left_arguments, right_arguments)
                    }
                    _ => false,
                }
            }
            // Both sides are List or Set functions (constructor-built sides
            // were routed above): a function's value is not determined by the
            // syntax of its operands, so equal operands are not necessary and
            // different operands do not separate (conservative).
            (
                Pattern::List {
                    sort: left_sort, ..
                },
                Pattern::List {
                    sort: right_sort, ..
                },
            )
            | (
                Pattern::Set {
                    sort: left_sort, ..
                },
                Pattern::Set {
                    sort: right_sort, ..
                },
            ) => self.graph.compatible(&left_sort, &right_sort),
            (
                Pattern::Cell {
                    sort: left_sort,
                    cell: left_cell,
                    children: left_children,
                },
                Pattern::Cell {
                    sort: right_sort,
                    cell: right_cell,
                    children: right_children,
                },
            ) => {
                left_cell == right_cell
                    && self.graph.compatible(&left_sort, &right_sort)
                    && self.unify_arguments(left_children, right_children)
            }
            _ => false,
        }
    }

    fn unify_arguments(&mut self, left: Vec<Pattern>, right: Vec<Pattern>) -> bool {
        left.len() == right.len()
            && left
                .into_iter()
                .zip(right)
                .all(|(left, right)| self.unify(left, right))
    }

    fn unify_variables(
        &mut self,
        left: VariableKey,
        left_sort: SemanticSortRef,
        right: VariableKey,
        right_sort: SemanticSortRef,
    ) -> bool {
        self.add_requirement(left, left_sort);
        self.add_requirement(right, right_sort);
        if left == right {
            return true;
        }
        let (root, merged) = if left < right {
            (left, right)
        } else {
            (right, left)
        };
        let merged_requirements = self.requirements.remove(&merged).unwrap_or_default();
        let root_requirements = self.requirements.entry(root).or_default();
        root_requirements.extend(merged_requirements);
        if !requirements_compatible(self.graph, root_requirements) {
            return false;
        }
        let root_sort = root_requirements
            .iter()
            .next()
            .cloned()
            .expect("both variables contributed a sort");
        self.substitutions.insert(
            merged,
            Pattern::Variable {
                key: root,
                sort: root_sort,
            },
        );
        true
    }

    fn bind(&mut self, key: VariableKey, sort: SemanticSortRef, term: Pattern) -> bool {
        self.add_requirement(key, sort);
        if self.occurs(key, &term, &mut BTreeSet::new()) {
            // Modulo unit, `X = X Y` holds with `Y` empty, so a variable
            // occurring in a collection proves nothing; it stays unbound.
            return Collection::of(&term).is_some();
        }
        let requirements = self.requirements.get(&key).cloned().unwrap_or_default();
        if !requirements
            .iter()
            .all(|required| self.graph.is_subsort(term.sort(), required))
        {
            return false;
        }
        self.substitutions.insert(key, term);
        true
    }

    fn add_requirement(&mut self, key: VariableKey, sort: SemanticSortRef) {
        self.requirements.entry(key).or_default().insert(sort);
    }

    fn resolve(&self, mut pattern: Pattern) -> Pattern {
        let mut visited = BTreeSet::new();
        while let Pattern::Variable { key, .. } = &pattern {
            if !visited.insert(*key) {
                break;
            }
            let Some(replacement) = self.substitutions.get(key) else {
                break;
            };
            pattern = replacement.clone();
        }
        pattern
    }

    fn occurs(
        &self,
        needle: VariableKey,
        pattern: &Pattern,
        visited: &mut BTreeSet<VariableKey>,
    ) -> bool {
        match pattern {
            Pattern::Variable { key, .. } => {
                if *key == needle {
                    return true;
                }
                if !visited.insert(*key) {
                    return false;
                }
                self.substitutions
                    .get(key)
                    .is_some_and(|term| self.occurs(needle, term, visited))
            }
            Pattern::Application { arguments, .. }
            | Pattern::KSequence {
                items: arguments, ..
            }
            | Pattern::Map { arguments, .. }
            | Pattern::List { arguments, .. }
            | Pattern::Set { arguments, .. } => arguments
                .iter()
                .any(|term| self.occurs(needle, term, visited)),
            Pattern::Cell { children, .. } => children
                .iter()
                .any(|term| self.occurs(needle, term, visited)),
            Pattern::Matches { subject, .. } => self.occurs(needle, subject, visited),
            Pattern::Opaque { .. } | Pattern::Token { .. } => false,
        }
    }
}

/// A collection theory the unifier reasons in modulo its axioms (F2
/// amendment, clause 7e).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Collection {
    /// K sequences: `~>` is associative with unit `.K`.
    Sequence,
    /// `_List_` is associative with unit `.List`.
    List,
    /// `_Set_` is associative and commutative with unit `.Set`, on disjoint
    /// operands.
    Set,
}

impl Collection {
    /// The theory a pattern built by a collection constructor belongs to.
    const fn of(pattern: &Pattern) -> Option<Self> {
        match pattern {
            Pattern::KSequence { .. } => Some(Self::Sequence),
            Pattern::List {
                operation: ListOperation::Empty | ListOperation::Item | ListOperation::Concat,
                ..
            } => Some(Self::List),
            Pattern::Set {
                operation: SetOperation::Empty | SetOperation::Item | SetOperation::Concat,
                ..
            } => Some(Self::Set),
            _ => None,
        }
    }
}

/// One piece of a collection pattern flattened modulo associativity and
/// unit.
#[derive(Clone, Debug)]
enum Segment {
    /// One element: a List or Set item's element, or one K-sequence item.
    Element(Pattern),
    /// A sub-collection of unknown size: a collection variable, a term the
    /// unifier does not model, or a clause's omitted frame (`None`).
    Open(Option<Pattern>),
}

impl Segment {
    const fn is_element(&self) -> bool {
        matches!(self, Self::Element(_))
    }

    const fn element(&self) -> Option<&Pattern> {
        match self {
            Self::Element(element) => Some(element),
            Self::Open(_) => None,
        }
    }
}

/// A saved substitution and its sort requirements.
type Snapshot = (
    BTreeMap<VariableKey, Pattern>,
    BTreeMap<VariableKey, BTreeSet<SemanticSortRef>>,
);

/// Whether a K-sequence item splices into the sequence rather than being
/// one item: a `K`-sorted term other than a constructor application, token
/// or cell, such as a `K` variable, which may stand for any number of items.
fn splices(item: &Pattern) -> bool {
    *item.sort() == SemanticSortRef::Builtin(BuiltinSort::KSequence)
        && !matches!(
            item,
            Pattern::Application {
                application: ApplicationRef::Declared(id),
                ..
            } if id.item_kind() == krs_ir::ItemKind::Constructor
        )
        && !matches!(item, Pattern::Token { .. } | Pattern::Cell { .. })
}

fn requirements_compatible(graph: &SortGraph, requirements: &BTreeSet<SemanticSortRef>) -> bool {
    graph.candidates.iter().any(|candidate| {
        requirements
            .iter()
            .all(|required| graph.is_subsort(candidate, required))
    })
}

fn pattern(term: &SemanticTerm, rule: usize, catalog: &mut VariableCatalog) -> Pattern {
    match term.kind() {
        SemanticTermKind::Variable { variable } => Pattern::Variable {
            key: catalog.key(rule, variable),
            sort: term.sort().clone(),
        },
        SemanticTermKind::Application {
            application,
            arguments,
            instance,
            ..
        } => Pattern::Application {
            sort: term.sort().clone(),
            instance: instance.clone(),
            application: application.clone(),
            arguments: arguments
                .iter()
                .map(|argument| pattern(argument, rule, catalog))
                .collect(),
        },
        SemanticTermKind::Token { value } => Pattern::Token {
            sort: term.sort().clone(),
            value: value.clone(),
        },
        SemanticTermKind::KSequence { items, .. } => Pattern::KSequence {
            sort: term.sort().clone(),
            items: items
                .iter()
                .map(|item| pattern(item, rule, catalog))
                .collect(),
        },
        SemanticTermKind::Map(operands) => Pattern::Map {
            sort: term.sort().clone(),
            operation: operands.operation(),
            arguments: operands
                .operands()
                .map(|operand| pattern(operand, rule, catalog))
                .collect(),
        },
        SemanticTermKind::List(operands) => Pattern::List {
            sort: term.sort().clone(),
            operation: operands.operation(),
            arguments: operands
                .operands()
                .map(|operand| pattern(operand, rule, catalog))
                .collect(),
        },
        SemanticTermKind::Set(operands) => Pattern::Set {
            sort: term.sort().clone(),
            operation: operands.operation(),
            arguments: operands
                .operands()
                .map(|operand| pattern(operand, rule, catalog))
                .collect(),
        },
        SemanticTermKind::Cell { cell, children } => Pattern::Cell {
            sort: term.sort().clone(),
            cell: cell.clone(),
            children: children
                .iter()
                .map(|child| pattern(child, rule, catalog))
                .collect(),
        },
        // A single-body clause (KF-011) unifies through its left image.
        SemanticTermKind::Rewrite { from, .. } => pattern(from, rule, catalog),
        SemanticTermKind::Let { .. } => Pattern::Opaque {
            sort: term.sort().clone(),
        },
        SemanticTermKind::Matches {
            subject,
            pattern: matched,
            ..
        } => Pattern::Matches {
            sort: term.sort().clone(),
            subject: Box::new(pattern(subject, rule, catalog)),
            shape: matches_shape(matched, &mut BTreeMap::new()),
        },
        // `alias @ pattern` unifies as its pattern, with the alias bound to
        // the pattern (clause 7b, KF-029).
        SemanticTermKind::As {
            alias,
            pattern: aliased,
        } => {
            let key = catalog.key(rule, alias);
            let aliased = pattern(aliased, rule, catalog);
            catalog
                .aliases
                .push((key, term.sort().clone(), aliased.clone()));
            aliased
        }
        // `A | B` stands for the alternative this unification chose (clause
        // 7b, KF-030).
        SemanticTermKind::Or { alternatives } => {
            let index = catalog.choices[rule]
                .get(&node_address(term))
                .copied()
                .unwrap_or(0);
            let alternative = alternatives
                .iter()
                .nth(index)
                .expect("a choice names one of the node's alternatives");
            pattern(alternative, rule, catalog)
        }
    }
}

/// Every nested (group) cell below `cells`: its identity, its generated cell
/// sort, and every cell below it (KF-016).
fn group_cells(
    cells: &[krs_ir::FixedCell<SemanticSortRef, SemanticId>],
    output: &mut Vec<(SemanticId, SemanticSortRef, BTreeSet<SemanticId>)>,
) {
    fn below(
        cells: &[krs_ir::FixedCell<SemanticSortRef, SemanticId>],
        output: &mut BTreeSet<SemanticId>,
    ) {
        for cell in cells {
            output.insert(cell.id().clone());
            if let krs_ir::FixedCellContent::Children { children } = cell.content() {
                below(children, output);
            }
        }
    }
    for cell in cells {
        if let krs_ir::FixedCellContent::Children { children } = cell.content() {
            if let Some(declaration) = cell.declaration() {
                let mut descendants = BTreeSet::new();
                below(children, &mut descendants);
                output.push((
                    cell.id().clone(),
                    SemanticSortRef::Cell(declaration.clone()),
                    descendants,
                ));
            }
            group_cells(children, output);
        }
    }
}

/// What a clause's frame omits from its cell content, which decides the
/// theory the omitted part belongs to.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Frame {
    /// Nothing: the pattern is the whole content.
    Exact,
    /// A K-sequence tail after the pattern's items.
    Sequence,
    /// A List tail after the pattern's items.
    List,
    /// A map remainder beside the pattern's entries.
    Map,
}

impl Frame {
    const fn of(frame: &krs_ir::CellContentFrame) -> Self {
        match frame {
            krs_ir::CellContentFrame::Exact => Self::Exact,
            krs_ir::CellContentFrame::KSequenceTail { .. } => Self::Sequence,
            krs_ir::CellContentFrame::ListRemainder { .. } => Self::List,
            krs_ir::CellContentFrame::MapRemainder { .. } => Self::Map,
        }
    }
}

/// One clause a transition places on a cell, as the overlap check sees it.
#[derive(Clone)]
struct ClauseView<'a> {
    cell: &'a SemanticId,
    before: &'a SemanticTerm,
    /// The pattern is a computation-cell head completed with an implicit `KSequence`.
    completed_head: bool,
    /// What the clause's frame omits from the cell content.
    frame: Frame,
    /// The cell is in the footprint only through a function context
    /// (clause 5, KF-025): its content is an unconstrained variable, and
    /// `before` is the context's pattern, used only for its sort.
    unconstrained: bool,
}

/// The cells each function's equations read through their function contexts,
/// and the functions they call (clause 5, R5, KF-025).
#[derive(Default)]
struct FunctionContexts<'a> {
    functions: BTreeMap<&'a StableItemId, FunctionReads<'a>>,
}

/// One function's context cells and callees, over all its equations.
#[derive(Default)]
struct FunctionReads<'a> {
    cells: Vec<(&'a SemanticId, &'a SemanticTerm)>,
    callees: BTreeSet<&'a StableItemId>,
}

impl<'a> FunctionContexts<'a> {
    fn from_rules(rules: impl IntoIterator<Item = &'a SemanticRule>) -> Self {
        let mut functions = BTreeMap::<_, FunctionReads<'a>>::new();
        for rule in rules {
            if rule.kind() != krs_ir::SentenceKind::Equation {
                continue;
            }
            let RuleBodyRef::Term(body) = rule.relational_body() else {
                continue;
            };
            let SemanticTermKind::Application {
                application: ApplicationRef::Declared(function),
                ..
            } = body.from().kind()
            else {
                continue;
            };
            let reads = functions.entry(function).or_default();
            if let Some(context) = rule.function_context() {
                for cell in context.cells().cells() {
                    reads.cells.push((cell.cell(), cell.pattern()));
                }
            }
            declared_applications(body.to(), &mut reads.callees);
            for term in rule.requires().into_iter().flat_map(IrCondition::terms) {
                declared_applications(term, &mut reads.callees);
            }
        }
        Self { functions }
    }

    /// The cells read by the function contexts of every equation reachable
    /// from `terms`, each with one context pattern: the closure over the
    /// functions applied in `terms`, then in those functions' equations'
    /// requires and right-hand sides.
    fn reachable_cells(
        &self,
        terms: impl IntoIterator<Item = &'a SemanticTerm>,
    ) -> BTreeMap<&'a SemanticId, &'a SemanticTerm> {
        let mut pending = BTreeSet::new();
        for term in terms {
            declared_applications(term, &mut pending);
        }
        let mut visited = BTreeSet::new();
        let mut cells = BTreeMap::new();
        while let Some(function) = pending.pop_first() {
            if !visited.insert(function) {
                continue;
            }
            let Some(reads) = self.functions.get(function) else {
                continue;
            };
            for (cell, pattern) in &reads.cells {
                cells.entry(*cell).or_insert(*pattern);
            }
            pending.extend(
                reads
                    .callees
                    .iter()
                    .filter(|callee| !visited.contains(*callee)),
            );
        }
        cells
    }
}

/// Every declared production applied in `term`.
fn declared_applications<'a>(term: &'a SemanticTerm, output: &mut BTreeSet<&'a StableItemId>) {
    if let SemanticTermKind::Application {
        application: ApplicationRef::Declared(production),
        ..
    } = term.kind()
    {
        output.insert(production);
    }
    for child in subterms(term) {
        declared_applications(child, output);
    }
}

/// One transition in the scope of the overlap check (F2 amendment, clause 1).
struct TransitionView<'a> {
    rule: &'a SemanticRule,
    priority: u32,
    group: Option<(&'a krs_ir::PackageId, &'a str)>,
    configuration: &'a SemanticId,
    clauses: Vec<ClauseView<'a>>,
    requires: Option<&'a SemanticTerm>,
    /// The application at the head of the computation cell, when there is one.
    head: Option<&'a SemanticApplicationRef>,
}

impl TransitionView<'_> {
    fn id(&self) -> &StableItemId {
        self.rule.id()
    }
}

/// The unique fixed configuration and its computation cell, which term rules are completed to.
fn computation_cell(modules: &[SemanticModule]) -> Option<(&SemanticId, &SemanticId)> {
    let mut configurations = modules.iter().filter_map(SemanticModule::configuration);
    let configuration = configurations.next()?;
    if configurations.next().is_some() {
        return None;
    }
    let mut cells = configuration.cells().iter().filter(|cell| {
        matches!(
            cell.content(),
            krs_ir::FixedCellContent::Term {
                sort: SemanticSortRef::Builtin(BuiltinSort::KSequence),
                ..
            }
        )
    });
    let cell = cells.next()?;
    if cells.next().is_some() {
        return None;
    }
    Some((configuration.id(), cell.id()))
}

fn head_application(term: &SemanticTerm, completed: bool) -> Option<&SemanticApplicationRef> {
    let head = if completed {
        term
    } else if let SemanticTermKind::KSequence { items, .. } = term.kind() {
        items.first()?
    } else {
        return None;
    };
    match head.kind() {
        SemanticTermKind::Application { application, .. } => Some(application),
        // A local rewrite of the head (KF-011) matches its left side.
        SemanticTermKind::Rewrite { from, .. } => head_application(from, true),
        _ => None,
    }
}

/// Every transition the check covers: configuration rules, readable head rules,
/// and term rules completed to the computation-cell head. Equations,
/// simplifications, aliases, claims, anywhere rules, and heat and cool rules
/// are outside its scope.
fn transitions(modules: &[SemanticModule]) -> Vec<TransitionView<'_>> {
    let computation = computation_cell(modules);
    let contexts = FunctionContexts::from_rules(modules.iter().flat_map(SemanticModule::rules));
    let mut views = Vec::new();
    for rule in modules.iter().flat_map(SemanticModule::rules) {
        if rule.kind() != krs_ir::SentenceKind::Transition
            || rule.anywhere().is_some()
            || rule.evaluation().is_some()
        {
            continue;
        }
        let (configuration, variants) = match rule.relational_body() {
            RuleBodyRef::Configuration { body, .. } => {
                (body.configuration(), clause_variants(body.clauses()))
            }
            RuleBodyRef::Term(body) => {
                let Some((configuration, cell)) = computation else {
                    continue;
                };
                (
                    configuration,
                    vec![vec![ClauseView {
                        cell,
                        before: body.from(),
                        completed_head: true,
                        frame: Frame::Sequence,
                        unconstrained: false,
                    }]],
                )
            }
            // A predicate rewrite is a simplification, never a transition.
            RuleBodyRef::Predicate(_) => continue,
        };
        for mut clauses in variants {
            let read = contexts.reachable_cells(rule_results(rule));
            add_context_clauses(&mut clauses, read);
            let head = computation.and_then(|(_, cell)| {
                clauses
                    .iter()
                    .find(|clause| clause.cell == cell && !clause.unconstrained)
                    .and_then(|clause| head_application(clause.before, clause.completed_head))
            });
            views.push(TransitionView {
                rule,
                priority: rule
                    .priority()
                    .map_or(DEFAULT_PRIORITY, krs_ir_levels::SemanticRulePriority::value),
                group: rule
                    .nondet_group()
                    .map(|group| (rule.id().package(), group.name())),
                configuration,
                clauses,
                // A matching-logic condition is a claim's or a simplification's
                // (KF-039), and neither is an overlap view.
                requires: rule
                    .requires()
                    .and_then(IrCondition::as_bool)
                    .map(krs_ir_levels::SemanticRuleCondition::term),
                head,
            });
        }
    }
    views.sort_by(|left, right| left.id().cmp(right.id()));
    views
}

/// The clause views of a configuration rule, one list per choice of one
/// matched instance of each collection it names (X10.6, KF-023): two rules
/// overlap only if some pair of their instance patterns unifies, since rules
/// on different instances are K's intended concurrency. A present optional
/// cell is a clause over its content; an absent or created one constrains no
/// content.
fn clause_variants(
    clauses: &[krs_ir::ConfigurationClause<SemanticId, SemanticTerm>],
) -> Vec<Vec<ClauseView<'_>>> {
    fn view<'a>(
        cell: &'a SemanticId,
        before: &'a SemanticTerm,
        frame: &krs_ir::CellContentFrame,
    ) -> ClauseView<'a> {
        ClauseView {
            cell,
            before,
            completed_head: false,
            frame: Frame::of(frame),
            unconstrained: false,
        }
    }
    let mut variants = vec![Vec::new()];
    for clause in clauses {
        match clause {
            krs_ir::ConfigurationClause::Fixed(clause) => {
                for variant in &mut variants {
                    variant.push(view(clause.cell(), clause.before(), clause.frame()));
                }
            }
            krs_ir::ConfigurationClause::Optional(clause) => {
                if let krs_ir::Presence::Present { term } = clause.before() {
                    for variant in &mut variants {
                        variant.push(view(clause.cell(), term, clause.frame()));
                    }
                }
            }
            krs_ir::ConfigurationClause::Instances(clause) => {
                let choices = clause
                    .instances()
                    .filter_map(|instance| match instance {
                        krs_ir::InstanceClause::Kept { children, .. } => Some(
                            children
                                .iter()
                                .map(|child| view(child.cell(), child.before(), child.frame()))
                                .collect::<Vec<_>>(),
                        ),
                        krs_ir::InstanceClause::Removed { children, .. } => Some(
                            children
                                .iter()
                                .map(|child| view(child.cell(), child.term(), child.frame()))
                                .collect(),
                        ),
                        krs_ir::InstanceClause::Created { .. } => None,
                    })
                    .collect::<Vec<_>>();
                if choices.is_empty() {
                    continue;
                }
                variants = variants
                    .into_iter()
                    .flat_map(|variant| {
                        choices.iter().map(move |choice| {
                            let mut variant = variant.clone();
                            variant.extend(choice.iter().cloned());
                            variant
                        })
                    })
                    .collect();
            }
        }
    }
    variants
}

/// The terms a rule's footprint reaches functions through (clause 5): its
/// result and its requires condition.
fn rule_results(rule: &SemanticRule) -> Vec<&SemanticTerm> {
    let mut terms = match rule.relational_body() {
        RuleBodyRef::Term(body) => vec![body.to()],
        RuleBodyRef::Configuration { body, .. } => body
            .parts()
            .into_iter()
            .filter_map(|part| match part {
                // A single-body clause's right sides sit inside `before`.
                krs_ir::ClausePart::Matched {
                    before,
                    after: krs_ir::PartPost::Local,
                    ..
                } => Some(before),
                part => part.post_term(),
            })
            .collect(),
        RuleBodyRef::Predicate(body) => body.rhs().terms(),
    };
    terms.extend(rule.requires().into_iter().flat_map(IrCondition::terms));
    terms
}

/// Adds a clause for each cell `read` through a function context that the
/// rule does not already name: the cell joins its footprint as an
/// unconstrained variable (clause 5, R5).
fn add_context_clauses<'a>(
    clauses: &mut Vec<ClauseView<'a>>,
    read: BTreeMap<&'a SemanticId, &'a SemanticTerm>,
) {
    for (cell, pattern) in read {
        if clauses.iter().any(|clause| clause.cell == cell) {
            continue;
        }
        clauses.push(ClauseView {
            cell,
            before: pattern,
            completed_head: false,
            // The variable stands for the whole content.
            frame: Frame::Exact,
            unconstrained: true,
        });
    }
}

/// K's default rule priority.
const DEFAULT_PRIORITY: u32 = 50;

fn clause_pattern(clause: &ClauseView<'_>, rule: usize, catalog: &mut VariableCatalog) -> Pattern {
    if clause.unconstrained {
        return Pattern::Variable {
            key: catalog.unconstrained(rule),
            sort: clause.before.sort().clone(),
        };
    }
    let before = pattern(clause.before, rule, catalog);
    if clause.completed_head {
        Pattern::KSequence {
            sort: SemanticSortRef::Builtin(BuiltinSort::KSequence),
            items: vec![before],
        }
    } else {
        before
    }
}

impl Unifier<'_> {
    /// Unifies two cell contents. A frame adds an open segment of its
    /// theory after the pattern's items (a K-sequence or List tail) or a
    /// remainder beside its entries (a Map), so a framed side is unified
    /// modulo that theory's axioms.
    fn unify_clause(
        &mut self,
        left: Pattern,
        left_frame: Frame,
        right: Pattern,
        right_frame: Frame,
    ) -> bool {
        let theory = match (left_frame, right_frame) {
            (Frame::Exact, Frame::Exact) => return self.unify(left, right),
            (Frame::Map, _) | (_, Frame::Map) => {
                return self.unify_map_clause(left, left_frame, right, right_frame);
            }
            (Frame::Sequence, _) | (_, Frame::Sequence) => Collection::Sequence,
            (Frame::List, _) | (_, Frame::List) => Collection::List,
        };
        self.unify_collection(
            theory,
            &left,
            left_frame != Frame::Exact,
            &right,
            right_frame != Frame::Exact,
        )
    }

    /// Unifies two Map cell contents of which at least one has a remainder.
    /// A remainder may hold any entries, so the one refutation kept is an
    /// exact empty map against framed entries, which need at least one
    /// entry; everything else may overlap.
    fn unify_map_clause(
        &mut self,
        left: Pattern,
        left_frame: Frame,
        right: Pattern,
        right_frame: Frame,
    ) -> bool {
        let left = self.resolve(left);
        let right = self.resolve(right);
        let entries = |pattern: &Pattern| {
            matches!(
                pattern,
                Pattern::Map {
                    operation: MapOperation::Item,
                    ..
                }
            )
        };
        let empty = |pattern: &Pattern| {
            matches!(
                pattern,
                Pattern::Map {
                    operation: MapOperation::Empty,
                    ..
                }
            )
        };
        let refuted = |framed: &Pattern, frame: Frame, exact: &Pattern, other: Frame| {
            frame != Frame::Exact && other == Frame::Exact && entries(framed) && empty(exact)
        };
        self.graph.compatible(left.sort(), right.sort())
            && !refuted(&left, left_frame, &right, right_frame)
            && !refuted(&right, right_frame, &left, left_frame)
    }

    /// Unifies two patterns of one collection theory modulo its axioms:
    /// List and K sequences are associative with a unit, and Set is
    /// associative and commutative with a unit, on disjoint operands. The
    /// answer over-approximates: `false` only when no instance matches both
    /// sides, and every committed binding holds in every common instance
    /// (F2 amendment, clause 7e).
    fn unify_collection(
        &mut self,
        theory: Collection,
        left: &Pattern,
        left_framed: bool,
        right: &Pattern,
        right_framed: bool,
    ) -> bool {
        // A K-sequence item injects into `KItem`, so sequence sides are
        // compared item by item; List and Set sides must share a sort.
        if theory != Collection::Sequence && !self.graph.compatible(left.sort(), right.sort()) {
            return false;
        }
        let mut left_segments = Vec::new();
        self.segments(theory, left.clone(), &mut left_segments);
        if left_framed {
            left_segments.push(Segment::Open(None));
        }
        let mut right_segments = Vec::new();
        self.segments(theory, right.clone(), &mut right_segments);
        if right_framed {
            right_segments.push(Segment::Open(None));
        }
        // A side that is exactly one collection variable denotes the whole
        // other side; if that binding fails (a sort the variable cannot
        // take), the general procedure below decides instead.
        for (segments, other, other_framed) in [
            (&left_segments, right, right_framed),
            (&right_segments, left, left_framed),
        ] {
            if !other_framed
                && let [Segment::Open(Some(variable @ Pattern::Variable { .. }))] =
                    segments.as_slice()
            {
                let snapshot = self.snapshot();
                if self.unify(variable.clone(), other.clone()) {
                    return true;
                }
                self.restore(snapshot);
            }
        }
        match theory {
            Collection::Set => self.unify_set_segments(&left_segments, &right_segments),
            Collection::Sequence | Collection::List => {
                self.unify_sequence_segments(&left_segments, &right_segments)
            }
        }
    }

    /// Flattens a collection pattern modulo associativity and unit: nested
    /// concatenations are spliced, units dropped, items become elements, and
    /// any other term of the collection's sort becomes an open segment.
    fn segments(&self, theory: Collection, pattern: Pattern, output: &mut Vec<Segment>) {
        match (theory, self.resolve(pattern)) {
            (Collection::Sequence, Pattern::KSequence { items, .. }) => {
                for item in items {
                    self.segments(theory, item, output);
                }
            }
            (Collection::Sequence, item) => {
                output.push(if splices(&item) {
                    Segment::Open(Some(item))
                } else {
                    Segment::Element(item)
                });
            }
            (
                Collection::List,
                Pattern::List {
                    operation: ListOperation::Empty,
                    ..
                },
            )
            | (
                Collection::Set,
                Pattern::Set {
                    operation: SetOperation::Empty,
                    ..
                },
            ) => {}
            (
                Collection::List,
                Pattern::List {
                    operation: ListOperation::Item,
                    arguments,
                    ..
                },
            )
            | (
                Collection::Set,
                Pattern::Set {
                    operation: SetOperation::Item,
                    arguments,
                    ..
                },
            ) => output.push(
                arguments
                    .into_iter()
                    .next()
                    .map_or(Segment::Open(None), Segment::Element),
            ),
            (
                Collection::List,
                Pattern::List {
                    operation: ListOperation::Concat,
                    arguments,
                    ..
                },
            )
            | (
                Collection::Set,
                Pattern::Set {
                    operation: SetOperation::Concat,
                    arguments,
                    ..
                },
            ) => {
                for argument in arguments {
                    self.segments(theory, argument, output);
                }
            }
            (_, other) => output.push(Segment::Open(Some(other))),
        }
    }

    /// Unifies two flattened sequences (List or K). Two closed sequences
    /// unify element by element. Otherwise the elements before the first
    /// open segment of both sides, and after the last, sit at the same
    /// position in every common instance, so they are unified pairwise; a
    /// closed side must have room for the other side's elements; and the
    /// middle is assumed to align (conservative).
    fn unify_sequence_segments(&mut self, left: &[Segment], right: &[Segment]) -> bool {
        let closed = |segments: &[Segment]| segments.iter().all(Segment::is_element);
        let elements = |segments: &[Segment]| {
            segments
                .iter()
                .filter(|segment| segment.is_element())
                .count()
        };
        let leading = |segments: &[Segment]| {
            segments
                .iter()
                .take_while(|segment| segment.is_element())
                .count()
        };
        let trailing = |segments: &[Segment]| {
            segments
                .iter()
                .rev()
                .take_while(|segment| segment.is_element())
                .count()
        };
        let pairs: Vec<(Pattern, Pattern)> = if closed(left) && closed(right) {
            if left.len() != right.len() {
                return false;
            }
            left.iter()
                .zip(right)
                .filter_map(|(left, right)| {
                    Some((left.element()?.clone(), right.element()?.clone()))
                })
                .collect()
        } else {
            if (closed(left) && elements(right) > left.len())
                || (closed(right) && elements(left) > right.len())
            {
                return false;
            }
            let prefix = leading(left).min(leading(right));
            let suffix = trailing(left).min(trailing(right));
            let front = (0..prefix).map(|index| (&left[index], &right[index]));
            let back = (1..=suffix)
                .map(|offset| (&left[left.len() - offset], &right[right.len() - offset]));
            front
                .chain(back)
                .filter_map(|(left, right)| {
                    Some((left.element()?.clone(), right.element()?.clone()))
                })
                .collect()
        };
        pairs
            .into_iter()
            .all(|(left, right)| self.unify(left, right))
    }

    /// Unifies two flattened sets. A set concatenation is defined only on
    /// disjoint operands, so a closed side of `n` items denotes sets of
    /// exactly `n` elements and a side with an open segment sets of at
    /// least its item count. Which element of one side matches which of
    /// the other is a choice, so elements are unified only when a single
    /// element on each side is forced to be the same one.
    fn unify_set_segments(&mut self, left: &[Segment], right: &[Segment]) -> bool {
        let elements = |segments: &[Segment]| {
            segments
                .iter()
                .filter_map(Segment::element)
                .cloned()
                .collect::<Vec<_>>()
        };
        let (left_elements, right_elements) = (elements(left), elements(right));
        let left_closed = left_elements.len() == left.len();
        let right_closed = right_elements.len() == right.len();
        if (left_closed && right_elements.len() > left_elements.len())
            || (right_closed && left_elements.len() > right_elements.len())
        {
            return false;
        }
        match (left_elements.as_slice(), right_elements.as_slice()) {
            ([left], [right]) if left_closed || right_closed => {
                self.unify(left.clone(), right.clone())
            }
            _ => true,
        }
    }

    /// The current substitution, to return to after a failed attempt that
    /// does not decide the answer.
    fn snapshot(&self) -> Snapshot {
        (self.substitutions.clone(), self.requirements.clone())
    }

    fn restore(&mut self, (substitutions, requirements): Snapshot) {
        self.substitutions = substitutions;
        self.requirements = requirements;
    }

    /// Whether two patterns are identical under the current substitution.
    #[expect(
        clippy::too_many_lines,
        reason = "One exhaustive comparison over the closed pattern sum."
    )]
    fn same(&self, left: &Pattern, right: &Pattern) -> bool {
        let left = self.resolve(left.clone());
        let right = self.resolve(right.clone());
        let all = |left: &[Pattern], right: &[Pattern]| {
            left.len() == right.len()
                && left
                    .iter()
                    .zip(right)
                    .all(|(left, right)| self.same(left, right))
        };
        match (&left, &right) {
            (Pattern::Variable { key: left, .. }, Pattern::Variable { key: right, .. }) => {
                left == right
            }
            (
                Pattern::Application {
                    application: left_application,
                    arguments: left_arguments,
                    instance: left_instance,
                    ..
                },
                Pattern::Application {
                    application: right_application,
                    arguments: right_arguments,
                    instance: right_instance,
                    ..
                },
            ) => {
                left_application == right_application
                    && left_instance == right_instance
                    && all(left_arguments, right_arguments)
            }
            (
                Pattern::Token {
                    sort: left_sort,
                    value: left_value,
                },
                Pattern::Token {
                    sort: right_sort,
                    value: right_value,
                },
            ) => left_sort == right_sort && left_value == right_value,
            (Pattern::KSequence { items: left, .. }, Pattern::KSequence { items: right, .. }) => {
                all(left, right)
            }
            (
                Pattern::Map {
                    operation: left_operation,
                    arguments: left_arguments,
                    ..
                },
                Pattern::Map {
                    operation: right_operation,
                    arguments: right_arguments,
                    ..
                },
            ) => left_operation == right_operation && all(left_arguments, right_arguments),
            (
                Pattern::List {
                    operation: left_operation,
                    arguments: left_arguments,
                    ..
                },
                Pattern::List {
                    operation: right_operation,
                    arguments: right_arguments,
                    ..
                },
            ) => left_operation == right_operation && all(left_arguments, right_arguments),
            (
                Pattern::Set {
                    operation: left_operation,
                    arguments: left_arguments,
                    ..
                },
                Pattern::Set {
                    operation: right_operation,
                    arguments: right_arguments,
                    ..
                },
            ) => left_operation == right_operation && all(left_arguments, right_arguments),
            (
                Pattern::Cell {
                    cell: left_cell,
                    children: left_children,
                    ..
                },
                Pattern::Cell {
                    cell: right_cell,
                    children: right_children,
                    ..
                },
            ) => left_cell == right_cell && all(left_children, right_children),
            (
                Pattern::Matches {
                    subject: left_subject,
                    shape: left_shape,
                    ..
                },
                Pattern::Matches {
                    subject: right_subject,
                    shape: right_shape,
                    ..
                },
            ) => left_shape == right_shape && self.same(left_subject, right_subject),
            _ => false,
        }
    }

    /// Whether some conjunct of one guard is the complement of a conjunct of
    /// the other (F2 amendment, clause 4).
    fn guards_complementary(&self, left: Option<&Pattern>, right: Option<&Pattern>) -> bool {
        let (Some(left), Some(right)) = (left, right) else {
            return false;
        };
        let left = conjuncts(left);
        let right = conjuncts(right);
        left.iter()
            .any(|left| right.iter().any(|right| self.complementary(left, right)))
    }

    /// Whether the two guards cannot both hold under the current
    /// substitution: a pair of conjuncts is complementary, or a conjunct of
    /// either guard evaluates to false (F2 amendment, clause 4).
    fn guards_separate(&self, left: Option<&Pattern>, right: Option<&Pattern>) -> bool {
        self.guards_complementary(left, right)
            || self.guard_refuted(left)
            || self.guard_refuted(right)
            || self.int_facts_conflict(left, right)
    }

    /// Whether the Int facts the conjuncts of both guards state cannot hold
    /// together: for some term, a bit required both 0 and 1, two different
    /// values, a value outside a bound or against a bit, or bounds that
    /// leave no integer (see [`IntFact`]). Each fact is implied by its
    /// conjunct, so unsatisfiable facts make the guards' conjunction
    /// unsatisfiable; an unrecognized conjunct states no fact.
    fn int_facts_conflict(&self, left: Option<&Pattern>, right: Option<&Pattern>) -> bool {
        let mut facts = Vec::<(Pattern, IntFact)>::new();
        for conjunct in left.into_iter().chain(right).flat_map(conjuncts) {
            let conjunct = self.resolve(conjunct.clone());
            match self.int_fact(&conjunct) {
                Some(Ok(fact)) => facts.push(fact),
                // A conjunct false on its own refutes the guards.
                Some(Err(())) => return true,
                None => {}
            }
        }
        let mut groups = Vec::<(Pattern, IntFacts)>::new();
        for (term, fact) in facts {
            let index = groups
                .iter()
                .position(|(existing, _)| self.same(existing, &term))
                .unwrap_or_else(|| {
                    groups.push((term, IntFacts::default()));
                    groups.len() - 1
                });
            groups[index].1.add(fact);
        }
        groups.iter().any(|(_, group)| !group.satisfiable())
    }

    /// The fact a resolved guard conjunct states about one Int term:
    /// `Some(Err(()))` when the conjunct cannot hold at all, `None` when it
    /// states no recognized fact.
    fn int_fact(&self, conjunct: &Pattern) -> Option<Result<(Pattern, IntFact), ()>> {
        let literal = relation_literal(conjunct)?;
        let [left, right] = literal.operands;
        let left_value = self.int_literal(left);
        let right_value = self.int_literal(right);
        match (literal.relation, literal.positive) {
            (BuiltinOperation::IntEqual, true) => {
                let (term, value) = match (left_value, right_value) {
                    (None, Some(value)) => (left, value),
                    (Some(value), None) => (right, value),
                    _ => return None,
                };
                Some(self.equality_fact(term, value))
            }
            (BuiltinOperation::IntLess, positive) => {
                // `left < right` when positive, `right <= left` otherwise.
                let fact = match (left_value, right_value, positive) {
                    (None, Some(bound), true) => IntFact::Below(bound),
                    (None, Some(bound), false) => IntFact::AtLeast(bound),
                    (Some(bound), None, true) => IntFact::AtLeast(bound.checked_add(1)?),
                    (Some(bound), None, false) => IntFact::Below(bound.checked_add(1)?),
                    _ => return None,
                };
                let term = if left_value.is_none() { left } else { right };
                Some(Ok((self.resolve(term.clone()), fact)))
            }
            _ => None,
        }
    }

    /// The fact of `term ==Int value`: bits of `t` for `bitRangeInt(t, o, l)`
    /// and for `t &Int m` with literal `o`, `l`, and `m`; otherwise the value
    /// of `term` itself.
    fn equality_fact(&self, term: &Pattern, value: i128) -> Result<(Pattern, IntFact), ()> {
        let term = self.resolve(term.clone());
        if let Pattern::Application {
            application: ApplicationRef::Builtin(operation),
            arguments,
            ..
        } = &term
        {
            match (operation, arguments.as_slice()) {
                (BuiltinOperation::IntBitRange, [subject, offset, length]) => {
                    if let (Some(offset), Some(length)) =
                        (self.int_literal(offset), self.int_literal(length))
                        && let Some(fact) = IntFact::bit_range(offset, length, value)
                    {
                        return fact.map(|fact| (self.resolve(subject.clone()), fact));
                    }
                }
                (BuiltinOperation::IntBitAnd, [first, second]) => {
                    let pair = match (self.int_literal(first), self.int_literal(second)) {
                        (None, Some(mask)) => Some((first, mask)),
                        (Some(mask), None) => Some((second, mask)),
                        _ => None,
                    };
                    if let Some((subject, mask)) = pair
                        && let Some(fact) = IntFact::masked(mask, value)
                    {
                        return fact.map(|fact| (self.resolve(subject.clone()), fact));
                    }
                }
                _ => {}
            }
        }
        Ok((term, IntFact::Equal(value)))
    }

    /// Whether some conjunct of a guard, after the unifier's substitution,
    /// evaluates to false, such as `x >=Int 10` once the other rule's
    /// pattern binds `x` to `0`.
    fn guard_refuted(&self, guard: Option<&Pattern>) -> bool {
        guard.is_some_and(|guard| {
            conjuncts(guard)
                .into_iter()
                .any(|conjunct| self.ground_truth(conjunct) == Some(false))
        })
    }

    /// The value of a guard conjunct under the current substitution: a Bool
    /// literal, a relation literal ([`GuardMeaning::Relation`]) whose
    /// canonical relation is decided on its operands, or a Boolean
    /// connective of such conjuncts. Anything else has no value here
    /// (conservative). A connective is decided by an operand that fixes it
    /// whatever the other operand is, which also covers an undefined other
    /// operand: an undefined conjunct does not hold either.
    fn ground_truth(&self, pattern: &Pattern) -> Option<bool> {
        let pattern = self.resolve(pattern.clone());
        let (operation, arguments) = match &pattern {
            Pattern::Token {
                sort: SemanticSortRef::Builtin(BuiltinSort::Bool),
                value,
            } => return bool_literal(value),
            Pattern::Application {
                application: ApplicationRef::Builtin(operation),
                arguments,
                ..
            } => (*operation, arguments.as_slice()),
            _ => return None,
        };
        match (operation.guard_meaning(), arguments) {
            (GuardMeaning::Negation, [operand]) => self.ground_truth(operand).map(|value| !value),
            (GuardMeaning::Conjunction, [left, right]) => {
                connective(self.ground_truth(left), self.ground_truth(right), false)
            }
            (GuardMeaning::Disjunction, [left, right]) => {
                connective(self.ground_truth(left), self.ground_truth(right), true)
            }
            (GuardMeaning::Implication, [left, right]) => connective(
                self.ground_truth(left).map(|value| !value),
                self.ground_truth(right),
                true,
            ),
            (GuardMeaning::Relation(literal), [left, right]) => {
                let (left, right) = if literal.swapped {
                    (right, left)
                } else {
                    (left, right)
                };
                self.relation_truth(literal.relation, left, right)
                    .map(|holds| holds == literal.positive)
            }
            _ => None,
        }
    }

    /// Whether a canonical relation holds of two operands that are literals
    /// (or, for `==K`, terms built from literals and free constructors)
    /// under the current substitution. `<String` is the lexicographic order
    /// on code points, which is the byte order of their UTF-8 encoding.
    /// Float equality is not evaluated.
    fn relation_truth(
        &self,
        relation: BuiltinOperation,
        left: &Pattern,
        right: &Pattern,
    ) -> Option<bool> {
        match relation {
            BuiltinOperation::IntLess => Some(self.int_literal(left)? < self.int_literal(right)?),
            BuiltinOperation::IntEqual => Some(self.int_literal(left)? == self.int_literal(right)?),
            BuiltinOperation::StringLess => {
                Some(self.string_literal(left)? < self.string_literal(right)?)
            }
            BuiltinOperation::StringEqual => {
                Some(self.string_literal(left)? == self.string_literal(right)?)
            }
            BuiltinOperation::BoolEqual => {
                Some(self.ground_truth(left)? == self.ground_truth(right)?)
            }
            BuiltinOperation::KEqualEq => self.term_equal(left, right),
            _ => None,
        }
    }

    /// The value of an Int literal under the current substitution, or of a
    /// builtin Int operation on such values whose result is defined and fits
    /// (`+Int`, `-Int`, `*Int`, `&Int`, `>>Int` by a non-negative amount,
    /// `divInt` and `modInt` by a non-zero divisor, and `bitRangeInt` with a
    /// non-negative index and length): evaluating a builtin on literals is
    /// its definition. A value outside `i128` has none.
    fn int_literal(&self, pattern: &Pattern) -> Option<i128> {
        match self.resolve(pattern.clone()) {
            Pattern::Token {
                sort: SemanticSortRef::Builtin(BuiltinSort::Int),
                value,
            } => value.parse().ok(),
            Pattern::Application {
                application: ApplicationRef::Builtin(operation),
                arguments,
                ..
            } => {
                let values = arguments
                    .iter()
                    .map(|argument| self.int_literal(argument))
                    .collect::<Option<Vec<_>>>()?;
                evaluate_int(operation, &values)
            }
            _ => None,
        }
    }

    /// The value of a String literal under the current substitution, its
    /// escapes decoded.
    fn string_literal(&self, pattern: &Pattern) -> Option<String> {
        match self.resolve(pattern.clone()) {
            Pattern::Token {
                sort: SemanticSortRef::Builtin(BuiltinSort::String),
                value,
            } => string_value(&value),
            _ => None,
        }
    }

    /// `==K` of two terms under the current substitution, decided only when
    /// both are K sequences of literals and free constructor applications.
    /// Free constructors are injective and pairwise distinct, a literal is
    /// no constructor application, and `~>` is associative with unit `.K`
    /// over such items, so two such terms are equal exactly when they have
    /// the same items. A variable, a function application, a collection or
    /// a cell anywhere in an operand leaves the equality undecided.
    fn term_equal(&self, left: &Pattern, right: &Pattern) -> Option<bool> {
        let left = self.items(left)?;
        let right = self.items(right)?;
        if left.len() != right.len() {
            return Some(false);
        }
        all_equal(
            left.iter()
                .zip(&right)
                .map(|(left, right)| self.item_equal(left, right)),
        )
    }

    /// The items of a K sequence of literals and free constructor
    /// applications under the current substitution, or `None` when the term
    /// is not one.
    fn items(&self, pattern: &Pattern) -> Option<Vec<Pattern>> {
        let resolved = self.resolve(pattern.clone());
        match &resolved {
            Pattern::KSequence { items, .. } => {
                let mut flat = Vec::new();
                for item in items {
                    flat.extend(self.items(item)?);
                }
                Some(flat)
            }
            Pattern::Token { .. } => Some(vec![resolved]),
            Pattern::Application {
                application: ApplicationRef::Declared(id),
                ..
            } if self.graph.free_constructor(id) => Some(vec![resolved]),
            _ => None,
        }
    }

    /// `==K` of two items returned by [`Self::items`].
    fn item_equal(&self, left: &Pattern, right: &Pattern) -> Option<bool> {
        match (left, right) {
            (
                Pattern::Token {
                    sort: left_sort,
                    value: left_value,
                },
                Pattern::Token {
                    sort: right_sort,
                    value: right_value,
                },
            ) => {
                if left_sort == right_sort {
                    token_equal(left_sort, left_value, right_value)
                } else {
                    None
                }
            }
            (
                Pattern::Application {
                    application: ApplicationRef::Declared(left_id),
                    arguments: left_arguments,
                    instance: left_instance,
                    ..
                },
                Pattern::Application {
                    application: ApplicationRef::Declared(right_id),
                    arguments: right_arguments,
                    instance: right_instance,
                    ..
                },
            ) => {
                if left_id == right_id {
                    if left_instance != right_instance
                        || left_arguments.len() != right_arguments.len()
                    {
                        return None;
                    }
                    all_equal(
                        left_arguments
                            .iter()
                            .zip(right_arguments)
                            .map(|(left, right)| self.term_equal(left, right)),
                    )
                } else if self.graph.overload_root(left_id) == self.graph.overload_root(right_id) {
                    // Overload axioms identify applications of one family.
                    None
                } else {
                    Some(false)
                }
            }
            (Pattern::Token { .. }, Pattern::Application { .. })
            | (Pattern::Application { .. }, Pattern::Token { .. }) => Some(false),
            _ => None,
        }
    }

    /// Whether two guard conjuncts cannot both hold: one is `bool::not` of
    /// the other, or both are literals of one relation on the same operands
    /// (in either order for a symmetric relation) with opposite polarity.
    fn complementary(&self, left: &Pattern, right: &Pattern) -> bool {
        if let (Some(left), Some(right)) = (relation_literal(left), relation_literal(right))
            && left.relation == right.relation
            && left.positive != right.positive
            && ((self.same(left.operands[0], right.operands[0])
                && self.same(left.operands[1], right.operands[1]))
                || (left.symmetric
                    && self.same(left.operands[0], right.operands[1])
                    && self.same(left.operands[1], right.operands[0])))
        {
            return true;
        }
        negated(left).is_some_and(|negated| self.same(negated, right))
            || negated(right).is_some_and(|negated| self.same(negated, left))
    }
}

/// A guard conjunct read as a literal of a canonical relation, its operands
/// in the relation's order (catalog [`GuardMeaning::Relation`]), with
/// `bool::not` folded into the polarity.
#[derive(Clone, Copy)]
struct Literal<'a> {
    relation: BuiltinOperation,
    positive: bool,
    symmetric: bool,
    operands: [&'a Pattern; 2],
}

fn relation_literal(pattern: &Pattern) -> Option<Literal<'_>> {
    let Pattern::Application {
        application: ApplicationRef::Builtin(operation),
        arguments,
        ..
    } = pattern
    else {
        return None;
    };
    match (operation.guard_meaning(), arguments.as_slice()) {
        (GuardMeaning::Negation, [operand]) => relation_literal(operand).map(|literal| Literal {
            positive: !literal.positive,
            ..literal
        }),
        (GuardMeaning::Relation(meaning), [left, right]) => Some(Literal {
            relation: meaning.relation,
            positive: meaning.positive,
            symmetric: meaning.symmetric,
            operands: if meaning.swapped {
                [right, left]
            } else {
                [left, right]
            },
        }),
        _ => None,
    }
}

/// The operand of a `bool::not` conjunct.
fn negated(pattern: &Pattern) -> Option<&Pattern> {
    match pattern {
        Pattern::Application {
            application: ApplicationRef::Builtin(operation),
            arguments,
            ..
        } if matches!(operation.guard_meaning(), GuardMeaning::Negation) => {
            match arguments.as_slice() {
                [operand] => Some(operand),
                _ => None,
            }
        }
        _ => None,
    }
}

/// A binary connective with an absorbing value (false for conjunction,
/// true for disjunction): an operand with that value decides it, and two
/// operands with the other value give the other value.
fn connective(left: Option<bool>, right: Option<bool>, absorbing: bool) -> Option<bool> {
    if left == Some(absorbing) || right == Some(absorbing) {
        Some(absorbing)
    } else if left == Some(!absorbing) && right == Some(!absorbing) {
        Some(!absorbing)
    } else {
        None
    }
}

/// The conjunction of component equalities of injective constructions: one
/// unequal component makes the whole unequal, all equal make it equal.
fn all_equal(components: impl Iterator<Item = Option<bool>>) -> Option<bool> {
    let mut all = Some(true);
    for component in components {
        match component {
            Some(false) => return Some(false),
            Some(true) => {}
            None => all = None,
        }
    }
    all
}

fn bool_literal(value: &str) -> Option<bool> {
    match value {
        "true" => Some(true),
        "false" => Some(false),
        _ => None,
    }
}

/// Equality of two tokens of one sort: an Int, Bool or String literal by
/// its value, an identifier or a user token by its lexeme. Other builtin
/// tokens (Float, Bytes) are not compared.
fn token_equal(sort: &SemanticSortRef, left: &str, right: &str) -> Option<bool> {
    match sort {
        SemanticSortRef::Builtin(BuiltinSort::Int) => {
            Some(left.parse::<i128>().ok()? == right.parse::<i128>().ok()?)
        }
        SemanticSortRef::Builtin(BuiltinSort::Bool) => {
            Some(bool_literal(left)? == bool_literal(right)?)
        }
        SemanticSortRef::Builtin(BuiltinSort::String) => {
            Some(string_value(left)? == string_value(right)?)
        }
        SemanticSortRef::Builtin(BuiltinSort::Id) | SemanticSortRef::Declared(_) => {
            Some(left == right)
        }
        _ => None,
    }
}

/// The value of a String token: the quoted body with its `\n`, `\r`, `\t`,
/// `\f`, `\"`, `\\`, `\xHH`, `\uHHHH` and `\UHHHHHHHH` escapes decoded, or
/// `None` for a malformed token or an escape that names no character.
fn string_value(token: &str) -> Option<String> {
    let body = token.strip_prefix('"')?.strip_suffix('"')?;
    let mut value = String::with_capacity(body.len());
    let mut characters = body.chars();
    while let Some(character) = characters.next() {
        if character != '\\' {
            value.push(character);
            continue;
        }
        let digits = match characters.next()? {
            'n' => {
                value.push('\n');
                continue;
            }
            'r' => {
                value.push('\r');
                continue;
            }
            't' => {
                value.push('\t');
                continue;
            }
            'f' => {
                value.push('\u{c}');
                continue;
            }
            escaped @ ('"' | '\\') => {
                value.push(escaped);
                continue;
            }
            'x' => 2,
            'u' => 4,
            'U' => 8,
            _ => return None,
        };
        let hex = characters.by_ref().take(digits).collect::<String>();
        if hex.len() != digits || !hex.bytes().all(|byte| byte.is_ascii_hexdigit()) {
            return None;
        }
        value.push(char::from_u32(u32::from_str_radix(&hex, 16).ok()?)?);
    }
    Some(value)
}

/// The conjuncts of a guard: the operands of nested conjunctions
/// ([`GuardMeaning::Conjunction`]: `bool::and` and `bool::and_then`, `&&`),
/// each of which holds only when both operands do.
fn conjuncts(pattern: &Pattern) -> Vec<&Pattern> {
    match pattern {
        Pattern::Application {
            application: ApplicationRef::Builtin(operation),
            arguments,
            ..
        } if matches!(operation.guard_meaning(), GuardMeaning::Conjunction) => {
            arguments.iter().flat_map(conjuncts).collect()
        }
        other => vec![other],
    }
}

/// Whether two transitions can apply to one configuration: their shared cells
/// unify, no pair of guard conjuncts is complementary, and no guard conjunct
/// evaluates to false on literal operands.
fn transitions_overlap(
    left: &TransitionView<'_>,
    right: &TransitionView<'_>,
    graph: &SortGraph,
) -> bool {
    if left.configuration != right.configuration {
        return false;
    }
    if let (Some(left), Some(right)) = (left.head, right.head)
        && !graph.same_head(left, right)
    {
        return false;
    }
    clauses_overlap(
        &left.clauses,
        left.requires,
        &right.clauses,
        right.requires,
        graph,
    )
}

/// Whether two transitions' clauses over one configuration can match the same
/// configuration. Disjoint footprints are independent: the rules commute (F2
/// amendment, clause 5; a cell read through a function context is in the
/// footprint as an unconstrained clause). Otherwise only the shared cells are
/// unified.
fn clauses_overlap(
    left: &[ClauseView<'_>],
    left_requires: Option<&SemanticTerm>,
    right: &[ClauseView<'_>],
    right_requires: Option<&SemanticTerm>,
    graph: &SortGraph,
) -> bool {
    let right_cells = right
        .iter()
        .map(|clause| (clause.cell, clause))
        .collect::<BTreeMap<_, _>>();
    // A whole group clause shares its leaves with a clause on any cell
    // inside it (KF-016); such pairs are assumed to unify (conservative).
    if !left.iter().any(|clause| {
        right_cells.contains_key(clause.cell)
            || right
                .iter()
                .any(|other| graph.nested(clause.cell, other.cell))
    }) {
        return false;
    }
    // An or-pattern contributes the cross product of its alternatives
    // (clause 7b): the rules overlap when some combination unifies.
    let mut left_nodes = Vec::new();
    for clause in left.iter().filter(|clause| !clause.unconstrained) {
        or_nodes(clause.before, &mut left_nodes);
    }
    let mut right_nodes = Vec::new();
    for clause in right.iter().filter(|clause| !clause.unconstrained) {
        or_nodes(clause.before, &mut right_nodes);
    }
    let right_choices = choices(&right_nodes);
    choices(&left_nodes).into_iter().any(|left_choice| {
        right_choices.iter().any(|right_choice| {
            let catalog = VariableCatalog {
                choices: [left_choice.clone(), right_choice.clone()],
                ..VariableCatalog::default()
            };
            chosen_clauses_overlap(
                left,
                left_requires,
                &right_cells,
                right_requires,
                graph,
                catalog,
            )
        })
    })
}

/// Whether one combination of the two sides' or-pattern alternatives
/// unifies, completing [`clauses_overlap`].
fn chosen_clauses_overlap(
    left: &[ClauseView<'_>],
    left_requires: Option<&SemanticTerm>,
    right_cells: &BTreeMap<&SemanticId, &ClauseView<'_>>,
    right_requires: Option<&SemanticTerm>,
    graph: &SortGraph,
    mut catalog: VariableCatalog,
) -> bool {
    let mut unifier = Unifier::new(graph);
    let cells_unify = left.iter().all(|left_clause| {
        right_cells
            .get(left_clause.cell)
            .is_none_or(|right_clause| {
                let left_pattern = clause_pattern(left_clause, 0, &mut catalog);
                let right_pattern = clause_pattern(right_clause, 1, &mut catalog);
                unifier.unify_clause(
                    left_pattern,
                    left_clause.frame,
                    right_pattern,
                    right_clause.frame,
                )
            })
    });
    if !cells_unify {
        return false;
    }
    for (key, sort, aliased) in std::mem::take(&mut catalog.aliases) {
        if !unifier.unify(Pattern::Variable { key, sort }, aliased) {
            return false;
        }
    }
    let left_guard = left_requires.map(|term| pattern(term, 0, &mut catalog));
    let right_guard = right_requires.map(|term| pattern(term, 1, &mut catalog));
    !unifier.guards_separate(left_guard.as_ref(), right_guard.as_ref())
}

/// A violation of the F2 overlap check (decisions.md, F2 amendment).
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum OverlapViolation {
    /// Two transitions outside one nondet group can apply at the same priority.
    Overlap {
        first: StableItemId,
        second: StableItemId,
    },
    /// A nondet group has a single rule.
    SingleMemberGroup { group: String, rule: StableItemId },
    /// A nondet group mixes priorities.
    MixedPriorityGroup {
        group: String,
        rule: StableItemId,
        priorities: (u32, u32),
    },
    /// A rule of a nondet group overlaps no other rule of the group.
    StaleGroupMember { group: String, rule: StableItemId },
    /// Two alternatives of one or-pattern can match the same term with
    /// different bindings (clause 8, KF-030).
    AmbiguousAlternatives {
        rule: StableItemId,
        first: String,
        second: String,
        range: Option<krs_ir::SourceRange>,
    },
}

/// Returns the first deterministic violation of the overlap check over every
/// transition: an overlapping pair at one priority outside one nondet group,
/// then each group's validation.
pub(crate) fn first_overlap_violation(modules: &[SemanticModule]) -> Option<OverlapViolation> {
    let graph = SortGraph::from_modules(modules);
    if let Some(violation) = first_ambiguous_alternatives(modules, &graph) {
        return Some(violation);
    }
    let rules = transitions(modules);
    if rules.is_empty() {
        return None;
    }
    for (index, left) in rules.iter().enumerate() {
        for right in &rules[index + 1..] {
            // Views of one rule are its instance choices (X10.6).
            if left.priority != right.priority || left.id() == right.id() {
                continue;
            }
            if left.group.is_some() && left.group == right.group {
                continue;
            }
            if transitions_overlap(left, right, &graph) {
                return Some(OverlapViolation::Overlap {
                    first: left.id().clone(),
                    second: right.id().clone(),
                });
            }
        }
    }
    let mut groups = BTreeMap::<(&krs_ir::PackageId, &str), Vec<&TransitionView<'_>>>::new();
    for rule in &rules {
        if let Some(group) = rule.group {
            groups.entry(group).or_default().push(rule);
        }
    }
    for ((_, name), members) in groups {
        let group = (*name).to_owned();
        if let [only] = members.as_slice() {
            return Some(OverlapViolation::SingleMemberGroup {
                group,
                rule: only.id().clone(),
            });
        }
        if let Some(other) = members
            .iter()
            .find(|member| member.priority != members[0].priority)
        {
            return Some(OverlapViolation::MixedPriorityGroup {
                group,
                rule: other.id().clone(),
                priorities: (members[0].priority, other.priority),
            });
        }
        for member in &members {
            let overlaps = members.iter().any(|other| {
                member.id() != other.id() && transitions_overlap(member, other, &graph)
            });
            if !overlaps {
                return Some(OverlapViolation::StaleGroupMember {
                    group,
                    rule: member.id().clone(),
                });
            }
        }
    }
    None
}

/// The pre-patterns of a rule of any kind.
fn pre_patterns(rule: &SemanticRule) -> Vec<&SemanticTerm> {
    match rule.relational_body() {
        RuleBodyRef::Term(body) => vec![body.from()],
        RuleBodyRef::Predicate(body) => body.lhs().terms(),
        RuleBodyRef::Configuration { body, .. } => body
            .parts()
            .iter()
            .filter_map(krs_ir::ClausePart::pre_term)
            .collect(),
    }
}

/// The intra-pattern check (clause 8, KF-030), over every sentence kind:
/// two alternatives of one or-pattern that bind variables must not match
/// one term with different bindings, because K's `#Or` is then ambiguous
/// (LLVM takes one alternative, Haskell explores both). Alternatives that
/// bind no variables may overlap freely, and a name also bound outside the
/// or-pattern is one value in every alternative.
fn first_ambiguous_alternatives(
    modules: &[SemanticModule],
    graph: &SortGraph,
) -> Option<OverlapViolation> {
    let mut rules = modules
        .iter()
        .flat_map(SemanticModule::rules)
        .collect::<Vec<_>>();
    rules.sort_by(|left, right| left.id().cmp(right.id()));
    for rule in rules {
        let patterns = pre_patterns(rule);
        let mut everywhere = BTreeMap::new();
        let mut nodes = Vec::new();
        for term in &patterns {
            named_occurrences(term, &mut everywhere);
            or_nodes(term, &mut nodes);
        }
        for (node, _) in nodes {
            let SemanticTermKind::Or { alternatives } = node.kind() else {
                continue;
            };
            let mut inside = BTreeMap::new();
            named_occurrences(node, &mut inside);
            let outer = everywhere
                .iter()
                .filter(|(name, count)| inside.get(*name).is_none_or(|inner| inner < *count))
                .map(|(name, _)| name.clone())
                .collect::<BTreeSet<_>>();
            let alternatives = alternatives.iter().collect::<Vec<_>>();
            for (index, first) in alternatives.iter().enumerate() {
                for second in &alternatives[index + 1..] {
                    if alternatives_ambiguous(first, second, &outer, graph) {
                        return Some(OverlapViolation::AmbiguousAlternatives {
                            rule: rule.id().clone(),
                            first: render_alternative(first),
                            second: render_alternative(second),
                            range: node.origin().origin().exact_authored_range(),
                        });
                    }
                }
            }
        }
    }
    None
}

/// Whether two alternatives of one or-pattern can match one term with
/// different bindings of a name they bind.
fn alternatives_ambiguous(
    first: &SemanticTerm,
    second: &SemanticTerm,
    outer: &BTreeSet<SemanticId>,
    graph: &SortGraph,
) -> bool {
    let mut bound = BTreeMap::new();
    named_occurrences(first, &mut bound);
    let bound = bound
        .into_keys()
        .filter(|name| !outer.contains(name))
        .collect::<Vec<_>>();
    if bound.is_empty() {
        return false;
    }
    let mut first_nodes = Vec::new();
    or_nodes(first, &mut first_nodes);
    let mut second_nodes = Vec::new();
    or_nodes(second, &mut second_nodes);
    let second_choices = choices(&second_nodes);
    choices(&first_nodes).into_iter().any(|first_choice| {
        second_choices.iter().any(|second_choice| {
            let mut catalog = VariableCatalog {
                choices: [first_choice.clone(), second_choice.clone()],
                ..VariableCatalog::default()
            };
            // A name bound outside the or-pattern is one value in both.
            for name in outer {
                let key = catalog.key(0, name);
                catalog.by_rule[1].insert(name.clone(), key);
            }
            let mut unifier = Unifier::new(graph);
            let left = pattern(first, 0, &mut catalog);
            let right = pattern(second, 1, &mut catalog);
            if !unifier.unify(left, right) {
                return false;
            }
            for (key, sort, aliased) in std::mem::take(&mut catalog.aliases) {
                if !unifier.unify(Pattern::Variable { key, sort }, aliased) {
                    return false;
                }
            }
            bound.iter().any(|name| {
                let (Some(left), Some(right)) =
                    (catalog.by_rule[0].get(name), catalog.by_rule[1].get(name))
                else {
                    return false;
                };
                let sort = SemanticSortRef::Builtin(BuiltinSort::KSequence);
                !unifier.same(
                    &Pattern::Variable {
                        key: *left,
                        sort: sort.clone(),
                    },
                    &Pattern::Variable { key: *right, sort },
                )
            })
        })
    })
}

/// A compact Rust-like rendering of one alternative for diagnostics.
fn render_alternative(term: &SemanticTerm) -> String {
    let list = |terms: Vec<&SemanticTerm>| {
        terms
            .into_iter()
            .map(render_alternative)
            .collect::<Vec<_>>()
            .join(", ")
    };
    match term.kind() {
        SemanticTermKind::Variable { variable } => match variable.kind() {
            krs_ir::SemanticIdKind::Named => variable.as_str().to_owned(),
            _ => "_".to_owned(),
        },
        SemanticTermKind::Token { value } => value.clone(),
        SemanticTermKind::Application {
            application,
            arguments,
            ..
        } => {
            let head = match application {
                ApplicationRef::Declared(id) => id
                    .item_name()
                    .rsplit("::")
                    .next()
                    .unwrap_or_else(|| id.item_name())
                    .to_owned(),
                _ => "..".to_owned(),
            };
            format!("{head}({})", list(arguments.iter().collect()))
        }
        SemanticTermKind::As { alias, pattern } => {
            format!("{} @ {}", alias.as_str(), render_alternative(pattern))
        }
        SemanticTermKind::Or { alternatives } => format!(
            "({})",
            alternatives
                .iter()
                .map(render_alternative)
                .collect::<Vec<_>>()
                .join(" | ")
        ),
        _ => "..".to_owned(),
    }
}

#[cfg(test)]
mod int_fact_tests;
#[cfg(test)]
mod rule_keys_tests;

#[cfg(test)]
mod token_literal_tests;

#[cfg(test)]
mod framing_tests;

#[cfg(test)]
mod lexeme_tests;

#[cfg(test)]
mod overload_tests;

#[cfg(test)]
mod pattern_as_tests;

#[cfg(test)]
mod pattern_or_tests;

#[cfg(test)]
mod function_context_tests;

#[cfg(test)]
mod parametric_tests;

#[cfg(test)]
mod local_rewrite_tests;

#[cfg(test)]
mod cell_collection_tests;

#[cfg(test)]
mod collection_theory_tests;

#[cfg(test)]
mod guard_meaning_tests;

#[cfg(test)]
mod tests {
    use super::*;
    use krs_ir::{ApplicationRef, ItemKind, PackageId};

    fn declared(name: &str, kind: ItemKind) -> StableItemId {
        StableItemId::new(
            PackageId::new("OVERLAP", "overlap", "0.1.0", "test").unwrap(),
            ["fixture"],
            name,
            kind,
            "",
        )
        .unwrap()
    }

    fn application(name: &str, arguments: Vec<Pattern>) -> Pattern {
        Pattern::Application {
            instance: Vec::new(),
            sort: SemanticSortRef::Builtin(BuiltinSort::KSequence),
            application: ApplicationRef::Declared(declared(name, ItemKind::Constructor)),
            arguments,
        }
    }

    fn variable(rule: usize, ordinal: usize, sort: BuiltinSort) -> Pattern {
        Pattern::Variable {
            key: VariableKey { rule, ordinal },
            sort: SemanticSortRef::Builtin(sort),
        }
    }

    fn token(value: &str, sort: BuiltinSort) -> Pattern {
        Pattern::Token {
            sort: SemanticSortRef::Builtin(sort),
            value: value.into(),
        }
    }

    #[test]
    fn distinct_constructors_and_literal_values_are_disjoint() {
        let graph = SortGraph::default_with_builtins();
        assert!(!Unifier::new(&graph).unify(
            application("Left", Vec::new()),
            application("Right", Vec::new())
        ));
        assert!(!Unifier::new(&graph).unify(
            token("true", BuiltinSort::Bool),
            token("false", BuiltinSort::Bool)
        ));
    }

    #[test]
    fn incompatible_where_refinements_are_disjoint() {
        let graph = SortGraph::default_with_builtins();
        assert!(!Unifier::new(&graph).unify(
            variable(0, 0, BuiltinSort::Bool),
            variable(1, 0, BuiltinSort::Int)
        ));
    }

    #[test]
    fn repeated_bindings_participate_in_unification() {
        let graph = SortGraph::default_with_builtins();
        let repeated = application(
            "Pair",
            vec![
                variable(0, 0, BuiltinSort::Bool),
                variable(0, 0, BuiltinSort::Bool),
            ],
        );
        let contradictory = application(
            "Pair",
            vec![
                token("true", BuiltinSort::Bool),
                token("false", BuiltinSort::Bool),
            ],
        );
        assert!(!Unifier::new(&graph).unify(repeated, contradictory));
    }

    #[test]
    fn transitive_subsorts_and_shared_descendants_remain_compatible() {
        let child = SemanticSortRef::Declared(declared("Child", ItemKind::Sort));
        let left = SemanticSortRef::Declared(declared("Left", ItemKind::Sort));
        let right = SemanticSortRef::Declared(declared("Right", ItemKind::Sort));
        let ancestor = SemanticSortRef::Declared(declared("Ancestor", ItemKind::Sort));
        let mut graph = SortGraph::default();
        graph
            .candidates
            .extend([child.clone(), left.clone(), right.clone(), ancestor.clone()]);
        graph
            .parents
            .insert(child.clone(), BTreeSet::from([left.clone(), right.clone()]));
        graph
            .parents
            .insert(left.clone(), BTreeSet::from([ancestor.clone()]));
        graph
            .parents
            .insert(right.clone(), BTreeSet::from([ancestor.clone()]));
        graph.build_closure();

        assert!(graph.is_subsort(&child, &ancestor));
        assert!(!graph.is_subsort(&ancestor, &child));
        assert!(graph.compatible(&left, &right));
        assert!(requirements_compatible(
            &graph,
            &BTreeSet::from([left.clone(), right.clone()])
        ));
        assert!(!requirements_compatible(
            &graph,
            &BTreeSet::from([left, SemanticSortRef::Builtin(BuiltinSort::Bool)])
        ));
        assert!(!graph.compatible(&child, &SemanticSortRef::Builtin(BuiltinSort::Bool)));
    }

    #[test]
    fn subsort_cycle_closure_terminates() {
        let left = SemanticSortRef::Declared(declared("CycleLeft", ItemKind::Sort));
        let right = SemanticSortRef::Declared(declared("CycleRight", ItemKind::Sort));
        let unrelated = SemanticSortRef::Declared(declared("Unrelated", ItemKind::Sort));
        let mut graph = SortGraph::default();
        graph.candidates.extend([left.clone(), right.clone()]);
        graph
            .parents
            .insert(left.clone(), BTreeSet::from([right.clone()]));
        graph
            .parents
            .insert(right.clone(), BTreeSet::from([left.clone()]));
        graph.build_closure();

        assert!(graph.is_subsort(&left, &right));
        assert!(graph.is_subsort(&right, &left));
        assert!(graph.compatible(&left, &right));
        assert!(!graph.is_subsort(&left, &unrelated));
    }

    #[test]
    fn sort_outside_candidates_has_only_reflexive_subsort_relation() {
        let candidate = SemanticSortRef::Declared(declared("Candidate", ItemKind::Sort));
        let outside = SemanticSortRef::Declared(declared("Outside", ItemKind::Sort));
        let mut graph = SortGraph::default();
        graph.candidates.insert(candidate.clone());
        graph
            .parents
            .insert(outside.clone(), BTreeSet::from([candidate.clone()]));
        graph.build_closure();

        assert!(graph.is_subsort(&outside, &outside));
        assert!(!graph.is_subsort(&outside, &candidate));
        assert!(!graph.compatible(&outside, &outside));
        assert!(!graph.compatible(&outside, &candidate));
    }

    #[test]
    fn builtin_sorts_are_only_compatible_with_themselves() {
        let graph = SortGraph::default_with_builtins();
        for left in BuiltinSort::ALL {
            for right in BuiltinSort::ALL {
                let left = SemanticSortRef::Builtin(left);
                let right = SemanticSortRef::Builtin(right);
                assert_eq!(graph.is_subsort(&left, &right), left == right);
                assert_eq!(graph.compatible(&left, &right), left == right);
            }
        }
    }

    #[test]
    fn compatibility_is_symmetric() {
        let child = SemanticSortRef::Declared(declared("Child", ItemKind::Sort));
        let left = SemanticSortRef::Declared(declared("Left", ItemKind::Sort));
        let right = SemanticSortRef::Declared(declared("Right", ItemKind::Sort));
        let outside = SemanticSortRef::Declared(declared("Outside", ItemKind::Sort));
        let mut graph = SortGraph::default_with_builtins();
        graph
            .candidates
            .extend([child.clone(), left.clone(), right.clone()]);
        graph.parents.insert(child, BTreeSet::from([left, right]));
        graph.build_closure();

        for left in graph.candidates.iter().chain(std::iter::once(&outside)) {
            for right in graph.candidates.iter().chain(std::iter::once(&outside)) {
                assert_eq!(graph.compatible(left, right), graph.compatible(right, left));
            }
        }
    }

    impl SortGraph {
        fn default_with_builtins() -> Self {
            let mut graph = Self {
                candidates: BuiltinSort::ALL
                    .into_iter()
                    .map(SemanticSortRef::Builtin)
                    .collect(),
                ..Self::default()
            };
            graph.build_closure();
            graph
        }
    }
}
