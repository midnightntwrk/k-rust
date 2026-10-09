//! Sort-aware overlap checking of transitions (decisions.md, F2 and its amendment).
//!
//! Every transition is checked: readable tables, `#[k::rule]` term rules
//! completed to the computation-cell head, and `cells!` rules. Equations,
//! simplifications, aliases, claims, and anywhere rules are not. Rules at
//! different priorities never overlap; rules of one `nondet` group may, and
//! the group is validated instead; and literal complementary guards separate
//! two rules after unification. Members of one `overload` family are one
//! head: K's overload axioms identify `expDot(inj(L), F)` with
//! `inj(lValDot(L, F))`, so their applications unify when their arguments do
//! (clause 7c). An `A | B` or-pattern contributes the cross product of its
//! alternatives (clause 7b), and in any sentence two of its alternatives
//! that bind variables must not match one term with different bindings
//! (clause 8, KF-030).

use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    ApplicationRef, BuiltinOperation, BuiltinSort, ListOperation, MapOperation,
    ProductionAttribute, SemanticId, SetOperation, StableItemId,
};
use krs_ir_levels::{
    RuleBodyRef, SemanticApplicationRef, SemanticModule, SemanticRule, SemanticSortRef,
    SemanticTerm, SemanticTermKind,
};

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
        } => format!(
            "{application:?}({})",
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
    for child in subterms(term) {
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
    for child in subterms(term) {
        named_occurrences(child, output);
    }
}

impl VariableCatalog {
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
        // Every generated group-cell sort (KF-016) is a subsort of KItem.
        let k_item = graph
            .candidates
            .iter()
            .find(|sort| {
                matches!(sort, SemanticSortRef::Declared(id)
                    if id.item_name() == "KItem" && id.package().k_namespace() == "KRS-FRAMEWORK")
            })
            .cloned();
        for module in modules {
            let mut groups = Vec::new();
            if let Some(configuration) = module.configuration() {
                group_cells(configuration.cells(), &mut groups);
            }
            for (cell, sort, descendants) in groups {
                graph.descendants.insert(cell, descendants);
                graph.candidates.insert(sort.clone());
                if let Some(k_item) = &k_item {
                    graph
                        .parents
                        .entry(sort)
                        .or_default()
                        .insert(k_item.clone());
                }
            }
        }
        graph.build_closure();
        graph.resolve_overload_roots();
        graph
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
                },
                Pattern::Application {
                    sort: right_sort,
                    application: right_application,
                    arguments: right_arguments,
                },
            ) => {
                self.graph.same_head(&left_application, &right_application)
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
                Pattern::KSequence {
                    sort: left_sort,
                    items: left_items,
                },
                Pattern::KSequence {
                    sort: right_sort,
                    items: right_items,
                },
            ) => {
                self.graph.compatible(&left_sort, &right_sort)
                    && self.unify_arguments(left_items, right_items)
            }
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
            (
                Pattern::List {
                    sort: left_sort,
                    operation: left_operation,
                    arguments: left_arguments,
                },
                Pattern::List {
                    sort: right_sort,
                    operation: right_operation,
                    arguments: right_arguments,
                },
            ) => {
                self.graph.compatible(&left_sort, &right_sort)
                    && left_operation == right_operation
                    && self.unify_arguments(left_arguments, right_arguments)
            }
            (
                Pattern::Set {
                    sort: left_sort,
                    operation: left_operation,
                    arguments: left_arguments,
                },
                Pattern::Set {
                    sort: right_sort,
                    operation: right_operation,
                    arguments: right_arguments,
                },
            ) => {
                self.graph.compatible(&left_sort, &right_sort)
                    && left_operation == right_operation
                    && self.unify_arguments(left_arguments, right_arguments)
            }
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
            return false;
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
        } => Pattern::Application {
            sort: term.sort().clone(),
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
        SemanticTermKind::Rewrite { .. } => {
            unreachable!("configuration clause pre-patterns are never rewrites")
        }
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

/// One clause a transition places on a cell, as the overlap check sees it.
struct ClauseView<'a> {
    cell: &'a SemanticId,
    before: &'a SemanticTerm,
    /// The pattern is a computation-cell head completed with an implicit `KSequence`.
    completed_head: bool,
    /// The cell content is a prefix: its omitted tail may hold more items.
    framed: bool,
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
                sort: SemanticSortRef::Builtin(BuiltinSort::KSequence)
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
        _ => None,
    }
}

/// Every transition the check covers: configuration rules, readable head rules,
/// and term rules completed to the computation-cell head. Equations,
/// simplifications, aliases, claims, and anywhere rules are outside its scope.
fn transitions(modules: &[SemanticModule]) -> Vec<TransitionView<'_>> {
    let computation = computation_cell(modules);
    let mut views = Vec::new();
    for rule in modules.iter().flat_map(SemanticModule::rules) {
        if rule.kind() != krs_ir::SentenceKind::Transition || rule.anywhere().is_some() {
            continue;
        }
        let (configuration, clauses) = match rule.relational_body() {
            RuleBodyRef::Configuration { body, .. } => (
                body.configuration(),
                body.clauses()
                    .iter()
                    .map(|clause| ClauseView {
                        cell: clause.cell(),
                        before: clause.before(),
                        completed_head: false,
                        framed: !matches!(clause.frame(), krs_ir::CellContentFrame::Exact),
                    })
                    .collect::<Vec<_>>(),
            ),
            RuleBodyRef::Term(body) => {
                let Some((configuration, cell)) = computation else {
                    continue;
                };
                (
                    configuration,
                    vec![ClauseView {
                        cell,
                        before: body.from(),
                        completed_head: true,
                        framed: true,
                    }],
                )
            }
        };
        let head = computation.and_then(|(_, cell)| {
            clauses
                .iter()
                .find(|clause| clause.cell == cell)
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
            requires: rule
                .requires()
                .map(krs_ir_levels::SemanticRuleCondition::term),
            head,
        });
    }
    views.sort_by(|left, right| left.id().cmp(right.id()));
    views
}

/// K's default rule priority.
const DEFAULT_PRIORITY: u32 = 50;

fn clause_pattern(clause: &ClauseView<'_>, rule: usize, catalog: &mut VariableCatalog) -> Pattern {
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
    /// Unifies two cell contents, letting a framed sequence absorb the other's longer tail.
    fn unify_clause(
        &mut self,
        left: Pattern,
        left_framed: bool,
        right: Pattern,
        right_framed: bool,
    ) -> bool {
        match (left, right) {
            (
                Pattern::KSequence {
                    sort: left_sort,
                    items: mut left_items,
                },
                Pattern::KSequence {
                    sort: right_sort,
                    items: mut right_items,
                },
            ) if left_framed || right_framed => {
                if !self.graph.compatible(&left_sort, &right_sort) {
                    return false;
                }
                let shared = match (left_framed, right_framed) {
                    (true, true) => left_items.len().min(right_items.len()),
                    (true, false) if left_items.len() <= right_items.len() => left_items.len(),
                    (false, true) if right_items.len() <= left_items.len() => right_items.len(),
                    _ => return false,
                };
                left_items.truncate(shared);
                right_items.truncate(shared);
                self.unify_arguments(left_items, right_items)
            }
            (left, right) => self.unify(left, right),
        }
    }

    /// Whether two patterns are identical under the current substitution.
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
                    ..
                },
                Pattern::Application {
                    application: right_application,
                    arguments: right_arguments,
                    ..
                },
            ) => left_application == right_application && all(left_arguments, right_arguments),
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

    /// Whether some conjunct of one guard is the literal complement of a
    /// conjunct of the other (F2 amendment, clause 4).
    fn guards_complementary(&self, left: Option<&Pattern>, right: Option<&Pattern>) -> bool {
        let (Some(left), Some(right)) = (left, right) else {
            return false;
        };
        let left = conjuncts(left);
        let right = conjuncts(right);
        left.iter().any(|left| {
            right
                .iter()
                .any(|right| self.complementary(&Guard::of(left), &Guard::of(right)))
        })
    }

    fn complementary(&self, left: &Guard<'_>, right: &Guard<'_>) -> bool {
        match (left, right) {
            (Guard::Not(negated), other) | (other, Guard::Not(negated))
                if self.same(negated, other.pattern()) =>
            {
                true
            }
            (Guard::IntLess(a, b, _), Guard::IntLessEqual(c, d, _))
            | (Guard::IntLessEqual(c, d, _), Guard::IntLess(a, b, _)) => {
                self.same(a, d) && self.same(b, c)
            }
            (Guard::IntEqual(a, b, _), Guard::IntNotEqual(c, d, _))
            | (Guard::IntNotEqual(c, d, _), Guard::IntEqual(a, b, _))
            | (Guard::BoolEqual(a, b, _), Guard::BoolNotEqual(c, d, _))
            | (Guard::BoolNotEqual(c, d, _), Guard::BoolEqual(a, b, _)) => {
                (self.same(a, c) && self.same(b, d)) || (self.same(a, d) && self.same(b, c))
            }
            _ => false,
        }
    }
}

/// One guard conjunct, with `>` and `>=` normalised to `<` and `<=` by swapping operands.
enum Guard<'a> {
    Not(&'a Pattern),
    IntLess(&'a Pattern, &'a Pattern, &'a Pattern),
    IntLessEqual(&'a Pattern, &'a Pattern, &'a Pattern),
    IntEqual(&'a Pattern, &'a Pattern, &'a Pattern),
    IntNotEqual(&'a Pattern, &'a Pattern, &'a Pattern),
    BoolEqual(&'a Pattern, &'a Pattern, &'a Pattern),
    BoolNotEqual(&'a Pattern, &'a Pattern, &'a Pattern),
    Other(&'a Pattern),
}

impl<'a> Guard<'a> {
    fn of(pattern: &'a Pattern) -> Self {
        let Pattern::Application {
            application: ApplicationRef::Builtin(operation),
            arguments,
            ..
        } = pattern
        else {
            return Self::Other(pattern);
        };
        match (operation, arguments.as_slice()) {
            (BuiltinOperation::BoolNot, [negated]) => Self::Not(negated),
            (BuiltinOperation::IntLess, [a, b]) => Self::IntLess(a, b, pattern),
            (BuiltinOperation::IntGreater, [a, b]) => Self::IntLess(b, a, pattern),
            (BuiltinOperation::IntLessEqual, [a, b]) => Self::IntLessEqual(a, b, pattern),
            (BuiltinOperation::IntGreaterEqual, [a, b]) => Self::IntLessEqual(b, a, pattern),
            (BuiltinOperation::IntEqual, [a, b]) => Self::IntEqual(a, b, pattern),
            (BuiltinOperation::IntNotEqual, [a, b]) => Self::IntNotEqual(a, b, pattern),
            (BuiltinOperation::BoolEqual, [a, b]) => Self::BoolEqual(a, b, pattern),
            (BuiltinOperation::BoolNotEqual, [a, b]) => Self::BoolNotEqual(a, b, pattern),
            _ => Self::Other(pattern),
        }
    }

    const fn pattern(&self) -> &'a Pattern {
        match self {
            Self::Not(pattern)
            | Self::Other(pattern)
            | Self::IntLess(_, _, pattern)
            | Self::IntLessEqual(_, _, pattern)
            | Self::IntEqual(_, _, pattern)
            | Self::IntNotEqual(_, _, pattern)
            | Self::BoolEqual(_, _, pattern)
            | Self::BoolNotEqual(_, _, pattern) => pattern,
        }
    }
}

/// The conjuncts of a guard: the operands of nested `bool::and`.
fn conjuncts(pattern: &Pattern) -> Vec<&Pattern> {
    match pattern {
        Pattern::Application {
            application: ApplicationRef::Builtin(BuiltinOperation::BoolAnd),
            arguments,
            ..
        } => arguments.iter().flat_map(conjuncts).collect(),
        other => vec![other],
    }
}

/// Whether two transitions can apply to one configuration: their shared cells
/// unify, and no pair of literal guard conjuncts is complementary.
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
/// amendment, clause 5, without the function-context part). Otherwise only the
/// shared cells are unified.
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
    for clause in left {
        or_nodes(clause.before, &mut left_nodes);
    }
    let mut right_nodes = Vec::new();
    for clause in right {
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
                    left_clause.framed,
                    right_pattern,
                    right_clause.framed,
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
    !unifier.guards_complementary(left_guard.as_ref(), right_guard.as_ref())
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
            if left.priority != right.priority {
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
                !std::ptr::eq(*member, *other) && transitions_overlap(member, other, &graph)
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
        RuleBodyRef::Configuration { body, .. } => body
            .clauses()
            .iter()
            .map(krs_ir::FixedCellClause::before)
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
