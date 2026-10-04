//! Sort-aware overlap checking for readable computation-head rules.

use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    BuiltinSort, FixedConfigurationRewrite, ListOperation, MapOperation, SemanticId, SetOperation,
    StableItemId,
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
            | Self::Cell { sort, .. } => sort,
        }
    }
}

#[derive(Default)]
struct VariableCatalog {
    by_rule: [BTreeMap<SemanticId, VariableKey>; 2],
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
        graph.build_closure();
        graph
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

    #[allow(clippy::too_many_lines)] // Keeps the symmetric unification cases in one exhaustive match.
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
                left_application == right_application
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
            Pattern::Token { .. } => false,
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
        SemanticTermKind::Map {
            operation,
            arguments,
        } => Pattern::Map {
            sort: term.sort().clone(),
            operation: *operation,
            arguments: arguments
                .iter()
                .map(|argument| pattern(argument, rule, catalog))
                .collect(),
        },
        SemanticTermKind::List {
            operation,
            arguments,
        } => Pattern::List {
            sort: term.sort().clone(),
            operation: *operation,
            arguments: arguments
                .iter()
                .map(|argument| pattern(argument, rule, catalog))
                .collect(),
        },
        SemanticTermKind::Set {
            operation,
            arguments,
        } => Pattern::Set {
            sort: term.sort().clone(),
            operation: *operation,
            arguments: arguments
                .iter()
                .map(|argument| pattern(argument, rule, catalog))
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
    }
}

fn configuration_body(
    rule: &SemanticRule,
) -> Option<&FixedConfigurationRewrite<SemanticId, SemanticTerm>> {
    match rule.relational_body() {
        RuleBodyRef::Configuration { body, .. } => Some(body),
        RuleBodyRef::Term(_) => None,
    }
}

fn rules_overlap(left: &SemanticRule, right: &SemanticRule, graph: &SortGraph) -> bool {
    let (Some(left), Some(right)) = (configuration_body(left), configuration_body(right)) else {
        return false;
    };
    if left.configuration() != right.configuration() {
        return false;
    }
    let right_cells = right
        .clauses()
        .iter()
        .map(|clause| (clause.cell(), clause.before()))
        .collect::<BTreeMap<_, _>>();
    let mut catalog = VariableCatalog::default();
    let mut unifier = Unifier::new(graph);
    left.clauses().iter().all(|left_clause| {
        right_cells
            .get(left_clause.cell())
            .is_none_or(|right_term| {
                unifier.unify(
                    pattern(left_clause.before(), 0, &mut catalog),
                    pattern(right_term, 1, &mut catalog),
                )
            })
    })
}

/// Returns the first deterministic pair of overlapping readable head rules.
pub(crate) fn first_head_rule_overlap(
    modules: &[SemanticModule],
    head_rule_ids: &BTreeSet<StableItemId>,
) -> Option<(StableItemId, StableItemId)> {
    if head_rule_ids.len() < 2 {
        return None;
    }
    let graph = SortGraph::from_modules(modules);
    let mut rules = modules
        .iter()
        .flat_map(SemanticModule::rules)
        .filter(|rule| head_rule_ids.contains(rule.id()))
        .collect::<Vec<_>>();
    rules.sort_by(|left, right| left.id().cmp(right.id()));
    for (index, left) in rules.iter().enumerate() {
        for right in &rules[index + 1..] {
            let left_priority = left
                .priority()
                .map_or(50, krs_ir_levels::SemanticRulePriority::value);
            let right_priority = right
                .priority()
                .map_or(50, krs_ir_levels::SemanticRulePriority::value);
            if left_priority != right_priority {
                continue;
            }
            if rules_overlap(left, right, &graph) {
                return Some((left.id().clone(), right.id().clone()));
            }
        }
    }
    None
}

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
