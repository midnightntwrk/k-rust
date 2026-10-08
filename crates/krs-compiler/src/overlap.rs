//! Sort-aware overlap checking of transitions (decisions.md, F2 and its amendment).
//!
//! Every transition is checked: readable tables, `#[k::rule]` term rules
//! completed to the computation-cell head, and `cells!` rules. Equations,
//! simplifications, aliases, claims, and anywhere rules are not. Rules at
//! different priorities never overlap; rules of one `nondet` group may, and
//! the group is validated instead; and literal complementary guards separate
//! two rules after unification.

use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    ApplicationRef, BuiltinOperation, BuiltinSort, ListOperation, MapOperation, SemanticId,
    SetOperation, StableItemId,
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
        && left != right
    {
        return false;
    }
    let right_cells = right
        .clauses
        .iter()
        .map(|clause| (clause.cell, clause))
        .collect::<BTreeMap<_, _>>();
    let mut catalog = VariableCatalog::default();
    let mut unifier = Unifier::new(graph);
    let cells_unify = left.clauses.iter().all(|left_clause| {
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
    let left_guard = left.requires.map(|term| pattern(term, 0, &mut catalog));
    let right_guard = right.requires.map(|term| pattern(term, 1, &mut catalog));
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
}

/// Returns the first deterministic violation of the overlap check over every
/// transition: an overlapping pair at one priority outside one nondet group,
/// then each group's validation.
pub(crate) fn first_overlap_violation(modules: &[SemanticModule]) -> Option<OverlapViolation> {
    let rules = transitions(modules);
    if rules.is_empty() {
        return None;
    }
    let graph = SortGraph::from_modules(modules);
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

#[cfg(test)]
mod rule_keys_tests;

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
