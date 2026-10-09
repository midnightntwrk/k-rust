//! Unit tests for the function-context part of the F2 amendment's clause 5
//! (R5, KF-025): a rule's footprint includes the cells read by the function
//! contexts of every equation reachable from its requires and result, and
//! such a cell is unified as an unconstrained variable.

use std::collections::BTreeSet;

use krs_ir::{
    ApplicationRef, BuiltinSort, CellContentFrame, FixedCellPattern, FixedConfigurationPattern,
    ItemKind, NodeOrigin, PackageId, SemanticId, SentenceKind, SourceMapKey, StableItemId,
};
use krs_ir_levels::{SemanticFunctionContext, SemanticRule, SemanticSortRef, SemanticTerm};

use super::{ClauseView, FunctionContexts, SortGraph, add_context_clauses, clauses_overlap};

fn graph() -> SortGraph {
    let mut graph = SortGraph {
        candidates: BuiltinSort::ALL
            .into_iter()
            .map(SemanticSortRef::Builtin)
            .collect::<BTreeSet<_>>(),
        ..SortGraph::default()
    };
    graph.build_closure();
    graph
}

fn origin() -> NodeOrigin {
    NodeOrigin::new(
        SourceMapKey::new("sem.function-context").unwrap(),
        krs_ir::testing::authored(0, 1),
    )
}

fn id(name: &str) -> SemanticId {
    SemanticId::new(name.to_owned()).unwrap()
}

fn item(name: &str, kind: ItemKind) -> StableItemId {
    StableItemId::new(
        PackageId::new("CONTEXTS", "contexts", "0.1.0", "test").unwrap(),
        ["fixture"],
        name,
        kind,
        "",
    )
    .unwrap()
}

fn int_sort() -> SemanticSortRef {
    SemanticSortRef::Builtin(BuiltinSort::Int)
}

fn variable(name: &str) -> SemanticTerm {
    SemanticTerm::variable(origin(), int_sort(), id(name))
}

fn int(value: &str) -> SemanticTerm {
    SemanticTerm::token(origin(), int_sort(), value).unwrap()
}

fn apply(name: &str, arguments: Vec<SemanticTerm>) -> SemanticTerm {
    SemanticTerm::application(
        origin(),
        int_sort(),
        ApplicationRef::Declared(item(name, ItemKind::Constructor)),
        arguments,
    )
}

/// `function(N) => result`, an equation, reading `<bar> B </bar>` when
/// `context` is set.
fn equation(function: &str, result: SemanticTerm, context: bool) -> SemanticRule {
    let rewrite = SemanticTerm::rewrite(
        origin(),
        int_sort(),
        apply(function, vec![variable("N")]),
        result,
    )
    .unwrap();
    let rule = SemanticRule::new(
        origin(),
        item(function, ItemKind::Rule),
        SentenceKind::Equation,
        Vec::new(),
        rewrite,
    )
    .unwrap();
    if !context {
        return rule;
    }
    let cells = FixedConfigurationPattern::new(
        origin(),
        id("Machine"),
        vec![FixedCellPattern::new(
            origin(),
            id("bar"),
            variable("B"),
            CellContentFrame::Exact,
        )],
        Vec::new(),
    )
    .unwrap();
    rule.with_function_context(Some(SemanticFunctionContext::new(origin(), cells)))
}

/// `<k> ReadBar() => result ... </k>` completed to the computation-cell head.
fn read_clause<'a>(k: &'a SemanticId, head: &'a SemanticTerm) -> ClauseView<'a> {
    ClauseView {
        cell: k,
        before: head,
        completed_head: true,
        framed: true,
        unconstrained: false,
    }
}

/// `bump: { bar: x } => { bar: int::add(x, 1) }`, which writes `<bar>`.
fn bump_clause<'a>(bar: &'a SemanticId, before: &'a SemanticTerm) -> ClauseView<'a> {
    ClauseView {
        cell: bar,
        before,
        completed_head: false,
        framed: false,
        unconstrained: false,
    }
}

/// Whether `read: ReadBar() => <read_result>` and `bump` overlap under the
/// given equations.
fn read_overlaps_bump(equations: &[SemanticRule], read_result: &SemanticTerm) -> bool {
    let graph = graph();
    let (k, bar) = (id("k"), id("bar"));
    let head = apply("ReadBar", Vec::new());
    let bumped = variable("X");
    let contexts = FunctionContexts::from_rules(equations);
    let mut read = vec![read_clause(&k, &head)];
    add_context_clauses(&mut read, contexts.reachable_cells([read_result]));
    let bump = vec![bump_clause(&bar, &bumped)];
    clauses_overlap(&read, None, &bump, None, &graph)
}

#[test]
fn a_rule_calling_a_context_function_reads_its_cells() {
    let bar_plus = equation("BarPlus", variable("B"), true);
    assert!(read_overlaps_bump(
        &[bar_plus],
        &apply("BarPlus", vec![int("1")])
    ));
}

#[test]
fn the_same_pair_is_not_reported_without_the_context() {
    let bar_plus = equation("BarPlus", variable("B"), false);
    assert!(!read_overlaps_bump(
        &[bar_plus],
        &apply("BarPlus", vec![int("1")])
    ));
}

#[test]
fn contexts_are_reached_through_callers_transitively() {
    let bar_plus = equation("BarPlus", variable("B"), true);
    let bar_twice = equation("BarTwice", apply("BarPlus", vec![variable("N")]), false);
    assert!(read_overlaps_bump(
        &[bar_plus, bar_twice],
        &apply("BarTwice", vec![int("1")])
    ));
}

#[test]
fn a_context_cell_the_rule_already_names_adds_no_clause() {
    let bar_plus = equation("BarPlus", variable("B"), true);
    let equations = [bar_plus];
    let contexts = FunctionContexts::from_rules(&equations);
    let result = apply("BarPlus", vec![int("1")]);
    let bar = id("bar");
    let before = variable("X");
    let mut clauses = vec![bump_clause(&bar, &before)];
    add_context_clauses(&mut clauses, contexts.reachable_cells([&result]));
    assert_eq!(clauses.len(), 1);
    assert!(!clauses[0].unconstrained);
}
