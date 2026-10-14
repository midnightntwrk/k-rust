//! Unit tests for the F2 amendment's clause 5 as U07 implements it (KF-015):
//! rules with disjoint footprints commute and are never reported, and rules
//! that share a cell are unified on the shared cells only. A whole nested
//! (group) cell clause (KF-016) shares every cell inside the group.

use std::collections::BTreeSet;

use krs_ir::{
    ApplicationRef, BuiltinSort, ItemKind, NodeOrigin, PackageId, SemanticId, SourceMapKey,
    StableItemId,
};
use krs_ir_levels::{SemanticSortRef, SemanticTerm};

use super::{ClauseView, SortGraph, clauses_overlap};

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
        SourceMapKey::new("sem.framing").unwrap(),
        krs_ir::testing::authored(0, 1),
    )
}

fn cell(name: &str) -> SemanticId {
    SemanticId::new(name.to_owned()).unwrap()
}

fn variable(name: &str, sort: BuiltinSort) -> SemanticTerm {
    SemanticTerm::variable(origin(), SemanticSortRef::Builtin(sort), cell(name))
}

fn int(value: &str) -> SemanticTerm {
    SemanticTerm::token(origin(), SemanticSortRef::Builtin(BuiltinSort::Int), value).unwrap()
}

fn constructor(name: &str) -> SemanticTerm {
    SemanticTerm::application(
        origin(),
        SemanticSortRef::Builtin(BuiltinSort::KSequence),
        ApplicationRef::Declared(
            StableItemId::new(
                PackageId::new("FRAMING", "framing", "0.1.0", "test").unwrap(),
                ["fixture"],
                name,
                ItemKind::Constructor,
                "",
            )
            .unwrap(),
        ),
        Vec::new(),
    )
}

fn k_head(item: &SemanticTerm) -> SemanticTerm {
    SemanticTerm::k_sequence(
        origin(),
        SemanticSortRef::Builtin(BuiltinSort::KSequence),
        vec![item.clone()],
    )
}

fn exact<'a>(cell: &'a SemanticId, before: &'a SemanticTerm) -> ClauseView<'a> {
    ClauseView {
        cell,
        before,
        completed_head: false,
        framed: false,
        unconstrained: false,
    }
}

fn framed<'a>(cell: &'a SemanticId, before: &'a SemanticTerm) -> ClauseView<'a> {
    ClauseView {
        cell,
        before,
        completed_head: false,
        framed: true,
        unconstrained: false,
    }
}

#[test]
fn disjoint_footprints_are_not_reported() {
    let graph = graph();
    let (k, fuel) = (cell("k"), cell("fuel"));
    let done = k_head(&constructor("Done"));
    let burned = variable("F", BuiltinSort::Int);
    // `done` erases its program item; `burn` leaves `k` out and reads only `fuel`.
    assert!(!clauses_overlap(
        &[framed(&k, &done)],
        None,
        &[exact(&fuel, &burned)],
        None,
        &graph,
    ));
}

#[test]
fn a_shared_cell_is_still_unified_and_reported() {
    let graph = graph();
    let (k, env, acc) = (cell("k"), cell("env"), cell("acc"));
    let step = k_head(&constructor("Step"));
    let left_env = variable("E", BuiltinSort::Map);
    let right_env = variable("E", BuiltinSort::Map);
    let right_acc = variable("A", BuiltinSort::Int);
    // A k rule and a k-less rule that both read `env` can fire on one configuration.
    assert!(clauses_overlap(
        &[framed(&k, &step), exact(&env, &left_env)],
        None,
        &[exact(&env, &right_env), exact(&acc, &right_acc)],
        None,
        &graph,
    ));
}

#[test]
fn only_shared_cells_are_unified() {
    let graph = graph();
    let (fuel, acc) = (cell("fuel"), cell("acc"));
    let zero = int("0");
    let one = int("1");
    let anything = variable("A", BuiltinSort::Int);
    // The `acc` literals differ, so the rules are disjoint on their shared cell.
    assert!(!clauses_overlap(
        &[exact(&acc, &zero)],
        None,
        &[exact(&fuel, &anything), exact(&acc, &one)],
        None,
        &graph,
    ));
    // `fuel` is not shared, so its pattern cannot separate the rules.
    assert!(clauses_overlap(
        &[exact(&fuel, &zero), exact(&acc, &anything)],
        None,
        &[exact(&acc, &one)],
        None,
        &graph,
    ));
}

fn group_sort() -> SemanticSortRef {
    SemanticSortRef::Cell(
        StableItemId::new(
            PackageId::new("FRAMING", "framing", "0.1.0", "test").unwrap(),
            ["fixture"],
            "Frame",
            ItemKind::Cell,
            "",
        )
        .unwrap(),
    )
}

/// A graph where `frame` is a group cell containing `pc` and `gas`.
fn group_graph() -> SortGraph {
    let mut graph = SortGraph {
        candidates: BuiltinSort::ALL
            .into_iter()
            .map(SemanticSortRef::Builtin)
            .chain([group_sort()])
            .collect::<BTreeSet<_>>(),
        ..SortGraph::default()
    };
    graph
        .descendants
        .insert(cell("frame"), BTreeSet::from([cell("pc"), cell("gas")]));
    graph.build_closure();
    graph
}

#[test]
fn a_group_clause_shares_the_cells_inside_it() {
    let graph = group_graph();
    let (frame, pc) = (cell("frame"), cell("pc"));
    let whole = SemanticTerm::variable(origin(), group_sort(), cell("F"));
    let zero = int("0");
    // `frame: f` constrains `pc`, so a k-less rule on `pc` is not independent.
    assert!(clauses_overlap(
        &[exact(&frame, &whole)],
        None,
        &[exact(&pc, &zero)],
        None,
        &graph,
    ));
    assert!(clauses_overlap(
        &[exact(&pc, &zero)],
        None,
        &[exact(&frame, &whole)],
        None,
        &graph,
    ));
}

#[test]
fn two_group_variables_unify() {
    let graph = group_graph();
    let frame = cell("frame");
    let left = SemanticTerm::variable(origin(), group_sort(), cell("F"));
    let right = SemanticTerm::variable(origin(), group_sort(), cell("G"));
    assert!(clauses_overlap(
        &[exact(&frame, &left)],
        None,
        &[exact(&frame, &right)],
        None,
        &graph,
    ));
}
