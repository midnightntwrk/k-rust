//! Parametric applications in the overlap check (U17, KF-027, X10.7d).
//!
//! A parametric application's identity is its (symbol, instance) pair: K's
//! KORE declares `Lblwrap{SortVal{}}` and `Lblwrap{SortDone{}}` as distinct
//! symbols, so heads at different instances never overlap, while two heads
//! at the same instance unify like any other application.

use krs_ir::{ApplicationRef, BuiltinSort, ItemKind, PackageId, StableItemId};
use krs_ir_levels::SemanticSortRef;

use super::{Pattern, SortGraph, Unifier, VariableKey};

fn sort(name: &str) -> SemanticSortRef {
    SemanticSortRef::Declared(
        StableItemId::new(
            PackageId::new("OVERLAP", "overlap", "0.1.0", "test").unwrap(),
            ["fixture"],
            name,
            ItemKind::Sort,
            "",
        )
        .unwrap(),
    )
}

fn wrap(instance: &SemanticSortRef, argument: Pattern) -> Pattern {
    Pattern::Application {
        instance: vec![instance.clone()],
        sort: instance.clone(),
        application: ApplicationRef::Declared(
            StableItemId::new(
                PackageId::new("OVERLAP", "overlap", "0.1.0", "test").unwrap(),
                ["fixture"],
                "Wrap",
                ItemKind::Constructor,
                "",
            )
            .unwrap(),
        ),
        arguments: vec![argument],
    }
}

fn variable(ordinal: usize, sort: &SemanticSortRef) -> Pattern {
    Pattern::Variable {
        key: VariableKey { rule: 1, ordinal },
        sort: sort.clone(),
    }
}

fn graph() -> SortGraph {
    let mut graph = SortGraph {
        candidates: BuiltinSort::ALL
            .into_iter()
            .map(SemanticSortRef::Builtin)
            .chain([sort("Val"), sort("Done")])
            .collect(),
        ..SortGraph::default()
    };
    graph.build_closure();
    graph
}

#[test]
fn heads_at_different_instances_never_overlap() {
    let graph = graph();
    let (val, done) = (sort("Val"), sort("Done"));
    assert!(!Unifier::new(&graph).unify(
        wrap(&val, variable(0, &val)),
        wrap(&done, variable(1, &done)),
    ));
}

#[test]
fn heads_at_one_instance_unify() {
    let graph = graph();
    let val = sort("Val");
    assert!(
        Unifier::new(&graph).unify(wrap(&val, variable(0, &val)), wrap(&val, variable(1, &val)),)
    );
}

#[test]
fn the_instance_separates_applications_of_one_result_sort() {
    // A parametric production whose result is fixed (`syntax {S} Bool ::=
    // same(S, S)`) has one result sort at every instance, so only the
    // instance tells `same{Int}` from `same{Bool}`.
    let graph = graph();
    let same = |instance: BuiltinSort, ordinal| Pattern::Application {
        instance: vec![SemanticSortRef::Builtin(instance)],
        sort: SemanticSortRef::Builtin(BuiltinSort::Bool),
        application: ApplicationRef::Declared(
            StableItemId::new(
                PackageId::new("OVERLAP", "overlap", "0.1.0", "test").unwrap(),
                ["fixture"],
                "Same",
                ItemKind::Constructor,
                "",
            )
            .unwrap(),
        ),
        arguments: vec![variable(ordinal, &SemanticSortRef::Builtin(instance))],
    };
    assert!(!Unifier::new(&graph).unify(same(BuiltinSort::Int, 0), same(BuiltinSort::Bool, 1)));
    assert!(Unifier::new(&graph).unify(same(BuiltinSort::Int, 0), same(BuiltinSort::Int, 1)));
}
