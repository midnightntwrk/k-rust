//! Signed Int literals in the overlap check (U05, KF-006).
//!
//! Tokens unify only with an identical canonical token or a variable of a
//! compatible sort, so `Sgn(-1)` and `Sgn(1)` are disjoint while `Sgn(-1)`
//! and `Sgn(v)` overlap.

use krs_ir::{ApplicationRef, BuiltinSort, ItemKind, PackageId, StableItemId};
use krs_ir_levels::SemanticSortRef;

use super::{Pattern, SortGraph, Unifier, VariableKey};

fn sgn(argument: Pattern) -> Pattern {
    Pattern::Application {
        instance: Vec::new(),
        sort: SemanticSortRef::Builtin(BuiltinSort::Int),
        application: ApplicationRef::Declared(
            StableItemId::new(
                PackageId::new("OVERLAP", "overlap", "0.1.0", "test").unwrap(),
                ["fixture"],
                "Sgn",
                ItemKind::Constructor,
                "",
            )
            .unwrap(),
        ),
        arguments: vec![argument],
    }
}

fn int(value: &str) -> Pattern {
    Pattern::Token {
        sort: SemanticSortRef::Builtin(BuiltinSort::Int),
        value: value.into(),
    }
}

fn graph() -> SortGraph {
    let mut graph = SortGraph {
        candidates: BuiltinSort::ALL
            .into_iter()
            .map(SemanticSortRef::Builtin)
            .collect(),
        ..SortGraph::default()
    };
    graph.build_closure();
    graph
}

#[test]
fn a_negative_literal_is_disjoint_from_its_absolute_value() {
    let graph = graph();
    assert!(!Unifier::new(&graph).unify(sgn(int("-1")), sgn(int("1"))));
    assert!(!Unifier::new(&graph).unify(sgn(int("-1")), sgn(int("-2"))));
    assert!(Unifier::new(&graph).unify(sgn(int("-1")), sgn(int("-1"))));
}

#[test]
fn a_negative_literal_overlaps_an_int_variable() {
    let graph = graph();
    let variable = Pattern::Variable {
        key: VariableKey {
            rule: 1,
            ordinal: 0,
        },
        sort: SemanticSortRef::Builtin(BuiltinSort::Int),
    };
    assert!(Unifier::new(&graph).unify(sgn(int("-1")), sgn(variable)));
}
