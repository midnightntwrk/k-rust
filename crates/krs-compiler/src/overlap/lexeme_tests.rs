//! User token sorts in the overlap check (U10, KF-003; F2 clause 7a).
//!
//! A `k::lexeme!` term is a token of a user token sort, compared by its
//! text: different texts never overlap, and a lexeme overlaps a variable of
//! its sort.

use krs_ir::{ApplicationRef, ItemKind, PackageId, StableItemId};
use krs_ir_levels::SemanticSortRef;

use super::{Pattern, SortGraph, Unifier, VariableKey};

fn item(name: &str, kind: ItemKind) -> StableItemId {
    StableItemId::new(
        PackageId::new("TOKENS", "tokens", "0.1.0", "test").unwrap(),
        ["fixture"],
        name,
        kind,
        "",
    )
    .unwrap()
}

fn name_sort() -> SemanticSortRef {
    SemanticSortRef::Declared(item("Name", ItemKind::Sort))
}

fn call(argument: Pattern) -> Pattern {
    Pattern::Application {
        instance: Vec::new(),
        sort: SemanticSortRef::Declared(item("Stmt", ItemKind::Sort)),
        application: ApplicationRef::Declared(item("Call", ItemKind::Constructor)),
        arguments: vec![argument],
    }
}

fn lexeme(text: &str) -> Pattern {
    Pattern::Token {
        sort: name_sort(),
        value: text.into(),
    }
}

fn graph() -> SortGraph {
    let mut graph = SortGraph {
        candidates: [
            name_sort(),
            SemanticSortRef::Declared(item("Stmt", ItemKind::Sort)),
        ]
        .into_iter()
        .collect(),
        ..SortGraph::default()
    };
    graph.build_closure();
    graph
}

#[test]
fn lexemes_with_different_texts_never_overlap() {
    let graph = graph();
    assert!(!Unifier::new(&graph).unify(call(lexeme("main")), call(lexeme("foo"))));
    assert!(Unifier::new(&graph).unify(call(lexeme("main")), call(lexeme("main"))));
}

#[test]
fn a_lexeme_overlaps_a_variable_of_its_sort() {
    let graph = graph();
    let variable = Pattern::Variable {
        key: VariableKey {
            rule: 1,
            ordinal: 0,
        },
        sort: name_sort(),
    };
    assert!(Unifier::new(&graph).unify(call(lexeme("main")), call(variable)));
}
