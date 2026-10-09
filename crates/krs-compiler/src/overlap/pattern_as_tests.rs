//! `name @ pattern` (K's `#as`) in the overlap check (U11, KF-029; F2
//! clause 7b): an alias unifies as its subpattern, and the alias is the
//! term the subpattern matched.

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
        SourceMapKey::new("sem.pattern-as").unwrap(),
        krs_ir::testing::authored(0, 1),
    )
}

fn id(name: &str) -> SemanticId {
    SemanticId::new(name.to_owned()).unwrap()
}

fn sort() -> SemanticSortRef {
    SemanticSortRef::Builtin(BuiltinSort::KSequence)
}

fn variable(name: &str) -> SemanticTerm {
    SemanticTerm::variable(origin(), sort(), id(name))
}

fn constructor(name: &str, arguments: Vec<SemanticTerm>) -> SemanticTerm {
    SemanticTerm::application(
        origin(),
        sort(),
        ApplicationRef::Declared(
            StableItemId::new(
                PackageId::new("ALIASES", "aliases", "0.1.0", "test").unwrap(),
                ["fixture"],
                name,
                ItemKind::Constructor,
                "",
            )
            .unwrap(),
        ),
        arguments,
    )
}

fn alias(name: &str, pattern: SemanticTerm) -> SemanticTerm {
    SemanticTerm::pattern_as(origin(), sort(), id(name), pattern)
}

fn overlap(left: &SemanticTerm, right: &SemanticTerm) -> bool {
    let k = id("k");
    let view = |before| ClauseView {
        cell: &k,
        before,
        completed_head: false,
        framed: false,
        unconstrained: false,
    };
    clauses_overlap(&[view(left)], None, &[view(right)], None, &graph())
}

#[test]
fn an_alias_unifies_as_its_subpattern() {
    // `Dup(p @ Pair(a, b))`
    let aliased = constructor(
        "Dup",
        vec![alias(
            "p",
            constructor("Pair", vec![variable("a"), variable("b")]),
        )],
    );
    let pair = constructor(
        "Dup",
        vec![constructor("Pair", vec![variable("x"), variable("y")])],
    );
    let red = constructor("Dup", vec![constructor("Red", Vec::new())]);
    assert!(overlap(&aliased, &pair));
    assert!(!overlap(&aliased, &red));
}

#[test]
fn an_alias_is_the_term_its_subpattern_matched() {
    // `Two(p @ Red(), p)` binds `p` to `Red()` in both places, so it
    // cannot match `Two(Red(), Blue())` but matches `Two(Red(), Red())`.
    let aliased = constructor(
        "Two",
        vec![alias("p", constructor("Red", Vec::new())), variable("p")],
    );
    let different = constructor(
        "Two",
        vec![
            constructor("Red", Vec::new()),
            constructor("Blue", Vec::new()),
        ],
    );
    let same = constructor(
        "Two",
        vec![
            constructor("Red", Vec::new()),
            constructor("Red", Vec::new()),
        ],
    );
    assert!(!overlap(&aliased, &different));
    assert!(overlap(&aliased, &same));
}
