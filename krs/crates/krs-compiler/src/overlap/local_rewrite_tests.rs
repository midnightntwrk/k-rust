//! Local rewrites (K's `=>` below the root, U12, KF-011) in the overlap
//! check: a single-body clause unifies through its pre-pattern, the left
//! image of each `k::rewrite!`.

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
        SourceMapKey::new("sem.local-rewrite").unwrap(),
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
                PackageId::new("LOCAL", "local", "0.1.0", "test").unwrap(),
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

fn rewrite(from: SemanticTerm, to: SemanticTerm) -> SemanticTerm {
    SemanticTerm::rewrite(origin(), sort(), from, to).unwrap()
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
fn a_local_rewrite_unifies_as_its_left_side() {
    // `Assign(k::rewrite!(Red() => Blue()), v)` matches what `Assign(Red(), v)`
    // matches: its right side `Blue()` is the post-state, never matched.
    let local = constructor(
        "Assign",
        vec![
            rewrite(
                constructor("Red", Vec::new()),
                constructor("Blue", Vec::new()),
            ),
            variable("v"),
        ],
    );
    let red = constructor(
        "Assign",
        vec![constructor("Red", Vec::new()), variable("w")],
    );
    let blue = constructor(
        "Assign",
        vec![constructor("Blue", Vec::new()), variable("w")],
    );
    assert!(overlap(&local, &red));
    assert!(!overlap(&local, &blue));
}

#[test]
fn two_local_rewrites_overlap_on_their_left_images() {
    // `Pair(k::rewrite!(a => Red()), b)` and `Pair(c, k::rewrite!(Blue() => d))`
    // both match `Pair(x, Blue())`.
    let left = constructor(
        "Pair",
        vec![
            rewrite(variable("a"), constructor("Red", Vec::new())),
            variable("b"),
        ],
    );
    let right = constructor(
        "Pair",
        vec![
            variable("c"),
            rewrite(constructor("Blue", Vec::new()), variable("d")),
        ],
    );
    let red_right = constructor(
        "Pair",
        vec![
            variable("e"),
            rewrite(constructor("Red", Vec::new()), variable("f")),
        ],
    );
    assert!(overlap(&left, &right));
    assert!(overlap(&left, &red_right));
    let blue_left = constructor(
        "Pair",
        vec![
            rewrite(constructor("Blue", Vec::new()), variable("g")),
            variable("h"),
        ],
    );
    let red_left = constructor(
        "Pair",
        vec![
            rewrite(constructor("Red", Vec::new()), variable("i")),
            variable("j"),
        ],
    );
    assert!(!overlap(&blue_left, &red_left));
}
