//! `A | B` (K's `#Or`) in the overlap check (U11, KF-030; F2 clauses 7b
//! and 8): an or-pattern contributes the cross product of its alternatives,
//! and two alternatives that bind variables must not match one term with
//! different bindings.

use std::collections::BTreeSet;

use krs_ir::{
    ApplicationRef, AtLeastTwo, BuiltinSort, ItemKind, NodeOrigin, PackageId, SemanticId,
    SourceMapKey, StableItemId,
};
use krs_ir_levels::{SemanticSortRef, SemanticTerm};

use super::{ClauseView, SortGraph, alternatives_ambiguous, clauses_overlap, render_alternative};

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
        SourceMapKey::new("sem.pattern-or").unwrap(),
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
                PackageId::new("ALTERNATIVES", "alternatives", "0.1.0", "test").unwrap(),
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

fn unit(name: &str) -> SemanticTerm {
    constructor(name, Vec::new())
}

fn or(alternatives: Vec<SemanticTerm>) -> SemanticTerm {
    SemanticTerm::pattern_or(
        origin(),
        sort(),
        AtLeastTwo::try_from(alternatives).unwrap(),
    )
}

fn overlap(left: &SemanticTerm, right: &SemanticTerm) -> bool {
    let k = id("k");
    let view = |before| ClauseView {
        cell: &k,
        before,
        completed_head: false,
        framed: false,
    };
    clauses_overlap(&[view(left)], None, &[view(right)], None, &graph())
}

fn ambiguous(first: &SemanticTerm, second: &SemanticTerm, outer: &[&str]) -> bool {
    let outer = outer.iter().map(|name| id(name)).collect::<BTreeSet<_>>();
    alternatives_ambiguous(first, second, &outer, &graph())
}

#[test]
fn an_or_pattern_overlaps_a_rule_matching_any_alternative() {
    // `Color(Red() | Green() | Blue())`
    let rgb = constructor(
        "Color",
        vec![or(vec![unit("Red"), unit("Green"), unit("Blue")])],
    );
    assert!(overlap(&rgb, &constructor("Color", vec![unit("Green")])));
    assert!(overlap(&rgb, &constructor("Color", vec![variable("c")])));
    assert!(!overlap(&rgb, &constructor("Color", vec![unit("Black")])));
    // Two or-patterns overlap when some pair of their alternatives does.
    let warm = constructor("Color", vec![or(vec![unit("Red"), unit("Orange")])]);
    let cool = constructor("Color", vec![or(vec![unit("Blue"), unit("Green")])]);
    assert!(overlap(&rgb, &warm));
    assert!(!overlap(&warm, &cool));
}

#[test]
fn alternatives_that_can_bind_differently_are_ambiguous() {
    // `Pair(x, y) | Pair(y, x)` matches `Pair(1, 2)` with x = 1 or x = 2.
    let swapped = (
        constructor("Pair", vec![variable("x"), variable("y")]),
        constructor("Pair", vec![variable("y"), variable("x")]),
    );
    assert!(ambiguous(&swapped.0, &swapped.1, &[]));
    // `Pair(x, Red()) | Pair(x, Green())` never matches one term twice.
    let disjoint = (
        constructor("Pair", vec![variable("x"), unit("Red")]),
        constructor("Pair", vec![variable("x"), unit("Green")]),
    );
    assert!(!ambiguous(&disjoint.0, &disjoint.1, &[]));
    // Alternatives binding no variables may overlap freely.
    assert!(!ambiguous(&unit("Red"), &unit("Red"), &[]));
    // Overlapping alternatives that bind a name alike are not ambiguous.
    let same = (
        constructor("Wrap", vec![variable("x")]),
        constructor("Wrap", vec![variable("x")]),
    );
    assert!(!ambiguous(&same.0, &same.1, &[]));
}

#[test]
fn a_name_bound_outside_the_or_pattern_is_one_value() {
    // In `F(x, Pair(x, _) | Pair(_, x))` the outer `x` fixes the binding.
    let first = constructor("Pair", vec![variable("x"), variable("_0")]);
    let second = constructor("Pair", vec![variable("_1"), variable("x")]);
    assert!(ambiguous(&first, &second, &[]));
    assert!(!ambiguous(&first, &second, &["x"]));
}

#[test]
fn alternatives_render_as_rust_patterns() {
    let pair = constructor("Pair", vec![variable("x"), unit("Red")]);
    assert_eq!(render_alternative(&pair), "Pair(x, Red())");
}
