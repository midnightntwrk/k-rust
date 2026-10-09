//! `overload` families in the overlap check (U10, KF-038; F2 clause 7c).
//!
//! K's overload axioms identify `expDot(inj(L), F)` with `inj(lValDot(L, F))`,
//! so applications of two members of one family unify when their arguments
//! do, and a rule on the general production can overlap a rule on the
//! specific one.

use krs_ir::{ApplicationRef, BuiltinSort, ItemKind, PackageId, StableItemId};
use krs_ir_levels::SemanticSortRef;

use super::{Pattern, SortGraph, Unifier, VariableKey};

fn item(name: &str, kind: ItemKind) -> StableItemId {
    StableItemId::new(
        PackageId::new("OVERLOAD", "overload", "0.1.0", "test").unwrap(),
        ["fixture"],
        name,
        kind,
        "",
    )
    .unwrap()
}

fn sort(name: &str) -> SemanticSortRef {
    SemanticSortRef::Declared(item(name, ItemKind::Sort))
}

fn id_sort() -> SemanticSortRef {
    SemanticSortRef::Builtin(BuiltinSort::Id)
}

/// `Exp`, `LVal: Exp`, `Int: Exp`, and `Id: LVal`, with the given overload edges.
fn graph(overloads: &[(&str, &str)]) -> SortGraph {
    let int = SemanticSortRef::Builtin(BuiltinSort::Int);
    let mut graph = SortGraph {
        candidates: [sort("Exp"), sort("LVal"), int.clone(), id_sort()]
            .into_iter()
            .collect(),
        parents: [
            (sort("LVal"), [sort("Exp")].into_iter().collect()),
            (int, [sort("Exp")].into_iter().collect()),
            (id_sort(), [sort("LVal")].into_iter().collect()),
        ]
        .into_iter()
        .collect(),
        overload_roots: overloads
            .iter()
            .map(|(member, target)| {
                (
                    item(member, ItemKind::Constructor),
                    item(target, ItemKind::Constructor),
                )
            })
            .collect(),
        ..SortGraph::default()
    };
    graph.build_closure();
    graph.resolve_overload_roots();
    graph
}

fn variable(rule: usize, ordinal: usize, sort: SemanticSortRef) -> Pattern {
    Pattern::Variable {
        key: VariableKey { rule, ordinal },
        sort,
    }
}

fn dot(constructor: &str, result: &str, base: Pattern, field: Pattern) -> Pattern {
    Pattern::Application {
        instance: Vec::new(),
        sort: sort(result),
        application: ApplicationRef::Declared(item(constructor, ItemKind::Constructor)),
        arguments: vec![base, field],
    }
}

#[test]
fn family_members_unify_on_compatible_arguments() {
    let graph = graph(&[("LvalDot", "Dot")]);
    let general = dot(
        "Dot",
        "Exp",
        variable(0, 0, sort("LVal")),
        variable(0, 1, id_sort()),
    );
    let specific = dot(
        "LvalDot",
        "LVal",
        variable(1, 0, sort("LVal")),
        variable(1, 1, id_sort()),
    );
    assert!(Unifier::new(&graph).unify(general, specific));
}

#[test]
fn family_members_with_disjoint_argument_sorts_do_not_unify() {
    let graph = graph(&[("LvalDot", "Dot")]);
    let general = dot(
        "Dot",
        "Exp",
        variable(0, 0, SemanticSortRef::Builtin(BuiltinSort::Int)),
        variable(0, 1, id_sort()),
    );
    let specific = dot(
        "LvalDot",
        "LVal",
        variable(1, 0, sort("LVal")),
        variable(1, 1, id_sort()),
    );
    assert!(!Unifier::new(&graph).unify(general, specific));
}

#[test]
fn productions_outside_a_family_never_unify() {
    let graph = graph(&[]);
    let general = dot(
        "Dot",
        "Exp",
        variable(0, 0, sort("LVal")),
        variable(0, 1, id_sort()),
    );
    let specific = dot(
        "LvalDot",
        "LVal",
        variable(1, 0, sort("LVal")),
        variable(1, 1, id_sort()),
    );
    assert!(!Unifier::new(&graph).unify(general, specific));
}

#[test]
fn a_chain_of_targets_is_one_family() {
    let graph = graph(&[("IdDot", "LvalDot"), ("LvalDot", "Dot")]);
    let root = ApplicationRef::Declared(item("Dot", ItemKind::Constructor));
    let leaf = ApplicationRef::Declared(item("IdDot", ItemKind::Constructor));
    let middle = ApplicationRef::Declared(item("LvalDot", ItemKind::Constructor));
    assert!(graph.same_head(&leaf, &root));
    assert!(graph.same_head(&middle, &leaf));
    let other = ApplicationRef::Declared(item("Other", ItemKind::Constructor));
    assert!(!graph.same_head(&leaf, &other));
}
