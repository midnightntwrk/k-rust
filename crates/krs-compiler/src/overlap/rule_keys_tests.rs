//! Unit tests for the F2 amendment's clauses implemented with rule keys (KF-012):
//! the guard procedure and computation-head completion.

use std::collections::BTreeSet;

use krs_ir::{ApplicationRef, BuiltinOperation, BuiltinSort, ItemKind, PackageId, StableItemId};
use krs_ir_levels::SemanticSortRef;

use super::{Pattern, SortGraph, Unifier, VariableKey};

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

fn variable(rule: usize, ordinal: usize, sort: BuiltinSort) -> Pattern {
    Pattern::Variable {
        key: VariableKey { rule, ordinal },
        sort: SemanticSortRef::Builtin(sort),
    }
}

fn int(value: &str) -> Pattern {
    Pattern::Token {
        sort: SemanticSortRef::Builtin(BuiltinSort::Int),
        value: value.into(),
    }
}

fn builtin(operation: BuiltinOperation, arguments: Vec<Pattern>) -> Pattern {
    Pattern::Application {
        instance: Vec::new(),
        sort: SemanticSortRef::Builtin(
            operation
                .result_sort()
                .builtin()
                .expect("these fixtures use operations with a fixed result sort"),
        ),
        application: ApplicationRef::Builtin(operation),
        arguments,
    }
}

fn constructor(name: &str, arguments: Vec<Pattern>) -> Pattern {
    Pattern::Application {
        instance: Vec::new(),
        sort: SemanticSortRef::Builtin(BuiltinSort::KSequence),
        application: ApplicationRef::Declared(
            StableItemId::new(
                PackageId::new("GUARDS", "guards", "0.1.0", "test").unwrap(),
                ["fixture"],
                name,
                ItemKind::Constructor,
                "",
            )
            .unwrap(),
        ),
        arguments,
    }
}

fn sequence(items: Vec<Pattern>) -> Pattern {
    Pattern::KSequence {
        sort: SemanticSortRef::Builtin(BuiltinSort::KSequence),
        items,
    }
}

/// Unifies `Div(lhs, rhs)` subjects of two rules, then asks whether the guards
/// are complementary under the resulting substitution.
fn separated(left_guard: &Pattern, right_guard: &Pattern) -> bool {
    let graph = graph();
    let mut unifier = Unifier::new(&graph);
    assert!(unifier.unify(
        constructor(
            "Div",
            vec![
                variable(0, 0, BuiltinSort::Int),
                variable(0, 1, BuiltinSort::Int)
            ]
        ),
        constructor(
            "Div",
            vec![
                variable(1, 0, BuiltinSort::Int),
                variable(1, 1, BuiltinSort::Int)
            ]
        ),
    ));
    unifier.guards_complementary(Some(left_guard), Some(right_guard))
}

#[test]
fn negated_guard_complements_its_operand_after_unification() {
    let left = builtin(
        BuiltinOperation::IntEqual,
        vec![variable(0, 1, BuiltinSort::Int), int("0")],
    );
    let right = builtin(
        BuiltinOperation::BoolNot,
        vec![builtin(
            BuiltinOperation::IntEqual,
            vec![variable(1, 1, BuiltinSort::Int), int("0")],
        )],
    );
    assert!(separated(&left, &right));
    assert!(separated(&right, &left));
}

#[test]
fn equality_and_disequality_on_identical_operands_are_complementary() {
    let eq = builtin(
        BuiltinOperation::IntEqual,
        vec![variable(0, 1, BuiltinSort::Int), int("0")],
    );
    let ne = builtin(
        BuiltinOperation::IntNotEqual,
        vec![int("0"), variable(1, 1, BuiltinSort::Int)],
    );
    assert!(separated(&eq, &ne));
    let bool_eq = builtin(
        BuiltinOperation::BoolEqual,
        vec![
            builtin(
                BuiltinOperation::IntLess,
                vec![variable(0, 0, BuiltinSort::Int), int("1")],
            ),
            Pattern::Token {
                sort: SemanticSortRef::Builtin(BuiltinSort::Bool),
                value: "true".into(),
            },
        ],
    );
    let bool_ne = builtin(
        BuiltinOperation::BoolNotEqual,
        vec![
            builtin(
                BuiltinOperation::IntLess,
                vec![variable(1, 0, BuiltinSort::Int), int("1")],
            ),
            Pattern::Token {
                sort: SemanticSortRef::Builtin(BuiltinSort::Bool),
                value: "true".into(),
            },
        ],
    );
    assert!(separated(&bool_eq, &bool_ne));
}

#[test]
fn ordering_guards_are_complementary_with_swapped_operands() {
    let less = builtin(
        BuiltinOperation::IntLess,
        vec![
            variable(0, 0, BuiltinSort::Int),
            variable(0, 1, BuiltinSort::Int),
        ],
    );
    let greater_equal = builtin(
        BuiltinOperation::IntGreaterEqual,
        vec![
            variable(1, 0, BuiltinSort::Int),
            variable(1, 1, BuiltinSort::Int),
        ],
    );
    let swapped_less_equal = builtin(
        BuiltinOperation::IntLessEqual,
        vec![
            variable(1, 1, BuiltinSort::Int),
            variable(1, 0, BuiltinSort::Int),
        ],
    );
    assert!(separated(&less, &greater_equal));
    assert!(separated(&less, &swapped_less_equal));
    let less_equal = builtin(
        BuiltinOperation::IntLessEqual,
        vec![
            variable(0, 0, BuiltinSort::Int),
            variable(0, 1, BuiltinSort::Int),
        ],
    );
    let greater = builtin(
        BuiltinOperation::IntGreater,
        vec![
            variable(1, 0, BuiltinSort::Int),
            variable(1, 1, BuiltinSort::Int),
        ],
    );
    assert!(separated(&less_equal, &greater));
}

#[test]
fn a_complementary_conjunct_inside_a_conjunction_separates() {
    let left = builtin(
        BuiltinOperation::BoolAnd,
        vec![
            builtin(
                BuiltinOperation::IntGreater,
                vec![variable(0, 0, BuiltinSort::Int), int("5")],
            ),
            builtin(
                BuiltinOperation::IntNotEqual,
                vec![variable(0, 1, BuiltinSort::Int), int("0")],
            ),
        ],
    );
    let right = builtin(
        BuiltinOperation::IntEqual,
        vec![variable(1, 1, BuiltinSort::Int), int("0")],
    );
    assert!(separated(&left, &right));
}

#[test]
fn non_complementary_guards_still_overlap() {
    // `lhs < rhs` and `lhs > rhs` exclude each other, but only through
    // reasoning the syntactic procedure does not do.
    let less = builtin(
        BuiltinOperation::IntLess,
        vec![
            variable(0, 0, BuiltinSort::Int),
            variable(0, 1, BuiltinSort::Int),
        ],
    );
    let greater = builtin(
        BuiltinOperation::IntGreater,
        vec![
            variable(1, 0, BuiltinSort::Int),
            variable(1, 1, BuiltinSort::Int),
        ],
    );
    assert!(!separated(&less, &greater));
    // Different operands are not complementary.
    let zero = builtin(
        BuiltinOperation::IntEqual,
        vec![variable(0, 1, BuiltinSort::Int), int("0")],
    );
    let one = builtin(
        BuiltinOperation::IntNotEqual,
        vec![variable(1, 1, BuiltinSort::Int), int("1")],
    );
    assert!(!separated(&zero, &one));
    // A guard on one rule alone separates nothing.
    let graph = graph();
    assert!(!Unifier::new(&graph).guards_complementary(Some(&zero), None));
}

/// Unifies a left rule matching the literal `subject` with a right rule
/// binding `X`, then asks whether the right rule's `guard` on `X` separates
/// the two (lesson 1.21's `0` and `X` with `X >=Int 10`).
fn literal_separated(subject: &str, guard: &Pattern) -> bool {
    let graph = graph();
    let mut unifier = Unifier::new(&graph);
    assert!(unifier.unify(
        sequence(vec![int(subject)]),
        sequence(vec![variable(1, 0, BuiltinSort::Int)]),
    ));
    unifier.guards_separate(None, Some(guard))
}

#[test]
fn a_ground_false_comparison_after_unification_separates() {
    let at_least_ten = builtin(
        BuiltinOperation::IntGreaterEqual,
        vec![variable(1, 0, BuiltinSort::Int), int("10")],
    );
    assert!(literal_separated("0", &at_least_ten));
    assert!(literal_separated("-3", &at_least_ten));
    assert!(!literal_separated("10", &at_least_ten));
    assert!(!literal_separated("12", &at_least_ten));
    for (operation, separated_at_zero) in [
        (BuiltinOperation::IntLess, false),
        (BuiltinOperation::IntLessEqual, false),
        (BuiltinOperation::IntGreater, true),
        (BuiltinOperation::IntEqual, true),
        (BuiltinOperation::IntNotEqual, false),
    ] {
        let guard = builtin(operation, vec![variable(1, 0, BuiltinSort::Int), int("1")]);
        assert_eq!(
            literal_separated("0", &guard),
            separated_at_zero,
            "{operation:?}"
        );
    }
    // A negation and a conjunct inside a conjunction are evaluated too.
    let below_ten = builtin(
        BuiltinOperation::IntLess,
        vec![variable(1, 0, BuiltinSort::Int), int("10")],
    );
    let not_below_ten = builtin(BuiltinOperation::BoolNot, vec![below_ten.clone()]);
    assert!(literal_separated("0", &not_below_ten));
    assert!(!literal_separated("0", &below_ten));
    let conjunction = builtin(
        BuiltinOperation::BoolAnd,
        vec![
            builtin(
                BuiltinOperation::IntNotEqual,
                vec![variable(1, 1, BuiltinSort::Int), int("0")],
            ),
            at_least_ten,
        ],
    );
    assert!(literal_separated("0", &conjunction));
}

#[test]
fn comparisons_that_stay_symbolic_or_exceed_i128_still_overlap() {
    // The guard's operand is a variable the other rule does not bind.
    let unbound = builtin(
        BuiltinOperation::IntGreaterEqual,
        vec![variable(1, 1, BuiltinSort::Int), int("10")],
    );
    assert!(!literal_separated("0", &unbound));
    // An arithmetic operand is not evaluated.
    let sum = builtin(
        BuiltinOperation::IntGreaterEqual,
        vec![
            builtin(
                BuiltinOperation::IntAdd,
                vec![variable(1, 0, BuiltinSort::Int), int("20")],
            ),
            int("10"),
        ],
    );
    assert!(!literal_separated("0", &sum));
    // A literal outside `i128` is left undecided.
    let huge = builtin(
        BuiltinOperation::IntGreaterEqual,
        vec![
            variable(1, 0, BuiltinSort::Int),
            int("1000000000000000000000000000000000000000000"),
        ],
    );
    assert!(!literal_separated("0", &huge));
}

#[test]
fn completed_heads_unify_with_longer_framed_sequences() {
    let graph = graph();
    // `Toss()` completed to `<k> Toss() ~> _ </k>` against `<k> Toss() ~> Next() ~> _ </k>`.
    let completed = sequence(vec![constructor("Toss", vec![])]);
    let longer = sequence(vec![
        constructor("Toss", vec![]),
        constructor("Next", vec![]),
    ]);
    assert!(Unifier::new(&graph).unify_clause(completed.clone(), true, longer.clone(), true));
    // A framed prefix also matches an exact sequence that extends it ...
    assert!(Unifier::new(&graph).unify_clause(longer.clone(), false, completed.clone(), true));
    // ... but not an exact sequence shorter than the prefix.
    assert!(!Unifier::new(&graph).unify_clause(completed.clone(), false, longer, true));
    let other = sequence(vec![constructor("Flip", vec![])]);
    assert!(!Unifier::new(&graph).unify_clause(completed, true, other, true));
}
