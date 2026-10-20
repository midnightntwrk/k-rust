//! The guard procedure's reading of every Bool-valued builtin (F2 amendment,
//! clause 4, CS-11-3). Two guards separate two rules when no valuation of the
//! unified rule variables makes both true. The catalog states what each
//! Bool-valued builtin means as a conjunct ([`krs_ir::GuardMeaning`]): `=/=`
//! is the negation of `==` for Int, Bool, String, K and Float, `xorBool` is
//! `=/=Bool`, and the Int and String orders are strict total orders, so a
//! comparison and its converse-negation are complements. A conjunct whose
//! operands unification makes literals, or free constructor terms for `==K`,
//! has a value, and a false one separates the rules.

use std::collections::BTreeSet;

use krs_ir::{ApplicationRef, BuiltinOperation, BuiltinSort, ItemKind, PackageId, StableItemId};
use krs_ir_levels::SemanticSortRef;

use super::{Pattern, SortGraph, Unifier, VariableKey};

fn constructor_id(name: &str) -> StableItemId {
    StableItemId::new(
        PackageId::new("GUARDS", "guards", "0.1.0", "test").unwrap(),
        ["fixture"],
        name,
        ItemKind::Constructor,
        "",
    )
    .unwrap()
}

/// The builtin sorts, with `Pair`, `Wrap`, `Name`, `Flag`, `Cons` and
/// `Null` free constructors; `Lazy` is a constructor whose applications are
/// not free (an anywhere rule's head, say).
fn graph() -> SortGraph {
    let mut graph = SortGraph {
        candidates: BuiltinSort::ALL
            .into_iter()
            .map(SemanticSortRef::Builtin)
            .collect::<BTreeSet<_>>(),
        free_constructors: ["Pair", "Wrap", "Name", "Flag", "Cons", "Null"]
            .into_iter()
            .map(constructor_id)
            .collect(),
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

fn token(sort: BuiltinSort, value: &str) -> Pattern {
    Pattern::Token {
        sort: SemanticSortRef::Builtin(sort),
        value: value.into(),
    }
}

fn string(value: &str) -> Pattern {
    token(BuiltinSort::String, &format!("\"{value}\""))
}

fn int(value: &str) -> Pattern {
    token(BuiltinSort::Int, value)
}

fn boolean(value: bool) -> Pattern {
    token(BuiltinSort::Bool, if value { "true" } else { "false" })
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

fn not(operand: Pattern) -> Pattern {
    builtin(BuiltinOperation::BoolNot, vec![operand])
}

fn constructor(name: &str, arguments: Vec<Pattern>) -> Pattern {
    Pattern::Application {
        instance: Vec::new(),
        sort: SemanticSortRef::Builtin(BuiltinSort::KSequence),
        application: ApplicationRef::Declared(constructor_id(name)),
        arguments,
    }
}

/// Unifies `Pair(a0, b0)` with `Pair(a1, b1)` over variables of `sort`, then
/// asks whether `left` (over `a0`, `b0`) and `right` (over `a1`, `b1`)
/// separate the two rules.
fn pair_separated(sort: BuiltinSort, left: &Pattern, right: &Pattern) -> bool {
    let graph = graph();
    let mut unifier = Unifier::new(&graph);
    assert!(unifier.unify(
        constructor("Pair", vec![variable(0, 0, sort), variable(0, 1, sort)]),
        constructor("Pair", vec![variable(1, 0, sort), variable(1, 1, sort)]),
    ));
    unifier.guards_separate(Some(left), Some(right))
}

/// `op(a, b)` over the left rule's variables and the right rule's.
fn both(
    left: BuiltinOperation,
    left_swapped: bool,
    right: BuiltinOperation,
    right_swapped: bool,
    sort: BuiltinSort,
) -> (Pattern, Pattern) {
    let operands = |rule: usize, swapped: bool| {
        let (a, b) = (variable(rule, 0, sort), variable(rule, 1, sort));
        if swapped { vec![b, a] } else { vec![a, b] }
    };
    (
        builtin(left, operands(0, left_swapped)),
        builtin(right, operands(1, right_swapped)),
    )
}

fn complementary(
    left: BuiltinOperation,
    left_swapped: bool,
    right: BuiltinOperation,
    right_swapped: bool,
    sort: BuiltinSort,
) -> bool {
    let (left, right) = both(left, left_swapped, right, right_swapped, sort);
    let forward = pair_separated(sort, &left, &right);
    assert_eq!(forward, pair_separated(sort, &right, &left));
    forward
}

#[test]
fn term_equality_and_inequality_are_complementary() {
    use BuiltinOperation::{KEqualEq, KEqualNe};
    let k = BuiltinSort::KSequence;
    assert!(complementary(KEqualEq, false, KEqualNe, false, k));
    // `==K` is symmetric.
    assert!(complementary(KEqualEq, false, KEqualNe, true, k));
    assert!(!complementary(KEqualEq, false, KEqualEq, true, k));
    assert!(!complementary(KEqualNe, false, KEqualNe, false, k));
    // `bool::not` folds into the polarity: `notBool (a ==K b)` is `a =/=K b`,
    // the complement of `a ==K b` and not of `a =/=K b`.
    let (eq, ne) = both(KEqualEq, false, KEqualNe, false, k);
    let (_, right_eq) = both(KEqualEq, false, KEqualEq, false, k);
    assert!(pair_separated(k, &not(eq.clone()), &right_eq));
    assert!(!pair_separated(k, &not(eq), &ne));
}

#[test]
fn string_equalities_and_orders_are_complementary() {
    use BuiltinOperation::{
        StringEqual, StringGreater, StringGreaterEqual, StringLess, StringLessEqual, StringNotEqual,
    };
    let s = BuiltinSort::String;
    assert!(complementary(StringEqual, false, StringNotEqual, false, s));
    assert!(complementary(StringEqual, false, StringNotEqual, true, s));
    assert!(complementary(
        StringLess,
        false,
        StringGreaterEqual,
        false,
        s
    ));
    assert!(complementary(StringLess, false, StringLessEqual, true, s));
    assert!(complementary(
        StringLessEqual,
        false,
        StringGreater,
        false,
        s
    ));
    assert!(complementary(
        StringGreater,
        false,
        StringGreaterEqual,
        true,
        s
    ));
    // An order is not symmetric, and `<` against `>` is disjoint but not
    // complementary, as for Int.
    assert!(!complementary(
        StringLess,
        false,
        StringGreaterEqual,
        true,
        s
    ));
    assert!(!complementary(StringLess, false, StringGreater, false, s));
}

#[test]
fn bool_exclusive_or_is_the_negation_of_bool_equality() {
    use BuiltinOperation::{BoolEqual, BoolNotEqual, BoolXor};
    let b = BuiltinSort::Bool;
    assert!(complementary(BoolXor, false, BoolEqual, false, b));
    assert!(complementary(BoolXor, false, BoolEqual, true, b));
    assert!(!complementary(BoolXor, false, BoolNotEqual, false, b));
}

#[test]
fn float_equality_complements_its_negation_but_float_order_does_not() {
    use BuiltinOperation::{
        FloatEqual, FloatGreater, FloatGreaterEqual, FloatLess, FloatLessEqual, FloatNotEqual,
    };
    let f = BuiltinSort::Float;
    assert!(complementary(FloatEqual, false, FloatNotEqual, false, f));
    // `a >=Float b` is not `notBool (a <Float b)`: with a NaN operand both
    // comparisons are false, so `notBool (a <Float b)` and
    // `notBool (a >=Float b)` hold together. The orders are opaque, so the
    // negations are not separated, and neither (conservatively) are the
    // comparisons themselves.
    let (less, greater_equal) = both(FloatLess, false, FloatGreaterEqual, false, f);
    assert!(!pair_separated(f, &not(less), &not(greater_equal)));
    assert!(!complementary(
        FloatLess,
        false,
        FloatGreaterEqual,
        false,
        f
    ));
    assert!(!complementary(
        FloatLessEqual,
        false,
        FloatGreater,
        false,
        f
    ));
    // A negated Float comparison still complements the comparison itself.
    let (less, right_less) = both(FloatLess, false, FloatLess, false, f);
    assert!(pair_separated(f, &not(less), &right_less));
}

#[test]
fn int_complements_are_unchanged() {
    use BuiltinOperation::{
        IntEqual, IntGreater, IntGreaterEqual, IntLess, IntLessEqual, IntNotEqual,
    };
    let i = BuiltinSort::Int;
    assert!(complementary(IntEqual, false, IntNotEqual, true, i));
    assert!(complementary(IntLess, false, IntGreaterEqual, false, i));
    assert!(complementary(IntLessEqual, false, IntGreater, false, i));
    assert!(!complementary(IntLess, false, IntGreater, false, i));
}

/// Unifies a left rule on `subject` with a right rule on `binder`, then asks
/// whether the right rule's `guard` separates the two.
fn subject_separated(subject: Pattern, binder: Pattern, guard: &Pattern) -> bool {
    let graph = graph();
    let mut unifier = Unifier::new(&graph);
    assert!(unifier.unify(subject, binder));
    unifier.guards_separate(None, Some(guard))
}

fn name_separated(subject: &str, guard: &Pattern) -> bool {
    subject_separated(
        constructor("Name", vec![string(subject)]),
        constructor("Name", vec![variable(1, 0, BuiltinSort::String)]),
        guard,
    )
}

#[test]
fn a_string_comparison_on_literals_after_unification_is_evaluated() {
    let s = variable(1, 0, BuiltinSort::String);
    let is_a = builtin(BuiltinOperation::StringEqual, vec![s.clone(), string("a")]);
    assert!(name_separated("b", &is_a));
    assert!(!name_separated("a", &is_a));
    // Escapes are decoded: `"\x61"` is `"a"`.
    assert!(!name_separated("\\x61", &is_a));
    assert!(name_separated("\\x62", &is_a));
    let not_a = builtin(
        BuiltinOperation::StringNotEqual,
        vec![string("a"), s.clone()],
    );
    assert!(name_separated("a", &not_a));
    assert!(!name_separated("b", &not_a));
    // `<String` is lexicographic on code points.
    let below_b = builtin(BuiltinOperation::StringLess, vec![s.clone(), string("b")]);
    assert!(!name_separated("a", &below_b));
    assert!(!name_separated("ab", &below_b));
    assert!(name_separated("b", &below_b));
    assert!(name_separated("ba", &below_b));
    assert!(name_separated("\u{e9}", &below_b));
    let at_least_b = builtin(BuiltinOperation::StringGreaterEqual, vec![s, string("b")]);
    assert!(name_separated("a", &at_least_b));
    assert!(!name_separated("b", &at_least_b));
}

fn flag_separated(subject: bool, guard: &Pattern) -> bool {
    subject_separated(
        constructor("Flag", vec![boolean(subject)]),
        constructor("Flag", vec![variable(1, 0, BuiltinSort::Bool)]),
        guard,
    )
}

#[test]
fn a_bool_guard_that_unification_makes_a_literal_is_evaluated() {
    let b = variable(1, 0, BuiltinSort::Bool);
    assert!(flag_separated(false, &b));
    assert!(!flag_separated(true, &b));
    assert!(flag_separated(true, &not(b.clone())));
    assert!(!flag_separated(false, &not(b.clone())));
    // Connectives are decided by an operand that fixes them.
    let or_false = builtin(BuiltinOperation::BoolOr, vec![b.clone(), boolean(false)]);
    assert!(flag_separated(false, &or_false));
    assert!(!flag_separated(true, &or_false));
    let implies_false = builtin(
        BuiltinOperation::BoolImplies,
        vec![b.clone(), boolean(false)],
    );
    assert!(flag_separated(true, &implies_false));
    assert!(!flag_separated(false, &implies_false));
    let xor_true = builtin(BuiltinOperation::BoolXor, vec![b, boolean(true)]);
    assert!(flag_separated(true, &xor_true));
    assert!(!flag_separated(false, &xor_true));
}

fn wrap_separated(subject: Pattern, guard: &Pattern) -> bool {
    subject_separated(
        constructor("Wrap", vec![subject]),
        constructor("Wrap", vec![variable(1, 0, BuiltinSort::KSequence)]),
        guard,
    )
}

#[test]
fn term_equality_on_free_constructor_terms_is_evaluated() {
    let v = variable(1, 0, BuiltinSort::KSequence);
    let null = || constructor("Null", Vec::new());
    let cons = |head: &str| constructor("Cons", vec![int(head)]);
    let is_null = builtin(BuiltinOperation::KEqualEq, vec![v.clone(), null()]);
    let not_null = builtin(BuiltinOperation::KEqualNe, vec![v.clone(), null()]);
    assert!(wrap_separated(cons("1"), &is_null));
    assert!(!wrap_separated(null(), &is_null));
    assert!(wrap_separated(null(), &not_null));
    assert!(!wrap_separated(cons("1"), &not_null));
    // Arguments are compared by value.
    let is_one = builtin(BuiltinOperation::KEqualEq, vec![v.clone(), cons("1")]);
    assert!(wrap_separated(cons("2"), &is_one));
    assert!(!wrap_separated(cons("+1"), &is_one));
    // Distinct heads are unequal whatever their arguments are.
    let unbound = constructor("Cons", vec![variable(0, 5, BuiltinSort::Int)]);
    assert!(wrap_separated(unbound.clone(), &is_null));
    assert!(!wrap_separated(unbound, &is_one));
    // A one-item K sequence is its item.
    let sequence = Pattern::KSequence {
        sort: SemanticSortRef::Builtin(BuiltinSort::KSequence),
        items: vec![cons("1")],
    };
    assert!(wrap_separated(sequence, &is_null));
}

#[test]
fn term_equality_with_functions_or_unfree_constructors_stays_undecided() {
    let v = variable(1, 0, BuiltinSort::KSequence);
    // An anywhere rule may rewrite `Lazy()` to `Cons(1)`.
    let lazy = builtin(
        BuiltinOperation::KEqualEq,
        vec![v.clone(), constructor("Lazy", Vec::new())],
    );
    assert!(!wrap_separated(constructor("Cons", vec![int("1")]), &lazy));
    // A function application's value is not its syntax.
    let sum = builtin(
        BuiltinOperation::KEqualEq,
        vec![
            v,
            constructor(
                "Cons",
                vec![builtin(BuiltinOperation::IntAdd, vec![int("0"), int("1")])],
            ),
        ],
    );
    assert!(!wrap_separated(constructor("Cons", vec![int("2")]), &sum));
}
