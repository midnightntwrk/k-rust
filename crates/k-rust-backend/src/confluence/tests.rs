//! Unit tests of the critical-pair unifier (one per row of the overlap inventory), and of the
//! check on small definitions.

use k_rust_kore::kore::parser::{parse_definition, parse_pattern};
use std::sync::Arc;

use super::{
    PollBudgetRecord, UnjoinedReason, switches,
    unify::{Families, Unifier, UnresolvedShape},
};
use crate::{
    definition::BackendDefinition,
    substitution::{Substitution, substitute},
    term::Term,
};

/// Sorts `C < A, B < T` and `D < A, B` (so `A` and `B` have two maximal common subsorts), the
/// naturals with a declared function `f` and an equation head `w`, and an overload family:
/// `consE` and `nilE` over `consN` and `nilN`, with `N < E` and `Ns < Es`.
const SIGNATURE: &str = r#"
    hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
    sort SortT{} []
    sort SortA{} []
    sort SortB{} []
    sort SortC{} []
    sort SortD{} []
    sort SortU{} []
    sort SortV{} []
    sort SortNat{} []
    sort SortS{} []
    sort SortE{} []
    sort SortN{} []
    sort SortEs{} []
    sort SortNs{} []
    symbol inj{From, To}(From) : To [sortInjection{}(), injective{}()]
    axiom{R} \exists{R}(V:SortT{}, \equals{SortT{}, R}(V:SortT{}, inj{SortA{}, SortT{}}(F:SortA{}))) [subsort{SortA{}, SortT{}}()]
    axiom{R} \exists{R}(V:SortT{}, \equals{SortT{}, R}(V:SortT{}, inj{SortB{}, SortT{}}(F:SortB{}))) [subsort{SortB{}, SortT{}}()]
    axiom{R} \exists{R}(V:SortA{}, \equals{SortA{}, R}(V:SortA{}, inj{SortC{}, SortA{}}(F:SortC{}))) [subsort{SortC{}, SortA{}}()]
    axiom{R} \exists{R}(V:SortB{}, \equals{SortB{}, R}(V:SortB{}, inj{SortC{}, SortB{}}(F:SortC{}))) [subsort{SortC{}, SortB{}}()]
    axiom{R} \exists{R}(V:SortA{}, \equals{SortA{}, R}(V:SortA{}, inj{SortD{}, SortA{}}(F:SortD{}))) [subsort{SortD{}, SortA{}}()]
    axiom{R} \exists{R}(V:SortB{}, \equals{SortB{}, R}(V:SortB{}, inj{SortD{}, SortB{}}(F:SortD{}))) [subsort{SortD{}, SortB{}}()]
    axiom{R} \exists{R}(V:SortE{}, \equals{SortE{}, R}(V:SortE{}, inj{SortN{}, SortE{}}(F:SortN{}))) [subsort{SortN{}, SortE{}}()]
    axiom{R} \exists{R}(V:SortEs{}, \equals{SortEs{}, R}(V:SortEs{}, inj{SortNs{}, SortEs{}}(F:SortNs{}))) [subsort{SortNs{}, SortEs{}}()]
    symbol a0{}() : SortA{} [constructor{}(), functional{}(), injective{}()]
    symbol b0{}() : SortB{} [constructor{}(), functional{}(), injective{}()]
    symbol c0{}() : SortC{} [constructor{}(), functional{}(), injective{}()]
    symbol d0{}() : SortD{} [constructor{}(), functional{}(), injective{}()]
    symbol u0{}() : SortU{} [constructor{}(), functional{}(), injective{}()]
    symbol pa{}(SortA{}) : SortT{} [constructor{}(), functional{}(), injective{}()]
    symbol z{}() : SortNat{} [constructor{}(), functional{}(), injective{}()]
    symbol s{}(SortNat{}) : SortNat{} [constructor{}(), functional{}(), injective{}()]
    symbol k{}(SortNat{}, SortNat{}) : SortNat{} [constructor{}(), functional{}(), injective{}()]
    symbol f{}(SortNat{}) : SortNat{} [function{}()]
    symbol w{}(SortNat{}) : SortS{} [anywhere{}()]
    symbol m{}(SortNat{}) : SortS{} [constructor{}(), functional{}(), injective{}()]
    symbol n0{}() : SortN{} [constructor{}(), functional{}(), injective{}()]
    symbol e0{}() : SortE{} [constructor{}(), functional{}(), injective{}()]
    symbol nilN{}() : SortNs{} [constructor{}(), functional{}(), injective{}()]
    symbol consN{}(SortN{}, SortNs{}) : SortNs{} [constructor{}(), functional{}(), injective{}()]
    symbol nilE{}() : SortEs{} [anywhere{}(), functional{}()]
    symbol consE{}(SortE{}, SortEs{}) : SortEs{} [anywhere{}(), functional{}()]
    axiom{R} \equals{SortEs{}, R}(
        consE{}(inj{SortN{}, SortE{}}(K0:SortN{}), inj{SortNs{}, SortEs{}}(K1:SortNs{})),
        inj{SortNs{}, SortEs{}}(consN{}(K0:SortN{}, K1:SortNs{}))
    ) [symbol-overload{}(consE{}(), consN{}())]
    axiom{R} \equals{SortEs{}, R}(nilE{}(), inj{SortNs{}, SortEs{}}(nilN{}()))
        [symbol-overload{}(nilE{}(), nilN{}())]
"#;

const COLLECTIONS: &str = r#"
    sort SortElement{} [hasDomainValues{}()]
    sort SortKey{} [hasDomainValues{}()]
    sort SortValue{} [hasDomainValues{}()]
    hooked-sort SortList{}
        [hook{}("LIST.List"), unit{}(listUnit{}()), element{}(listItem{}()), concat{}(listConcat{}())]
    hooked-sort SortMap{}
        [hook{}("MAP.Map"), unit{}(mapUnit{}()), element{}(mapItem{}()), concat{}(mapConcat{}())]
    hooked-symbol listUnit{}() : SortList{} [function{}(), total{}(), hook{}("LIST.unit")]
    hooked-symbol listItem{}(SortElement{}) : SortList{} [function{}(), total{}(), hook{}("LIST.element")]
    hooked-symbol listConcat{}(SortList{}, SortList{}) : SortList{} [function{}(), hook{}("LIST.concat"), assoc{}()]
    hooked-symbol mapUnit{}() : SortMap{} [function{}(), total{}(), hook{}("MAP.unit")]
    hooked-symbol mapItem{}(SortKey{}, SortValue{}) : SortMap{} [function{}(), total{}(), hook{}("MAP.element")]
    hooked-symbol mapConcat{}(SortMap{}, SortMap{}) : SortMap{} [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
"#;

fn definition(extra: &str) -> BackendDefinition {
    let source = format!("[] module MAIN {SIGNATURE} {COLLECTIONS} {extra} endmodule []");
    let syntax = parse_definition(&source).expect("the definition parses");
    internalized(&syntax)
}

/// `syntax` internalized at module `MAIN`. No fixture of these tests is meant to stop the check:
/// each of their conditions is decided within the budget of polls, and none needs more stack
/// than a test thread has, so the check records no stop.
fn internalized(syntax: &k_rust_kore::kore::ast::Definition) -> BackendDefinition {
    let definition =
        BackendDefinition::internalize(syntax, "MAIN").expect("the definition internalizes");
    let counts = definition.value_claims().counts();
    assert_eq!(
        (counts.condition_budget_stops, counts.condition_stack_stops),
        (0, 0),
        "the check stopped: {counts:?}"
    );
    definition
}

fn term(definition: &BackendDefinition, source: &str) -> Term {
    definition
        .internalize_term(&parse_pattern(source).expect("the term parses"), &[])
        .expect("the term internalizes")
}

/// Unify two terms of `definition`, with every overload family confluent when `lifting`.
fn unify(
    definition: &BackendDefinition,
    lifting: bool,
    left: &str,
    right: &str,
) -> Result<Vec<Substitution>, UnresolvedShape> {
    let mut families = Families::of(definition);
    for family in 0..families.len() {
        families.set_confluent(family);
    }
    let mut fresh = 0;
    let nothing_normal = |_: &Term| false;
    Unifier {
        definition,
        families: &families,
        lifting,
        known_normal: &nothing_normal,
        fresh: &mut fresh,
        branches: 0,
        defer: false,
    }
    .unify(&term(definition, left), &term(definition, right))
}

/// Every unifier makes the two terms syntactically equal (with injections composed).
fn assert_unifies(
    definition: &BackendDefinition,
    left: &str,
    right: &str,
    unifiers: &[Substitution],
) {
    let (left, right) = (term(definition, left), term(definition, right));
    for unifier in unifiers {
        assert_eq!(
            substitute(&left, unifier),
            substitute(&right, unifier),
            "{unifier:?}"
        );
    }
}

fn binding<'s>(unifier: &'s Substitution, name: &str) -> Option<&'s Term> {
    unifier
        .iter()
        .find(|(variable, _)| variable.name.as_ref() == name)
        .map(|(_, value)| value)
}

#[test]
fn a_variable_binds_a_term_of_its_sort_or_of_a_subsort_through_an_injection() {
    let definition = definition("");
    let unifiers = unify(&definition, false, "X:SortNat{}", "s{}(Y:SortNat{})").expect("decided");
    assert_eq!(unifiers.len(), 1);
    assert_unifies(&definition, "X:SortNat{}", "s{}(Y:SortNat{})", &unifiers);
    let unifiers = unify(&definition, false, "X:SortA{}", "c0{}()").expect("decided");
    assert_eq!(
        binding(&unifiers[0], "X"),
        Some(&term(&definition, "inj{SortC{}, SortA{}}(c0{}())"))
    );
}

#[test]
fn a_variable_occurring_in_its_value_has_no_unifier() {
    let definition = definition("");
    assert_eq!(
        unify(&definition, false, "X:SortNat{}", "s{}(X:SortNat{})"),
        Ok(Vec::new())
    );
}

#[test]
fn two_variables_of_incomparable_sorts_meet_in_each_maximal_common_subsort() {
    let definition = definition("");
    let unifiers = unify(&definition, false, "X:SortA{}", "Y:SortB{}").expect("decided");
    // `C` and `D` are both maximal below `A` and `B`.
    assert_eq!(unifiers.len(), 2);
    assert_unifies(
        &definition,
        "inj{SortA{}, SortT{}}(X:SortA{})",
        "inj{SortB{}, SortT{}}(Y:SortB{})",
        &unifiers,
    );
    // `U` is below nothing but itself: no common value.
    assert_eq!(
        unify(&definition, false, "X:SortA{}", "Y:SortU{}"),
        Ok(Vec::new())
    );
}

#[test]
fn a_conjunction_unifies_both_conjuncts() {
    let definition = definition("");
    let unifiers = unify(
        &definition,
        false,
        r"\and{SortNat{}}(s{}(X:SortNat{}), Y:SortNat{})",
        "s{}(z{}())",
    )
    .expect("decided");
    assert_eq!(unifiers.len(), 1);
    assert_eq!(
        binding(&unifiers[0], "Y"),
        Some(&term(&definition, "s{}(z{}())"))
    );
    assert_eq!(
        binding(&unifiers[0], "X"),
        Some(&term(&definition, "z{}()"))
    );
}

#[test]
fn domain_values_unify_only_when_equal() {
    let definition = definition("");
    assert_eq!(
        unify(
            &definition,
            false,
            r#"\dv{SortInt{}}("1")"#,
            r#"\dv{SortInt{}}("1")"#
        )
        .map(|unifiers| unifiers.len()),
        Ok(1)
    );
    assert_eq!(
        unify(
            &definition,
            false,
            r#"\dv{SortInt{}}("1")"#,
            r#"\dv{SortInt{}}("2")"#
        ),
        Ok(Vec::new())
    );
}

#[test]
fn different_free_roots_clash_and_one_root_decomposes() {
    let definition = definition("");
    assert_eq!(
        unify(&definition, false, "s{}(X:SortNat{})", "z{}()"),
        Ok(Vec::new())
    );
    assert_eq!(
        unify(&definition, false, "w{}(X:SortNat{})", "m{}(z{}())"),
        Ok(Vec::new())
    );
    let unifiers = unify(
        &definition,
        false,
        "k{}(X:SortNat{}, s{}(Y:SortNat{}))",
        "k{}(s{}(Z:SortNat{}), X:SortNat{})",
    )
    .expect("decided");
    assert_eq!(unifiers.len(), 1);
    assert_unifies(
        &definition,
        "k{}(X:SortNat{}, s{}(Y:SortNat{}))",
        "k{}(s{}(Z:SortNat{}), X:SortNat{})",
        &unifiers,
    );
}

#[test]
fn injections_compose_and_branch_over_common_subsorts() {
    let definition = definition("");
    // `C < A`: `inj{C,T}(c)` is `inj{A,T}(inj{C,A}(c))`.
    let unifiers = unify(
        &definition,
        false,
        "inj{SortA{}, SortT{}}(X:SortA{})",
        "inj{SortC{}, SortT{}}(c0{}())",
    )
    .expect("decided");
    assert_eq!(
        binding(&unifiers[0], "X"),
        Some(&term(&definition, "inj{SortC{}, SortA{}}(c0{}())"))
    );
    // `A` and `B` are incomparable: one branch per maximal common subsort, each binding both
    // operands to injections of one fresh variable.
    let unifiers = unify(
        &definition,
        false,
        "inj{SortA{}, SortT{}}(X:SortA{})",
        "inj{SortB{}, SortT{}}(Y:SortB{})",
    )
    .expect("decided");
    assert_eq!(unifiers.len(), 2);
    // A constructor of `A` against an injection from `B`: no common subsort holds `a0`.
    assert_eq!(
        unify(
            &definition,
            false,
            "inj{SortA{}, SortT{}}(a0{}())",
            "inj{SortB{}, SortT{}}(Y:SortB{})",
        ),
        Ok(Vec::new())
    );
}

#[test]
fn a_greater_application_meets_an_injection_of_a_lesser_one_by_lifting() {
    let definition = definition("");
    let left = "consE{}(E:SortE{}, Es:SortEs{})";
    let right = "inj{SortNs{}, SortEs{}}(consN{}(n0{}(), nilN{}()))";
    let unifiers = unify(&definition, true, left, right).expect("decided");
    assert_eq!(unifiers.len(), 1);
    assert_eq!(
        binding(&unifiers[0], "E"),
        Some(&term(&definition, "inj{SortN{}, SortE{}}(n0{}())"))
    );
    assert_eq!(
        binding(&unifiers[0], "Es"),
        Some(&term(&definition, "inj{SortNs{}, SortEs{}}(nilN{}())"))
    );
    // Without the overload axioms the comparison is not decided.
    assert!(matches!(
        unify(&definition, false, left, right),
        Err(UnresolvedShape::Family(_))
    ));
}

#[test]
fn a_greater_application_against_an_injected_variable_branches_over_lesser_productions() {
    let definition = definition("");
    let left = "consE{}(E:SortE{}, Es:SortEs{})";
    let right = "inj{SortNs{}, SortEs{}}(L:SortNs{})";
    let unifiers = unify(&definition, true, left, right).expect("decided");
    // The lesser productions of `consE` whose sort is below `Ns`: `consN` only.
    assert_eq!(unifiers.len(), 1);
    let value = binding(&unifiers[0], "L").expect("L is bound");
    assert!(
        matches!(value.kind(), crate::term::TermKind::Application { symbol, .. } if symbol.name.as_ref() == "consN")
    );
    // A greater application of another family member: `nilE` lifts to nothing of `consE`.
    assert_eq!(
        unify(
            &definition,
            true,
            "consE{}(E:SortE{}, Es:SortEs{})",
            "nilE{}()"
        ),
        Ok(Vec::new())
    );
}

#[test]
fn a_known_normal_greater_application_is_not_an_injection_of_a_lesser_one() {
    let definition = definition("");
    let mut families = Families::of(&definition);
    for family in 0..families.len() {
        families.set_confluent(family);
    }
    let mut fresh = 0;
    let normal = term(&definition, "consE{}(e0{}(), Es:SortEs{})");
    let known_normal = |candidate: &Term| *candidate == normal;
    let unifiers = Unifier {
        definition: &definition,
        families: &families,
        lifting: true,
        known_normal: &known_normal,
        fresh: &mut fresh,
        branches: 0,
        defer: false,
    }
    .unify(
        &normal,
        &term(&definition, "inj{SortNs{}, SortEs{}}(L:SortNs{})"),
    )
    .expect("decided");
    assert!(unifiers.is_empty());
}

#[test]
fn a_function_application_is_not_decided() {
    let definition = definition("");
    assert!(matches!(
        unify(&definition, false, "s{}(f{}(X:SortNat{}))", "s{}(z{}())"),
        Err(UnresolvedShape::Function(_))
    ));
}

#[test]
fn lists_with_fixed_elements_at_one_end_unify_elementwise() {
    let definition = definition("");
    let x = r#"\dv{SortElement{}}("x")"#;
    let unifiers = unify(
        &definition,
        false,
        &format!("listConcat{{}}(listItem{{}}({x}), L:SortList{{}})"),
        "listConcat{}(listItem{}(E:SortElement{}), listConcat{}(listItem{}(F:SortElement{}), M:SortList{}))",
    )
    .expect("decided");
    assert_eq!(unifiers.len(), 1);
    assert_eq!(binding(&unifiers[0], "E"), Some(&term(&definition, x)));
    // Two closed lists of different lengths have no common instance.
    assert_eq!(
        unify(
            &definition,
            false,
            "listItem{}(E:SortElement{})",
            "listConcat{}(listItem{}(F:SortElement{}), listItem{}(G:SortElement{}))",
        ),
        Ok(Vec::new())
    );
}

#[test]
fn maps_on_both_sides_are_not_decided() {
    let definition = definition("");
    assert_eq!(
        unify(
            &definition,
            false,
            "mapConcat{}(mapItem{}(K:SortKey{}, V:SortValue{}), M:SortMap{})",
            "mapConcat{}(mapItem{}(J:SortKey{}, W:SortValue{}), N:SortMap{})",
        ),
        Err(UnresolvedShape::Collection)
    );
    // A map pattern against a map variable binds it.
    assert_eq!(
        unify(
            &definition,
            false,
            "M:SortMap{}",
            "mapConcat{}(mapItem{}(J:SortKey{}, W:SortValue{}), N:SortMap{})",
        )
        .map(|unifiers| unifiers.len()),
        Ok(1)
    );
}

/// Extra symbols for the map tests: a key bound after the map (`#removeZeros`' order), an
/// injection branch beside a postponed map, and an opaque map rest.
const MAP_EXTRA: &str = r"
    symbol km2{}(SortKey{}, SortMap{}) : SortS{} [constructor{}(), functional{}(), injective{}()]
    symbol h3{}(SortT{}, SortKey{}, SortMap{}) : SortS{} [constructor{}(), functional{}(), injective{}()]
    symbol fm{}() : SortMap{} [function{}()]
";

fn unify_relaxed_for_tests(
    definition: &BackendDefinition,
    left: &str,
    right: &str,
) -> Result<Vec<(Substitution, Option<UnresolvedShape>)>, UnresolvedShape> {
    let families = Families::of(definition);
    let mut fresh = 0;
    let nothing_normal = |_: &Term| false;
    Unifier {
        definition,
        families: &families,
        lifting: false,
        known_normal: &nothing_normal,
        fresh: &mut fresh,
        branches: 0,
        defer: true,
    }
    .unify_all_relaxed(vec![(term(definition, left), term(definition, right))])
}

/// The decided answers of the map rule, as `(left, right, number of unifiers)`; each must hold,
/// and each unifier make the two terms equal.
const MAP_DECISIONS: [(&str, &str, usize); 7] = [
    // A key written alike: value with value, rest with rest.
    (
        "mapConcat{}(mapItem{}(K:SortKey{}, V:SortValue{}), M:SortMap{})",
        "mapConcat{}(mapItem{}(K:SortKey{}, W:SortValue{}), N:SortMap{})",
        1,
    ),
    // Size test: an empty map against an entry.
    (
        "mapUnit{}()",
        "mapConcat{}(mapItem{}(K:SortKey{}, V:SortValue{}), M:SortMap{})",
        0,
    ),
    // Size test: closed maps of sizes 1 and 2.
    (
        "mapItem{}(K:SortKey{}, V:SortValue{})",
        "mapConcat{}(mapItem{}(J:SortKey{}, W:SortValue{}), mapItem{}(L:SortKey{}, X:SortValue{}))",
        0,
    ),
    // Size test: a closed map with fewer entries than a map with a rest (P7-KEVM-S2B).
    (
        "mapItem{}(K:SortKey{}, V:SortValue{})",
        "mapConcat{}(mapItem{}(A:SortKey{}, B:SortValue{}), mapConcat{}(mapItem{}(C:SortKey{}, D:SortValue{}), M:SortMap{}))",
        0,
    ),
    // The variable rest of the side left without entries is the other side, its rest included.
    (
        "mapConcat{}(mapItem{}(K:SortKey{}, V:SortValue{}), M:SortMap{})",
        "mapConcat{}(mapItem{}(K:SortKey{}, W:SortValue{}), mapConcat{}(mapItem{}(J:SortKey{}, X:SortValue{}), N:SortMap{}))",
        1,
    ),
    // The key is bound by an argument unified after the map.
    (
        "km2{}(K:SortKey{}, mapConcat{}(mapItem{}(K:SortKey{}, V:SortValue{}), M:SortMap{}))",
        "km2{}(J:SortKey{}, mapConcat{}(mapItem{}(J:SortKey{}, W:SortValue{}), N:SortMap{}))",
        1,
    ),
    // A postponed map survives the injection branch (two maximal common subsorts C and D).
    (
        "h3{}(inj{SortA{}, SortT{}}(X:SortA{}), K:SortKey{}, mapConcat{}(mapItem{}(K:SortKey{}, V:SortValue{}), M:SortMap{}))",
        "h3{}(inj{SortB{}, SortT{}}(Y:SortB{}), J:SortKey{}, mapConcat{}(mapItem{}(J:SortKey{}, W:SortValue{}), N:SortMap{}))",
        2,
    ),
];

/// The failures of the map rule's unit checks: the decided answers, an opaque rest and keys
/// not written alike staying `Collection` (in both modes), and a repeated key.
fn map_rule_failures() -> Vec<String> {
    let definition = definition(MAP_EXTRA);
    let mut failures = Vec::new();
    for (left, right, expected) in MAP_DECISIONS {
        match unify(&definition, false, left, right) {
            Ok(unifiers) if unifiers.len() == expected => {
                let (l, r) = (term(&definition, left), term(&definition, right));
                if unifiers
                    .iter()
                    .any(|unifier| substitute(&l, unifier) != substitute(&r, unifier))
                {
                    failures.push(format!("{left} = {right}: a solution is no unifier"));
                }
            }
            other => failures.push(format!("{left} = {right}: {other:?}, expected {expected}")),
        }
    }
    // The rest binding is the most general one: `M` is bound to the other side's remaining
    // entry and its rest, not to a narrower map.
    let (left, right, _) = MAP_DECISIONS[4];
    if let Ok(unifiers) = unify(&definition, false, left, right) {
        let expected = term(
            &definition,
            "mapConcat{}(mapItem{}(J:SortKey{}, X:SortValue{}), N:SortMap{})",
        );
        if unifiers
            .iter()
            .any(|unifier| binding(unifier, "M") != Some(&expected))
        {
            failures.push(format!("{left} = {right}: `M` not bound to `J |-> X N`"));
        }
    }
    let opaque = unify(
        &definition,
        false,
        "mapConcat{}(mapItem{}(K:SortKey{}, V:SortValue{}), fm{}())",
        "mapConcat{}(mapItem{}(K:SortKey{}, W:SortValue{}), mapConcat{}(mapItem{}(J:SortKey{}, X:SortValue{}), N:SortMap{}))",
    );
    if opaque != Err(UnresolvedShape::Collection) {
        failures.push(format!("opaque rest: {opaque:?}"));
    }
    // A closed entry against an entry and a rest: no size clash, keys apart (P7-KEVM-S2B).
    let one = unify(
        &definition,
        false,
        "mapItem{}(K:SortKey{}, V:SortValue{})",
        "mapConcat{}(mapItem{}(J:SortKey{}, W:SortValue{}), M:SortMap{})",
    );
    if one != Err(UnresolvedShape::Collection) {
        failures.push(format!("closed entry against entry and rest: {one:?}"));
    }
    let apart = (
        "mapConcat{}(mapItem{}(K:SortKey{}, V:SortValue{}), M:SortMap{})",
        "mapConcat{}(mapItem{}(J:SortKey{}, W:SortValue{}), N:SortMap{})",
    );
    let exact = unify(&definition, false, apart.0, apart.1);
    if exact != Err(UnresolvedShape::Collection) {
        failures.push(format!("keys apart, exact: {exact:?}"));
    }
    match unify_relaxed_for_tests(&definition, apart.0, apart.1) {
        Ok(solutions)
            if solutions.len() == 1 && solutions[0].1 == Some(UnresolvedShape::Collection) => {}
        other => failures.push(format!("keys apart, deferring: {other:?}")),
    }
    // A key repeated in one pattern: the pattern has no instance, any answer is complete, and
    // every solution must still be a unifier.
    let repeated = (
        "mapConcat{}(mapItem{}(K:SortKey{}, V:SortValue{}), mapItem{}(K:SortKey{}, W:SortValue{}))",
        "mapConcat{}(mapItem{}(K:SortKey{}, X:SortValue{}), M:SortMap{})",
    );
    if let Ok(unifiers) = unify(&definition, false, repeated.0, repeated.1) {
        let (l, r) = (term(&definition, repeated.0), term(&definition, repeated.1));
        if unifiers
            .iter()
            .any(|unifier| substitute(&l, unifier) != substitute(&r, unifier))
        {
            failures.push("repeated key: a solution is no unifier".into());
        }
    }
    failures
}

#[test]
fn maps_are_decided_by_size_shared_keys_and_rests() {
    assert_eq!(map_rule_failures(), Vec::<String>::new());
}

/// Each map switch fails the unit checks or is left to the axiom harness (`mutations.rs`).
#[test]
fn the_map_unit_checks_see_their_switches() {
    for (name, switches) in [
        (
            "rest_binding_drops_rest",
            switches::Switches {
                rest_binding_drops_rest: true,
                ..switches::Switches::default()
            },
        ),
        (
            "raw_rest_clashes",
            switches::Switches {
                raw_rest_clashes: true,
                ..switches::Switches::default()
            },
        ),
        (
            "last_resort_clashes",
            switches::Switches {
                last_resort_clashes: true,
                ..switches::Switches::default()
            },
        ),
        (
            "size_counts_rest",
            switches::Switches {
                size_counts_rest: true,
                ..switches::Switches::default()
            },
        ),
    ] {
        assert!(
            !switches::with(switches, map_rule_failures).is_empty(),
            "{name} went unnoticed by the map unit checks"
        );
    }
}

/// An anywhere equation of `w` from `pattern` to `right` (a pattern of the naturals).
fn w_equation(pattern: &str, right: &str) -> String {
    format!(
        r"axiom{{R}} \implies{{R}}(
            \and{{R}}(\top{{R}}(), \and{{R}}(\in{{SortNat{{}}, R}}(X0:SortNat{{}}, {pattern}), \top{{R}}())),
            \equals{{SortS{{}}, R}}(w{{}}(X0:SortNat{{}}), \and{{SortS{{}}}}({right}, \top{{SortS{{}}}}()))
        ) [anywhere{{}}()]"
    )
}

#[test]
fn a_root_pair_that_joins_taints_nothing_and_one_that_does_not_is_named() {
    // `w(s(X)) = w(X)` and `w(s(s(X))) = w(X)` overlap at `w(s(s(X)))`: the sides `w(s(X))` and
    // `w(X)` join in one step.
    let joining = definition(&format!(
        "{} {}",
        w_equation("s{}(X:SortNat{})", "w{}(X:SortNat{})"),
        w_equation("s{}(s{}(X:SortNat{}))", "w{}(X:SortNat{})"),
    ));
    assert!(joining.value_claims().unjoined().is_empty());
    // With `w(s(s(X))) = m(X)` the sides `w(s(X))` and `m(X)` do not join.
    let apart = definition(&format!(
        "{} {}",
        w_equation("s{}(X:SortNat{})", "w{}(X:SortNat{})"),
        w_equation("s{}(s{}(X:SortNat{}))", "m{}(X:SortNat{})"),
    ));
    let unjoined = apart.value_claims().unjoined();
    assert_eq!(unjoined.len(), 1, "{unjoined:?}");
    assert_eq!(unjoined[0].reason, UnjoinedReason::DifferentResults);
    assert_eq!(unjoined[0].withdrawn, vec![crate::term::Name::from("w")]);
    assert_eq!(
        apart.value_claims().tainted_symbols(),
        vec![crate::term::Name::from("w")]
    );
}

#[test]
fn the_overload_family_is_confluent_and_its_equations_join() {
    let definition = definition("");
    let counts = definition.value_claims().counts();
    assert_eq!(counts.families, counts.confluent_families);
    assert!(counts.families > 0);
    assert!(definition.value_claims().unjoined().is_empty());
}

/// An anywhere equation of the value production `vp` from `pattern` to `right`.
fn vp_equation(pattern: &str, right: &str) -> String {
    w_equation(pattern, right).replace("w{}(X0", "vp{}(X0")
}

/// Whether the load discharged the definedness of every rewrite rule of a definition whose value
/// production `vp` the check withdraws (`vp(z) = m(z)` beside `vp(z) = m(s(z))`); its one rule
/// rewrites `m(s(z))` to the irreducible `vp(s(z))`.
fn withdrawn_rule_is_discharged() -> bool {
    let definition = definition(&format!(
        r#"symbol vp{{}}(SortNat{{}}) : SortS{{}} [anywhere{{}}(), value-production{{}}()]
        {} {}
        axiom{{}} \rewrites{{SortS{{}}}}(
            \and{{SortS{{}}}}(m{{}}(s{{}}(z{{}}())), \top{{SortS{{}}}}()),
            \and{{SortS{{}}}}(vp{{}}(s{{}}(z{{}}())), \top{{SortS{{}}}}())
        ) [label{{}}("r")]"#,
        vp_equation("z{}()", "m{}(z{}())"),
        vp_equation("z{}()", "m{}(s{}(z{}()))"),
    ));
    assert_eq!(
        definition.value_claims().tainted_symbols(),
        vec![crate::term::Name::from("vp")]
    );
    definition
        .rewrite_theory()
        .values()
        .flat_map(|groups| groups.values().flatten())
        .all(|rule| rule.rule.computed_attributes.definedness_discharged)
}

/// The rewrite rules' definedness is discharged after the check and reads its verdict: the
/// right-hand side of the rule is an application of a withdrawn head, so the rule keeps its
/// obligation.
#[test]
fn a_rewrite_rule_over_a_withdrawn_head_keeps_its_definedness_obligation() {
    assert!(!withdrawn_rule_is_discharged());
}

/// V7: discharging before the check (with every claim admitted) is caught by the test above.
#[test]
fn discharging_before_the_check_is_caught() {
    let switches = super::switches::Switches {
        discharge_before_check: true,
        ..super::switches::Switches::default()
    };
    assert!(super::switches::with(
        switches,
        withdrawn_rule_is_discharged
    ));
}

/// What the load records about each rewrite rule's definedness, by label: the declared attribute,
/// the discharge, and whether the run-time obligation is cleared.
fn definedness_records() -> Vec<(String, bool, bool, bool)> {
    let definition = definition(
        r#"axiom{} \rewrites{SortS{}}(\and{SortS{}}(m{}(z{}()), \top{SortS{}}()),
            \and{SortS{}}(m{}(s{}(z{}())), \top{SortS{}}())) [label{}("plain")]
        axiom{} \rewrites{SortS{}}(\and{SortS{}}(m{}(s{}(z{}())), \top{SortS{}}()),
            \and{SortS{}}(m{}(f{}(z{}())), \top{SortS{}}())) [label{}("declared"), preserves-definedness{}()]
        axiom{} \rewrites{SortS{}}(\and{SortS{}}(m{}(k{}(z{}(), z{}())), \top{SortS{}}()),
            \and{SortS{}}(m{}(f{}(z{}())), \top{SortS{}}())) [label{}("open")]"#,
    );
    let mut records = definition
        .rewrite_theory()
        .values()
        .flat_map(|groups| groups.values().flatten())
        .map(|rule| {
            let rule = &rule.rule;
            (
                rule.attributes.label.clone().unwrap_or_default(),
                rule.attributes.preserves_definedness,
                rule.computed_attributes.definedness_discharged,
                rule.computed_attributes.undefined_symbols.is_empty(),
            )
        })
        .collect::<Vec<_>>();
    records.sort();
    records
}

/// The declared attribute is the author's claim and the discharge a separate fact: a rule over
/// constructors only is discharged and not declared, a declared rule over the partial `f` (no
/// ceil equation) is declared and not discharged, and the same rule undeclared is neither and
/// keeps its obligation. Under `discharge_before_check` the load discharges twice, and the
/// second discharge keeps what the first recorded.
#[test]
fn the_discharge_is_recorded_apart_from_the_declared_attribute_and_once() {
    let expected = [
        ("declared".to_owned(), true, false, true),
        ("open".to_owned(), false, false, false),
        ("plain".to_owned(), false, true, true),
    ];
    assert_eq!(definedness_records(), expected);
    let switches = super::switches::Switches {
        discharge_before_check: true,
        ..super::switches::Switches::default()
    };
    assert_eq!(
        super::switches::with(switches, definedness_records),
        expected
    );
}

/// `f(a) = s(b)` and `\ceil(f(b))`, as one conjunction over the variables named `a` and `b`.
fn two_conjuncts(definition: &BackendDefinition, a: &str, b: &str) -> crate::rule::Predicate {
    use crate::rule::Predicate;
    Predicate::And(
        vec![
            Predicate::Equals(
                term(definition, &format!("f{{}}({a}:SortNat{{}})")),
                term(definition, &format!("s{{}}({b}:SortNat{{}})")),
            ),
            Predicate::Ceil(term(definition, &format!("f{{}}({b}:SortNat{{}})"))),
        ]
        .into(),
    )
}

/// The memo's key identifies two conditions exactly when one is the other renamed injectively:
/// the variables are numbered by first occurrence, keeping their sorts.
#[test]
fn conditions_share_a_memo_key_exactly_when_one_renames_to_the_other() {
    use super::memo::Canonical;
    let definition = definition("");
    let key = |predicate| Canonical::of(&predicate).key;
    let first = key(two_conjuncts(&definition, "X", "Y"));
    assert_eq!(first, key(two_conjuncts(&definition, "Y", "X")));
    assert_eq!(first, key(two_conjuncts(&definition, "A0", "VarB1")));
    // Identifying the two variables is not a renaming.
    assert_ne!(first, key(two_conjuncts(&definition, "X", "X")));
    assert!(
        first
            .free_variables()
            .iter()
            .all(|variable| variable.name.ends_with("!memo0") || variable.name.ends_with("!memo1")),
        "{first:?}"
    );
}

/// An answer stored for one condition answers a condition that renames to the same key, renamed
/// back to that condition's variables; a stop is stored as deciding nothing.
#[test]
fn the_memo_answers_a_renamed_condition_with_its_answer_renamed_back() {
    use super::memo::{Lookup, Memo};
    use crate::rule::Predicate;
    let definition = definition("");
    let mut memo = Memo::default();
    let Lookup::Miss(canonical) = memo.lookup(&two_conjuncts(&definition, "X", "Y")) else {
        panic!("an empty memo answers nothing");
    };
    // The simplifier's answer for the key: its first conjunct.
    let Predicate::And(conjuncts) = &canonical.key else {
        panic!("the key keeps the conjunction");
    };
    let answer = conjuncts[0].clone();
    let renamed = memo
        .store(canonical, Some(answer), PollBudgetRecord::default())
        .expect("an answer over the key's variables is stored");
    let Predicate::And(original) = two_conjuncts(&definition, "X", "Y") else {
        unreachable!()
    };
    assert_eq!(renamed, Some(original[0].clone()));
    let Lookup::Hit(hit, _) = memo.lookup(&two_conjuncts(&definition, "U", "V")) else {
        panic!("a renamed condition is answered from the memo");
    };
    let Predicate::And(renamed_conjuncts) = two_conjuncts(&definition, "U", "V") else {
        unreachable!()
    };
    assert_eq!(hit, Some(renamed_conjuncts[0].clone()));
    // A condition identifying the variables is another key.
    let Lookup::Miss(canonical) = memo.lookup(&two_conjuncts(&definition, "U", "U")) else {
        panic!("a condition that is not a renaming is not answered");
    };
    assert_eq!(
        memo.store(canonical, None, PollBudgetRecord::default()),
        Ok(None)
    );
    assert!(matches!(
        memo.lookup(&two_conjuncts(&definition, "W", "W")),
        Lookup::Hit(None, _)
    ));
}

/// An answer the memo cannot rename back without capturing or conflating a variable is not
/// stored: one with a free variable the key does not have, and one with a quantifier under a
/// renamed key. A condition with a quantifier is keyed as written, and its answers are stored.
#[test]
fn the_memo_stores_no_answer_a_renaming_could_capture_in() {
    use super::memo::{Canonical, Lookup, Memo};
    use crate::rule::Predicate;
    let definition = definition("");
    let condition = two_conjuncts(&definition, "X", "Y");
    let other = term(&definition, "f{}(Z:SortNat{})");
    let mut memo = Memo::default();
    let Lookup::Miss(canonical) = memo.lookup(&condition) else {
        panic!("an empty memo answers nothing");
    };
    assert_eq!(
        memo.store(
            canonical,
            Some(Predicate::Ceil(other.clone())),
            PollBudgetRecord::default()
        ),
        Err(())
    );
    assert!(
        matches!(memo.lookup(&condition), Lookup::AsWritten),
        "the refused answer is not stored, and the refusal is"
    );
    let bound = crate::term::Variable::new("Z", crate::term::Sort::simple("SortNat"));
    let quantified = Predicate::Exists(bound, Arc::new(Predicate::Ceil(other)));
    let mut memo = Memo::default();
    let Lookup::Miss(canonical) = memo.lookup(&condition) else {
        panic!("an empty memo answers nothing");
    };
    assert_eq!(
        memo.store(
            canonical,
            Some(quantified.clone()),
            PollBudgetRecord::default()
        ),
        Err(())
    );
    assert!(matches!(memo.lookup(&condition), Lookup::AsWritten));
    // Keyed as written.
    let with_binder = Predicate::And(vec![condition, quantified.clone()].into());
    assert_eq!(Canonical::of(&with_binder).key, with_binder);
    let Lookup::Miss(canonical) = memo.lookup(&with_binder) else {
        panic!("an empty key answers nothing");
    };
    assert_eq!(
        memo.store(
            canonical,
            Some(quantified.clone()),
            PollBudgetRecord::default()
        ),
        Ok(Some(quantified.clone()))
    );
    assert!(matches!(
        memo.lookup(&with_binder),
        Lookup::Hit(Some(answer), _) if answer == quantified
    ));
}

/// A key is simplified at most once per check. When the memo refuses the key's answer, the
/// caller simplifies the predicate as written; a later predicate with the same key must go
/// straight to that, not simplify the key again only to have its answer refused again, which
/// costs two simplifications per occurrence instead of one.
#[test]
fn a_key_whose_answer_was_refused_is_not_simplified_again() {
    use super::memo::{Lookup, Memo};
    use crate::rule::Predicate;
    let definition = definition("");
    let other = term(&definition, "f{}(Z:SortNat{})");
    let mut memo = Memo::default();
    let Lookup::Miss(canonical) = memo.lookup(&two_conjuncts(&definition, "X", "Y")) else {
        panic!("an empty memo answers nothing");
    };
    assert_eq!(
        memo.store(
            canonical,
            Some(Predicate::Ceil(other)),
            PollBudgetRecord::default()
        ),
        Err(())
    );
    assert!(
        matches!(
            memo.lookup(&two_conjuncts(&definition, "U", "V")),
            Lookup::AsWritten
        ),
        "the memo asks again for the simplification of a key whose answer it refused"
    );
}

/// `w(Y) = m(z) requires \ceil(f(Y))` beside `w(Y) = m(s(z))` and `w(Y) = m(s(s(z)))`, with
/// the lemma `\ceil(f(X)) = \exists Z. X = s(Z)`: the first equation's two root pairs have
/// the same condition with differently named variables, so one memo key, and that key's answer
/// has a quantifier, which the memo refuses under a renamed key. Each condition is answered in
/// one way (from the memo, through its key, or as written), and the key is simplified once: the
/// second condition is simplified as written only. The verdict and the counts but the memo's
/// own work are those of the check without the memo.
#[test]
fn a_check_simplifies_a_refused_key_once_and_counts_every_condition() {
    use super::{CheckScope, ConditionMemo};
    let w = |requires: &str, right: &str, id: &str| {
        format!(
            r#"axiom{{R}} \implies{{R}}(
                \and{{R}}({requires}, \and{{R}}(\in{{SortNat{{}}, R}}(X0:SortNat{{}}, Y:SortNat{{}}), \top{{R}}())),
                \equals{{SortS{{}}, R}}(w{{}}(X0:SortNat{{}}), \and{{SortS{{}}}}({right}, \top{{SortS{{}}}}()))
            ) [anywhere{{}}(), UNIQUE'Unds'ID{{}}("{id}")]"#
        )
    };
    let definition = definition(&format!(
        r#"{} {} {}
        axiom{{R}} \implies{{R}}(\top{{R}}(), \equals{{R, R}}(
            \ceil{{SortNat{{}}, R}}(f{{}}(X:SortNat{{}})),
            \and{{R}}(\exists{{R}}(Z:SortNat{{}}, \equals{{SortNat{{}}, R}}(X:SortNat{{}}, s{{}}(Z:SortNat{{}}))), \top{{R}}())))
            [simplification{{}}()]"#,
        w(
            r"\ceil{SortNat{}, R}(f{}(Y:SortNat{}))",
            "m{}(z{}())",
            "w-ceil"
        ),
        w(r"\top{R}()", "m{}(s{}(z{}()))", "w-one"),
        w(r"\top{R}()", "m{}(s{}(s{}(z{}())))", "w-two"),
    ));
    for scope in [CheckScope::Gate, CheckScope::All] {
        let on = definition.value_claims_checked(scope, ConditionMemo::On);
        let counts = on.counts();
        assert_eq!(
            (
                counts.simplifier_calls,
                counts.condition_memo_hits,
                counts.key_simplifications,
                counts.as_written_simplifications,
                counts.condition_memo_refusals,
            ),
            (2, 0, 1, 1, 1),
            "{scope:?}: {counts:?}"
        );
        let off = definition.value_claims_checked(scope, ConditionMemo::Off);
        assert!(on.verdict_differences(&off).is_empty(), "{scope:?}");
        assert_eq!(
            counts.without_memo_work(),
            off.counts().without_memo_work(),
            "{scope:?}"
        );
        assert_eq!(
            off.counts().as_written_simplifications,
            off.counts().simplifier_calls
        );
    }
}

/// `w(z) = m(z) requires f(z) = z` beside `w(z) = m(s(z))`, with `f(z) = f_z`: the pair's
/// condition is the same ground predicate in every such definition, and its answer is `f_z = z`.
fn condition_reading_f(f_z: &str) -> BackendDefinition {
    let w = |requires: &str, right: &str, id: &str| {
        format!(
            r#"axiom{{R}} \implies{{R}}(
                \and{{R}}({requires}, \and{{R}}(\in{{SortNat{{}}, R}}(X0:SortNat{{}}, z{{}}()), \top{{R}}())),
                \equals{{SortS{{}}, R}}(w{{}}(X0:SortNat{{}}), \and{{SortS{{}}}}({right}, \top{{SortS{{}}}}()))
            ) [anywhere{{}}(), UNIQUE'Unds'ID{{}}("{id}")]"#
        )
    };
    definition(&format!(
        r#"{} {}
        axiom{{R}} \implies{{R}}(
            \and{{R}}(\top{{R}}(), \and{{R}}(\in{{SortNat{{}}, R}}(X0:SortNat{{}}, z{{}}()), \top{{R}}())),
            \equals{{SortNat{{}}, R}}(f{{}}(X0:SortNat{{}}), \and{{SortNat{{}}}}({f_z}, \top{{SortNat{{}}}}()))
        ) [UNIQUE'Unds'ID{{}}("f-z")]"#,
        w(
            r"\equals{SortNat{}, R}(f{}(z{}()), z{}())",
            "m{}(z{}())",
            "w-if"
        ),
        w(r"\top{R}()", "m{}(s{}(z{}()))", "w-else"),
    ))
}

/// The memo's answers live as long as one check: its soundness rests on the definition, the
/// withheld claims, the options and the solver being fixed, which holds within a check and not
/// across checks. Two definitions loaded in turn on one thread share the pair's condition
/// `f(z) = z` and answer it differently: `false` under `f(z) = s(z)`, which separates the two
/// equations, and `true` under `f(z) = z`, under which the reducts differ and `w` is withdrawn.
/// Each verdict is the one the check reaches without the memo, whichever definition is loaded
/// first.
#[test]
fn the_memo_answers_only_within_one_check() {
    use super::{CheckScope, ConditionMemo};
    let withdraws_w = |definition: &BackendDefinition| {
        definition
            .value_claims()
            .tainted_symbols()
            .contains(&crate::term::Name::from("w"))
    };
    for order in [["s{}(z{}())", "z{}()"], ["z{}()", "s{}(z{}())"]] {
        let definitions = order.map(condition_reading_f);
        for (f_z, definition) in order.iter().zip(&definitions) {
            assert_eq!(withdraws_w(definition), *f_z == "z{}()", "f(z) = {f_z}");
            let off = definition.value_claims_checked(CheckScope::Gate, ConditionMemo::Off);
            let differences = definition.value_claims().verdict_differences(&off);
            assert!(differences.is_empty(), "f(z) = {f_z}: {differences:?}");
        }
    }
}

/// The integers with their comparisons, a constructor `mk`, a map from `Int` to `Int`, and the
/// declared functions `f : Int -> Int` and `pick : Map -> S`, with `extra`: no equation head and
/// no overloaded symbol, so nothing a pair could withdraw.
fn head_free(extra: &str) -> BackendDefinition {
    let source = format!(
        r#"[] module MAIN
            hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
            hooked-sort SortBool{{}} [hook{{}}("BOOL.Bool"), hasDomainValues{{}}()]
            hooked-symbol gtInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
                [function{{}}(), total{{}}(), hook{{}}("INT.gt"), smt-hook{{}}(">")]
            hooked-symbol leInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
                [function{{}}(), total{{}}(), hook{{}}("INT.le"), smt-hook{{}}("<=")]
            hooked-symbol geInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
                [function{{}}(), total{{}}(), hook{{}}("INT.ge"), smt-hook{{}}(">=")]
            hooked-symbol ltInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
                [function{{}}(), total{{}}(), hook{{}}("INT.lt"), smt-hook{{}}("<")]
            hooked-sort SortMap{{}}
                [hook{{}}("MAP.Map"), unit{{}}(mapUnit{{}}()), element{{}}(mapItem{{}}()), concat{{}}(mapConcat{{}}())]
            hooked-symbol mapUnit{{}}() : SortMap{{}} [function{{}}(), total{{}}(), hook{{}}("MAP.unit")]
            hooked-symbol mapItem{{}}(SortInt{{}}, SortInt{{}}) : SortMap{{}} [function{{}}(), total{{}}(), hook{{}}("MAP.element")]
            hooked-symbol mapConcat{{}}(SortMap{{}}, SortMap{{}}) : SortMap{{}}
                [function{{}}(), hook{{}}("MAP.concat"), assoc{{}}(), comm{{}}(), unit{{}}(mapUnit{{}}())]
            sort SortS{{}} []
            symbol mk{{}}(SortInt{{}}) : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol f{{}}(SortInt{{}}) : SortInt{{}} [function{{}}()]
            symbol pick{{}}(SortMap{{}}) : SortS{{}} [function{{}}()]
            {extra}
        endmodule []"#
    );
    internalized(&parse_definition(&source).expect("the definition parses"))
}

fn int(value: i64) -> String {
    format!(r#"\dv{{SortInt{{}}}}("{value}")"#)
}

/// `f(X0) = right requires X0 <comparison> bound`, labelled `id`.
fn f_equation(comparison: &str, bound: i64, right: i64, id: &str) -> String {
    int_equation("f", "SortInt{}", comparison, bound, &int(right), id)
}

/// `head(X0) = right requires X0 <comparison> bound` with `head : Int -> result`, labelled `id`.
fn int_equation(
    head: &str,
    result: &str,
    comparison: &str,
    bound: i64,
    right: &str,
    id: &str,
) -> String {
    format!(
        r#"axiom{{R}} \implies{{R}}(
            \and{{R}}(
                \equals{{SortBool{{}}, R}}({comparison}{{}}(X:SortInt{{}}, {}), \dv{{SortBool{{}}}}("true")),
                \and{{R}}(\in{{SortInt{{}}, R}}(X0:SortInt{{}}, X:SortInt{{}}), \top{{R}}())),
            \equals{{{result}, R}}({head}{{}}(X0:SortInt{{}}), \and{{{result}}}({right}, \top{{{result}}}()))
        ) [UNIQUE'Unds'ID{{}}("{id}")]"#,
        int(bound),
    )
}

/// The non-joined pairs of `claims` between two distinct equations.
fn pairs(claims: &super::ValueClaims) -> Vec<&super::UnjoinedPair> {
    claims
        .unjoined()
        .iter()
        .filter(|pair| !pair.reason.describes_one_equation())
        .collect()
}

/// `CheckScope::All` classifies every candidate pair of a definition with nothing to withdraw;
/// only the load, whose scope reads claims, skips them.
#[test]
fn every_pair_is_classified_in_scope_all_without_an_equation_head() {
    use super::CheckScope;
    // `X >Int 0` and `X >Int -5` overlap on `X = 1` with the results 1 and 2.
    let overlapping = head_free(&format!(
        "{} {}",
        f_equation("gtInt", 0, 1, "one"),
        f_equation("gtInt", -5, 2, "two"),
    ));
    assert_eq!(overlapping.value_claims().counts().pairs, 0);
    let all = overlapping.value_claims_in_scope(CheckScope::All);
    let counts = all.counts();
    assert_eq!((counts.pairs, counts.skipped), (1, 0), "{counts:?}");
    let found = pairs(&all);
    assert_eq!(found.len(), 1, "{:?}", all.unjoined());
    assert!(found[0].withdrawn.is_empty(), "{:?}", found[0]);
    // `X >Int 0` beside `X <=Int 0` holds on no integer: refuted.
    let complementary = head_free(&format!(
        "{} {}",
        f_equation("gtInt", 0, 1, "one"),
        f_equation("leInt", 0, 2, "two"),
    ));
    let all = complementary.value_claims_in_scope(CheckScope::All);
    assert_eq!(
        (all.counts().pairs, all.counts().refuted),
        (1, 1),
        "{:?}",
        all.counts()
    );
    assert!(pairs(&all).is_empty(), "{:?}", all.unjoined());
}

/// The self pair of a map pattern that matches one map in several ways, with results that
/// differ between matchings, is classified and reported by `CheckScope::All` in a definition with
/// nothing to withdraw.
#[test]
fn a_self_pair_is_classified_in_scope_all_without_an_equation_head() {
    use super::{CheckScope, unify::UnresolvedShape};
    let definition = head_free(
        r#"axiom{R} \implies{R}(
            \and{R}(\top{R}(), \and{R}(\in{SortMap{}, R}(X0:SortMap{},
                mapConcat{}(mapItem{}(K:SortInt{}, V:SortInt{}), M:SortMap{})), \top{R}())),
            \equals{SortS{}, R}(pick{}(X0:SortMap{}), \and{SortS{}}(mk{}(K:SortInt{}), \top{SortS{}}()))
        ) [UNIQUE'Unds'ID{}("pick")]"#,
    );
    assert_eq!(definition.value_claims().counts().several_matches, 0);
    let all = definition.value_claims_in_scope(CheckScope::All);
    assert_eq!(all.counts().several_matches, 1, "{:?}", all.counts());
    assert!(
        all.unjoined()
            .iter()
            .any(|pair| pair.reason == UnjoinedReason::Unresolved(UnresolvedShape::SeveralMatches)),
        "{:?}",
        all.unjoined()
    );
}

/// An overload family of two hooked functions, `hE` over `hN` (hooks that never apply to these
/// sorts), so the only overloaded symbols cannot be withdrawn; an equation `hE(inj(n0)) = m(z)`
/// rooted at `hE`, and `gg(hE(inj(n0))) = z`, whose argument pattern `hE` rewrites.
fn hooked_overloads() -> BackendDefinition {
    let source = r#"[] module MAIN
        sort SortNat{} []
        sort SortS{} []
        sort SortE{} []
        sort SortN{} []
        symbol inj{From, To}(From) : To [sortInjection{}(), injective{}()]
        axiom{R} \exists{R}(V:SortE{}, \equals{SortE{}, R}(V:SortE{}, inj{SortN{}, SortE{}}(F:SortN{}))) [subsort{SortN{}, SortE{}}()]
        symbol z{}() : SortNat{} [constructor{}(), functional{}(), injective{}()]
        symbol m{}(SortNat{}) : SortS{} [constructor{}(), functional{}(), injective{}()]
        symbol n0{}() : SortN{} [constructor{}(), functional{}(), injective{}()]
        hooked-symbol hE{}(SortE{}) : SortS{} [function{}(), hook{}("INT.abs")]
        hooked-symbol hN{}(SortN{}) : SortS{} [function{}(), hook{}("INT.abs")]
        axiom{R} \equals{SortS{}, R}(hE{}(inj{SortN{}, SortE{}}(K0:SortN{})), hN{}(K0:SortN{}))
            [symbol-overload{}(hE{}(), hN{}())]
        symbol gg{}(SortS{}) : SortNat{} [function{}()]
        axiom{R} \implies{R}(
            \and{R}(\top{R}(), \and{R}(\in{SortE{}, R}(X0:SortE{}, inj{SortN{}, SortE{}}(n0{}())), \top{R}())),
            \equals{SortS{}, R}(hE{}(X0:SortE{}), \and{SortS{}}(m{}(z{}()), \top{SortS{}}()))
        ) [UNIQUE'Unds'ID{}("he")]
        axiom{R} \implies{R}(
            \and{R}(\top{R}(), \and{R}(\in{SortS{}, R}(X0:SortS{}, hE{}(inj{SortN{}, SortE{}}(n0{}()))), \top{R}())),
            \equals{SortNat{}, R}(gg{}(X0:SortS{}), \and{SortNat{}}(z{}(), \top{SortNat{}}()))
        ) [UNIQUE'Unds'ID{}("gg")]
    endmodule []"#;
    internalized(&parse_definition(source).expect("the definition parses"))
}

/// The load names an inner pair at an argument whose second equation is rooted at an overloaded
/// symbol even when that symbol cannot be withdrawn (it is hooked), as `CheckScope::All` does:
/// such a pair is named whatever it withdraws. Both equations rooted at `hE` rewrite `gg`'s
/// argument pattern: `he` and the overload equation `hE(inj(K0)) = hN(K0)`.
#[test]
fn the_load_names_an_argument_pair_at_a_hooked_overloaded_symbol() {
    use super::CheckScope;
    let definition = hooked_overloads();
    let load = definition.value_claims();
    let named = load
        .unjoined()
        .iter()
        .filter(|pair| pair.in_argument() && pair.reported())
        .map(|pair| {
            (
                pair.first.attributes.unique_id.as_str(),
                pair.position.clone(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        named,
        [("gg", vec![0]), ("gg", vec![0])],
        "{:?}",
        load.unjoined()
    );
    assert!(
        load.unjoined()
            .iter()
            .any(|pair| pair.in_argument() && pair.second.attributes.unique_id == "he"),
        "{:?}",
        load.unjoined()
    );
    let all = definition.value_claims_in_scope(CheckScope::All);
    let differences = load.claim_differences(&all, &definition);
    assert!(differences.is_empty(), "{differences:?}");
}

/// Constructors `b`, `c`, `d1`, `d2` whose overload relations (`d1` and `d2` each over `b` and
/// `c`) ride on equations of unrelated functions `q1` to `q4`: nothing can be withdrawn and no
/// executable equation is rooted at a gate symbol, so the load takes its shortcut; `b` and `c`
/// have two minimal common overloads.
const OVERLOAD_DIAMOND: &str = r#"[] module MAIN
        sort SortNat{} []
        sort SortS{} []
        sort SortE{} []
        sort SortN{} []
        symbol inj{From, To}(From) : To [sortInjection{}(), injective{}()]
        axiom{R} \exists{R}(V:SortE{}, \equals{SortE{}, R}(V:SortE{}, inj{SortN{}, SortE{}}(F:SortN{}))) [subsort{SortN{}, SortE{}}()]
        symbol z{}() : SortNat{} [constructor{}(), functional{}(), injective{}()]
        symbol m{}(SortNat{}) : SortS{} [constructor{}(), functional{}(), injective{}()]
        symbol n0{}() : SortN{} [constructor{}(), functional{}(), injective{}()]
        symbol b{}(SortNat{}) : SortS{} [constructor{}(), functional{}(), injective{}()]
        symbol c{}(SortNat{}) : SortS{} [constructor{}(), functional{}(), injective{}()]
        symbol d1{}(SortNat{}) : SortS{} [constructor{}(), functional{}(), injective{}()]
        symbol d2{}(SortNat{}) : SortS{} [constructor{}(), functional{}(), injective{}()]
        
        symbol q1{}(SortNat{}) : SortNat{} [function{}()]
        symbol q2{}(SortNat{}) : SortNat{} [function{}()]
        symbol q3{}(SortNat{}) : SortNat{} [function{}()]
        symbol q4{}(SortNat{}) : SortNat{} [function{}()]
        axiom{R} \equals{SortNat{}, R}(q1{}(K0:SortNat{}), z{}()) [symbol-overload{}(d1{}(), b{}())]
        axiom{R} \equals{SortNat{}, R}(q2{}(K0:SortNat{}), z{}()) [symbol-overload{}(d1{}(), c{}())]
        axiom{R} \equals{SortNat{}, R}(q3{}(K0:SortNat{}), z{}()) [symbol-overload{}(d2{}(), b{}())]
        axiom{R} \equals{SortNat{}, R}(q4{}(K0:SortNat{}), z{}()) [symbol-overload{}(d2{}(), c{}())]
endmodule []"#;

/// The precondition rows of the overload families read no pair, so the load reports them as
/// `CheckScope::All` does, also where it classifies no pair.
#[test]
fn the_load_reports_the_overload_rows_where_it_classifies_no_pair() {
    use super::{CheckScope, ViolationKind};
    let definition =
        internalized(&parse_definition(OVERLOAD_DIAMOND).expect("the definition parses"));
    let kinds = |claims: &super::ValueClaims| {
        claims
            .violations()
            .iter()
            .map(|violation| format!("{:?}", violation.kind))
            .collect::<Vec<_>>()
    };
    let load = definition.value_claims();
    assert_eq!(load.counts().pairs, 0);
    assert!(
        load.violations()
            .iter()
            .any(|violation| matches!(violation.kind, ViolationKind::NoLeastCommonOverload(..))),
        "{:?}",
        load.violations()
    );
    let all = definition.value_claims_in_scope(CheckScope::All);
    assert_eq!(kinds(load), kinds(&all));
}

/// A free-constructor overload family, `cE` over `cN`, with its overload equation and
/// `gg(cE(inj(n0))) = z`: the overload equation is rooted at an overloaded symbol, so the load
/// classifies the argument pair at `gg` (which joins: `cE(inj(n0))` and `cN(n0)` are one value)
/// as `CheckScope::All` does.
#[test]
fn the_load_classifies_an_argument_pair_at_a_free_constructor_overload() {
    use super::CheckScope;
    let definition = internalized(&parse_definition(r#"[] module MAIN
        sort SortNat{} []
        sort SortS{} []
        sort SortE{} []
        sort SortN{} []
        symbol inj{From, To}(From) : To [sortInjection{}(), injective{}()]
        axiom{R} \exists{R}(V:SortE{}, \equals{SortE{}, R}(V:SortE{}, inj{SortN{}, SortE{}}(F:SortN{}))) [subsort{SortN{}, SortE{}}()]
        symbol z{}() : SortNat{} [constructor{}(), functional{}(), injective{}()]
        symbol m{}(SortNat{}) : SortS{} [constructor{}(), functional{}(), injective{}()]
        symbol n0{}() : SortN{} [constructor{}(), functional{}(), injective{}()]
        symbol cE{}(SortE{}) : SortS{} [constructor{}(), functional{}(), injective{}()]
        symbol cN{}(SortN{}) : SortS{} [constructor{}(), functional{}(), injective{}()]
        axiom{R} \equals{SortS{}, R}(cE{}(inj{SortN{}, SortE{}}(K0:SortN{})), cN{}(K0:SortN{}))
            [symbol-overload{}(cE{}(), cN{}())]
        symbol gg{}(SortS{}) : SortNat{} [function{}()]
        axiom{R} \implies{R}(
            \and{R}(\top{R}(), \and{R}(\in{SortS{}, R}(X0:SortS{}, cE{}(inj{SortN{}, SortE{}}(n0{}()))), \top{R}())),
            \equals{SortNat{}, R}(gg{}(X0:SortS{}), \and{SortNat{}}(z{}(), \top{SortNat{}}()))
        ) [UNIQUE'Unds'ID{}("gg")]
endmodule []"#).expect("the definition parses"));
    let load = definition.value_claims();
    assert_eq!(
        (load.counts().pairs, load.counts().families),
        (1, 1),
        "{:?}",
        load.counts()
    );
    assert!(load.unjoined().is_empty(), "{:?}", load.unjoined());
    let all = definition.value_claims_in_scope(CheckScope::All);
    let differences = load.claim_differences(&all, &definition);
    assert!(differences.is_empty(), "{differences:?}");
}

/// Comparisons of one integer term with literals refute a pair whose requires bound it to no
/// integer, in a definition with nothing to withdraw (under `CheckScope::All`).
#[test]
fn a_pair_whose_requires_bound_an_integer_to_nothing_is_refuted() {
    use super::CheckScope;
    // `X >Int 5` beside `X <=Int 0`: refuted.
    let apart = head_free(&format!(
        "{} {}",
        f_equation("gtInt", 5, 1, "one"),
        f_equation("leInt", 0, 2, "two"),
    ));
    let all = apart.value_claims_in_scope(CheckScope::All);
    assert_eq!(
        (all.counts().pairs, all.counts().refuted),
        (1, 1),
        "{:?}",
        all.counts()
    );
    assert!(pairs(&all).is_empty(), "{:?}", all.unjoined());
    // `X >=Int -5` beside `X <Int 0` overlap on -5 to -1 with different results: not joined.
    let overlapping = head_free(&format!(
        "{} {}",
        f_equation("geInt", -5, 1, "one"),
        f_equation("ltInt", 0, 2, "two"),
    ));
    let all = overlapping.value_claims_in_scope(CheckScope::All);
    assert_eq!(pairs(&all).len(), 1, "{:?}", all.unjoined());
}

/// An equation head `wi` whose two equations are separated only by integer bounds keeps its
/// claims at the load (`CheckScope::Gate`).
#[test]
fn an_equation_head_separated_by_integer_bounds_keeps_its_claims() {
    let head = head_free(&format!(
        r"symbol wi{{}}(SortInt{{}}) : SortS{{}} [anywhere{{}}()] {} {}",
        int_equation(
            "wi",
            "SortS{}",
            "gtInt",
            5,
            &format!("mk{{}}({})", int(1)),
            "wi-one"
        ),
        int_equation(
            "wi",
            "SortS{}",
            "leInt",
            0,
            &format!("mk{{}}({})", int(2)),
            "wi-two"
        ),
    ));
    let load = head.value_claims();
    assert!(load.unjoined().is_empty(), "{:?}", load.unjoined());
    assert!(
        load.admit(&crate::rule::TermIndex::Symbol("wi".into()))
            .is_some(),
        "{:?}",
        load.tainted_symbols()
    );
}

/// An equation `head(X0) = right` with `X0` matching `pattern`, over the sorts given, with the
/// attributes `attributes` (a KORE attribute list without brackets).
fn unary_equation(
    head: &str,
    (argument, result): (&str, &str),
    pattern: &str,
    right: &str,
    attributes: &str,
) -> String {
    format!(
        r"axiom{{R}} \implies{{R}}(
            \and{{R}}(\top{{R}}(), \and{{R}}(\in{{{argument}, R}}(X0:{argument}, {pattern}), \top{{R}}())),
            \equals{{{result}, R}}({head}{{}}(X0:{argument}), \and{{{result}}}({right}, \top{{{result}}}()))
        ) [{attributes}]"
    )
}

/// Every kind of pair in one definition: the overload family with a second equation at `consE`
/// (a stage-1 root pair), two equations of the equation head `w` (a root pair that does not
/// join), three equations of the declared function `f` and one `[symbolic]` one, an equation of
/// `g` whose argument pattern `w(z)` the equations of `w` are tried against (inner pairs), and
/// `pick` over a map pattern that matches one map in several ways (a self pair).
fn every_kind_of_pair() -> BackendDefinition {
    let nat = ("SortNat{}", "SortNat{}");
    definition(&format!(
        r"symbol g{{}}(SortS{{}}) : SortNat{{}} [function{{}}()]
        symbol pick{{}}(SortMap{{}}) : SortKey{{}} [function{{}}()]
        axiom{{R}} \implies{{R}}(
            \and{{R}}(\top{{R}}(), \and{{R}}(\in{{SortE{{}}, R}}(X0:SortE{{}}, e0{{}}()),
                \and{{R}}(\in{{SortEs{{}}, R}}(X1:SortEs{{}}, K1:SortEs{{}}), \top{{R}}()))),
            \equals{{SortEs{{}}, R}}(consE{{}}(X0:SortE{{}}, X1:SortEs{{}}), \and{{SortEs{{}}}}(nilE{{}}(), \top{{SortEs{{}}}}()))
        ) []
        {} {} {} {} {} {} {} {}",
        w_equation("s{}(X:SortNat{})", "w{}(X:SortNat{})"),
        w_equation("s{}(s{}(X:SortNat{}))", "m{}(X:SortNat{})"),
        unary_equation("f", nat, "z{}()", "z{}()", ""),
        unary_equation("f", nat, "s{}(X:SortNat{})", "X:SortNat{}", ""),
        unary_equation("f", nat, "X:SortNat{}", "z{}()", ""),
        unary_equation(
            "f",
            nat,
            "k{}(X:SortNat{}, Y:SortNat{})",
            "z{}()",
            "symbolic{}()"
        ),
        unary_equation("g", ("SortS{}", "SortNat{}"), "w{}(z{}())", "z{}()", ""),
        unary_equation(
            "pick",
            ("SortMap{}", "SortKey{}"),
            "mapConcat{}(mapItem{}(K:SortKey{}, V:SortValue{}), M:SortMap{})",
            "K:SortKey{}",
            ""
        ),
    ))
}

/// The field-wise sum of the per-group counts of `claims`.
fn summed_group_counts(claims: &super::ValueClaims) -> super::GroupCounts {
    let mut sum = super::GroupCounts::default();
    for counts in claims.group_counts().values() {
        sum.equations += counts.equations;
        sum.symbolic_equations += counts.symbolic_equations;
        sum.root_pairs += counts.root_pairs;
        sum.self_pairs += counts.self_pairs;
        sum.inner_pairs += counts.inner_pairs;
        sum.skipped += counts.skipped;
        sum.overlaps += counts.overlaps;
        sum.uninhabited += counts.uninhabited;
        sum.refuted += counts.refuted;
        sum.joined += counts.joined;
        sum.not_joined += counts.not_joined;
    }
    sum
}

/// The counts of the group of `claims` at the symbol `name`, which must be the only group there.
fn group_at(claims: &super::ValueClaims, name: &str) -> super::GroupCounts {
    let index = crate::rule::TermIndex::Symbol(name.into());
    let groups = claims
        .group_counts()
        .iter()
        .filter(|(key, _)| key.index == index)
        .map(|(_, counts)| *counts)
        .collect::<Vec<_>>();
    assert_eq!(groups.len(), 1, "{:?}", claims.group_counts());
    groups[0]
}

/// Summed over the index and priority groups, the per-group counts are the check's totals, in
/// both scopes: every classified pair is a root or an inner pair of one group, every self pair
/// is one group's, and every overlap (and each over a sort with no normal form), refutation, join and skipped pair is counted in
/// one group. Under `CheckScope::All` each group of `n` executable equations has its `n(n-1)/2`
/// root pairs, and the `[symbolic]` equation, which no check pairs, is counted only in its
/// group's `symbolic_equations`.
#[test]
fn group_counts_sum_to_the_totals() {
    use super::CheckScope;
    let definition = every_kind_of_pair();
    for (scope, claims) in [
        (CheckScope::Gate, definition.value_claims().clone()),
        (
            CheckScope::All,
            definition.value_claims_in_scope(CheckScope::All),
        ),
    ] {
        let (counts, sum) = (claims.counts(), summed_group_counts(&claims));
        assert_eq!(sum.equations, counts.equations, "{scope:?}");
        assert_eq!(sum.root_pairs + sum.inner_pairs, counts.pairs, "{scope:?}");
        assert_eq!(sum.self_pairs, counts.several_matches, "{scope:?}");
        assert_eq!(
            (
                sum.skipped,
                sum.overlaps,
                sum.uninhabited,
                sum.refuted,
                sum.joined
            ),
            (
                counts.skipped,
                counts.overlaps,
                counts.uninhabited,
                counts.refuted,
                counts.joined
            ),
            "{scope:?}"
        );
        assert_eq!(sum.not_joined, pairs(&claims).len(), "{scope:?}");
        assert_eq!(sum.symbolic_equations, 1, "{scope:?}");
        let f = group_at(&claims, "f");
        assert_eq!(
            (f.equations, f.symbolic_equations),
            (3, 1),
            "{scope:?}: {f:?}"
        );
        // Every equation of `f` is irrelevant to the gate and has no inner candidate, so the
        // load skips each root pair it does not classify.
        assert_eq!(f.root_pairs + f.skipped, 3, "{scope:?}: {f:?}");
        assert_eq!(group_at(&claims, "consE").root_pairs, 1, "{scope:?}");
        assert_eq!(group_at(&claims, "w").not_joined, 1, "{scope:?}");
        let g = group_at(&claims, "g");
        assert_eq!(g.inner_pairs, 2, "{scope:?}: {g:?}");
        let pick = group_at(&claims, "pick");
        assert_eq!(
            (pick.self_pairs, pick.not_joined),
            (1, 1),
            "{scope:?}: {pick:?}"
        );
        if scope == CheckScope::Gate {
            assert_eq!((f.root_pairs, f.skipped), (0, 3), "{f:?}");
            continue;
        }
        assert_eq!(counts.skipped, 0);
        for (key, group) in claims.group_counts() {
            assert_eq!(
                group.root_pairs,
                group.equations * group.equations.saturating_sub(1) / 2,
                "{key:?}: {group:?}"
            );
        }
        assert_eq!(f.root_pairs, 3, "{f:?}");
    }
}

/// Three priority groups at the index `f` (priority 10, the default, owise), a simplification
/// equation of `f`, and a bare-variable equation `listConcat(L, listUnit) = listUnit` beside
/// `hl(z) = listItem(1)`. Under `CheckScope::All` each group of `f` is counted apart: its root
/// pairs are formed within it and never across the priorities, so only the default group's two
/// equations make a root pair. The simplification equation is in no group and no count. The
/// bare-variable equation has its own group at `TermIndex::Variable`, and its root overlap with
/// `hl(z) = listItem(1)` (both apply at the root of `hl(z)`) is formed in neither group: the
/// precondition row for the Variable index is what says so.
#[test]
fn group_counts_keep_priorities_and_the_bare_variable_group_apart() {
    use super::{CheckScope, GroupKey, ViolationKind};
    use crate::rule::TermIndex;
    let nat = ("SortNat{}", "SortNat{}");
    let variable = r#"axiom{R} \implies{R}(
            \and{R}(\top{R}(), \and{R}(\in{SortList{}, R}(X0:SortList{}, L:SortList{}),
                \and{R}(\in{SortList{}, R}(X1:SortList{}, listUnit{}()), \top{R}()))),
            \equals{SortList{}, R}(listConcat{}(X0:SortList{}, X1:SortList{}),
                \and{SortList{}}(listUnit{}(), \top{SortList{}}()))
        ) []"#;
    let definition = definition(&format!(
        "symbol hl{{}}(SortNat{{}}) : SortList{{}} [function{{}}()] {variable} {} {} {} {} {} {}",
        unary_equation("f", nat, "z{}()", "z{}()", r#"priority{}("10")"#),
        unary_equation("f", nat, "s{}(X:SortNat{})", "X:SortNat{}", ""),
        unary_equation("f", nat, "s{}(z{}())", "z{}()", ""),
        unary_equation("f", nat, "X:SortNat{}", "z{}()", "owise{}()"),
        unary_equation(
            "f",
            nat,
            "k{}(X:SortNat{}, Y:SortNat{})",
            "z{}()",
            "simplification{}()"
        ),
        unary_equation(
            "hl",
            ("SortNat{}", "SortList{}"),
            "z{}()",
            r#"listItem{}(\dv{SortElement{}}("1"))"#,
            ""
        ),
    ));
    let claims = definition.value_claims_in_scope(CheckScope::All);
    let at = |index: TermIndex, priority: u8| {
        claims
            .group_counts()
            .get(&GroupKey { index, priority })
            .copied()
            .unwrap_or_else(|| panic!("{:?}", claims.group_counts()))
    };
    let f = |priority| at(TermIndex::Symbol("f".into()), priority);
    let shape = |group: super::GroupCounts| (group.equations, group.root_pairs, group.not_joined);
    assert_eq!(shape(f(10)), (1, 0, 0), "{:?}", f(10));
    assert_eq!(shape(f(50)), (2, 1, 0), "{:?}", f(50));
    assert_eq!(f(50).joined, 1, "{:?}", f(50));
    assert_eq!(shape(f(255)), (1, 0, 0), "{:?}", f(255));
    let f_groups = claims
        .group_counts()
        .keys()
        .filter(|key| key.index == TermIndex::Symbol("f".into()))
        .count();
    assert_eq!(f_groups, 3, "{:?}", claims.group_counts());
    let hl = at(TermIndex::Symbol("hl".into()), 50);
    let variable = at(TermIndex::Variable, 50);
    assert_eq!(shape(hl), (1, 0, 0), "{hl:?}");
    assert_eq!(shape(variable), (1, 0, 0), "{variable:?}");
    // The groups of `f` hold its four executable equations, not the simplification equation,
    // and the groups together count exactly the check's executable equations.
    assert_eq!(f(10).equations + f(50).equations + f(255).equations, 4);
    assert_eq!(
        summed_group_counts(&claims).equations,
        claims.counts().equations
    );
    assert!(
        claims
            .violations()
            .iter()
            .any(|violation| violation.kind == ViolationKind::IndexedAt(TermIndex::Variable)),
        "{:?}",
        claims.violations()
    );
    assert!(claims.unjoined().is_empty(), "{:?}", claims.unjoined());
}

/// The head-free `f` with the complementary guards `X >Int 0` and `X <=Int 0`: its group's one
/// root pair is refuted, and the group says so.
#[test]
fn group_counts_name_the_refuted_pair() {
    use super::CheckScope;
    let definition = head_free(&format!(
        "{} {}",
        f_equation("gtInt", 0, 1, "one"),
        f_equation("leInt", 0, 2, "two"),
    ));
    let all = definition.value_claims_in_scope(CheckScope::All);
    let f = group_at(&all, "f");
    assert_eq!(
        (
            f.equations,
            f.root_pairs,
            f.overlaps,
            f.refuted,
            f.not_joined
        ),
        (2, 1, 1, 1, 0),
        "{f:?}"
    );
    // The load classifies no pair of this definition (nothing can be withdrawn), and its
    // groups say that too.
    let load = group_at(definition.value_claims(), "f");
    assert_eq!((load.equations, load.root_pairs), (2, 0), "{load:?}");
}

mod hooks;
mod review_one;
mod review_two;
mod scope;
mod split;
mod uninhabited;
mod witness;
