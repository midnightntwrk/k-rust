//! Unit tests of the critical-pair unifier (one per row of the overlap inventory), and of the
//! check on small definitions.

use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use super::{
    UnjoinedReason,
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
    BackendDefinition::internalize(&syntax, "MAIN").expect("the definition internalizes")
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

/// Whether every rewrite rule of a definition whose value production `vp` the check withdraws
/// (`vp(z) = m(z)` beside `vp(z) = m(s(z))`) is marked as preserving definedness; its one rule
/// rewrites `m(s(z))` to the irreducible `vp(s(z))`.
fn withdrawn_rule_preserves_definedness() -> bool {
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
        .all(|rule| rule.rule.attributes.preserves_definedness)
}

/// The rewrite rules' definedness is discharged after the check and reads its verdict: the
/// right-hand side of the rule is an application of a withdrawn head, so the rule keeps its
/// obligation.
#[test]
fn a_rewrite_rule_over_a_withdrawn_head_keeps_its_definedness_obligation() {
    assert!(!withdrawn_rule_preserves_definedness());
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
        withdrawn_rule_preserves_definedness
    ));
}

mod review_one;
mod review_two;
