//! A definition's axioms are read as predicates only where they are predicate-shaped.
//!
//! An `\equals` of two terms is their equality; an `\equals` of two predicates (patterns that are
//! all of their sort or empty) is their `\iff`; and `\equals{Bool, R}(P, true)` in a frontend's
//! condition slot (an equation's `requires`, the conjunct a side's root `\and` holds beside the
//! author's pattern), with `P` a connective, is the encoding of "`P` holds", read as `P`. Any
//! other `\equals` has an operand that is a matching-logic connective over terms, which denotes
//! a set of values the backend does not represent, a term read as a predicate means `t = true`,
//! which states something only of a Boolean term, and a connective over terms conjoined to a term
//! is a set of values, not a condition. Such axioms are refused when the definition loads, naming
//! the axiom, rather than read with a meaning they do not have.

use k_rust_kore::kore::parser::parse_definition;

use crate::{
    definition::{BackendDefinition, DefinitionError},
    rule::{Predicate, RewriteRule},
};

fn load(axioms: &str) -> Result<BackendDefinition, DefinitionError> {
    let source = format!(
        r#"[] module TEST
            hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
            hooked-sort SortBool{{}} [hook{{}}("BOOL.Bool"), hasDomainValues{{}}()]
            symbol f{{}}(SortInt{{}}) : SortInt{{}} [function{{}}()]
            symbol g{{}}(SortInt{{}}) : SortInt{{}} [function{{}}()]
            symbol p1{{}}(SortInt{{}}) : SortBool{{}} [function{{}}(), total{{}}(), no-evaluators{{}}()]
            symbol p2{{}}(SortInt{{}}) : SortBool{{}} [function{{}}(), total{{}}(), no-evaluators{{}}()]
            {axioms}
        endmodule []"#
    );
    BackendDefinition::internalize(
        &parse_definition(&source).expect("the definition parses"),
        "TEST",
    )
}

const B1: &str = r#"p1{}(X:SortInt{})"#;
const B2: &str = r#"p2{}(X:SortInt{})"#;
const TRUE: &str = r#"\dv{SortBool{}}("true")"#;
const FALSE: &str = r#"\dv{SortBool{}}("false")"#;

fn int(value: i64) -> String {
    format!(r#"\dv{{SortInt{{}}}}("{value}")"#)
}

/// The function equation `f(X) = 1 requires <requires>`, labelled `eq`.
fn equation(requires: &str) -> String {
    equation_with(requires, &int(1))
}

/// The function equation `f(X) = <rhs> requires <requires>`, labelled `eq`.
fn equation_with(requires: &str, rhs: &str) -> String {
    format!(
        r#"axiom{{R}} \implies{{R}}(
            \and{{R}}({requires}, \and{{R}}(\in{{SortInt{{}}, R}}(X0:SortInt{{}}, X:SortInt{{}}), \top{{R}}())),
            \equals{{SortInt{{}}, R}}(f{{}}(X0:SortInt{{}}), \and{{SortInt{{}}}}({rhs}, \top{{SortInt{{}}}}())))
            [label{{}}("eq")]"#
    )
}

/// The only equation of `f`.
fn equation_of_f(definition: &BackendDefinition) -> &RewriteRule {
    let mut equations = definition
        .function_theory()
        .values()
        .flat_map(|priorities| priorities.values())
        .flatten();
    let equation = equations.next().expect("f has an equation");
    assert!(equations.next().is_none(), "f has one equation");
    equation
}

fn assert_refused_naming_the_axiom(requires: &str) {
    let error = load(&equation(requires)).expect_err(requires);
    assert!(
        matches!(&error, DefinitionError::AxiomReadsTermAsPredicate { axiom, sentence }
            if axiom == "eq" && sentence.0.as_ref() == "TEST"),
        "{requires}: {error:?}"
    );
    let text = error.to_string();
    assert!(text.contains("Axiom eq"), "{text}");
    assert!(text.contains("module TEST"), "{text}");
}

/// `B1 /\ B2 = false` of two Boolean terms is "their intersection is {false}", not the `\iff` of
/// `B1 = true /\ B2 = true` and `false = true`.
#[test]
fn an_equality_of_a_boolean_conjunction_and_false_is_refused() {
    assert_refused_naming_the_axiom(&format!(
        r#"\equals{{SortBool{{}}, R}}(\and{{SortBool{{}}}}({B1}, {B2}), {FALSE})"#
    ));
}

/// `X = 1 \/ 2` states that `{X}` is the set `{1, 2}`, which no value satisfies.
#[test]
fn an_equality_of_a_term_and_a_disjunction_of_terms_is_refused() {
    assert_refused_naming_the_axiom(&format!(
        r#"\equals{{SortInt{{}}, R}}(X:SortInt{{}}, \or{{SortInt{{}}}}({}, {}))"#,
        int(1),
        int(2)
    ));
}

/// The encoding of a condition `B1 #Or B2` at the root of the `requires` is read as the
/// disjunction: the `\iff` of the disjunction of the Boolean terms and `true`.
#[test]
fn the_encoding_of_a_disjunction_at_the_condition_root_is_read_as_the_disjunction() {
    let definition = load(&equation(&format!(
        r#"\equals{{SortBool{{}}, R}}(\or{{SortBool{{}}}}({B1}, {B2}), {TRUE})"#
    )))
    .expect("the encoding loads");
    let requires = equation_of_f(&definition)
        .requires
        .iter()
        .collect::<Vec<_>>();
    let [Predicate::Iff(disjunction, holds)] = requires.as_slice() else {
        panic!("{requires:?}");
    };
    assert!(
        matches!(disjunction.as_ref(), Predicate::Or(operands)
            if operands.len() == 2
                && operands.iter().all(|operand| matches!(operand, Predicate::Term(_)))),
        "{disjunction:?}"
    );
    assert!(matches!(holds.as_ref(), Predicate::Term(_)), "{holds:?}");
}

/// Below the encoding's root its operand is read as written, so an author's
/// `{(B1 #Or B2) #Equals true}` inside it, whose operand is a set of Boolean values, is refused.
#[test]
fn an_equality_with_a_connective_operand_nested_in_the_encoding_is_refused() {
    assert_refused_naming_the_axiom(&format!(
        r#"\equals{{SortBool{{}}, R}}(\not{{SortBool{{}}}}(
            \equals{{SortBool{{}}, SortBool{{}}}}(\or{{SortBool{{}}}}({B1}, {B2}), {TRUE})), {TRUE})"#
    ));
}

/// An `\equals` of two predicates is their `\iff`.
#[test]
fn an_equality_of_two_predicates_loads() {
    load(&equation(
        r#"\equals{SortBool{}, R}(\top{SortBool{}}(), \ceil{SortInt{}, SortBool{}}(g{}(X:SortInt{})))"#,
    ))
    .expect("an equality of two predicates loads");
}

/// A connective over Int terms beside a right-hand side's term is no predicate: conjoined to the
/// term it is a set of Int values, and its operands would be read as `t = true`.
#[test]
fn a_connective_over_int_terms_beside_a_term_is_refused() {
    for (connective, name) in [
        (
            format!(r#"\iff{{SortInt{{}}}}({}, {})"#, int(1), int(2)),
            "iff",
        ),
        (
            format!(
                r#"\or{{SortInt{{}}}}(\not{{SortInt{{}}}}({}), \not{{SortInt{{}}}}({}))"#,
                int(2),
                int(3)
            ),
            "or",
        ),
    ] {
        let rhs = format!(r#"\and{{SortInt{{}}}}({}, {connective})"#, int(1));
        let error = load(&equation_with(r#"\top{R}()"#, &rhs)).expect_err(&connective);
        assert_term_connective(&error, name, "eq");
    }
}

/// `error` refuses the connective `connective` conjoined to a term in the axiom `axiom`.
fn assert_term_connective(error: &DefinitionError, connective: &str, axiom: &str) {
    assert!(
        matches!(
            error,
            DefinitionError::RulePattern(crate::rule::RulePatternError::TermConnectiveInConjunction {
                connective: refused,
                axiom: Some(refused_axiom),
                sentence: Some(sentence),
            }) if *refused == connective && refused_axiom == axiom && sentence.0.as_ref() == "TEST"
        ),
        "{error:?}"
    );
    let text = error.to_string();
    assert!(text.contains(&format!("\\{connective}")), "{text}");
    assert!(text.contains(&format!("the axiom {axiom}")), "{text}");
    assert!(text.contains("module TEST"), "{text}");
}

/// A connective over Int terms under a term-level `\and` of a rewrite's left-hand side is refused
/// naming its connective and the axiom. Its position is the slot's, but a condition there has no
/// term in a predicate position, so it is conjoined to the left-hand side's term.
#[test]
fn a_connective_over_int_terms_in_a_left_hand_side_is_refused() {
    let error = load(&format!(
        r#"axiom{{}} \rewrites{{SortInt{{}}}}(
            \and{{SortInt{{}}}}(X:SortInt{{}}, \implies{{SortInt{{}}}}({}, {})),
            {}) [label{{}}("rw")]"#,
        int(3),
        int(4),
        int(0)
    ))
    .expect_err("the connective is refused");
    assert_term_connective(&error, "implies", "rw");
}

/// A condition conjoined to a term inside a rewrite's left-hand side (here the argument of `f`)
/// is no condition root, so an `\equals(P, true)` there is an author's equality whose operand
/// `P` is a term position, and is refused.
#[test]
fn an_encoding_shaped_equality_conjoined_to_a_matched_term_is_refused() {
    let error = load(&format!(
        r#"axiom{{}} \rewrites{{SortInt{{}}}}(
            \and{{SortInt{{}}}}(
                f{{}}(\and{{SortInt{{}}}}(X:SortInt{{}}, \equals{{SortBool{{}}, SortInt{{}}}}(
                    \or{{SortBool{{}}}}({B1}, {B2}), {TRUE}))),
                \top{{SortInt{{}}}}()),
            {}) [label{{}}("rw")]"#,
        int(0)
    ))
    .expect_err("the conjoined equality is refused");
    assert!(
        matches!(&error, DefinitionError::AxiomReadsTermAsPredicate { axiom, .. } if axiom == "rw"),
        "{error:?}"
    );
}

/// The predicate simplification `{X #Equals 7} => {(B1 #Or B2) #Equals true}`: its right-hand
/// side's first conjunct is the author's predicate, not the frontend's `ensures` slot, so the
/// encoding-shaped equality there is the author's `{B1, B2} = {true}` and is refused.
#[test]
fn an_encoding_shaped_equality_on_a_predicate_simplification_side_is_refused() {
    let encoded =
        format!(r#"\equals{{SortBool{{}}, Q0}}(\or{{SortBool{{}}}}({B1}, {B2}), {TRUE})"#);
    let seven = format!(r#"\equals{{SortInt{{}}, Q0}}(X:SortInt{{}}, {})"#, int(7));
    for (lhs, rhs) in [
        (
            seven.clone(),
            format!(r#"\and{{Q0}}({encoded}, \top{{Q0}}())"#),
        ),
        (
            encoded.clone(),
            format!(r#"\and{{Q0}}({seven}, \top{{Q0}}())"#),
        ),
    ] {
        let error = load(&format!(
            r#"axiom{{R, Q0}} \implies{{R}}(\top{{R}}(), \equals{{Q0, R}}({lhs}, {rhs}))
                [simplification{{}}(""), label{{}}("lem")]"#
        ))
        .expect_err(&lhs);
        assert!(
            matches!(&error, DefinitionError::AxiomReadsTermAsPredicate { axiom, .. } if axiom == "lem"),
            "{lhs} => {rhs}: {error:?}"
        );
    }
}

/// The same encoding in the predicate simplification's `ensures` slot, the last conjunct of its
/// right-hand side, is the frontend's condition and loads.
#[test]
fn the_encoding_in_a_predicate_simplification_ensures_loads() {
    let seven = format!(r#"\equals{{SortInt{{}}, Q0}}(X:SortInt{{}}, {})"#, int(7));
    load(&format!(
        r#"axiom{{R, Q0}} \implies{{R}}(\top{{R}}(), \equals{{Q0, R}}({seven}, \and{{Q0}}({seven},
            \equals{{SortBool{{}}, Q0}}(\or{{SortBool{{}}}}({B1}, {B2}), {TRUE}))))
            [simplification{{}}(""), label{{}}("lem")]"#
    ))
    .expect("the ensures slot's encoding loads");
}

/// The simplification `h(X) => X #And {(B1 #Or B2) #Equals true}`: the conjoined equality is in
/// the author's right-hand side, beside its term, and is refused.
#[test]
fn an_encoding_shaped_equality_conjoined_to_an_equation_right_hand_side_is_refused() {
    let error = load(&format!(
        r#"axiom{{R}} \implies{{R}}(\top{{R}}(), \equals{{SortInt{{}}, R}}(g{{}}(X:SortInt{{}}),
            \and{{SortInt{{}}}}(
                \and{{SortInt{{}}}}(X:SortInt{{}}, \equals{{SortBool{{}}, SortInt{{}}}}(
                    \or{{SortBool{{}}}}({B1}, {B2}), {TRUE})),
                \top{{SortInt{{}}}}())))
            [simplification{{}}(""), label{{}}("lem")]"#
    ))
    .expect_err("the conjoined equality is refused");
    assert!(
        matches!(&error, DefinitionError::AxiomReadsTermAsPredicate { axiom, .. } if axiom == "lem"),
        "{error:?}"
    );
}

/// `B #And #Not(true)` in a rewrite's right-hand side is the term-level set `{B} ∩ {false}`, not
/// the condition `not(true = true)`: refused naming the axiom.
#[test]
fn a_boolean_connective_conjoined_to_a_right_hand_side_term_is_refused() {
    let error = load(&format!(
        r#"axiom{{}} \rewrites{{SortBool{{}}}}(
            \and{{SortBool{{}}}}({B1}, \top{{SortBool{{}}}}()),
            \and{{SortBool{{}}}}(
                \and{{SortBool{{}}}}({B1}, \not{{SortBool{{}}}}({TRUE})),
                \top{{SortBool{{}}}}())) [label{{}}("rw")]"#
    ))
    .expect_err("the conjoined negation is refused");
    assert_term_connective(&error, "not", "rw");
}

/// A negation of a configuration in a rewrite's left-hand side keeps its refusal, which names the
/// axiom.
#[test]
fn a_negated_configuration_names_the_axiom() {
    let error = load(
        r#"axiom{} \rewrites{SortInt{}}(
            \and{SortInt{}}(\not{SortInt{}}(f{}(X:SortInt{})), g{}(X:SortInt{})),
            X:SortInt{}) [label{}("rw")]"#,
    )
    .expect_err("the negation is refused");
    assert!(
        matches!(&error, DefinitionError::RulePattern(crate::rule::RulePatternError::NegatedConfiguration {
            axiom,
            sentence,
        }) if axiom == "rw" && sentence.0.as_ref() == "TEST"),
        "{error:?}"
    );
    assert!(error.to_string().contains("rewrite rw"), "{error}");
}

/// The frontend's encodings of predicate conditions in a rewrite's `requires` and `ensures`
/// slots (`requires {X #Equals 3} ensures #Ceil(g(X))`, as the pinned frontend writes them) are
/// read as their conditions.
#[test]
fn the_encodings_in_a_rewrite_requires_and_ensures_load_as_their_conditions() {
    let definition = load(&format!(
        r#"axiom{{}} \rewrites{{SortInt{{}}}}(
            \and{{SortInt{{}}}}(f{{}}(X:SortInt{{}}), \equals{{SortBool{{}}, SortInt{{}}}}(
                \equals{{SortInt{{}}, SortBool{{}}}}(X:SortInt{{}}, {}), {TRUE})),
            \and{{SortInt{{}}}}(X:SortInt{{}}, \equals{{SortBool{{}}, SortInt{{}}}}(
                \ceil{{SortInt{{}}, SortBool{{}}}}(g{{}}(X:SortInt{{}})), {TRUE})))
            [label{{}}("rw")]"#,
        int(3)
    ))
    .expect("the slots' encodings load");
    let rule = definition
        .rewrite_theory()
        .values()
        .flat_map(|priorities| priorities.values())
        .flatten()
        .next()
        .expect("the rewrite is loaded");
    let encodes = |predicates: Vec<&Predicate>, atom: fn(&Predicate) -> bool| {
        matches!(predicates.as_slice(), [Predicate::Iff(condition, holds)]
            if atom(condition) && matches!(holds.as_ref(), Predicate::Term(_)))
    };
    assert!(
        encodes(rule.requires.iter().collect(), |atom| matches!(
            atom,
            Predicate::Equals(..)
        )),
        "{:?}",
        rule.requires
    );
    assert!(
        encodes(rule.ensures.iter().collect(), |atom| matches!(
            atom,
            Predicate::Ceil(_)
        )),
        "{:?}",
        rule.ensures
    );
}

/// A request has no condition slot: an encoding in it is refused as at base, and so is an
/// equality with a connective operand conjoined inside its term, and a connective over terms
/// conjoined to its term.
#[test]
fn a_request_reads_every_predicate_as_written() {
    let definition = load("").expect("the definition loads");
    let refused = |pattern: &str| {
        let pattern =
            k_rust_kore::kore::parser::parse_pattern(pattern).expect("the pattern parses");
        definition
            .admit_unverified(&pattern, &[])
            .internalize_pattern()
            .expect_err("the request is refused")
    };
    for pattern in [
        format!(
            r#"\and{{SortInt{{}}}}(f{{}}(X:SortInt{{}}), \equals{{SortBool{{}}, SortInt{{}}}}(
                \ceil{{SortInt{{}}, SortBool{{}}}}(g{{}}(X:SortInt{{}})), {TRUE}))"#
        ),
        format!(
            r#"f{{}}(\and{{SortInt{{}}}}(X:SortInt{{}}, \equals{{SortBool{{}}, SortInt{{}}}}(
                \and{{SortBool{{}}}}({B1}, {B2}), {FALSE})))"#
        ),
    ] {
        let error = refused(&pattern);
        assert!(
            matches!(
                error,
                DefinitionError::UnstatedDefinedness(
                    crate::definition::UnstatedDefinedness::TermReadAsPredicate
                )
            ),
            "{pattern}: {error:?}"
        );
    }
    let error = refused(&format!(
        r#"\and{{SortBool{{}}}}({B1}, \not{{SortBool{{}}}}({TRUE}))"#
    ));
    assert!(
        matches!(
            &error,
            DefinitionError::RulePattern(
                crate::rule::RulePatternError::TermConnectiveInConjunction {
                    connective: "not",
                    axiom: None,
                    sentence: None,
                }
            )
        ),
        "{error:?}"
    );
}
