//! A definition's axioms are read as predicates only where they are predicate-shaped.
//!
//! An `\equals` of two terms is their equality; an `\equals` of two predicates (patterns that are
//! all of their sort or empty) is their `\iff`; and `\equals{Bool, R}(P, true)` at the root of a
//! condition, with `P` a connective, is the encoding of "`P` holds", read as `P`. Any other
//! `\equals` has an operand that is a matching-logic connective over terms, which denotes a set
//! of values the backend does not represent, and a term read as a predicate means `t = true`,
//! which states something only of a Boolean term. Such axioms are refused when the definition
//! loads, naming the axiom, rather than read with a meaning they do not have.

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

/// A connective over Int terms beside a right-hand side's term is no predicate: its operands
/// would be read as `t = true`, which states nothing of an Int.
#[test]
fn a_connective_over_int_terms_beside_a_term_is_refused() {
    for connective in [
        format!(r#"\iff{{SortInt{{}}}}({}, {})"#, int(1), int(2)),
        format!(
            r#"\or{{SortInt{{}}}}(\not{{SortInt{{}}}}({}), \not{{SortInt{{}}}}({}))"#,
            int(2),
            int(3)
        ),
    ] {
        let rhs = format!(r#"\and{{SortInt{{}}}}({}, {connective})"#, int(1));
        let error = load(&equation_with(r#"\top{R}()"#, &rhs)).expect_err(&connective);
        assert!(
            matches!(
                &error,
                DefinitionError::RulePattern(crate::rule::RulePatternError::NonBoolTermAsPredicate {
                    sort,
                    axiom: Some(axiom),
                    sentence: Some(_),
                }) if axiom == "eq" && sort.to_string() == "SortInt{}"
            ),
            "{connective}: {error:?}"
        );
        assert!(error.to_string().contains("SortInt{}"), "{error}");
        assert!(error.to_string().contains("eq"), "{error}");
    }
}

/// A connective over Int terms under a term-level `\and` of a rewrite's left-hand side is refused
/// naming its connective and the axiom's sentence.
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
    assert!(
        matches!(
            &error,
            DefinitionError::RulePattern(crate::rule::RulePatternError::TermConnectiveInConjunction {
                connective: "implies",
                sentence,
            }) if sentence.0.as_ref() == "TEST"
        ),
        "{error:?}"
    );
    assert!(error.to_string().contains("\\implies"), "{error}");
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
