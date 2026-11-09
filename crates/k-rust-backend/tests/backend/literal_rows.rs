//! A function equation whose left-hand side has a literal where the subject has a term of the
//! literal's sort (`decode(118)` against `decode(Op)`) matches the subject exactly where that term
//! equals the literal. An `owise` equation's premise negates the left-hand side, so the `owise`
//! equation applies where the path condition refutes that equality, for every such row, and
//! only there: where one row may match, the application stays unevaluated.

#![cfg(feature = "z3")]

use k_rust_backend::{
    definition::BackendDefinition, rule::Predicate, simplify::SimplificationOptions, smt::Z3Solver,
    term::Term,
};
use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use crate::support::{internal_term, unstopped::simplify_with_solver};

/// `decode(118) = 1` and `decode(24) = 2` above `decode(X) = 0` (`owise`), and `pick(N, 7) = 3`
/// above `pick(N, M) = 4` (`owise`), whose literal row also binds `N`.
fn definition() -> BackendDefinition {
    let row = |head: &str, arguments: &str, value: i64, attributes: &str| {
        format!(
            r#"
            axiom{{R}} \implies{{R}}(
                \and{{R}}(\top{{R}}(), {arguments}),
                \equals{{SortInt{{}}, R}}({head}, \and{{SortInt{{}}}}(\dv{{SortInt{{}}}}("{value}"), \top{{SortInt{{}}}}()))
            ) [{attributes}]"#
        )
    };
    let argument = |position: usize, pattern: &str, rest: &str| {
        format!(r#"\and{{R}}(\in{{SortInt{{}}, R}}(X{position}:SortInt{{}}, {pattern}), {rest})"#)
    };
    let decode = |pattern: &str, value: i64, attributes: &str| {
        row(
            "decode{}(X0:SortInt{})",
            &argument(0, pattern, r"\top{R}()"),
            value,
            attributes,
        )
    };
    let pick = |pattern: &str, value: i64, attributes: &str| {
        row(
            "pick{}(X0:SortInt{}, X1:SortInt{})",
            &argument(0, "VarN:SortInt{}", &argument(1, pattern, r"\top{R}()")),
            value,
            attributes,
        )
    };
    let source = format!(
        r#"[] module MAIN
            hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
            hooked-sort SortBool{{}} [hook{{}}("BOOL.Bool"), hasDomainValues{{}}()]
            hooked-symbol eqInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
                [function{{}}(), total{{}}(), hook{{}}("INT.eq"), smt-hook{{}}("=")]
            hooked-symbol geInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
                [function{{}}(), total{{}}(), hook{{}}("INT.ge"), smt-hook{{}}(">=")]
            hooked-symbol add{{}}(SortInt{{}}, SortInt{{}}) : SortInt{{}}
                [function{{}}(), total{{}}(), hook{{}}("INT.add"), smt-hook{{}}("+")]
            symbol decode{{}}(SortInt{{}}) : SortInt{{}} [function{{}}(), total{{}}()]
            symbol pick{{}}(SortInt{{}}, SortInt{{}}) : SortInt{{}} [function{{}}(), total{{}}()]
            {}
            {}
            {}
            {}
            {}
        endmodule []"#,
        decode(r#"\dv{SortInt{}}("118")"#, 1, r#"label{}("decode-118")"#),
        decode(r#"\dv{SortInt{}}("24")"#, 2, r#"label{}("decode-24")"#),
        decode("VarX:SortInt{}", 0, r#"label{}("decode-owise"), owise{}()"#),
        pick(r#"\dv{SortInt{}}("7")"#, 3, r#"label{}("pick-7")"#),
        pick("VarM:SortInt{}", 4, r#"label{}("pick-owise"), owise{}()"#),
    );
    let syntax = parse_definition(&source).expect("the definition parses");
    BackendDefinition::internalize(&syntax, "MAIN").expect("the definition internalizes")
}

/// The path condition that the Bool term `condition` is `value`.
fn fact(definition: &BackendDefinition, condition: &str, value: bool) -> Predicate {
    let syntax = parse_pattern(&format!(
        r#"\equals{{SortBool{{}}, SortInt{{}}}}({condition}, \dv{{SortBool{{}}}}("{value}"))"#
    ))
    .expect("the path condition parses");
    definition
        .admit_unverified(&syntax, &[])
        .internalize_predicate()
        .expect("the path condition internalizes")
        .0
}

fn int(value: i64) -> String {
    format!(r#"\dv{{SortInt{{}}}}("{value}")"#)
}

/// `source` simplified under the path condition `known`: the result and the equations applied.
fn simplified(
    definition: &BackendDefinition,
    source: &str,
    known: &[Predicate],
) -> (Term, Vec<String>) {
    let solver = Z3Solver::new(definition).unwrap();
    let result = simplify_with_solver(
        definition,
        &internal_term(definition, source),
        known,
        SimplificationOptions::default(),
        &solver,
    )
    .unwrap_or_else(|error| panic!("{source}: {error:?}"));
    (result.term, result.applied_rules.to_vec())
}

fn assert_kept(definition: &BackendDefinition, source: &str, known: &[Predicate]) {
    let (term, applied) = simplified(definition, source, known);
    assert_eq!(
        term,
        internal_term(definition, source),
        "{source}: {known:?}"
    );
    assert!(applied.is_empty(), "{source}: {applied:?}");
}

fn assert_evaluates(
    definition: &BackendDefinition,
    source: &str,
    known: &[Predicate],
    expected: i64,
    rule: &str,
) {
    let (term, applied) = simplified(definition, source, known);
    assert_eq!(
        term,
        internal_term(definition, &int(expected)),
        "{source}: {known:?}"
    );
    assert_eq!(applied, [rule], "{source}: {known:?}");
}

/// `decode(Op)`: with nothing known, or where only one literal row is refuted, a row may match
/// and the application stays; where the path condition refutes both rows (`Op` differs from
/// both, or `Op >= 256`) the `owise` equation applies.
#[test]
fn an_owise_equation_applies_where_every_literal_row_is_refuted() {
    let definition = definition();
    let subject = "decode{}(VarOp:SortInt{})";
    let differs = |value: i64| {
        fact(
            &definition,
            &format!("eqInt{{}}(VarOp:SortInt{{}}, {})", int(value)),
            false,
        )
    };
    assert_kept(&definition, subject, &[]);
    assert_kept(&definition, subject, &[differs(118)]);
    assert_evaluates(
        &definition,
        subject,
        &[differs(118), differs(24)],
        0,
        "decode-owise",
    );
    let high = fact(
        &definition,
        &format!("geInt{{}}(VarOp:SortInt{{}}, {})", int(256)),
        true,
    );
    assert_evaluates(&definition, subject, &[high], 0, "decode-owise");
}

/// A computed argument: `decode(Op +Int 100)` matches a row only where `Op +Int 100` equals its
/// literal, so `Op >= 0` refutes the row at 24 but not the one at 118, and the application stays,
/// while `Op >= 20` refutes both, and the `owise` equation applies.
#[test]
fn a_literal_row_against_a_computed_argument_is_refuted_by_its_value() {
    let definition = definition();
    let subject = format!("decode{{}}(add{{}}(VarOp:SortInt{{}}, {}))", int(100));
    let at_least = |bound: i64| {
        fact(
            &definition,
            &format!("geInt{{}}(VarOp:SortInt{{}}, {})", int(bound)),
            true,
        )
    };
    assert_kept(&definition, &subject, &[at_least(0)]);
    assert_evaluates(&definition, &subject, &[at_least(20)], 0, "decode-owise");
}

/// A literal row whose other argument binds a variable: `pick(A, B)` matches `pick(N, 7)` with
/// `N = A` exactly where `B = 7`.
#[test]
fn a_literal_row_beside_a_bound_variable_is_refuted_by_its_literal_alone() {
    let definition = definition();
    let subject = "pick{}(VarA:SortInt{}, VarB:SortInt{})";
    assert_kept(&definition, subject, &[]);
    let differs = fact(
        &definition,
        &format!("eqInt{{}}(VarB:SortInt{{}}, {})", int(7)),
        false,
    );
    assert_evaluates(&definition, subject, &[differs], 4, "pick-owise");
}
