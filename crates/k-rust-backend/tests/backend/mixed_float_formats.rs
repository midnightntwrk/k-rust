//! A Float operation over a binary32 and a binary64 operand has a result whose format domains.md
//! does not name. Inside an execution (`EvaluationMode::Execution`) k-rust rounds the exact
//! result to binary64, the operand format that contains the other; outside one the application
//! stays unevaluated as a defined value, so that no proof verdict reads that choice.

use k_rust_backend::{
    definition::BackendDefinition,
    diagnostic::{self, BackendDiagnostic},
    evaluation::{EvaluationMode, current, with_evaluation},
    rule::Predicate,
    simplify::SimplificationOptions,
    smt::NoSolver,
    term::Term,
};
use k_rust_kore::kore::parser::parse_definition;

use crate::support::{internal_term, unstopped};

const FIXTURE: &str = r#"[]
module MAIN
  hooked-sort SortFloat{} [hook{}("FLOAT.Float"), hasDomainValues{}()]
  hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
  hooked-symbol divFloat{}(SortFloat{}, SortFloat{}) : SortFloat{}
    [function{}(), hook{}("FLOAT.div")]
  hooked-symbol addFloat{}(SortFloat{}, SortFloat{}) : SortFloat{}
    [function{}(), hook{}("FLOAT.add")]
  hooked-symbol maxFloat{}(SortFloat{}, SortFloat{}) : SortFloat{}
    [function{}(), hook{}("FLOAT.max")]
  hooked-symbol gtFloat{}(SortFloat{}, SortFloat{}) : SortBool{}
    [function{}(), hook{}("FLOAT.gt")]
endmodule []"#;

fn definition() -> BackendDefinition {
    let syntax = parse_definition(FIXTURE).expect("mixed Float fixture should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("mixed Float fixture should internalize")
}

fn float(token: &str) -> String {
    format!(r#"\dv{{SortFloat{{}}}}("{token}")"#)
}

fn apply(symbol: &str, left: &str, right: &str) -> String {
    format!("{symbol}{{}}({}, {})", float(left), float(right))
}

/// The simplification of `source`, and the diagnostics it emitted.
fn simplified(definition: &BackendDefinition, source: &str) -> (Term, Vec<BackendDiagnostic>) {
    let term = internal_term(definition, source);
    let (result, diagnostics) = diagnostic::collect(|| {
        unstopped::simplify(definition, &term, SimplificationOptions::default())
    });
    (
        result
            .expect("a Float application simplifies without an error")
            .term,
        diagnostics,
    )
}

const BINARY32: [&str; 3] = ["0.1f", "0.1p24x8", "0.1p024x008"];
const BINARY64: [&str; 3] = ["2.0", "2.0d", "2.0p53x11"];

/// Every spelling of a binary32 operand against every spelling of a binary64 one, in both orders.
fn mixed_pairs() -> Vec<(&'static str, &'static str)> {
    let mut pairs = Vec::new();
    for single in BINARY32 {
        for double in BINARY64 {
            pairs.push((single, double));
            pairs.push((double, single));
        }
    }
    pairs
}

/// Outside an execution a mixed `/Float` stays unevaluated, without the unsupported-hook
/// warning, and is a defined value: its `\ceil` holds. Every spelling of each format is read as
/// that format, so none slips past to be evaluated.
#[test]
fn a_mixed_format_operation_stays_unevaluated_and_defined_outside_an_execution() {
    let definition = definition();
    assert_eq!(current(), EvaluationMode::Proof);
    for (left, right) in mixed_pairs() {
        let source = apply("divFloat", left, right);
        let (term, diagnostics) = simplified(&definition, &source);
        assert_eq!(
            term,
            internal_term(&definition, &source),
            "{source}: {term:?}"
        );
        assert!(diagnostics.is_empty(), "{source}: {diagnostics:?}");
        let ceil = unstopped::simplify_predicate_with_solver(
            &definition,
            &Predicate::Ceil(term),
            &[],
            SimplificationOptions::default(),
            &NoSolver,
        )
        .expect("the definedness of a mixed Float operation simplifies");
        assert_eq!(ceil, Predicate::True, "{source}");
    }
    for symbol in ["addFloat", "maxFloat"] {
        let source = apply(symbol, "0.1f", "0.2");
        let (term, _) = simplified(&definition, &source);
        assert_eq!(term, internal_term(&definition, &source), "{source}");
    }
}

/// Inside an execution a mixed `/Float` is the exact quotient rounded once to binary64, for
/// every spelling and order.
#[test]
fn a_mixed_format_operation_rounds_to_binary64_inside_an_execution() {
    let definition = definition();
    for (left, right) in mixed_pairs() {
        let source = apply("divFloat", left, right);
        let expected = if left.starts_with("0.1") {
            "5.0000000745058060e-02p53x11"
        } else {
            "1.9999999701976780e+01p53x11"
        };
        let (term, _) = with_evaluation(EvaluationMode::Execution, || {
            simplified(&definition, &source)
        });
        assert_eq!(
            term,
            internal_term(&definition, &float(expected)),
            "{source}"
        );
    }
}

/// One format is evaluated in every mode, and so is a comparison of two formats, which needs no
/// result format.
#[test]
fn one_format_and_mixed_comparisons_are_evaluated_in_every_mode() {
    let definition = definition();
    for mode in [EvaluationMode::Proof, EvaluationMode::Execution] {
        let (term, _) = with_evaluation(mode, || {
            simplified(&definition, &apply("divFloat", "0.1f", "2.0f"))
        });
        assert_eq!(
            term,
            internal_term(&definition, &float("5.00000007e-02p24x8")),
            "{mode:?}"
        );
        let (term, _) = with_evaluation(mode, || {
            simplified(&definition, &apply("gtFloat", "0.1f", "0.1"))
        });
        assert_eq!(
            term,
            internal_term(&definition, r#"\dv{SortBool{}}("true")"#),
            "{mode:?}"
        );
    }
}
