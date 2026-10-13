//! `signFloat` is "the value of the sign bit", and `domains.md` gives the `NaN` literal no sign
//! bit, while every IEEE-like format has NaNs of both signs: the hook is total, so `signFloat`
//! of a NaN has a Bool value in every model, but which one the definition leaves open. Inside an
//! execution (`EvaluationMode::Execution`) k-rust answers `false`; outside one the application
//! stays unevaluated as a defined value, so that no proof verdict reads that choice. Every other
//! sign is determined and evaluated in every mode.

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
  hooked-symbol signFloat{}(SortFloat{}) : SortBool{}
    [function{}(), total{}(), hook{}("FLOAT.sign")]
endmodule []"#;

fn definition() -> BackendDefinition {
    let syntax = parse_definition(FIXTURE).expect("NaN sign fixture should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("NaN sign fixture should internalize")
}

fn sign(token: &str) -> String {
    format!(r#"signFloat{{}}(\dv{{SortFloat{{}}}}("{token}"))"#)
}

fn boolean(value: bool) -> String {
    format!(r#"\dv{{SortBool{{}}}}("{value}")"#)
}

/// The simplification of `source`, and the diagnostics it emitted.
fn simplified(definition: &BackendDefinition, source: &str) -> (Term, Vec<BackendDiagnostic>) {
    let term = internal_term(definition, source);
    let (result, diagnostics) = diagnostic::collect(|| {
        unstopped::simplify(definition, &term, SimplificationOptions::default())
    });
    (
        result.expect("signFloat simplifies without an error").term,
        diagnostics,
    )
}

/// The NaN of binary64, binary32 and a format the backend does not compute.
const NANS: [&str; 5] = ["NaN", "NaNd", "NaNf", "NaNp24x8", "NaNp113x15"];

/// Outside an execution `signFloat` of a NaN stays unevaluated, without the unsupported-hook
/// warning, and is a defined value: its `\ceil` holds.
#[test]
fn the_sign_of_a_nan_stays_unevaluated_and_defined_outside_an_execution() {
    let definition = definition();
    assert_eq!(current(), EvaluationMode::Proof);
    for nan in NANS {
        let source = sign(nan);
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
        .expect("the definedness of signFloat of a NaN simplifies");
        assert_eq!(ceil, Predicate::True, "{source}");
    }
}

/// Inside an execution `signFloat` of a NaN is k-rust's `false`.
#[test]
fn the_sign_of_a_nan_is_false_inside_an_execution() {
    let definition = definition();
    for nan in NANS {
        let (term, _) = with_evaluation(EvaluationMode::Execution, || {
            simplified(&definition, &sign(nan))
        });
        assert_eq!(term, internal_term(&definition, &boolean(false)), "{nan}");
    }
}

/// The sign of every other value is its sign bit, in every mode.
#[test]
fn every_other_sign_is_evaluated_in_every_mode() {
    let definition = definition();
    for mode in [EvaluationMode::Proof, EvaluationMode::Execution] {
        for (token, negative) in [
            ("-0.0", true),
            ("-Infinity", true),
            ("-Infinityf", true),
            ("-1e0p113x15", true),
            ("0.0", false),
            ("Infinityp113x15", false),
            ("1.5f", false),
        ] {
            let (term, _) = with_evaluation(mode, || simplified(&definition, &sign(token)));
            assert_eq!(
                term,
                internal_term(&definition, &boolean(negative)),
                "{mode:?} {token}"
            );
        }
    }
}
