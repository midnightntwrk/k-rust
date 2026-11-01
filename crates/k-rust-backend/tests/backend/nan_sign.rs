//! `signFloat` is "the value of the sign bit", and a format has one NaN, which every spelling of
//! `NaN` in one format names (determined by `Float2String`'s round trip through the one `NaN`
//! lexeme per format), whose sign bit `domains.md` does not give: the hook is total, so
//! `signFloat` of a NaN has a Bool value in every model, but which one the definition leaves
//! open (class `nan-sign`). Inside an
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
  hooked-symbol mulFloat{}(SortFloat{}, SortFloat{}) : SortFloat{}
    [function{}(), total{}(), hook{}("FLOAT.mul")]
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
///
/// GAP K3 re-pin: the infinities are also reached by the product's overflow, which `fp.mul` with
/// `roundNearestTiesToEven` fixes. GAP A2: the `Infinity` lexemes K3 removed are back beside them,
/// an `Infinity` lexeme naming the infinity of its sign (`docs/amendments.md`, AM-8), so a request
/// holding one is evaluated in every mode; `Infinityp113x15` is of a format whose arithmetic
/// k-rust does not compute, its sign read from the token.
#[test]
fn every_other_sign_is_evaluated_in_every_mode() {
    let definition = definition();
    let float = |token: &str| format!(r#"\dv{{SortFloat{{}}}}("{token}")"#);
    let product =
        |left: &str, right: &str| format!("mulFloat{{}}({}, {})", float(left), float(right));
    for mode in [EvaluationMode::Proof, EvaluationMode::Execution] {
        for (operand, negative) in [
            (float("-0.0"), true),
            (product("-1.0e308", "10.0"), true),
            (product("-3.0e38f", "10.0f"), true),
            (float("-1e0p113x15"), true),
            (float("-Infinity"), true),
            (float("-Infinityf"), true),
            (float("0.0"), false),
            (float("Infinityp113x15"), false),
            (product("1.0e308", "10.0"), false),
            (float("1e0p113x15"), false),
            (float("1.5f"), false),
        ] {
            let source = format!("signFloat{{}}({operand})");
            let (term, _) = with_evaluation(mode, || simplified(&definition, &source));
            assert_eq!(
                term,
                internal_term(&definition, &boolean(negative)),
                "{mode:?} {operand}"
            );
        }
    }
}
