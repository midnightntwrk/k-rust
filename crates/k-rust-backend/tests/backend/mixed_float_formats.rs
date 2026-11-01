//! A Float operation over a binary32 and a binary64 operand has a result whose format domains.md
//! does not name. Inside an execution (`EvaluationMode::Execution`) k-rust rounds the exact
//! result to binary64, the operand format that contains the other; outside one the application
//! stays unevaluated as a defined value, so that no proof verdict reads that choice.

use k_rust_backend::{
    definition::BackendDefinition,
    diagnostic::{self, BackendDiagnostic},
    evaluation::{EvaluationMode, current, with_evaluation},
    ill_formed::IllFormed,
    rule::Predicate,
    simplify::SimplificationOptions,
    smt::NoSolver,
    term::Term,
};
use k_rust_domain::float::FloatFormat;
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

/// A definition with one nullary function `head` of sort `Float` per pair of `equations`, each
/// defined by its equation `head() = right` labelled `head`. `seed()` and `degree()` are `Int`
/// functions without equations, so no load folds what holds them.
fn equations_definition(equations: &[(&str, String)]) -> BackendDefinition {
    let symbols = equations
        .iter()
        .map(|(head, _)| format!("  symbol {head}{{}}() : SortFloat{{}} [function{{}}()]\n"))
        .collect::<String>();
    let axioms = equations
        .iter()
        .map(|(head, right)| {
            format!(
                "  axiom{{R}} \\implies{{R}}(\\and{{R}}(\\top{{R}}(), \\top{{R}}()), \\equals{{SortFloat{{}}, R}}({head}{{}}(), \\and{{SortFloat{{}}}}({right}, \\top{{SortFloat{{}}}}()))) [label{{}}(\"{head}\")]\n"
            )
        })
        .collect::<String>();
    let source = format!(
        r#"[]
module MAIN
  hooked-sort SortFloat{{}} [hook{{}}("FLOAT.Float"), hasDomainValues{{}}()]
  hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
  hooked-symbol addFloat{{}}(SortFloat{{}}, SortFloat{{}}) : SortFloat{{}}
    [function{{}}(), hook{{}}("FLOAT.add")]
  hooked-symbol int2Float{{}}(SortInt{{}}, SortInt{{}}, SortInt{{}}) : SortFloat{{}}
    [function{{}}(), hook{{}}("FLOAT.int2float")]
  hooked-symbol rootFloat{{}}(SortFloat{{}}, SortInt{{}}) : SortFloat{{}}
    [function{{}}(), hook{{}}("FLOAT.root")]
  symbol seed{{}}() : SortInt{{}} [function{{}}()]
  symbol degree{{}}() : SortInt{{}} [function{{}}()]
{symbols}{axioms}endmodule []"#
    );
    let syntax = parse_definition(&source).expect("the equations should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("the equations should internalize")
}

fn int(value: &str) -> String {
    format!(r#"\dv{{SortInt{{}}}}("{value}")"#)
}

/// The labels of the equations the load names as mixed-format applications, each with the two
/// formats it names, in the order the load names them.
fn named_mixed(definition: &BackendDefinition) -> Vec<(String, FloatFormat, FloatFormat)> {
    k_rust_backend::ill_formed::ill_formed_uses(definition)
        .into_iter()
        .map(|found| match found.found {
            IllFormed::MixedFormats { left, right, .. } => (
                found
                    .attributes
                    .label
                    .clone()
                    .expect("every equation is labelled"),
                left,
                right,
            ),
            other => panic!("only mixed applications are written: {other:?}"),
        })
        .collect()
}

/// The load's scan for ill-formed Float applications reads each node's evident format once: a
/// left-nested chain of 20,000 binary32 additions under a binary64 operand is named once, as
/// the outermost application, and the scan takes a time linear in the chain (it read the
/// chain's whole left spine again at every level, quadratic in its depth, and recursed once per
/// level on the calling thread).
#[test]
fn the_load_reads_the_formats_of_a_deep_float_chain_in_linear_time() {
    let mut chain = format!("int2Float{{}}(seed{{}}(), {}, {})", int("24"), int("8"));
    for _ in 0..20_000 {
        chain = format!("addFloat{{}}({chain}, {})", float("1.0f"));
    }
    let chain = format!("addFloat{{}}({chain}, {})", float("2.0"));
    let definition = equations_definition(&[("chain", chain)]);
    let start = std::time::Instant::now();
    let named = named_mixed(&definition);
    let elapsed = start.elapsed();
    assert_eq!(
        named,
        vec![(
            "chain".to_owned(),
            FloatFormat::of(24, 8),
            FloatFormat::of(53, 11)
        )]
    );
    assert!(
        elapsed < std::time::Duration::from_secs(5),
        "the scan of a 20,000-level chain took {elapsed:?}"
    );
}

/// `rootFloat` has its radicand's format only where the amendments fix its result (AM-4, AM-11):
/// a positive odd degree, or a positive even one at a radicand literal whose sign bit is clear.
/// A degree of 0 or below, an even root of a negative value or of `-0.0`, a degree the form does
/// not fix and an even root of a radicand whose sign the form does not fix are outside-domain in
/// some model, where every `Float`, of either format, is a value, so their sum with a binary64
/// operand is not named.
#[test]
fn a_root_has_its_operands_format_only_where_the_amendments_fix_its_result() {
    let unknown = format!("int2Float{{}}(seed{{}}(), {}, {})", int("24"), int("8"));
    let sum = |radicand: &str, degree: &str| {
        format!(
            "addFloat{{}}(rootFloat{{}}({radicand}, {degree}), {})",
            float("1.0")
        )
    };
    let equations = [
        ("even", sum(&float("4.0f"), &int("2"))),
        ("evenzero", sum(&float("0.0f"), &int("2"))),
        ("evennan", sum(&float("NaNf"), &int("2"))),
        ("odd", sum(&float("-8.0f"), &int("3"))),
        ("oddunknown", sum(&unknown, &int("3"))),
        ("zero", sum(&float("4.0f"), &int("0"))),
        ("negative", sum(&float("4.0f"), &int("-3"))),
        ("symbolic", sum(&float("4.0f"), "degree{}()")),
        ("evennegative", sum(&float("-8.0f"), &int("2"))),
        ("evenminuszero", sum(&float("-0.0f"), &int("2"))),
        ("evenunknown", sum(&unknown, &int("2"))),
    ];
    let definition = equations_definition(&equations);
    let mut named = named_mixed(&definition)
        .into_iter()
        .map(|(label, left, right)| {
            assert_eq!(
                (left, right),
                (FloatFormat::of(24, 8), FloatFormat::of(53, 11))
            );
            label
        })
        .collect::<Vec<_>>();
    named.sort();
    assert_eq!(named, ["even", "evennan", "evenzero", "odd", "oddunknown"]);
}
