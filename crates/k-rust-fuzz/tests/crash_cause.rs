//! Halts read by their structured cause (FZ-CRASH-CAUSE): a leaf that halts on a builtin failure
//! (a hook declared at a signature its builtin does not take) is a crash finding of kind
//! `internal-halt`, while a simplification bound and a query the solver could not answer stay
//! `unsupported` with their own reasons and no crash.
//!
//! The tests read the report's canonical JSON, the form every client reads.

mod support;

use std::sync::Arc;

use k_rust_fuzz::{
    Budget, CallerIdentity, Campaign, CampaignSpec, CaseOptions, Definitions, HoleDecl,
    HoleLocation, ProgramInput, ProposerConfig, SpanAddress, Target, TargetKind,
    spec::DEFAULT_REJECTION_CAP,
    target::{PatternAt, PatternTarget},
    values::{Constraints, GenerationBounds, IntRange},
};
use num_bigint::BigInt;
use serde_json::Value as Json;
use support::HALTCAUSE;

/// A campaign over `program`'s `Int` hole at `literal` (in `0..=9`), against a pattern no run
/// reaches, with `options`, for `cases` cases; the report as JSON.
fn campaign(program: &str, literal: &str, options: CaseOptions, cases: u64) -> Json {
    let compiled = HALTCAUSE.compiled();
    let spec = CampaignSpec {
        definitions: Definitions {
            baseline: Arc::new(compiled.definition()),
            mutant: None,
        },
        program: ProgramInput::Source(compiled.program_source(program)),
        holes: vec![HoleDecl {
            name: "N".into(),
            sort: "Int".into(),
            location: HoleLocation::Span(SpanAddress {
                program: program.into(),
                line: None,
                column: None,
                find: literal.into(),
                literal: "3".into(),
            }),
            constraints: Constraints {
                range: Some(IntRange {
                    min: Some(BigInt::from(0)),
                    max: Some(BigInt::from(9)),
                }),
                ..Constraints::default()
            },
            allow_refused_sort: false,
        }],
        target: Target {
            kind: TargetKind::Pattern(PatternTarget {
                pattern: "<s> 1000 </s>".into(),
                at: PatternAt::Final,
            }),
            run_to_completion: false,
            negated_property: false,
            data_end: false,
            comparable: false,
            query_confirmable: false,
        },
        options,
        proposers: ProposerConfig::default(),
        bounds: GenerationBounds::default(),
        rejection_cap: DEFAULT_REJECTION_CAP,
        seed: 5,
        identity: CallerIdentity {
            k_rust_revision: "fz26-test".into(),
            thread_stack_size: None,
        },
    };
    let report = Campaign::new(spec)
        .expect("the campaign is valid")
        .run(Budget::Cases(cases), None);
    serde_json::from_str(&report.to_canonical_json()).expect("the report is JSON")
}

/// The report's `totals.unsupported-reasons` as `(reason, count)` pairs.
fn unsupported_reasons(report: &Json) -> Vec<(String, u64)> {
    report["totals"]["unsupported-reasons"]
        .as_object()
        .map(|reasons| {
            reasons
                .iter()
                .map(|(reason, count)| (reason.clone(), count.as_u64().unwrap_or(0)))
                .collect()
        })
        .unwrap_or_default()
}

/// The number of `unsupported` cases.
fn unsupported(report: &Json) -> u64 {
    report["totals"]["classes"]["unsupported"]
        .as_u64()
        .unwrap_or(0)
}

/// A hook declared at an arity its builtin does not take is a defect of the hook's declaration
/// or of k-rust (terms are sort-checked, so such a declaration should have been refused): every
/// case is `unsupported` with the reason `internal-halt`, and the report keeps one crash of kind
/// `internal-halt` whose site names the failure and the hook, not the input, re-run on a fresh
/// backend and reproduced.
#[test]
fn a_builtin_failure_is_an_internal_halt_crash() {
    let report = campaign("haltcause/arity.pgm", "arity(3)", CaseOptions::default(), 6);
    let cases = unsupported(&report);
    assert_eq!(cases, 6, "{}", report["totals"]);
    assert_eq!(
        unsupported_reasons(&report),
        [("internal-halt".to_owned(), cases)],
        "{}",
        report["totals"]
    );
    let crashes = report["crashes"].as_array().expect("one crash finding");
    assert_eq!(crashes.len(), 1, "{crashes:?}");
    let crash = &crashes[0];
    assert_eq!(
        crash["signature"],
        serde_json::json!({
            "kind": "internal-halt",
            "side": "baseline",
            "stage": "execute",
            "site-kind": "cause",
            "site": "builtin:wrong-arity:INT.add",
        }),
        "{crash}"
    );
    assert_eq!(crash["phase"], "case", "{crash}");
    assert_eq!(crash["reproduced"], true, "{crash}");
    assert_eq!(crash["count"], cases, "{crash}");
    assert!(
        crash["krun-command"].is_string(),
        "an execute crash has a krun line: {crash}"
    );
    // No backend panicked, so nothing was rebuilt; the crash work is the confirmation's and
    // the shrinking's alone.
    assert!(
        report["totals"]["crash-work"].as_u64().unwrap_or(0) > 0,
        "{}",
        report["totals"]
    );
}

/// A simplification bound is an option, no defect: the leaf of a simplification that never
/// ends keeps its partial term marked exhausted, the cases stay `unsupported` with the reason
/// `iteration-exhaustion`, and no crash is recorded. (A leaf halted on the bound itself,
/// `iteration-limit`, reads `halt-iteration-limit` and is no crash either: the exec unit tests
/// construct one, since no execution of a K definition was found to give one.)
#[test]
fn a_simplification_bound_is_no_crash() {
    let options = CaseOptions {
        max_simplification_iterations: 5,
        ..CaseOptions::default()
    };
    let report = campaign("haltcause/loop.pgm", "loop(3)", options, 4);
    let cases = unsupported(&report);
    assert_eq!(cases, 4, "{}", report["totals"]);
    assert_eq!(
        unsupported_reasons(&report),
        [("iteration-exhaustion".to_owned(), cases)],
        "{}",
        report["totals"]
    );
    assert!(report.get("crashes").is_none(), "{}", report["crashes"]);
}

/// A rule condition over a function smt-hooked to an operator SMT-LIB lacks: the solver rejects
/// the script for text the definition supplied, which is no defect of k-rust, so the cases stay
/// `unsupported` with the reason `halt-smt` and no crash. Without a solver the condition is
/// undecided before any script is written (`halt-indeterminate`).
#[test]
fn a_script_rejected_for_the_definitions_smt_text_is_no_crash() {
    let report = campaign("haltcause/smt.pgm", "smt(3)", CaseOptions::default(), 3);
    let cases = unsupported(&report);
    assert_eq!(cases, 3, "{}", report["totals"]);
    let expected = if cfg!(feature = "z3") {
        "halt-smt"
    } else {
        "halt-indeterminate"
    };
    assert_eq!(
        unsupported_reasons(&report),
        [(expected.to_owned(), cases)],
        "{}",
        report["totals"]
    );
    assert!(report.get("crashes").is_none(), "{}", report["crashes"]);
}
