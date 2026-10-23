//! Cases that cannot be judged say why (FZ-UNSUPPORTED): the report counts `unsupported` and
//! `baseline-incomplete` cases per reason, the no-witness statement names the largest with its
//! remedy, and a threaded definition's finished runs are natural ends under the every-`<k>`
//! default (ARCHITECTURE 5.2, 5.3).

mod support;

use std::{collections::BTreeMap, sync::Arc};

use k_rust_fuzz::{
    Budget, CallerIdentity, Campaign, CampaignSpec, CaseOptions, Definitions, HoleDecl,
    HoleLocation, OutcomeClass, ProgramInput, ProposerConfig, SpanAddress, Target, TargetKind,
    exec::{NormalEndKind, UnjudgedReason},
    report::{FuzzReport, NormalEnds},
    spec::DEFAULT_REJECTION_CAP,
    target::{DifferentialTarget, PatternAt, PatternTarget},
    values::{Constraints, GenerationBounds, IntRange},
};
use num_bigint::BigInt;
use support::{COIN, COIN_FUNC, Fixture, TAINT, THREADS};

/// A campaign over one `Int` hole at `literal` in `find` of `program`, ranging over
/// `min..=max`, against `target`, on `baseline` (and `mutant` for a differential target).
#[expect(
    clippy::too_many_arguments,
    reason = "one campaign, spelled out per test"
)]
fn spec(
    baseline: &'static Fixture,
    mutant: Option<&'static Fixture>,
    program: &str,
    find: &str,
    literal: &str,
    (min, max): (i64, i64),
    target: TargetKind,
    options: CaseOptions,
) -> CampaignSpec {
    CampaignSpec {
        definitions: Definitions {
            baseline: Arc::new(baseline.compiled().definition()),
            mutant: mutant.map(|mutant| Arc::new(mutant.compiled().definition())),
        },
        program: ProgramInput::Source(baseline.compiled().program_source(program)),
        holes: vec![HoleDecl {
            name: "N".into(),
            sort: "Int".into(),
            location: HoleLocation::Span(SpanAddress {
                program: program.into(),
                line: None,
                find: find.into(),
                literal: literal.into(),
            }),
            constraints: Constraints {
                range: Some(IntRange {
                    min: Some(BigInt::from(min)),
                    max: Some(BigInt::from(max)),
                }),
                ..Constraints::default()
            },
            allow_refused_sort: false,
        }],
        target: Target {
            kind: target,
            run_to_completion: false,
            negated_property: false,
            data_end: true,
        },
        options,
        proposers: ProposerConfig::default(),
        bounds: GenerationBounds::default(),
        rejection_cap: DEFAULT_REJECTION_CAP,
        seed: 11,
        identity: CallerIdentity {
            k_rust_revision: "fz26-test".into(),
            thread_stack_size: None,
        },
    }
}

fn unreachable_pattern() -> TargetKind {
    TargetKind::Pattern(PatternTarget {
        pattern: "<out> 1000 </out>".into(),
        at: PatternAt::Final,
    })
}

fn run(spec: CampaignSpec, cases: u64) -> FuzzReport {
    Campaign::new(spec)
        .expect("the campaign is valid")
        .run(Budget::Cases(cases), None)
}

fn count(report: &FuzzReport, class: OutcomeClass) -> u64 {
    report.totals.classes.get(&class).copied().unwrap_or(0)
}

/// Every unjudged count is split by reason, and the splits add up.
fn assert_reasons_sum(report: &FuzzReport) {
    let sum = |reasons: &BTreeMap<UnjudgedReason, u64>| reasons.values().sum::<u64>();
    assert_eq!(
        sum(&report.totals.unsupported_reasons),
        count(report, OutcomeClass::Unsupported),
        "{:?}",
        report.totals
    );
    assert_eq!(
        sum(&report.totals.baseline_incomplete_reasons),
        count(report, OutcomeClass::BaselineIncomplete),
        "{:?}",
        report.totals
    );
}

/// THREADS `go(5) ; wait(N)`: N = 5 finishes with no thread left (`miss`), any other N leaves
/// the main thread waiting (`stuck`). At base every case was `unsupported`.
#[test]
fn a_threaded_campaign_without_a_pattern_classes_finished_and_deadlocked_runs() {
    let report = run(
        spec(
            &THREADS,
            None,
            "threads/spawn.pgm",
            "wait(5)",
            "5",
            (3, 7),
            unreachable_pattern(),
            CaseOptions::default(),
        ),
        40,
    );
    assert!(
        report.engine_defects.is_empty(),
        "{:?}",
        report.engine_defects
    );
    assert_eq!(
        count(&report, OutcomeClass::Unsupported),
        0,
        "{:?}",
        report.totals
    );
    assert!(
        count(&report, OutcomeClass::Miss) > 0,
        "{:?}",
        report.totals
    );
    assert!(
        count(&report, OutcomeClass::Stuck) > 0,
        "{:?}",
        report.totals
    );
    assert_eq!(
        report.normal_end,
        Some(NormalEnds {
            baseline: NormalEndKind::EveryK,
            mutant: None,
        })
    );
    assert_reasons_sum(&report);
    let json = report.to_canonical_json();
    assert!(
        json.contains(r#""normal-end":{"baseline":"every-k"}"#),
        "{json}"
    );
}

/// TAINT `get(N)`: N = 1 ends cleanly, any other N leaves `find(1 |-> 10, N)` unevaluated on a
/// leaf, which is not ceil-free. The report counts those cases under `not-ceil-free`, names
/// `find` in a warning, and the statement gives the reason and its remedy.
#[test]
fn not_ceil_free_cases_are_counted_and_name_the_partial_function() {
    let report = run(
        spec(
            &TAINT,
            None,
            "taint/get.pgm",
            "get(1)",
            "1",
            (1, 4),
            unreachable_pattern(),
            CaseOptions::default(),
        ),
        30,
    );
    let unsupported = count(&report, OutcomeClass::Unsupported);
    assert!(unsupported > 0, "{:?}", report.totals);
    assert_eq!(
        report.totals.unsupported_reasons,
        BTreeMap::from([(UnjudgedReason::NotCeilFree, unsupported)])
    );
    assert_reasons_sum(&report);
    assert!(
        report
            .warnings
            .iter()
            .any(|warning| warning.contains("application of `find`")),
        "{:?}",
        report.warnings
    );
    let statement = &report.no_witness().expect("no witness").statement;
    assert!(
        statement.contains(&format!("By reason: {unsupported} not-ceil-free.")),
        "{statement}"
    );
    assert!(statement.contains("For not-ceil-free:"), "{statement}");
    let json = report.to_canonical_json();
    assert!(
        json.contains(&format!(
            r#""unsupported-reasons":{{"not-ceil-free":{unsupported}}}"#
        )),
        "{json}"
    );
}

/// COIN against COIN-FUNC on `flip(N)`: for N > 10 the mutant ends with `opaque(N)`, a total
/// function's application that is not data, so the case is `unsupported` with the reason that
/// the mutant's end is not data (TRIAL2's SIMPLE shape, where the fuzz gave no reason).
#[test]
fn a_differential_end_that_is_not_data_is_named() {
    let report = run(
        spec(
            &COIN,
            Some(&COIN_FUNC),
            "coin/flip.pgm",
            "3",
            "3",
            (8, 20),
            TargetKind::Differential(DifferentialTarget::default()),
            CaseOptions::default(),
        ),
        30,
    );
    assert!(report.witness().is_none());
    let unsupported = count(&report, OutcomeClass::Unsupported);
    assert!(unsupported > 0, "{:?}", report.totals);
    assert_eq!(
        report.totals.unsupported_reasons,
        BTreeMap::from([(UnjudgedReason::MutantEndNotData, unsupported)])
    );
    assert_reasons_sum(&report);
    assert_eq!(
        report.normal_end,
        Some(NormalEnds {
            baseline: NormalEndKind::SingleK,
            mutant: Some(NormalEndKind::SingleK),
        })
    );
    let statement = &report.no_witness().expect("no witness").statement;
    assert!(statement.contains("mutant-end-not-data"), "{statement}");
}

/// COIN `count(N)` under `max-depth` 4: the baseline's all-paths run is cut for N >= 3, so
/// those cases are `baseline-incomplete` with the reason `depth-bound`.
#[test]
fn an_incomplete_baseline_names_the_bound() {
    let report = run(
        spec(
            &COIN,
            Some(&COIN_FUNC),
            "coin/count.pgm",
            "3",
            "3",
            (0, 8),
            TargetKind::Differential(DifferentialTarget::default()),
            CaseOptions {
                max_depth: Some(4),
                ..CaseOptions::default()
            },
        ),
        30,
    );
    let incomplete = count(&report, OutcomeClass::BaselineIncomplete);
    assert!(incomplete > 0, "{:?}", report.totals);
    assert_eq!(
        report.totals.baseline_incomplete_reasons,
        BTreeMap::from([(UnjudgedReason::DepthBound, incomplete)])
    );
    assert_reasons_sum(&report);
}

/// Review S3 (`crash.toml`): THREADS `fail(N)` against a negated property that holds. `fail(0)`
/// removes its thread on error, so the every-`<k>` default calls it finished and every case is
/// `miss`; the report must say once that the default applied and how to override it. With the
/// pattern the warning is gone, and the crash is `stuck`.
#[test]
fn the_every_k_default_is_named_when_it_decides_cases() {
    let crash = |normal_end_pattern: Option<&str>| {
        let mut spec = spec(
            &THREADS,
            None,
            "threads/fail.pgm",
            "fail(3)",
            "3",
            (0, 3),
            unreachable_pattern(),
            CaseOptions {
                normal_end_pattern: normal_end_pattern.map(str::to_owned),
                ..CaseOptions::default()
            },
        );
        spec.target.negated_property = true;
        run(spec, 20)
    };
    let every_k = |report: &FuzzReport| {
        report
            .warnings
            .iter()
            .filter(|warning| warning.starts_with("every-k:"))
            .count()
    };
    let default = crash(None);
    assert_eq!(count(&default, OutcomeClass::Miss), default.totals.cases);
    assert_eq!(every_k(&default), 1, "{:?}", default.warnings);
    let warning = default
        .warnings
        .iter()
        .find(|warning| warning.starts_with("every-k:"))
        .expect("the warning");
    for spelling in [
        "normal-end-pattern",
        "--normal-end",
        "removes a thread on error",
    ] {
        assert!(warning.contains(spelling), "{warning}");
    }
    let pattern = crash(Some("<errors> 0 </errors>"));
    assert_eq!(every_k(&pattern), 0, "{:?}", pattern.warnings);
    assert!(
        count(&pattern, OutcomeClass::Stuck) > 0,
        "{:?}",
        pattern.totals
    );
    // A single-`<k>` definition never gets it.
    let taint = run(
        spec(
            &TAINT,
            None,
            "taint/get.pgm",
            "get(1)",
            "1",
            (1, 1),
            unreachable_pattern(),
            CaseOptions::default(),
        ),
        3,
    );
    assert_eq!(every_k(&taint), 0, "{:?}", taint.warnings);
}
