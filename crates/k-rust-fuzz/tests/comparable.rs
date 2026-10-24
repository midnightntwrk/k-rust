//! Comparable ends and query-confirmable hits (FZ-COMPARABLE-A and -Q, P7-ADDENDUM section 4):
//! the conditions kink's verdicts rest on, read from k-rust's facts.
//!
//! `comparable-end` ([`Target::comparable`]) makes a rule or pattern hit also require that the
//! witness program's all-paths run is complete and comparable (conditions P1, P2, P4 and P5);
//! without it, a witness still carries that judgement. `query-confirmable`
//! ([`Target::query_confirmable`]) makes a pattern hit also require no diagnostic anywhere in
//! the run, read over the whole run (conditions Q2', Q4' and Q5'). Every campaign fixes its
//! seed.

mod support;

use std::sync::Arc;

use k_rust_fuzz::{
    Budget, CallerIdentity, Campaign, CampaignSpec, CaseOptions, Definitions, HoleDecl,
    HoleLocation, OutcomeClass, ProgramInput, ProposerConfig, SpanAddress, Target, TargetKind,
    report::FuzzReport,
    spec::{DEFAULT_REJECTION_CAP, PathMode},
    target::{PatternAt, PatternTarget, RuleMode, RuleRef, RuleTarget},
    values::{Constraints, GenerationBounds, IntRange},
};
use num_bigint::BigInt;
use serde_json::{Value as Json, json};
use support::{COMPARABLE, COMPARABLE_ENDS, Fixture, LOADCLAIM};

/// An `Int` hole `N` at `literal` in `find` of `program`, over `min..=max`.
fn hole(program: &str, find: &str, literal: &str, (min, max): (i64, i64)) -> HoleDecl {
    HoleDecl {
        name: "N".into(),
        sort: "Int".into(),
        location: HoleLocation::Span(SpanAddress {
            program: program.into(),
            line: None,
            column: None,
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
    }
}

/// A target of `kind`, neither run to completion nor a property, with neither option.
fn plain(kind: TargetKind) -> Target {
    Target {
        kind,
        run_to_completion: false,
        negated_property: false,
        data_end: true,
        comparable: false,
        query_confirmable: false,
    }
}

/// `target` with the `comparable-end` option.
fn comparable(target: Target) -> Target {
    Target {
        comparable: true,
        ..target
    }
}

/// `target` with the `query-confirmable` option.
fn query_confirmable(target: Target) -> Target {
    Target {
        query_confirmable: true,
        ..target
    }
}

fn fired(label: &str) -> TargetKind {
    TargetKind::Rule(RuleTarget {
        rule: RuleRef::Label(label.into()),
        mode: RuleMode::Fired,
    })
}

fn pattern(pattern: &str, at: PatternAt) -> TargetKind {
    TargetKind::Pattern(PatternTarget {
        pattern: pattern.into(),
        at,
    })
}

fn options(paths: PathMode) -> CaseOptions {
    CaseOptions {
        paths,
        ..CaseOptions::default()
    }
}

fn spec(
    fixture: &'static Fixture,
    program: &str,
    holes: Vec<HoleDecl>,
    target: Target,
    options: CaseOptions,
) -> CampaignSpec {
    let compiled = fixture.compiled();
    CampaignSpec {
        definitions: Definitions {
            baseline: Arc::new(compiled.definition()),
            mutant: None,
        },
        program: ProgramInput::Source(compiled.program_source(program)),
        holes,
        target,
        options,
        proposers: ProposerConfig::default(),
        bounds: GenerationBounds::default(),
        rejection_cap: DEFAULT_REJECTION_CAP,
        seed: 7,
        identity: CallerIdentity {
            k_rust_revision: "fz26-test".into(),
            thread_stack_size: None,
        },
    }
}

fn run(spec: CampaignSpec, cases: u64) -> FuzzReport {
    let report = Campaign::new(spec)
        .expect("the campaign is valid")
        .run(Budget::Cases(cases), None);
    assert!(
        report.engine_defects.is_empty(),
        "{:?}",
        report.engine_defects
    );
    report
}

/// The report as JSON, as it is written.
fn json(report: &FuzzReport) -> Json {
    serde_json::from_str(&report.to_canonical_json()).expect("a report is JSON")
}

/// The first witness case's `comparable` judgement (`Null` without a witness, or without the
/// judgement).
fn witness_comparable(report: &FuzzReport) -> Json {
    json(report)["outcome"]["witness"]["first"]["comparable"].clone()
}

/// The report's `unsupported` cases per reason name.
fn unsupported(report: &FuzzReport) -> Vec<(String, u64)> {
    report
        .totals
        .unsupported_reasons
        .iter()
        .map(|(reason, count)| (reason.name(), *count))
        .collect()
}

fn hits(report: &FuzzReport) -> u64 {
    report
        .totals
        .classes
        .get(&OutcomeClass::Hit)
        .copied()
        .unwrap_or(0)
}

fn witness_found(report: &FuzzReport) -> bool {
    json(report)["outcome"]["status"] == "witness-found"
}

/// The campaign found no witness and no hit, and every `unsupported` case (at least one) has the
/// reason named `reason`.
fn refused_for(report: &FuzzReport, reason: &str) {
    assert!(!witness_found(report), "{}", json(report));
    assert_eq!(hits(report), 0);
    let reasons = unsupported(report);
    assert_eq!(reasons.len(), 1, "{reasons:?}");
    assert_eq!(reasons[0].0, reason, "{reasons:?}");
    assert!(reasons[0].1 > 0);
}

/// One path of `start(N)` fires `finish` and ends cleanly; the other path loops, so the
/// program's all-paths run is cut by the work bound. The confirming all-paths run refuses the
/// hit under `comparable-end`; without it the witness says why it is not comparable.
#[test]
fn a_one_path_hit_whose_program_loops_on_another_path_is_not_comparable() {
    let campaign = |target| {
        spec(
            &COMPARABLE,
            "comparable/start.pgm",
            vec![hole("comparable/start.pgm", "start(5)", "5", (1, 9))],
            target,
            options(PathMode::OnePath),
        )
    };
    let off = run(campaign(plain(fired("finish"))), 4);
    assert!(witness_found(&off), "{}", json(&off));
    assert_eq!(
        witness_comparable(&off),
        json!({"holds": false, "reasons": ["work-bound"]})
    );
    let on = run(campaign(comparable(plain(fired("finish")))), 4);
    refused_for(&on, "end-not-comparable:work-bound");
}

/// LOADCLAIM's load contradicts `td`'s `total` claim: the fuzz's own verdicts read no load
/// record (T-5), so `go-big` is a hit, but kink excludes the definition (D-6), so the hit is not
/// comparable.
#[test]
fn a_hit_on_a_definition_whose_load_contradicts_a_claim_is_not_comparable() {
    let campaign = |target| {
        spec(
            &LOADCLAIM,
            "loadclaim/go.pgm",
            vec![hole("loadclaim/go.pgm", "go(7)", "7", (101, 200))],
            target,
            options(PathMode::OnePath),
        )
    };
    let off = run(campaign(plain(fired("go-big"))), 4);
    assert!(witness_found(&off), "{}", json(&off));
    assert_eq!(
        witness_comparable(&off),
        json!({"holds": false, "reasons": ["contradicted-claim"]})
    );
    let on = run(campaign(comparable(plain(fired("go-big")))), 4);
    refused_for(&on, "end-not-comparable:contradicted-claim");
}

/// `cond(N)` ends with the unevaluated total `f(N)`, a clean leaf for the fuzz, which carries
/// the `undecided-condition` of `f-pos` unless N is 0. Kink makes any diagnosed leaf incomplete
/// (P1), so under `comparable-end` only `cond(0)` is a hit.
#[test]
fn an_all_paths_end_carrying_an_undecided_condition_is_not_comparable() {
    let campaign = |target, range| {
        spec(
            &COMPARABLE,
            "comparable/cond.pgm",
            vec![hole("comparable/cond.pgm", "cond(3)", "3", range)],
            target,
            options(PathMode::AllPaths),
        )
    };
    let off = run(campaign(plain(fired("cond")), (1, 9)), 4);
    assert!(witness_found(&off), "{}", json(&off));
    assert_eq!(
        witness_comparable(&off),
        json!({"holds": false, "reasons": ["undecided-condition"]})
    );
    let on = run(campaign(comparable(plain(fired("cond"))), (1, 9)), 4);
    refused_for(&on, "end-not-comparable:undecided-condition");
    // Over 0..=9 the campaign finds `cond(0)`, whose run is comparable.
    let zero = run(campaign(comparable(plain(fired("cond"))), (0, 9)), 40);
    assert!(witness_found(&zero), "{}", json(&zero));
    let witness = &json(&zero)["outcome"]["witness"];
    let last = if witness["shrunk"].is_null() {
        &witness["first"]
    } else {
        &witness["shrunk"]
    };
    assert_eq!(last["comparable"], json!({"holds": true, "reasons": []}));
    assert_eq!(last["holes"][0]["k-text"], "0", "{witness}");
}

/// The named programs ([`support::COMPARABLE_ENDS`]): each one's witness carries the expected
/// judgement of its all-paths run, whichever path mode found it.
#[test]
fn every_named_program_carries_its_comparable_judgement() {
    for end in &COMPARABLE_ENDS {
        for paths in [PathMode::OnePath, PathMode::AllPaths] {
            let report = run(
                spec(
                    end.fixture,
                    end.program,
                    Vec::new(),
                    plain(pattern(end.pattern, PatternAt::Final)),
                    options(paths),
                ),
                1,
            );
            assert!(
                witness_found(&report),
                "{end:?} {paths:?}: {}",
                json(&report)
            );
            assert_eq!(
                witness_comparable(&report),
                json!({"holds": end.conditions.is_empty(), "reasons": end.conditions}),
                "{end:?} {paths:?}"
            );
            let on = run(
                spec(
                    end.fixture,
                    end.program,
                    Vec::new(),
                    comparable(plain(pattern(end.pattern, PatternAt::Final))),
                    options(paths),
                ),
                1,
            );
            match end.conditions.first() {
                None => assert!(witness_found(&on), "{end:?} {paths:?}: {}", json(&on)),
                Some(first) => assert_eq!(
                    unsupported(&on),
                    [(format!("end-not-comparable:{first}"), 1)],
                    "{end:?} {paths:?}"
                ),
            }
        }
    }
}

/// A pattern hit on `cond(N)`'s clean end, which carries an `undecided-condition`: kink's query
/// refuses a match on a diagnosed state, so under `query-confirmable` the hit is refused, at
/// `final` and at `any-state`.
#[test]
fn a_pattern_hit_whose_leaf_carries_an_undecided_condition_is_not_query_confirmable() {
    for at in [PatternAt::Final, PatternAt::AnyState] {
        let campaign = |target| {
            spec(
                &COMPARABLE,
                "comparable/cond.pgm",
                vec![hole("comparable/cond.pgm", "cond(3)", "3", (1, 9))],
                target,
                options(PathMode::OnePath),
            )
        };
        let off = run(campaign(plain(pattern("<k> .K </k>", at))), 4);
        assert!(witness_found(&off), "{at:?}: {}", json(&off));
        let on = run(
            campaign(query_confirmable(plain(pattern("<k> .K </k>", at)))),
            4,
        );
        refused_for(&on, "query-not-confirmable:undecided-condition");
    }
}

/// `query-confirmable` reads every diagnostic of the run, not the matching leaf's alone (review
/// S2: kink's search absorbs the facts of converging paths into a matching state). `both(3)`'s
/// end `<out> 3 </out>` carries no diagnostic, with or without a work budget, beside the end
/// that carries the `undecided-condition`.
#[test]
fn query_confirmable_reads_every_diagnostic_of_the_run() {
    let unbudgeted = CaseOptions {
        max_depth: Some(100),
        ..options(PathMode::AllPaths)
    };
    for options in [options(PathMode::AllPaths), unbudgeted] {
        let campaign = |target| {
            spec(
                &COMPARABLE,
                "comparable/both.pgm",
                vec![hole("comparable/both.pgm", "both(3)", "3", (3, 3))],
                target,
                options.clone(),
            )
        };
        let target = || plain(pattern("<out> 3 </out>", PatternAt::Final));
        let off = run(campaign(target()), 2);
        assert!(witness_found(&off), "{}", json(&off));
        let on = run(campaign(query_confirmable(target())), 2);
        refused_for(&on, "query-not-confirmable:undecided-condition");
    }
}
