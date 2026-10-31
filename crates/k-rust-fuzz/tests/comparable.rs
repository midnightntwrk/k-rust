//! Comparable ends and query-confirmable hits (FZ-COMPARABLE-A and -Q, P7-ADDENDUM section 4):
//! the conditions kink's verdicts rest on, read from k-rust's facts.
//!
//! `comparable-end` ([`Target::comparable`]) makes a rule or pattern hit also require that the
//! witness program's all-paths run is complete and comparable (conditions P1 to P5);
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
use support::{COMPARABLE, COMPARABLE_COND, COMPARABLE_ENDS, Fixture, LOADCLAIM};

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
/// the `undecided-condition` of `f-some` unless N is 0. Kink makes any diagnosed leaf incomplete
/// (P1), and the diagnostic, which says why the end stayed unevaluated, is named first. `f-some`
/// also leaves the definition without data, so no end of it is comparable (P3): `cond(0)` is
/// refused for that alone.
#[test]
fn an_all_paths_end_carrying_an_undecided_condition_is_not_comparable() {
    let campaign = |target, range| {
        spec(
            &COMPARABLE_COND,
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
        json!({"holds": false, "reasons": ["undecided-condition", "end-not-data"]})
    );
    let on = run(campaign(comparable(plain(fired("cond"))), (1, 9)), 4);
    refused_for(&on, "end-not-comparable:undecided-condition");
    // Over 0..=9 the witness shrinks to `cond(0)`, whose end carries no diagnostic and is
    // still not data.
    let zero = run(campaign(plain(fired("cond")), (0, 9)), 4);
    let witness = &json(&zero)["outcome"]["witness"];
    assert_eq!(witness["shrunk"]["holes"][0]["k-text"], "0", "{witness}");
    assert_eq!(
        witness["shrunk"]["comparable"],
        json!({"holds": false, "reasons": ["end-not-data"]})
    );
}

/// `stay(N)` ends with the irreducible `g(N)`: a clean leaf with no diagnostic, but not data,
/// so its end cannot be compared by its term (P3, INT9 review S3), on one path or all.
#[test]
fn a_hit_whose_end_is_not_data_is_not_comparable() {
    for paths in [PathMode::OnePath, PathMode::AllPaths] {
        let campaign = |target| {
            spec(
                &COMPARABLE,
                "comparable/stay.pgm",
                vec![hole("comparable/stay.pgm", "stay(3)", "3", (1, 9))],
                target,
                options(paths),
            )
        };
        let off = run(campaign(plain(fired("stay"))), 4);
        assert!(witness_found(&off), "{paths:?}: {}", json(&off));
        assert_eq!(
            witness_comparable(&off),
            json!({"holds": false, "reasons": ["end-not-data"]}),
            "{paths:?}"
        );
        let on = run(campaign(comparable(plain(fired("stay")))), 4);
        refused_for(&on, "end-not-comparable:end-not-data");
    }
}

/// The witness of a campaign on `program` of `fixture` as written, for the rule `label`, with
/// and without `comparable-end`, on all paths.
fn undefined_step_campaigns(
    fixture: &'static support::Fixture,
    program: &str,
    label: &str,
) -> (FuzzReport, FuzzReport) {
    let campaign = |target| {
        spec(
            fixture,
            program,
            Vec::new(),
            target,
            options(PathMode::AllPaths),
        )
    };
    (
        run(campaign(plain(fired(label))), 1),
        run(campaign(comparable(plain(fired(label)))), 1),
    )
}

/// `go(1)` takes an undefined step from `<k> step(1) </k> <log> g(1) </log> <out> 0 </out>`:
/// ground, with no path condition, and existing (`g` is total), though `g(1)` is no value. An
/// undefined step is no end and its term is never compared, and the definition has data, so the
/// run is comparable with the empty set of ends (kink27 FUZZ-UNDEF-P3).
#[test]
fn an_undefined_step_from_a_configuration_that_exists_is_comparable() {
    let (off, on) = undefined_step_campaigns(
        &support::COMPARABLE_UNDEFINED,
        "comparable/undefined-go.pgm",
        "go",
    );
    assert!(witness_found(&off), "{}", json(&off));
    assert_eq!(
        witness_comparable(&off),
        json!({"holds": true, "reasons": []})
    );
    assert!(witness_found(&on), "{}", json(&on));
}

/// `go(1)` takes a decided undefined step from a configuration that exists, in a definition
/// without data (`unapplied.k`, an equation between two `List` constructions the evaluator never
/// applies): that no rule gives a defined successor rests on constructors and collections being
/// distinct normal forms, which is the definition's meaning only when it has data, so the run is
/// refused `end-not-data` (kink27 FUZZ-UNDEF-P3 review, finding 1).
#[test]
fn an_undefined_step_of_a_definition_without_data_is_not_comparable() {
    let (off, on) = undefined_step_campaigns(
        &support::COMPARABLE_UNAPPLIED,
        "comparable/unapplied-go.pgm",
        "go",
    );
    assert!(witness_found(&off), "{}", json(&off));
    assert_eq!(
        witness_comparable(&off),
        json!({"holds": false, "reasons": ["end-not-data"]})
    );
    refused_for(&on, "end-not-comparable:end-not-data");
}

/// Without `comparable-end`, the run of every path that judges a one-path witness is not part
/// of the hit case (INT9 review S2): a clock that stops it does not put the case outside the
/// determinism contract. The judgement names the clock, so it says that it may not repeat.
/// With the option the run is part of the case, and its clock makes the case `timeout`, as every
/// case a clock was involved in.
#[test]
fn a_clock_in_the_run_of_every_path_stays_out_of_the_hit_case_without_the_option() {
    let options = CaseOptions {
        // The loop on the other path runs into the clock long before this bound.
        max_work: Some(1_000_000_000),
        safety_limit_ms: Some(1_000),
        ..options(PathMode::OnePath)
    };
    let campaign = |target| {
        spec(
            &COMPARABLE,
            "comparable/start.pgm",
            Vec::new(),
            target,
            options.clone(),
        )
    };
    let off = run(campaign(plain(fired("finish"))), 1);
    assert!(witness_found(&off), "{}", json(&off));
    assert_eq!(off.totals.outside_determinism, 0, "{}", json(&off));
    let judged = witness_comparable(&off);
    assert_eq!(judged["holds"], false, "{judged}");
    assert!(
        judged["reasons"]
            .as_array()
            .is_some_and(|reasons| reasons.contains(&json!("clock"))),
        "{judged}"
    );
    let on = run(campaign(comparable(plain(fired("finish")))), 1);
    assert!(!witness_found(&on), "{}", json(&on));
    assert_eq!(
        on.totals.classes.get(&OutcomeClass::Timeout).copied(),
        Some(1),
        "{}",
        json(&on)
    );
    assert_eq!(on.totals.outside_determinism, 1, "{}", json(&on));
}

/// The run of every path that judges a one-path hit has a work bound even when the campaign
/// bounds only the depth (INT9 review S2): `start(5)`'s loop is cut by the default work bound,
/// long before the depth bound, with the option or without it.
#[test]
fn the_run_of_every_path_is_work_bounded_when_the_campaign_bounds_only_the_depth() {
    let options = CaseOptions {
        max_depth: Some(300_000),
        ..options(PathMode::OnePath)
    };
    assert_eq!(options.max_work, None);
    let campaign = |target| {
        spec(
            &COMPARABLE,
            "comparable/start.pgm",
            Vec::new(),
            target,
            options.clone(),
        )
    };
    let off = run(campaign(plain(fired("finish"))), 1);
    assert!(witness_found(&off), "{}", json(&off));
    assert_eq!(
        witness_comparable(&off),
        json!({"holds": false, "reasons": ["work-bound"]})
    );
    let on = run(campaign(comparable(plain(fired("finish")))), 1);
    refused_for(&on, "end-not-comparable:work-bound");
}

/// The witness names the options it was checked under among its clean-leaf facts (INT9 review
/// F1): a `comparable` judgement that holds reads the same with the option and without it, and
/// `query-confirmable` leaves no other trace in the report.
#[test]
fn the_clean_leaf_facts_name_the_options_a_witness_was_checked_under() {
    let campaign = |target| {
        spec(
            &COMPARABLE,
            "comparable/stay-zero.pgm",
            Vec::new(),
            target,
            options(PathMode::AllPaths),
        )
    };
    let facts = |report: &FuzzReport| {
        report.witness().map_or_else(
            || panic!("a witness: {}", json(report)),
            |witness| witness.clean_leaf_facts.clone(),
        )
    };
    let target = || plain(pattern("<out> 1 </out>", PatternAt::Final));
    let off = facts(&run(campaign(target()), 1));
    assert!(!off.iter().any(|fact| fact == "comparable-end"), "{off:?}");
    assert!(
        !off.iter().any(|fact| fact == "query-confirmable"),
        "{off:?}"
    );
    let on = facts(&run(campaign(query_confirmable(comparable(target()))), 1));
    assert!(on.iter().any(|fact| fact == "comparable-end"), "{on:?}");
    assert!(on.iter().any(|fact| fact == "query-confirmable"), "{on:?}");
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
                &COMPARABLE_COND,
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
                &COMPARABLE_COND,
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
