//! All-paths cases on state sets (FZ-STATESET, C1; ARCHITECTURE 5.1, 5.3, 9.3).
//!
//! Rule targets, patterns `at: final` and the program's run of every path for `comparable`
//! run as k-rust state sets under all paths, which explore each distinct configuration of a
//! depth once. The path set of a nondeterministic program grows with every interleaving, so
//! cases the path set left `work-bound` are judged complete (V4). A `fired` target is a hit
//! only from a retained leaf's trace or a terminal halt, and a case whose target rule is in
//! coverage `applied` but on no retained trace is never `miss` (`fired-off-trace`, B1). Without
//! `max_work`, a merged leaf carries the facts of its first arrival only (V1).

mod support;

use std::sync::{Arc, OnceLock};

use k_rust::{backend::HaltReasonOutput, diagnostic::DiagnosticCode};
use k_rust_fuzz::{
    Budget, CallerIdentity, Campaign, CampaignSpec, CaseOptions, Definitions, HoleDecl,
    HoleLocation, OutcomeClass, ProgramInput, ProgramSource, ProposerConfig, SpanAddress, Target,
    TargetKind,
    report::FuzzReport,
    spec::{CompiledDefinition, DEFAULT_REJECTION_CAP, PathMode, ProgramText},
    target::{DifferentialTarget, PatternAt, PatternTarget, RuleMode, RuleRef, RuleTarget},
    values::{Constraints, GenerationBounds, IntRange},
};
use num_bigint::BigInt;
use support::{COIN, COIN_SWAPPED, Fixture, IMP_DIFF, MERGE};

/// The left-operand heating rule of IMP's strict `/` (`AExp "/" AExp [left, strict]`): the
/// compiler labels it with the production's klabel and `1-heat`.
const DIVISION_HEATING: &str = "IMP-SYNTAX._/__IMP-SYNTAX_AExp_AExp_AExp1-heat";

/// The right-operand heating rule of IMP's strict `/` (`2-heat`).
const DIVISION_RIGHT_HEATING: &str = "IMP-SYNTAX._/__IMP-SYNTAX_AExp_AExp_AExp2-heat";

/// An `Int` hole named `name` at `literal` in `find`, ranging over `min..=max`.
fn int_hole(
    name: &str,
    program: &str,
    find: &str,
    literal: &str,
    (min, max): (i64, i64),
) -> HoleDecl {
    HoleDecl {
        name: name.into(),
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

fn target(kind: TargetKind) -> Target {
    Target {
        kind,
        run_to_completion: false,
        negated_property: false,
        data_end: true,
        comparable: false,
        query_confirmable: false,
    }
}

fn rule(reference: RuleRef, mode: RuleMode) -> Target {
    target(TargetKind::Rule(RuleTarget {
        rule: reference,
        mode,
    }))
}

fn label(label: &str) -> RuleRef {
    RuleRef::Label(label.into())
}

fn final_pattern(pattern: &str) -> Target {
    target(TargetKind::Pattern(PatternTarget {
        pattern: pattern.into(),
        at: PatternAt::Final,
    }))
}

fn spec(
    definition: Arc<CompiledDefinition>,
    program: ProgramSource,
    holes: Vec<HoleDecl>,
    target: Target,
    options: CaseOptions,
) -> CampaignSpec {
    CampaignSpec {
        definitions: Definitions {
            baseline: definition,
            mutant: None,
        },
        program: ProgramInput::Source(program),
        holes,
        target,
        options,
        proposers: ProposerConfig::default(),
        bounds: GenerationBounds::default(),
        rejection_cap: DEFAULT_REJECTION_CAP,
        seed: 3,
        identity: CallerIdentity {
            k_rust_revision: "fz26-test".into(),
            thread_stack_size: None,
        },
    }
}

/// A campaign on `fixture`'s `program`, with one `Int` hole `N` at `literal` in `find` that
/// takes the single value `value`.
fn fixture_spec(
    fixture: &'static Fixture,
    program: &str,
    (find, literal, value): (&str, &str, i64),
    target: Target,
    options: CaseOptions,
) -> CampaignSpec {
    spec(
        Arc::new(fixture.compiled().definition()),
        fixture.compiled().program_source(program),
        vec![int_hole("N", program, find, literal, (value, value))],
        target,
        options,
    )
}

/// SIMPLE untyped (`tests/data/simple/simple.md`), compiled once per test binary.
fn simple() -> Arc<CompiledDefinition> {
    static SIMPLE: OnceLock<Arc<CompiledDefinition>> = OnceLock::new();
    Arc::clone(SIMPLE.get_or_init(|| {
        Arc::new(support::compile_source_with(
            "simple/simple.md",
            include_str!("data/simple/simple.md"),
            "SIMPLE-UNTYPED",
            &[DiagnosticCode::CellCollectionVarWithoutInitial],
        ))
    }))
}

/// TRIAL3's `rdv` template with main's rendezvous value `R` fixed to 3, the spawned thread's.
fn rendezvous(target: Target, options: CaseOptions) -> CampaignSpec {
    spec(
        simple(),
        ProgramSource {
            program: Some(ProgramText {
                name: "rdv.simple".into(),
                text: include_str!("data/simple/rdv.simple").into(),
                start_sort: "Stmt".into(),
            }),
            config_vars: Vec::new(),
        },
        vec![int_hole("R", "rdv.simple", "rendezvous 5;", "5", (3, 3))],
        target,
        options,
    )
}

fn all_paths(max_work: Option<u64>, max_depth: Option<u64>) -> CaseOptions {
    CaseOptions {
        paths: PathMode::AllPaths,
        max_work,
        max_depth,
        ..CaseOptions::default()
    }
}

fn run(spec: CampaignSpec) -> FuzzReport {
    Campaign::new(spec)
        .expect("the campaign is valid")
        .run(Budget::Cases(4), None)
}

/// The one judged case's class and, when it is `unsupported`, its reason's report name.
fn verdict(report: &FuzzReport) -> (OutcomeClass, Option<String>) {
    assert!(
        report.engine_defects.is_empty(),
        "{:?}",
        report.engine_defects
    );
    // The anchor, the program's own literal, is rejected when it lies outside the hole's one
    // value; that one value is the case judged.
    let judged: Vec<(&OutcomeClass, &u64)> = report
        .totals
        .classes
        .iter()
        .filter(|(class, count)| **class != OutcomeClass::Rejected && **count > 0)
        .collect();
    let [(class, 1)] = judged[..] else {
        panic!("one judged case: {:?}", report.totals);
    };
    let class = *class;
    let reason = serde_json::to_value(&report.totals.unsupported_reasons)
        .expect("the reasons are JSON")
        .as_object()
        .and_then(|reasons| reasons.keys().next().cloned());
    (class, reason)
}

fn modality(report: &FuzzReport) -> serde_json::Value {
    serde_json::to_value(&report.identity).expect("the identity is JSON")["execution-modality"]
        .clone()
}

/// Test 1. IMP primes with `m = 4`: the left heating of `/` is covered. Its path set, 203
/// leaves of 2 distinct ends, is `work-bound` at max-work 2000 (base); its state set explores
/// 467 states and completes, every leaf clean, so the run-level coverage is a hit.
#[test]
fn imp_primes_covers_the_division_heating_within_max_work_2000() {
    let report = run(fixture_spec(
        &IMP_DIFF,
        "imp-diff/primes.imp",
        ("m = 4;", "4", 4),
        rule(label(DIVISION_HEATING), RuleMode::Covered),
        all_paths(Some(2000), None),
    ));
    assert_eq!(
        verdict(&report),
        (OutcomeClass::Hit, None),
        "{:?}",
        report.outcome
    );
    assert!(report.witness().is_some(), "{:?}", report.outcome);
    assert!(report.totals.work <= 2000, "{}", report.totals.work);
    assert_eq!(
        modality(&report),
        serde_json::json!({"cases": "state-set", "every-path": "state-set"})
    );
}

/// Test 2. SIMPLE `rdv` with R = 3, `fired` on `rendezvous` (`simple.md:1048`) under
/// `comparable`: the case runs a state set (2 ends at work 194), the rendezvous is on both
/// retained traces, and the program's run of every path (a state set too) is complete and
/// comparable. The path set was `work-bound` at max-work 1000 (base; 16799 leaves at 200000).
#[test]
fn the_simple_rendezvous_is_a_comparable_hit_within_max_work_1000() {
    let mut fired = rule(
        RuleRef::Source {
            source: "simple.md".into(),
            line: 1048,
        },
        RuleMode::Fired,
    );
    fired.comparable = true;
    let report = run(rendezvous(fired, all_paths(Some(1000), None)));
    assert_eq!(
        verdict(&report),
        (OutcomeClass::Hit, None),
        "{:?}",
        report.outcome
    );
    let witness = report.witness().expect("a witness");
    assert_eq!(
        witness
            .first
            .comparable
            .as_ref()
            .map(|comparable| comparable.holds),
        Some(true)
    );
}

/// Test 3. SIMPLE `rdv` with R = 3 against `pattern at: final` on the output `a`, `b`, newline,
/// within max-work 1000. The state set's run is complete: its two ends (`ab` and `ba`) are the
/// witness's whole result, both `stuck`. The path set also met an `ab` end before its bound, a
/// hit at base, but its witness held every leaf up to the bound, one of them `work-bound`; and a
/// pattern no end matches (`c`) was `work-bound` at base, where the state set decides `miss`
/// (V4).
#[test]
fn the_simple_rendezvous_ends_printing_ab_within_max_work_1000() {
    let report = run(rendezvous(
        final_pattern(r#"<output> ListItem("a") ListItem("b") ListItem("\n") </output>"#),
        all_paths(Some(1000), None),
    ));
    assert_eq!(
        verdict(&report),
        (OutcomeClass::Hit, None),
        "{:?}",
        report.outcome
    );
    let side = &report.witness().expect("a witness").first.sides[0];
    assert_eq!(
        side.halts,
        [HaltReasonOutput::Stuck, HaltReasonOutput::Stuck]
    );
    assert_eq!(side.final_configurations.len(), 2);
    let never = run(rendezvous(
        final_pattern(r#"<output> ListItem("c") _:List </output>"#),
        all_paths(Some(1000), None),
    ));
    assert_eq!(verdict(&never), (OutcomeClass::Miss, None));
}

/// Test 4 (B1), and FZ-STATESET-MATCH test 6. MERGE `go(5)`: `ac` fires on the branch the state
/// set absorbs into the `ab` branch's end, so no retained trace holds it. Its successor was
/// committed (`collectCommitted`), and the run's one leaf is a clean end, which every path ends
/// at: a hit of the whole run (at C1, `unsupported` with `fired-off-trace`). `ab`, on the
/// retained trace, stays a hit of its leaf.
#[test]
fn a_rule_fired_only_on_an_absorbed_branch_is_a_hit_by_committed() {
    let go = |rule_label: &str| {
        run(fixture_spec(
            &MERGE,
            "merge/go.pgm",
            ("go(5)", "5", 5),
            rule(label(rule_label), RuleMode::Fired),
            all_paths(None, None),
        ))
    };
    let absorbed = go("ac");
    assert_eq!(verdict(&absorbed), (OutcomeClass::Hit, None));
    // The hit names no leaf: the reaching path is not the retained one.
    let witness = absorbed.witness().expect("a witness");
    assert_eq!(witness.first.reaching.leaf, None, "{witness:?}");
    let retained = go("ab");
    assert_eq!(verdict(&retained), (OutcomeClass::Hit, None));
    assert_eq!(
        retained.witness().expect("a witness").first.reaching.leaf,
        Some(0)
    );
    // Under the depth bound alone, the same.
    let depth_only = run(fixture_spec(
        &MERGE,
        "merge/go.pgm",
        ("go(5)", "5", 5),
        rule(label("ac"), RuleMode::Fired),
        all_paths(None, Some(10)),
    ));
    assert_eq!(verdict(&depth_only), (OutcomeClass::Hit, None));
}

/// Test 6. The identity records the result modality of each kind of run the campaign makes:
/// `cases`, the program's run of every path that judges comparability (`every-path`, rule and
/// pattern targets) and the run an `at: any-state` pattern is judged on (`any-state`), which
/// since FZ-STATESET-MATCH is the case's own state-set run with its state matches.
#[test]
fn the_identity_records_the_execution_modality() {
    let identity = |target: Target, paths: PathMode| {
        modality(&run(fixture_spec(
            &MERGE,
            "merge/go.pgm",
            ("go(5)", "5", 5),
            target,
            CaseOptions {
                paths,
                ..CaseOptions::default()
            },
        )))
    };
    let fired = || rule(label("ab"), RuleMode::Fired);
    assert_eq!(
        identity(fired(), PathMode::AllPaths),
        serde_json::json!({"cases": "state-set", "every-path": "state-set"})
    );
    assert_eq!(
        identity(fired(), PathMode::OnePath),
        serde_json::json!({"cases": "path-set", "every-path": "state-set"})
    );
    assert_eq!(
        identity(final_pattern("<out> 5 </out>"), PathMode::AllPaths),
        serde_json::json!({"cases": "state-set", "every-path": "state-set"})
    );
    let any_state = target(TargetKind::Pattern(PatternTarget {
        pattern: "<out> 5 </out>".into(),
        at: PatternAt::AnyState,
    }));
    assert_eq!(
        identity(any_state, PathMode::AllPaths),
        serde_json::json!({
            "cases": "state-set",
            "every-path": "state-set",
            "any-state": "state-set",
        })
    );
    let differential = Campaign::new(CampaignSpec {
        definitions: Definitions {
            baseline: Arc::new(COIN.compiled().definition()),
            mutant: Some(Arc::new(COIN_SWAPPED.compiled().definition())),
        },
        ..fixture_spec(
            &COIN,
            "coin/flip.pgm",
            ("flip(3)", "3", 3),
            target(TargetKind::Differential(DifferentialTarget {})),
            CaseOptions::default(),
        )
    })
    .expect("the campaign is valid")
    .run(Budget::Cases(1), None);
    assert_eq!(
        modality(&differential),
        serde_json::json!({"cases": "state-set"})
    );
}

/// Test 7 (V1). MERGE `mark(5)` against `<out> 5 </out>`: the branch met first reads an
/// implementation-chosen value, the other reads nothing, and both end at `<out> 5`.
/// - Depth bound alone: the state set's one leaf carries its first arrival's mark, so the case
///   is `unsupported`, where the path set's clean `fd` leaf was a hit (base).
/// - With `max_work`: every leaf carries every run fact in both modalities, so the case is
///   `unsupported` on either, as at base: nothing moves.
#[test]
fn a_depth_only_merge_keeps_the_first_arrivals_facts_and_max_work_moves_nothing() {
    let mark = |options| {
        verdict(&run(fixture_spec(
            &MERGE,
            "merge/mark.pgm",
            ("mark(5)", "5", 5),
            final_pattern("<out> 5 </out>"),
            options,
        )))
    };
    let unsupported = (
        OutcomeClass::Unsupported,
        Some("implementation-chosen-value".into()),
    );
    assert_eq!(mark(all_paths(None, Some(10))), unsupported);
    assert_eq!(mark(all_paths(Some(1000), None)), unsupported);
}

/// Guard (B1, review N6), and FZ-STATESET-MATCH test 5. MERGE `pick(0)`: `bad`'s successor is
/// undefined beside `good`'s, so it is rolled back; it is in coverage `applied`, on no path, and
/// not in the committed transitions. `fired` on it is never a hit: `miss` on the state set (at
/// C1, `fired-off-trace`) and on one path. On `pick(1)` it fires and is a hit. `covered` asks
/// whether some explored step took the rule, which no path does on `pick(0)`, so it is no hit
/// either (FZ-ENGINE-R4, final review S2: it read `applied`, which holds the rolled-back
/// candidate).
#[test]
fn a_rolled_back_target_rule_is_never_a_hit() {
    let pick = |value, mode, paths| {
        verdict(&run(fixture_spec(
            &MERGE,
            "merge/pick.pgm",
            ("pick(1)", "1", value),
            rule(label("bad"), mode),
            CaseOptions {
                paths,
                ..CaseOptions::default()
            },
        )))
    };
    for mode in [RuleMode::Fired, RuleMode::Covered] {
        assert_eq!(pick(0, mode, PathMode::AllPaths), (OutcomeClass::Miss, None));
        assert_eq!(pick(0, mode, PathMode::OnePath), (OutcomeClass::Miss, None));
        assert_eq!(pick(1, mode, PathMode::AllPaths), (OutcomeClass::Hit, None));
        assert_eq!(pick(1, mode, PathMode::OnePath), (OutcomeClass::Hit, None));
    }
}

fn any_state(pattern: &str) -> Target {
    target(TargetKind::Pattern(PatternTarget {
        pattern: pattern.into(),
        at: PatternAt::AnyState,
    }))
}

/// D1 (review of C1). MERGE `tri(5)`, `fired` on `te` under `run-to-completion`: `te` fires
/// only on the `t` branch, whose end the state set merges with the `u` branch's, so it is
/// committed but on no retained trace; the other leaf, `h(5)` with `<out> 7` after `s` and `t`,
/// is a clean abnormal stop, so not every leaf is a natural end and the case is
/// `fired-off-trace`. That leaf is a real `stuck` leaf of the program, whatever the target can
/// judge, so the report keeps it as the incidental `stuck` finding (the class the leaves gave),
/// as it does for a `stuck` case. (Without `run-to-completion` both leaves are clean, so the
/// committed `te` is a hit of the whole run since FZ-STATESET-MATCH.)
#[test]
fn a_fired_off_trace_case_keeps_its_incidental_stuck_finding() {
    let mut fired = rule(label("te"), RuleMode::Fired);
    fired.run_to_completion = true;
    let report = run(fixture_spec(
        &MERGE,
        "merge/tri.pgm",
        ("tri(5)", "5", 5),
        fired,
        all_paths(None, None),
    ));
    assert_eq!(
        verdict(&report),
        (OutcomeClass::Unsupported, Some("fired-off-trace".into()))
    );
    let stuck = report
        .incidental
        .stuck
        .as_ref()
        .expect("the abnormal stop is an incidental finding");
    assert_eq!(stuck.k_heads, ["h ( 5 )"], "{stuck:?}");
    assert!(report.incidental.undefined.is_none());
}

/// S1 (review of C1). MERGE `tri(5)`, `fired` on `t` under `run-to-completion`: `t` fires on
/// the branch the state set absorbs, whose clean natural end would be a hit on a path set, and
/// on the `s` branch, which stops abnormally at `h(5)`. The retained leaves show only the
/// unfinished reach, so `reached-unfinished` would claim that no path that fired `t` ended
/// cleanly and naturally; the case is `fired-off-trace`. Without `run-to-completion` the
/// abnormal stop on `t`'s path is a retained hit.
#[test]
fn an_unfinished_reach_beside_an_absorbed_one_is_fired_off_trace() {
    let tri = |run_to_completion| {
        let mut fired = rule(label("t"), RuleMode::Fired);
        fired.run_to_completion = run_to_completion;
        verdict(&run(fixture_spec(
            &MERGE,
            "merge/tri.pgm",
            ("tri(5)", "5", 5),
            fired,
            all_paths(None, None),
        )))
    };
    assert_eq!(
        tri(true),
        (OutcomeClass::Unsupported, Some("fired-off-trace".into()))
    );
    assert_eq!(tri(false), (OutcomeClass::Hit, None));
}

/// N2 (review of C1). MERGE `chain(10)` against `at: any-state` `<k> chain(0) ~> _ </k>` under
/// `comparable`, within max-work 400: the program's run of every path is a state set of
/// 3 * 10 + 1 states, which completes, and the hit is comparable. At C1 the case ran a path set
/// (2^10 paths, `work-bound`) and made that run separately; since FZ-STATESET-MATCH the case's
/// own run is that state set, with its state matches, and serves as the run of every path. On a
/// path set it would be `unsupported` (`end-not-comparable:work-bound`).
#[test]
fn an_any_state_case_judges_comparability_on_a_state_set() {
    let mut reached = any_state("<k> chain(0) ~> _ </k>");
    reached.comparable = true;
    let report = run(fixture_spec(
        &MERGE,
        "merge/chain.pgm",
        ("chain(10)", "10", 10),
        reached,
        all_paths(Some(400), None),
    ));
    assert_eq!(
        verdict(&report),
        (OutcomeClass::Hit, None),
        "{:?}",
        report.outcome
    );
    let witness = report.witness().expect("a witness");
    assert_eq!(
        witness
            .first
            .comparable
            .as_ref()
            .map(|comparable| comparable.holds),
        Some(true)
    );
}

/// Guard (review of C1, M5). MERGE `go(5)` against `at: any-state` `<k> c(5) ~> _ </k>`, the
/// absorbed branch's state at depth 1: the state set shows no leaf whose path passes `c(5)`,
/// since that branch's arrival at depth 2 is absorbed, but k-rust matches `c(5)` when the run
/// reaches it (FZ-STATESET-MATCH), so the case is a hit. Reading the state set's leaves alone
/// would give a false `miss`.
#[test]
fn an_any_state_case_sees_the_branch_a_state_set_would_absorb() {
    let report = run(fixture_spec(
        &MERGE,
        "merge/go.pgm",
        ("go(5)", "5", 5),
        any_state("<k> c(5) ~> _ </k>"),
        all_paths(None, None),
    ));
    assert_eq!(
        verdict(&report),
        (OutcomeClass::Hit, None),
        "{:?}",
        report.outcome
    );
}

// ------------------------------------------------------------ FZ-STATESET-MATCH (C2)

/// Design test 3 (FZ-STATESET-MATCH, S3). MERGE `both(12)` against `at: any-state`
/// `<k> chain(12) </k> <out> 5 </out>`: `mark(5)`'s first branch (`me`/`ed`) reads an
/// implementation-chosen value and reaches that configuration at depth 3; its second branch
/// (`mf`/`fd`) reaches it at the same depth without one. The state set expands it once, on the
/// dirty prefix, and absorbs the clean arrival, which k-rust reports as the clean reach: a hit,
/// with max-work 2000 and with the depth bound alone. At the base the case ran a path set, which
/// explored the dirty branch's 2^12 paths first and was cut at max-work 2000 before the clean
/// branch: `unsupported` (`implementation-chosen-value`). On one path only the dirty branch runs,
/// so its reach is never a clean hit.
#[test]
fn a_cleaner_merged_arrival_is_an_any_state_hit() {
    for options in [all_paths(Some(2000), None), all_paths(None, Some(100))] {
        let report = run(fixture_spec(
            &MERGE,
            "merge/both.pgm",
            ("both(12)", "12", 12),
            any_state("<k> chain(12) </k> <out> 5 </out>"),
            options.clone(),
        ));
        assert_eq!(
            verdict(&report),
            (OutcomeClass::Hit, None),
            "{:?}",
            report.outcome
        );
        let witness = report.witness().expect("a witness");
        assert_eq!(witness.first.reaching.step, Some(3), "{witness:?}");
        assert_eq!(witness.first.reaching.leaf, None, "{witness:?}");
        assert!(report.totals.work < 200, "{}", report.totals.work);
        // The krun line is the search; a depth bound bounds it, and without one it says it
        // may not terminate and names the work bound krun cannot take.
        let krun = witness.krun_command.as_deref().expect("a krun line");
        assert!(krun.contains(" --search-all --pattern "), "{krun}");
        if options.max_depth.is_some() {
            assert!(krun.contains(" --depth 100 "), "{krun}");
        } else {
            assert!(
                krun.contains("max-work 2000") && krun.contains("may not terminate"),
                "{krun}"
            );
        }
    }
    // On one path only `mark(5)`'s first branch runs: its reach is on the dirty prefix alone,
    // never a clean hit.
    let report = run(fixture_spec(
        &MERGE,
        "merge/both.pgm",
        ("both(12)", "12", 12),
        any_state("<k> chain(12) </k> <out> 5 </out>"),
        CaseOptions::default(),
    ));
    assert_eq!(
        verdict(&report),
        (
            OutcomeClass::Unsupported,
            Some("implementation-chosen-value".into())
        ),
        "{:?}",
        report.outcome
    );
}

/// MERGE `stall(5)`, all-paths `fired` on `sb`: both branches reach `<k> z(5) </k>` at depth 2,
/// an abnormal stop, and the `sb` arrival is absorbed, so `sb` is on no retained trace but is
/// committed. Without `run-to-completion` the one leaf is clean, so the case is a hit of the
/// whole run; with it no path ends naturally, so the target was reached and the run did not end
/// naturally: `reached-unfinished`, whichever path reached it. At C1 both were
/// `fired-off-trace` (the coarseness the C1 landing recorded for `reached-unfinished`).
#[test]
fn a_committed_rule_on_a_run_that_never_ends_naturally_is_reached_unfinished() {
    let stall = |run_to_completion| {
        let mut fired = rule(label("sb"), RuleMode::Fired);
        fired.run_to_completion = run_to_completion;
        verdict(&run(fixture_spec(
            &MERGE,
            "merge/stall.pgm",
            ("stall(5)", "5", 5),
            fired,
            all_paths(None, None),
        )))
    };
    assert_eq!(stall(false), (OutcomeClass::Hit, None));
    assert_eq!(stall(true), (OutcomeClass::ReachedUnfinished, None));
    // The hit is the run's: `sb` is on no retained trace.
    let report = run(fixture_spec(
        &MERGE,
        "merge/stall.pgm",
        ("stall(5)", "5", 5),
        rule(label("sb"), RuleMode::Fired),
        all_paths(None, None),
    ));
    let witness = report.witness().expect("a witness");
    assert_eq!(witness.first.reaching.leaf, None, "{witness:?}");
}

/// Design test 4 and its fuzz-level guard: a verdict that only execution mode gives is never a
/// refutation. MERGE `go(5)`'s end against `<out> X </out> requires isFirst(X)`, whether `X`
/// is the first key `keys_list` lists of a two-key map, which the definition leaves open:
/// execution mode refutes it (5 is neither 1 nor 2), proof mode does not decide it, so the
/// configuration is `undecided-match` and the case `unsupported`, never `miss`. (The base's
/// two-mode match judged it the same way.)
#[test]
fn a_verdict_only_execution_mode_gives_is_never_a_miss() {
    let report = run(fixture_spec(
        &MERGE,
        "merge/go.pgm",
        ("go(5)", "5", 5),
        any_state("<k> .K </k> <out> X </out> requires isFirst(X)"),
        all_paths(None, None),
    ));
    assert_eq!(
        verdict(&report),
        (OutcomeClass::Unsupported, Some("undecided-match".into())),
        "{:?}",
        report.outcome
    );
}

/// Regression guard (FZ-STATESET-MATCH). IMP primes with `m = 4`, all-paths `fired` on the right
/// heating of `/`: the strict operator's evaluation orders meet, and the state set keeps the
/// left-first arrival, whose path also heats the right operand (after the left one is
/// evaluated), so the rule is on a retained trace and the hit is that leaf's. (A rule that
/// fires only on an absorbed arrival, whose hit is the run's, is MERGE's `ac` and `sb` in this file;
/// IMP's strictness rules fire on the kept order as well, so it offers none.)
#[test]
fn imp_primes_fires_the_right_division_heating_on_a_retained_trace() {
    let report = run(fixture_spec(
        &IMP_DIFF,
        "imp-diff/primes.imp",
        ("m = 4;", "4", 4),
        rule(label(DIVISION_RIGHT_HEATING), RuleMode::Fired),
        all_paths(Some(2000), None),
    ));
    assert_eq!(
        verdict(&report),
        (OutcomeClass::Hit, None),
        "{:?}",
        report.outcome
    );
    // The hit is a retained leaf's: its own trace holds the rule.
    let witness = report.witness().expect("a witness");
    assert_eq!(witness.first.reaching.leaf, Some(0), "{witness:?}");
}

/// ANY-STATE-MEM (TRIAL3): IMP `primes` with `m = 4` against `at: any-state`
/// `<k> _:Int / 0 ~> _ </k>` on all paths within max-work 1000. The base held every configuration
/// of its path set (7.4 GB) and was cut `work-bound` at work 1000; the state set with in-run
/// matching completes at work 467 and misses: no reached state divides by zero. (Memory is
/// measured outside the test suite; the class and the work are what the in-run judgement
/// changes.)
#[test]
fn the_any_state_mem_case_completes_and_misses() {
    let report = run(fixture_spec(
        &IMP_DIFF,
        "imp-diff/primes.imp",
        ("m = 4;", "4", 4),
        any_state("<k> _:Int / 0 ~> _ </k>"),
        all_paths(Some(1000), None),
    ));
    assert_eq!(
        verdict(&report),
        (OutcomeClass::Miss, None),
        "{:?}",
        report.outcome
    );
    assert_eq!(report.totals.work, 467);
}
