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

/// Test 4 (B1). MERGE `go(5)`: `ac` fires on the branch the state set absorbs into the `ab`
/// branch's end, so no retained trace holds it while coverage `applied` does. The path set has
/// a leaf whose trace holds it (a hit at base); the state set cannot show a clean path that
/// fired it, nor that none did, so the case is `unsupported` with `fired-off-trace`, never
/// `miss`. `ab`, on the retained trace, stays a hit.
#[test]
fn a_rule_fired_only_on_an_absorbed_branch_is_fired_off_trace() {
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
    assert_eq!(
        verdict(&absorbed),
        (OutcomeClass::Unsupported, Some("fired-off-trace".into()))
    );
    assert_eq!(verdict(&go("ab")), (OutcomeClass::Hit, None));
    // Under the depth bound alone, the same.
    let depth_only = run(fixture_spec(
        &MERGE,
        "merge/go.pgm",
        ("go(5)", "5", 5),
        rule(label("ac"), RuleMode::Fired),
        all_paths(None, Some(10)),
    ));
    assert_eq!(
        verdict(&depth_only),
        (OutcomeClass::Unsupported, Some("fired-off-trace".into()))
    );
}

/// Test 6. The identity records the result modality of each kind of run the campaign makes:
/// `cases`, the program's run of every path that judges comparability (`every-path`, rule and
/// pattern targets) and the run an `at: any-state` pattern is judged on (`any-state`).
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
            "cases": "path-set",
            "every-path": "state-set",
            "any-state": "path-set",
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

/// Guard (B1, review N6). MERGE `pick(0)`: `bad`'s successor is undefined beside `good`'s, so
/// it is rolled back; it is in coverage `applied` and on no path. `fired` on it is never a hit:
/// on the state set it is `fired-off-trace` (C2's committed transitions will make it `miss`),
/// on one path `miss`. On `pick(1)` it fires and is a hit.
#[test]
fn a_rolled_back_target_rule_is_never_a_hit() {
    let pick = |value, paths| {
        verdict(&run(fixture_spec(
            &MERGE,
            "merge/pick.pgm",
            ("pick(1)", "1", value),
            rule(label("bad"), RuleMode::Fired),
            CaseOptions {
                paths,
                ..CaseOptions::default()
            },
        )))
    };
    assert_eq!(
        pick(0, PathMode::AllPaths),
        (OutcomeClass::Unsupported, Some("fired-off-trace".into()))
    );
    assert_eq!(pick(0, PathMode::OnePath), (OutcomeClass::Miss, None));
    assert_eq!(pick(1, PathMode::AllPaths), (OutcomeClass::Hit, None));
}
