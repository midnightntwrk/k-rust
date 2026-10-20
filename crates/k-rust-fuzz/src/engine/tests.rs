//! Unit tests of the engine's loop, schedule, budget, confirmation and shrinking, against a
//! scripted [`CaseRunner`] and scripted proposers (no definition is executed).

use std::collections::BTreeMap;

use k_rust::backend::CancellationToken;
use num_bigint::BigInt;

use super::{
    campaign_loop::{CutCounts, Cuts, Ending, LoopSettings, MAX_SHRINK_RUNS, no_witness, run_loop},
    explicit_proposals,
    proposer::{
        CoverageFeedback, Feedback as _, Observation, Origin, Proposal, ProposalContext, Proposer,
        ValueShrinker,
    },
    runner::{CaseRun, CaseRunner, ConfirmFailure, Cut, HitDetail},
    schedule::{Schedule, derive_seed},
    shrink::{Verdict, shrink},
};
use crate::{
    error::CampaignError,
    exec::{Abort, OutcomeClass},
    holes::HoleLocation,
    report::{
        CampaignOutcome, DefinitionIdentity, DefinitionRole, FuzzReport, HitLabel, HoleValue,
        KillKind, Reaching, RejectionReason, ReportIdentity, Totals, WitnessSide,
    },
    spec::{Budget, CaseOptions, PathMode, ProposerConfig, ProposerKind},
    values::{Constraints, GenerationBounds, IntRange, LengthRange, Value},
};

// ---------------------------------------------------------------------------------------------
// Scripted pieces

fn int(n: i64) -> Value {
    Value::Int(BigInt::from(n))
}

fn as_int(value: &Value) -> i64 {
    match value {
        Value::Int(n) => i64::try_from(n).expect("small test integer"),
        other => panic!("not an int: {other:?}"),
    }
}

fn run(class: OutcomeClass, work: u64) -> CaseRun {
    CaseRun {
        class,
        work,
        applied: Vec::new(),
        matched: Vec::new(),
        blocked: false,
        outside_determinism: false,
        rejection: None,
        load_records: Vec::new(),
        defects: Vec::new(),
        warnings: Vec::new(),
        hit: None,
        cut: Cut::default(),
    }
}

fn detail(values: &[Value], state: &str) -> HitDetail {
    HitDetail {
        holes: values
            .iter()
            .enumerate()
            .map(|(index, value)| HoleValue {
                name: format!("H{index}"),
                location: HoleLocation::ConfigVar {
                    name: format!("H{index}"),
                },
                k_text: Some(format!("{value:?}")),
                kore: format!("{value:?}"),
                value: value.clone(),
            })
            .collect(),
        sides: vec![WitnessSide {
            role: DefinitionRole::Baseline,
            initial_configuration: format!("init{values:?}"),
            final_configurations: vec![state.to_owned()],
        }],
        reaching: Reaching {
            role: DefinitionRole::Baseline,
            leaf: Some(0),
        },
        kill: None,
        steps: Some(3),
        reaching_state: state.to_owned(),
        krun_command: Some(format!("krust krun {values:?}")),
    }
}

fn hit(values: &[Value], work: u64, state: &str) -> CaseRun {
    CaseRun {
        hit: Some(detail(values, state)),
        ..run(OutcomeClass::Hit, work)
    }
}

type CaseScript = Box<dyn FnMut(&[Value]) -> CaseRun>;
type ConfirmScript = Box<dyn FnMut(&[Value]) -> Result<CaseRun, String>>;
type AdmissibleScript = Box<dyn Fn(usize, &Value) -> bool>;

/// A runner whose cases and confirmations follow closures, recording every call.
struct Scripted {
    case: CaseScript,
    confirm: ConfirmScript,
    admissible: AdmissibleScript,
    abort_at: Option<usize>,
    /// Every confirmation aborts as a failed solver prelude does.
    confirm_aborts: bool,
    cases: Vec<Vec<Value>>,
    confirmed: Vec<Vec<Value>>,
}

impl Scripted {
    fn new(
        case: impl FnMut(&[Value]) -> CaseRun + 'static,
        confirm: impl FnMut(&[Value]) -> Result<CaseRun, String> + 'static,
    ) -> Self {
        Self {
            case: Box::new(case),
            confirm: Box::new(confirm),
            admissible: Box::new(|_, _| true),
            abort_at: None,
            confirm_aborts: false,
            cases: Vec::new(),
            confirmed: Vec::new(),
        }
    }
}

impl CaseRunner for Scripted {
    fn run_case(
        &mut self,
        values: &[Value],
        _cancel: Option<&CancellationToken>,
    ) -> Result<CaseRun, Abort> {
        if self.abort_at == Some(self.cases.len()) {
            return Err(Abort {
                reason: "solver prelude failed".into(),
            });
        }
        self.cases.push(values.to_vec());
        Ok((self.case)(values))
    }

    fn confirm(
        &mut self,
        values: &[Value],
        _cancel: Option<&CancellationToken>,
    ) -> Result<CaseRun, ConfirmFailure> {
        self.confirmed.push(values.to_vec());
        if self.confirm_aborts {
            return Err(ConfirmFailure::Abort(Abort {
                reason: "the fresh backend's solver prelude failed".into(),
            }));
        }
        (self.confirm)(values).map_err(ConfirmFailure::Failed)
    }

    fn admissible(&self, hole: usize, value: &Value) -> bool {
        (self.admissible)(hole, value)
    }
}

/// A proposer of one hole whose values are `start`, `start + step`, …, labelled `kind`.
struct Counter {
    kind: ProposerKind,
    next: i64,
    step: i64,
    left: Option<u32>,
}

impl Counter {
    fn boxed(kind: ProposerKind, start: i64, step: i64) -> Box<dyn Proposer> {
        Box::new(Self {
            kind,
            next: start,
            step,
            left: None,
        })
    }
}

impl Proposer for Counter {
    fn kind(&self) -> ProposerKind {
        self.kind
    }

    fn propose(&mut self, _context: &mut ProposalContext<'_>) -> Option<Proposal> {
        if let Some(left) = &mut self.left {
            if *left == 0 {
                return None;
            }
            *left -= 1;
        }
        let value = self.next;
        self.next += self.step;
        Some(Proposal::plain(
            Origin::Scheduled(self.kind),
            vec![int(value)],
        ))
    }

    fn observe(&mut self, _proposal: &Proposal, _observation: &Observation, _interesting: bool) {}
}

fn identity() -> ReportIdentity {
    ReportIdentity {
        engine_version: crate::ENGINE_VERSION,
        k_rust_revision: "test".into(),
        definitions: vec![DefinitionIdentity {
            role: DefinitionRole::Baseline,
            main_module: "MAIN".into(),
            syntax_module: "MAIN-SYNTAX".into(),
            frontend_digest: "f".into(),
            execution_definition_digest: "e".into(),
            syntax_definition_digest: "s".into(),
            initial_configuration_digest: None,
            execution_digest: "00".into(),
            route: "from-definition".into(),
            execution_rewrite_order_digest: None,
        }],
        program_digest: "p".into(),
        overlay_digest: "o".into(),
        target_digest: "t".into(),
        options: CaseOptions::default(),
        proposers: ProposerConfig::default(),
        bounds: GenerationBounds::default(),
        caps: crate::report::GenerationCaps::current(),
        rejection_cap: 1000,
        seed: 1,
        budget: Budget::Cases(0),
        thread_stack_size: None,
        solver: "none".into(),
    }
}

fn settings(holes: usize) -> LoopSettings {
    LoopSettings {
        identity: identity(),
        rejection_cap: 1000,
        options: CaseOptions {
            max_work: Some(1000),
            ..CaseOptions::default()
        },
        label: HitLabel::Hit,
        clean_leaf_facts: vec!["ceil-free".into()],
        constraints: vec![Constraints::default(); holes],
        sort_overrides: Vec::new(),
        warnings: Vec::new(),
    }
}

fn counter_schedule(seed: u64, start: i64) -> Schedule {
    Schedule::new(
        seed,
        Vec::new(),
        vec![(1, Counter::boxed(ProposerKind::Blind, start, 1))],
    )
}

fn classes(report: &FuzzReport) -> Vec<(OutcomeClass, u64)> {
    report
        .totals
        .classes
        .iter()
        .map(|(class, count)| (*class, *count))
        .collect()
}

// ---------------------------------------------------------------------------------------------
// Budget

#[test]
fn a_case_budget_counts_cases_and_not_confirmation_or_shrink_runs() {
    let mut runner = Scripted::new(
        |values| {
            if as_int(&values[0]) == 3 {
                hit(values, 10, "end-3")
            } else {
                run(OutcomeClass::Miss, 10)
            }
        },
        |values| {
            if as_int(&values[0]) == 3 {
                Ok(hit(values, 7, "end-3"))
            } else {
                Ok(run(OutcomeClass::Miss, 7))
            }
        },
    );
    let report = run_loop(
        &mut runner,
        &mut counter_schedule(1, 1),
        &settings(1),
        Budget::Cases(10),
        None,
    );
    assert!(matches!(
        report.outcome,
        CampaignOutcome::WitnessFound { .. }
    ));
    assert_eq!(report.totals.cases, 3);
    assert_eq!(
        classes(&report),
        [(OutcomeClass::Hit, 1), (OutcomeClass::Miss, 2)]
    );
    // Cases 1, 2, 3; then the shrink candidates 0, 1 and 2 (bisection towards zero), all misses
    // on the campaign's backend, so none is confirmed.
    let runs: Vec<i64> = runner
        .cases
        .iter()
        .map(|values| as_int(&values[0]))
        .collect();
    assert_eq!(runs, [1, 2, 3, 0, 1, 2]);
    assert_eq!(runner.confirmed, [vec![int(3)]]);
    assert_eq!(report.totals.work, 3 * 10 + 7 + 3 * 10);
    let witness = report.witness().cloned().expect("a witness");
    assert_eq!(witness.first.holes[0].value, int(3));
    assert_eq!(witness.shrunk, None);
    assert_eq!(report.identity.budget, Budget::Cases(10));
    assert_eq!(report.no_witness(), None);
}

#[test]
fn a_work_budget_charges_confirmation_and_shrinking() {
    let mut runner = Scripted::new(
        |values| {
            if as_int(&values[0]) >= 40 {
                hit(values, 10, "end")
            } else {
                run(OutcomeClass::Miss, 10)
            }
        },
        |values| Ok(hit(values, 5, "end")),
    );
    let mut schedule = Schedule::new(
        1,
        Vec::new(),
        vec![(1, Counter::boxed(ProposerKind::Blind, 100, 0))],
    );
    let report = run_loop(
        &mut runner,
        &mut schedule,
        &settings(1),
        Budget::Work(60),
        None,
    );
    // Case 100 (10) and its confirmation (5); shrink candidate 0 misses (10), 50 hits (10) and
    // is confirmed (5), 25 misses (10), 37 misses (10): 60 spent, so 43 never runs.
    let runs: Vec<i64> = runner
        .cases
        .iter()
        .map(|values| as_int(&values[0]))
        .collect();
    assert_eq!(runs, [100, 0, 50, 25, 37]);
    assert_eq!(runner.confirmed, [vec![int(100)], vec![int(50)]]);
    assert_eq!(report.totals.work, 60);
    assert_eq!(report.totals.cases, 1);
    let witness = report.witness().cloned().expect("a witness");
    assert_eq!(witness.first.holes[0].value, int(100));
    assert_eq!(
        witness.shrunk.expect("a shrunk witness").holes[0].value,
        int(50)
    );
}

#[test]
fn a_work_budget_stops_before_an_execution_and_charges_failed_runs_one_unit() {
    let mut runner = Scripted::new(
        |_| CaseRun {
            defects: Vec::new(),
            ..run(OutcomeClass::Unsupported, 0)
        },
        |_| unreachable!("no case hits"),
    );
    let report = run_loop(
        &mut runner,
        &mut counter_schedule(1, 1),
        &settings(1),
        Budget::Work(5),
        None,
    );
    assert!(matches!(
        report.outcome,
        CampaignOutcome::NoWitnessFound { .. }
    ));
    assert_eq!(report.totals.cases, 5);
    assert_eq!(report.totals.work, 5);
    assert_eq!(classes(&report), [(OutcomeClass::Unsupported, 5)]);
}

/// A blind-kind proposer whose draws fail on odd calls, as a failed `Generator::try_generate`
/// leaves them: the values drawn so far and the generator's message.
struct Failing {
    calls: i64,
}

impl Proposer for Failing {
    fn kind(&self) -> ProposerKind {
        ProposerKind::Blind
    }

    fn propose(&mut self, _context: &mut ProposalContext<'_>) -> Option<Proposal> {
        self.calls += 1;
        let mut proposal = Proposal::plain(
            Origin::Scheduled(ProposerKind::Blind),
            vec![int(self.calls)],
        );
        if self.calls % 2 == 1 {
            proposal.values.clear();
            proposal.failure = Some("hole 0: the generator rejected a draw: test".to_owned());
        }
        Some(proposal)
    }

    fn observe(&mut self, _proposal: &Proposal, _observation: &Observation, _interesting: bool) {}
}

#[test]
fn a_failed_draw_is_a_rejected_case_that_is_not_run() {
    let mut runner = Scripted::new(|_| run(OutcomeClass::Miss, 2), |_| unreachable!("no hit"));
    let mut schedule = Schedule::new(1, Vec::new(), vec![(1, Box::new(Failing { calls: 0 }))]);
    let report = run_loop(
        &mut runner,
        &mut schedule,
        &settings(1),
        Budget::Cases(4),
        None,
    );
    assert_eq!(report.totals.cases, 4);
    assert_eq!(
        classes(&report),
        [(OutcomeClass::Miss, 2), (OutcomeClass::Rejected, 2)]
    );
    assert_eq!(
        report.totals.rejections,
        BTreeMap::from([(RejectionReason::Generation, 2)])
    );
    // Only the complete draws ran; a rejected draw is charged one unit, as every case is.
    assert_eq!(runner.cases, [vec![int(2)], vec![int(4)]]);
    assert_eq!(report.totals.work, 2 * 2 + 2);
    // The generator's message is reported once.
    let warnings: Vec<_> = report
        .warnings
        .iter()
        .filter(|warning| warning.contains("generator rejected a draw"))
        .collect();
    assert_eq!(warnings.len(), 1, "{:?}", report.warnings);
}

#[test]
fn a_case_warning_is_reported_once() {
    let mut runner = Scripted::new(
        |_| CaseRun {
            warnings: vec!["applied id X is ambiguous".to_owned()],
            ..run(OutcomeClass::Miss, 1)
        },
        |_| unreachable!("no case hits"),
    );
    let mut loop_settings = settings(1);
    loop_settings.warnings = vec!["statically-unreachable: rule R".to_owned()];
    let report = run_loop(
        &mut runner,
        &mut counter_schedule(1, 1),
        &loop_settings,
        Budget::Cases(3),
        None,
    );
    assert_eq!(
        report.warnings,
        [
            "statically-unreachable: rule R".to_owned(),
            "applied id X is ambiguous".to_owned()
        ]
    );
}

#[test]
fn the_rejection_cap_ends_the_campaign_with_rejected_out() {
    let mut runner = Scripted::new(
        |values| {
            if as_int(&values[0]) % 2 == 0 {
                CaseRun::rejected(RejectionReason::RoundTrip, 0)
            } else {
                CaseRun::rejected(RejectionReason::Constraint, 0)
            }
        },
        |_| unreachable!("no case hits"),
    );
    let mut loop_settings = settings(1);
    loop_settings.rejection_cap = 3;
    let report = run_loop(
        &mut runner,
        &mut counter_schedule(1, 1),
        &loop_settings,
        Budget::Cases(100),
        None,
    );
    assert!(matches!(
        report.outcome,
        CampaignOutcome::RejectedOut { .. }
    ));
    assert_eq!(report.totals.cases, 3);
    assert_eq!(classes(&report), [(OutcomeClass::Rejected, 3)]);
    assert_eq!(
        report.totals.rejections,
        BTreeMap::from([
            (RejectionReason::Constraint, 2),
            (RejectionReason::RoundTrip, 1)
        ])
    );
    assert_eq!(report.totals.rejection_rate_permille, 1000);
    let statement = report
        .no_witness()
        .cloned()
        .expect("a no-witness statement")
        .statement;
    assert!(statement.contains("rejection cap of 3"), "{statement}");
}

// ---------------------------------------------------------------------------------------------
// Explicit proposals and the schedule

#[test]
fn explicit_proposals_try_the_anchors_first_then_the_assignments() {
    let names = ["X".to_owned(), "Y".to_owned()];
    let anchors = [Some(int(3)), Some(int(5))];
    let config = ProposerConfig {
        anchors_first: true,
        explicit: vec![
            BTreeMap::from([("Y".to_owned(), int(-1))]),
            BTreeMap::from([("X".to_owned(), int(9)), ("Y".to_owned(), int(8))]),
        ],
        weights: BTreeMap::new(),
    };
    let proposals = explicit_proposals(&names, &anchors, &config).expect("valid assignments");
    assert_eq!(
        proposals,
        [
            vec![int(3), int(5)],
            vec![int(3), int(-1)],
            vec![int(9), int(8)]
        ]
    );

    let without_anchors = ProposerConfig {
        anchors_first: false,
        ..config.clone()
    };
    assert_eq!(
        explicit_proposals(&names, &anchors, &without_anchors).expect("valid assignments"),
        [vec![int(3), int(-1)], vec![int(9), int(8)]]
    );

    // A hole without an anchor (a KORE-template variable) makes the anchor proposal impossible;
    // an assignment must then give it a value.
    let partial = [None, Some(int(5))];
    assert_eq!(
        explicit_proposals(&names, &partial, &config),
        Err(CampaignError::ExplicitAssignment {
            index: 0,
            hole: "X".into(),
            message: "the hole has no anchor value and the assignment omits it".into(),
        })
        .map(|()| Vec::new())
    );
    let complete = ProposerConfig {
        explicit: vec![config.explicit[1].clone()],
        ..config.clone()
    };
    assert_eq!(
        explicit_proposals(&names, &partial, &complete).expect("valid assignments"),
        [vec![int(9), int(8)]]
    );

    let unknown = ProposerConfig {
        explicit: vec![BTreeMap::from([("Z".to_owned(), int(0))])],
        ..config
    };
    assert_eq!(
        explicit_proposals(&names, &anchors, &unknown),
        Err(CampaignError::ExplicitAssignment {
            index: 0,
            hole: "Z".into(),
            message: "no hole has this name".into(),
        })
        .map(|()| Vec::new())
    );
}

#[test]
fn the_loop_runs_explicit_proposals_before_any_scheduled_one() {
    let mut runner = Scripted::new(|_| run(OutcomeClass::Miss, 1), |_| unreachable!());
    let mut schedule = Schedule::new(
        9,
        vec![vec![int(-3)], vec![int(-2)]],
        vec![(1, Counter::boxed(ProposerKind::Blind, 100, 1))],
    );
    run_loop(
        &mut runner,
        &mut schedule,
        &settings(1),
        Budget::Cases(4),
        None,
    );
    let runs: Vec<i64> = runner
        .cases
        .iter()
        .map(|values| as_int(&values[0]))
        .collect();
    assert_eq!(runs, [-3, -2, 100, 101]);
}

fn kinds(seed: u64, draws: usize) -> Vec<ProposerKind> {
    let mut schedule = Schedule::new(
        seed,
        Vec::new(),
        vec![
            (1, Counter::boxed(ProposerKind::Blind, 0, 0)),
            (3, Counter::boxed(ProposerKind::Climb, 1, 0)),
            (0, Counter::boxed(ProposerKind::Corpus, 2, 0)),
        ],
    );
    (0..draws)
        .map(|_| match schedule.next().expect("never exhausted").origin {
            Origin::Scheduled(kind) => kind,
            Origin::Explicit => panic!("no explicit proposals"),
        })
        .collect()
}

#[test]
fn the_schedule_is_a_function_of_the_seed() {
    let first = kinds(7, 400);
    assert_eq!(first, kinds(7, 400));
    assert_ne!(first, kinds(8, 400));
    let climbs = first
        .iter()
        .filter(|kind| **kind == ProposerKind::Climb)
        .count();
    assert!(
        (250..=350).contains(&climbs),
        "{climbs} of 400 at weight 3:1"
    );
    assert!(
        !first.contains(&ProposerKind::Corpus),
        "weight 0 never runs"
    );
    assert_ne!(derive_seed(7, "schedule"), derive_seed(7, "values"));
    assert_ne!(derive_seed(7, "schedule"), derive_seed(8, "schedule"));
}

#[test]
fn an_exhausted_proposer_leaves_the_schedule() {
    let mut limited = Counter {
        kind: ProposerKind::Climb,
        next: 50,
        step: 1,
        left: Some(2),
    };
    let mut context_rng = rand::SeedableRng::seed_from_u64(0);
    assert!(
        limited
            .propose(&mut ProposalContext {
                rng: &mut context_rng
            })
            .is_some()
    );
    let mut schedule = Schedule::new(3, Vec::new(), vec![(1, Box::new(limited))]);
    assert!(schedule.next().is_some());
    assert!(schedule.next().is_none());

    // The loop ends when the schedule is exhausted, and says so.
    let mut runner = Scripted::new(|_| run(OutcomeClass::Miss, 1), |_| unreachable!());
    let mut only_explicit = Schedule::new(3, vec![vec![int(1)]], Vec::new());
    let report = run_loop(
        &mut runner,
        &mut only_explicit,
        &settings(1),
        Budget::Cases(10),
        None,
    );
    assert_eq!(report.totals.cases, 1);
    let statement = report.no_witness().cloned().expect("no witness").statement;
    assert!(
        statement.contains("every proposer was exhausted"),
        "{statement}"
    );
}

#[test]
fn equal_inputs_give_equal_report_bytes() {
    let report = |seed| {
        let mut runner = Scripted::new(
            |values| {
                let mut case = run(OutcomeClass::Miss, 2);
                case.applied = vec![format!("rule-{}", as_int(&values[0]) % 3)];
                case
            },
            |_| unreachable!(),
        );
        run_loop(
            &mut runner,
            &mut counter_schedule(seed, 0),
            &settings(1),
            Budget::Cases(6),
            None,
        )
        .to_canonical_json()
    };
    assert_eq!(report(5), report(5));
}

// ---------------------------------------------------------------------------------------------
// Confirmation

#[test]
fn a_confirmation_that_disagrees_is_an_engine_defect_never_a_hit() {
    let mut runner = Scripted::new(
        |values| {
            if as_int(&values[0]) == 2 {
                hit(values, 1, "end")
            } else {
                run(OutcomeClass::Miss, 1)
            }
        },
        |_| Ok(run(OutcomeClass::Miss, 1)),
    );
    let report = run_loop(
        &mut runner,
        &mut counter_schedule(1, 1),
        &settings(1),
        Budget::Cases(4),
        None,
    );
    assert!(matches!(
        report.outcome,
        CampaignOutcome::NoWitnessFound { .. }
    ));
    assert_eq!(report.witness(), None);
    assert_eq!(
        classes(&report),
        [(OutcomeClass::Miss, 3), (OutcomeClass::Unsupported, 1)]
    );
    assert_eq!(report.engine_defects.len(), 1);
    assert_eq!(report.engine_defects[0].case, Some(1));
    assert!(
        report.engine_defects[0]
            .description
            .contains("confirmation"),
        "{:?}",
        report.engine_defects
    );
}

#[test]
fn a_confirmation_that_reaches_another_state_or_fails_is_an_engine_defect() {
    for confirm in [
        Box::new(|values: &[Value]| Ok(hit(values, 1, "another end"))) as ConfirmScript,
        Box::new(|_: &[Value]| Err("the fresh backend did not build".to_owned())),
    ] {
        let mut runner = Scripted::new(|values| hit(values, 1, "end"), |_| unreachable!());
        runner.confirm = confirm;
        let report = run_loop(
            &mut runner,
            &mut counter_schedule(1, 1),
            &settings(1),
            Budget::Cases(2),
            None,
        );
        assert_eq!(report.witness(), None);
        assert_eq!(classes(&report), [(OutcomeClass::Unsupported, 2)]);
        assert_eq!(report.engine_defects.len(), 2);
    }
}

#[test]
fn shrink_candidates_are_kept_only_when_their_confirmation_agrees() {
    // The campaign's backend says every value from 10 hits; the fresh confirmation agrees only
    // from 20. Candidates in between are dropped, each as an engine defect.
    let mut runner = Scripted::new(
        |values| {
            if as_int(&values[0]) >= 10 {
                hit(values, 1, "end")
            } else {
                run(OutcomeClass::Miss, 1)
            }
        },
        |values| {
            if as_int(&values[0]) >= 20 {
                Ok(hit(values, 1, "end"))
            } else {
                Ok(run(OutcomeClass::Miss, 1))
            }
        },
    );
    let mut schedule = Schedule::new(
        1,
        Vec::new(),
        vec![(1, Counter::boxed(ProposerKind::Blind, 100, 0))],
    );
    let report = run_loop(
        &mut runner,
        &mut schedule,
        &settings(1),
        Budget::Cases(1),
        None,
    );
    let witness = report.witness().cloned().expect("a witness");
    assert_eq!(witness.first.holes[0].value, int(100));
    let shrunk = witness.shrunk.expect("a shrunk witness");
    assert_eq!(shrunk.holes[0].value, int(20));
    // Every candidate the campaign's backend said hits was confirmed, kept or not.
    let prescreen_hits: Vec<Vec<Value>> = runner.cases[1..]
        .iter()
        .filter(|values| as_int(&values[0]) >= 10)
        .cloned()
        .collect();
    assert_eq!(runner.confirmed[1..], prescreen_hits[..]);
    assert!(
        !report.engine_defects.is_empty()
            && report
                .engine_defects
                .iter()
                .all(|defect| defect.case == Some(0) && defect.description.contains("shrink")),
        "{:?}",
        report.engine_defects
    );
    assert!(matches!(
        report.outcome,
        CampaignOutcome::WitnessFound { .. }
    ));
}

#[test]
fn self_check_defects_of_shrink_screening_and_confirmation_runs_are_recorded() {
    // Phase-1 review N3: a shrink candidate's screening run and every confirmation carry the
    // rule graph's self-check defects like a case.
    let mut runner = Scripted::new(
        |values| CaseRun {
            defects: vec!["screened defect".to_owned()],
            ..hit(values, 1, "end")
        },
        |values| {
            Ok(CaseRun {
                defects: vec!["confirmed defect".to_owned()],
                ..hit(values, 1, "end")
            })
        },
    );
    let mut schedule = Schedule::new(
        1,
        Vec::new(),
        vec![(1, Counter::boxed(ProposerKind::Blind, 100, 0))],
    );
    let report = run_loop(
        &mut runner,
        &mut schedule,
        &settings(1),
        Budget::Cases(1),
        None,
    );
    assert!(report.witness().is_some(), "{:?}", report.outcome);
    let described = |prefix: &str, suffix: &str| {
        report.engine_defects.iter().any(|defect| {
            defect.case == Some(0)
                && defect.description.starts_with(prefix)
                && defect.description.ends_with(suffix)
        })
    };
    assert!(
        described("confirmation of [", "confirmed defect"),
        "{:?}",
        report.engine_defects
    );
    assert!(
        described("shrink candidate [", "screened defect"),
        "{:?}",
        report.engine_defects
    );
    // The case's own defect, recorded without a prefix.
    assert!(
        described("screened", "screened defect"),
        "{:?}",
        report.engine_defects
    );
}

#[test]
fn a_confirmation_that_aborts_aborts_the_campaign() {
    // Phase-1 review N6: a fresh backend whose solver prelude fails would fail every run, so
    // the campaign aborts rather than booking one engine defect per candidate.
    let mut runner = Scripted::new(|values| hit(values, 1, "end"), |_| unreachable!());
    runner.confirm_aborts = true;
    let report = run_loop(
        &mut runner,
        &mut counter_schedule(1, 1),
        &settings(1),
        Budget::Cases(10),
        None,
    );
    let CampaignOutcome::Aborted { reason, .. } = &report.outcome else {
        panic!("{:?}", report.outcome);
    };
    assert!(reason.contains("solver prelude"), "{reason}");
    assert_eq!(report.totals.cases, 1);
    assert_eq!(report.totals.unconfirmed, 1);
    assert_eq!(classes(&report), [(OutcomeClass::Unsupported, 1)]);
    assert!(
        report.engine_defects.is_empty(),
        "{:?}",
        report.engine_defects
    );
    assert_eq!(runner.confirmed.len(), 1);
}

#[test]
fn shrinking_stops_at_the_candidate_cap() {
    // Every candidate hits on the campaign's backend and never on confirmation, so shrinking
    // never progresses; the cap bounds it.
    let mut runner = Scripted::new(
        |values| hit(values, 1, "end"),
        |values| {
            if as_int(&values[0]) == i64::MAX {
                Ok(hit(values, 1, "end"))
            } else {
                Ok(run(OutcomeClass::Miss, 1))
            }
        },
    );
    let mut schedule = Schedule::new(
        1,
        Vec::new(),
        vec![(1, Counter::boxed(ProposerKind::Blind, i64::MAX, 0))],
    );
    run_loop(
        &mut runner,
        &mut schedule,
        &settings(1),
        Budget::Cases(1),
        None,
    );
    let shrink_runs = u64::try_from(runner.cases.len() - 1).expect("small");
    assert!(shrink_runs <= MAX_SHRINK_RUNS, "{shrink_runs}");
}

// ---------------------------------------------------------------------------------------------
// Outcomes and totals

#[test]
fn a_cancelled_token_ends_the_campaign_before_the_next_case() {
    let token = CancellationToken::new();
    token.cancel();
    let mut runner = Scripted::new(|_| run(OutcomeClass::Miss, 1), |_| unreachable!());
    let report = run_loop(
        &mut runner,
        &mut counter_schedule(1, 1),
        &settings(1),
        Budget::Cases(10),
        Some(&token),
    );
    assert!(matches!(report.outcome, CampaignOutcome::Cancelled { .. }));
    assert_eq!(report.totals.cases, 0);
    assert!(report.no_witness().is_some());
}

#[test]
fn an_abort_ends_the_campaign() {
    let mut runner = Scripted::new(|_| run(OutcomeClass::Miss, 1), |_| unreachable!());
    runner.abort_at = Some(2);
    let report = run_loop(
        &mut runner,
        &mut counter_schedule(1, 1),
        &settings(1),
        Budget::Cases(10),
        None,
    );
    let CampaignOutcome::Aborted { reason, .. } = &report.outcome else {
        panic!("{:?}", report.outcome)
    };
    assert_eq!(reason, "solver prelude failed");
    assert_eq!(report.totals.cases, 2);
}

#[test]
fn cases_outside_the_determinism_contract_are_counted_and_add_no_coverage() {
    let mut runner = Scripted::new(
        |values| {
            let n = as_int(&values[0]);
            let mut case = run(
                if n == 2 {
                    OutcomeClass::Timeout
                } else {
                    OutcomeClass::Miss
                },
                1,
            );
            case.applied = vec![format!("applied-{n}")];
            case.matched = vec![format!("matched-{n}")];
            case.blocked = n == 3;
            case.outside_determinism = n == 2;
            case.load_records = vec![crate::report::LoadRecord {
                kind: "contradicted-claim".into(),
                detail: "td".into(),
            }];
            case
        },
        |_| unreachable!(),
    );
    let report = run_loop(
        &mut runner,
        &mut counter_schedule(1, 1),
        &settings(1),
        Budget::Cases(3),
        None,
    );
    assert_eq!(report.totals.outside_determinism, 1);
    assert_eq!(report.totals.target_blocked, 1);
    let applied: Vec<&str> = report
        .totals
        .coverage
        .applied
        .iter()
        .map(String::as_str)
        .collect();
    assert_eq!(applied, ["applied-1", "applied-3"]);
    assert_eq!(report.load_records.len(), 1, "load records reported once");
}

// ---------------------------------------------------------------------------------------------
// The no-witness statement

fn totals_with(classes: &[(OutcomeClass, u64)]) -> Totals {
    Totals {
        cases: classes.iter().map(|(_, count)| count).sum(),
        work: 1234,
        classes: classes.iter().copied().collect(),
        ..Totals::default()
    }
}

#[test]
fn the_no_witness_statement_names_the_path_mode_and_the_bound_to_raise() {
    let options = CaseOptions {
        max_depth: Some(20),
        max_work: Some(500),
        ..CaseOptions::default()
    };
    let bounded = totals_with(&[
        (OutcomeClass::Miss, 5),
        (OutcomeClass::DepthBound, 2),
        (OutcomeClass::WorkBound, 1),
    ]);
    let statement = no_witness(
        Ending::Budget,
        &bounded,
        &Cuts::default(),
        Budget::Cases(8),
        &options,
        100,
    );
    assert_eq!(statement.path_mode, PathMode::OnePath);
    let text = statement.statement;
    for expected in [
        "No witness was found in 8 cases",
        "not a proof that no witness exists",
        "one-path mode",
        "first-applicable path",
        "all-paths",
        "2 cases stopped at max-depth 20: raise max-depth",
        "1 case stopped at max-work 500: raise max-work",
        "raise the case budget",
    ] {
        assert!(text.contains(expected), "missing {expected:?} in {text:?}");
    }

    let all_paths = CaseOptions {
        paths: PathMode::AllPaths,
        ..CaseOptions::default()
    };
    let misses = totals_with(&[(OutcomeClass::Miss, 3)]);
    let text = no_witness(
        Ending::Budget,
        &misses,
        &Cuts::default(),
        Budget::Work(9000),
        &all_paths,
        100,
    )
    .statement;
    for expected in [
        "No witness was found in 3 cases",
        "all-paths mode",
        "raise the work budget above 9000",
    ] {
        assert!(text.contains(expected), "missing {expected:?} in {text:?}");
    }
    assert!(!text.contains("max-depth"), "{text}");
    assert!(!text.contains("first-applicable"), "{text}");
}

#[test]
fn a_campaign_without_a_witness_reports_the_statement_and_its_totals() {
    let mut runner = Scripted::new(
        |values| {
            if as_int(&values[0]) % 2 == 0 {
                run(OutcomeClass::DepthBound, 1)
            } else {
                run(OutcomeClass::Miss, 1)
            }
        },
        |_| unreachable!(),
    );
    let mut loop_settings = settings(1);
    loop_settings.options.max_depth = Some(7);
    let report = run_loop(
        &mut runner,
        &mut counter_schedule(1, 1),
        &loop_settings,
        Budget::Cases(4),
        None,
    );
    let statement = report.no_witness().cloned().expect("no witness").statement;
    assert!(statement.contains("max-depth 7"), "{statement}");
    assert!(statement.contains("one-path mode"), "{statement}");
}

// ---------------------------------------------------------------------------------------------
// Shrinking

fn shrink_ints(start: i64, constraints: Constraints, hits: impl Fn(i64) -> bool) -> (i64, usize) {
    let mut tests = 0;
    let shrunk = shrink(&[int(start)], vec![None], &[constraints], &mut |values| {
        tests += 1;
        if hits(as_int(&values[0])) {
            Verdict::Hit
        } else {
            Verdict::Miss
        }
    });
    (as_int(&shrunk[0]), tests)
}

#[test]
fn integer_moves_bisect_towards_the_admissible_value_nearest_zero() {
    let (value, tests) = shrink_ints(1_000_000, Constraints::default(), |n| n >= 17);
    assert_eq!(value, 17);
    // About log2(10^6) bisection steps, then a second pass that confirms 17 is a fixpoint.
    assert!(tests <= 30, "{tests} tests");
    assert_eq!(
        shrink_ints(-1_000, Constraints::default(), |n| n <= -5).0,
        -5
    );
    assert_eq!(shrink_ints(40, Constraints::default(), |_| true).0, 0);
    let from_ten = Constraints {
        range: Some(IntRange {
            min: Some(BigInt::from(10)),
            max: None,
        }),
        ..Constraints::default()
    };
    assert_eq!(shrink_ints(400, from_ten, |n| n >= 10).0, 10);
}

#[test]
fn length_moves_keep_the_shortest_prefix_that_still_hits() {
    let list = Value::List((0..40).map(int).collect());
    let shrunk = shrink(
        &[list],
        vec![None],
        &[Constraints::default()],
        &mut |values| match &values[0] {
            Value::List(items) if items.len() >= 3 => Verdict::Hit,
            _ => Verdict::Miss,
        },
    );
    assert_eq!(shrunk, [Value::List(vec![int(0), int(1), int(2)])]);

    let at_least_five = Constraints {
        length: Some(LengthRange {
            min: Some(5),
            max: None,
        }),
        ..Constraints::default()
    };
    let shrunk = shrink(
        &[Value::String("abcdefghij".into())],
        vec![None],
        &[at_least_five],
        &mut |_| Verdict::Hit,
    );
    assert_eq!(shrunk, [Value::String("abcde".into())]);
}

/// A value tree over a fixed sequence of ever simpler values.
struct Steps {
    values: Vec<i64>,
    at: usize,
}

impl ValueShrinker for Steps {
    fn current(&self) -> Value {
        int(self.values[self.at])
    }

    fn simplify(&mut self) -> bool {
        if self.at + 1 < self.values.len() {
            self.at += 1;
            true
        } else {
            false
        }
    }

    fn complicate(&mut self) -> bool {
        false
    }
}

#[test]
fn value_trees_shrink_blind_values_and_stop_ends_shrinking() {
    let tree = Steps {
        values: vec![64, 32, 16, 8, 4],
        at: 0,
    };
    let mut seen = Vec::new();
    let shrunk = shrink(
        &[int(64), int(7)],
        vec![Some(Box::new(tree)), None],
        &[Constraints::default(), Constraints::default()],
        &mut |values| {
            seen.push(values.to_vec());
            if as_int(&values[0]) >= 16 && as_int(&values[1]) >= 7 {
                Verdict::Hit
            } else {
                Verdict::Miss
            }
        },
    );
    assert_eq!(shrunk, [int(16), int(7)]);
    assert_eq!(
        seen[..3],
        [
            vec![int(32), int(7)],
            vec![int(16), int(7)],
            vec![int(8), int(7)]
        ]
    );

    let mut tests = 0;
    let shrunk = shrink(
        &[int(1000)],
        vec![None],
        &[Constraints::default()],
        &mut |_| {
            tests += 1;
            Verdict::Stop
        },
    );
    assert_eq!(shrunk, [int(1000)]);
    assert_eq!(tests, 1);
}

#[test]
fn the_coverage_feedback_finds_new_rules_only_in_misses() {
    let observation = |class, applied: &[&str]| Observation {
        case: 0,
        class,
        applied: applied.iter().map(|rule| (*rule).to_owned()).collect(),
        matched: Vec::new(),
        work: 1,
        score: None,
    };
    let mut feedback = CoverageFeedback::default();
    assert!(!feedback.is_interesting(&observation(OutcomeClass::DepthBound, &["a"])));
    assert!(feedback.is_interesting(&observation(OutcomeClass::Miss, &["a"])));
    assert!(!feedback.is_interesting(&observation(OutcomeClass::Miss, &["a"])));
    assert!(feedback.is_interesting(&observation(OutcomeClass::Miss, &["a", "b"])));
}

// ---------------------------------------------------------------------------------------------
// Fix round: kinds of kill, cancelled confirmations, the statement's counts, the case sequence

fn kill(values: &[Value], state: &str, kind: KillKind) -> CaseRun {
    let mut case = hit(values, 1, state);
    if let Some(detail) = &mut case.hit {
        detail.kill = Some(kind);
    }
    case
}

#[test]
fn a_confirmation_with_another_kind_of_kill_is_an_engine_defect() {
    let mut runner = Scripted::new(
        |values| kill(values, "end", KillKind::AddedEnd),
        |values| Ok(kill(values, "end", KillKind::RemovedEnd)),
    );
    let report = run_loop(
        &mut runner,
        &mut counter_schedule(1, 1),
        &settings(1),
        Budget::Cases(1),
        None,
    );
    assert_eq!(report.witness(), None);
    assert_eq!(report.totals.unconfirmed, 1);
    assert_eq!(report.engine_defects.len(), 1);
    let statement = report.no_witness().expect("no witness").statement.clone();
    assert!(
        statement.contains("1 candidate reached the target but was not confirmed"),
        "{statement}"
    );
}

#[test]
fn shrinking_keeps_the_kind_of_kill_and_the_facts_follow_it() {
    // From 50 down the mutant removes an end instead of adding one: another behaviour, which
    // shrinking must not slide into.
    let judge = |values: &[Value]| {
        let n = as_int(&values[0]);
        if n >= 50 {
            kill(values, "end", KillKind::RemovedEnd)
        } else if n >= 10 {
            kill(values, "end", KillKind::AddedEnd)
        } else {
            run(OutcomeClass::Miss, 1)
        }
    };
    let mut runner = Scripted::new(judge, move |values| Ok(judge(values)));
    let mut schedule = Schedule::new(
        1,
        Vec::new(),
        vec![(1, Counter::boxed(ProposerKind::Blind, 100, 0))],
    );
    let report = run_loop(
        &mut runner,
        &mut schedule,
        &settings(1),
        Budget::Cases(1),
        None,
    );
    let witness = report.witness().expect("a witness");
    assert_eq!(witness.first.kill, Some(KillKind::RemovedEnd));
    let shrunk = witness.shrunk.as_ref().expect("a shrunk witness");
    assert_eq!(shrunk.holes[0].value, int(50));
    assert_eq!(shrunk.kill, Some(KillKind::RemovedEnd));
    assert!(
        witness
            .clean_leaf_facts
            .contains(&"baseline-end-not-in-mutant-ends".to_owned()),
        "{:?}",
        witness.clean_leaf_facts
    );
    assert!(
        !witness
            .clean_leaf_facts
            .contains(&"every-baseline-end-constructor-only".to_owned())
    );
}

#[test]
fn a_cancelled_confirmation_leaves_a_trace_and_counts_outside_determinism() {
    let token = CancellationToken::new();
    let cancelling = token.clone();
    let mut runner = Scripted::new(
        |values| {
            let mut case = hit(values, 1, "end");
            case.applied = vec!["covered".into()];
            case
        },
        move |_| {
            cancelling.cancel();
            Ok(run(OutcomeClass::Timeout, 1))
        },
    );
    let report = run_loop(
        &mut runner,
        &mut counter_schedule(1, 7),
        &settings(1),
        Budget::Cases(10),
        Some(&token),
    );
    assert!(matches!(report.outcome, CampaignOutcome::Cancelled { .. }));
    assert_eq!(classes(&report), [(OutcomeClass::Timeout, 1)]);
    assert_eq!(report.totals.outside_determinism, 1);
    assert_eq!(report.totals.unconfirmed, 1);
    assert!(report.totals.coverage.applied.is_empty());
    assert!(
        report
            .warnings
            .iter()
            .any(|warning| warning.contains("case 0")
                && warning.contains("confirmation was cancelled")
                && warning.contains(r#"{"int":"7"}"#)),
        "{:?}",
        report.warnings
    );
    let statement = &report.no_witness().expect("a statement").statement;
    assert!(statement.contains("not confirmed"), "{statement}");
    assert!(
        statement.contains("outside the determinism contract"),
        "{statement}"
    );
}

#[test]
fn the_statement_counts_every_case_that_could_not_yield_a_witness() {
    let all_incomplete = totals_with(&[(OutcomeClass::BaselineIncomplete, 64)]);
    let text = no_witness(
        Ending::Budget,
        &all_incomplete,
        &Cuts::default(),
        Budget::Cases(64),
        &CaseOptions::default(),
        100,
    )
    .statement;
    assert!(
        text.contains("64 cases had an incomplete baseline, so no kill could be judged"),
        "{text}"
    );

    let mut mixed = totals_with(&[
        (OutcomeClass::Miss, 2),
        (OutcomeClass::Unsupported, 3),
        (OutcomeClass::Rejected, 4),
        (OutcomeClass::DepthBound, 1),
    ]);
    mixed.unconfirmed = 2;
    mixed.outside_determinism = 1;
    let all_paths = CaseOptions {
        paths: PathMode::AllPaths,
        max_depth: Some(9),
        ..CaseOptions::default()
    };
    let text = no_witness(
        Ending::Budget,
        &mixed,
        &Cuts::default(),
        Budget::Cases(10),
        &all_paths,
        100,
    )
    .statement;
    for expected in [
        "4 cases were rejected and not run",
        "3 cases could not be judged (unsupported) and may hide a witness",
        "2 candidates reached the target but were not confirmed",
        "1 case was outside the determinism contract",
        "followed up to the bounds below (all-paths mode)",
        "1 case stopped at max-depth 9",
    ] {
        assert!(text.contains(expected), "missing {expected:?} in {text:?}");
    }
    assert!(
        !text.contains("Every path of each input was explored"),
        "{text}"
    );

    let mut rejected = totals_with(&[(OutcomeClass::Rejected, 3)]);
    rejected.rejections =
        BTreeMap::from([(RejectionReason::Print, 1), (RejectionReason::Assembly, 2)]);
    let text = no_witness(
        Ending::RejectedOut,
        &rejected,
        &Cuts::default(),
        Budget::Cases(10),
        &CaseOptions::default(),
        3,
    )
    .statement;
    assert!(
        text.contains("rejection cap of 3 rejected cases (1 print, 2 assembly)"),
        "{text}"
    );
}

#[test]
fn the_statement_never_claims_every_path_explored_for_cut_or_unjudged_cases() {
    // Phase-1 review S2: in all-paths mode, `baseline-incomplete` and `reached-unfinished`
    // cases were not explored to their ends either.
    let all_paths = CaseOptions {
        paths: PathMode::AllPaths,
        max_depth: Some(3),
        ..CaseOptions::default()
    };
    let depth_cut = CutCounts {
        depth: 10,
        ..CutCounts::default()
    };
    let incomplete = totals_with(&[(OutcomeClass::BaselineIncomplete, 10)]);
    let cuts = Cuts {
        incomplete: depth_cut,
        ..Cuts::default()
    };
    let text = no_witness(
        Ending::Budget,
        &incomplete,
        &cuts,
        Budget::Cases(10),
        &all_paths,
        100,
    )
    .statement;
    for expected in [
        "10 cases had an incomplete baseline, so no kill could be judged.",
        "In 10 of them a baseline path stopped at max-depth 3: raise max-depth.",
        "followed up to the bounds below (all-paths mode)",
    ] {
        assert!(text.contains(expected), "missing {expected:?} in {text:?}");
    }
    assert!(
        !text.contains("Every path of each input was explored"),
        "{text}"
    );

    // A baseline cut by no bound: no bound advice.
    let cuts = Cuts {
        incomplete: CutCounts {
            none: 10,
            ..CutCounts::default()
        },
        ..Cuts::default()
    };
    let text = no_witness(
        Ending::Budget,
        &incomplete,
        &cuts,
        Budget::Cases(10),
        &all_paths,
        100,
    )
    .statement;
    assert!(
        text.contains("In 10 of them no bound cut the baseline"),
        "{text}"
    );
    assert!(!text.contains("raise max-depth"), "{text}");
    assert!(
        !text.contains("Every path of each input was explored"),
        "{text}"
    );
}

#[test]
fn the_statement_advises_raising_a_bound_only_for_unfinished_cases_a_bound_cut() {
    let all_paths = CaseOptions {
        paths: PathMode::AllPaths,
        max_depth: Some(3),
        ..CaseOptions::default()
    };
    // Unfinished cases: bound advice only for the ones a bound cut.
    let unfinished = totals_with(&[(OutcomeClass::ReachedUnfinished, 3)]);
    let cuts = Cuts {
        unfinished: CutCounts {
            depth: 1,
            none: 2,
            ..CutCounts::default()
        },
        ..Cuts::default()
    };
    let text = no_witness(
        Ending::Budget,
        &unfinished,
        &cuts,
        Budget::Cases(3),
        &all_paths,
        100,
    )
    .statement;
    for expected in [
        "3 cases reached the target without ending naturally.",
        "In 1 of them a path stopped at max-depth 3: raise max-depth so that they finish.",
        "2 of them stopped abnormally (stuck before a natural end, or at an undefined step), \
         which no bound changes.",
    ] {
        assert!(text.contains(expected), "missing {expected:?} in {text:?}");
    }
    assert!(
        !text.contains("Every path of each input was explored"),
        "{text}"
    );
    let abnormal = Cuts {
        unfinished: CutCounts {
            none: 3,
            ..CutCounts::default()
        },
        ..Cuts::default()
    };
    let text = no_witness(
        Ending::Budget,
        &unfinished,
        &abnormal,
        Budget::Cases(3),
        &all_paths,
        100,
    )
    .statement;
    assert!(!text.contains("so that they finish"), "{text}");
    assert!(!text.contains("raise max-depth"), "{text}");
}

#[test]
fn the_statement_does_not_say_backend_refused_cases_were_not_run() {
    let mut rejected = totals_with(&[(OutcomeClass::Miss, 1), (OutcomeClass::Rejected, 5)]);
    rejected.rejections = BTreeMap::from([
        (RejectionReason::Print, 2),
        (RejectionReason::BackendRefused, 3),
    ]);
    let text = no_witness(
        Ending::Budget,
        &rejected,
        &Cuts::default(),
        Budget::Cases(6),
        &CaseOptions::default(),
        100,
    )
    .statement;
    for expected in [
        "2 cases were rejected and not run.",
        "3 cases were rejected by the backend, which refused the initial state.",
    ] {
        assert!(text.contains(expected), "missing {expected:?} in {text:?}");
    }
    rejected.rejections = BTreeMap::from([(RejectionReason::BackendRefused, 5)]);
    let text = no_witness(
        Ending::Budget,
        &rejected,
        &Cuts::default(),
        Budget::Cases(6),
        &CaseOptions::default(),
        100,
    )
    .statement;
    assert!(!text.contains("not run"), "{text}");
    assert!(
        text.contains("5 cases were rejected by the backend"),
        "{text}"
    );
}

#[test]
fn the_loop_counts_what_cut_each_unfinished_case() {
    let mut runner = Scripted::new(
        |values| CaseRun {
            cut: Cut {
                work: as_int(&values[0]) % 2 == 0,
                ..Cut::default()
            },
            ..run(OutcomeClass::ReachedUnfinished, 1)
        },
        |_| unreachable!("no case hits"),
    );
    let report = run_loop(
        &mut runner,
        &mut counter_schedule(1, 1),
        &settings(1),
        Budget::Cases(4),
        None,
    );
    let statement = &report.no_witness().expect("no witness").statement;
    assert!(
        statement.contains("4 cases reached the target without ending naturally."),
        "{statement}"
    );
    assert!(
        statement.contains("In 2 of them a path stopped at max-work 1000: raise max-work"),
        "{statement}"
    );
    assert!(
        statement.contains("2 of them stopped abnormally"),
        "{statement}"
    );
}

#[test]
fn the_case_sequence_digest_pins_the_proposed_values() {
    let digest = |start: i64, cases: u64| {
        let mut runner = Scripted::new(|_| run(OutcomeClass::Miss, 1), |_| unreachable!());
        run_loop(
            &mut runner,
            &mut counter_schedule(1, start),
            &settings(1),
            Budget::Cases(cases),
            None,
        )
        .totals
        .case_sequence_digest
    };
    assert_eq!(digest(1, 5), digest(1, 5));
    assert_ne!(digest(1, 5), digest(2, 5));
    assert_ne!(digest(1, 5), digest(1, 4));
    assert_eq!(digest(1, 0), crate::report::digest_hex(b""));
}

#[test]
fn a_state_the_backend_refuses_is_recognized_on_either_side() {
    use crate::exec::{CaseFailure, CaseResult, FailureCause};
    let result = |cause| CaseResult {
        leaves: Vec::new(),
        work: 0,
        coverage: None,
        stack_stops: 0,
        smt_unknowns: 0,
        run_allowance_refusals: 0,
        load_records: Vec::new(),
        safety_limit_hit: false,
        failure: Some(CaseFailure {
            message: "refused".into(),
            cause,
        }),
        run_facts_off_leaves: false,
    };
    assert!(super::live::refused(&result(FailureCause::StateRefused)));
    assert!(!super::live::refused(&result(FailureCause::Other)));
}
