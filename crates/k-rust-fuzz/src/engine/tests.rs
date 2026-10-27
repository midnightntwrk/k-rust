//! Unit tests of the engine's loop, schedule, budget, confirmation and shrinking, against a
//! scripted [`CaseRunner`] and scripted proposers (no definition is executed).

use std::collections::BTreeMap;

use k_rust::backend::CancellationToken;
use num_bigint::BigInt;

use super::{
    campaign_loop::{
        CutCounts, Cuts, Ending, LoopSettings, MAX_SHRINK_RUNS, no_witness, run_loop,
        run_loop_filtered,
    },
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
    exec::{Abort, ComparableCondition, OutcomeClass},
    filter::{FilterRefusal, WitnessFilter},
    holes::HoleLocation,
    report::{
        CampaignOutcome, Comparability, DefinitionIdentity, DefinitionRole, FuzzReport, HitLabel,
        HoleValue, KillKind, Reaching, RejectionReason, ReportIdentity, Totals, WitnessSide,
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
        applied_counts: std::collections::BTreeMap::new(),
        blocked: false,
        guards: std::collections::BTreeMap::new(),
        comparisons: Vec::new(),
        progress: None,
        outside_determinism: false,
        rejection: None,
        unjudged: matches!(
            class,
            OutcomeClass::Unsupported | OutcomeClass::BaselineIncomplete
        )
        .then_some(crate::exec::UnjudgedReason::EngineDefect),
        load_records: Vec::new(),
        defects: Vec::new(),
        warnings: Vec::new(),
        hit: None,
        incidental: None,
        cut: Cut::default(),
        baseline_ended_within: None,
        pattern_body_matches: None,
        pattern_body_judged: 0,
        named_hooks: None,
        crash: None,
        poisoned: false,
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
            halts: Vec::new(),
            undefined_rules: Vec::new(),
            work: None,
        }],
        reaching: Reaching {
            role: DefinitionRole::Baseline,
            leaf: Some(0),
            step: None,
            configuration: None,
        },
        kill: None,
        steps: Some(3),
        reaching_state: state.to_owned(),
        krun_command: Some(format!("krust krun {values:?}")),
        mutant_krun_command: None,
        program: None,
        comparable: None,
        config_vars: std::collections::BTreeMap::new(),
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
    /// The classes the loop said it kept an incidental finding of, in order.
    kept: Vec<OutcomeClass>,
    /// The work of the comparable judgement a witness case's case did not make
    /// ([`CaseRunner::comparability`]); `None` gives none.
    judgement_work: Option<u64>,
    /// The values of every comparable judgement asked for, in order.
    judged: Vec<Vec<Value>>,
    /// Every rebuild after a crash fails ([`CaseRunner::recover`]).
    recover_fails: bool,
    /// The kind of the abort at [`Self::abort_at`].
    abort_kind: crate::report::AbortKind,
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
            kept: Vec::new(),
            judgement_work: None,
            judged: Vec::new(),
            recover_fails: false,
            abort_kind: crate::report::AbortKind::SolverPreludeInconsistent,
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
            return Err(Abort::new(self.abort_kind, "solver prelude failed"));
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
            return Err(ConfirmFailure::Abort(Abort::new(
                crate::report::AbortKind::SolverPreludeInconsistent,
                "the fresh backend's solver prelude failed",
            )));
        }
        (self.confirm)(values).map_err(ConfirmFailure::Failed)
    }

    fn admissible(&self, hole: usize, value: &Value) -> bool {
        (self.admissible)(hole, value)
    }

    fn incidental_kept(&mut self, class: OutcomeClass) {
        self.kept.push(class);
    }

    fn comparability_pending(&self) -> bool {
        self.judgement_work.is_some()
    }

    fn recover(&mut self) -> Result<(), String> {
        if self.recover_fails {
            Err("the scripted rebuild fails".into())
        } else {
            Ok(())
        }
    }

    fn comparability(
        &mut self,
        values: &[Value],
        _cancel: Option<&CancellationToken>,
    ) -> Option<super::runner::JudgedComparability> {
        let work = self.judgement_work?;
        self.judged.push(values.to_vec());
        Some(super::runner::JudgedComparability {
            comparable: Comparability {
                holds: false,
                reasons: vec![ComparableCondition::Clock],
                hooks: BTreeMap::new(),
            },
            work,
            crash: None,
            poisoned: false,
        })
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
        fuzz_revision: "test".into(),
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
        target_rule: None,
        options: CaseOptions::default(),
        execution_modality: None,
        proposers: ProposerConfig::default(),
        bounds: GenerationBounds::default(),
        caps: crate::report::GenerationCaps::current(),
        rejection_cap: 1000,
        seed: 1,
        budget: Budget::Cases(0),
        thread_stack_size: None,
        solver: "none".into(),
        parse_diagnostic_work: "1048576".into(),
        dictionary: None,
        climb: None,
        corpus: None,
        solve: None,
        effective_constraints: Vec::new(),
        filter: None,
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
        hole_names: (0..holes).map(|hole| format!("H{hole}")).collect(),
        sort_overrides: Vec::new(),
        warnings: Vec::new(),
        definition_findings: Vec::new(),
        scorer: None,
        pool_rank: std::collections::BTreeMap::new(),
        normal_end: None,
        rule_names: std::sync::Arc::default(),
        domain: None,
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

/// A witness case's comparable judgement that its case did not make is made after shrinking,
/// once per reported witness case, outside every case (INT9 review S2): under a work budget the
/// same cases, confirmations and shrink candidates run as without it, and its work goes to the
/// total alone.
#[test]
fn a_comparable_judgement_outside_the_case_moves_no_case_or_shrink_run() {
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
    runner.judgement_work = Some(1000);
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
    // As in `a_work_budget_charges_confirmation_and_shrinking`.
    let runs: Vec<i64> = runner
        .cases
        .iter()
        .map(|values| as_int(&values[0]))
        .collect();
    assert_eq!(runs, [100, 0, 50, 25, 37]);
    assert_eq!(runner.confirmed, [vec![int(100)], vec![int(50)]]);
    assert_eq!(runner.judged, [vec![int(50)], vec![int(100)]]);
    assert_eq!(report.totals.work, 60 + 2 * 1000);
    assert_eq!(report.totals.cases, 1);
    assert_eq!(report.totals.outside_determinism, 0);
    let witness = report.witness().cloned().expect("a witness");
    let judged = Some(Comparability {
        holds: false,
        reasons: vec![ComparableCondition::Clock],
        hooks: BTreeMap::new(),
    });
    assert_eq!(witness.first.comparable, judged);
    assert_eq!(witness.shrunk.expect("a shrunk witness").comparable, judged);
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

/// FZ-REPLAY-WHOLE fix round S-C: a confirmation the clock stopped is no engine defect; the
/// candidate's case is outside the determinism contract (another run may confirm it and end the
/// campaign there), so it is the first case a re-run may differ at.
#[test]
fn a_confirmation_outside_the_contract_puts_its_case_outside_the_contract() {
    let mut runner = Scripted::new(
        |values| {
            if as_int(&values[0]) == 2 {
                hit(values, 10, "end-2")
            } else {
                run(OutcomeClass::Miss, 10)
            }
        },
        |_| {
            let mut stopped = run(OutcomeClass::Timeout, 3);
            stopped.outside_determinism = true;
            Ok(stopped)
        },
    );
    let report = run_loop(
        &mut runner,
        &mut counter_schedule(1, 1),
        &settings(1),
        Budget::Cases(4),
        None,
    );
    assert!(report.witness().is_none());
    assert!(
        report.engine_defects.is_empty(),
        "{:?}",
        report.engine_defects
    );
    assert_eq!(report.totals.unconfirmed, 1);
    assert_eq!(report.totals.outside_determinism, 1);
    assert_eq!(report.totals.first_outside_determinism, Some(1));
    assert_eq!(report.totals.classes.get(&OutcomeClass::Timeout), Some(&1));
}

/// Counts up from 1, and reports one run outside the determinism contract once it has made
/// `after` proposals, as the solve proposer does when the clock stops its symbolic run.
struct OutsideAfter {
    calls: u32,
    after: u32,
}

impl Proposer for OutsideAfter {
    fn kind(&self) -> ProposerKind {
        ProposerKind::Blind
    }

    fn propose(&mut self, _context: &mut ProposalContext<'_>) -> Option<Proposal> {
        self.calls += 1;
        Some(Proposal::plain(
            Origin::Scheduled(ProposerKind::Blind),
            vec![int(i64::from(self.calls))],
        ))
    }

    fn observe(&mut self, _proposal: &Proposal, _observation: &Observation, _interesting: bool) {}

    fn outside_determinism(&self) -> u64 {
        u64::from(self.calls >= self.after)
    }
}

/// FZ-REPLAY-WHOLE fix round S-C: a proposer's run outside the contract (the solve proposer's
/// symbolic run a clock or a stack stop ended) decides the case it proposes, so the first case
/// a re-run may differ at is that case, even when no case run is outside the contract. (A real
/// solve run is stopped only by the clock, a cancellation or a stack stop, which no test can
/// provoke at a chosen run; the loop reads the count every proposer reports.)
#[test]
fn a_proposer_run_outside_the_contract_sets_the_first_case_a_re_run_may_differ_at() {
    let mut runner = Scripted::new(|_| run(OutcomeClass::Miss, 1), |_| unreachable!());
    let mut schedule = Schedule::new(
        1,
        Vec::new(),
        vec![(
            1,
            Box::new(OutsideAfter { calls: 0, after: 3 }) as Box<dyn Proposer>,
        )],
    );
    let report = run_loop(
        &mut runner,
        &mut schedule,
        &settings(1),
        Budget::Cases(5),
        None,
    );
    assert_eq!(report.totals.outside_determinism, 0);
    assert_eq!(report.totals.first_outside_determinism, Some(2));
    let statement = &report.no_witness().expect("no witness").statement;
    assert!(
        statement.contains("reproduces this report only up to case 2"),
        "{statement}"
    );
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
    // FZ-REPLAY-WHOLE S3: the case a re-run may first differ at (the value 2 is case 1).
    assert_eq!(report.totals.first_outside_determinism, Some(1));
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
    // The hole's least value first (FZ-POLISH N-T2), then its tree.
    assert_eq!(
        seen[..4],
        [
            vec![int(0), int(7)],
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

/// A hole the hit does not need ends at its least value at once, its tree unused, and a hole
/// with a tree is moved again after another hole shrank (FZ-POLISH N-T2): the first hole hits
/// only at or above the second, so it cannot leave 40 while the second is 40.
#[test]
fn shrinking_tries_the_least_value_first_and_revisits_holes_with_trees() {
    let tree = |values: Vec<i64>| -> Option<Box<dyn ValueShrinker>> {
        Some(Box::new(Steps { values, at: 0 }))
    };
    let mut seen = Vec::new();
    let shrunk = shrink(
        &[int(64), int(40), int(9)],
        vec![tree(vec![64, 32, 16]), tree(vec![40, 20]), tree(vec![9, 5])],
        &[
            Constraints::default(),
            Constraints::default(),
            Constraints::default(),
        ],
        &mut |values| {
            seen.push(values.to_vec());
            if as_int(&values[0]) >= as_int(&values[1]) {
                Verdict::Hit
            } else {
                Verdict::Miss
            }
        },
    );
    assert_eq!(shrunk, [int(0), int(0), int(0)]);
    // The first hole's least value and tree miss; the second and third holes' least values hit
    // at once (their trees unused); a later pass moves the first hole to 0.
    assert_eq!(
        seen[..5],
        [
            vec![int(0), int(40), int(9)],
            vec![int(32), int(40), int(9)],
            vec![int(64), int(0), int(9)],
            vec![int(64), int(0), int(0)],
            vec![int(0), int(0), int(0)],
        ]
    );
}

#[test]
fn the_coverage_feedback_finds_new_rules_only_in_misses() {
    let observation = |class, applied: &[&str]| Observation {
        case: 0,
        class,
        applied: applied.iter().map(|rule| (*rule).to_owned()).collect(),
        matched: Vec::new(),
        applied_counts: std::collections::BTreeMap::new(),
        work: 1,
        score: None,
        reads: Vec::new(),
        blocked: None,
        comparisons: Vec::new(),
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
            .contains(&"every-baseline-end-data".to_owned())
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
    mixed.first_outside_determinism = Some(6);
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
        // FZ-REPLAY-WHOLE S3: what that means for a re-run.
        "such a case may end otherwise on another run",
        "reproduces this report only up to case 6, the first case outside the contract or \
         proposed after such a solve run, and may differ from it on",
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
        failure: Some(CaseFailure::new(
            "refused",
            cause,
            crate::report::CrashStage::Execute,
        )),
        run_facts_off_leaves: false,
        hooks: crate::exec::RunHooks::default(),
    };
    assert!(super::live::refused(&result(FailureCause::StateRefused)));
    assert!(!super::live::refused(&result(FailureCause::Other)));
}

// ---------------------------------------------------------------------------------------------
// Scores and the climb's share of the budget (FZ-12)

/// Every observation's class and score, as a [`Sharing`] proposer records them.
type Seen = std::rc::Rc<std::cell::RefCell<Vec<(OutcomeClass, Option<crate::score::Score>)>>>;

/// A proposer of one hole that is ready only from its `ready_after`-th observed case on, spends
/// at most `share` of the budget, and records every observation's class and score.
struct Sharing {
    kind: ProposerKind,
    share: Option<(u32, u32)>,
    ready_after: u64,
    seen: Seen,
}

impl Proposer for Sharing {
    fn kind(&self) -> ProposerKind {
        self.kind
    }

    fn propose(&mut self, _context: &mut ProposalContext<'_>) -> Option<Proposal> {
        Some(Proposal::plain(Origin::Scheduled(self.kind), vec![int(7)]))
    }

    fn observe(&mut self, _proposal: &Proposal, _observation: &Observation, _interesting: bool) {}

    fn observe_all(&mut self, _proposal: &Proposal, observation: &Observation) {
        self.seen
            .borrow_mut()
            .push((observation.class, observation.score.clone()));
    }

    fn ready(&self) -> bool {
        u64::try_from(self.seen.borrow().len()).expect("a count") >= self.ready_after
    }

    fn budget_share(&self) -> Option<(u32, u32)> {
        self.share
    }
}

/// The observation of a `miss` case of `work`.
fn observed(work: u64) -> Observation {
    Observation {
        case: 0,
        class: OutcomeClass::Miss,
        applied: Vec::new(),
        matched: Vec::new(),
        applied_counts: std::collections::BTreeMap::new(),
        work,
        score: None,
        reads: Vec::new(),
        blocked: None,
        comparisons: Vec::new(),
    }
}

#[test]
fn a_shared_proposer_spends_at_most_its_share_of_cases_and_work_over_every_prefix() {
    for (climb_work, blind_work) in [(1, 1), (10, 1), (1, 10)] {
        let seen = std::rc::Rc::default();
        let mut schedule = Schedule::new(
            11,
            vec![vec![int(0)]],
            vec![
                (1, Counter::boxed(ProposerKind::Blind, 0, 1)),
                (
                    50,
                    Box::new(Sharing {
                        kind: ProposerKind::Climb,
                        share: Some((1, 2)),
                        ready_after: 0,
                        seen: std::rc::Rc::clone(&seen),
                    }),
                ),
            ],
        );
        let (mut cases, mut work, mut climb_cases, mut climb_work_total) = (0u64, 0u64, 0u64, 0u64);
        for _ in 0..300 {
            let proposal = schedule.next().expect("blind never runs out");
            let climbing = proposal.origin == Origin::Scheduled(ProposerKind::Climb);
            // The climb is drawn only while its share, counting this case, holds.
            if climbing {
                assert!(
                    2 * (climb_cases + 1) <= cases + 1,
                    "cases {climb_cases}/{cases}"
                );
                assert!(
                    2 * climb_work_total <= work,
                    "work {climb_work_total}/{work}"
                );
            }
            let case_work = if climbing { climb_work } else { blind_work };
            cases += 1;
            work += case_work;
            if climbing {
                climb_cases += 1;
                climb_work_total += case_work;
            }
            schedule.observe(&proposal, &observed(case_work), false);
        }
        // At weight 50:1 the share, not the weight, bounds the climb: it takes about half of the
        // cases (or of the work when its cases cost more).
        assert!(climb_cases > 0);
        assert!(2 * climb_cases <= cases);
        assert!(2 * climb_work_total <= work + climb_work);
        if climb_work == blind_work {
            assert!(climb_cases >= 140, "{climb_cases} of {cases}");
        }
    }
}

#[test]
fn guided_proposers_together_spend_at_most_half_of_the_cases_and_work_over_every_prefix() {
    // Blind 1, climb 4, corpus 4: each guided proposer alone keeps within half, but without a
    // joint bound the two together would take about 8 cases in 9.
    for (guided_work, blind_work) in [(1, 1), (7, 1), (1, 7)] {
        let sharing = |kind| -> Box<dyn Proposer> {
            Box::new(Sharing {
                kind,
                share: Some((1, 2)),
                ready_after: 0,
                seen: std::rc::Rc::default(),
            })
        };
        let mut schedule = Schedule::new(
            12,
            vec![vec![int(0)]],
            vec![
                (1, Counter::boxed(ProposerKind::Blind, 0, 1)),
                (4, sharing(ProposerKind::Climb)),
                (4, sharing(ProposerKind::Corpus)),
            ],
        );
        let (mut cases, mut work, mut guided_cases, mut guided_total) = (0u64, 0u64, 0u64, 0u64);
        let mut kinds = std::collections::BTreeSet::new();
        for _ in 0..400 {
            let proposal = schedule.next().expect("blind never runs out");
            let guided = proposal.origin != Origin::Scheduled(ProposerKind::Blind)
                && proposal.origin != Origin::Explicit;
            if guided {
                kinds.insert(proposal.origin);
                assert!(
                    2 * (guided_cases + 1) <= cases + 1,
                    "cases {guided_cases}/{cases}"
                );
                assert!(2 * guided_total <= work, "work {guided_total}/{work}");
            }
            let case_work = if guided { guided_work } else { blind_work };
            cases += 1;
            work += case_work;
            if guided {
                guided_cases += 1;
                guided_total += case_work;
            }
            schedule.observe(&proposal, &observed(case_work), false);
        }
        assert_eq!(kinds.len(), 2, "both guided proposers ran");
        if guided_work == blind_work {
            assert!(guided_cases >= 190, "{guided_cases} of {cases}");
        }
    }
}

/// A guided proposer of share 1/4 that, like the solve proposer, spends work outside cases: every
/// other call it charges `extra` work and answers no proposal (it may propose later), and the
/// call after that proposes a case.
struct Solving {
    extra: u64,
    pending: u64,
    calls: u64,
    charged: std::rc::Rc<std::cell::Cell<u64>>,
}

impl Proposer for Solving {
    fn kind(&self) -> ProposerKind {
        ProposerKind::Solve
    }

    fn propose(&mut self, _context: &mut ProposalContext<'_>) -> Option<Proposal> {
        self.calls += 1;
        if self.calls % 2 == 1 {
            self.pending = self.extra;
            None
        } else {
            Some(Proposal::plain(
                Origin::Scheduled(ProposerKind::Solve),
                vec![int(9)],
            ))
        }
    }

    fn observe(&mut self, _proposal: &Proposal, _observation: &Observation, _interesting: bool) {}

    fn budget_share(&self) -> Option<(u32, u32)> {
        Some((1, 4))
    }

    fn may_propose_later(&self) -> bool {
        true
    }

    fn take_extra_work(&mut self) -> u64 {
        let extra = std::mem::take(&mut self.pending);
        self.charged.set(self.charged.get() + extra);
        extra
    }
}

#[test]
fn the_joint_share_counts_the_solve_proposers_share_and_its_work_outside_cases() {
    // Blind 1, climb 4, solve 4, the solve proposer's failed runs charging 40 work each. Over
    // every prefix the guided proposers together stay within half of the cases and of the work,
    // the solve proposer's runs included, also when the climb is drawn right after a run that
    // gave no case; and the solve proposer within its own quarter.
    let charged = std::rc::Rc::new(std::cell::Cell::new(0));
    let mut schedule = Schedule::new(
        21,
        Vec::new(),
        vec![
            (1, Counter::boxed(ProposerKind::Blind, 0, 1)),
            (
                4,
                Box::new(Sharing {
                    kind: ProposerKind::Climb,
                    share: Some((1, 2)),
                    ready_after: 0,
                    seen: std::rc::Rc::default(),
                }),
            ),
            (
                4,
                Box::new(Solving {
                    extra: 40,
                    pending: 0,
                    calls: 0,
                    charged: std::rc::Rc::clone(&charged),
                }),
            ),
        ],
    );
    let (mut cases, mut case_work) = (0u64, 0u64);
    let (mut guided_cases, mut guided_case_work, mut solve_cases) = (0u64, 0u64, 0u64);
    let mut kinds = std::collections::BTreeSet::new();
    for _ in 0..600 {
        let proposal = schedule.next().expect("blind never runs out");
        // A call that proposes charges nothing, so every run charged so far preceded this draw.
        let (work, guided_work) = (case_work + charged.get(), guided_case_work + charged.get());
        let guided = proposal.origin != Origin::Scheduled(ProposerKind::Blind);
        if guided {
            kinds.insert(proposal.origin);
            assert!(
                2 * (guided_cases + 1) <= cases + 1,
                "cases {guided_cases}/{cases}"
            );
            assert!(2 * guided_work <= work, "work {guided_work}/{work}");
        }
        if proposal.origin == Origin::Scheduled(ProposerKind::Solve) {
            assert!(
                4 * (solve_cases + 1) <= cases + 1,
                "solve {solve_cases}/{cases}"
            );
            solve_cases += 1;
        }
        cases += 1;
        case_work += 1;
        if guided {
            guided_cases += 1;
            guided_case_work += 1;
        }
        schedule.observe(&proposal, &observed(1), false);
    }
    assert_eq!(kinds.len(), 2, "both guided proposers ran");
    assert!(charged.get() > 0, "the solve proposer charged work");
}

#[test]
fn a_proposer_that_is_not_ready_waits_without_leaving_the_schedule() {
    let seen = std::rc::Rc::default();
    let mut schedule = Schedule::new(
        5,
        Vec::new(),
        vec![
            (1, Counter::boxed(ProposerKind::Blind, 0, 1)),
            (
                1000,
                Box::new(Sharing {
                    kind: ProposerKind::Climb,
                    share: None,
                    ready_after: 3,
                    seen: std::rc::Rc::clone(&seen),
                }),
            ),
        ],
    );
    let mut origins = Vec::new();
    for _ in 0..6 {
        let proposal = schedule.next().expect("a proposal");
        origins.push(proposal.origin);
        schedule.observe(&proposal, &observed(1), false);
    }
    let blind = Origin::Scheduled(ProposerKind::Blind);
    assert_eq!(origins[..3], [blind, blind, blind]);
    assert!(origins[3..].contains(&Origin::Scheduled(ProposerKind::Climb)));
}

#[test]
fn only_miss_cases_are_scored() {
    use crate::score::{Guard, Level, RuleScorer, Scorer};
    let classes = [
        OutcomeClass::Miss,
        OutcomeClass::Stuck,
        OutcomeClass::DepthBound,
        OutcomeClass::Unsupported,
        OutcomeClass::Rejected,
        OutcomeClass::Miss,
    ];
    let mut index = 0;
    let mut runner = Scripted::new(
        move |_| {
            let class = classes[index % classes.len()];
            index += 1;
            CaseRun {
                // Every case reports the target's condition entered, so any scored case has a
                // score at level 0: the loop alone decides which are scored.
                matched: vec!["t".to_owned()],
                rejection: (class == OutcomeClass::Rejected).then_some(RejectionReason::Constraint),
                ..run(class, 1)
            }
        },
        |_| unreachable!(),
    );
    let seen = std::rc::Rc::default();
    let mut schedule = Schedule::new(
        2,
        Vec::new(),
        vec![(
            1,
            Box::new(Sharing {
                kind: ProposerKind::Blind,
                share: None,
                ready_after: 0,
                seen: std::rc::Rc::clone(&seen),
            }) as Box<dyn Proposer>,
        )],
    );
    let mut settings = settings(1);
    settings.scorer = Some(Scorer::Rule(RuleScorer::from_parts("t", &[("t", 0)], &[])));
    let report = run_loop(
        &mut runner,
        &mut schedule,
        &settings,
        Budget::Cases(6),
        None,
    );
    assert_eq!(report.totals.cases, 6);
    let seen = seen.borrow();
    assert_eq!(seen.len(), 6);
    for (class, score) in seen.iter() {
        if *class == OutcomeClass::Miss {
            assert_eq!(
                score.as_ref().map(|score| (&score.level, &score.guard)),
                Some((&Level::At(0), &Guard::Unknown)),
            );
        } else {
            assert_eq!(*score, None, "{class:?}");
        }
    }
    // Without a scorer nothing is scored.
    let mut runner = Scripted::new(|_| run(OutcomeClass::Miss, 1), |_| unreachable!());
    let seen = std::rc::Rc::default();
    let mut schedule = Schedule::new(
        2,
        Vec::new(),
        vec![(
            1,
            Box::new(Sharing {
                kind: ProposerKind::Blind,
                share: None,
                ready_after: 0,
                seen: std::rc::Rc::clone(&seen),
            }) as Box<dyn Proposer>,
        )],
    );
    run_loop(
        &mut runner,
        &mut schedule,
        &self::settings(1),
        Budget::Cases(3),
        None,
    );
    assert!(seen.borrow().iter().all(|(_, score)| score.is_none()));
}

/// A proposer that delegates to `inner` and counts the cases and work of its own proposals.
struct Counted {
    inner: Box<dyn Proposer>,
    tally: std::rc::Rc<std::cell::Cell<(u64, u64)>>,
}

impl Proposer for Counted {
    fn kind(&self) -> ProposerKind {
        self.inner.kind()
    }

    fn propose(&mut self, context: &mut ProposalContext<'_>) -> Option<Proposal> {
        self.inner.propose(context)
    }

    fn observe(&mut self, proposal: &Proposal, observation: &Observation, interesting: bool) {
        let (cases, work) = self.tally.get();
        self.tally.set((cases + 1, work + observation.work.max(1)));
        self.inner.observe(proposal, observation, interesting);
    }

    fn observe_all(&mut self, proposal: &Proposal, observation: &Observation) {
        self.inner.observe_all(proposal, observation);
    }

    fn ready(&self) -> bool {
        self.inner.ready()
    }

    fn budget_share(&self) -> Option<(u32, u32)> {
        self.inner.budget_share()
    }
}

/// The climb proposer itself, weighted far above blind sampling and climbing a scripted score,
/// spends at most half of the cases over the campaign, and at most half of the work plus its
/// last case's work, whatever the cases cost (cheap blind cases, expensive climb cases).
#[test]
fn the_climb_spends_at_most_half_of_the_cases_and_of_the_work() {
    use crate::{
        proposers::climb::{ClimbHole, ClimbProposer},
        score::{Distance, GuardEntry, RuleScorer, Scorer},
        values::{Generator, ValueSort},
    };
    let bounds = GenerationBounds {
        int_bits: 16,
        length: 4,
        depth: 2,
    };
    for (climb_cost, budget) in [(1u64, 400u64), (9, 400), (40, 120)] {
        let hole = ClimbHole {
            sort: ValueSort::Int,
            constraints: Constraints::default(),
            generator: Generator::new(&ValueSort::Int, &Constraints::default(), &bounds)
                .expect("a generator"),
        };
        let tally = std::rc::Rc::new(std::cell::Cell::new((0, 0)));
        let climb = Counted {
            inner: Box::new(ClimbProposer::new(vec![hole], bounds, 7)),
            tally: std::rc::Rc::clone(&tally),
        };
        // The Counter proposes 0, 1, 2, ...; the climb moves from the best of them. A value
        // the counter never proposes (negative, or far) is a climb case: it costs more.
        let mut runner = Scripted::new(
            move |values| {
                let x = as_int(&values[0]);
                let mut guards = crate::score::Guards::new();
                guards.insert(
                    "t".to_owned(),
                    vec![GuardEntry {
                        distance: Some(Distance::normalized(
                            u32::try_from((x - 30_000).unsigned_abs())
                                .unwrap_or(u32::MAX)
                                .into(),
                        )),
                        refuted: true,
                        reads: Vec::new(),
                        guard_values: Vec::new(),
                    }],
                );
                let work = if (0..=10_000).contains(&x) {
                    1
                } else {
                    climb_cost
                };
                CaseRun {
                    matched: vec!["t".to_owned()],
                    guards,
                    ..run(OutcomeClass::Miss, work)
                }
            },
            |_| unreachable!(),
        );
        let mut schedule = Schedule::new(
            4,
            vec![vec![int(5)]],
            vec![
                (1, Counter::boxed(ProposerKind::Blind, 0, 1)),
                (50, Box::new(climb)),
            ],
        );
        let mut settings = settings(1);
        settings.scorer = Some(Scorer::Rule(RuleScorer::from_parts("t", &[("t", 0)], &[])));
        let report = run_loop(
            &mut runner,
            &mut schedule,
            &settings,
            Budget::Cases(budget),
            None,
        );
        let (climb_cases, climb_work) = tally.get();
        let (cases, work) = (report.totals.cases, report.totals.work);
        assert!(climb_cases > 0, "the climb ran");
        assert!(2 * climb_cases <= cases, "cases {climb_cases}/{cases}");
        assert!(
            2 * climb_work <= work + climb_cost,
            "work {climb_work}/{work} (cost {climb_cost})"
        );
    }
}

// ---------------------------------------------------------------------------------------------
// Incidental findings (FZ-INCIDENTAL)

/// A case of `class` whose runner describes it as an incidental finding at `head`.
fn incidental(values: &[Value], class: OutcomeClass, head: &str) -> CaseRun {
    CaseRun {
        incidental: Some((
            class,
            Box::new(crate::report::IncidentalCase {
                case: 0,
                holes: detail(values, head).holes,
                leaves: 1,
                leaf: 0,
                steps: 4,
                k_heads: vec![head.to_owned()],
                configuration: format!("config-{head}"),
                krun_command: Some(format!("krust krun {values:?}")),
                baseline_run: false,
            }),
        )),
        ..run(class, 10)
    }
}

#[test]
fn the_first_stuck_and_the_first_undefined_case_are_kept_and_nothing_else_moves() {
    // Values 1, 2, …: 2 and 5 get stuck, 3 and 6 take an undefined step, 4 is stuck outside the
    // determinism contract (so its runner describes no finding), the rest miss.
    let script = |values: &[Value]| match as_int(&values[0]) {
        2 | 5 => incidental(values, OutcomeClass::Stuck, "stop"),
        3 | 6 => incidental(values, OutcomeClass::Undefined, "undef"),
        4 => CaseRun {
            outside_determinism: true,
            ..run(OutcomeClass::Stuck, 10)
        },
        _ => run(OutcomeClass::Miss, 10),
    };
    let mut runner = Scripted::new(script, |_| Ok(run(OutcomeClass::Miss, 7)));
    let report = run_loop(
        &mut runner,
        &mut counter_schedule(1, 1),
        &settings(1),
        Budget::Cases(8),
        None,
    );
    // The runner is told once per class, so it describes no later case of it.
    assert_eq!(
        runner.kept,
        vec![OutcomeClass::Stuck, OutcomeClass::Undefined]
    );
    let stuck = report.incidental.stuck.as_ref().expect("a stuck finding");
    assert_eq!((stuck.case, stuck.holes[0].value.clone()), (1, int(2)));
    assert_eq!(stuck.k_heads, vec!["stop".to_owned()]);
    let undefined = report
        .incidental
        .undefined
        .as_ref()
        .expect("an undefined finding");
    assert_eq!(
        (undefined.case, undefined.holes[0].value.clone()),
        (2, int(3))
    );
    // The classes, counts and case sequence are a run's without findings.
    let mut plain = Scripted::new(
        move |values: &[Value]| CaseRun {
            incidental: None,
            ..script(values)
        },
        |_| Ok(run(OutcomeClass::Miss, 7)),
    );
    let without = run_loop(
        &mut plain,
        &mut counter_schedule(1, 1),
        &settings(1),
        Budget::Cases(8),
        None,
    );
    assert!(without.incidental.is_empty());
    assert_eq!(report.totals, without.totals);
    assert_eq!(report.outcome, without.outcome);
    // The summary words each finding as information, in one line.
    let lines = report.incidental.lines();
    assert_eq!(lines.len(), 2);
    assert!(lines.iter().all(|line| !line.contains('\n')
        && line.starts_with("incidental (information, not a failure): case ")));
    assert!(
        lines[0].contains(
            "case 1 (H0 = Int(2)) got stuck before a natural end after 4 steps at `stop`"
        ),
        "{}",
        lines[0]
    );
    assert!(lines[1].contains("took an undefined step"), "{}", lines[1]);
}

#[test]
fn a_finding_outside_the_determinism_contract_leaves_the_class_open() {
    // The only stuck case is outside the contract and its runner describes no finding: no
    // finding, though the class is counted.
    let mut runner = Scripted::new(
        |_| CaseRun {
            outside_determinism: true,
            ..run(OutcomeClass::Stuck, 10)
        },
        |_| Ok(run(OutcomeClass::Miss, 7)),
    );
    let report = run_loop(
        &mut runner,
        &mut counter_schedule(1, 1),
        &settings(1),
        Budget::Cases(2),
        None,
    );
    assert_eq!(classes(&report), vec![(OutcomeClass::Stuck, 2)]);
    assert!(report.incidental.is_empty());
    assert!(!report.to_canonical_json().contains("\"incidental\""));
}

#[test]
fn the_loop_keeps_the_finding_the_runner_gives_whatever_the_cases_determinism() {
    // A differential case whose mutant run broke the determinism contract while its baseline's
    // did not: the case is outside the contract, and the runner describes the baseline's
    // finding, which reproduces; the loop keeps it.
    let mut runner = Scripted::new(
        |values| CaseRun {
            outside_determinism: true,
            ..incidental(values, OutcomeClass::Stuck, "stop")
        },
        |_| Ok(run(OutcomeClass::Miss, 7)),
    );
    let report = run_loop(
        &mut runner,
        &mut counter_schedule(1, 1),
        &settings(1),
        Budget::Cases(2),
        None,
    );
    assert_eq!(report.totals.outside_determinism, 2);
    assert_eq!(
        report.incidental.stuck.as_ref().map(|found| found.case),
        Some(0)
    );
}

#[test]
fn a_witness_report_keeps_the_findings_before_it() {
    let mut runner = Scripted::new(
        |values| match as_int(&values[0]) {
            1 => incidental(values, OutcomeClass::Undefined, "undef"),
            2 => hit(values, 10, "end-2"),
            _ => run(OutcomeClass::Miss, 10),
        },
        |values| Ok(hit(values, 7, "end-2")),
    );
    let report = run_loop(
        &mut runner,
        &mut counter_schedule(1, 1),
        &settings(1),
        Budget::Cases(8),
        None,
    );
    assert!(report.witness().is_some());
    assert_eq!(
        report.incidental.undefined.as_ref().map(|found| found.case),
        Some(0)
    );
    let read = FuzzReport::from_json(&report.to_canonical_json()).expect("reads back");
    assert_eq!(read, report);
}

#[test]
fn an_incidental_line_counts_steps_holes_paths_and_threads() {
    let mut case = crate::report::IncidentalCase {
        case: 0,
        holes: Vec::new(),
        leaves: 1,
        leaf: 0,
        steps: 1,
        k_heads: vec!["join 0 ;".into(), "10 / 0".into()],
        configuration: String::new(),
        krun_command: None,
        baseline_run: false,
    };
    let lines = |case: &crate::report::IncidentalCase, stuck: bool| {
        let incidentals = crate::report::Incidentals {
            stuck: stuck.then(|| case.clone()),
            undefined: (!stuck).then(|| case.clone()),
        };
        incidentals.lines().remove(0)
    };
    // No holes: no empty list; one step; every thread's head.
    assert!(
        lines(&case, true).starts_with(
            "incidental (information, not a failure): case 0 got stuck before a natural end after \
             1 step at `join 0 ;` | `10 / 0`;"
        ),
        "{}",
        lines(&case, true)
    );
    // An undefined step is the step after the leaf's depth; one path of several says so.
    case.leaves = 2;
    case.k_heads = vec!["a ( 0 )".into()];
    assert!(
        lines(&case, false).starts_with(
            "incidental (information, not a failure): case 0 on one of its 2 paths took an \
             undefined step at step 2 on `a ( 0 )`;"
        ),
        "{}",
        lines(&case, false)
    );
    // A differential baseline's run says it is that run, not the pair's class.
    case.baseline_run = true;
    assert!(
        lines(&case, false).starts_with(
            "incidental (information, not a failure): case 0, in the baseline's own run on all \
             paths (not the pair's class), on one of its 2 paths took an undefined step at step \
             2 on `a ( 0 )`;"
        ),
        "{}",
        lines(&case, false)
    );
    case.baseline_run = false;
    // At most four heads, then a count.
    case.k_heads = (0..6).map(|n| format!("t{n}")).collect();
    assert!(
        lines(&case, true).contains("at `t0` | `t1` | `t2` | `t3` and 2 more;"),
        "{}",
        lines(&case, true)
    );
}

/// The holes' finite domain (FZ-POLISH N-T1): choices, a Boolean and bounded integer ranges
/// multiply; an unbounded hole, another sort or a product above the cap has none.
#[test]
fn a_finite_domain_is_the_product_of_the_holes_finite_domains() {
    use super::campaign_loop::{FiniteDomain, MAX_EXHAUSTIVE};
    use crate::values::ValueSort;
    let range = |min: i64, max: i64| Constraints {
        range: Some(IntRange {
            min: Some(BigInt::from(min)),
            max: Some(BigInt::from(max)),
        }),
        ..Constraints::default()
    };
    let choices = Constraints {
        choices: Some(vec![int(1), int(2), int(1)]),
        ..Constraints::default()
    };
    let unbounded = Constraints::default();
    let size = |holes: &[(&ValueSort, &Constraints)]| {
        FiniteDomain::of(holes.iter().copied()).map(|domain| domain.size())
    };
    let small = range(-2, 2);
    assert_eq!(
        size(&[
            (&ValueSort::Int, &small),
            (&ValueSort::Bool, &unbounded),
            (&ValueSort::Int, &choices)
        ]),
        Some(5 * 2 * 2)
    );
    assert_eq!(
        size(&[(&ValueSort::MInt { width: 4 }, &unbounded)]),
        Some(16)
    );
    assert_eq!(size(&[(&ValueSort::Int, &unbounded)]), None);
    assert_eq!(size(&[(&ValueSort::String, &unbounded)]), None);
    let wide = range(1, i64::try_from(MAX_EXHAUSTIVE).expect("fits") + 1);
    assert_eq!(size(&[(&ValueSort::Int, &wide)]), None);
    assert_eq!(size(&[]), None);
    // The seeded walk visits every assignment once, and the same seed gives the same walk.
    let domain = FiniteDomain::of([(&ValueSort::Int, &small), (&ValueSort::Bool, &unbounded)])
        .expect("finite");
    let order = domain.permutation(7);
    assert_eq!(order, domain.permutation(7));
    let mut sorted = order.clone();
    sorted.sort_unstable();
    assert_eq!(sorted, (0..10).collect::<Vec<u64>>());
    let assignments: std::collections::BTreeSet<Vec<Value>> = order
        .iter()
        .map(|index| domain.assignment(*index))
        .collect();
    assert_eq!(assignments.len(), 10);
    assert!(assignments.contains(&vec![int(-2), Value::Bool(true)]));
}

// ---------------------------------------------------------------------------------------------
// Crash findings (FZ-CRASH): a panic in the runner is a finding with its input, and the
// campaign goes on. These tests read the report as JSON, the form every client reads.

fn report_json(report: &FuzzReport) -> serde_json::Value {
    serde_json::from_str(&report.to_canonical_json()).expect("a report is JSON")
}

/// (B) A panic while the campaign's runner runs case 3 of 10 is one crash finding of the
/// engine, with the case's values; the case is `unsupported` with the reason `panic`, and the
/// other nine cases run.
#[test]
fn a_panicking_case_is_a_crash_finding_and_the_campaign_goes_on() {
    let mut runner = Scripted::new(
        |values| {
            assert!(as_int(&values[0]) != 4, "the scripted runner panics at 4");
            run(OutcomeClass::Miss, 1)
        },
        |_| Ok(run(OutcomeClass::Miss, 1)),
    );
    let report = run_loop(
        &mut runner,
        &mut counter_schedule(1, 1),
        &settings(1),
        Budget::Cases(10),
        None,
    );
    let json = report_json(&report);
    assert_eq!(json["totals"]["cases"], 10, "{}", json["totals"]);
    assert_eq!(json["totals"]["classes"]["unsupported"], 1);
    assert_eq!(json["totals"]["unsupported-reasons"]["panic"], 1);
    let crashes = json["crashes"].as_array().expect("a crashes list");
    assert_eq!(crashes.len(), 1, "{crashes:?}");
    let crash = &crashes[0];
    assert_eq!(crash["signature"]["kind"], "panic", "{crash}");
    assert_eq!(crash["signature"]["side"], "engine", "{crash}");
    assert_eq!(crash["phase"], "case", "{crash}");
    assert_eq!(crash["case"], 3, "{crash}");
    assert_eq!(crash["holes"][0]["value"]["int"], "4", "{crash}");
    assert!(
        crash["message"]
            .as_str()
            .is_some_and(|message| message.contains("panics at 4")),
        "{crash}"
    );
}

/// (B) A panic in a candidate's confirmation leaves the candidate unconfirmed, and is a crash
/// finding of phase `confirmation`.
#[test]
fn a_panicking_confirmation_leaves_the_candidate_unconfirmed() {
    let mut runner = Scripted::new(
        |values| {
            if as_int(&values[0]) == 3 {
                hit(values, 1, "end-3")
            } else {
                run(OutcomeClass::Miss, 1)
            }
        },
        |_| panic!("the scripted confirmation panics"),
    );
    let report = run_loop(
        &mut runner,
        &mut counter_schedule(1, 1),
        &settings(1),
        Budget::Cases(5),
        None,
    );
    let json = report_json(&report);
    assert_eq!(
        json["outcome"]["status"], "no-witness-found",
        "{}",
        json["outcome"]
    );
    assert_eq!(json["totals"]["unconfirmed"], 1, "{}", json["totals"]);
    assert_eq!(json["totals"]["cases"], 5, "{}", json["totals"]);
    let crashes = json["crashes"].as_array().expect("a crashes list");
    assert_eq!(crashes.len(), 1, "{crashes:?}");
    assert_eq!(crashes[0]["phase"], "confirmation", "{}", crashes[0]);
    assert_eq!(crashes[0]["case"], 2, "{}", crashes[0]);
    assert_eq!(
        crashes[0]["holes"][0]["value"]["int"], "3",
        "{}",
        crashes[0]
    );
}

/// (B) A panic while a shrink candidate is screened drops the candidate, and is a crash finding
/// of phase `shrink` with the candidate's values, not the witness's.
#[test]
fn a_panicking_shrink_candidate_is_dropped_and_recorded_with_its_values() {
    let mut runner = Scripted::new(
        |values| {
            let value = as_int(&values[0]);
            assert!(value != 0, "the scripted runner panics at 0");
            if value >= 10 {
                hit(values, 1, "end")
            } else {
                run(OutcomeClass::Miss, 1)
            }
        },
        |values| {
            if as_int(&values[0]) >= 10 {
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
    let json = report_json(&report);
    assert_eq!(
        json["outcome"]["status"], "witness-found",
        "{}",
        json["outcome"]
    );
    let shrunk = &json["outcome"]["witness"]["shrunk"];
    assert_eq!(shrunk["holes"][0]["value"]["int"], "10", "{shrunk}");
    let crashes = json["crashes"].as_array().expect("a crashes list");
    assert_eq!(crashes.len(), 1, "{crashes:?}");
    assert_eq!(crashes[0]["phase"], "shrink", "{}", crashes[0]);
    assert_eq!(crashes[0]["case"], 0, "{}", crashes[0]);
    assert_eq!(
        crashes[0]["holes"][0]["value"]["int"], "0",
        "{}",
        crashes[0]
    );
}

/// (Fix round, D3) A rebuild that fails after a hit's confirmation panicked keeps the crash that
/// made the rebuild necessary.
#[test]
fn a_failed_rebuild_after_a_panicking_confirmation_keeps_its_crash() {
    let mut runner = Scripted::new(
        |values| {
            if as_int(&values[0]) == 3 {
                hit(values, 1, "end-3")
            } else {
                run(OutcomeClass::Miss, 1)
            }
        },
        |_| panic!("the scripted confirmation panics"),
    );
    runner.recover_fails = true;
    let report = run_loop(
        &mut runner,
        &mut counter_schedule(1, 1),
        &settings(1),
        Budget::Cases(5),
        None,
    );
    let json = report_json(&report);
    assert_eq!(
        json["outcome"]["kind"], "rebuild-failed",
        "{}",
        json["outcome"]
    );
    let crashes = json["crashes"].as_array().expect("a crashes list");
    assert_eq!(crashes.len(), 1, "{crashes:?}");
    assert_eq!(crashes[0]["phase"], "confirmation", "{}", crashes[0]);
}

/// (Fix round, S2) A crash whose confirmation could not even build was not re-run: it is
/// neither reproduced nor unreproduced, and its determinism stays unknown.
#[test]
fn a_crash_whose_confirmation_did_not_build_has_no_reproduced() {
    let mut runner = Scripted::new(
        |values| {
            assert!(as_int(&values[0]) != 4, "the scripted runner panics at 4");
            run(OutcomeClass::Miss, 1)
        },
        |_| Err("the fresh backend did not build".into()),
    );
    let report = run_loop(
        &mut runner,
        &mut counter_schedule(1, 1),
        &settings(1),
        Budget::Cases(6),
        None,
    );
    let json = report_json(&report);
    let crash = &json["crashes"][0];
    assert_eq!(crash.get("reproduced"), None, "{crash}");
    assert_eq!(crash["determinism"], "unknown", "{crash}");
    assert_eq!(json["totals"]["outside-determinism"], 0);
}

/// (Fix round, S4) When the runner did not rebuild while a witness was shrunk, the witness's
/// comparable judgement, which no run made, says that a crash stopped it instead of being
/// absent, which reads as judged or not applicable.
#[test]
fn a_witness_whose_judgement_a_failed_rebuild_stopped_names_the_crash() {
    let mut runner = Scripted::new(
        |values| {
            let value = as_int(&values[0]);
            assert!(value != 0, "the scripted runner panics at 0");
            if value >= 10 {
                hit(values, 1, "end")
            } else {
                run(OutcomeClass::Miss, 1)
            }
        },
        |values| {
            if as_int(&values[0]) >= 10 {
                Ok(hit(values, 1, "end"))
            } else {
                Ok(run(OutcomeClass::Miss, 1))
            }
        },
    );
    runner.recover_fails = true;
    runner.judgement_work = Some(5);
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
    let json = report_json(&report);
    let first = &json["outcome"]["witness"]["first"];
    assert_eq!(
        first["comparable"],
        serde_json::json!({"holds": false, "reasons": ["crash"]}),
        "{first}"
    );
}

/// Panics at one location, so that two closures share one crash signature.
fn shared_panic() -> ! {
    panic!("the shared location panics")
}

/// (Fix round, minor) A signature first kept from a confirmation is taken over by the first
/// case that crashes with it: the finding then names that case's values and is examined as a
/// case's crash.
#[test]
fn a_case_takes_over_a_signature_first_seen_in_a_confirmation() {
    let mut runner = Scripted::new(
        |values| {
            let value = as_int(&values[0]);
            if value == 5 {
                shared_panic();
            }
            if value == 3 {
                hit(values, 1, "end-3")
            } else {
                run(OutcomeClass::Miss, 1)
            }
        },
        |_| shared_panic(),
    );
    let report = run_loop(
        &mut runner,
        &mut counter_schedule(1, 1),
        &settings(1),
        Budget::Cases(6),
        None,
    );
    let json = report_json(&report);
    let crashes = json["crashes"].as_array().expect("a crashes list");
    assert_eq!(crashes.len(), 1, "{crashes:?}");
    let crash = &crashes[0];
    assert_eq!(crash["phase"], "case", "{crash}");
    assert_eq!(crash["case"], 4, "{crash}");
    assert_eq!(crash["holes"][0]["value"]["int"], "5", "{crash}");
    assert_eq!(crash["count"], 1, "{crash}");
    assert_eq!(crash["reproduced"], true, "{crash}");
}

/// (Fix round, minor) The engine defects and warnings of a crash's shrink candidates are
/// recorded, as a hit's are.
#[test]
fn a_crash_shrink_candidates_notes_are_recorded() {
    let crashed = |_: &[Value]| CaseRun {
        crash: Some(Box::new(super::runner::CaseCrash::engine(
            "scripted".into(),
            Some("k-rust/src/a.rs:1:1".into()),
            false,
        ))),
        defects: vec!["a scripted self-check defect".into()],
        unjudged: Some(crate::exec::UnjudgedReason::Panic),
        ..run(OutcomeClass::Unsupported, 1)
    };
    let mut runner = Scripted::new(
        move |values| {
            if as_int(&values[0]) >= 5 {
                crashed(values)
            } else {
                run(OutcomeClass::Miss, 1)
            }
        },
        move |values| Ok(crashed(values)),
    );
    let mut schedule = Schedule::new(
        1,
        Vec::new(),
        vec![(1, Counter::boxed(ProposerKind::Blind, 40, 0))],
    );
    let report = run_loop(
        &mut runner,
        &mut schedule,
        &settings(1),
        Budget::Cases(1),
        None,
    );
    assert_eq!(report.crashes.0.len(), 1);
    assert!(
        report
            .engine_defects
            .iter()
            .any(|defect| defect.description.starts_with("crash shrink candidate")),
        "{:?}",
        report.engine_defects
    );
}

/// (Fix round, D2) A client's observer that panics while a confirmed witness is shrunk aborts
/// the campaign with the candidate's values, since the observer cannot be trusted after its
/// panic; a warning keeps the confirmed witness's values.
#[test]
fn an_observer_panic_while_a_witness_shrinks_aborts_and_names_the_witness() {
    let mut runner = Scripted::new(
        |values| {
            if as_int(&values[0]) >= 10 {
                hit(values, 1, "end")
            } else {
                run(OutcomeClass::Miss, 1)
            }
        },
        |values| Ok(hit(values, 1, "end")),
    );
    runner.abort_at = Some(1);
    runner.abort_kind = crate::report::AbortKind::ClientPanic;
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
    let json = report_json(&report);
    let outcome = &json["outcome"];
    assert_eq!(outcome["status"], "aborted", "{outcome}");
    assert_eq!(outcome["kind"], "client-panic", "{outcome}");
    assert_eq!(outcome["holes"][0]["value"]["int"], "0", "{outcome}");
    assert!(
        report
            .warnings
            .iter()
            .any(|warning| warning.contains("confirmed witness") && warning.contains("100")),
        "{:?}",
        report.warnings
    );
}

// ---------------------------------------------------------------------------------------------
// The witness filter (FZ-COMPARABLE-B)

type JudgeScript = Box<dyn FnMut(&crate::report::WitnessCase) -> Option<FilterRefusal>>;
type RepairScript = Box<dyn FnMut(&[Value]) -> Vec<Vec<Value>>>;

/// A witness filter whose verdicts and repair candidates follow closures, recording the hole
/// values of every case it judged and every repair it was asked for.
struct Judging {
    refuse: JudgeScript,
    repair: RepairScript,
    judged: Vec<Vec<Value>>,
    repairs: Vec<Vec<Value>>,
}

impl Judging {
    fn new(
        refuse: impl FnMut(&crate::report::WitnessCase) -> Option<FilterRefusal> + 'static,
    ) -> Self {
        Self {
            refuse: Box::new(refuse),
            repair: Box::new(|_| Vec::new()),
            judged: Vec::new(),
            repairs: Vec::new(),
        }
    }

    /// Refuse every case whose first hole is below `bound`, for the cause `small`.
    fn below(bound: i64) -> Self {
        Self::new(move |case| (as_int(&case.holes[0].value) < bound).then(|| refusal("small")))
    }
}

impl WitnessFilter for Judging {
    fn id(&self) -> String {
        "test-filter/v1".into()
    }

    fn judge(&mut self, case: &crate::report::WitnessCase) -> Result<(), FilterRefusal> {
        self.judged
            .push(case.holes.iter().map(|hole| hole.value.clone()).collect());
        (self.refuse)(case).map_or(Ok(()), Err)
    }

    fn repair(
        &mut self,
        _case: &crate::report::WitnessCase,
        values: &[Value],
        _refusal: &FilterRefusal,
    ) -> Vec<Vec<Value>> {
        self.repairs.push(values.to_vec());
        (self.repair)(values)
    }
}

fn refusal(cause: &str) -> FilterRefusal {
    FilterRefusal {
        cause: cause.into(),
        detail: format!("{cause} detail"),
        remedy: Some(format!("avoid {cause}")),
    }
}

fn filtered(
    runner: &mut Scripted,
    schedule: &mut Schedule,
    settings: &LoopSettings,
    budget: Budget,
    filter: &mut Judging,
) -> FuzzReport {
    run_loop_filtered(runner, schedule, settings, budget, None, Some(filter))
}

fn ints(values: &[Vec<Value>]) -> Vec<Vec<i64>> {
    values
        .iter()
        .map(|values| values.iter().map(as_int).collect())
        .collect()
}

/// A refused hit is judged before its confirmation, so it costs no confirmation run, and is
/// counted `unsupported` (`client-refused`) under its cause; the search goes on, and a later hit
/// the filter accepts is the witness. Shrink candidates the filter refuses are dropped before
/// their confirmation.
#[test]
fn a_refused_hit_is_demoted_and_a_later_accepted_hit_is_the_witness() {
    let mut runner = Scripted::new(
        |values| {
            if as_int(&values[0]) >= 3 {
                hit(values, 10, "end")
            } else {
                run(OutcomeClass::Miss, 10)
            }
        },
        |values| Ok(hit(values, 7, "end")),
    );
    let mut filter = Judging::below(5);
    let report = filtered(
        &mut runner,
        &mut counter_schedule(1, 1),
        &settings(1),
        Budget::Cases(10),
        &mut filter,
    );
    let witness = report.witness().cloned().expect("a witness");
    assert_eq!(witness.first.holes[0].value, int(5));
    assert_eq!(witness.shrunk, None);
    assert_eq!(witness.repaired_from, None);
    // Cases 1, 2, 3, 4, 5, then shrink candidates 0, 2, 3, 4 (bisection between 0 and 5): only
    // the accepted case 5 is confirmed.
    assert_eq!(ints(&runner.confirmed), [[5]]);
    assert_eq!(report.totals.cases, 5);
    assert_eq!(
        report.totals.unsupported_reasons,
        BTreeMap::from([(crate::exec::UnjudgedReason::ClientRefused, 2)])
    );
    assert_eq!(
        report.totals.filter.refused,
        BTreeMap::from([("small".into(), 2)])
    );
    assert_eq!(report.totals.filter.refused_shrink_candidates, 2);
    assert_eq!(report.client_refusals.len(), 1);
    let refused = &report.client_refusals[0];
    assert_eq!(
        (refused.case, refused.count, refused.repaired),
        (2, 2, false)
    );
    assert_eq!(refused.holes[0].value, int(3));
    assert_eq!(refused.remedy.as_deref(), Some("avoid small"));
    assert_eq!(report.identity.filter.as_deref(), Some("test-filter/v1"));
    // 3 and 4 judged once each (refused), 5 before and after its confirmation, and the shrink
    // candidates that hit (3 and 4) once each.
    assert_eq!(ints(&filter.judged), [[3], [4], [5], [5], [3], [4]]);
}

/// The shrink screen keeps only candidates the filter accepts both before and after their
/// confirmation: the hit needs X >= 1, the filter refuses X < 3, so the witness shrinks to 3,
/// not to 1, and 2 is never confirmed.
#[test]
fn the_shrink_screen_keeps_only_candidates_the_filter_accepts() {
    let mut runner = Scripted::new(
        |values| {
            if as_int(&values[0]) >= 1 {
                hit(values, 1, "end")
            } else {
                run(OutcomeClass::Miss, 1)
            }
        },
        |values| Ok(hit(values, 1, "end")),
    );
    let mut filter = Judging::below(3);
    let mut schedule = Schedule::new(
        1,
        Vec::new(),
        vec![(1, Counter::boxed(ProposerKind::Blind, 10, 0))],
    );
    let report = filtered(
        &mut runner,
        &mut schedule,
        &settings(1),
        Budget::Cases(1),
        &mut filter,
    );
    let witness = report.witness().cloned().expect("a witness");
    assert_eq!(witness.first.holes[0].value, int(10));
    assert_eq!(
        witness.shrunk.expect("a shrunk witness").holes[0].value,
        int(3)
    );
    assert_eq!(ints(&runner.confirmed), [[10], [5], [3]]);
    // 2 in the first pass, then 1 and 2 again in the pass from 3; none is confirmed.
    assert_eq!(report.totals.filter.refused_shrink_candidates, 3);
    assert!(report.totals.filter.refused.is_empty());
}

/// A refused hit is repaired from the filter's candidates: each runs as a full case, charged as
/// extra work, and a candidate the filter refuses again is not taken; the first that hits, is
/// accepted, confirmed and accepted again is the witness's `first`, and the witness names the
/// refused case (`repaired-from`).
#[test]
fn a_refused_hit_is_repaired_from_the_filters_candidates() {
    let mut runner = Scripted::new(
        |values| hit(values, 10, "end"),
        |values| Ok(hit(values, 7, "end")),
    );
    runner.admissible = Box::new(|_, value| as_int(value) != 99);
    let mut filter = Judging::new(|case| {
        case.holes
            .iter()
            .any(|hole| as_int(&hole.value) < 0)
            .then(|| refusal("negative"))
    });
    filter.repair = Box::new(|values| {
        vec![
            // The refused case itself, and an inadmissible candidate, are never run.
            values.to_vec(),
            vec![int(99), int(99)],
            // Still negative: refused again.
            vec![int(-1), int(4)],
            vec![int(3), int(4)],
            vec![int(3), int(4)],
        ]
    });
    let mut schedule = Schedule::new(1, vec![vec![int(-3), int(4)]], Vec::new());
    let report = filtered(
        &mut runner,
        &mut schedule,
        &settings(2),
        Budget::Cases(1),
        &mut filter,
    );
    let witness = report.witness().cloned().expect("a repaired witness");
    assert_eq!(
        witness
            .first
            .holes
            .iter()
            .map(|hole| as_int(&hole.value))
            .collect::<Vec<_>>(),
        [3, 4]
    );
    let from = witness.repaired_from.expect("repaired-from");
    assert_eq!((from.case, from.cause.as_str()), (0, "negative"));
    assert_eq!(from.holes[0].value, int(-3));
    assert!(report.client_refusals[0].repaired);
    assert_eq!(report.totals.filter.repairs, 1);
    assert_eq!(report.totals.filter.repair_candidates, 2);
    // Two candidate runs (10 each) and one confirmation (7).
    assert_eq!(report.totals.filter.repair_work, 27);
    assert_eq!(report.totals.cases, 1);
    // The candidate refused again is never confirmed.
    assert_eq!(ints(&runner.confirmed)[0], [3, 4]);
    assert_eq!(ints(&filter.repairs), [[-3, 4]]);
}

/// Without shrinking the found case itself is the witness the caller asked for, so a refused hit
/// is not repaired.
#[test]
fn without_shrinking_a_refused_hit_is_not_repaired() {
    let mut runner = Scripted::new(
        |values| hit(values, 1, "end"),
        |values| Ok(hit(values, 1, "end")),
    );
    let mut filter = Judging::below(100);
    filter.repair = Box::new(|_| vec![vec![int(500)]]);
    let mut settings = settings(1);
    settings.options.shrink = false;
    let report = filtered(
        &mut runner,
        &mut counter_schedule(1, 1),
        &settings,
        Budget::Cases(3),
        &mut filter,
    );
    assert_eq!(report.witness(), None);
    assert!(filter.repairs.is_empty());
    assert_eq!(
        report.totals.filter.refused,
        BTreeMap::from([("small".into(), 3)])
    );
}

/// A cause whose repairs failed `MAX_FAILED_REPAIRS` times is repaired no more (review M7), and
/// a campaign whose every hit was refused says so in its statement and a warning, so that it
/// does not read as survival (review M5).
#[test]
fn a_cause_whose_repairs_failed_is_no_longer_repaired() {
    let mut runner = Scripted::new(
        |values| hit(values, 1, "end"),
        |values| Ok(hit(values, 1, "end")),
    );
    let mut filter = Judging::new(|_| Some(refusal("always")));
    filter.repair = Box::new(|values| vec![vec![int(as_int(&values[0]) + 1000)]]);
    let report = filtered(
        &mut runner,
        &mut counter_schedule(1, 1),
        &settings(1),
        Budget::Cases(10),
        &mut filter,
    );
    assert_eq!(report.witness(), None);
    let max = crate::filter::MAX_FAILED_REPAIRS;
    assert_eq!(filter.repairs.len(), usize::try_from(max).expect("small"));
    assert_eq!(report.totals.filter.repairs, max);
    assert_eq!(report.totals.filter.repair_candidates, max);
    assert_eq!(report.totals.filter.repairs_skipped, 10 - max);
    assert_eq!(
        report.totals.filter.refused,
        BTreeMap::from([("always".into(), 10)])
    );
    let statement = report.no_witness().cloned().expect("no witness").statement;
    assert!(
        statement.contains(
            "10 candidate hits were refused by the client's witness filter, so none is a witness \
             the client accepts (by cause: 10 always). For always: avoid always."
        ),
        "{statement}"
    );
    assert!(
        report
            .warnings
            .iter()
            .any(|warning| warning.starts_with("client-refused:")),
        "{:?}",
        report.warnings
    );
}

/// A panic of the filter aborts the campaign as a panicking observer does (`client-panic`),
/// naming the case and its values.
#[test]
fn a_panicking_filter_aborts_the_campaign_with_client_panic() {
    let mut runner = Scripted::new(
        |values| hit(values, 1, "end"),
        |values| Ok(hit(values, 1, "end")),
    );
    let mut filter = Judging::new(|_| panic!("the filter fails"));
    let report = filtered(
        &mut runner,
        &mut counter_schedule(1, 7),
        &settings(1),
        Budget::Cases(3),
        &mut filter,
    );
    let json = report_json(&report);
    let outcome = &json["outcome"];
    assert_eq!(outcome["status"], "aborted", "{outcome}");
    assert_eq!(outcome["kind"], "client-panic", "{outcome}");
    assert_eq!(outcome["holes"][0]["value"]["int"], "7", "{outcome}");
    assert!(
        outcome["reason"].as_str().unwrap().contains("phase filter"),
        "{outcome}"
    );
    assert!(runner.confirmed.is_empty());
}

/// A filter that judges two equal witness cases differently (here: it accepts a case once, then
/// refuses every case) breaks its contract: the campaign aborts with `client-defect` (review
/// M1).
#[test]
fn a_filter_that_judges_equal_cases_differently_is_a_client_defect() {
    let mut runner = Scripted::new(
        |values| hit(values, 1, "end"),
        |values| Ok(hit(values, 1, "end")),
    );
    let mut calls = 0;
    let mut filter = Judging::new(move |_| {
        calls += 1;
        (calls > 1).then(|| refusal("flaky"))
    });
    let report = filtered(
        &mut runner,
        &mut counter_schedule(1, 4),
        &settings(1),
        Budget::Cases(3),
        &mut filter,
    );
    let json = report_json(&report);
    assert_eq!(json["outcome"]["kind"], "client-defect", "{json}");
    assert_eq!(json["outcome"]["case"], 0, "{json}");
    assert!(
        json["outcome"]["reason"]
            .as_str()
            .unwrap()
            .contains("not a function of the case"),
        "{json}"
    );
}

/// A refusal whose cause is no cause token is client misuse: `client-defect` (review M1).
#[test]
fn a_malformed_cause_is_a_client_defect() {
    let mut runner = Scripted::new(
        |values| hit(values, 1, "end"),
        |values| Ok(hit(values, 1, "end")),
    );
    let mut filter = Judging::new(|_| Some(refusal("Not A Token")));
    let report = filtered(
        &mut runner,
        &mut counter_schedule(1, 4),
        &settings(1),
        Budget::Cases(3),
        &mut filter,
    );
    let json = report_json(&report);
    assert_eq!(json["outcome"]["kind"], "client-defect", "{json}");
    assert_eq!(report.totals.cases, 1);
}

/// When the confirmation's witness case differs from the case's in what the filter reads (here a
/// side's work) and the filter refuses it, the refusal wins and the difference is an engine
/// defect, not the client's (review M1).
#[test]
fn a_refused_confirmation_of_another_case_is_an_engine_defect_and_the_refusal_wins() {
    let mut runner = Scripted::new(
        |values| hit(values, 1, "end"),
        |values| {
            let mut confirmation = hit(values, 1, "end");
            if let Some(detail) = confirmation.hit.as_mut() {
                detail.sides[0].work = Some(2);
            }
            Ok(confirmation)
        },
    );
    let mut filter = Judging::new(|case| (case.sides[0].work == Some(2)).then(|| refusal("work")));
    let report = filtered(
        &mut runner,
        &mut counter_schedule(1, 4),
        &settings(1),
        Budget::Cases(1),
        &mut filter,
    );
    assert_eq!(report.witness(), None);
    assert_eq!(
        report.totals.filter.refused,
        BTreeMap::from([("work".into(), 1)])
    );
    assert_eq!(
        report.engine_defects.len(),
        1,
        "{:?}",
        report.engine_defects
    );
    assert!(
        report.engine_defects[0]
            .description
            .contains("the refusal wins"),
        "{:?}",
        report.engine_defects
    );
}

/// A filter that accepts every case gives the unfiltered report, byte for byte, apart from
/// `identity.filter` (review M8): the filter only removes candidates.
#[test]
fn an_accepting_filter_gives_the_unfiltered_report() {
    let script = || {
        Scripted::new(
            |values| {
                if as_int(&values[0]) >= 40 {
                    hit(values, 10, "end")
                } else {
                    run(OutcomeClass::Miss, 10)
                }
            },
            |values| Ok(hit(values, 5, "end")),
        )
    };
    let schedule = || {
        Schedule::new(
            1,
            Vec::new(),
            vec![(1, Counter::boxed(ProposerKind::Blind, 7, 13))],
        )
    };
    let unfiltered = run_loop(
        &mut script(),
        &mut schedule(),
        &settings(1),
        Budget::Cases(20),
        None,
    );
    let mut filter = Judging::new(|_| None);
    let mut accepted = filtered(
        &mut script(),
        &mut schedule(),
        &settings(1),
        Budget::Cases(20),
        &mut filter,
    );
    assert!(!filter.judged.is_empty());
    assert!(
        unfiltered
            .witness()
            .and_then(|w| w.shrunk.as_ref())
            .is_some()
    );
    assert_eq!(
        accepted.identity.filter.take().as_deref(),
        Some("test-filter/v1")
    );
    assert_eq!(accepted.to_canonical_json(), unfiltered.to_canonical_json());
}

/// `client-refusals[].repaired` marks the case that was repaired (review M1): the first refused
/// hit's repair misses, the second's hits, so the cause's entry (the first case) stays
/// unrepaired, and `repaired-from` names the second.
#[test]
fn the_refusal_entry_marks_only_the_case_that_was_repaired() {
    let mut runner = Scripted::new(
        |values| {
            if as_int(&values[0]) == 1000 {
                run(OutcomeClass::Miss, 1)
            } else {
                hit(values, 1, "end")
            }
        },
        |values| Ok(hit(values, 1, "end")),
    );
    let mut filter = Judging::below(100);
    // Case 1's candidate (1000) misses; case 2's (102) hits.
    filter.repair = Box::new(|values| {
        let value = as_int(&values[0]);
        vec![vec![int(if value == 1 { 1000 } else { 100 + value })]]
    });
    let report = filtered(
        &mut runner,
        &mut counter_schedule(1, 1),
        &settings(1),
        Budget::Cases(5),
        &mut filter,
    );
    let witness = report.witness().cloned().expect("a repaired witness");
    assert_eq!(witness.repaired_from.expect("repaired-from").case, 1);
    let entry = &report.client_refusals[0];
    assert_eq!((entry.case, entry.count, entry.repaired), (0, 2, false));
}

/// A repair counts only once a candidate runs (review M5): candidates that are all inadmissible
/// cost no run, count no repair and never reach the cause's failure cut-off.
#[test]
fn a_repair_whose_candidates_never_run_counts_nothing() {
    let mut runner = Scripted::new(
        |values| hit(values, 1, "end"),
        |values| Ok(hit(values, 1, "end")),
    );
    runner.admissible = Box::new(|_, value| as_int(value) != 99);
    let mut filter = Judging::new(|_| Some(refusal("always")));
    filter.repair = Box::new(|_| vec![vec![int(99)]]);
    let report = filtered(
        &mut runner,
        &mut counter_schedule(1, 1),
        &settings(1),
        Budget::Cases(6),
        &mut filter,
    );
    assert_eq!(
        filter.repairs.len(),
        6,
        "every refused hit is offered a repair"
    );
    assert_eq!(report.totals.filter.repairs, 0);
    assert_eq!(report.totals.filter.repair_candidates, 0);
    assert_eq!(report.totals.filter.repairs_skipped, 0);
}

/// The `client-refused` warning says every hit was refused only when no accepted hit was lost
/// to its confirmation (review M3): here hit 2 is accepted but its confirmation disagrees.
#[test]
fn the_refusal_warning_does_not_claim_every_hit_when_one_was_unconfirmed() {
    let mut runner = Scripted::new(
        |values| hit(values, 1, "end"),
        |values| Ok(hit(values, 1, "another end")),
    );
    let mut filter = Judging::below(2);
    let report = filtered(
        &mut runner,
        &mut counter_schedule(1, 1),
        &settings(1),
        Budget::Cases(2),
        &mut filter,
    );
    assert_eq!(report.witness(), None);
    assert_eq!(report.totals.unconfirmed, 1);
    let warning = report
        .warnings
        .iter()
        .find(|warning| warning.starts_with("client-refused:"))
        .expect("a client-refused warning");
    assert!(!warning.contains("every candidate hit"), "{warning}");
    assert!(
        warning.contains("1 other candidate was not confirmed"),
        "{warning}"
    );
}
