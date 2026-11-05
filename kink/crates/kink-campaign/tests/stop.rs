//! The counted stop (`RunOptions::stop`): a campaign over a definition that never terminates ends
//! its result runs at named rewrite rules, at the `N`th stop event of a path, by resuming each
//! request's stop leaves (`testdata/k/clock.k`, a free-running clock whose `frame` step comes
//! every fourth step, and whose negative counts reach each next frame two ways).
//!
//! Every verdict here is relative to the stop: a kill says that the ends of the truncated system
//! (each path cut at its `N`th stop event, or at its own end) differ.

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::num::NonZeroU64;
use std::path::Path;
use std::time::Duration;

use k_rust::definition::AttributeKey;
use k_rust::kast::{Sort, Term};
use k_rust::kompile::CompileOptions;
use k_rust::kore::ast::Pattern;
use kink_campaign::{
    BaselineSession, Campaign, CampaignFailureKind, CampaignOptions, CampaignRun, CrashPolicy,
    ExecutionFailureKind, ManifestError, MultiManifestInput, MutantScopeFailure, MutantStatus,
    OneSided, OracleDeclaration, OracleOutcome, OracleSide, Projection, RunOptions, RunStop,
    ScheduleMode, SelectionPolicy as Sel, SideRun, StateProjection, Stop, TestCase, TestRun,
    WorkBudget, campaign_manifest_multi_with_options, run_campaign_multi_with, run_campaign_with,
};
use kink_native::NativeValidator;
use kink_native::execution::{ExecutionBudget, ResultModality, StopRules};
use kink_native::step_events::{StepEventSpec, StepObservation};
use kink_patch::{
    Baseline, CandidateGeneration, Edit, InsertPosition, Patch, SelectionPolicy, SiteSelector,
    TermRef, derive_sites, select,
};
use kink_pattern::{Atom, ExecutionTerminalKind, PatternArm, PatternPlan};

fn normal(_: &Pattern) -> ExecutionTerminalKind {
    ExecutionTerminalKind::Normal
}

fn validator() -> NativeValidator {
    NativeValidator::bind(
        support::load_path(&Path::new(support::DIR).join("clock.k"), "CLOCK"),
        CompileOptions::default(),
    )
}

fn clock(n: i64, phase: i64) -> Pattern {
    support::initial_state(
        support::app("Lblclock", vec![support::int(n), support::int(phase)]),
        "SortClock",
    )
}

fn test(id: &str) -> TestCase {
    TestCase {
        id: id.into(),
        initial_state: clock(0, 0),
        oracles: vec![
            OracleDeclaration::new(
                CrashPolicy::Reject,
                Projection::State(StateProjection::WholeTerm),
            )
            .unwrap(),
        ],
    }
}

/// The time bound of every run: nextest stops a test after ten minutes, so this clock fires only
/// on a test that fails anyway, and the stop, the depth bound or the work budget decides every
/// passing run.
const NO_CLOCK: Duration = Duration::from_secs(600);

/// Each request's depth bound: a path that never reaches its next stop (a mutant whose frame
/// step has a sibling runs past every frame) ends here instead of at the clock.
const MAX_DEPTH: u64 = 64;

fn campaign<'a>(validator: &'a NativeValidator, tests: &'a [TestCase]) -> Campaign<'a> {
    Campaign {
        validator,
        module: "CLOCK",
        observation: &[],
        classify: &normal,
        tests,
        budget: ExecutionBudget {
            time: NO_CLOCK,
            max_simplification_iterations: 10_000,
            max_depth: Some(MAX_DEPTH),
            max_breadth: None,
        },
    }
}

const FRAME: &str = "CLOCK.frame";

/// The rule that resets a phase past 4, which only a negative count reaches.
const SKIP: &str = "CLOCK.skip";

fn count(count: u64) -> NonZeroU64 {
    NonZeroU64::new(count).unwrap()
}

/// The stop after `frame`, at its `count`th step.
fn after_frame(count: u64) -> Stop {
    Stop::new(
        StopRules {
            before: Vec::new(),
            after: vec![FRAME.into()],
        },
        self::count(count),
    )
    .unwrap()
}

/// The stop before `frame`, at its `count`th step.
fn before_frame(count: u64) -> Stop {
    Stop::new(
        StopRules {
            before: vec![FRAME.into()],
            after: Vec::new(),
        },
        self::count(count),
    )
    .unwrap()
}

fn options(stop: Stop) -> RunOptions {
    RunOptions {
        stop,
        ..RunOptions::default()
    }
}

/// The reference to the only Int token `token` of rule `rule` whose operation also reads the
/// variable `beside` (`N +Int 1` beside `N`, not `P +Int 1`), or of the rule anywhere without it.
fn token(baseline: &Baseline, rule: &str, token: &str, beside: Option<&str>) -> TermRef {
    fn walk(b: &Baseline, at: &TermRef, token: &str, out: &mut Vec<TermRef>) {
        let Some(term) = b.term(at) else {
            return;
        };
        if matches!(term.unannotated(), Term::Token { token: t, .. } if t == token) {
            out.push(at.clone());
        }
        for index in 0.. {
            let mut path = at.path.0.clone();
            path.push(index);
            let child = TermRef::new(at.sentence.clone(), path);
            if b.term(&child).is_none() {
                break;
            }
            walk(b, &child, token, out);
        }
    }
    let sentence = support::rule(baseline, rule);
    let mut found = Vec::new();
    for part in 0..3 {
        walk(
            baseline,
            &TermRef::new(sentence.clone(), [part]),
            token,
            &mut found,
        );
    }
    // A variable operand is read through its sort cast (`#SemanticCastToInt(N)`).
    fn reads(term: &Term, variable: &str) -> bool {
        match term.unannotated() {
            Term::Variable { name, .. } => name == variable,
            Term::Apply { arguments, .. } => arguments.iter().any(|a| reads(a, variable)),
            _ => false,
        }
    }
    found.retain(|at| {
        beside.is_none_or(|beside| {
            let parent = TermRef::new(at.sentence.clone(), &at.path.0[..at.path.0.len() - 1]);
            baseline
                .term(&parent)
                .is_some_and(|operation| reads(operation, beside))
        })
    });
    let [at] = found
        .try_into()
        .unwrap_or_else(|found: Vec<_>| panic!("{rule}: {} tokens {token}", found.len()));
    at
}

/// The patch replacing the Int token at `at` by `to`.
fn replace(baseline: &Baseline, at: TermRef, to: &str) -> (TermRef, Patch) {
    let patch = Patch::new(vec![Edit::ReplaceTerm {
        expected: baseline.term(&at).unwrap().clone(),
        at: at.clone(),
        replacement: Term::Token {
            token: to.into(),
            sort: Sort::new("Int"),
        },
    }])
    .unwrap();
    (at, patch)
}

/// The one-candidate generation of `patch` at the site `site`.
fn generation<'b>(
    baseline: &'b Baseline,
    (site, patch): (TermRef, Patch),
) -> CandidateGeneration<'b> {
    let label = baseline
        .sentence(&site.sentence)
        .and_then(|rule| rule.attributes().string(AttributeKey::Label))
        .expect("a labelled rule")
        .to_owned();
    let discovery = derive_sites(
        baseline,
        "site",
        &[
            SiteSelector::RuleLabel(label),
            SiteSelector::Path(site.path.0.clone()),
        ],
    )
    .unwrap();
    let generation = select(&discovery, SelectionPolicy::Each, 1)
        .unwrap()
        .fold("stop", |_| patch.clone())
        .unwrap();
    assert_eq!(
        generation.candidates().len(),
        1,
        "{:?}",
        generation.dispositions()
    );
    generation
}

/// tick's count step 1 becomes 2.
fn faster_tick(baseline: &Baseline) -> CandidateGeneration<'_> {
    generation(
        baseline,
        replace(baseline, token(baseline, "CLOCK.tick", "1", Some("N")), "2"),
    )
}

/// frame's count step 1 becomes 5: an edit of the stop rule's right-hand side only.
fn frame_rhs(baseline: &Baseline) -> CandidateGeneration<'_> {
    generation(
        baseline,
        replace(baseline, token(baseline, FRAME, "1", Some("N")), "5"),
    )
}

/// frame loses its label: the rule deleted and inserted again at the module's end without it (an
/// inserted sentence carries no label).
fn unlabelled_frame(baseline: &Baseline) -> CandidateGeneration<'_> {
    let frame = support::rule(baseline, FRAME);
    let mut clone = baseline.sentence(&frame).unwrap().clone();
    for key in [
        AttributeKey::Label,
        AttributeKey::UniqueId,
        AttributeKey::Origin,
        AttributeKey::Location,
        AttributeKey::Source,
        AttributeKey::SourceId,
        AttributeKey::SentenceStartOffset,
        AttributeKey::SentenceEndOffset,
        AttributeKey::ContentStartLine,
        AttributeKey::ContentStartColumn,
        AttributeKey::ContentStartOffset,
    ] {
        clone.attributes_mut().remove(key.as_str());
    }
    let patch = Patch::new(vec![
        Edit::DeleteSentence { at: frame.clone() },
        Edit::InsertSentence {
            position: InsertPosition::ModuleEnd("CLOCK".into()),
            ordinal: 0,
            sentence: clone,
        },
    ])
    .unwrap();
    generation(baseline, (TermRef::new(frame, [0]), patch))
}

/// tick's guard 3 becomes 4: at phase 3 both tick and frame apply, so frame's step has a sibling.
fn frame_choice(baseline: &Baseline) -> CandidateGeneration<'_> {
    generation(
        baseline,
        replace(baseline, token(baseline, "CLOCK.tick", "3", None), "4"),
    )
}

/// halt's bound becomes 2: the run ends on its own (`halted(3)`) before its first frame.
fn early_halt(baseline: &Baseline) -> CandidateGeneration<'_> {
    generation(
        baseline,
        replace(
            baseline,
            token(baseline, "CLOCK.halt", "1000000", None),
            "2",
        ),
    )
}

/// warp's -1 becomes 0: the first step branches into tick's way to the first frame (the
/// baseline's, four steps) and warp's (`clock(100, 3)`, one step to its frame).
fn warp(baseline: &Baseline) -> CandidateGeneration<'_> {
    generation(
        baseline,
        replace(baseline, token(baseline, "CLOCK.warp", "-1", None), "0"),
    )
}

fn run(
    campaign: &Campaign<'_>,
    generation: &CandidateGeneration<'_>,
    run: RunOptions,
) -> CampaignRun {
    run_campaign_with(
        campaign,
        generation,
        &CampaignOptions {
            schedule: ScheduleMode::Full,
            selection: Sel::None,
            share_evidence: true,
            run,
            compile_workers: 1,
        },
    )
    .unwrap()
}

fn on_a_big_stack(work: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(work)
        .unwrap()
        .join()
        .unwrap();
}

/// The run's one test's slot outcomes on its one mutant.
fn outcomes(run: &CampaignRun) -> &TestRun {
    &run.mutants[0].plan.tests[0].run
}

/// The ends of the baseline's run of each test, in test order.
fn baseline_ends(run: &CampaignRun) -> Vec<Vec<Pattern>> {
    run.baseline
        .iter()
        .map(|evidence| evidence.ends.iter().cloned().collect())
        .collect()
}

/// The ends of the one mutant's run of each test.
fn mutant_ends(run: &CampaignRun) -> Vec<Vec<Pattern>> {
    run.mutants[0]
        .evidence
        .iter()
        .map(|evidence| evidence.ends.iter().cloned().collect())
        .collect()
}

/// The configuration `<k> halted(n) </k>`.
fn halted(n: i64) -> Pattern {
    support::initial_state(
        support::app("Lblhalted", vec![support::int(n)]),
        "SortClock",
    )
}

/// The stop is reached by resuming: after the `N`th frame the clock is at `4N` and phase 0;
/// before it, at `4N - 1` and phase 3, the `N - 1` earlier frames taken. A test's own count
/// overrides the campaign's for that test only.
#[test]
fn a_counted_stop_ends_each_run_at_its_nth_frame() {
    on_a_big_stack(|| {
        let validator = validator();
        let tests = [test("clock")];
        let campaign = campaign(&validator, &tests);
        let generation = faster_tick(validator.baseline());
        for (stop, end) in [
            (after_frame(1), clock(4, 0)),
            (after_frame(2), clock(8, 0)),
            (after_frame(3), clock(12, 0)),
            (before_frame(1), clock(3, 3)),
            (before_frame(3), clock(11, 3)),
        ] {
            let run = run(&campaign, &generation, options(stop));
            assert_eq!(baseline_ends(&run), [vec![end]], "{stop:?}");
        }
        let tests = [test("one"), test("three")];
        let campaign = self::campaign(&validator, &tests);
        let stop = after_frame(1).with_test_count("three", count(3));
        let run = run(&campaign, &generation, options(stop));
        assert_eq!(baseline_ends(&run), [vec![clock(4, 0)], vec![clock(12, 0)]]);
    });
}

/// frame's count step 1 becomes 5, an edit of the stop rule's right-hand side only: stopping
/// before the first frame never takes the step, so the edit is invisible and the mutant survives
/// for that reason; stopping before the third frame takes two of them, and stopping after the
/// first takes it, so both kill.
#[test]
fn an_edit_of_a_before_stop_rules_right_hand_side_is_seen_only_through_earlier_stops() {
    on_a_big_stack(|| {
        let validator = validator();
        let tests = [test("clock")];
        let campaign = campaign(&validator, &tests);
        let generation = frame_rhs(validator.baseline());
        let hidden = run(&campaign, &generation, options(before_frame(1)));
        assert_eq!(hidden.mutants[0].report.status, MutantStatus::Survived);
        assert_eq!(
            *outcomes(&hidden),
            TestRun::Compared(vec![OracleOutcome::Agree])
        );
        for stop in [before_frame(3), after_frame(1)] {
            let run = run(&campaign, &generation, options(stop));
            assert_eq!(
                run.mutants[0].report.status,
                MutantStatus::Killed,
                "{stop:?}"
            );
        }
    });
}

/// frame loses its label: the stop names no rewrite rule of the mutant, so the observation is
/// not defined there and the mutant is not admitted, before any test runs; it is never run
/// without its stop.
#[test]
fn a_mutant_without_the_stop_rule_is_not_admitted() {
    on_a_big_stack(|| {
        let validator = validator();
        let tests = [test("clock")];
        let campaign = campaign(&validator, &tests);
        let generation = unlabelled_frame(validator.baseline());
        for stop in [after_frame(1), before_frame(3)] {
            let run = run(&campaign, &generation, options(stop));
            let mutant = &run.mutants[0];
            assert_eq!(
                mutant.plan.mutant_failure,
                Some(MutantScopeFailure::StopUnresolved)
            );
            assert_eq!(mutant.report.status, MutantStatus::NotAdmitted);
            assert!(mutant.plan.tests.is_empty());
            assert!(mutant.evidence.is_empty());
        }
    });
}

/// tick's guard 3 becomes 4: at phase 3 both tick and frame apply, so frame's step is not its
/// state's one successor and k-rust runs past it. The run's leaves are not the truncated
/// system's ends, so it is excluded (`passed-stop`) and the mutant is unknown, never killed.
#[test]
fn a_stop_rule_turned_into_a_choice_is_unknown() {
    on_a_big_stack(|| {
        let validator = validator();
        let tests = [test("clock")];
        let campaign = campaign(&validator, &tests);
        let generation = frame_choice(validator.baseline());
        for stop in [after_frame(1), after_frame(2), before_frame(1)] {
            let run = run(&campaign, &generation, options(stop));
            assert_eq!(
                run.mutants[0].report.status,
                MutantStatus::Unknown,
                "{stop:?}"
            );
            assert_eq!(
                *outcomes(&run),
                TestRun::Failed(ExecutionFailureKind::PassedStop)
            );
        }
    });
}

/// warp's -1 becomes 0: the first step branches into tick's way (the baseline's ends) and warp's
/// (`clock(100, 3)`, whose frames end it at 101 and then 105). Stopping after the second frame,
/// both runs are complete without a work budget and the mutant is killed two-sidedly.
///
/// Under a work budget of the baseline's work plus 2 states, stage 1 (both branches to their
/// first frame) costs one state more than the baseline's, and stage 2 resumes its starts in the
/// order of their patterns: `clock(101, 0)` before `clock(4, 0)` (the Int `"101"` sorts before
/// `"4"`). The first reaches `clock(105, 0)`, and the second ends at the budget. The mutant's run
/// is work-bound, so its side is unknown, but its explored stage-2 stop leaf is a final
/// configuration of every completion of the run, outside the baseline's ends: a one-sided kill.
/// With no state over the baseline's work the budget ends stage 2's first request too, and the
/// mutant is unknown; with five or more, the run completes.
#[test]
fn a_work_bound_mutant_is_killed_one_sidedly_at_its_last_stage() {
    on_a_big_stack(|| {
        let validator = validator();
        let tests = [test("clock")];
        let campaign = campaign(&validator, &tests);
        let generation = warp(validator.baseline());
        let unbounded = run(&campaign, &generation, options(after_frame(2)));
        assert_eq!(unbounded.mutants[0].report.status, MutantStatus::Killed);
        assert_eq!(mutant_ends(&unbounded), [vec![clock(105, 0), clock(8, 0)]]);
        let budget = |floor| RunOptions {
            work: WorkBudget::Calibrated { factor: 1, floor },
            one_sided: OneSided::NoCrashClassifier,
            ..options(after_frame(2))
        };
        let bounded = run(&campaign, &generation, budget(2));
        let mutant = &bounded.mutants[0];
        assert_eq!(mutant.report.status, MutantStatus::Killed);
        assert_eq!(
            *outcomes(&bounded),
            TestRun::Compared(vec![OracleOutcome::Distinguish])
        );
        assert_eq!(
            mutant.evidence[0].run,
            SideRun::Sides {
                sides: vec![OracleSide::Unknown]
            }
        );
        assert_eq!(
            mutant.evidence[0].one_sided_ends.iter().collect::<Vec<_>>(),
            [&clock(105, 0)]
        );
        let tight = run(&campaign, &generation, budget(0));
        assert_eq!(tight.mutants[0].report.status, MutantStatus::Unknown);
        assert!(tight.mutants[0].evidence[0].one_sided_ends.is_empty());
    });
}

/// A stop's names are exact labels of rewrite rules of the baseline: an unknown label, a label
/// without its module (`frame` for `CLOCK.frame`), or the label of an equation (`CLOCK.later`,
/// a function's: k-rust stops only at rewrite steps) refuses the campaign before anything runs,
/// naming them.
#[test]
fn a_stop_that_names_no_rewrite_rule_of_the_baseline_is_refused() {
    on_a_big_stack(|| {
        let validator = validator();
        let tests = [test("clock")];
        let campaign = campaign(&validator, &tests);
        let generation = faster_tick(validator.baseline());
        let stop = Stop::new(
            StopRules {
                before: vec!["frame".into()],
                after: vec![FRAME.into(), "CLOCK.nothing".into(), "CLOCK.later".into()],
            },
            count(1),
        )
        .unwrap();
        let failure = run_campaign_with(
            &campaign,
            &generation,
            &CampaignOptions {
                schedule: ScheduleMode::Full,
                selection: Sel::None,
                share_evidence: true,
                run: options(stop),
                compile_workers: 1,
            },
        )
        .unwrap_err();
        assert_eq!(failure.kind(), CampaignFailureKind::InvalidDeclaration);
        assert_eq!(
            failure.unresolved_stop(),
            ["frame", "CLOCK.nothing", "CLOCK.later"]
        );
        assert!(failure.to_string().contains("stop-unresolved"), "{failure}");
    });
}

/// A pattern oracle's stepped run takes no stop, so its sides would be of another observation
/// than the stop's ends: a campaign with a stop and a pattern oracle is refused before anything
/// runs.
#[test]
fn a_campaign_with_a_stop_and_a_pattern_oracle_is_refused() {
    on_a_big_stack(|| {
        let validator = validator();
        let specs = [StepEventSpec {
            constructor: "beforeFrame".into(),
            pre: support::k_config(
                support::app(
                    "Lblclock",
                    vec![support::var("N", "SortInt"), support::int(3)],
                ),
                "SortClock",
                "R",
                "C",
            ),
            post: None,
            payload: Vec::new(),
        }];
        let vocabulary = StepObservation::vocabulary_of(&specs).unwrap();
        let plan = PatternPlan::new(
            &vocabulary,
            Vec::new(),
            vec![PatternArm {
                atoms: vec![Atom {
                    constructor: "beforeFrame".into(),
                    payload: Vec::new(),
                }],
                relations: Vec::new(),
            }],
            None,
        )
        .unwrap();
        let mut tests = [test("clock")];
        tests[0].oracles.push(
            OracleDeclaration::new(
                CrashPolicy::Reject,
                Projection::Pattern {
                    plan,
                    with_bindings: false,
                },
            )
            .unwrap(),
        );
        let campaign = Campaign {
            observation: &specs,
            ..campaign(&validator, &tests)
        };
        let generation = faster_tick(validator.baseline());
        let failure = run_campaign_with(
            &campaign,
            &generation,
            &CampaignOptions {
                schedule: ScheduleMode::Full,
                selection: Sel::None,
                share_evidence: true,
                run: options(after_frame(1)),
                compile_workers: 1,
            },
        )
        .unwrap_err();
        assert_eq!(failure.kind(), CampaignFailureKind::InvalidDeclaration);
        assert!(failure.to_string().contains("pattern oracle"), "{failure}");
    });
}

/// A campaign manifest records no stop, so none is written for runs with one.
#[test]
fn a_manifest_for_runs_with_a_stop_is_refused() {
    on_a_big_stack(|| {
        let validator = validator();
        let tests = [test("clock")];
        let campaign = campaign(&validator, &tests);
        let generation = faster_tick(validator.baseline());
        let refused = campaign_manifest_multi_with_options(
            &MultiManifestInput {
                campaign: &campaign,
                generations: std::slice::from_ref(&generation),
                operators: &[],
                universe: None,
                schedule: ScheduleMode::Full,
                selection: Sel::None,
                classifier: "normal",
            },
            None,
            &options(after_frame(1)),
        );
        assert!(matches!(refused, Err(ManifestError::Stopped)));
    });
}

mod kink_tier {
    use super::*;

    /// tick's count step 1 becomes 2: every frame comes at another count, killed under every stop.
    #[test]
    #[ignore = "kink"]
    fn a_faster_tick_is_killed() {
        on_a_big_stack(|| {
            let validator = validator();
            let tests = [test("clock")];
            let campaign = campaign(&validator, &tests);
            let generation = faster_tick(validator.baseline());
            for stop in [after_frame(1), after_frame(3), before_frame(1)] {
                let run = run(&campaign, &generation, options(stop));
                assert_eq!(
                    run.mutants[0].report.status,
                    MutantStatus::Killed,
                    "{stop:?}"
                );
                assert_eq!(
                    *outcomes(&run),
                    TestRun::Compared(vec![OracleOutcome::Distinguish])
                );
            }
        });
    }

    /// halt's bound becomes 2: the mutant's run ends on its own at `halted(3)` before its first
    /// frame, an end the baseline's stopped run does not have.
    #[test]
    #[ignore = "kink"]
    fn a_mutant_that_ends_before_its_stop_is_killed_by_its_own_end() {
        on_a_big_stack(|| {
            let validator = validator();
            let tests = [test("clock")];
            let campaign = campaign(&validator, &tests);
            let generation = early_halt(validator.baseline());
            for stop in [after_frame(1), after_frame(3)] {
                let run = run(&campaign, &generation, options(stop));
                assert_eq!(
                    run.mutants[0].report.status,
                    MutantStatus::Killed,
                    "{stop:?}"
                );
                assert_eq!(mutant_ends(&run), [vec![halted(3)]]);
            }
        });
    }

    /// A state set and a path set of the same staged run have the same ends, and give the same
    /// verdicts, at one stop and at three (the warp mutant's run branches, and k-rust merges the
    /// state set's equal leaves within a request; equal starts of one stage are
    /// `a_state_set_resumes_equal_starts_once`'s).
    #[test]
    #[ignore = "kink"]
    fn a_state_set_and_a_path_set_of_a_staged_run_agree() {
        on_a_big_stack(|| {
            let validator = validator();
            let tests = [test("clock")];
            let campaign = campaign(&validator, &tests);
            let baseline = validator.baseline();
            for generation in [warp(baseline), faster_tick(baseline), early_halt(baseline)] {
                for stop in [after_frame(1), after_frame(3), before_frame(3)] {
                    let [state_set, path_set] = [ResultModality::StateSet, ResultModality::PathSet]
                        .map(|result_modality| {
                            run(
                                &campaign,
                                &generation,
                                RunOptions {
                                    result_modality,
                                    ..options(stop)
                                },
                            )
                        });
                    assert_eq!(baseline_ends(&state_set), baseline_ends(&path_set));
                    assert_eq!(mutant_ends(&state_set), mutant_ends(&path_set));
                    assert_eq!(
                        state_set.mutants[0].report.status,
                        path_set.mutants[0].report.status
                    );
                    assert_eq!(state_set.mutants[0].plan, path_set.mutants[0].plan);
                }
            }
        });
    }

    /// A stop before frame proposes frame's step without taking it, so the first frame has not
    /// fired when the run stops before it; resumed at that stop to reach the second, the run takes
    /// the first frame's step, and frame has fired, as it has after the first frame.
    #[test]
    #[ignore = "kink"]
    fn a_resumed_cut_point_fires_its_rule() {
        on_a_big_stack(|| {
            let validator = validator();
            let tests = [test("clock")];
            let campaign = campaign(&validator, &tests);
            let baseline = validator.baseline();
            let generation = faster_tick(baseline);
            let frame = support::rule(baseline, FRAME);
            let tick = support::rule(baseline, "CLOCK.tick");
            for (stop, fired) in [
                (before_frame(1), false),
                (before_frame(2), true),
                (after_frame(1), true),
            ] {
                let run = run(&campaign, &generation, options(stop));
                let coverage = &run.baseline_coverage[0];
                assert!(coverage.complete, "{stop:?}");
                assert!(coverage.fired_sentences.contains(&tick), "{stop:?}");
                assert_eq!(coverage.fired_sentences.contains(&frame), fired, "{stop:?}");
            }
        });
    }

    /// From `clock(-16, 0)`, `split` branches off each frame's first tick, so each frame is
    /// reached two ways: by ticks to phase 3, where `frame` steps, and by `split` to phase 5,
    /// where `skip` steps, both to the same next state. Stopping before either rule, a request
    /// ends at two cut points of different states (`clock(-13, 3)` and `clock(-13, 5)`), whose
    /// proposals are one state, `clock(-12, 0)`. A state set resumes it once, crediting both
    /// rules (each start's taken step is credited when it is resumed, so the one start carries
    /// both): its second and last stage is one request, with two stop leaves. A path set resumes
    /// it once per leaf: two requests, four leaves. Both have the same ends, and in both every
    /// rule whose step the staged run took has fired, though no request took either.
    #[test]
    #[ignore = "kink"]
    fn a_state_set_resumes_equal_starts_once() {
        on_a_big_stack(|| {
            let validator = validator();
            let tests = [TestCase {
                initial_state: clock(-16, 0),
                ..test("split")
            }];
            let campaign = campaign(&validator, &tests);
            let baseline = validator.baseline();
            let generation = faster_tick(baseline);
            let stop = Stop::new(
                StopRules {
                    before: vec![FRAME.into(), SKIP.into()],
                    after: Vec::new(),
                },
                count(2),
            )
            .unwrap();
            for (result_modality, leaves) in
                [(ResultModality::StateSet, 2), (ResultModality::PathSet, 4)]
            {
                let mut session = BaselineSession::new(&validator);
                let run = run_campaign_multi_with(
                    &campaign,
                    std::slice::from_ref(&generation),
                    &CampaignOptions {
                        schedule: ScheduleMode::Full,
                        selection: Sel::None,
                        share_evidence: true,
                        run: RunOptions {
                            result_modality,
                            ..options(stop)
                        },
                        compile_workers: 1,
                    },
                    &mut session,
                )
                .unwrap();
                assert_eq!(
                    run.baseline[0].ends,
                    [clock(-9, 3), clock(-9, 5)].into(),
                    "{result_modality:?}"
                );
                let census = &session
                    .last_call()
                    .baseline_of("split")
                    .expect("the baseline's run")
                    .run
                    .census;
                assert_eq!(census.total(), leaves, "{result_modality:?}");
                let coverage = &run.baseline_coverage[0];
                assert!(coverage.complete, "{result_modality:?}");
                for rule in [FRAME, SKIP] {
                    assert!(
                        coverage
                            .fired_sentences
                            .contains(&support::rule(baseline, rule)),
                        "{result_modality:?}: {rule}"
                    );
                }
            }
        });
    }

    /// The time budget bounds the whole staged run, as one watchdog: each request has the time the
    /// run has left. A stop at the millionth frame is a million requests of four steps each,
    /// which a second does not reach, so the baseline's run times out (and a baseline without
    /// evidence refuses the campaign); with a second per request it would end at its stop.
    #[test]
    #[ignore = "kink"]
    fn the_time_budget_bounds_the_whole_staged_run() {
        on_a_big_stack(|| {
            let validator = validator();
            let tests = [test("clock")];
            let mut campaign = campaign(&validator, &tests);
            campaign.budget.time = Duration::from_secs(1);
            let generation = faster_tick(validator.baseline());
            let mut session = BaselineSession::new(&validator);
            let failure = run_campaign_multi_with(
                &campaign,
                std::slice::from_ref(&generation),
                &CampaignOptions {
                    schedule: ScheduleMode::Full,
                    selection: Sel::None,
                    share_evidence: true,
                    run: options(after_frame(1_000_000)),
                    compile_workers: 1,
                },
                &mut session,
            )
            .unwrap_err();
            assert_eq!(failure.kind(), CampaignFailureKind::BaselineError);
            let census = &session
                .last_call()
                .baseline_of("clock")
                .expect("the baseline's run")
                .run
                .census;
            assert_eq!(census.stop, RunStop::Time);
        });
    }
}
