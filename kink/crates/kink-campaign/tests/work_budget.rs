//! Re-pin lane 1 (L1-1): the mutants' work budget (`RunOptions::work`) and the result-run
//! modality (`RunOptions::result_modality`) as a campaign uses them.
//!
//! A calibrated work budget bounds a mutant's result run of a test by the work of the baseline's
//! run of that test. It only stops runs: a run it does not stop is the unbounded run, and a run it
//! stops ends in a `work-bound` leaf, so the test is `Unknown`. It never bounds a baseline run.
//! So the budget decides only how many mutants end `Unknown`: never a kill.

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::path::Path;
use std::time::Duration;

use k_rust::kast::{Sort, Term};
use k_rust::kompile::CompileOptions;
use k_rust::kore::ast::Pattern;
use kink_campaign::{
    Campaign, CampaignOptions, CampaignRun, CrashPolicy, ExecutionFailureKind, MutantStatus,
    OneSided, OracleDeclaration, OracleOutcome, Projection, RunOptions, ScheduleMode,
    SelectionPolicy as Sel, StateProjection, TestCase, TestRun, WorkBudget, run_campaign_with,
};
use kink_native::NativeValidator;
use kink_native::execution::{ExecutionBudget, ResultModality};
use kink_patch::{
    Baseline, CandidateGeneration, Edit, Patch, SelectionPolicy, SiteSelector, TermRef,
    derive_sites, select,
};
use kink_pattern::ExecutionTerminalKind;

fn normal(_: &Pattern) -> ExecutionTerminalKind {
    ExecutionTerminalKind::Normal
}

fn validator() -> NativeValidator {
    NativeValidator::bind(
        support::load_path(&Path::new(support::DIR).join("l1/workloop.k"), "WORKLOOP"),
        CompileOptions::default(),
    )
}

fn tests() -> Vec<TestCase> {
    vec![TestCase {
        id: "three".into(),
        initial_state: support::initial_state(
            support::app("Lblcount", vec![support::int(3)]),
            "SortProg",
        ),
        oracles: [
            StateProjection::ExitStop {
                exit_code_cell: None,
            },
            StateProjection::WholeTerm,
        ]
        .into_iter()
        .map(|p| OracleDeclaration::new(CrashPolicy::Reject, Projection::State(p)).unwrap())
        .collect(),
    }]
}

/// The time bound of the runs that must time out: the never-ending mutant without a work budget
/// (`RunOptions::default()`), which no other bound stops, so `Timeout` is its only outcome at any
/// load. Its baseline ends in a handful of steps.
const UNBOUNDED_TIME: Duration = Duration::from_secs(3);

/// The time bound of a run whose expected outcome comes from the work budget or from a complete
/// run: nextest stops a test after ten minutes, so this clock fires only on a test that fails
/// anyway, and the bound decides every passing run (R4-WALLCLOCK).
const NO_CLOCK: Duration = Duration::from_secs(600);

fn campaign<'a>(
    validator: &'a NativeValidator,
    tests: &'a [TestCase],
    time: Duration,
) -> Campaign<'a> {
    Campaign {
        validator,
        module: "WORKLOOP",
        observation: &[],
        classify: &normal,
        tests,
        budget: ExecutionBudget {
            time,
            max_simplification_iterations: 10_000,
            max_depth: None,
            max_breadth: None,
        },
    }
}

/// The one-candidate generation whose patch replaces the only Int token `from` of `rule` by `to`.
fn replace<'b>(
    baseline: &'b Baseline,
    rule: &str,
    from: &str,
    to: &str,
) -> CandidateGeneration<'b> {
    fn walk(
        b: &Baseline,
        at: &kink_patch::SentenceRef,
        path: &mut Vec<u32>,
        token: &str,
    ) -> Vec<TermRef> {
        let here = TermRef::new(at.clone(), path.as_slice());
        let Some(term) = b.term(&here) else {
            return Vec::new();
        };
        let mut out = Vec::new();
        if matches!(term.unannotated(), Term::Token { token: t, .. } if t == token) {
            out.push(here);
        }
        for index in 0.. {
            path.push(index);
            if b.term(&TermRef::new(at.clone(), path.as_slice())).is_none() {
                path.pop();
                break;
            }
            out.extend(walk(b, at, path, token));
            path.pop();
        }
        out
    }
    // The rule's body, then its condition.
    let sentence = support::rule(baseline, rule);
    let [at] = (0..3)
        .flat_map(|part| walk(baseline, &sentence, &mut vec![part], from))
        .collect::<Vec<_>>()
        .try_into()
        .unwrap_or_else(|found: Vec<_>| panic!("{rule}: {} tokens {from}", found.len()));
    let patch = Patch::new(vec![Edit::ReplaceTerm {
        expected: baseline.term(&at).unwrap().clone(),
        at,
        replacement: Term::Token {
            token: to.into(),
            sort: Sort::new("Int"),
        },
    }])
    .unwrap();
    let discovery = derive_sites(
        baseline,
        rule,
        &[
            SiteSelector::RuleLabel(rule.into()),
            SiteSelector::Path(vec![0]),
        ],
    )
    .unwrap();
    let generation = select(&discovery, SelectionPolicy::Each, 1)
        .unwrap()
        .fold(rule, |_| patch.clone())
        .unwrap();
    assert_eq!(generation.candidates().len(), 1);
    generation
}

fn run(
    campaign: &Campaign<'_>,
    generation: &CandidateGeneration<'_>,
    schedule: ScheduleMode,
    run: RunOptions,
) -> CampaignRun {
    run_campaign_with(
        campaign,
        generation,
        &CampaignOptions {
            schedule,
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

const fn calibrated(factor: u64, floor: u64) -> RunOptions {
    RunOptions {
        result_modality: ResultModality::StateSet,
        work: WorkBudget::Calibrated { factor, floor },
        one_sided: OneSided::Off,
    }
}

#[test]
fn the_limit_is_factor_times_baseline_work_plus_floor() {
    assert_eq!(WorkBudget::Unbounded.limit(5), None);
    assert_eq!(
        WorkBudget::Calibrated {
            factor: 4,
            floor: 10
        }
        .limit(5),
        Some(30)
    );
    assert_eq!(
        WorkBudget::Calibrated {
            factor: u64::MAX,
            floor: 1
        }
        .limit(2),
        Some(u64::MAX)
    );
    assert_eq!(RunOptions::default().work, WorkBudget::Unbounded);
    assert_eq!(
        RunOptions::default().result_modality,
        ResultModality::StateSet
    );
}

/// The step's `1` becomes `-1`: `count(3)` counts up forever. Without a work budget its run is
/// stopped by the time bound (`Timeout`); under a calibrated budget it ends in a work-bound leaf
/// long before, and the mutant is `Unknown`, never killed. That the work budget, not the clock,
/// stopped the bounded run is its outcome: a run the clock stops is `Failed(TimeLimit)`, so no
/// elapsed time is compared (a wall-time bound fails under load). The time bound is waited for once, in
/// Full: the test has one test case, so FirstKill runs it as Full does;
/// `heavy::a_mutant_that_never_ends_times_out_unbounded_in_first_kill` waits for it in FirstKill.
#[test]
fn a_mutant_that_never_ends_is_unknown_under_a_work_budget() {
    on_a_big_stack(|| {
        let validator = validator();
        let tests = tests();
        let generation = replace(validator.baseline(), "WORKLOOP.step", "1", "-1");
        let unbounded = run(
            &campaign(&validator, &tests, UNBOUNDED_TIME),
            &generation,
            ScheduleMode::Full,
            RunOptions::default(),
        );
        assert_never_ends_unbounded(&unbounded);
        let no_clock = campaign(&validator, &tests, NO_CLOCK);
        for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
            let bounded = run(&no_clock, &generation, schedule, calibrated(4, 100));
            assert_never_ends_bounded(&bounded, &unbounded);
        }
    });
}

/// The unbounded run of the never-ending mutant: stopped by the time bound.
fn assert_never_ends_unbounded(unbounded: &CampaignRun) {
    assert_eq!(
        unbounded.mutants[0].plan.tests[0].run,
        TestRun::Failed(ExecutionFailureKind::TimeLimit)
    );
    assert_eq!(unbounded.mutants[0].report.status, MutantStatus::Timeout);
}

/// The bounded run of the never-ending mutant: a work-bound leaf, `Unknown`, never killed.
fn assert_never_ends_bounded(bounded: &CampaignRun, unbounded: &CampaignRun) {
    assert_eq!(
        bounded.mutants[0].plan.tests[0].run,
        TestRun::Compared(vec![OracleOutcome::Unknown, OracleOutcome::Unknown])
    );
    assert_eq!(bounded.mutants[0].report.status, MutantStatus::Unknown);
    assert!(bounded.mutants[0].report.killing_test_ids.is_empty());
    // The baseline is never bounded.
    assert_eq!(bounded.baseline, unbounded.baseline);
}

mod heavy {
    use super::*;

    /// `a_mutant_that_never_ends_is_unknown_under_a_work_budget` in FirstKill: the unbounded run
    /// waits for the time bound, and the bounded run keeps its baseline.
    #[test]
    #[ignore = "heavy"]
    fn a_mutant_that_never_ends_times_out_unbounded_in_first_kill() {
        on_a_big_stack(|| {
            let validator = validator();
            let tests = tests();
            let generation = replace(validator.baseline(), "WORKLOOP.step", "1", "-1");
            let unbounded = run(
                &campaign(&validator, &tests, UNBOUNDED_TIME),
                &generation,
                ScheduleMode::FirstKill,
                RunOptions::default(),
            );
            assert_never_ends_unbounded(&unbounded);
            let bounded = run(
                &campaign(&validator, &tests, NO_CLOCK),
                &generation,
                ScheduleMode::FirstKill,
                calibrated(4, 100),
            );
            assert_never_ends_bounded(&bounded, &unbounded);
        });
    }
}

mod kink_tier {
    use super::*;

    /// The budget only decides how many mutants end `Unknown`. `stop`'s `7` becomes `8`: the same
    /// work, another result, killed under every budget. The guard's `0` becomes `-2`: two more
    /// states and another final state, killed without a budget and under a budget with room, and
    /// `Unknown` (never another verdict) under a budget of exactly the baseline's work. The result
    /// modality changes no status.
    #[test]
    #[ignore = "kink"]
    fn a_work_budget_decides_only_how_many_mutants_are_unknown() {
        on_a_big_stack(|| {
            let validator = validator();
            let tests = tests();
            let campaign = campaign(&validator, &tests, NO_CLOCK);
            let baseline = validator.baseline();
            let same_work = replace(baseline, "WORKLOOP.stop", "7", "8");
            let more_work = replace(baseline, "WORKLOOP.step", "0", "-2");
            let path_set = RunOptions {
                result_modality: ResultModality::PathSet,
                work: WorkBudget::Unbounded,
                one_sided: OneSided::Off,
            };
            for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
                for options in [
                    RunOptions::default(),
                    path_set,
                    calibrated(1, 0),
                    calibrated(1, 10),
                ] {
                    let report = &run(&campaign, &same_work, schedule, options).mutants[0].report;
                    assert_eq!(report.status, MutantStatus::Killed, "{options:?}");
                    assert_eq!(report.killing_test_ids, ["three"]);
                }
                for (options, expected) in [
                    (RunOptions::default(), MutantStatus::Killed),
                    (path_set, MutantStatus::Killed),
                    (calibrated(1, 10), MutantStatus::Killed),
                    (calibrated(1, 0), MutantStatus::Unknown),
                ] {
                    let run = run(&campaign, &more_work, schedule, options);
                    assert_eq!(run.mutants[0].report.status, expected, "{options:?}");
                    if expected == MutantStatus::Unknown {
                        assert_eq!(
                            run.mutants[0].plan.tests[0].run,
                            TestRun::Compared(vec![OracleOutcome::Unknown, OracleOutcome::Unknown])
                        );
                    }
                }
            }
        });
    }
}
