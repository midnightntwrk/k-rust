//! Re-pin L1-2 (ANALYSIS.md section 4 decision 6, finding A-15): the one-sided early kill
//! (`RunOptions::one_sided`).
//!
//! A mutant's state slot whose run ended at its work budget distinguishes when the explored part
//! of the run holds a clean, ground, stuck final configuration whose projection the baseline's
//! complete set lacks: every completion of the run holds that configuration, so the mutant's
//! projected set differs from the baseline's whatever the unexplored part holds. The fixture
//! `testdata/k/l1/onesided.k` finishes its early branch before the work budget cuts its loop.
//!
//! Each test pins the verdict with the rule off and on, and checks it against the two-sided
//! verdict of the unbounded run: a one-sided kill only where the unbounded run distinguishes, and
//! no other verdict than the unbounded one or `Unknown` under any budget.
//!
//! The principle is per path (Sebastien, 2026-10-17; root README, "What a kill trusts"): a
//! contradicted claim or a terminal that is not a value on another path of the mutant run does
//! not void the killing leaf, one on its own path does. The L1-2 review's probes
//! `testdata/k/l1/l12ct.k` and `l12cs.k` pin it (re-pin L1-2-fix-1): their unbounded mutant runs
//! are `Unknown` (a contradicted claim, a non-value terminal on the late branch), and the
//! one-sided rule kills them from the early branch, each kill explained leaf by leaf
//! (`testdata/k/one_sided_support.rs`). The fixture differential runs them too.

#[path = "../../../testdata/k/support.rs"]
mod support;

#[path = "../../../testdata/k/one_sided_support.rs"]
mod one_sided_support;

use std::path::Path;
use std::time::Duration;

use k_rust::kast::{Sort, Term};
use k_rust::kompile::CompileOptions;
use k_rust::kore::{ast::Pattern, walk};
use kink_campaign::{
    BaselineSession, Campaign, CampaignOptions, CampaignRun, CrashPolicy, ExecutionFailureKind,
    MutantId, MutantStatus, OneSided, OracleDeclaration, OracleOutcome, OracleSide, Projection,
    RunOptions, ScheduleMode, SelectionPolicy as Sel, SideRun, StateProjection, TestCase, TestRun,
    WorkBudget, run_campaign_multi_with,
};
use kink_native::execution::{ExecutionBudget, ResultModality};
use kink_native::{NativeValidator, ValidatedDefinition};
use kink_patch::{
    Baseline, CandidateGeneration, ClaimSupport, Edit, Patch, SelectionPolicy, SiteSelector,
    TermRef, derive_sites, select,
};
use kink_pattern::ExecutionTerminalKind;

use OracleOutcome::{Agree, Distinguish, Unknown};

const BUDGET: ExecutionBudget = ExecutionBudget {
    time: Duration::from_secs(20),
    max_simplification_iterations: 10_000,
    max_depth: None,
    max_breadth: None,
};

const START: i64 = 10;

fn normal(_: &Pattern) -> ExecutionTerminalKind {
    ExecutionTerminalKind::Normal
}

/// The argument of the first application of `symbol` in `term`, as its domain-value text.
fn argument_of(term: &Pattern, symbol: &str) -> Option<String> {
    if let Pattern::Application {
        symbol: head,
        arguments,
    } = term
        && head.name == symbol
    {
        return match arguments.as_slice() {
            [Pattern::DomainValue { value, .. }] => value.as_utf8().ok().map(str::to_owned),
            _ => None,
        };
    }
    walk::children(term)
        .into_iter()
        .find_map(|child| argument_of(child, symbol))
}

/// The child-index path to the first application of `symbol` in `term`.
fn path_to(term: &Pattern, symbol: &str) -> Option<Vec<u32>> {
    if matches!(term, Pattern::Application { symbol: head, .. } if head.name == symbol) {
        return Some(Vec::new());
    }
    walk::children(term)
        .into_iter()
        .enumerate()
        .find_map(|(index, child)| {
            let mut path = path_to(child, symbol)?;
            path.insert(0, u32::try_from(index).ok()?);
            Some(path)
        })
}

fn validator() -> NativeValidator {
    validator_of("onesided", "ONESIDED")
}

/// The validator of `testdata/k/l1/<name>.k`, main module `module`.
fn validator_of(name: &str, module: &str) -> NativeValidator {
    NativeValidator::bind(
        support::load_path(
            &Path::new(support::DIR).join(format!("l1/{name}.k")),
            module,
        ),
        CompileOptions::default(),
    )
}

fn initial(argument: i64) -> Pattern {
    support::initial_state(
        support::app("Lblstart", vec![support::int(argument)]),
        "SortProg",
    )
}

/// The test `t` of `start(START)` with the given state projections, crash policy `Reject`.
fn test(projections: Vec<StateProjection>) -> Vec<TestCase> {
    vec![TestCase {
        id: "t".into(),
        initial_state: initial(START),
        oracles: projections
            .into_iter()
            .map(|p| OracleDeclaration::new(CrashPolicy::Reject, Projection::State(p)).unwrap())
            .collect(),
    }]
}

/// kink-flow's two slots: the exit stop without an exit-code cell, and the whole term.
fn flow_slots() -> Vec<TestCase> {
    test(vec![
        StateProjection::ExitStop {
            exit_code_cell: None,
        },
        StateProjection::WholeTerm,
    ])
}

fn campaign<'a>(
    validator: &'a NativeValidator,
    tests: &'a [TestCase],
    classify: &'a dyn Fn(&Pattern) -> ExecutionTerminalKind,
) -> Campaign<'a> {
    campaign_of("ONESIDED", validator, tests, classify)
}

fn campaign_of<'a>(
    module: &'a str,
    validator: &'a NativeValidator,
    tests: &'a [TestCase],
    classify: &'a dyn Fn(&Pattern) -> ExecutionTerminalKind,
) -> Campaign<'a> {
    Campaign {
        validator,
        module,
        observation: &[],
        classify,
        tests,
        budget: BUDGET,
    }
}

/// The one-candidate generation whose patch replaces the only Int token `from` of `rule` by `to`.
fn replace<'b>(
    baseline: &'b Baseline,
    rule: &str,
    from: &str,
    to: &str,
) -> CandidateGeneration<'b> {
    let patch = token_patch(baseline, rule, from, to);
    let discovery = derive_sites(
        baseline,
        rule,
        &[
            SiteSelector::RuleLabel(rule.into()),
            SiteSelector::Path(vec![0]),
        ],
    )
    .unwrap();
    select(&discovery, SelectionPolicy::Each, 1)
        .unwrap()
        .fold(rule, |_| patch.clone())
        .unwrap()
}

/// The claim-free mutant of `patch`, as the campaign runner builds it (kink-patch
/// `ClaimSupport::withdraw`), with the claims it withdrew.
fn claim_free(validator: &NativeValidator, patch: &Patch) -> (ValidatedDefinition, usize) {
    let baseline = validator.baseline();
    let withdrawal = ClaimSupport::new(baseline)
        .withdraw(baseline, patch)
        .unwrap();
    assert!(withdrawal.trusted(), "{withdrawal:?}");
    let compiled = validator
        .validate(withdrawal.patch().unwrap_or(patch))
        .unwrap();
    (compiled, withdrawal.withdrawn.len())
}

/// The patch that replaces the only Int token `from` of `rule` by `to`.
fn token_patch(baseline: &Baseline, rule: &str, from: &str, to: &str) -> Patch {
    fn tokens(
        baseline: &Baseline,
        at: &kink_patch::SentenceRef,
        path: &mut Vec<u32>,
        token: &str,
    ) -> Vec<TermRef> {
        let here = TermRef::new(at.clone(), path.as_slice());
        let Some(term) = baseline.term(&here) else {
            return Vec::new();
        };
        let mut found = Vec::new();
        if matches!(term.unannotated(), Term::Token { token: t, .. } if t == token) {
            found.push(here);
        }
        for index in 0.. {
            path.push(index);
            if baseline
                .term(&TermRef::new(at.clone(), path.as_slice()))
                .is_none()
            {
                path.pop();
                break;
            }
            found.extend(tokens(baseline, at, path, token));
            path.pop();
        }
        found
    }
    let sentence = support::rule(baseline, rule);
    let [at] = (0..3)
        .flat_map(|part| tokens(baseline, &sentence, &mut vec![part], from))
        .collect::<Vec<_>>()
        .try_into()
        .unwrap_or_else(|found: Vec<_>| panic!("{rule}: {} tokens {from}", found.len()));
    Patch::new(vec![Edit::ReplaceTerm {
        expected: baseline.term(&at).unwrap().clone(),
        at,
        replacement: Term::Token {
            token: to.into(),
            sort: Sort::new("Int"),
        },
    }])
    .unwrap()
}

/// A state-set run with the mutants' work budget `max_work` (none: unbounded) and the rule on or
/// off.
const fn options(max_work: Option<u64>, one_sided: OneSided) -> RunOptions {
    RunOptions {
        result_modality: ResultModality::StateSet,
        work: match max_work {
            None => WorkBudget::Unbounded,
            Some(floor) => WorkBudget::Calibrated { factor: 0, floor },
        },
        one_sided,
    }
}

const ON: OneSided = OneSided::NoCrashClassifier;
const OFF: OneSided = OneSided::Off;

/// The campaign run, and the work of the mutant's run of `t` (its census).
fn run(
    campaign: &Campaign<'_>,
    generation: &CandidateGeneration<'_>,
    schedule: ScheduleMode,
    run: RunOptions,
) -> (CampaignRun, Option<u64>) {
    let mut session = BaselineSession::new(campaign.validator);
    let result = run_campaign_multi_with(
        campaign,
        std::slice::from_ref(generation),
        &CampaignOptions {
            schedule,
            selection: Sel::None,
            share_evidence: true,
            run,
            compile_workers: 1,
        },
        &mut session,
    )
    .unwrap();
    let work = session
        .last_call()
        .mutant_run(MutantId(0), "t")
        .and_then(|recording| recording.census.work);
    (result, work)
}

/// The test's run and status of the only mutant.
fn verdict(run: &CampaignRun) -> (TestRun, MutantStatus) {
    let [mutant] = run.mutants.as_slice() else {
        panic!("one mutant")
    };
    (mutant.plan.tests[0].run.clone(), mutant.report.status)
}

fn on_a_big_stack(work: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(work)
        .unwrap()
        .join()
        .unwrap();
}

/// The fixture's differential (A-15's test, as the IMP one in kink-flow `tests/one_sided.rs`):
/// for every mutant and every budget of `budgets(work)` (each below the mutant's work), each slot
/// is the unbounded run's outcome or `Unknown`, and a slot distinguishes only where the unbounded
/// run's distinguishes. The early mutant is killed one-sidedly from the first budget that lets it
/// finish the early branch on, budget 2. The kink tier runs the budgets 0, 2 and `work - 1`, the
/// heavy tier every budget below the work.
fn one_sided_kills_agree_with_the_unbounded_verdict(budgets: fn(u64) -> Vec<u64>) {
    on_a_big_stack(move || {
        let validator = validator();
        let tests = flow_slots();
        let campaign = campaign(&validator, &tests, &normal);
        let baseline = validator.baseline();
        let mut one_sided_kills = Vec::new();
        for (rule, from, to) in [
            ("ONESIDED.early", "7", "8"),
            ("ONESIDED.stop", "5", "6"),
            ("ONESIDED.late", "2", "3"),
        ] {
            let generation = replace(baseline, rule, from, to);
            let (unbounded, work) = run(
                &campaign,
                &generation,
                ScheduleMode::Full,
                options(None, ON),
            );
            let TestRun::Compared(reference) = verdict(&unbounded).0 else {
                panic!("{rule}: the unbounded run compares")
            };
            let work = work.expect("the mutant's work");
            for budget in budgets(work) {
                assert!(
                    budget < work,
                    "{rule}: budget {budget} below the work {work}"
                );
                let (on, _) = run(
                    &campaign,
                    &generation,
                    ScheduleMode::Full,
                    options(Some(budget), ON),
                );
                let TestRun::Compared(outcomes) = verdict(&on).0 else {
                    panic!("{rule} budget {budget}: compares")
                };
                for (slot, (outcome, expected)) in outcomes.iter().zip(&reference).enumerate() {
                    assert!(
                        outcome == expected || *outcome == Unknown,
                        "{rule} budget {budget} slot {slot}: {outcome:?} against {expected:?}"
                    );
                    if *outcome == Distinguish {
                        one_sided_kills.push((rule, budget, slot));
                    }
                }
            }
        }
        // Visiting start(10) and done(18) finishes the early branch: budgets 2 and up.
        assert!(
            one_sided_kills
                .iter()
                .all(|(rule, ..)| *rule == "ONESIDED.early")
        );
        assert_eq!(
            one_sided_kills
                .first()
                .map(|(_, budget, slot)| (*budget, *slot)),
            Some((2, 1))
        );
    });
}

/// The review's probes (re-pin L1-2-fix-1): the mutant, init's 7 becomes 6, and the unbounded
/// verdict of its run of `start(10)`, which does not compare, with the leaf that makes it so.
const PROBES: [(&str, &str, &str, Expected, &str); 2] = [
    // f(0) on the late branch: k-rust names the contradicted `total` of f, so the test is no
    // evidence (decision 2, per test).
    (
        "l12ct",
        "L12CT",
        "L12CT.init",
        Expected::Failed(ExecutionFailureKind::ContradictedClaim),
        "contradicted",
    ),
    // f(-1) on the late branch: no equation applies and k-rust names nothing, so the stuck
    // configuration done(f(-1)) is not a value and both slots are unknown.
    (
        "l12cs",
        "L12CS",
        "L12CS.init",
        Expected::Compared([Unknown, Unknown]),
        "not a value",
    ),
];

#[derive(Clone, Copy)]
enum Expected {
    Failed(ExecutionFailureKind),
    Compared([OracleOutcome; 2]),
}

impl Expected {
    fn run(self) -> TestRun {
        match self {
            Self::Failed(kind) => TestRun::Failed(kind),
            Self::Compared(outcomes) => TestRun::Compared(outcomes.to_vec()),
        }
    }
}

/// The differential beyond clean unbounded runs (L1-2 review minor 2): on the probes, whose
/// unbounded run does not compare, every budget of `budgets(work)` (each below the mutant's work)
/// gives `Unknown` on every slot or a one-sided `Distinguish`, and every one-sided kill is
/// explained: the unbounded run is unknown only because of a contradicted claim or a non-value
/// terminal on a leaf other than the killing one (`one_sided_support::explain_one_sided_kill`);
/// anything else fails the test. The kills are exactly the budgets from 3 on. The kink tier runs
/// the budgets 0, 3 (the first kill) and `work - 1`, the heavy tier every budget below the work.
fn one_sided_kills_beside_an_unclean_unbounded_run_are_explained(budgets: fn(u64) -> Vec<u64>) {
    on_a_big_stack(move || {
        for (name, module, rule, expected, _) in PROBES {
            let validator = validator_of(name, module);
            let tests = flow_slots();
            let campaign = campaign_of(module, &validator, &tests, &normal);
            let patch = token_patch(validator.baseline(), rule, "7", "6");
            let generation = replace(validator.baseline(), rule, "7", "6");
            let (compiled, _) = claim_free(&validator, &patch);
            let encoded = k_rust::kast::identifier::encode(module);
            let (unbounded, work) = run(
                &campaign,
                &generation,
                ScheduleMode::Full,
                options(None, ON),
            );
            let reference = verdict(&unbounded).0;
            assert_eq!(reference, expected.run(), "{name}");
            let work = work.expect("the mutant's work");
            let mut kills = Vec::new();
            let budgets = budgets(work);
            for &budget in &budgets {
                assert!(
                    budget < work,
                    "{name}: budget {budget} below the work {work}"
                );
                let (on, _) = run(
                    &campaign,
                    &generation,
                    ScheduleMode::Full,
                    options(Some(budget), ON),
                );
                let TestRun::Compared(outcomes) = verdict(&on).0 else {
                    panic!("{name} budget {budget}: compares")
                };
                for (slot, outcome) in outcomes.iter().enumerate() {
                    match outcome {
                        Unknown => {}
                        Distinguish => {
                            let explanation = one_sided_support::explain_one_sided_kill(
                                &compiled,
                                &encoded,
                                &initial(START),
                                BUDGET,
                                budget,
                                (&reference, slot),
                                &normal,
                            )
                            .unwrap_or_else(|why| {
                                panic!("{name} budget {budget} slot {slot}: unexplained: {why}")
                            });
                            eprintln!("{name} budget {budget} slot {slot}: {explanation:?}");
                            kills.push((budget, slot));
                        }
                        other => panic!("{name} budget {budget} slot {slot}: {other:?}"),
                    }
                }
            }
            // start(10), go(10, 6), done(16): the early branch is finished from budget 3 on, and
            // only the whole-term slot can see it (its exit stop is the baseline's).
            assert_eq!(
                kills,
                budgets
                    .iter()
                    .filter(|budget| (3..work).contains(budget))
                    .map(|budget| (*budget, 1))
                    .collect::<Vec<_>>(),
                "{name}"
            );
        }
    });
}

/// Every budget below the mutant's work: the full sweep.
fn every_budget(work: u64) -> Vec<u64> {
    (0..work).collect()
}

mod kink_tier {
    use super::*;

    #[test]
    #[ignore = "kink"]
    fn every_one_sided_kill_agrees_with_the_unbounded_verdict() {
        one_sided_kills_agree_with_the_unbounded_verdict(|work| vec![0, 1, 2, work - 1]);
    }

    #[test]
    #[ignore = "kink"]
    fn every_one_sided_kill_beside_an_unclean_unbounded_run_is_explained() {
        one_sided_kills_beside_an_unclean_unbounded_run_are_explained(|work| {
            vec![0, 2, 3, work - 1]
        });
    }

    /// early's 7 becomes 8: the early final configuration `done(18)` is not among the baseline's
    /// `{done(17), done(5)}`. Without a budget both runs are complete and the whole-term slot
    /// distinguishes. Under a budget smaller than the mutant's work, its run has finished the early
    /// branch and is cut in the loop: with the rule off the test is `Unknown`, with it on the
    /// whole-term slot distinguishes one-sidedly. The exit-stop slot stays `Unknown`: the leaf's exit
    /// stop (normal, no code) is the baseline's. The mutant's sides stay `Unknown`; only the outcome
    /// of the whole-term slot changes.
    #[test]
    #[ignore = "kink"]
    fn a_clean_ground_stuck_leaf_outside_the_baseline_set_kills_a_work_bound_mutant() {
        on_a_big_stack(|| {
            let validator = validator();
            let tests = flow_slots();
            let campaign = campaign(&validator, &tests, &normal);
            let generation = replace(validator.baseline(), "ONESIDED.early", "7", "8");
            for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
                let (unbounded, work) = run(&campaign, &generation, schedule, options(None, ON));
                assert_eq!(
                    verdict(&unbounded),
                    (
                        TestRun::Compared(vec![Agree, Distinguish]),
                        MutantStatus::Killed
                    )
                );
                let work = work.expect("the mutant's work");
                assert!(work > 2 * START as u64, "{work}");
                assert_eq!(
                    run(&campaign, &generation, schedule, options(None, OFF)).0,
                    unbounded
                );
                let budget = Some(work / 2);
                let (off, _) = run(&campaign, &generation, schedule, options(budget, OFF));
                assert_eq!(
                    verdict(&off),
                    (
                        TestRun::Compared(vec![Unknown, Unknown]),
                        MutantStatus::Unknown
                    )
                );
                let (on, _) = run(&campaign, &generation, schedule, options(budget, ON));
                assert_eq!(
                    verdict(&on),
                    (
                        TestRun::Compared(vec![Unknown, Distinguish]),
                        MutantStatus::Killed
                    )
                );
                assert_eq!(on.mutants[0].report.killing_test_ids, ["t"]);
                assert_eq!(
                    on.mutants[0].evidence[0].run,
                    SideRun::Sides {
                        sides: vec![OracleSide::Unknown, OracleSide::Unknown]
                    },
                    "the mutant's sides stay unknown"
                );
                // The baseline is never bounded, and the rule does not touch it.
                assert_eq!(on.baseline, unbounded.baseline);
            }
        });
    }

    /// A leaf inside the baseline's set kills nothing. stop's 5 becomes 6: only the late final
    /// configuration changes, so the explored early leaf `done(17)` is the baseline's, and a
    /// work-bound run is `Unknown` although the unbounded run distinguishes. late's 2 becomes 3: a
    /// longer loop to the same final configurations, so the mutant survives unbounded and is
    /// `Unknown`, never killed, under every budget.
    #[test]
    #[ignore = "kink"]
    fn a_leaf_in_the_baseline_set_kills_nothing() {
        on_a_big_stack(|| {
            let validator = validator();
            let tests = flow_slots();
            let campaign = campaign(&validator, &tests, &normal);
            let baseline = validator.baseline();
            for (rule, from, to, unbounded_expected) in [
                (
                    "ONESIDED.stop",
                    "5",
                    "6",
                    (
                        TestRun::Compared(vec![Agree, Distinguish]),
                        MutantStatus::Killed,
                    ),
                ),
                (
                    "ONESIDED.late",
                    "2",
                    "3",
                    (
                        TestRun::Compared(vec![Agree, Agree]),
                        MutantStatus::Survived,
                    ),
                ),
            ] {
                let generation = replace(baseline, rule, from, to);
                let (unbounded, work) = run(
                    &campaign,
                    &generation,
                    ScheduleMode::Full,
                    options(None, ON),
                );
                assert_eq!(verdict(&unbounded), unbounded_expected, "{rule}");
                let work = work.expect("the mutant's work");
                for budget in [1, 2, 3, work / 2, work - 1] {
                    let (on, _) = run(
                        &campaign,
                        &generation,
                        ScheduleMode::Full,
                        options(Some(budget), ON),
                    );
                    assert_eq!(
                        verdict(&on),
                        (
                            TestRun::Compared(vec![Unknown, Unknown]),
                            MutantStatus::Unknown
                        ),
                        "{rule} budget {budget}"
                    );
                }
            }
        });
    }

    /// The per-path principle on the review's probes (Sebastien, 2026-10-17, "Land per-path, on";
    /// re-pin L1-2-fix-1). The mutant's claim-free definition keeps f's false `total` (the edit is
    /// in a rewrite rule, which removes no claim of f). Unbounded, the two-sided per-test rule makes
    /// the test unknown: l12ct's late branch contradicts the claim (the test is no evidence), l12cs's
    /// ends in done(f(-1)), which is not a value. Under the work budgets 14, 7 and 3 (the mutant's
    /// work is 15) the run has finished the early branch, done(16), which the baseline's complete set
    /// lacks, and the rule kills one-sidedly in both schedules; with it off the test is `Unknown`, as
    /// at budget 2, where done(16) is not yet reached. The killing leaf's own path carries no
    /// contradiction: it is a clean stuck leaf of the unbounded run, distinct from the late branch's
    /// offending leaf, which is the only one. So the two-sided per-test rule is the conservative one
    /// here: a budget gives `Killed` where the unbounded run gives `Unknown`.
    #[test]
    #[ignore = "kink"]
    fn a_contradiction_on_another_path_does_not_void_the_killing_leaf() {
        on_a_big_stack(|| {
            for (name, module, rule, expected, offence) in PROBES {
                let validator = validator_of(name, module);
                let tests = flow_slots();
                let campaign = campaign_of(module, &validator, &tests, &normal);
                let patch = token_patch(validator.baseline(), rule, "7", "6");
                let generation = replace(validator.baseline(), rule, "7", "6");
                let (compiled, withdrawn) = claim_free(&validator, &patch);
                assert_eq!(withdrawn, 0, "{name}: f keeps its `total`");
                for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
                    let (unbounded, work) =
                        run(&campaign, &generation, schedule, options(None, ON));
                    assert_eq!(
                        verdict(&unbounded),
                        (expected.run(), MutantStatus::Unknown),
                        "{name}"
                    );
                    assert_eq!(work, Some(15), "{name}");
                    assert_eq!(
                        run(&campaign, &generation, schedule, options(None, OFF)).0,
                        unbounded
                    );
                    for budget in [14, 7, 3] {
                        let (on, _) =
                            run(&campaign, &generation, schedule, options(Some(budget), ON));
                        assert_eq!(
                            verdict(&on),
                            (
                                TestRun::Compared(vec![Unknown, Distinguish]),
                                MutantStatus::Killed
                            ),
                            "{name} budget {budget}"
                        );
                        assert_eq!(
                            on.mutants[0].evidence[0].run,
                            SideRun::Sides {
                                sides: vec![OracleSide::Unknown, OracleSide::Unknown]
                            },
                            "{name} budget {budget}: the mutant's sides stay unknown"
                        );
                        assert_eq!(on.baseline, unbounded.baseline);
                        let (off, _) =
                            run(&campaign, &generation, schedule, options(Some(budget), OFF));
                        assert_eq!(
                            verdict(&off),
                            (
                                TestRun::Compared(vec![Unknown, Unknown]),
                                MutantStatus::Unknown
                            ),
                            "{name} budget {budget} off"
                        );
                    }
                    let (early, _) = run(&campaign, &generation, schedule, options(Some(2), ON));
                    assert_eq!(
                        verdict(&early),
                        (
                            TestRun::Compared(vec![Unknown, Unknown]),
                            MutantStatus::Unknown
                        ),
                        "{name} budget 2"
                    );
                }
                let encoded = k_rust::kast::identifier::encode(module);
                for budget in [14, 7, 3] {
                    let explanation = one_sided_support::explain_one_sided_kill(
                        &compiled,
                        &encoded,
                        &initial(START),
                        BUDGET,
                        budget,
                        (&expected.run(), 1),
                        &normal,
                    )
                    .unwrap_or_else(|why| panic!("{name} budget {budget}: {why}"));
                    let [offender] = explanation.offenders.as_slice() else {
                        panic!("{name}: one offending leaf: {explanation:?}")
                    };
                    assert!(offender.contains(offence), "{name}: {offender}");
                    let [killing] = explanation.killing.as_slice() else {
                        panic!("{name}: one killing leaf: {explanation:?}")
                    };
                    assert!(!offender.starts_with(&format!("{killing} ")), "{name}");
                }
            }
        });
    }

    /// fz26 KINK-PATHSET-FALLBACK: the rule on a work-bound state set that holds an undefined step
    /// (`testdata/k/stateset/onesidedz.k`, START = 10; the baseline's complete run holds the
    /// undefined step at `zm(10)`, which is no end, kink27 R1-UNDEF). With early's 7 made 8 the run, cut in the loop, holds
    /// the clean leaf `done(18)` the baseline lacks beside the `Trivial` leaf, and kills
    /// one-sidedly, as its unbounded run kills. With zc's 0 made 1 the cut run holds the clean
    /// `done(111)` the baseline lacks, but the undefined step `td(11)` on another explored path
    /// contradicts td's `total` (a leaf contradiction, and a record on the run's list, which every
    /// leaf of a work-bound run also carries): the run is excluded, so the fact voids the kill and
    /// the test is `Unknown`, as the unbounded run is.
    #[test]
    #[ignore = "kink"]
    fn a_work_bound_state_set_with_an_undefined_step_kills_one_sidedly_unless_a_fact_voids_it() {
        on_a_big_stack(|| {
            let validator = NativeValidator::bind(
                support::load_path(
                    &Path::new(support::DIR).join("stateset/onesidedz.k"),
                    "ONESIDEDZ",
                ),
                CompileOptions::default(),
            );
            let tests = flow_slots();
            let campaign = campaign_of("ONESIDEDZ", &validator, &tests, &normal);
            let baseline = validator.baseline();
            for (rule, from, to, unbounded_expected, bounded_expected) in [
                (
                    "ONESIDEDZ.early",
                    "7",
                    "8",
                    (
                        TestRun::Compared(vec![Agree, Distinguish]),
                        MutantStatus::Killed,
                    ),
                    (
                        TestRun::Compared(vec![Unknown, Distinguish]),
                        MutantStatus::Killed,
                    ),
                ),
                (
                    "ONESIDEDZ.zc",
                    "0",
                    "1",
                    (
                        TestRun::Failed(ExecutionFailureKind::ContradictedClaim),
                        MutantStatus::Unknown,
                    ),
                    (
                        TestRun::Failed(ExecutionFailureKind::ContradictedClaim),
                        MutantStatus::Unknown,
                    ),
                ),
            ] {
                let generation = replace(baseline, rule, from, to);
                let (unbounded, work) = run(
                    &campaign,
                    &generation,
                    ScheduleMode::Full,
                    options(None, ON),
                );
                assert_eq!(verdict(&unbounded), unbounded_expected, "{rule}");
                let work = work.expect("the mutant's work");
                // The loop counts 40 steps down, after every other branch: 10 short of the work
                // cuts it there.
                let budget = work - 10;
                let (on, _) = run(
                    &campaign,
                    &generation,
                    ScheduleMode::Full,
                    options(Some(budget), ON),
                );
                assert_eq!(verdict(&on), bounded_expected, "{rule} budget {budget}");
                assert_eq!(
                    on.mutants[0].evidence[0].notes.leaf_contradiction,
                    rule == "ONESIDEDZ.zc",
                    "{rule}"
                );
            }
        });
    }

    /// The rule's other conditions, each pinned by a slot or a classifier that breaks it, with the
    /// early mutant under half its work.
    /// - A term-path slot: a projection that can fail on an unexplored configuration is refused
    ///   (the unbounded run distinguishes on it).
    /// - A classifier that calls the early leaf `done(18)` a crash: the explored crash refuses the
    ///   rule, and the unbounded mutant's set mixes a crash with a normal terminal, which the state
    ///   slot does not compare (`Unknown`).
    #[test]
    #[ignore = "kink"]
    fn the_rule_needs_a_total_projection_and_no_crash() {
        on_a_big_stack(|| {
            let validator = validator();
            let baseline = validator.baseline();
            let generation = replace(baseline, "ONESIDED.early", "7", "8");

            // The path to `done(_)` in a final configuration of the baseline.
            let compiled = validator.compile_baseline().unwrap();
            let mut backend = k_rust::backend::Backend::from_definition(
                k_rust::kore::parser::parse_definition(&compiled.artifacts().definition_kore)
                    .unwrap(),
                "ONESIDED",
                k_rust::backend::BackendOptions::default(),
            )
            .unwrap();
            let execution = kink_native::execution::ExecutionAdapter::with_profile(
                kink_native::execution::SolverProfile::BUILD,
            )
            .execute(&mut backend, &initial(START), BUDGET)
            .unwrap();
            let state: Pattern =
                k_rust::kore::codec::from_value(&execution.leaves()[0].branch.state).unwrap();
            let done = path_to(&state, "Lbldone").expect("a done(_) subterm");
            let tests = test(vec![StateProjection::TermPaths(vec![done])]);
            let term_paths = campaign(&validator, &tests, &normal);
            let (unbounded, work) = run(
                &term_paths,
                &generation,
                ScheduleMode::Full,
                options(None, ON),
            );
            assert_eq!(
                verdict(&unbounded),
                (TestRun::Compared(vec![Distinguish]), MutantStatus::Killed)
            );
            let (on, _) = run(
                &term_paths,
                &generation,
                ScheduleMode::Full,
                options(work.map(|work| work / 2), ON),
            );
            assert_eq!(
                verdict(&on),
                (TestRun::Compared(vec![Unknown]), MutantStatus::Unknown)
            );

            let crash_18 = |term: &Pattern| {
                if argument_of(term, "Lbldone").as_deref() == Some("18") {
                    ExecutionTerminalKind::SemanticCrash
                } else {
                    ExecutionTerminalKind::Normal
                }
            };
            let tests = flow_slots();
            let campaign = campaign(&validator, &tests, &crash_18);
            let (unbounded, work) = run(
                &campaign,
                &generation,
                ScheduleMode::Full,
                options(None, ON),
            );
            assert_eq!(
                verdict(&unbounded),
                (
                    TestRun::Compared(vec![Unknown, Unknown]),
                    MutantStatus::Unknown
                )
            );
            let (on, _) = run(
                &campaign,
                &generation,
                ScheduleMode::Full,
                options(work.map(|work| work / 2), ON),
            );
            assert_eq!(
                verdict(&on),
                (
                    TestRun::Compared(vec![Unknown, Unknown]),
                    MutantStatus::Unknown
                )
            );
        });
    }
}

mod heavy {
    use super::*;

    #[test]
    #[ignore = "heavy"]
    fn every_one_sided_kill_agrees_with_the_unbounded_verdict() {
        one_sided_kills_agree_with_the_unbounded_verdict(every_budget);
    }

    #[test]
    #[ignore = "heavy"]
    fn every_one_sided_kill_beside_an_unclean_unbounded_run_is_explained() {
        one_sided_kills_beside_an_unclean_unbounded_run_are_explained(every_budget);
    }
}
