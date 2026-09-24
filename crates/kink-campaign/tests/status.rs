//! Mutant status, schedule, score and baseline-admission truth tables.
//!
//! The rows are transcribed from the former vector files
//! (`mutation-status-vectors.json`, the `campaignCases` and
//! `oracleTerminalCases` of `mutation-vectors.json`, and
//! `cross-feature-vectors.json`), which no longer exist in the tree. Row IDs
//! are kept verbatim. Rows the current API cannot express are left out and
//! named in the commit that added this file. Crash sides are terminal terms,
//! so the four crash-versus-crash `oracleTerminalCases` rows are in the
//! terminal table. Tables marked Rust-only have no source vector.

#[path = "../../../testdata/k/support.rs"]
mod support;

use k_rust::kompile::initial_configuration::kore_application;
use k_rust::kore::ast::Pattern;
use kink_campaign::{
    BaselineAdmission, CampaignFailureKind, CrashPolicy, ExecutionFailureKind, ExitStop,
    FinalResult, ManifestTest, MutantId, MutantPlan, MutantReport, MutantScopeFailure,
    MutantStatus, OracleKind, OracleOutcome, OracleSide, OracleValue, PatternValue, Rational,
    ScheduleMode, Score, TerminalClass, TestPlan, TestRun, compare_supplied, derive_mutant_report,
    score, validate_baseline,
};
use kink_patch::{
    CandidateDisposition, Edit, Patch, SelectionPolicy, SiteSelector, TermRef, derive_sites, select,
};

use MutantStatus::{Error, Invalid, Killed, Survived, Timeout, Unknown};
use OracleOutcome::{Agree, Distinguish, Skipped};

const KINDS: [OracleKind; 3] = [
    OracleKind::ExitStop,
    OracleKind::FinalResult,
    OracleKind::ExecutionPattern,
];

/// The constant term `name`.
fn term(name: &str) -> Pattern {
    kore_application(&format!("Lbl{name}"), Vec::new(), Vec::new())
}

/// A complete value of `kind`; equal tags give equal values, and `'a'` and `'b'` differ.
fn value(kind: OracleKind, tag: char) -> OracleValue {
    match kind {
        OracleKind::ExitStop => OracleValue::ExitStop(
            [ExitStop {
                class: TerminalClass::Normal,
                code: Some(i64::from(u32::from(tag))),
            }]
            .into(),
        ),
        OracleKind::FinalResult => {
            OracleValue::FinalResult(FinalResult::WholeTerm([term(&tag.to_string())].into()))
        }
        OracleKind::ExecutionPattern => OracleValue::Pattern(if tag == 'a' {
            PatternValue::Match { bindings: None }
        } else {
            PatternValue::NoMatch
        }),
    }
}

fn compared(id: &str, outcomes: &[OracleOutcome]) -> TestPlan {
    TestPlan {
        test_id: id.to_owned(),
        run: TestRun::Compared(outcomes.to_vec()),
    }
}

fn one_test(outcomes: &[OracleOutcome]) -> Vec<TestPlan> {
    vec![compared("t1", outcomes)]
}

/// A valid mutant's plan over `tests`.
fn plan(tests: Vec<TestPlan>) -> MutantPlan {
    MutantPlan {
        mutant_id: MutantId(0),
        tests,
        mutant_failure: None,
    }
}

/// A manifest of `(test id, declared slot count)` pairs.
fn manifest(tests: &[(&str, usize)]) -> Vec<ManifestTest> {
    tests
        .iter()
        .map(|(id, slot_count)| ManifestTest {
            test_id: (*id).to_owned(),
            slot_count: *slot_count,
        })
        .collect()
}

/// The manifest a well-formed plan was built against; a failed test declares
/// one slot.
fn manifest_of(plan: &MutantPlan) -> Vec<ManifestTest> {
    plan.tests
        .iter()
        .map(|test| ManifestTest {
            test_id: test.test_id.clone(),
            slot_count: match &test.run {
                TestRun::Compared(outcomes) => outcomes.len(),
                TestRun::Failed(_) => 1,
            },
        })
        .collect()
}

fn report(plan: &MutantPlan, manifest: &[ManifestTest], schedule: ScheduleMode) -> MutantReport {
    derive_mutant_report(plan, manifest, schedule).expect("plan derives a report")
}

fn ratio(numerator: u64, denominator: u64) -> Option<Rational> {
    Some(Rational {
        numerator,
        denominator,
    })
}

/// What the source row's single test `t1` produced, if the mutant reached it.
#[derive(Clone, Copy, Debug)]
enum Run {
    /// Every slot was compared.
    Compared(&'static [OracleOutcome]),
    /// The mutant run failed; the source row marks the remaining slot
    /// `skipped`, which Rust reserves for the scheduler.
    Failed(ExecutionFailureKind),
    /// A mutant-scope failure stopped the mutant before execution.
    NotExecuted,
}

/// (id, mutant-scope failure, t1 run, status, excluded bucket)
type StatusRow = (
    &'static str,
    Option<MutantScopeFailure>,
    Run,
    MutantStatus,
    Option<MutantStatus>,
);

/// C1: mutant status is a total function of the mutant-scope failure and the
/// per-test runs, and only killed and survived enter the score.
///
/// The source rows put the lowering time and resource limits on a selected
/// test with a `mutant-execution` failure; here they are mutant-scope failures,
/// so `t1` is skipped rather than executed. The taxonomy gives both contexts
/// the same disposition, so the status is unchanged. The source row
/// `infrastructure-failure-is-error` has validation outcome `error`, which is
/// the mutant-scope `Infrastructure` failure.
#[test]
fn mutant_status_is_derived_from_validation_then_oracle_outcomes() {
    use ExecutionFailureKind as E;
    use MutantScopeFailure as S;
    use OracleOutcome as O;
    use Run::{Compared, Failed, NotExecuted};
    #[rustfmt::skip]
    let rows: [StatusRow; 10] = [
        ("ordinary-result-kill", None, Compared(&[O::Distinguish, O::Agree]), Killed, None),
        ("complete-survival", None, Compared(&[O::Agree, O::Agree]), Survived, None),
        ("ill-sorted-invalid", Some(S::Rejected), NotExecuted, Invalid, Some(Invalid)),
        ("lowering-nontermination-is-invalid", Some(S::LoweringNontermination), NotExecuted, Invalid, Some(Invalid)),
        ("lowering-time-limit-is-timeout", Some(S::LoweringTimeLimit), NotExecuted, Timeout, Some(Timeout)),
        ("lowering-resource-limit-is-unknown", Some(S::LoweringResourceLimit), NotExecuted, Unknown, Some(Unknown)),
        ("time-limit-is-timeout", None, Failed(E::TimeLimit), Timeout, Some(Timeout)),
        ("solver-indeterminate-is-unknown", None, Failed(E::Indeterminate), Unknown, Some(Unknown)),
        ("infrastructure-failure-is-error", Some(S::Infrastructure), NotExecuted, Error, Some(Error)),
        ("bounded-agreement-is-survived-not-equivalent", None, Compared(&[O::Agree, O::Agree]), Survived, None),
    ];
    let declared = manifest(&[("t1", 2)]);
    for (id, mutant_failure, run, expected, excluded) in rows {
        let tests = match run {
            Compared(outcomes) => one_test(outcomes),
            Failed(kind) => vec![TestPlan {
                test_id: "t1".to_owned(),
                run: TestRun::Failed(kind),
            }],
            NotExecuted => Vec::new(),
        };
        let plan = MutantPlan {
            mutant_failure,
            ..plan(tests)
        };
        for schedule in [ScheduleMode::FirstKill, ScheduleMode::Full] {
            let actual = report(&plan, &declared, schedule);
            assert_eq!(actual.status, expected, "{id} under {schedule:?}");
            let executed: &[&str] = if matches!(run, NotExecuted) {
                &[]
            } else {
                &["t1"]
            };
            assert_eq!(
                actual.executed_test_ids, executed,
                "{id} under {schedule:?}"
            );
            let counted = score(&[actual.status]);
            assert_eq!(counted.killed, u64::from(actual.status == Killed), "{id}");
            assert_eq!(
                counted.survived,
                u64::from(actual.status == Survived),
                "{id}"
            );
            assert_eq!(
                (counted.denominator == 0).then_some(actual.status),
                excluded,
                "{id}: excluded bucket"
            );
        }
    }
}

/// C1 `statusContradictionCases`: a kill never survives a mutant-scope
/// failure, and no conclusive status can be supplied as one.
///
/// The source row paired a validation rejection with a kill and expected
/// `Invalid`. A rejected mutant never ran, so that plan is now refused as
/// inconsistent; `Invalid` is what the rejection alone derives. A failure that
/// can follow execution (`Infrastructure`) still decides the status over a
/// kill.
///
/// The three failure-classification rows of `statusContradictionCases`
/// (`lowering-time-limit-cannot-be-unknown`,
/// `lowering-resource-limit-cannot-be-timeout` and
/// `lowering-nontermination-cannot-be-timeout`) are unrepresentable: each
/// paired a failure with a slot outcome reporting a different one, but a
/// failed test carries no slots and a mutant-scope failure is not a slot.
#[test]
fn killed_cannot_fail_validation() {
    let declared = manifest(&[("t1", 2)]);
    let with_failure = |failure, tests| MutantPlan {
        mutant_failure: Some(failure),
        ..plan(tests)
    };
    let killed = with_failure(
        MutantScopeFailure::Rejected,
        one_test(&[Distinguish, Agree]),
    );
    let rejected = with_failure(MutantScopeFailure::Rejected, Vec::new());
    let corrupted = with_failure(
        MutantScopeFailure::Infrastructure,
        one_test(&[Distinguish, Agree]),
    );
    for schedule in [ScheduleMode::FirstKill, ScheduleMode::Full] {
        assert_eq!(
            derive_mutant_report(&killed, &declared, schedule)
                .expect_err("a rejected mutant cannot carry a kill")
                .kind(),
            CampaignFailureKind::InvalidManifest,
            "{schedule:?}"
        );
        let actual = report(&rejected, &declared, schedule);
        assert_eq!(actual.status, Invalid, "{schedule:?}");
        assert!(actual.killing_test_ids.is_empty(), "{schedule:?}");
        let actual = report(&corrupted, &declared, schedule);
        assert_eq!(actual.status, Error, "{schedule:?}");
        assert!(actual.killing_test_ids.is_empty(), "{schedule:?}");
    }
}

/// One row per failure-kind `status` arm. A mutant-scope failure decides the
/// status, even over a kill; only `Infrastructure` may follow executed tests,
/// and any other kind beside them is rejected as inconsistent. A failed test
/// contributes its status to the fold, so it never survives and never
/// overrides a kill in another test.
#[test]
fn every_failure_kind_maps_to_one_status() {
    use ExecutionFailureKind as E;
    use MutantScopeFailure as S;
    let scope_rows = [
        (S::Rejected, Invalid),
        (S::LoweringNontermination, Invalid),
        (S::LoweringTimeLimit, Timeout),
        (S::LoweringResourceLimit, Unknown),
        (S::Infrastructure, Error),
    ];
    let execution_rows = [
        (E::Indeterminate, Unknown),
        (E::ResourceLimit, Unknown),
        (E::TimeLimit, Timeout),
        (E::Infrastructure, Error),
    ];
    let declared = manifest(&[("t1", 2)]);
    for schedule in [ScheduleMode::FirstKill, ScheduleMode::Full] {
        for (kind, expected) in scope_rows {
            assert_eq!(kind.status(), expected, "{kind:?}");
            for tests in [
                Vec::new(),
                one_test(&[Distinguish, Agree]),
                one_test(&[Agree, Agree]),
            ] {
                let executed = !tests.is_empty();
                let derived = derive_mutant_report(
                    &MutantPlan {
                        mutant_failure: Some(kind),
                        ..plan(tests)
                    },
                    &declared,
                    schedule,
                );
                if executed && kind != S::Infrastructure {
                    assert_eq!(
                        derived.expect_err("no test ran").kind(),
                        CampaignFailureKind::InvalidManifest,
                        "{kind:?} under {schedule:?}"
                    );
                    continue;
                }
                let actual = derived.expect("plan derives a report");
                assert_eq!(actual.status, expected, "{kind:?} under {schedule:?}");
                assert!(
                    actual.killing_test_ids.is_empty(),
                    "{kind:?} under {schedule:?}"
                );
            }
        }
        for (kind, expected) in execution_rows {
            assert_eq!(kind.status(), expected, "{kind:?}");
            let failed = TestPlan {
                test_id: "t1".to_owned(),
                run: TestRun::Failed(kind),
            };
            let alone = plan(vec![failed.clone(), compared("t2", &[Agree])]);
            let actual = report(&alone, &manifest_of(&alone), schedule);
            assert_eq!(
                actual.status, expected,
                "{kind:?} beside agreement under {schedule:?}"
            );
            let killed = plan(vec![failed, compared("t2", &[Distinguish])]);
            let actual = report(&killed, &manifest_of(&killed), schedule);
            assert_eq!(
                actual.status, Killed,
                "{kind:?}: a kill takes precedence under {schedule:?}"
            );
        }
    }
}

/// One test's run in a fold-order row.
#[derive(Clone, Copy, Debug)]
enum Fold {
    C(&'static [OracleOutcome]),
    F(ExecutionFailureKind),
}

/// (id, mutant-scope failure, tests, status, killing tests under full,
/// executed tests under first-kill)
type FoldRow = (
    &'static str,
    Option<MutantScopeFailure>,
    &'static [(&'static str, Fold)],
    MutantStatus,
    &'static [&'static str],
    &'static [&'static str],
);

/// Rust-only: the single fold precedence is mutant-scope failure, then kill,
/// then error (including incomparable), timeout and unknown, then survival,
/// within a test and across tests alike.
#[test]
fn inconclusive_outcomes_fold_error_then_timeout_then_unknown() {
    use ExecutionFailureKind as E;
    use Fold::{C, F};
    use OracleOutcome as O;
    #[rustfmt::skip]
    let rows: [FoldRow; 17] = [
        ("timeout-over-unknown", None, &[("t1", C(&[O::Timeout, O::Unknown]))], Timeout, &[], &["t1"]),
        ("error-over-unknown", None, &[("t1", C(&[O::Unknown, O::Error]))], Error, &[], &["t1"]),
        ("error-over-timeout", None, &[("t1", C(&[O::Timeout, O::Error]))], Error, &[], &["t1"]),
        ("agree-does-not-mask", None, &[("t1", C(&[O::Agree, O::Unknown]))], Unknown, &[], &["t1"]),
        ("incomparable-is-error", None, &[("t1", C(&[O::Incomparable]))], Error, &[], &["t1"]),
        ("incomparable-over-timeout", None, &[("t1", C(&[O::Incomparable, O::Timeout]))], Error, &[], &["t1"]),
        ("fold-across-tests", None, &[("t1", C(&[O::Unknown])), ("t2", C(&[O::Timeout]))], Timeout, &[], &["t1", "t2"]),
        ("error-in-one-test", None, &[("t1", C(&[O::Error])), ("t2", C(&[O::Agree]))], Error, &[], &["t1", "t2"]),
        ("kill-after-inconclusive", None, &[("t1", C(&[O::Timeout])), ("t2", C(&[O::Distinguish]))], Killed, &["t2"], &["t1", "t2"]),
        ("kill-beats-error-in-same-test", None, &[("t1", C(&[O::Distinguish, O::Error]))], Killed, &["t1"], &["t1"]),
        ("kill-after-incomparable", None, &[("t1", C(&[O::Incomparable])), ("t2", C(&[O::Distinguish])), ("t3", C(&[O::Agree]))], Killed, &["t2"], &["t1", "t2"]),
        ("failed-resource-limit-beside-timeout-slot", None, &[("t1", F(E::ResourceLimit)), ("t2", C(&[O::Timeout]))], Timeout, &[], &["t1", "t2"]),
        ("failed-time-limit-beside-error-slot", None, &[("t1", F(E::TimeLimit)), ("t2", C(&[O::Error]))], Error, &[], &["t1", "t2"]),
        ("failed-infrastructure-then-kill", None, &[("t1", F(E::Infrastructure)), ("t2", C(&[O::Distinguish]))], Killed, &["t2"], &["t1", "t2"]),
        ("every-test-failed", None, &[("t1", F(E::TimeLimit)), ("t2", F(E::Indeterminate))], Timeout, &[], &["t1", "t2"]),
        ("failed-test-beside-agreement", None, &[("t1", F(E::ResourceLimit)), ("t2", C(&[O::Agree]))], Unknown, &[], &["t1", "t2"]),
        ("mutant-failure-beats-kill", Some(MutantScopeFailure::Infrastructure), &[("t1", C(&[O::Distinguish])), ("t2", C(&[O::Agree]))], Error, &[], &["t1"]),
    ];
    for (id, mutant_failure, tests, expected, killing, first_kill_executed) in rows {
        let plan = MutantPlan {
            mutant_failure,
            ..plan(
                tests
                    .iter()
                    .map(|(test_id, run)| TestPlan {
                        test_id: (*test_id).to_owned(),
                        run: match run {
                            C(outcomes) => TestRun::Compared(outcomes.to_vec()),
                            F(kind) => TestRun::Failed(*kind),
                        },
                    })
                    .collect(),
            )
        };
        let declared = manifest_of(&plan);
        let all = tests
            .iter()
            .map(|(test_id, _)| *test_id)
            .collect::<Vec<_>>();
        let full = report(&plan, &declared, ScheduleMode::Full);
        assert_eq!(full.status, expected, "{id} under Full");
        assert_eq!(full.executed_test_ids, all, "{id} under Full");
        assert_eq!(full.killing_test_ids, killing, "{id} under Full");
        assert!(full.skipped_test_ids.is_empty(), "{id} under Full");
        let first_kill = report(&plan, &declared, ScheduleMode::FirstKill);
        assert_eq!(first_kill.status, expected, "{id} under FirstKill");
        assert_eq!(
            first_kill.executed_test_ids, first_kill_executed,
            "{id} under FirstKill"
        );
        assert_eq!(
            first_kill.killing_test_ids,
            &killing[..killing.len().min(1)],
            "{id} under FirstKill"
        );
        assert_eq!(
            first_kill.skipped_test_ids,
            &all[first_kill_executed.len()..],
            "{id} under FirstKill"
        );
    }
}

/// (id, mutant-scope failure, tests, manifest, rejection)
type RejectionRow = (
    &'static str,
    Option<MutantScopeFailure>,
    Vec<TestPlan>,
    &'static [(&'static str, usize)],
    CampaignFailureKind,
);

/// Rust-only: a plan must match the selected-test manifest exactly, so no
/// omitted test or slot can let an inconclusive mutant survive, and a mutant
/// rejected or not lowered cannot carry executed tests.
#[test]
fn plans_that_differ_from_the_manifest_are_rejected() {
    use CampaignFailureKind::{FabricatedSkip, InvalidManifest};
    use ExecutionFailureKind as E;
    use MutantScopeFailure as S;
    use OracleOutcome as O;
    let agree = |id| compared(id, &[Agree]);
    let failed = |id: &str, kind| TestPlan {
        test_id: id.to_owned(),
        run: TestRun::Failed(kind),
    };
    let t1_t2: &[(&str, usize)] = &[("t1", 1), ("t2", 1)];
    #[rustfmt::skip]
    let rows: [RejectionRow; 16] = [
        ("missing-test", None, vec![agree("t1")], t1_t2, InvalidManifest),
        ("extra-test", None, vec![agree("t1"), agree("t2")], &[("t1", 1)], InvalidManifest),
        ("reordered-tests", None, vec![agree("t2"), agree("t1")], t1_t2, InvalidManifest),
        ("fewer-slots", None, vec![agree("t1")], &[("t1", 2)], InvalidManifest),
        ("more-slots", None, vec![compared("t1", &[Agree, Agree])], &[("t1", 1)], InvalidManifest),
        ("no-tests-without-mutant-failure", None, Vec::new(), &[("t1", 1)], InvalidManifest),
        ("partial-tests-with-mutant-failure", Some(MutantScopeFailure::Infrastructure), vec![agree("t1")], t1_t2, InvalidManifest),
        ("empty-manifest", Some(MutantScopeFailure::Rejected), Vec::new(), &[], InvalidManifest),
        ("duplicate-manifest-test", None, vec![agree("t1"), agree("t1")], &[("t1", 1), ("t1", 1)], InvalidManifest),
        ("manifest-test-without-slots", Some(MutantScopeFailure::Rejected), Vec::new(), &[("t1", 0)], InvalidManifest),
        ("fabricated-skip", None, vec![compared("t1", &[O::Timeout, Skipped])], &[("t1", 2)], FabricatedSkip),
        ("rejected-with-executed-tests", Some(S::Rejected), vec![agree("t1"), agree("t2")], t1_t2, InvalidManifest),
        ("rejected-with-failed-test", Some(S::Rejected), vec![failed("t1", E::Infrastructure), agree("t2")], t1_t2, InvalidManifest),
        ("lowering-nontermination-with-kill", Some(S::LoweringNontermination), vec![compared("t1", &[Distinguish]), agree("t2")], t1_t2, InvalidManifest),
        ("lowering-time-limit-with-failed-test", Some(S::LoweringTimeLimit), vec![failed("t1", E::TimeLimit), agree("t2")], t1_t2, InvalidManifest),
        ("lowering-resource-limit-with-executed-tests", Some(S::LoweringResourceLimit), vec![agree("t1"), failed("t2", E::ResourceLimit)], t1_t2, InvalidManifest),
    ];
    for (id, mutant_failure, tests, declared, expected) in rows {
        let plan = MutantPlan {
            mutant_failure,
            ..plan(tests)
        };
        for schedule in [ScheduleMode::FirstKill, ScheduleMode::Full] {
            assert_eq!(
                derive_mutant_report(&plan, &manifest(declared), schedule)
                    .expect_err("the plan is rejected")
                    .kind(),
                expected,
                "{id} under {schedule:?}"
            );
        }
    }
}

/// (schedule, executed, killing, skipped)
type ScheduleRow = (
    ScheduleMode,
    &'static [&'static str],
    &'static [&'static str],
    &'static [&'static str],
);

/// C2: first-kill runs the manifest-order prefix through the first kill and
/// skips the rest, full runs everything, and both agree on the status.
#[test]
fn first_kill_and_full_schedules_agree_on_status() {
    // `scheduleCases` first-kill/full and `campaignCases` first-kill-and-full-agree
    // share this manifest.
    let plan = plan(vec![
        compared("t1", &[Agree]),
        compared("t2", &[Distinguish]),
        compared("t3", &[Distinguish]),
    ]);
    let rows: [ScheduleRow; 2] = [
        (ScheduleMode::FirstKill, &["t1", "t2"], &["t2"], &["t3"]),
        (ScheduleMode::Full, &["t1", "t2", "t3"], &["t2", "t3"], &[]),
    ];
    for (schedule, executed, killing, skipped) in rows {
        let actual = report(&plan, &manifest_of(&plan), schedule);
        assert_eq!(actual.status, Killed, "{schedule:?}");
        assert_eq!(actual.executed_test_ids, executed, "{schedule:?}");
        assert_eq!(actual.killing_test_ids, killing, "{schedule:?}");
        assert_eq!(actual.skipped_test_ids, skipped, "{schedule:?}");
    }
}

/// C3: the score is the exact reduced killed/(killed+survived), and every
/// excluded status leaves it unchanged. `Score` has no exclusion buckets; the
/// duplicate and no-change buckets are candidate dispositions that never
/// become a `MutantStatus` (see S5).
#[test]
fn score_is_exact_and_excluded_statuses_do_not_count() {
    // `scoreCases`
    let rows: [(&[MutantStatus], Score); 3] = [
        (
            &[],
            Score {
                killed: 0,
                survived: 0,
                denominator: 0,
                ratio: None,
            },
        ),
        (
            &[Killed, Survived],
            Score {
                killed: 1,
                survived: 1,
                denominator: 2,
                ratio: ratio(1, 2),
            },
        ),
        (
            &[Killed, Survived, Survived],
            Score {
                killed: 1,
                survived: 2,
                denominator: 3,
                ratio: ratio(1, 3),
            },
        ),
    ];
    for (statuses, expected) in rows {
        assert_eq!(score(statuses), expected, "{statuses:?}");
        let mut padded = statuses.to_vec();
        padded.extend([Invalid, Timeout, Unknown, Error]);
        assert_eq!(score(&padded), expected, "{statuses:?} with exclusions");
    }
}

/// A plan over the one-slot manifest `t1` whose outcome folds to `status`.
fn plan_for(status: MutantStatus, id: usize) -> MutantPlan {
    let outcome = match status {
        Killed => Distinguish,
        Survived => Agree,
        Timeout => OracleOutcome::Timeout,
        Unknown => OracleOutcome::Unknown,
        Error => OracleOutcome::Error,
        Invalid => {
            return MutantPlan {
                mutant_id: MutantId(id),
                tests: Vec::new(),
                mutant_failure: Some(MutantScopeFailure::Rejected),
            };
        }
    };
    MutantPlan {
        mutant_id: MutantId(id),
        ..plan(one_test(&[outcome]))
    }
}

/// Campaign-level fold over the current API: baseline admission first, then
/// one report per mutant plan, then the score over the derived statuses.
/// `mutants` is only called after admission, so a rejected baseline does no
/// mutant work. Every plan is checked against the one-slot manifest `t1`
/// unless `mutants` returns another manifest.
fn run_campaign(
    admission: BaselineAdmission,
    schedule: ScheduleMode,
    mutants: impl FnOnce() -> (Vec<MutantPlan>, Option<Vec<ManifestTest>>),
) -> Result<(Vec<MutantReport>, Score), CampaignFailureKind> {
    validate_baseline(admission).map_err(|failure| failure.kind())?;
    let (plans, declared) = mutants();
    let declared = declared.unwrap_or_else(|| manifest(&[("t1", 1)]));
    let reports = plans
        .iter()
        .map(|plan| report(plan, &declared, schedule))
        .collect::<Vec<_>>();
    let statuses = reports.iter().map(|item| item.status).collect::<Vec<_>>();
    Ok((reports, score(&statuses)))
}

fn statuses(reports: &[MutantReport]) -> Vec<MutantStatus> {
    reports.iter().map(|item| item.status).collect()
}

fn normal(kind: OracleKind, tag: char) -> OracleSide {
    OracleSide::Normal(value(kind, tag))
}

/// A crash whose terminal term is `crash<tag>`.
fn crash(tag: char) -> OracleSide {
    OracleSide::SemanticCrash(term(&format!("crash{tag}")))
}

/// C4 (`campaignCases`, and the baseline rows of the C1 `cases`): baseline
/// admission comes first; a rejected baseline yields no mutants and no score.
#[test]
fn baseline_admission_gates_mutants_and_score() {
    // baseline-invalid-aborts, baseline-oracle-failure-aborts (C1:
    // baseline-compilation-invalid-aborts, baseline-oracle-failure-aborts), and
    // the admission-error variant of the same property.
    let rejections = [
        (
            BaselineAdmission::Invalid,
            CampaignFailureKind::BaselineInvalid,
        ),
        (
            BaselineAdmission::OracleFailed,
            CampaignFailureKind::BaselineOracleFailed,
        ),
        (BaselineAdmission::Error, CampaignFailureKind::BaselineError),
    ];
    for (admission, expected) in rejections {
        let outcome = run_campaign(admission, ScheduleMode::Full, || {
            panic!("{admission:?}: mutant work began before baseline admission")
        });
        assert_eq!(outcome, Err(expected), "{admission:?}");
    }

    // default-score-exclusions. The duplicate and no-change entries of the
    // source row are candidate dispositions that never reach a `MutantPlan`.
    let (reports, counted) = run_campaign(BaselineAdmission::Accepted, ScheduleMode::Full, || {
        let plans = [Killed, Survived, Invalid, Timeout, Unknown, Error]
            .into_iter()
            .zip(0..)
            .map(|(status, id)| plan_for(status, id))
            .collect();
        (plans, None)
    })
    .expect("default-score-exclusions admits");
    assert_eq!(
        statuses(&reports),
        [Killed, Survived, Invalid, Timeout, Unknown, Error]
    );
    assert_eq!(
        counted,
        Score {
            killed: 1,
            survived: 1,
            denominator: 2,
            ratio: ratio(1, 2),
        }
    );

    // coupled-patch-is-one-mutant: a two-edit patch is one plan and one entry.
    let (reports, counted) = run_campaign(BaselineAdmission::Accepted, ScheduleMode::Full, || {
        (vec![plan_for(Killed, 0)], None)
    })
    .expect("coupled-patch-is-one-mutant admits");
    assert_eq!(reports.len(), 1);
    assert_eq!((counted.killed, counted.denominator), (1, 1));
    assert_eq!(counted.ratio, ratio(1, 1));

    // timeout-is-not-survived
    let (reports, counted) = run_campaign(BaselineAdmission::Accepted, ScheduleMode::Full, || {
        (vec![plan_for(Timeout, 0)], None)
    })
    .expect("timeout-is-not-survived admits");
    assert_eq!(statuses(&reports), [Timeout]);
    assert_eq!((counted.killed, counted.survived), (0, 0));
    assert_eq!((counted.denominator, counted.ratio), (0, None));

    // nonterminating-decimal-is-exact-rational
    let (_, counted) = run_campaign(BaselineAdmission::Accepted, ScheduleMode::Full, || {
        let plans = vec![
            plan_for(Killed, 0),
            plan_for(Survived, 1),
            plan_for(Survived, 2),
        ];
        (plans, None)
    })
    .expect("nonterminating-decimal-is-exact-rational admits");
    assert_eq!((counted.killed, counted.survived), (1, 2));
    assert_eq!((counted.denominator, counted.ratio), (3, ratio(1, 3)));

    // first-kill-and-full-agree (the schedule details are in C2).
    let manifest = || {
        let tests = [("t1", Agree), ("t2", Distinguish), ("t3", Distinguish)]
            .into_iter()
            .map(|(id, outcome)| compared(id, &[outcome]))
            .collect();
        let plan = plan(tests);
        let declared = manifest_of(&plan);
        (vec![plan], Some(declared))
    };
    let (first_kill, _) = run_campaign(
        BaselineAdmission::Accepted,
        ScheduleMode::FirstKill,
        manifest,
    )
    .expect("first-kill admits");
    let (full, _) = run_campaign(BaselineAdmission::Accepted, ScheduleMode::Full, manifest)
        .expect("full admits");
    assert_eq!(statuses(&first_kill), [Killed]);
    assert_eq!(statuses(&full), [Killed]);
    assert_eq!(first_kill[0].executed_test_ids, ["t1", "t2"]);
    assert_eq!(full[0].executed_test_ids, ["t1", "t2", "t3"]);
    assert_eq!(full[0].killing_test_ids, ["t2", "t3"]);

    // semantic-crash-may-kill, infrastructure-crash-is-error
    let rows = [
        ("semantic-crash-may-kill", crash('c'), Distinguish, Killed),
        (
            "infrastructure-crash-is-error",
            OracleSide::Error,
            OracleOutcome::Error,
            Error,
        ),
    ];
    for (id, mutant_side, outcome, status) in rows {
        let compared = compare_supplied(
            OracleKind::ExitStop,
            CrashPolicy::Distinguish,
            &normal(OracleKind::ExitStop, 'a'),
            &mutant_side,
        )
        .expect("sides compare");
        assert_eq!(compared, outcome, "{id}");
        let (reports, _) = run_campaign(BaselineAdmission::Accepted, ScheduleMode::Full, || {
            (vec![plan(one_test(&[compared]))], None)
        })
        .expect("admitted");
        assert_eq!(statuses(&reports), [status], "{id}");
    }
}

/// C5 case 1 (unchanged-final-result-killed-by-event-pattern): an
/// execution-pattern oracle kills a mutant whose final result is unchanged.
#[test]
fn execution_pattern_kills_mutant_with_unchanged_final_result() {
    let final_result = OracleSide::Normal(OracleValue::FinalResult(FinalResult::WholeTerm(
        [term("final")].into(),
    )));
    let baseline_pattern =
        OracleSide::Normal(OracleValue::Pattern(PatternValue::Match { bindings: None }));
    let mutant_pattern = OracleSide::Normal(OracleValue::Pattern(PatternValue::NoMatch));
    let oracles = [
        (OracleKind::FinalResult, &final_result, &final_result, Agree),
        (
            OracleKind::ExecutionPattern,
            &baseline_pattern,
            &mutant_pattern,
            Distinguish,
        ),
    ];
    let outcomes = oracles
        .iter()
        .map(|(kind, baseline, mutant, expected)| {
            let actual = compare_supplied(*kind, CrashPolicy::Distinguish, baseline, mutant)
                .expect("kind-shaped values compare");
            assert_eq!(actual, *expected, "{kind:?}");
            actual
        })
        .collect::<Vec<_>>();
    let plan = plan(one_test(&outcomes));
    let actual = report(&plan, &manifest_of(&plan), ScheduleMode::Full);
    assert_eq!(actual.status, Killed);
    assert_eq!(actual.killing_test_ids, ["t1"]);
    let counted = score(&[actual.status]);
    assert_eq!((counted.killed, counted.denominator), (1, 1));
}

/// E1 (`oracleTerminalCases`): equal normal values agree, different ones
/// distinguish, a crash on one side distinguishes or is incomparable per crash
/// policy, two crashes compare by their terminal terms, and a failure is error.
#[test]
fn terminal_comparison_truth_table() {
    #[derive(Clone, Copy, Debug)]
    enum Side {
        Normal(char),
        Crash(char),
        Failure,
    }
    fn side(kind: OracleKind, value: Side) -> OracleSide {
        match value {
            Side::Normal(tag) => normal(kind, tag),
            Side::Crash(tag) => crash(tag),
            Side::Failure => OracleSide::Error,
        }
    }
    use CrashPolicy::{CompareIdentity as Incomparable, Distinguish as Distinguishes};
    use Side::{Crash, Failure, Normal};
    // "semantic-crash-distinguishes" is `CrashPolicy::Distinguish`;
    // "semantic-crash-incomparable" is `CrashPolicy::CompareIdentity`.
    // different-crashes-incomparable keeps `CompareIdentity`'s Distinguish for
    // two unequal crash terms; the former Python checker expected incomparable.
    #[rustfmt::skip]
    let rows = [
        ("normal-normal-equal", Normal('a'), Normal('a'), Distinguishes, Agree),
        ("normal-normal-different", Normal('a'), Normal('b'), Distinguishes, Distinguish),
        ("baseline-normal-mutant-crash-distinguishes", Normal('a'), Crash('a'), Distinguishes, Distinguish),
        ("baseline-crash-mutant-normal-distinguishes", Crash('a'), Normal('a'), Distinguishes, Distinguish),
        ("baseline-normal-mutant-crash-incomparable", Normal('a'), Crash('a'), Incomparable, OracleOutcome::Incomparable),
        ("baseline-crash-mutant-normal-incomparable", Crash('a'), Normal('a'), Incomparable, OracleOutcome::Incomparable),
        ("mutant-worker-loss", Normal('a'), Failure, Distinguishes, OracleOutcome::Error),
        ("identical-crashes-distinguishing-policy", Crash('a'), Crash('a'), Distinguishes, Agree),
        ("identical-crashes-incomparable-policy", Crash('a'), Crash('a'), Incomparable, Agree),
        ("different-crashes-distinguish", Crash('a'), Crash('b'), Distinguishes, Distinguish),
        ("different-crashes-incomparable", Crash('a'), Crash('b'), Incomparable, Distinguish),
    ];
    for kind in KINDS {
        for (id, baseline, mutant, policy, expected) in rows {
            assert_eq!(
                compare_supplied(kind, policy, &side(kind, baseline), &side(kind, mutant))
                    .expect("admitted sides compare"),
                expected,
                "{id} for {kind:?}"
            );
        }
        for (baseline, mutant) in [(Crash('a'), Crash('a')), (Normal('a'), Crash('a'))] {
            assert_eq!(
                compare_supplied(
                    kind,
                    CrashPolicy::Reject,
                    &side(kind, baseline),
                    &side(kind, mutant)
                )
                .expect_err("the policy rejects crashes")
                .kind(),
                kink_campaign::OracleFailureKind::CrashRejected,
                "{kind:?}"
            );
        }
    }
}

/// Rust-only: a failed side decides the comparison in the order error,
/// timeout, unknown, whichever side failed and whatever the other side is.
#[test]
fn failed_sides_compare_error_then_timeout_then_unknown() {
    use OracleOutcome as O;
    use OracleSide::{Error as SError, Timeout as STimeout, Unknown as SUnknown};
    #[rustfmt::skip]
    let rows = [
        ("mutant-timeout", normal(OracleKind::ExitStop, 'a'), STimeout, O::Timeout),
        ("baseline-timeout", STimeout, normal(OracleKind::ExitStop, 'a'), O::Timeout),
        ("timeout-against-crash", crash('a'), STimeout, O::Timeout),
        ("timeout-over-unknown", SUnknown, STimeout, O::Timeout),
        ("timeout-over-unknown-reversed", STimeout, SUnknown, O::Timeout),
        ("error-over-timeout", STimeout, SError, O::Error),
        ("error-over-timeout-reversed", SError, STimeout, O::Error),
    ];
    for (id, baseline, mutant, expected) in rows {
        for policy in [
            CrashPolicy::Reject,
            CrashPolicy::CompareIdentity,
            CrashPolicy::Distinguish,
        ] {
            assert_eq!(
                compare_supplied(OracleKind::ExitStop, policy, &baseline, &mutant)
                    .expect("a failed side always compares"),
                expected,
                "{id} under {policy:?}"
            );
        }
    }
}

/// Every oracle kind keeps agree, distinguish and unknown apart, and an
/// unknown oracle neither kills nor survives, so it is never scored.
#[test]
fn every_oracle_kind_keeps_agree_distinguish_and_unknown_distinct() {
    for kind in KINDS {
        let left = normal(kind, 'a');
        for (mutant, expected) in [
            (normal(kind, 'a'), Agree),
            (normal(kind, 'b'), Distinguish),
            (OracleSide::Unknown, OracleOutcome::Unknown),
        ] {
            assert_eq!(
                compare_supplied(kind, CrashPolicy::Distinguish, &left, &mutant)
                    .expect("complete values compare"),
                expected,
                "{kind:?}"
            );
        }
    }
    let unknown = report(
        &plan(one_test(&[OracleOutcome::Unknown])),
        &manifest(&[("t1", 1)]),
        ScheduleMode::Full,
    );
    assert_eq!(unknown.status, Unknown);
    assert_eq!(score(&[unknown.status]).denominator, 0);
}

/// S5 (duplicate-discovery-is-not-a-second-mutant): two origins that produce
/// the same patch fold into one candidate that keeps both origins, and that
/// candidate is one mutant and one score entry.
#[test]
fn duplicate_discovery_is_one_mutant_that_keeps_both_origins() {
    let memory = support::load("memory.k");
    // The bodies of `write` and `load`.
    let mut discovery = derive_sites(&memory, "body", &[SiteSelector::Root(0)]);
    discovery.tuples.truncate(2);
    let generation = select(&discovery, SelectionPolicy::Each, 4).expect("selection");
    let origins = generation.selected_origins.clone();
    assert_eq!(origins.len(), 2);
    // Both origins build the patch that turns `write`'s right-hand side into
    // its left-hand side.
    let write = support::rule(&memory, "MEMORY.write");
    let term = |path: &[u32]| {
        memory
            .term(&TermRef::new(write.clone(), path))
            .expect("term")
            .clone()
    };
    let patch = Patch::new(vec![Edit::ReplaceTerm {
        at: TermRef::new(write.clone(), [0, 1]),
        expected: term(&[0, 1]),
        replacement: term(&[0, 0]),
    }])
    .expect("one edit");
    let (generation, dispositions) = generation.fold(&memory, "rhs-to-lhs", |_| patch.clone());
    assert_eq!(generation.candidates.len(), 1);
    let candidate = &generation.candidates[0];
    assert_eq!(candidate.origins, origins);
    assert_eq!(
        dispositions,
        [
            CandidateDisposition::Mutant(0),
            CandidateDisposition::Mutant(0)
        ]
    );
    let duplicates = generation.selected_origins.len() - generation.candidates.len();
    assert_eq!(duplicates, 1);

    let reports = (0..generation.candidates.len())
        .map(|index| {
            report(
                &MutantPlan {
                    mutant_id: MutantId(index),
                    ..plan(one_test(&[Distinguish]))
                },
                &manifest(&[("t1", 1)]),
                ScheduleMode::Full,
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(reports.len(), 1);
    assert_eq!(reports[0].mutant_id, MutantId(0));
    let counted = score(&statuses(&reports));
    assert_eq!((counted.killed, counted.denominator), (1, 1));
}
