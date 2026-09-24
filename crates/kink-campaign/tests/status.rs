//! Mutant status, schedule, score and baseline-admission truth tables.
//!
//! The rows are transcribed from the former vector files
//! (`mutation-status-vectors.json`, the `campaignCases` and
//! `oracleTerminalCases` of `mutation-vectors.json`, and
//! `cross-feature-vectors.json`), which no longer exist in the tree. Row IDs
//! are kept verbatim. Rows the current API cannot express are left out and
//! named in the commit that added this file.

use kink_campaign::{
    BaselineAdmission, CampaignFailureKind, CrashPolicy, MutantFailureKind, MutantPlan,
    MutantReport, MutantStatus, OracleKind, OracleOutcome, OracleSide, Rational, ScheduleMode,
    Score, TestPlan, compare_supplied, derive_mutant_report, score, validate_baseline,
};
use kink_pattern::{
    CandidateGeneration, Completeness, PatchOrigin, SuppliedPatch, derive_mutant_id,
};
use kink_portable::{Digest, SemanticJson};
use std::collections::BTreeMap;

use MutantStatus::{Error, Invalid, Killed, Survived, Timeout, Unknown};
use OracleOutcome::{Agree, Distinguish, Skipped};

fn digest(character: char) -> Digest {
    Digest::parse(&character.to_string().repeat(64)).expect("test digest is valid")
}

fn object(values: &[(&str, SemanticJson)]) -> SemanticJson {
    SemanticJson::Object(
        values
            .iter()
            .map(|(key, value)| ((*key).to_owned(), value.clone()))
            .collect::<BTreeMap<_, _>>(),
    )
}

fn text(value: &str) -> SemanticJson {
    SemanticJson::String(value.to_owned())
}

fn one_test(outcomes: Vec<OracleOutcome>) -> Vec<TestPlan> {
    vec![TestPlan {
        test_id: "t1".to_owned(),
        oracle_outcomes: outcomes,
    }]
}

fn report(plan: &MutantPlan, schedule: ScheduleMode) -> MutantReport {
    derive_mutant_report(plan, schedule).expect("plan derives a report")
}

fn ratio(numerator: u64, denominator: u64) -> Option<Rational> {
    Some(Rational {
        numerator,
        denominator,
    })
}

/// Mutant validation outcome, decided before any oracle runs.
#[derive(Clone, Copy, Debug)]
enum Validation {
    Valid,
    Invalid,
    Error,
}

/// The kind of an old failure-taxonomy classification reached by these rows.
fn failure_kind(classification: &str) -> MutantFailureKind {
    match classification {
        "ill-sorted" => MutantFailureKind::Rejected,
        "lowering-nontermination" => MutantFailureKind::LoweringNontermination,
        "time-limit" => MutantFailureKind::TimeLimit,
        "resource-limit" => MutantFailureKind::ResourceLimit,
        "solver-unknown" => MutantFailureKind::Indeterminate,
        "worker-lost" => MutantFailureKind::Infrastructure,
        other => panic!("no failure kind for classification {other}"),
    }
}

/// Builds the plan for one validation outcome and the source row's oracle
/// slots and failure classification.
///
/// A mutant that failed validation is preclassified. For a valid mutant the
/// source rows mark the slot that was never evaluated after a failed mutant
/// execution as `skipped`; Rust reserves `Skipped` for the scheduler and rejects
/// it as input, so that slot is omitted.
fn status_plan(
    validation: Validation,
    outcomes: &[OracleOutcome],
    failure: Option<&str>,
) -> MutantPlan {
    let (preclassified, outcomes) = match validation {
        Validation::Valid => (
            None,
            outcomes
                .iter()
                .copied()
                .filter(|outcome| *outcome != Skipped)
                .collect(),
        ),
        Validation::Invalid => (Some(Invalid), outcomes.to_vec()),
        Validation::Error => (Some(Error), outcomes.to_vec()),
    };
    MutantPlan {
        mutant_id: digest('a'),
        tests: one_test(outcomes),
        preclassified,
        failure: failure.map(failure_kind),
    }
}

/// (id, validation, oracle slots, failure classification, status, excluded bucket)
type StatusRow = (
    &'static str,
    Validation,
    &'static [OracleOutcome],
    Option<&'static str>,
    MutantStatus,
    Option<MutantStatus>,
);

/// C1: mutant status is a total function of validation and oracle outcomes,
/// and only killed and survived enter the score.
#[test]
fn mutant_status_is_derived_from_validation_then_oracle_outcomes() {
    use OracleOutcome as O;
    use Validation::{Error as VError, Invalid as VInvalid, Valid};
    #[rustfmt::skip]
    let rows: [StatusRow; 10] = [
        ("ordinary-result-kill", Valid, &[O::Distinguish, O::Agree], None, Killed, None),
        ("complete-survival", Valid, &[O::Agree, O::Agree], None, Survived, None),
        ("ill-sorted-invalid", VInvalid, &[O::Skipped, O::Skipped], Some("ill-sorted"), Invalid, Some(Invalid)),
        ("lowering-nontermination-is-invalid", VInvalid, &[O::Skipped, O::Skipped], Some("lowering-nontermination"), Invalid, Some(Invalid)),
        ("lowering-time-limit-is-timeout", Valid, &[O::Timeout, O::Skipped], Some("time-limit"), Timeout, Some(Timeout)),
        ("lowering-resource-limit-is-unknown", Valid, &[O::Unknown, O::Skipped], Some("resource-limit"), Unknown, Some(Unknown)),
        ("time-limit-is-timeout", Valid, &[O::Timeout, O::Skipped], Some("time-limit"), Timeout, Some(Timeout)),
        ("solver-indeterminate-is-unknown", Valid, &[O::Unknown, O::Skipped], Some("solver-unknown"), Unknown, Some(Unknown)),
        ("infrastructure-failure-is-error", VError, &[O::Error, O::Skipped], Some("worker-lost"), Error, Some(Error)),
        ("bounded-agreement-is-survived-not-equivalent", Valid, &[O::Agree, O::Agree], None, Survived, None),
    ];
    for (id, validation, outcomes, failure, expected, excluded) in rows {
        if matches!(validation, Validation::Valid) && outcomes.contains(&Skipped) {
            let verbatim = MutantPlan {
                mutant_id: digest('a'),
                tests: one_test(outcomes.to_vec()),
                preclassified: None,
                failure: None,
            };
            assert_eq!(
                derive_mutant_report(&verbatim, ScheduleMode::Full)
                    .expect_err("a supplied skip is rejected")
                    .kind(),
                CampaignFailureKind::FabricatedSkip,
                "{id}"
            );
        }
        for schedule in [ScheduleMode::FirstKill, ScheduleMode::Full] {
            let actual = report(&status_plan(validation, outcomes, failure), schedule).status;
            assert_eq!(actual, expected, "{id} ({failure:?}) under {schedule:?}");
            let counted = score(&[actual]);
            assert_eq!(counted.killed, u64::from(actual == Killed), "{id}");
            assert_eq!(counted.survived, u64::from(actual == Survived), "{id}");
            assert_eq!(
                (counted.denominator == 0).then_some(actual),
                excluded,
                "{id}: excluded bucket"
            );
        }
    }
}

/// C1 `statusContradictionCases`: a status that contradicts validation cannot
/// be derived, and cannot be supplied as a preclassification either.
#[test]
fn killed_cannot_fail_validation() {
    let plan = status_plan(
        Validation::Invalid,
        &[Distinguish, Agree],
        Some("ill-sorted"),
    );
    assert_eq!(report(&plan, ScheduleMode::Full).status, Invalid);
    for claimed in [Killed, Survived] {
        let forged = MutantPlan {
            preclassified: Some(claimed),
            ..plan.clone()
        };
        assert_eq!(
            derive_mutant_report(&forged, ScheduleMode::Full)
                .expect_err("a conclusive preclassification is rejected")
                .kind(),
            CampaignFailureKind::InvalidPreclassification,
            "{claimed:?}"
        );
    }
}

/// C1 `statusContradictionCases` on failure classification: a valid mutant
/// whose oracles neither distinguish nor all agree takes its status from the
/// failure kind, not from the inconclusive oracle outcome.
#[test]
fn failure_kind_decides_status_over_inconclusive_outcomes() {
    use OracleOutcome as O;
    // (id, oracle slots, failure classification, contradicting status, status)
    #[rustfmt::skip]
    let rows: [(&str, &[OracleOutcome], &str, MutantStatus, MutantStatus); 3] = [
        ("lowering-time-limit-cannot-be-unknown", &[O::Unknown, O::Skipped], "time-limit", Unknown, Timeout),
        ("lowering-resource-limit-cannot-be-timeout", &[O::Timeout, O::Skipped], "resource-limit", Timeout, Unknown),
        ("lowering-nontermination-cannot-be-timeout", &[O::Timeout, O::Skipped], "lowering-nontermination", Timeout, Invalid),
    ];
    for (id, outcomes, failure, contradicting, expected) in rows {
        for schedule in [ScheduleMode::FirstKill, ScheduleMode::Full] {
            let actual = report(
                &status_plan(Validation::Valid, outcomes, Some(failure)),
                schedule,
            )
            .status;
            assert_eq!(actual, expected, "{id} under {schedule:?}");
            assert_ne!(actual, contradicting, "{id} under {schedule:?}");
        }
    }
}

/// One row per `MutantFailureKind::status` arm: the failure kind decides an
/// inconclusive valid mutant, but never overrides a kill, complete agreement
/// or a validation preclassification.
#[test]
fn every_failure_kind_maps_to_one_status() {
    use MutantFailureKind as F;
    let rows = [
        (F::Rejected, Invalid),
        (F::LoweringNontermination, Invalid),
        (F::TimeLimit, Timeout),
        (F::ResourceLimit, Unknown),
        (F::Indeterminate, Unknown),
        (F::Infrastructure, Error),
    ];
    for (kind, expected) in rows {
        assert_eq!(kind.status(), expected, "{kind:?}");
        let plan = |outcomes: Vec<OracleOutcome>, preclassified| MutantPlan {
            mutant_id: digest('a'),
            tests: one_test(outcomes),
            preclassified,
            failure: Some(kind),
        };
        for inconclusive in [
            OracleOutcome::Timeout,
            OracleOutcome::Unknown,
            OracleOutcome::Incomparable,
            OracleOutcome::Error,
        ] {
            let actual = report(&plan(vec![Agree, inconclusive], None), ScheduleMode::Full);
            assert_eq!(actual.status, expected, "{kind:?} with {inconclusive:?}");
        }
        let killed = report(
            &plan(vec![OracleOutcome::Unknown, Distinguish], None),
            ScheduleMode::Full,
        );
        assert_eq!(killed.status, Killed, "{kind:?}: a kill takes precedence");
        let survived = report(&plan(vec![Agree, Agree], None), ScheduleMode::Full);
        assert_eq!(
            survived.status, Survived,
            "{kind:?}: complete agreement takes precedence"
        );
        for preclassified in [Invalid, Error, Timeout, Unknown] {
            let actual = report(
                &plan(vec![OracleOutcome::Unknown], Some(preclassified)),
                ScheduleMode::Full,
            );
            assert_eq!(
                actual.status, preclassified,
                "{kind:?}: validation takes precedence"
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
    let manifest = [("t1", Agree), ("t2", Distinguish), ("t3", Distinguish)];
    let plan = MutantPlan {
        mutant_id: digest('a'),
        tests: manifest
            .iter()
            .map(|(id, outcome)| TestPlan {
                test_id: (*id).to_owned(),
                oracle_outcomes: vec![*outcome],
            })
            .collect(),
        preclassified: None,
        failure: None,
    };
    let rows: [ScheduleRow; 2] = [
        (ScheduleMode::FirstKill, &["t1", "t2"], &["t2"], &["t3"]),
        (ScheduleMode::Full, &["t1", "t2", "t3"], &["t2", "t3"], &[]),
    ];
    for (schedule, executed, killing, skipped) in rows {
        let actual = report(&plan, schedule);
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

/// A one-test plan whose single oracle slot folds to `status`.
fn plan_for(status: MutantStatus, character: char) -> MutantPlan {
    let (outcome, preclassified) = match status {
        Killed => (Distinguish, None),
        Survived => (Agree, None),
        Timeout => (OracleOutcome::Timeout, None),
        Unknown => (OracleOutcome::Unknown, None),
        Error => (OracleOutcome::Error, None),
        Invalid => (Skipped, Some(Invalid)),
    };
    MutantPlan {
        mutant_id: digest(character),
        tests: one_test(vec![outcome]),
        preclassified,
        failure: None,
    }
}

/// Campaign-level fold over the current API: baseline admission first, then
/// one report per mutant plan, then the score over the derived statuses.
/// `mutants` is only called after admission, so a rejected baseline does no
/// mutant work.
fn run_campaign(
    admission: BaselineAdmission,
    schedule: ScheduleMode,
    mutants: impl FnOnce() -> Vec<MutantPlan>,
) -> Result<(Vec<MutantReport>, Score), CampaignFailureKind> {
    validate_baseline(admission).map_err(|failure| failure.kind())?;
    let reports = mutants()
        .iter()
        .map(|plan| report(plan, schedule))
        .collect::<Vec<_>>();
    let statuses = reports.iter().map(|item| item.status).collect::<Vec<_>>();
    Ok((reports, score(&statuses)))
}

fn statuses(reports: &[MutantReport]) -> Vec<MutantStatus> {
    reports.iter().map(|item| item.status).collect()
}

fn normal(value: SemanticJson) -> OracleSide {
    OracleSide::Normal {
        value,
        completeness: Completeness::CompleteFinite,
    }
}

fn crash(character: char) -> OracleSide {
    OracleSide::SemanticCrash(digest(character))
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
        [Killed, Survived, Invalid, Timeout, Unknown, Error]
            .into_iter()
            .zip('a'..)
            .map(|(status, character)| plan_for(status, character))
            .collect()
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
        vec![plan_for(Killed, 'a')]
    })
    .expect("coupled-patch-is-one-mutant admits");
    assert_eq!(reports.len(), 1);
    assert_eq!((counted.killed, counted.denominator), (1, 1));
    assert_eq!(counted.ratio, ratio(1, 1));

    // timeout-is-not-survived
    let (reports, counted) = run_campaign(BaselineAdmission::Accepted, ScheduleMode::Full, || {
        vec![plan_for(Timeout, 'a')]
    })
    .expect("timeout-is-not-survived admits");
    assert_eq!(statuses(&reports), [Timeout]);
    assert_eq!((counted.killed, counted.survived), (0, 0));
    assert_eq!((counted.denominator, counted.ratio), (0, None));

    // nonterminating-decimal-is-exact-rational
    let (_, counted) = run_campaign(BaselineAdmission::Accepted, ScheduleMode::Full, || {
        vec![
            plan_for(Killed, 'a'),
            plan_for(Survived, 'b'),
            plan_for(Survived, 'c'),
        ]
    })
    .expect("nonterminating-decimal-is-exact-rational admits");
    assert_eq!((counted.killed, counted.survived), (1, 2));
    assert_eq!((counted.denominator, counted.ratio), (3, ratio(1, 3)));

    // first-kill-and-full-agree (the schedule details are in C2).
    let manifest = || {
        vec![MutantPlan {
            mutant_id: digest('a'),
            tests: [("t1", Agree), ("t2", Distinguish), ("t3", Distinguish)]
                .into_iter()
                .map(|(id, outcome)| TestPlan {
                    test_id: id.to_owned(),
                    oracle_outcomes: vec![outcome],
                })
                .collect(),
            preclassified: None,
            failure: None,
        }]
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
            &normal(text("a")),
            &mutant_side,
        )
        .expect("sides compare");
        assert_eq!(compared, outcome, "{id}");
        let (reports, _) = run_campaign(BaselineAdmission::Accepted, ScheduleMode::Full, || {
            vec![MutantPlan {
                mutant_id: digest('a'),
                tests: one_test(vec![compared]),
                preclassified: None,
                failure: None,
            }]
        })
        .expect("admitted");
        assert_eq!(statuses(&reports), [status], "{id}");
    }
}

/// C5 case 1 (unchanged-final-result-killed-by-event-pattern): an
/// execution-pattern oracle kills a mutant whose final result is unchanged.
#[test]
fn execution_pattern_kills_mutant_with_unchanged_final_result() {
    let final_result = object(&[
        ("projection", text("whole-term")),
        ("term", text("final-configuration")),
        ("terminalState", text("normal")),
    ]);
    let baseline_pattern = object(&[
        ("bindingTuples", SemanticJson::Array(Vec::new())),
        ("outcome", text("match")),
        (
            "patternResult",
            object(&[(
                "witnessIndices",
                SemanticJson::Array(vec![SemanticJson::Integer(0), SemanticJson::Integer(2)]),
            )]),
        ),
    ]);
    let mutant_pattern = object(&[
        ("bindingTuples", SemanticJson::Array(Vec::new())),
        ("outcome", text("no-match")),
        (
            "patternResult",
            object(&[("completeCoverage", SemanticJson::Bool(true))]),
        ),
    ]);
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
            let actual = compare_supplied(
                *kind,
                CrashPolicy::Distinguish,
                &normal((*baseline).clone()),
                &normal((*mutant).clone()),
            )
            .expect("kind-shaped values compare");
            assert_eq!(actual, *expected, "{kind:?}");
            actual
        })
        .collect::<Vec<_>>();
    let actual = report(
        &MutantPlan {
            mutant_id: digest('a'),
            tests: one_test(outcomes),
            preclassified: None,
            failure: None,
        },
        ScheduleMode::Full,
    );
    assert_eq!(actual.status, Killed);
    assert_eq!(actual.killing_test_ids, ["t1"]);
    let counted = score(&[actual.status]);
    assert_eq!((counted.killed, counted.denominator), (1, 1));
}

/// E1 (`oracleTerminalCases` without the crash-vs-crash rows): equal normal
/// values agree, different ones distinguish, a crash on one side distinguishes
/// or is incomparable per crash policy, and a failure is error.
#[test]
fn terminal_comparison_truth_table_without_crash_pairs() {
    #[derive(Clone, Copy, Debug)]
    enum Side {
        Normal(&'static str),
        Crash(char),
        Failure,
    }
    fn side(value: Side) -> OracleSide {
        match value {
            Side::Normal(value) => normal(text(value)),
            Side::Crash(character) => crash(character),
            Side::Failure => OracleSide::Error,
        }
    }
    use CrashPolicy::{CompareIdentity as Incomparable, Distinguish as Distinguishes};
    use Side::{Crash, Failure, Normal};
    // "semantic-crash-distinguishes" is `CrashPolicy::Distinguish`;
    // "semantic-crash-incomparable" is `CrashPolicy::CompareIdentity`.
    #[rustfmt::skip]
    let rows = [
        ("normal-normal-equal", Normal("a"), Normal("a"), Distinguishes, Agree),
        ("normal-normal-different", Normal("a"), Normal("b"), Distinguishes, Distinguish),
        ("baseline-normal-mutant-crash-distinguishes", Normal("a"), Crash('a'), Distinguishes, Distinguish),
        ("baseline-crash-mutant-normal-distinguishes", Crash('a'), Normal("a"), Distinguishes, Distinguish),
        ("baseline-normal-mutant-crash-incomparable", Normal("a"), Crash('a'), Incomparable, OracleOutcome::Incomparable),
        ("baseline-crash-mutant-normal-incomparable", Crash('a'), Normal("a"), Incomparable, OracleOutcome::Incomparable),
        ("mutant-worker-loss", Normal("a"), Failure, Distinguishes, OracleOutcome::Error),
    ];
    for kind in [
        OracleKind::ExitStop,
        OracleKind::FinalResult,
        OracleKind::ExecutionPattern,
    ] {
        for (id, baseline, mutant, policy, expected) in rows {
            assert_eq!(
                compare_supplied(kind, policy, &side(baseline), &side(mutant))
                    .expect("admitted sides compare"),
                expected,
                "{id} for {kind:?}"
            );
        }
    }
}

/// Every oracle kind keeps agree, distinguish and unknown apart, and an
/// unknown oracle neither kills nor survives, so it is never scored.
#[test]
fn every_oracle_kind_keeps_agree_distinguish_and_unknown_distinct() {
    let left = normal(SemanticJson::Bool(true));
    let different = normal(SemanticJson::Bool(false));
    for kind in [
        OracleKind::ExitStop,
        OracleKind::FinalResult,
        OracleKind::ConcreteOutput,
        OracleKind::Reachability,
        OracleKind::ExecutionPattern,
        OracleKind::StructuredPredicate,
    ] {
        for (mutant, expected) in [
            (&left, Agree),
            (&different, Distinguish),
            (&OracleSide::Unknown, OracleOutcome::Unknown),
        ] {
            assert_eq!(
                compare_supplied(kind, CrashPolicy::Distinguish, &left, mutant)
                    .expect("complete values compare"),
                expected,
                "{kind:?}"
            );
        }
    }
    let unknown = report(
        &MutantPlan {
            mutant_id: digest('a'),
            tests: one_test(vec![OracleOutcome::Unknown]),
            preclassified: None,
            failure: None,
        },
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
    let baseline = digest('b');
    let origin = |character| PatchOrigin {
        site_tuple: vec![digest(character)],
        discovery_tuples: Vec::new(),
    };
    let origins = vec![origin('1'), origin('2')];
    let patch_id = digest('e');
    let generation = CandidateGeneration {
        candidates: Vec::new(),
        selected_origins: origins.clone(),
        completeness: Completeness::CompleteFinite,
        failure: None,
        scored: true,
    }
    .fold_patches(
        "op",
        1,
        &baseline,
        origins
            .into_iter()
            .map(|origin| SuppliedPatch {
                patch_id: patch_id.clone(),
                origin,
                edit_receipts: Vec::new(),
            })
            .collect(),
    )
    .expect("equal patches fold");
    assert_eq!(generation.candidates.len(), 1);
    let candidate = &generation.candidates[0];
    assert_eq!(candidate.origins.len(), 2);
    let duplicates = generation.selected_origins.len() - generation.candidates.len();
    assert_eq!(duplicates, 1);

    let reports = generation
        .candidates
        .iter()
        .map(|candidate| {
            report(
                &MutantPlan {
                    mutant_id: derive_mutant_id(&baseline, &candidate.patch_id),
                    tests: one_test(vec![Distinguish]),
                    preclassified: None,
                    failure: None,
                },
                ScheduleMode::Full,
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(reports.len(), 1);
    let counted = score(&statuses(&reports));
    assert_eq!((counted.killed, counted.denominator), (1, 1));
}
