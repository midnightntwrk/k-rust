use kink_campaign::{
    AdapterContract, ArtifactKey, BranchCollection, BranchDecision, CacheRecord, CacheStore,
    CampaignReport, CollectionDecision, CollectionStop, CrashPolicy, EvaluatorAuthority,
    InvocationFailureKind, KeyKind, MaterialEligibility, MutantPlan, MutantReport, MutantStatus,
    OperationInvocation, OperationKind, OperationReceipt, OracleKind, OracleOutcome, OracleSide,
    PortableProductionWitness, Producer, Publication, ReceiptOutput, ReplayManifest, RequestKey,
    ReuseClass, ScheduleMode, ScriptedReceipt, TestPlan, WorkerResult, WorkerResultKind,
    WorkerTerminal, compare_supplied, derive_collection_decision, derive_mutant_report, score,
};
use kink_contracts::{Completeness, NativeConformance};
use kink_portable::{Digest, SemanticJson, parse_json};
use serde_json::Value;
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

fn package_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("investigations/backend-agnostic-goal-closure")
}

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

fn invocation(kind: OperationKind) -> OperationInvocation {
    OperationInvocation::new(
        kind,
        1,
        AdapterContract {
            adapter_id: "scripted-test".to_owned(),
            adapter_version: 1,
        },
        object(&[]),
        Vec::new(),
        Vec::new(),
    )
    .expect("test invocation is valid")
}

fn artifact(role: &str, character: char) -> ArtifactKey {
    ArtifactKey::new(role, digest(character)).expect("test artifact is valid")
}

fn receipt(producer: Producer, outputs: Vec<ArtifactKey>) -> ScriptedReceipt {
    let invocation = invocation(OperationKind::ExecutionAttempt);
    ScriptedReceipt::complete(
        invocation,
        producer,
        ReceiptOutput {
            wrapper: artifact("execution-attempt-result", 'a'),
            semantic_terminal: Some(artifact("terminal-state", 'b')),
            produced_artifacts: outputs,
            completeness: Completeness::CompleteFinite,
        },
    )
    .expect("test receipt is valid")
}

#[test]
fn scripted_boundary_keeps_all_terminal_classes_and_never_promotes_native() {
    let terminal_files = [
        (
            "material/bag14-cache-record-baseline-execution-t1.json",
            WorkerResultKind::Normal,
        ),
        (
            "material/bag14-cache-record-mutant-execution-t1.json",
            WorkerResultKind::Stuck,
        ),
        (
            "material/bag14-cache-record-bounded-attempt.json",
            WorkerResultKind::Bounded,
        ),
        (
            "material/bag14-cache-record-diagnostic-attempt.json",
            WorkerResultKind::Infrastructure,
        ),
    ];
    let terminals = terminal_files.map(|(path, kind)| {
        let value = parse_json(&fs::read(package_root().join(path)).expect("record is readable"))
            .expect("record is JSON");
        let terminal = value
            .as_object()
            .and_then(|fields| fields.get("terminalRecord"))
            .expect("record terminal");
        (
            WorkerTerminal::from_portable_json(terminal).expect("terminal parses"),
            kind,
        )
    });
    for (terminal, expected) in terminals {
        let result = WorkerResult::scripted(terminal, Vec::new(), Completeness::Unknown);
        assert_eq!(result.kind(), expected);
        assert_eq!(result.native_conformance(), NativeConformance::NotProven);
    }
}

#[test]
fn all_seven_operations_have_one_distinct_wrapper() {
    let kinds = [
        OperationKind::MutationMaterialization,
        OperationKind::ExecutionAttempt,
        OperationKind::OracleOperandProduction,
        OperationKind::BaselineAdmission,
        OperationKind::OracleComparison,
        OperationKind::CampaignDerivation,
        OperationKind::ReportPublication,
    ];
    let wrappers = kinds
        .into_iter()
        .map(|kind| kind.output_role())
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(wrappers.len(), 7);
}

#[test]
fn every_bundled_bag15_receipt_rederives_and_failed_producers_publish_nothing() {
    let material = package_root().join("material");
    let mut checked = 0;
    for entry in fs::read_dir(material).expect("material directory exists") {
        let path = entry.expect("directory entry is readable").path();
        let Some(name) = path.file_name().and_then(|name| name.to_str()) else {
            continue;
        };
        if !name.starts_with("bag15-receipt-")
            || path.extension().and_then(|ext| ext.to_str()) != Some("json")
        {
            continue;
        }
        let value = parse_json(&fs::read(&path).expect("receipt is readable"))
            .expect("receipt is restricted JSON");
        OperationReceipt::validate_portable_json(&value)
            .unwrap_or_else(|error| panic!("{}: {error}", path.display()));
        checked += 1;
    }
    assert!(checked >= 20, "expected the complete BAG-15 receipt family");

    let failed = package_root().join("material/bag15-receipt-failed-producer.json");
    let mut value =
        parse_json(&fs::read(failed).expect("fixture is readable")).expect("fixture is valid JSON");
    let SemanticJson::Object(fields) = &mut value else {
        unreachable!()
    };
    fields.insert(
        "outputs".to_owned(),
        SemanticJson::Array(vec![object(&[(
            "artifact",
            object(&[
                ("digest", SemanticJson::String(digest('f').to_string())),
                (
                    "role",
                    SemanticJson::String("execution-attempt-result".to_owned()),
                ),
            ]),
        )])]),
    );
    assert_eq!(
        OperationReceipt::validate_portable_json(&value)
            .expect_err("failed producer with output must reject")
            .kind(),
        InvocationFailureKind::FailedProducerOutput
    );
}

#[test]
fn request_keys_exclude_results_schedules_and_lookup_provenance() {
    let value = parse_json(
        &fs::read(package_root().join("material/bag14-cache-record-baseline-execution-t1.json"))
            .expect("record is readable"),
    )
    .expect("record is JSON");
    let key = value
        .as_object()
        .and_then(|fields| fields.get("key"))
        .expect("record key");
    RequestKey::from_portable_json(KeyKind::ExecutionAttempt, key)
        .expect("exact execution key validates");
    for forbidden in [
        "terminal",
        "result",
        "scheduleMode",
        "cacheState",
        "receipt",
    ] {
        let mut value = key.clone();
        let SemanticJson::Object(fields) = &mut value else {
            unreachable!()
        };
        fields.insert(forbidden.to_owned(), SemanticJson::Null);
        assert!(RequestKey::from_portable_json(KeyKind::ExecutionAttempt, &value).is_err());
    }
}

#[test]
fn cache_reuse_requires_authority_and_conflicts_quarantine_the_key() {
    let path = package_root().join("material/bag14-cache-record-baseline-execution-t1.json");
    let value = parse_json(&fs::read(path).expect("record is readable")).expect("record is JSON");
    let finite =
        CacheRecord::from_portable_json(&value, PortableProductionWitness::BundledFiniteVector)
            .expect("finite record is valid");
    assert_eq!(finite.reuse_class(), ReuseClass::SemanticResult);

    let diagnostic_value = parse_json(
        &fs::read(package_root().join("material/bag14-cache-record-diagnostic-attempt.json"))
            .expect("diagnostic record is readable"),
    )
    .expect("diagnostic record is JSON");
    let diagnostic = CacheRecord::from_portable_json(
        &diagnostic_value,
        PortableProductionWitness::BundledFiniteVector,
    )
    .expect("diagnostic record is valid");
    let key = diagnostic.key().clone();
    let outputs = diagnostic.produced_artifacts().to_vec();
    let scripted = receipt(Producer::scripted("script", 1), outputs.clone());
    let first = CacheRecord::scripted_diagnostic(
        key.clone(),
        diagnostic.terminal_record().clone(),
        outputs.clone(),
        MaterialEligibility::Eligible,
        &scripted,
    )
    .expect("scripted diagnostic is valid");
    assert_eq!(first.reuse_class(), ReuseClass::NotReusable);
    let mut conflicting_terminal = diagnostic.terminal_record().clone();
    let SemanticJson::Object(fields) = &mut conflicting_terminal else {
        unreachable!()
    };
    let failure = fields
        .get_mut("failure")
        .and_then(|value| match value {
            SemanticJson::Object(fields) => Some(fields),
            _ => None,
        })
        .expect("diagnostic failure");
    failure.insert(
        "classification".to_owned(),
        SemanticJson::String("internal".to_owned()),
    );
    failure.insert(
        "retryability".to_owned(),
        SemanticJson::String("never".to_owned()),
    );
    let conflicting = CacheRecord::scripted_diagnostic(
        key.clone(),
        conflicting_terminal,
        outputs,
        MaterialEligibility::Eligible,
        &scripted,
    )
    .expect("conflicting scripted diagnostic is structurally valid");
    let mut store = CacheStore::default();
    assert_eq!(store.publish(first), Publication::Published);
    assert_eq!(store.publish(conflicting), Publication::Quarantined);
    assert!(store.is_quarantined(key.key_digest()));
    assert!(store.reusable(key.key_digest()).is_none());
}

fn parse_outcome(value: &str) -> OracleOutcome {
    match value {
        "agree" => OracleOutcome::Agree,
        "distinguish" => OracleOutcome::Distinguish,
        "incomparable" => OracleOutcome::Incomparable,
        "timeout" => OracleOutcome::Timeout,
        "unknown" => OracleOutcome::Unknown,
        "error" => OracleOutcome::Error,
        "skipped" => OracleOutcome::Skipped,
        other => panic!("unknown frozen oracle outcome {other}"),
    }
}

fn parse_status(value: &str) -> MutantStatus {
    match value {
        "killed" => MutantStatus::Killed,
        "survived" => MutantStatus::Survived,
        "invalid" => MutantStatus::Invalid,
        "timeout" => MutantStatus::Timeout,
        "unknown" => MutantStatus::Unknown,
        "error" => MutantStatus::Error,
        other => panic!("unknown frozen mutant status {other}"),
    }
}

#[test]
fn mutation_status_schedule_and_score_vectors_pass_unchanged() {
    let value: Value = serde_json::from_slice(
        &fs::read(package_root().join("vectors/mutation-status-vectors.json"))
            .expect("vector is readable"),
    )
    .expect("vector is JSON");
    for case in value["scheduleCases"].as_array().expect("schedule cases") {
        let tests = case["manifestOrder"]
            .as_array()
            .expect("manifest order")
            .iter()
            .map(|entry| TestPlan {
                test_id: entry["id"].as_str().expect("test id").to_owned(),
                oracle_outcomes: vec![parse_outcome(entry["outcome"].as_str().expect("outcome"))],
            })
            .collect();
        let mode = match case["mode"].as_str().expect("mode") {
            "first-kill" => ScheduleMode::FirstKill,
            "full" => ScheduleMode::Full,
            other => panic!("unknown schedule {other}"),
        };
        let report = derive_mutant_report(
            &MutantPlan {
                mutant_id: digest('a'),
                tests,
                preclassified: None,
            },
            mode,
        )
        .expect("schedule derives");
        assert_eq!(
            report.status.frozen_name(),
            case["expected"]["status"].as_str().unwrap()
        );
        assert_eq!(
            report.executed_test_ids,
            strings(&case["expected"]["executed"])
        );
        assert_eq!(
            report.killing_test_ids,
            strings(&case["expected"]["killingTests"])
        );
    }
    for case in value["scoreCases"].as_array().expect("score cases") {
        let statuses = case["statuses"]
            .as_array()
            .expect("statuses")
            .iter()
            .map(|value| parse_status(value.as_str().expect("status")))
            .collect::<Vec<_>>();
        let actual = score(&statuses);
        assert_eq!(actual.killed, case["expected"]["killed"].as_u64().unwrap());
        assert_eq!(
            actual.survived,
            case["expected"]["survived"].as_u64().unwrap()
        );
        assert_eq!(
            actual.denominator,
            case["expected"]["denominator"].as_u64().unwrap()
        );
        match (&actual.ratio, &case["expected"]["ratio"]) {
            (None, Value::Null) => {}
            (Some(actual), expected) => {
                assert_eq!(actual.numerator, expected["numerator"].as_u64().unwrap());
                assert_eq!(
                    actual.denominator,
                    expected["denominator"].as_u64().unwrap()
                );
            }
            other => panic!("ratio mismatch: {other:?}"),
        }
    }
}

fn strings(value: &Value) -> Vec<String> {
    value
        .as_array()
        .expect("string array")
        .iter()
        .map(|value| value.as_str().expect("string").to_owned())
        .collect()
}

#[test]
fn bag14_cache_source_variants_fold_to_identical_record_closures() {
    let value: Value = serde_json::from_slice(
        &fs::read(package_root().join("vectors/cache-semantics-vectors.json"))
            .expect("vector is readable"),
    )
    .expect("vector is JSON");
    for fold in value["scheduleFolds"].as_array().expect("schedule folds") {
        let materializations = fold["materializations"]
            .as_array()
            .expect("materializations");
        let closures = materializations
            .iter()
            .map(|item| {
                item["recordSources"]
                    .as_array()
                    .expect("record sources")
                    .iter()
                    .map(|entry| {
                        (
                            entry["slotId"].as_str().unwrap(),
                            entry["recordId"].as_str().unwrap(),
                        )
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        assert!(closures.windows(2).all(|pair| pair[0] == pair[1]));
        let expected_len = if fold["scheduleMode"] == "first-kill" {
            7
        } else {
            10
        };
        assert_eq!(closures[0].len(), expected_len);
    }
}

#[test]
fn semantic_report_ignores_cache_hit_miss_provenance() {
    let mutant = MutantReport {
        mutant_id: digest('a'),
        status: MutantStatus::Killed,
        executed_test_ids: vec!["t1".to_owned()],
        killing_test_ids: vec!["t1".to_owned()],
        skipped_test_ids: Vec::new(),
    };
    let ids = vec![digest('b'), digest('c')];
    let uncached = CampaignReport::new(ScheduleMode::Full, ids.clone(), vec![mutant.clone()])
        .expect("report derives");
    let full_hit =
        CampaignReport::new(ScheduleMode::Full, ids, vec![mutant]).expect("report derives");
    assert_eq!(uncached.report_id, full_hit.report_id);
    assert_eq!(
        uncached.campaign_invocation_id,
        full_hit.campaign_invocation_id
    );
}

#[test]
fn every_v1_replay_manifest_rederives_both_identities() {
    let material = package_root().join("material");
    let mut checked = 0;
    for entry in fs::read_dir(material).expect("material directory exists") {
        let path = entry.expect("directory entry is readable").path();
        let Some(name) = path.file_name().and_then(|name| name.to_str()) else {
            continue;
        };
        if !name.starts_with("replay-")
            || path.extension().and_then(|ext| ext.to_str()) != Some("json")
        {
            continue;
        }
        let value = parse_json(&fs::read(&path).expect("replay is readable"))
            .expect("replay is restricted JSON");
        ReplayManifest::from_json(&value)
            .unwrap_or_else(|error| panic!("{}: {error}", path.display()));
        checked += 1;
    }
    assert!(
        checked >= 2,
        "expected ordinary and pattern replay fixtures"
    );
}

#[test]
fn cross_feature_unknown_neither_kills_nor_survives() {
    let plan = MutantPlan {
        mutant_id: digest('a'),
        tests: vec![TestPlan {
            test_id: "pattern".to_owned(),
            oracle_outcomes: vec![OracleOutcome::Unknown],
        }],
        preclassified: None,
    };
    let report = derive_mutant_report(&plan, ScheduleMode::Full).expect("report derives");
    assert_eq!(report.status, MutantStatus::Unknown);
    assert_eq!(score(&[report.status]).denominator, 0);
}

#[test]
fn all_six_oracle_kinds_keep_agree_distinguish_unknown_and_crash_distinct() {
    let kinds = [
        OracleKind::ExitStop,
        OracleKind::FinalResult,
        OracleKind::ConcreteOutput,
        OracleKind::Reachability,
        OracleKind::ExecutionPattern,
        OracleKind::StructuredPredicate,
    ];
    let left = OracleSide::Normal {
        value: SemanticJson::Bool(true),
        completeness: Completeness::CompleteFinite,
    };
    let same = left.clone();
    let different = OracleSide::Normal {
        value: SemanticJson::Bool(false),
        completeness: Completeness::CompleteFinite,
    };
    for kind in kinds {
        assert_eq!(
            compare_supplied(kind, CrashPolicy::Distinguish, &left, &same)
                .expect("complete values compare"),
            OracleOutcome::Agree
        );
        assert_eq!(
            compare_supplied(kind, CrashPolicy::Distinguish, &left, &different)
                .expect("complete values compare"),
            OracleOutcome::Distinguish
        );
        assert_eq!(
            compare_supplied(kind, CrashPolicy::Distinguish, &left, &OracleSide::Unknown)
                .expect("unknown is a typed outer outcome"),
            OracleOutcome::Unknown
        );
    }
    assert!(
        EvaluatorAuthority::finite_vector()
            .validate_k_authored()
            .is_err()
    );
    assert_eq!(
        compare_supplied(
            OracleKind::ExitStop,
            CrashPolicy::CompareIdentity,
            &OracleSide::SemanticCrash(artifact("semantic-crash", 'a')),
            &left,
        )
        .expect("mixed crash policy is typed"),
        OracleOutcome::Incomparable
    );
}

#[test]
fn bag16_collection_fold_requires_explicit_exhaustion_and_match_dominates_local_unknown() {
    let complete_empty = BranchCollection {
        visited: Vec::new(),
        pending_work: 0,
        stop: CollectionStop::Exhausted,
        empty_search_marker: true,
    };
    assert_eq!(
        derive_collection_decision(&complete_empty).expect("explicit empty exhaustion is valid"),
        CollectionDecision::NoMatch
    );
    let missing_marker = BranchCollection {
        empty_search_marker: false,
        ..complete_empty
    };
    assert!(derive_collection_decision(&missing_marker).is_err());
    let conclusive_match = BranchCollection {
        visited: vec![BranchDecision::Unknown, BranchDecision::Match],
        pending_work: 4,
        stop: CollectionStop::MatchFound,
        empty_search_marker: false,
    };
    assert_eq!(
        derive_collection_decision(&conclusive_match).expect("match fold is valid"),
        CollectionDecision::Match
    );
    let bounded_absence = BranchCollection {
        visited: vec![BranchDecision::NoMatch],
        pending_work: 1,
        stop: CollectionStop::Bounded,
        empty_search_marker: false,
    };
    assert_eq!(
        derive_collection_decision(&bounded_absence).expect("bounded fold is typed"),
        CollectionDecision::Unknown
    );
}

trait StatusName {
    fn frozen_name(self) -> &'static str;
}

impl StatusName for MutantStatus {
    fn frozen_name(self) -> &'static str {
        match self {
            MutantStatus::Killed => "killed",
            MutantStatus::Survived => "survived",
            MutantStatus::Invalid => "invalid",
            MutantStatus::Timeout => "timeout",
            MutantStatus::Unknown => "unknown",
            MutantStatus::Error => "error",
        }
    }
}
