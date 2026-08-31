use kink_campaign::{
    CacheFailureKind, CacheRecord, CacheStore, CampaignReport, CompletionClass,
    InvocationFailureKind, MaterialEligibility, MutantReport, MutantStatus, OperationReceipt,
    PortableProductionWitness, Publication, ReuseClass, ScheduleMode, ScriptedReceipt,
    WorkerFailureClassification, WorkerResult, WorkerResultKind, WorkerTerminal,
};
use kink_contracts::{Completeness, EvidenceClass, NativeConformance};
use kink_portable::{Digest, DigestDomain, SemanticJson, digest_without_field, parse_json};
use serde_json::Value;
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

fn package_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("investigations/backend-agnostic-goal-closure")
}

fn read(relative: &str) -> SemanticJson {
    parse_json(&fs::read(package_root().join(relative)).expect("frozen file is readable"))
        .expect("frozen file is restricted JSON")
}

fn refresh(value: &mut SemanticJson, field: &str, domain: &str) {
    let digest = digest_without_field(
        &DigestDomain::new(domain).expect("test domain is valid"),
        value,
        field,
    )
    .expect("mutated value is semantic JSON");
    value
        .as_object_mut_for_test()
        .insert(field.to_owned(), SemanticJson::String(digest.to_string()));
}

trait ObjectMut {
    fn as_object_mut_for_test(&mut self) -> &mut BTreeMap<String, SemanticJson>;
}

impl ObjectMut for SemanticJson {
    fn as_object_mut_for_test(&mut self) -> &mut BTreeMap<String, SemanticJson> {
        let SemanticJson::Object(fields) = self else {
            panic!("test value is not an object")
        };
        fields
    }
}

#[test]
fn all_seven_receipt_and_wrapper_shapes_run_through_schema_and_rust_correspondence() {
    let pairs = [
        (
            "material/bag15-receipt-materialization.json",
            "material/bag15-materialization-result.json",
        ),
        (
            "material/bag15-receipt-execution-b20cd6744f39666b2e95eb0cd0460ad0b6cff25143ced9a06065f7ddebf041f8.json",
            "material/bag15-execution-result-b20cd6744f39666b2e95eb0cd0460ad0b6cff25143ced9a06065f7ddebf041f8.json",
        ),
        (
            "material/bag15-receipt-operand-69209b2dd8ccb71c27d10336c3912c6ddcf6e5aa0d63ae61a601ff9670c56f2d.json",
            "material/bag15-operand-result-69209b2dd8ccb71c27d10336c3912c6ddcf6e5aa0d63ae61a601ff9670c56f2d.json",
        ),
        (
            "material/bag15-receipt-baseline-admission-59bac8d4df058c319361d359367ec775462a94dc09d453894709a8faaf7eba03.json",
            "material/bag15-baseline-admission-result-59bac8d4df058c319361d359367ec775462a94dc09d453894709a8faaf7eba03.json",
        ),
        (
            "material/bag15-receipt-oracle-comparison-c96237c839da4d98e38f9665c86dbe7671ac4964a7801e83dca7f09c86631d70.json",
            "material/bag15-oracle-comparison-production-result-c96237c839da4d98e38f9665c86dbe7671ac4964a7801e83dca7f09c86631d70.json",
        ),
        (
            "material/bag15-receipt-derivation-full.json",
            "material/bag15-derivation-result-full.json",
        ),
        (
            "material/bag15-receipt-publication-full.json",
            "material/bag15-publication-result-full.json",
        ),
    ];
    let mut operations = std::collections::BTreeSet::new();
    for (receipt_path, wrapper_path) in pairs {
        let receipt = read(receipt_path);
        let wrapper = read(wrapper_path);
        let validated = OperationReceipt::validate_portable_bundle(&receipt, &wrapper)
            .unwrap_or_else(|error| panic!("{receipt_path}: {error}"));
        operations.insert(validated.operation().as_str());
    }
    assert_eq!(operations.len(), 7);
}

#[test]
fn wrapper_terminal_drift_rejects_after_every_outer_identity_is_refreshed() {
    let mut receipt = read(
        "material/bag15-receipt-execution-b20cd6744f39666b2e95eb0cd0460ad0b6cff25143ced9a06065f7ddebf041f8.json",
    );
    let mut wrapper = read(
        "material/bag15-execution-result-b20cd6744f39666b2e95eb0cd0460ad0b6cff25143ced9a06065f7ddebf041f8.json",
    );
    wrapper
        .as_object_mut_for_test()
        .get_mut("terminalRecord")
        .expect("terminal")
        .as_object_mut_for_test()
        .insert("kind".to_owned(), SemanticJson::String("stuck".to_owned()));
    refresh(
        &mut wrapper,
        "resultId",
        "k-in-k/execution-attempt-result/v1",
    );
    let wrapper_id = wrapper
        .as_object()
        .and_then(|fields| fields.get("resultId"))
        .and_then(SemanticJson::as_str)
        .expect("wrapper ID")
        .to_owned();
    let receipt_fields = receipt.as_object_mut_for_test();
    receipt_fields
        .get_mut("outputs")
        .and_then(|outputs| match outputs {
            SemanticJson::Array(outputs) => outputs.first_mut(),
            _ => None,
        })
        .expect("receipt output")
        .as_object_mut_for_test()
        .get_mut("artifact")
        .expect("output artifact")
        .as_object_mut_for_test()
        .insert("digest".to_owned(), SemanticJson::String(wrapper_id));
    refresh(&mut receipt, "receiptId", "k-in-k/operation-receipt/v1");
    assert_eq!(
        OperationReceipt::validate_portable_bundle(&receipt, &wrapper)
            .expect_err("receipt terminal must not be trusted")
            .kind(),
        InvocationFailureKind::WrapperCorrespondence
    );
}

#[test]
fn worker_parses_closed_bag10_placements_and_cannot_promote_scripted_results() {
    let bounded_record = read("material/bag14-cache-record-bounded-attempt.json");
    let bounded_terminal = bounded_record
        .as_object()
        .and_then(|fields| fields.get("terminalRecord"))
        .expect("bounded terminal");
    let terminal = WorkerTerminal::from_portable_json(bounded_terminal)
        .expect("frozen bounded placement validates");
    let result = WorkerResult::scripted(terminal, Vec::new(), Completeness::CompleteFinite);
    assert_eq!(result.kind(), WorkerResultKind::Bounded);
    assert_eq!(result.evidence(), EvidenceClass::Scripted);
    assert_eq!(result.native_conformance(), NativeConformance::NotProven);

    let diagnostic = read("material/bag14-cache-record-diagnostic-attempt.json");
    let terminal = diagnostic
        .as_object()
        .and_then(|fields| fields.get("terminalRecord"))
        .expect("diagnostic terminal");
    let parsed = WorkerTerminal::from_portable_json(terminal)
        .expect("frozen diagnostic placement validates");
    let WorkerTerminal::Infrastructure(failure) = parsed else {
        panic!("worker-lost must remain infrastructure")
    };
    assert_eq!(
        failure.classification(),
        WorkerFailureClassification::WorkerLost
    );

    let mut forged = bounded_terminal.clone();
    forged.as_object_mut_for_test().insert(
        "classification".to_owned(),
        SemanticJson::String("host-exception".to_owned()),
    );
    assert!(WorkerTerminal::from_portable_json(&forged).is_err());
}

fn bag14_records() -> BTreeMap<String, CacheRecord> {
    let material = package_root().join("material");
    let mut records = BTreeMap::new();
    for entry in fs::read_dir(material).expect("material directory exists") {
        let path = entry.expect("entry is readable").path();
        let Some(name) = path.file_name().and_then(|name| name.to_str()) else {
            continue;
        };
        if !name.starts_with("bag14-cache-record-") {
            continue;
        }
        let value =
            parse_json(&fs::read(&path).expect("record is readable")).expect("record is JSON");
        let record =
            CacheRecord::from_portable_json(&value, PortableProductionWitness::BundledFiniteVector)
                .unwrap_or_else(|error| panic!("{}: {error}", path.display()));
        records.insert(record.record_id().to_string(), record);
    }
    assert_eq!(records.len(), 12);
    records
}

#[test]
fn every_bag14_key_record_and_authority_row_is_rederived() {
    let records = bag14_records();
    assert_eq!(
        records
            .values()
            .filter(|record| record.reuse_class() == ReuseClass::SemanticResult)
            .count(),
        10
    );
    assert_eq!(
        records
            .values()
            .filter(|record| record.completion() == CompletionClass::ExactBoundedAttempt)
            .count(),
        1
    );
    assert_eq!(
        records
            .values()
            .filter(|record| record.reuse_class() == ReuseClass::NotReusable)
            .count(),
        1
    );
}

#[test]
fn nested_key_and_output_drift_reject_after_outer_record_refresh() {
    let mut key_drift = read("material/bag14-cache-record-baseline-execution-t1.json");
    let fields = key_drift.as_object_mut_for_test();
    fields
        .get_mut("key")
        .expect("key")
        .as_object_mut_for_test()
        .insert(
            "testInvocationDigest".to_owned(),
            SemanticJson::String("a".repeat(64)),
        );
    refresh(&mut key_drift, "recordId", "k-in-k/cache-record/v1");
    assert_eq!(
        CacheRecord::from_portable_json(
            &key_drift,
            PortableProductionWitness::BundledFiniteVector,
        )
        .expect_err("nested key drift must reject")
        .kind(),
        CacheFailureKind::KeyDigestMismatch
    );

    let mut output_drift = read("material/bag14-cache-record-baseline-execution-t1.json");
    let fields = output_drift.as_object_mut_for_test();
    let SemanticJson::Array(outputs) = fields
        .get_mut("producedArtifacts")
        .expect("produced artifacts")
    else {
        panic!("outputs are not an array")
    };
    outputs.reverse();
    refresh(&mut output_drift, "recordId", "k-in-k/cache-record/v1");
    assert_eq!(
        CacheRecord::from_portable_json(
            &output_drift,
            PortableProductionWitness::BundledFiniteVector,
        )
        .expect_err("ordered output drift must reject")
        .kind(),
        CacheFailureKind::OutputMismatch
    );
}

#[test]
fn forged_native_authority_and_failed_producers_never_expose_a_record() {
    let mut forged = read("material/bag14-cache-record-baseline-execution-t1.json");
    forged
        .as_object_mut_for_test()
        .get_mut("completion")
        .expect("completion")
        .as_object_mut_for_test()
        .insert(
            "executionConformance".to_owned(),
            SemanticJson::String("native-proven".to_owned()),
        );
    refresh(&mut forged, "recordId", "k-in-k/cache-record/v1");
    assert_eq!(
        CacheRecord::from_portable_json(&forged, PortableProductionWitness::BundledFiniteVector,)
            .expect_err("finite label must not become native authority")
            .kind(),
        CacheFailureKind::NativeAuthorityUnavailable
    );

    let failed = read("material/bag15-receipt-failed-producer.json");
    assert!(OperationReceipt::validate_portable_json(&failed).is_ok());
    let wrapper = read(
        "material/bag15-execution-result-b20cd6744f39666b2e95eb0cd0460ad0b6cff25143ced9a06065f7ddebf041f8.json",
    );
    assert_eq!(
        OperationReceipt::validate_portable_bundle(&failed, &wrapper)
            .expect_err("failed producer has no wrapper")
            .kind(),
        InvocationFailureKind::FailedProducerOutput
    );

    let records = bag14_records();
    let source = &records["a2bac6818309965a9357104c4e5821df3350d0a6dcd28eb7d5209263818c3a3d"];
    let invocation = kink_campaign::OperationInvocation::new(
        kink_campaign::OperationKind::ExecutionAttempt,
        1,
        kink_campaign::AdapterContract {
            adapter_id: "rp03-failed".to_owned(),
            adapter_version: 1,
        },
        SemanticJson::Object(BTreeMap::new()),
        Vec::new(),
        Vec::new(),
    )
    .expect("scripted invocation");
    let failed = ScriptedReceipt::failed(
        invocation,
        kink_campaign::Producer::scripted("rp03-failed", 1),
    );
    assert_eq!(
        CacheRecord::scripted_diagnostic(
            source.key().clone(),
            source.terminal_record().clone(),
            source.produced_artifacts().to_vec(),
            MaterialEligibility::Eligible,
            &failed,
        )
        .expect_err("failed producer cannot expose a cache record")
        .kind(),
        CacheFailureKind::ProducerFailed
    );
}

#[test]
fn all_receipt_backed_cache_records_validate_exact_wrapper_correspondence() {
    let triples = [
        (
            "b20cd6744f39666b2e95eb0cd0460ad0b6cff25143ced9a06065f7ddebf041f8",
            "execution",
            "execution-result",
        ),
        (
            "c2d3fe566e13442711609e0f36de6c952f98ef5a1cd21f2166bb5e34a7ffe4bd",
            "execution",
            "execution-result",
        ),
        (
            "3bf9681f820854b5b153a408d48991a94f7900b14cbe3274bd950e2a0cce7c4d",
            "execution",
            "execution-result",
        ),
        (
            "a4a717f787be8bf61a94d69b348ecd592f4606e1520c1012ac79a46de62c6bbd",
            "execution",
            "execution-result",
        ),
        (
            "817974ee3eac690c33f2d9707e20f01aa11a73beca3f42e729b78273a22a5a24",
            "execution",
            "execution-result",
        ),
        (
            "a2bac6818309965a9357104c4e5821df3350d0a6dcd28eb7d5209263818c3a3d",
            "execution",
            "execution-result",
        ),
        (
            "59bac8d4df058c319361d359367ec775462a94dc09d453894709a8faaf7eba03",
            "baseline-admission",
            "baseline-admission-result",
        ),
        (
            "51fc16c7373cef65853a8289d4ead5842f2e568c0db0b37559df653306b63c35",
            "baseline-admission",
            "baseline-admission-result",
        ),
        (
            "3c043d492bbe91e05087f36691ceb893bc826141030b39b70b1b597d0a0ef9ab",
            "baseline-admission",
            "baseline-admission-result",
        ),
        (
            "c96237c839da4d98e38f9665c86dbe7671ac4964a7801e83dca7f09c86631d70",
            "oracle-comparison",
            "oracle-comparison-production-result",
        ),
        (
            "33e2e1ae92fb14142d3ceaf08eda6b1214b0373db55b9ca148867188627c1e2e",
            "oracle-comparison",
            "oracle-comparison-production-result",
        ),
        (
            "4b941c424649b5c3856b551b8a0d5c2d0d6a6fbf27680c60d9761d11d5f2ddef",
            "oracle-comparison",
            "oracle-comparison-production-result",
        ),
    ];
    for (suffix, receipt_kind, result_kind) in triples {
        let record = read(&format!("material/bag15-cache-record-{suffix}.json"));
        let receipt = read(&format!(
            "material/bag15-receipt-{receipt_kind}-{suffix}.json"
        ));
        let result = read(&format!("material/bag15-{result_kind}-{suffix}.json"));
        CacheRecord::from_portable_json(
            &record,
            PortableProductionWitness::BundledOperationReceipt {
                receipt: &receipt,
                result: &result,
            },
        )
        .unwrap_or_else(|error| panic!("{suffix}: {error}"));
    }
}

#[test]
fn uncached_partial_and_full_hit_folds_execute_cache_and_match_semantic_reports() {
    let records = bag14_records();
    let vectors: Value = serde_json::from_slice(
        &fs::read(package_root().join("vectors/cache-semantics-vectors.json"))
            .expect("vectors are readable"),
    )
    .expect("vectors are JSON");
    for fold in vectors["scheduleFolds"].as_array().expect("schedule folds") {
        let schedule = match fold["scheduleMode"].as_str().expect("schedule") {
            "first-kill" => ScheduleMode::FirstKill,
            "full" => ScheduleMode::Full,
            other => panic!("unknown schedule {other}"),
        };
        let mut reports = Vec::new();
        for materialization in fold["materializations"]
            .as_array()
            .expect("materializations")
        {
            let sources = materialization["recordSources"]
                .as_array()
                .expect("record sources");
            let mut store = CacheStore::default();
            for source in sources {
                if source["source"] == "cache-hit" {
                    let id = source["recordId"].as_str().expect("record ID");
                    assert_eq!(store.publish(records[id].clone()), Publication::Published);
                }
            }
            let mut selected = Vec::new();
            for source in sources {
                let id = source["recordId"].as_str().expect("record ID");
                let record = &records[id];
                if source["source"] == "executed" {
                    assert_eq!(store.publish(record.clone()), Publication::Published);
                }
                let selected_record = store
                    .reusable(record.key().key_digest())
                    .expect("selected slot has a reusable record");
                assert_eq!(selected_record.record_id().as_str(), id);
                selected.push(selected_record.record_id().clone());
            }
            let mutant = MutantReport {
                mutant_id: Digest::parse(&"a".repeat(64)).expect("digest"),
                status: MutantStatus::Killed,
                executed_test_ids: vec!["t1".to_owned()],
                killing_test_ids: vec!["t1".to_owned()],
                skipped_test_ids: Vec::new(),
            };
            reports.push(
                CampaignReport::new(schedule, selected, vec![mutant])
                    .expect("semantic report derives from selected records"),
            );
        }
        assert!(
            reports
                .windows(2)
                .all(|pair| pair[0].report_id == pair[1].report_id
                    && pair[0].campaign_invocation_id == pair[1].campaign_invocation_id)
        );
    }
}

#[test]
fn conflicting_validated_records_permanently_quarantine_the_key() {
    let records = bag14_records();
    let finite = &records["a2bac6818309965a9357104c4e5821df3350d0a6dcd28eb7d5209263818c3a3d"];
    let receipt = kink_campaign::Producer::scripted("rp03-conflict", 1);
    let invocation = kink_campaign::OperationInvocation::new(
        kink_campaign::OperationKind::ExecutionAttempt,
        1,
        kink_campaign::AdapterContract {
            adapter_id: "rp03-scripted".to_owned(),
            adapter_version: 1,
        },
        SemanticJson::Object(BTreeMap::new()),
        Vec::new(),
        Vec::new(),
    )
    .expect("scripted invocation");
    let operation_receipt = ScriptedReceipt::complete(
        invocation,
        receipt,
        kink_campaign::ReceiptOutput {
            wrapper: kink_campaign::ArtifactKey::new(
                "execution-attempt-result",
                Digest::parse(&"b".repeat(64)).expect("digest"),
            )
            .expect("artifact"),
            semantic_terminal: None,
            produced_artifacts: finite.produced_artifacts().to_vec(),
            completeness: Completeness::Unknown,
        },
    )
    .expect("scripted receipt");
    let first = CacheRecord::scripted_diagnostic(
        finite.key().clone(),
        finite.terminal_record().clone(),
        finite.produced_artifacts().to_vec(),
        MaterialEligibility::Eligible,
        &operation_receipt,
    )
    .expect("first diagnostic");
    let mut second_terminal = finite.terminal_record().clone();
    let failure = second_terminal
        .as_object_mut_for_test()
        .get_mut("failure")
        .expect("failure")
        .as_object_mut_for_test();
    failure.insert(
        "classification".to_owned(),
        SemanticJson::String("internal".to_owned()),
    );
    failure.insert(
        "retryability".to_owned(),
        SemanticJson::String("never".to_owned()),
    );
    let second = CacheRecord::scripted_diagnostic(
        finite.key().clone(),
        second_terminal,
        finite.produced_artifacts().to_vec(),
        MaterialEligibility::Eligible,
        &operation_receipt,
    )
    .expect("second diagnostic");
    let key = finite.key().key_digest().clone();
    let mut store = CacheStore::default();
    assert_eq!(store.publish(first), Publication::Published);
    assert_eq!(store.publish(second), Publication::Quarantined);
    assert!(store.is_quarantined(&key));
    assert!(store.reusable(&key).is_none());
    assert_eq!(
        store.publish(
            CacheRecord::scripted_diagnostic(
                finite.key().clone(),
                finite.terminal_record().clone(),
                finite.produced_artifacts().to_vec(),
                MaterialEligibility::Eligible,
                &operation_receipt,
            )
            .expect("repeat diagnostic"),
        ),
        Publication::Quarantined
    );
}
