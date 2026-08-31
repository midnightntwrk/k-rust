use kink_campaign::{
    AdapterContract, ArtifactKey, CacheRecord, DurableArtifactInput, DurableCacheFailpoint,
    DurableCacheFailureKind, DurableCachePublication, DurableCacheStore, DurableConflictState,
    MaterialEligibility, OperationInvocation, OperationKind, PortableProductionWitness, Producer,
    ReceiptOutput, ScriptedReceipt,
};
use kink_contracts::Completeness;
use kink_portable::{
    ArtifactCatalogEntry, Digest, DigestDomain, DurableArtifactAuthority, DurableArtifactFailpoint,
    DurableArtifactFailureKind, DurableArtifactStore, SemanticJson, canonical_json_bytes,
    digest_without_field, parse_json,
};
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static TEMP_NONCE: AtomicU64 = AtomicU64::new(0);
const SUBPROCESS_ROOT: &str = "KINK_DURABLE_CACHE_SUBPROCESS_ROOT";
const FINITE_RECORD: &str = "material/bag14-cache-record-baseline-execution-t1.json";

struct TestDirectory(PathBuf);

impl TestDirectory {
    fn new(label: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "kink-{label}-{}-{}",
            std::process::id(),
            TEMP_NONCE.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).expect("unique test directory is created");
        Self(path)
    }
}

impl Drop for TestDirectory {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

struct OutputFixture {
    entries: Vec<ArtifactCatalogEntry>,
    bytes: Vec<Vec<u8>>,
    catalog_bytes: Vec<u8>,
}

impl OutputFixture {
    fn inputs(&self) -> Vec<DurableArtifactInput<'_>> {
        self.entries
            .iter()
            .zip(&self.bytes)
            .map(|(entry, bytes)| DurableArtifactInput { entry, bytes })
            .collect()
    }
}

fn repository_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn package_root() -> PathBuf {
    repository_root().join("investigations/backend-agnostic-goal-closure")
}

fn load_record(relative: &str) -> CacheRecord {
    let value = parse_json(&fs::read(package_root().join(relative)).expect("record is readable"))
        .expect("record is restricted JSON");
    CacheRecord::from_portable_json(&value, PortableProductionWitness::BundledFiniteVector)
        .expect("frozen finite record validates")
}

fn output_fixture(record: &CacheRecord) -> OutputFixture {
    let bundled_catalog = parse_json(
        &fs::read(package_root().join("fixtures/bag14-cache-artifact-catalog.json"))
            .expect("cache artifact catalog is readable"),
    )
    .expect("cache artifact catalog is restricted JSON");
    let rows = bundled_catalog
        .as_object()
        .and_then(|fields| fields.get("entries"))
        .and_then(SemanticJson::as_array)
        .expect("catalog entries exist");
    let mut entries = Vec::new();
    let mut bytes = Vec::new();
    let mut external_rows = Vec::new();
    for key in record.produced_artifacts() {
        let row = rows
            .iter()
            .find(|row| {
                let fields = row.as_object().expect("catalog row is an object");
                fields.get("role").and_then(SemanticJson::as_str) == Some(key.role.as_str())
                    && fields.get("digest").and_then(SemanticJson::as_str)
                        == Some(key.digest.as_str())
            })
            .expect("record output has one catalog entry");
        let source = row
            .as_object()
            .and_then(|fields| fields.get("logicalPath"))
            .and_then(SemanticJson::as_str)
            .and_then(|value| value.strip_prefix("repo://"))
            .expect("frozen output is bundled");
        bytes.push(fs::read(repository_root().join(source)).expect("output bytes are readable"));

        let mut external = row.clone();
        let SemanticJson::Object(fields) = &mut external else {
            unreachable!("catalog row is an object")
        };
        fields.insert(
            "availability".to_owned(),
            SemanticJson::String("external-required".to_owned()),
        );
        fields.insert(
            "logicalPath".to_owned(),
            SemanticJson::String(format!(
                "artifact://cache-outputs/{}/{}.json",
                key.role, key.digest
            )),
        );
        fields.insert(
            "resolverId".to_owned(),
            SemanticJson::String("rust-artifact-store-v1".to_owned()),
        );
        entries.push(
            ArtifactCatalogEntry::from_json(&external)
                .expect("transport-adjusted catalog entry validates"),
        );
        external_rows.push(external);
    }
    if external_rows.is_empty() {
        let mut authority_only = rows[0].clone();
        let SemanticJson::Object(fields) = &mut authority_only else {
            unreachable!("catalog row is an object")
        };
        fields.insert(
            "availability".to_owned(),
            SemanticJson::String("external-required".to_owned()),
        );
        fields.insert(
            "logicalPath".to_owned(),
            SemanticJson::String("artifact://cache-outputs/authority-only.json".to_owned()),
        );
        fields.insert(
            "resolverId".to_owned(),
            SemanticJson::String("rust-artifact-store-v1".to_owned()),
        );
        external_rows.push(authority_only);
    }
    OutputFixture {
        entries,
        bytes,
        catalog_bytes: catalog(&external_rows),
    }
}

fn catalog(rows: &[SemanticJson]) -> Vec<u8> {
    let mut catalog = SemanticJson::Object(BTreeMap::from([
        ("catalogId".to_owned(), SemanticJson::String("0".repeat(64))),
        ("entries".to_owned(), SemanticJson::Array(rows.to_vec())),
        ("schemaVersion".to_owned(), SemanticJson::Integer(1)),
        (
            "unboundRequirements".to_owned(),
            SemanticJson::Array(Vec::new()),
        ),
    ]));
    let id = digest_without_field(
        &DigestDomain::new("k-in-k/artifact-catalog/v1").expect("domain is valid"),
        &catalog,
        "catalogId",
    )
    .expect("catalog identity derives");
    let SemanticJson::Object(fields) = &mut catalog else {
        unreachable!("catalog is object")
    };
    fields.insert("catalogId".to_owned(), SemanticJson::String(id.to_string()));
    canonical_json_bytes(&catalog).expect("catalog encodes canonically")
}

fn stores(root: &Path, outputs: &OutputFixture) -> (DurableCacheStore, DurableArtifactStore) {
    let authority = DurableArtifactAuthority::from_repository_catalog(
        &repository_root(),
        &outputs.catalog_bytes,
    )
    .expect("output authority validates");
    (
        DurableCacheStore::open(&root.join("cache")).expect("cache store opens"),
        DurableArtifactStore::open(&root.join("artifacts"), authority)
            .expect("artifact store opens"),
    )
}

fn publish_finite(root: &Path) -> DurableCachePublication {
    let record = load_record(FINITE_RECORD);
    let outputs = output_fixture(&record);
    let (cache, artifacts) = stores(root, &outputs);
    cache
        .publish(&record, &outputs.inputs(), &artifacts)
        .expect("finite record publishes")
}

#[test]
fn output_before_record_publication_reopens_and_revalidates() {
    let directory = TestDirectory::new("durable-cache-basic");
    let record = load_record(FINITE_RECORD);
    let outputs = output_fixture(&record);
    let key = record.key().key_digest().clone();
    let (cache, artifacts) = stores(&directory.0, &outputs);

    assert_eq!(
        cache
            .publish(&record, &outputs.inputs(), &artifacts)
            .expect("first publication succeeds"),
        DurableCachePublication::Published
    );
    assert_eq!(
        cache
            .publish(&record, &outputs.inputs(), &artifacts)
            .expect("identical publication succeeds"),
        DurableCachePublication::AlreadyPresent
    );
    drop(cache);
    drop(artifacts);

    let (cache, artifacts) = stores(&directory.0, &outputs);
    let reused = cache
        .reusable(
            &key,
            PortableProductionWitness::BundledFiniteVector,
            &outputs.entries,
            &artifacts,
        )
        .expect("reopened record revalidates")
        .expect("semantic record is reusable");
    assert_eq!(reused.record_id(), record.record_id());
}

#[test]
fn canonical_record_sidecar_cannot_borrow_an_unrelated_committed_transaction() {
    let directory = TestDirectory::new("durable-cache-transaction-closure");
    let record = load_record(FINITE_RECORD);
    let outputs = output_fixture(&record);
    let key = record.key().key_digest().clone();
    let (cache, artifacts) = stores(&directory.0, &outputs);
    cache
        .publish(&record, &outputs.inputs(), &artifacts)
        .expect("complete output transaction publishes");

    let inputs = outputs.inputs();
    let unrelated = artifacts
        .prepare_transaction(&inputs[..1])
        .expect("a different committed subset transaction can coexist");
    let unrelated_id = unrelated.id().clone();
    unrelated.commit().expect("subset transaction commits");

    let sidecar_path = cache
        .root()
        .join("record-transactions")
        .join(format!("{key}.json"));
    let mut sidecar = parse_json(&fs::read(&sidecar_path).expect("sidecar is readable"))
        .expect("sidecar is restricted JSON");
    let SemanticJson::Object(fields) = &mut sidecar else {
        panic!("record sidecar is an object")
    };
    fields.insert(
        "artifactTransactionId".to_owned(),
        SemanticJson::String(unrelated_id.to_string()),
    );
    fs::write(
        &sidecar_path,
        canonical_json_bytes(&sidecar).expect("forged sidecar is canonical"),
    )
    .expect("test installs a canonical but semantically mismatched sidecar");

    assert_eq!(
        cache
            .reusable(
                &key,
                PortableProductionWitness::BundledFiniteVector,
                &outputs.entries,
                &artifacts,
            )
            .expect_err("an unrelated committed transaction cannot authorize this record")
            .kind(),
        DurableCacheFailureKind::CorruptRecord
    );
}

#[test]
fn sequence_and_prepublication_ingress_failures_expose_no_record_or_output() {
    let directory = TestDirectory::new("durable-cache-ordering");
    let record = load_record(FINITE_RECORD);
    let outputs = output_fixture(&record);
    let key = record.key().key_digest().clone();
    let (cache, artifacts) = stores(&directory.0, &outputs);

    let mut reversed = outputs.inputs();
    reversed.reverse();
    assert_eq!(
        cache
            .publish(&record, &reversed, &artifacts)
            .expect_err("reordered outputs reject")
            .kind(),
        DurableCacheFailureKind::InvalidOutputSequence
    );

    let mut corrupt_bytes = outputs.bytes.clone();
    corrupt_bytes[1].push(b'!');
    let corrupt_inputs = outputs
        .entries
        .iter()
        .zip(&corrupt_bytes)
        .map(|(entry, bytes)| DurableArtifactInput { entry, bytes })
        .collect::<Vec<_>>();
    assert_eq!(
        cache
            .publish(&record, &corrupt_inputs, &artifacts)
            .expect_err("one invalid output rejects the complete publication")
            .kind(),
        DurableCacheFailureKind::ArtifactPublication
    );
    assert!(
        cache
            .reusable(
                &key,
                PortableProductionWitness::BundledFiniteVector,
                &outputs.entries,
                &artifacts,
            )
            .expect("absent record is a miss")
            .is_none()
    );
    assert_eq!(
        artifacts
            .ingest(&outputs.entries[0])
            .expect_err("preflight failure publishes no earlier output")
            .kind(),
        DurableArtifactFailureKind::Uncommitted
    );

    let mut duplicate_locator_entries = outputs.entries.clone();
    duplicate_locator_entries[1].locator = duplicate_locator_entries[0].locator.clone();
    let duplicate_inputs = duplicate_locator_entries
        .iter()
        .zip(&outputs.bytes)
        .map(|(entry, bytes)| DurableArtifactInput { entry, bytes })
        .collect::<Vec<_>>();
    assert_eq!(
        cache
            .publish(&record, &duplicate_inputs, &artifacts)
            .expect_err("one normalized locator cannot identify two outputs")
            .kind(),
        DurableCacheFailureKind::InvalidOutputSequence
    );
}

#[test]
fn record_sync_and_rename_failures_expose_no_record_or_accepted_output() {
    for point in [
        DurableCacheFailpoint::BeforeRecordStageSync,
        DurableCacheFailpoint::BeforeRecordRename,
    ] {
        let directory = TestDirectory::new("durable-cache-record-failpoint");
        let record = load_record(FINITE_RECORD);
        let outputs = output_fixture(&record);
        let key = record.key().key_digest().clone();
        let (cache, artifacts) = stores(&directory.0, &outputs);
        let failing = cache.clone().with_failpoint(point);

        assert_eq!(
            failing
                .publish(&record, &outputs.inputs(), &artifacts)
                .expect_err("record publication failure is injected")
                .kind(),
            DurableCacheFailureKind::Io
        );
        assert!(
            cache
                .reusable(
                    &key,
                    PortableProductionWitness::BundledFiniteVector,
                    &outputs.entries,
                    &artifacts,
                )
                .expect("failed publication is a cache miss")
                .is_none()
        );
        for entry in &outputs.entries {
            assert_eq!(
                artifacts
                    .ingest(entry)
                    .expect_err("record failure commits no output")
                    .kind(),
                DurableArtifactFailureKind::Uncommitted
            );
        }
    }
}

#[test]
fn late_artifact_failures_expose_no_reusable_record_or_accepted_output() {
    for point in [
        DurableArtifactFailpoint::AfterRawOutput(1),
        DurableArtifactFailpoint::BeforeTransactionCommit,
    ] {
        let directory = TestDirectory::new("durable-cache-artifact-failpoint");
        let record = load_record(FINITE_RECORD);
        let outputs = output_fixture(&record);
        let key = record.key().key_digest().clone();
        let (cache, artifacts) = stores(&directory.0, &outputs);
        let failing_artifacts = artifacts.clone().with_failpoint(point);

        assert_eq!(
            cache
                .publish(&record, &outputs.inputs(), &failing_artifacts)
                .expect_err("artifact transaction failure is injected")
                .kind(),
            DurableCacheFailureKind::ArtifactPublication
        );
        assert!(
            cache
                .reusable(
                    &key,
                    PortableProductionWitness::BundledFiniteVector,
                    &outputs.entries,
                    &artifacts,
                )
                .expect("uncommitted transaction is a cache miss")
                .is_none()
        );
        for entry in &outputs.entries {
            assert_eq!(
                artifacts
                    .ingest(entry)
                    .expect_err("late failure accepts no output")
                    .kind(),
                DurableArtifactFailureKind::Uncommitted
            );
        }
    }
}

#[test]
fn readers_reject_missing_corrupt_and_misordered_output_closure() {
    let directory = TestDirectory::new("durable-cache-output-corruption");
    let record = load_record(FINITE_RECORD);
    let outputs = output_fixture(&record);
    let key = record.key().key_digest().clone();
    let (cache, artifacts) = stores(&directory.0, &outputs);
    cache
        .publish(&record, &outputs.inputs(), &artifacts)
        .expect("record publishes");

    let mut reversed = outputs.entries.clone();
    reversed.reverse();
    assert_eq!(
        cache
            .reusable(
                &key,
                PortableProductionWitness::BundledFiniteVector,
                &reversed,
                &artifacts,
            )
            .expect_err("misordered output closure rejects")
            .kind(),
        DurableCacheFailureKind::MissingOutput
    );

    let first_path = artifacts
        .root()
        .join("objects")
        .join(outputs.entries[0].locator.tail());
    fs::remove_file(&first_path).expect("test removes one output");
    assert_eq!(
        cache
            .reusable(
                &key,
                PortableProductionWitness::BundledFiniteVector,
                &outputs.entries,
                &artifacts,
            )
            .expect_err("missing output rejects reuse")
            .kind(),
        DurableCacheFailureKind::MissingOutput
    );

    fs::write(&first_path, &outputs.bytes[0]).expect("test restores exact output");
    fs::write(&first_path, b"corrupt").expect("test corrupts output");
    assert_eq!(
        cache
            .reusable(
                &key,
                PortableProductionWitness::BundledFiniteVector,
                &outputs.entries,
                &artifacts,
            )
            .expect_err("corrupt output rejects reuse")
            .kind(),
        DurableCacheFailureKind::CorruptOutput
    );
}

#[test]
fn record_corruption_and_orphan_staging_fail_closed_across_restart() {
    let directory = TestDirectory::new("durable-cache-recovery");
    let record = load_record(FINITE_RECORD);
    let outputs = output_fixture(&record);
    let key = record.key().key_digest().clone();
    let (cache, artifacts) = stores(&directory.0, &outputs);
    cache
        .publish(&record, &outputs.inputs(), &artifacts)
        .expect("record publishes");
    let orphan = cache.root().join("staging/.interrupted");
    fs::write(&orphan, b"partial record").expect("orphan stage is created");
    drop(cache);

    #[cfg(target_os = "linux")]
    {
        let lock = directory.0.join("cache/locks").join(format!("{key}.lock"));
        fs::create_dir(&lock).expect("interrupted cache lock is created");
        fs::write(lock.join("owner"), b"4294967295 1 0\n")
            .expect("dead process identity is recorded");
    }

    let cache = DurableCacheStore::open(&directory.0.join("cache")).expect("cache reopens");
    assert_eq!(cache.recover().expect("recovery succeeds"), 1);
    assert!(!orphan.exists());
    fs::write(
        cache.root().join("records").join(format!("{key}.json")),
        b"{}",
    )
    .expect("test corrupts visible record");
    assert_eq!(
        cache
            .reusable(
                &key,
                PortableProductionWitness::BundledFiniteVector,
                &outputs.entries,
                &artifacts,
            )
            .expect_err("corrupt record rejects")
            .kind(),
        DurableCacheFailureKind::CorruptRecord
    );
}

fn scripted_conflict_records() -> (CacheRecord, CacheRecord) {
    let source = load_record("material/bag14-cache-record-diagnostic-attempt.json");
    let invocation = OperationInvocation::new(
        OperationKind::ExecutionAttempt,
        1,
        AdapterContract {
            adapter_id: "durable-cache-conflict".to_owned(),
            adapter_version: 1,
        },
        SemanticJson::Object(BTreeMap::new()),
        Vec::new(),
        Vec::new(),
    )
    .expect("scripted invocation validates");
    let receipt = ScriptedReceipt::complete(
        invocation,
        Producer::scripted("durable-cache-conflict", 1),
        ReceiptOutput {
            wrapper: ArtifactKey::new(
                "execution-attempt-result",
                Digest::parse(&"b".repeat(64)).expect("digest validates"),
            )
            .expect("wrapper key validates"),
            semantic_terminal: None,
            produced_artifacts: source.produced_artifacts().to_vec(),
            completeness: Completeness::Unknown,
        },
    )
    .expect("scripted receipt validates");
    let first = CacheRecord::scripted_diagnostic(
        source.key().clone(),
        source.terminal_record().clone(),
        source.produced_artifacts().to_vec(),
        MaterialEligibility::Eligible,
        &receipt,
    )
    .expect("first diagnostic validates");
    let mut terminal = source.terminal_record().clone();
    let SemanticJson::Object(terminal_fields) = &mut terminal else {
        unreachable!("terminal is an object")
    };
    let SemanticJson::Object(failure) = terminal_fields
        .get_mut("failure")
        .expect("diagnostic has a failure")
    else {
        unreachable!("failure is an object")
    };
    failure.insert(
        "classification".to_owned(),
        SemanticJson::String("internal".to_owned()),
    );
    failure.insert(
        "retryability".to_owned(),
        SemanticJson::String("never".to_owned()),
    );
    let second = CacheRecord::scripted_diagnostic(
        source.key().clone(),
        terminal,
        source.produced_artifacts().to_vec(),
        MaterialEligibility::Eligible,
        &receipt,
    )
    .expect("conflicting diagnostic validates");
    (first, second)
}

#[test]
fn conflicting_records_durably_quarantine_both_observations() {
    let directory = TestDirectory::new("durable-cache-conflict");
    let (first, second) = scripted_conflict_records();
    let outputs = output_fixture(&first);
    let key = first.key().key_digest().clone();
    let (cache, artifacts) = stores(&directory.0, &outputs);
    assert_eq!(
        cache
            .publish(&first, &outputs.inputs(), &artifacts)
            .expect("first diagnostic publishes"),
        DurableCachePublication::Published
    );
    assert_eq!(
        cache
            .publish(&second, &outputs.inputs(), &artifacts)
            .expect("conflict is recorded"),
        DurableCachePublication::Quarantined
    );
    assert_eq!(
        cache.conflict_state(&key).expect("state is readable"),
        DurableConflictState::QuarantinedPendingConsistencyRerun
    );
    let ledger = fs::read_to_string(cache.root().join("quarantine").join(format!("{key}.json")))
        .expect("quarantine marker is readable");
    assert!(ledger.contains("manual-consistency-rerun-v1"));
    assert!(ledger.contains("quarantined-pending-consistency-rerun"));
    assert_eq!(
        fs::read_dir(cache.root().join("conflicts").join(key.as_str()))
            .expect("conflict observations are readable")
            .count(),
        2
    );
    drop(cache);

    let cache = DurableCacheStore::open(&directory.0.join("cache")).expect("cache reopens");
    assert_eq!(
        cache.conflict_state(&key).expect("state survives restart"),
        DurableConflictState::QuarantinedPendingConsistencyRerun
    );
    assert_eq!(
        cache
            .publish(&first, &outputs.inputs(), &artifacts)
            .expect("repeat remains quarantined"),
        DurableCachePublication::Quarantined
    );
    assert_eq!(
        cache
            .reusable(
                &key,
                PortableProductionWitness::BundledFiniteVector,
                &outputs.entries,
                &artifacts,
            )
            .expect_err("quarantine selects no record")
            .kind(),
        DurableCacheFailureKind::Quarantined
    );

    let observation = fs::read_dir(cache.root().join("conflicts").join(key.as_str()))
        .expect("observation directory is readable")
        .next()
        .expect("an observation exists")
        .expect("observation directory entry is readable")
        .path();
    fs::write(observation, b"corrupt").expect("test corrupts one observation");
    assert_eq!(
        cache
            .conflict_state(&key)
            .expect_err("observation corruption is reported")
            .kind(),
        DurableCacheFailureKind::CorruptRecord
    );
    assert_eq!(
        cache
            .reusable(
                &key,
                PortableProductionWitness::BundledFiniteVector,
                &outputs.entries,
                &artifacts,
            )
            .expect_err("corrupt conflict evidence remains fail-closed")
            .kind(),
        DurableCacheFailureKind::Quarantined
    );
}

#[test]
fn cache_conflict_boundary_failure_still_selects_neither_record() {
    for point in [
        DurableCacheFailpoint::BeforeConflictMarker,
        DurableCacheFailpoint::AfterConflictMarker,
    ] {
        let directory = TestDirectory::new("durable-cache-conflict-boundary");
        let (first, second) = scripted_conflict_records();
        let outputs = output_fixture(&first);
        let key = first.key().key_digest().clone();
        let (cache, artifacts) = stores(&directory.0, &outputs);
        cache
            .publish(&first, &outputs.inputs(), &artifacts)
            .expect("first record publishes");
        let failing = cache.clone().with_failpoint(point);
        assert_eq!(
            failing
                .publish(&second, &outputs.inputs(), &artifacts)
                .expect_err("ledger-boundary failure is injected")
                .kind(),
            DurableCacheFailureKind::Io
        );
        assert_eq!(
            cache
                .reusable(
                    &key,
                    PortableProductionWitness::BundledFiniteVector,
                    &outputs.entries,
                    &artifacts,
                )
                .expect_err("conflict evidence selects neither record")
                .kind(),
            DurableCacheFailureKind::Quarantined
        );
    }
}

#[test]
fn subprocess_identical_cache_writer_helper() {
    let Some(root) = std::env::var_os(SUBPROCESS_ROOT) else {
        return;
    };
    assert!(matches!(
        publish_finite(Path::new(&root)),
        DurableCachePublication::Published | DurableCachePublication::AlreadyPresent
    ));
}

#[test]
fn concurrent_subprocess_writers_publish_one_reusable_record() {
    let directory = TestDirectory::new("durable-cache-processes");
    let mut children = Vec::new();
    for _ in 0..5 {
        children.push(
            Command::new(std::env::current_exe().expect("test executable is available"))
                .arg("--exact")
                .arg("subprocess_identical_cache_writer_helper")
                .arg("--nocapture")
                .env(SUBPROCESS_ROOT, &directory.0)
                .spawn()
                .expect("cache writer subprocess starts"),
        );
    }
    for mut child in children {
        assert!(
            child
                .wait()
                .expect("cache writer subprocess exits")
                .success()
        );
    }

    let record = load_record(FINITE_RECORD);
    let outputs = output_fixture(&record);
    let (cache, artifacts) = stores(&directory.0, &outputs);
    assert!(
        cache
            .reusable(
                record.key().key_digest(),
                PortableProductionWitness::BundledFiniteVector,
                &outputs.entries,
                &artifacts,
            )
            .expect("concurrent publication revalidates")
            .is_some()
    );
    assert!(
        fs::read_dir(cache.root().join("locks"))
            .expect("cache lock directory is readable")
            .next()
            .is_some()
    );
}
