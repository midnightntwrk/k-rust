use kink_contracts::{ArtifactAvailability, ArtifactLocator, ResolverId};
use kink_portable::{
    ArtifactCatalogEntry, DigestDomain, DurableArtifactAuthority, DurableArtifactConflictState,
    DurableArtifactFailpoint, DurableArtifactFailureKind, DurableArtifactInput,
    DurableArtifactPublication, DurableArtifactStore, DurableProcessLock, SemanticJson,
    canonical_json_bytes, digest, digest_without_field, sha256_bytes,
};
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
use std::thread;
use std::time::Duration;

static TEMP_NONCE: AtomicU64 = AtomicU64::new(0);
const SUBPROCESS_MODE: &str = "KINK_DURABLE_ARTIFACT_SUBPROCESS_MODE";
const SUBPROCESS_ROOT: &str = "KINK_DURABLE_ARTIFACT_SUBPROCESS_ROOT";
const SUBPROCESS_READY: &str = "KINK_DURABLE_ARTIFACT_SUBPROCESS_READY";

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

fn repository_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn opaque_row(locator: &str, bytes: &[u8]) -> SemanticJson {
    let content_sha256 = sha256_bytes(bytes);
    let envelope = SemanticJson::Object(BTreeMap::from([
        (
            "contentSha256".to_owned(),
            SemanticJson::String(content_sha256.to_string()),
        ),
        (
            "mediaType".to_owned(),
            SemanticJson::String("application/octet-stream".to_owned()),
        ),
        (
            "role".to_owned(),
            SemanticJson::String("execution-profile".to_owned()),
        ),
    ]));
    let semantic_digest = digest(
        &DigestDomain::new("k-in-k/opaque-artifact/v1").expect("domain is valid"),
        &envelope,
    )
    .expect("opaque envelope hashes");
    SemanticJson::Object(BTreeMap::from([
        (
            "availability".to_owned(),
            SemanticJson::String("external-required".to_owned()),
        ),
        (
            "contentModel".to_owned(),
            SemanticJson::String("opaque-bytes".to_owned()),
        ),
        (
            "contentSha256".to_owned(),
            SemanticJson::String(content_sha256.to_string()),
        ),
        (
            "digest".to_owned(),
            SemanticJson::String(semantic_digest.to_string()),
        ),
        (
            "logicalPath".to_owned(),
            SemanticJson::String(locator.to_owned()),
        ),
        (
            "mediaType".to_owned(),
            SemanticJson::String("application/octet-stream".to_owned()),
        ),
        (
            "resolverId".to_owned(),
            SemanticJson::String("rust-artifact-store-v1".to_owned()),
        ),
        (
            "role".to_owned(),
            SemanticJson::String("execution-profile".to_owned()),
        ),
    ]))
}

fn entry(row: &SemanticJson) -> ArtifactCatalogEntry {
    ArtifactCatalogEntry::from_json(row).expect("test catalog entry validates")
}

fn catalog(rows: &[SemanticJson]) -> Vec<u8> {
    let mut value = SemanticJson::Object(BTreeMap::from([
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
        &value,
        "catalogId",
    )
    .expect("catalog identity derives");
    let SemanticJson::Object(fields) = &mut value else {
        unreachable!("catalog is an object")
    };
    fields.insert("catalogId".to_owned(), SemanticJson::String(id.to_string()));
    canonical_json_bytes(&value).expect("catalog encodes canonically")
}

fn authority(rows: &[SemanticJson]) -> DurableArtifactAuthority {
    DurableArtifactAuthority::from_repository_catalog(&repository_root(), &catalog(rows))
        .expect("test authority validates")
}

fn open_store(root: &Path, rows: &[SemanticJson]) -> DurableArtifactStore {
    DurableArtifactStore::open(root, authority(rows)).expect("store opens")
}

fn object_path(store: &DurableArtifactStore, entry: &ArtifactCatalogEntry) -> PathBuf {
    store.root().join("objects").join(entry.locator.tail())
}

fn quarantine_path(store: &DurableArtifactStore, entry: &ArtifactCatalogEntry) -> PathBuf {
    store.root().join("quarantine").join(format!(
        "{}.json",
        sha256_bytes(entry.locator.normalized().as_bytes())
    ))
}

#[test]
fn publication_is_catalog_bound_idempotent_and_strictly_ingressed() {
    let directory = TestDirectory::new("durable-artifact-basic");
    let bytes = b"opaque execution profile";
    let row = opaque_row("artifact://profiles/execution/profile.bin", bytes);
    let entry = entry(&row);
    let store = open_store(&directory.0, std::slice::from_ref(&row));

    assert_eq!(
        store
            .publish(&entry, bytes.to_vec())
            .expect("first publication succeeds"),
        DurableArtifactPublication::Published
    );
    assert_eq!(
        store
            .publish(&entry, bytes.to_vec())
            .expect("identical publication succeeds"),
        DurableArtifactPublication::AlreadyPresent
    );
    assert_eq!(store.ingest(&entry).expect("ingress succeeds").bytes, bytes);
    assert_eq!(
        store
            .publish(&entry, b"different".to_vec())
            .expect_err("metadata-inconsistent bytes reject")
            .kind(),
        DurableArtifactFailureKind::Validation
    );
}

#[test]
fn authority_drift_and_unknown_entries_reject_before_object_storage() {
    let directory = TestDirectory::new("durable-artifact-authority");
    let first_row = opaque_row("artifact://authority/first.bin", b"first");
    let second_row = opaque_row("artifact://authority/second.bin", b"second");
    let first = entry(&first_row);
    let second = entry(&second_row);

    let mut invalid_catalog = catalog(std::slice::from_ref(&first_row));
    let catalog_text = String::from_utf8(invalid_catalog.clone()).expect("catalog is UTF-8");
    let offset = catalog_text
        .find("\"catalogId\":\"")
        .expect("catalogId exists")
        + 13;
    invalid_catalog[offset] = if invalid_catalog[offset] == b'0' {
        b'1'
    } else {
        b'0'
    };
    assert_eq!(
        DurableArtifactAuthority::from_repository_catalog(&repository_root(), &invalid_catalog)
            .expect_err("catalog identity drift rejects")
            .kind(),
        DurableArtifactFailureKind::Authority
    );

    let store = open_store(&directory.0, std::slice::from_ref(&first_row));
    assert_eq!(
        store
            .publish(&second, b"second".to_vec())
            .expect_err("entry outside bound catalog rejects")
            .kind(),
        DurableArtifactFailureKind::Authority
    );
    assert!(!object_path(&store, &second).exists());
    drop(store);
    assert_eq!(
        DurableArtifactStore::open(&directory.0, authority(std::slice::from_ref(&second_row)),)
            .expect_err("store cannot reopen under a different catalog")
            .kind(),
        DurableArtifactFailureKind::Authority
    );
    assert!(first.locator.is_artifact());
}

#[test]
fn valid_candidate_conflict_quarantines_both_observations_and_selects_neither() {
    let directory = TestDirectory::new("durable-artifact-conflict");
    let row = opaque_row("artifact://shared/profile.bin", b"expected");
    let entry = entry(&row);
    let store = open_store(&directory.0, std::slice::from_ref(&row));
    store
        .publish(&entry, b"expected".to_vec())
        .expect("initial object publishes");
    fs::write(object_path(&store, &entry), b"competing-observation")
        .expect("test installs a competing observation");

    assert_eq!(
        store
            .publish(&entry, b"expected".to_vec())
            .expect_err("conflict rejects")
            .kind(),
        DurableArtifactFailureKind::Conflict
    );
    assert_eq!(
        store
            .ingest(&entry)
            .expect_err("quarantine selects neither observation")
            .kind(),
        DurableArtifactFailureKind::Quarantined
    );
    assert_eq!(
        store
            .conflict_state(&entry.locator)
            .expect("ledger revalidates"),
        DurableArtifactConflictState::QuarantinedPendingConsistencyRerun
    );
    let conflict_dir = store
        .root()
        .join("conflicts")
        .join(sha256_bytes(entry.locator.normalized().as_bytes()).as_str());
    assert_eq!(
        fs::read_dir(conflict_dir)
            .expect("observations are readable")
            .count(),
        2
    );

    fs::write(quarantine_path(&store, &entry), b"{}").expect("test corrupts the canonical ledger");
    assert_eq!(
        store
            .ingest(&entry)
            .expect_err("corrupt quarantine remains fail-closed")
            .kind(),
        DurableArtifactFailureKind::Quarantined
    );
    assert_eq!(
        store
            .conflict_state(&entry.locator)
            .expect_err("ledger corruption is reported")
            .kind(),
        DurableArtifactFailureKind::Corrupt
    );
}

#[test]
fn conflict_boundary_failure_still_leaves_quarantine_visible() {
    for point in [
        DurableArtifactFailpoint::BeforeConflictMarker,
        DurableArtifactFailpoint::AfterConflictMarker,
    ] {
        let directory = TestDirectory::new("durable-artifact-conflict-boundary");
        let row = opaque_row("artifact://shared/boundary.bin", b"expected");
        let entry = entry(&row);
        let store = open_store(&directory.0, std::slice::from_ref(&row));
        store
            .publish(&entry, b"expected".to_vec())
            .expect("initial object publishes");
        fs::write(object_path(&store, &entry), b"competing-observation")
            .expect("test installs competing bytes");
        let failing = store.clone().with_failpoint(point);
        assert_eq!(
            failing
                .publish(&entry, b"expected".to_vec())
                .expect_err("ledger-boundary failure is injected")
                .kind(),
            DurableArtifactFailureKind::Io
        );
        assert_eq!(
            store
                .ingest(&entry)
                .expect_err("conflict evidence selects neither observation")
                .kind(),
            DurableArtifactFailureKind::Quarantined
        );
    }
}

#[test]
fn missing_corrupt_and_nonregular_objects_fail_closed() {
    let directory = TestDirectory::new("durable-artifact-corruption");
    let row = opaque_row("artifact://corruption/profile.bin", b"expected");
    let entry = entry(&row);
    let store = open_store(&directory.0, std::slice::from_ref(&row));

    assert_eq!(
        store
            .ingest(&entry)
            .expect_err("uncommitted object rejects")
            .kind(),
        DurableArtifactFailureKind::Uncommitted
    );
    store
        .publish(&entry, b"expected".to_vec())
        .expect("object publishes");
    fs::write(object_path(&store, &entry), b"corrupt").expect("test corrupts object");
    assert_eq!(
        store
            .ingest(&entry)
            .expect_err("content drift rejects")
            .kind(),
        DurableArtifactFailureKind::Corrupt
    );
    fs::remove_file(object_path(&store, &entry)).expect("corrupt object is removed");
    fs::create_dir(object_path(&store, &entry)).expect("nonregular object is installed");
    assert_eq!(
        store
            .ingest(&entry)
            .expect_err("nonregular object rejects")
            .kind(),
        DurableArtifactFailureKind::Corrupt
    );
}

#[test]
fn object_publication_failpoints_never_commit_an_output() {
    for point in [
        DurableArtifactFailpoint::BeforeStageSync,
        DurableArtifactFailpoint::BeforeObjectRename,
        DurableArtifactFailpoint::BeforeAcceptanceReference,
        DurableArtifactFailpoint::BeforeTransactionCommit,
    ] {
        let directory = TestDirectory::new("durable-artifact-failpoint");
        let row = opaque_row("artifact://failpoint/profile.bin", b"expected");
        let entry = entry(&row);
        let store = open_store(&directory.0, std::slice::from_ref(&row));
        let failing = store.clone().with_failpoint(point);
        assert_eq!(
            failing
                .publish(&entry, b"expected".to_vec())
                .expect_err("publication failure is injected")
                .kind(),
            DurableArtifactFailureKind::Io
        );
        assert_eq!(
            store
                .ingest(&entry)
                .expect_err("failed publication is not accepted")
                .kind(),
            DurableArtifactFailureKind::Uncommitted
        );
        store.recover().expect("orphan staging is recoverable");
    }
}

#[test]
fn late_multi_output_failure_accepts_no_output() {
    let directory = TestDirectory::new("durable-artifact-multi-output");
    let first_row = opaque_row("artifact://multi/first.bin", b"first");
    let second_row = opaque_row("artifact://multi/second.bin", b"second");
    let first = entry(&first_row);
    let second = entry(&second_row);
    let rows = [first_row, second_row];
    let store = open_store(&directory.0, &rows);
    let failing = store
        .clone()
        .with_failpoint(DurableArtifactFailpoint::AfterRawOutput(1));
    let inputs = [
        DurableArtifactInput {
            entry: &first,
            bytes: b"first",
        },
        DurableArtifactInput {
            entry: &second,
            bytes: b"second",
        },
    ];
    assert_eq!(
        failing
            .prepare_transaction(&inputs)
            .expect_err("late raw-output failure is injected")
            .kind(),
        DurableArtifactFailureKind::Io
    );
    for entry in [&first, &second] {
        assert_eq!(
            store
                .ingest(entry)
                .expect_err("no transaction output is accepted")
                .kind(),
            DurableArtifactFailureKind::Uncommitted
        );
    }
}

#[test]
fn committed_transaction_rejects_an_unauthorized_sibling_row() {
    let directory = TestDirectory::new("durable-artifact-transaction-sibling");
    let first_row = opaque_row("artifact://transaction/first.bin", b"first");
    let second_row = opaque_row("artifact://transaction/second.bin", b"second");
    let first = entry(&first_row);
    let store = open_store(&directory.0, &[first_row, second_row]);
    store
        .publish(&first, b"first".to_vec())
        .expect("the authorized first output publishes");

    let mut transaction = SemanticJson::Object(BTreeMap::from([
        (
            "catalogId".to_owned(),
            SemanticJson::String(store.authority().catalog_id().to_string()),
        ),
        (
            "outputs".to_owned(),
            SemanticJson::Array(vec![
                SemanticJson::Object(BTreeMap::from([
                    (
                        "contentSha256".to_owned(),
                        SemanticJson::String(first.content_sha256.to_string()),
                    ),
                    (
                        "locator".to_owned(),
                        SemanticJson::String(first.locator.normalized()),
                    ),
                ])),
                SemanticJson::Object(BTreeMap::from([
                    (
                        "contentSha256".to_owned(),
                        SemanticJson::String(sha256_bytes(b"outsider").to_string()),
                    ),
                    (
                        "locator".to_owned(),
                        SemanticJson::String(
                            "artifact://transaction/outside-authority.bin".to_owned(),
                        ),
                    ),
                ])),
            ]),
        ),
        ("schemaVersion".to_owned(), SemanticJson::Integer(1)),
    ]));
    let transaction_id = digest(
        &DigestDomain::new("k-in-k/durable-artifact-transaction/v1").expect("domain is valid"),
        &transaction,
    )
    .expect("forged transaction identity derives");
    let SemanticJson::Object(fields) = &mut transaction else {
        unreachable!("transaction is an object")
    };
    fields.insert(
        "transactionId".to_owned(),
        SemanticJson::String(transaction_id.to_string()),
    );
    fs::write(
        store
            .root()
            .join("transactions")
            .join(format!("{transaction_id}.json")),
        canonical_json_bytes(&transaction).expect("forged transaction is canonical"),
    )
    .expect("test installs a canonical transaction marker");

    assert_eq!(
        store
            .transaction_is_committed(&transaction_id)
            .expect_err("every sibling must remain within the bound catalog")
            .kind(),
        DurableArtifactFailureKind::Corrupt
    );
}

#[test]
fn ownerless_advisory_lock_file_and_orphan_staging_are_recoverable() {
    let directory = TestDirectory::new("durable-artifact-recovery");
    let row = opaque_row("artifact://restart/profile.bin", b"restart profile");
    let entry = entry(&row);
    let store = open_store(&directory.0, std::slice::from_ref(&row));
    let orphan = store.root().join("staging/.interrupted");
    fs::write(&orphan, b"partial").expect("orphan stage is created");
    assert_eq!(store.recover().expect("recovery succeeds"), 1);
    assert!(!orphan.exists());

    let lock = store.root().join("locks").join(format!(
        "{}.lock",
        sha256_bytes(entry.locator.normalized().as_bytes())
    ));
    fs::write(lock, b"").expect("ownerless advisory lock file is installed");
    assert_eq!(
        store
            .publish(&entry, b"restart profile".to_vec())
            .expect("kernel ownership, not file contents, controls the lock"),
        DurableArtifactPublication::Published
    );
}

#[test]
fn subprocess_lock_helper() {
    let Some(mode) = std::env::var_os(SUBPROCESS_MODE) else {
        return;
    };
    let root = PathBuf::from(std::env::var_os(SUBPROCESS_ROOT).expect("root is supplied"));
    let row = opaque_row(
        "artifact://concurrent/profile.bin",
        b"cross-process profile",
    );
    let entry = entry(&row);
    match mode.to_str().expect("mode is UTF-8") {
        "hold" => {
            let _lock =
                DurableProcessLock::acquire(&root.join("locks"), &entry.locator.normalized())
                    .expect("subprocess holds advisory lock");
            fs::write(
                std::env::var_os(SUBPROCESS_READY).expect("ready path is supplied"),
                b"ready",
            )
            .expect("holder announces readiness");
            thread::sleep(Duration::from_secs(30));
        }
        "write" => {
            open_store(&root, std::slice::from_ref(&row))
                .publish(&entry, b"cross-process profile".to_vec())
                .expect("subprocess publication succeeds");
        }
        other => panic!("unknown subprocess mode {other}"),
    }
}

fn subprocess(root: &Path, mode: &str) -> Command {
    let mut command = Command::new(std::env::current_exe().expect("test executable exists"));
    command
        .arg("--exact")
        .arg("subprocess_lock_helper")
        .arg("--nocapture")
        .env(SUBPROCESS_MODE, mode)
        .env(SUBPROCESS_ROOT, root);
    command
}

#[test]
fn killing_a_paused_lock_owner_releases_without_aba_cleanup() {
    let directory = TestDirectory::new("durable-artifact-paused-owner");
    let row = opaque_row(
        "artifact://concurrent/profile.bin",
        b"cross-process profile",
    );
    open_store(&directory.0, std::slice::from_ref(&row));
    let ready = directory.0.join("holder-ready");
    let mut holder = subprocess(&directory.0, "hold")
        .env(SUBPROCESS_READY, &ready)
        .spawn()
        .expect("lock holder starts");
    for _ in 0..200 {
        if ready.exists() {
            break;
        }
        thread::sleep(Duration::from_millis(10));
    }
    assert!(ready.exists(), "lock holder became ready");

    let mut writer = subprocess(&directory.0, "write")
        .spawn()
        .expect("blocked writer starts");
    thread::sleep(Duration::from_millis(150));
    assert!(
        writer
            .try_wait()
            .expect("writer state is readable")
            .is_none()
    );
    holder.kill().expect("paused owner is killed");
    assert!(holder.wait().expect("holder exits").code().is_none());
    assert!(writer.wait().expect("writer exits").success());
}

#[test]
fn concurrent_subprocess_writers_publish_one_exact_object() {
    let directory = TestDirectory::new("durable-artifact-processes");
    let mut children = (0..6)
        .map(|_| {
            subprocess(&directory.0, "write")
                .spawn()
                .expect("writer subprocess starts")
        })
        .collect::<Vec<_>>();
    for child in &mut children {
        assert!(child.wait().expect("writer subprocess exits").success());
    }

    let bytes = b"cross-process profile";
    let row = opaque_row("artifact://concurrent/profile.bin", bytes);
    let entry = entry(&row);
    let store = open_store(&directory.0, std::slice::from_ref(&row));
    assert_eq!(
        store
            .ingest(&entry)
            .expect("one exact durable object is visible")
            .bytes,
        bytes
    );
}

#[test]
fn concurrent_alias_writers_reject_before_storage_can_be_addressed() {
    let invalid = [
        "artifact://a/../b",
        "artifact://a//b",
        "artifact://a/./b",
        "artifact://a\\b",
        "artifact://a%2fb",
        "artifact:///absolute",
    ];
    let untouched = std::env::temp_dir().join(format!(
        "kink-alias-storage-sentinel-{}-{}",
        std::process::id(),
        TEMP_NONCE.fetch_add(1, Ordering::Relaxed)
    ));
    assert!(!untouched.exists());
    thread::scope(|scope| {
        for locator in invalid {
            scope.spawn(move || {
                ArtifactLocator::parse(
                    locator,
                    ResolverId::RustArtifactStoreV1,
                    ArtifactAvailability::ExternalRequired,
                )
                .expect_err("alias locator rejects at the sealed constructor");
            });
        }
    });
    assert!(!untouched.exists());
}
