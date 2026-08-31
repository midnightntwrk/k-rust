use crate::{CacheRecord, PortableProductionWitness, ReuseClass};
pub use kink_portable::DurableArtifactInput;
use kink_portable::{
    ArtifactCatalogEntry, Digest, DurableArtifactFailure, DurableArtifactFailureKind,
    DurableArtifactStore, DurableProcessLock, SemanticJson, canonical_json_bytes, parse_json,
    sha256_bytes,
};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::fs::{self, File, OpenOptions};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

static TEMP_NONCE: AtomicU64 = AtomicU64::new(0);
const CONFLICT_POLICY: &str = "manual-consistency-rerun-v1";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DurableCacheFailureKind {
    InvalidOutputSequence,
    ArtifactPublication,
    MissingOutput,
    CorruptOutput,
    CorruptRecord,
    Quarantined,
    LockTimeout,
    Io,
}

#[derive(Debug)]
pub struct DurableCacheFailure {
    kind: DurableCacheFailureKind,
    detail: String,
}
impl DurableCacheFailure {
    fn new(kind: DurableCacheFailureKind, detail: impl Into<String>) -> Self {
        Self {
            kind,
            detail: detail.into(),
        }
    }
    #[must_use]
    pub const fn kind(&self) -> DurableCacheFailureKind {
        self.kind
    }
}
impl fmt::Display for DurableCacheFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}: {}", self.kind, self.detail)
    }
}
impl std::error::Error for DurableCacheFailure {}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DurableCachePublication {
    Published,
    AlreadyPresent,
    Quarantined,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DurableConflictState {
    Active,
    QuarantinedPendingConsistencyRerun,
}

#[doc(hidden)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DurableCacheFailpoint {
    BeforeRecordStageSync,
    BeforeRecordRename,
    BeforeConflictMarker,
    AfterConflictMarker,
}

#[derive(Clone, Debug)]
pub struct DurableCacheStore {
    root: PathBuf,
    records: PathBuf,
    record_transactions: PathBuf,
    quarantine: PathBuf,
    conflicts: PathBuf,
    locks: PathBuf,
    staging: PathBuf,
    failpoint: Option<DurableCacheFailpoint>,
}

impl DurableCacheStore {
    pub fn open(root: &Path) -> Result<Self, DurableCacheFailure> {
        fs::create_dir_all(root).map_err(io_failure("create cache root"))?;
        let root = fs::canonicalize(root).map_err(io_failure("canonicalize cache root"))?;
        let records = checked_directory(&root, "records")?;
        let record_transactions = checked_directory(&root, "record-transactions")?;
        let quarantine = checked_directory(&root, "quarantine")?;
        let conflicts = checked_directory(&root, "conflicts")?;
        let locks = checked_directory(&root, "locks")?;
        let staging = checked_directory(&root, "staging")?;
        sync_directory(&root)?;
        Ok(Self {
            root,
            records,
            record_transactions,
            quarantine,
            conflicts,
            locks,
            staging,
            failpoint: None,
        })
    }
    #[doc(hidden)]
    #[must_use]
    pub fn with_failpoint(mut self, point: DurableCacheFailpoint) -> Self {
        self.failpoint = Some(point);
        self
    }
    pub fn publish(
        &self,
        record: &CacheRecord,
        outputs: &[DurableArtifactInput<'_>],
        artifacts: &DurableArtifactStore,
    ) -> Result<DurableCachePublication, DurableCacheFailure> {
        validate_output_sequence(record, outputs)?;
        let bytes = canonical_json_bytes(record.as_json())
            .map_err(|e| fail(DurableCacheFailureKind::CorruptRecord, e.to_string()))?;
        let key = record.key().key_digest().as_str();
        let _lock = DurableProcessLock::acquire(&self.locks, key).map_err(lock_failure)?;
        if self.quarantine_exists(key)? {
            return Ok(DurableCachePublication::Quarantined);
        }
        let target = self.record_path(key);
        let existed = path_exists(&target)?;
        let output_entries = outputs
            .iter()
            .map(|output| output.entry.clone())
            .collect::<Vec<_>>();
        if existed {
            let old = read_regular(&target, DurableCacheFailureKind::CorruptRecord)?;
            if old != bytes {
                self.quarantine_conflict(key, &old, &bytes)?;
                return Ok(DurableCachePublication::Quarantined);
            }
            if self.record_is_committed(key, &bytes, &output_entries, artifacts)? {
                validate_outputs(outputs, artifacts)?;
                return Ok(DurableCachePublication::AlreadyPresent);
            }
        }
        let transaction = artifacts
            .prepare_transaction(outputs)
            .map_err(artifact_failure)?;
        if !existed {
            self.publish_record(&target, &bytes)?;
        }
        let reference = object([
            ("artifactTransactionId", string(transaction.id().as_str())),
            ("keyDigest", string(key)),
            ("recordSha256", string(sha256_bytes(&bytes).as_str())),
            ("schemaVersion", SemanticJson::Integer(1)),
        ]);
        publish_immutable(
            &self.staging,
            &self.record_transaction_path(key),
            "record-transaction",
            &encode(reference)?,
        )?;
        transaction.commit().map_err(artifact_failure)?;
        Ok(DurableCachePublication::Published)
    }
    pub fn reusable(
        &self,
        key: &Digest,
        witness: PortableProductionWitness<'_>,
        output_entries: &[ArtifactCatalogEntry],
        artifacts: &DurableArtifactStore,
    ) -> Result<Option<CacheRecord>, DurableCacheFailure> {
        let text = key.as_str();
        let _lock = DurableProcessLock::acquire(&self.locks, text).map_err(lock_failure)?;
        if self.quarantine_exists(text)? {
            return Err(fail(
                DurableCacheFailureKind::Quarantined,
                "cache key is quarantined",
            ));
        }
        let path = self.record_path(text);
        if !path_exists(&path)? {
            return Ok(None);
        }
        let bytes = read_regular(&path, DurableCacheFailureKind::CorruptRecord)?;
        let value = parse_json(&bytes)
            .map_err(|e| fail(DurableCacheFailureKind::CorruptRecord, e.to_string()))?;
        if canonical_json_bytes(&value)
            .map_err(|e| fail(DurableCacheFailureKind::CorruptRecord, e.to_string()))?
            != bytes
        {
            return Err(fail(
                DurableCacheFailureKind::CorruptRecord,
                "record is not canonical JSON",
            ));
        }
        let record = CacheRecord::from_portable_json(&value, witness)
            .map_err(|e| fail(DurableCacheFailureKind::CorruptRecord, e.to_string()))?;
        if record.key().key_digest() != key {
            return Err(fail(
                DurableCacheFailureKind::CorruptRecord,
                "record path and key disagree",
            ));
        }
        validate_catalog_sequence(&record, output_entries)?;
        if !self.record_is_committed(text, &bytes, output_entries, artifacts)? {
            return Ok(None);
        }
        if record.reuse_class() == ReuseClass::NotReusable {
            return Ok(None);
        }
        for entry in output_entries {
            artifacts.ingest(entry).map_err(output_failure)?;
        }
        Ok(Some(record))
    }
    pub fn conflict_state(
        &self,
        key: &Digest,
    ) -> Result<DurableConflictState, DurableCacheFailure> {
        let _lock = DurableProcessLock::acquire(&self.locks, key.as_str()).map_err(lock_failure)?;
        let marker = self.quarantine_path(key.as_str());
        if !path_exists(&marker)? {
            if path_exists(&self.conflicts.join(key.as_str()))? {
                return Err(fail(
                    DurableCacheFailureKind::CorruptRecord,
                    "cache conflict evidence has no canonical ledger",
                ));
            }
            return Ok(DurableConflictState::Active);
        }
        self.validate_conflict_ledger(key.as_str(), &marker)?;
        Ok(DurableConflictState::QuarantinedPendingConsistencyRerun)
    }
    pub fn recover(&self) -> Result<usize, DurableCacheFailure> {
        let mut removed = 0;
        for item in fs::read_dir(&self.staging).map_err(io_failure("scan cache staging"))? {
            let path = item.map_err(io_failure("read cache staging"))?.path();
            if fs::symlink_metadata(&path)
                .map_err(io_failure("inspect cache staging"))?
                .file_type()
                .is_file()
            {
                fs::remove_file(path).map_err(io_failure("remove cache staging"))?;
                removed += 1;
            }
        }
        if removed > 0 {
            sync_directory(&self.staging)?;
        }
        Ok(removed)
    }
    #[must_use]
    pub fn root(&self) -> &Path {
        &self.root
    }
    fn record_is_committed(
        &self,
        key: &str,
        record: &[u8],
        output_entries: &[ArtifactCatalogEntry],
        artifacts: &DurableArtifactStore,
    ) -> Result<bool, DurableCacheFailure> {
        let path = self.record_transaction_path(key);
        if !path_exists(&path)? {
            return Ok(false);
        }
        let value = read_canonical(&path, DurableCacheFailureKind::CorruptRecord)?;
        let f = exact_fields(
            &value,
            &[
                "artifactTransactionId",
                "keyDigest",
                "recordSha256",
                "schemaVersion",
            ],
            DurableCacheFailureKind::CorruptRecord,
            "record transaction",
        )?;
        if f.get("schemaVersion").and_then(SemanticJson::as_i64) != Some(1)
            || f.get("keyDigest").and_then(SemanticJson::as_str) != Some(key)
            || f.get("recordSha256").and_then(SemanticJson::as_str)
                != Some(sha256_bytes(record).as_str())
        {
            return Err(fail(
                DurableCacheFailureKind::CorruptRecord,
                "record transaction mismatch",
            ));
        }
        let id = f
            .get("artifactTransactionId")
            .and_then(SemanticJson::as_str)
            .and_then(|v| Digest::parse(v).ok())
            .ok_or_else(|| {
                fail(
                    DurableCacheFailureKind::CorruptRecord,
                    "invalid artifact transaction ID",
                )
            })?;
        if !artifacts
            .transaction_is_committed(&id)
            .map_err(output_failure)?
        {
            return Ok(false);
        }
        if !artifacts
            .transaction_commits_exact_entries(&id, output_entries)
            .map_err(output_failure)?
        {
            return Err(fail(
                DurableCacheFailureKind::CorruptRecord,
                "record transaction does not commit the exact ordered output set",
            ));
        }
        Ok(true)
    }
    fn quarantine_exists(&self, key: &str) -> Result<bool, DurableCacheFailure> {
        let marker = self.quarantine_path(key);
        if !path_exists(&marker)? {
            return path_exists(&self.conflicts.join(key));
        }
        if let Err(e) = self.validate_conflict_ledger(key, &marker) {
            return Err(fail(
                DurableCacheFailureKind::Quarantined,
                format!("corrupt ledger remains fail-closed: {e}"),
            ));
        }
        Ok(true)
    }
    fn quarantine_conflict(
        &self,
        key: &str,
        old: &[u8],
        candidate: &[u8],
    ) -> Result<(), DurableCacheFailure> {
        let dir = checked_child_directory(&self.conflicts, key)?;
        let mut observations = [
            (sha256_bytes(old), old),
            (sha256_bytes(candidate), candidate),
        ];
        observations.sort_by(|left, right| left.0.cmp(&right.0));
        for (digest, bytes) in &observations {
            publish_immutable(
                &self.staging,
                &dir.join(format!("{digest}.json")),
                "conflict",
                bytes,
            )?;
        }
        sync_directory(&dir)?;
        self.trip(DurableCacheFailpoint::BeforeConflictMarker)?;
        let ledger = object([
            ("keyDigest", string(key)),
            (
                "observations",
                SemanticJson::Array(
                    observations
                        .iter()
                        .map(|(digest, _)| string(digest.as_str()))
                        .collect(),
                ),
            ),
            ("policy", string(CONFLICT_POLICY)),
            ("schemaVersion", SemanticJson::Integer(1)),
            ("state", string("quarantined-pending-consistency-rerun")),
        ]);
        publish_immutable(
            &self.staging,
            &self.quarantine_path(key),
            "quarantine",
            &encode(ledger)?,
        )?;
        self.trip(DurableCacheFailpoint::AfterConflictMarker)
    }
    fn validate_conflict_ledger(
        &self,
        key: &str,
        marker: &Path,
    ) -> Result<(), DurableCacheFailure> {
        let value = read_canonical(marker, DurableCacheFailureKind::CorruptRecord)?;
        let f = exact_fields(
            &value,
            &[
                "keyDigest",
                "observations",
                "policy",
                "schemaVersion",
                "state",
            ],
            DurableCacheFailureKind::CorruptRecord,
            "cache conflict ledger",
        )?;
        if f.get("schemaVersion").and_then(SemanticJson::as_i64) != Some(1)
            || f.get("keyDigest").and_then(SemanticJson::as_str) != Some(key)
            || f.get("policy").and_then(SemanticJson::as_str) != Some(CONFLICT_POLICY)
            || f.get("state").and_then(SemanticJson::as_str)
                != Some("quarantined-pending-consistency-rerun")
        {
            return Err(fail(
                DurableCacheFailureKind::CorruptRecord,
                "cache conflict ledger mismatch",
            ));
        }
        for d in parse_observations(f)? {
            let bytes = read_regular(
                &self.conflicts.join(key).join(format!("{d}.json")),
                DurableCacheFailureKind::CorruptRecord,
            )?;
            if sha256_bytes(&bytes) != d {
                return Err(fail(
                    DurableCacheFailureKind::CorruptRecord,
                    "cache conflict observation mismatch",
                ));
            }
        }
        Ok(())
    }
    fn publish_record(&self, target: &Path, bytes: &[u8]) -> Result<(), DurableCacheFailure> {
        let stage = unique_path(&self.staging, "record");
        write_new(&stage, bytes, false)?;
        self.trip(DurableCacheFailpoint::BeforeRecordStageSync)?;
        File::open(&stage)
            .and_then(|f| f.sync_all())
            .map_err(io_failure("sync record stage"))?;
        sync_directory(&self.staging)?;
        self.trip(DurableCacheFailpoint::BeforeRecordRename)?;
        fs::rename(&stage, target).map_err(io_failure("rename record"))?;
        sync_directory(&self.records)?;
        sync_directory(&self.staging)
    }
    fn trip(&self, point: DurableCacheFailpoint) -> Result<(), DurableCacheFailure> {
        if self.failpoint == Some(point) {
            Err(fail(
                DurableCacheFailureKind::Io,
                format!("injected failure at {point:?}"),
            ))
        } else {
            Ok(())
        }
    }
    fn record_path(&self, key: &str) -> PathBuf {
        self.records.join(format!("{key}.json"))
    }
    fn record_transaction_path(&self, key: &str) -> PathBuf {
        self.record_transactions.join(format!("{key}.json"))
    }
    fn quarantine_path(&self, key: &str) -> PathBuf {
        self.quarantine.join(format!("{key}.json"))
    }
}

fn validate_output_sequence(
    record: &CacheRecord,
    outputs: &[DurableArtifactInput<'_>],
) -> Result<(), DurableCacheFailure> {
    if record.produced_artifacts().len() != outputs.len()
        || record
            .produced_artifacts()
            .iter()
            .zip(outputs)
            .any(|(k, o)| k.role != o.entry.role || k.digest != o.entry.digest)
    {
        return Err(fail(
            DurableCacheFailureKind::InvalidOutputSequence,
            "outputs differ from producedArtifacts order",
        ));
    }
    let mut locators = BTreeSet::new();
    if !outputs
        .iter()
        .all(|o| locators.insert(o.entry.locator.normalized()))
    {
        return Err(fail(
            DurableCacheFailureKind::InvalidOutputSequence,
            "outputs repeat locator",
        ));
    }
    Ok(())
}
fn validate_outputs(
    outputs: &[DurableArtifactInput<'_>],
    store: &DurableArtifactStore,
) -> Result<(), DurableCacheFailure> {
    for output in outputs {
        store.ingest(output.entry).map_err(output_failure)?;
    }
    Ok(())
}
fn validate_catalog_sequence(
    record: &CacheRecord,
    entries: &[ArtifactCatalogEntry],
) -> Result<(), DurableCacheFailure> {
    if record.produced_artifacts().len() != entries.len()
        || record
            .produced_artifacts()
            .iter()
            .zip(entries)
            .any(|(k, e)| k.role != e.role || k.digest != e.digest)
    {
        Err(fail(
            DurableCacheFailureKind::MissingOutput,
            "catalog does not exactly cover outputs",
        ))
    } else {
        Ok(())
    }
}
fn output_failure(e: DurableArtifactFailure) -> DurableCacheFailure {
    let kind = match e.kind() {
        DurableArtifactFailureKind::Missing | DurableArtifactFailureKind::Uncommitted => {
            DurableCacheFailureKind::MissingOutput
        }
        DurableArtifactFailureKind::LockTimeout => DurableCacheFailureKind::LockTimeout,
        DurableArtifactFailureKind::Io => DurableCacheFailureKind::Io,
        _ => DurableCacheFailureKind::CorruptOutput,
    };
    fail(kind, e.to_string())
}
fn artifact_failure(e: DurableArtifactFailure) -> DurableCacheFailure {
    let kind = if e.kind() == DurableArtifactFailureKind::LockTimeout {
        DurableCacheFailureKind::LockTimeout
    } else {
        DurableCacheFailureKind::ArtifactPublication
    };
    fail(kind, e.to_string())
}
fn lock_failure(e: DurableArtifactFailure) -> DurableCacheFailure {
    let kind = if e.kind() == DurableArtifactFailureKind::LockTimeout {
        DurableCacheFailureKind::LockTimeout
    } else {
        DurableCacheFailureKind::Io
    };
    fail(kind, e.to_string())
}
fn checked_directory(root: &Path, name: &str) -> Result<PathBuf, DurableCacheFailure> {
    let path = root.join(name);
    fs::create_dir_all(&path).map_err(io_failure("create cache directory"))?;
    let c = fs::canonicalize(&path).map_err(io_failure("canonicalize cache directory"))?;
    if !c.starts_with(root) {
        return Err(fail(DurableCacheFailureKind::Io, "cache directory escapes"));
    }
    Ok(c)
}
fn checked_child_directory(root: &Path, name: &str) -> Result<PathBuf, DurableCacheFailure> {
    let path = root.join(name);
    let made = match fs::create_dir(&path) {
        Ok(()) => true,
        Err(e) if e.kind() == io::ErrorKind::AlreadyExists => false,
        Err(e) => return Err(fail(DurableCacheFailureKind::Io, e.to_string())),
    };
    let c = fs::canonicalize(&path).map_err(io_failure("canonicalize conflict directory"))?;
    if !c.starts_with(root) {
        return Err(fail(
            DurableCacheFailureKind::Io,
            "conflict directory escapes",
        ));
    }
    if made {
        sync_directory(root)?;
    }
    Ok(c)
}
fn publish_immutable(
    staging: &Path,
    target: &Path,
    prefix: &str,
    bytes: &[u8],
) -> Result<(), DurableCacheFailure> {
    if path_exists(target)? {
        return if read_regular(target, DurableCacheFailureKind::CorruptRecord)? == bytes {
            Ok(())
        } else {
            Err(fail(
                DurableCacheFailureKind::CorruptRecord,
                "immutable cache metadata conflict",
            ))
        };
    }
    let stage = unique_path(staging, prefix);
    write_new(&stage, bytes, true)?;
    sync_directory(staging)?;
    fs::rename(&stage, target).map_err(io_failure("rename cache metadata"))?;
    sync_directory(target.parent().expect("parent"))?;
    sync_directory(staging)
}
fn read_regular(
    path: &Path,
    kind: DurableCacheFailureKind,
) -> Result<Vec<u8>, DurableCacheFailure> {
    let m = fs::symlink_metadata(path).map_err(io_failure("inspect cache file"))?;
    if !m.file_type().is_file() {
        return Err(fail(kind, "cache path is not regular file"));
    }
    fs::read(path).map_err(io_failure("read cache file"))
}
fn read_canonical(
    path: &Path,
    kind: DurableCacheFailureKind,
) -> Result<SemanticJson, DurableCacheFailure> {
    let bytes = read_regular(path, kind)?;
    let value = parse_json(&bytes).map_err(|e| fail(kind, e.to_string()))?;
    if canonical_json_bytes(&value).map_err(|e| fail(kind, e.to_string()))? != bytes {
        return Err(fail(kind, "cache JSON is not canonical"));
    }
    Ok(value)
}
fn exact_fields<'a>(
    value: &'a SemanticJson,
    expected: &[&str],
    kind: DurableCacheFailureKind,
    context: &str,
) -> Result<&'a BTreeMap<String, SemanticJson>, DurableCacheFailure> {
    let f = value
        .as_object()
        .ok_or_else(|| fail(kind, format!("{context} not object")))?;
    if f.len() != expected.len() || expected.iter().any(|k| !f.contains_key(*k)) {
        return Err(fail(kind, format!("{context} unsupported fields")));
    }
    Ok(f)
}
fn parse_observations(
    f: &BTreeMap<String, SemanticJson>,
) -> Result<[Digest; 2], DurableCacheFailure> {
    let v = f
        .get("observations")
        .and_then(SemanticJson::as_array)
        .filter(|v| v.len() == 2)
        .ok_or_else(|| {
            fail(
                DurableCacheFailureKind::CorruptRecord,
                "two observations required",
            )
        })?;
    let a = v[0]
        .as_str()
        .and_then(|v| Digest::parse(v).ok())
        .ok_or_else(|| {
            fail(
                DurableCacheFailureKind::CorruptRecord,
                "invalid observation",
            )
        })?;
    let b = v[1]
        .as_str()
        .and_then(|v| Digest::parse(v).ok())
        .ok_or_else(|| {
            fail(
                DurableCacheFailureKind::CorruptRecord,
                "invalid observation",
            )
        })?;
    if a >= b {
        return Err(fail(
            DurableCacheFailureKind::CorruptRecord,
            "observations not canonical",
        ));
    }
    Ok([a, b])
}
fn path_exists(path: &Path) -> Result<bool, DurableCacheFailure> {
    match fs::symlink_metadata(path) {
        Ok(_) => Ok(true),
        Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(false),
        Err(e) => Err(fail(DurableCacheFailureKind::Io, e.to_string())),
    }
}
fn unique_path(parent: &Path, prefix: &str) -> PathBuf {
    parent.join(format!(
        ".{prefix}-{}-{}",
        std::process::id(),
        TEMP_NONCE.fetch_add(1, Ordering::Relaxed)
    ))
}
fn write_new(path: &Path, bytes: &[u8], sync: bool) -> Result<(), DurableCacheFailure> {
    let mut f = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .map_err(io_failure("create cache stage"))?;
    f.write_all(bytes)
        .map_err(io_failure("write cache stage"))?;
    if sync {
        f.sync_all().map_err(io_failure("sync cache stage"))?;
    }
    Ok(())
}
fn sync_directory(path: &Path) -> Result<(), DurableCacheFailure> {
    File::open(path)
        .and_then(|f| f.sync_all())
        .map_err(io_failure("sync cache directory"))
}
fn object(values: impl IntoIterator<Item = (&'static str, SemanticJson)>) -> SemanticJson {
    SemanticJson::Object(values.into_iter().map(|(k, v)| (k.to_owned(), v)).collect())
}
fn string(v: &str) -> SemanticJson {
    SemanticJson::String(v.to_owned())
}
fn encode(v: SemanticJson) -> Result<Vec<u8>, DurableCacheFailure> {
    canonical_json_bytes(&v)
        .map_err(|e| fail(DurableCacheFailureKind::CorruptRecord, e.to_string()))
}
fn fail(kind: DurableCacheFailureKind, detail: impl Into<String>) -> DurableCacheFailure {
    DurableCacheFailure::new(kind, detail)
}
fn io_failure(context: &'static str) -> impl FnOnce(io::Error) -> DurableCacheFailure {
    move |e| fail(DurableCacheFailureKind::Io, format!("{context}: {e}"))
}
