use crate::{
    ArtifactCatalogEntry, ArtifactStore, Digest, DigestDomain, IngressedArtifact, RoleSpecRegistry,
    SemanticJson, canonical_json_bytes, digest, digest_without_field, ingest_artifact, parse_json,
    sha256_bytes,
};
use fs2::FileExt;
use kink_contracts::{ArtifactAvailability, ArtifactFailure, ArtifactLocator, ResolverId};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::fs::{self, File, OpenOptions};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::thread;
use std::time::{Duration, Instant};

#[cfg(not(target_os = "linux"))]
compile_error!("the durable artifact store currently supports Linux only");

static TEMP_NONCE: AtomicU64 = AtomicU64::new(0);
const LOCK_TIMEOUT: Duration = Duration::from_secs(10);
const CONFLICT_POLICY: &str = "manual-consistency-rerun-v1";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DurableArtifactFailureKind {
    InvalidLocator,
    Authority,
    Validation,
    Missing,
    Uncommitted,
    Conflict,
    Quarantined,
    Corrupt,
    LockTimeout,
    Io,
}

#[derive(Debug)]
pub struct DurableArtifactFailure {
    kind: DurableArtifactFailureKind,
    detail: String,
}
impl DurableArtifactFailure {
    fn new(kind: DurableArtifactFailureKind, detail: impl Into<String>) -> Self {
        Self {
            kind,
            detail: detail.into(),
        }
    }
    #[must_use]
    pub const fn kind(&self) -> DurableArtifactFailureKind {
        self.kind
    }
}
impl fmt::Display for DurableArtifactFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}: {}", self.kind, self.detail)
    }
}
impl std::error::Error for DurableArtifactFailure {}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DurableArtifactPublication {
    Published,
    AlreadyPresent,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DurableArtifactConflictState {
    Active,
    QuarantinedPendingConsistencyRerun,
}

#[derive(Clone, Copy, Debug)]
pub struct DurableArtifactInput<'a> {
    pub entry: &'a ArtifactCatalogEntry,
    pub bytes: &'a [u8],
}

#[derive(Clone, Debug)]
pub struct DurableArtifactAuthority {
    registry: RoleSpecRegistry,
    registry_authority_sha256: Digest,
    catalog_id: Digest,
    entries: BTreeMap<(String, Digest), ArtifactCatalogEntry>,
}

impl DurableArtifactAuthority {
    pub fn from_repository_catalog(
        repository_root: &Path,
        catalog_bytes: &[u8],
    ) -> Result<Self, DurableArtifactFailure> {
        let registry_path = repository_root
            .join("investigations/backend-agnostic-goal-closure/artifact-role-specs.json");
        let registry_bytes = fs::read(&registry_path).map_err(|e| {
            fail(
                DurableArtifactFailureKind::Authority,
                format!("read {}: {e}", registry_path.display()),
            )
        })?;
        let registry =
            RoleSpecRegistry::from_repository_root(repository_root).map_err(authority_failure)?;
        let registry_authority_sha256 =
            registry_authority_sha256(repository_root, &registry_bytes)?;
        let catalog = parse_json(catalog_bytes).map_err(|e| {
            fail(
                DurableArtifactFailureKind::Authority,
                format!("invalid catalog JSON: {e}"),
            )
        })?;
        let fields = exact_fields(
            &catalog,
            &[
                "catalogId",
                "entries",
                "schemaVersion",
                "unboundRequirements",
            ],
            DurableArtifactFailureKind::Authority,
            "artifact catalog",
        )?;
        if fields.get("schemaVersion").and_then(SemanticJson::as_i64) != Some(1) {
            return Err(fail(
                DurableArtifactFailureKind::Authority,
                "unsupported artifact catalog version",
            ));
        }
        validate_unbound(fields.get("unboundRequirements"), &registry)?;
        let catalog_id = parse_digest(fields, "catalogId", DurableArtifactFailureKind::Authority)?;
        let derived = digest_without_field(
            &DigestDomain::new("k-in-k/artifact-catalog/v1").expect("domain"),
            &catalog,
            "catalogId",
        )
        .map_err(|e| fail(DurableArtifactFailureKind::Authority, e.to_string()))?;
        if catalog_id != derived {
            return Err(fail(
                DurableArtifactFailureKind::Authority,
                "artifact catalog identity mismatch",
            ));
        }
        let rows = fields
            .get("entries")
            .and_then(SemanticJson::as_array)
            .filter(|v| !v.is_empty())
            .ok_or_else(|| {
                fail(
                    DurableArtifactFailureKind::Authority,
                    "catalog entries must be nonempty",
                )
            })?;
        let mut entries = BTreeMap::new();
        let mut locators = BTreeSet::new();
        for row in rows {
            let entry = ArtifactCatalogEntry::from_json(row).map_err(authority_failure)?;
            if !registry.contains(&entry.role) {
                return Err(fail(
                    DurableArtifactFailureKind::Authority,
                    "catalog uses unknown role",
                ));
            }
            if !locators.insert(entry.locator.normalized()) {
                return Err(fail(
                    DurableArtifactFailureKind::Authority,
                    "catalog repeats normalized locator",
                ));
            }
            if entries
                .insert((entry.role.clone(), entry.digest.clone()), entry)
                .is_some()
            {
                return Err(fail(
                    DurableArtifactFailureKind::Authority,
                    "catalog repeats role/digest",
                ));
            }
        }
        Ok(Self {
            registry,
            registry_authority_sha256,
            catalog_id,
            entries,
        })
    }
    #[must_use]
    pub fn entry(&self, role: &str, digest: &Digest) -> Option<&ArtifactCatalogEntry> {
        self.entries.get(&(role.to_owned(), digest.clone()))
    }
    #[must_use]
    pub fn catalog_id(&self) -> &Digest {
        &self.catalog_id
    }
    fn validate_entry(&self, entry: &ArtifactCatalogEntry) -> Result<(), DurableArtifactFailure> {
        match self
            .entries
            .get(&(entry.role.clone(), entry.digest.clone()))
        {
            Some(v) if v == entry => Ok(()),
            _ => Err(fail(
                DurableArtifactFailureKind::Authority,
                "entry differs from bound catalog authority",
            )),
        }
    }
    fn descriptor(&self) -> Result<Vec<u8>, DurableArtifactFailure> {
        encode(object([
            ("catalogId", string(self.catalog_id.as_str())),
            (
                "registryAuthoritySha256",
                string(self.registry_authority_sha256.as_str()),
            ),
            ("schemaVersion", SemanticJson::Integer(1)),
        ]))
    }
}

#[doc(hidden)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DurableArtifactFailpoint {
    BeforeStageSync,
    BeforeObjectRename,
    AfterRawOutput(usize),
    BeforeAcceptanceReference,
    BeforeTransactionCommit,
    BeforeConflictMarker,
    AfterConflictMarker,
}

#[derive(Clone, Debug)]
pub struct DurableArtifactStore {
    root: PathBuf,
    objects: PathBuf,
    locks: PathBuf,
    staging: PathBuf,
    acceptance: PathBuf,
    transactions: PathBuf,
    quarantine: PathBuf,
    conflicts: PathBuf,
    authority: Arc<DurableArtifactAuthority>,
    failpoint: Option<DurableArtifactFailpoint>,
}

impl DurableArtifactStore {
    pub fn open(
        root: &Path,
        authority: DurableArtifactAuthority,
    ) -> Result<Self, DurableArtifactFailure> {
        fs::create_dir_all(root).map_err(io_failure("create store root"))?;
        let root = fs::canonicalize(root).map_err(io_failure("canonicalize store root"))?;
        let objects = checked_directory(&root, "objects")?;
        let locks = checked_directory(&root, "locks")?;
        let staging = checked_directory(&root, "staging")?;
        let acceptance = checked_directory(&root, "acceptance")?;
        let transactions = checked_directory(&root, "transactions")?;
        let quarantine = checked_directory(&root, "quarantine")?;
        let conflicts = checked_directory(&root, "conflicts")?;
        sync_directory(&root)?;
        let _authority_lock = DurableProcessLock::acquire(&locks, "store-authority-v1")?;
        bind_authority(&root, &authority.descriptor()?)?;
        Ok(Self {
            root,
            objects,
            locks,
            staging,
            acceptance,
            transactions,
            quarantine,
            conflicts,
            authority: Arc::new(authority),
            failpoint: None,
        })
    }
    #[doc(hidden)]
    #[must_use]
    pub fn with_failpoint(mut self, point: DurableArtifactFailpoint) -> Self {
        self.failpoint = Some(point);
        self
    }
    pub fn publish(
        &self,
        entry: &ArtifactCatalogEntry,
        bytes: Vec<u8>,
    ) -> Result<DurableArtifactPublication, DurableArtifactFailure> {
        let tx = self.prepare_transaction(&[DurableArtifactInput {
            entry,
            bytes: &bytes,
        }])?;
        let already = tx.already_accepted;
        tx.commit()?;
        Ok(if already {
            DurableArtifactPublication::AlreadyPresent
        } else {
            DurableArtifactPublication::Published
        })
    }
    pub fn prepare_transaction(
        &self,
        inputs: &[DurableArtifactInput<'_>],
    ) -> Result<PreparedArtifactTransaction, DurableArtifactFailure> {
        let mut unique = BTreeSet::new();
        for input in inputs {
            self.validate_input(input)?;
            if !unique.insert(input.entry.locator.normalized()) {
                return Err(fail(
                    DurableArtifactFailureKind::Validation,
                    "transaction repeats locator",
                ));
            }
        }
        let value = transaction_value(self.authority.catalog_id(), inputs);
        let id = digest(
            &DigestDomain::new("k-in-k/durable-artifact-transaction/v1").expect("domain"),
            &value,
        )
        .map_err(|e| fail(DurableArtifactFailureKind::Validation, e.to_string()))?;
        let bytes = encode(with_id(value, &id))?;
        let mut keys = inputs
            .iter()
            .map(|v| v.entry.locator.normalized())
            .collect::<Vec<_>>();
        keys.sort();
        let mut locks = Vec::new();
        for key in keys {
            locks.push(DurableProcessLock::acquire(&self.locks, &key)?);
        }
        let mut already = true;
        for input in inputs {
            if self.quarantine_exists(&input.entry.locator)? {
                return Err(fail(
                    DurableArtifactFailureKind::Quarantined,
                    "locator is quarantined",
                ));
            }
            already &= self.is_accepted_locked(input.entry)?;
            let target = self.object_path(&input.entry.locator)?;
            if path_exists(&target)? {
                let old = read_regular(&self.objects, &target)?;
                if old != input.bytes {
                    self.quarantine_conflict(&input.entry.locator, &old, input.bytes)?;
                    return Err(fail(
                        DurableArtifactFailureKind::Conflict,
                        "artifact conflict quarantined",
                    ));
                }
            }
        }
        for (index, input) in inputs.iter().enumerate() {
            let target = self.object_path(&input.entry.locator)?;
            if !path_exists(&target)? {
                create_contained_directory(&self.objects, target.parent().expect("parent"))?;
                self.publish_object(&target, input.bytes)?;
            }
            self.validate_raw(input.entry)?;
            self.trip(DurableArtifactFailpoint::AfterRawOutput(index + 1))?;
        }
        for input in inputs {
            self.trip(DurableArtifactFailpoint::BeforeAcceptanceReference)?;
            let directory =
                checked_child_directory(&self.acceptance, &locator_hash(&input.entry.locator))?;
            let reference = object([
                ("catalogId", string(self.authority.catalog_id().as_str())),
                ("contentSha256", string(input.entry.content_sha256.as_str())),
                ("locator", string(&input.entry.locator.normalized())),
                ("schemaVersion", SemanticJson::Integer(1)),
                ("transactionId", string(id.as_str())),
            ]);
            publish_immutable(
                &self.staging,
                &directory.join(format!("{id}.json")),
                "acceptance",
                &encode(reference)?,
            )?;
        }
        Ok(PreparedArtifactTransaction {
            store: self.clone(),
            id,
            bytes,
            already_accepted: already,
            _locks: locks,
        })
    }
    pub fn ingest(
        &self,
        entry: &ArtifactCatalogEntry,
    ) -> Result<IngressedArtifact, DurableArtifactFailure> {
        self.authority.validate_entry(entry)?;
        validate_locator(&entry.locator)?;
        let _lock = DurableProcessLock::acquire(&self.locks, &entry.locator.normalized())?;
        if self.quarantine_exists(&entry.locator)? {
            return Err(fail(
                DurableArtifactFailureKind::Quarantined,
                "quarantined locator selects neither observation",
            ));
        }
        if !self.is_accepted_locked(entry)? {
            return Err(fail(
                DurableArtifactFailureKind::Uncommitted,
                "artifact is not transaction-committed",
            ));
        }
        self.validate_raw(entry)
    }
    pub fn conflict_state(
        &self,
        locator: &ArtifactLocator,
    ) -> Result<DurableArtifactConflictState, DurableArtifactFailure> {
        validate_locator(locator)?;
        let _lock = DurableProcessLock::acquire(&self.locks, &locator.normalized())?;
        let marker = self.quarantine_path(locator);
        if !path_exists(&marker)? {
            if path_exists(&self.conflicts.join(locator_hash(locator)))? {
                return Err(fail(
                    DurableArtifactFailureKind::Corrupt,
                    "conflict evidence has no canonical ledger",
                ));
            }
            return Ok(DurableArtifactConflictState::Active);
        }
        self.validate_conflict_ledger(locator, &marker)?;
        Ok(DurableArtifactConflictState::QuarantinedPendingConsistencyRerun)
    }
    pub fn transaction_is_committed(&self, id: &Digest) -> Result<bool, DurableArtifactFailure> {
        let path = self.transaction_path(id);
        if !path_exists(&path)? {
            return Ok(false);
        }
        self.read_transaction_outputs(id).map(|_| true)
    }
    /// Reports whether one committed transaction contains exactly the supplied ordered entries.
    ///
    /// Every transaction row is revalidated against the store-bound catalog before comparison.
    /// A referring cache record must use this exact closure check instead of treating any
    /// unrelated committed transaction as evidence for outputs accepted by other transactions.
    pub fn transaction_commits_exact_entries(
        &self,
        id: &Digest,
        entries: &[ArtifactCatalogEntry],
    ) -> Result<bool, DurableArtifactFailure> {
        if !path_exists(&self.transaction_path(id))? {
            return Ok(false);
        }
        for entry in entries {
            self.authority.validate_entry(entry)?;
            validate_locator(&entry.locator)?;
        }
        let outputs = self.read_transaction_outputs(id)?;
        Ok(outputs.len() == entries.len()
            && outputs
                .iter()
                .zip(entries)
                .all(|((locator, digest), entry)| {
                    locator == &entry.locator && digest == &entry.content_sha256
                }))
    }
    pub fn recover(&self) -> Result<usize, DurableArtifactFailure> {
        let mut removed = 0;
        for item in fs::read_dir(&self.staging).map_err(io_failure("scan staging"))? {
            let item = item.map_err(io_failure("read staging"))?;
            if fs::symlink_metadata(item.path())
                .map_err(io_failure("inspect staging"))?
                .file_type()
                .is_file()
            {
                fs::remove_file(item.path()).map_err(io_failure("remove staging"))?;
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
    #[must_use]
    pub fn authority(&self) -> &DurableArtifactAuthority {
        &self.authority
    }
    fn validate_input(
        &self,
        input: &DurableArtifactInput<'_>,
    ) -> Result<(), DurableArtifactFailure> {
        self.authority.validate_entry(input.entry)?;
        validate_locator(&input.entry.locator)?;
        ingest_artifact(&self.authority.registry, input.entry, input.bytes.to_vec())
            .map(|_| ())
            .map_err(validation_failure)
    }
    fn validate_raw(
        &self,
        entry: &ArtifactCatalogEntry,
    ) -> Result<IngressedArtifact, DurableArtifactFailure> {
        let path = self.object_path(&entry.locator)?;
        if !path_exists(&path)? {
            return Err(fail(
                DurableArtifactFailureKind::Missing,
                "raw object missing",
            ));
        }
        ingest_artifact(
            &self.authority.registry,
            entry,
            read_regular(&self.objects, &path)?,
        )
        .map_err(|e| fail(DurableArtifactFailureKind::Corrupt, e.to_string()))
    }
    fn is_accepted_locked(
        &self,
        entry: &ArtifactCatalogEntry,
    ) -> Result<bool, DurableArtifactFailure> {
        let dir = self.acceptance.join(locator_hash(&entry.locator));
        if !path_exists(&dir)? {
            return Ok(false);
        }
        let canonical = fs::canonicalize(&dir).map_err(io_failure("canonicalize acceptance"))?;
        if !canonical.starts_with(&self.acceptance) {
            return Err(fail(
                DurableArtifactFailureKind::Corrupt,
                "acceptance escapes root",
            ));
        }
        let mut invalid = false;
        let mut accepted = false;
        for item in fs::read_dir(&dir).map_err(io_failure("scan acceptance"))? {
            let path = item.map_err(io_failure("read acceptance"))?.path();
            match self.validate_reference(entry, &path) {
                Ok(id)
                    if self.transaction_is_committed(&id)?
                        && self.transaction_contains(&id, entry)? =>
                {
                    accepted = true;
                }
                Ok(_) => {}
                Err(_) => invalid = true,
            }
        }
        if invalid {
            Err(fail(
                DurableArtifactFailureKind::Corrupt,
                "invalid acceptance reference",
            ))
        } else {
            Ok(accepted)
        }
    }
    fn validate_reference(
        &self,
        entry: &ArtifactCatalogEntry,
        path: &Path,
    ) -> Result<Digest, DurableArtifactFailure> {
        let value = read_canonical(path, DurableArtifactFailureKind::Corrupt)?;
        let f = exact_fields(
            &value,
            &[
                "catalogId",
                "contentSha256",
                "locator",
                "schemaVersion",
                "transactionId",
            ],
            DurableArtifactFailureKind::Corrupt,
            "acceptance reference",
        )?;
        if f.get("schemaVersion").and_then(SemanticJson::as_i64) != Some(1)
            || f.get("catalogId").and_then(SemanticJson::as_str)
                != Some(self.authority.catalog_id().as_str())
            || f.get("contentSha256").and_then(SemanticJson::as_str)
                != Some(entry.content_sha256.as_str())
            || f.get("locator").and_then(SemanticJson::as_str)
                != Some(entry.locator.normalized().as_str())
        {
            return Err(fail(
                DurableArtifactFailureKind::Corrupt,
                "acceptance reference mismatch",
            ));
        }
        parse_digest(f, "transactionId", DurableArtifactFailureKind::Corrupt)
    }
    fn read_transaction(&self, id: &Digest) -> Result<SemanticJson, DurableArtifactFailure> {
        let value = read_canonical(
            &self.transaction_path(id),
            DurableArtifactFailureKind::Corrupt,
        )?;
        let f = exact_fields(
            &value,
            &["catalogId", "outputs", "schemaVersion", "transactionId"],
            DurableArtifactFailureKind::Corrupt,
            "transaction",
        )?;
        if f.get("schemaVersion").and_then(SemanticJson::as_i64) != Some(1)
            || f.get("catalogId").and_then(SemanticJson::as_str)
                != Some(self.authority.catalog_id().as_str())
            || f.get("transactionId").and_then(SemanticJson::as_str) != Some(id.as_str())
        {
            return Err(fail(
                DurableArtifactFailureKind::Corrupt,
                "transaction metadata mismatch",
            ));
        }
        let derived = digest_without_field(
            &DigestDomain::new("k-in-k/durable-artifact-transaction/v1").expect("domain"),
            &value,
            "transactionId",
        )
        .map_err(|e| fail(DurableArtifactFailureKind::Corrupt, e.to_string()))?;
        if &derived != id {
            return Err(fail(
                DurableArtifactFailureKind::Corrupt,
                "transaction identity mismatch",
            ));
        }
        Ok(value)
    }
    fn transaction_contains(
        &self,
        id: &Digest,
        entry: &ArtifactCatalogEntry,
    ) -> Result<bool, DurableArtifactFailure> {
        Ok(self
            .read_transaction_outputs(id)?
            .iter()
            .any(|(locator, digest)| locator == &entry.locator && digest == &entry.content_sha256))
    }
    fn read_transaction_outputs(
        &self,
        id: &Digest,
    ) -> Result<Vec<(ArtifactLocator, Digest)>, DurableArtifactFailure> {
        let value = self.read_transaction(id)?;
        let rows = value
            .as_object()
            .and_then(|fields| fields.get("outputs"))
            .and_then(SemanticJson::as_array)
            .filter(|rows| !rows.is_empty())
            .ok_or_else(|| {
                fail(
                    DurableArtifactFailureKind::Corrupt,
                    "transaction outputs must be nonempty",
                )
            })?;
        let mut outputs = Vec::with_capacity(rows.len());
        let mut locators = BTreeSet::new();
        for row in rows {
            let fields = exact_fields(
                row,
                &["contentSha256", "locator"],
                DurableArtifactFailureKind::Corrupt,
                "transaction output",
            )?;
            let locator_text = fields
                .get("locator")
                .and_then(SemanticJson::as_str)
                .ok_or_else(|| {
                    fail(
                        DurableArtifactFailureKind::Corrupt,
                        "transaction output locator is invalid",
                    )
                })?;
            let locator = ArtifactLocator::parse(
                locator_text,
                ResolverId::RustArtifactStoreV1,
                ArtifactAvailability::ExternalRequired,
            )
            .map_err(|error| {
                fail(
                    DurableArtifactFailureKind::Corrupt,
                    format!("transaction output locator is invalid: {error}"),
                )
            })?;
            let content_sha256 =
                parse_digest(fields, "contentSha256", DurableArtifactFailureKind::Corrupt)?;
            if !locators.insert(locator.normalized()) {
                return Err(fail(
                    DurableArtifactFailureKind::Corrupt,
                    "transaction repeats one normalized locator",
                ));
            }
            if !self
                .authority
                .entries
                .values()
                .any(|entry| entry.locator == locator && entry.content_sha256 == content_sha256)
            {
                return Err(fail(
                    DurableArtifactFailureKind::Corrupt,
                    "transaction output is outside the bound catalog authority",
                ));
            }
            outputs.push((locator, content_sha256));
        }
        Ok(outputs)
    }
    fn quarantine_exists(&self, locator: &ArtifactLocator) -> Result<bool, DurableArtifactFailure> {
        let path = self.quarantine_path(locator);
        if !path_exists(&path)? {
            return path_exists(&self.conflicts.join(locator_hash(locator)));
        }
        if let Err(e) = self.validate_conflict_ledger(locator, &path) {
            return Err(fail(
                DurableArtifactFailureKind::Quarantined,
                format!("corrupt quarantine remains fail-closed: {e}"),
            ));
        }
        Ok(true)
    }
    fn quarantine_conflict(
        &self,
        locator: &ArtifactLocator,
        existing: &[u8],
        candidate: &[u8],
    ) -> Result<(), DurableArtifactFailure> {
        let dir = checked_child_directory(&self.conflicts, &locator_hash(locator))?;
        let mut observations = [
            (sha256_bytes(existing), existing),
            (sha256_bytes(candidate), candidate),
        ];
        observations.sort_by(|left, right| left.0.cmp(&right.0));
        for (digest, bytes) in &observations {
            publish_immutable(
                &self.staging,
                &dir.join(format!("{digest}.bin")),
                "conflict",
                bytes,
            )?;
        }
        sync_directory(&dir)?;
        self.trip(DurableArtifactFailpoint::BeforeConflictMarker)?;
        let ledger = object([
            ("catalogId", string(self.authority.catalog_id().as_str())),
            ("locator", string(&locator.normalized())),
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
            &self.quarantine_path(locator),
            "quarantine",
            &encode(ledger)?,
        )?;
        self.trip(DurableArtifactFailpoint::AfterConflictMarker)
    }
    fn validate_conflict_ledger(
        &self,
        locator: &ArtifactLocator,
        marker: &Path,
    ) -> Result<(), DurableArtifactFailure> {
        let v = read_canonical(marker, DurableArtifactFailureKind::Corrupt)?;
        let f = exact_fields(
            &v,
            &[
                "catalogId",
                "locator",
                "observations",
                "policy",
                "schemaVersion",
                "state",
            ],
            DurableArtifactFailureKind::Corrupt,
            "conflict ledger",
        )?;
        if f.get("schemaVersion").and_then(SemanticJson::as_i64) != Some(1)
            || f.get("catalogId").and_then(SemanticJson::as_str)
                != Some(self.authority.catalog_id().as_str())
            || f.get("locator").and_then(SemanticJson::as_str)
                != Some(locator.normalized().as_str())
            || f.get("policy").and_then(SemanticJson::as_str) != Some(CONFLICT_POLICY)
            || f.get("state").and_then(SemanticJson::as_str)
                != Some("quarantined-pending-consistency-rerun")
        {
            return Err(fail(
                DurableArtifactFailureKind::Corrupt,
                "conflict ledger mismatch",
            ));
        }
        for d in parse_observations(f, DurableArtifactFailureKind::Corrupt)? {
            let bytes = read_regular(
                &self.conflicts,
                &self
                    .conflicts
                    .join(locator_hash(locator))
                    .join(format!("{d}.bin")),
            )?;
            if sha256_bytes(&bytes) != d {
                return Err(fail(
                    DurableArtifactFailureKind::Corrupt,
                    "conflict observation mismatch",
                ));
            }
        }
        Ok(())
    }
    fn publish_object(&self, target: &Path, bytes: &[u8]) -> Result<(), DurableArtifactFailure> {
        let staged = unique_path(&self.staging, "artifact");
        write_new(&staged, bytes, false)?;
        self.trip(DurableArtifactFailpoint::BeforeStageSync)?;
        File::open(&staged)
            .and_then(|f| f.sync_all())
            .map_err(io_failure("sync stage"))?;
        sync_directory(&self.staging)?;
        self.trip(DurableArtifactFailpoint::BeforeObjectRename)?;
        fs::rename(&staged, target).map_err(io_failure("rename object"))?;
        sync_directory(target.parent().expect("parent"))?;
        sync_directory(&self.staging)
    }
    fn trip(&self, point: DurableArtifactFailpoint) -> Result<(), DurableArtifactFailure> {
        if self.failpoint == Some(point) {
            Err(fail(
                DurableArtifactFailureKind::Io,
                format!("injected failure at {point:?}"),
            ))
        } else {
            Ok(())
        }
    }
    fn object_path(&self, locator: &ArtifactLocator) -> Result<PathBuf, DurableArtifactFailure> {
        validate_locator(locator)?;
        Ok(self.objects.join(locator.tail()))
    }
    fn quarantine_path(&self, locator: &ArtifactLocator) -> PathBuf {
        self.quarantine
            .join(format!("{}.json", locator_hash(locator)))
    }
    fn transaction_path(&self, id: &Digest) -> PathBuf {
        self.transactions.join(format!("{id}.json"))
    }
}

pub struct PreparedArtifactTransaction {
    store: DurableArtifactStore,
    id: Digest,
    bytes: Vec<u8>,
    already_accepted: bool,
    _locks: Vec<DurableProcessLock>,
}
impl PreparedArtifactTransaction {
    #[must_use]
    pub fn id(&self) -> &Digest {
        &self.id
    }
    pub fn commit(self) -> Result<(), DurableArtifactFailure> {
        self.store
            .trip(DurableArtifactFailpoint::BeforeTransactionCommit)?;
        publish_immutable(
            &self.store.staging,
            &self.store.transaction_path(&self.id),
            "transaction",
            &self.bytes,
        )
    }
}
impl fmt::Debug for PreparedArtifactTransaction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PreparedArtifactTransaction")
            .field("id", &self.id)
            .finish_non_exhaustive()
    }
}

impl ArtifactStore for DurableArtifactStore {
    fn fetch(&self, locator: &ArtifactLocator) -> Result<Vec<u8>, ArtifactFailure> {
        validate_locator(locator).map_err(durable_to_artifact)?;
        let entry = self
            .authority
            .entries
            .values()
            .find(|e| &e.locator == locator)
            .ok_or_else(|| {
                ArtifactFailure::new(
                    kink_contracts::ArtifactFailureKind::MissingArtifact,
                    "locator outside bound catalog",
                )
            })?;
        self.ingest(entry)
            .map(|v| v.bytes)
            .map_err(durable_to_artifact)
    }
}

#[doc(hidden)]
pub struct DurableProcessLock {
    file: File,
}
impl DurableProcessLock {
    pub fn acquire(parent: &Path, key: &str) -> Result<Self, DurableArtifactFailure> {
        let path = parent.join(format!("{}.lock", sha256_bytes(key.as_bytes())));
        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(path)
            .map_err(io_failure("open advisory lock"))?;
        sync_directory(parent)?;
        let start = Instant::now();
        loop {
            match file.try_lock_exclusive() {
                Ok(()) => return Ok(Self { file }),
                Err(e) if e.kind() == io::ErrorKind::WouldBlock => {
                    if start.elapsed() >= LOCK_TIMEOUT {
                        return Err(fail(
                            DurableArtifactFailureKind::LockTimeout,
                            "lock timeout",
                        ));
                    }
                    thread::sleep(Duration::from_millis(10));
                }
                Err(e) => return Err(fail(DurableArtifactFailureKind::Io, e.to_string())),
            }
        }
    }
}
impl Drop for DurableProcessLock {
    fn drop(&mut self) {
        let _ = FileExt::unlock(&self.file);
    }
}

fn validate_unbound(
    value: Option<&SemanticJson>,
    registry: &RoleSpecRegistry,
) -> Result<(), DurableArtifactFailure> {
    let rows = value.and_then(SemanticJson::as_array).ok_or_else(|| {
        fail(
            DurableArtifactFailureKind::Authority,
            "unboundRequirements must be array",
        )
    })?;
    let mut seen = BTreeSet::new();
    for row in rows {
        let f = exact_fields(
            row,
            &["requirementId", "role"],
            DurableArtifactFailureKind::Authority,
            "unbound requirement",
        )?;
        let id = f
            .get("requirementId")
            .and_then(SemanticJson::as_str)
            .filter(|v| valid_kebab(v))
            .ok_or_else(|| {
                fail(
                    DurableArtifactFailureKind::Authority,
                    "invalid requirementId",
                )
            })?;
        let role = f
            .get("role")
            .and_then(SemanticJson::as_str)
            .filter(|v| registry.contains(v))
            .ok_or_else(|| {
                fail(
                    DurableArtifactFailureKind::Authority,
                    "invalid requirement role",
                )
            })?;
        if !seen.insert((id, role)) {
            return Err(fail(
                DurableArtifactFailureKind::Authority,
                "duplicate requirement",
            ));
        }
    }
    Ok(())
}

fn registry_authority_sha256(
    repository_root: &Path,
    registry_bytes: &[u8],
) -> Result<Digest, DurableArtifactFailure> {
    let schema_root = repository_root.join("investigations/backend-agnostic-goal-closure/schemas");
    let mut paths = fs::read_dir(&schema_root)
        .map_err(io_failure("scan role schema authority"))?
        .map(|item| item.map(|entry| entry.path()))
        .collect::<Result<Vec<_>, _>>()
        .map_err(io_failure("read role schema authority"))?;
    paths.retain(|path| path.extension().and_then(|value| value.to_str()) == Some("json"));
    paths.sort();

    let mut authority = Vec::new();
    append_authority_part(&mut authority, b"artifact-role-specs.json", registry_bytes);
    for path in paths {
        let name = path
            .file_name()
            .and_then(|value| value.to_str())
            .ok_or_else(|| {
                fail(
                    DurableArtifactFailureKind::Authority,
                    "role schema filename is not UTF-8",
                )
            })?;
        let bytes = fs::read(&path).map_err(io_failure("read role schema authority"))?;
        append_authority_part(&mut authority, name.as_bytes(), &bytes);
    }
    Ok(sha256_bytes(&authority))
}

fn append_authority_part(target: &mut Vec<u8>, name: &[u8], bytes: &[u8]) {
    target.extend_from_slice(&(name.len() as u64).to_be_bytes());
    target.extend_from_slice(name);
    target.extend_from_slice(&(bytes.len() as u64).to_be_bytes());
    target.extend_from_slice(bytes);
}
fn valid_kebab(v: &str) -> bool {
    !v.is_empty()
        && v.split('-').all(|p| {
            !p.is_empty()
                && p.bytes()
                    .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit())
        })
}
fn validate_locator(locator: &ArtifactLocator) -> Result<&str, DurableArtifactFailure> {
    if !locator.is_artifact() {
        return Err(fail(
            DurableArtifactFailureKind::InvalidLocator,
            "artifact:// required",
        ));
    }
    let parsed = ArtifactLocator::parse(
        &locator.normalized(),
        ResolverId::RustArtifactStoreV1,
        ArtifactAvailability::ExternalRequired,
    )
    .map_err(|e| fail(DurableArtifactFailureKind::InvalidLocator, e.to_string()))?;
    if &parsed != locator {
        return Err(fail(
            DurableArtifactFailureKind::InvalidLocator,
            "noncanonical locator",
        ));
    }
    Ok(locator.tail())
}
fn transaction_value(catalog: &Digest, inputs: &[DurableArtifactInput<'_>]) -> SemanticJson {
    object([
        ("catalogId", string(catalog.as_str())),
        (
            "outputs",
            SemanticJson::Array(
                inputs
                    .iter()
                    .map(|i| {
                        object([
                            ("contentSha256", string(i.entry.content_sha256.as_str())),
                            ("locator", string(&i.entry.locator.normalized())),
                        ])
                    })
                    .collect(),
            ),
        ),
        ("schemaVersion", SemanticJson::Integer(1)),
    ])
}
fn with_id(mut value: SemanticJson, id: &Digest) -> SemanticJson {
    let SemanticJson::Object(f) = &mut value else {
        unreachable!()
    };
    f.insert("transactionId".to_owned(), string(id.as_str()));
    value
}
fn bind_authority(root: &Path, bytes: &[u8]) -> Result<(), DurableArtifactFailure> {
    let path = root.join("authority.json");
    match OpenOptions::new().write(true).create_new(true).open(&path) {
        Ok(mut f) => {
            f.write_all(bytes).map_err(io_failure("write authority"))?;
            f.sync_all().map_err(io_failure("sync authority"))?;
            sync_directory(root)
        }
        Err(e) if e.kind() == io::ErrorKind::AlreadyExists => {
            if read_regular(root, &path)? == bytes {
                Ok(())
            } else {
                Err(fail(
                    DurableArtifactFailureKind::Authority,
                    "store authority mismatch",
                ))
            }
        }
        Err(e) => Err(fail(DurableArtifactFailureKind::Io, e.to_string())),
    }
}
fn locator_hash(locator: &ArtifactLocator) -> String {
    sha256_bytes(locator.normalized().as_bytes()).to_string()
}
fn checked_directory(root: &Path, name: &str) -> Result<PathBuf, DurableArtifactFailure> {
    let path = root.join(name);
    fs::create_dir_all(&path).map_err(io_failure("create directory"))?;
    let c = fs::canonicalize(&path).map_err(io_failure("canonicalize directory"))?;
    if !c.starts_with(root) {
        return Err(fail(
            DurableArtifactFailureKind::Io,
            "directory escapes root",
        ));
    }
    Ok(c)
}
fn checked_child_directory(root: &Path, name: &str) -> Result<PathBuf, DurableArtifactFailure> {
    let path = root.join(name);
    let created = match fs::create_dir(&path) {
        Ok(()) => true,
        Err(e) if e.kind() == io::ErrorKind::AlreadyExists => false,
        Err(e) => return Err(fail(DurableArtifactFailureKind::Io, e.to_string())),
    };
    let c = fs::canonicalize(&path).map_err(io_failure("canonicalize child"))?;
    if !c.starts_with(root) {
        return Err(fail(DurableArtifactFailureKind::Io, "child escapes root"));
    }
    if created {
        sync_directory(root)?;
    }
    Ok(c)
}
fn create_contained_directory(root: &Path, path: &Path) -> Result<(), DurableArtifactFailure> {
    let relative = path
        .strip_prefix(root)
        .map_err(|_| fail(DurableArtifactFailureKind::Io, "parent outside root"))?;
    let mut current = root.to_path_buf();
    for part in relative.components() {
        let previous = current.clone();
        current.push(part);
        let made = match fs::create_dir(&current) {
            Ok(()) => true,
            Err(e) if e.kind() == io::ErrorKind::AlreadyExists => false,
            Err(e) => return Err(fail(DurableArtifactFailureKind::Io, e.to_string())),
        };
        let c = fs::canonicalize(&current).map_err(io_failure("canonicalize object parent"))?;
        if !c.starts_with(root) {
            return Err(fail(
                DurableArtifactFailureKind::Io,
                "object parent escapes",
            ));
        }
        if made {
            sync_directory(&previous)?;
        }
    }
    sync_directory(&current)
}
fn publish_immutable(
    staging: &Path,
    target: &Path,
    prefix: &str,
    bytes: &[u8],
) -> Result<(), DurableArtifactFailure> {
    if path_exists(target)? {
        return if read_regular(target.parent().expect("parent"), target)? == bytes {
            Ok(())
        } else {
            Err(fail(
                DurableArtifactFailureKind::Corrupt,
                "immutable metadata conflict",
            ))
        };
    }
    let stage = unique_path(staging, prefix);
    write_new(&stage, bytes, true)?;
    sync_directory(staging)?;
    fs::rename(&stage, target).map_err(io_failure("rename metadata"))?;
    sync_directory(target.parent().expect("parent"))?;
    sync_directory(staging)
}
fn read_regular(root: &Path, path: &Path) -> Result<Vec<u8>, DurableArtifactFailure> {
    let m = fs::symlink_metadata(path).map_err(io_failure("inspect file"))?;
    if !m.file_type().is_file() {
        return Err(fail(
            DurableArtifactFailureKind::Corrupt,
            "not regular file",
        ));
    }
    let c = fs::canonicalize(path).map_err(io_failure("canonicalize file"))?;
    if !c.starts_with(root) {
        return Err(fail(
            DurableArtifactFailureKind::Corrupt,
            "file escapes root",
        ));
    }
    fs::read(path).map_err(io_failure("read file"))
}
fn read_canonical(
    path: &Path,
    kind: DurableArtifactFailureKind,
) -> Result<SemanticJson, DurableArtifactFailure> {
    let bytes = read_regular(path.parent().expect("parent"), path)?;
    let value = parse_json(&bytes).map_err(|e| fail(kind, e.to_string()))?;
    if canonical_json_bytes(&value).map_err(|e| fail(kind, e.to_string()))? != bytes {
        return Err(fail(kind, "noncanonical JSON"));
    }
    Ok(value)
}
fn exact_fields<'a>(
    value: &'a SemanticJson,
    expected: &[&str],
    kind: DurableArtifactFailureKind,
    context: &str,
) -> Result<&'a BTreeMap<String, SemanticJson>, DurableArtifactFailure> {
    let f = value
        .as_object()
        .ok_or_else(|| fail(kind, format!("{context} not object")))?;
    if f.len() != expected.len() || expected.iter().any(|k| !f.contains_key(*k)) {
        return Err(fail(kind, format!("{context} unsupported fields")));
    }
    Ok(f)
}
fn parse_digest(
    fields: &BTreeMap<String, SemanticJson>,
    name: &str,
    kind: DurableArtifactFailureKind,
) -> Result<Digest, DurableArtifactFailure> {
    fields
        .get(name)
        .and_then(SemanticJson::as_str)
        .and_then(|v| Digest::parse(v).ok())
        .ok_or_else(|| fail(kind, format!("invalid {name}")))
}
fn parse_observations(
    f: &BTreeMap<String, SemanticJson>,
    kind: DurableArtifactFailureKind,
) -> Result<[Digest; 2], DurableArtifactFailure> {
    let v = f
        .get("observations")
        .and_then(SemanticJson::as_array)
        .filter(|v| v.len() == 2)
        .ok_or_else(|| fail(kind, "two observations required"))?;
    let a = v[0]
        .as_str()
        .and_then(|v| Digest::parse(v).ok())
        .ok_or_else(|| fail(kind, "invalid observation"))?;
    let b = v[1]
        .as_str()
        .and_then(|v| Digest::parse(v).ok())
        .ok_or_else(|| fail(kind, "invalid observation"))?;
    if a >= b {
        return Err(fail(kind, "observations not canonical distinct order"));
    }
    Ok([a, b])
}
fn path_exists(path: &Path) -> Result<bool, DurableArtifactFailure> {
    match fs::symlink_metadata(path) {
        Ok(_) => Ok(true),
        Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(false),
        Err(e) => Err(fail(DurableArtifactFailureKind::Io, e.to_string())),
    }
}
fn unique_path(parent: &Path, prefix: &str) -> PathBuf {
    parent.join(format!(
        ".{prefix}-{}-{}",
        std::process::id(),
        TEMP_NONCE.fetch_add(1, Ordering::Relaxed)
    ))
}
fn write_new(path: &Path, bytes: &[u8], sync: bool) -> Result<(), DurableArtifactFailure> {
    let mut f = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .map_err(io_failure("create stage"))?;
    f.write_all(bytes).map_err(io_failure("write stage"))?;
    if sync {
        f.sync_all().map_err(io_failure("sync stage"))?;
    }
    Ok(())
}
fn sync_directory(path: &Path) -> Result<(), DurableArtifactFailure> {
    File::open(path)
        .and_then(|f| f.sync_all())
        .map_err(io_failure("sync directory"))
}
fn object(values: impl IntoIterator<Item = (&'static str, SemanticJson)>) -> SemanticJson {
    SemanticJson::Object(values.into_iter().map(|(k, v)| (k.to_owned(), v)).collect())
}
fn string(v: &str) -> SemanticJson {
    SemanticJson::String(v.to_owned())
}
fn encode(v: SemanticJson) -> Result<Vec<u8>, DurableArtifactFailure> {
    canonical_json_bytes(&v).map_err(|e| fail(DurableArtifactFailureKind::Corrupt, e.to_string()))
}
fn authority_failure(e: ArtifactFailure) -> DurableArtifactFailure {
    fail(DurableArtifactFailureKind::Authority, e.to_string())
}
fn validation_failure(e: ArtifactFailure) -> DurableArtifactFailure {
    fail(DurableArtifactFailureKind::Validation, e.to_string())
}
fn durable_to_artifact(e: DurableArtifactFailure) -> ArtifactFailure {
    let kind = match e.kind() {
        DurableArtifactFailureKind::InvalidLocator => {
            kink_contracts::ArtifactFailureKind::ResolverMismatch
        }
        DurableArtifactFailureKind::Missing | DurableArtifactFailureKind::Uncommitted => {
            kink_contracts::ArtifactFailureKind::MissingArtifact
        }
        DurableArtifactFailureKind::Conflict | DurableArtifactFailureKind::Quarantined => {
            kink_contracts::ArtifactFailureKind::Conflict
        }
        DurableArtifactFailureKind::Corrupt => kink_contracts::ArtifactFailureKind::NotRegularFile,
        _ => kink_contracts::ArtifactFailureKind::Io,
    };
    ArtifactFailure::new(kind, e.to_string())
}
fn fail(kind: DurableArtifactFailureKind, detail: impl Into<String>) -> DurableArtifactFailure {
    DurableArtifactFailure::new(kind, detail)
}
fn io_failure(context: &'static str) -> impl FnOnce(io::Error) -> DurableArtifactFailure {
    move |e| fail(DurableArtifactFailureKind::Io, format!("{context}: {e}"))
}
