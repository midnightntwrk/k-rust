//! The per-user cache of compiled stages for `krs parse`, `run`, `search`, and `prove`.
//!
//! Each of those commands compiles its Definition IR through the native frontend before it does anything else, and that compilation dominates a short run.
//! The compiled stage ([`krs_exec::CompiledStage`]) is stored under a key that digests the Definition IR's canonical JSON, the pinned k-rust commit, the stage format, and the identity of the running `krs` executable, so a changed definition, k-rust pin, or `krs` build misses.
//! `krs prove --spec-module NAME` also compiles that author spec module's proof definition ([`krs_exec::SpecStage`]); it is stored under the same key plus the module name, and the Definition IR digest covers the spec module's content.
//! Results are never cached: a run still runs.
//!
//! The store is `KRS_STAGE_CACHE_DIR`, or `${XDG_CACHE_HOME:-~/.cache}/krs/compiled-stages/v1`, and belongs to one Unix user.
//! A store inside the input's Cargo workspace is not used, so an entry is never committed with the package; the command warns (`krs::exec::stage-cache`) and compiles the stage.
//! An entry unused for 30 days is deleted, at most once a day.
//! Every failure to read or write the store only means the stage is compiled again.

use super::result_cache::{Executable, executable};
use krs_exec::{CompiledStage, SPEC_STAGE_FORMAT, STAGE_FORMAT, SpecStage};
use krs_ir_levels::DefinitionIr;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::fs;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::time::{Duration, SystemTime};

/// Overrides the store directory.
const STAGE_CACHE_VARIABLE: &str = "KRS_STAGE_CACHE_DIR";
/// The layout version of the store directory.
const LAYOUT: &str = "v1";
/// The schema of an entry's header.
const SCHEMA: u32 = 1;
const MAX_UNUSED: Duration = Duration::from_hours(30 * 24);
const PRUNE_INTERVAL: Duration = Duration::from_hours(24);
/// The repository lock that pins k-rust; `krs` is always built from a KRS checkout.
const LOCK: &str = include_str!("../../../../Krs.lock");

/// What the key digests.
#[derive(Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct Key {
    stage_format: String,
    krs_version: String,
    k_rust_commit: Option<String>,
    krs: Executable,
    definition_ir_sha256: String,
    /// The author spec module of a [`SpecStage`]; absent for the definition's [`CompiledStage`].
    #[serde(default, skip_serializing_if = "Option::is_none")]
    spec_module: Option<String>,
}

/// An entry: its key in full, then the payload digest, ahead of the payload.
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Header {
    schema: u32,
    key: Key,
    payload_len: usize,
    payload_sha256: String,
}

/// One definition's place in the store.
pub(super) struct StageCache {
    root: PathBuf,
    entry: PathBuf,
    key: Key,
}

/// A store directory that lies inside the input's Cargo workspace, which is therefore not used.
#[derive(Debug, PartialEq, Eq)]
pub(super) struct StoreInsideWorkspace {
    /// The store directory, resolved.
    store: PathBuf,
    /// The workspace root, resolved.
    workspace: PathBuf,
    /// Whether [`STAGE_CACHE_VARIABLE`] named the store.
    explicit: bool,
}

impl StoreInsideWorkspace {
    /// The warning text.
    pub(super) fn message(&self) -> String {
        let named = if self.explicit {
            format!("{STAGE_CACHE_VARIABLE} names `{}`", self.store.display())
        } else {
            format!("the stage cache `{}`", self.store.display())
        };
        format!(
            "{named}, which is inside the Cargo workspace `{}`, so the compiled stage is neither restored nor stored and every command compiles the definition again; set {STAGE_CACHE_VARIABLE} to a directory outside the workspace",
            self.workspace.display()
        )
    }
}

impl StageCache {
    /// The entry for `definition`: `Ok(None)` when there is no usable store, and an error when the store lies inside the input's Cargo workspace.
    pub(super) fn new(
        definition: &DefinitionIr,
        workspace_root: Option<&Path>,
    ) -> Result<Option<Self>, StoreInsideWorkspace> {
        let Some(root) = store_root(std::env::var_os(STAGE_CACHE_VARIABLE), workspace_root)? else {
            return Ok(None);
        };
        Ok(Self::at(root, definition))
    }

    fn at(root: PathBuf, definition: &DefinitionIr) -> Option<Self> {
        let krs = executable(&std::env::current_exe().ok()?, true)?;
        let ir = definition.to_canonical_json().ok()?;
        let key = Key {
            stage_format: STAGE_FORMAT.to_owned(),
            krs_version: env!("CARGO_PKG_VERSION").to_owned(),
            k_rust_commit: k_rust_commit(),
            krs,
            definition_ir_sha256: sha256(ir.as_bytes()),
            spec_module: None,
        };
        Self::keyed(root, key)
    }

    fn keyed(root: PathBuf, key: Key) -> Option<Self> {
        let digest = sha256(&serde_json::to_vec(&key).ok()?);
        let entry = root
            .join("entries")
            .join(&digest[..2])
            .join(format!("{digest}.stage"));
        Some(Self { root, entry, key })
    }

    /// The entry for the proof definition of the author spec module `module` of the same Definition IR.
    pub(super) fn for_spec_module(&self, module: &str) -> Option<Self> {
        let key = Key {
            stage_format: SPEC_STAGE_FORMAT.to_owned(),
            spec_module: Some(module.to_owned()),
            ..self.key.clone()
        };
        Self::keyed(self.root.clone(), key)
    }

    /// The stored stage, when the entry exists, is intact, and was written under this exact key.
    pub(super) fn load(&self) -> Option<CompiledStage> {
        let stage = CompiledStage::decode(&self.load_payload()?)?;
        self.touch();
        Some(stage)
    }

    /// The stored spec stage, when the entry exists, is intact, and was written under this exact key.
    pub(super) fn load_spec(&self) -> Option<SpecStage> {
        let stage = SpecStage::decode(&self.load_payload()?)
            .filter(|stage| self.key.spec_module.as_deref() == Some(stage.module()))?;
        self.touch();
        Some(stage)
    }

    /// The entry's payload, when the entry is intact and was written under this exact key.
    fn load_payload(&self) -> Option<Vec<u8>> {
        let mut bytes = fs::read(&self.entry).ok()?;
        let length = usize::try_from(u64::from_le_bytes(bytes.get(..8)?.try_into().ok()?)).ok()?;
        let payload_start = 8usize.checked_add(length)?;
        let header: Header = serde_json::from_slice(bytes.get(8..payload_start)?).ok()?;
        let payload = bytes.get(payload_start..)?;
        if header.schema != SCHEMA
            || header.key != self.key
            || header.payload_len != payload.len()
            || header.payload_sha256 != sha256(payload)
        {
            return None;
        }
        bytes.drain(..payload_start);
        Some(bytes)
    }

    /// Mark the entry used, which keeps it from being pruned.
    fn touch(&self) {
        let _ = fs::File::options()
            .write(true)
            .open(&self.entry)
            .and_then(|file| file.set_modified(SystemTime::now()));
    }

    /// Store `stage`, replacing the entry atomically; a stage without a faithful encoding is not stored.
    pub(super) fn store(&self, stage: &CompiledStage) {
        if let Some(payload) = stage.encode() {
            self.store_payload(&payload);
        }
    }

    /// Store a spec stage, as [`Self::store`] does.
    pub(super) fn store_spec(&self, stage: &SpecStage) {
        if let Some(payload) = stage.encode() {
            self.store_payload(&payload);
        }
    }

    fn store_payload(&self, payload: &[u8]) {
        let header = Header {
            schema: SCHEMA,
            key: self.key.clone(),
            payload_len: payload.len(),
            payload_sha256: sha256(payload),
        };
        let Ok(header) = serde_json::to_vec(&header) else {
            return;
        };
        let Some(directory) = self.entry.parent() else {
            return;
        };
        if fs::create_dir_all(directory).is_err() {
            return;
        }
        let Ok(mut temporary) = tempfile::NamedTempFile::new_in(directory) else {
            return;
        };
        let written = temporary
            .write_all(&(header.len() as u64).to_le_bytes())
            .and_then(|()| temporary.write_all(&header))
            .and_then(|()| temporary.write_all(payload));
        if written.is_ok() {
            let _ = temporary.persist(&self.entry);
        }
        self.prune();
    }

    /// Delete entries unused for [`MAX_UNUSED`], at most once per [`PRUNE_INTERVAL`].
    fn prune(&self) {
        let stamp = self.root.join("last-prune");
        let now = SystemTime::now();
        let recent = fs::metadata(&stamp)
            .and_then(|metadata| metadata.modified())
            .is_ok_and(|modified| {
                now.duration_since(modified)
                    .is_ok_and(|age| age < PRUNE_INTERVAL)
            });
        if recent || fs::write(&stamp, b"").is_err() {
            return;
        }
        let Ok(shards) = fs::read_dir(self.root.join("entries")) else {
            return;
        };
        for shard in shards.flatten() {
            let Ok(entries) = fs::read_dir(shard.path()) else {
                continue;
            };
            for entry in entries.flatten() {
                let unused = entry
                    .metadata()
                    .and_then(|metadata| metadata.modified())
                    .is_ok_and(|modified| {
                        now.duration_since(modified)
                            .is_ok_and(|age| age > MAX_UNUSED)
                    });
                if unused {
                    let _ = fs::remove_file(entry.path());
                }
            }
        }
    }
}

/// The store directory: `explicit` (from [`STAGE_CACHE_VARIABLE`]), or the per-user default; `Ok(None)` when neither can be named, and an error when the store would lie inside the input's Cargo workspace.
fn store_root(
    explicit: Option<std::ffi::OsString>,
    workspace_root: Option<&Path>,
) -> Result<Option<PathBuf>, StoreInsideWorkspace> {
    let explicit = explicit.filter(|value| !value.is_empty());
    let is_explicit = explicit.is_some();
    let root = if let Some(explicit) = explicit {
        PathBuf::from(explicit)
    } else {
        let Some(base) = std::env::var_os("XDG_CACHE_HOME")
            .map(PathBuf::from)
            .filter(|base| base.is_absolute())
            .or_else(|| {
                std::env::var_os("HOME")
                    .map(PathBuf::from)
                    .filter(|home| home.is_absolute())
                    .map(|home| home.join(".cache"))
            })
        else {
            return Ok(None);
        };
        base.join("krs").join("compiled-stages").join(LAYOUT)
    };
    let Ok(root) = std::path::absolute(root) else {
        return Ok(None);
    };
    if let Some(workspace) = workspace_root {
        let resolved = nearest_canonical(&root);
        let workspace = fs::canonicalize(workspace).unwrap_or_else(|_| workspace.to_path_buf());
        if resolved.starts_with(&workspace) {
            return Err(StoreInsideWorkspace {
                store: resolved,
                workspace,
                explicit: is_explicit,
            });
        }
    }
    Ok(Some(root))
}

/// `path` with its longest existing ancestor resolved, so a store that does not exist yet is still placed correctly.
fn nearest_canonical(path: &Path) -> PathBuf {
    let mut missing = Vec::new();
    let mut current = path;
    loop {
        if let Ok(resolved) = fs::canonicalize(current) {
            return missing
                .iter()
                .rev()
                .fold(resolved, |resolved, part| resolved.join(part));
        }
        match (current.parent(), current.file_name()) {
            (Some(parent), Some(name)) => {
                missing.push(name.to_owned());
                current = parent;
            }
            _ => return path.to_path_buf(),
        }
    }
}

/// `[k_rust] commit` of the repository lock this `krs` was built with.
fn k_rust_commit() -> Option<String> {
    let lock = LOCK.parse::<toml_edit::DocumentMut>().ok()?;
    lock.get("k_rust")?
        .get("commit")?
        .as_str()
        .map(str::to_owned)
}

fn sha256(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_lock_names_the_k_rust_commit() {
        let commit = k_rust_commit().expect("Krs.lock pins a k-rust commit");
        assert_eq!(commit.len(), 40, "{commit}");
        assert!(
            commit.bytes().all(|byte| byte.is_ascii_hexdigit()),
            "{commit}"
        );
    }

    #[test]
    fn an_explicit_store_is_used_outside_the_workspace_and_refused_inside_it() {
        let workspace = tempfile::tempdir().expect("temporary workspace");
        let outside = tempfile::tempdir().expect("temporary store");
        let explicit = outside.path().join("stages");
        assert_eq!(
            store_root(Some(explicit.clone().into()), Some(workspace.path())),
            Ok(Some(explicit))
        );
        let inside = workspace.path().join("target").join("stages");
        let refused = store_root(Some(inside.into()), Some(workspace.path()))
            .expect_err("a store inside the workspace is refused");
        let workspace = fs::canonicalize(workspace.path()).unwrap();
        assert_eq!(refused.store, workspace.join("target").join("stages"));
        assert_eq!(refused.workspace, workspace);
        assert!(refused.explicit);
        assert!(
            refused.message().starts_with("KRS_STAGE_CACHE_DIR names `"),
            "{}",
            refused.message()
        );
    }
}
