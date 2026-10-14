//! The killer cache (flow README 5.6 step 5): per specification digest, which program last
//! killed each mutation.
//!
//! `<cache>/killers/<spec digest>.json` maps a mutation digest (`Patch::digest`) to
//! `{mutation_id, program_id, program_digest}`. An entry is a scheduling hint and nothing
//! else: the kill search runs the named program first, and the verdict always comes from that
//! run. An entry is written only from a `Killed` status's first killing test; every other
//! status removes it. A file that does not parse, or names another schema or specification,
//! is treated as empty (and replaced on the next write); deleting it is always safe.

use kink_corpus::{Store, StoreError};
use kink_patch::Sha256Digest;
use serde_json::{Map, Value, json};
use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
};

/// The `schema` field of a killer cache file.
pub const KILLERS_SCHEMA: &str = "kink-flow-killers";
/// The killer cache file's version.
pub const KILLERS_VERSION: u64 = 1;

/// One cached killer.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct KillerEntry {
    /// The mutation's id when the entry was written (informational).
    pub mutation_id: String,
    /// The program that killed the mutation.
    pub program_id: String,
    /// That program's digest when it killed the mutation.
    pub program_digest: String,
}

/// The killer cache of one specification.
#[derive(Clone, Debug)]
pub struct KillerCache {
    path: PathBuf,
    spec: Sha256Digest,
    entries: BTreeMap<String, KillerEntry>,
}

/// The killer cache file of a specification under `cache`.
pub fn killers_path(cache: &Path, spec: Sha256Digest) -> PathBuf {
    cache.join("killers").join(format!("{spec}.json"))
}

impl KillerCache {
    /// Read the specification's killer cache; a missing or unreadable file is empty.
    pub fn read(cache: &Path, spec: Sha256Digest) -> Self {
        let path = killers_path(cache, spec);
        let entries = fs::read_to_string(&path)
            .ok()
            .and_then(|text| serde_json::from_str::<Value>(&text).ok())
            .filter(|value| {
                value["schema"] == KILLERS_SCHEMA
                    && value["version"] == KILLERS_VERSION
                    && value["spec"] == spec.to_string()
            })
            .and_then(|value| value.get("killers").and_then(Value::as_object).cloned())
            .map(|killers| {
                killers
                    .into_iter()
                    .filter_map(|(digest, entry)| Some((digest, entry_of(&entry)?)))
                    .collect()
            })
            .unwrap_or_default();
        Self {
            path,
            spec,
            entries,
        }
    }

    /// The cached killer of the mutation with `digest`.
    pub fn get(&self, digest: Sha256Digest) -> Option<&KillerEntry> {
        self.entries.get(&digest.to_string())
    }

    /// Record `entry` as the killer of the mutation with `digest`.
    pub fn insert(&mut self, digest: Sha256Digest, entry: KillerEntry) {
        self.entries.insert(digest.to_string(), entry);
    }

    /// Forget the killer of the mutation with `digest`.
    pub fn remove(&mut self, digest: Sha256Digest) {
        self.entries.remove(&digest.to_string());
    }

    /// The number of entries.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// No entry.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// The file's JSON value.
    pub fn value(&self) -> Value {
        let killers = self
            .entries
            .iter()
            .map(|(digest, entry)| {
                (
                    digest.clone(),
                    json!({
                        "mutation_id": entry.mutation_id,
                        "program_id": entry.program_id,
                        "program_digest": entry.program_digest,
                    }),
                )
            })
            .collect::<Map<_, _>>();
        json!({
            "schema": KILLERS_SCHEMA,
            "version": KILLERS_VERSION,
            "spec": self.spec.to_string(),
            "killers": killers,
        })
    }

    /// Write the cache atomically (temporary name, fsync, rename; kink-corpus `Store`).
    pub fn write(&self, store: &Store) -> Result<(), StoreError> {
        store.write_json(&self.path, &self.value())
    }

    /// The cache file's path.
    pub fn path(&self) -> &Path {
        &self.path
    }
}

fn entry_of(value: &Value) -> Option<KillerEntry> {
    let field = |key: &str| value.get(key)?.as_str().map(str::to_owned);
    Some(KillerEntry {
        mutation_id: field("mutation_id")?,
        program_id: field("program_id")?,
        program_digest: field("program_digest")?,
    })
}
