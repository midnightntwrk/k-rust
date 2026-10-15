//! The killer hints, tier 2 of the outcome cache (flow README 7.5.5): which program last killed
//! each mutation, under a key that survives edits of the specification elsewhere.
//!
//! `<cache>/hints.json` is `{schema: "kink-flow-hints", version: 1, hints: {<hint key>:
//! {program_digest, program_id, mutation_id}}}`. The hint key (digest::hint_key) is the
//! mutation's edits as written (without `line`) and the K text of each addressed rule before
//! the edit: no position and no specification digest. A hint matches the first comparable
//! program with its program digest, so a renamed program keeps its hint.
//!
//! A hint is a scheduling hint and nothing else: the kill search runs the named program first,
//! and every status comes from runs (or from tier 1). It is written as the first killing
//! program after a `killed` status, removed after any other status, and removed whenever the
//! search ignores it because it names no comparable program. The file is written after every
//! mutation, a corpus error included. A file that does not parse, or names another schema, is
//! treated as empty and replaced on the next write; deleting it is always safe.
//!
//! It replaces F-05's `killers/<spec digest>.json`, which kink-flow neither reads nor writes
//! any more.

use kink_corpus::{Store, StoreError};
use kink_patch::Sha256Digest;
use serde_json::{Map, Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
};

/// The `schema` field of the hints file.
pub const HINTS_SCHEMA: &str = "kink-flow-hints";
/// The hints file's version.
pub const HINTS_VERSION: u64 = 1;
/// The hints file's name in the cache directory.
pub const HINTS_FILE: &str = "hints.json";

/// One killer hint.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HintEntry {
    /// The digest of the program that killed the mutation.
    pub program_digest: String,
    /// That program's id when the hint was written (informational).
    pub program_id: String,
    /// The mutation's id when the hint was written (informational).
    pub mutation_id: String,
}

/// The killer hints of one cache directory.
#[derive(Clone, Debug)]
pub struct Hints {
    path: PathBuf,
    entries: BTreeMap<String, HintEntry>,
}

/// The hints file under `cache`.
pub fn hints_path(cache: &Path) -> PathBuf {
    cache.join(HINTS_FILE)
}

impl Hints {
    /// Read the hints of `cache`; a missing or unreadable file has none.
    pub fn read(cache: &Path) -> Self {
        let path = hints_path(cache);
        let entries = fs::read_to_string(&path)
            .ok()
            .and_then(|text| serde_json::from_str::<Value>(&text).ok())
            .filter(|value| value["schema"] == HINTS_SCHEMA && value["version"] == HINTS_VERSION)
            .and_then(|value| value.get("hints").and_then(Value::as_object).cloned())
            .map(|hints| {
                hints
                    .into_iter()
                    .filter_map(|(key, entry)| Some((key, entry_of(&entry)?)))
                    .collect()
            })
            .unwrap_or_default();
        Self { path, entries }
    }

    /// The hint of the mutation with hint key `key`.
    pub fn get(&self, key: Sha256Digest) -> Option<&HintEntry> {
        self.entries.get(&key.to_string())
    }

    /// Record `entry` as the hint of `key`.
    pub fn insert(&mut self, key: Sha256Digest, entry: HintEntry) {
        self.entries.insert(key.to_string(), entry);
    }

    /// Forget the hint of `key`.
    pub fn remove(&mut self, key: Sha256Digest) {
        self.entries.remove(&key.to_string());
    }

    /// The program digests some hint names.
    pub fn program_digests(&self) -> BTreeSet<&str> {
        self.entries
            .values()
            .map(|entry| entry.program_digest.as_str())
            .collect()
    }

    /// The number of hints.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// No hint.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// The file's JSON value.
    pub fn value(&self) -> Value {
        let hints = self
            .entries
            .iter()
            .map(|(key, entry)| {
                (
                    key.clone(),
                    json!({
                        "program_digest": entry.program_digest,
                        "program_id": entry.program_id,
                        "mutation_id": entry.mutation_id,
                    }),
                )
            })
            .collect::<Map<_, _>>();
        json!({"schema": HINTS_SCHEMA, "version": HINTS_VERSION, "hints": hints})
    }

    /// Write the hints atomically (temporary name, fsync, rename; kink-corpus `Store`).
    pub fn write(&self, store: &Store) -> Result<(), StoreError> {
        store.write_json(&self.path, &self.value())
    }

    /// The hints file's path.
    pub fn path(&self) -> &Path {
        &self.path
    }
}

fn entry_of(value: &Value) -> Option<HintEntry> {
    let field = |key: &str| value.get(key)?.as_str().map(str::to_owned);
    Some(HintEntry {
        program_digest: field("program_digest")?,
        program_id: field("program_id")?,
        mutation_id: field("mutation_id")?,
    })
}
