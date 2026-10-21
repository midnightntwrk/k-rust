//! The warm path's memos (re-pin L1-4): what `run` would otherwise recompute, in every command,
//! from inputs that did not change.
//!
//! On `examples/imp` warm, every mutation is decided by tier 1, yet 70 % of the run's wall time
//! was resolution: one full k-rust load of the specification and its prelude per mutation
//! ([`crate::mutation::resolve`]), and most of the rest was the specification's declaration
//! census. Neither has an exact cheaper form inside one process (a load parses every bubble of
//! the definition, and k-rust documents no load of only the edited module), so each gets a
//! persistent memo, under the rule every store kink honours without re-deriving follows (packet
//! CACHE-ID-fix-1): a memo is sound when its key names every input its value depends on and it
//! adds no premise to the ones the uncached path rests on. Then a hit returns exactly what
//! recomputation returns.
//!
//! **The resolution memo** holds, per mutation, the facts of its resolution that a row decided by
//! tier 1 reads: the patch digest, the edited rules (texts, lines, labels, whether the
//! `requires` changed), the tier-1 mutation identity, the edited rules' typing diagnostics and
//! the claims the edit leaves unbacked ([`Facts`]). It never holds the patch, and a memo hit is
//! used only for a mutation that tier 1 decides with no call (a valid killed record, or a valid
//! agreement for every program of O): every mutation that compiles or runs anything is resolved
//! live in this command, so no memo ever feeds a compile, a load of a mutant or an execution
//! (the patch's canonical JSON does not carry k-rust's term metadata, so a decoded patch would
//! not be the patch resolution builds). Its key ([`resolution_key`]) names every input
//! resolution reads:
//! - the specification digest (`digest::spec_digest`): the k-rust revision and solver profile,
//!   the entry, main and syntax modules, the Markdown selector, the include directories and
//!   every source file the load read, by name and SHA-256. Resolution reads the specification
//!   only through them: the admitted load (`loaded`: its baseline, file list and selector, a
//!   function of these by k-rust's load determinism, the premise the result cache and tier 1's
//!   execution digest already rest on), each touched file's bytes, checked against the
//!   recorded SHA-256 (`View::read`, else `source-changed`), and the edited load, which reads the
//!   same files under the same options with the edited views in place of the edited files
//!   (`load_source_with_overlay` with `admit::corpus_source`). Before any record is read, every
//!   source file must still have its recorded SHA-256 ([`sources_unchanged`]), so the files the
//!   uncached path would read are the ones the key names;
//! - the mutation's edits, in order, every field ([`mutation_entry`]: `file`, `rule`, `line`,
//!   `find`/`replace` or `delete`). Its `id` only names the row and its `note` is never read by
//!   resolution;
//! - kink's build (`kink_build`, which also fixes the linked k-rust, the load options and every
//!   algorithm with or without a version) and its semantics identity (`kink`);
//! - the record's format and meaning ([`RESOLUTION_MEMO_VERSION`]).
//!
//! kink-flow `tests/memo.rs` builds both keys member by member from these inputs and requires
//! them equal to the keys built here, and `tests/results.rs` requires the specification digest
//! to change with each `[spec]` field, so a key or digest that drops an input fails a test; so
//! does a run that reads a record after a source file changed (re-pin L1-4-tail, review L1-4-2
//! N1).
//!
//! The facts derived from the resolved patch (identity, typing diagnostics, claims) are
//! functions of the patch and the baseline, so of the same inputs. A typing diagnostic that says
//! a rule was not typed (a stack segment refused by kink's limit or by the host) depends on the
//! host and is never memoised.
//!
//! **The host premise** (re-pin L1-4 fix 1; review L1-4-1 D4 and its new premise). A record exists
//! only because resolution succeeded where it was written, and success itself can depend on the
//! host: the patch codec's native stack segment (live, a refused segment is the row `error`,
//! reason `host-stack-refused`), the heap and address space of the edited load (live, an
//! exhausted allocation aborts the process), and the native stack segment each edited rule is
//! typed on, sized from the rule's depth apart from the codec's (kink-patch `apply`; live, a host
//! that grants the codec's segment and refuses the typing segment resolves the mutation with a
//! typing diagnostic that says the rule was not typed, and the row's status is unchanged). The
//! key does not name the host's capacity, and kink does not try to: a memo hit returns the
//! tier-1-decided row that a host which could resolve the mutation computed for the same mutant
//! identity, where live resolution on a smaller host would end `host-stack-refused`, abort, or
//! give the same row with a typing diagnostic that says the rule was not typed where the memo
//! gives the writer's typing diagnostics (re-pin L1-4-tail; review L1-4-2 N2). That cannot make a
//! false kill or hide a survivor (the row is the verdict of the same mutant, judged where the host
//! granted the stack, as the README recommends for `host-stack-refused`, and typing diagnostics
//! decide nothing), but it is a premise the uncached path does not have: before L1-4 every
//! resolution was recomputed in every command, so nothing stored a success the reading host could
//! not reproduce. So the documents of a run with and without memos are equal on a host that
//! grants the stack and heap resolution needs; on a smaller one, the run with memos can give a
//! decided row where the run without gives `host-stack-refused` or aborts, or the writer's typing
//! diagnostics where the run without says a rule was not typed (kink-flow README, **Memos**).
//!
//! **The census memo** holds the specification's declaration census (kink-native
//! `declaration_census`, the VI-T13 admission gate), a function of the compiled baseline and of
//! kink's build (its reference prelude, the hooks k-rust implements). The compiled baseline is
//! the compile of the admitted load under fixed options, so the key is the specification digest,
//! `kink_build` and `kink` ([`census_key`]); the premise is compile determinism (C-12), the one
//! every kill rests on.
//!
//! Both are off under the Z3 profile, as tier 1 is (`search::tier1_refusal`: k-rust's load can
//! ask Z3, whose queries can time out), when kink's build identity is unknown, and with `run
//! --no-memo`. `run --verify` reads no memo: it resolves every mutation and runs every census
//! live and reports each stored record that differs (`resolution-mismatch`, a census mismatch in
//! `mismatches`, also when the live census refuses the specification, and also for a mutation
//! `--only` does not select or a corpus error left unsearched). No memo is ever written by
//! `--verify`, and a memo never enters the run document: on a host that grants the stack and heap
//! resolution needs (the host premise above), a run with and without memos writes the same
//! document, outcomes and hints.

use crate::mutation::{EditAction, EditSpec, EditedRule, Mutation};
use kink_corpus::{LoadedSource, Store};
use kink_native::DeclarationCensus;
use kink_patch::{SentenceRef, Sha256Digest, canonical_json, parse_json, payload_digest, sha256};
use serde_json::{Value, json};
use std::{fs, path::Path};

/// The format and meaning of a resolution memo record (its key's `version` and its digest's
/// domain).
pub const RESOLUTION_MEMO_VERSION: &str = "kink-flow/resolution-memo/v1";
/// The format and meaning of a census memo record (its key's `version` and its digest's domain).
pub const CENSUS_MEMO_VERSION: &str = "kink-flow/census-memo/v1";
/// The memos' directory in the cache directory: `memo/resolutions/<spec digest>/<entry
/// digest>.json` and `memo/census/<spec digest>.json`.
pub const MEMO_DIRECTORY: &str = "memo";

/// The record schema of both memos.
const MEMO_SCHEMA: &str = "kink-flow-memo";

/// Whether `run` uses the memos (`--no-memo`: never read or written).
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum MemoUse {
    #[default]
    On,
    Off,
}

/// The facts of a mutation's resolution that a row decided by tier 1 reads (`search_one` steps 1
/// to 3): computed from the live resolution, or read from the resolution memo.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Facts {
    /// [`kink_patch::Patch::digest`] of the patch.
    pub digest: Sha256Digest,
    /// The edited rules ([`crate::mutation::ResolvedMutation::rules`]).
    pub rules: Vec<EditedRule>,
    /// The tier-1 mutation identity (`digest::mutation_identity`).
    pub identity: Option<Sha256Digest>,
    /// The row's `typing_diagnostics` (`report::typing_diagnostics_value` of the generation's
    /// candidate).
    pub typing_diagnostics: Value,
    /// The row's `removed_claims` before any call (`report::claims_value` of the patch's
    /// withdrawal, null when there is none).
    pub removed_claims: Value,
}

impl Facts {
    /// The record value of the facts.
    pub fn value(&self) -> Value {
        json!({
            "digest": self.digest.to_string(),
            "rules": self.rules.iter().map(|rule| {
                let EditedRule {
                    at,
                    edits,
                    file,
                    label,
                    start_line,
                    end_line,
                    before,
                    after,
                    requires_edited,
                } = rule;
                json!({
                    "module": at.module,
                    "index": at.index,
                    "edits": edits,
                    "file": file,
                    "label": label,
                    "start_line": start_line,
                    "end_line": end_line,
                    "before": before,
                    "after": after,
                    "requires_edited": requires_edited,
                })
            }).collect::<Vec<_>>(),
            "identity": self.identity.map(|identity| identity.to_string()),
            "typing_diagnostics": self.typing_diagnostics,
            "removed_claims": self.removed_claims,
        })
    }

    /// The facts whose [`Self::value`] is `value`, or `None` for any other value.
    pub fn from_value(value: &Value) -> Option<Self> {
        let text = |v: &Value| v.as_str().map(str::to_owned);
        let rules = value["rules"]
            .as_array()?
            .iter()
            .map(|rule| {
                Some(EditedRule {
                    at: SentenceRef::new(
                        rule["module"].as_str()?,
                        u32::try_from(rule["index"].as_u64()?).ok()?,
                    ),
                    edits: rule["edits"]
                        .as_array()?
                        .iter()
                        .map(|edit| usize::try_from(edit.as_u64()?).ok())
                        .collect::<Option<Vec<_>>>()?,
                    file: text(&rule["file"])?,
                    label: if rule["label"].is_null() {
                        None
                    } else {
                        Some(text(&rule["label"])?)
                    },
                    start_line: u32::try_from(rule["start_line"].as_u64()?).ok()?,
                    end_line: u32::try_from(rule["end_line"].as_u64()?).ok()?,
                    before: text(&rule["before"])?,
                    after: if rule["after"].is_null() {
                        None
                    } else {
                        Some(text(&rule["after"])?)
                    },
                    requires_edited: rule["requires_edited"].as_bool()?,
                })
            })
            .collect::<Option<Vec<_>>>()?;
        let facts = Self {
            digest: Sha256Digest::parse(value["digest"].as_str()?)?,
            rules,
            identity: if value["identity"].is_null() {
                None
            } else {
                Some(Sha256Digest::parse(value["identity"].as_str()?)?)
            },
            typing_diagnostics: value.get("typing_diagnostics")?.clone(),
            removed_claims: value.get("removed_claims")?.clone(),
        };
        (facts.value() == *value).then_some(facts)
    }

    /// Whether the facts may be memoised: they depend on the key's inputs alone. A typing
    /// diagnostic that says a rule was not typed (kink-patch `apply`: its stack segment was
    /// refused by kink's limit or by the host) depends on the host's address space, so the
    /// facts that carry one are never written.
    pub fn memoisable(&self) -> bool {
        self.typing_diagnostics
            .as_array()
            .is_some_and(|diagnostics| {
                diagnostics.iter().all(|diagnostic| {
                    !diagnostic["message"]
                        .as_str()
                        .is_some_and(|message| message.starts_with("not typed"))
                })
            })
    }
}

/// Every input of a mutation that resolution reads (module docs): its edits in order, each with
/// every field. The id only names the row, and the note is free text resolution never reads.
pub fn mutation_entry(mutation: &Mutation) -> Value {
    let Mutation {
        id: _,
        note: _,
        edits,
    } = mutation;
    Value::Array(
        edits
            .iter()
            .map(|edit| {
                let EditSpec {
                    file,
                    rule,
                    line,
                    action,
                } = edit;
                let (find, replace, delete) = match action {
                    EditAction::Replace { find, replace } => (json!(find), json!(replace), false),
                    EditAction::Delete => (Value::Null, Value::Null, true),
                };
                json!({
                    "file": file,
                    "rule": rule,
                    "line": line,
                    "find": find,
                    "replace": replace,
                    "delete": delete,
                })
            })
            .collect(),
    )
}

/// The resolution memo key of `mutation` under the specification digest `spec` and kink's build
/// `build` (module docs: every input resolution reads).
pub fn resolution_key(spec: Sha256Digest, build: Sha256Digest, mutation: &Mutation) -> Value {
    json!({
        "version": RESOLUTION_MEMO_VERSION,
        "kink_build": build.to_string(),
        "kink": kink_campaign::kink_identity(),
        "spec": spec.to_string(),
        "mutation": mutation_entry(mutation),
    })
}

/// The census memo key of the specification digest `spec` under kink's build `build`.
pub fn census_key(spec: Sha256Digest, build: Sha256Digest) -> Value {
    json!({
        "version": CENSUS_MEMO_VERSION,
        "kink_build": build.to_string(),
        "kink": kink_campaign::kink_identity(),
        "spec": spec.to_string(),
    })
}

/// Where the resolution memo keeps the record of `mutation` under the specification digest
/// `spec`. The key decides what a record may be used for; the path only finds it.
pub fn resolution_path(
    cache: &Path,
    spec: Sha256Digest,
    mutation: &Mutation,
) -> std::path::PathBuf {
    cache
        .join(MEMO_DIRECTORY)
        .join("resolutions")
        .join(spec.to_string())
        .join(format!(
            "{}.json",
            sha256(canonical_json(&mutation_entry(mutation)).as_bytes())
        ))
}

/// Where the census memo keeps the census of the specification digest `spec`.
pub fn census_path(cache: &Path, spec: Sha256Digest) -> std::path::PathBuf {
    cache
        .join(MEMO_DIRECTORY)
        .join("census")
        .join(format!("{spec}.json"))
}

fn record_sha256(domain: &str, key: &Value, value: &Value) -> Sha256Digest {
    payload_digest(
        domain,
        canonical_json(&json!({"key": key, "value": value})).as_bytes(),
    )
}

/// The stored value under exactly `key` at `path`: `None` when the file is missing or
/// unreadable, is not a memo record, names another key, or does not carry its own digest.
fn read(path: &Path, domain: &str, key: &Value) -> Option<Value> {
    let record = parse_json(&fs::read_to_string(path).ok()?).ok()?;
    let value = record.get("value")?;
    (record["schema"] == MEMO_SCHEMA
        && record["key"] == *key
        && record["record_sha256"].as_str()
            == Some(record_sha256(domain, key, value).to_string().as_str()))
    .then(|| value.clone())
}

/// Write `value` under `key` at `path`. A memo that cannot be written is only a later
/// recomputation, so a failure is not reported.
fn write(store: &Store, path: &Path, domain: &str, key: &Value, value: &Value) {
    let _ = store.write_json(
        path,
        &json!({
            "schema": MEMO_SCHEMA,
            "key": key,
            "value": value,
            "record_sha256": record_sha256(domain, key, value).to_string(),
        }),
    );
}

/// The facts stored under exactly `key` at `path`.
pub fn read_facts(path: &Path, key: &Value) -> Option<Facts> {
    Facts::from_value(&read(path, RESOLUTION_MEMO_VERSION, key)?)
}

/// Store `facts` under `key` at `path`, when they are [`Facts::memoisable`].
pub fn write_facts(store: &Store, path: &Path, key: &Value, facts: &Facts) {
    if facts.memoisable() {
        write(store, path, RESOLUTION_MEMO_VERSION, key, &facts.value());
    }
}

/// The census stored under exactly `key` at `path`.
pub fn read_census(path: &Path, key: &Value) -> Option<DeclarationCensus> {
    DeclarationCensus::from_value(&read(path, CENSUS_MEMO_VERSION, key)?)
}

/// Store `census` under `key` at `path`.
pub fn write_census(store: &Store, path: &Path, key: &Value, census: &DeclarationCensus) {
    write(store, path, CENSUS_MEMO_VERSION, key, &census.value());
}

/// Whether every source file of the admitted load still has, in the manifest's directory
/// `directory`, the SHA-256 the load recorded: the condition under which the files resolution
/// would read are the ones the specification digest names. Read before any resolution record.
pub fn sources_unchanged(directory: &Path, loaded: &LoadedSource) -> bool {
    loaded.files.iter().all(|file| {
        fs::read(directory.join(&file.name)).is_ok_and(|bytes| sha256(&bytes) == file.sha256)
    })
}
