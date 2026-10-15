//! The outcome cache, tier 1 (flow README 7.5.3): the proved outcome of one mutation on one
//! program, kept across commands under a key that names every input it depends on.
//!
//! The trust premise (README 7.5.1, approved by Sebastien on 2026-10-15): with identical
//! inputs, a cached proved Distinguish stands without being re-run in this command. It rests on
//! k-rust's compile and execution determinism (KINK-06), on the key naming every input of the
//! outcome, and on the integrity of the cache directory. `kink-flow run --verify` re-proves
//! every cached outcome and reports a disagreement as an error.
//!
//! Only outcomes computed from complete evidence are cached: a compared test with some
//! `distinguish` slot (outcome `killed`) or with every slot `agree` (outcome `agree`). A
//! timeout, unknown, error or incomparable slot, a failed or skipped test, and every test of a
//! call that ended in a corpus error or whose plan carries a mutant-scope failure are never
//! written (decisions D14-2 and D14-3).
//!
//! `<cache>/outcomes/<context digest>/<mutation identity>.json` holds one mutation's records:
//! `{schema: "kink-flow-outcomes", version: 1, context, context_sha256, mutation_identity,
//! mutation_id, records: {<program digest>: {program_id, baseline_run_sha256, outcome, slots,
//! mutant_run_sha256, record_sha256}}}`. [`OutcomeStore::read`] returns only the records that
//! pass every check that needs no corpus (schema, version, context, record digest, outcome
//! consistent with its slots); the kill search then requires the program to be a current
//! comparable candidate whose result record has the record's `baseline_run_sha256`. Anything
//! else is ignored, never trusted, and deleting `outcomes/` is always safe.

use crate::{digest::context_sha256, results::ORACLE_SLOTS};
use kink_campaign::{OracleOutcome, TestRun};
use kink_corpus::{Store, StoreError};
use kink_patch::{Sha256Digest, canonical_json, payload_digest};
use serde_json::{Map, Value, json};
use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
};

/// The `schema` field of an outcome file.
pub const OUTCOMES_SCHEMA: &str = "kink-flow-outcomes";
/// The outcome file's version.
pub const OUTCOMES_VERSION: u64 = 1;
/// Domain of a record's integrity digest.
pub const RECORD_DOMAIN: &str = "kink-flow/outcome-record/v1";
/// The tier-1 directory's name in the cache directory.
pub const OUTCOMES_DIRECTORY: &str = "outcomes";

/// A cacheable outcome of one mutant on one program.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CachedOutcome {
    /// Some oracle slot proved a difference: the program kills the mutant.
    Killed,
    /// Every oracle slot agreed on complete evidence.
    Agree,
}

impl CachedOutcome {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Killed => "killed",
            Self::Agree => "agree",
        }
    }

    fn parse(text: &str) -> Option<Self> {
        match text {
            "killed" => Some(Self::Killed),
            "agree" => Some(Self::Agree),
            _ => None,
        }
    }

    /// The outcome compared slots give, when it is cacheable: `killed` iff some slot is
    /// `distinguish`, `agree` iff every slot is `agree`; `None` otherwise (or with no slot).
    pub fn of_slots(slots: &[OracleOutcome]) -> Option<Self> {
        if slots.contains(&OracleOutcome::Distinguish) {
            Some(Self::Killed)
        } else if !slots.is_empty() && slots.iter().all(|slot| *slot == OracleOutcome::Agree) {
            Some(Self::Agree)
        } else {
            None
        }
    }
}

/// The cacheable outcome of one test's mutant run and its slots, or `None`: only a compared
/// test whose slots give `killed` or `agree` is cacheable.
pub fn cacheable(run: &TestRun) -> Option<(CachedOutcome, &[OracleOutcome])> {
    match run {
        TestRun::Compared(slots) => CachedOutcome::of_slots(slots).map(|o| (o, slots.as_slice())),
        TestRun::Failed(_) | TestRun::SkippedAfterKill => None,
    }
}

/// An oracle slot outcome as the run document and the outcome records name it.
pub const fn slot_name(outcome: OracleOutcome) -> &'static str {
    match outcome {
        OracleOutcome::Agree => "agree",
        OracleOutcome::Distinguish => "distinguish",
        OracleOutcome::Incomparable => "incomparable",
        OracleOutcome::Timeout => "timeout",
        OracleOutcome::Unknown => "unknown",
        OracleOutcome::Error => "error",
    }
}

fn parse_slot(text: &str) -> Option<OracleOutcome> {
    [
        OracleOutcome::Agree,
        OracleOutcome::Distinguish,
        OracleOutcome::Incomparable,
        OracleOutcome::Timeout,
        OracleOutcome::Unknown,
        OracleOutcome::Error,
    ]
    .into_iter()
    .find(|outcome| slot_name(*outcome) == text)
}

/// One cached outcome of a mutation on a program.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OutcomeRecord {
    /// The program's id when the record was written (informational).
    pub program_id: String,
    /// The run digest of the baseline evidence the outcome was compared with: the program's
    /// result record's `run_sha256` at the time.
    pub baseline_run_sha256: String,
    pub outcome: CachedOutcome,
    /// The slot outcomes, one per oracle slot (results::ORACLE_SLOTS).
    pub slots: Vec<OracleOutcome>,
    /// The run digest of the mutant's evidence row for the program (results::run_digest of
    /// `CampaignReport::baseline_row` of the mutant's `TestEvidence`).
    pub mutant_run_sha256: String,
}

impl OutcomeRecord {
    /// The record's slot outcomes as a compared test run.
    pub fn test_run(&self) -> TestRun {
        TestRun::Compared(self.slots.clone())
    }

    fn slot_names(&self) -> Vec<&'static str> {
        self.slots.iter().map(|slot| slot_name(*slot)).collect()
    }

    /// The record's integrity digest under its context, mutation and program.
    pub fn digest(
        &self,
        context_sha256: &str,
        mutation_identity: &str,
        program_digest: &str,
    ) -> Sha256Digest {
        record_sha256(
            context_sha256,
            mutation_identity,
            program_digest,
            &self.baseline_run_sha256,
            self.outcome.as_str(),
            &self.slot_names(),
            &self.mutant_run_sha256,
        )
    }

    fn value(&self, context_sha256: &str, mutation_identity: &str, program_digest: &str) -> Value {
        json!({
            "program_id": self.program_id,
            "baseline_run_sha256": self.baseline_run_sha256,
            "outcome": self.outcome.as_str(),
            "slots": self.slot_names(),
            "mutant_run_sha256": self.mutant_run_sha256,
            "record_sha256": self
                .digest(context_sha256, mutation_identity, program_digest)
                .to_string(),
        })
    }
}

/// `record_sha256 = payload_digest("kink-flow/outcome-record/v1", canonical JSON of
/// {context_sha256, mutation_identity, program_digest, baseline_run_sha256, outcome, slots,
/// mutant_run_sha256})`. It detects corruption and a record moved under another key, not
/// forgery (README 7.5.1).
pub fn record_sha256(
    context_sha256: &str,
    mutation_identity: &str,
    program_digest: &str,
    baseline_run_sha256: &str,
    outcome: &str,
    slots: &[&str],
    mutant_run_sha256: &str,
) -> Sha256Digest {
    payload_digest(
        RECORD_DOMAIN,
        canonical_json(&json!({
            "context_sha256": context_sha256,
            "mutation_identity": mutation_identity,
            "program_digest": program_digest,
            "baseline_run_sha256": baseline_run_sha256,
            "outcome": outcome,
            "slots": slots,
            "mutant_run_sha256": mutant_run_sha256,
        }))
        .as_bytes(),
    )
}

/// The tier-1 store of one command: its context and the directory the context's digest names.
#[derive(Clone, Debug)]
pub struct OutcomeStore {
    directory: PathBuf,
    context: Value,
    context_sha256: String,
}

impl OutcomeStore {
    /// The store of `context` (digest::outcome_context) under the cache directory `cache`.
    pub fn new(cache: &Path, context: Value) -> Self {
        let context_sha256 = context_sha256(&context).to_string();
        Self {
            directory: cache.join(OUTCOMES_DIRECTORY).join(&context_sha256),
            context,
            context_sha256,
        }
    }

    pub fn context(&self) -> &Value {
        &self.context
    }

    pub fn context_sha256(&self) -> &str {
        &self.context_sha256
    }

    /// The outcome file of the mutation with `identity`.
    pub fn path(&self, identity: Sha256Digest) -> PathBuf {
        self.directory.join(format!("{identity}.json"))
    }

    /// The records of the mutation's file, by program digest, that pass every check needing
    /// no corpus: the file's schema, version, context and identity are the current ones, the
    /// record's digest recomputes, and its outcome agrees with its slots. A missing or
    /// unreadable file has none.
    pub fn read(&self, identity: Sha256Digest) -> BTreeMap<String, OutcomeRecord> {
        self.file(identity)
            .map(|records| {
                records
                    .iter()
                    .filter_map(|(program, value)| {
                        Some((program.clone(), self.record(identity, program, value)?))
                    })
                    .collect()
            })
            .unwrap_or_default()
    }

    /// The `records` object of the mutation's file when the file's own fields are current.
    fn file(&self, identity: Sha256Digest) -> Option<Map<String, Value>> {
        let text = fs::read_to_string(self.path(identity)).ok()?;
        let value = serde_json::from_str::<Value>(&text).ok()?;
        let current = value["schema"] == OUTCOMES_SCHEMA
            && value["version"] == OUTCOMES_VERSION
            && value["context"] == self.context
            && value["context_sha256"] == self.context_sha256.as_str()
            && value["mutation_identity"] == identity.to_string();
        if !current {
            return None;
        }
        value.get("records")?.as_object().cloned()
    }

    /// One stored record, if it passes the integrity checks.
    fn record(
        &self,
        identity: Sha256Digest,
        program: &str,
        value: &Value,
    ) -> Option<OutcomeRecord> {
        let field = |key: &str| value.get(key)?.as_str().map(str::to_owned);
        Sha256Digest::parse(program)?;
        let slots = value
            .get("slots")?
            .as_array()?
            .iter()
            .map(|slot| parse_slot(slot.as_str()?))
            .collect::<Option<Vec<_>>>()?;
        if slots.len() != ORACLE_SLOTS.len() {
            return None;
        }
        let outcome = CachedOutcome::parse(&field("outcome")?)?;
        if CachedOutcome::of_slots(&slots) != Some(outcome) {
            return None;
        }
        let record = OutcomeRecord {
            program_id: field("program_id")?,
            baseline_run_sha256: field("baseline_run_sha256")?,
            outcome,
            slots,
            mutant_run_sha256: field("mutant_run_sha256")?,
        };
        let digest = record.digest(&self.context_sha256, &identity.to_string(), program);
        (field("record_sha256")? == digest.to_string()).then_some(record)
    }

    /// Add `records` (by program digest) to the mutation's file: read, keep the stored records
    /// that pass the integrity checks (records of programs absent from the corpus are kept),
    /// replace or add the new ones (the last of several with one program digest), and write
    /// the file atomically (kink-corpus `Store`). Returns the number of records written: the
    /// number of distinct programs in `records` (flow F-16).
    pub fn write(
        &self,
        store: &Store,
        identity: Sha256Digest,
        mutation_id: &str,
        records: &[(String, OutcomeRecord)],
    ) -> Result<usize, StoreError> {
        let mut all = self.read(identity);
        for (program, record) in records {
            all.insert(program.clone(), record.clone());
        }
        let identity_text = identity.to_string();
        let values = all
            .iter()
            .map(|(program, record)| {
                (
                    program.clone(),
                    record.value(&self.context_sha256, &identity_text, program),
                )
            })
            .collect::<Map<_, _>>();
        let written = records
            .iter()
            .map(|(program, _)| program)
            .collect::<std::collections::BTreeSet<_>>()
            .len();
        store.write_json(
            &self.path(identity),
            &json!({
                "schema": OUTCOMES_SCHEMA,
                "version": OUTCOMES_VERSION,
                "context": self.context,
                "context_sha256": self.context_sha256,
                "mutation_identity": identity_text,
                "mutation_id": mutation_id,
                "records": values,
            }),
        )?;
        Ok(written)
    }
}
