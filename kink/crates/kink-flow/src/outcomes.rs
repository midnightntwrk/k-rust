//! The outcome cache, tier 1 (flow README 7.5.3): the proved outcome of one mutation on one
//! program, kept across commands under a key that names every input it depends on.
//!
//! The trust premise (README 7.5.1, approved by Sebastien on 2026-10-15): with identical
//! inputs, a cached proved Distinguish stands without being re-run in this command. It rests on
//! k-rust's compile and execution determinism (KINK-06), on the key naming every input of the
//! outcome, and on the integrity of the cache directory. Identical inputs are an identical loaded
//! definition up to positions (the context's execution digest, `digest::execution_digest`, whose
//! doc states the premises that reading rests on), not identical bytes. `kink-flow run --verify`
//! re-proves every cached outcome and reports a disagreement as an error.
//!
//! An outcome is cached exactly when it is a function of what its key names. A compared test
//! with some `distinguish` slot (outcome `killed`) or with every slot `agree` (outcome `agree`)
//! is, by the Execute promise below. So, since CF-33d, is a compared test whose slots are
//! `agree` or `unknown`, some `unknown` (outcome `unknown`), when the mutant's run was judged.
//!
//! **Unknown outcomes.** An `unknown` slot of a compared test is a mutant side that is no
//! comparable value although the run returned (the watchdog stopped no part of it: a run it
//! stopped is `Failed(TimeLimit)`, and a path it stopped makes its side `timeout`, not
//! `unknown`). Its causes, each read from the run's leaves and from kink's judgement of them:
//! - a path stopped by a bound of the request: the work budget (`[budget] work_factor`: at most
//!   `factor * W + floor` states, `W` the states the program's baseline run visited, itself a
//!   function of the baseline's request, which the context and the program digest name),
//!   `max_depth`, `max_simplification_iterations` or `max_breadth`. Each counts work, not time,
//!   so it stops the same request at the same place on every host; each is in the context's
//!   `budget` (the work budget as `budget.work: {factor, floor}`);
//! - a leaf k-rust left indeterminate or vacuous, or a state kink's feasibility check did not
//!   decide: without Z3 no solver is asked; under the Z3 profile every query, k-rust's and
//!   kink's own (leaf feasibility, the observation decider, the pair's judgement), is bounded by
//!   Z3 resource units, and its answer, decided or not, is a function of the query, the units
//!   and the Z3 build (k-rust's `docs/compatibility.md`, "Execute", clock-free solver mode),
//!   which the context's `budget.smt` names; a clock-bounded solver turns tier 1 off;
//! - an end that is no value kink compares (a symbolic term, a collection kink cannot compare,
//!   a mix of crashes), or that is not data under the other side's definition (kink-campaign
//!   `judge_across`): a function of the ends and of the two definitions;
//! - the one-sided rule (re-pin L1-2): a work-bound run kills when one of its stuck ground
//!   terminals is outside the baseline's set, and stays `unknown` otherwise, a function of the
//!   run and of the rule's version (`kink.one_sided` in the context);
//! - the baseline's side: a baseline end the pair's judgement finds not data under the mutant's
//!   definition (`judge_across`), or a pattern slot whose baseline side is no value (kink-flow's
//!   slots are state slots, so not here): functions of the baseline run, which the record's
//!   `baseline_run_sha256` names, and of the two definitions.
//!
//! The run's stop (`[stop]`, the context's `stop`), the projection (`oracles`, `not_compared`),
//! the build (`kink_build`, `kink`, `profile`) and the definition (`execution_digest`) are in
//! the context too. What is not a fact of the run is excluded: a judgement of the run the backend
//! refused (kink-campaign `RunNotes::unjudged`: a refused stack segment, solver initialization or
//! prelude makes its slots `unknown`, possibly for the host's reason; and a definition whose
//! full check ran out of native stack admits no end as data, for a reason of the thread), so such
//! an outcome is not written. Every other inconclusive outcome is not written either: a `timeout` slot (the
//! watchdog's clock), an `error` slot (an untrustworthy backend result, which can come from the
//! host), an `incomparable` slot (whose status is `error`), every failed test (a run the watchdog
//! stopped, an infrastructure failure, the host exclusions: stack stop, load stack stop,
//! allowance refusal; and the exclusions of the definition or the run, which are facts of the
//! key but whose row's `reason` and diagnostics a live call gives; and `Indeterminate` and
//! `ResourceLimit`, which would be facts of the key too, but which the runner does not produce
//! and which stay uncached, conservatively), a skipped test, and every
//! test of a call that ended in a corpus error or whose plan carries a mutant-scope failure
//! (decisions D14-2 and D14-3).
//!
//! An `unknown` record keeps the live executed entry's `cause` (and every record the run's
//! undecided-answer counts), so a cached unknown reports why, as the live one does, and whether
//! that cause is an open application of an edited function (`open_application`), so that a row's
//! `reason` is the same whether its unknowns were read live or from the cache.
//!
//! The Execute promise (k-rust `docs/compatibility.md`, "Execute"; re-pin finding B-02) is what
//! makes a cached outcome a function of its key, and it excludes runs: a token cancelled before
//! return, a step timeout, a nonzero `stackStops`, a Bytes allowance refusal, a load stack stop,
//! and in Z3 builds any run in which a query can time out. Each of them is excluded for the whole
//! test, both sides and every slot, before anything here sees it: a cancelled run is a timeout;
//! kink sets no step timeout; a stack stop, a load stack stop or an allowance refusal on either
//! side makes that side's run `failed` (kink-native `exclusion`), so the test is not compared, and
//! on the baseline the program is not comparable; and under the Z3 profile every query of kink's
//! backends is bounded by Z3 resource units, never by the clock (`[budget] smt_resource_limit`),
//! so none times out: an undecided answer is a function of the query, the units and the Z3 build,
//! which the context names, and the promise covers such a run. kink's own queries outside a run
//! (leaf feasibility, the observation decider) are bounded the same way, so an outcome they
//! decide is a function of the context too; with a solver the clock bounds, or a Z3 build that
//! cannot be named, tier 1 is off (`search::tier1_refusal`).
//!
//! `<cache>/outcomes/<context digest>/<mutation identity>.json` holds one mutation's records:
//! `{schema: "kink-flow-outcomes", version: 6, context, context_sha256, mutation_identity,
//! mutation_id, removed_claims, witness, records: {<program digest>: {program_id,
//! baseline_run_sha256, outcome, slots, mutant_run_sha256, difference, cause, open_application,
//! smt_unknowns, decider_smt_unknowns, allowance_bytes, observation?, record_sha256}}}`.
//!
//! `removed_claims` is the row's (`report::claims_value`):
//! the claims the mutant every record ran on does not carry (re-pin R0c-fix-2).
//! It is informational, a function of the specification, the mutation
//! and the `claim_removal` version of the context's kink identity,
//! and is neither read back nor in a record digest.
//!
//! `witness` (version 3) is the mutant's compiled edit as a ground program witnesses it, read
//! through the baseline's rule authors (`search::EditWitness`: `{reading, global, matched,
//! applied}`, the baseline sentences whose coverage witnesses the edit by k-rust `matched` and by
//! `applied`), from the live call that wrote the records, or null. `reading` is
//! `ground-programs`: the edit is the claim-free mutant's, or the mutant as written's when only
//! definedness claims were withdrawn from it (kink-campaign `CompiledEdit::for_ground_tests`).
//! A file written before `reading` was read from the claim-free side alone; its `witness` is read
//! when the row's `removed_claims` names no withdrawn claim or one that is not a definedness
//! claim, where it is the same edit, and is otherwise not read.
//! It is a function of the key: the mutant as written and the claim-free mutant are compiled
//! from the mutation's patch under the context's kink identity, and the baseline's rule authors
//! from the definition the execution digest names, so it rests on the compile determinism every
//! record rests on.
//! A row tier 1 decides with no compile reads it for its `witnesses` and for which of several
//! cached killers it names; it decides no status and orders no call (a live call orders its
//! programs by its own compiled edit), so it is outside every record digest, and a file whose
//! `witness` does not decode gives no `witnesses` and names the first cached killer in O.
//! `run --verify` compares it with the cold call's compiled edit and reports a difference in the
//! run document's `mismatches`.
//!
//! `allowance_bytes` is k-rust's `Allowance::of_process().bytes()`
//! of the process that wrote the record, for diagnosis only:
//! it is neither in the key nor in the record digest (re-pin decision 5, finding B-07):
//! an allowance only refuses Bytes results,
//! a refused run is excluded, and no excluded run is cached.
//!
//! `difference` (CF-16, version 2) is a `killed` record's kill evidence ([`crate::evidence`]):
//! the first differing cell path of the killing test's ends and both values as K text, bounded;
//! null on an `agree` record.
//! It is outside the key, which it is a function of (the key names every input of both runs),
//! and inside the record digest,
//! so a record whose evidence was altered is ignored like any other altered record.
//! Nothing reads it but the report, so it decides no verdict.
//! A version 1 file (no `difference`) is not current and is ignored,
//! so its records are recomputed, never read as records without evidence.
//! Since version 4 the evidence names its format (`format`: kink's own `kink-k/1`, or a front
//! end's, which the context names as `evidence`; [`crate::evidence`], "The format of the
//! evidence"); a file of an earlier version is not current, so its records are recomputed with
//! evidence that names its format.
//!
//! `cause` (version 5) is an `unknown` record's cause (null on any other), and `smt_unknowns` and
//! `decider_smt_unknowns` the run's undecided solver answers: outside the key, of which they are
//! functions, and inside the record digest (domain v3).
//!
//! `open_application` (version 6) is whether an `unknown` record's program is undecided because
//! the ends of the mutant's run hold open applications of a function the mutation edits
//! (`report::open_application_cause`; false on any other record): a function of the run, so of
//! the key, outside the key and inside the record digest (domain v4). A row folds its `reason`
//! `open-application` from it for a cached unknown as from the census for a live one; a version 5
//! record, which does not keep it, is not current and is recomputed.
//!
//! `observation` is, under `[observe]` (whose declaration the context names), what the
//! observation slot reported beside its outcome: `{position: {channel, index, at_end}}` on a
//! record whose slot distinguished, `{horizon: {<channel>: n}}` on one whose slot agreed up to the
//! baseline's horizons, `{cause}` on one whose slot was unknown. It is absent from a record whose
//! context has no `observe`, and inside the record digest as a member of `report` only where
//! present, so every record without it has the bytes and digest it had: no version moves, since
//! no stored file has a context that names `observe`. A record under such a context has one slot
//! more, the observation slot, after the end slots.
//!
//! [`OutcomeStore::read`] returns only the records that pass every check that needs no corpus
//! (schema, version, context, record digest, outcome consistent with its slots, a cause exactly
//! on an `unknown` record, `open_application` true only on one);
//! the kill search then requires the program to be a current comparable candidate
//! whose result record has the record's `baseline_run_sha256`.
//! Anything else is ignored, never trusted, and deleting `outcomes/` is always safe.

use crate::{digest::context_sha256, results::ORACLE_SLOTS};
use kink_campaign::{OracleOutcome, RunNotes, TestRun};
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
/// The outcome file's version: 2 since CF-16 added each record's `difference`; 3 since the file
/// keeps the mutant's compiled edit (`witness`, module doc); 4 since each record's `difference`
/// names its format, and is a front end's evidence where the context names one (`evidence`); 5
/// since a record's outcome can be `unknown` (CF-33d) and every record carries `cause`,
/// `smt_unknowns` and `decider_smt_unknowns`; 6 since an `unknown` record keeps whether its cause
/// is an open application of an edited function (`open_application`).
pub const OUTCOMES_VERSION: u64 = 6;
/// Domain of a record's integrity digest: v2 since CF-16 added `difference` to the digest; v3
/// since CF-33d added the record's report (`cause`, `smt_unknowns`, `decider_smt_unknowns`); v4
/// since the report holds `open_application`.
pub const RECORD_DOMAIN: &str = "kink-flow/outcome-record/v4";
/// The tier-1 directory's name in the cache directory.
pub const OUTCOMES_DIRECTORY: &str = "outcomes";

/// A cacheable outcome of one mutant on one program.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CachedOutcome {
    /// Some oracle slot proved a difference: the program kills the mutant.
    Killed,
    /// Every oracle slot agreed on complete evidence.
    Agree,
    /// No slot distinguished, some slot is `unknown` and every other agreed, on evidence that is
    /// a function of the context (module doc, "Unknown outcomes"; CF-33d).
    Unknown,
}

impl CachedOutcome {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Killed => "killed",
            Self::Agree => "agree",
            Self::Unknown => "unknown",
        }
    }

    fn parse(text: &str) -> Option<Self> {
        match text {
            "killed" => Some(Self::Killed),
            "agree" => Some(Self::Agree),
            "unknown" => Some(Self::Unknown),
            _ => None,
        }
    }

    /// The outcome compared slots give, when they can be cached: `killed` iff some slot is
    /// `distinguish`, `agree` iff every slot is `agree`, `unknown` iff every slot is `agree` or
    /// `unknown` and some is `unknown`; `None` otherwise (a `timeout`, `error` or `incomparable`
    /// slot, or no slot). Whether an `unknown` is cached also depends on the run's notes
    /// ([`cacheable`]).
    pub fn of_slots(slots: &[OracleOutcome]) -> Option<Self> {
        if slots.contains(&OracleOutcome::Distinguish) {
            Some(Self::Killed)
        } else if slots.is_empty() {
            None
        } else if slots.iter().all(|slot| *slot == OracleOutcome::Agree) {
            Some(Self::Agree)
        } else if slots
            .iter()
            .all(|slot| matches!(slot, OracleOutcome::Agree | OracleOutcome::Unknown))
        {
            Some(Self::Unknown)
        } else {
            None
        }
    }
}

/// The cacheable outcome of one test's mutant run and its slots, or `None` (module doc): a
/// compared test whose slots give `killed` or `agree`, or `unknown` when the mutant's evidence
/// `notes` say the run was judged (`RunNotes::unjudged` false: no judgement of it was refused by
/// the backend, which can be the host's doing) and carry nothing an excluded run carries (no
/// contradicted claim, no counting short-circuit reading: such a run is excluded, never compared,
/// so this is defensive). A failed or skipped test is never cacheable.
pub fn cacheable<'r>(
    run: &'r TestRun,
    notes: Option<&RunNotes>,
) -> Option<(CachedOutcome, &'r [OracleOutcome])> {
    let TestRun::Compared(slots) = run else {
        return None;
    };
    let outcome = CachedOutcome::of_slots(slots)?;
    let judged = |notes: &RunNotes| {
        !notes.unjudged
            && notes.contradicted_claims.is_empty()
            && notes.short_circuit_readings.is_empty()
    };
    (outcome != CachedOutcome::Unknown || notes.is_some_and(judged))
        .then_some((outcome, slots.as_slice()))
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
    /// The kill evidence of a `killed` record ([`crate::evidence`], `EndReader::difference`);
    /// null on an `agree` record, and on a `killed` one whose sides held no whole-term value.
    /// Outside the key, inside the record digest; read only by the report.
    pub difference: Value,
    /// An `unknown` record's cause, the live executed entry's (`report::executed_cause`): why the
    /// mutant's run gave no comparable value, so that a cached unknown says why as a live one
    /// does; `None` on a `killed` or `agree` record. Outside the key (a function of it), inside
    /// the record digest; read only by the report.
    pub cause: Option<String>,
    /// Whether an `unknown` record's program is undecided because the ends of the mutant's run
    /// hold open applications of a function the mutation edits (`report::open_application_cause`),
    /// the fact a row's `open-application` reason is folded from; false on a `killed` or `agree`
    /// record. Outside the key (a function of it), inside the record digest.
    pub open_application: bool,
    /// The undecided solver answers of the mutant's run, k-rust's (`smt_unknowns`) and kink's
    /// own about it (`decider_smt_unknowns`), as the live executed entry reports them (decision
    /// D-7 (a1)). Outside the key, inside the record digest; read only by the report.
    pub smt_unknowns: u64,
    pub decider_smt_unknowns: u64,
    /// The writing process's memory allowance in bytes (k-rust `Allowance::of_process`), for
    /// diagnosis only: outside the key and the record digest; `None` in a record without it.
    pub allowance_bytes: Option<u64>,
    /// Under `[observe]`, what the observation slot reported beside its outcome
    /// ([`crate::report::observation_slot`]): `{position}` where it distinguished, `{horizon}`
    /// where it agreed up to the baseline's horizons, `{cause}` where it was unknown; null
    /// without `[observe]`. Outside the key (a function of it), inside the record digest, where
    /// it is a member of the report only when not null, so a record without it has the digest it
    /// had; read only by the report.
    pub observation: Value,
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
            &self.difference,
            &self.report(),
        )
    }

    /// The record's report, as its digest holds it: `{cause, open_application, smt_unknowns,
    /// decider_smt_unknowns}`.
    pub fn report(&self) -> Value {
        let mut report = Self::report_of(
            self.cause.as_ref(),
            self.open_application,
            self.smt_unknowns,
            self.decider_smt_unknowns,
        );
        if !self.observation.is_null() {
            report["observation"] = self.observation.clone();
        }
        report
    }

    /// A report of these fields ([`Self::report`]).
    pub fn report_of(
        cause: Option<&String>,
        open_application: bool,
        smt_unknowns: u64,
        decider_smt_unknowns: u64,
    ) -> Value {
        json!({
            "cause": cause,
            "open_application": open_application,
            "smt_unknowns": smt_unknowns,
            "decider_smt_unknowns": decider_smt_unknowns,
        })
    }

    /// The report of a record with no cause and no undecided answer.
    pub fn no_report() -> Value {
        Self::report_of(None, false, 0, 0)
    }

    /// The report of a stored record's JSON value, for its digest (a test that reseals a record
    /// it edited reads it back this way).
    pub fn report_value(record: &Value) -> Value {
        let mut report = json!({
            "cause": record["cause"],
            "open_application": record["open_application"],
            "smt_unknowns": record["smt_unknowns"],
            "decider_smt_unknowns": record["decider_smt_unknowns"],
        });
        if let Some(observation) = record.get("observation").filter(|value| !value.is_null()) {
            report["observation"] = observation.clone();
        }
        report
    }

    fn value(&self, context_sha256: &str, mutation_identity: &str, program_digest: &str) -> Value {
        let mut value = json!({
            "program_id": self.program_id,
            "baseline_run_sha256": self.baseline_run_sha256,
            "outcome": self.outcome.as_str(),
            "slots": self.slot_names(),
            "mutant_run_sha256": self.mutant_run_sha256,
            "difference": self.difference,
            "cause": self.cause,
            "open_application": self.open_application,
            "smt_unknowns": self.smt_unknowns,
            "decider_smt_unknowns": self.decider_smt_unknowns,
            "allowance_bytes": self.allowance_bytes,
            "record_sha256": self
                .digest(context_sha256, mutation_identity, program_digest)
                .to_string(),
        });
        if !self.observation.is_null() {
            value["observation"] = self.observation.clone();
        }
        value
    }
}

/// `record_sha256 = payload_digest("kink-flow/outcome-record/v4", canonical JSON of
/// {context_sha256, mutation_identity, program_digest, baseline_run_sha256, outcome, slots,
/// mutant_run_sha256, difference, report})`, where `report` is `{cause, open_application,
/// smt_unknowns, decider_smt_unknowns}`. It detects corruption and a record moved under another key, not
/// forgery (README 7.5.1).
#[allow(clippy::too_many_arguments)]
pub fn record_sha256(
    context_sha256: &str,
    mutation_identity: &str,
    program_digest: &str,
    baseline_run_sha256: &str,
    outcome: &str,
    slots: &[&str],
    mutant_run_sha256: &str,
    difference: &Value,
    report: &Value,
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
            "difference": difference,
            "report": report,
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
        self.read_with_witness(identity).0
    }

    /// [`Self::read`]'s records and the file's `witness` (module doc), null when the file is
    /// missing, not current or has none.
    pub fn read_with_witness(
        &self,
        identity: Sha256Digest,
    ) -> (BTreeMap<String, OutcomeRecord>, Value) {
        let Some(mut file) = self.file(identity) else {
            return (BTreeMap::new(), Value::Null);
        };
        let records = file
            .get("records")
            .and_then(Value::as_object)
            .into_iter()
            .flatten()
            .filter_map(|(program, value)| {
                Some((program.clone(), self.record(identity, program, value)?))
            })
            .collect();
        (records, file.remove("witness").unwrap_or(Value::Null))
    }

    /// The mutation's file when its own fields are current.
    fn file(&self, identity: Sha256Digest) -> Option<Map<String, Value>> {
        let text = fs::read_to_string(self.path(identity)).ok()?;
        let value = kink_patch::parse_json(&text).ok()?;
        let current = value["schema"] == OUTCOMES_SCHEMA
            && value["version"] == OUTCOMES_VERSION
            && value["context"] == self.context
            && value["context_sha256"] == self.context_sha256.as_str()
            && value["mutation_identity"] == identity.to_string();
        if !current {
            return None;
        }
        match value {
            Value::Object(file) => Some(file),
            _ => None,
        }
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
        // Under `[observe]` (the context names it) the observation slot follows the end slots.
        let observed = self.context.get("observe").is_some();
        if slots.len() != ORACLE_SLOTS.len() + usize::from(observed) {
            return None;
        }
        let outcome = CachedOutcome::parse(&field("outcome")?)?;
        if CachedOutcome::of_slots(&slots) != Some(outcome) {
            return None;
        }
        // An `unknown` record says why; no other record has a cause.
        let cause = match value.get("cause")? {
            Value::String(cause) if outcome == CachedOutcome::Unknown => Some(cause.clone()),
            Value::Null if outcome != CachedOutcome::Unknown => None,
            _ => return None,
        };
        // Only an `unknown` record can be undecided by an open application.
        let open_application = value.get("open_application")?.as_bool()?;
        if open_application && outcome != CachedOutcome::Unknown {
            return None;
        }
        let record = OutcomeRecord {
            program_id: field("program_id")?,
            baseline_run_sha256: field("baseline_run_sha256")?,
            outcome,
            slots,
            mutant_run_sha256: field("mutant_run_sha256")?,
            difference: value.get("difference")?.clone(),
            cause,
            open_application,
            smt_unknowns: value.get("smt_unknowns")?.as_u64()?,
            decider_smt_unknowns: value.get("decider_smt_unknowns")?.as_u64()?,
            allowance_bytes: value.get("allowance_bytes").and_then(Value::as_u64),
            observation: value.get("observation").cloned().unwrap_or(Value::Null),
        };
        let digest = record.digest(&self.context_sha256, &identity.to_string(), program);
        (field("record_sha256")? == digest.to_string()).then_some(record)
    }

    /// Add `records` (by program digest) to the mutation's file: read, keep the stored records
    /// that pass the integrity checks (records of programs absent from the corpus are kept),
    /// replace or add the new ones (the last of several with one program digest), and write
    /// the file atomically (kink-corpus `Store`). The file's `witness` is `witness` when it is not
    /// null, else the stored one. Returns the number of records written: the number of distinct
    /// programs in `records` (flow F-16).
    pub fn write(
        &self,
        store: &Store,
        identity: Sha256Digest,
        mutation_id: &str,
        removed_claims: &Value,
        witness: &Value,
        records: &[(String, OutcomeRecord)],
    ) -> Result<usize, StoreError> {
        let (mut all, stored_witness) = self.read_with_witness(identity);
        let witness = if witness.is_null() {
            &stored_witness
        } else {
            witness
        };
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
                "removed_claims": removed_claims,
                "witness": witness,
                "records": values,
            }),
        )?;
        Ok(written)
    }
}
