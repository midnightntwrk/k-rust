//! The mutant ends store (PJ-11, gate G1): the ends of each mutant run `run` makes live, kept
//! under the mutant's own key, with no projection in the key or the value, so that a judgement
//! of the same mutant under another projection can read them instead of running the mutant again.
//!
//! Nothing in `run` reads the store: every status, killer, exit status, lock row and outcome
//! record is decided as without it. It is evidence beside tier 1 ([`crate::outcomes`]), written
//! at the same sites, for a later reader.
//!
//! **What is stored.** For one test of one mutant: the run's ends, as kink-campaign's evidence
//! holds them (`TestEvidence::ends`: the terminals of the run's complete paths that are not
//! undefined steps, each in its own definition's canonical form, before any slot projects it, so
//! with the generated counter and every cell's content as the run left them), as KORE text in the
//! set's order; which of them a path reached at its last stop (`stop_ends`, indices into `ends`);
//! the poll-bound run's one-sided terminals the pair kept (`one_sided_ends`); whether a complete
//! path is an undefined step (`undefined_steps`); whether the ends are the whole set
//! ([`MutantEnds::complete`]); what the pair's cross-definition judgement said of each side's ends
//! ([`Across`]); and the polls of the run ([`RunPolls`]).
//!
//! **When a record is written** ([`MutantEnds::of`]): for a test the call compared, whose slots
//! hold no `timeout`, `error` or `incomparable` outcome and whose mutant sides hold no `timeout` or
//! `error` side (under `[observe]` a prefix program's end slots agree whatever the mutant's sides
//! are, so the slots alone do not show a path the watchdog stopped), whose run was judged (no
//! judgement of it refused by the backend, `RunNotes::unjudged`; no contradicted claim; no counting
//! short-circuit reading) and that counted its polls under a bound. So a run the watchdog stopped
//! stores nothing (it is the host's clock), nor does a failed run (an exclusion, a stack stop, an
//! allowance refusal, infrastructure, an undecided stop condition), which has no ends. A run whose
//! ends are not its whole ground set is stored with `complete` false: a path a deterministic bound
//! cut (the poll bound, which also sets `polls.cut`, or `max_depth`, `max_breadth`), a leaf left
//! undecided, or an end with a variable; its `ends` are those of its complete paths only. A record
//! is written only for a program whose tier-1 outcome record the same call writes (its outcome is
//! cacheable, [`crate::outcomes::cacheable`]); an outcome record need not have an ends record.
//! No record is written for a call whose plan carries a mutant-scope failure, after a corpus
//! error, under `run --verify`, or where tier 1 is off (`search::tier1_store`).
//!
//! **The key.** `<cache>/mutant-ends/<context digest>/<mutation identity>/<program digest>.json`.
//! The context ([`crate::digest::mutant_ends_context`]) is tier 1's with every member that names a
//! projection removed (`oracles`, `not_compared`, `evidence`) and an execution digest without
//! `[result] cells` ([`crate::digest::ends_execution_digest`]): it names kink's build and semantics
//! identity, the solver profile, the loaded definition up to positions (its `unobservable`
//! declarations included), the bounds and, under the Z3 profile, the solver and its build, the
//! classifier, and the stop and observation declarations, both of which are part of every run's
//! request. The mutation identity names one patch against the baseline, so, with the context's
//! claim-removal and compiled-reading versions, one compiled claim-free mutant (compile
//! determinism, the premise tier 1 rests on); it is used rather than the compiled mutant's digest
//! because that digest exists only after the mutant compiles, and a reader should not have to
//! compile it. The baseline's run digest is not in the key: it digests the baseline's projected
//! sides, and every input the mutant's run and the pair's judgement take from the baseline is a
//! function of the context and the program digest, except the bound of polls, which the record
//! names ([`RunPolls::serves`]).
//!
//! **Reading.** [`MutantEndStore::read`] returns a record only when its schema, version, context
//! digest, mutation identity and program digest are the current ones and its `record_sha256`
//! recomputes; a reader must also check that the record serves the request's bound of polls
//! ([`RunPolls::serves`]) and that the program is a comparable program of the current results.
//! Anything else is ignored, never trusted, and deleting `mutant-ends/` is always safe.

use crate::outcomes::RunPolls;
use k_rust::kore::{ast::Pattern, parser::parse_pattern};
use kink_campaign::{
    CrossCause, CrossEnd, OracleOutcome, OracleSide, RunNotes, SideRun, TestEvidence, TestRun,
};
use kink_corpus::{Store, StoreError};
use kink_patch::{Sha256Digest, canonical_json, payload_digest};
use serde_json::{Value, json};
use std::{
    fs,
    path::{Path, PathBuf},
};

/// The `schema` field of a mutant ends record.
pub const MUTANT_ENDS_SCHEMA: &str = "kink-flow-mutant-ends";
/// The format and meaning of a mutant ends record: the `version` of every record and the
/// `ends_schema` of every context, so a change moves the directory too.
pub const MUTANT_ENDS_VERSION: &str = "kink-flow/mutant-ends/v1";
/// Domain of a mutant ends record's integrity digest.
pub const MUTANT_ENDS_DOMAIN: &str = "kink-flow/mutant-ends-record/v1";
/// The store's directory in the cache directory.
pub const MUTANT_ENDS_DIRECTORY: &str = "mutant-ends";

/// Why one side's ends are not data under the other side's definition, as the pair's judgement
/// found it (kink-campaign `CrossCause`).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NotData {
    /// The side's state value has no ends to judge.
    NoEnds,
    /// The other definition admits no end as data.
    NoData,
    /// An end is not its own terminal value under the other definition.
    NotData,
}

impl NotData {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::NoEnds => "no-ends",
            Self::NoData => "no-data",
            Self::NotData => "not-data",
        }
    }

    fn parse(text: &str) -> Option<Self> {
        [Self::NoEnds, Self::NoData, Self::NotData]
            .into_iter()
            .find(|cause| cause.as_str() == text)
    }

    const fn of(cause: &CrossCause) -> Self {
        match cause {
            CrossCause::NoEnds => Self::NoEnds,
            CrossCause::NoData => Self::NoData,
            CrossCause::NotData(_) => Self::NotData,
        }
    }
}

/// What the pair's cross-definition judgement (kink-campaign `judge_across`) said of each side's
/// ends: `None` where they are data under the other side's definition, or where they were not
/// judged (the mutant's, when its ends are not [`MutantEnds::complete`]).
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Across {
    /// The baseline's ends under the mutant's definition.
    pub baseline: Option<NotData>,
    /// The mutant's ends under the baseline's definition.
    pub mutant: Option<NotData>,
}

impl Across {
    /// The terminal refusals of the mutant's evidence of a pair (`RunNotes::across`), by side.
    fn of(notes: &RunNotes) -> Self {
        let side = |baseline_end: bool| {
            notes
                .across
                .iter()
                .find(|refusal| {
                    refusal.end == CrossEnd::Terminal && refusal.baseline_end == baseline_end
                })
                .map(|refusal| NotData::of(&refusal.cause))
        };
        Self {
            baseline: side(true),
            mutant: side(false),
        }
    }

    fn value(self) -> Value {
        json!({
            "baseline": self.baseline.map(NotData::as_str),
            "mutant": self.mutant.map(NotData::as_str),
        })
    }

    fn from_value(value: &Value) -> Option<Self> {
        let side = |key: &str| match value.get(key)? {
            Value::Null => Some(None),
            Value::String(text) => NotData::parse(text).map(Some),
            _ => None,
        };
        Some(Self {
            baseline: side("baseline")?,
            mutant: side("mutant")?,
        })
    }
}

/// The ends of one mutant's run of one program (module documentation).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MutantEnds {
    /// The program's id when the record was written (informational: outside the digest).
    pub program_id: String,
    /// The run's ends (`TestEvidence::ends`) as KORE text, in the set's order.
    pub ends: Vec<String>,
    /// The indices in [`Self::ends`] of the ends some path reached at its last stop
    /// (`TestEvidence::stop_ends`), ascending.
    pub stop_ends: Vec<usize>,
    /// The poll-bound run's one-sided terminals the pair kept (`TestEvidence::one_sided_ends`),
    /// as KORE text, in the set's order; empty for a run the bound did not cut.
    pub one_sided_ends: Vec<String>,
    /// Whether a complete path of the run is an undefined step (`TestEvidence::undefined_steps`),
    /// which is no end: with no ends, the run's every path takes one (or it has no start).
    pub undefined_steps: bool,
    /// Whether [`Self::ends`] are every end of the run, each ground: the runner gave the mutant a
    /// state side with a value (every path complete, the path collection exhausted, no end with a
    /// variable; kink-campaign `state_side`), or the pair refused such a side because its ends are
    /// not data under the baseline's definition ([`Across::mutant`]). kink-flow's slots are state
    /// slots whose having a value does not depend on the cells they project, so this is a fact of
    /// the run. False wherever that does not hold: a path a deterministic bound cut (polls, depth,
    /// breadth), a leaf left undecided, an end with a variable; the ends are then the complete
    /// paths' only. A reader branches on this flag, never on `polls.cut`.
    pub complete: bool,
    pub across: Across,
    /// The polls of the run: which bounds of polls the record serves ([`RunPolls::serves`]).
    pub polls: RunPolls,
}

impl MutantEnds {
    /// The record of a test whose run a live call compared as `run`, from the mutant's evidence
    /// of the pair `evidence`, when one is written (module documentation, "When a record is
    /// written"); `None` otherwise.
    pub fn of(program_id: &str, run: &TestRun, evidence: &TestEvidence) -> Option<Self> {
        let TestRun::Compared(slots) = run else {
            return None;
        };
        if slots.is_empty()
            || slots.iter().any(|slot| {
                matches!(
                    slot,
                    OracleOutcome::Timeout | OracleOutcome::Error | OracleOutcome::Incomparable
                )
            })
        {
            return None;
        }
        Self::of_evidence(program_id, evidence)
    }

    /// The record of a test the mutant ran alone, with no baseline run beside it (kink-campaign
    /// `run_mutant_alone`, PJ-34 `mutant-accepts`), read from its evidence by the rules
    /// [`Self::of`] reads a pair's mutant evidence by; `None` where those rules write none. Its
    /// [`Across::baseline`] is `None`, since there is no baseline end.
    #[must_use]
    pub fn alone(program_id: &str, evidence: &TestEvidence) -> Option<Self> {
        Self::of_evidence(program_id, evidence)
    }

    /// [`Self::of`] once the pair's slots are known to give a record: from the mutant's evidence,
    /// `None` where a side timed out or failed, a judgement was refused, a claim was contradicted,
    /// a short-circuit reading counted or no polls were counted.
    fn of_evidence(program_id: &str, evidence: &TestEvidence) -> Option<Self> {
        let SideRun::Sides { sides } = &evidence.run else {
            return None;
        };
        if sides
            .iter()
            .any(|side| matches!(side, OracleSide::Timeout | OracleSide::Error))
        {
            return None;
        }
        let notes = &evidence.notes;
        if notes.unjudged
            || !notes.contradicted_claims.is_empty()
            || !notes.short_circuit_readings.is_empty()
        {
            return None;
        }
        let polls = RunPolls::of(notes)?;
        let across = Across::of(notes);
        let complete = across.mutant.is_some()
            || sides
                .iter()
                .any(|side| matches!(side, OracleSide::Normal(_) | OracleSide::SemanticCrash(_)));
        let stop_ends = evidence
            .ends
            .iter()
            .enumerate()
            .filter(|(_, end)| evidence.stop_ends.contains(end))
            .map(|(index, _)| index)
            .collect();
        Some(Self {
            program_id: program_id.to_owned(),
            ends: evidence.ends.iter().map(Pattern::to_string).collect(),
            stop_ends,
            one_sided_ends: evidence
                .one_sided_ends
                .iter()
                .map(Pattern::to_string)
                .collect(),
            undefined_steps: evidence.undefined_steps,
            complete,
            across,
            polls,
        })
    }

    /// The ends as patterns, or the first one that does not parse.
    pub fn patterns(&self) -> Result<Vec<Pattern>, String> {
        self.ends
            .iter()
            .map(|text| {
                parse_pattern(text).map_err(|e| format!("a stored mutant end does not parse: {e}"))
            })
            .collect()
    }

    /// The members the record digest holds, in the record's JSON form.
    fn payload(&self) -> Value {
        json!({
            "ends": self.ends,
            "stop_ends": self.stop_ends,
            "one_sided_ends": self.one_sided_ends,
            "undefined_steps": self.undefined_steps,
            "complete": self.complete,
            "across": self.across.value(),
            "polls": self.polls.value(),
        })
    }

    /// Whether `other` records the same run: every member but the informational `program_id`
    /// and the bound of polls the run was asked under. A run that ended serves every bound at
    /// least the smaller of its bound and its count ([`RunPolls::serves`]), so the record a
    /// request reads may have run under another bound; a cut run serves its own bound only, so
    /// two records of it that serve one request have one bound (`run --verify`).
    #[must_use]
    pub fn same_run(&self, other: &Self) -> bool {
        self.ends == other.ends
            && self.stop_ends == other.stop_ends
            && self.one_sided_ends == other.one_sided_ends
            && self.undefined_steps == other.undefined_steps
            && self.complete == other.complete
            && self.across == other.across
            && self.polls.count == other.polls.count
            && self.polls.cut == other.polls.cut
    }

    /// The record's integrity digest under its context, mutation and program:
    /// `payload_digest(MUTANT_ENDS_DOMAIN, canonical JSON of {context_sha256, mutation_identity,
    /// program_digest, ends, stop_ends, one_sided_ends, undefined_steps, complete, across,
    /// polls})`. It detects corruption and a record moved under another key, not forgery.
    pub fn digest(
        &self,
        context_sha256: &str,
        mutation_identity: &str,
        program_digest: &str,
    ) -> Sha256Digest {
        let mut payload = self.payload();
        payload["context_sha256"] = json!(context_sha256);
        payload["mutation_identity"] = json!(mutation_identity);
        payload["program_digest"] = json!(program_digest);
        payload_digest(MUTANT_ENDS_DOMAIN, canonical_json(&payload).as_bytes())
    }

    fn from_value(value: &Value) -> Option<Self> {
        let texts = |key: &str| {
            value
                .get(key)?
                .as_array()?
                .iter()
                .map(|text| text.as_str().map(str::to_owned))
                .collect::<Option<Vec<_>>>()
        };
        let ends = texts("ends")?;
        let stop_ends = value
            .get("stop_ends")?
            .as_array()?
            .iter()
            .map(|index| usize::try_from(index.as_u64()?).ok())
            .collect::<Option<Vec<_>>>()?;
        if stop_ends.iter().any(|index| *index >= ends.len())
            || stop_ends.windows(2).any(|pair| pair[0] >= pair[1])
        {
            return None;
        }
        let record = Self {
            program_id: value.get("program_id")?.as_str()?.to_owned(),
            ends,
            stop_ends,
            one_sided_ends: texts("one_sided_ends")?,
            undefined_steps: value.get("undefined_steps")?.as_bool()?,
            complete: value.get("complete")?.as_bool()?,
            across: Across::from_value(value.get("across")?)?,
            polls: RunPolls::from_value(value.get("polls")?)?,
        };
        // Only a complete run's ends are judged across.
        (record.complete || record.across.mutant.is_none()).then_some(record)
    }
}

/// The mutant ends store of one command: its context and the directory the context's digest
/// names.
#[derive(Clone, Debug)]
pub struct MutantEndStore {
    directory: PathBuf,
    context: Value,
    context_sha256: String,
}

impl MutantEndStore {
    /// The store of `context` ([`crate::digest::mutant_ends_context`]) under the cache directory
    /// `cache`.
    pub fn new(cache: &Path, context: Value) -> Self {
        let context_sha256 = crate::digest::context_sha256(&context).to_string();
        Self {
            directory: cache.join(MUTANT_ENDS_DIRECTORY).join(&context_sha256),
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

    /// The record file of the mutation with `identity` on the program with digest `program`.
    pub fn path(&self, identity: Sha256Digest, program: &str) -> PathBuf {
        self.directory
            .join(identity.to_string())
            .join(format!("{program}.json"))
    }

    /// The stored ends of the mutation with `identity` on the program with digest `program`,
    /// when the record passes every check that needs no corpus (module documentation,
    /// "Reading"). A missing or unreadable record is `None`.
    pub fn read(&self, identity: Sha256Digest, program: &str) -> Option<MutantEnds> {
        Sha256Digest::parse(program)?;
        let text = fs::read_to_string(self.path(identity, program)).ok()?;
        let value = kink_patch::parse_json(&text).ok()?;
        let identity = identity.to_string();
        let current = value["schema"] == MUTANT_ENDS_SCHEMA
            && value["version"] == MUTANT_ENDS_VERSION
            && value["context_sha256"] == self.context_sha256.as_str()
            && value["mutation_identity"] == identity.as_str()
            && value["program_digest"] == program;
        if !current {
            return None;
        }
        let record = MutantEnds::from_value(&value)?;
        let digest = record.digest(&self.context_sha256, &identity, program);
        (value.get("record_sha256")?.as_str()? == digest.to_string()).then_some(record)
    }

    /// Write the records (by program digest) of the mutation with `identity`, each to its own
    /// file, atomically (kink-corpus `Store`), replacing what was there. Returns the number of
    /// files written.
    pub fn write(
        &self,
        store: &Store,
        identity: Sha256Digest,
        mutation_id: &str,
        records: &[(String, MutantEnds)],
    ) -> Result<usize, StoreError> {
        let identity_text = identity.to_string();
        for (program, record) in records {
            let mut value = record.payload();
            value["schema"] = json!(MUTANT_ENDS_SCHEMA);
            value["version"] = json!(MUTANT_ENDS_VERSION);
            value["context_sha256"] = json!(self.context_sha256);
            value["mutation_identity"] = json!(identity_text);
            value["program_digest"] = json!(program);
            value["mutation_id"] = json!(mutation_id);
            value["program_id"] = json!(record.program_id);
            value["record_sha256"] = json!(
                record
                    .digest(&self.context_sha256, &identity_text, program)
                    .to_string()
            );
            store.write_json(&self.path(identity, program), &value)?;
        }
        Ok(records.len())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use kink_campaign::{CrossRefusal, FinalResult, OracleValue};
    use std::collections::BTreeSet;

    fn int(value: i64) -> Pattern {
        parse_pattern(&format!("\\dv{{SortInt{{}}}}(\"{value}\")")).unwrap()
    }

    fn normal(ends: &BTreeSet<Pattern>) -> OracleSide {
        OracleSide::Normal(OracleValue::FinalResult(FinalResult::WholeTerm(
            ends.clone(),
        )))
    }

    fn notes(count: u64, bound: u64, cut: bool) -> RunNotes {
        RunNotes {
            polls: Some(count),
            max_polls: Some(bound),
            poll_bound: cut,
            ..RunNotes::default()
        }
    }

    /// The evidence of a run that ended at `ends`, every side a value.
    fn ended(ends: &[i64]) -> TestEvidence {
        let ends = ends
            .iter()
            .map(|value| int(*value))
            .collect::<BTreeSet<_>>();
        TestEvidence {
            test_id: "p".into(),
            run: SideRun::Sides {
                sides: vec![normal(&ends), normal(&ends)],
            },
            notes: notes(40, 145, false),
            stop_ends: ends.iter().take(1).cloned().collect(),
            ends,
            undefined_steps: false,
            one_sided_ends: BTreeSet::new(),
            payloads: std::collections::BTreeMap::new(),
        }
    }

    fn compared(slots: &[OracleOutcome]) -> TestRun {
        TestRun::Compared(slots.to_vec())
    }

    fn identity() -> Sha256Digest {
        kink_patch::sha256(b"mutation")
    }

    fn program() -> String {
        kink_patch::sha256(b"program").to_string()
    }

    /// A run that ended is stored with every end, complete, with its polls; a run the poll bound
    /// cut is stored with the ends of its complete paths, not complete, and serves only its own
    /// bound; a run with no end but undefined steps is stored as the empty set, which differs from
    /// no record.
    #[test]
    fn a_record_states_whether_its_ends_are_the_whole_set() {
        let agree = compared(&[OracleOutcome::Agree, OracleOutcome::Agree]);
        let record = MutantEnds::of("p", &agree, &ended(&[1, 2])).unwrap();
        assert_eq!(record.ends.len(), 2);
        assert_eq!(record.stop_ends, vec![0]);
        assert!(record.complete);
        assert_eq!(record.across, Across::default());
        assert!(record.polls.serves(145) && record.polls.serves(40) && !record.polls.serves(39));
        assert_eq!(record.patterns().unwrap(), vec![int(1), int(2)]);

        let mut cut = ended(&[3]);
        cut.run = SideRun::Sides {
            sides: vec![OracleSide::Unknown, OracleSide::Unknown],
        };
        cut.notes = notes(145, 145, true);
        cut.one_sided_ends = BTreeSet::from([int(9)]);
        let unknown = compared(&[OracleOutcome::Unknown, OracleOutcome::Unknown]);
        let record = MutantEnds::of("p", &unknown, &cut).unwrap();
        assert!(!record.complete);
        assert_eq!(record.ends, vec![int(3).to_string()]);
        assert_eq!(record.one_sided_ends, vec![int(9).to_string()]);
        assert!(record.polls.serves(145) && !record.polls.serves(146));

        let mut undefined = ended(&[]);
        undefined.undefined_steps = true;
        let record = MutantEnds::of("p", &agree, &undefined).unwrap();
        assert!(record.complete && record.undefined_steps && record.ends.is_empty());
    }

    /// No record for a run the watchdog stopped (a `timeout` side or slot, even where a prefix
    /// program's slots agree), a failed or skipped test, a run whose judgement was refused or
    /// that carries no polls; a pair's refusal of the mutant's ends keeps the record complete and
    /// says why.
    #[test]
    fn only_a_run_that_is_a_function_of_its_key_is_stored() {
        let agree = compared(&[OracleOutcome::Agree, OracleOutcome::Agree]);
        let mut timed_out = ended(&[1]);
        timed_out.run = SideRun::Sides {
            sides: vec![OracleSide::Timeout, OracleSide::Timeout],
        };
        assert_eq!(MutantEnds::of("p", &agree, &timed_out), None);
        let killed_with_timeout = compared(&[OracleOutcome::Distinguish, OracleOutcome::Timeout]);
        assert_eq!(
            MutantEnds::of("p", &killed_with_timeout, &ended(&[1])),
            None
        );
        let failed = TestRun::Failed(kink_campaign::ExecutionFailureKind::TimeLimit);
        assert_eq!(MutantEnds::of("p", &failed, &ended(&[1])), None);
        assert_eq!(
            MutantEnds::of("p", &TestRun::SkippedAfterKill, &ended(&[1])),
            None
        );
        let mut unjudged = ended(&[1]);
        unjudged.notes.unjudged = true;
        assert_eq!(MutantEnds::of("p", &agree, &unjudged), None);
        let mut unbounded = ended(&[1]);
        unbounded.notes.max_polls = None;
        assert_eq!(MutantEnds::of("p", &agree, &unbounded), None);

        let mut refused = ended(&[1]);
        refused.run = SideRun::Sides {
            sides: vec![OracleSide::Unknown, OracleSide::Unknown],
        };
        refused.notes.across = [0, 1]
            .into_iter()
            .map(|slot| CrossRefusal {
                slot,
                baseline_end: false,
                end: CrossEnd::Terminal,
                cause: CrossCause::NoData,
            })
            .collect();
        let unknown = compared(&[OracleOutcome::Unknown, OracleOutcome::Unknown]);
        let record = MutantEnds::of("p", &unknown, &refused).unwrap();
        assert!(record.complete);
        assert_eq!(
            record.across,
            Across {
                baseline: None,
                mutant: Some(NotData::NoData),
            }
        );
    }

    /// The store's context is tier 1's without what a projection compares: two tier-1 contexts
    /// that differ only in their slots, cells left out or evidence give one ends context, and
    /// every other member (an input of the run) still keys it.
    #[test]
    fn the_context_names_no_projection() {
        use crate::digest::{EXECUTION_DIGEST_KIND, ExecutionDigest, mutant_ends_context};
        let execution = ExecutionDigest {
            kind: EXECUTION_DIGEST_KIND,
            digest: kink_patch::sha256(b"definition"),
        };
        let outcome = json!({
            "outcome_schema": "kink-flow/outcome/v4",
            "kink_build": "b",
            "kink": {"one_sided": 5},
            "profile": "portable",
            "execution_digest": {"kind": "x", "digest": "with result cells"},
            "budget": {"max_depth": 10},
            "oracles": ["exit-stop", "whole-term"],
            "classifier": "all-normal",
            "stop": {"rules": ["r"]},
            "observe": {"logs": []},
        });
        let mut projected = outcome.clone();
        projected["oracles"] = json!(["exit-stop", "cells"]);
        projected["not_compared"] = json!(["<k>"]);
        projected["evidence"] = json!({"format": "krs", "identity": "i"});
        let context = mutant_ends_context(&outcome, execution);
        assert_eq!(context, mutant_ends_context(&projected, execution));
        assert_eq!(
            context,
            json!({
                "ends_schema": MUTANT_ENDS_VERSION,
                "kink_build": "b",
                "kink": {"one_sided": 5},
                "profile": "portable",
                "execution_digest": execution.value(),
                "budget": {"max_depth": 10},
                "classifier": "all-normal",
                "stop": {"rules": ["r"]},
                "observe": {"logs": []},
            })
        );
        let mut other = outcome.clone();
        other["budget"] = json!({"max_depth": 11});
        assert_ne!(context, mutant_ends_context(&other, execution));
    }

    /// A record reads back as written; it is not read under another context, mutation or
    /// program, nor once any member is altered.
    #[test]
    fn a_record_is_read_only_under_its_own_key_and_unaltered() {
        let directory = std::env::temp_dir().join(format!(
            "kink-flow-mutant-ends-{}-{}",
            std::process::id(),
            line!()
        ));
        let _ = fs::remove_dir_all(&directory);
        let store = Store::new(&directory);
        let ends = MutantEndStore::new(&directory, json!({"test": "u11a"}));
        let agree = compared(&[OracleOutcome::Agree, OracleOutcome::Agree]);
        let record = MutantEnds::of("p", &agree, &ended(&[1, 2])).unwrap();
        let written = ends
            .write(&store, identity(), "m", &[(program(), record.clone())])
            .unwrap();
        assert_eq!(written, 1);
        assert_eq!(ends.read(identity(), &program()), Some(record));

        let other = MutantEndStore::new(&directory, json!({"test": "other"}));
        assert_eq!(other.read(identity(), &program()), None);
        assert_eq!(ends.read(kink_patch::sha256(b"other"), &program()), None);
        assert_eq!(
            ends.read(identity(), &kink_patch::sha256(b"other").to_string()),
            None
        );
        // A record moved under another program's name is not that program's.
        let path = ends.path(identity(), &program());
        let moved = ends.path(identity(), &kink_patch::sha256(b"moved").to_string());
        fs::copy(&path, &moved).unwrap();
        assert_eq!(
            ends.read(identity(), &kink_patch::sha256(b"moved").to_string()),
            None
        );
        // An altered end, or completeness, is ignored.
        let text = fs::read_to_string(&path).unwrap();
        let mut value: Value = serde_json::from_str(&text).unwrap();
        value["ends"][0] = json!(int(7).to_string());
        fs::write(&path, value.to_string()).unwrap();
        assert_eq!(ends.read(identity(), &program()), None);
        let mut value: Value = serde_json::from_str(&text).unwrap();
        value["complete"] = json!(false);
        fs::write(&path, value.to_string()).unwrap();
        assert_eq!(ends.read(identity(), &program()), None);
        let _ = fs::remove_dir_all(&directory);
    }
}
