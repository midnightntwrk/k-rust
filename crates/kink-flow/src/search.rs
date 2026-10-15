//! The kill search with its outcome cache (flow README 5.4, 5.6 and 7.5): `kink-flow run`.
//!
//! One command admits the specification once and uses its one `NativeValidator` for the
//! result cache update and for every mutation. Per mutation, in the list's order:
//!
//! 1. Resolve it into one pinned patch (F-04); an `invalid-mutation` ends there.
//! 2. Choose the programs O: the comparable programs of the up-to-date result cache, the ones
//!    whose cached coverage reaches an edited rule first, then the rest, each group in corpus
//!    order.
//! 3. Tier 1 (README 7.5.3): the valid outcome records of the programs of O, under a key that
//!    names every input of the outcome (kink's build, the k-rust revision, the solver profile,
//!    the specification's execution digest, the budget, the oracles, the mutation's identity,
//!    the program digest and the program's baseline run digest). A valid `killed` record makes
//!    the status `killed` with no call (its killer the first such program in O); otherwise the
//!    programs with a valid `agree` record form A, and L = O minus A. With L empty the status
//!    is the runner's fold over A's cached outcomes (survived), with no call.
//! 4. Otherwise the mutant runs live on L. Tier 2 (README 7.5.5): when the killer hint names a
//!    comparable program of L, one call runs that program alone; if it kills, that is the
//!    verdict. Otherwise the cold call runs L in O's order (the hinted program included).
//! 5. Every status is `kink_campaign::derive_mutant_report` (schedule `FirstKill`) over the
//!    assembled plan: A's cached outcomes in O's order, then the last live call's tests in
//!    their order, with that call's mutant-scope failure. kink-flow adds no fold and compares
//!    no terms: a mutation is killed only by a proved `Distinguish`, live from
//!    `run_campaign_multi` in this command or cached under an exactly matching key. A cached
//!    agreement is the fold's bottom, so the assembled status is the cold call's status; a
//!    live mutant-scope failure that precedes execution next to a cached agreement is the
//!    corpus error `outcome-conflict`.
//! 6. After every call, each program's baseline row from that call is compared, by run
//!    digest, with its cached record. Any difference is a corpus error: the mutation gets the
//!    status `error` with reason `baseline-mismatch:<program id>` (or
//!    `baseline-count-mismatch`), nothing is written to tier 1 for it, and the run stops.
//! 7. After a verdict, every live test whose outcome is cacheable (killed or agree) gets a
//!    tier-1 record, unless its call's plan carries a mutant-scope failure. A `killed` status
//!    makes its first killing program the mutation's hint; any other status removes it. The
//!    hints file and the report are written after every mutation, corpus errors included.
//!
//! Every campaign call goes through the command's one [`BaselineRunner`] and its in-memory
//! baseline session (flow F-12, README 6.3): each program's baseline runs live at most once per
//! command, in the result update or in the first call that needs it, and later calls of the
//! same command reuse that live run where the runner produces baseline evidence. The drift check
//! still compares every call's baseline rows with the cached records. The run document's
//! `baseline_runs` counts the live and reused baseline runs.
//!
//! `run --verify` ([`RunMode::Verify`]) decides nothing from tier 1: it runs the cold call over
//! O for every mutation, then one call per valid record whose program the cold call did not
//! execute, and reports every record (and the cached path's status) that differs from the live
//! runs as `outcome-mismatch:<program id>`. It writes no record and no hint.

use crate::{
    admit::{AdmittedSpec, ProgramInputs, admit_spec},
    digest::{execution_digest, hint_key, kink_build_identity, mutation_identity, outcome_context},
    hints::{HintEntry, Hints},
    manifest::{Budget, FlowManifest},
    mutation::{InvalidMutation, Mutation, MutationList, ResolvedMutation, resolve},
    outcomes::{CachedOutcome, OutcomeRecord, OutcomeStore, cacheable, slot_name},
    report::{
        RUN_SCHEMA, RUN_VERSION, action, executed_cause, rules_value, survivors, unusable_programs,
    },
    results::{
        BaselineRunner, ORACLE_SLOTS, ProgramRow, RESULT_SCHEMA_VERSION, ResultClass,
        cache_directory, fixed_oracles, kebab, rerun_timeout_record, run_digest, runner_refusal,
        update_results,
    },
};
use kink_campaign::{
    CampaignFailure, CampaignOptions, CampaignReport, ManifestTest, MutantId, MutantPlan,
    MutantReport, MutantRun, MutantStatus, OracleOutcome, ScheduleMode, TestCase, TestPlan,
    TestRun, derive_mutant_report,
};
use kink_corpus::{Store, admission::AdmissionRecord};
use kink_native::{K_RUST_REVISION, execution::SolverProfile};
use kink_patch::{CandidateGeneration, Sha256Digest, Withdrawal};
use serde_json::{Map, Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};

/// The run document's file in the cache directory, rewritten after every mutation.
pub const REPORT_FILE: &str = "report.json";

/// The status of a mutation that does not resolve to a patch (README 5.5).
pub const INVALID_MUTATION: &str = "invalid-mutation";

/// The `killer_source` of a status decided by a valid tier-1 `killed` record.
pub const SOURCE_OUTCOME_CACHE: &str = "outcome-cache";
/// The `killer_source` of a kill found by the one-program call over the hinted program.
pub const SOURCE_HINT: &str = "hint";
/// The `killer_source` of a kill found by the cold call.
pub const SOURCE_SEARCH: &str = "search";

/// Every status a mutation can have, in the order the counts list them: the runner's
/// mutant statuses, then the flow's own `invalid-mutation`. `error` is also the status of a
/// corpus error and of an `outcome-mismatch` (their reasons say which).
pub const STATUSES: [&str; 8] = [
    "killed",
    "survived",
    "equivalent",
    "invalid",
    "timeout",
    "unknown",
    "error",
    INVALID_MUTATION,
];

/// The runner's mutant status as the run document names it.
pub const fn status_name(status: MutantStatus) -> &'static str {
    match status {
        MutantStatus::Killed => "killed",
        MutantStatus::Survived => "survived",
        MutantStatus::Equivalent => "equivalent",
        MutantStatus::Invalid => "invalid",
        MutantStatus::Timeout => "timeout",
        MutantStatus::Unknown => "unknown",
        MutantStatus::Error => "error",
    }
}

/// Options of the `run` command.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct RunOptions {
    /// Run only the mutations with these ids (all when empty).
    pub only: Vec<String>,
    /// The cache directory; default `<directory of FLOW.toml>/.kink-flow`.
    pub cache: Option<PathBuf>,
}

/// How `run` uses the outcome cache.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum RunMode {
    /// The kill search with both tiers (`kink-flow run`).
    #[default]
    Search,
    /// Re-prove every valid tier-1 record and decide nothing from it (`kink-flow run
    /// --verify`, README 7.5.3): no tier-1 decision, no hint, no write but the report.
    Verify,
}

/// One comparable program: a possible killer.
struct Candidate<'r> {
    /// The manifest's program index.
    index: usize,
    id: &'r str,
    digest: Sha256Digest,
    /// The cached record's run digest (a comparable record always has one, unless edited).
    run_sha256: Option<&'r str>,
    /// The `(module, index)` of every baseline sentence its cached coverage reaches.
    reaches: BTreeSet<(String, u64)>,
}

fn candidate<'r>(index: usize, id: &'r str, row: &'r ProgramRow) -> Option<Candidate<'r>> {
    if row.class() != Some(ResultClass::Comparable.as_str()) {
        return None;
    }
    let record = row.record.as_ref()?;
    let reaches = record["coverage"]["sentences"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|sentence| {
            Some((
                sentence["module"].as_str()?.to_owned(),
                sentence["index"].as_u64()?,
            ))
        })
        .collect();
    Some(Candidate {
        index,
        id,
        digest: row.digest?,
        run_sha256: record["run_sha256"].as_str(),
        reaches,
    })
}

/// A corpus error: no verdict for the mutation, and the run stops.
struct CorpusError {
    reason: String,
    detail: String,
}

/// What the command counts about tier 1, for the run document's `outcome_cache`.
#[derive(Clone, Copy, Debug, Default)]
struct Stats {
    /// Mutations whose status came from tier 1 with no campaign call.
    mutations_from_cache: usize,
    /// (mutation, program) outcomes taken from valid records into a status.
    programs_from_cache: usize,
    /// Tier-1 records written.
    records_written: usize,
}

/// A live program's outcome in `run --verify`.
enum Live {
    /// The test ran: its run and the run digest of the mutant's evidence row.
    Ran(TestRun, Option<String>),
    /// The one-program call ran no test (a mutant-scope failure): the call's status.
    NotRun(&'static str),
}

/// The command's state: the admitted specification, its one validator, the corpus, the
/// caches.
struct Search<'a> {
    spec: &'a AdmittedSpec,
    manifest: &'a FlowManifest,
    inputs: &'a mut ProgramInputs,
    /// The command's campaign calls, through its one baseline session.
    runner: &'a BaselineRunner<'a>,
    rows: &'a [ProgramRow],
    candidates: Vec<Candidate<'a>>,
    /// Each candidate's test case with the fixed oracles, assembled on first use.
    tests: Vec<Option<TestCase>>,
    mode: RunMode,
    /// The tier-1 store; `None` when kink's build identity cannot be computed.
    tier1: Option<OutcomeStore>,
    hints: Hints,
    store: Store,
    stats: Stats,
    /// `run --verify`'s disagreements, for the run document's `mismatches`.
    mismatches: Vec<Value>,
}

impl Search<'_> {
    fn test(&mut self, candidate: usize) -> Result<TestCase, CorpusError> {
        if let Some(test) = &self.tests[candidate] {
            return Ok(test.clone());
        }
        let index = self.candidates[candidate].index;
        let program = &self.manifest.programs[index];
        let row = &self.rows[index];
        let mut test = match (&row.test, &row.text) {
            (Some(test), _) => test.clone(),
            (None, Some(text)) => self
                .inputs
                .test_case(self.spec, program, text.clone())
                .map_err(|refusal| CorpusError {
                    reason: format!("program-refused:{}", program.id),
                    detail: format!("{}/{}: {}", refusal.stage, refusal.reason, refusal.detail),
                })?,
            (None, None) => {
                return Err(CorpusError {
                    reason: format!("program-refused:{}", program.id),
                    detail: "the program has a comparable record but no text".into(),
                });
            }
        };
        test.oracles = fixed_oracles();
        self.tests[candidate] = Some(test.clone());
        Ok(test)
    }

    /// One campaign call over `order` (candidate indices), then the drift check. The mutant's
    /// run, or the corpus error.
    fn call(
        &mut self,
        generation: &CandidateGeneration<'_>,
        order: &[usize],
    ) -> Result<MutantRun, CorpusError> {
        let mut tests = Vec::with_capacity(order.len());
        for &candidate in order {
            tests.push(self.test(candidate)?);
        }
        let options = CampaignOptions {
            schedule: ScheduleMode::FirstKill,
            selection: kink_campaign::SelectionPolicy::None,
            share_evidence: false,
        };
        let mut run = self
            .runner
            .call(&tests, std::slice::from_ref(generation), &options)
            .map_err(|failure| CorpusError {
                reason: "campaign-refused".into(),
                detail: format!(
                    "the campaign runner refused the call over {:?}: {failure}; the cached \
                         results no longer describe the baseline runs: run `kink-flow results \
                         --verify`",
                    self.ids(order)
                ),
            })?;
        // The drift check (README 5.4): every program's baseline row of this call must have
        // its cached record's run digest. The reason names the program from the candidate,
        // never from a message (F-05 review 1 minor 2).
        let mut mismatched = Vec::new();
        for &candidate in order {
            let candidate = &self.candidates[candidate];
            let now = run
                .baseline
                .iter()
                .find(|evidence| evidence.test_id == candidate.id)
                .and_then(|evidence| CampaignReport::baseline_row(evidence).ok())
                .as_ref()
                .and_then(run_digest)
                .map(|digest| digest.to_string());
            if now.is_none() || now.as_deref() != candidate.run_sha256 {
                mismatched.push((
                    candidate.id,
                    format!(
                        "{}: cached run_sha256 {}, now {}",
                        candidate.id,
                        candidate.run_sha256.unwrap_or("null"),
                        now.as_deref().unwrap_or("no baseline row"),
                    ),
                ));
            }
        }
        let count = (run.baseline.len() != order.len()).then(|| {
            format!(
                "the call ran {} baseline programs for {} tests",
                run.baseline.len(),
                order.len()
            )
        });
        if let Some(reason) = drift_reason(mismatched.first().map(|(id, _)| *id), count.is_some()) {
            let details = mismatched
                .into_iter()
                .map(|(_, detail)| detail)
                .chain(count)
                .collect::<Vec<_>>();
            return Err(CorpusError {
                reason,
                detail: format!("{}; run `kink-flow results --verify`", details.join("; ")),
            });
        }
        if run.mutants.len() != 1 {
            return Err(CorpusError {
                reason: "campaign-refused".into(),
                detail: format!("the runner returned {} mutants for one", run.mutants.len()),
            });
        }
        Ok(run.mutants.remove(0))
    }

    fn ids(&self, order: &[usize]) -> Vec<&str> {
        order.iter().map(|&c| self.candidates[c].id).collect()
    }

    fn position(&self, id: &str) -> Option<usize> {
        self.candidates.iter().position(|c| c.id == id)
    }

    /// The `calls` of a mutation row: the programs each campaign call ran, and its status.
    fn calls(&self, calls: &[(Vec<usize>, Value)]) -> Vec<Value> {
        calls
            .iter()
            .map(|(order, status)| json!({"programs": self.ids(order), "status": status}))
            .collect()
    }

    /// The executed entry of a valid tier-1 record (`cached: true`).
    fn cached_entry(&self, candidate: usize, record: &OutcomeRecord) -> Value {
        json!({
            "program": self.candidates[candidate].id,
            "outcome": compared_outcome(&record.slots),
            "slots": record.slots.iter().map(|o| slot_name(*o)).collect::<Vec<_>>(),
            "cause": null,
            "cached": true,
        })
    }

    /// The valid tier-1 records of the programs of `order`, in that order (README 7.5.3): the
    /// store's integrity checks, then the program is a current comparable candidate whose
    /// result record has the record's baseline run digest. A `killed` record of a program
    /// that is in the corpus but not comparable is reported as the row's `unusable_killer`.
    fn valid_records(
        &self,
        identity: Option<Sha256Digest>,
        order: &[usize],
        row: &mut Map<String, Value>,
    ) -> Vec<(usize, OutcomeRecord)> {
        let (Some(store), Some(identity)) = (&self.tier1, identity) else {
            return Vec::new();
        };
        let stored = store.read(identity);
        for (program, record) in &stored {
            if record.outcome == CachedOutcome::Killed
                && !self
                    .candidates
                    .iter()
                    .any(|c| c.digest.to_string() == *program)
            {
                self.unusable(row, program, SOURCE_OUTCOME_CACHE);
            }
        }
        order
            .iter()
            .filter_map(|&c| {
                let candidate = &self.candidates[c];
                let record = stored.get(&candidate.digest.to_string())?;
                (candidate.run_sha256 == Some(record.baseline_run_sha256.as_str()))
                    .then(|| (c, record.clone()))
            })
            .collect()
    }

    /// Report, once per row, a killer that names a program of the corpus whose class is not
    /// comparable: `unusable_killer: {program, class, cause, source}` (README 7.5.7).
    fn unusable(&self, row: &mut Map<String, Value>, digest: &str, source: &str) {
        if row.contains_key("unusable_killer") {
            return;
        }
        let found = self
            .manifest
            .programs
            .iter()
            .zip(self.rows)
            .find(|(_, r)| r.digest.is_some_and(|d| d.to_string() == digest));
        if let Some((program, program_row)) = found {
            row.insert(
                "unusable_killer".into(),
                json!({
                    "program": program.id,
                    "class": program_row.row["class"],
                    "cause": program_row.row["cause"],
                    "source": source,
                }),
            );
        }
    }

    /// The assembled plan's report (README 7.5.3 step 5): the cached outcomes in the given
    /// order, then the live plan's tests (`live`: the call's order and plan), with the live
    /// plan's mutant-scope failure, mutant id and claims; the manifest lists the same ids in
    /// the same order. The fold is kink-campaign's own.
    fn assemble(
        &self,
        cached: &[(usize, OutcomeRecord)],
        live: Option<(&[usize], &MutantPlan)>,
    ) -> Result<MutantReport, CampaignFailure> {
        let mut tests = cached
            .iter()
            .map(|(c, record)| TestPlan {
                test_id: self.candidates[*c].id.to_owned(),
                run: record.test_run(),
            })
            .collect::<Vec<_>>();
        let mut ids = cached
            .iter()
            .map(|(c, _)| self.candidates[*c].id.to_owned())
            .collect::<Vec<_>>();
        let (mutant_failure, mutant_id, claims) = match live {
            Some((order, plan)) => {
                tests.extend(plan.tests.iter().cloned());
                ids.extend(self.ids(order).into_iter().map(str::to_owned));
                (plan.mutant_failure, plan.mutant_id, plan.claims.clone())
            }
            None => (None, MutantId(0), Withdrawal::default()),
        };
        let plan = MutantPlan {
            selection: None,
            mutant_id,
            tests,
            mutant_failure,
            claims,
        };
        let manifest = ids
            .into_iter()
            .map(|test_id| ManifestTest {
                test_id,
                slot_count: ORACLE_SLOTS.len(),
            })
            .collect::<Vec<_>>();
        derive_mutant_report(&plan, &manifest, ScheduleMode::FirstKill)
    }

    /// The tier-1 records a live call gives (README 7.5.3 step 7): one per test whose outcome
    /// is cacheable, none when the call's plan carries a mutant-scope failure.
    fn live_records(&self, run: &MutantRun) -> Vec<(String, OutcomeRecord)> {
        if run.plan.mutant_failure.is_some() {
            return Vec::new();
        }
        run.plan
            .tests
            .iter()
            .filter_map(|test| {
                let (outcome, slots) = cacheable(&test.run)?;
                let candidate = &self.candidates[self.position(&test.test_id)?];
                Some((
                    candidate.digest.to_string(),
                    OutcomeRecord {
                        program_id: candidate.id.to_owned(),
                        // Equal to the live baseline row's digest: the drift check passed.
                        baseline_run_sha256: candidate.run_sha256?.to_owned(),
                        outcome,
                        slots: slots.to_vec(),
                        mutant_run_sha256: mutant_run_sha256(run, &test.test_id)?,
                    },
                ))
            })
            .collect()
    }

    fn hint_entry(&self, candidate: usize, mutation: &Mutation) -> HintEntry {
        let candidate = &self.candidates[candidate];
        HintEntry {
            program_digest: candidate.digest.to_string(),
            program_id: candidate.id.to_owned(),
            mutation_id: mutation.id.clone(),
        }
    }

    /// The kill search for one mutation: its row of the run document, and whether it ended in
    /// a corpus error (the run then stops, and nothing is written to tier 1 for it).
    fn search_one(&mut self, mutation: &Mutation) -> (Value, bool) {
        let mut row = Map::new();
        row.insert("id".into(), json!(mutation.id));
        row.insert("note".into(), json!(mutation.note));
        let resolved = match resolve(self.manifest, &self.spec.loaded, mutation) {
            Ok(resolved) => resolved,
            Err(e) => return (invalid(row, e, Value::Null), false),
        };
        let digest = resolved.digest;
        row.insert("digest".into(), json!(digest.to_string()));
        // The survivor report's rule texts (README 5.7); a killed mutation drops them below.
        row.insert("rules".into(), rules_value(&resolved));
        // The generation must derive from the validator's own baseline (the runner refuses any
        // other); the patch is pinned, so it applies to it as to the loaded baseline.
        let generation = match resolved.generation(self.spec.validator.baseline()) {
            Ok(generation) => generation,
            Err(e) => return (invalid(row, e, json!(digest.to_string())), false),
        };
        let order = order(&self.candidates, &resolved);
        let reaching = order
            .iter()
            .filter(|&&c| reaches(&self.candidates[c], &resolved))
            .map(|&c| self.candidates[c].id.to_owned())
            .collect::<Vec<_>>();
        row.insert("reaching".into(), json!(reaching));
        let identity = mutation_identity(&self.spec.loaded.baseline, &resolved.patch);
        row.insert(
            "identity".into(),
            json!(identity.map(|identity| identity.to_string())),
        );
        let key = hint_key(mutation, &resolved);
        let records = self.valid_records(identity, &order, &mut row);
        // Tier 2: the hint, when it names a comparable program; otherwise it is removed.
        let mut hint = None;
        if self.mode == RunMode::Search
            && let Some(entry) = self.hints.get(key).cloned()
        {
            hint = self
                .candidates
                .iter()
                .position(|c| c.digest.to_string() == entry.program_digest);
            if hint.is_none() {
                row.insert(
                    "stale_killer".into(),
                    json!(format!(
                        "the hinted killer {} (digest {}) is not a comparable program; the hint \
                         is removed",
                        entry.program_id, entry.program_digest
                    )),
                );
                self.unusable(&mut row, &entry.program_digest, SOURCE_HINT);
                self.hints.remove(key);
            }
        }
        if order.is_empty() {
            row.insert("status".into(), json!("error"));
            row.insert("reason".into(), json!("no-comparable-program"));
            row.insert(
                "detail".into(),
                json!("no program of the corpus has a comparable result, so nothing can kill"),
            );
            if self.mode == RunMode::Search {
                self.hints.remove(key);
            }
            return (finish(row, None, None, Vec::new(), Vec::new()), false);
        }
        if self.mode == RunMode::Verify {
            return self.verify_one(row, mutation, &generation, &order, &records);
        }

        // Tier 1, step 2: a valid killed record decides, with no call.
        if let Some((c, record)) = records
            .iter()
            .find(|(_, record)| record.outcome == CachedOutcome::Killed)
        {
            let report = self.assemble(&[(*c, record.clone())], None);
            let report = report.expect("one cached killed test is a valid plan");
            debug_assert_eq!(report.status, MutantStatus::Killed);
            self.stats.mutations_from_cache += 1;
            self.stats.programs_from_cache += 1;
            self.hints.insert(key, self.hint_entry(*c, mutation));
            let executed = vec![self.cached_entry(*c, record)];
            return (
                verdict_row(
                    row,
                    &report,
                    None,
                    Some(SOURCE_OUTCOME_CACHE),
                    Vec::new(),
                    executed,
                ),
                false,
            );
        }
        // Step 3: A (every valid record is now an agreement) and L.
        let agree = records;
        let live_order = order
            .iter()
            .copied()
            .filter(|c| !agree.iter().any(|(a, _)| a == c))
            .collect::<Vec<_>>();
        let mut executed = agree
            .iter()
            .map(|(c, record)| self.cached_entry(*c, record))
            .collect::<Vec<_>>();
        self.stats.programs_from_cache += agree.len();
        if live_order.is_empty() {
            let report = self
                .assemble(&agree, None)
                .expect("cached agreements form a valid plan");
            self.stats.mutations_from_cache += 1;
            self.hints.remove(key);
            return (
                verdict_row(row, &report, None, None, Vec::new(), executed),
                false,
            );
        }

        // Step 4: live calls, the hinted program alone first.
        let mut calls = Vec::new();
        let mut runs = Vec::<(Vec<usize>, MutantRun)>::new();
        let mut source = SOURCE_SEARCH;
        if let Some(h) = hint.filter(|h| live_order.contains(h)) {
            match self.call(&generation, &[h]) {
                Err(error) => {
                    calls.push((vec![h], json!("error")));
                    return self.corpus_error(row, error, &calls, executed);
                }
                Ok(run) => {
                    calls.push((vec![h], json!(status_name(run.report.status))));
                    executed.extend(executed_entries(&run, self.manifest.budget));
                    if run.report.status == MutantStatus::Killed {
                        source = SOURCE_HINT;
                    }
                    runs.push((vec![h], run));
                }
            }
        }
        if source != SOURCE_HINT {
            match self.call(&generation, &live_order) {
                Err(error) => {
                    calls.push((live_order.clone(), json!("error")));
                    return self.corpus_error(row, error, &calls, executed);
                }
                Ok(run) => {
                    calls.push((live_order.clone(), json!(status_name(run.report.status))));
                    executed.extend(executed_entries(&run, self.manifest.budget));
                    runs.push((live_order.clone(), run));
                }
            }
        }
        // Step 5: the status of the assembled plan.
        let (last_order, last) = runs.last().expect("a live call");
        let report = match self.assemble(&agree, Some((last_order, &last.plan))) {
            Ok(report) => report,
            Err(failure) => {
                let error = CorpusError {
                    reason: "outcome-conflict".into(),
                    detail: format!(
                        "the cached agreements of {:?} and the live call over {:?} do not form \
                         one plan ({failure}): a cached outcome says the mutant ran, the live \
                         call says it did not; run `kink-flow run FLOW.toml MUTATIONS.toml \
                         --verify`",
                        agree
                            .iter()
                            .map(|(c, _)| self.candidates[*c].id)
                            .collect::<Vec<_>>(),
                        self.ids(last_order)
                    ),
                };
                return self.corpus_error(row, error, &calls, executed);
            }
        };
        let reason = last
            .plan
            .mutant_failure
            .map(|failure| kebab(&format!("{failure:?}")));
        // Step 7: the records of the live calls, then the hint.
        if let (Some(store), Some(identity)) = (&self.tier1, identity) {
            let records = runs
                .iter()
                .flat_map(|(_, run)| self.live_records(run))
                .collect::<Vec<_>>();
            if !records.is_empty() {
                match store.write(&self.store, identity, &mutation.id, &records) {
                    Ok(written) => self.stats.records_written += written,
                    Err(e) => {
                        row.insert(
                            "cache_error".into(),
                            json!(format!("cannot write the outcome records: {e}")),
                        );
                    }
                }
            }
        }
        let killer = (report.status == MutantStatus::Killed)
            .then(|| report.killing_test_ids.first())
            .flatten()
            .and_then(|program| self.position(program));
        match killer {
            Some(killer) => self.hints.insert(key, self.hint_entry(killer, mutation)),
            None => self.hints.remove(key),
        }
        let source = (report.status == MutantStatus::Killed).then_some(source);
        let calls = self.calls(&calls);
        (
            verdict_row(row, &report, reason, source, calls, executed),
            false,
        )
    }

    /// `run --verify` for one resolved mutation (README 7.5.3): the cold call over O, a
    /// one-program call per valid record the cold call did not execute, and the comparison of
    /// every valid record and of the cached path's status with the live ones.
    fn verify_one(
        &mut self,
        mut row: Map<String, Value>,
        mutation: &Mutation,
        generation: &CandidateGeneration<'_>,
        order: &[usize],
        records: &[(usize, OutcomeRecord)],
    ) -> (Value, bool) {
        let mut calls = Vec::new();
        let mut executed = Vec::new();
        let cold = match self.call(generation, order) {
            Err(error) => {
                calls.push((order.to_vec(), json!("error")));
                return self.corpus_error(row, error, &calls, executed);
            }
            Ok(run) => run,
        };
        calls.push((order.to_vec(), json!(status_name(cold.report.status))));
        executed.extend(executed_entries(&cold, self.manifest.budget));
        let mut live = BTreeMap::new();
        self.collect_live(&cold, &mut live);
        for (c, _) in records {
            if live.contains_key(c) {
                continue;
            }
            match self.call(generation, &[*c]) {
                Err(error) => {
                    calls.push((vec![*c], json!("error")));
                    return self.corpus_error(row, error, &calls, executed);
                }
                Ok(run) => {
                    calls.push((vec![*c], json!(status_name(run.report.status))));
                    executed.extend(executed_entries(&run, self.manifest.budget));
                    self.collect_live(&run, &mut live);
                    live.entry(*c)
                        .or_insert(Live::NotRun(status_name(run.report.status)));
                }
            }
        }
        // Every valid record against its program's live outcome.
        let mut mismatches = Vec::new();
        for (c, record) in records {
            let (outcome, mutant) = match &live[c] {
                Live::Ran(run, mutant) => (
                    cacheable(run)
                        .map_or_else(|| run_label(run).to_owned(), |(o, _)| o.as_str().to_owned()),
                    mutant.clone(),
                ),
                Live::NotRun(status) => ((*status).to_owned(), None),
            };
            if outcome != record.outcome.as_str()
                || mutant.as_deref() != Some(record.mutant_run_sha256.as_str())
            {
                mismatches.push(json!({
                    "mutation": mutation.id,
                    "program": self.candidates[*c].id,
                    "cached": {"outcome": record.outcome.as_str(),
                               "mutant_run_sha256": record.mutant_run_sha256},
                    "live": {"outcome": outcome, "mutant_run_sha256": mutant},
                }));
            }
        }
        // The status the cached path would have given, against the cold call's.
        let cached_status = self.cached_path_status(order, records, &cold);
        if cached_status != Some(cold.report.status) {
            mismatches.push(json!({
                "mutation": mutation.id,
                "program": null,
                "cached": {"status": cached_status.map(status_name)},
                "live": {"status": status_name(cold.report.status)},
            }));
        }
        let calls = self.calls(&calls);
        if let Some(first) = mismatches.first() {
            let program = first["program"]
                .as_str()
                .map(str::to_owned)
                .or_else(|| {
                    records
                        .first()
                        .map(|(c, _)| self.candidates[*c].id.to_owned())
                })
                .unwrap_or_else(|| "status".to_owned());
            row.insert("status".into(), json!("error"));
            row.insert(
                "reason".into(),
                json!(format!("outcome-mismatch:{program}")),
            );
            row.insert(
                "detail".into(),
                json!(format!(
                    "{} cached outcome(s) differ from the live runs (top-level mismatches); \
                     delete the cache's outcomes/ directory and report it",
                    mismatches.len()
                )),
            );
            self.mismatches.extend(mismatches);
            return (finish(row, None, None, calls, executed), false);
        }
        let reason = cold
            .plan
            .mutant_failure
            .map(|failure| kebab(&format!("{failure:?}")));
        let source = (cold.report.status == MutantStatus::Killed).then_some(SOURCE_SEARCH);
        (
            verdict_row(row, &cold.report, reason, source, calls, executed),
            false,
        )
    }

    /// Each executed test of a live run, by candidate.
    fn collect_live(&self, run: &MutantRun, live: &mut BTreeMap<usize, Live>) {
        for test in &run.plan.tests {
            if test.run == TestRun::SkippedAfterKill {
                continue;
            }
            if let Some(c) = self.position(&test.test_id) {
                live.insert(
                    c,
                    Live::Ran(test.run.clone(), mutant_run_sha256(run, &test.test_id)),
                );
            }
        }
    }

    /// The status the cached path gives for the records (README 7.5.3 steps 2-5), with the
    /// cold call's tests of L standing in for the live call over L; `None` when that plan is
    /// refused (the cached path's `outcome-conflict`).
    fn cached_path_status(
        &self,
        order: &[usize],
        records: &[(usize, OutcomeRecord)],
        cold: &MutantRun,
    ) -> Option<MutantStatus> {
        if records
            .iter()
            .any(|(_, record)| record.outcome == CachedOutcome::Killed)
        {
            return Some(MutantStatus::Killed);
        }
        let live_order = order
            .iter()
            .copied()
            .filter(|c| !records.iter().any(|(a, _)| a == c))
            .collect::<Vec<_>>();
        if live_order.is_empty() {
            return self.assemble(records, None).ok().map(|r| r.status);
        }
        let ids = self.ids(&live_order);
        let mut plan = cold.plan.clone();
        plan.tests
            .retain(|test| ids.contains(&test.test_id.as_str()));
        self.assemble(records, Some((&live_order, &plan)))
            .ok()
            .map(|r| r.status)
    }

    fn corpus_error(
        &self,
        mut row: Map<String, Value>,
        error: CorpusError,
        calls: &[(Vec<usize>, Value)],
        executed: Vec<Value>,
    ) -> (Value, bool) {
        row.insert("status".into(), json!("error"));
        row.insert("reason".into(), json!(error.reason));
        row.insert("detail".into(), json!(error.detail));
        (finish(row, None, None, self.calls(calls), executed), true)
    }
}

/// The reason of a failed drift check (README 5.4): `baseline-mismatch:<program id>` for the
/// first program whose baseline row does not have its cached run digest (the id is the
/// candidate's, so an id containing ':' stays whole), else `baseline-count-mismatch` when the
/// call ran another number of baseline programs than it had tests; `None` when the check
/// passed. The runner returns one baseline row per test, so the count mismatch is defensive.
pub fn drift_reason(first_mismatch: Option<&str>, count_mismatch: bool) -> Option<String> {
    match (first_mismatch, count_mismatch) {
        (Some(program), _) => Some(format!("baseline-mismatch:{program}")),
        (None, true) => Some("baseline-count-mismatch".to_owned()),
        (None, false) => None,
    }
}

/// The run digest of the mutant's evidence row for `test_id`: the mutant's `TestEvidence`
/// encoded by `CampaignReport::baseline_row`, which is the `side_run` encoding the campaign
/// report uses for mutant evidence too (kink-campaign report.rs, `baseline_row` and the
/// mutants' `tests[].mutant`).
fn mutant_run_sha256(run: &MutantRun, test_id: &str) -> Option<String> {
    let evidence = run.evidence.iter().find(|e| e.test_id == test_id)?;
    let row = CampaignReport::baseline_row(evidence).ok()?;
    run_digest(&row).map(|digest| digest.to_string())
}

/// The programs a live mutant run ran on, in the runner's order, each with its outcome and,
/// unless it agreed or distinguished, the cause the runner's evidence gives (`cached: false`).
fn executed_entries(mutant: &MutantRun, budget: Budget) -> Vec<Value> {
    mutant
        .plan
        .tests
        .iter()
        .filter_map(|test| {
            let evidence = mutant
                .evidence
                .iter()
                .find(|evidence| evidence.test_id == test.test_id)
                .map(|evidence| &evidence.run);
            let cause = executed_cause(&test.run, evidence, budget);
            match &test.run {
                TestRun::SkippedAfterKill => None,
                TestRun::Compared(outcomes) => Some(json!({
                    "program": test.test_id,
                    "outcome": compared_outcome(outcomes),
                    "slots": outcomes.iter().map(|o| slot_name(*o)).collect::<Vec<_>>(),
                    "cause": cause,
                    "cached": false,
                })),
                TestRun::Failed(kind) => Some(json!({
                    "program": test.test_id,
                    "outcome": status_name(kind.status()),
                    "failure": kebab(&format!("{kind:?}")),
                    "cause": cause,
                    "cached": false,
                })),
            }
        })
        .collect()
}

/// The executed entry's `outcome` label of a test run.
fn run_label(run: &TestRun) -> &'static str {
    match run {
        TestRun::Compared(outcomes) => compared_outcome(outcomes),
        TestRun::Failed(kind) => status_name(kind.status()),
        TestRun::SkippedAfterKill => "skipped",
    }
}

/// A label for a compared program's slot outcomes (for the reader; the status is the
/// runner's): `distinguish` if a slot distinguished, `agree` if every slot agreed, else the
/// first inconclusive slot's outcome.
fn compared_outcome(outcomes: &[OracleOutcome]) -> &'static str {
    if outcomes.contains(&OracleOutcome::Distinguish) {
        "distinguish"
    } else {
        outcomes
            .iter()
            .find(|outcome| **outcome != OracleOutcome::Agree)
            .map_or("agree", |outcome| slot_name(*outcome))
    }
}

/// `kink-flow run`: the run document and whether the command found no corpus or
/// infrastructure error (the caller's exit status). Survivors, timeouts and invalid mutations
/// are results, not errors.
pub fn run(manifest: &FlowManifest, list: &MutationList, options: &RunOptions) -> (Value, bool) {
    run_with(manifest, list, options, RunMode::Search)
}

/// `kink-flow run` (mode [`RunMode::Search`]) or `kink-flow run --verify` (mode
/// [`RunMode::Verify`]).
pub fn run_with(
    manifest: &FlowManifest,
    list: &MutationList,
    options: &RunOptions,
    mode: RunMode,
) -> (Value, bool) {
    let cache = cache_directory(manifest, options.cache.as_deref());
    let store = Store::new(&cache);
    let report_path = cache.join(REPORT_FILE);
    // A run that admits no specification still replaces the report, so `report` always prints
    // the last run's document.
    let refused = |record: &AdmissionRecord| {
        let document = document(record, None, &[], Vec::new(), None, Accounting::NONE);
        let _ = store.write_json(&report_path, &document);
        (document, false)
    };
    let (mut record, admitted) = admit_spec(manifest);
    let Some((spec, mut inputs)) = admitted else {
        return refused(&record);
    };
    let runner = match BaselineRunner::new(&spec, manifest) {
        Ok(runner) => runner,
        Err(e) => {
            record.refusal = Some(runner_refusal(e));
            return refused(&record);
        }
    };
    let verify = mode == RunMode::Verify;
    let mut update = update_results(&spec, manifest, &mut inputs, &runner, &cache, verify);
    let hints = Hints::read(&cache);
    if !verify {
        // F-05 review 1 minor 1 (README 7.5.7): a timeout record is host-dependent, so a
        // program a hint names is re-run once when its record says timeout. A record this
        // command just computed is already this command's live run, which the baseline session
        // would return again (F-12): only a record read from the cache is re-run.
        let named = hints
            .program_digests()
            .into_iter()
            .map(str::to_owned)
            .collect::<BTreeSet<_>>();
        for (index, program) in manifest.programs.iter().enumerate() {
            let row = &update.rows[index];
            if row.class() == Some(ResultClass::Timeout.as_str())
                && row.row["cached"] == true
                && row
                    .digest
                    .is_some_and(|digest| named.contains(&digest.to_string()))
            {
                update.rows[index] =
                    rerun_timeout_record(&spec, manifest, &mut inputs, &runner, &cache, program);
            }
        }
    }
    let mut ok = update.ok();
    let (tier1, tier1_reason) = match kink_build_identity() {
        Ok(build) => (
            Some(OutcomeStore::new(
                &cache,
                outcome_context(
                    build,
                    execution_digest(manifest, &spec.loaded),
                    manifest.budget,
                ),
            )),
            None,
        ),
        Err(e) => (
            None,
            Some(format!(
                "tier 1 is disabled: kink's build identity is unknown ({e}); every mutation runs \
                 live"
            )),
        ),
    };
    let candidates = manifest
        .programs
        .iter()
        .zip(&update.rows)
        .enumerate()
        .filter_map(|(index, (program, row))| candidate(index, &program.id, row))
        .collect::<Vec<_>>();
    let program_rows = update
        .rows
        .iter()
        .map(|row| row.row.clone())
        .collect::<Vec<_>>();
    let mut search = Search {
        spec: &spec,
        manifest,
        inputs: &mut inputs,
        runner: &runner,
        rows: &update.rows,
        tests: vec![None; candidates.len()],
        candidates,
        mode,
        tier1,
        hints,
        store: Store::new(&cache),
        stats: Stats::default(),
        mismatches: Vec::new(),
    };
    let outcome_cache = |search: &Search<'_>| {
        json!({
            "context_sha256": search.tier1.as_ref().map(OutcomeStore::context_sha256),
            "enabled": search.tier1.is_some() && !verify,
            "verify": verify,
            "reason": if verify {
                Some("run --verify decides nothing from the outcome cache: it re-proves every \
                      valid record and writes none".to_owned())
            } else {
                tier1_reason.clone()
            },
            "mutations_from_cache": search.stats.mutations_from_cache,
            "programs_from_cache": search.stats.programs_from_cache,
            "records_written": search.stats.records_written,
        })
    };
    let mut rows = Vec::new();
    let mut stopped = None;
    let selected = list
        .mutations
        .iter()
        .filter(|mutation| options.only.is_empty() || options.only.contains(&mutation.id));
    // The document as last written to the report file, if it was.
    let mut written = None;
    for mutation in selected {
        let (mut row, corpus_error) = search.search_one(mutation);
        if corpus_error {
            stopped = Some(json!({"mutation": mutation.id, "reason": row["reason"]}));
            ok = false;
        }
        // The hints are written after every mutation, a corpus error included (F-05 review 1
        // minor 3); `--verify` writes none.
        if !verify && let Err(e) = search.hints.write(&store) {
            row["cache_error"] = json!(format!("cannot write the hints: {e}"));
        }
        if row.get("cache_error").is_some()
            || (row["status"] == "error" && row["reason"] == "no-comparable-program")
        {
            ok = false;
        }
        rows.push(row);
        let document = document(
            &record,
            Some(update.spec_digest),
            &program_rows,
            rows.clone(),
            stopped.clone(),
            Accounting {
                outcome_cache: outcome_cache(&search),
                mismatches: &search.mismatches,
                baseline_runs: runner.baseline_runs(),
            },
        );
        match store.write_json(&report_path, &document) {
            Ok(()) => written = Some(document),
            Err(e) => {
                if let Some(last) = rows.last_mut() {
                    last["cache_error"] = json!(format!("cannot write the report: {e}"));
                }
                ok = false;
            }
        }
        if stopped.is_some() {
            break;
        }
    }
    if !search.mismatches.is_empty() {
        ok = false;
    }
    let document = document(
        &record,
        Some(update.spec_digest),
        &program_rows,
        rows,
        stopped,
        Accounting {
            outcome_cache: outcome_cache(&search),
            mismatches: &search.mismatches,
            baseline_runs: runner.baseline_runs(),
        },
    );
    // The stored report is the document the command prints: write it unless the last write
    // already stored exactly this document (no mutation was selected, or a write failed).
    if written.as_ref() != Some(&document) && store.write_json(&report_path, &document).is_err() {
        ok = false;
    }
    (document, ok)
}

/// The row of a mutation that does not resolve (or whose patch kink-patch refuses).
fn invalid(mut row: Map<String, Value>, invalid: InvalidMutation, digest: Value) -> Value {
    row.insert("digest".into(), digest);
    row.insert("status".into(), json!(INVALID_MUTATION));
    row.insert("reason".into(), json!(invalid.reason.as_str()));
    row.insert("edit".into(), json!(invalid.edit));
    row.insert("detail".into(), json!(invalid.detail));
    row.insert("rules".into(), Value::Null);
    finish(row, None, None, Vec::new(), Vec::new())
}

/// The row of a verdict: the report's status, its first killing program as the killer, the
/// killer's source, the deciding call's mutant-scope failure as the reason.
fn verdict_row(
    mut row: Map<String, Value>,
    report: &MutantReport,
    reason: Option<String>,
    source: Option<&str>,
    calls: Vec<Value>,
    executed: Vec<Value>,
) -> Value {
    row.insert("status".into(), json!(status_name(report.status)));
    row.insert("reason".into(), json!(reason));
    let killer = (report.status == MutantStatus::Killed)
        .then(|| report.killing_test_ids.first().cloned())
        .flatten();
    if killer.is_some() {
        row.insert("rules".into(), Value::Null);
    }
    let source = killer.as_ref().and(source);
    finish(row, killer, source, calls, executed)
}

/// Complete a mutation row: killer, killer_source, killer_from_cache, executed, calls and the
/// survivor report's action (`rules` is null unless the mutation resolved and was not killed).
fn finish(
    mut row: Map<String, Value>,
    killer: Option<String>,
    source: Option<&str>,
    calls: Vec<Value>,
    executed: Vec<Value>,
) -> Value {
    row.entry("reason").or_insert(Value::Null);
    row.entry("reaching").or_insert_with(|| json!([]));
    row.entry("rules").or_insert(Value::Null);
    row.entry("identity").or_insert(Value::Null);
    row.entry("unusable_killer").or_insert(Value::Null);
    let action = action(
        row["status"].as_str().unwrap_or_default(),
        row["reason"].as_str(),
    );
    row.insert("action".into(), json!(action));
    row.insert("killer".into(), json!(killer));
    row.insert("killer_source".into(), json!(source));
    row.insert(
        "killer_from_cache".into(),
        json!(matches!(
            source,
            Some(SOURCE_OUTCOME_CACHE) | Some(SOURCE_HINT)
        )),
    );
    row.insert("executed".into(), json!(executed));
    row.insert("calls".into(), json!(calls));
    Value::Object(row)
}

fn reaches(candidate: &Candidate<'_>, resolved: &ResolvedMutation) -> bool {
    resolved.rules.iter().any(|rule| {
        candidate
            .reaches
            .contains(&(rule.at.module.clone(), u64::from(rule.at.index)))
    })
}

/// The chosen order O (README 5.6 step 2): the comparable programs whose cached coverage
/// reaches an edited rule, in corpus order, then the rest, in corpus order.
fn order(candidates: &[Candidate<'_>], resolved: &ResolvedMutation) -> Vec<usize> {
    let mut order = Vec::with_capacity(candidates.len());
    for first in [true, false] {
        order.extend(
            candidates
                .iter()
                .enumerate()
                .filter(|(_, c)| reaches(c, resolved) == first)
                .map(|(index, _)| index),
        );
    }
    order
}

/// The run document's accounting of the command's caches: `outcome_cache`, `mismatches` and
/// `baseline_runs` (outside every digest and key).
struct Accounting<'m> {
    outcome_cache: Value,
    mismatches: &'m [Value],
    baseline_runs: Value,
}

impl Accounting<'_> {
    const NONE: Accounting<'static> = Accounting {
        outcome_cache: Value::Null,
        mismatches: &[],
        baseline_runs: Value::Null,
    };
}

fn document(
    record: &AdmissionRecord,
    digest: Option<Sha256Digest>,
    programs: &[Value],
    mutations: Vec<Value>,
    stopped: Option<Value>,
    accounting: Accounting<'_>,
) -> Value {
    let refusal = record.refusal.as_ref();
    let survivors = survivors(&mutations);
    let counts = STATUSES
        .iter()
        .map(|status| {
            (
                (*status).to_owned(),
                json!(mutations.iter().filter(|m| m["status"] == *status).count()),
            )
        })
        .collect::<Map<_, _>>();
    json!({
        "schema": RUN_SCHEMA,
        "version": RUN_VERSION,
        "k_rust_revision": K_RUST_REVISION,
        "profile": SolverProfile::BUILD.name(),
        "result_schema_version": RESULT_SCHEMA_VERSION,
        "spec": {
            "outcome": if refusal.is_some() { "refused" } else { "admitted" },
            "stage": refusal.map(|r| &r.stage),
            "reason": refusal.map(|r| &r.reason),
            "detail": refusal.map(|r| &r.detail),
            "digest": digest.map(|d| d.to_string()),
            "files": record
                .files
                .iter()
                .map(|f| json!({"name": f.name, "sha256": f.sha256.to_string()}))
                .collect::<Vec<_>>(),
        },
        "programs": programs,
        "unusable_programs": unusable_programs(programs),
        "mutations": mutations,
        "counts": counts,
        "survivors": survivors,
        "stopped": stopped,
        "outcome_cache": accounting.outcome_cache,
        "mismatches": accounting.mismatches,
        "baseline_runs": accounting.baseline_runs,
    })
}

/// The run document of a mutation list that does not decode.
pub fn mutation_list_refused(detail: &str) -> Value {
    json!({
        "schema": RUN_SCHEMA,
        "version": RUN_VERSION,
        "k_rust_revision": K_RUST_REVISION,
        "profile": SolverProfile::BUILD.name(),
        "mutation_list": {"outcome": "refused", "detail": detail},
    })
}

/// The path of the run document of the cache `cache` (or the manifest's default cache).
pub fn report_path(manifest: &FlowManifest, cache: Option<&Path>) -> PathBuf {
    cache_directory(manifest, cache).join(REPORT_FILE)
}
