//! The kill search with its killer cache (flow README 5.4 and 5.6): `kink-flow run`.
//!
//! One command admits the specification once and uses its one `NativeValidator` for the
//! result cache update and for every mutation. Per mutation, in the list's order:
//!
//! 1. Resolve it into one pinned patch (F-04); an `invalid-mutation` ends there.
//! 2. Choose the programs: the comparable programs of the up-to-date result cache, the ones
//!    whose cached coverage reaches an edited rule first, then the rest, each group in corpus
//!    order.
//! 3. If the killer cache names a killer for the mutation that is still a comparable program
//!    with the same digest, one campaign call runs that program alone. If it kills, that is
//!    the verdict. Otherwise the entry is removed and a second call runs every chosen program
//!    in the order of step 2, exactly the call a run without the entry makes, so a stale or
//!    wrong entry costs runs but never changes a verdict.
//! 4. Every verdict is the status `kink_campaign::run_campaign_multi` derives for the
//!    mutant, with schedule `FirstKill`, no coverage selection, and `Campaign.tests` in the
//!    chosen order (the runner then runs the mutant on them in that order). kink-flow compares
//!    no terms: only the runner's proved `Distinguish` kills.
//! 5. After every call, each program's baseline row from that call is compared, by run
//!    digest, with its cached record. Any difference is a corpus error: the mutation gets the
//!    status `error` with reason `baseline-mismatch:<program id>`, nothing is written to the
//!    killer cache for it, and the run stops.
//! 6. A `Killed` status writes its first killing test as the mutation's killer; every other
//!    status removes the entry. The killer cache and the report are written after every
//!    mutation.

use crate::{
    admit::{AdmittedSpec, ProgramInputs, admit_spec},
    killers::{KillerCache, KillerEntry},
    manifest::{Budget, FlowManifest},
    mutation::{InvalidMutation, Mutation, MutationList, ResolvedMutation, resolve},
    report::{
        RUN_SCHEMA, RUN_VERSION, action, executed_cause, rules_value, survivors, unusable_programs,
    },
    results::{
        BaselineRunner, ProgramRow, RESULT_SCHEMA_VERSION, ResultClass, cache_directory,
        execution_budget, fixed_oracles, kebab, run_digest, runner_refusal, update_results,
    },
};
use kink_campaign::{
    Campaign, CampaignOptions, CampaignReport, MutantRun, MutantStatus, OracleOutcome,
    ScheduleMode, TestCase, TestRun, run_campaign_multi,
};
use kink_corpus::{Store, admission::AdmissionRecord, runner::all_normal};
use kink_native::{K_RUST_REVISION, execution::SolverProfile};
use kink_patch::{CandidateGeneration, Sha256Digest};
use serde_json::{Map, Value, json};
use std::{
    collections::BTreeSet,
    path::{Path, PathBuf},
};

/// The run document's file in the cache directory, rewritten after every mutation.
pub const REPORT_FILE: &str = "report.json";

/// The status of a mutation that does not resolve to a patch (README 5.5).
pub const INVALID_MUTATION: &str = "invalid-mutation";

/// Every status a mutation can have, in the order the counts list them: the runner's
/// mutant statuses, then the flow's own `invalid-mutation`. `error` is also the status of a
/// corpus error (its reason says which).
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

const fn outcome_name(outcome: OracleOutcome) -> &'static str {
    match outcome {
        OracleOutcome::Agree => "agree",
        OracleOutcome::Distinguish => "distinguish",
        OracleOutcome::Incomparable => "incomparable",
        OracleOutcome::Timeout => "timeout",
        OracleOutcome::Unknown => "unknown",
        OracleOutcome::Error => "error",
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

/// What one campaign call produced, after the baseline drift check.
enum Call {
    /// The runner's verdict for the mutant.
    Verdict {
        status: MutantStatus,
        killing: Vec<String>,
        executed: Vec<Value>,
        reason: Option<String>,
    },
    /// A corpus error: no verdict, and the run stops.
    CorpusError { reason: String, detail: String },
}

/// The command's state: the admitted specification, its one validator, the corpus.
struct Search<'a> {
    spec: &'a AdmittedSpec,
    manifest: &'a FlowManifest,
    inputs: &'a mut ProgramInputs,
    module: String,
    rows: &'a [ProgramRow],
    candidates: Vec<Candidate<'a>>,
    /// Each candidate's test case with the fixed oracles, assembled on first use.
    tests: Vec<Option<TestCase>>,
}

impl Search<'_> {
    fn test(&mut self, candidate: usize) -> Result<TestCase, (String, String)> {
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
                .map_err(|refusal| {
                    (
                        format!("program-refused:{}", program.id),
                        format!("{}/{}: {}", refusal.stage, refusal.reason, refusal.detail),
                    )
                })?,
            (None, None) => {
                return Err((
                    format!("program-refused:{}", program.id),
                    "the program has a comparable record but no text".into(),
                ));
            }
        };
        test.oracles = fixed_oracles();
        self.tests[candidate] = Some(test.clone());
        Ok(test)
    }

    /// One campaign call over `order` (candidate indices), then the drift check.
    fn call(&mut self, generation: &CandidateGeneration<'_>, order: &[usize]) -> Call {
        let mut tests = Vec::with_capacity(order.len());
        for &candidate in order {
            match self.test(candidate) {
                Ok(test) => tests.push(test),
                Err((reason, detail)) => return Call::CorpusError { reason, detail },
            }
        }
        let campaign = Campaign {
            validator: &self.spec.validator,
            module: &self.module,
            observation: &[],
            classify: &all_normal,
            tests: &tests,
            budget: execution_budget(self.manifest.budget),
        };
        let options = CampaignOptions {
            schedule: ScheduleMode::FirstKill,
            selection: kink_campaign::SelectionPolicy::None,
            share_evidence: false,
        };
        let run = match run_campaign_multi(&campaign, std::slice::from_ref(generation), &options) {
            Ok(run) => run,
            Err(failure) => {
                return Call::CorpusError {
                    reason: "campaign-refused".into(),
                    detail: format!(
                        "the campaign runner refused the call over {:?}: {failure}; the cached \
                         results no longer describe the baseline runs: run `kink-flow results \
                         --verify`",
                        self.ids(order)
                    ),
                };
            }
        };
        // The drift check (README 5.4): every program's baseline row of this call must have
        // its cached record's run digest.
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
                mismatched.push(format!(
                    "{}: cached run_sha256 {}, now {}",
                    candidate.id,
                    candidate.run_sha256.unwrap_or("null"),
                    now.as_deref().unwrap_or("no baseline row"),
                ));
            }
        }
        if run.baseline.len() != order.len() {
            mismatched.push(format!(
                "the call ran {} baseline programs for {} tests",
                run.baseline.len(),
                order.len()
            ));
        }
        if let Some(first) = mismatched.first() {
            let program = first.split(':').next().unwrap_or_default().to_owned();
            return Call::CorpusError {
                reason: format!("baseline-mismatch:{program}"),
                detail: format!(
                    "{}; run `kink-flow results --verify`",
                    mismatched.join("; ")
                ),
            };
        }
        let [mutant] = run.mutants.as_slice() else {
            return Call::CorpusError {
                reason: "campaign-refused".into(),
                detail: format!("the runner returned {} mutants for one", run.mutants.len()),
            };
        };
        verdict(mutant, self.manifest.budget)
    }

    fn ids(&self, order: &[usize]) -> Vec<&str> {
        order.iter().map(|&c| self.candidates[c].id).collect()
    }

    /// The `calls` of a mutation row: the programs each campaign call ran, and its status.
    fn calls(&self, calls: &[(Vec<usize>, Value)]) -> Vec<Value> {
        calls
            .iter()
            .map(|(order, status)| json!({"programs": self.ids(order), "status": status}))
            .collect()
    }
}

/// The runner's verdict and the programs the mutant ran on, in the runner's order, each with
/// its outcome and, unless it agreed or distinguished, the cause the runner's evidence gives.
fn verdict(mutant: &MutantRun, budget: Budget) -> Call {
    let executed = mutant
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
                    "slots": outcomes.iter().map(|o| outcome_name(*o)).collect::<Vec<_>>(),
                    "cause": cause,
                })),
                TestRun::Failed(kind) => Some(json!({
                    "program": test.test_id,
                    "outcome": status_name(kind.status()),
                    "failure": kebab(&format!("{kind:?}")),
                    "cause": cause,
                })),
            }
        })
        .collect();
    Call::Verdict {
        status: mutant.report.status,
        killing: mutant.report.killing_test_ids.clone(),
        executed,
        reason: mutant
            .plan
            .mutant_failure
            .map(|failure| kebab(&format!("{failure:?}"))),
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
            .map_or("agree", |outcome| outcome_name(*outcome))
    }
}

/// `kink-flow run`: the run document and whether the command found no corpus or
/// infrastructure error (the caller's exit status). Survivors, timeouts and invalid mutations
/// are results, not errors.
pub fn run(manifest: &FlowManifest, list: &MutationList, options: &RunOptions) -> (Value, bool) {
    let cache = cache_directory(manifest, options.cache.as_deref());
    let store = Store::new(&cache);
    let report_path = cache.join(REPORT_FILE);
    // A run that admits no specification still replaces the report, so `report` always prints
    // the last run's document.
    let refused = |record: &AdmissionRecord| {
        let document = document(record, None, &[], Vec::new(), None);
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
    let update = update_results(&spec, manifest, &mut inputs, &runner, &cache, false);
    let mut ok = update.ok();
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
        module: k_rust::kast::identifier::encode(&manifest.spec.main_module),
        rows: &update.rows,
        tests: vec![None; candidates.len()],
        candidates,
    };
    let mut killers = KillerCache::read(&cache, update.spec_digest);
    let mut rows = Vec::new();
    let mut stopped = None;
    let selected = list
        .mutations
        .iter()
        .filter(|mutation| options.only.is_empty() || options.only.contains(&mutation.id));
    // The document as last written to the report file, if it was.
    let mut written = None;
    for mutation in selected {
        let (mut row, corpus_error) = search_one(&mut search, &mut killers, mutation);
        if corpus_error {
            stopped = Some(json!({"mutation": mutation.id, "reason": row["reason"]}));
            ok = false;
        } else if let Err(e) = killers.write(&store) {
            row["cache_error"] = json!(format!("cannot write the killer cache: {e}"));
            ok = false;
        }
        if row["status"] == "error" && row["reason"] == "no-comparable-program" {
            ok = false;
        }
        rows.push(row);
        let document = document(
            &record,
            Some(update.spec_digest),
            &program_rows,
            rows.clone(),
            stopped.clone(),
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
    let document = document(
        &record,
        Some(update.spec_digest),
        &program_rows,
        rows,
        stopped,
    );
    // The stored report is the document the command prints: write it unless the last write
    // already stored exactly this document (no mutation was selected, or a write failed).
    if written.as_ref() != Some(&document) && store.write_json(&report_path, &document).is_err() {
        ok = false;
    }
    (document, ok)
}

/// The kill search for one mutation: its row of the run document, and whether it ended in
/// a corpus error (the run then stops, and the killer cache is not written for it).
fn search_one(
    search: &mut Search<'_>,
    killers: &mut KillerCache,
    mutation: &Mutation,
) -> (Value, bool) {
    let mut row = Map::new();
    row.insert("id".into(), json!(mutation.id));
    row.insert("note".into(), json!(mutation.note));
    let invalid = |mut row: Map<String, Value>, invalid: InvalidMutation, digest: Value| {
        row.insert("digest".into(), digest);
        row.insert("status".into(), json!(INVALID_MUTATION));
        row.insert("reason".into(), json!(invalid.reason.as_str()));
        row.insert("edit".into(), json!(invalid.edit));
        row.insert("detail".into(), json!(invalid.detail));
        row.insert("rules".into(), Value::Null);
        finish(row, None, false, Vec::new(), Vec::new())
    };
    let resolved = match resolve(search.manifest, &search.spec.loaded, mutation) {
        Ok(resolved) => resolved,
        Err(e) => return (invalid(row, e, Value::Null), false),
    };
    let digest = resolved.digest;
    row.insert("digest".into(), json!(digest.to_string()));
    // The survivor report's rule texts (README 5.7); a killed mutation drops them below.
    row.insert("rules".into(), rules_value(&resolved));
    // The generation must derive from the validator's own baseline (the runner refuses any
    // other); the patch is pinned, so it applies to it as to the loaded baseline.
    let generation = match resolved.generation(search.spec.validator.baseline()) {
        Ok(generation) => generation,
        Err(e) => return (invalid(row, e, json!(digest.to_string())), false),
    };
    let order = order(&search.candidates, &resolved);
    let reaching = order
        .iter()
        .filter(|&&c| reaches(&search.candidates[c], &resolved))
        .map(|&c| search.candidates[c].id.to_owned())
        .collect::<Vec<_>>();
    row.insert("reaching".into(), json!(reaching));
    let cached = killers.get(digest).cloned();
    let killer = cached.as_ref().and_then(|entry| {
        search
            .candidates
            .iter()
            .position(|c| c.id == entry.program_id && c.digest.to_string() == entry.program_digest)
    });
    if let (Some(entry), None) = (&cached, killer) {
        row.insert(
            "stale_killer".into(),
            json!(format!(
                "the cached killer {} is no longer a comparable program with digest {}; \
                 the entry is removed",
                entry.program_id, entry.program_digest
            )),
        );
        killers.remove(digest);
    }
    if order.is_empty() {
        row.insert("status".into(), json!("error"));
        row.insert("reason".into(), json!("no-comparable-program"));
        row.insert(
            "detail".into(),
            json!("no program of the corpus has a comparable result, so nothing can kill"),
        );
        killers.remove(digest);
        return (finish(row, None, false, Vec::new(), Vec::new()), false);
    }
    let mut calls = Vec::new();
    let mut executed = Vec::new();
    let mut from_cache = false;
    let mut outcome = None;
    if let Some(killer) = killer {
        let call = search.call(&generation, &[killer]);
        let killed = matches!(
            &call,
            Call::Verdict {
                status: MutantStatus::Killed,
                ..
            }
        );
        calls.push((vec![killer], call_status(&call)));
        match call {
            Call::CorpusError { reason, detail } => {
                return corpus_error(row, reason, detail, search, &calls, executed);
            }
            Call::Verdict {
                executed: ran,
                status,
                killing,
                reason,
            } => {
                executed.extend(ran);
                if killed {
                    from_cache = true;
                    outcome = Some((status, killing, reason));
                } else {
                    killers.remove(digest);
                }
            }
        }
    }
    if outcome.is_none() {
        let call = search.call(&generation, &order);
        calls.push((order.clone(), call_status(&call)));
        match call {
            Call::CorpusError { reason, detail } => {
                return corpus_error(row, reason, detail, search, &calls, executed);
            }
            Call::Verdict {
                executed: ran,
                status,
                killing,
                reason,
            } => {
                executed.extend(ran);
                outcome = Some((status, killing, reason));
            }
        }
    }
    let (status, killing, reason) = outcome.expect("a verdict");
    row.insert("status".into(), json!(status_name(status)));
    row.insert("reason".into(), json!(reason));
    if status == MutantStatus::Killed {
        row.insert("rules".into(), Value::Null);
    }
    // Only a Killed status writes an entry, and only its first killing test (README 5.6 step
    // 5); every other status removes the mutation's entry.
    let killer = match (status, killing.first()) {
        (MutantStatus::Killed, Some(program)) => {
            let candidate = search
                .candidates
                .iter()
                .find(|c| c.id == program)
                .expect("a killing test is a chosen program");
            killers.insert(
                digest,
                KillerEntry {
                    mutation_id: mutation.id.clone(),
                    program_id: program.clone(),
                    program_digest: candidate.digest.to_string(),
                },
            );
            Some(program.clone())
        }
        _ => {
            killers.remove(digest);
            None
        }
    };
    let calls = search.calls(&calls);
    (finish(row, killer, from_cache, calls, executed), false)
}

fn call_status(call: &Call) -> Value {
    match call {
        Call::Verdict { status, .. } => json!(status_name(*status)),
        Call::CorpusError { .. } => json!("error"),
    }
}

fn corpus_error(
    mut row: Map<String, Value>,
    reason: String,
    detail: String,
    search: &Search<'_>,
    calls: &[(Vec<usize>, Value)],
    executed: Vec<Value>,
) -> (Value, bool) {
    row.insert("status".into(), json!("error"));
    row.insert("reason".into(), json!(reason));
    row.insert("detail".into(), json!(detail));
    (
        finish(row, None, false, search.calls(calls), executed),
        true,
    )
}

/// Complete a mutation row: killer, killer_from_cache, executed, calls and the survivor
/// report's action (`rules` is null unless the mutation resolved and was not killed).
fn finish(
    mut row: Map<String, Value>,
    killer: Option<String>,
    from_cache: bool,
    calls: Vec<Value>,
    executed: Vec<Value>,
) -> Value {
    row.entry("reason").or_insert(Value::Null);
    row.entry("reaching").or_insert_with(|| json!([]));
    row.entry("rules").or_insert(Value::Null);
    let action = action(
        row["status"].as_str().unwrap_or_default(),
        row["reason"].as_str(),
    );
    row.insert("action".into(), json!(action));
    row.insert("killer".into(), json!(killer));
    row.insert("killer_from_cache".into(), json!(from_cache));
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

/// The chosen order (README 5.6 step 2, without the killer): the comparable programs whose
/// cached coverage reaches an edited rule, in corpus order, then the rest, in corpus order.
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

fn document(
    record: &AdmissionRecord,
    digest: Option<Sha256Digest>,
    programs: &[Value],
    mutations: Vec<Value>,
    stopped: Option<Value>,
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
