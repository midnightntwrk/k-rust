//! `kink-flow query FLOW.toml PATTERNS.toml` (flow F-18): the per-input pattern checks of
//! [`crate::pattern`], with a cache of their definitive answers.
//!
//! The command admits the specification, brings the result cache up to date (`results` without
//! `--verify`, or with it under `query --verify`), lowers every selected pattern once, and asks
//! each pattern of each program it names (its claimed programs, or the whole corpus): one
//! `search_pattern` per (pattern, program), unless a cached answer stands.
//!
//! **The cache** holds only `hit` and a final `no`, one record per (pattern, program):
//! `patterns/<spec digest>/<pattern digest>/<program digest>.json` in the cache directory, written
//! atomically, `{schema: "kink-flow-pattern", key, pattern_id, program_id, answer, witness,
//! baseline_run_sha256, record_sha256}`. The key ([`answer_key`]) names every input an answer
//! depends on: the record's schema, the lowering version, the k-rust revision, kink's build
//! (`kink_build`, the executable's SHA-256, so any rebuild starts a new key: packet CACHE-ID-fix-1)
//! and its semantics identity (`kink`), the specification digest (every source file, the load
//! options, the k-rust revision and the profile), the program digest (its bytes, start sort and
//! variables), the pattern's digest (its KORE target and generated variables), the budget, and the
//! search's modality (search type all, state set, at most one result). A record is used only when
//! its key is exactly the current one and its `record_sha256` recomputes; a `no` also only while
//! the program's current result record is comparable with the baseline run digest the `no` was
//! given against. A used record's answer is judged again with the current command's facts (the
//! definition exclusions of this command's load, the initial state's exclusion, the baseline
//! class, the profile), so a record never answers more than a live search would.
//!
//! **Trust.** A cached answer stands without a search in this command. It rests on the integrity
//! of the cache directory (whoever can write it can forge an answer, as for every kink cache) and
//! on the key naming every input; it does not rest on k-rust's determinism: a `hit` and a final
//! `no` are facts about the definition and the program, which a later search can only fail to
//! re-derive (an unknown), never contradict. `--verify` re-derives every answer of the selected
//! patterns live, compares it with each stored record a command without `--verify` would use,
//! reports every difference (`mismatches`: `{pattern, program, record, cached, live}`) and exits 1
//! on one; it writes no pattern record. Each live answer is judged with the program's live
//! baseline run (`ProgramRow::live`), not with a stored result record `--verify` found different.
//! The cache is off under the Z3 profile, as tier 1 is, and when kink's build identity is unknown.
//!
//! No answer enters a result record, an outcome record, a hint or a run document: pattern answers
//! feed no kill and no mutation verdict.

use crate::{
    admit::admit_spec,
    digest::spec_digest,
    manifest::{FlowManifest, ManifestError},
    pattern::{
        Answer, Facts, INVALID_PATTERN, LOWERING_VERSION, LoweredPattern, Lowering, PatternList,
        SearchOutcome, Searcher, judge, search_modality,
    },
    results::{
        BaselineRunner, ProgramRow, ResultsUpdate, cache_directory, result_key, runner_refusal,
        update_results,
    },
    search::tier1_refusal,
};
use kink_corpus::{Store, admission::AdmissionRecord};
use kink_native::{K_RUST_REVISION, execution::SolverProfile};
use kink_patch::{Sha256Digest, canonical_json, parse_json, payload_digest};
use serde_json::{Map, Value, json};
use std::{
    fs,
    path::{Path, PathBuf},
};

/// The query document's schema and version.
pub const QUERY_SCHEMA: &str = "kink-flow-query";
pub const QUERY_VERSION: u64 = 1;
/// A cached answer's schema, and its key's `schema_version`.
pub const RECORD_SCHEMA: &str = "kink-flow-pattern";
/// The record's format and what its answers mean: it changes whenever what counts as a hit or a
/// no changes (v2, flow F-18 tail: a matched state holding a term-level `\and` is not a hit; v3,
/// fz26 KRUST-ANYWHERE-HEAD: a matched state is defined when k-rust's `ground_defined` holds,
/// which also accepts an irreducible `value-production` application such as SIMPLE's `a[4]`; v4,
/// KINK-R4: a match is no hit when the search left a hook application unevaluated, its
/// `unsupportedHooks` or `allowanceRefusals` list not empty, so a v3 `hit` may no longer be one;
/// an exploration with such a list is not complete, so a v3 `no` may no longer be one either; and
/// a `no` needs the definition to have data, its check complete as well as finding-free).
pub const ANSWER_SCHEMA_VERSION: &str = "kink-flow/pattern-answer/v4";
/// Domain of a record's digest.
pub const PATTERN_RECORD_DOMAIN: &str = "kink-flow/pattern-answer/v1";
/// The cache's directory in the cache directory.
pub const PATTERN_DIRECTORY: &str = "patterns";
/// Every answer a row can have, in the order `counts` lists them.
pub const ANSWERS: [&str; 5] = ["hit", "no", "unknown", INVALID_PATTERN, "error"];

/// Options of the `query` command.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct QueryOptions {
    /// The ids of the patterns to ask; empty asks every pattern.
    pub only: Vec<String>,
    /// Re-derive every answer and compare it with its stored record (module docs).
    pub verify: bool,
    /// The cache directory; default `<directory of FLOW.toml>/.kink-flow`.
    pub cache: Option<PathBuf>,
}

/// The key of a cached answer (module docs).
pub fn answer_key(
    build: Sha256Digest,
    spec: Sha256Digest,
    program: Sha256Digest,
    pattern: Sha256Digest,
    budget: crate::manifest::Budget,
) -> Value {
    json!({
        "schema_version": ANSWER_SCHEMA_VERSION,
        "lowering": LOWERING_VERSION,
        "k_rust_revision": K_RUST_REVISION,
        "kink_build": build.to_string(),
        "kink": kink_campaign::kink_identity(),
        "spec": spec.to_string(),
        "program": program.to_string(),
        "pattern": pattern.to_string(),
        // The result key's budget object, so both keys name the same bounds.
        "budget": result_key(spec, program, budget, Some(build))["budget"],
        "modality": search_modality(),
    })
}

/// Where the record of (`pattern`, `program`) is kept under the specification digest `spec`. The
/// key decides what a record may be used for; the path only finds it.
pub fn answer_path(
    cache: &Path,
    spec: Sha256Digest,
    pattern: Sha256Digest,
    program: Sha256Digest,
) -> PathBuf {
    cache
        .join(PATTERN_DIRECTORY)
        .join(spec.to_string())
        .join(pattern.to_string())
        .join(format!("{program}.json"))
}

/// The digest a record carries: of its key, answer, witness and baseline run digest.
pub fn record_sha256(
    key: &Value,
    answer: &str,
    witness: &Value,
    baseline_run_sha256: &Value,
) -> Sha256Digest {
    payload_digest(
        PATTERN_RECORD_DOMAIN,
        canonical_json(&json!({
            "key": key,
            "answer": answer,
            "witness": witness,
            "baseline_run_sha256": baseline_run_sha256,
        }))
        .as_bytes(),
    )
}

/// A stored answer that may be used (module docs): `(answer, witness, baseline_run_sha256)`.
struct Stored {
    answer: String,
    witness: Value,
    baseline_run_sha256: Value,
}

impl Stored {
    /// The search outcome the record stands for.
    fn outcome(&self) -> SearchOutcome {
        if self.answer == "hit" {
            SearchOutcome::Hit(self.witness.clone())
        } else {
            SearchOutcome::Complete
        }
    }
}

fn read_record(path: &Path, key: &Value) -> Option<Stored> {
    let record = parse_json(&fs::read_to_string(path).ok()?).ok()?;
    let answer = record["answer"].as_str()?.to_owned();
    let witness = record.get("witness")?.clone();
    let baseline = record.get("baseline_run_sha256")?.clone();
    let well_formed = match answer.as_str() {
        "hit" => witness.is_object() && baseline.is_null(),
        "no" => witness.is_null() && baseline.is_string(),
        _ => false,
    };
    (record["schema"] == RECORD_SCHEMA
        && record["key"] == *key
        && well_formed
        && record["record_sha256"].as_str()
            == Some(
                record_sha256(key, &answer, &witness, &baseline)
                    .to_string()
                    .as_str(),
            ))
    .then_some(Stored {
        answer,
        witness,
        baseline_run_sha256: baseline,
    })
}

/// Why the cache is off for this command, or `None`.
fn cache_refusal(build: Option<Sha256Digest>) -> Option<String> {
    if tier1_refusal(SolverProfile::BUILD).is_some() {
        return Some(
            "the pattern cache is off under the z3 profile, as tier 1 is: a solver query can time \
             out and k-rust reports no per-run signal that one did"
                .to_owned(),
        );
    }
    build.is_none().then(|| {
        "kink's build identity is unknown (the executable cannot be read): the pattern cache is \
         neither read nor written"
            .to_owned()
    })
}

/// `kink-flow query`: the query document and whether the command found no corpus or
/// infrastructure error (the caller's exit status).
pub fn query(manifest: &FlowManifest, list: &PatternList, options: &QueryOptions) -> (Value, bool) {
    query_with(manifest, list, options, &|_| {})
}

/// [`query`], with `adjust` applied to the definition exclusions of the searcher's load before
/// any answer is judged: the unit tests' seam for a load fact a test cannot provoke (a load
/// stack stop depends on the host's stack).
pub(crate) fn query_with(
    manifest: &FlowManifest,
    list: &PatternList,
    options: &QueryOptions,
    adjust: &dyn Fn(&mut kink_native::exclusion::DefinitionExclusions),
) -> (Value, bool) {
    if let Err(error) = list.check_programs(manifest) {
        return (pattern_list_refused(&error), false);
    }
    let (mut record, admitted) = admit_spec(manifest);
    let Some((spec, mut inputs)) = admitted else {
        return (refused_document(&record), false);
    };
    let cache = cache_directory(manifest, options.cache.as_deref());
    let runner = match BaselineRunner::new(&spec, manifest) {
        Ok(runner) => runner,
        Err(e) => {
            record.refusal = Some(runner_refusal(e));
            return (refused_document(&record), false);
        }
    };
    let update = update_results(
        &spec,
        manifest,
        &mut inputs,
        &runner,
        &cache,
        options.verify,
    );
    let mut ok = update.ok();
    let setup =
        Searcher::new(&spec, &manifest.spec.main_module, manifest.budget).and_then(|searcher| {
            Lowering::new(&spec, &manifest.spec.main_module).map(|lowering| (searcher, lowering))
        });
    let (mut searcher, lowering) = match setup {
        Ok(setup) => setup,
        Err(detail) => {
            record.refusal = Some(kink_corpus::admission::AdmissionRefusal {
                stage: "query".into(),
                reason: "search-backend".into(),
                detail,
            });
            return (refused_document(&record), false);
        }
    };
    let mut exclusions = searcher.exclusions().clone();
    adjust(&mut exclusions);
    let build = kink_campaign::kink_build().ok();
    let refusal = cache_refusal(build);
    let cache_build = build.filter(|_| refusal.is_none());
    let store = Store::new(&cache);
    let spec_digest = spec_digest(manifest, &spec.loaded.files);
    let mut mismatches = update.mismatches.clone();
    let mut accounting = json!({"from_cache": 0, "records_written": 0});
    let mut patterns = Vec::new();
    let mut rows = Vec::new();
    for entry in list
        .patterns
        .iter()
        .filter(|entry| options.only.is_empty() || options.only.contains(&entry.id))
    {
        let lowered = lowering.lower(&entry.pattern, searcher.definition());
        let asked: Vec<&str> = match &entry.programs {
            Some(claimed) => claimed.iter().map(String::as_str).collect(),
            None => manifest.programs.iter().map(|p| p.id.as_str()).collect(),
        };
        let claimed = entry.programs.is_some();
        patterns.push(json!({
            "id": entry.id,
            "note": entry.note,
            "pattern": entry.pattern,
            "outcome": if lowered.is_ok() { "valid" } else { INVALID_PATTERN },
            "detail": lowered.as_ref().err(),
            "digest": lowered.as_ref().ok().map(|l| l.digest.to_string()),
            "kore": lowered.as_ref().ok().map(LoweredPattern::kore),
            "asked": if claimed { "claimed" } else { "corpus" },
        }));
        for program_id in asked {
            let index = manifest
                .programs
                .iter()
                .position(|p| p.id == program_id)
                .expect("check_programs: every claimed program exists");
            let mut row = Map::new();
            row.insert("pattern".into(), json!(entry.id));
            row.insert("program".into(), json!(program_id));
            row.insert("claimed".into(), json!(claimed));
            let lowered = match &lowered {
                Ok(lowered) => lowered,
                Err(detail) => {
                    let answer = Answer {
                        answer: INVALID_PATTERN,
                        cause: Some(detail.clone()),
                        witness: None,
                    };
                    rows.push(finish_row(row, &answer, false, None, claimed));
                    continue;
                }
            };
            let context = Context {
                manifest,
                update: &update,
                cache: &cache,
                store: &store,
                build: cache_build,
                spec: spec_digest,
                verify: options.verify,
                exclusions: &exclusions,
            };
            let (row, row_ok) = ask(
                &context,
                &mut inputs,
                &spec,
                &mut searcher,
                index,
                &entry.id,
                lowered,
                row,
                claimed,
                &mut mismatches,
                &mut accounting,
            );
            ok &= row_ok;
            rows.push(row);
        }
    }
    ok &= mismatches.is_empty();
    let pattern_cache = json!({
        "enabled": refusal.is_none(),
        "reason": refusal,
        "verify": options.verify,
        "from_cache": accounting["from_cache"],
        "records_written": accounting["records_written"],
    });
    let programs = crate::results::data_marked(
        update.rows.iter().map(|row| row.row.clone()).collect(),
        &spec.data,
    );
    let mut document = document(
        &record,
        Some(spec_digest),
        programs,
        patterns,
        rows,
        mismatches,
        pattern_cache,
        runner.baseline_runs(),
    );
    document["data"] = spec.data.value();
    (document, ok)
}

struct Context<'a> {
    manifest: &'a FlowManifest,
    update: &'a ResultsUpdate,
    cache: &'a Path,
    store: &'a Store,
    /// kink's build when the cache is on.
    build: Option<Sha256Digest>,
    spec: Sha256Digest,
    verify: bool,
    /// The definition exclusions of the searcher's load.
    exclusions: &'a kink_native::exclusion::DefinitionExclusions,
}

/// One (pattern, program) row and whether it found no error.
#[allow(clippy::too_many_arguments)]
fn ask(
    context: &Context<'_>,
    inputs: &mut crate::admit::ProgramInputs,
    spec: &crate::admit::AdmittedSpec,
    searcher: &mut Searcher,
    index: usize,
    pattern_id: &str,
    lowered: &LoweredPattern,
    row: Map<String, Value>,
    claimed: bool,
    mismatches: &mut Vec<Value>,
    accounting: &mut Value,
) -> (Value, bool) {
    let program = &context.manifest.programs[index];
    let result: &ProgramRow = &context.update.rows[index];
    let (Some(digest), Some(text)) = (result.digest, result.text.clone()) else {
        let answer = Answer::error(format!(
            "the program is not admitted: {}",
            result.row["cause"]
                .as_str()
                .unwrap_or("its text cannot be read")
        ));
        return (finish_row(row, &answer, false, None, claimed), false);
    };
    let test = match &result.test {
        Some(test) => test.clone(),
        None => match inputs.test_case(spec, program, text) {
            Ok(test) => test,
            Err(refusal) => {
                let answer = Answer::error(format!(
                    "the program is not admitted: {}/{}: {}",
                    refusal.stage, refusal.reason, refusal.detail
                ));
                return (finish_row(row, &answer, false, None, claimed), false);
            }
        },
    };
    let state = searcher.state_exclusion(&test.initial_state);
    // The stored result record decides which stored no may be used (as a command without
    // --verify would); the answer is judged with this command's own baseline run, which under
    // --verify is the live run, not a stored record it may differ from.
    let baseline_run = result
        .record
        .as_ref()
        .and_then(|record| record["run_sha256"].as_str())
        .map(str::to_owned);
    let baseline = result.live.as_ref().or(result.record.as_ref());
    let facts = Facts {
        exclusions: context.exclusions,
        state,
        baseline_class: baseline.and_then(|record| record["class"].as_str()),
        baseline_cause: baseline.map_or_else(
            || result.row["cause"].as_str(),
            |record| record["cause"].as_str(),
        ),
        profile: SolverProfile::BUILD,
        no_data: crate::pattern::no_data(&spec.data),
    };
    let keyed = context.build.map(|build| {
        (
            answer_key(
                build,
                context.spec,
                digest,
                lowered.digest,
                context.manifest.budget,
            ),
            answer_path(context.cache, context.spec, lowered.digest, digest),
        )
    });
    let stored = keyed
        .as_ref()
        .and_then(|(key, path)| read_record(path, key))
        .filter(|stored| {
            stored.answer == "hit"
                || (result.class() == Some("comparable")
                    && stored.baseline_run_sha256.as_str() == baseline_run.as_deref())
        });
    if !context.verify
        && let Some(stored) = &stored
    {
        let answer = judge(&stored.outcome(), &facts);
        accounting["from_cache"] = json!(accounting["from_cache"].as_u64().unwrap_or(0) + 1);
        return (finish_row(row, &answer, true, None, claimed), true);
    }
    let (outcome, wall_ms) = searcher.search(&test.initial_state, lowered);
    let answer = judge(&outcome, &facts);
    let mut ok = answer.answer != "error";
    let mut row = finish_row(row, &answer, false, Some(wall_ms), claimed);
    if context.verify {
        if let (Some(stored), Some((_, path))) = (&stored, &keyed)
            && (stored.answer != answer.answer
                || (stored.answer == "hit" && answer.witness.as_ref() != Some(&stored.witness)))
        {
            let relative = path
                .strip_prefix(context.cache)
                .unwrap_or(path)
                .to_string_lossy()
                .into_owned();
            mismatches.push(json!({
                "pattern": pattern_id,
                "program": program.id,
                "record": relative,
                "cached": {"answer": stored.answer, "witness": stored.witness},
                "live": {"answer": answer.answer, "cause": answer.cause, "witness": answer.witness},
            }));
            row["verify"] = json!("mismatch");
        } else if stored.is_some() {
            row["verify"] = json!("match");
        }
        return (row, ok);
    }
    if let Some((key, path)) = &keyed
        && matches!(answer.answer, "hit" | "no")
    {
        let witness = answer.witness.clone().unwrap_or(Value::Null);
        let baseline = if answer.answer == "no" {
            json!(baseline_run)
        } else {
            Value::Null
        };
        let record = json!({
            "schema": RECORD_SCHEMA,
            "key": key,
            "pattern_id": pattern_id,
            "program_id": program.id,
            "answer": answer.answer,
            "witness": witness,
            "baseline_run_sha256": baseline,
            "record_sha256": record_sha256(key, answer.answer, &witness, &baseline).to_string(),
        });
        match context.store.write_json(path, &record) {
            Ok(()) => {
                accounting["records_written"] =
                    json!(accounting["records_written"].as_u64().unwrap_or(0) + 1);
            }
            Err(e) => {
                row["cache_error"] = json!(format!("cannot write the answer's record: {e}"));
                ok = false;
            }
        }
    }
    (row, ok)
}

/// A row with its answer: `{pattern, program, claimed, answer, cause, witness, cached, wall_ms,
/// claim}`. `claim` is null for a program the corpus form asked, else `confirmed` (hit),
/// `refuted` (no: the run reaches no state matching the pattern) or `unconfirmed`.
fn finish_row(
    mut row: Map<String, Value>,
    answer: &Answer,
    cached: bool,
    wall_ms: Option<u64>,
    claimed: bool,
) -> Value {
    row.insert("answer".into(), json!(answer.answer));
    row.insert("cause".into(), json!(answer.cause));
    row.insert(
        "witness".into(),
        answer.witness.clone().unwrap_or(Value::Null),
    );
    row.insert("cached".into(), json!(cached));
    row.insert("wall_ms".into(), json!(wall_ms));
    row.insert(
        "claim".into(),
        if claimed {
            json!(match answer.answer {
                "hit" => "confirmed",
                "no" => "refuted",
                _ => "unconfirmed",
            })
        } else {
            Value::Null
        },
    );
    Value::Object(row)
}

#[allow(clippy::too_many_arguments)]
fn document(
    record: &AdmissionRecord,
    digest: Option<Sha256Digest>,
    programs: Vec<Value>,
    patterns: Vec<Value>,
    rows: Vec<Value>,
    mismatches: Vec<Value>,
    pattern_cache: Value,
    baseline_runs: Value,
) -> Value {
    let refusal = record.refusal.as_ref();
    let counts = ANSWERS
        .iter()
        .map(|answer| {
            (
                (*answer).to_owned(),
                json!(rows.iter().filter(|row| row["answer"] == *answer).count()),
            )
        })
        .collect::<Map<_, _>>();
    let refuted = rows
        .iter()
        .filter(|row| row["claim"] == "refuted")
        .map(|row| json!({"pattern": row["pattern"], "program": row["program"]}))
        .collect::<Vec<_>>();
    json!({
        "schema": QUERY_SCHEMA,
        "version": QUERY_VERSION,
        "k_rust_revision": crate::k_rust_revision(),
        "profile": SolverProfile::BUILD.name(),
        "kink_build": kink_campaign::kink_build().map_or(Value::Null, |b| json!(b.to_string())),
        "kink": kink_campaign::kink_identity(),
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
        "patterns": patterns,
        "rows": rows,
        "counts": counts,
        "refuted_claims": refuted,
        "mismatches": mismatches,
        "pattern_cache": pattern_cache,
        "baseline_runs": baseline_runs,
    })
}

fn refused_document(record: &AdmissionRecord) -> Value {
    document(
        record,
        None,
        Vec::new(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
        Value::Null,
        Value::Null,
    )
}

/// The query document of a pattern list that does not decode (or names a program the manifest
/// does not have).
pub fn pattern_list_refused(error: &ManifestError) -> Value {
    json!({
        "schema": QUERY_SCHEMA,
        "version": QUERY_VERSION,
        "k_rust_revision": crate::k_rust_revision(),
        "profile": SolverProfile::BUILD.name(),
        "pattern_list": {"outcome": "refused", "detail": error.to_string()},
    })
}

#[cfg(test)]
// Under Z3 the tests of the pattern cache (off by design) compile out, and their helpers with them.
#[cfg_attr(feature = "z3", allow(dead_code, unused_imports))]
mod tests {
    //! A cached answer is judged again with the current command's facts (F-18 fix 1): the load
    //! facts a test cannot provoke are set through [`query_with`].
    use super::*;
    use kink_native::exclusion::{DefinitionExclusions, HookReference};

    fn calc() -> (FlowManifest, PatternList) {
        let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../testdata/flow/calc");
        (
            FlowManifest::read(&dir.join("FLOW.toml")).unwrap(),
            PatternList::read(&dir.join("PATTERNS.toml")).unwrap(),
        )
    }

    /// `query_with` on calc with the cache `cache`, on a thread with the command's stack.
    fn run(
        cache: &Path,
        adjust: impl Fn(&mut DefinitionExclusions) + Send + 'static,
    ) -> (Value, bool) {
        let cache = cache.to_path_buf();
        std::thread::Builder::new()
            .stack_size(kink_corpus::cli::DEFINITION_STACK_BYTES)
            .spawn(move || {
                let (manifest, list) = calc();
                let options = QueryOptions {
                    cache: Some(cache),
                    ..QueryOptions::default()
                };
                query_with(&manifest, &list, &options, &adjust)
            })
            .unwrap()
            .join()
            .unwrap()
    }

    fn row<'a>(document: &'a Value, pattern: &str, program: &str) -> &'a Value {
        document["rows"]
            .as_array()
            .unwrap()
            .iter()
            .find(|row| row["pattern"] == pattern && row["program"] == program)
            .unwrap_or_else(|| panic!("no row ({pattern}, {program}) in {document:#}"))
    }

    mod kink_tier {
        use super::*;

        // Portable only: tests the pattern cache, off under Z3 by design as tier 1 is.
        #[cfg(not(feature = "z3"))]
        #[test]
        #[ignore = "kink"]
        fn a_cached_answer_is_judged_with_the_current_facts() {
            let cache = std::env::temp_dir()
                .join(format!("kink-flow-query-rejudge-{}", std::process::id()));
            let _ = fs::remove_dir_all(&cache);
            let (first, ok) = run(&cache, |_| {});
            assert!(ok, "{first:#}");
            assert_eq!(row(&first, "result-three", "add")["answer"], "hit");
            assert_eq!(row(&first, "result-four", "add")["answer"], "no");
            assert_eq!(row(&first, "result-four", "add")["cached"], false);

            // The same facts: both answers come from the cache.
            let (second, _) = run(&cache, |_| {});
            for (pattern, answer) in [("result-three", "hit"), ("result-four", "no")] {
                let row = row(&second, pattern, "add");
                assert_eq!(row["answer"], answer, "{row:#}");
                assert_eq!(row["cached"], true, "{row:#}");
            }

            // This command's load counts a stack stop: neither cached answer stands.
            let (stopped, _) = run(&cache, |exclusions| exclusions.load_stack_stops = 1);
            for pattern in ["result-three", "result-four"] {
                let row = row(&stopped, pattern, "add");
                assert_eq!(row["cached"], true, "{row:#}");
                assert_eq!(row["answer"], "unknown", "{row:#}");
                assert!(
                    row["cause"].as_str().unwrap().contains("load-stack-stop"),
                    "{row:#}"
                );
            }

            // This command's census flags a hook: the cached no is unknown, the cached hit stands.
            let (census, _) = run(&cache, |exclusions| {
                exclusions.implementation_chosen.push(HookReference {
                    module: "M".into(),
                    sentence: "r".into(),
                    symbol: "Lblkeys'Unds'list".into(),
                    hook: "MAP.keys_list".into(),
                });
            });
            let no = row(&census, "result-four", "add");
            assert_eq!(
                (no["cached"].clone(), no["answer"].clone()),
                (json!(true), json!("unknown"))
            );
            assert!(
                no["cause"]
                    .as_str()
                    .unwrap()
                    .contains("implementation-chosen-hook"),
                "{no:#}"
            );
            let hit = row(&census, "result-three", "add");
            assert_eq!(
                (hit["cached"].clone(), hit["answer"].clone()),
                (json!(true), json!("hit"))
            );
            let _ = fs::remove_dir_all(&cache);
        }
    }
}
