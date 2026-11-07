//! The outcome cache (flow F-14, README 7.5): tier 1, the proved outcome of a mutation on a
//! program under an exact key, and tier 2, the recorded killer of the lock (`--lock`), which
//! survives specification edits.
//!
//! Every status here is checked against a cold run (a fresh cache) of the same files: a
//! cached outcome or a recorded killer may change the calls and the killer, never a status.
//! Each run here uses the lock `verdicts.lock` beside the manifest, which a copied cold run
//! starts with as that run would have written it. The tests read the run document, `outcomes/`
//! and the lock, and edit them by hand only to forge what a corrupted or hostile cache, or a
//! hand-edited lock, would hold.

mod flow_support;

use k_rust::definition::AttributeKey;
use kink_corpus::load_source;
use kink_flow::{
    FlowManifest, MutationList,
    admit::corpus_source,
    cli::{EXIT_UNASKED, EXIT_YES, results},
    digest::{mutation_identity, spec_digest},
    mutation::InvalidReason,
    outcomes::{OUTCOMES_DIRECTORY, record_sha256},
    resolve,
    results::{CACHE_DIRECTORY, ResultsOptions},
    search::{RunMode, RunOptions, drift_reason, run_with},
    verdicts::lock_text,
};
use kink_patch::{Edit, Patch};
use serde_json::{Value, json};
use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
    process::Command,
};

fn flow(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../testdata/flow")
        .join(name)
}

/// A fresh directory for one test, under the target's temporary directory.
fn scratch(name: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-outcomes-{}", std::process::id()))
        .join(name);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
}

fn copy_dir(from: &Path, to: &Path) {
    fs::create_dir_all(to).unwrap();
    for entry in fs::read_dir(from).unwrap() {
        let entry = entry.unwrap();
        let name = entry.file_name();
        if name == CACHE_DIRECTORY {
            continue;
        }
        if entry.file_type().unwrap().is_dir() {
            copy_dir(&entry.path(), &to.join(&name));
        } else {
            fs::copy(entry.path(), to.join(&name)).unwrap();
        }
    }
}

/// A private copy of a testdata/flow fixture.
fn fixture(name: &str, test: &str) -> PathBuf {
    let dir = scratch(test).join(name);
    copy_dir(&flow(name), &dir);
    dir
}

/// A private copy of the testdata/flow fixture `name` whose cache holds a cold run of
/// `mutations` under `manifest`, and that run's document. Each cold run is made once per test
/// binary and test run (its admission dominates a debug test's time) and copied for each test
/// (`flow_support::after_cold`).
fn after_cold(name: &str, manifest: &str, mutations: &str, test: &str) -> (PathBuf, Value) {
    let dir = scratch(test).join(name);
    let cold = flow_support::after_cold(name, manifest, mutations, &dir);
    // The lock the cold run writes with an empty one: its killers are the search's first.
    fs::write(lock_of(&dir.join(manifest)), lock_text(&cold).unwrap()).unwrap();
    (dir, cold)
}

/// [`after_cold`] of calc's MUTATIONS.toml.
fn calc_after_cold(test: &str) -> (PathBuf, Value) {
    after_cold("calc", "FLOW.toml", "MUTATIONS.toml", test)
}

/// `statuses` of the rows of the named mutations only.
fn statuses_of(document: &Value, ids: &[&str]) -> Vec<(String, String, Option<String>)> {
    statuses(document)
        .into_iter()
        .filter(|(id, ..)| ids.contains(&id.as_str()))
        .collect()
}

fn edit(path: &Path, from: &str, to: &str) {
    let text = fs::read_to_string(path).unwrap();
    assert!(text.contains(from), "{} has no {from:?}", path.display());
    fs::write(path, text.replacen(from, to, 1)).unwrap();
}

/// Replace each `(from, to)` once in the file at `path`.
fn edit_lines(path: &Path, pairs: &[(&str, &str)]) {
    let mut text = fs::read_to_string(path).unwrap();
    for (from, to) in pairs {
        assert_eq!(text.matches(from).count(), 1, "{from}");
        text = text.replace(from, to);
    }
    fs::write(path, text).unwrap();
}

fn append(path: &Path, text: &str) {
    let mut contents = fs::read_to_string(path).unwrap();
    contents.push_str(text);
    fs::write(path, contents).unwrap();
}

/// `kink-flow run` (or `run --verify`) through the library, as the binary runs it.
fn search_mode(manifest: &Path, mutations: &Path, only: &[&str], mode: RunMode) -> (Value, bool) {
    let lock = lock_of(manifest);
    let manifest = FlowManifest::read(manifest).unwrap();
    let list = MutationList::read(mutations).unwrap();
    run_with(
        &manifest,
        &list,
        &RunOptions {
            only: only.iter().map(|id| (*id).to_owned()).collect(),
            cache: None,
            compile_workers: None,
            memo: kink_flow::memo::MemoUse::On,
            schedule: kink_campaign::ScheduleMode::FirstKill,
            lock: Some(lock),
            locked: false,
        },
        mode,
    )
}

/// The lock every run of this binary uses: `verdicts.lock` beside the manifest.
fn lock_of(manifest: &Path) -> PathBuf {
    manifest.with_file_name("verdicts.lock")
}

fn search(manifest: &Path, mutations: &Path, only: &[&str]) -> (Value, bool) {
    search_mode(manifest, mutations, only, RunMode::Search)
}

fn rows(document: &Value) -> &Vec<Value> {
    document["mutations"].as_array().unwrap()
}

fn mutation<'d>(document: &'d Value, id: &str) -> &'d Value {
    rows(document)
        .iter()
        .find(|m| m["id"] == id)
        .unwrap_or_else(|| panic!("no mutation {id}"))
}

/// `(id, status, killer)` of every mutation row.
fn statuses(document: &Value) -> Vec<(String, String, Option<String>)> {
    rows(document)
        .iter()
        .map(|m| {
            (
                m["id"].as_str().unwrap().to_owned(),
                m["status"].as_str().unwrap().to_owned(),
                m["killer"].as_str().map(str::to_owned),
            )
        })
        .collect()
}

/// `(id, status)` of every mutation row.
fn status_only(document: &Value) -> Vec<(String, String)> {
    statuses(document)
        .into_iter()
        .map(|(id, status, _)| (id, status))
        .collect()
}

/// The programs of each campaign call of a mutation.
fn calls(document: &Value, id: &str) -> Vec<Vec<String>> {
    mutation(document, id)["calls"]
        .as_array()
        .unwrap()
        .iter()
        .map(|call| {
            call["programs"]
                .as_array()
                .unwrap()
                .iter()
                .map(|p| p.as_str().unwrap().to_owned())
                .collect()
        })
        .collect()
}

/// `(program, outcome, cached)` of every executed entry of a mutation.
fn executed(document: &Value, id: &str) -> Vec<(String, String, bool)> {
    mutation(document, id)["executed"]
        .as_array()
        .unwrap()
        .iter()
        .map(|e| {
            (
                e["program"].as_str().unwrap().to_owned(),
                e["outcome"].as_str().unwrap().to_owned(),
                e["cached"].as_bool().unwrap(),
            )
        })
        .collect()
}

fn strings(items: &[&str]) -> Vec<String> {
    items.iter().map(|s| (*s).to_owned()).collect()
}

fn cache_of(manifest: &Path) -> PathBuf {
    manifest.parent().unwrap().join(CACHE_DIRECTORY)
}

fn forget_outcomes(manifest: &Path) {
    let _ = fs::remove_dir_all(cache_of(manifest).join(OUTCOMES_DIRECTORY));
}

fn program_digest(document: &Value, id: &str) -> String {
    document["programs"]
        .as_array()
        .unwrap()
        .iter()
        .find(|p| p["id"] == id)
        .unwrap_or_else(|| panic!("no program {id}"))["digest"]
        .as_str()
        .unwrap()
        .to_owned()
}

/// The outcome file of mutation `id` in the context of `document`.
fn outcome_file(manifest: &Path, document: &Value, id: &str) -> PathBuf {
    cache_of(manifest)
        .join(OUTCOMES_DIRECTORY)
        .join(
            document["outcome_cache"]["context_sha256"]
                .as_str()
                .unwrap(),
        )
        .join(format!(
            "{}.json",
            mutation(document, id)["identity"].as_str().unwrap()
        ))
}

fn read_json(path: &Path) -> Value {
    serde_json::from_str(&fs::read_to_string(path).unwrap()).unwrap()
}

fn write_json(path: &Path, value: &Value) {
    fs::write(path, serde_json::to_string_pretty(value).unwrap()).unwrap();
}

/// A result record without its host-measured timing (`wall_ms`, the live baseline's wall
/// time, outside the key; flow F-17): a re-run gives the same record up to that field. The
/// field must be present, as an integer or null, so a test that compares the rest still
/// pins the record's shape.
fn without_wall_ms(record: &Value) -> Value {
    let wall_ms = &record["wall_ms"];
    assert!(
        record.get("wall_ms").is_some() && (wall_ms.is_u64() || wall_ms.is_null()),
        "{record:#}"
    );
    let mut record = record.clone();
    record.as_object_mut().unwrap().remove("wall_ms");
    record
}

/// The program ids of the records of mutation `id`'s outcome file, with their outcomes.
fn records(manifest: &Path, document: &Value, id: &str) -> BTreeMap<String, String> {
    let path = outcome_file(manifest, document, id);
    if !path.exists() {
        return BTreeMap::new();
    }
    read_json(&path)["records"]
        .as_object()
        .unwrap()
        .values()
        .map(|record| {
            (
                record["program_id"].as_str().unwrap().to_owned(),
                record["outcome"].as_str().unwrap().to_owned(),
            )
        })
        .collect()
}

/// Rewrite one record of mutation `id`'s file with `change`, then recompute its
/// `record_sha256` when `reseal`.
fn forge_record(
    manifest: &Path,
    document: &Value,
    id: &str,
    program: &str,
    reseal: bool,
    change: impl FnOnce(&mut Value),
) {
    let path = outcome_file(manifest, document, id);
    let mut file = read_json(&path);
    let digest = program_digest(document, program);
    let context = file["context_sha256"].as_str().unwrap().to_owned();
    let identity = file["mutation_identity"].as_str().unwrap().to_owned();
    let record = &mut file["records"][&digest];
    assert!(record.is_object(), "{id} has no record for {program}");
    change(record);
    if reseal {
        let slots = record["slots"]
            .as_array()
            .unwrap()
            .iter()
            .map(|s| s.as_str().unwrap())
            .collect::<Vec<_>>();
        let sealed = record_sha256(
            &context,
            &identity,
            &digest,
            record["baseline_run_sha256"].as_str().unwrap(),
            record["outcome"].as_str().unwrap(),
            &slots,
            record["mutant_run_sha256"].as_str().unwrap(),
            &record["difference"],
            &kink_flow::outcomes::OutcomeRecord::report_value(record),
        );
        record["record_sha256"] = json!(sealed.to_string());
    }
    write_json(&path, &file);
}

/// The lock's recorded killer of each mutation it lists.
fn recorded_killers(manifest: &Path) -> BTreeMap<String, Option<String>> {
    let lock: toml::Table = fs::read_to_string(lock_of(manifest))
        .unwrap()
        .parse()
        .unwrap();
    lock["mutation"]
        .as_array()
        .unwrap()
        .iter()
        .map(|row| {
            (
                row["id"].as_str().unwrap().to_owned(),
                row.get("killer")
                    .and_then(toml::Value::as_str)
                    .map(str::to_owned),
            )
        })
        .collect()
}

/// Hand-edit the lock: the recorded killer of `mutation` becomes `program`.
fn set_record(manifest: &Path, mutation: &str, program: &str) {
    let path = lock_of(manifest);
    let mut lock: toml::Table = fs::read_to_string(&path).unwrap().parse().unwrap();
    let rows = lock["mutation"].as_array_mut().unwrap();
    let row = rows
        .iter_mut()
        .find(|row| row["id"].as_str() == Some(mutation))
        .unwrap_or_else(|| panic!("the lock lists no {mutation}"));
    row.as_table_mut()
        .unwrap()
        .insert("killer".into(), toml::Value::String(program.to_owned()));
    fs::write(&path, toml::to_string(&lock).unwrap()).unwrap();
}

fn result_record_path(manifest: &Path, document: &Value, program: &str) -> PathBuf {
    cache_of(manifest)
        .join("results")
        .join(
            document["spec"]["execution_digest"]["digest"]
                .as_str()
                .unwrap(),
        )
        .join(format!("{}.json", program_digest(document, program)))
}

/// Check (a): a warm run after no change has the cold run's statuses and killers; a killed
/// mutation and a survivor whose every program is cached make no call.
fn warm_after_no_change(manifest: &Path, mutations: &Path, cold: &Value, name: &str) {
    assert!(cold["outcome_cache"]["enabled"].as_bool().unwrap());
    assert!(cold["outcome_cache"]["records_written"].as_u64().unwrap() > 0);
    let (warm, ok) = search(manifest, mutations, &[]);
    assert!(ok, "{warm:#}");
    assert_eq!(statuses(&warm), statuses(cold), "{name}");
    assert_eq!(
        warm["outcome_cache"]["context_sha256"],
        cold["outcome_cache"]["context_sha256"]
    );
    assert_eq!(warm["outcome_cache"]["records_written"], 0, "{name}");
    let mut from_cache = 0;
    for row in rows(&warm) {
        let id = row["id"].as_str().unwrap();
        match row["status"].as_str().unwrap() {
            "killed" => {
                assert_eq!(row["killer_source"], "outcome-cache", "{id}");
                assert_eq!(row["killer_from_cache"], true, "{id}");
                assert_eq!(row["calls"], json!([]), "{id}");
                // The cached prefix of the search order up to the killer, which comes last.
                let entries = executed(&warm, id);
                let (killer, prefix) = entries.split_last().unwrap();
                assert_eq!(
                    (killer.0.as_str(), killer.1.as_str(), killer.2),
                    (row["killer"].as_str().unwrap(), "distinguish", true),
                    "{id}"
                );
                assert!(
                    prefix
                        .iter()
                        .all(|(_, outcome, cached)| outcome != "distinguish" && *cached),
                    "{id}"
                );
                from_cache += 1;
            }
            "survived" => {
                assert_eq!(row["calls"], json!([]), "{id}");
                assert!(
                    executed(&warm, id)
                        .iter()
                        .all(|(_, outcome, cached)| outcome == "agree" && *cached),
                    "{id}"
                );
                from_cache += 1;
            }
            // CF-33d: an unknown whose every cell is cached (agreements and unknowns a work or
            // depth bound gave) makes no call.
            "unknown" if executed(&warm, id).iter().all(|(_, _, cached)| *cached) => {
                assert_eq!(row["calls"], json!([]), "{id}");
                from_cache += 1;
            }
            // Never cached: a timeout, an unknown of a failed run, a mutant-scope status; an
            // invalid mutation is never run.
            "invalid-mutation" => assert_eq!(row["calls"], json!([]), "{id}"),
            _ => assert_ne!(row["calls"], json!([]), "{id}"),
        }
    }
    assert_eq!(warm["outcome_cache"]["mutations_from_cache"], from_cache);
}

/// Packet CACHE-ID: the tier-1 context holds kink's semantics identity (kink-campaign
/// `identity`). An outcome file written under a context of a build before CACHE-ID (no `kink`
/// member, its three admission versions at the top level, as at 64b56fa) or under any one other
/// identity component lies in another context directory, and the same file placed in this
/// build's directory is ignored: its context is not this build's. Re-pin L1-2-land: so is one
/// written under a context that lacks the one-sided rule's component (`one_sided`, as at
/// 830c18e), where a one-sided kill could not have been recorded.
#[test]
fn an_outcome_written_under_another_identity_is_ignored() {
    use kink_flow::{
        digest::{EXECUTION_DIGEST_KIND, ExecutionDigest, outcome_context},
        manifest::Budget,
        outcomes::{CachedOutcome, OutcomeRecord, OutcomeStore},
    };
    let cache = scratch("identity");
    let store = kink_corpus::Store::new(&cache);
    let context = outcome_context(
        kink_patch::sha256(b"kink build"),
        ExecutionDigest {
            kind: EXECUTION_DIGEST_KIND,
            digest: kink_patch::sha256(b"specification"),
        },
        Budget::default(),
        &kink_flow::ResultProjection {
            state: kink_campaign::StateProjection::WholeTerm,
            compared: Some(vec!["k".into()]),
            not_compared: Vec::new(),
            unobservable: Vec::new(),
        },
        None,
        None,
    );
    assert_eq!(context["kink"], kink_campaign::kink_identity());
    let identity = kink_patch::sha256(b"mutation");
    let program = kink_patch::sha256(b"program").to_string();
    let record = OutcomeRecord {
        program_id: "program".into(),
        baseline_run_sha256: "0".repeat(64),
        outcome: CachedOutcome::Killed,
        slots: vec![
            kink_campaign::OracleOutcome::Distinguish,
            kink_campaign::OracleOutcome::Agree,
        ],
        mutant_run_sha256: "1".repeat(64),
        difference: serde_json::Value::Null,
        cause: None,
        open_application: false,
        smt_unknowns: 0,
        decider_smt_unknowns: 0,
        allowance_bytes: None,
    };
    let records = [(program.clone(), record)];
    let here = OutcomeStore::new(&cache, context.clone());
    let mut before = context.clone();
    let object = before.as_object_mut().unwrap();
    object.remove("kink");
    for key in [
        "k_rust_revision",
        "result_schema",
        "claim_removal",
        "mutant_consistency",
        "mutant_effect",
    ] {
        object.insert(key.into(), context["kink"][key].clone());
    }
    // Re-pin L1-2-land: a context from before the one-sided rule was a component (830c18e).
    let mut before_one_sided = context.clone();
    before_one_sided["kink"]
        .as_object_mut()
        .unwrap()
        .remove("one_sided")
        .unwrap();
    let mut stale = vec![
        ("before CACHE-ID", before),
        ("before one_sided", before_one_sided),
    ];
    for component in kink_campaign::KINK_IDENTITY {
        let mut changed = context.clone();
        changed["kink"][component.key] = json!(format!("{}-other", component.value));
        stale.push((component.key, changed));
    }
    for (name, stale) in stale {
        here.write(&store, identity, "m", &json!(null), &json!(null), &records)
            .unwrap();
        assert_eq!(here.read(identity).len(), 1, "{name}: control");
        let there = OutcomeStore::new(&cache, stale);
        assert_ne!(there.context_sha256(), here.context_sha256(), "{name}");
        there
            .write(&store, identity, "m", &json!(null), &json!(null), &records)
            .unwrap();
        assert_eq!(
            there.read(identity).len(),
            1,
            "{name}: the stale build's own read"
        );
        fs::copy(there.path(identity), here.path(identity)).unwrap();
        assert!(here.read(identity).is_empty(), "{name}");
    }
}

/// The outcome file keeps the mutant's compiled edit (`witness`, version 3) beside its records:
/// a write with none keeps the stored one, a write with one replaces it, and a version 2 file,
/// which has none, is not current.
#[test]
fn the_outcome_file_keeps_the_compiled_edit() {
    use kink_flow::outcomes::{CachedOutcome, OUTCOMES_VERSION, OutcomeRecord, OutcomeStore};
    let cache = scratch("witness");
    let store = kink_corpus::Store::new(&cache);
    let outcomes = OutcomeStore::new(&cache, json!({"test": "witness"}));
    let identity = kink_patch::sha256(b"mutation");
    let record = |program: &str| {
        (
            kink_patch::sha256(program.as_bytes()).to_string(),
            OutcomeRecord {
                program_id: program.into(),
                baseline_run_sha256: "0".repeat(64),
                outcome: CachedOutcome::Agree,
                slots: vec![
                    kink_campaign::OracleOutcome::Agree,
                    kink_campaign::OracleOutcome::Agree,
                ],
                mutant_run_sha256: "1".repeat(64),
                difference: Value::Null,
                cause: None,
                open_application: false,
                smt_unknowns: 0,
                decider_smt_unknowns: 0,
                allowance_bytes: None,
            },
        )
    };
    let witness = json!({
        "global": false,
        "matched": [],
        "applied": [{"module": "DIVIDE", "index": 3}],
    });
    outcomes
        .write(
            &store,
            identity,
            "m",
            &json!(null),
            &witness,
            &[record("one")],
        )
        .unwrap();
    let (records, read) = outcomes.read_with_witness(identity);
    assert_eq!((records.len(), &read), (1, &witness));
    // A later write with no compiled edit keeps the stored one and adds its records.
    outcomes
        .write(
            &store,
            identity,
            "m",
            &json!(null),
            &json!(null),
            &[record("two")],
        )
        .unwrap();
    let (records, read) = outcomes.read_with_witness(identity);
    assert_eq!((records.len(), &read), (2, &witness));
    let global = json!({"global": true, "matched": [], "applied": []});
    outcomes
        .write(
            &store,
            identity,
            "m",
            &json!(null),
            &global,
            &[record("two")],
        )
        .unwrap();
    assert_eq!(outcomes.read_with_witness(identity).1, global);
    let path = outcomes.path(identity);
    let mut file: Value = serde_json::from_str(&fs::read_to_string(&path).unwrap()).unwrap();
    assert_eq!(file["version"], OUTCOMES_VERSION);
    file["version"] = json!(2);
    fs::write(&path, file.to_string()).unwrap();
    let (records, read) = outcomes.read_with_witness(identity);
    assert!(records.is_empty() && read.is_null());
}

/// CF-33d, the cacheability of an outcome (outcomes.rs, "Unknown outcomes"): `killed` and
/// `agree` as before; an `unknown` only from a compared test whose slots are `agree` or `unknown`
/// and whose run the backend judged (`RunNotes::unjudged` false), so that it is a function of the
/// outcome key. A host-bound cause is never cacheable: a slot the clock stopped (`timeout`), an
/// untrustworthy backend result (`error`), a run the watchdog stopped (`TimeLimit`), a host
/// exclusion (stack stop, load stack stop, allowance refusal), an infrastructure failure, and a
/// judgement the backend refused, a stop condition without an answer at an arrival (an undecided
/// answer can be its evaluation's budget); nor is an `incomparable` slot (status `error`) or a
/// failed run excluded for a fact of the definition or the run, whose row's reason a live call
/// gives.
#[test]
fn an_unknown_is_cacheable_only_when_the_run_was_judged() {
    use kink_campaign::{ExecutionFailureKind as F, OracleOutcome as O, RunNotes, TestRun};
    use kink_flow::outcomes::{CachedOutcome, cacheable};
    let judged = RunNotes::default();
    let unjudged = RunNotes {
        unjudged: true,
        ..RunNotes::default()
    };
    let outcome =
        |run: &TestRun, notes: Option<&RunNotes>| cacheable(run, notes).map(|(outcome, _)| outcome);
    let compared = |slots: &[O]| TestRun::Compared(slots.to_vec());
    for (slots, expected) in [
        (
            &[O::Distinguish, O::Unknown][..],
            Some(CachedOutcome::Killed),
        ),
        (&[O::Agree, O::Agree], Some(CachedOutcome::Agree)),
        (&[O::Unknown, O::Agree], Some(CachedOutcome::Unknown)),
        (&[O::Unknown, O::Unknown], Some(CachedOutcome::Unknown)),
        (&[O::Timeout, O::Agree], None),
        (&[O::Unknown, O::Timeout], None),
        (&[O::Error, O::Unknown], None),
        (&[O::Incomparable, O::Agree], None),
        (&[], None),
    ] {
        assert_eq!(
            outcome(&compared(slots), Some(&judged)),
            expected,
            "{slots:?}"
        );
    }
    // A judgement the backend refused, or no evidence to read it from: not cached as unknown.
    let unknown = compared(&[O::Unknown, O::Agree]);
    assert_eq!(outcome(&unknown, Some(&unjudged)), None);
    assert_eq!(outcome(&unknown, None), None);
    // Killed and agree rest on no refused judgement (one leaves its slots unknown), so the flag
    // does not change them.
    assert_eq!(
        outcome(&compared(&[O::Agree, O::Agree]), Some(&unjudged)),
        Some(CachedOutcome::Agree)
    );
    for kind in [
        F::TimeLimit,
        F::Infrastructure,
        F::StackStop,
        F::LoadStackStop,
        F::AllowanceRefusal,
        F::ContradictedClaim,
        F::ShortCircuitReading,
        F::ImplementationChosenValue,
        F::Indeterminate,
        F::ResourceLimit,
        // A stop condition left undecided at an arrival, possibly by its evaluation's budget,
        // or refused there: the run is not a function of the key.
        F::StopCondition,
    ] {
        assert_eq!(
            outcome(&TestRun::Failed(kind), Some(&judged)),
            None,
            "{kind:?}"
        );
    }
    assert_eq!(outcome(&TestRun::SkippedAfterKill, Some(&judged)), None);
}

/// CF-33d: an `unknown` record keeps its cause and the run's undecided-answer counts, inside its
/// digest; the reader returns it only with a cause, and returns no other record with one.
#[test]
fn an_unknown_record_says_why_and_no_other_record_has_a_cause() {
    use kink_campaign::OracleOutcome as O;
    use kink_flow::outcomes::{CachedOutcome, OutcomeRecord, OutcomeStore};
    let cache = scratch("unknown-record");
    let store = kink_corpus::Store::new(&cache);
    let outcomes = OutcomeStore::new(&cache, json!({"test": "unknown-record"}));
    let identity = kink_patch::sha256(b"mutation");
    let program = |name: &str| kink_patch::sha256(name.as_bytes()).to_string();
    let record = |outcome, slots: Vec<O>, cause: Option<&str>| OutcomeRecord {
        program_id: "p".into(),
        baseline_run_sha256: "0".repeat(64),
        outcome,
        slots,
        mutant_run_sha256: "1".repeat(64),
        difference: Value::Null,
        cause: cause.map(str::to_owned),
        open_application: false,
        smt_unknowns: 2,
        decider_smt_unknowns: 1,
        allowance_bytes: None,
    };
    let unknown = record(
        CachedOutcome::Unknown,
        vec![O::Unknown, O::Agree],
        Some("exit-stop: the run reached its work budget"),
    );
    let agree = record(CachedOutcome::Agree, vec![O::Agree, O::Agree], None);
    outcomes
        .write(
            &store,
            identity,
            "m",
            &json!(null),
            &json!(null),
            &[
                (program("unknown"), unknown.clone()),
                (program("agree"), agree.clone()),
                // An unknown with no cause and an agreement with one are written as given here,
                // and refused by the reader below.
                (
                    program("no-cause"),
                    record(CachedOutcome::Unknown, vec![O::Unknown, O::Agree], None),
                ),
                (
                    program("agree-cause"),
                    record(CachedOutcome::Agree, vec![O::Agree, O::Agree], Some("why")),
                ),
            ],
        )
        .unwrap();
    let read = outcomes.read(identity);
    assert_eq!(read.get(&program("unknown")), Some(&unknown));
    assert_eq!(read.get(&program("agree")), Some(&agree));
    assert_eq!(read.len(), 2, "{read:?}");
    // The cause is inside the record's digest: an edited cause is not read.
    let path = outcomes.path(identity);
    let mut file: Value = serde_json::from_str(&fs::read_to_string(&path).unwrap()).unwrap();
    file["records"][program("unknown")]["cause"] = json!("edited");
    file["records"][program("agree")]["smt_unknowns"] = json!(0);
    fs::write(&path, file.to_string()).unwrap();
    assert!(outcomes.read(identity).is_empty());
}

/// Stop rule 1 (README 7.5.3 step 6): every mutation of the list run with a cache that a run
/// over the corpus without its first program filled has the cold run's status, and, unless a
/// cached kill decided it, the cold run's first killer. Returns the number of mutations whose
/// status mixed cached agreements with a live call.
fn partially_cached_equals_cold(
    name: &str,
    manifest_name: &str,
    mutations_name: &str,
    cold: &Value,
) -> usize {
    let dir = fixture(name, &format!("partial-{name}-{mutations_name}"));
    let manifest = dir.join(manifest_name);
    let mutations = dir.join(mutations_name);
    let flow = FlowManifest::read(&manifest).unwrap();
    let first = &flow.programs[0].id;
    let text = fs::read_to_string(&manifest).unwrap();
    let start = text.find("[[program]]").unwrap();
    let end = start + 1 + text[start + 1..].find("[[program]]").unwrap();
    let subset = dir.join("FLOW-subset.toml");
    fs::write(&subset, format!("{}{}", &text[..start], &text[end..])).unwrap();
    assert!(
        !FlowManifest::read(&subset)
            .unwrap()
            .programs
            .iter()
            .any(|p| &p.id == first)
    );
    let (filled, _) = search(&subset, &mutations, &[]);
    assert!(filled["outcome_cache"]["records_written"].as_u64().unwrap() > 0);
    let (partial, _) = search(&manifest, &mutations, &[]);
    assert_eq!(status_only(&partial), status_only(cold), "{name}");
    let mut mixed = 0;
    for (row, cold_row) in rows(&partial).iter().zip(rows(cold)) {
        if row["killer_source"] != "outcome-cache" {
            assert_eq!(row["killer"], cold_row["killer"], "{name}: {row:#}");
        }
        let entries = row["executed"].as_array().unwrap();
        if entries.iter().any(|e| e["cached"] == true)
            && !row["calls"].as_array().unwrap().is_empty()
        {
            mixed += 1;
        }
    }
    mixed
}

/// (a) and (g) on one fixture list after its cold run: a warm run after no change, then a run
/// with every recorded killer forged and tier 1 deleted.
fn warm_and_forged(name: &str, manifest: &str, mutations: &str) {
    let (dir, cold) = after_cold(
        name,
        manifest,
        mutations,
        &format!("tiers-{name}-{mutations}"),
    );
    let (manifest, mutations) = (dir.join(manifest), dir.join(mutations));
    warm_after_no_change(&manifest, &mutations, &cold, name);
    forged_records_change_no_status(&manifest, &mutations, &cold, name);
}

/// (e) on one fixture list against its cold run.
fn partial(name: &str, manifest: &str, mutations: &str) -> usize {
    let (_, cold) = after_cold(
        name,
        manifest,
        mutations,
        &format!("cold-copy-{name}-{mutations}"),
    );
    partially_cached_equals_cold(name, manifest, mutations, &cold)
}

/// Every mutation of a list resolved against its specification: (id, patch digest,
/// identity), for the mutations that resolve.
fn identities(manifest: &Path, mutations: &Path) -> Vec<(String, String, Option<String>)> {
    let flow = FlowManifest::read(manifest).unwrap();
    let list = MutationList::read(mutations).unwrap();
    let loaded = load_source(&corpus_source(&flow)).unwrap();
    list.mutations
        .iter()
        .filter_map(|mutation| {
            let resolved = resolve(&flow, &loaded, mutation).ok()?;
            Some((
                mutation.id.clone(),
                resolved.digest.to_string(),
                mutation_identity(&loaded.baseline, &resolved.patch).map(|d| d.to_string()),
            ))
        })
        .collect()
}

#[test]
fn a_position_only_edit_changes_the_patch_digest_but_not_the_identity() {
    // A blank line and a comment before the addressed rule move it: the patch digest (which
    // pins positions) and the specification digest change, the identity does not.
    let dir = fixture("calc", "positions");
    let manifest = dir.join("FLOW.toml");
    let mutations = dir.join("MUTATIONS.toml");
    // Replacements carry the rule's position attributes; a deletion (no-mul) pins only the
    // sentence's index, which a comment does not move.
    let replaced = ["add-becomes-sub", "mul-becomes-add"];
    let flow = FlowManifest::read(&manifest).unwrap();
    let before = identities(&manifest, &mutations);
    let spec_before = spec_digest(&flow, &load_source(&corpus_source(&flow)).unwrap().files);
    edit(
        &dir.join("calc.k"),
        "  rule [add]:",
        "\n  // the addition rule\n  rule [add]:",
    );
    let after = identities(&manifest, &mutations);
    let spec_after = spec_digest(&flow, &load_source(&corpus_source(&flow)).unwrap().files);
    assert_ne!(spec_before, spec_after);
    for id in replaced {
        let old = before.iter().find(|(m, ..)| m == id).unwrap();
        let new = after.iter().find(|(m, ..)| m == id).unwrap();
        assert_ne!(old.1, new.1, "{id}: the patch digest pins positions");
        assert_eq!(old.2, new.2, "{id}: the identity does not");
    }
    let old = before.iter().find(|(m, ..)| m == "no-mul").unwrap();
    let new = after.iter().find(|(m, ..)| m == "no-mul").unwrap();
    assert_eq!(old.2, new.2);
}

#[test]
fn identical_rules_have_distinct_identities() {
    // Two identical rules share a fingerprint; their occurrence tells them apart.
    let all = identities(
        &flow("twin").join("FLOW.toml"),
        &flow("twin").join("MUTATIONS.toml"),
    );
    assert_eq!(all.len(), 2);
    assert_ne!(all[0].1, all[1].1);
    assert_ne!(all[0].2, all[1].2);
    assert!(all.iter().all(|(_, _, identity)| identity.is_some()));
}

#[test]
fn a_replacement_with_other_input_addresses_has_no_identity() {
    // kink-patch does not check InputAddresses on a replacement; the identity refuses any
    // replacement whose position attributes are not the addressed sentence's.
    let manifest = flow("calc").join("FLOW.toml");
    let flow = FlowManifest::read(&manifest).unwrap();
    let list = MutationList::read(&manifest.with_file_name("MUTATIONS.toml")).unwrap();
    let mutation = &list.mutations[0];
    let loaded = load_source(&corpus_source(&flow)).unwrap();
    let resolved = resolve(&flow, &loaded, mutation).unwrap();
    assert!(mutation_identity(&loaded.baseline, &resolved.patch).is_some());
    let edits = resolved
        .patch
        .edits()
        .iter()
        .map(|edit| match edit {
            Edit::ReplaceSentence { at, replacement } => {
                let mut replacement = replacement.clone();
                replacement
                    .attributes_mut()
                    .insert(AttributeKey::InputAddresses.as_str(), json!("forged"));
                Edit::ReplaceSentence {
                    at: at.clone(),
                    replacement,
                }
            }
            other => other.clone(),
        })
        .collect();
    let forged = Patch::new(edits).unwrap().pinned(&loaded.baseline).unwrap();
    assert_eq!(mutation_identity(&loaded.baseline, &forged), None);
}

/// (g): a recorded killer never changes a status. Every mutation's recorded killer is forged to a
/// program the cold run did not find killing it, tier 1 is deleted, and the statuses are the cold
/// run's.
fn forged_records_change_no_status(manifest: &Path, mutations: &Path, cold: &Value, name: &str) {
    let programs = cold["programs"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|p| p["class"] == "comparable")
        .map(|p| p["id"].as_str().unwrap().to_owned())
        .collect::<Vec<_>>();
    let mut forged = 0;
    for row in rows(cold) {
        if row["digest"].is_null() || row["status"] == "error" {
            continue;
        }
        let id = row["id"].as_str().unwrap();
        // A program the cold run did not find killing the mutation, else the last one.
        let program = row["executed"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|e| e["outcome"] != "distinguish")
            .find_map(|e| e["program"].as_str())
            .map_or_else(|| programs.last().unwrap().clone(), str::to_owned);
        set_record(manifest, id, &program);
        forged += 1;
    }
    assert!(forged > 0);
    forget_outcomes(manifest);
    let (recorded, _) = search(manifest, mutations, &[]);
    assert_eq!(status_only(&recorded), status_only(cold), "{name}");
}

#[test]
fn a_doubly_qualified_label_is_unknown() {
    // (i) F-10 review 1 m1: `LIT.LIT.inc` does not address the rule stored as `LIT.inc`.
    let manifest = flow("markdown").join("FLOW.toml");
    let flow = FlowManifest::read(&manifest).unwrap();
    let loaded = load_source(&corpus_source(&flow)).unwrap();
    let resolve_label = |label: &str| {
        let list = MutationList::decode(&format!(
            "[[mutation]]\nid = \"m\"\nmisunderstanding = \"a test mutation\"\n[[mutation.edit]]\nrule = \"{label}\"\nfind = \"+Int 1\"\nreplace = \"+Int 3\"\n"
        ))
        .unwrap();
        resolve(&flow, &loaded, &list.mutations[0])
    };
    assert!(resolve_label("LIT.inc").is_ok());
    assert!(resolve_label("inc").is_ok());
    assert_eq!(
        resolve_label("LIT.LIT.inc").unwrap_err().reason,
        InvalidReason::UnknownLabel
    );
    // The [label(dec)] rule is still addressed by LIT.dec, not by LIT.LIT.dec.
    let dec = |label: &str| {
        let list = MutationList::decode(&format!(
            "[[mutation]]\nid = \"m\"\nmisunderstanding = \"a test mutation\"\n[[mutation.edit]]\nrule = \"{label}\"\ndelete = true\n"
        ))
        .unwrap();
        resolve(&flow, &loaded, &list.mutations[0]).map(|r| r.digest)
    };
    assert!(dec("LIT.dec").is_ok());
    assert_eq!(
        dec("LIT.LIT.dec").unwrap_err().reason,
        InvalidReason::UnknownLabel
    );
}

/// Write an outcome file for mutation `id` holding a forged, correctly sealed `agree` record for
/// each of `programs` (the file of `template`, another mutation of the same context, gives the
/// schema and context): what a cache would hold if an earlier command had seen the mutant run.
fn forge_agreements(
    manifest: &Path,
    document: &Value,
    template: &str,
    id: &str,
    programs: &[&str],
) {
    let mut file = read_json(&outcome_file(manifest, document, template));
    let context = file["context_sha256"].as_str().unwrap().to_owned();
    let identity = mutation(document, id)["identity"]
        .as_str()
        .unwrap()
        .to_owned();
    let mut records = serde_json::Map::new();
    for program in programs {
        let digest = program_digest(document, program);
        let baseline = read_json(&result_record_path(manifest, document, program))["run_sha256"]
            .as_str()
            .unwrap()
            .to_owned();
        let sealed = record_sha256(
            &context,
            &identity,
            &digest,
            &baseline,
            "agree",
            &["agree", "agree"],
            &baseline,
            &Value::Null,
            &kink_flow::outcomes::OutcomeRecord::no_report(),
        );
        records.insert(
            digest,
            json!({
                "program_id": program,
                "baseline_run_sha256": baseline,
                "outcome": "agree",
                "slots": ["agree", "agree"],
                "mutant_run_sha256": baseline,
                "difference": null,
                "cause": null,
                "open_application": false,
                "smt_unknowns": 0,
                "decider_smt_unknowns": 0,
                "record_sha256": sealed.to_string(),
            }),
        );
    }
    file["mutation_identity"] = json!(identity);
    file["mutation_id"] = json!(id);
    file["records"] = Value::Object(records);
    let path = outcome_file(manifest, document, id);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    write_json(&path, &file);
}

/// The macro fixture's cold statuses: with a macro in the specification, a mutant that
/// compiles equal to the baseline fails kink-native's equivalence check, the runner's
/// mutant-scope `Infrastructure` failure (status error, reason infrastructure), on every host.
fn macro_after_cold(test: &str) -> (PathBuf, Value) {
    let (dir, cold) = after_cold("macro", "FLOW.toml", "MUTATIONS.toml", test);
    assert_eq!(
        statuses(&cold),
        vec![
            ("plus-in-a-group".into(), "error".into(), None),
            (
                "plus-becomes-minus".into(),
                "killed".into(),
                Some("sum".into())
            ),
            ("plus-unbound".into(), "not-admitted".into(), None),
        ]
    );
    assert_eq!(
        mutation(&cold, "plus-in-a-group")["reason"],
        "infrastructure"
    );
    assert_eq!(mutation(&cold, "plus-unbound")["reason"], "rejected");
    (dir, cold)
}

/// The known stack-dependence gap at the pin, as both READMEs state it (flow F-17, fix round
/// 1 of its review): k-rust dismisses a stop for lack of stack silently both while it loads a
/// definition (the discharge of rewrite-rule definedness, KINK-06/4) and while a run refines a
/// result (KINK-06/5), and its execution contract excludes the two separately. So the text
/// may not say the re-pin closes the gap through the run's `stackStops` alone: it must also
/// name the load's stack-stop counts of either definition.
#[test]
fn the_known_stack_gap_names_the_load_counts_beside_stack_stops() {
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    // Re-pin R0b deliverable 10: the text says what closes the gap for execute comparisons and
    // names the residuals (the Z3 profile, where tier 1 is off; the non-execute calls, B-13(a)).
    for (readme, anchor) in [
        (
            manifest.join("../../trust.md"),
            "Stack dependence (k-rust KINK-06/4",
        ),
        (manifest.join("README.md"), "The Execute promise of k-rust"),
    ] {
        let text = fs::read_to_string(&readme).unwrap();
        let start = text
            .find(anchor)
            .unwrap_or_else(|| panic!("{} names the known gap", readme.display()));
        let gap = &text[start..];
        let gap = &gap[..gap.find("\n\n").unwrap_or(gap.len())];
        for needle in [
            "stackStops",
            "load",
            "discharge_counts().stack_stops",
            "condition_stack_stops",
            "KINK-06/4",
            "KINK-06/5",
            "Z3",
            "tier 1",
            "B-13(a)",
            "definition_facts",
        ] {
            assert!(
                gap.contains(needle),
                "{}: the known-gap text lacks {needle:?}:\n{gap}",
                readme.display()
            );
        }
    }
}

mod heavy {
    use super::*;

    #[test]
    #[ignore = "heavy"]
    fn warm_and_forged_records_on_register() {
        warm_and_forged("register", "FLOW.toml", "MUTATIONS.toml");
    }

    #[test]
    #[ignore = "heavy"]
    fn warm_and_forged_records_on_markdown() {
        warm_and_forged("markdown", "FLOW.toml", "MUTATIONS.toml");
    }

    #[test]
    #[ignore = "heavy"]
    fn partially_cached_statuses_are_cold_statuses_on_register() {
        // Every register mutation is killed by a program of the subset: a cached kill decides.
        partial("register", "FLOW.toml", "MUTATIONS.toml");
    }

    #[test]
    #[ignore = "heavy"]
    fn partially_cached_statuses_are_cold_statuses_on_markdown() {
        partial("markdown", "FLOW.toml", "MUTATIONS.toml");
    }
}

/// Merge packet M-1 (S-1), CF-33: under the Z3 profile both of kink-flow's verdict caches are on,
/// tier 1 (the outcome records, and with it the warm-path memos) and the pattern cache, since
/// every solver query of kink's backends is bounded by Z3 resource units and the keys name the
/// units and the Z3 build. This light test keeps the Z3 side of the cache tests in k-rust's own
/// (Z3) test run. The kink-tier pins of both profiles are
/// tier_one_is_off_exactly_for_a_clock_bounded_solver (below) and query.rs's
/// the_pattern_cache_is_on_in_both_profiles.
#[cfg(feature = "z3")]
#[test]
fn both_caches_are_on_under_the_z3_profile() {
    use kink_flow::{cli::EXIT_NO, query::QueryOptions, search::tier1_refusal};
    use kink_native::execution::SolverProfile;
    assert_eq!(SolverProfile::BUILD, SolverProfile::Z3);
    assert_eq!(
        tier1_refusal(SolverProfile::BUILD, kink_native::BACKEND_OPTIONS),
        None
    );
    let dir = fixture("calc", "z3-caches-on");
    let manifest = dir.join("FLOW.toml");
    let (run, ok) = search(&manifest, &dir.join("MUTATIONS.toml"), &["add-becomes-sub"]);
    assert!(ok, "{run:#}");
    assert_eq!(run["outcome_cache"]["enabled"], true, "{run:#}");
    assert_eq!(run["outcome_cache"]["reason"], Value::Null, "{run:#}");
    assert!(
        run["outcome_cache"]["records_written"].as_u64().unwrap() > 0,
        "{run:#}"
    );
    assert!(cache_of(&manifest).join(OUTCOMES_DIRECTORY).exists());
    let patterns = dir.join("PATTERNS.toml");
    let (query, status) = std::thread::Builder::new()
        .stack_size(kink_corpus::cli::DEFINITION_STACK_BYTES)
        .spawn(move || kink_flow::cli::query(&manifest, &patterns, &QueryOptions::default()))
        .unwrap()
        .join()
        .unwrap();
    // calc's PATTERNS.toml asks pairs no exploration matches (`result-four` of `add`, for one),
    // whose searches receive no undecided solver answer, so under Z3 too they are `no`
    // (query.rs's NO) and a claim no case reaches is refuted (query.rs's REFUTED_STATUS).
    assert_eq!(status, EXIT_NO, "{query:#}");
    assert_eq!(query["pattern_cache"]["enabled"], true, "{query:#}");
    assert_eq!(query["pattern_cache"]["reason"], Value::Null, "{query:#}");
}

mod kink_tier {
    use super::*;

    /// Re-pin R0c-fix-2 (a mutant drops the claims its edit leaves unbacked), through kink-flow: the
    /// mutation `I +Int 0` of `td`'s equation leaves `td`'s `total` unbacked, so every program runs on
    /// the mutant without it. On `tdiv(0)` the claim-free mutant takes an undefined step (`10 /Int 0`
    /// is undefined in every model of it) where the baseline gives `val(10)`: `zero` kills it, and
    /// its runs are clean. Before R0c-fix-2 the mutant carried the claim, contradicted it on
    /// `tdiv(0)`, and the program was `unknown` (`contradicted-claim`). The row's `removed_claims`
    /// names the removed claim, the outcome file repeats it, and the tier-1 context names the
    /// claim-removal algorithm.
    #[test]
    #[ignore = "kink"]
    fn a_mutation_drops_the_claims_its_edit_leaves_unbacked() {
        let definition = r"module DROP-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= tdiv(Int) [symbol(tdiv)]
                | val(Int) [symbol(val)]
  syntax Int ::= td(Int) [function, total, symbol(td)]
endmodule

module DROP
  imports DROP-SYNTAX
  imports INT
  configuration <k> $PGM:Prog </k>
  rule [tdeq]: td(I) => 10 /Int (I +Int 1)
  rule [tdiv]: <k> tdiv(I) => val(td(I)) </k>
endmodule
";
        let dir = scratch("claim-free");
        fs::write(dir.join("drop.k"), definition).unwrap();
        fs::write(
            dir.join("FLOW.toml"),
            "[spec]\nentry = \"drop.k\"\nmain_module = \"DROP\"\nsyntax_module = \"DROP-SYNTAX\"\n\n\
             [[program]]\nid = \"zero\"\ntext = \"tdiv(0)\"\n",
        )
        .unwrap();
        fs::write(
            dir.join("MUTATIONS.toml"),
            r#"[[mutation]]
id = "denominator"
misunderstanding = "a test mutation"
  [[mutation.edit]]
  rule = "tdeq"
  find = "I +Int 1"
  replace = "I +Int 0"
"#,
        )
        .unwrap();
        let manifest = dir.join("FLOW.toml");
        let (document, ok) = search(&manifest, &dir.join("MUTATIONS.toml"), &[]);
        assert!(ok, "{document:#}");
        let row = mutation(&document, "denominator");
        assert_eq!(
            (row["status"].as_str(), row["killer"].as_str()),
            (Some("killed"), Some("zero")),
            "{row:#}"
        );
        let removed = row["removed_claims"]["removed"].as_array().unwrap();
        assert_eq!(removed.len(), 1, "{row:#}");
        assert_eq!(
            (removed[0]["module"].as_str(), removed[0]["key"].as_str()),
            (Some("DROP-SYNTAX"), Some("total")),
            "{row:#}"
        );
        assert_eq!(row["removed_claims"]["unsupported"], json!([]));
        let file = read_json(&outcome_file(&manifest, &document, "denominator"));
        assert_eq!(file["removed_claims"], row["removed_claims"], "{file:#}");
        assert_eq!(
            file["context"]["kink"]["claim_removal"],
            json!(kink_patch::CLAIM_REMOVAL_VERSION)
        );
    }

    #[test]
    #[ignore = "kink"]
    fn a_program_id_with_a_colon_and_the_count_mismatch_have_their_reasons() {
        // (i) F-05 review 1 minor 2: the reason carries the program id from the candidate.
        let dir = fixture("calc", "colon");
        let manifest = dir.join("FLOW.toml");
        let mutations = dir.join("MUTATIONS.toml");
        edit(&manifest, "id = \"add\"", "id = \"add:one\"");
        let (filled, status) = results(&manifest, &ResultsOptions::default());
        assert_eq!(status, EXIT_YES);
        let record = result_record_path(&manifest, &filled, "add:one");
        let mut value = read_json(&record);
        value["run_sha256"] = json!("0".repeat(64));
        write_json(&record, &value);
        let (document, ok) = search(&manifest, &mutations, &["add-becomes-sub"]);
        assert!(!ok);
        assert_eq!(
            mutation(&document, "add-becomes-sub")["reason"],
            "baseline-mismatch:add:one"
        );
        // The runner returns one baseline row per test, so a count mismatch cannot be produced
        // through it; the reason is pinned on the drift check's reason function.
        assert_eq!(
            drift_reason(Some("a:b"), true).as_deref(),
            Some("baseline-mismatch:a:b")
        );
        assert_eq!(
            drift_reason(None, true).as_deref(),
            Some("baseline-count-mismatch")
        );
        assert_eq!(drift_reason(None, false), None);
    }

    /// Re-pin R0b deliverable 9 (decision 5, finding B-09), CF-33: tier 1 is off exactly for a
    /// solver the clock bounds under the Z3 profile, which follows kink-native's `z3` feature (and
    /// so workspace feature unification), since such an answer depends on the host's load. kink's
    /// own resource-bounded budget keeps it on in both profiles: a run writes records and a second
    /// run reads them.
    #[test]
    #[ignore = "kink"]
    fn tier_one_is_off_exactly_for_a_clock_bounded_solver() {
        use kink_flow::search::{TIER1_CLOCK, tier1_refusal};
        use kink_native::execution::SolverProfile;
        let resource = kink_native::BACKEND_OPTIONS;
        let clock = k_rust::backend::BackendOptions {
            smt_resource_limit: None,
            ..resource
        };
        assert_eq!(tier1_refusal(SolverProfile::NoZ3, resource), None);
        assert_eq!(tier1_refusal(SolverProfile::NoZ3, clock), None);
        assert_eq!(tier1_refusal(SolverProfile::Z3, clock), Some(TIER1_CLOCK));
        assert!(TIER1_CLOCK.contains("z3 profile"), "{TIER1_CLOCK}");
        assert_eq!(
            tier1_refusal(SolverProfile::Z3, resource),
            kink_native::solver_named().err()
        );
        let dir = fixture("map-store", "tier-one-profile");
        let manifest = dir.join("FLOW.toml");
        let (document, ok) = search(&manifest, &dir.join("MUTATIONS.toml"), &[]);
        assert!(ok, "{document:#}");
        let cache = &document["outcome_cache"];
        assert_eq!(cache["enabled"], true, "{cache:#}");
        assert!(cache["records_written"].as_u64().unwrap() > 0, "{cache:#}");
        assert!(cache_of(&manifest).join(OUTCOMES_DIRECTORY).exists());
        let (again, ok) = search(&manifest, &dir.join("MUTATIONS.toml"), &[]);
        assert!(ok, "{again:#}");
        assert_eq!(statuses(&again), statuses(&document));
        assert_eq!(
            again["outcome_cache"]["mutations_from_cache"],
            document["mutations"].as_array().unwrap().len(),
            "{again:#}"
        );
    }

    #[test]
    #[ignore = "kink"]
    fn a_depth_bound_unknown_is_cached_with_its_cause() {
        // (d), since CF-33d: countdown never ends on the mutant. Under a small depth bound its
        // outcome is unknown; the depth bound counts steps, not time, and is in the outcome key,
        // so the unknown is a function of the key and is written with its cause, beside twice's
        // agreement. The next command decides the row from the cache with no call, and reports
        // the cached unknown's cause as the live one gave it. (The timeout case, which is never
        // written: warm_and_forged_records_on_loop.)
        let dir = fixture("loop", "depth-unknown");
        let manifest = dir.join("FLOW-depth.toml");
        let mutations = dir.join("MUTATIONS.toml");
        let (first, ok) = search(&manifest, &mutations, &[]);
        assert!(ok, "{first:#}");
        assert_eq!(
            status_only(&first),
            vec![("countdown-escapes".to_owned(), "unknown".to_owned())]
        );
        assert_eq!(
            records(&manifest, &first, "countdown-escapes"),
            BTreeMap::from([
                ("countdown".to_owned(), "unknown".to_owned()),
                ("twice".to_owned(), "agree".to_owned()),
            ])
        );
        let cause = |document: &Value| {
            mutation(document, "countdown-escapes")["executed"]
                .as_array()
                .unwrap()
                .iter()
                .find(|entry| entry["program"] == "countdown")
                .unwrap()["cause"]
                .clone()
        };
        let live_cause = cause(&first);
        assert!(
            live_cause
                .as_str()
                .is_some_and(|cause| cause.contains("max_depth")),
            "{live_cause}"
        );
        let file = read_json(&outcome_file(&manifest, &first, "countdown-escapes"));
        assert_eq!(
            file["records"][program_digest(&first, "countdown")]["cause"],
            live_cause
        );
        let (second, ok) = search(&manifest, &mutations, &[]);
        assert!(ok, "{second:#}");
        assert_eq!(statuses(&second), statuses(&first));
        assert!(calls(&second, "countdown-escapes").is_empty());
        assert_eq!(
            executed(&second, "countdown-escapes"),
            vec![
                ("countdown".into(), "unknown".into(), true),
                ("twice".into(), "agree".into(), true),
            ]
        );
        assert_eq!(cause(&second), live_cause);
        assert_eq!(second["outcome_cache"]["mutations_from_cache"], 1);
        assert_eq!(second["outcome_cache"]["records_written"], 0);
        // `run --verify` re-proves the cached unknown, its cause included.
        let (verified, ok) = search_mode(&manifest, &mutations, &[], RunMode::Verify);
        assert!(ok, "{verified:#}");
        assert_eq!(verified["mismatches"], json!([]));
        // A record whose cause was edited and resealed differs from the live run's.
        forge_record(
            &manifest,
            &first,
            "countdown-escapes",
            "countdown",
            true,
            |record| {
                record["cause"] = json!("forged");
            },
        );
        let (forged, ok) = search_mode(&manifest, &mutations, &[], RunMode::Verify);
        assert!(!ok, "{forged:#}");
        assert_eq!(
            mutation(&forged, "countdown-escapes")["reason"],
            "outcome-mismatch:countdown"
        );
        assert_eq!(forged["mismatches"][0]["cached"]["cause"], "forged");
        assert_eq!(forged["mismatches"][0]["live"]["cause"], live_cause);
    }

    /// CF-33d (review): the kill search runs the mutants under `[budget] smt_resource_limit`,
    /// the units its outcome context names, and an unknown that rests on undecided solver answers
    /// is cached with them. `pick-anything` makes `go(N)` choose an existential `?M`, so the
    /// mutant's run branches on `?M >Int 0`, a question for Z3 (the baseline's concrete run asks
    /// none). With kink's units Z3 decides both branches feasible and `go` kills the mutation;
    /// with 1 unit (8 with the retries) it decides neither, so the mutant's leaves are unknown,
    /// with a nonzero `smt_unknowns`. Before the fix the kill search ran at kink's default units
    /// whatever the manifest said, and killed. The unknown is written with its cause and counts,
    /// answered from the cache by the next command, and re-proved by `run --verify`.
    #[cfg(feature = "z3")]
    #[test]
    #[ignore = "kink"]
    fn the_kill_search_uses_the_manifests_solver_units_and_caches_an_undecided_unknown() {
        let dir = scratch("undecided");
        fs::write(
            dir.join("und.k"),
            r#"module UND-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= go(Int) [symbol(go)]
endmodule
module UND
  imports UND-SYNTAX
  imports INT
  configuration <k> $PGM:Prog </k> <out> 0 </out>
  syntax KItem ::= pick(Int) [symbol(pick)]
  rule [go]: <k> go(N) => pick(N) ... </k>
  rule [pos]: <k> pick(N) => .K ... </k> <out> _ => 1 </out> requires N >Int 0
  rule [neg]: <k> pick(N) => .K ... </k> <out> _ => 2 </out> requires N <=Int 0
endmodule
"#,
        )
        .unwrap();
        let manifest = |units: &str| {
            let path = dir.join(format!("FLOW-{units}.toml"));
            fs::write(
                &path,
                format!(
                    r#"[spec]
entry = "und.k"
main_module = "UND"
syntax_module = "UND-SYNTAX"

[budget]
time_ms = 600000
{units}

[[program]]
id = "go"
text = "go(1)"
"#
                ),
            )
            .unwrap();
            path
        };
        let mutations = dir.join("MUTATIONS.toml");
        fs::write(
            &mutations,
            r#"[[mutation]]
id = "pick-anything"
note = "go picks any integer"
  [[mutation.edit]]
  rule = "go"
  find = "pick(N)"
  replace = "pick(?M:Int)"
"#,
        )
        .unwrap();
        let entry = |document: &Value| mutation(document, "pick-anything")["executed"][0].clone();
        // kink's units: decided, killed.
        let (killed, ok) = search(&manifest(""), &mutations, &[]);
        assert!(ok, "{killed:#}");
        assert_eq!(
            status_only(&killed),
            [("pick-anything".to_owned(), "killed".to_owned())]
        );

        // One unit: undecided, unknown, with the undecided answers counted.
        let tiny = manifest("smt_resource_limit = 1");
        let (first, ok) = search(&tiny, &mutations, &[]);
        assert!(ok, "{first:#}");
        assert_eq!(
            status_only(&first),
            [("pick-anything".to_owned(), "unknown".to_owned())]
        );
        let live = entry(&first);
        assert_eq!(live["cached"], false, "{live:#}");
        assert!(
            live["smt_unknowns"].as_u64().unwrap_or(0) > 0
                || live["decider_smt_unknowns"].as_u64().unwrap_or(0) > 0,
            "{live:#}"
        );
        assert_eq!(
            records(&tiny, &first, "pick-anything"),
            BTreeMap::from([("go".to_owned(), "unknown".to_owned())])
        );
        // The next command answers it from the cache, as the live entry reported it.
        let (second, ok) = search(&tiny, &mutations, &[]);
        assert!(ok, "{second:#}");
        assert!(calls(&second, "pick-anything").is_empty(), "{second:#}");
        let cached = entry(&second);
        assert_eq!(cached["cached"], true);
        for field in ["outcome", "cause", "smt_unknowns", "decider_smt_unknowns"] {
            assert_eq!(cached[field], live[field], "{field}");
        }
        let (verified, ok) = search_mode(&tiny, &mutations, &[], RunMode::Verify);
        assert!(ok, "{verified:#}");
        assert_eq!(verified["mismatches"], json!([]));
    }

    #[test]
    #[ignore = "kink"]
    fn the_binary_parses_run_verify() {
        // `run --verify` through the binary: the flag is accepted once; a repeated flag is a
        // usage error.
        let dir = fixture("calc", "verify-binary");
        let binary = env!("CARGO_BIN_EXE_kink-flow");
        for (args, code) in [
            (
                vec!["run", "FLOW.toml", "MUTATIONS.toml", "--verify", "--verify"],
                EXIT_UNASKED,
            ),
            (
                vec![
                    "run",
                    "FLOW.toml",
                    "MUTATIONS.toml",
                    "--only",
                    "add-becomes-sub",
                    "--verify",
                ],
                EXIT_YES,
            ),
        ] {
            let output = Command::new(binary)
                .args(&args)
                .current_dir(&dir)
                .output()
                .unwrap();
            assert_eq!(output.status.code(), Some(i32::from(code)), "{args:?}");
            if code == EXIT_YES {
                let document: Value = serde_json::from_slice(&output.stdout).unwrap();
                assert_eq!(document["outcome_cache"]["verify"], true);
                assert_eq!(document["mismatches"], json!([]));
                assert_eq!(mutation(&document, "add-becomes-sub")["status"], "killed");
            }
        }
    }

    /// The determinism failure `outcome-conflict` is meant for stays one (flow F-16): a mutant
    /// that no longer compiles (here `plus-unbound`, rejected) next to a cached agreement, which
    /// says the mutant ran, is the corpus error `outcome-conflict`: no verdict, nothing written,
    /// the run stops.
    #[test]
    #[ignore = "kink"]
    fn a_rejected_mutant_next_to_cached_agreements_is_an_outcome_conflict() {
        let (dir, cold) = macro_after_cold("rejected-conflict");
        let manifest = dir.join("FLOW.toml");
        let mutations = dir.join("MUTATIONS.toml");
        forge_agreements(
            &manifest,
            &cold,
            "plus-becomes-minus",
            "plus-unbound",
            &["seven"],
        );
        let before = fs::read_to_string(outcome_file(&manifest, &cold, "plus-unbound")).unwrap();
        let (document, ok) = search(&manifest, &mutations, &["plus-unbound"]);
        assert!(!ok, "{document:#}");
        let row = mutation(&document, "plus-unbound");
        assert_eq!(row["status"], "error");
        assert_eq!(row["reason"], "outcome-conflict", "{row:#}");
        assert_eq!(calls(&document, "plus-unbound"), vec![strings(&["sum"])]);
        assert_eq!(document["outcome_cache"]["records_written"], 0);
        assert_eq!(
            fs::read_to_string(outcome_file(&manifest, &cold, "plus-unbound")).unwrap(),
            before
        );
    }

    #[test]
    #[ignore = "kink"]
    fn a_new_program_runs_alone_and_only_for_survivors() {
        // (b): the survivor runs on the new program alone; the killed mutations make no call.
        let (dir, cold) = calc_after_cold("new-program");
        let manifest = dir.join("FLOW.toml");
        let mutations = dir.join("MUTATIONS.toml");
        append(
            &manifest,
            "\n[[program]]\nid = \"more\"\ntext = \"3 + 4\"\n",
        );
        let (warm, ok) = search(&manifest, &mutations, &[]);
        assert!(ok, "{warm:#}");
        assert_eq!(statuses(&warm), statuses(&cold));
        for row in rows(&warm) {
            let id = row["id"].as_str().unwrap();
            if row["status"] == "killed" {
                assert_eq!(row["calls"], json!([]), "{id}");
            }
        }
        assert_eq!(calls(&warm, "add-swaps-operands"), vec![strings(&["more"])]);
        assert_eq!(
            executed(&warm, "add-swaps-operands"),
            vec![
                ("add".into(), "agree".into(), true),
                ("nested".into(), "agree".into(), true),
                ("inline".into(), "agree".into(), true),
                ("sub".into(), "agree".into(), true),
                ("more".into(), "agree".into(), false),
            ]
        );
    }

    #[test]
    #[ignore = "kink"]
    fn a_corpus_error_writes_no_record_and_leaves_the_lock() {
        // (d) and (i): a hand-edited result run digest is a corpus error; no record is written
        // for the mutation, and the lock, whose recorded killer names no program, is left as it
        // was, since the run judged no mutation.
        let dir = fixture("calc", "corpus-error");
        let manifest = dir.join("FLOW.toml");
        let mutations = dir.join("MUTATIONS.toml");
        let (filled, status) = results(&manifest, &ResultsOptions::default());
        assert_eq!(status, EXIT_YES);
        let record = result_record_path(&manifest, &filled, "add");
        let mut value = read_json(&record);
        value["run_sha256"] = json!("0".repeat(64));
        write_json(&record, &value);
        fs::write(
            lock_of(&manifest),
            "schema = \"kink-flow-verdicts\"\ndocument = \"run\"\n\n[[mutation]]\nid = \
             \"add-becomes-sub\"\nstatus = \"killed\"\nkiller = \"gone\"\n",
        )
        .unwrap();
        let lock = fs::read_to_string(lock_of(&manifest)).unwrap();
        let (document, ok) = search(&manifest, &mutations, &[]);
        assert!(!ok);
        assert_eq!(
            status_only(&document),
            vec![("add-becomes-sub".to_owned(), "error".to_owned())]
        );
        assert_eq!(
            mutation(&document, "add-becomes-sub")["reason"],
            "baseline-mismatch:add"
        );
        assert_eq!(
            mutation(&document, "add-becomes-sub")["killer_change"],
            "not-in-corpus"
        );
        assert!(!outcome_file(&manifest, &document, "add-becomes-sub").exists());
        assert_eq!(document["outcome_cache"]["records_written"], 0);
        assert_eq!(
            (&document["lock"]["status"], &document["lock"]["reason"]),
            (&json!("not-written"), &json!("stopped"))
        );
        assert_eq!(fs::read_to_string(lock_of(&manifest)).unwrap(), lock);
    }

    /// Re-pin R0c-fix-1 deliverable 1 (decision 2 per test, Sebastien 2026-10-17), through
    /// kink-flow's first-kill search: the mutation `I +Int 0` of the rewrite rule `tdiv` keeps `td`'s
    /// `total` (re-pin R0c-fix-2: its edit does not reach `td`, so the claim stays), contradicts it
    /// on `tdiv(-1)` and distinguishes on `tdiv(1)`. (Before R0c-fix-2 the mutation edited `td`'s
    /// equation and contradicted the claim on `tdiv(0)`; such a mutation now runs without the claim
    /// and `tdiv(0)` kills it, see `a_mutation_drops_the_claims_its_edit_leaves_unbacked`.) In both program orders the
    /// mutation is killed by `kill`, whose runs are clean, and the contradicting program is listed
    /// `unknown` with failure `contradicted-claim` when it ran (under R0c's mutant-wide rule the
    /// contradicting program first made the mutation `unknown` and wrote no record). The killing
    /// program's record is written (tier 1, no-Z3 profile): it rests on that program's runs alone.
    #[test]
    #[ignore = "kink"]
    fn a_contradicted_claim_leaves_the_kill_of_another_program_standing() {
        let definition = r"module CONTRA-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= tdiv(Int) [symbol(tdiv)]
                | val(Int) [symbol(val)]
  syntax Int ::= td(Int) [function, total, symbol(td)]
endmodule

module CONTRA
  imports CONTRA-SYNTAX
  imports INT
  configuration <k> $PGM:Prog </k>
  rule [tdeq]: td(I) => 10 /Int (I +Int 1)
  rule [tdiv]: <k> tdiv(I) => val(td(I +Int 1)) </k>
endmodule
";
        let mutations = r#"[[mutation]]
id = "denominator"
misunderstanding = "a test mutation"
  [[mutation.edit]]
  rule = "tdiv"
  find = "I +Int 1"
  replace = "I +Int 0"
"#;
        for order in [["contra", "kill"], ["kill", "contra"]] {
            let (status, killer, reason) = ("killed", Some("kill"), None::<&str>);
            let dir = scratch(&format!("contradicted-{}", order[0]));
            fs::write(dir.join("contra.k"), definition).unwrap();
            let programs = order
                .iter()
                .map(|id| {
                    format!(
                        "[[program]]\nid = \"{id}\"\ntext = \"tdiv({})\"\n",
                        if *id == "contra" { -1 } else { 1 }
                    )
                })
                .collect::<String>();
            fs::write(
                dir.join("FLOW.toml"),
                format!(
                    "[spec]\nentry = \"contra.k\"\nmain_module = \"CONTRA\"\nsyntax_module = \
                     \"CONTRA-SYNTAX\"\n\n{programs}"
                ),
            )
            .unwrap();
            fs::write(dir.join("MUTATIONS.toml"), mutations).unwrap();
            let manifest = dir.join("FLOW.toml");
            let (document, ok) = search(&manifest, &dir.join("MUTATIONS.toml"), &[]);
            assert!(ok, "{document:#}");
            let row = mutation(&document, "denominator");
            assert_eq!(
                (
                    row["status"].as_str(),
                    row["killer"].as_str(),
                    row["reason"].as_str()
                ),
                (Some(status), killer, reason),
                "{order:?} {row:#}"
            );
            let executed = row["executed"].as_array().unwrap();
            let entry = |program: &str| {
                executed
                    .iter()
                    .find(|entry| entry["program"] == program)
                    .cloned()
            };
            assert_eq!(
                entry("kill").map(|entry| entry["outcome"].clone()),
                Some(json!("distinguish")),
                "{row:#}"
            );
            if order[0] == "contra" {
                let contra = entry("contra").expect("the contradicting program ran first");
                assert_eq!(
                    (contra["outcome"].as_str(), contra["failure"].as_str()),
                    (Some("unknown"), Some("contradicted-claim")),
                    "{row:#}"
                );
            } else {
                assert_eq!(entry("contra"), None, "{row:#}");
            }
            assert!(
                outcome_file(&manifest, &document, "denominator").exists(),
                "{order:?}"
            );
        }
    }

    #[test]
    #[ignore = "kink"]
    fn partially_cached_statuses_are_cold_statuses_on_loop() {
        // The timeout mixes twice's cached agreement with a live call over countdown.
        assert!(partial("loop", "FLOW-search.toml", "MUTATIONS.toml") > 0);
    }

    /// Re-pin R0b deliverables 7 and 9 (decision 1; finding B-02): a mutation that makes the
    /// specification apply `choice` to a map (an item domains.md does not name) is `unknown` with
    /// reason `implementation-chosen-hook`, whether its value would agree with the baseline's
    /// (`choice-agrees`, a survivor before R0b) or not (`choice-differs`, killed before R0b), and no
    /// outcome record is written for it; the other
    /// mutations keep their statuses and records, and each record carries the writing process's
    /// memory allowance outside its key and digest (decision 5, finding B-07).
    ///
    /// Re-pin kink27 R3-CENSUS-RUNLEVEL: `MAP.choice` is a k-rust class, judged per run by the
    /// run's `implementationChosenValues` list, not by the census. On `store(1, 2)` the memory is
    /// empty, so `choice-agrees` takes `choice` of the one binding `2 |-> 1` and `choice-differs`
    /// of `1 |-> 2`: a map of one item has one choice in every model, k-rust notes none, and each
    /// run is evidence. `choice-agrees` stores 2 at 1, the baseline's memory, and survives;
    /// `choice-differs` stores 1 at 1 and is killed by `store`; both are cached as any compared
    /// status is (before: `unknown`, `implementation-chosen-hook`, never cached). The new
    /// `choice-of-two` takes `choice` of `1 |-> 2` and `2 |-> 1`, an item the definition leaves
    /// open, which k-rust notes (class `item`): it is `unknown`, reason `implementation-chosen-value`,
    /// and never cached.
    #[test]
    #[ignore = "kink"]
    fn an_implementation_chosen_mutant_is_unknown_and_never_cached() {
        let dir = fixture("map-store", "implementation-chosen");
        let manifest = dir.join("FLOW.toml");
        let mutations = dir.join("MUTATIONS.toml");
        append(
            &mutations,
            r#"[[mutation]]
id = "choice-agrees"
misunderstanding = "a test mutation"
  [[mutation.edit]]
  rule = "store"
  find = "M[K <- V]"
  replace = "M[K <- choice(M (V |-> K))]"
[[mutation]]
id = "choice-differs"
misunderstanding = "a test mutation"
  [[mutation.edit]]
  rule = "store"
  find = "M[K <- V]"
  replace = "M[K <- choice(M (K |-> V))]"
[[mutation]]
id = "choice-of-two"
misunderstanding = "a test mutation"
  [[mutation.edit]]
  rule = "store"
  find = "M[K <- V]"
  replace = "M[K <- choice(M (K |-> V) (V |-> K))]"
"#,
        );
        let (document, ok) = search(&manifest, &mutations, &[]);
        assert!(ok, "{document:#}");
        let row = mutation(&document, "choice-of-two");
        assert_eq!(
            (row["status"].as_str(), row["reason"].as_str()),
            (Some("unknown"), Some("implementation-chosen-value")),
            "{row:#}"
        );
        assert_eq!(
            executed(&document, "choice-of-two"),
            [("store".to_owned(), "unknown".to_owned(), false)],
            "{row:#}"
        );
        assert!(
            row["executed"][0]["cause"]
                .as_str()
                .is_some_and(|cause| cause.starts_with("implementation-chosen-value")),
            "{row:#}"
        );
        assert_eq!(
            statuses_of(
                &document,
                &[
                    "value-plus-one",
                    "key-value-swap",
                    "choice-agrees",
                    "choice-differs"
                ]
            ),
            [
                (
                    "value-plus-one".to_owned(),
                    "killed".to_owned(),
                    Some("store".to_owned())
                ),
                (
                    "key-value-swap".to_owned(),
                    "killed".to_owned(),
                    Some("store".to_owned())
                ),
                ("choice-agrees".to_owned(), "survived".to_owned(), None),
                (
                    "choice-differs".to_owned(),
                    "killed".to_owned(),
                    Some("store".to_owned())
                ),
            ]
        );
        assert!(!outcome_file(&manifest, &document, "choice-of-two").exists());
        for id in ["choice-agrees", "choice-differs"] {
            assert!(outcome_file(&manifest, &document, id).exists(), "{id}");
        }
        let file = read_json(&outcome_file(&manifest, &document, "value-plus-one"));
        let record = file["records"]
            .as_object()
            .unwrap()
            .values()
            .next()
            .unwrap()
            .clone();
        assert_eq!(
            record["allowance_bytes"],
            json!(k_rust::k_rust_backend::allowance::Allowance::of_process().bytes()),
            "{record:#}"
        );
        assert!(file["context"].get("allowance_bytes").is_none(), "{file:#}");
        // The allowance is outside the digest: the record seals without it.
        let sealed = record_sha256(
            file["context_sha256"].as_str().unwrap(),
            file["mutation_identity"].as_str().unwrap(),
            file["records"].as_object().unwrap().keys().next().unwrap(),
            record["baseline_run_sha256"].as_str().unwrap(),
            record["outcome"].as_str().unwrap(),
            &record["slots"]
                .as_array()
                .unwrap()
                .iter()
                .map(|slot| slot.as_str().unwrap())
                .collect::<Vec<_>>(),
            record["mutant_run_sha256"].as_str().unwrap(),
            &record["difference"],
            &kink_flow::outcomes::OutcomeRecord::report_value(&record),
        );
        assert_eq!(record["record_sha256"], json!(sealed.to_string()));
    }

    /// F-14 review 1 m3 (flow F-16): a recorded killer that does not kill runs again in the
    /// canonical call; it is listed once in `executed` (with the canonical call's run, the one the
    /// status folds) and its record is counted once in `records_written`.
    #[test]
    #[ignore = "kink"]
    fn a_recorded_killer_run_twice_is_listed_and_counted_once() {
        let (dir, _) = calc_after_cold("record-counted-once");
        let manifest = dir.join("FLOW.toml");
        let mutations = dir.join("MUTATIONS.toml");
        set_record(&manifest, "add-swaps-operands", "add");
        forget_outcomes(&manifest);
        let (document, ok) = search(&manifest, &mutations, &["add-swaps-operands"]);
        assert!(ok, "{document:#}");
        assert_eq!(
            status_only(&document),
            vec![("add-swaps-operands".into(), "survived".into())]
        );
        assert_eq!(
            calls(&document, "add-swaps-operands"),
            vec![
                strings(&["add"]),
                strings(&["add", "nested", "inline", "sub"])
            ]
        );
        assert_eq!(
            executed(&document, "add-swaps-operands"),
            vec![
                ("add".into(), "agree".into(), false),
                ("nested".into(), "agree".into(), false),
                ("inline".into(), "agree".into(), false),
                ("sub".into(), "agree".into(), false),
            ]
        );
        assert_eq!(document["outcome_cache"]["records_written"], 4);
        assert_eq!(records(&manifest, &document, "add-swaps-operands").len(), 4);
        let row = mutation(&document, "add-swaps-operands");
        assert_eq!(
            (&row["recorded_killer"], &row["killer_change"]),
            (&json!("add"), &json!("no-longer-kills"))
        );
    }

    #[test]
    #[ignore = "kink"]
    fn warm_and_forged_records_on_loop() {
        // countdown never ends on the mutant: under a small time bound its outcome is a timeout,
        // which is never written (d); twice's agreement is.
        let (dir, cold) = after_cold("loop", "FLOW-search.toml", "MUTATIONS.toml", "loop-records");
        let manifest = dir.join("FLOW-search.toml");
        assert_eq!(
            status_only(&cold),
            vec![("countdown-escapes".to_owned(), "timeout".to_owned())]
        );
        assert_eq!(
            records(&manifest, &cold, "countdown-escapes"),
            BTreeMap::from([("twice".to_owned(), "agree".to_owned())])
        );
        warm_and_forged("loop", "FLOW-search.toml", "MUTATIONS.toml");
    }

    #[test]
    #[ignore = "kink"]
    fn a_comment_or_layout_edit_keeps_every_result_and_outcome() {
        // (g): the result cache and tier 1 are keyed by the execution digest, the loaded
        // definition without positions, so neither a comment at the end nor a comment and blank
        // lines at the top (every line shifts) misses: the specification digest changes, the
        // execution digest does not, no baseline runs, and every mutation the cold run cached is
        // decided from tier 1 with no call, with the cold run's statuses and killers.
        let (dir, cold) = calc_after_cold("comment");
        let manifest = dir.join("FLOW.toml");
        let mutations = dir.join("MUTATIONS.toml");
        let calc = dir.join("calc.k");
        let mut previous = cold["spec"]["digest"].clone();
        for (name, edit) in [
            ("comment at the end", "end"),
            ("comment and blank lines at the top", "top"),
        ] {
            let text = fs::read_to_string(&calc).unwrap();
            let text = match edit {
                "end" => format!("{text}// a comment at the end\n"),
                _ => {
                    // Every line moves down by three, so the mutations addressed by line are
                    // updated as their author would update them; no other input changes.
                    edit_lines(
                        &mutations,
                        &[("line = 23", "line = 26"), ("line = 21", "line = 24")],
                    );
                    format!("// a comment at the top\n\n\n{text}")
                }
            };
            fs::write(&calc, text).unwrap();
            warm_after_no_change(&manifest, &mutations, &cold, name);
            let (edited, ok) = search(&manifest, &mutations, &[]);
            assert!(ok, "{edited:#}");
            assert_ne!(edited["spec"]["digest"], previous, "{name}");
            assert_eq!(
                edited["spec"]["execution_digest"], cold["spec"]["execution_digest"],
                "{name}"
            );
            assert!(
                edited["programs"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .all(|program| program["cached"] == true),
                "{name}: {edited:#}"
            );
            assert_eq!(edited["baseline_runs"]["live"], 0, "{name}");
            assert_eq!(statuses(&edited), statuses(&cold), "{name}");
            previous = edited["spec"]["digest"].clone();
        }
    }

    #[test]
    #[ignore = "kink"]
    fn a_mixed_cached_and_live_status_is_the_cold_status() {
        // (e): mul-becomes-add survives a corpus where 2 * 2 equals 2 + 2; a new program 2 * 3
        // kills it. Cached agreements plus the live kill give the cold run's status and killer.
        let text = "\n[[program]]\nid = \"square\"\ntext = \"2 * 2\"\n";
        let dir = fixture("calc", "mixed");
        let manifest = dir.join("FLOW.toml");
        let mutations = dir.join("MUTATIONS.toml");
        edit(
            &manifest,
            "[[program]]\nid = \"nested\"\nfile = \"programs/nested.calc\"\n",
            "",
        );
        edit(
            &manifest,
            "[[program]]\nid = \"inline\"\ntext = \"2 * 3 + 1\"\n",
            "",
        );
        append(&manifest, text);
        let (first, ok) = search(&manifest, &mutations, &["mul-becomes-add"]);
        assert!(ok, "{first:#}");
        assert_eq!(mutation(&first, "mul-becomes-add")["status"], "survived");
        append(
            &manifest,
            "\n[[program]]\nid = \"product\"\ntext = \"2 * 3\"\n",
        );
        let (mixed, ok) = search(&manifest, &mutations, &["mul-becomes-add"]);
        assert!(ok, "{mixed:#}");
        assert_eq!(
            calls(&mixed, "mul-becomes-add"),
            vec![strings(&["product"])]
        );
        assert_eq!(
            executed(&mixed, "mul-becomes-add")
                .into_iter()
                .map(|(program, _, cached)| (program, cached))
                .collect::<Vec<_>>(),
            vec![
                ("square".into(), true),
                ("add".into(), true),
                ("sub".into(), true),
                ("product".into(), false),
            ]
        );
        // The same files with a fresh cache.
        let cold_dir = scratch("mixed-cold").join("calc");
        copy_dir(&dir, &cold_dir);
        let (cold, ok) = search(
            &cold_dir.join("FLOW.toml"),
            &cold_dir.join("MUTATIONS.toml"),
            &["mul-becomes-add"],
        );
        assert!(ok, "{cold:#}");
        assert_eq!(statuses(&mixed), statuses(&cold));
        assert_eq!(
            statuses(&mixed),
            vec![(
                "mul-becomes-add".to_owned(),
                "killed".to_owned(),
                Some("product".to_owned())
            )]
        );
    }

    #[test]
    #[ignore = "kink"]
    fn partially_cached_statuses_are_cold_statuses_on_calc_statuses() {
        // add-commutes mixes cached agreements with a live call over add.
        assert!(partial("calc", "FLOW.toml", "MUTATIONS-statuses.toml") > 0);
    }

    #[test]
    #[ignore = "kink"]
    fn a_recorded_killer_that_left_the_corpus_is_replaced() {
        // (g): no-mul's recorded killer is nested; nested leaves the corpus. The record names no
        // program: the row says so, the status is a cold run's, and a run of the whole list
        // records the search's first killer.
        let (dir, _) = calc_after_cold("record-removed");
        let manifest = dir.join("FLOW.toml");
        let mutations = dir.join("MUTATIONS.toml");
        assert_eq!(
            recorded_killers(&manifest)["no-mul"].as_deref(),
            Some("nested")
        );
        edit(
            &manifest,
            "[[program]]\nid = \"nested\"\nfile = \"programs/nested.calc\"\n",
            "",
        );
        let (removed, ok) = search(&manifest, &mutations, &["no-mul"]);
        assert!(ok, "{removed:#}");
        assert_eq!(
            mutation(&removed, "no-mul")["killer_change"],
            "not-in-corpus"
        );
        assert_eq!(mutation(&removed, "no-mul")["unusable_killer"], Value::Null);
        assert_eq!(removed["lock"]["status"], "not-written");
        let cold_dir = scratch("record-removed-cold").join("calc");
        copy_dir(&dir, &cold_dir);
        let (cold, ok) = search(
            &cold_dir.join("FLOW.toml"),
            &cold_dir.join("MUTATIONS.toml"),
            &["no-mul"],
        );
        assert!(ok, "{cold:#}");
        assert_eq!(statuses(&removed), statuses(&cold));
        let (whole, ok) = search(&manifest, &mutations, &[]);
        assert!(ok, "{whole:#}");
        assert_eq!(whole["lock"]["status"], "written");
        assert_eq!(
            recorded_killers(&manifest)["no-mul"].as_deref(),
            mutation(&cold, "no-mul")["killer"].as_str()
        );
    }

    #[test]
    #[ignore = "kink"]
    fn warm_and_forged_records_on_calc_statuses() {
        warm_and_forged("calc", "FLOW.toml", "MUTATIONS-statuses.toml");
    }

    /// F-14 review 1 m2 (flow F-16): a mutant-scope infrastructure failure while cached agreements
    /// exist gives the status a cold run gives (error, reason infrastructure), not the corpus
    /// error `outcome-conflict`; the run goes on, the cached agreements do not enter the row, and
    /// nothing is written.
    #[test]
    #[ignore = "kink"]
    fn an_infrastructure_failure_next_to_cached_agreements_is_the_cold_status() {
        let (dir, cold) = macro_after_cold("infrastructure-conflict");
        let manifest = dir.join("FLOW.toml");
        let mutations = dir.join("MUTATIONS.toml");
        forge_agreements(
            &manifest,
            &cold,
            "plus-becomes-minus",
            "plus-in-a-group",
            &["seven"],
        );
        let before = fs::read_to_string(outcome_file(&manifest, &cold, "plus-in-a-group")).unwrap();
        let (document, ok) = search(&manifest, &mutations, &["plus-in-a-group"]);
        assert!(ok, "no corpus error: {document:#}");
        let row = mutation(&document, "plus-in-a-group");
        let cold_row = mutation(&cold, "plus-in-a-group");
        assert_eq!(
            (&row["status"], &row["reason"]),
            (&cold_row["status"], &cold_row["reason"])
        );
        assert_eq!(row["reason"], "infrastructure");
        // The live call ran over the program without a record only; the cached agreement left
        // the row and the counts, so the row's executed list is the cold row's.
        assert_eq!(calls(&document, "plus-in-a-group"), vec![strings(&["sum"])]);
        assert_eq!(row["executed"], cold_row["executed"]);
        assert_eq!(document["outcome_cache"]["programs_from_cache"], 0);
        assert_eq!(document["outcome_cache"]["records_written"], 0);
        assert_eq!(
            fs::read_to_string(outcome_file(&manifest, &cold, "plus-in-a-group")).unwrap(),
            before
        );
        // `run --verify` re-proves the forged agreement and reports it.
        let (verified, ok) =
            search_mode(&manifest, &mutations, &["plus-in-a-group"], RunMode::Verify);
        assert!(!ok);
        let row = mutation(&verified, "plus-in-a-group");
        assert_eq!(row["status"], "error");
        assert!(
            row["reason"]
                .as_str()
                .unwrap()
                .starts_with("outcome-mismatch:"),
            "{row:#}"
        );
    }

    #[test]
    #[ignore = "kink"]
    fn warm_and_forged_records_on_calc() {
        warm_and_forged("calc", "FLOW.toml", "MUTATIONS.toml");
    }

    #[test]
    #[ignore = "kink"]
    fn hand_edited_contexts_and_records_are_ignored() {
        // (c): a hand-changed context field (kink_build, and the k_rust_revision and result_schema
        // of the context's kink identity, packet CACHE-ID), a hand-changed baseline run digest
        // (record digest recomputed), a record whose digest does not recompute and a record whose
        // outcome contradicts its slots each miss. One forgery per mutation file, so one run checks
        // them all.
        let (dir, cold) = calc_after_cold("forged");
        let manifest = dir.join("FLOW.toml");
        let mutations = dir.join("MUTATIONS.toml");
        for (id, field, value) in [
            (
                "add-becomes-sub",
                "/context/kink_build",
                json!("0".repeat(64)),
            ),
            (
                "sub-off-by-one",
                "/context/kink/k_rust_revision",
                json!("0".repeat(40)),
            ),
            (
                "mul-becomes-add",
                "/context/kink/result_schema",
                json!("kink-flow/result/v1"),
            ),
        ] {
            let path = outcome_file(&manifest, &cold, id);
            let mut file = read_json(&path);
            *file.pointer_mut(field).unwrap() = value;
            write_json(&path, &file);
        }
        forge_record(&manifest, &cold, "no-mul", "nested", true, |r| {
            r["baseline_run_sha256"] = json!("0".repeat(64));
        });
        // The survivor: add's record no longer matches its digest, and nested's is resealed with
        // an outcome its slots contradict.
        forge_record(&manifest, &cold, "add-swaps-operands", "add", false, |r| {
            r["mutant_run_sha256"] = json!("0".repeat(64));
        });
        forge_record(
            &manifest,
            &cold,
            "add-swaps-operands",
            "nested",
            true,
            |r| {
                r["outcome"] = json!("killed");
            },
        );
        let (document, ok) = search(&manifest, &mutations, &[]);
        assert!(ok, "{document:#}");
        assert_eq!(statuses(&document), statuses(&cold));
        for (id, status, killer) in statuses(&document) {
            if status == "killed" {
                assert_eq!(mutation(&document, &id)["killer_source"], "record", "{id}");
                assert_eq!(calls(&document, &id), vec![vec![killer.unwrap()]], "{id}");
            }
        }
        assert_eq!(
            calls(&document, "add-swaps-operands"),
            vec![strings(&["add", "nested"])]
        );
        assert_eq!(document["outcome_cache"]["mutations_from_cache"], 0);
        // The live calls rewrote each file with fresh records: the next run decides from tier 1.
        let (warm, ok) = search(&manifest, &mutations, &["add-becomes-sub"]);
        assert!(ok);
        assert_eq!(
            mutation(&warm, "add-becomes-sub")["killer_source"],
            "outcome-cache"
        );
    }

    #[test]
    #[ignore = "kink"]
    fn a_change_of_an_input_misses_tier_1() {
        // (c): a change of a bound in the key is another context (`time_ms` is in no key: no
        // cached outcome depends on it); a program text change misses for that program only.
        let (dir, cold) = calc_after_cold("inputs");
        let manifest = dir.join("FLOW.toml");
        let mutations = dir.join("MUTATIONS.toml");
        let only = ["add-becomes-sub", "add-swaps-operands"];
        edit(
            &manifest,
            "syntax_module = \"CALC-SYNTAX\"\n",
            "syntax_module = \"CALC-SYNTAX\"\n\n[budget]\nmax_depth = 200000\n",
        );
        let (budget, ok) = search(&manifest, &mutations, &only);
        assert!(ok, "{budget:#}");
        assert_eq!(statuses(&budget), statuses_of(&cold, &only));
        assert_ne!(
            budget["outcome_cache"]["context_sha256"],
            cold["outcome_cache"]["context_sha256"]
        );
        assert_eq!(budget["outcome_cache"]["mutations_from_cache"], 0);
        assert_eq!(
            mutation(&budget, "add-becomes-sub")["killer_source"],
            "record"
        );
        assert_eq!(calls(&budget, "add-becomes-sub"), vec![strings(&["add"])]);
        assert_eq!(
            calls(&budget, "add-swaps-operands"),
            vec![strings(&["add", "nested", "inline", "sub"])]
        );
        // The program text of sub changes: only sub runs for the survivor.
        fs::write(dir.join("programs/sub.calc"), "9 - 4 - 3\n").unwrap();
        let (program, ok) = search(&manifest, &mutations, &only);
        assert!(ok, "{program:#}");
        assert_eq!(statuses(&program), statuses_of(&cold, &only));
        assert_eq!(
            mutation(&program, "add-becomes-sub")["killer_source"],
            "outcome-cache"
        );
        assert_eq!(
            calls(&program, "add-swaps-operands"),
            vec![strings(&["sub"])]
        );
    }

    #[test]
    #[ignore = "kink"]
    fn a_recorded_killer_that_stops_killing_changes_no_status() {
        // (g): after an edit of the add rule, (1 + 2) is stuck, so nested, the recorded killer of
        // mul-becomes-add, agrees on it; its call agrees and the canonical call decides.
        let (dir, first) = calc_after_cold("record-stops");
        let manifest = dir.join("FLOW.toml");
        let mutations = dir.join("MUTATIONS.toml");
        assert_eq!(mutation(&first, "mul-becomes-add")["killer"], "nested");
        edit(
            &dir.join("calc.k"),
            "rule [add]: I1:Int + I2:Int => I1 +Int I2",
            "rule [add]: I1:Int + I2:Int => I1 +Int I2 requires I1 >Int 5",
        );
        let cold_dir = scratch("record-stops-cold").join("calc");
        copy_dir(&dir, &cold_dir);
        let (edited, ok) = search(&manifest, &mutations, &[]);
        assert!(ok, "{edited:#}");
        let (cold, ok) = search(
            &cold_dir.join("FLOW.toml"),
            &cold_dir.join("MUTATIONS.toml"),
            &[],
        );
        assert!(ok, "{cold:#}");
        assert_eq!(status_only(&edited), status_only(&cold));
        assert_eq!(
            calls(&edited, "mul-becomes-add")[0],
            strings(&["nested"]),
            "the recorded killer is tried first"
        );
        assert_eq!(
            mutation(&edited, "mul-becomes-add")["killer_source"],
            "search"
        );
        assert_eq!(
            mutation(&edited, "mul-becomes-add")["killer_change"],
            "no-longer-kills"
        );
        assert_eq!(statuses(&edited), statuses(&cold));
    }

    #[test]
    #[ignore = "kink"]
    fn run_verify_reproves_every_record_and_reports_a_forged_one() {
        // (h): a warm cache gives no mismatch. A record forged to killed with a recomputed
        // record_sha256 makes the plain warm run report Killed: this is the trust premise of
        // README 7.5.1 (whoever can write the cache directory can forge a kill, as whoever can
        // write the build can). `run --verify` re-proves it and reports the forgery.
        let (dir, cold) = calc_after_cold("verify");
        let manifest = dir.join("FLOW.toml");
        let mutations = dir.join("MUTATIONS.toml");
        let lock_before = fs::read_to_string(lock_of(&manifest)).unwrap();
        let (verified, ok) = search_mode(&manifest, &mutations, &[], RunMode::Verify);
        assert!(ok, "{verified:#}");
        assert_eq!(verified["mismatches"], json!([]));
        assert_eq!(verified["outcome_cache"]["verify"], true);
        assert_eq!(verified["outcome_cache"]["enabled"], false);
        assert_eq!(verified["outcome_cache"]["records_written"], 0);
        assert_eq!(statuses(&verified), statuses(&cold));
        // Each killed mutation's cold call ran its killer; the survivor re-proved its four
        // agreements in the cold call itself.
        assert_eq!(
            calls(&verified, "add-swaps-operands"),
            vec![strings(&["add", "nested", "inline", "sub"])]
        );

        forge_record(&manifest, &cold, "add-swaps-operands", "add", true, |r| {
            r["outcome"] = json!("killed");
            r["slots"] = json!(["distinguish", "agree"]);
        });
        let (trusted, ok) = search(&manifest, &mutations, &["add-swaps-operands"]);
        assert!(ok, "{trusted:#}");
        assert_eq!(
            statuses(&trusted),
            vec![(
                "add-swaps-operands".to_owned(),
                "killed".to_owned(),
                Some("add".to_owned())
            )]
        );
        assert_eq!(
            mutation(&trusted, "add-swaps-operands")["killer_source"],
            "outcome-cache"
        );
        let (verified, ok) = search_mode(&manifest, &mutations, &[], RunMode::Verify);
        assert!(!ok);
        let row = mutation(&verified, "add-swaps-operands");
        assert_eq!(row["status"], "error");
        assert_eq!(row["reason"], "outcome-mismatch:add");
        assert_eq!(
            verified["mismatches"][0],
            json!({
                "mutation": "add-swaps-operands",
                "program": "add",
                "cached": {
                    "outcome": "killed",
                    "mutant_run_sha256": read_json(&outcome_file(&manifest, &cold, "add-swaps-operands"))
                        ["records"][program_digest(&cold, "add")]["mutant_run_sha256"],
                    "cause": null,
                    "open_application": false,
                    "smt_unknowns": 0,
                    "decider_smt_unknowns": 0,
                },
                "live": {
                    "outcome": "agree",
                    "mutant_run_sha256": verified["mismatches"][0]["live"]["mutant_run_sha256"],
                    "cause": null,
                    "open_application": false,
                    "smt_unknowns": 0,
                    "decider_smt_unknowns": 0,
                },
            })
        );
        // The cached path's status (killed) differs from the live one (survived) too.
        assert!(
            verified["mismatches"]
                .as_array()
                .unwrap()
                .iter()
                .any(|m| m["program"].is_null()
                    && m["cached"]["status"] == "killed"
                    && m["live"]["status"] == "survived")
        );
        // The other mutations are verified and keep their statuses; neither `--only` nor
        // `--verify` writes the lock.
        for (id, status, _) in statuses(&cold) {
            if id != "add-swaps-operands" {
                assert_eq!(mutation(&verified, &id)["status"], status.as_str(), "{id}");
            }
        }
        assert_eq!(verified["lock"]["status"], "not-written");
        assert_eq!(verified["lock"]["reason"], "verify");
        assert_eq!(fs::read_to_string(lock_of(&manifest)).unwrap(), lock_before);
    }

    #[test]
    #[ignore = "kink"]
    fn partially_cached_statuses_are_cold_statuses_on_calc() {
        // add-swaps-operands mixes cached agreements with a live call over add.
        assert!(partial("calc", "FLOW.toml", "MUTATIONS.toml") > 0);
    }

    #[test]
    #[ignore = "kink"]
    fn identity_equality_is_patch_digest_equality_on_every_fixture() {
        // Stop rule 2 (README 7.5.4): within one specification, two mutations have equal
        // identities exactly when they have equal patch digests.
        let examples = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/imp");
        let lists = [
            (
                flow("calc").join("FLOW.toml"),
                flow("calc").join("MUTATIONS.toml"),
            ),
            (
                flow("calc").join("FLOW.toml"),
                flow("calc").join("MUTATIONS-statuses.toml"),
            ),
            (
                flow("register").join("FLOW.toml"),
                flow("register").join("MUTATIONS.toml"),
            ),
            (
                flow("loop").join("FLOW.toml"),
                flow("loop").join("MUTATIONS.toml"),
            ),
            (
                flow("markdown").join("FLOW.toml"),
                flow("markdown").join("MUTATIONS.toml"),
            ),
            (
                flow("twin").join("FLOW.toml"),
                flow("twin").join("MUTATIONS.toml"),
            ),
            (examples.join("FLOW.toml"), examples.join("MUTATIONS.toml")),
        ];
        let mut checked = 0;
        for (manifest, mutations) in &lists {
            // Every list of one specification together: calc's two lists share calc.k.
            let all = identities(manifest, mutations);
            for (id, digest, identity) in &all {
                assert!(
                    identity.is_some(),
                    "{id}: every fixture mutation has an identity"
                );
                for (other, other_digest, other_identity) in &all {
                    assert_eq!(
                        identity == other_identity,
                        digest == other_digest,
                        "{}: {id} and {other}",
                        mutations.display()
                    );
                }
                checked += 1;
            }
        }
        // Across calc's two lists (one specification): add-becomes-sub is in both.
        let mut calc = identities(&lists[0].0, &lists[0].1);
        calc.extend(identities(&lists[1].0, &lists[1].1));
        for (id, digest, identity) in &calc {
            for (other, other_digest, other_identity) in &calc {
                assert_eq!(
                    identity == other_identity,
                    digest == other_digest,
                    "{id}, {other}"
                );
            }
        }
        assert!(checked >= 21 + 5 + 4 + 4);
    }

    #[test]
    #[ignore = "kink"]
    fn a_stored_timeout_record_is_never_honoured() {
        // (i): add's record says timeout (as a build that cached timeouts, or a hand edit, could
        // have left it). A timeout depends on the host's load, so no record of it is read: add's
        // baseline runs again, comparable, the record is replaced, and the recorded killer kills
        // again.
        let (dir, cold) = calc_after_cold("rerun");
        let manifest = dir.join("FLOW.toml");
        let mutations = dir.join("MUTATIONS.toml");
        let only = ["add-becomes-sub"];
        let record = result_record_path(&manifest, &cold, "add");
        let original = read_json(&record);
        let mut timeout = original.clone();
        timeout["class"] = json!("timeout");
        timeout["cause"] = json!("the run did not finish within time_ms = 10000");
        timeout["baseline"] = Value::Null;
        timeout["run_sha256"] = Value::Null;
        write_json(&record, &timeout);
        forget_outcomes(&manifest);
        let (rerun, ok) = search(&manifest, &mutations, &only);
        assert!(ok, "{rerun:#}");
        let add = rerun["programs"]
            .as_array()
            .unwrap()
            .iter()
            .find(|p| p["id"] == "add")
            .unwrap();
        assert!(add.get("rerun").is_none(), "{add:#}");
        assert_eq!(add["class"], "comparable");
        assert_eq!(add["cached"], false);
        // The replaced record is the original up to the re-run's measured wall time (F-16 review
        // 1 minor 3: a whole-record comparison failed when the two runs' times differed).
        let replaced = read_json(&record);
        assert!(replaced["wall_ms"].is_u64() && original["wall_ms"].is_u64());
        assert_eq!(without_wall_ms(&replaced), without_wall_ms(&original));
        assert_eq!(statuses(&rerun), statuses_of(&cold, &only));
        assert_eq!(
            mutation(&rerun, "add-becomes-sub")["killer_source"],
            "record"
        );
        assert_eq!(calls(&rerun, "add-becomes-sub"), vec![strings(&["add"])]);

        // A stored unknown is honoured, so the program is not run again: its killed record and the
        // lock's record of it are reported as unusable, never silently dropped, and the search
        // goes on.
        let mut unknown = original.clone();
        unknown["class"] = json!("unknown");
        unknown["cause"] = json!("hand-edited");
        unknown["baseline"] = Value::Null;
        unknown["run_sha256"] = Value::Null;
        write_json(&record, &unknown);
        let (unusable, ok) = search(&manifest, &mutations, &only);
        assert!(ok, "{unusable:#}");
        let row = mutation(&unusable, "add-becomes-sub");
        assert_eq!(
            row["unusable_killer"],
            json!({"program": "add", "class": "unknown", "cause": "hand-edited",
                   "source": "outcome-cache"})
        );
        assert_eq!(row["status"], "killed");
        assert_eq!(row["killer"], "nested");
        forget_outcomes(&manifest);
        write_json(&record, &unknown);
        set_record(&manifest, "add-becomes-sub", "add");
        let (recorded, ok) = search(&manifest, &mutations, &only);
        assert!(ok, "{recorded:#}");
        let row = mutation(&recorded, "add-becomes-sub");
        assert_eq!(row["unusable_killer"]["source"], "record");
        assert_eq!(row["killer_change"], "not-comparable");
    }
}
