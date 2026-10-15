//! The outcome cache (flow F-14, README 7.5): tier 1, the proved outcome of a mutation on a
//! program under an exact key, and tier 2, the killer hint that survives specification edits.
//!
//! Every status here is checked against a cold run (a fresh cache) of the same files: a
//! cached outcome or a hint may change the calls and the killer found first, never a status.
//! The tests read the run document, `outcomes/` and `hints.json`, and edit them by hand only
//! to forge what a corrupted or hostile cache would hold.

use k_rust::definition::AttributeKey;
use kink_corpus::load_source;
use kink_flow::{
    FlowManifest, MutationList,
    admit::corpus_source,
    cli::{EXIT_OK, EXIT_USAGE, results},
    digest::{hint_key, mutation_identity, spec_digest},
    hints::{HINTS_SCHEMA, hints_path},
    mutation::InvalidReason,
    outcomes::{OUTCOMES_DIRECTORY, record_sha256},
    resolve,
    results::{CACHE_DIRECTORY, ResultsOptions},
    search::{RunMode, RunOptions, drift_reason, run_with},
};
use kink_patch::{Edit, Patch};
use serde_json::{Value, json};
use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
    process::Command,
    sync::{Arc, Mutex, OnceLock},
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

/// Copy every file of `from` into `to`, the cache directory included.
fn copy_all(from: &Path, to: &Path) {
    fs::create_dir_all(to).unwrap();
    for entry in fs::read_dir(from).unwrap() {
        let entry = entry.unwrap();
        if entry.file_type().unwrap().is_dir() {
            copy_all(&entry.path(), &to.join(entry.file_name()));
        } else {
            fs::copy(entry.path(), to.join(entry.file_name())).unwrap();
        }
    }
}

/// A private copy of the testdata/flow fixture `name` whose cache holds a cold run of
/// `mutations` under `manifest`, and that run's document. Each cold run is made once per test
/// process (its admission dominates a debug test's time) and copied for each test.
fn after_cold(name: &str, manifest: &str, mutations: &str, test: &str) -> (PathBuf, Value) {
    type Cell = Arc<OnceLock<(PathBuf, Value)>>;
    static COLD: Mutex<BTreeMap<String, Cell>> = Mutex::new(BTreeMap::new());
    let key = format!("{name}-{manifest}-{mutations}");
    let cell = COLD.lock().unwrap().entry(key.clone()).or_default().clone();
    let (source, cold) = cell.get_or_init(|| {
        let dir = fixture(name, &format!("cold-{key}"));
        let (cold, ok) = search(&dir.join(manifest), &dir.join(mutations), &[]);
        assert!(ok, "{cold:#}");
        (dir, cold)
    });
    let dir = scratch(test).join(name);
    copy_all(source, &dir);
    (dir, cold.clone())
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

fn append(path: &Path, text: &str) {
    let mut contents = fs::read_to_string(path).unwrap();
    contents.push_str(text);
    fs::write(path, contents).unwrap();
}

/// `kink-flow run` (or `run --verify`) through the library, as the binary runs it.
fn search_mode(manifest: &Path, mutations: &Path, only: &[&str], mode: RunMode) -> (Value, bool) {
    let manifest = FlowManifest::read(manifest).unwrap();
    let list = MutationList::read(mutations).unwrap();
    run_with(
        &manifest,
        &list,
        &RunOptions {
            only: only.iter().map(|id| (*id).to_owned()).collect(),
            cache: None,
        },
        mode,
    )
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
        );
        record["record_sha256"] = json!(sealed.to_string());
    }
    write_json(&path, &file);
}

/// The hint key of every mutation of `mutations` that resolves under `manifest`.
fn hint_keys(manifest: &Path, mutations: &Path) -> BTreeMap<String, String> {
    let flow = FlowManifest::read(manifest).unwrap();
    let list = MutationList::read(mutations).unwrap();
    let loaded = load_source(&corpus_source(&flow)).unwrap();
    list.mutations
        .iter()
        .filter_map(|mutation| {
            let resolved = resolve(&flow, &loaded, mutation).ok()?;
            Some((
                mutation.id.clone(),
                hint_key(mutation, &resolved).to_string(),
            ))
        })
        .collect()
}

/// The hint key of mutation `id` of `mutations` under `manifest`.
fn hint_key_of(manifest: &Path, mutations: &Path, id: &str) -> String {
    hint_keys(manifest, mutations).remove(id).unwrap()
}

/// The hints file: hint key -> (mutation id, program id).
fn hints(manifest: &Path) -> BTreeMap<String, (String, String)> {
    let value = read_json(&hints_path(&cache_of(manifest)));
    assert_eq!(value["schema"], HINTS_SCHEMA);
    value["hints"]
        .as_object()
        .unwrap()
        .iter()
        .map(|(key, entry)| {
            (
                key.clone(),
                (
                    entry["mutation_id"].as_str().unwrap().to_owned(),
                    entry["program_id"].as_str().unwrap().to_owned(),
                ),
            )
        })
        .collect()
}

fn set_hint(manifest: &Path, key: &str, mutation: &str, program: &str, digest: &str) {
    let path = hints_path(&cache_of(manifest));
    let mut value = fs::read_to_string(&path)
        .ok()
        .map(|text| serde_json::from_str::<Value>(&text).unwrap())
        .unwrap_or_else(|| json!({"schema": HINTS_SCHEMA, "version": 1, "hints": {}}));
    value["hints"][key] = json!({
        "mutation_id": mutation,
        "program_id": program,
        "program_digest": digest,
    });
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    write_json(&path, &value);
}

fn result_record_path(manifest: &Path, document: &Value, program: &str) -> PathBuf {
    cache_of(manifest)
        .join("results")
        .join(document["spec"]["digest"].as_str().unwrap())
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
                let entries = executed(&warm, id);
                assert_eq!(entries.len(), 1, "{id}");
                assert_eq!(
                    (entries[0].1.as_str(), entries[0].2),
                    ("distinguish", true),
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
            // Never cached: a timeout, an unknown, a mutant-scope status; an invalid
            // mutation is never run.
            "invalid-mutation" => assert_eq!(row["calls"], json!([]), "{id}"),
            _ => assert_ne!(row["calls"], json!([]), "{id}"),
        }
    }
    assert_eq!(warm["outcome_cache"]["mutations_from_cache"], from_cache);
}

#[test]
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
fn a_change_of_an_input_misses_tier_1() {
    // (c): a budget change is another context; a program text change misses for that
    // program only.
    let (dir, cold) = calc_after_cold("inputs");
    let manifest = dir.join("FLOW.toml");
    let mutations = dir.join("MUTATIONS.toml");
    let only = ["add-becomes-sub", "add-swaps-operands"];
    edit(
        &manifest,
        "syntax_module = \"CALC-SYNTAX\"\n",
        "syntax_module = \"CALC-SYNTAX\"\n\n[budget]\ntime_ms = 20000\n",
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
        "hint"
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
fn hand_edited_contexts_and_records_are_ignored() {
    // (c): a hand-changed context field (kink_build, k_rust_revision, result_schema), a
    // hand-changed baseline run digest (record digest recomputed), a record whose digest does
    // not recompute and a record whose outcome contradicts its slots each miss. One forgery
    // per mutation file, so one run checks them all.
    let (dir, cold) = calc_after_cold("forged");
    let manifest = dir.join("FLOW.toml");
    let mutations = dir.join("MUTATIONS.toml");
    for (id, field, value) in [
        ("add-becomes-sub", "kink_build", json!("0".repeat(64))),
        ("sub-off-by-one", "k_rust_revision", json!("0".repeat(40))),
        (
            "mul-becomes-add",
            "result_schema",
            json!("kink-flow/result/v1"),
        ),
    ] {
        let path = outcome_file(&manifest, &cold, id);
        let mut file = read_json(&path);
        file["context"][field] = value;
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
            assert_eq!(mutation(&document, &id)["killer_source"], "hint", "{id}");
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
fn unknowns_are_never_cached() {
    // (d): countdown never ends on the mutant. Under a small depth bound its outcome is
    // unknown: it is not written, and countdown runs again in the next command; twice's
    // agreement is cached. (The timeout case: warm_and_forged_hints_on_loop.)
    let dir = fixture("loop", "never-unknown");
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
        BTreeMap::from([("twice".to_owned(), "agree".to_owned())])
    );
    let (second, ok) = search(&manifest, &mutations, &[]);
    assert!(ok, "{second:#}");
    assert_eq!(statuses(&second), statuses(&first));
    assert_eq!(
        calls(&second, "countdown-escapes"),
        vec![strings(&["countdown"])]
    );
    assert_eq!(
        executed(&second, "countdown-escapes"),
        vec![
            ("twice".into(), "agree".into(), true),
            ("countdown".into(), "unknown".into(), false),
        ]
    );
    assert_eq!(
        records(&manifest, &second, "countdown-escapes"),
        BTreeMap::from([("twice".to_owned(), "agree".to_owned())])
    );
}

#[test]
fn a_corpus_error_writes_no_record_and_keeps_the_hints_written() {
    // (d) and (i): a hand-edited result run digest is a corpus error; no record is written
    // for the mutation, and the hints file is written with the ignored hint removed.
    let dir = fixture("calc", "corpus-error");
    let manifest = dir.join("FLOW.toml");
    let mutations = dir.join("MUTATIONS.toml");
    let (filled, status) = results(&manifest, &ResultsOptions::default());
    assert_eq!(status, EXIT_OK);
    let record = result_record_path(&manifest, &filled, "add");
    let mut value = read_json(&record);
    value["run_sha256"] = json!("0".repeat(64));
    write_json(&record, &value);
    let key = hint_key_of(&manifest, &mutations, "add-becomes-sub");
    set_hint(&manifest, &key, "add-becomes-sub", "gone", &"f".repeat(64));
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
    assert!(mutation(&document, "add-becomes-sub")["stale_killer"].is_string());
    assert!(!outcome_file(&manifest, &document, "add-becomes-sub").exists());
    assert_eq!(document["outcome_cache"]["records_written"], 0);
    assert!(hints(&manifest).is_empty());
}

#[test]
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
/// with every hint forged and tier 1 deleted.
fn warm_and_forged(name: &str, manifest: &str, mutations: &str) {
    let (dir, cold) = after_cold(
        name,
        manifest,
        mutations,
        &format!("tiers-{name}-{mutations}"),
    );
    let (manifest, mutations) = (dir.join(manifest), dir.join(mutations));
    warm_after_no_change(&manifest, &mutations, &cold, name);
    forged_hints_change_no_status(&manifest, &mutations, &cold, name);
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

#[test]
fn warm_and_forged_hints_on_calc() {
    warm_and_forged("calc", "FLOW.toml", "MUTATIONS.toml");
}

#[test]
fn warm_and_forged_hints_on_calc_statuses() {
    warm_and_forged("calc", "FLOW.toml", "MUTATIONS-statuses.toml");
}

#[test]
fn warm_and_forged_hints_on_register() {
    warm_and_forged("register", "FLOW.toml", "MUTATIONS.toml");
}

#[test]
fn warm_and_forged_hints_on_loop() {
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
fn warm_and_forged_hints_on_markdown() {
    warm_and_forged("markdown", "FLOW.toml", "MUTATIONS.toml");
}

#[test]
fn partially_cached_statuses_are_cold_statuses_on_calc() {
    // add-swaps-operands mixes cached agreements with a live call over add.
    assert!(partial("calc", "FLOW.toml", "MUTATIONS.toml") > 0);
}

#[test]
fn partially_cached_statuses_are_cold_statuses_on_calc_statuses() {
    // add-commutes mixes cached agreements with a live call over add.
    assert!(partial("calc", "FLOW.toml", "MUTATIONS-statuses.toml") > 0);
}

#[test]
fn partially_cached_statuses_are_cold_statuses_on_register() {
    // Every register mutation is killed by a program of the subset: a cached kill decides.
    partial("register", "FLOW.toml", "MUTATIONS.toml");
}

#[test]
fn partially_cached_statuses_are_cold_statuses_on_loop() {
    // The timeout mixes twice's cached agreement with a live call over countdown.
    assert!(partial("loop", "FLOW-search.toml", "MUTATIONS.toml") > 0);
}

#[test]
fn partially_cached_statuses_are_cold_statuses_on_markdown() {
    partial("markdown", "FLOW.toml", "MUTATIONS.toml");
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

#[test]
fn a_comment_only_edit_reproves_each_kill_with_its_hint() {
    // (g): any edit of the specification misses tier 1 (the execution digest is the exact
    // specification digest until KINK-14); each killed mutation is one call over its hint.
    let (dir, cold) = calc_after_cold("comment");
    let manifest = dir.join("FLOW.toml");
    let mutations = dir.join("MUTATIONS.toml");
    append(&dir.join("calc.k"), "// a comment at the end\n");
    let (edited, ok) = search(&manifest, &mutations, &[]);
    assert!(ok, "{edited:#}");
    assert_eq!(statuses(&edited), statuses(&cold));
    assert_ne!(edited["spec"]["digest"], cold["spec"]["digest"]);
    assert_eq!(edited["outcome_cache"]["mutations_from_cache"], 0);
    for (id, status, killer) in statuses(&edited) {
        if status == "killed" {
            let killer = killer.unwrap();
            assert_eq!(mutation(&edited, &id)["killer_source"], "hint", "{id}");
            assert_eq!(calls(&edited, &id), vec![vec![killer]], "{id}");
        }
    }
}

#[test]
fn a_hint_that_stops_killing_changes_no_status() {
    // (g): after an edit of the add rule, (1 + 2) is stuck, so nested, the hint of
    // mul-becomes-add, agrees on it; the hint's call agrees and the cold call decides.
    let (dir, first) = calc_after_cold("hint-stops");
    let manifest = dir.join("FLOW.toml");
    let mutations = dir.join("MUTATIONS.toml");
    assert_eq!(mutation(&first, "mul-becomes-add")["killer"], "nested");
    edit(
        &dir.join("calc.k"),
        "rule [add]: I1:Int + I2:Int => I1 +Int I2",
        "rule [add]: I1:Int + I2:Int => I1 +Int I2 requires I1 >Int 5",
    );
    let cold_dir = scratch("hint-stops-cold").join("calc");
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
        "the hint is tried first"
    );
    assert_eq!(
        mutation(&edited, "mul-becomes-add")["killer_source"],
        "search"
    );
    assert_eq!(statuses(&edited), statuses(&cold));
}

#[test]
fn a_hint_naming_a_removed_program_is_ignored_and_removed() {
    // (g): no-mul's hint names nested; nested leaves the corpus. The hint names no comparable
    // program: it is reported, removed, and the status is a cold run's.
    let (dir, _) = calc_after_cold("hint-removed");
    let manifest = dir.join("FLOW.toml");
    let mutations = dir.join("MUTATIONS.toml");
    let key = hint_key_of(&manifest, &mutations, "no-mul");
    assert_eq!(hints(&manifest)[&key].1, "nested");
    edit(
        &manifest,
        "[[program]]\nid = \"nested\"\nfile = \"programs/nested.calc\"\n",
        "",
    );
    let (removed, ok) = search(&manifest, &mutations, &["no-mul"]);
    assert!(ok, "{removed:#}");
    assert!(mutation(&removed, "no-mul")["stale_killer"].is_string());
    assert_eq!(mutation(&removed, "no-mul")["unusable_killer"], Value::Null);
    let cold_dir = scratch("hint-removed-cold").join("calc");
    copy_dir(&dir, &cold_dir);
    let (cold, ok) = search(
        &cold_dir.join("FLOW.toml"),
        &cold_dir.join("MUTATIONS.toml"),
        &["no-mul"],
    );
    assert!(ok, "{cold:#}");
    assert_eq!(statuses(&removed), statuses(&cold));
    assert_eq!(hints(&manifest)[&key].1, "inline");
}

/// (g): a hint never changes a status. Every mutation's hint is forged to a program the cold
/// run did not find killing it, tier 1 is deleted, and the statuses are the cold run's.
fn forged_hints_change_no_status(manifest: &Path, mutations: &Path, cold: &Value, name: &str) {
    let programs = cold["programs"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|p| p["class"] == "comparable")
        .map(|p| p["id"].as_str().unwrap().to_owned())
        .collect::<Vec<_>>();
    let keys = hint_keys(manifest, mutations);
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
        set_hint(
            manifest,
            &keys[id],
            id,
            &program,
            &program_digest(cold, &program),
        );
        forged += 1;
    }
    assert!(forged > 0);
    forget_outcomes(manifest);
    let (hinted, _) = search(manifest, mutations, &[]);
    assert_eq!(status_only(&hinted), status_only(cold), "{name}");
}

#[test]
fn run_verify_reproves_every_record_and_reports_a_forged_one() {
    // (h): a warm cache gives no mismatch. A record forged to killed with a recomputed
    // record_sha256 makes the plain warm run report Killed: this is the trust premise of
    // README 7.5.1 (whoever can write the cache directory can forge a kill, as whoever can
    // write the build can). `run --verify` re-proves it and reports the forgery.
    let (dir, cold) = calc_after_cold("verify");
    let manifest = dir.join("FLOW.toml");
    let mutations = dir.join("MUTATIONS.toml");
    let hints_before = fs::read_to_string(hints_path(&cache_of(&manifest))).unwrap();
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
    let hints_forged = fs::read_to_string(hints_path(&cache_of(&manifest))).unwrap();
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
            },
            "live": {
                "outcome": "agree",
                "mutant_run_sha256": verified["mismatches"][0]["live"]["mutant_run_sha256"],
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
    // The other mutations are verified and keep their statuses; --verify writes no hint.
    for (id, status, _) in statuses(&cold) {
        if id != "add-swaps-operands" {
            assert_eq!(mutation(&verified, &id)["status"], status.as_str(), "{id}");
        }
    }
    assert_eq!(
        fs::read_to_string(hints_path(&cache_of(&manifest))).unwrap(),
        hints_forged
    );
    assert_ne!(hints_before, hints_forged);
}

#[test]
fn the_binary_parses_run_verify() {
    // `run --verify` through the binary: the flag is accepted once; a repeated flag is a
    // usage error.
    let dir = fixture("calc", "verify-binary");
    let binary = env!("CARGO_BIN_EXE_kink-flow");
    for (args, code) in [
        (
            vec!["run", "FLOW.toml", "MUTATIONS.toml", "--verify", "--verify"],
            EXIT_USAGE,
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
            EXIT_OK,
        ),
    ] {
        let output = Command::new(binary)
            .args(&args)
            .current_dir(&dir)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(i32::from(code)), "{args:?}");
        if code == EXIT_OK {
            let document: Value = serde_json::from_slice(&output.stdout).unwrap();
            assert_eq!(document["outcome_cache"]["verify"], true);
            assert_eq!(document["mismatches"], json!([]));
            assert_eq!(mutation(&document, "add-becomes-sub")["status"], "killed");
        }
    }
}

#[test]
fn a_program_id_with_a_colon_and_the_count_mismatch_have_their_reasons() {
    // (i) F-05 review 1 minor 2: the reason carries the program id from the candidate.
    let dir = fixture("calc", "colon");
    let manifest = dir.join("FLOW.toml");
    let mutations = dir.join("MUTATIONS.toml");
    edit(&manifest, "id = \"add\"", "id = \"add:one\"");
    let (filled, status) = results(&manifest, &ResultsOptions::default());
    assert_eq!(status, EXIT_OK);
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

#[test]
fn a_timeout_record_named_by_a_hint_is_rerun_once() {
    // (i) F-05 review 1 minor 1: add's record says timeout (as a run under host load could
    // have left it). A hint names add, so `run` re-runs add's baseline once: it is
    // comparable, the record is replaced, and the hint's program kills again.
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
    assert_eq!(add["rerun"], "timeout");
    assert_eq!(add["class"], "comparable");
    assert_eq!(add["cached"], false);
    assert_eq!(read_json(&record), original);
    assert_eq!(statuses(&rerun), statuses_of(&cold, &only));
    assert_eq!(mutation(&rerun, "add-becomes-sub")["killer_source"], "hint");
    assert_eq!(calls(&rerun, "add-becomes-sub"), vec![strings(&["add"])]);

    // A program with another non-comparable class is not re-run: its killed record and its
    // hint are reported as unusable, never silently dropped, and the search goes on.
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
    let key = hint_key_of(&manifest, &mutations, "add-becomes-sub");
    set_hint(
        &manifest,
        &key,
        "add-becomes-sub",
        "add",
        &program_digest(&cold, "add"),
    );
    let (hinted, ok) = search(&manifest, &mutations, &only);
    assert!(ok, "{hinted:#}");
    assert_eq!(
        mutation(&hinted, "add-becomes-sub")["unusable_killer"]["source"],
        "hint"
    );
}

#[test]
fn a_doubly_qualified_label_is_unknown() {
    // (i) F-10 review 1 m1: `LIT.LIT.inc` does not address the rule stored as `LIT.inc`.
    let manifest = flow("markdown").join("FLOW.toml");
    let flow = FlowManifest::read(&manifest).unwrap();
    let loaded = load_source(&corpus_source(&flow)).unwrap();
    let resolve_label = |label: &str| {
        let list = MutationList::decode(&format!(
            "[[mutation]]\nid = \"m\"\n[[mutation.edit]]\nrule = \"{label}\"\nfind = \"+Int 1\"\nreplace = \"+Int 3\"\n"
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
            "[[mutation]]\nid = \"m\"\n[[mutation.edit]]\nrule = \"{label}\"\ndelete = true\n"
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
