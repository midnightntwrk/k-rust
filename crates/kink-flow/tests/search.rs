//! The kill search with its killer cache and `kink-flow run` (flow F-05 deliverables 1-5).
//!
//! Every test pins statuses and killer ids. Each verdict is the status kink-campaign's
//! runner derives; the tests only read the run document, the killer hints file and the
//! result records. Since F-14 the killer cache is tier 2 of the outcome cache (`hints.json`,
//! keyed by the hint key); a test that pins the warm cost of a killer deletes tier 1
//! (`outcomes/`) first, so that the hint, not a cached outcome, decides the calls.

use kink_corpus::load_source;
use kink_flow::{
    FlowManifest, MutationList,
    admit::corpus_source,
    cli::{EXIT_CORPUS, EXIT_OK, EXIT_USAGE, results},
    digest::hint_key,
    hints::{HINTS_SCHEMA, hints_path},
    outcomes::OUTCOMES_DIRECTORY,
    resolve,
    results::{CACHE_DIRECTORY, ResultsOptions},
    search::{REPORT_FILE, RunOptions, run},
};
use kink_patch::Sha256Digest;
use serde_json::{Value, json};
use std::{
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
        .join(format!("kink-flow-search-{}", std::process::id()))
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

fn append(path: &Path, text: &str) {
    let mut contents = fs::read_to_string(path).unwrap();
    contents.push_str(text);
    fs::write(path, contents).unwrap();
}

/// `kink-flow run` through the library, as the binary runs it.
fn search(manifest: &Path, mutations: &Path, only: &[&str]) -> (Value, bool) {
    let manifest = FlowManifest::read(manifest).unwrap();
    let list = MutationList::read(mutations).unwrap();
    run(
        &manifest,
        &list,
        &RunOptions {
            only: only.iter().map(|id| (*id).to_owned()).collect(),
            cache: None,
        },
    )
}

/// `(id, status, killer, killer_from_cache)` of every mutation row.
fn verdicts(document: &Value) -> Vec<(String, String, Option<String>, bool)> {
    document["mutations"]
        .as_array()
        .unwrap()
        .iter()
        .map(|m| {
            (
                m["id"].as_str().unwrap().to_owned(),
                m["status"].as_str().unwrap().to_owned(),
                m["killer"].as_str().map(str::to_owned),
                m["killer_from_cache"].as_bool().unwrap(),
            )
        })
        .collect()
}

fn expect(
    rows: &[(&str, &str, Option<&str>, bool)],
) -> Vec<(String, String, Option<String>, bool)> {
    rows.iter()
        .map(|(id, status, killer, cached)| {
            (
                (*id).to_owned(),
                (*status).to_owned(),
                killer.map(str::to_owned),
                *cached,
            )
        })
        .collect()
}

fn mutation<'d>(document: &'d Value, id: &str) -> &'d Value {
    document["mutations"]
        .as_array()
        .unwrap()
        .iter()
        .find(|m| m["id"] == id)
        .unwrap_or_else(|| panic!("no mutation {id}"))
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

/// `(program, outcome)` of every program the mutant ran on, in the runner's order.
fn executed(document: &Value, id: &str) -> Vec<(String, String)> {
    mutation(document, id)["executed"]
        .as_array()
        .unwrap()
        .iter()
        .map(|e| {
            (
                e["program"].as_str().unwrap().to_owned(),
                e["outcome"].as_str().unwrap().to_owned(),
            )
        })
        .collect()
}

fn strings(items: &[&str]) -> Vec<String> {
    items.iter().map(|s| (*s).to_owned()).collect()
}

fn pairs(items: &[(&str, &str)]) -> Vec<(String, String)> {
    items
        .iter()
        .map(|(a, b)| ((*a).to_owned(), (*b).to_owned()))
        .collect()
}

fn spec_digest(document: &Value) -> Sha256Digest {
    Sha256Digest::parse(document["spec"]["digest"].as_str().unwrap()).unwrap()
}

fn program_digest(document: &Value, id: &str) -> String {
    document["programs"]
        .as_array()
        .unwrap()
        .iter()
        .find(|p| p["id"] == id)
        .unwrap()["digest"]
        .as_str()
        .unwrap()
        .to_owned()
}

fn cache_of(manifest: &Path) -> PathBuf {
    manifest.parent().unwrap().join(CACHE_DIRECTORY)
}

fn killers_file(manifest: &Path) -> PathBuf {
    hints_path(&cache_of(manifest))
}

/// Delete tier 1 of the outcome cache, so that the next run's calls come from the hints.
fn forget_outcomes(manifest: &Path) {
    let _ = fs::remove_dir_all(cache_of(manifest).join(OUTCOMES_DIRECTORY));
}

/// The hint key of mutation `id` of the manifest's `MUTATIONS.toml`.
fn hint_key_of(manifest: &Path, id: &str) -> String {
    let flow = FlowManifest::read(manifest).unwrap();
    let list = MutationList::read(&manifest.with_file_name("MUTATIONS.toml")).unwrap();
    let mutation = list.mutations.iter().find(|m| m.id == id).unwrap();
    let loaded = load_source(&corpus_source(&flow)).unwrap();
    let resolved = resolve(&flow, &loaded, mutation).unwrap();
    hint_key(mutation, &resolved).to_string()
}

/// The killer hints: hint key -> (mutation id, program id, program digest).
fn killers(manifest: &Path, _document: &Value) -> Vec<(String, String, String, String)> {
    let path = killers_file(manifest);
    let Ok(text) = fs::read_to_string(&path) else {
        return Vec::new();
    };
    let value: Value = serde_json::from_str(&text).unwrap();
    assert_eq!(value["schema"], HINTS_SCHEMA);
    value["hints"]
        .as_object()
        .unwrap()
        .iter()
        .map(|(digest, entry)| {
            (
                digest.clone(),
                entry["mutation_id"].as_str().unwrap().to_owned(),
                entry["program_id"].as_str().unwrap().to_owned(),
                entry["program_digest"].as_str().unwrap().to_owned(),
            )
        })
        .collect()
}

fn killer_of(manifest: &Path, document: &Value, id: &str) -> Option<(String, String)> {
    let key = hint_key_of(manifest, id);
    killers(manifest, document)
        .into_iter()
        .find(|(k, ..)| *k == key)
        .map(|(_, _, program, program_digest)| (program, program_digest))
}

/// Replace the killer hint of mutation `id` by hand.
fn set_killer(manifest: &Path, _document: &Value, id: &str, program: &str, program_digest: &str) {
    let path = killers_file(manifest);
    let mut value: Value = fs::read_to_string(&path)
        .ok()
        .map(|text| serde_json::from_str(&text).unwrap())
        .unwrap_or_else(|| json!({"schema": HINTS_SCHEMA, "version": 1, "hints": {}}));
    value["hints"][hint_key_of(manifest, id)] = json!({
        "mutation_id": id,
        "program_id": program,
        "program_digest": program_digest,
    });
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, serde_json::to_string_pretty(&value).unwrap()).unwrap();
}

fn record_path(manifest: &Path, document: &Value, program: &str) -> PathBuf {
    cache_of(manifest)
        .join("results")
        .join(spec_digest(document).to_string())
        .join(format!("{}.json", program_digest(document, program)))
}

/// Hand-edit program `program`'s cached run digest, as a stale record would have it.
fn corrupt_run_digest(manifest: &Path, document: &Value, program: &str) {
    let path = record_path(manifest, document, program);
    let mut record: Value = serde_json::from_str(&fs::read_to_string(&path).unwrap()).unwrap();
    assert_eq!(record["class"], "comparable");
    record["run_sha256"] = json!("0".repeat(64));
    fs::write(&path, serde_json::to_string(&record).unwrap()).unwrap();
}

const CALC_VERDICTS: [(&str, &str, Option<&str>); 5] = [
    // 1 + 2 is 3 on the baseline and -1 on the mutant: the first program reaching add.
    ("add-becomes-sub", "killed", Some("add")),
    // 10 - 4 - 3 is 3 on the baseline and 1 on the mutant: the only program reaching sub.
    ("sub-off-by-one", "killed", Some("sub")),
    // (1 + 2) * 3 is 9 on the baseline and 6 on the mutant.
    ("mul-becomes-add", "killed", Some("nested")),
    // Without the mul rule, (1 + 2) * 3 is stuck at 3 * 3.
    ("no-mul", "killed", Some("nested")),
    // I2 +Int I1 equals I1 +Int I2 on every input: no program can tell.
    ("add-swaps-operands", "survived", None),
];

#[test]
fn a_killed_mutation_caches_its_killer_and_a_second_run_runs_only_that_program() {
    let manifest = fixture("calc", "warm").join("FLOW.toml");
    let mutations = manifest.with_file_name("MUTATIONS.toml");
    let (first, ok) = search(&manifest, &mutations, &[]);
    assert!(ok, "{first:#}");
    assert_eq!(
        verdicts(&first),
        CALC_VERDICTS
            .iter()
            .map(|(id, status, killer)| (
                (*id).to_owned(),
                (*status).to_owned(),
                killer.map(str::to_owned),
                false
            ))
            .collect::<Vec<_>>()
    );
    // Cold cache: one call over every comparable program, those reaching the edited rule
    // first; under FirstKill the mutant stops at its first kill.
    assert_eq!(
        calls(&first, "add-becomes-sub"),
        vec![strings(&["add", "nested", "inline", "sub"])]
    );
    assert_eq!(
        executed(&first, "add-becomes-sub"),
        pairs(&[("add", "distinguish")])
    );
    assert_eq!(
        mutation(&first, "add-becomes-sub")["reaching"],
        json!(["add", "nested", "inline"])
    );
    // The killer cache holds exactly the killed mutations, each with its first killing test
    // and that program's digest; the survivor has no entry.
    let mut entries = killers(&manifest, &first)
        .into_iter()
        .map(|(key, mutation, program, program_digest)| {
            assert_eq!(key, hint_key_of(&manifest, &mutation));
            assert_eq!(program_digest, self::program_digest(&first, &program));
            (mutation, program)
        })
        .collect::<Vec<_>>();
    entries.sort();
    assert_eq!(
        entries,
        vec![
            ("add-becomes-sub".to_owned(), "add".to_owned()),
            ("mul-becomes-add".to_owned(), "nested".to_owned()),
            ("no-mul".to_owned(), "nested".to_owned()),
            ("sub-off-by-one".to_owned(), "sub".to_owned()),
        ]
    );
    assert_eq!(killer_of(&manifest, &first, "add-swaps-operands"), None);
    // The report file is the document.
    let report: Value =
        serde_json::from_str(&fs::read_to_string(cache_of(&manifest).join(REPORT_FILE)).unwrap())
            .unwrap();
    assert_eq!(report, first);
    assert_eq!(
        first["counts"],
        json!({"killed": 4, "survived": 1, "equivalent": 0, "invalid": 0, "timeout": 0,
               "unknown": 0, "error": 0, "invalid-mutation": 0})
    );

    // Warm cache: a killed mutation costs one campaign call over one program, whose baseline
    // and mutant run once each; the survivor is scanned again. (Tier 1 is deleted: with it,
    // a killed mutation and the survivor cost no call at all; tests/outcomes.rs.)
    forget_outcomes(&manifest);
    let (second, ok) = search(&manifest, &mutations, &[]);
    assert!(ok, "{second:#}");
    assert_eq!(
        verdicts(&second),
        CALC_VERDICTS
            .iter()
            .map(|(id, status, killer)| (
                (*id).to_owned(),
                (*status).to_owned(),
                killer.map(str::to_owned),
                killer.is_some()
            ))
            .collect::<Vec<_>>()
    );
    for (id, _, killer) in CALC_VERDICTS {
        if let Some(killer) = killer {
            assert_eq!(calls(&second, id), vec![strings(&[killer])], "{id}");
            assert_eq!(
                executed(&second, id),
                pairs(&[(killer, "distinguish")]),
                "{id}"
            );
        }
    }
    assert_eq!(
        calls(&second, "add-swaps-operands"),
        vec![strings(&["add", "nested", "inline", "sub"])]
    );
    assert_eq!(killers(&manifest, &second), killers(&manifest, &first));
}

#[test]
fn the_runner_runs_the_mutant_in_the_chosen_order() {
    // The scheduling premise of README 5.6: under FirstKill and no coverage selection the
    // runner runs the mutant on Campaign.tests in the order given. The survivor runs on every
    // program, so its executed list is the whole order: the programs reaching the add rule
    // (add, nested, inline) in corpus order, then sub; the corpus order is add, nested, sub,
    // inline.
    let manifest = fixture("calc", "order").join("FLOW.toml");
    let (document, ok) = search(
        &manifest,
        &manifest.with_file_name("MUTATIONS.toml"),
        &["add-swaps-operands"],
    );
    assert!(ok);
    assert_eq!(
        verdicts(&document),
        expect(&[("add-swaps-operands", "survived", None, false)])
    );
    assert_eq!(
        executed(&document, "add-swaps-operands"),
        pairs(&[
            ("add", "agree"),
            ("nested", "agree"),
            ("inline", "agree"),
            ("sub", "agree"),
        ])
    );
    assert_eq!(
        calls(&document, "add-swaps-operands"),
        vec![strings(&["add", "nested", "inline", "sub"])]
    );
    // A survivor creates no entry: the cache file holds none.
    assert!(killers(&manifest, &document).is_empty());
}

#[test]
fn the_register_mutations_have_the_statuses_their_programs_imply() {
    let manifest = fixture("register", "register").join("FLOW.toml");
    let (document, ok) = search(&manifest, &manifest.with_file_name("MUTATIONS.toml"), &[]);
    assert!(ok, "{document:#}");
    assert_eq!(
        verdicts(&document),
        expect(&[
            // put(5) leaves 6 in <reg> instead of 5. The correlated get edit returns 6 - 1 =
            // 5 for every read, so a program that only compares values it reads back could
            // not tell; but the whole-term oracle sees the final <reg> cell, so the first
            // program reaching put (store) kills it.
            ("put-and-get-offset", "killed", Some("store"), false),
            // put alone: put(5) leaves 6 in <reg>.
            ("put-offset", "killed", Some("store"), false),
            // get alone: store never reads; increment's put(get + 1) stores 5 instead of 6.
            ("get-offset", "killed", Some("increment"), false),
            // Without seq, put(5); put(get + 1) is stuck at the first ';'.
            ("no-seq", "killed", Some("increment"), false),
        ])
    );
    // get-offset reaches the get rule through increment and double only, so store runs last.
    assert_eq!(
        mutation(&document, "get-offset")["reaching"],
        json!(["increment", "double"])
    );
    assert_eq!(
        calls(&document, "get-offset"),
        vec![strings(&["increment", "double", "store"])]
    );
    assert_eq!(
        killer_of(&manifest, &document, "put-and-get-offset")
            .unwrap()
            .0,
        "store"
    );
}

#[test]
fn a_wrong_or_stale_killer_entry_changes_cost_but_never_the_verdict() {
    let manifest = fixture("calc", "stale").join("FLOW.toml");
    let mutations = manifest.with_file_name("MUTATIONS.toml");
    let only = ["add-becomes-sub", "add-swaps-operands"];
    let (first, _) = search(&manifest, &mutations, &only);
    assert_eq!(
        killer_of(&manifest, &first, "add-becomes-sub").unwrap().0,
        "add"
    );

    // An entry naming a comparable program that does not kill: one call over it alone, then
    // the entry is removed and the call a cold cache makes decides; the new killer replaces
    // the entry.
    let sub = program_digest(&first, "sub");
    set_killer(&manifest, &first, "add-becomes-sub", "sub", &sub);
    // An entry for the survivor naming a program that does not kill it.
    let add = program_digest(&first, "add");
    set_killer(&manifest, &first, "add-swaps-operands", "add", &add);
    forget_outcomes(&manifest);
    let (second, ok) = search(&manifest, &mutations, &only);
    assert!(ok, "{second:#}");
    assert_eq!(
        verdicts(&second),
        expect(&[
            ("add-becomes-sub", "killed", Some("add"), false),
            ("add-swaps-operands", "survived", None, false),
        ])
    );
    assert_eq!(
        calls(&second, "add-becomes-sub"),
        vec![
            strings(&["sub"]),
            strings(&["add", "nested", "inline", "sub"])
        ]
    );
    assert_eq!(
        executed(&second, "add-becomes-sub"),
        pairs(&[("sub", "agree"), ("add", "distinguish")])
    );
    assert_eq!(
        calls(&second, "add-swaps-operands"),
        vec![
            strings(&["add"]),
            strings(&["add", "nested", "inline", "sub"])
        ]
    );
    assert_eq!(
        killer_of(&manifest, &second, "add-becomes-sub"),
        Some(("add".to_owned(), add.clone()))
    );
    assert_eq!(killer_of(&manifest, &second, "add-swaps-operands"), None);

    // Entries naming a program that no longer exists, or a program whose digest changed, are
    // ignored and removed: the mutation is scanned as with a cold cache. Since F-14 a hint
    // names a program by its digest (a renamed program keeps its hint), so both entries name
    // a digest no program of the corpus has.
    let gone = "f".repeat(64);
    set_killer(&manifest, &first, "add-becomes-sub", "gone", &gone);
    forget_outcomes(&manifest);
    let (third, ok) = search(&manifest, &mutations, &["add-becomes-sub"]);
    assert!(ok);
    assert_eq!(
        verdicts(&third),
        expect(&[("add-becomes-sub", "killed", Some("add"), false)])
    );
    assert!(mutation(&third, "add-becomes-sub")["stale_killer"].is_string());
    assert_eq!(
        calls(&third, "add-becomes-sub"),
        vec![strings(&["add", "nested", "inline", "sub"])]
    );
    let changed = "1".repeat(64);
    set_killer(&manifest, &first, "add-becomes-sub", "add", &changed);
    forget_outcomes(&manifest);
    let (fourth, ok) = search(&manifest, &mutations, &["add-becomes-sub"]);
    assert!(ok);
    assert_eq!(
        verdicts(&fourth),
        expect(&[("add-becomes-sub", "killed", Some("add"), false)])
    );
    assert_eq!(
        calls(&fourth, "add-becomes-sub"),
        vec![strings(&["add", "nested", "inline", "sub"])]
    );
    assert_eq!(
        killer_of(&manifest, &fourth, "add-becomes-sub"),
        Some(("add".to_owned(), add))
    );

    // A killer cache file that does not parse is empty, and is replaced.
    fs::write(killers_file(&manifest), "{ not json").unwrap();
    forget_outcomes(&manifest);
    let (fifth, ok) = search(&manifest, &mutations, &["add-becomes-sub"]);
    assert!(ok);
    assert_eq!(
        verdicts(&fifth),
        expect(&[("add-becomes-sub", "killed", Some("add"), false)])
    );
    assert_eq!(
        killer_of(&manifest, &fifth, "add-becomes-sub").unwrap().0,
        "add"
    );
}

#[test]
fn a_timeout_is_never_cached_and_a_later_clean_kill_is() {
    let manifest = fixture("loop", "timeout").join("FLOW-search.toml");
    let mutations = manifest.with_file_name("MUTATIONS.toml");
    // countdown(3) never ends on the mutant (3 steps to 3); twice(4) does not reach the
    // countdown rule and agrees. The status is the runner's Timeout, and nothing is cached.
    let (first, ok) = search(&manifest, &mutations, &[]);
    assert!(ok, "{first:#}");
    assert_eq!(
        verdicts(&first),
        expect(&[("countdown-escapes", "timeout", None, false)])
    );
    assert_eq!(
        executed(&first, "countdown-escapes"),
        pairs(&[("countdown", "timeout"), ("twice", "agree")])
    );
    assert!(killers(&manifest, &first).is_empty());

    // A hand-made entry naming the program that times out: the cached call is a timeout, so
    // the entry is removed and the full call decides. Its status stays Timeout: a stale entry
    // never turns the verdict into the status of the other programs alone.
    let countdown = program_digest(&first, "countdown");
    set_killer(
        &manifest,
        &first,
        "countdown-escapes",
        "countdown",
        &countdown,
    );
    forget_outcomes(&manifest);
    let (stale, ok) = search(&manifest, &mutations, &[]);
    assert!(ok);
    assert_eq!(
        verdicts(&stale),
        expect(&[("countdown-escapes", "timeout", None, false)])
    );
    assert_eq!(
        calls(&stale, "countdown-escapes"),
        vec![strings(&["countdown"]), strings(&["countdown", "twice"])]
    );
    assert!(killers(&manifest, &stale).is_empty());

    // countdown(1) ends at countdown(-1) on the mutant and at 0 on the baseline. It runs
    // after the program that times out, and FirstKill folds the clean kill above the
    // timeout: Killed, with countdown-one cached.
    append(
        &manifest,
        "\n[[program]]\nid = \"countdown-one\"\ntext = \"countdown(1)\"\n",
    );
    forget_outcomes(&manifest);
    let (second, ok) = search(&manifest, &mutations, &[]);
    assert!(ok, "{second:#}");
    assert_eq!(
        verdicts(&second),
        expect(&[("countdown-escapes", "killed", Some("countdown-one"), false)])
    );
    assert_eq!(
        executed(&second, "countdown-escapes"),
        pairs(&[("countdown", "timeout"), ("countdown-one", "distinguish")])
    );
    assert_eq!(
        killer_of(&manifest, &second, "countdown-escapes")
            .unwrap()
            .0,
        "countdown-one"
    );
    forget_outcomes(&manifest);
    let (third, ok) = search(&manifest, &mutations, &[]);
    assert!(ok);
    assert_eq!(
        verdicts(&third),
        expect(&[("countdown-escapes", "killed", Some("countdown-one"), true)])
    );
    assert_eq!(
        calls(&third, "countdown-escapes"),
        vec![strings(&["countdown-one"])]
    );

    // A cached killer that times out never keeps its entry: the full call decides again.
    set_killer(
        &manifest,
        &third,
        "countdown-escapes",
        "countdown",
        &countdown,
    );
    forget_outcomes(&manifest);
    let (fourth, ok) = search(&manifest, &mutations, &[]);
    assert!(ok);
    assert_eq!(
        verdicts(&fourth),
        expect(&[("countdown-escapes", "killed", Some("countdown-one"), false)])
    );
    assert_eq!(
        calls(&fourth, "countdown-escapes"),
        vec![
            strings(&["countdown"]),
            strings(&["countdown", "countdown-one", "twice"])
        ]
    );
    assert_eq!(
        killer_of(&manifest, &fourth, "countdown-escapes")
            .unwrap()
            .0,
        "countdown-one"
    );
}

#[test]
fn every_status_and_an_invalid_mutation_that_does_not_stop_the_others() {
    let manifest = fixture("calc", "statuses").join("FLOW.toml");
    let mutations = manifest.with_file_name("MUTATIONS-statuses.toml");
    let (document, ok) = search(&manifest, &mutations, &[]);
    assert!(ok, "{document:#}");
    assert_eq!(
        verdicts(&document),
        expect(&[
            ("no-such-rule", "invalid-mutation", None, false),
            ("add-becomes-sub", "killed", Some("add"), false),
            ("add-commutes", "survived", None, false),
            ("add-in-a-group", "equivalent", None, false),
            ("add-unbound", "invalid", None, false),
            ("add-ill-sorted", "invalid-mutation", None, false),
        ])
    );
    let reason = |id: &str| mutation(&document, id)["reason"].clone();
    assert_eq!(reason("no-such-rule"), json!("unknown-label"));
    assert_eq!(reason("add-ill-sorted"), json!("edited-load-failed"));
    assert_eq!(reason("add-in-a-group"), json!("equivalent-compilation"));
    assert_eq!(reason("add-unbound"), json!("rejected"));
    // A mutation that does not resolve is never compiled or run.
    for id in ["no-such-rule", "add-ill-sorted"] {
        assert_eq!(mutation(&document, id)["calls"], json!([]), "{id}");
        assert_eq!(mutation(&document, id)["digest"], Value::Null, "{id}");
    }
    // Equivalent and Invalid are mutant-scope statuses: the mutant runs on no program.
    for id in ["add-in-a-group", "add-unbound"] {
        assert_eq!(executed(&document, id), Vec::new(), "{id}");
        assert_eq!(calls(&document, id).len(), 1, "{id}");
    }
    assert_eq!(
        killers(&manifest, &document)
            .into_iter()
            .map(|(_, mutation, program, _)| (mutation, program))
            .collect::<Vec<_>>(),
        vec![("add-becomes-sub".to_owned(), "add".to_owned())]
    );
    assert_eq!(
        document["counts"],
        json!({"killed": 1, "survived": 1, "equivalent": 1, "invalid": 1, "timeout": 0,
               "unknown": 0, "error": 0, "invalid-mutation": 2})
    );
}

#[test]
fn a_baseline_mismatch_stops_the_run_without_a_verdict() {
    // Cold killer cache: the first call over every comparable program finds that add's
    // baseline run no longer has its cached run digest.
    let manifest = fixture("calc", "mismatch-cold").join("FLOW.toml");
    let mutations = manifest.with_file_name("MUTATIONS.toml");
    let (filled, status) = results(&manifest, &ResultsOptions::default());
    assert_eq!(status, EXIT_OK);
    let filled = json!({"spec": filled["spec"], "programs": filled["programs"]});
    corrupt_run_digest(&manifest, &filled, "add");
    let (document, ok) = search(&manifest, &mutations, &[]);
    assert!(!ok);
    assert_eq!(
        verdicts(&document),
        expect(&[("add-becomes-sub", "error", None, false)])
    );
    assert_eq!(
        mutation(&document, "add-becomes-sub")["reason"],
        json!("baseline-mismatch:add")
    );
    assert_eq!(
        document["stopped"],
        json!({"mutation": "add-becomes-sub", "reason": "baseline-mismatch:add"})
    );
    // Since F-14 the hints are written after a corpus error too (F-05 review 1 minor 3): the
    // file holds no hint.
    assert!(killers_file(&manifest).is_file());
    assert!(killers(&manifest, &filled).is_empty());

    // Warm killer cache: the one-program call over a cached killer checks its baseline too.
    // The mutations before it keep their verdicts; its entry is not touched.
    let manifest = fixture("calc", "mismatch-warm").join("FLOW.toml");
    let (warm, ok) = search(&manifest, &mutations, &[]);
    assert!(ok);
    let before = killers(&manifest, &warm);
    corrupt_run_digest(&manifest, &warm, "nested");
    forget_outcomes(&manifest);
    let (document, ok) = search(&manifest, &mutations, &[]);
    assert!(!ok);
    assert_eq!(
        verdicts(&document),
        expect(&[
            ("add-becomes-sub", "killed", Some("add"), true),
            ("sub-off-by-one", "killed", Some("sub"), true),
            ("mul-becomes-add", "error", None, false),
        ])
    );
    assert_eq!(
        mutation(&document, "mul-becomes-add")["reason"],
        json!("baseline-mismatch:nested")
    );
    assert_eq!(
        calls(&document, "mul-becomes-add"),
        vec![strings(&["nested"])]
    );
    assert_eq!(killers(&manifest, &document), before);
    let report: Value =
        serde_json::from_str(&fs::read_to_string(cache_of(&manifest).join(REPORT_FILE)).unwrap())
            .unwrap();
    assert_eq!(report, document);
}

#[test]
fn only_runs_the_named_mutations() {
    let manifest = fixture("register", "only").join("FLOW.toml");
    let (document, ok) = search(
        &manifest,
        &manifest.with_file_name("MUTATIONS.toml"),
        &["no-seq", "get-offset"],
    );
    assert!(ok);
    // File order, not --only order.
    assert_eq!(
        verdicts(&document),
        expect(&[
            ("get-offset", "killed", Some("increment"), false),
            ("no-seq", "killed", Some("increment"), false),
        ])
    );
    assert_eq!(killers(&manifest, &document).len(), 2);
}

#[test]
fn programs_that_cannot_kill_are_never_run() {
    // A refused program fails the command but not the search; a timeout program is never
    // given to the runner.
    let manifest = fixture("calc", "refused").join("FLOW-bad-program.toml");
    let (document, ok) = search(
        &manifest,
        &manifest.with_file_name("MUTATIONS.toml"),
        &["add-becomes-sub"],
    );
    assert!(!ok);
    assert_eq!(
        verdicts(&document),
        expect(&[("add-becomes-sub", "killed", Some("add"), false)])
    );
    assert_eq!(
        calls(&document, "add-becomes-sub"),
        vec![strings(&["add", "sub"])]
    );

    let manifest = fixture("loop", "no-comparable").join("FLOW-timeout.toml");
    let text = fs::read_to_string(&manifest).unwrap().replace(
        "[[program]]\nid = \"countdown\"\nfile = \"programs/countdown.loop\"\n",
        "",
    );
    fs::write(&manifest, text).unwrap();
    let (document, ok) = search(&manifest, &manifest.with_file_name("MUTATIONS.toml"), &[]);
    assert!(!ok);
    assert_eq!(document["programs"][0]["class"], "timeout");
    assert_eq!(
        verdicts(&document),
        expect(&[("countdown-escapes", "error", None, false)])
    );
    assert_eq!(
        mutation(&document, "countdown-escapes")["reason"],
        json!("no-comparable-program")
    );
    assert_eq!(
        calls(&document, "countdown-escapes"),
        Vec::<Vec<String>>::new()
    );
}

#[test]
fn the_binarys_run_command() {
    let binary = env!("CARGO_BIN_EXE_kink-flow");
    let dir = fixture("register", "binary");
    let manifest = dir.join("FLOW.toml");
    let mutations = dir.join("MUTATIONS.toml");
    let cache = scratch("binary-cache");
    let output = Command::new(binary)
        .arg("run")
        .arg(&manifest)
        .arg(&mutations)
        .args(["--only", "put-offset", "--cache"])
        .arg(&cache)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(i32::from(EXIT_OK)));
    let document: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(document["schema"], "kink-flow-run");
    assert_eq!(
        verdicts(&document),
        expect(&[("put-offset", "killed", Some("store"), false)])
    );
    assert!(cache.join(REPORT_FILE).is_file());
    assert!(hints_path(&cache).is_file());
    assert!(!dir.join(CACHE_DIRECTORY).exists());

    let bad = dir.join("BAD.toml");
    fs::write(&bad, "[[mutation]]\nid = \"m\"\nlabel = \"x\"\n").unwrap();
    for (args, code) in [
        (vec!["run"], EXIT_USAGE),
        (vec!["run", "FLOW.toml"], EXIT_USAGE),
        (
            vec!["run", "FLOW.toml", "MUTATIONS.toml", "--only"],
            EXIT_USAGE,
        ),
        (
            vec!["run", "FLOW.toml", "MUTATIONS.toml", "--only", "nope"],
            EXIT_USAGE,
        ),
        (
            vec!["run", "FLOW.toml", "MUTATIONS.toml", "--frobnicate"],
            EXIT_USAGE,
        ),
        (vec!["run", "FLOW.toml", "missing.toml"], EXIT_USAGE),
        (vec!["run", "FLOW.toml", "BAD.toml"], EXIT_CORPUS),
    ] {
        let output = Command::new(binary)
            .args(&args)
            .current_dir(&dir)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(i32::from(code)), "{args:?}");
        if code == EXIT_CORPUS {
            let document: Value = serde_json::from_slice(&output.stdout).unwrap();
            assert_eq!(document["mutation_list"]["outcome"], "refused");
        }
    }
}
