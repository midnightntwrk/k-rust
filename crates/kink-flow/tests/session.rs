//! One baseline session per command (flow F-12, README 6.3): in one `kink-flow` command each
//! program's baseline runs live at most once, shared by the result update and every call of the
//! kill search; `results --verify` runs every program live; the drift check still stops a run on
//! a hand-edited record. Every document reports `baseline_runs: {live, reused}`.

use kink_flow::{
    FlowManifest, MutationList,
    cli::{EXIT_OK, results},
    outcomes::OUTCOMES_DIRECTORY,
    results::{CACHE_DIRECTORY, ResultsOptions},
    search::{RunMode, RunOptions, run_with},
};
use serde_json::{Value, json};
use std::{
    collections::BTreeSet,
    fs,
    path::{Path, PathBuf},
};

fn flow(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../testdata/flow")
        .join(name)
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

/// A private copy of a testdata/flow fixture; its `FLOW.toml`.
fn fixture(name: &str, test: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-session-{}", std::process::id()))
        .join(test);
    let _ = fs::remove_dir_all(&dir);
    copy_dir(&flow(name), &dir.join(name));
    dir.join(name).join("FLOW.toml")
}

/// `kink-flow run` (or `run --verify`) through the library, as the binary runs it.
fn run(manifest: &Path, mode: RunMode) -> (Value, bool) {
    let flow = FlowManifest::read(manifest).unwrap();
    let list = MutationList::read(&manifest.with_file_name("MUTATIONS.toml")).unwrap();
    run_with(&flow, &list, &RunOptions::default(), mode)
}

fn results_with(manifest: &Path, verify: bool) -> Value {
    let (document, code) = results(
        manifest,
        &ResultsOptions {
            verify,
            cache: None,
        },
    );
    assert_eq!(code, EXIT_OK, "{document:#}");
    document
}

fn forget_outcomes(manifest: &Path) {
    let _ = fs::remove_dir_all(
        manifest
            .parent()
            .unwrap()
            .join(CACHE_DIRECTORY)
            .join(OUTCOMES_DIRECTORY),
    );
}

/// `(live, reused)` of a document's `baseline_runs`.
fn baseline_runs(document: &Value) -> (u64, u64) {
    let runs = &document["baseline_runs"];
    (
        runs["live"].as_u64().unwrap(),
        runs["reused"].as_u64().unwrap(),
    )
}

/// The programs of every campaign call of every mutation row, in order.
fn call_programs(document: &Value) -> Vec<String> {
    document["mutations"]
        .as_array()
        .unwrap()
        .iter()
        .flat_map(|m| m["calls"].as_array().unwrap().iter())
        .flat_map(|call| call["programs"].as_array().unwrap().iter())
        .map(|p| p.as_str().unwrap().to_owned())
        .collect()
}

/// The programs the result update ran in this command (rows not taken from the cache).
fn computed(document: &Value) -> BTreeSet<String> {
    document["programs"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|p| p["cached"] == false)
        .map(|p| p["id"].as_str().unwrap().to_owned())
        .collect()
}

/// `(id, status, killer)` of every mutation row.
fn verdicts(document: &Value) -> Vec<(String, String, Option<String>)> {
    document["mutations"]
        .as_array()
        .unwrap()
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

/// tests/search.rs `CALC_VERDICTS`, which F-12 must not change.
fn calc_verdicts() -> Vec<(String, String, Option<String>)> {
    [
        ("add-becomes-sub", "killed", Some("add")),
        ("sub-off-by-one", "killed", Some("sub")),
        ("mul-becomes-add", "killed", Some("nested")),
        ("no-mul", "killed", Some("nested")),
        ("add-swaps-operands", "survived", None),
    ]
    .iter()
    .map(|(id, status, killer)| {
        (
            (*id).to_owned(),
            (*status).to_owned(),
            killer.map(str::to_owned),
        )
    })
    .collect()
}

/// Each program's baseline ran live at most once in the command: every live run is a distinct
/// program the command executed (the result update's or a call's), and every other baseline
/// request of a call was answered by the session.
fn assert_once_per_program(document: &Value, executed: &BTreeSet<String>) {
    let calls = call_programs(document);
    let (live, reused) = baseline_runs(document);
    assert_eq!(live as usize, executed.len(), "{document:#}");
    assert_eq!(
        (live + reused) as usize,
        computed(document).len() + calls.len(),
        "every baseline request is one live run or one reuse"
    );
}

#[test]
fn each_program_baseline_runs_live_at_most_once_per_run_command() {
    let manifest = fixture("calc", "run");
    // Cold: the result update runs every program live; every call then reuses those runs.
    let (cold, ok) = run(&manifest, RunMode::Search);
    assert!(ok, "{cold:#}");
    assert_eq!(verdicts(&cold), calc_verdicts());
    let programs = computed(&cold);
    assert_eq!(programs.len(), 4);
    assert!(call_programs(&cold).iter().all(|p| programs.contains(p)));
    assert_eq!(baseline_runs(&cold), (4, call_programs(&cold).len() as u64));
    assert_once_per_program(&cold, &programs);

    // Warm: tier 1 decides every mutation with no call, and the results are cached: no
    // baseline runs at all.
    let (warm, ok) = run(&manifest, RunMode::Search);
    assert!(ok, "{warm:#}");
    assert_eq!(verdicts(&warm), calc_verdicts());
    assert!(call_programs(&warm).is_empty());
    assert_eq!(baseline_runs(&warm), (0, 0));

    // Hints only: the live baseline runs are the distinct programs the calls ran; a program
    // two calls run (nested: the hint of two mutations, then the survivor's cold call) is
    // live once.
    forget_outcomes(&manifest);
    let (hinted, ok) = run(&manifest, RunMode::Search);
    assert!(ok, "{hinted:#}");
    assert_eq!(verdicts(&hinted), calc_verdicts());
    let calls = call_programs(&hinted);
    let distinct = calls.iter().cloned().collect::<BTreeSet<_>>();
    assert!(computed(&hinted).is_empty());
    assert!(calls.len() > distinct.len(), "{calls:?}");
    assert_eq!(
        baseline_runs(&hinted),
        (distinct.len() as u64, (calls.len() - distinct.len()) as u64)
    );
    assert_once_per_program(&hinted, &distinct);
}

#[test]
fn results_runs_each_program_live_and_verify_runs_every_program_live() {
    let manifest = fixture("calc", "results");
    let fresh = results_with(&manifest, false);
    assert_eq!(fresh["baseline_runs"], json!({"live": 4, "reused": 0}));
    let cached = results_with(&manifest, false);
    assert_eq!(cached["summary"]["computed"], 0);
    assert_eq!(cached["baseline_runs"], json!({"live": 0, "reused": 0}));
    // A fresh session per command: `--verify` runs every program live, none is reused.
    let verified = results_with(&manifest, true);
    assert_eq!(verified["summary"]["mismatches"], 0);
    assert_eq!(verified["baseline_runs"], json!({"live": 4, "reused": 0}));
    assert!(
        verified["programs"]
            .as_array()
            .unwrap()
            .iter()
            .all(|p| p["verify"] == "match")
    );
}

#[test]
fn run_verify_reuses_its_live_runs_and_the_drift_check_still_stops_a_run() {
    let manifest = fixture("calc", "verify");
    let (cold, ok) = run(&manifest, RunMode::Search);
    assert!(ok, "{cold:#}");
    // run --verify: the result update re-runs every program live; the cold calls reuse them.
    let (verified, ok) = run(&manifest, RunMode::Verify);
    assert!(ok, "{verified:#}");
    assert_eq!(verdicts(&verified), calc_verdicts());
    let calls = call_programs(&verified);
    assert_eq!(baseline_runs(&verified), (4, calls.len() as u64));

    // A hand-edited record: the program's record is cached, so the first call that runs it
    // runs its baseline live in this command, and the drift check compares that run with the
    // record and stops the run without a verdict.
    let digest = |id: &str| {
        cold["programs"]
            .as_array()
            .unwrap()
            .iter()
            .find(|p| p["id"] == id)
            .unwrap()["digest"]
            .as_str()
            .unwrap()
            .to_owned()
    };
    let record = manifest
        .parent()
        .unwrap()
        .join(CACHE_DIRECTORY)
        .join("results")
        .join(cold["spec"]["digest"].as_str().unwrap())
        .join(format!("{}.json", digest("add")));
    let mut value: Value = serde_json::from_str(&fs::read_to_string(&record).unwrap()).unwrap();
    value["run_sha256"] = json!("0".repeat(64));
    fs::write(&record, serde_json::to_string(&value).unwrap()).unwrap();
    forget_outcomes(&manifest);
    let (drifted, ok) = run(&manifest, RunMode::Search);
    assert!(!ok);
    let first = &drifted["mutations"][0];
    assert_eq!(first["id"], "add-becomes-sub");
    assert_eq!(first["status"], "error");
    assert_eq!(first["reason"], "baseline-mismatch:add");
    assert_eq!(drifted["stopped"]["mutation"], "add-becomes-sub");
    assert_eq!(drifted["mutations"].as_array().unwrap().len(), 1);
    assert_eq!(baseline_runs(&drifted), (1, 0));
}
