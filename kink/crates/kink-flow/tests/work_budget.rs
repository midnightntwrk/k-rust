//! Re-pin lane 1 (L1-1): `[budget] work_factor`, the work budget of the mutants' runs.
//!
//! The loop fixture's `countdown-escapes` makes `countdown(3)` step to itself forever. Under the
//! fixture's time bound it is a timeout (tests/search.rs); with a work budget its run ends in a
//! work-bound leaf long before any time bound, so the program is `unknown` for the mutant with a
//! cause that names the budget, never a kill, and nothing is cached for it. The budget enters the
//! outcome key: another factor reuses no cached outcome.

use kink_flow::{
    FlowManifest, MutationList,
    results::CACHE_DIRECTORY,
    search::{ProgramOrder, RunOptions, run},
};
use serde_json::Value;
use std::{
    fs,
    path::{Path, PathBuf},
};

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

/// A private copy of the loop fixture whose search manifest has a one-minute time bound and
/// `work_factor = factor`.
fn fixture(test: &str, factor: u64) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-work-{}", std::process::id()))
        .join(test);
    let _ = fs::remove_dir_all(&dir);
    copy_dir(
        &Path::new(env!("CARGO_MANIFEST_DIR")).join("../../testdata/flow/loop"),
        &dir,
    );
    let manifest = dir.join("FLOW-search.toml");
    set_factor(&manifest, factor);
    manifest
}

fn set_factor(manifest: &Path, factor: u64) {
    let text = fs::read_to_string(manifest).unwrap();
    let text = text
        .lines()
        .filter(|line| !line.starts_with("work_factor"))
        .map(|line| match line {
            "time_ms = 500" | "time_ms = 60000" => "time_ms = 60000".to_owned(),
            "[budget]" => format!("[budget]\nwork_factor = {factor}"),
            line => line.to_owned(),
        })
        .collect::<Vec<_>>()
        .join("\n");
    fs::write(manifest, text + "\n").unwrap();
}

fn search(manifest: &Path) -> Value {
    let (document, ok) = run(
        &FlowManifest::read(manifest).unwrap(),
        &MutationList::read(&manifest.with_file_name("MUTATIONS.toml")).unwrap(),
        &RunOptions {
            only: Vec::new(),
            cache: None,
            order: ProgramOrder::Corpus,
            compile_workers: None,
            memo: kink_flow::memo::MemoUse::On,
        },
    );
    assert!(ok, "{document:#}");
    document
}

/// `(program, outcome, cause, cached)` of every executed entry of `countdown-escapes`.
fn executed(document: &Value) -> Vec<(String, String, Option<String>, bool)> {
    let mutation = document["mutations"]
        .as_array()
        .unwrap()
        .iter()
        .find(|m| m["id"] == "countdown-escapes")
        .unwrap();
    assert_eq!(mutation["status"], "unknown", "{mutation:#}");
    assert!(mutation["killer"].is_null());
    mutation["executed"]
        .as_array()
        .unwrap()
        .iter()
        .map(|e| {
            (
                e["program"].as_str().unwrap().to_owned(),
                e["outcome"].as_str().unwrap().to_owned(),
                e["cause"].as_str().map(str::to_owned),
                e["cached"].as_bool().unwrap(),
            )
        })
        .collect()
}

mod kink_tier {
    use super::*;

    #[test]
    #[ignore = "kink"]
    fn a_mutant_that_never_ends_is_unknown_under_the_work_budget_and_never_cached() {
        let manifest = fixture("loop-work", 2);
        let started = std::time::Instant::now();
        let first = search(&manifest);
        // The time bound is a minute; the work budget stops the loop long before.
        assert!(
            started.elapsed() < std::time::Duration::from_secs(30),
            "{:?}",
            started.elapsed()
        );
        let entries = executed(&first);
        assert_eq!(entries.len(), 2, "{entries:?}");
        let (program, outcome, cause, cached) = &entries[0];
        assert_eq!(
            (program.as_str(), outcome.as_str(), *cached),
            ("countdown", "unknown", false)
        );
        let cause = cause.as_deref().unwrap();
        assert!(
            cause.contains("the run reached its work budget (work_factor = 2)")
                && cause.contains("work-bound 1"),
            "{cause}"
        );
        assert_eq!(
            (entries[1].0.as_str(), entries[1].1.as_str(), entries[1].3),
            ("twice", "agree", false)
        );

        // A re-run: the agreement is cached, the unknown outcome is not.
        let second = executed(&search(&manifest));
        assert_eq!(
            second
                .iter()
                .map(|(program, outcome, _, cached)| (program.as_str(), outcome.as_str(), *cached))
                .collect::<Vec<_>>(),
            [("twice", "agree", true), ("countdown", "unknown", false)]
        );

        // Another factor is another outcome key: nothing cached applies.
        set_factor(&manifest, 3);
        let third = executed(&search(&manifest));
        assert!(third.iter().all(|(.., cached)| !cached), "{third:?}");
    }
}
