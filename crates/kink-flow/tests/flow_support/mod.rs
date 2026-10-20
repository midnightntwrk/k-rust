//! Fixture helpers shared by kink-flow's integration tests (test-gate TG-F), included with
//! `mod flow_support;`; each test binary uses a subset of them.
//!
//! [`after_cold`] shares the cold run of a fixture list between the tests of one test binary in
//! one test run: under nextest every test is its own process, so the run is made once, by the
//! first test that needs it, in a directory of the binary and the run, under a file lock, and
//! every test gets a private copy of the fixture with that run's cache, and its document. A test
//! that checks a cold run against another fresh run (determinism, timings) makes its own.
#![allow(dead_code)]

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

/// The testdata/flow fixture `name`.
pub fn flow(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../testdata/flow")
        .join(name)
}

/// Copy `from` into `to` without its cache directory.
pub fn copy_dir(from: &Path, to: &Path) {
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

/// Copy every file of `from` into `to`, the cache directory included.
pub fn copy_all(from: &Path, to: &Path) {
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

/// `kink-flow run` of every mutation of `mutations` through the library, as the binary runs it,
/// in F-05's corpus order (so that the pinned calls and killers do not depend on host timing),
/// with the default compile workers and the memos.
pub fn corpus_run(manifest: &Path, mutations: &Path) -> (Value, bool) {
    let manifest = FlowManifest::read(manifest).unwrap();
    let list = MutationList::read(mutations).unwrap();
    run(
        &manifest,
        &list,
        &RunOptions {
            only: Vec::new(),
            cache: None,
            order: ProgramOrder::Corpus,
            compile_workers: None,
            memo: kink_flow::memo::MemoUse::On,
        },
    )
}

/// Where this test binary keeps the cold runs of this test run: one directory per nextest run
/// (`NEXTEST_RUN_ID`) or, under `cargo test`, per process, and per test binary.
fn cold_root() -> PathBuf {
    let run = std::env::var("NEXTEST_RUN_ID")
        .ok()
        .filter(|id| !id.is_empty() && id.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-'))
        .unwrap_or_else(|| format!("process-{}", std::process::id()));
    let binary = std::env::current_exe().unwrap();
    Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join("kink-flow-cold")
        .join(run)
        .join(binary.file_name().unwrap())
}

/// A private copy, at `into`, of the testdata/flow fixture `name` whose cache holds the cold
/// [`corpus_run`] of `mutations` under `manifest` (file names in the fixture), and that run's
/// document. The cold run is made once per test binary and test run (its admission dominates a
/// test's time) and copied for each test.
pub fn after_cold(name: &str, manifest: &str, mutations: &str, into: &Path) -> Value {
    let key = format!("{}-{manifest}-{mutations}", name.replace('/', "_"));
    let root = cold_root().join(&key);
    fs::create_dir_all(root.parent().unwrap()).unwrap();
    let lock = fs::File::create(root.with_extension("lock")).unwrap();
    lock.lock().unwrap();
    let done = root.join("cold.json");
    if !done.is_file() {
        let _ = fs::remove_dir_all(&root);
        let dir = root.join("fixture");
        copy_dir(&flow(name), &dir);
        let (cold, ok) = corpus_run(&dir.join(manifest), &dir.join(mutations));
        assert!(ok, "{cold:#}");
        // Written last: a run that failed or was cut short leaves no document to share.
        fs::write(&done, serde_json::to_vec(&cold).unwrap()).unwrap();
    }
    let cold: Value = serde_json::from_slice(&fs::read(&done).unwrap()).unwrap();
    let _ = fs::remove_dir_all(into);
    copy_all(&root.join("fixture"), into);
    drop(lock);
    cold
}
