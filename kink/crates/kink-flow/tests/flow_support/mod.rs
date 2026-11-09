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
    search::{RunOptions, run},
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

/// Rewrite the manifest at `manifest` with its `[[program]]` entries in reverse order: a corpus
/// with the same programs, whose search order lists them the other way round. A program's
/// digest does not name its place, so every result record stays in use.
pub fn reverse_programs(manifest: &Path) {
    let mut value: toml::Table = fs::read_to_string(manifest).unwrap().parse().unwrap();
    if let Some(toml::Value::Array(programs)) = value.get_mut("program") {
        programs.reverse();
    }
    fs::write(manifest, toml::to_string(&value).unwrap()).unwrap();
}

/// `kink-flow run` of every mutation of `mutations` through the library, as the binary runs it,
/// with the default compile workers and the memos.
pub fn corpus_run(manifest: &Path, mutations: &Path) -> (Value, bool) {
    let manifest = FlowManifest::read(manifest).unwrap();
    let list = MutationList::read(mutations).unwrap();
    run(
        &manifest,
        &list,
        &RunOptions {
            legacy_lock: None,
            only: Vec::new(),
            cache: None,
            compile_workers: None,
            memo: kink_flow::memo::MemoUse::On,
            schedule: kink_campaign::ScheduleMode::FirstKill,
            lock: None,
            locked: false,
        },
    )
}

/// Where this test binary keeps the cold runs of this test run: one directory per nextest run
/// (`NEXTEST_RUN_ID`) or, under `cargo test`, per process, and per test binary. A process is
/// named by its id and the time it first asked, so a later process that reuses the id never
/// finds an earlier build's cold run.
fn cold_root() -> PathBuf {
    static PROCESS: std::sync::OnceLock<String> = std::sync::OnceLock::new();
    let run = std::env::var("NEXTEST_RUN_ID")
        .ok()
        .filter(|id| !id.is_empty() && id.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-'))
        .unwrap_or_else(|| {
            PROCESS
                .get_or_init(|| {
                    let started = std::time::SystemTime::now()
                        .duration_since(std::time::UNIX_EPOCH)
                        .unwrap()
                        .as_nanos();
                    format!("process-{}-{started}", std::process::id())
                })
                .clone()
        });
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
        // Written last, and renamed into place: a run that failed or was cut short leaves no
        // document to share, and no half-written one.
        let partial = root.join("cold.json.partial");
        fs::write(&partial, serde_json::to_vec(&cold).unwrap()).unwrap();
        fs::rename(&partial, &done).unwrap();
    }
    let cold: Value = serde_json::from_slice(&fs::read(&done).unwrap()).unwrap();
    let _ = fs::remove_dir_all(into);
    copy_all(&root.join("fixture"), into);
    drop(lock);
    cold
}

/// The `z3` member every kink-flow document of this build has: under the Z3 profile the Z3 build,
/// `{version, library_sha256}`, read from k-rust's `z3_build` rather than from kink-flow; `None`
/// under the portable profile, whose documents have no such member.
pub fn z3_member() -> Option<Value> {
    cfg!(feature = "z3").then(|| {
        let build = k_rust::backend::z3_build().expect("a Z3 build links Z3");
        serde_json::json!({"version": build.version, "library_sha256": build.library_sha256})
    })
}

/// The lines a verdicts rendering of a `document` (`run` or `coverage`) opens with: the record's
/// header (its comment and `schema`), then the command's section's `[run]` or `[coverage]` line,
/// the comment naming the command whose verdicts it holds, and `version`, before
/// [`solver_lines`].
pub fn heading(document: &str) -> String {
    let comment = match document {
        "run" => {
            "# The verdicts of kink's `run` command (`krs kink run`, `kink-flow run`): the next run tries\n\
             # each `killer` first, a run without --locked rewrites this section, and `run --locked` checks\n\
             # that it is current.\n"
        }
        "coverage" => {
            "# The verdicts of kink's `coverage` command (`krs kink coverage`, `kink-flow coverage`): the\n\
             # next run tries each flip's `killer` first, a run without --locked rewrites this section, and\n\
             # `coverage --locked` checks that it is current.\n"
        }
        other => panic!("no rendering of a {other} document"),
    };
    format!(
        "# kink's verdicts of a corpus, one section per command: [run] (`run` on a mutation list) and\n\
         # [coverage] (`coverage`). As a lock (`--lock FILE`; krs keeps <corpus>/kink.lock), each command\n\
         # reads, checks (--locked) and rewrites only its own section, and keeps the other as it is.\n\
         schema = \"kink-flow-verdicts\"\n\n[{document}]\n{comment}version = 24\n"
    )
}

/// The comment a run section writes before its first `[[run.mutation]]`.
pub const MUTATIONS_LEGEND: &str = "\
# Each [[run.mutation]] is a mutation of the list, by its id, and its verdict: killed (a
# program's result differs on the mutant; `killer` names it), survived (every program agreed;
# `horizon`, those that agreed only up to an observation horizon), equivalent or unkillable (no
# program can tell the mutant apart), timeout, unknown or error (no verdict), invalid-mutation
# or not-admitted (its author must fix it; `reason` says why).
";

/// The lines a verdicts rendering of this build writes for its solver, after `document`:
/// `profile`, and under the Z3 profile the Z3 build, `z3_version` and, when the build names its
/// library, `z3_library_sha256`, read from k-rust's `z3_build` rather than from kink-flow.
pub fn solver_lines() -> String {
    let profile = if cfg!(feature = "z3") { "z3" } else { "no-z3" };
    let mut lines = format!("profile = \"{profile}\"\n");
    if cfg!(feature = "z3") {
        let build = k_rust::backend::z3_build().expect("a Z3 build links Z3");
        lines.push_str(&format!("z3_version = \"{}\"\n", build.version));
        if let Some(digest) = &build.library_sha256 {
            lines.push_str(&format!("z3_library_sha256 = \"{digest}\"\n"));
        }
    }
    lines
}
