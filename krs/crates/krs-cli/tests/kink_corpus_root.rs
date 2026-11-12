//! `[corpus] root` through `krs kink` (CORPUS-ROOT): two KRS definitions of one interface, each
//! with its flow beside it, read their cases from one corpus root, and each case has one id in
//! both.
//!
//! The definitions are the introduction's story package (`docs-site/story/plus`, here
//! `story-plus`) and `story-refined`, the same package whose `plus_succ` recurses on its
//! accumulator: the same initializer, the same cell, other rules. The workspace is
//!
//! ```text
//! corpus/cases/t1.nat .. t4.nat      the story's four cases, in no definition's directory
//! spec/kink/FLOW.toml                story-plus's flow: `[corpus] root = "../../corpus"`
//! spec/kink/mutations/plus.toml      the story's edits, patches of story-plus's emitted K
//! spec/kink/answer.sh                an implementation's command, beside the flow
//! refined/kink/FLOW.toml             story-refined's flow, naming the same root
//! refined/kink/mutations/zero.toml   an edit of story-refined's emitted K
//! ```
//!
//! and each flow's `definition.k`, `kink.lock` and `.kink-flow/` are written beside its
//! `FLOW.toml`.

#![cfg(feature = "kink")]

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Output;

use krs_test_support::{
    SharedFixtureTarget, TempDir, fixture_build_env, krs_command, shared_fixture_target, temp_dir,
};
use serde_json::{Value, json};

const STORY: &str = include_str!("../../../../docs-site/story/plus/src/lib.rs");
const STORY_MUTATIONS: &str =
    include_str!("../../../../docs-site/story/plus/kink/mutations/plus.toml");
const STORY_CASES: [(&str, &str); 4] = [
    (
        "t1",
        include_str!("../../../../docs-site/story/plus/kink/cases/t1.nat"),
    ),
    (
        "t2",
        include_str!("../../../../docs-site/story/plus/kink/cases/t2.nat"),
    ),
    (
        "t3",
        include_str!("../../../../docs-site/story/plus/kink/cases/t3.nat"),
    ),
    (
        "t4",
        include_str!("../../../../docs-site/story/plus/kink/cases/t4.nat"),
    ),
];

/// The ids of the cases in every flow that names the root: their paths relative to it.
const IDS: [&str; 4] = [
    "cases/t1.nat",
    "cases/t2.nat",
    "cases/t3.nat",
    "cases/t4.nat",
];

/// The story's first edit, which `story-refined`'s unchanged `plus_zero` takes too.
const REFINED_MUTATIONS: &str = "[[mutation]]\nid = \"a\"\nmisunderstanding = \"forgets what the \
                                 base case returns\"\n\n  [[mutation.edit]]\n  rule = \
                                 \"plus_zero\"\n  find = \"=> N:Nat\"\n  replace = \"=> zero\"\n";

/// An implementation that records each request beside the flow and applies no program.
const ANSWER: &str = "#!/bin/sh\nrequest=$(cat)\nprintf '%s\\n' \"$request\" >> \
                      requests.log\nprintf '{\"end\":\"could-not-apply\",\"reason\":\"records \
                      only\"}\\n'\n";

/// A flow of `package` that reads the corpus root, with `rest` after its programs.
fn flow(package: &str, rest: &str) -> String {
    format!(
        "[spec]\nkrs = {{ package = \"{package}\", definition = \"main\" }}\n\n[corpus]\nroot = \
         \"../../corpus\"\n\n[[program]]\nfiles = \"cases/*.nat\"\n\n{rest}"
    )
}

/// The two packages and the corpus root, in one directory.
struct Workspace {
    directory: TempDir,
    target: SharedFixtureTarget,
}

impl Workspace {
    fn new() -> Self {
        let workspace = Self {
            directory: temp_dir(),
            target: shared_fixture_target(),
        };
        let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../krs")
            .canonicalize()
            .unwrap();
        let krs = serde_json::to_string(krs.to_str().unwrap()).unwrap();
        let refined = STORY.replace("NatSyntax::Succ(Plus(m, n))", "Plus(m, NatSyntax::Succ(n))");
        assert_ne!(refined, STORY);
        for (directory, package, namespace, library) in [
            ("spec", "story-plus", "NAT", STORY),
            ("refined", "story-refined", "NATR", &refined),
        ] {
            workspace.write(
                &format!("{directory}/Cargo.toml"),
                &format!(
                    "[package]\nname = \"{package}\"\nversion = \"0.0.0\"\nedition = \
                     \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path \
                     = {krs} }}\n\n[package.metadata.krs]\nk-namespace = \
                     \"{namespace}\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\n"
                ),
            );
            workspace.write(&format!("{directory}/src/lib.rs"), library);
        }
        for (id, text) in STORY_CASES {
            workspace.write(&format!("corpus/cases/{id}.nat"), text);
        }
        let implementation = "[[implementation]]\nname = \"recorder\"\ncommand = [\"sh\", \
                              \"answer.sh\"]\ngiven = \"inputs\"\nviews = [{ name = \"whole\", \
                              required = true }]\n";
        workspace.write("spec/kink/FLOW.toml", &flow("story-plus", implementation));
        workspace.write("spec/kink/mutations/plus.toml", STORY_MUTATIONS);
        workspace.write("spec/kink/answer.sh", ANSWER);
        workspace.write("refined/kink/FLOW.toml", &flow("story-refined", ""));
        workspace.write("refined/kink/mutations/zero.toml", REFINED_MUTATIONS);
        workspace
    }

    fn path(&self, relative: &str) -> PathBuf {
        self.directory.path().join(relative)
    }

    fn write(&self, relative: &str, contents: &str) {
        let path = self.path(relative);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, contents).unwrap();
    }

    fn read(&self, relative: &str) -> String {
        fs::read_to_string(self.path(relative)).unwrap()
    }

    /// `krs kink VERB --corpus kink ARGUMENTS` from the directory of the package in `package`:
    /// the flow (`kink/FLOW.toml`) names the definition, so the command selects none.
    fn kink(&self, package: &str, verb: &str, arguments: &[&str]) -> Output {
        let mut process = krs_command!();
        fixture_build_env(&mut process, self.target.path());
        process
            .current_dir(self.path(package))
            .args(["kink", verb, "--corpus", "kink"])
            .args(arguments);
        process.output().unwrap()
    }

    /// Every file under the corpus root, sorted.
    fn root_files(&self) -> Vec<PathBuf> {
        let mut files = Vec::new();
        let mut stack = vec![self.path("corpus")];
        while let Some(next) = stack.pop() {
            for entry in fs::read_dir(&next).unwrap() {
                let entry = entry.unwrap();
                if entry.file_type().unwrap().is_dir() {
                    stack.push(entry.path());
                } else {
                    files.push(entry.path());
                }
            }
        }
        files.sort();
        files
    }
}

fn text(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).into_owned()
}

fn json_of(output: &Output) -> Value {
    serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
        panic!(
            "stdout is not JSON ({error}):\n{}\nstderr:\n{}",
            text(&output.stdout),
            text(&output.stderr)
        )
    })
}

#[track_caller]
fn assert_status(output: &Output, code: i32) {
    assert_eq!(
        output.status.code(),
        Some(code),
        "stdout:\n{}\nstderr:\n{}",
        text(&output.stdout),
        text(&output.stderr)
    );
}

/// The program ids a corpus record names in its `[run]` and `[compare]` rows.
fn recorded_programs(lock: &str) -> BTreeSet<String> {
    lock.lines()
        .filter_map(|line| {
            let (key, value) = line.trim().split_once(" = ")?;
            matches!(key, "killer" | "program").then(|| value.trim_matches('"').to_owned())
        })
        .collect()
}

/// Two flows of two definitions over one corpus root: `coverage` and `run` pass in both, every
/// document and both records name the cases by their paths under the root, each flow's files
/// are written beside it and nothing under the root; `compare` states each case's inputs to an
/// implementation from the files under the root, running the implementation's command beside
/// the flow; `prune` says that its report holds for the flow alone; and a case a link leads out
/// of the root is refused, naming the root.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One workspace built once: every verb's reading of the cases under the root."
)]
fn two_definitions_read_one_corpus_root() {
    let workspace = Workspace::new();
    let root_files = workspace.root_files();
    let mut locks = Vec::new();
    for (package, definition, killers) in [
        (
            "spec",
            "story-plus:main",
            vec![
                ("plus/a", "cases/t2.nat"),
                ("plus/b", "cases/t3.nat"),
                ("plus/c", "cases/t4.nat"),
            ],
        ),
        (
            "refined",
            "story-refined:main",
            vec![("zero/a", "cases/t2.nat")],
        ),
    ] {
        let coverage = workspace.kink(package, "coverage", &[]);
        assert_status(&coverage, 0);
        let document = json_of(&coverage);
        assert_eq!(document["definition"]["path"], "kink/definition.k");
        let programs = document["programs"]
            .as_array()
            .unwrap()
            .iter()
            .map(|row| (row["id"].as_str().unwrap(), row["class"].as_str().unwrap()))
            .collect::<Vec<_>>();
        assert_eq!(programs, IDS.map(|id| (id, "comparable")), "{document:#}");

        let run = workspace.kink(package, "run", &[]);
        assert_status(&run, 0);
        let document = json_of(&run);
        let killed = document["mutations"]
            .as_array()
            .unwrap()
            .iter()
            .map(|row| (row["id"].as_str().unwrap(), row["killer"].as_str().unwrap()))
            .collect::<Vec<_>>();
        assert_eq!(killed, killers, "{document:#}");

        // The flow's files are beside it: the emitted K, the record and the cache.
        for file in ["definition.k", "kink.lock", ".kink-flow"] {
            assert!(
                workspace.path(&format!("{package}/kink/{file}")).exists(),
                "{package}/kink/{file}"
            );
        }
        let lock = workspace.read(&format!("{package}/kink/kink.lock"));
        assert!(
            lock.contains(&format!("definition = \"{definition}\"")),
            "{lock}"
        );
        assert!(
            recorded_programs(&lock)
                .iter()
                .all(|id| IDS.contains(&&**id)),
            "{lock}"
        );
        locks.push(lock);
    }
    // Both records name the case that kills the edit both definitions take by one id.
    for lock in &locks {
        assert!(recorded_programs(lock).contains("cases/t2.nat"), "{lock}");
    }

    // `compare`: the request of each case states its input from the file under the root, and
    // the implementation's command is the flow's own file.
    let compare = workspace.kink("spec", "compare", &[]);
    assert_status(&compare, 0);
    let document = json_of(&compare);
    let rows = document["rows"]
        .as_array()
        .unwrap()
        .iter()
        .map(|row| row["program"].as_str().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(rows, IDS, "{document:#}");
    let requests = workspace
        .read("spec/kink/requests.log")
        .lines()
        .map(|line| {
            let request: Value = serde_json::from_str(line).unwrap();
            (request["program"].clone(), request["inputs"].clone())
        })
        .collect::<Vec<_>>();
    let expected = IDS
        .iter()
        .zip(STORY_CASES)
        .map(|(id, (_, text))| (json!(id), json!({"pgm": {"$text": text}})))
        .collect::<Vec<_>>();
    assert_eq!(requests, expected);
    let lock = workspace.read("spec/kink/kink.lock");
    assert_eq!(
        recorded_programs(&lock),
        IDS.iter().map(|id| (*id).to_owned()).collect(),
        "{lock}"
    );

    // `prune`: the report of a flow that names a root holds for that flow alone.
    let prune = workspace.kink("refined", "prune", &[]);
    assert_status(&prune, 0);
    let document = json_of(&prune);
    assert_eq!(document["scope"]["flow_only"], true, "{document:#}");
    assert_eq!(document["scope"]["corpus_root"], "../../corpus");
    let prune = workspace.kink("refined", "prune", &["--output", "text"]);
    assert_status(&prune, 0);
    assert!(
        text(&prune.stdout).contains(
            "note: the cases are read from the corpus root `../../corpus`, which other flows may \
             name: the report holds for this flow alone, and a case redundant here may be the \
             only discharger of another flow's obligation\n"
        ),
        "{}",
        text(&prune.stdout)
    );

    // Nothing was written under the root.
    assert_eq!(workspace.root_files(), root_files);

    // A case a link leads out of the root, here into the flow's own directory, is refused,
    // naming the root as the flow writes it.
    #[cfg(unix)]
    {
        workspace.write("spec/kink/own.nat", "plus(zero, zero)\n");
        std::os::unix::fs::symlink(
            workspace.path("spec/kink/own.nat"),
            workspace.path("corpus/cases/t5.nat"),
        )
        .unwrap();
        let coverage = workspace.kink("spec", "coverage", &[]);
        let document = json_of(&coverage);
        let refused = document["programs"]
            .as_array()
            .unwrap()
            .iter()
            .find(|row| row["id"] == "cases/t5.nat")
            .unwrap_or_else(|| panic!("{document:#}"));
        assert_eq!(refused["class"], "refused", "{refused:#}");
        assert_eq!(
            refused["cause"],
            "load/load-error: cases/t5.nat escapes the corpus root `../../corpus`",
            "{refused:#}"
        );
    }
}
