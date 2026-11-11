//! `kink-flow prune` (FB54-PRUNE): which programs of a corpus are redundant, read from the
//! obligations `coverage`, `run --full` and `query --full` decide in process.
//!
//! The corpus is calc's language with three pairs of programs: `a1` and `a2` each add, so each is
//! the other's only alternative on what addition discharges; `s1` and `s2` each subtract, and a
//! pattern claims `s1`; `m1` and `m2` each multiply, and a mutation that makes a product count up
//! forever leaves both cells unknown under the work budget, with no other program that kills it.

mod flow_support;

use flow_support::flow;
use kink_flow::{
    FlowManifest, FrontEnd, MutationList,
    cli::{CommandFiles, EXIT_UNASKED, EXIT_YES, FlowCommand},
    dispatch,
    lock::LOCK_FILE,
    results::CACHE_DIRECTORY,
    search::{REPORT_FILE, RunMode, RunOptions, run_with},
};
use serde_json::{Value, json};
use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
};

const MANIFEST: &str = r#"[spec]
entry = "calc.k"
main_module = "CALC"
syntax_module = "CALC-SYNTAX"

[[program]]
id = "a1"
text = "1 + 2"

[[program]]
id = "a2"
text = "3 + 4"

[[program]]
id = "s1"
text = "5 - 1"

[[program]]
id = "s2"
text = "4 - 2"

[[program]]
id = "m1"
text = "2 * 3"

[[program]]
id = "m2"
text = "4 * 5"
"#;

const MUTATIONS: &str = r#"[[mutation]]
id = "add-becomes-sub"
misunderstanding = "addition evaluates as subtraction"
  [[mutation.edit]]
  rule = "add"
  find = "I1 +Int I2"
  replace = "I1 -Int I2"

[[mutation]]
id = "sub-off-by-one"
misunderstanding = "subtraction subtracts one more"
  [[mutation.edit]]
  line = 23
  find = "I1 -Int I2"
  replace = "I1 -Int I2 -Int 1"

[[mutation]]
id = "mul-becomes-add"
misunderstanding = "multiplication evaluates as addition"
  [[mutation.edit]]
  rule = "mul"
  find = "I1 *Int I2"
  replace = "I1 +Int I2"

[[mutation]]
id = "mul-never-ends"
misunderstanding = "multiplication counts its left operand up and never ends"
  [[mutation.edit]]
  rule = "mul"
  find = "=> I1 *Int I2"
  replace = "=> (I1 +Int 1) * I2"
"#;

const PATTERNS: &str = r#"[[pattern]]
id = "sub-four"
pattern = "<k> 4 </k>"
programs = ["s1"]

[[pattern]]
id = "above-two"
pattern = "<k> I:Int </k> requires I >Int 2"
"#;

/// A fresh corpus for one test, under the target's temporary directory.
fn corpus(name: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-prune-{}", std::process::id()))
        .join(name);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    fs::copy(flow("calc").join("calc.k"), dir.join("calc.k")).unwrap();
    fs::write(dir.join("FLOW.toml"), MANIFEST).unwrap();
    fs::write(dir.join("MUTATIONS.toml"), MUTATIONS).unwrap();
    fs::write(dir.join("PATTERNS.toml"), PATTERNS).unwrap();
    dir
}

/// `kink-flow prune` through the library, with the files `files` gives.
fn prune(dir: &Path, files: CommandFiles, options: &[&str]) -> (Value, u8) {
    let options = options.iter().map(|o| (*o).to_owned()).collect::<Vec<_>>();
    let command = FlowCommand::parse("prune", files, &options).unwrap();
    let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
    dispatch(manifest, command, FrontEnd::default()).unwrap()
}

fn every_file(dir: &Path) -> CommandFiles {
    CommandFiles {
        mutations: Some(dir.join("MUTATIONS.toml")),
        patterns: Some(dir.join("PATTERNS.toml")),
        templates: None,
    }
}

fn ids(value: &Value) -> Vec<&str> {
    value
        .as_array()
        .unwrap_or_else(|| panic!("not a list: {value}"))
        .iter()
        .map(|id| id.as_str().unwrap())
        .collect()
}

fn entry<'d>(list: &'d Value, case: &str) -> &'d Value {
    list.as_array()
        .unwrap()
        .iter()
        .find(|entry| entry["case"] == case)
        .unwrap_or_else(|| panic!("no entry for {case}: {list:#}"))
}

fn family<'d>(document: &'d Value, name: &str) -> &'d Value {
    document["families"]
        .as_array()
        .unwrap()
        .iter()
        .find(|family| family["family"] == name)
        .unwrap()
}

/// The report of the whole corpus: `a1`, `a2` and `s2` are redundant alone; `a1` and `a2` are
/// each other's only alternative, so the reverse walk removes `a2` and keeps `a1`; `s1` is kept
/// by its claim, so `s2` is removable; `m1` and `m2` are kept by their unknown cells, though each
/// is the other's alternative on everything else. The command exits 0, writes no lock and stores
/// no run report.
#[test]
fn the_report_keeps_claims_unknowns_and_one_of_two_alternatives() {
    let dir = corpus("report");
    let (document, status) = prune(&dir, every_file(&dir), &[]);
    assert_eq!(status, EXIT_YES, "{document:#}");
    assert_eq!(document["schema"], "kink-flow-prune");
    assert_eq!(document["cases"], 6);
    let redundant = document["redundant"]
        .as_array()
        .unwrap()
        .iter()
        .map(|entry| entry["case"].as_str().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(redundant, ["a1", "a2", "s2"]);
    assert_eq!(document["removable"]["order"], "reverse-manifest");
    assert_eq!(ids(&document["removable"]["cases"]), ["a2", "s2"]);

    // Redundant alone, with the other dischargers of each obligation it discharges.
    let a2 = entry(&document["redundant"], "a2");
    assert_eq!(a2["removable"], true);
    let obligations = a2["obligations"].as_array().unwrap();
    assert!(
        obligations.contains(&json!({"family": "mutations", "id": "add-becomes-sub",
                                     "others": ["a1"]})),
        "{a2:#}"
    );
    assert!(
        obligations.contains(&json!({"family": "patterns", "id": "above-two",
                                     "others": ["a1", "s1", "m1", "m2"]})),
        "{a2:#}"
    );
    // The mutual alternative: once a2 is removed, a1 is the only killer of add-becomes-sub.
    let a1 = entry(&document["redundant"], "a1");
    assert_eq!(a1["removable"], false);
    assert!(
        a1["kept_for"].as_array().unwrap().contains(&json!({
            "reason": "sole-discharger", "family": "mutations", "id": "add-becomes-sub"
        })),
        "{a1:#}"
    );

    // A claimed case is kept, and so is a case whose unknown cell has no other discharger.
    let s1 = entry(&document["kept"], "s1");
    assert!(
        s1["reasons"].as_array().unwrap().contains(&json!({
            "reason": "claimed", "family": "patterns", "id": "sub-four"
        })),
        "{s1:#}"
    );
    for case in ["m1", "m2"] {
        let kept = entry(&document["kept"], case);
        assert_eq!(
            kept["reasons"],
            json!([{"reason": "unknown", "family": "mutations", "id": "mul-never-ends"}]),
            "{kept:#}"
        );
    }
    assert_eq!(document["unanswered"]["cells"], 2);
    assert_eq!(family(&document, "mutations")["unanswered"], 2);
    assert_eq!(family(&document, "patterns")["obligations"], 2);
    assert_eq!(family(&document, "flips")["run"], false);

    // Read-only: no lock, and the run's report is not stored.
    assert!(!dir.join(LOCK_FILE).exists());
    assert!(!dir.join(CACHE_DIRECTORY).join(REPORT_FILE).exists());
}

/// A removable case that the corpus record names as a killer is flagged with the rows its
/// removal moves; the record and the stored run report are left as they were. The record here is
/// one whose killer of `add-becomes-sub` is `a2`, as a record written while `a2` was the first
/// adding program would be.
#[test]
fn a_removable_recorded_killer_is_flagged() {
    let dir = corpus("lock");
    let lock = dir.join(LOCK_FILE);
    let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
    let list = MutationList::read(&dir.join("MUTATIONS.toml")).unwrap();
    let (_, ok) = run_with(
        &manifest,
        &list,
        &RunOptions {
            lock: Some(lock.clone()),
            compile_workers: Some(1),
            ..RunOptions::default()
        },
        RunMode::Search,
    );
    assert!(ok);
    let recorded = fs::read_to_string(&lock).unwrap();
    assert!(recorded.contains("killer = \"a1\""), "{recorded}");
    fs::write(
        &lock,
        recorded.replace("killer = \"a1\"", "killer = \"a2\""),
    )
    .unwrap();
    let before = fs::read(&lock).unwrap();
    let report = dir.join(CACHE_DIRECTORY).join(REPORT_FILE);
    let stored = fs::read(&report).unwrap();
    let (document, status) = prune(&dir, every_file(&dir), &["--lock", lock.to_str().unwrap()]);
    assert_eq!(status, EXIT_YES, "{document:#}");
    assert_eq!(ids(&document["removable"]["cases"]), ["a2", "s2"]);
    assert_eq!(
        document["removable"]["lock"],
        json!([{"case": "a2", "rows": {"run": ["add-becomes-sub"]}}])
    );
    assert_eq!(
        entry(&document["redundant"], "a2")["lock"],
        json!({"run": ["add-becomes-sub"]})
    );
    assert_eq!(entry(&document["redundant"], "s2")["lock"], Value::Null);
    assert_eq!(document["lock"]["sections"], json!(["run"]));
    assert_eq!(fs::read(&lock).unwrap(), before);
    assert_eq!(fs::read(&report).unwrap(), stored);
}

/// A family whose input is absent is skipped, and the document says so: with no pattern list
/// (none named, none declared) the pattern family, and with no mutation list (a front end's
/// layout with none) the mutation family. Without the patterns nothing claims `s1`, so it is
/// redundant alone; without the mutations nothing is unknown, so `m1` and `m2` are each other's
/// alternative.
#[test]
fn a_missing_family_is_skipped() {
    let dir = corpus("skipped");
    let (document, status) = prune(
        &dir,
        CommandFiles {
            mutations: Some(dir.join("MUTATIONS.toml")),
            ..CommandFiles::default()
        },
        &[],
    );
    assert_eq!(status, EXIT_YES, "{document:#}");
    let patterns = family(&document, "patterns");
    assert_eq!(patterns["run"], false);
    assert_eq!(patterns["reason"], "no-patterns");
    assert!(entry(&document["redundant"], "s1")["obligations"].is_array());
    assert_eq!(ids(&document["removable"]["cases"]), ["a2", "s2"]);

    let (document, status) = prune(&dir, CommandFiles::default(), &[]);
    assert_eq!(status, EXIT_YES, "{document:#}");
    let mutations = family(&document, "mutations");
    assert_eq!(mutations["run"], false);
    assert_eq!(mutations["reason"], "no-mutation-list");
    assert_eq!(document["unanswered"]["cells"], 0);
    assert_eq!(ids(&document["removable"]["cases"]), ["a2", "s2", "m2"]);
    assert_eq!(document["kept"], json!([]));
}

/// The command line: the verb's operands, its text rendering and its exit statuses (0 for a
/// computed report, 2 for an input that does not decode or a missing operand; never 1).
#[test]
fn the_command_line_prints_the_report_and_refuses_bad_input() {
    let dir = corpus("command-line");
    let binary = env!("CARGO_BIN_EXE_kink-flow");
    let output = Command::new(binary)
        .current_dir(&dir)
        .args([
            "prune",
            "FLOW.toml",
            "MUTATIONS.toml",
            "PATTERNS.toml",
            "--output",
            "text",
        ])
        .output()
        .unwrap();
    let text = String::from_utf8(output.stdout).unwrap();
    assert_eq!(output.status.code(), Some(0), "{text}");
    assert!(
        text.starts_with(
            "6 cases: 3 redundant alone, 2 removable together (in reverse-manifest order): a2, s2\n"
        ),
        "{text}"
    );
    assert!(
        text.contains("  s1: claimed by the pattern sub-four; "),
        "{text}"
    );
    assert!(
        text.contains(
            "  m1: its cell is unknown on mutations mul-never-ends, which no other case \
             discharges\n"
        ),
        "{text}"
    );
    assert!(text.contains("unanswered cells: 2;"), "{text}");

    fs::write(dir.join("BAD.toml"), "[[mutation]]\nid = 3\n").unwrap();
    let output = Command::new(binary)
        .current_dir(&dir)
        .args(["prune", "FLOW.toml", "BAD.toml"])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(i32::from(EXIT_UNASKED)));
    let document: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(document["refused"]["family"], "mutations", "{document:#}");

    let output = Command::new(binary)
        .current_dir(&dir)
        .args(["prune", "FLOW.toml"])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(i32::from(EXIT_UNASKED)));
}
