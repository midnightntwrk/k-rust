//! `kink-flow prune` (FB54-PRUNE): which programs of a corpus are redundant, read from the
//! obligations `coverage`, the kill search and the pattern walk decide in process; a cell of the
//! kill and pattern matrices is asked only where a decision needs it, with the decisions `run
//! --full` and `query --full` give (FB56, `--full`).
//!
//! The corpus is calc's language with three pairs of programs: `a1` and `a2` each add, so each is
//! the other's only alternative on what addition discharges; `s1` and `s2` each subtract, and a
//! pattern claims `s1`; `m1` and `m2` each multiply, and a mutation that makes a product count up
//! forever leaves both cells unknown under the work budget, with no other program that kills it.
//! A unique-cause requirement (`[coverage] mcdc`, the mcdc fixture's definition) is discharged
//! by a pair of programs together, so each side of its only pair is kept.

mod flow_support;

use flow_support::flow;
use kink_flow::{
    FlowManifest, FrontEnd, MutationList,
    cli::{CommandFiles, EXIT_UNASKED, EXIT_YES, FlowCommand},
    dispatch,
    lock::LOCK_FILE,
    prune::CorpusLists,
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
    corpus_of(name, MANIFEST, PATTERNS)
}

/// A fresh corpus of `manifest` and `patterns` with the calc definition and mutations.
fn corpus_of(name: &str, manifest: &str, patterns: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-prune-{}", std::process::id()))
        .join(name);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    fs::copy(flow("calc").join("calc.k"), dir.join("calc.k")).unwrap();
    fs::write(dir.join("FLOW.toml"), manifest).unwrap();
    fs::write(dir.join("MUTATIONS.toml"), MUTATIONS).unwrap();
    fs::write(dir.join("PATTERNS.toml"), patterns).unwrap();
    dir
}

/// `kink-flow prune` through the library, with the files `files` gives.
fn prune(dir: &Path, files: CommandFiles, options: &[&str]) -> (Value, u8) {
    prune_with(dir, files, options, None)
}

/// [`prune`], with what a front end states of the corpus's own lists.
fn prune_with(
    dir: &Path,
    files: CommandFiles,
    options: &[&str],
    lists: Option<CorpusLists>,
) -> (Value, u8) {
    let options = options.iter().map(|o| (*o).to_owned()).collect::<Vec<_>>();
    let mut command = FlowCommand::parse("prune", files, &options).unwrap();
    if let Some(lists) = lists {
        command.set_corpus_lists(lists);
    }
    let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
    dispatch(manifest, command, FrontEnd::default()).unwrap()
}

/// What a prune document decides, without its evidence: each case redundant alone with whether
/// the removable set removes it and what kept it there, the removable set, and each kept case
/// with its reasons. A lazy report and a `--full` one decide the same.
fn decisions(document: &Value) -> Value {
    json!({
        "redundant": document["redundant"]
            .as_array()
            .unwrap_or_else(|| panic!("no report: {document:#}"))
            .iter()
            .map(|entry| json!({
                "case": entry["case"],
                "removable": entry["removable"],
                "kept_for": entry["kept_for"],
            }))
            .collect::<Vec<_>>(),
        "removable": document["removable"]["cases"],
        "kept": document["kept"],
    })
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
///
/// Lazily (no `--full`, on a fresh cache), the decisions are the full report's, and it asks
/// fewer cells: each killer and hitter the searches found is judged alone by a second-killer
/// (second-hitter) search, and the walk asks again only where the known second one is removed.
#[test]
fn the_report_keeps_claims_unknowns_and_one_of_two_alternatives() {
    let dir = corpus("report");
    let (lazy, status) = prune(&dir, every_file(&dir), &[]);
    assert_eq!(status, EXIT_YES, "{lazy:#}");
    assert_eq!(lazy["mode"], "lazy");
    let (document, status) = prune(&dir, every_file(&dir), &["--full"]);
    assert_eq!(status, EXIT_YES, "{document:#}");
    assert_eq!(document["mode"], "full");
    assert_eq!(decisions(&lazy), decisions(&document));
    // The full matrix is 4 mutations of 6 comparable cases. The lazy report held the 9 cells of
    // the first-kill search and asked 6 more, all live: the second killer of each of the three
    // killers (a2, s2, m2), and, once the walk removed a2, the 3 kept cases' cells of
    // add-becomes-sub that show a1 is its only killer left. Of the 12 pattern cells it held 4
    // and asked 5.
    let cells = &lazy["accounting"]["cells"];
    assert_eq!(
        cells["mutations"],
        json!({"matrix": 24, "searched": 9, "asked": 6, "from_cache": 0}),
        "{cells:#}"
    );
    assert_eq!(
        cells["patterns"],
        json!({"matrix": 12, "searched": 4, "asked": 5, "from_cache": 0}),
        "{cells:#}"
    );
    assert_eq!(family(&lazy, "mutations")["complete"], false);
    assert_eq!(lazy["unanswered"]["complete"], false);
    assert!(
        lazy["limits"]
            .as_array()
            .unwrap()
            .iter()
            .any(|limit| limit["limit"] == "lazy")
    );
    // The full report holds every cell, the 15 the lazy one asked from the outcome cache.
    let full_cells = &document["accounting"]["cells"]["mutations"];
    assert_eq!(full_cells["searched"], 24, "{full_cells:#}");
    assert_eq!(full_cells["asked"], 0, "{full_cells:#}");
    assert_eq!(
        document["accounting"]["mutations"]["outcome_cache"]["programs_from_cache"],
        15
    );
    assert_eq!(document["unanswered"]["complete"], true);
    assert_eq!(document["schema"], "kink-flow-prune");
    assert_eq!(document["version"], 3);
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
                                     "others": ["a1"], "complete": true})),
        "{a2:#}"
    );
    assert!(
        obligations.contains(&json!({"family": "patterns", "id": "above-two",
                                     "others": ["a1", "s1", "m1", "m2"], "complete": true})),
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
    // The lazy search tried the recorded killer a2 first; the full report decides the same.
    let (full, status) = prune(
        &dir,
        every_file(&dir),
        &["--full", "--lock", lock.to_str().unwrap()],
    );
    assert_eq!(status, EXIT_YES, "{full:#}");
    assert_eq!(decisions(&full), decisions(&document));
    assert_eq!(full["removable"]["lock"], document["removable"]["lock"]);
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
    let files = || CommandFiles {
        mutations: Some(dir.join("MUTATIONS.toml")),
        ..CommandFiles::default()
    };
    let (full, _) = prune(&dir, files(), &["--full"]);
    assert_eq!(decisions(&full), decisions(&document));

    let (document, status) = prune(&dir, CommandFiles::default(), &[]);
    assert_eq!(status, EXIT_YES, "{document:#}");
    let mutations = family(&document, "mutations");
    assert_eq!(mutations["run"], false);
    assert_eq!(mutations["reason"], "no-mutation-list");
    assert_eq!(document["unanswered"]["cells"], 0);
    assert_eq!(ids(&document["removable"]["cases"]), ["a2", "s2", "m2"]);
    assert_eq!(document["kept"], json!([]));
    let (full, _) = prune(&dir, CommandFiles::default(), &["--full"]);
    assert_eq!(decisions(&full), decisions(&document));
}

/// A second killer the walk had removed is searched past: `a3` adds too and a pattern claims it.
/// Judging `a1` (the first-kill search's killer of `add-becomes-sub`) alone finds `a2`, the next
/// adding program; the walk removes `a2` (`a1` still kills), and at `a1` the one known killer
/// kept is `a1` itself, so the walk asks on and finds `a3`, which it never asked before: `a1` is
/// removable. The full report decides the same.
#[test]
fn the_walk_searches_past_a_removed_second_killer() {
    const MANIFEST3: &str = r#"[spec]
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
id = "a3"
text = "2 + 2"

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
    let patterns = format!(
        "{PATTERNS}\n[[pattern]]\nid = \"two-plus-two\"\npattern = \"<k> 4 </k>\"\n\
         programs = [\"a3\"]\n"
    );
    let dir = corpus_of("removed-second", MANIFEST3, &patterns);
    let (lazy, status) = prune(&dir, every_file(&dir), &[]);
    assert_eq!(status, EXIT_YES, "{lazy:#}");
    assert_eq!(
        ids(&lazy["removable"]["cases"]),
        ["a1", "a2", "s2"],
        "{lazy:#}"
    );
    let a1 = entry(&lazy["redundant"], "a1");
    assert_eq!(a1["removable"], true);
    assert!(
        a1["obligations"].as_array().unwrap().contains(&json!({
            "family": "mutations", "id": "add-becomes-sub", "others": ["a2", "a3"],
            "complete": false
        })),
        "{a1:#}"
    );
    let (full, status) = prune(&dir, every_file(&dir), &["--full"]);
    assert_eq!(status, EXIT_YES, "{full:#}");
    assert_eq!(decisions(&lazy), decisions(&full));
    let lazy_cells = &lazy["accounting"]["cells"]["mutations"];
    assert_eq!(lazy_cells["matrix"], 28, "{lazy_cells:#}");
    assert!(
        lazy_cells["searched"].as_u64().unwrap() + lazy_cells["asked"].as_u64().unwrap() < 28,
        "{lazy_cells:#}"
    );
}

/// A second lazy report asks the same cells as the first, each from the outcome cache: no
/// mutant runs and no record is written.
#[test]
fn a_second_lazy_report_runs_no_mutant() {
    let dir = corpus("again");
    let (first, status) = prune(&dir, every_file(&dir), &[]);
    assert_eq!(status, EXIT_YES, "{first:#}");
    let (second, status) = prune(&dir, every_file(&dir), &[]);
    assert_eq!(status, EXIT_YES, "{second:#}");
    assert_eq!(decisions(&first), decisions(&second));
    let cells = &second["accounting"]["cells"]["mutations"];
    assert_eq!(
        cells["asked"],
        first["accounting"]["cells"]["mutations"]["asked"]
    );
    assert_eq!(cells["from_cache"], cells["asked"], "{cells:#}");
    assert_eq!(
        second["accounting"]["mutations"]["outcome_cache"]["records_written"], 0,
        "{:#}",
        second["accounting"]
    );
}

/// Each list-reading family names its list and whether it is the corpus's own: unknown (null)
/// for kink-flow's own command line, which has no corpus layout, and as a front end states it
/// otherwise; `--output text` notes a list that is not the corpus's own.
#[test]
fn the_report_names_its_lists_and_whether_they_are_the_corpus_own() {
    let dir = corpus("lists");
    let (document, status) = prune(&dir, every_file(&dir), &[]);
    assert_eq!(status, EXIT_YES, "{document:#}");
    let mutations = family(&document, "mutations");
    assert_eq!(
        mutations["list"],
        json!({"path": dir.join("MUTATIONS.toml").display().to_string(), "corpus_own": null})
    );
    assert_eq!(
        family(&document, "patterns")["list"]["corpus_own"],
        Value::Null
    );
    assert!(family(&document, "rules").get("list").is_none());

    let lists = CorpusLists {
        mutations: false,
        patterns: true,
    };
    let (document, status) = prune_with(&dir, every_file(&dir), &[], Some(lists));
    assert_eq!(status, EXIT_YES, "{document:#}");
    assert_eq!(family(&document, "mutations")["list"]["corpus_own"], false);
    assert_eq!(family(&document, "patterns")["list"]["corpus_own"], true);
    let text = kink_flow::prune::text_rendering(&document).unwrap();
    assert!(
        text.contains(&format!(
            "note: the mutations family read `{}`, not the corpus's own list: the report holds \
             for that list, not for the corpus\n",
            dir.join("MUTATIONS.toml").display()
        )),
        "{text}"
    );
    assert!(!text.contains("note: the patterns family"), "{text}");
}

/// A flow that names its corpus root reads cases other flows may read, so its report says that
/// it holds for this flow alone, in the document (`scope`) and in one line of the text; its
/// decisions are those of the same flow with the cases in its own directory, whose document has
/// no `scope` and whose text has no such line.
#[test]
fn a_flow_that_names_its_corpus_root_says_its_report_holds_for_this_flow_alone() {
    let own = corpus("scope-own");
    let (own_document, status) = prune(&own, every_file(&own), &[]);
    assert_eq!(status, EXIT_YES, "{own_document:#}");
    assert!(own_document.get("scope").is_none(), "{own_document:#}");
    let own_text = kink_flow::prune::text_rendering(&own_document).unwrap();
    assert!(!own_text.contains("this flow alone"), "{own_text}");

    let manifest = MANIFEST.replacen(
        "\n[[program]]",
        "\n[corpus]\nroot = \".\"\n\n[[program]]",
        1,
    );
    assert_ne!(manifest, MANIFEST);
    let dir = corpus_of("scope-root", &manifest, PATTERNS);
    let (document, status) = prune(&dir, every_file(&dir), &[]);
    assert_eq!(status, EXIT_YES, "{document:#}");
    let detail = "the cases are read from the corpus root `.`, which other flows may name: the \
                  report holds for this flow alone, and a case redundant here may be the only \
                  discharger of another flow's obligation";
    assert_eq!(
        document["scope"],
        json!({"flow_only": true, "corpus_root": ".", "detail": detail})
    );
    assert_eq!(decisions(&document), decisions(&own_document));
    let text = kink_flow::prune::text_rendering(&document).unwrap();
    let lines = text.lines().collect::<Vec<_>>();
    assert_eq!(lines[1], format!("note: {detail}"), "{text}");
    assert_eq!(
        text.replace(&format!("note: {detail}\n"), ""),
        own_text.replace("scope-own", "scope-root"),
        "{text}"
    );
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
    assert!(
        text.contains(
            "cells (lazy, as each decision needs them; --full asks every one): mutations 9 held \
             by the search and 6 asked after it, of 24; patterns 4 held by the search and 5 \
             asked after it, of 12\n"
        ),
        "{text}"
    );
    assert!(
        text.contains("  a2: mutations add-becomes-sub (also a1, of the cases asked); "),
        "{text}"
    );

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

/// A corpus of the mcdc fixture's definition with `[coverage] mcdc` selecting `both` (A
/// andThenBool B) and the programs `programs` (each `(id, text)`).
fn mcdc_corpus(name: &str, programs: &[(&str, &str)]) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-prune-{}", std::process::id()))
        .join(name);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    fs::copy(flow("mcdc").join("mcdc.k"), dir.join("mcdc.k")).unwrap();
    let mut manifest = "[coverage]\nmcdc = [\"MCDC.both\"]\n\n[spec]\nentry = \"mcdc.k\"\n\
                        main_module = \"MCDC\"\nsyntax_module = \"MCDC-SYNTAX\"\n"
        .to_owned();
    for (id, text) in programs {
        manifest.push_str(&format!(
            "\n[[program]]\nid = \"{id}\"\ntext = \"{text}\"\n"
        ));
    }
    fs::write(dir.join("FLOW.toml"), manifest).unwrap();
    dir
}

const BOTH_A: &str = "requirement:MCDC.both:A:Bool:mcdc";

/// FB54-PRUNE, PRUNE-MCDC-PAIR: A of `both` has one unique-cause pair, `x`'s (true, true),
/// where the condition holds, with `y`'s (false, true), where it is refuted; no other program
/// gives either. Its covering list names both, but neither discharges it alone, so both are
/// kept as its sole dischargers, though every other obligation `y` discharges has another
/// discharger (`z`'s (true, false) and `w`'s (false, false) are refuted too, and `w` has A
/// false). With `y2` also giving (false, true), `y` and `y2` are each redundant alone, each
/// naming the pair that holds without it, and the walk removes `y2` and keeps `y`. Lazily and
/// with `--full` the decisions are the same.
#[test]
fn each_side_of_a_unique_cause_pair_is_kept() {
    let programs = [
        ("x", "both(true, true)"),
        ("y", "both(false, true)"),
        ("z", "both(true, false)"),
        ("w", "both(false, false)"),
    ];
    let sole = json!({"reason": "sole-discharger", "family": "requirements", "id": BOTH_A});
    let dir = mcdc_corpus("mcdc-pair", &programs);
    let (lazy, status) = prune(&dir, CommandFiles::default(), &[]);
    assert_eq!(status, EXIT_YES, "{lazy:#}");
    let (full, status) = prune(&dir, CommandFiles::default(), &["--full"]);
    assert_eq!(status, EXIT_YES, "{full:#}");
    assert_eq!(decisions(&lazy), decisions(&full));
    for case in ["x", "y"] {
        let kept = entry(&full["kept"], case);
        assert!(
            kept["reasons"].as_array().unwrap().contains(&sole),
            "{kept:#}"
        );
    }
    assert_eq!(
        entry(&full["kept"], "y")["reasons"],
        json!([sole]),
        "{full:#}"
    );
    assert_eq!(ids(&full["removable"]["cases"]), ["w"], "{full:#}");

    let dir = mcdc_corpus(
        "mcdc-pair-side",
        &[
            programs.as_slice(),
            &[("y2", "both(false, true) ; both(false, true)")],
        ]
        .concat(),
    );
    let (lazy, status) = prune(&dir, CommandFiles::default(), &[]);
    assert_eq!(status, EXIT_YES, "{lazy:#}");
    let (full, status) = prune(&dir, CommandFiles::default(), &["--full"]);
    assert_eq!(status, EXIT_YES, "{full:#}");
    assert_eq!(decisions(&lazy), decisions(&full));
    assert_eq!(ids(&full["removable"]["cases"]), ["w", "y2"], "{full:#}");
    let y = entry(&full["redundant"], "y");
    assert_eq!(y["removable"], false, "{y:#}");
    // Once the walk removed `w` and `y2`, `y` is also A's only reached-false case.
    assert!(y["kept_for"].as_array().unwrap().contains(&sole), "{y:#}");
    let pair = |refuted: &str| {
        json!({"family": "requirements", "id": BOTH_A,
               "pairs": [{"held": ["x"], "refuted": [refuted]}], "complete": true})
    };
    assert!(
        y["obligations"].as_array().unwrap().contains(&pair("y2")),
        "{y:#}"
    );
    let y2 = entry(&full["redundant"], "y2");
    assert!(
        y2["obligations"].as_array().unwrap().contains(&pair("y")),
        "{y2:#}"
    );
    let text = kink_flow::prune::text_rendering(&full).unwrap();
    assert!(
        text.contains(&format!(
            "requirements {BOTH_A} (also the pair held by x and refuted by y2)"
        )),
        "{text}"
    );
}
