//! The survivor report and `kink-flow report` (flow F-06 deliverables 1 and 3), and the root
//! README's "Using kink-flow" walkthrough, followed literally.
//!
//! The report adds fields to the run document and decides nothing: every status here is the
//! kill search's (pinned by tests/search.rs); these tests pin what a survivor's row says.

use kink_flow::{
    FlowManifest, MutationList,
    cli::{EXIT_CORPUS, EXIT_OK, EXIT_USAGE},
    report::{MISSING_SCHEMA, RUN_SCHEMA, RUN_VERSION},
    results::CACHE_DIRECTORY,
    search::{ProgramOrder, REPORT_FILE, RunOptions, run},
};
use serde_json::{Value, json};
use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
};

fn flow(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../testdata/flow")
        .join(name)
}

/// A fresh directory for one test, under the target's temporary directory.
fn scratch(name: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-report-{}", std::process::id()))
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
            // F-05's corpus order, so that the pinned calls and killers do not depend on host
            // timing (F-13's cost order: tests/usability.rs).
            order: ProgramOrder::Corpus,
        },
    )
}

fn mutation<'d>(document: &'d Value, id: &str) -> &'d Value {
    document["mutations"]
        .as_array()
        .unwrap()
        .iter()
        .find(|m| m["id"] == id)
        .unwrap_or_else(|| panic!("no mutation {id}"))
}

/// `(program, outcome, cause)` of every program the mutant ran on, in the runner's order.
fn executed(document: &Value, id: &str) -> Vec<(String, String, Value)> {
    mutation(document, id)["executed"]
        .as_array()
        .unwrap()
        .iter()
        .map(|e| {
            (
                e["program"].as_str().unwrap().to_owned(),
                e["outcome"].as_str().unwrap().to_owned(),
                e["cause"].clone(),
            )
        })
        .collect()
}

fn triples(items: &[(&str, &str, Value)]) -> Vec<(String, String, Value)> {
    items
        .iter()
        .map(|(a, b, c)| ((*a).to_owned(), (*b).to_owned(), c.clone()))
        .collect()
}

fn binary(args: &[&str], dir: &Path) -> Output {
    Command::new(env!("CARGO_BIN_EXE_kink-flow"))
        .args(args)
        .current_dir(dir)
        .output()
        .unwrap()
}

/// `excerpt` is contained in `actual`: every key of an excerpt object is in the actual object
/// with a contained value; arrays have the same length and contained elements; scalars are
/// equal.
fn contains(actual: &Value, excerpt: &Value) -> bool {
    match (actual, excerpt) {
        (Value::Object(actual), Value::Object(excerpt)) => excerpt
            .iter()
            .all(|(key, value)| actual.get(key).is_some_and(|a| contains(a, value))),
        (Value::Array(actual), Value::Array(excerpt)) => {
            actual.len() == excerpt.len() && actual.iter().zip(excerpt).all(|(a, e)| contains(a, e))
        }
        _ => actual == excerpt,
    }
}

#[test]
fn a_survivor_row_carries_its_rule_texts_reaching_programs_and_outcomes() {
    let manifest = fixture("calc", "survivor").join("FLOW.toml");
    let (document, ok) = search(&manifest, &manifest.with_file_name("MUTATIONS.toml"), &[]);
    assert!(ok, "{document:#}");
    assert_eq!(document["schema"], RUN_SCHEMA);
    assert_eq!(document["version"], RUN_VERSION);
    assert_eq!(document["survivors"], json!(["add-swaps-operands"]));
    assert_eq!(document["unusable_programs"], json!([]));
    let survivor = mutation(&document, "add-swaps-operands");
    assert_eq!(survivor["status"], "survived");
    // The two edits of the mutation address one rule; its text before and after is sliced
    // from the sources by the sentence's span.
    assert_eq!(
        survivor["rules"],
        json!([{
            "module": "CALC",
            "index": 1,
            "file": "calc.k",
            "label": "CALC.add",
            "start_line": 21,
            "end_line": 21,
            "edits": [0, 1],
            "before": "rule [add]: I1:Int + I2:Int => I1 +Int I2",
            "after": "rule [add]: I1:Int + I2:Int => I2 +Int I1",
        }])
    );
    assert_eq!(survivor["reaching"], json!(["add", "nested", "inline"]));
    assert_eq!(
        executed(&document, "add-swaps-operands"),
        triples(&[
            ("add", "agree", Value::Null),
            ("nested", "agree", Value::Null),
            ("inline", "agree", Value::Null),
            ("sub", "agree", Value::Null),
        ])
    );
    assert!(
        survivor["action"]
            .as_str()
            .unwrap()
            .starts_with("write a program that reaches an edited rule")
    );
    // A killed row names its killer and carries no survivor fields.
    for id in [
        "add-becomes-sub",
        "sub-off-by-one",
        "mul-becomes-add",
        "no-mul",
    ] {
        let row = mutation(&document, id);
        assert_eq!(row["status"], "killed", "{id}");
        assert_eq!(row["rules"], Value::Null, "{id}");
        assert_eq!(row["action"], Value::Null, "{id}");
        assert!(row["killer"].is_string(), "{id}");
    }

    // A deleted rule has no text after the edit; with only `add` in the corpus, nothing
    // reaches the mul rule, so nothing can kill its deletion.
    let text = fs::read_to_string(&manifest).unwrap();
    let only_add = text[..text.find("[[program]]\nid = \"nested\"").unwrap()].to_owned();
    let manifest = manifest.with_file_name("FLOW-add.toml");
    fs::write(&manifest, only_add).unwrap();
    let (document, ok) = search(
        &manifest,
        &manifest.with_file_name("MUTATIONS.toml"),
        &["no-mul"],
    );
    assert!(ok, "{document:#}");
    assert_eq!(document["survivors"], json!(["no-mul"]));
    let row = mutation(&document, "no-mul");
    assert_eq!(row["status"], "survived");
    assert_eq!(row["reaching"], json!([]));
    assert_eq!(
        row["rules"],
        json!([{
            "module": "CALC",
            "index": 2,
            "file": "calc.k",
            "label": "CALC.mul",
            "start_line": 22,
            "end_line": 22,
            "edits": [0],
            "before": "rule [mul]: I1:Int * I2:Int => I1 *Int I2",
            "after": null,
        }])
    );
    assert_eq!(
        executed(&document, "no-mul"),
        triples(&[("add", "agree", Value::Null)])
    );
}

#[test]
fn rows_of_the_other_statuses_say_what_to_fix() {
    let manifest = fixture("calc", "statuses").join("FLOW.toml");
    let (document, ok) = search(
        &manifest,
        &manifest.with_file_name("MUTATIONS-statuses.toml"),
        &["no-such-rule", "add-in-a-group", "add-unbound"],
    );
    assert!(ok, "{document:#}");
    // Neither an equivalent nor an invalid mutant is a survivor: no program can kill it.
    assert_eq!(document["survivors"], json!([]));
    let row = mutation(&document, "no-such-rule");
    assert_eq!(row["status"], "invalid-mutation");
    assert_eq!(row["rules"], Value::Null);
    assert!(
        row["action"]
            .as_str()
            .unwrap()
            .starts_with("fix the mutation")
    );
    for (id, status, action) in [
        ("add-in-a-group", "equivalent", "nothing can kill it"),
        ("add-unbound", "invalid", "fix the mutation"),
    ] {
        let row = mutation(&document, id);
        assert_eq!(row["status"], status, "{id}");
        assert_eq!(row["rules"][0]["label"], "CALC.add", "{id}");
        assert_eq!(
            row["rules"][0]["before"], "rule [add]: I1:Int + I2:Int => I1 +Int I2",
            "{id}"
        );
        assert!(
            row["action"].as_str().unwrap().starts_with(action),
            "{id}: {}",
            row["action"]
        );
    }
}

#[test]
fn a_run_where_every_mutation_is_killed_lists_no_survivors() {
    let manifest = fixture("register", "all-killed").join("FLOW.toml");
    let (document, ok) = search(&manifest, &manifest.with_file_name("MUTATIONS.toml"), &[]);
    assert!(ok, "{document:#}");
    assert_eq!(document["survivors"], json!([]));
    assert_eq!(document["counts"]["killed"], 4);
    for row in document["mutations"].as_array().unwrap() {
        assert_eq!(row["status"], "killed", "{row:#}");
        assert_eq!(row["rules"], Value::Null, "{row:#}");
        assert_eq!(row["action"], Value::Null, "{row:#}");
    }
}

#[test]
fn timeouts_unknowns_and_unusable_programs_carry_their_causes() {
    // countdown(3) never ends on the mutant: under a 500 ms bound and a depth bound it cannot
    // reach, its outcome is a timeout; twice agrees.
    let dir = fixture("loop", "causes");
    let mutations = dir.join("MUTATIONS.toml");
    let (document, ok) = search(&dir.join("FLOW-search.toml"), &mutations, &[]);
    assert!(ok, "{document:#}");
    assert_eq!(document["survivors"], json!(["countdown-escapes"]));
    assert_eq!(
        mutation(&document, "countdown-escapes")["status"],
        "timeout"
    );
    // F-13: a timeout's cause continues with the leaf census of the mutant's run
    // (host-dependent; tests/usability.rs pins its form).
    let mut entries = executed(&document, "countdown-escapes");
    let cause = entries[0].2.as_str().unwrap().to_owned();
    assert!(
        cause.starts_with(
            "the mutant's run did not end within time_ms = 500; when the bound fired "
        ),
        "{cause}"
    );
    entries[0].2 = json!("the mutant's run did not end within time_ms = 500");
    assert_eq!(
        entries,
        triples(&[
            (
                "countdown",
                "timeout",
                json!("the mutant's run did not end within time_ms = 500")
            ),
            ("twice", "agree", Value::Null),
        ])
    );
    assert!(
        mutation(&document, "countdown-escapes")["action"]
            .as_str()
            .unwrap()
            .starts_with("write a program that ends under the mutant")
    );

    // Under a depth bound of 200 and a generous time bound the same run stops at the depth
    // bound: both oracle slots are unknown, for one cause.
    fs::remove_dir_all(dir.join(CACHE_DIRECTORY)).unwrap();
    let (document, ok) = search(&dir.join("FLOW-depth.toml"), &mutations, &[]);
    assert!(ok, "{document:#}");
    assert_eq!(document["survivors"], json!(["countdown-escapes"]));
    assert_eq!(
        mutation(&document, "countdown-escapes")["status"],
        "unknown"
    );
    let executed = executed(&document, "countdown-escapes");
    assert_eq!(executed.len(), 2);
    assert_eq!(executed[0].1, "unknown");
    assert!(
        executed[0].2.as_str().unwrap().starts_with(
            "exit-stop, whole-term: the mutant's run did not end in a value kink can compare \
             (a path stopped at max_depth = 200"
        ),
        "{}",
        executed[0].2
    );
    assert_eq!(executed[1], ("twice".into(), "agree".into(), Value::Null));

    // A program that cannot kill is listed once, with its class and cause, and never run.
    fs::remove_dir_all(dir.join(CACHE_DIRECTORY)).unwrap();
    let (document, ok) = search(&dir.join("FLOW-timeout.toml"), &mutations, &[]);
    assert!(ok, "{document:#}");
    let mut unusable = document["unusable_programs"].clone();
    let cause = unusable[0]["cause"].as_str().unwrap().to_owned();
    assert!(
        cause.starts_with("the run did not finish within time_ms = 500; when the bound fired "),
        "{cause}"
    );
    unusable[0]["cause"] = json!("the run did not finish within time_ms = 500");
    assert_eq!(
        unusable,
        json!([{"id": "spin", "class": "timeout",
                "cause": "the run did not finish within time_ms = 500"}])
    );
    assert_eq!(
        mutation(&document, "countdown-escapes")["calls"],
        json!([{"programs": ["countdown"], "status": "timeout"}])
    );
}

#[test]
fn report_reprints_the_same_bytes() {
    let dir = fixture("calc", "reprint");
    let cache = dir.join(CACHE_DIRECTORY);
    // No run yet: nothing to print.
    let output = binary(&["report", "FLOW.toml"], &dir);
    assert_eq!(output.status.code(), Some(i32::from(EXIT_CORPUS)));
    let document: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(document["schema"], MISSING_SCHEMA);
    assert_eq!(document["outcome"], "missing");

    let ran = binary(
        &[
            "run",
            "FLOW.toml",
            "MUTATIONS.toml",
            "--only",
            "add-swaps-operands",
        ],
        &dir,
    );
    assert_eq!(ran.status.code(), Some(i32::from(EXIT_OK)));
    let reported = binary(&["report", "FLOW.toml"], &dir);
    assert_eq!(reported.status.code(), Some(i32::from(EXIT_OK)));
    assert_eq!(reported.stdout, ran.stdout);
    let document: Value = serde_json::from_slice(&ran.stdout).unwrap();
    let stored: Value =
        serde_json::from_str(&fs::read_to_string(cache.join(REPORT_FILE)).unwrap()).unwrap();
    assert_eq!(stored, document);
    assert_eq!(document["survivors"], json!(["add-swaps-operands"]));

    // The report is the last run's: a run that selects no mutation replaces it too.
    fs::write(dir.join("EMPTY.toml"), "").unwrap();
    let empty = binary(&["run", "FLOW.toml", "EMPTY.toml"], &dir);
    assert_eq!(empty.status.code(), Some(i32::from(EXIT_OK)));
    let reported = binary(&["report", "FLOW.toml"], &dir);
    assert_eq!(reported.stdout, empty.stdout);
    let document: Value = serde_json::from_slice(&empty.stdout).unwrap();
    assert_eq!(document["mutations"], json!([]));

    // --cache selects another cache; a stored report that is not a current run document is
    // refused, not printed.
    let other = scratch("reprint-cache");
    let output = binary(
        &["report", "FLOW.toml", "--cache", other.to_str().unwrap()],
        &dir,
    );
    assert_eq!(output.status.code(), Some(i32::from(EXIT_CORPUS)));
    fs::write(
        other.join(REPORT_FILE),
        r#"{"schema": "kink-flow-run", "version": 1}"#,
    )
    .unwrap();
    let output = binary(
        &["report", "FLOW.toml", "--cache", other.to_str().unwrap()],
        &dir,
    );
    assert_eq!(output.status.code(), Some(i32::from(EXIT_CORPUS)));
    let document: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(document["outcome"], "unreadable");
    fs::write(other.join(REPORT_FILE), "not json").unwrap();
    let output = binary(
        &["report", "FLOW.toml", "--cache", other.to_str().unwrap()],
        &dir,
    );
    assert_eq!(output.status.code(), Some(i32::from(EXIT_CORPUS)));
    for args in [
        vec!["report"],
        vec!["report", "missing.toml"],
        vec!["report", "FLOW.toml", "--cache"],
        vec!["report", "FLOW.toml", "--verify"],
    ] {
        let output = binary(&args, &dir);
        assert_eq!(
            output.status.code(),
            Some(i32::from(EXIT_USAGE)),
            "{args:?}"
        );
    }
}

/// One step of the README walkthrough: the action of its `<!-- example: ... -->` marker and
/// the fenced block after it.
struct Step {
    action: String,
    body: String,
}

/// The steps of the root README's "Using kink-flow" section, in order.
fn walkthrough() -> Vec<Step> {
    let readme =
        fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join("../../README.md")).unwrap();
    let start = readme
        .find("\n## Using kink-flow\n")
        .expect("README has a Using kink-flow section");
    let section = &readme[start + 1..];
    let section = &section[..section[1..]
        .find("\n## ")
        .map_or(section.len(), |end| end + 1)];
    let mut steps = Vec::new();
    let mut lines = section.lines();
    while let Some(line) = lines.next() {
        let Some(action) = line
            .trim()
            .strip_prefix("<!-- example:")
            .and_then(|rest| rest.strip_suffix("-->"))
        else {
            continue;
        };
        let fence = lines.next().expect("a fenced block after the marker");
        assert!(fence.starts_with("```"), "{action}: {fence}");
        let body = lines
            .by_ref()
            .take_while(|line| *line != "```")
            .collect::<Vec<_>>()
            .join("\n");
        steps.push(Step {
            action: action.trim().to_owned(),
            body,
        });
    }
    steps
}

#[test]
fn the_readme_walkthrough_works_as_written() {
    let dir = fixture("calc", "readme");
    let steps = walkthrough();
    let mut kinds = Vec::new();
    // The last command's stdout and document; the stdout of the last `run`.
    let mut last: Option<(Vec<u8>, Value)> = None;
    let mut last_run: Option<Vec<u8>> = None;
    // Each `run` document, with the program ids of the manifest when it ran.
    let mut runs = Vec::new();
    for step in &steps {
        let (kind, argument) = step
            .action
            .split_once(' ')
            .unwrap_or((step.action.as_str(), ""));
        kinds.push(kind.to_owned());
        let text = format!("{}\n", step.body);
        match kind {
            // The fresh copy of testdata/flow/calc already holds the file, exactly as shown.
            "file" => assert_eq!(
                fs::read_to_string(dir.join(argument)).unwrap(),
                text,
                "{argument}"
            ),
            "write" => fs::write(dir.join(argument), &text).unwrap(),
            "append" => {
                let mut contents = fs::read_to_string(dir.join(argument)).unwrap();
                contents.push_str(&text);
                fs::write(dir.join(argument), contents).unwrap();
            }
            "run" => {
                for command in step.body.lines().filter(|line| !line.trim().is_empty()) {
                    let words = command.split_whitespace().collect::<Vec<_>>();
                    assert_eq!(words[0], "kink-flow", "{command}");
                    kinds.push(words[1].to_owned());
                    let output = binary(&words[1..], &dir);
                    assert_eq!(
                        output.status.code(),
                        Some(i32::from(EXIT_OK)),
                        "{command}: {}",
                        String::from_utf8_lossy(&output.stdout)
                    );
                    let document: Value = serde_json::from_slice(&output.stdout)
                        .unwrap_or_else(|e| panic!("{command}: {e}"));
                    match words[1] {
                        "report" => assert_eq!(
                            Some(&output.stdout),
                            last_run.as_ref(),
                            "report reprints the last run"
                        ),
                        "run" => {
                            let manifest = FlowManifest::read(&dir.join(words[2])).unwrap();
                            let programs = manifest
                                .programs
                                .iter()
                                .map(|p| p.id.clone())
                                .collect::<Vec<_>>();
                            runs.push((document.clone(), programs));
                            last_run = Some(output.stdout.clone());
                        }
                        _ => {}
                    }
                    last = Some((output.stdout, document));
                }
            }
            "output" => {
                let (_, document) = last.as_ref().expect("an output follows a command");
                let excerpt: Value = serde_json::from_str(&step.body)
                    .unwrap_or_else(|e| panic!("output {argument}: {e}"));
                let actual = document
                    .pointer(argument)
                    .unwrap_or_else(|| panic!("output {argument}: no such value"));
                assert!(
                    contains(actual, &excerpt),
                    "output {argument}: {actual:#} does not contain {excerpt:#}"
                );
            }
            other => panic!("unknown example action {other:?}"),
        }
    }
    // The section shows every input file and every command of the loop.
    for kind in [
        "file", "write", "append", "run", "output", "check", "results", "report",
    ] {
        assert!(
            kinds.iter().any(|k| k == kind),
            "the walkthrough has no {kind}"
        );
    }
    // The first run leaves a survivor; after the program the walkthrough adds, the last run
    // kills it with that program, and nothing survives.
    let (first, before) = runs.first().expect("a run");
    let (last, _) = runs.last().unwrap();
    assert!(runs.len() >= 2);
    let survivors = first["survivors"].as_array().unwrap();
    assert!(!survivors.is_empty());
    assert_eq!(last["survivors"], json!([]));
    for id in survivors {
        let row = mutation(last, id.as_str().unwrap());
        assert_eq!(row["status"], "killed", "{id}");
        let killer = row["killer"].as_str().unwrap();
        assert!(
            !before.iter().any(|program| program == killer),
            "{id} is killed by {killer}, a program the first run already had"
        );
    }
}
