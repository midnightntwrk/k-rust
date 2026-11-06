//! `krs cases` runs a batch of named cases, the definition loaded once per worker: one verdict
//! record per case in document order (`krs-cases/2`) and a summary, exit 2 when a case is
//! refused, else 1 when one is unmet, else 3 when one is inconclusive or ran to no end, else 0;
//! `--jobs N` prints
//! what `--jobs 1` prints, views and their budget included. A case's views are evaluated in the
//! definition it runs on or in the observer it names, and each evaluation is bounded by a budget
//! of polls.
//!
//! The cases run on `fixtures/ends`, which copies each input into its own cell, steps `finish(v)`
//! to `done(v)` and `toss(v)` to `done(0)` or `done(1)`, and declares the views `EventCount`
//! (total) and `RegisterOrder` (left to the implementation on two or more keys). The observer,
//! [`OBSERVER`], is a second package of the workspace that depends on `ends`.

use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Output;
use std::sync::{Arc, Mutex, Weak};

use krs_test_support::{
    SharedFixtureTarget, TempDir, fixture_build_env, krs_command, shared_fixture_target, temp_dir,
};
use serde_json::{Value, json};

const ENDS: &str = include_str!("fixtures/ends/src/lib.rs");
const PACKAGE: &str = "krs-cli-cases-ends-fixture";
const OBSERVER_PACKAGE: &str = "krs-cli-cases-observe-fixture";
const UNDECIDED_PACKAGE: &str = "krs-cli-cases-undecided-fixture";

/// A definition whose exit cell, `status`, `quit c` sets to `c`; `open a` steps only where
/// `unsure(a)` holds, which no equation decides at `2`, so a run of `open 2` reaches two states
/// under a condition it cannot decide and has no one path. `OnlyOne(a)` has a value only at `1`,
/// where its guard holds. `UnsureAbove(a)` has no value at `0` or below, where its guard is
/// decided false, and above is as undecided as `Unsure(a)`.
const UNDECIDED: &str = r#"
use k::builtin::{Bool, Int, KSequence};
use k::KResult;
use k::Term;

k::sorts! {
    Stmt;
}

#[k::constructors(sort = Stmt, result = KResult)]
pub enum StmtSyntax {
    #[k::syntax("quit {code}")]
    Quit { code: Int },
    #[k::syntax("open {a}")]
    Open { a: Int },
}

#[k::function(total, internal)]
pub fn Opaque(a: Term<Int>) -> Term<Int>;

#[k::function(partial, internal)]
pub fn Unsure(a: Term<Int>) -> Term<Bool>;

#[k::equation]
#[k::requires(Opaque(a) == 1)]
fn unsure_one(Unsure(a): Term<Bool>) -> Term<Bool> {
    true
}

#[k::function(partial, internal)]
pub fn UnsureAbove(a: Term<Int>) -> Term<Bool>;

#[k::equation]
#[k::requires(a > 0 && Opaque(a) == 1)]
fn unsure_above(UnsureAbove(a): Term<Bool>) -> Term<Bool> {
    true
}

#[k::function(partial, internal)]
pub fn OnlyOne(a: Term<Int>) -> Term<Bool>;

#[k::equation]
#[k::requires(a == 1)]
fn only_one(OnlyOne(a): Term<Bool>) -> Term<Bool> {
    true
}

k::rules! {
    for Machine;
    use StmtSyntax::*;

    quit: { k: [Quit(code), ..], status: _ } => { k: [..], status: code };
    #[k::requires(Unsure(a))]
    open: { k: [Open(a), ..], status: _ } => { k: [..], status: 1 };
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell(exit)]
    pub status: Int,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self { k: k::k![pgm], status: 0 }
    }
}
"#;

/// An observer of `ends`: `WithRead` appends a read to an event log, built with the compared
/// definition's constructor, `Spin` climbs forever, so that its evaluation never ends, and `NotedStamp` gives a value of a
/// sort only the observer declares, with no document where it is `noted`, whose K text only the
/// observer's printer prints; `ClimbAbove` climbs for ever above `0` and has no value elsewhere.
const OBSERVER: &str = r#"//! An observer of the `ends` fixture, imported by no definition.

use k::Term;
use k::builtin::{Int, List};

/// The log with one more read.
#[k::function(total, internal)]
pub fn WithRead(log: Term<List>) -> Term<List> {
    [..log, ends::CpuEvent::Read(0)]
}

/// A view whose evaluation does not end.
#[k::function(total, internal)]
pub fn Spin(log: Term<List>) -> Term<Int> {
    Climb(log, 0)
}

/// `Climb(log, n + 1)`, for ever.
#[k::function(total, internal)]
pub fn Climb(log: Term<List>, n: Term<Int>) -> Term<Int> {
    Climb(log, n + 1)
}

k::sorts! {
    Stamp;
}

/// A stamp of a log: its length.
#[k::constructor(sort = Stamp, syntax = "tag({n})")]
pub struct Tag {
    pub n: Term<Int>,
}

/// `noted(x)` has the sort of `x`: a constructor of this package alone, parametric, so that no
/// form of the typed encoding writes a value that holds it.
#[k::constructor(sort = S, syntax = "noted({inner})")]
pub struct Noted<S: ?Sized> {
    pub inner: Term<S>,
}

/// A view of an `Int` whose evaluation climbs for ever above `0`, and that has no value at `0`
/// or below.
#[k::function(partial, internal)]
#[k::requires(n > 0)]
pub fn ClimbAbove(n: Term<Int>) -> Term<Int> {
    Rise(n)
}

/// `Rise(n + 1)`, for ever.
#[k::function(total, internal)]
pub fn Rise(n: Term<Int>) -> Term<Int> {
    Rise(n + 1)
}

/// A log's stamp, noted when the log is not empty.
#[k::function(total, internal)]
pub fn NotedStamp(log: Term<List>) -> Term<Stamp> {
    if log.len() > 0 { Noted { inner: Tag { n: log.len() } } } else { Tag { n: 0 } }
}
"#;

/// The workspace of `ends` and its observer, shared by the tests of this process, which run
/// `krs` on it one at a time.
struct Workspace {
    directory: TempDir,
    _target: SharedFixtureTarget,
    target: PathBuf,
    turn: Mutex<()>,
}

fn manifest(name: &str, namespace: &str, dependencies: &str) -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    let krs_literal = serde_json::to_string(krs.to_str().unwrap()).unwrap();
    format!(
        "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {krs_literal} }}\n{dependencies}\n[package.metadata.krs]\nk-namespace = \"{namespace}\"\n\n[package.metadata.krs.definitions.main]\n"
    )
}

fn workspace() -> Arc<Workspace> {
    static WORKSPACE: Mutex<Weak<Workspace>> = Mutex::new(Weak::new());
    let mut slot = WORKSPACE
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    if let Some(workspace) = slot.upgrade() {
        return workspace;
    }
    let target = shared_fixture_target();
    let directory = temp_dir();
    let root = directory.path();
    for (member, source, manifest) in [
        ("language", ENDS, manifest(PACKAGE, "ORG-KRS-CLI-CASES", "")),
        (
            "observe",
            OBSERVER,
            manifest(
                OBSERVER_PACKAGE,
                "ORG-KRS-CLI-CASES-OBSERVE",
                &format!("ends = {{ package = \"{PACKAGE}\", path = \"../language\" }}\n"),
            ),
        ),
        (
            "undecided",
            UNDECIDED,
            manifest(UNDECIDED_PACKAGE, "ORG-KRS-CLI-CASES-UNDECIDED", ""),
        ),
    ] {
        fs::create_dir_all(root.join(member).join("src")).unwrap();
        fs::write(root.join(member).join("src/lib.rs"), source).unwrap();
        fs::write(root.join(member).join("Cargo.toml"), manifest).unwrap();
    }
    fs::write(
        root.join("Cargo.toml"),
        "[workspace]\nmembers = [\"language\", \"observe\", \"undecided\"]\nresolver = \"3\"\n",
    )
    .unwrap();
    let workspace = Arc::new(Workspace {
        directory,
        target: target.path().to_path_buf(),
        _target: target,
        turn: Mutex::new(()),
    });
    *slot = Arc::downgrade(&workspace);
    workspace
}

impl Workspace {
    /// The `ends` package's directory, where `krs` runs and the case documents are written.
    fn path(&self) -> PathBuf {
        self.directory.path().join("language")
    }

    fn write(&self, relative: &str, contents: impl AsRef<[u8]>) {
        let path = self.path().join(relative);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, contents).unwrap();
    }

    /// `krs VERB --package ends --definition main ARGUMENTS`, from the `ends` package.
    fn krs(&self, verb: &str, arguments: &[&str]) -> Output {
        self.krs_in("language", PACKAGE, verb, arguments)
    }

    /// `krs VERB --package PACKAGE --definition main ARGUMENTS`, from the workspace member
    /// `member`.
    fn krs_in(&self, member: &str, package: &str, verb: &str, arguments: &[&str]) -> Output {
        self.krs_with(member, package, verb, arguments, |process| {
            process.output().unwrap()
        })
    }

    /// `krs VERB --package PACKAGE --definition main ARGUMENTS`, from the workspace member
    /// `member`, run by `run`.
    fn krs_with<T>(
        &self,
        member: &str,
        package: &str,
        verb: &str,
        arguments: &[&str],
        run: impl FnOnce(&mut std::process::Command) -> T,
    ) -> T {
        let _turn = self
            .turn
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let mut process = krs_command!();
        fixture_build_env(&mut process, &self.target);
        process
            .current_dir(self.directory.path().join(member))
            .arg(verb)
            .args(["--package", package, "--definition", "main"])
            .args(arguments);
        run(&mut process)
    }
}

/// The inputs of a case whose program is `pgm`, with `regs` as the register file.
fn inputs(pgm: &Value, regs: &Value) -> Value {
    json!({
        "pgm": pgm,
        "regs": regs,
        "f": {"Flags": {"zf": true, "cf": false}},
        "pc": 256,
        "bus": [{"Read": {"addr": 5}}],
        "memory": {"5": 6},
        "ime": true,
        "w": 9,
        "z": 4,
    })
}

/// A named case on `ends` whose program is `pgm`, expecting `expect`.
fn case(name: &str, pgm: &Value, expect: &Value) -> Value {
    json!({"name": name, "inputs": inputs(pgm, &json!({"A": 1})), "expect": expect})
}

/// `finish(3)`, which ends `done(3)`.
fn finish() -> Value {
    json!({"Finish": {"value": 3}})
}

/// An expectation of `finish(3)`'s end on `k`, `pc` and `bus`.
fn finished(pc: i64, bus: &Value) -> Value {
    json!({
        "halt": "stuck",
        "compare": ["k", "pc", "bus"],
        "cells": {"k": {"$seq": [{"Done": {"value": 3}}]}, "pc": pc, "bus": bus},
    })
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

/// The JSON records of `krs cases --output json`, one per line.
fn records(output: &Output) -> Vec<Value> {
    stdout(output)
        .lines()
        .map(|line| {
            serde_json::from_str(line).unwrap_or_else(|error| {
                panic!(
                    "a line is not JSON ({error}): {line}\nstderr:\n{}",
                    stderr(output)
                )
            })
        })
        .collect()
}

/// The batch: a document of three named cases (met, unmet, and an include of a JSON file) whose
/// included file holds three more (inconclusive, no expectation, and refused for a view with no
/// value).
fn write_batch(workspace: &Workspace) {
    let read = json!([{"Read": {"addr": 5}}]);
    let met = case("a-met", &finish(), &finished(256, &read));
    let unmet = case("a-unmet", &finish(), &finished(257, &read));
    let document = format!(
        "{}\n{}\n[[case]]\n\"$data-file\" = \"more/cases.json\"\n",
        toml_case(&met),
        toml_case(&unmet)
    );
    workspace.write("cases.toml", document);
    let toss = json!({"Toss": {"value": 0}});
    let regs = json!({"A": 1, "B": 2});
    let more = json!([
        case(
            "b-toss",
            &toss,
            &json!({"halt": "stuck", "compare": ["pc"], "cells": {"pc": 256}})
        ),
        {"name": "b-plain", "inputs": inputs(&finish(), &json!({"A": 1}))},
        {
            "name": "b-refused",
            "inputs": inputs(&finish(), &regs),
            "expect": {
                "halt": "stuck",
                "compare": ["regs"],
                "views": {"regs": "RegisterOrder"},
                "cells": {"regs": regs},
            },
        },
    ]);
    workspace.write("more/cases.json", more.to_string());
}

/// A named case as a TOML `[[case]]` table, each of its keys an inline value.
fn toml_case(case: &Value) -> String {
    let mut table = String::from("[[case]]\n");
    for (key, value) in case.as_object().unwrap() {
        let _ = writeln!(table, "{key} = {}", toml_inline(value));
    }
    table
}

/// `value` as a TOML inline value: a table's keys quoted, a string as JSON quotes it (which TOML
/// reads alike for the strings these cases hold).
fn toml_inline(value: &Value) -> String {
    match value {
        Value::Object(table) => {
            let members = table
                .iter()
                .map(|(key, value)| {
                    format!("{} = {}", Value::from(key.as_str()), toml_inline(value))
                })
                .collect::<Vec<_>>();
            format!("{{ {} }}", members.join(", "))
        }
        Value::Array(items) => {
            let items = items.iter().map(toml_inline).collect::<Vec<_>>();
            format!("[{}]", items.join(", "))
        }
        Value::Null => panic!("TOML has no null"),
        scalar => scalar.to_string(),
    }
}

#[test]
fn a_batch_reports_each_case_in_document_order() {
    let workspace = workspace();
    write_batch(&workspace);
    let one = workspace.krs("cases", &["cases.toml", "--output", "json", "--jobs", "1"]);
    assert_eq!(one.status.code(), Some(2), "{}", stderr(&one));
    let lines = records(&one);
    let verdicts = lines
        .iter()
        .take(lines.len() - 1)
        .map(|record| {
            assert_eq!(record["schema"], "krs-cases/2", "{record}");
            (
                record["case"].as_str().unwrap().to_owned(),
                record["verdict"].as_str().unwrap().to_owned(),
            )
        })
        .collect::<Vec<_>>();
    let expected = [
        ("cases.toml#a-met", "met"),
        ("cases.toml#a-unmet", "unmet"),
        ("cases.toml#b-toss", "inconclusive"),
        ("cases.toml#b-plain", "ran"),
        ("cases.toml#b-refused", "refused"),
    ]
    .map(|(case, verdict)| (case.to_owned(), verdict.to_owned()));
    assert_eq!(verdicts, expected, "{}", stdout(&one));
    assert_eq!(lines[0]["halt"], "stuck");
    assert_eq!(lines[0]["steps"], 1);
    assert_eq!(lines[1]["difference"]["format"], "krs-difference/3");
    assert_eq!(lines[1]["difference"]["path"], "pc");
    assert!(
        lines[2]["reason"]
            .as_str()
            .is_some_and(|reason| reason.contains("which has 2 successors")),
        "{}",
        lines[2]
    );
    assert_eq!(lines[3]["halt"], "stuck");
    assert!(
        lines[4]["reason"]
            .as_str()
            .is_some_and(|reason| reason.contains("RegisterOrder") && reason.contains("no value")),
        "{}",
        lines[4]
    );
    // A refused record names the views its expectation writes, as a checked one does.
    assert_eq!(
        lines[4]["views"],
        json!({"regs": "RegisterOrder"}),
        "{}",
        lines[4]
    );
    assert_eq!(
        lines[5],
        json!({
            "schema": "krs-cases/2",
            "summary": {"cases": 5, "met": 1, "unmet": 1, "inconclusive": 1, "refused": 1, "ran": 1},
            "status": 2,
        })
    );

    // Every worker count prints the same records.
    for jobs in ["2", "3"] {
        let many = workspace.krs("cases", &["cases.toml", "--output", "json", "--jobs", jobs]);
        assert_eq!(many.status.code(), Some(2), "{}", stderr(&many));
        assert_eq!(stdout(&many), stdout(&one), "--jobs {jobs}");
    }

    // The human records: the verdict lines `krs run --case` prints, named by the case's id.
    let human = workspace.krs("cases", &["cases.toml", "--jobs", "2"]);
    assert_eq!(human.status.code(), Some(2), "{}", stderr(&human));
    let text = stdout(&human);
    assert!(
        text.starts_with(
            "cases.toml#a-met: expectation met\ncases.toml#a-unmet: expectation unmet at `pc`\n  expected: 257\n  actual:   256\ncases.toml#b-toss: expectation inconclusive: "
        ),
        "{text}"
    );
    assert!(
        text.contains("\ncases.toml#b-plain: ran, stuck after 1 step\ncases.toml#b-refused: refused: case `b-refused` of `cases.toml`: "),
        "{text}"
    );
    assert!(
        text.ends_with("krs cases: 5 cases: 1 met, 1 unmet, 1 inconclusive, 1 refused, 1 ran\n"),
        "{text}"
    );
}

/// The document `file` of three cases of `finish(3)` whose `run.depth` is 0: `cut` expects the
/// cells its state holds, `plain` states no expectation, and `bound` expects a `depth-bound`
/// end. Each test writes its own file, since the tests share the workspace.
fn write_bounded(workspace: &Workspace, file: &str) {
    let read = json!([{"Read": {"addr": 5}}]);
    let at_start =
        json!({"halt": "stuck", "compare": ["pc", "bus"], "cells": {"pc": 256, "bus": read}});
    let bounded = |name: &str, expect: Option<&Value>| {
        let mut case = json!({"name": name, "inputs": inputs(&finish(), &json!({"A": 1})), "run": {"depth": 0}});
        if let Some(expect) = expect {
            case["expect"] = expect.clone();
        }
        case
    };
    let mut bound = at_start.clone();
    bound["halt"] = json!("depth-bound");
    workspace.write(
        file,
        json!({"case": [
            bounded("cut", Some(&at_start)),
            bounded("plain", None),
            bounded("bound", Some(&bound)),
        ]})
        .to_string(),
    );
}

/// A depth bound is a run status, never an end an expectation meets: a case whose run reaches
/// its `run.depth` before its end is inconclusive (3) under `krs cases`, as under
/// `krs run --case` ([`krs_run_case_is_inconclusive_at_its_depth_bound`]),
/// although its state holds the expected cells; one without an expectation ran to its bound,
/// which a plain run reports with exit 0; and an expectation of a `depth-bound` end is refused
/// (2), naming the stop at a rule with a stop count that states a point of a run.
#[test]
fn a_depth_bound_is_a_run_status_never_an_expected_end() {
    let workspace = workspace();
    write_bounded(&workspace, "bounded.json");
    let output = workspace.krs("cases", &["bounded.json", "--output", "json"]);
    assert_eq!(output.status.code(), Some(2), "{}", stderr(&output));
    let lines = records(&output);
    assert_eq!(lines[0]["verdict"], "inconclusive", "{}", lines[0]);
    assert_eq!(
        (&lines[0]["halt"], &lines[0]["steps"]),
        (&json!("depth-bound"), &json!(0))
    );
    assert!(
        lines[0]["reason"].as_str().is_some_and(
            |reason| reason.contains("a step budget ended the run at a `depth-bound` state")
        ),
        "{}",
        lines[0]
    );
    assert_eq!(lines[1]["verdict"], "ran", "{}", lines[1]);
    assert_eq!(lines[1]["halt"], "depth-bound", "{}", lines[1]);
    assert_eq!(lines[2]["verdict"], "refused", "{}", lines[2]);
    let reason = lines[2]["reason"].as_str().unwrap_or_default();
    assert!(
        reason.contains("`expect.halt`: an expected end is never `depth-bound`")
            && reason.contains("stop_before")
            && reason.contains("stop_count = N"),
        "{}",
        lines[2]
    );
    let status = |name: &str| {
        let output = workspace.krs("cases", &["bounded.json", "--name", name]);
        (output.status.code(), stdout(&output))
    };
    let (code, text) = status("cut");
    assert_eq!(code, Some(3), "{text}");
    assert!(
        text.starts_with(
            "bounded.json#cut: expectation inconclusive: the actual side has no end: "
        ),
        "{text}"
    );
    let (code, text) = status("plain");
    assert_eq!(code, Some(0), "{text}");
    assert!(
        text.starts_with("bounded.json#plain: ran, depth-bound after 0 steps\n"),
        "{text}"
    );
}

/// `krs run --case` reads the cases of [`write_bounded`] as `krs cases` does
/// ([`a_depth_bound_is_a_run_status_never_an_expected_end`]): inconclusive at the bound under an
/// expectation, exit 0 for a plain run, and an expectation of a `depth-bound` end refused.
#[test]
fn krs_run_case_is_inconclusive_at_its_depth_bound() {
    let workspace = workspace();
    write_bounded(&workspace, "bounded-run.json");
    let run = |name: &str| {
        workspace.krs(
            "run",
            &[
                "--case",
                "bounded-run.json",
                "--case-name",
                name,
                "--output",
                "none",
            ],
        )
    };
    let cut = run("cut");
    assert_eq!(cut.status.code(), Some(3), "{}", stderr(&cut));
    assert!(
        stderr(&cut).contains("krs run: depth-bound after 0 steps")
            && stderr(&cut)
                .contains("\nkrs run: expectation inconclusive: the actual side has no end: "),
        "{}",
        stderr(&cut)
    );
    let plain = run("plain");
    assert_eq!(plain.status.code(), Some(0), "{}", stderr(&plain));
    assert!(
        stderr(&plain).contains("krs run: depth-bound after 0 steps"),
        "{}",
        stderr(&plain)
    );
    let refused = run("bound");
    assert_eq!(refused.status.code(), Some(2), "{}", stderr(&refused));
    assert!(
        stderr(&refused).contains("`expect.halt`: an expected end is never `depth-bound`"),
        "{}",
        stderr(&refused)
    );
}

/// The status is 2 when a case is refused, else 1 when one is unmet, else 3 when one is
/// inconclusive, else 0; `--name` selects the named cases whose name it matches, and one that selects none is a usage
/// error. A document that cannot be read is a refused record, and the next document runs.
#[test]
fn the_status_follows_the_verdicts() {
    let workspace = workspace();
    write_batch(&workspace);
    let status = |arguments: &[&str]| {
        let mut all = vec!["cases.toml"];
        all.extend(arguments);
        let output = workspace.krs("cases", &all);
        (output.status.code(), output)
    };
    let (code, output) = status(&["--name", "a-met"]);
    assert_eq!(code, Some(0), "{}", stderr(&output));
    assert_eq!(
        stdout(&output),
        "cases.toml#a-met: expectation met\nkrs cases: 1 case: 1 met, 0 unmet, 0 inconclusive, 0 refused, 0 ran\n"
    );
    let (code, output) = status(&["--name", "c-*"]);
    assert_eq!(code, Some(2), "{}", stderr(&output));
    assert!(
        stderr(&output).contains("--name `c-*` selects no named case of the documents given"),
        "{}",
        stderr(&output)
    );
    let (code, output) = status(&["--name", "*-t*"]);
    assert_eq!(code, Some(3), "{}", stderr(&output));
    let (code, output) = status(&["--name", "b-p*"]);
    assert_eq!(code, Some(0), "{}", stderr(&output));
    // Met, unmet and inconclusive: the finding comes first.
    let (code, output) = status(&["--name", "*-*t*"]);
    assert_eq!(code, Some(1), "{}", stderr(&output));
    // Inconclusive, ran and refused: the refusal comes first.
    let (code, output) = status(&["--name", "b-*"]);
    assert_eq!(code, Some(2), "{}", stderr(&output));

    let read = json!([{"Read": {"addr": 5}}]);
    workspace.write(
        "one.json",
        json!({"inputs": inputs(&finish(), &json!({"A": 1})), "expect": finished(256, &read)})
            .to_string(),
    );
    let output = workspace.krs(
        "cases",
        &[
            "missing.toml",
            "one.json",
            "--output",
            "json",
            "--jobs",
            "2",
        ],
    );
    assert_eq!(output.status.code(), Some(2), "{}", stderr(&output));
    let lines = records(&output);
    assert_eq!(lines[0]["case"], "missing.toml");
    assert_eq!(lines[0]["verdict"], "refused");
    assert!(
        lines[0]["reason"]
            .as_str()
            .is_some_and(|reason| reason.contains("could not read the case `missing.toml`")),
        "{}",
        lines[0]
    );
    assert_eq!(lines[1]["case"], "one.json");
    assert_eq!(lines[1]["verdict"], "met");
    assert_eq!(lines[2]["summary"]["cases"], 2);

    // An observer named without a view is refused with the expectation, before the run, and is
    // not prepared: this one names no package of the workspace, which a preparation would report.
    let mut expect = finished(256, &read);
    expect["observer"] = json!("no-such-package:main");
    workspace.write(
        "unviewed.json",
        json!({"case": [case("unviewed", &finish(), &expect)]}).to_string(),
    );
    let output = workspace.krs("cases", &["unviewed.json", "--output", "json"]);
    assert_eq!(output.status.code(), Some(2), "{}", stderr(&output));
    let lines = records(&output);
    assert_eq!(lines[0]["verdict"], "refused", "{}", lines[0]);
    assert!(
        lines[0]["reason"].as_str().is_some_and(|reason| reason
            .contains("`observer` names the definition the views are evaluated in, and the expectation names no view")
            && !reason.contains("cannot be prepared")),
        "{}",
        lines[0]
    );
    assert_eq!(lines[0]["observer"], "no-such-package:main", "{}", lines[0]);
}

/// The views cases, written to `file`: views evaluated in the definition the cases run on
/// (`count`, met and unmet) and in the observer (`observed` met, `spin` without end, `noted` unmet
/// at a value of the observer's own sort); returns the observer's name.
fn write_views(workspace: &Workspace, file: &str) -> String {
    let read = json!([{"Read": {"addr": 5}}]);
    let observer = format!("{OBSERVER_PACKAGE}:main");
    let viewed = |bus: &Value, views: &Value, observer: Option<&str>| {
        let mut expect = finished(256, bus);
        expect["views"] = views.clone();
        if let Some(observer) = observer {
            expect["observer"] = json!(observer);
        }
        expect
    };
    let cases = json!({"case": [
        // Raw logs differ, their counts do not.
        case("count", &finish(), &viewed(&json!([{"Write": {"addr": 1, "value": 2}}]), &json!({"bus": "EventCount"}), None)),
        case("count-unmet", &finish(), &viewed(&json!([]), &json!({"bus": "EventCount"}), None)),
        case("observed", &finish(), &viewed(&read, &json!({"bus": "WithRead"}), Some(&observer))),
        case("spin", &finish(), &viewed(&read, &json!({"bus": "Spin"}), Some(&observer))),
        case("noted", &finish(), &viewed(&json!([]), &json!({"bus": "NotedStamp"}), Some(&observer))),
    ]});
    workspace.write(file, cases.to_string());
    observer
}

/// A case's views are evaluated in the definition it runs on, or in the observer its expectation
/// names: a met or inconclusive verdict prints the views it used, an unmet one shows the viewed
/// values (K text by the observer's printer where a value of the observer's own sort has no
/// document), and an evaluation that spends its `--view-budget` of polls is inconclusive, never
/// met. The budget counts the evaluation's own work, so every worker count prints the same
/// records.
#[test]
fn views_apply_where_cases_name_them() {
    let workspace = workspace();
    let observer = write_views(&workspace, "views.json");
    // A few polls evaluate each view that ends here; `Spin` spends any budget.
    let output = workspace.krs(
        "cases",
        &[
            "views.json",
            "--output",
            "json",
            "--view-budget",
            "100000",
            "--jobs",
            "1",
        ],
    );
    assert_eq!(output.status.code(), Some(1), "{}", stderr(&output));
    let lines = records(&output);
    assert_eq!(lines[0]["verdict"], "met", "{}", lines[0]);
    assert_eq!(lines[0]["views"], json!({"bus": "EventCount"}));
    assert!(lines[0].get("observer").is_none(), "{}", lines[0]);
    assert_eq!(lines[1]["verdict"], "unmet", "{}", lines[1]);
    let difference = &lines[1]["difference"];
    assert_eq!(difference["path"], "bus", "{difference}");
    assert_eq!(difference["views"], json!({"bus": "EventCount"}));
    assert_eq!(difference["left"]["value"]["document"], 0, "{difference}");
    assert_eq!(difference["right"]["value"]["document"], 1, "{difference}");
    assert_eq!(lines[2]["verdict"], "met", "{}", lines[2]);
    assert_eq!(lines[2]["views"], json!({"bus": "WithRead"}));
    assert_eq!(lines[2]["observer"], json!(observer));
    assert_eq!(lines[3]["verdict"], "inconclusive", "{}", lines[3]);
    assert!(
        lines[3]["reason"]
            .as_str()
            .is_some_and(|reason| reason.contains("it spent its budget of 100000 polls")),
        "{}",
        lines[3]
    );
    assert_eq!(lines[3]["views"], json!({"bus": "Spin"}));
    assert_eq!(lines[4]["verdict"], "unmet", "{}", lines[4]);
    let difference = &lines[4]["difference"];
    assert_eq!(
        difference["left"]["value"]["document"],
        json!({"Tag": {"n": 0}}),
        "{difference}"
    );
    assert_eq!(
        difference["right"]["value"]["rendering"], "k",
        "{difference}"
    );
    assert_eq!(
        difference["right"]["value"]["text"], "noted ( tag ( 1 ) )",
        "{difference}"
    );

    for jobs in ["2", "5"] {
        let many = workspace.krs(
            "cases",
            &[
                "views.json",
                "--output",
                "json",
                "--view-budget",
                "100000",
                "--jobs",
                jobs,
            ],
        );
        assert_eq!(stdout(&many), stdout(&output), "--jobs {jobs}");
    }
}

/// `krs cases` prints the views a met verdict used, and `krs run --case` evaluates the same views
/// in the same observer.
#[test]
fn krs_run_case_evaluates_the_views_krs_cases_does() {
    let workspace = workspace();
    let observer = write_views(&workspace, "views-run.json");
    let human = workspace.krs(
        "cases",
        &[
            "views-run.json",
            "--name",
            "observed",
            "--view-budget",
            "100000",
        ],
    );
    assert_eq!(human.status.code(), Some(0), "{}", stderr(&human));
    assert!(
        stdout(&human).starts_with(&format!(
            "views-run.json#observed: expectation met\n  views: `bus` = `WithRead`, in `{observer}`\n"
        )),
        "{}",
        stdout(&human)
    );

    let run = workspace.krs(
        "run",
        &[
            "--case",
            "views-run.json",
            "--case-name",
            "observed",
            "--output",
            "none",
        ],
    );
    assert_eq!(run.status.code(), Some(0), "{}", stderr(&run));
    assert!(
        stderr(&run).ends_with(&format!(
            "krs run: expectation met\n  views: `bus` = `WithRead`, in `{observer}`\n"
        )),
        "{}",
        stderr(&run)
    );
}

/// A view with no value at one side refuses the comparison even where its evaluation at the
/// other side stops (`ClimbAbove` of `pc` at `0` and at `1`): `krs compare` exits 2 in either
/// order of its sides, and `krs cases` and `krs run --case` refuse a case whichever of the
/// expected and actual sides has no value.
#[test]
fn a_view_with_no_value_refuses_whichever_side_comes_first() {
    let workspace = workspace();
    let observer = format!("{OBSERVER_PACKAGE}:main");
    let at = |pc: i64| {
        let mut inputs = inputs(&finish(), &json!({"A": 1}));
        inputs["pc"] = json!(pc);
        inputs
    };
    let expect = |pc: i64| {
        let mut expect = finished(pc, &json!([{"Read": {"addr": 5}}]));
        expect["views"] = json!({"pc": "ClimbAbove"});
        expect["observer"] = json!(observer);
        expect
    };
    let cases = json!({"case": [
        {"name": "up", "inputs": at(1)},
        {"name": "zero", "inputs": at(0)},
        {"name": "expect-up", "inputs": at(0), "expect": expect(1)},
        {"name": "expect-zero", "inputs": at(1), "expect": expect(0)},
    ]});
    workspace.write("order.json", cases.to_string());
    for (first, second, refused) in [
        ("order.json#up", "order.json#zero", "right"),
        ("order.json#zero", "order.json#up", "left"),
    ] {
        let output = workspace.krs(
            "compare",
            &[
                first,
                second,
                "--view",
                "pc=ClimbAbove",
                "--observer",
                &observer,
                "--view-budget",
                "10000",
            ],
        );
        assert_eq!(output.status.code(), Some(2), "{}", stdout(&output));
        assert!(
            stderr(&output).contains(&format!(
                "the view `ClimbAbove` of the cell `pc`: it has no value at the {refused} end's `pc`: the definition gives it no value"
            )),
            "{}",
            stderr(&output)
        );
    }

    let output = workspace.krs(
        "cases",
        &[
            "order.json",
            "--name",
            "expect-*",
            "--output",
            "json",
            "--view-budget",
            "10000",
        ],
    );
    assert_eq!(output.status.code(), Some(2), "{}", stderr(&output));
    let lines = records(&output);
    for (line, refused) in lines[..2].iter().zip(["actual", "expected"]) {
        assert_eq!(line["verdict"], "refused", "{line}");
        assert!(
            line["reason"]
                .as_str()
                .is_some_and(|reason| reason
                    .contains(&format!("it has no value at the {refused} end's `pc`"))),
            "{line}"
        );
    }
    for (name, refused) in [("expect-up", "actual"), ("expect-zero", "expected")] {
        let run = workspace.krs(
            "run",
            &[
                "--case",
                "order.json",
                "--case-name",
                name,
                "--output",
                "none",
                "--view-budget",
                "10000",
            ],
        );
        assert_eq!(run.status.code(), Some(2), "{name}: {}", stderr(&run));
        assert!(
            stderr(&run).contains(&format!("it has no value at the {refused} end's `pc`")),
            "{name}: {}",
            stderr(&run)
        );
    }
}

/// A case that states no expectation and whose run reaches several states under conditions it
/// cannot decide ran to no one end: a `ran` record with no halt and the reason, which counts as no
/// answer (exit 3), as an inconclusive halt does; `krs run --case` exits 3 on it, and `krs compare`
/// finds a side with no one end inconclusive (exit 3), not a refusal.
#[test]
fn a_case_whose_run_has_no_one_path_ran_to_no_end() {
    let workspace = workspace();
    let undecided = workspace.directory.path().join("undecided");
    let quit = json!({"pgm": {"Quit": {"code": 0}}});
    let open = json!({"pgm": {"Open": {"a": 2}}});
    let document = json!({"case": [
        {"name": "quit", "inputs": quit},
        {"name": "open", "inputs": open},
        {"name": "expected", "inputs": quit, "expect": {"halt": "stuck", "compare": ["status"], "cells": {"status": 0}}},
    ]});
    fs::write(undecided.join("cases.json"), document.to_string()).unwrap();
    let krs = |verb: &str, arguments: &[&str]| {
        workspace.krs_in("undecided", UNDECIDED_PACKAGE, verb, arguments)
    };

    let output = krs(
        "cases",
        &["cases.json", "--name", "open", "--output", "json"],
    );
    assert_eq!(output.status.code(), Some(3), "{}", stderr(&output));
    let lines = records(&output);
    assert_eq!(lines[0]["case"], "cases.json#open", "{}", lines[0]);
    assert_eq!(lines[0]["verdict"], "ran", "{}", lines[0]);
    assert!(lines[0].get("halt").is_none(), "{}", lines[0]);
    let reason = lines[0]["reason"].as_str().unwrap_or_default();
    assert!(
        reason.starts_with(
            "the run has no one end: the run reaches 2 states, under conditions over `unsure ( 2 )`"
        ),
        "{}",
        lines[0]
    );
    assert_eq!(
        lines[1]["summary"],
        json!({"cases": 1, "met": 0, "unmet": 0, "inconclusive": 0, "refused": 0, "ran": 1})
    );
    assert_eq!(lines[1]["status"], 3);
    let human = krs("cases", &["cases.json", "--name", "open"]);
    assert_eq!(human.status.code(), Some(3), "{}", stderr(&human));
    assert!(
        stdout(&human).starts_with("cases.json#open: ran: the run has no one end: "),
        "{}",
        stdout(&human)
    );
    let quit_only = krs("cases", &["cases.json", "--name", "quit"]);
    assert_eq!(quit_only.status.code(), Some(0), "{}", stderr(&quit_only));

    let run = krs("run", &["--case", "cases.json", "--case-name", "open"]);
    assert_eq!(run.status.code(), Some(3), "{}", stderr(&run));
    let compared = krs("compare", &["cases.json#open", "cases.json#quit"]);
    assert_eq!(compared.status.code(), Some(3), "{}", stderr(&compared));
    assert!(
        stdout(&compared).starts_with("krs compare: inconclusive: "),
        "{}",
        stdout(&compared)
    );
    let expected = krs(
        "compare",
        &["--expect", "cases.json#expected", "cases.json#open"],
    );
    assert_eq!(expected.status.code(), Some(3), "{}", stderr(&expected));
}

/// A view's equation guard that the solver answers `Unknown` (a starved solver, on the guard
/// `Opaque(2) == 1`) leaves the view's evaluation short of a value for a reason of that solver
/// run, not of the definition: the comparison is inconclusive (exit 3), naming the answer. The
/// same view with a solver that decides the guard's queries, where the guard stays undecided on
/// decided answers, and a view whose guard is decided false (`2 == 1`, decided under the starved
/// solver as well) have no value: the comparison is refused (exit 2).
#[test]
fn a_view_whose_guard_the_solver_answers_unknown_is_inconclusive_not_no_value() {
    let workspace = workspace();
    let undecided = workspace.directory.path().join("undecided");
    let document = json!({"case": [
        {"name": "two", "inputs": {"pgm": {"Quit": {"code": 2}}}},
        {"name": "zero", "inputs": {"pgm": {"Quit": {"code": 0}}}},
    ]});
    fs::write(undecided.join("views.json"), document.to_string()).unwrap();
    let compare_sides = |left: &str, right: &str, view: &str, solver: &[&str]| {
        let arguments = [&[left, right, "--view", view][..], solver].concat();
        workspace.krs_in("undecided", UNDECIDED_PACKAGE, "compare", &arguments)
    };
    let compare = |view: &str, solver: &[&str]| {
        compare_sides("views.json#two", "views.json#two", view, solver)
    };
    let starved = ["--smt-resource-limit", "1", "--smt-retries", "0"];

    let unknown = compare("status=Unsure", &starved);
    assert_eq!(unknown.status.code(), Some(3), "{}", stderr(&unknown));
    assert!(
        stdout(&unknown).starts_with(
            "krs compare: inconclusive: the view `Unsure` of the cell `status`: at the left end's `status`, the solver answered `Unknown` to "
        ),
        "{}",
        stdout(&unknown)
    );

    let refused = |output: &Output, view: &str| {
        assert_eq!(output.status.code(), Some(2), "{}", stdout(output));
        assert!(
            stderr(output).contains(&format!(
                "the view `{view}` of the cell `status`: it has no value at the left end's `status`: the definition gives it no value"
            )),
            "{}",
            stderr(output)
        );
    };
    refused(&compare("status=Unsure", &[]), "Unsure");
    refused(&compare("status=OnlyOne", &starved), "OnlyOne");

    // An `Unknown` answer at one value does not hide a view with no value at another, in either
    // order of the sides: `UnsureAbove` is undecided at `2` under the starved solver, and has no
    // value at `0` under any solver.
    let unknown = compare("status=UnsureAbove", &starved);
    assert_eq!(unknown.status.code(), Some(3), "{}", stderr(&unknown));
    for (left, right, side) in [
        ("views.json#two", "views.json#zero", "right"),
        ("views.json#zero", "views.json#two", "left"),
    ] {
        let output = compare_sides(left, right, "status=UnsureAbove", &starved);
        assert_eq!(output.status.code(), Some(2), "{}", stdout(&output));
        assert!(
            stderr(&output).contains(&format!(
                "the view `UnsureAbove` of the cell `status`: it has no value at the {side} end's `status`: the definition gives it no value"
            )),
            "{}",
            stderr(&output)
        );
    }
}

/// The solver's bound decides nothing here, so a run ends `indeterminate` and a search is
/// incomplete: no answer, exit 3. A run whose output cannot be written, or whose `--timings`
/// cannot be, exits 2, joined with its answer: the error comes before no answer.
#[test]
fn an_undecided_run_or_search_has_no_answer_and_an_unwritten_output_is_an_error() {
    let workspace = workspace();
    let undecided = workspace.directory.path().join("undecided");
    fs::write(undecided.join("open.txt"), "open 2\n").unwrap();
    fs::write(undecided.join("quit.txt"), "quit 0\n").unwrap();
    let krs = |verb: &str, arguments: &[&str]| {
        workspace.krs_in("undecided", UNDECIDED_PACKAGE, verb, arguments)
    };
    let starved = ["--smt-resource-limit", "1", "--smt-retries", "0"];

    let search = krs("search", &[&["open.txt"][..], &starved].concat());
    assert_eq!(search.status.code(), Some(3), "{}", stderr(&search));
    assert!(
        stderr(&search).contains("(incomplete: some paths were not decided)"),
        "{}",
        stderr(&search)
    );
    let run = krs("run", &[&["open.txt"][..], &starved].concat());
    assert_eq!(run.status.code(), Some(3), "{}", stderr(&run));
    assert!(
        stderr(&run).contains("krs run: indeterminate after 0 steps"),
        "{}",
        stderr(&run)
    );

    let full = workspace.krs_with(
        "undecided",
        UNDECIDED_PACKAGE,
        "run",
        &["quit.txt"],
        |process| {
            process
                .stdout(fs::File::create("/dev/full").unwrap())
                .stderr(std::process::Stdio::piped())
                .output()
                .unwrap()
        },
    );
    assert_eq!(full.status.code(), Some(2), "{}", stderr(&full));
    assert!(
        stderr(&full).contains("krs: could not write stdout"),
        "{}",
        stderr(&full)
    );

    let timings = undecided.join("no-such-directory/timings.json");
    let timings = timings.to_str().unwrap();
    let unmeasured = krs("run", &["quit.txt", "--timings", timings]);
    assert_eq!(unmeasured.status.code(), Some(2), "{}", stderr(&unmeasured));
    let unmeasured = krs(
        "run",
        &[&["open.txt", "--timings", timings][..], &starved].concat(),
    );
    assert_eq!(unmeasured.status.code(), Some(2), "{}", stderr(&unmeasured));
}

/// A dependency's item is named by its Cargo package name with `-` written `_`, the name the
/// definition records it by: the observer's manifest renames `ends`' package to `ends`, a name of
/// its own source alone, so a stop of the observer's definition (composed with `ends`' facet)
/// written `ends::finish` is refused
/// naming `krs_cli_cases_ends_fixture::finish`, which stops at the dependency's rule.
#[test]
fn a_renamed_dependency_is_named_by_its_package_name() {
    let workspace = workspace();
    workspace.write(
        "renamed.json",
        json!({"inputs": inputs(&finish(), &json!({"A": 1}))}).to_string(),
    );
    let run = |stop: &str| {
        workspace.krs_in(
            "observe",
            OBSERVER_PACKAGE,
            "run",
            &[
                "--dependency",
                &format!("{PACKAGE}:main"),
                "--case",
                "../language/renamed.json",
                "--stop-before",
                stop,
            ],
        )
    };
    let refused = run("ends::finish");
    assert_eq!(refused.status.code(), Some(2), "{}", stderr(&refused));
    let accepted = "krs_cli_cases_ends_fixture::finish";
    assert!(
        stderr(&refused).contains(&format!(
            "the definition records no package by the name `ends`: a dependency's item is named by its Cargo package name with `-` written `_`, never by a name a depending package's manifest renames it to or a library name its `[lib]` section gives it; did you mean `{accepted}`?"
        )),
        "{}",
        stderr(&refused)
    );
    let stopped = run(accepted);
    assert_eq!(stopped.status.code(), Some(0), "{}", stderr(&stopped));
    assert!(
        stderr(&stopped).contains(&format!(
            "krs run: stopped after 0 steps, before `{accepted}` (stop 1 of 1)"
        )),
        "{}\n{}",
        stdout(&stopped),
        stderr(&stopped)
    );
}
