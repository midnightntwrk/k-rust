//! `krs run` on a definition that declares ends (`#[k::end(finished)]`, `#[k::end(refused)]`):
//! a run that ends where no rule applies reports the declared class of its end, and a run of a
//! definition that declares none says what it said before.
//!
//! The fixture is a machine of one statement with an exit cell. Its declared ends are `halt`
//! and an empty computation (`finished`), `trap CODE` and a `quit CODE` above 9 (`refused`,
//! with the statement and the code as their reasons), `wait N` where a function that never
//! ends is true (which no budget decides), and `both` twice, once in each class.
//! `rest` has no rule and no declared end, and `lose 1` has no value.
//!
//! The classes are evaluated only where no rule applies: a state a step bound or a stop ended
//! the run at has none, whatever a declared end's function would say of it.

use std::fmt::Write as _;
use std::fs;
use std::path::Path;
use std::process::Output;
use std::sync::OnceLock;

use krs_test_support::{
    SharedFixtureTarget, TempDir, fixture_build_env, krs_command, shared_fixture_target, temp_dir,
};
use serde_json::{Value as Json, json};

const ENDS: &str = r"
/// `halt`: the program asks to stop.
#[k::end(finished)]
pub fn halted(
    k::cells! {
        k: k::configuration::KCell(StmtSyntax::Halt(), ..),
        ..
    }: Machine,
) {
}

/// Nothing is left to compute.
#[k::end(finished)]
pub fn drained(
    k::cells! {
        k: k::configuration::KCell(),
        ..
    }: Machine,
) {
}

/// A status above 9 is refused, with the status.
#[k::end(refused)]
#[k::requires(code > 9)]
pub fn too_big(
    code: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(StmtSyntax::Quit { code }, ..),
        ..
    }: Machine,
) -> Term<Int> {
    code
}

/// A wait ends where `Rise` is true, which its evaluation never decides.
#[k::end(finished)]
#[k::requires(Rise(n))]
pub fn waited(
    n: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(StmtSyntax::Wait { n }, ..),
        ..
    }: Machine,
) {
}

/// `both` is declared finished.
#[k::end(finished)]
pub fn both_finished(
    k::cells! {
        k: k::configuration::KCell(StmtSyntax::Both(), ..),
        ..
    }: Machine,
) {
}

/// `both` is declared refused too, which contradicts `both_finished`.
#[k::end(refused)]
pub fn both_refused(
    count: Term<Int>,
    k::cells! {
        k: k::configuration::KCell(StmtSyntax::Both(), ..),
        count: k::configuration::Cell(count),
        ..
    }: Machine,
) -> Term<Int> {
    count
}
";

const FIXTURE: &str = r#"
use k::builtin::{Bool, Int, KSequence};
use k::{KResult, Term};

k::sorts! {
    Stmt;
}

#[k::constructors(sort = Stmt, result = KResult)]
pub enum StmtSyntax {
    #[k::syntax("quit {code}")]
    Quit { code: Int },
    #[k::syntax("tick")]
    Tick(),
    #[k::syntax("lose {n}")]
    Lose { n: Int },
    #[k::syntax("rest")]
    Rest(),
    #[k::syntax("halt")]
    Halt(),
    /*TRAP*/
    #[k::syntax("trap {code}")]
    Trap { code: Int },
    #[k::syntax("fault {code}")]
    Fault { code: Int },
    #[k::syntax("wait {n}")]
    Wait { n: Int },
    #[k::syntax("both")]
    Both(),
}

/// `1` at `0`, and no value elsewhere.
#[k::function(partial, internal)]
#[k::requires(n.eq::<Int>(0))]
pub fn OnlyZero(n: k::Term<Int>) -> k::Term<Int> {
    1
}

/// `Rise(n + 1)`, for ever.
#[k::function(total, internal)]
pub fn Rise(n: Term<Int>) -> Term<Bool> {
    Rise(n + 1)
}

k::rules! {
    for Machine;
    use StmtSyntax::*;

    #[k::requires(code <= 9)]
    quit: { k: [Quit { code }, ..], status: _ } => { k: [..], status: code };
    tick: { k: [Tick(), ..], count } => { k: [Tick(), ..], count: count + 1 };
    lose: { k: [Lose { n }, ..], count: _ } => { k: [..], count: OnlyZero(n) };
    fault: { k: [Fault { code }, ..] } => { k: [Trap { code }, ..] };
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub count: Int,
    #[k::cell(exit)]
    pub status: Int,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self { k: k::k![pgm], count: 0, status: 0 }
    }
}
"#;

const DECLARING: &str = "krs-cli-declared-ends-fixture";
const PLAIN: &str = "krs-cli-no-declared-ends-fixture";

/// The fixture as two packages built once per test process: one that declares the ends, and
/// one of the same rules that declares none.
struct Project {
    directory: TempDir,
    target: SharedFixtureTarget,
}

fn project() -> &'static Project {
    static PROJECT: OnceLock<Project> = OnceLock::new();
    PROJECT.get_or_init(|| {
        let target = shared_fixture_target();
        let directory = temp_dir();
        let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../krs")
            .canonicalize()
            .unwrap();
        let krs_literal = serde_json::to_string(krs.to_str().unwrap()).unwrap();
        for (member, package, namespace, source) in [
            (
                "declaring",
                DECLARING,
                "ORG-KRS-CLI-DECLARED-ENDS",
                format!(
                    "{}{ENDS}",
                    FIXTURE.replace("/*TRAP*/", "#[k::end(refused)]")
                ),
            ),
            (
                "plain",
                PLAIN,
                "ORG-KRS-CLI-NO-DECLARED-ENDS",
                FIXTURE.replace("/*TRAP*/", ""),
            ),
        ] {
            let root = directory.path().join(member);
            fs::create_dir_all(root.join("src")).unwrap();
            fs::write(root.join("src/lib.rs"), source).unwrap();
            fs::write(
                root.join("Cargo.toml"),
                format!(
                    "[package]\nname = \"{package}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {krs_literal} }}\n\n[package.metadata.krs]\nk-namespace = \"{namespace}\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\n"
                ),
            )
            .unwrap();
        }
        Project { directory, target }
    })
}

/// `krs run PROGRAM ARGUMENTS` on the package `package` in `member`, `PROGRAM` the text of a
/// file.
fn run_in(member: &str, package: &str, name: &str, program: &str, arguments: &[&str]) -> Output {
    let project = project();
    let root = project.directory.path().join(member);
    let file = root.join(format!("{name}.pgm"));
    fs::write(&file, program).unwrap();
    let mut process = krs_command!();
    fixture_build_env(&mut process, project.target.path());
    process
        .current_dir(&root)
        .arg("run")
        .arg(&file)
        .args(["--package", package, "--definition", "main"])
        .args(arguments)
        .output()
        .unwrap()
}

/// `krs VERB --package PACKAGE --definition main ARGUMENTS` in `member`, after writing each of
/// `files` (a name and its text) there.
fn krs_in(
    member: &str,
    package: &str,
    verb: &str,
    files: &[(&str, &str)],
    arguments: &[&str],
) -> Output {
    let project = project();
    let root = project.directory.path().join(member);
    for (name, text) in files {
        fs::write(root.join(name), text).unwrap();
    }
    let mut process = krs_command!();
    fixture_build_env(&mut process, project.target.path());
    process
        .current_dir(&root)
        .arg(verb)
        .args(["--package", package, "--definition", "main"])
        .args(arguments)
        .output()
        .unwrap()
}

/// `krs VERB` on the definition that declares ends.
fn krs(verb: &str, files: &[(&str, &str)], arguments: &[&str]) -> Output {
    krs_in("declaring", DECLARING, verb, files, arguments)
}

/// A named case of the program `program`, its `expect` table `expect` when not empty.
fn named_case(name: &str, program: &str, expect: &str) -> String {
    let mut case =
        format!("[[case]]\nname = \"{name}\"\ninputs.pgm = {{ \"$text\" = \"{program}\" }}\n");
    if !expect.is_empty() {
        let _ = writeln!(case, "expect = {{ {expect} }}");
    }
    case
}

/// `krs run` on the definition that declares ends.
fn run(name: &str, program: &str, arguments: &[&str]) -> Output {
    run_in("declaring", DECLARING, name, program, arguments)
}

/// `krs run --case` on the definition that declares ends, the case document `case`.
fn run_case(name: &str, case: &str, arguments: &[&str]) -> Output {
    let project = project();
    let root = project.directory.path().join("declaring");
    let file = root.join(format!("{name}.toml"));
    fs::write(&file, case).unwrap();
    let mut process = krs_command!();
    fixture_build_env(&mut process, project.target.path());
    process
        .current_dir(&root)
        .arg("run")
        .args(["--package", DECLARING, "--definition", "main"])
        .arg("--case")
        .arg(&file)
        .args(arguments)
        .output()
        .unwrap()
}

fn text(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).into_owned()
}

/// The last line `krs run` wrote on standard error that is its status line.
fn status_line(output: &Output) -> String {
    text(&output.stderr)
        .lines()
        .rfind(|line| line.starts_with("krs run: "))
        .unwrap_or_default()
        .to_owned()
}

/// The `run` member of the JSON report of a run, which is `krs-exec/8`.
fn report(name: &str, program: &str, arguments: &[&str]) -> (Option<i32>, Json) {
    let mut all = arguments.to_vec();
    all.extend(["--output", "json"]);
    let output = run(name, program, &all);
    let document: Json = serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|error| panic!("{name}: {error}: {}", text(&output.stderr)));
    assert_eq!(document["schema"], "krs-exec/8", "{name}");
    (output.status.code(), document["run"].clone())
}

/// Each way a run of the declaring definition ends: its status line and its exit status, the
/// same whether or not the end's pattern is built.
#[test]
fn a_run_reports_the_class_of_its_end_in_its_status_line_and_status() {
    let cases: [(&str, &str, &[&str], &str, i32); 12] = [
        // A finished end by a constructor's item, at the initial state.
        (
            "halt",
            "halt",
            &[],
            "krs run: finished after 0 steps, at `crate::halted`; <k> starts with `halt`",
            0,
        ),
        // A finished end after a step, whose status is the exit cell's value.
        (
            "quit",
            "quit 3",
            &[],
            "krs run: finished after 1 step, at `crate::drained`; <k> is empty",
            3,
        ),
        // A refused end after a step: the reason is the statement, and the status is 0.
        (
            "fault",
            "fault 7",
            &[],
            "krs run: refused after 1 step, at `crate::trap`: `trap 7`; <k> starts with `trap 7`",
            0,
        ),
        // A refused end at the initial state: a refusal of the input, after no step.
        (
            "refused-input",
            "quit 12",
            &[],
            "krs run: refused after 0 steps, at `crate::too_big`: `12`; <k> starts with `quit 12`",
            0,
        ),
        // No rule and no declared end: a gap, which is a finding.
        (
            "gap",
            "rest",
            &[],
            "krs run: stuck after 0 steps, at no declared end; <k> starts with `rest`",
            1,
        ),
        // No state, so no class; a definition that declares ends does not account for it.
        (
            "undefined",
            "lose 1",
            &[],
            "krs run: undefined after 0 steps; <k> starts with `lose 1`",
            1,
        ),
        (
            "defined",
            "lose 0",
            &[],
            "krs run: finished after 1 step, at `crate::drained`; <k> is empty",
            0,
        ),
        // A step bound ends the run at a state not known to be an end: no class.
        (
            "depth-bound",
            "tick",
            &["--depth", "5"],
            "krs run: depth-bound after 5 steps; <k> starts with `tick`",
            0,
        ),
        // Also where a declared end's function would be true of the state.
        (
            "depth-zero",
            "halt",
            &["--depth", "0"],
            "krs run: depth-bound after 0 steps; <k> starts with `halt`",
            0,
        ),
        (
            "stop-before",
            "fault 7",
            &["--stop-before", "fault"],
            "krs run: stopped after 0 steps, before `crate::fault` (stop 1 of 1)",
            0,
        ),
        (
            "stop-after",
            "fault 7",
            &["--stop-after", "fault"],
            "krs run: stopped after 1 step, after `crate::fault` (stop 1 of 1)",
            0,
        ),
        // An end whose function no budget decides: the class is not known.
        (
            "undecided",
            "wait 1",
            &["--view-budget", "100"],
            "krs run: end-undecided after 0 steps, undecided whether the declared end `crate::waited` holds: the evaluation of whether it holds stopped before it ended (it spent its budget of 100 polls); a larger --view-budget can decide it; <k> starts with `wait 1`",
            3,
        ),
    ];
    for (name, program, arguments, status, code) in cases {
        let mut unbuilt = arguments.to_vec();
        unbuilt.extend(["--output", "none"]);
        let mut built = arguments.to_vec();
        built.extend(["--output", "pretty"]);
        let none = run(name, program, &unbuilt);
        let pretty = run(name, program, &built);
        assert_eq!(status_line(&none), status, "{name}: {}", text(&none.stderr));
        assert_eq!(text(&none.stderr), text(&pretty.stderr), "{name}");
        assert_eq!(none.status.code(), Some(code), "{name}");
        assert_eq!(pretty.status.code(), Some(code), "{name}");
        assert!(text(&none.stdout).is_empty(), "{name}");
    }
}

/// The JSON report states the class beside the halt, which stays the mechanical fact, and a run
/// a bound or a stop ended states none.
#[test]
fn the_json_report_states_the_class_of_the_end() {
    let (status, finished) = report("json-quit", "quit 3", &[]);
    assert_eq!(status, Some(3));
    assert_eq!(finished["halt"], "stuck");
    assert_eq!(
        finished["end"],
        json!({"class": "finished", "item": "crate::drained"})
    );

    let (status, refused) = report("json-refused", "quit 12", &[]);
    assert_eq!(status, Some(0));
    assert_eq!(refused["halt"], "stuck");
    assert_eq!(refused["steps"], 0);
    assert_eq!(
        refused["end"],
        json!({"class": "refused", "item": "crate::too_big", "reason": 12, "reason_text": "12"})
    );

    let (status, trapped) = report("json-fault", "fault 7", &[]);
    assert_eq!(status, Some(0));
    assert_eq!(trapped["end"]["class"], "refused");
    assert_eq!(trapped["end"]["item"], "crate::trap");
    assert_eq!(trapped["end"]["reason_text"], "trap 7");
    assert_eq!(trapped["end"]["reason"], json!({"Trap": {"code": 7}}));

    let (status, gap) = report("json-gap", "rest", &[]);
    assert_eq!(status, Some(1));
    assert_eq!(gap["halt"], "stuck");
    assert_eq!(gap["end"], json!({"class": "none"}));

    for (name, program, arguments) in [
        ("json-depth", "halt", &["--depth", "0"][..]),
        ("json-stop", "fault 7", &["--stop-before", "fault"][..]),
        ("json-undefined", "lose 1", &[][..]),
    ] {
        let (_, bounded) = report(name, program, arguments);
        assert_eq!(bounded.get("end"), None, "{name}: {bounded}");
        assert_eq!(bounded.get("end_undecided"), None, "{name}");
    }

    let (status, undecided) = report("json-undecided", "wait 1", &["--view-budget", "100"]);
    assert_eq!(status, Some(3));
    assert_eq!(undecided["halt"], "end-undecided");
    assert_eq!(undecided.get("end"), None);
    assert_eq!(undecided["end_undecided"]["item"], "crate::waited");
    assert_eq!(undecided["end_undecided"]["budget_spent"], true);
}

/// The end document states the class, the end and the reason, and reads back as an expectation
/// the run meets.
#[test]
fn the_end_document_states_the_class_and_reads_back() {
    let documents = [
        (
            "end-refused",
            "quit 12",
            json!({"halt": "stuck", "class": "refused", "end": "crate::too_big", "reason": 12}),
            0,
        ),
        (
            "end-finished",
            "quit 3",
            json!({"halt": "stuck", "class": "finished", "end": "crate::drained"}),
            3,
        ),
        (
            "end-gap",
            "rest",
            json!({"halt": "stuck", "class": "none"}),
            1,
        ),
        ("end-depth", "tick", json!({"halt": "depth-bound"}), 0),
    ];
    for (name, program, stated, code) in documents {
        let arguments: &[&str] = if name == "end-depth" {
            &["--depth", "2", "--output", "end"]
        } else {
            &["--output", "end"]
        };
        let output = run(name, program, arguments);
        assert_eq!(output.status.code(), Some(code), "{name}");
        let mut document: Json = serde_json::from_slice(&output.stdout).unwrap();
        let cells = document
            .as_object_mut()
            .unwrap()
            .remove("cells")
            .unwrap_or_else(|| panic!("{name}: no cells"));
        assert_eq!(document, stated, "{name}");
        if name == "end-depth" {
            continue;
        }
        // The document, with its cells, is an expectation the same run meets.
        let mut expect = stated.clone();
        expect["cells"] = cells;
        let case = format!(
            "inputs.pgm = {{ \"$text\" = \"{program}\" }}\n\n[expect]\n{}",
            toml_table(&expect)
        );
        let checked = run_case(name, &case, &["--output", "none"]);
        assert_eq!(
            checked.status.code(),
            Some(0),
            "{name}: {}",
            text(&checked.stderr)
        );
    }
}

/// A flat JSON object of strings and numbers, and its `cells` table, as TOML keys.
fn toml_table(object: &Json) -> String {
    object
        .as_object()
        .unwrap()
        .iter()
        .map(|(key, value)| format!("{key} = {}", toml_value(value)))
        .collect::<Vec<_>>()
        .join("\n")
        + "\n"
}

fn toml_value(value: &Json) -> String {
    match value {
        Json::Object(object) => format!(
            "{{ {} }}",
            object
                .iter()
                .map(|(key, value)| format!("{} = {}", Json::from(key.as_str()), toml_value(value)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Json::Array(items) => format!(
            "[{}]",
            items.iter().map(toml_value).collect::<Vec<_>>().join(", ")
        ),
        other => other.to_string(),
    }
}

/// An expectation narrows by what it states of the class: `halt = "stuck"` alone is met by an
/// end of any class, and `class`, `end` and `reason` are each compared when stated.
#[test]
fn an_expectation_is_compared_on_the_class_it_states() {
    let case = |program: &str, expect: &str| {
        format!(
            "inputs.pgm = {{ \"$text\" = \"{program}\" }}\n\n[expect]\nhalt = \"stuck\"\ncompare = [\"count\"]\ncells = {{ count = 0 }}\n{expect}"
        )
    };
    let cases = [
        ("any-refused", "quit 12", "", 0, ""),
        ("any-gap", "rest", "", 0, ""),
        ("class-met", "quit 12", "class = \"refused\"\n", 0, ""),
        (
            "class-unmet",
            "quit 12",
            "class = \"finished\"\n",
            1,
            "expected: stuck, class finished\n  actual:   stuck, class refused\n",
        ),
        ("gap-met", "rest", "class = \"none\"\n", 0, ""),
        (
            "gap-unmet",
            "rest",
            "class = \"finished\"\n",
            1,
            "expected: stuck, class finished\n  actual:   stuck, class none\n",
        ),
        ("end-met", "quit 3", "end = \"crate::drained\"\n", 0, ""),
        (
            "end-unmet",
            "halt",
            "end = \"crate::drained\"\n",
            1,
            "expected: stuck, at `crate::drained`\n  actual:   stuck, at `crate::halted`\n",
        ),
        (
            "reason-met",
            "quit 12",
            "end = \"crate::too_big\"\nreason = 12\n",
            0,
            "",
        ),
        (
            "reason-unmet",
            "quit 12",
            "end = \"crate::too_big\"\nreason = 13\n",
            1,
            "expected: stuck, at `crate::too_big`, reason `13`\n  actual:   stuck, at `crate::too_big`, reason `12`\n",
        ),
    ];
    for (name, program, expect, code, shown) in cases {
        let output = run_case(name, &case(program, expect), &["--output", "none"]);
        let stderr = text(&output.stderr);
        assert_eq!(output.status.code(), Some(code), "{name}: {stderr}");
        assert!(stderr.contains(shown), "{name}: {stderr}");
        if code == 1 {
            assert!(stderr.contains("at the end's halt"), "{name}: {stderr}");
        }
    }
    // A run a step bound ended has no end the definition reaches, whatever class is expected.
    let bounded = "inputs.pgm = { \"$text\" = \"halt\" }\nrun.depth = 0\n\n[expect]\nhalt = \"stuck\"\nclass = \"finished\"\ncompare = [\"count\"]\ncells = { count = 0 }\n";
    let output = run_case("bounded", bounded, &["--output", "none"]);
    assert_eq!(output.status.code(), Some(3), "{}", text(&output.stderr));
}

/// An expectation that states a class the end document does not allow is refused before the
/// run.
#[test]
fn an_expectation_s_class_is_checked_against_the_declarations() {
    let case = |expect: &str| {
        format!(
            "inputs.pgm = {{ \"$text\" = \"halt\" }}\n\n[expect]\n{expect}compare = [\"count\"]\ncells = {{ count = 0 }}\n"
        )
    };
    let refusals = [
        (
            "word",
            "halt = \"stuck\"\nclass = \"done\"\n",
            "`done` is no class of an end; an end is finished, refused, or none",
        ),
        (
            "item",
            "halt = \"stuck\"\nend = \"crate::nowhere\"\n",
            "`crate::nowhere` is no declared end of the definition; its declared ends are `crate::both_finished`, `crate::both_refused`, `crate::drained`, `crate::halted`, `crate::too_big`, `crate::trap`, `crate::waited`",
        ),
        (
            "disagree",
            "halt = \"stuck\"\nclass = \"finished\"\nend = \"crate::too_big\"\n",
            "`crate::too_big` is a `refused` end, and the document states the class `finished`",
        ),
        (
            "reason-of-finished",
            "halt = \"stuck\"\nend = \"crate::drained\"\nreason = 1\n",
            "`crate::drained` is a finished end, and only a refused end has a reason",
        ),
        (
            "reason-without-end",
            "halt = \"stuck\"\nreason = 1\n",
            "the definition's refused ends do not share one reason type",
        ),
        (
            "stopped",
            "halt = \"stopped\"\nrule = \"fault\"\nclass = \"finished\"\n",
            "only a `stuck` end has a declared class",
        ),
    ];
    for (name, expect, message) in refusals {
        let output = run_case(name, &case(expect), &["--output", "none"]);
        let stderr = text(&output.stderr);
        assert_eq!(output.status.code(), Some(2), "{name}: {stderr}");
        assert!(stderr.contains(message), "{name}: {stderr}");
    }
}

/// A state at which a finished end and a refused end both hold is a contradiction of the
/// definition, which the run refuses.
#[test]
fn ends_of_both_classes_at_one_state_refuse_the_run() {
    let output = run("both", "both", &["--output", "none"]);
    let stderr = text(&output.stderr);
    assert_eq!(output.status.code(), Some(2), "{stderr}");
    assert!(
        stderr.contains("error[krs::exec::end-classes-overlap]: after 0 steps the run ended where no rule applies, at a state where the declared ends `crate::both_finished` (finished) and `crate::both_refused` (refused) both hold"),
        "{stderr}"
    );
}

/// The definition of the same rules that declares no end: the status lines, the statuses and the
/// run document of `krs-exec/7`, with no `end`, and an end document that states no class and
/// refuses one.
#[test]
fn a_definition_that_declares_no_end_says_what_it_said() {
    let plain = |name: &str, program: &str, arguments: &[&str]| {
        run_in("plain", PLAIN, name, program, arguments)
    };
    let cases: [(&str, &str, &[&str], &str, i32); 6] = [
        (
            "halt",
            "halt",
            &[],
            "krs run: stuck after 0 steps; <k> starts with `halt`",
            0,
        ),
        (
            "quit",
            "quit 3",
            &[],
            "krs run: stuck after 1 step; <k> is empty",
            3,
        ),
        (
            "fault",
            "fault 7",
            &[],
            "krs run: stuck after 1 step; <k> starts with `trap 7`",
            0,
        ),
        (
            "rest",
            "rest",
            &[],
            "krs run: stuck after 0 steps; <k> starts with `rest`",
            0,
        ),
        (
            "undefined",
            "lose 1",
            &[],
            "krs run: undefined after 0 steps; <k> starts with `lose 1`",
            0,
        ),
        (
            "depth-bound",
            "tick",
            &["--depth", "5"],
            "krs run: depth-bound after 5 steps; <k> starts with `tick`",
            0,
        ),
    ];
    for (name, program, arguments, status, code) in cases {
        let mut all = arguments.to_vec();
        all.extend(["--output", "none"]);
        let output = plain(name, program, &all);
        assert_eq!(status_line(&output), status, "{name}");
        assert_eq!(output.status.code(), Some(code), "{name}");
    }
    let output = plain("json", "rest", &["--output", "json"]);
    let document: Json = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(document["schema"], "krs-exec/7");
    assert_eq!(document["run"]["halt"], "stuck");
    assert_eq!(document["run"].get("end"), None);
    let output = plain("end", "rest", &["--output", "end"]);
    let document: Json = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(document["halt"], "stuck");
    assert_eq!(document.get("class"), None);

    let project = project();
    let root = project.directory.path().join("plain");
    let file = root.join("class.toml");
    fs::write(
        &file,
        "inputs.pgm = { \"$text\" = \"rest\" }\n\n[expect]\nhalt = \"stuck\"\nclass = \"none\"\ncompare = [\"count\"]\ncells = { count = 0 }\n",
    )
    .unwrap();
    let mut process = krs_command!();
    fixture_build_env(&mut process, project.target.path());
    let output = process
        .current_dir(&root)
        .arg("run")
        .args(["--package", PLAIN, "--definition", "main", "--case"])
        .arg(&file)
        .output()
        .unwrap();
    let stderr = text(&output.stderr);
    assert_eq!(output.status.code(), Some(2), "{stderr}");
    assert!(
        stderr.contains(
            "`class` states the declared class of an end, and the definition declares no end"
        ),
        "{stderr}"
    );
}

/// `krs cases` answers a case of a declaring definition as `krs run` answers its run: a case that
/// states no expectation and ends at a declared end, finished or refused, ran to an end; one that
/// ends in no declared end, at a gap or `undefined`, is a finding; one whose end is left undecided
/// is no answer; and an expectation's verdict replaces all of these.
/// Each record names the class of its end as `krs run`'s status line does.
#[test]
fn a_batch_answers_each_case_as_krs_run_answers_its_run() {
    let ended = [
        named_case("finished", "quit 3", ""),
        named_case("refused", "fault 7", ""),
        named_case("refused-input", "quit 12", ""),
    ]
    .concat();
    let output = krs(
        "cases",
        &[("ended.toml", &ended)],
        &["ended.toml", "--jobs", "1"],
    );
    assert_eq!(output.status.code(), Some(0), "{}", text(&output.stderr));
    assert_eq!(
        text(&output.stdout),
        "ended.toml#finished: ran, finished after 1 step, at `crate::drained`\n\
         ended.toml#refused: ran, refused after 1 step, at `crate::trap`: `trap 7`\n\
         ended.toml#refused-input: ran, refused after 0 steps, at `crate::too_big`: `12`\n\
         krs cases: 3 cases: 0 met, 0 unmet, 0 inconclusive, 0 refused, 3 ran (0 at no declared end)\n"
    );
    batch_of_every_end(&ended);
}

/// A batch of a case of each kind of end, `ended` and the others: a gap and an undefined end
/// are findings, so the batch exits 1, and its records name each end's class.
fn batch_of_every_end(ended: &str) {
    let all = [
        ended.to_owned(),
        named_case("gap", "rest", ""),
        named_case("undefined", "lose 1", ""),
        named_case("undecided", "wait 1", ""),
        named_case(
            "gap-expected",
            "rest",
            "halt = \"stuck\", compare = [\"count\"], cells = { count = 0 }",
        ),
        named_case(
            "gap-stated",
            "rest",
            "halt = \"stuck\", class = \"none\", compare = [\"count\"], cells = { count = 0 }",
        ),
        named_case(
            "class-unmet",
            "quit 12",
            "halt = \"stuck\", class = \"finished\", compare = [\"count\"], cells = { count = 0 }",
        ),
    ]
    .concat();
    let files = [("all.toml", all.as_str())];
    let arguments = ["all.toml", "--jobs", "2", "--view-budget", "100"];
    let output = krs("cases", &files, &arguments);
    let stdout = text(&output.stdout);
    assert_eq!(output.status.code(), Some(1), "{}", text(&output.stderr));
    for line in [
        "all.toml#gap: ran, stuck after 0 steps, at no declared end\n",
        "all.toml#undefined: ran, undefined after 0 steps\n",
        "all.toml#undecided: ran, end-undecided after 0 steps, undecided whether the declared end `crate::waited` holds: the evaluation of whether it holds stopped before it ended (it spent its budget of 100 polls); a larger --view-budget can decide it\n",
        "all.toml#gap-expected: expectation met\n",
        "all.toml#gap-stated: expectation met\n",
        "krs cases: 9 cases: 2 met, 1 unmet, 0 inconclusive, 0 refused, 6 ran (2 at no declared end)\n",
    ] {
        assert!(stdout.contains(line), "{line}\n{stdout}");
    }
    assert!(
        stdout.contains("expected: stuck, class finished\n  actual:   stuck, class refused\n"),
        "{stdout}"
    );
    let mut json_arguments = arguments.to_vec();
    json_arguments.extend(["--output", "json"]);
    json_records_of_every_end(&files, &json_arguments);
}

/// The JSON records of [`batch_of_every_end`]'s batch: `krs-cases/5`, each carrying the class
/// of its end as `krs run --output json` does, and a summary that counts `undeclared`.
fn json_records_of_every_end(files: &[(&str, &str)], json_arguments: &[&str]) {
    let output = krs("cases", files, json_arguments);
    assert_eq!(output.status.code(), Some(1), "{}", text(&output.stderr));
    let records = text(&output.stdout)
        .lines()
        .map(|line| serde_json::from_str::<Json>(line).unwrap())
        .collect::<Vec<_>>();
    assert!(
        records
            .iter()
            .all(|record| record["schema"] == "krs-cases/5"),
        "{records:?}"
    );
    let record = |name: &str| {
        records
            .iter()
            .find(|record| record["case"] == format!("all.toml#{name}"))
            .unwrap_or_else(|| panic!("{name}: {records:?}"))
    };
    assert_eq!(
        record("finished")["end"],
        json!({"class": "finished", "item": "crate::drained"})
    );
    assert_eq!(
        record("refused-input")["end"],
        json!({"class": "refused", "item": "crate::too_big", "reason": 12, "reason_text": "12"})
    );
    assert_eq!(record("gap")["verdict"], "ran");
    assert_eq!(record("gap")["halt"], "stuck");
    assert_eq!(record("gap")["end"], json!({"class": "none"}));
    assert_eq!(record("undefined")["halt"], "undefined");
    assert_eq!(record("undefined").get("end"), None);
    assert_eq!(record("undecided")["halt"], "end-undecided");
    assert_eq!(record("undecided").get("end"), None);
    assert_eq!(
        record("undecided")["end_undecided"]["item"],
        "crate::waited"
    );
    assert_eq!(record("undecided")["end_undecided"]["budget_spent"], true);
    assert_eq!(record("gap-expected")["verdict"], "met");
    assert_eq!(record("gap-expected")["end"], json!({"class": "none"}));
    assert_eq!(record("class-unmet")["verdict"], "unmet");
    let summary = records.last().unwrap();
    assert_eq!(
        summary["summary"],
        json!({"cases": 9, "met": 2, "unmet": 1, "inconclusive": 0, "refused": 0, "ran": 6, "undeclared": 2})
    );
    assert_eq!(summary["status"], 1);
}

/// An end left undecided is no answer, and ends of both classes at one state refuse the case,
/// as they refuse the run.
#[test]
fn a_case_is_unanswered_at_an_undecided_end_and_refused_at_overlapping_ends() {
    // An end left undecided, alone, is no answer.
    let undecided = named_case("undecided", "wait 1", "");
    let output = krs(
        "cases",
        &[("undecided.toml", &undecided)],
        &["undecided.toml", "--view-budget", "100"],
    );
    assert_eq!(output.status.code(), Some(3), "{}", text(&output.stdout));

    // Ends of both classes at one state refuse the case, as they refuse the run.
    let both = named_case("both", "both", "");
    let output = krs("cases", &[("both.toml", &both)], &["both.toml"]);
    assert_eq!(output.status.code(), Some(2), "{}", text(&output.stdout));
    assert!(
        text(&output.stdout).contains("both.toml#both: refused: after 0 steps the run ended where no rule applies, at a state where the declared ends `crate::both_finished` (finished) and `crate::both_refused` (refused) both hold"),
        "{}",
        text(&output.stdout)
    );
}

/// A batch of the definition that declares no end keeps its version, its records and its summary.
#[test]
fn a_batch_of_a_definition_that_declares_no_end_says_what_it_said() {
    let cases = [
        named_case("rest", "rest", ""),
        named_case("lose", "lose 1", ""),
    ]
    .concat();
    let files = [("plain.toml", cases.as_str())];
    let output = krs_in(
        "plain",
        PLAIN,
        "cases",
        &files,
        &["plain.toml", "--jobs", "1"],
    );
    assert_eq!(output.status.code(), Some(0), "{}", text(&output.stderr));
    assert_eq!(
        text(&output.stdout),
        "plain.toml#rest: ran, stuck after 0 steps\n\
         plain.toml#lose: ran, undefined after 0 steps\n\
         krs cases: 2 cases: 0 met, 0 unmet, 0 inconclusive, 0 refused, 2 ran\n"
    );
    let output = krs_in(
        "plain",
        PLAIN,
        "cases",
        &files,
        &["plain.toml", "--jobs", "1", "--output", "json"],
    );
    assert_eq!(
        text(&output.stdout),
        "{\"case\":\"plain.toml#rest\",\"halt\":\"stuck\",\"schema\":\"krs-cases/4\",\"steps\":0,\"verdict\":\"ran\"}\n\
         {\"case\":\"plain.toml#lose\",\"halt\":\"undefined\",\"schema\":\"krs-cases/4\",\"steps\":0,\"verdict\":\"ran\"}\n\
         {\"schema\":\"krs-cases/4\",\"status\":0,\"summary\":{\"cases\":2,\"inconclusive\":0,\"met\":0,\"ran\":2,\"refused\":0,\"unmet\":0}}\n"
    );
}

/// `krs compare` compares two sides on what both state of the declared class, as an expectation
/// is compared on what it states: an end document that states only its halt is compared with a
/// run's end of any class on its halt and cells, and two ends that both state a class differ
/// where the classes do.
#[test]
fn compare_narrows_the_declared_class_to_what_both_sides_state() {
    let cases = [
        named_case("refused", "quit 12", ""),
        named_case("finished", "halt", ""),
        named_case("gap", "rest", ""),
    ]
    .concat();
    // Each document states its halt, its count, and the parts of the class shown.
    let documents = [
        ("stuck.json", json!({})),
        ("class-refused.json", json!({"class": "refused"})),
        ("class-finished.json", json!({"class": "finished"})),
        ("end-too-big.json", json!({"end": "crate::too_big"})),
        (
            "reason-13.json",
            json!({"end": "crate::too_big", "reason": 13}),
        ),
        ("class-none.json", json!({"class": "none"})),
    ]
    .map(|(name, mut document)| {
        document["halt"] = json!("stuck");
        document["cells"] = json!({"count": 0});
        (name, document.to_string())
    });
    let mut files = documents
        .iter()
        .map(|(name, text)| (*name, text.as_str()))
        .collect::<Vec<_>>();
    files.push(("sides.toml", &cases));
    let comparisons = [
        // No class stated: compared on the halt and the cells alone.
        ("stuck.json", "sides.toml#refused", 0, ""),
        ("stuck.json", "sides.toml#finished", 0, ""),
        ("stuck.json", "sides.toml#gap", 0, ""),
        ("sides.toml#gap", "stuck.json", 0, ""),
        ("stuck.json", "class-finished.json", 0, ""),
        // A stated class is compared with the run's.
        ("class-refused.json", "sides.toml#refused", 0, ""),
        (
            "class-finished.json",
            "sides.toml#refused",
            1,
            "  left:  stuck, class finished\n  right: stuck, class refused, reason `12`\n",
        ),
        ("class-finished.json", "sides.toml#finished", 0, ""),
        ("class-none.json", "sides.toml#gap", 0, ""),
        (
            "class-none.json",
            "sides.toml#finished",
            1,
            "  left:  stuck, class none\n  right: stuck, class finished, at `crate::halted`\n",
        ),
        // A stated end and reason likewise.
        ("end-too-big.json", "sides.toml#refused", 0, ""),
        (
            "reason-13.json",
            "sides.toml#refused",
            1,
            "  left:  stuck, at `crate::too_big`, reason `13`\n  right: stuck, at `crate::too_big`, reason `12`\n",
        ),
        // Two documents that state different classes differ.
        (
            "class-refused.json",
            "class-finished.json",
            1,
            "  left:  stuck, class refused\n  right: stuck, class finished\n",
        ),
        // One states its class, the other its end: compared on neither part.
        ("class-finished.json", "end-too-big.json", 0, ""),
        // Two runs of different classes differ.
        (
            "sides.toml#refused",
            "sides.toml#finished",
            1,
            "  left:  stuck, class refused, at `crate::too_big`, reason `12`\n  right: stuck, class finished, at `crate::halted`\n",
        ),
    ];
    for (left, right, code, shown) in comparisons {
        let output = krs("compare", &files, &[left, right, "--compare", "count"]);
        let stderr = text(&output.stderr);
        let stdout = text(&output.stdout);
        assert_eq!(
            output.status.code(),
            Some(code),
            "{left} {right}: {stdout}{stderr}"
        );
        if code == 0 {
            assert_eq!(stdout, "krs compare: equal\n", "{left} {right}: {stderr}");
        } else {
            assert!(
                stdout.contains("at the end's halt") && stdout.contains(shown),
                "{left} {right}: {stdout}{stderr}"
            );
        }
    }
}

/// `krs compare --expect` checks an end against an expectation's class as `krs run --case` does,
/// and refuses an end document that does not state a part of the class the expectation states,
/// as it refuses one that does not state a compared cell.
#[test]
fn compare_checks_an_end_against_the_class_an_expectation_states() {
    let expected = [
        named_case(
            "refused",
            "quit 12",
            "halt = \"stuck\", class = \"refused\", compare = [\"count\"], cells = { count = 0 }",
        ),
        named_case(
            "any",
            "quit 12",
            "halt = \"stuck\", compare = [\"count\"], cells = { count = 0 }",
        ),
    ]
    .concat();
    let stuck = json!({"halt": "stuck", "cells": {"count": 0}}).to_string();
    let finished = json!({"halt": "stuck", "class": "finished", "cells": {"count": 0}}).to_string();
    let stopped =
        json!({"halt": "stopped", "rule": "crate::fault", "cells": {"count": 0}}).to_string();
    let files = [
        ("expected.toml", expected.as_str()),
        ("stuck.json", stuck.as_str()),
        ("finished.json", finished.as_str()),
        ("stopped.json", stopped.as_str()),
    ];
    let checks = [
        ("expected.toml#any", "stuck.json", 0),
        ("expected.toml#any", "finished.json", 0),
        ("expected.toml#refused", "finished.json", 1),
        ("expected.toml#refused", "expected.toml#any", 0),
        // Another halt has no class to state, and differs at its halt.
        ("expected.toml#refused", "stopped.json", 1),
    ];
    for (case, actual, code) in checks {
        let output = krs("compare", &files, &["--expect", case, actual]);
        assert_eq!(
            output.status.code(),
            Some(code),
            "{case} {actual}: {}{}",
            text(&output.stdout),
            text(&output.stderr)
        );
    }
    let output = krs(
        "compare",
        &files,
        &["--expect", "expected.toml#refused", "stuck.json"],
    );
    let stderr = text(&output.stderr);
    assert_eq!(output.status.code(), Some(2), "{stderr}");
    assert!(
        stderr.contains("the actual end does not state `class`, which the expectation compares"),
        "{stderr}"
    );
}

/// `krs search` does not evaluate the declared ends at its final states, so it refuses a case
/// whose expectation states a declared class, and checks one that states only its halt.
#[test]
fn search_refuses_an_expectation_of_a_declared_class() {
    let cases = [
        named_case(
            "class",
            "quit 12",
            "halt = \"stuck\", class = \"refused\", compare = [\"count\"], cells = { count = 0 }",
        ),
        named_case(
            "halt",
            "quit 12",
            "halt = \"stuck\", compare = [\"count\"], cells = { count = 0 }",
        ),
    ]
    .concat();
    let files = [("search.toml", cases.as_str())];
    let output = krs("search", &files, &["--case", "search.toml#class"]);
    let stderr = text(&output.stderr);
    assert_eq!(output.status.code(), Some(2), "{stderr}");
    assert!(
        stderr.contains("expects a declared class of its end (`class`, `end` or `reason`), which krs search does not evaluate at its final states"),
        "{stderr}"
    );
    let output = krs("search", &files, &["--case", "search.toml#halt"]);
    assert_eq!(output.status.code(), Some(0), "{}", text(&output.stderr));
}
