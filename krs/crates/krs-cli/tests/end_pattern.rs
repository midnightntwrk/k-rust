//! `krs run --output none` decides a run's status on the backend's state of its end, without
//! building the end's KORE pattern, and says what a run that builds it says.
//!
//! `--output pretty` builds the pattern and reads the status from it: the term with no value
//! that makes a run `undefined`, the `stdout` buffer, the exit cell's value, and the head of the
//! main cell, which both outputs name in the grammar's notation. So for one run the two outputs
//! write the same lines on standard error, but for the end `pretty` prints on standard output,
//! and exit with the same status. The fixture has an exit cell, a `stream = "stdout"` cell, and
//! a partial function with no value at 1, and its programs end each way a run ends: complete
//! with an empty main cell, stuck at an item no rule rewrites, undefined, at the depth bound,
//! and at a stop before and after a rule.

use std::fs;
use std::path::Path;
use std::process::Output;
use std::sync::OnceLock;

use krs_test_support::{
    SharedFixtureTarget, TempDir, fixture_build_env, krs_command, shared_fixture_target, temp_dir,
};

const FIXTURE: &str = r#"
use k::builtin::{Int, KSequence, List, list};
use k::KResult;

k::sorts! {
    Stmt;
}

#[k::constructors(sort = Stmt, result = KResult)]
pub enum StmtSyntax {
    #[k::syntax("say {n}")]
    Say { n: Int },
    #[k::syntax("quit {code}")]
    Quit { code: Int },
    #[k::syntax("tick")]
    Tick(),
    #[k::syntax("lose {n}")]
    Lose { n: Int },
    #[k::syntax("rest")]
    Rest(),
}

/// `1` at `0`, and no value elsewhere.
#[k::function(partial, internal)]
#[k::requires(n.eq::<Int>(0))]
pub fn OnlyZero(n: k::Term<Int>) -> k::Term<Int> {
    1
}

k::rules! {
    for Machine;
    use StmtSyntax::*;

    say: { k: [Say(n), ..], output: out } => { k: [..], output: list::concat(out, list::item(n)) };
    quit: { k: [Quit(code), ..], status: _ } => { k: [..], status: code };
    tick: { k: [Tick(), ..], count } => { k: [Tick(), ..], count: count + 1 };
    lose: { k: [Lose(n), ..], count: _ } => { k: [..], count: OnlyZero(n) };
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub count: Int,
    #[k::cell(exit)]
    pub status: Int,
    #[k::cell(stream = "stdout")]
    pub output: List,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self { k: k::k![pgm], count: 0, status: 0, output: list::empty() }
    }
}
"#;
const PACKAGE: &str = "krs-cli-end-pattern-fixture";

/// The fixture as a package, built once per test process.
struct Project {
    directory: TempDir,
    target: SharedFixtureTarget,
}

fn project() -> &'static Project {
    static PROJECT: OnceLock<Project> = OnceLock::new();
    PROJECT.get_or_init(|| {
        let target = shared_fixture_target();
        let directory = temp_dir();
        fs::create_dir_all(directory.path().join("src")).unwrap();
        fs::write(directory.path().join("src/lib.rs"), FIXTURE).unwrap();
        let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../krs")
            .canonicalize()
            .unwrap();
        let krs_literal = serde_json::to_string(krs.to_str().unwrap()).unwrap();
        fs::write(
            directory.path().join("Cargo.toml"),
            format!(
                "[package]\nname = \"{PACKAGE}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {krs_literal} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-CLI-END-PATTERN\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\n"
            ),
        )
        .unwrap();
        Project { directory, target }
    })
}

/// `krs run PROGRAM ARGUMENTS --output OUTPUT` on the fixture, `PROGRAM` the text of a file.
fn run(name: &str, program: &str, arguments: &[&str], output: &str) -> Output {
    let project = project();
    let file = project.directory.path().join(format!("{name}.pgm"));
    fs::write(&file, program).unwrap();
    let mut process = krs_command!();
    fixture_build_env(&mut process, project.target.path());
    process
        .current_dir(project.directory.path())
        .arg("run")
        .arg(&file)
        .args(["--package", PACKAGE, "--definition", "main"])
        .args(arguments)
        .args(["--output", output])
        .output()
        .unwrap()
}

fn text(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).into_owned()
}

/// Each way a run ends: the status line `--output none` writes, the bytes it writes on standard
/// output (the `stdout` cell's buffer) and its exit status are those of `--output pretty`,
/// which reads them from the end's pattern.
#[test]
fn a_run_that_builds_no_pattern_of_its_end_says_what_one_that_builds_it_says() {
    let cases: [(&str, &str, &[&str], &str, i32); 11] = [
        ("complete", "say 7", &[], "krs run: stuck after ", 0),
        (
            "exit",
            "quit 3",
            &[],
            "krs run: stuck after 1 step; <k> is empty\n",
            3,
        ),
        // The exit cell's value where the process status keeps only its low byte.
        (
            "exit-wide",
            "quit 259",
            &[],
            "krs run: stuck after 1 step; <k> is empty\n",
            3,
        ),
        // The exit cell's value at a stop after the rule that sets it.
        (
            "exit-stopped",
            "quit 3",
            &["--stop-after", "quit"],
            "krs run: stopped after 1 step",
            3,
        ),
        (
            "stuck",
            "rest",
            &[],
            "krs run: stuck after 0 steps; <k> starts with `rest`\n",
            0,
        ),
        (
            "undefined",
            "lose 1",
            &[],
            "krs run: undefined after 0 steps; <k> starts with `lose 1`\n",
            0,
        ),
        (
            "defined",
            "lose 0",
            &[],
            "krs run: stuck after 1 step; <k> is empty\n",
            0,
        ),
        (
            "depth-bound",
            "tick",
            &["--depth", "5"],
            "krs run: depth-bound after 5 steps; <k> starts with `tick`\n",
            0,
        ),
        (
            "depth-zero",
            "quit 3",
            &["--depth", "0"],
            "krs run: depth-bound after 0 steps; <k> starts with `quit 3`\n",
            0,
        ),
        (
            "stop-after",
            "tick",
            &["--stop-after", "tick", "--stop-count", "3"],
            "krs run: stopped after 3 steps",
            0,
        ),
        (
            "stop-before",
            "tick",
            &["--stop-before", "tick", "--stop-count", "3"],
            "krs run: stopped after 2 steps",
            0,
        ),
    ];
    for (name, program, arguments, status, code) in cases {
        let none = run(name, program, arguments, "none");
        let pretty = run(name, program, arguments, "pretty");
        let (lines, built) = (text(&none.stderr), text(&pretty.stderr));
        assert!(lines.contains(status), "{name}: {lines}");
        assert_eq!(lines, built, "{name}");
        assert_eq!(none.status.code(), Some(code), "{name}: {lines}");
        assert_eq!(none.status.code(), pretty.status.code(), "{name}");
        // `pretty` prints the end after what the run wrote to its `stdout` cell.
        let (wrote, printed) = (text(&none.stdout), text(&pretty.stdout));
        assert!(printed.starts_with(&wrote), "{name}: {wrote:?} {printed:?}");
        assert!(printed.contains("<k>"), "{name}: {printed}");
        assert!(!wrote.contains("<k>"), "{name}: {wrote}");
    }
    assert_eq!(text(&run("complete", "say 7", &[], "none").stdout), "7");
}
