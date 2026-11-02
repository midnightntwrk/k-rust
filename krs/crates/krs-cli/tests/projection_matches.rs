//! `k::matches!(k::project!(S, t), P)` means that `t` is an `S` whose value matches `P`, and has
//! no value where `t` is not an `S` (NT-42, finding NT-37-1). In a condition the projection's test
//! comes first (NT-37), and the match is then stated on `t` itself, which the test makes the
//! projection's value: `isInt(A) andThenBool ( 1 :=K A )`, with no projection as `:=K`'s operand,
//! which Java K's frontend refuses. Each rule applies where `a` is an `Int` that matches, and not
//! where it is an `Int` that does not or no `Int` at all (where `!k::matches!(..)` has no value
//! either), on k-rust and on Java K's LLVM backend.
//!
//! A static clause's result that holds such a test, where it has no value, is a state the
//! program reaches with no value (finding NT-37-2): a rule's condition that reads it does not
//! hold, and `krs run` reports the run undefined there, naming the term, as it does for a rule's
//! result with the projection, which keeps it (a result is not tested).

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use krs_test_support::{
    fixture_build_env, kompile_reference, krs_command, shared_fixture_target, temp_dir,
};

const HEAD: &str = r#"
use k::builtin::{Bool, Int, KSequence};
use k::KResult;
use k::Term;

k::sorts! {
    Stmt;
    Arg;
    Value: KResult;
    impl Value for Int;
    impl Arg for Int;
    impl Arg for Bool;
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub acc: Value,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self { k: k::k![pgm], acc: 0 }
    }
}
"#;

/// Conditions and a static clause's result over the projection.
const CONDITIONS: &str = r#"
#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence((Yes, Not, Any, Pick, Flag))]
pub enum StmtSyntax {
    #[k::syntax("yes {a}")]
    Yes { a: Arg },
    #[k::syntax("not {a}")]
    Not { a: Arg },
    #[k::syntax("any {a}")]
    Any { a: Arg },
    #[k::syntax("pick {a}")]
    #[k::desugar]
    Pick { a: Arg },
    #[k::syntax("flag {b}")]
    Flag { b: Bool },
}

#[k::desugar]
fn pick(k::term![StmtSyntax::Pick(a)]: Term<Stmt>) -> Term<Stmt> {
    StmtSyntax::Flag(k::matches!(k::project!(Int, a), 1))
}

k::rules! {
    for Machine;
    use StmtSyntax::*;

    #[k::requires(k::matches!(k::project!(Int, a), 1))]
    yes: { k: [Yes(a), ..], acc: _ } => { k: [..], acc: 1 };
    #[k::requires(!k::matches!(k::project!(Int, a), 1))]
    not: { k: [Not(a), ..], acc: _ } => { k: [..], acc: 1 };
    #[k::requires(k::matches!(k::project!(Int, a), _))]
    any: { k: [Any(a), ..], acc: _ } => { k: [..], acc: 1 };
    #[k::requires(b)]
    flag: { k: [Flag(b), ..], acc: _ } => { k: [..], acc: 1 };
}
"#;

/// A rule's result over the projection, which keeps it: the result has no value where `a` is
/// not an `Int`.
const RESULT: &str = r#"
#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence((Res, Flag))]
pub enum StmtSyntax {
    #[k::syntax("res {a}")]
    Res { a: Arg },
    #[k::syntax("flag {b}")]
    Flag { b: Bool },
}

k::rules! {
    for Machine;
    use StmtSyntax::*;

    res: { k: [Res(a), ..] } => { k: [Flag(k::matches!(k::project!(Int, a), 1)), ..] };
    #[k::requires(b)]
    flag: { k: [Flag(b), ..], acc: _ } => { k: [..], acc: 1 };
}
"#;

/// Each program, and how its run ends: `Some(acc)` where the rule applies and the computation
/// ends empty, `None` where no rule applies and `acc` stays 0. An `Int` that matches, one that
/// does not, and a `Bool`, which is no `Int`.
const PROGRAMS: &[(&str, Option<&str>)] = &[
    ("yes 1", Some("1")),
    ("yes 2", None),
    ("yes true", None),
    ("not 2", Some("1")),
    ("not 1", None),
    ("not true", None),
    ("any 3", Some("1")),
    ("any true", None),
    ("pick 1", Some("1")),
    ("pick 2", None),
];

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

fn package(root: &Path, name: &str, library: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), format!("{HEAD}{library}")).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-PROJMATCH\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
            krs_path(),
        ),
    )
    .unwrap();
    directory.join("Cargo.toml")
}

/// Runs `krs <command>` on the package's `main` definition.
fn krs(target: &Path, manifest: &Path, command: &str, extra: &[&str]) -> (bool, String, String) {
    let package = manifest
        .parent()
        .and_then(Path::file_name)
        .and_then(|name| name.to_str())
        .unwrap();
    let mut process = krs_command!();
    fixture_build_env(&mut process, target);
    let output = process
        .args([command, "--manifest-path"])
        .arg(manifest)
        .args(["--package", package, "--definition", "main"])
        .args(extra)
        .env("NO_COLOR", "1")
        .env("KRS_STAGE_CACHE_DIR", target.join("stages"))
        .output()
        .unwrap();
    (
        output.status.success(),
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

/// The final `<acc>` of a run's KAST output, and whether its `<k>` is empty.
fn ended(stdout: &str) -> (Option<&str>, bool) {
    let acc = stdout
        .split("`<acc>`(#token(\"")
        .nth(1)
        .and_then(|rest| rest.split('"').next());
    (acc, stdout.contains("`<k>`(.K)"))
}

/// The emitted definition's lines holding `:=K`, without their labels.
fn matches_lines(definition: &str) -> Vec<String> {
    definition
        .lines()
        .map(str::trim)
        .filter(|line| line.contains(":=K"))
        .map(|line| line.split(" [label(").next().unwrap_or(line).to_owned())
        .collect()
}

/// `krs run` of `program`: its status line and notes, after the printed state.
fn run(target: &Path, manifest: &Path, directory: &Path, program: &str) -> (String, String) {
    let path = directory.join("program.pgm");
    fs::write(&path, program).unwrap();
    let (success, stdout, stderr) = krs(target, manifest, "run", &[path.to_str().unwrap()]);
    assert!(success, "krs run {program}:\n{stdout}\n{stderr}");
    (stdout, stderr)
}

#[test]
fn a_match_over_a_projection_is_stated_on_the_operand_after_its_test() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "projection-matches", CONDITIONS);
    let output = temporary.path().join("emitted");
    let (success, _, stderr) = krs(
        target.path(),
        &manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    let definition = fs::read_to_string(output.join("definition.k")).unwrap();
    expect_test::expect![[r#"
        [
            "requires isInt(A:Arg) andThenBool ( _ :=K A:Arg )",
            "requires isInt(A:Arg) andThenBool (notBool ( 1 :=K A:Arg ))",
            "requires isInt(A:Arg) andThenBool ( 1 :=K A:Arg )",
            "requires isInt(A:Arg) andThenBool (notBool ( 1 :=K A:Arg ))",
            "requires isInt(A:Arg) andThenBool ( 1 :=K A:Arg )",
        ]
    "#]]
    .assert_debug_eq(&matches_lines(&definition));

    for (program, acc) in PROGRAMS {
        let path = temporary.path().join("program.pgm");
        fs::write(&path, program).unwrap();
        let (success, stdout, stderr) = krs(
            target.path(),
            &manifest,
            "run",
            &[path.to_str().unwrap(), "--output", "kast"],
        );
        let (ended, done) = ended(&stdout);
        assert!(
            success && done == acc.is_some() && ended == Some(acc.unwrap_or("0")),
            "krs run {program}:\n{stdout}\n{stderr}"
        );
    }
    // The static result has no value at `pick true`: the run is undefined at the state holding
    // it, which `flag`'s condition reads, and the note names the term.
    let (_, stderr) = run(target.path(), &manifest, temporary.path(), "pick true");
    let lines = stderr.lines().collect::<Vec<_>>();
    assert!(
        lines.iter().any(|line| line
            .starts_with("krs run: undefined after 0 steps; <k> starts with `flag krsLocal_"))
            && lines
                .iter()
                .any(|line| line.starts_with("note: `krsLocal_") && line.contains("has no value")),
        "krs run pick true:\n{stderr}"
    );

    // The same programs on Java K's LLVM backend, from the emitted definition, which its
    // frontend reads (it refused `:=K {A}:>Int`).
    let compiled =
        kompile_reference(&definition, "ORG-KRS-PROJMATCH", "ORG-KRS-PROJMATCH-SYNTAX").run();
    let krun = std::env::var_os("KRS_K_BIN").map_or_else(
        || PathBuf::from("krun"),
        |directory| PathBuf::from(directory).join("krun"),
    );
    for (program, acc) in PROGRAMS {
        let path = temporary.path().join("program.pgm");
        fs::write(&path, program).unwrap();
        let output = Command::new(&krun)
            .arg("--definition")
            .arg(compiled.path().join("compiled"))
            .arg(&path)
            .args(["--output", "kast"])
            .output()
            .expect("the pinned krun starts");
        let stdout = String::from_utf8(output.stdout).unwrap();
        let (ended, done) = ended(&stdout);
        assert!(
            output.status.success() && done == acc.is_some() && ended == Some(acc.unwrap_or("0")),
            "krun {program}:\n{stdout}\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

#[test]
fn a_match_over_a_projection_in_a_result_keeps_the_projection() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "projection-result", RESULT);
    let output = temporary.path().join("emitted");
    let (success, _, stderr) = krs(
        target.path(),
        &manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    let definition = fs::read_to_string(output.join("definition.k")).unwrap();
    expect_test::expect![[r#"
        [
            "<k> res A:Arg => flag ( 1 :=K {A:Arg}:>Int ) ... </k>",
        ]
    "#]]
    .assert_debug_eq(&matches_lines(&definition));
    let (_, stderr) = run(target.path(), &manifest, temporary.path(), "res 1");
    assert!(
        stderr.contains("krs run: stuck after 2 steps; <k> is empty"),
        "krs run res 1:\n{stderr}"
    );
    let (_, stderr) = run(target.path(), &manifest, temporary.path(), "res true");
    assert!(
        stderr.contains("krs run: undefined after 0 steps; <k> starts with `res true`"),
        "krs run res true:\n{stderr}"
    );
}
