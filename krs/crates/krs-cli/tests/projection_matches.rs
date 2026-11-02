//! `k::matches!(k::project!(S, t), P)` means that `t` is an `S` whose value matches `P`, and has
//! no value where `t` is not an `S` (NT-42, finding NT-37-1). In a condition the projection's test
//! comes first (NT-37), and the match is then stated on `t` itself, which the test makes the
//! projection's value: `isInt(A) andThenBool ( 1 :=K A )`, with no projection as `:=K`'s operand,
//! which Java K's frontend refuses. That holds in every condition position: a conjunct, a `let`'s
//! value, and an `ensures`. Each rule applies where `a` is an `Int` that matches, and not where it
//! is an `Int` that does not or no `Int` at all (where `!k::matches!(..)` has no value either), on
//! k-rust and on Java K's LLVM backend.
//!
//! A result is not tested: where it has no value, the rule's result has none. There the test is
//! lifted into a function of its own (finding NT-42-1), whose equations' conditions are tested and
//! stated on `t`, so it has no value where `t` is no `Int`, and no projection stands as `:=K`'s
//! operand anywhere in the emitted K.
//!
//! A term has no value only where it is a ground application of a partial function defined by its
//! equations alone that the backend left unevaluated (findings NT-37-2 and NT-42-2): a state that
//! holds one has no value, so `krs run` reports the run undefined there, naming the term, with any
//! number of leaves, and a rule's condition that reads one does not hold. A split over a term that
//! may have a value (an existential's, or a `total` function's with no equation) is the
//! definition's: `krs run` names it as an error, and `krs search` prints both states.

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
#[k::precedence((Yes, Not, Any, Lett, Pick, Flag, Keep, Held))]
pub enum StmtSyntax {
    #[k::syntax("yes {a}")]
    Yes { a: Arg },
    #[k::syntax("not {a}")]
    Not { a: Arg },
    #[k::syntax("any {a}")]
    Any { a: Arg },
    #[k::syntax("lett {a}")]
    Lett { a: Arg },
    #[k::syntax("pick {a}")]
    #[k::desugar]
    Pick { a: Arg },
    #[k::syntax("flag {b}")]
    Flag { b: Bool },
    #[k::syntax("keep {a}")]
    #[k::desugar]
    Keep { a: Arg },
    #[k::syntax("held {b}")]
    Held { b: Bool },
}

#[k::desugar]
fn pick(k::term![StmtSyntax::Pick(a)]: Term<Stmt>) -> Term<Stmt> {
    StmtSyntax::Flag(k::matches!(k::project!(Int, a), 1))
}

/// No rule reads `held`'s test: a run of `keep a` ends in one state, holding it.
#[k::desugar]
fn keep(k::term![StmtSyntax::Keep(a)]: Term<Stmt>) -> Term<Stmt> {
    StmtSyntax::Held(k::matches!(k::project!(Int, a), 1))
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
    #[k::requires({ let b = k::matches!(k::project!(Int, a), 1); b })]
    lett: { k: [Lett(a), ..], acc: _ } => { k: [..], acc: 1 };
    #[k::requires(b)]
    flag: { k: [Flag(b), ..], acc: _ } => { k: [..], acc: 1 };
}
"#;

/// A rule's result over the projection, which has no value where `a` is not an `Int`; an
/// `ensures` over it; and a rule's result that applies a partial function with no equation.
const RESULT: &str = r#"
#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence((Res, Flag, Ens, Measure, Count))]
pub enum StmtSyntax {
    #[k::syntax("res {a}")]
    Res { a: Arg },
    #[k::syntax("flag {b}")]
    Flag { b: Bool },
    #[k::syntax("ens {a}")]
    Ens { a: Arg },
    #[k::syntax("measure {a}")]
    Measure { a: Arg },
    #[k::syntax("count {n}")]
    Count { n: Int },
}

/// Partial, and no equation defines it: no application of it has a value.
#[k::function(partial, internal)]
pub fn Size(a: Term<Arg>) -> Term<Int>;

k::rules! {
    for Machine;
    use StmtSyntax::*;

    res: { k: [Res(a), ..] } => { k: [Flag(k::matches!(k::project!(Int, a), 1)), ..] };
    #[k::requires(b)]
    flag: { k: [Flag(b), ..], acc: _ } => { k: [..], acc: 1 };
    #[k::requires(true)]
    #[k::ensures(k::matches!(k::project!(Int, a), 1))]
    ens: { k: [Ens(a), ..], acc: _ } => { k: [..], acc: 1 };
    measure: { k: [Measure(a), ..] } => { k: [Count(Size(a)), ..] };
}
"#;

/// A rule whose condition reads an existential's value: a run of `go` splits on it.
const EXISTS: &str = r#"
#[k::constructors(sort = Stmt, result = KResult)]
pub enum StmtSyntax {
    #[k::syntax("go")]
    Go {},
    #[k::syntax("test {a}")]
    Test { a: Int },
}

k::rules! {
    for Machine;
    use StmtSyntax::*;

    #[k::exists(v: Int)]
    go: { k: [Go(), ..] } => { k: [Test(v), ..] };
    #[k::requires(a == 1)]
    test: { k: [Test(a), ..], acc: _ } => { k: [..], acc: 1 };
}
"#;

/// A rule whose condition reads a `total` function no equation defines: it has a value at `1`,
/// which the definition does not say, so a run of `test 1` splits on it.
const TOTAL: &str = r#"
#[k::constructors(sort = Stmt, result = KResult)]
pub enum StmtSyntax {
    #[k::syntax("test {a}")]
    Test { a: Int },
}

#[k::function(total, internal)]
pub fn Opaque(a: Term<Int>) -> Term<Int>;

k::rules! {
    for Machine;
    use StmtSyntax::*;

    #[k::requires(Opaque(a) == 1)]
    test: { k: [Test(a), ..], acc: _ } => { k: [..], acc: 1 };
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
    ("lett 1", Some("1")),
    ("lett 2", None),
    ("lett true", None),
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
    let (success, stdout, stderr) = command(target, manifest, directory, "run", program);
    assert!(success, "krs run {program}:\n{stdout}\n{stderr}");
    (stdout, stderr)
}

/// `krs COMMAND` of `program`.
fn command(
    target: &Path,
    manifest: &Path,
    directory: &Path,
    command: &str,
    program: &str,
) -> (bool, String, String) {
    let path = directory.join("program.pgm");
    fs::write(&path, program).unwrap();
    krs(target, manifest, command, &[path.to_str().unwrap()])
}

/// The lines of `stderr` from the status line on, with each lifted function's digest written
/// `DIGEST`.
fn status(stderr: &str) -> String {
    let from = stderr.find("krs run:").unwrap_or(0);
    digests(&stderr[from..])
}

/// `text` with each `krsLocal_` digest written `DIGEST`.
fn digests(text: &str) -> String {
    let mut out = String::new();
    let mut rest = text;
    while let Some(at) = rest.find("krsLocal_") {
        out.push_str(&rest[..at]);
        out.push_str("krsLocal_DIGEST");
        rest = rest[at + "krsLocal_".len()..].trim_start_matches(|c: char| c.is_ascii_hexdigit());
    }
    out.push_str(rest);
    out
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
            "requires isInt(A:Arg) andThenBool ( #let B:Bool = ( 1 :=K A:Arg ) #in B:Bool )",
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
    // it, which `flag`'s condition reads, and the note names the term. At `keep true` no rule
    // reads it, and the one state the run ends in holds it, so it has no value either.
    let mut ends = Vec::new();
    for program in ["pick true", "keep true", "keep 1"] {
        let (_, stderr) = run(target.path(), &manifest, temporary.path(), program);
        ends.push(format!("{program}: {}", status(&stderr)));
    }
    expect_test::expect![[r"
        pick true: krs run: undefined after 0 steps; <k> starts with `flag krsLocal_DIGEST ( true )`
        note: `krsLocal_DIGEST ( true )` has no value: its function is partial and defined by its equations alone, and none applies there, so the state holding it has none

        keep true: krs run: undefined after 0 steps; <k> starts with `held krsLocal_DIGEST ( true )`
        note: `krsLocal_DIGEST ( true )` has no value: its function is partial and defined by its equations alone, and none applies there, so the state holding it has none

        keep 1: krs run: stuck after 0 steps; <k> starts with `held true`
    "]].assert_eq(&ends.join("\n"));

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
fn a_match_over_a_projection_in_a_result_or_an_ensures_is_read_by_every_frontend() {
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
    let lines = definition
        .lines()
        .map(str::trim)
        .filter(|line| line.contains(":=K") || line.contains("krsLocal_") || line.contains("res "))
        .map(|line| digests(line.split(" [label(").next().unwrap_or(line)))
        .collect::<Vec<_>>();
    expect_test::expect![[r#"
        [
            "syntax Bool ::= \"krsLocal_DIGEST\" \"(\" Arg \")\" [symbol(krsLocal_DIGEST), function]",
            "requires true",
            "ensures isInt(A:Arg) andThenBool ( 1 :=K A:Arg )",
            "requires B:Bool",
            "rule krsLocal_DIGEST ( A:Arg ) => true",
            "requires isInt(A:Arg) andThenBool ( 1 :=K A:Arg )",
            "rule krsLocal_DIGEST ( A:Arg ) => false",
            "requires isInt(A:Arg) andThenBool (notBool ( 1 :=K A:Arg ))",
            "<k> res A:Arg => flag krsLocal_DIGEST ( A:Arg ) ... </k>",
        ]
    "#]].assert_debug_eq(&lines);
    assert!(!definition.contains(":=K {"), "{definition}");
    // Java K's frontend reads the emitted definition (it refused `:=K {A}:>Int`).
    drop(kompile_reference(&definition, "ORG-KRS-PROJMATCH", "ORG-KRS-PROJMATCH-SYNTAX").run());

    let mut ends = Vec::new();
    for program in ["res 1", "res true", "ens 1", "ens true", "measure 1"] {
        let (_, stderr) = run(target.path(), &manifest, temporary.path(), program);
        ends.push(format!("{program}: {}", status(&stderr)));
    }
    expect_test::expect![[r"
        res 1: krs run: stuck after 2 steps; <k> is empty

        res true: krs run: undefined after 1 step; <k> starts with `flag krsLocal_DIGEST ( true )`
        note: `krsLocal_DIGEST ( true )` has no value: its function is partial and defined by its equations alone, and none applies there, so the state holding it has none

        ens 1: krs run: stuck after 1 step; <k> is empty

        ens true: krs run: undefined after 0 steps; <k> starts with `ens true`

        measure 1: krs run: undefined after 1 step; <k> starts with `count size ( 1 )`
        note: `size ( 1 )` has no value: its function is partial and defined by its equations alone, and none applies there, so the state holding it has none
    "]].assert_eq(&ends.join("\n"));
}

/// A split over a term that may have a value is the definition's: an existential's value, which
/// the run has not fixed, and a `total` function's application, which has a value no equation
/// names. `krs run` names the term as an error rather than choosing a state, and `krs search`
/// prints both states, each under its condition.
#[test]
fn a_run_names_a_split_over_a_term_that_may_have_a_value() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let mut ends = Vec::new();
    for (name, library, program) in [
        ("projection-exists", EXISTS, "go"),
        ("projection-total", TOTAL, "test 1"),
    ] {
        let manifest = package(temporary.path(), name, library);
        let (success, _, stderr) =
            command(target.path(), &manifest, temporary.path(), "run", program);
        assert!(!success, "krs run {program} of {name}:\n{stderr}");
        ends.push(format!("{name}: {}", stderr.trim()));
        let (success, stdout, stderr) = command(
            target.path(),
            &manifest,
            temporary.path(),
            "search",
            program,
        );
        assert!(
            success,
            "krs search {program} of {name}:\n{stdout}\n{stderr}"
        );
        ends.push(format!(
            "{name} search: {}",
            stderr.lines().last().unwrap_or_default()
        ));
    }
    expect_test::expect![[r"
        projection-exists: error[krs::exec::undecided]: the run reaches 2 states, under conditions over `hVar?V-b0:Int`, which holds a value the run has not fixed; the run cannot decide which holds, so it has no one path; `krs search` prints each state with its condition
        projection-exists search: krs search: 2 solutions
        projection-total: error[krs::exec::undecided]: the run reaches 2 states, under conditions over `opaque ( 1 )`, which may have a value the definition leaves open (no equation evaluates it, and it is not a partial function defined by its equations alone); the run cannot decide which holds, so it has no one path; `krs search` prints each state with its condition
        projection-total search: krs search: 2 solutions"]].assert_eq(&ends.join("\n"));
}
