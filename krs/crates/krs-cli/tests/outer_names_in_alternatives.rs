//! A left-hand side is one pattern however many terms it is written as, and a
//! name it repeats is one variable: nonlinear matching. Inside `A | B`, a
//! name the sentence binds outside the alternatives is that variable, a use
//! in each alternative and a binder in none, so `x | 1` beside a binding of
//! `x` matches a term equal to `x`, or `1`, and emits `( X #Or 1 )`. What
//! every alternative must bind alike is the names it binds fresh. Outside
//! means in every match, wherever the binding is written; a `k::matches!`
//! pattern is a match of its own, whose names are never the sentence's.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"
use k::builtin::{Int, KSequence, Map};
use k::{KResult, Term};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("same({a}, {b})")] Same { a: Int, b: Int },
    #[k::syntax("check({a})")] Check { a: Int },
    #[k::syntax("ask({a}, {b})")] Ask { a: Int, b: Int },
    #[k::syntax("look({a})")] Look { a: Int },
    #[k::syntax("yes")] Yes(),
}

/// A function the equations define where their alternatives match.
#[k::function(partial, sort = Int, syntax = "probe({a}, {b})")]
pub struct Probe {
    pub a: Term<Int>,
    pub b: Term<Int>,
}

/// A function whose equation reads the configuration.
#[k::function(partial, sort = Int, syntax = "peek({a})")]
pub struct Peek {
    pub a: Term<Int>,
}

/// A function a map key applies.
#[k::function(partial, sort = Int, syntax = "wk({a})")]
pub struct Wk {
    pub a: Term<Int>,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub pc: Int,
    #[k::cell]
    pub env: Map,
}

impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] pgm: Stmt,
        #[k::config_var(name = "PC")] pc: Int,
    ) -> Self {
        Self { k: k::k![pgm], pc, env: k::map![] }
    }
}
"#;

/// A sort rule, a machine rule whose alternatives stand before the cell that
/// binds their name, an equation, and an equation whose function context's
/// alternatives use a name its subject binds.
const RULES: &str = r"
k::rules! {
    for Stmt;
    use Cmd::*;

    same: Same(x, x | 1) => Yes();
    ask: Ask(a, b) => Probe(a, b);
    look: Look(a) => Peek(a);
}

k::rules! {
    for Machine;
    use Cmd::*;

    check: { k: [Check(x | 0), ..], pc: x } => { k: [Yes(), ..] };
}

#[k::equation]
fn probe_same(k::term![Probe(x, x | 1)]: Term<Int>) -> Term<Int> {
    0
}

#[k::equation]
fn peek_pc(
    x: Term<Int>,
    k::term![Peek(x)]: Term<Int>,
    k::cells! { pc: k::configuration::Cell(x | 7), .. }: Machine,
) -> Term<Int> {
    1
}
";

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// Writes a one-package workspace whose library is the preamble and
/// `source`; every package shares one K namespace.
fn package(root: &Path, name: &str, source: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), format!("{PREAMBLE}{source}")).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-OUTER-NAMES\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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

/// The rules of the K source `krs emit-k` writes for the package, without
/// the configuration and the declarations.
fn emitted_rules(target: &Path, manifest: &Path) -> String {
    let output = manifest.with_file_name("emitted");
    let (success, _, stderr) = krs(
        target,
        manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    let k = krs_test_support::without_source_comments(
        &fs::read_to_string(output.join("definition.k")).unwrap(),
    );
    k.lines()
        .map(str::trim)
        .filter(|line| line.starts_with("rule ") || line.starts_with('<'))
        .filter(|line| !line.starts_with("<k> $PGM") && !line.starts_with("<pc> $PC"))
        .filter(|line| !line.starts_with("<env> .Map"))
        .collect::<Vec<_>>()
        .join("\n")
}

/// The computation cell after `krs run` of `program` from `PC=pc`.
fn run(target: &Path, manifest: &Path, program: &str, pc: &str) -> String {
    let file = manifest.with_file_name("program.txt");
    fs::write(&file, program).unwrap();
    let (success, stdout, stderr) = krs(
        target,
        manifest,
        "run",
        &[file.to_str().unwrap(), "-c", &format!("PC={pc}")],
    );
    assert!(success, "{program}:\n{stdout}\n{stderr}");
    let flat = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
    let start = flat.find("<k>").unwrap();
    let end = flat.find("</k>").unwrap() + "</k>".len();
    format!("{program} (PC={pc}) => {}", &flat[start..end])
}

/// Each sentence's alternatives use the name its left side binds outside
/// them, in another argument, another cell, or the function context: the K
/// writes one variable at both places, the definition checks on the native
/// routes, and a run rewrites the terms equal to the name or to the other
/// alternative and leaves the rest stuck.
#[test]
fn a_name_bound_outside_alternatives_is_a_use_in_each() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "uses", RULES);
    expect_test::expect![[r"
        rule [ask]:
        <k> ask ( A:Int , B:Int ) => probe ( A:Int , B:Int ) ... </k>
        rule [check]:
        <k> check ( ( X:Int #Or 0 ) ) => yes ... </k>
        <pc> X:Int </pc>
        rule [look]:
        <k> look ( A:Int ) => peek ( A:Int ) ... </k>
        rule [[ peek ( X:Int ) => 1 ]]
        <pc> ( X:Int #Or 7 ) </pc> [label(org_krs_outer_names--peek_pc)]
        rule probe ( X:Int , ( X:Int #Or 1 ) ) => 0 [label(org_krs_outer_names--probe_same)]
        rule [same]:
        <k> same ( X:Int , ( X:Int #Or 1 ) ) => yes ... </k>"]]
    .assert_eq(&emitted_rules(target.path(), &manifest));
    let (success, stdout, stderr) = krs(target.path(), &manifest, "check", &[]);
    assert!(success, "{stdout}\n{stderr}");
    let runs = [
        ("same(2, 2)", "0"),
        ("same(2, 1)", "0"),
        ("same(2, 3)", "0"),
        ("check(5)", "5"),
        ("check(0)", "5"),
        ("check(4)", "5"),
        ("ask(2, 2)", "0"),
        ("ask(2, 1)", "0"),
        ("ask(2, 3)", "0"),
        ("look(5)", "5"),
        ("look(5)", "7"),
        ("look(5)", "6"),
    ]
    .map(|(program, pc)| run(target.path(), &manifest, program, pc));
    expect_test::expect![[r#"
        [
            "same(2, 2) (PC=0) => <k> yes ~> .K </k>",
            "same(2, 1) (PC=0) => <k> yes ~> .K </k>",
            "same(2, 3) (PC=0) => <k> same(2, 3) ~> .K </k>",
            "check(5) (PC=5) => <k> yes ~> .K </k>",
            "check(0) (PC=5) => <k> yes ~> .K </k>",
            "check(4) (PC=5) => <k> check(4) ~> .K </k>",
            "ask(2, 2) (PC=0) => <k> 0 ~> .K </k>",
            "ask(2, 1) (PC=0) => <k> 0 ~> .K </k>",
            "ask(2, 3) (PC=0) => <k> ask(2, 3) ~> .K </k>",
            "look(5) (PC=5) => <k> 1 ~> .K </k>",
            "look(5) (PC=7) => <k> 1 ~> .K </k>",
            "look(5) (PC=6) => <k> look(5) ~> .K </k>",
        ]
    "#]]
    .assert_debug_eq(&runs);
}

/// What stays refused: a name the alternatives bind fresh on one side only,
/// beside a use (`x | y`) or with no binding outside them (two or-patterns
/// that each bind `x` on one side, an equation's argument, a computed key
/// that only reads `x`, in a readable rule, a `cells!` rule and a function
/// context); a name the
/// sentence binds, inside a `k::matches!` pattern, where it binds a new
/// variable; alternatives below a function in a map key, which is built;
/// and alternatives in a simplification, which rewrites one term.
#[test]
fn alternatives_that_bind_a_fresh_name_unequally_stay_refused() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let cases = [
        (
            "fresh",
            "k::rules! {\n    for Stmt;\n    use Cmd::*;\n    same: Same(x, x | y) => Yes();\n}\n",
            "error[krs::syntax::invalid-pattern-or]: variable `y` is not bound in all alternatives",
        ),
        (
            "twice",
            "k::rules! {\n    for Stmt;\n    use Cmd::*;\n    same: Same(x | 1, x | 2) => Yes();\n}\n",
            "error[krs::syntax::invalid-pattern-or]: variable `x` is not bound in all alternatives",
        ),
        (
            "equation",
            "#[k::equation]\nfn probe_one(k::term![Probe(x | 1, 0)]: Term<Int>) -> Term<Int> {\n    0\n}\n",
            "error[krs::syntax::invalid-pattern-or]: variable `x` is not bound in all alternatives",
        ),
        // A name a computed key reads binds nothing: the key is evaluated from it, so on a
        // match through the other alternative nothing gives it a value.
        (
            "computed-key",
            "k::rules! {\n    for Machine;\n    use Cmd::*;\n    wkey: { k: [Check(x | 0), ..], env: { Wk(x) -> v, .. } } => { k: [Yes(), ..] };\n}\n",
            "error[krs::syntax::invalid-pattern-or]: variable `x` is not bound in all alternatives",
        ),
        (
            "computed-cells-key",
            "#[k::rule(label = \"wkey\")]\npub fn wkey(\n    x: Int,\n    v: k::KItem,\n    k::cells! { k: k::configuration::KCell(Cmd::Check(x | 0), tail @ ..), env: k::configuration::Cell(k::map![Wk(x) -> v, ..]), state @ .. }: Machine,\n) -> Machine {\n    k::cells! { k: k::configuration::KCell(Cmd::Yes(), ..tail), ..state }\n}\n",
            "error[krs::syntax::invalid-pattern-or]: variable `x` is not bound in all alternatives",
        ),
        (
            "computed-context-key",
            "#[k::equation]\nfn probe_env(\n    x: Term<Int>,\n    v: Term<k::KItem>,\n    k::term![Probe(x | 0, 1)]: Term<Int>,\n    k::cells! { env: k::configuration::Cell(k::map![Wk(x) -> v, ..]), .. }: Machine,\n) -> Term<Int> {\n    1\n}\n",
            "error[krs::syntax::invalid-pattern-or]: variable `x` is not bound in all alternatives",
        ),
        (
            "matches",
            "#[k::rule(label = \"same\")]\n#[k::requires(k::matches!(x, x | 1))]\nfn same(k::term![Cmd::Check(x)]: Term<Stmt>) -> Term<Stmt> {\n    Cmd::Yes()\n}\n",
            "error[krs::analysis::invalid-matches]: `x` in k::matches! binds a new variable; it does not compare with the `x` the sentence or the initializer already names",
        ),
        (
            "key",
            "k::rules! {\n    for Machine;\n    use Cmd::*;\n    look: { k: [Check(x), ..], env: { Wk(x | 1) -> v, .. } } => { k: [Yes(), ..] };\n}\n",
            "error[krs::analysis::ambiguous-operator]: alternatives `A | B` stands below the function `Wk` in a map key, which computes the value looked up, so the position is built",
        ),
        (
            "simplification",
            "#[k::simplification]\nfn probe_same(k::term![Probe(x, x | 1)]: Term<Int>) -> Term<Int> {\n    0\n}\n",
            "error[krs::analysis::invalid-pattern-or]: `A | B` (K's #Or) matches one of several terms, and a subject rewritten as one term in place stands for the one term it matched",
        ),
    ];
    for (name, source, message) in cases {
        let manifest = package(temporary.path(), name, source);
        let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
        assert!(!success, "{name}: {stderr}");
        assert!(stderr.contains(message), "{name}: {stderr}");
    }
}
