//! `A | B` at an equation's subject root. An equation's root alternatives are one equation per
//! alternative: every alternative applies the one function the equation defines, and an
//! application distributes over `|`, so `F(a) | F(b)` is `F(a | b)`, emitted as the alternatives
//! below the root are. Alternatives that are no one function's, or that differ in two arguments,
//! which no one equation matches, are refused at the alternative or the `|`; a subject rewritten
//! as one term takes no alternatives either way.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"
use k::builtin::{Int, KSequence};
use k::{KResult, Term};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence(cmd (Red, Green, Blue, Show, Tint, Duo) > right seq (Seq))]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("red")] Red(),
    #[k::syntax("green")] Green(),
    #[k::syntax("blue")] Blue(),
    #[k::syntax("show({c})")] Show { c: Stmt },
    #[k::syntax("tint({c})")] Tint { c: Stmt },
    #[k::syntax("duo({c}, {n})")] Duo { c: Stmt, n: Int },
    #[k::syntax("{first} {second}")] Seq { first: Stmt, second: Stmt },
}

#[k::function(total, sort = Int, syntax = "code({c})")]
pub struct Code {
    pub c: Term<Stmt>,
}

#[k::function(total, sort = Int, syntax = "tone({c})")]
pub struct Tone {
    pub c: Term<Stmt>,
}

#[k::function(partial, sort = Int, syntax = "mix({c}, {n})")]
pub struct Mix {
    pub c: Term<Stmt>,
    pub n: Term<Int>,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self { k: k::k![pgm] }
    }
}

#[k::rule(label = "show")]
fn show(Cmd::Show { c }: Term<Stmt>) -> Term<Stmt> {
    Code { c }
}

#[k::rule(label = "tint")]
fn tint(Cmd::Tint { c }: Term<Stmt>) -> Term<Stmt> {
    Tone { c }
}

#[k::rule(label = "duo")]
fn duo(Cmd::Duo { c, n }: Term<Stmt>) -> Term<Stmt> {
    Mix { c, n }
}

#[k::equation(owise)]
fn code_other(Code { c: _ }: Term<Int>) -> Term<Int> {
    20
}

#[k::equation(owise)]
fn tone_other(Tone { c: _ }: Term<Int>) -> Term<Int> {
    30
}
"#;

/// Root alternatives on an equation, one of them differing in one of two arguments written in
/// another field order.
const ACCEPTED: &str = r"
#[k::equation]
fn code_warm((Code { c: Cmd::Red() } | Code { c: Cmd::Green() }): Term<Int>) -> Term<Int> {
    10
}

#[k::equation]
fn mix_warm((Mix { c: Cmd::Red(), n } | Mix { n, c: Cmd::Green() }): Term<Int>) -> Term<Int> {
    n
}
";

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// A one-package workspace named `roots` whose library is the preamble and `source`.
fn package(root: &Path, source: &str) -> PathBuf {
    fs::create_dir_all(root.join("src")).unwrap();
    fs::write(root.join("src/lib.rs"), format!("{PREAMBLE}{source}")).unwrap();
    let manifest = root.join("Cargo.toml");
    fs::write(
        &manifest,
        format!(
            "[package]\nname = \"roots\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-ROOT-ALTERNATIVES\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
            krs_path(),
        ),
    )
    .unwrap();
    manifest
}

/// Runs `krs <command>` on the package's `main` definition: whether it passed, its stdout and
/// its stderr.
fn krs(target: &Path, manifest: &Path, command: &str, extra: &[&str]) -> (bool, String, String) {
    let mut process = krs_command!();
    fixture_build_env(&mut process, target);
    let output = process
        .args([command, "--manifest-path"])
        .arg(manifest)
        .args(["--package", "roots", "--definition", "main"])
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

/// The emitted rules that mention `needle`, one per line.
fn rules(k: &str, needle: &str) -> String {
    k.lines()
        .map(str::trim)
        .filter(|line| line.starts_with("rule ") && line.contains(needle))
        .collect::<Vec<_>>()
        .join("\n")
}

/// Root alternatives emit the K of the alternatives below the root, build natively, and take
/// each alternative.
#[test]
fn root_alternatives_emit_as_below_the_root_and_run() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), ACCEPTED);
    let output = manifest.with_file_name("emitted");
    let (success, _, stderr) = krs(
        target.path(),
        &manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    let k = fs::read_to_string(output.join("definition.k")).unwrap();
    expect_test::expect![[r"
        rule code ( ( red #Or green ) ) => 10 [label(krsRule_4ece98de534f7cd06929841e)]
        rule mix ( ( red #Or green ) , N:Int ) => N:Int [label(krsRule_019352ddef449f4bd3f0e54d)]"]]
    .assert_eq(&[rules(&k, "=> 10 "), rules(&k, "rule mix")].join("\n"));
    let program = manifest.with_file_name("program.txt");
    let runs = [
        "show(red)",
        "show(green)",
        "show(blue)",
        "tint(red)",
        "tint(green)",
        "tint(blue)",
        "duo(green, 7)",
        "red",
        "green",
        "blue",
    ]
    .map(|source| {
        fs::write(&program, source).unwrap();
        let (_, stdout, stderr) = krs(
            target.path(),
            &manifest,
            "run",
            &[program.to_str().unwrap()],
        );
        let flat = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
        let start = flat
            .find("<k>")
            .unwrap_or_else(|| panic!("{source}:\n{stdout}\n{stderr}"));
        let end = flat.find("</k>").unwrap() + "</k>".len();
        format!("{source} => {}", &flat[start..end])
    });
    expect_test::expect![[r#"
        [
            "show(red) => <k> 10 ~> .K </k>",
            "show(green) => <k> 10 ~> .K </k>",
            "show(blue) => <k> 20 ~> .K </k>",
            "tint(red) => <k> 30 ~> .K </k>",
            "tint(green) => <k> 30 ~> .K </k>",
            "tint(blue) => <k> 30 ~> .K </k>",
            "duo(green, 7) => <k> 7 ~> .K </k>",
            "red => <k> red ~> .K </k>",
            "green => <k> green ~> .K </k>",
            "blue => <k> blue ~> .K </k>",
        ]
    "#]]
    .assert_debug_eq(&runs);
}

/// `krs check` of the package: its `error[..]` headlines with the locations they point at.
fn check(target: &Path, manifest: &Path) -> Vec<String> {
    let (success, _, stderr) = krs(target, manifest, "check", &[]);
    assert!(!success, "{stderr}");
    let directory = format!("{}/", manifest.parent().unwrap().display());
    stderr
        .lines()
        .filter(|line| line.starts_with("error") || line.trim_start().starts_with("--> "))
        .map(|line| line.trim().replace(&directory, ""))
        .collect()
}

/// Each case's `krs check` refusal.
fn refusals<const N: usize>(cases: [(&'static str, &str); N]) -> String {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    cases
        .map(|(name, source)| {
            let manifest = package(&temporary.path().join(name), source);
            format!("{name}:\n{}", check(target.path(), &manifest).join("\n"))
        })
        .join("\n")
}

/// Alternatives of an equation's whole subject that apply different functions define no one
/// function, refused at the first that differs; alternatives that differ in both arguments of
/// a function are no one equation, refused at the `|`.
#[test]
fn root_alternatives_that_are_no_one_equation_are_refused() {
    expect_test::expect![[r"
        heads:
        error[krs::analysis::invalid-pattern-or]: an equation defines one function, and every alternative of its whole subject applies it, but this alternative applies `Tone` and the first applies `Code`; write an equation per function
        --> src/lib.rs:78:40
        arguments:
        error[krs::analysis::invalid-pattern-or]: these alternatives of an equation's whole subject differ in more than one argument; an equation matches each argument on its own, so `F(a, b) | F(c, d)` is not `F(a | c, b | d)`, which also matches `F(a, d)`: write the alternatives in the one argument where they differ, or write one equation per alternative
        --> src/lib.rs:78:13"]]
    .assert_eq(&refusals([
        (
            "heads",
            "#[k::equation]\nfn code_warm((Code { c: Cmd::Red() } | Tone { c: Cmd::Green() }): Term<Int>) -> Term<Int> {\n    10\n}\n",
        ),
                (
            "arguments",
            "#[k::equation]\nfn mix_two((Mix { c: Cmd::Red(), n: 1 } | Mix { c: Cmd::Green(), n: 2 }): Term<Int>) -> Term<Int> {\n    5\n}\n",
        ),
    ]));
}

/// A single-body rule and a simplification rewrite one term, so their subject takes no
/// alternatives, at its root as below it.
#[test]
fn a_subject_rewritten_as_one_term_refuses_root_alternatives() {
    expect_test::expect![[r"
        single-body:
        error[krs::analysis::invalid-pattern-or]: `A | B` (K's #Or) matches one of several terms, and a subject rewritten as one term in place stands for the one term it matched: write one sentence per alternative; here it stands in the subject of a single-body `#[k::rule]` fn
        --> src/lib.rs:78:8
        simplification:
        error[krs::analysis::invalid-pattern-or]: `A | B` (K's #Or) matches one of several terms, and a subject rewritten as one term in place stands for the one term it matched: write one sentence per alternative; here it stands in the subject of a `#[k::simplification]` fn
        --> src/lib.rs:78:9"]].assert_eq(&refusals([
        (
            "single-body",
            "#[k::rule(label = \"sb\")]\nfn sb((Cmd::Show { c: k::rewrite!(Cmd::Red() => Cmd::Blue()) } | Cmd::Show { c: k::rewrite!(Cmd::Green() => Cmd::Blue()) }): Term<Stmt>) {}\n",
        ),
                (
            "simplification",
            "#[k::simplification]\nfn sim((Code { c: Cmd::Red() } | Code { c: Cmd::Green() }): Term<Int>) -> Term<Int> {\n    10\n}\n",
        ),
            ]));
}
