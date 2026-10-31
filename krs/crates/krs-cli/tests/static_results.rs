//! A desugar's or an alias's result is the term a program's expansion writes in place of the
//! production's application, which then evaluates as the same term in a rule's result does
//! (NT-20). So the program is typed over the sort predicates and projections the definition
//! generates, as the compiled definition is, while programs are parsed with the syntax as
//! written; a parametric application whose instance would follow
//! from a program's term is refused; and a rule fn whose result is a cell's value is written
//! inside the computation cell. The class tiers run the generated cases; the cases here are
//! those no generated case writes.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"
use k::builtin::{Int, KSequence};
use k::{KItem, KResult, Term};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    Leaf: KResult;
    impl Value for Int;
}

/// An identifier token, which a sort predicate's name, `isInt`, also spells.
#[k::token(regex = r"[a-z][a-zA-Z]*")]
pub struct Name(pub String);

#[k::constructors(sort = Stmt, result = KResult)]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("go")] Go(),
    #[k::syntax("say({a})")] Say { a: Name },
    #[k::syntax("said({a})")] Said { a: Name },
    #[k::syntax("hold({a})")] Hold { a: KItem },
    #[k::syntax("got({a})")] Got { a: KItem },
    #[k::syntax("uns({a})")] Uns { a: KItem },
    #[k::syntax("test({a})")] #[k::desugar] Test { a: KItem },
    #[k::syntax("keep({a})")] #[k::desugar] Keep { a: KItem },
    #[k::syntax("frame({a})")] Frame { a: KItem },
}

#[k::constructors(sort = Value, result = KResult)]
#[rustfmt::skip]
pub enum Val {
    #[k::syntax("vv")] Vv(),
}

/// A sort with no sort below it.
#[k::constructors(sort = Leaf, result = KResult)]
#[rustfmt::skip]
pub enum Leaves {
    #[k::syntax("lf")] Lf(),
}

/// A parametric constructor, whose turbofish names its instance.
#[k::constructor(sort = S, syntax = "wrap({inner})")]
pub struct Wrap<S: ?Sized> {
    pub inner: Term<S>,
}

#[k::cell]
pub struct Fr {
    #[k::cell]
    pub ret: Int,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell(nested)]
    pub fr: Fr,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            fr: Fr { ret: 0 },
        }
    }
}

#[k::rule(label = "say")]
fn say(k::term![Cmd::Say(n)]: Term<Stmt>) -> Term<Stmt> {
    Cmd::Said(n)
}

#[k::desugar]
fn test(k::term![Cmd::Test(x)]: Term<Stmt>) -> Term<Stmt> {
    Cmd::Hold(k::is!(Int, x))
}

#[k::desugar]
fn keep(k::term![Cmd::Keep(x)]: Term<Stmt>) -> Term<Stmt> {
    Cmd::Hold(x)
}

#[k::rule(label = "frame")]
fn frame(k::term![Cmd::Frame(x)]: Term<Stmt>) -> Term<KItem> {
    k::fragment![crate::Fr { ret: 1 }]
}
"#;

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// A one-package workspace named `results` whose library is the preamble and `source`.
fn package(root: &Path, source: &str) -> PathBuf {
    fs::create_dir_all(root.join("src")).unwrap();
    fs::write(root.join("src/lib.rs"), format!("{PREAMBLE}{source}")).unwrap();
    let manifest = root.join("Cargo.toml");
    fs::write(
        &manifest,
        format!(
            "[package]\nname = \"results\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-STATIC-RESULTS\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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
        .args(["--package", "results", "--definition", "main"])
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

/// Each program's final computation under `krs run --depth 2`, or its first error.
fn runs(source: &str, programs: &[&str]) -> String {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), source);
    let mut printed = Vec::new();
    for program in programs {
        let file = manifest.with_file_name("program.txt");
        fs::write(&file, program).unwrap();
        let (_, stdout, stderr) = krs(
            target.path(),
            &manifest,
            "run",
            &["--depth", "2", file.to_str().unwrap()],
        );
        let state = stdout
            .lines()
            .skip_while(|line| line.trim() != "<k>")
            .skip(1)
            .take_while(|line| line.trim() != "</k>")
            .map(str::trim)
            .collect::<Vec<_>>()
            .join(" ");
        let shown = if state.is_empty() {
            stderr
                .lines()
                .find(|line| line.starts_with("error"))
                .unwrap_or_default()
                .to_owned()
        } else {
            state
        };
        printed.push(format!("{program} => {shown}"));
    }
    printed.join("\n")
}

/// A program is parsed with its syntax as written, so an identifier spelled as a sort predicate
/// (`isInt`, `isStmt`) is still an identifier; on the first NT-20 branch, which parsed programs
/// over the predicates too, `say(isInt)` did not parse. A desugar's `k::is!` result is typed over
/// the generated predicate, so `test(1)` expands to `hold(true)`, as a rule's result evaluates
/// it. A rule fn whose result is a cell's value replaces its item by the value inside the
/// computation cell, as the `for Stmt` clause does.
#[test]
fn a_static_result_evaluates_as_in_a_rule_and_programs_keep_their_syntax() {
    expect_test::expect![[r"
        say(isInt) => said(isInt) ~> .K
        say(isStmt) => said(isStmt) ~> .K
        test(1) => hold(true) ~> .K
        keep(vv) => hold(vv) ~> .K
        frame(1) => <fr> <ret> 1 </ret> </fr> ~> .K"]]
    .assert_eq(&runs(
        "",
        &[
            "say(isInt)",
            "say(isStmt)",
            "test(1)",
            "keep(vv)",
            "frame(1)",
        ],
    ));
}

/// A static clause's `KItem` binder should match a program's term of every sort, as a rule's
/// does (`cq(go)` runs), but `keep(go)` survives the program's expansion while `keep(1)` expands
/// (finding NT-20-1): k-rust's macro matcher compares a binder's sort with the subject's over the
/// subsorts the definition declares (`expand_macros.rs`), which lack K's `S < KItem` for a sort
/// declared below no other (`Stmt` here; `Value`, a `KResult`, has the edge). The expected output
/// is the run it should give.
#[test]
#[ignore = "finding NT-20-1: a static clause's KItem binder does not match a term of a sort the definition declares below no sort"]
fn a_static_kitem_binder_matches_a_term_of_every_sort() {
    expect_test::expect![[r"
        keep(go) => hold(go) ~> .K"]]
    .assert_eq(&runs("", &["keep(go)"]));
}

/// A parametric application in a static result whose instance follows from a binder of a sort
/// with a sort below it is refused (finding NT-12-2): with `Value < Stmt`, the desugar
/// `dus(x: Stmt) => uns(Wrap::<Stmt>(x))` expanded `dus(vv)` to `wrap` at `Value`, which the rule
/// `uns(Wrap::<Stmt>(y)) => got(y)` does not match, where the rule `rus(vv)` gives `got(vv)`. A
/// binder whose sort has none below it keeps the instance and is admitted.
#[test]
fn a_static_result_whose_instance_a_program_term_would_choose_is_refused() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let source = "
#[k::constructors(sort = Stmt, result = KResult)]
#[rustfmt::skip]
pub enum More {
    #[k::syntax(\"dus({a})\")] #[k::desugar] Dus { a: Stmt },
}

#[k::desugar]
fn dus(k::term![More::Dus(x)]: Term<Stmt>) -> Term<Stmt> {
    Cmd::Uns(Wrap::<dyn StmtSort>(x))
}
";
    let manifest = package(&temporary.path().join("refused"), source);
    let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
    assert!(!success, "{stderr}");
    let directory = format!("{}/", manifest.parent().unwrap().display());
    let lines = stderr
        .lines()
        .map(str::trim)
        .filter(|line| line.starts_with("error") || line.starts_with("--> "))
        .map(|line| line.replace(&directory, ""))
        .collect::<Vec<_>>()
        .join("\n");
    expect_test::expect![[r"
        error[krs::analysis::parametric-instance]: `Wrap::<Stmt>` in the result of desugar clause `dus` takes its instance from `x`, a `Stmt`: a program's expansion writes the program's term in `x`'s place, and a value takes its instance from its arguments, so where the program writes a term of a sort below `Stmt` the application is at that sort, another term than the clause states; write the clause as a rule, `#[k::rule(..)]`, whose result keeps `x` at `Stmt`
        --> src/lib.rs:101:14"]].assert_eq(&lines);
    let admitted = "
#[k::constructors(sort = Stmt, result = KResult)]
#[rustfmt::skip]
pub enum More {
    #[k::syntax(\"dui({a})\")] #[k::desugar] Dui { a: Leaf },
}

#[k::desugar]
fn dui(k::term![More::Dui(x)]: Term<Stmt>) -> Term<Stmt> {
    Cmd::Hold(Wrap::<dyn LeafSort>(x))
}
";
    expect_test::expect!["dui(lf) => hold(wrap ( lf )) ~> .K"]
        .assert_eq(&runs(admitted, &["dui(lf)"]));
}
