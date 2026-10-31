//! A desugar's or an alias's result is the term a program's expansion writes in place of the
//! production's application, which then evaluates as the same term in a rule's result does
//! (NT-20). So the program is typed over the sort predicates and projections the definition
//! generates, as the compiled definition is, while programs are parsed with the syntax as
//! written; a parametric application keeps the instance its clause states, whatever term a
//! program binds; and a rule fn whose result is a cell's value is written inside the computation
//! cell. The class tiers run the generated cases; the cases here are
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

/// A static clause's `KItem` binder matches a program's term of every sort, as a rule's does:
/// every sort is below `KItem` in the order a program is expanded under, so `keep(go)` expands as
/// `keep(1)` does, though `Stmt` is declared below no sort (finding NT-20-1, where `keep(go)`
/// survived the expansion).
#[test]
fn a_static_kitem_binder_matches_a_term_of_every_sort() {
    expect_test::expect![[r"
        keep(go) => hold(go) ~> .K
        keep(1) => hold(1) ~> .K"]]
    .assert_eq(&runs("", &["keep(go)", "keep(1)"]));
}

/// A parametric application in a static result is at the instance the clause's typing gives it,
/// whatever term a program binds in its binders' places (finding NT-12-2): with `Value < Stmt`,
/// the desugar `dus(x: Stmt) => uns(Wrap::<Stmt>(x))` expands `dus(vv)` to `wrap` at `Stmt` over
/// `vv`, which the rule `uns(Wrap::<Stmt>(y)) => got(y)` matches, as it matches the rule result
/// `rus(vv)` writes. A binder whose sort has none below it keeps the instance too.
#[test]
fn a_static_result_keeps_the_instance_its_clause_states() {
    let source = "
#[k::constructors(sort = Stmt, result = KResult)]
#[rustfmt::skip]
pub enum More {
    #[k::syntax(\"dus({a})\")] #[k::desugar] Dus { a: Stmt },
    #[k::syntax(\"rus({a})\")] Rus { a: Stmt },
    #[k::syntax(\"dui({a})\")] #[k::desugar] Dui { a: Leaf },
}

#[k::desugar]
fn dus(k::term![More::Dus(x)]: Term<Stmt>) -> Term<Stmt> {
    Cmd::Uns(Wrap::<dyn StmtSort>(x))
}

#[k::rule(label = \"rus\")]
fn rus(k::term![More::Rus(x)]: Term<Stmt>) -> Term<Stmt> {
    Cmd::Uns(Wrap::<dyn StmtSort>(x))
}

#[k::rule(label = \"uns\")]
fn uns(k::term![Cmd::Uns(Wrap::<dyn StmtSort>(y))]: Term<Stmt>) -> Term<Stmt> {
    Cmd::Got(y)
}

#[k::desugar]
fn dui(k::term![More::Dui(x)]: Term<Stmt>) -> Term<Stmt> {
    Cmd::Hold(Wrap::<dyn LeafSort>(x))
}
";
    expect_test::expect![[r"
        dus(vv) => got(vv) ~> .K
        rus(vv) => got(vv) ~> .K
        dus(go) => got(go) ~> .K
        dui(lf) => hold(wrap ( lf )) ~> .K"]]
    .assert_eq(&runs(source, &["dus(vv)", "rus(vv)", "dus(go)", "dui(lf)"]));
}

/// A later clause's subject matches a parametric constructor's application by its instance, and
/// a binding an earlier clause placed at its binder's sort as what it places (NT-22 review M1):
/// `mk(vv, go)` expands to the pair at `Stmt` over `vv` injected into `Stmt`, which the subject
/// `pick(Pair::<Stmt>(vv, y))` matches, as it matches the program's own `pick(pair(vv, go))`;
/// `mk(go, go)` meets the other clause, `pick(Pair::<Stmt>(go, y))`. The two subjects are
/// disjoint, as a static production's clauses must be, so a program's term that neither matched
/// would survive expansion and fail the run.
#[test]
fn a_static_subject_matches_a_placed_binding_by_its_instance() {
    let source = "
/// A parametric pair, whose turbofish names its instance.
#[k::constructor(sort = S, syntax = \"pair({a}, {b})\")]
pub struct Pair<S: ?Sized> {
    pub a: Term<S>,
    pub b: Term<S>,
}

#[k::constructors(sort = Stmt, result = KResult)]
#[rustfmt::skip]
pub enum More {
    #[k::syntax(\"mk({a}, {b})\")] #[k::desugar] Mk { a: Stmt, b: Stmt },
    #[k::syntax(\"pick({a})\")] #[k::desugar] Pick { a: Stmt },
}

#[k::desugar]
fn mk(k::term![More::Mk(x, z)]: Term<Stmt>) -> Term<Stmt> {
    More::Pick(Pair::<dyn StmtSort>(x, z))
}

#[k::desugar]
fn pick_vv(k::term![More::Pick(Pair::<dyn StmtSort>(Val::Vv(), y))]: Term<Stmt>) -> Term<Stmt> {
    Cmd::Got(1)
}

#[k::desugar]
fn pick_go(k::term![More::Pick(Pair::<dyn StmtSort>(Cmd::Go(), y))]: Term<Stmt>) -> Term<Stmt> {
    Cmd::Got(2)
}
";
    expect_test::expect![[r"
        mk(vv, go) => got(1) ~> .K
        pick(pair(vv, go)) => got(1) ~> .K
        mk(go, go) => got(2) ~> .K"]]
    .assert_eq(&runs(
        source,
        &["mk(vv, go)", "pick(pair(vv, go))", "mk(go, go)"],
    ));
}

/// A later desugar's subject with a repeated binder matches the term an earlier desugar's result
/// writes with one binding twice: `same(go)` expands to `twin(pair(go, go))`, whose two arguments
/// are one term, so the subject `twin(Pair::<Stmt>(a, a))` matches it and the run ends at
/// `got(3)`, as it does for the program's own `twin(pair(go, go))`. Finding NT-22-F1 was this
/// program beside a catch-all clause `twin(w)`: `krs run` applied the catch-all, krust's `krun`
/// of the same emitted K the other clause, each by its own order of two clauses that both match.
/// Two such clauses are now refused (`alias_clauses.rs`,
/// `two_static_clauses_whose_subjects_overlap_are_refused`), and the production here has one.
#[test]
fn a_later_desugar_matches_a_repeated_binder_against_an_earlier_one_s_result() {
    let source = "
/// A parametric pair, whose turbofish names its instance.
#[k::constructor(sort = S, syntax = \"pair({a}, {b})\")]
pub struct Pair<S: ?Sized> {
    pub a: Term<S>,
    pub b: Term<S>,
}

#[k::constructors(sort = Stmt, result = KResult)]
#[rustfmt::skip]
pub enum Tw {
    #[k::syntax(\"same({a})\")] #[k::desugar] Same { a: Stmt },
    #[k::syntax(\"twin({a})\")] #[k::desugar] Twin { a: Stmt },
}

#[k::desugar]
fn same(k::term![Tw::Same(x)]: Term<Stmt>) -> Term<Stmt> {
    Tw::Twin(Pair::<dyn StmtSort>(x, x))
}

#[k::desugar]
fn twin_equal(k::term![Tw::Twin(Pair::<dyn StmtSort>(a, a))]: Term<Stmt>) -> Term<Stmt> {
    Cmd::Got(3)
}
";
    expect_test::expect![[r"
        same(go) => got(3) ~> .K
        twin(pair(go, go)) => got(3) ~> .K"]]
    .assert_eq(&runs(source, &["same(go)", "twin(pair(go, go))"]));
}
