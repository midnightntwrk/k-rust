//! Constructs the language admits that KRS refused with an internal error before NT-28, each run
//! where it is accepted: a context alias's frame holding a parametric application with its
//! turbofish or a `_` item (its pattern's islands were not keyed, `missing-provenance-key`), a
//! record update in a single-body rule's rewrite right side (the wire refused its variable base,
//! `provenance-mismatch`), and constants whose value is a turbofish application or a collection's
//! unit, each used in a pattern and in a result (refused as not ground). The class tiers accept
//! the generated cases; K7 has no driver for a context alias, and the generated constants are
//! used nowhere, so the runs that show what each construct means are here.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const SOURCE: &str = r#"
use k::builtin::{Int, KSequence, Map, int};
use k::{KItem, KResult, Term};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

/// A parametric constructor, whose turbofish names its instance.
#[k::constructor(sort = S, syntax = "wrap({inner})")]
pub struct Wrap<S: ?Sized> {
    pub inner: Term<S>,
}

#[k::constructors(sort = Exp, result = KResult)]
#[rustfmt::skip]
pub enum Op {
    #[k::syntax("twice({operand})")] #[k::strict(using = before_wrapped)]
    Twice { operand: Exp },
    #[k::syntax("once({operand})")] #[k::strict(using = before_any)]
    Once { operand: Exp },
    #[k::syntax("add({lhs}, {rhs})")] Add { lhs: Exp, rhs: Exp },
    #[k::syntax("seq({first}, {then})")] Seq { first: KItem, then: KItem },
    #[k::syntax("mark({a})")] Mark { a: KItem },
    #[k::syntax("go")] Go(),
    #[k::syntax("done")] Done(),
    #[k::syntax("pair({a}, {b})")] Pair { a: KItem, b: KItem },
    #[k::syntax("pr({a}, {b})")] Pr { a: KItem, b: KItem },
    #[k::syntax("check({a})")] Check { a: KItem },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Exp) -> Self {
        Self { k: k::k![pgm] }
    }
}

/// Evaluate `twice`'s operand only before a mark of a wrapped term.
#[k::context_alias(name = before_wrapped, here = site)]
fn before_wrapped(
    k::cells! {
        k: k::configuration::KCell(site, Op::Mark(Wrap::<dyn ExpSort>(_)), tail @ ..),
        state @ ..
    }: Machine,
) {
}

/// Evaluate `once`'s operand only before some item.
#[k::context_alias(name = before_any, here = site)]
fn before_any(
    k::cells! { k: k::configuration::KCell(site, _, tail @ ..), state @ .. }: Machine,
) {
}

#[k::constant]
const WRAPPED: Exp = Op::Mark(Wrap::<dyn ExpSort>(Op::Go()));

#[k::constant]
const EMPTY: Map = map![];

k::rules! {
    for Exp;
    use Op::*;

    twice: Twice(o) => int::add(o, o) where o: Int;
    once : Once(o) => o where o: Int;
    add  : Add(l, r) => int::add(l, r) where l: Int, r: Int;
    check: Check(WRAPPED) => Pair(WRAPPED, EMPTY);
    empty: Pair(_, EMPTY) => Done();
}

/// Split a `seq` into its two items.
#[k::rule(label = "seq")]
pub fn seq(
    first: KItem,
    then: KItem,
    k::cells! { k: k::configuration::KCell(Op::Seq(first, then), tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(first, then, ..tail), ..state }
}

/// Keep a pair's second field and write its first.
#[k::rule(label = "update")]
fn update(
    k::term![Op::Pr(k::rewrite!(Op::Go() => Op::Done()), k::rewrite!(y @ Op::Pair { .. } => Op::Pair { a: 1, ..y }))]: Term<Exp>,
) {
}
"#;

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// A one-package workspace named `admitted` whose library is [`SOURCE`].
fn package(root: &Path) -> PathBuf {
    fs::create_dir_all(root.join("src")).unwrap();
    fs::write(root.join("src/lib.rs"), SOURCE).unwrap();
    let manifest = root.join("Cargo.toml");
    fs::write(
        &manifest,
        format!(
            "[package]\nname = \"admitted\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-ADMITTED\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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
        .args(["--package", "admitted", "--definition", "main"])
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

/// The definition passes `krs check`, and each program runs as written: `twice` heats its
/// operand only where a mark of a wrapped term follows (its alias's frame), and `once` only where
/// some item follows (`_`); the rewrite's record update writes `a` and keeps `b`; and `check`
/// matches exactly the constant's term, builds the pair holding it and the empty map, which the
/// `empty` clause then matches through the other constant.
#[test]
fn admitted_constructs_check_and_run_as_written() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path());
    let (passed, _, stderr) = krs(target.path(), &manifest, "check", &[]);
    assert!(passed, "{stderr}");
    let mut printed = Vec::new();
    for program in [
        "seq(twice(add(1, 2)), mark(wrap(done)))",
        "seq(twice(add(1, 2)), mark(7))",
        "seq(once(add(1, 2)), go)",
        "once(add(1, 2))",
        "pr(go, pair(2, 3))",
        "check(mark(wrap(go)))",
        "check(mark(wrap(done)))",
    ] {
        let file = manifest.with_file_name("program.txt");
        fs::write(&file, program).unwrap();
        let (_, stdout, stderr) = krs(target.path(), &manifest, "run", &[file.to_str().unwrap()]);
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
    expect_test::expect![[r"
        seq(twice(add(1, 2)), mark(wrap(done))) => 6 ~> mark(wrap ( done )) ~> .K
        seq(twice(add(1, 2)), mark(7)) => twice(add(1, 2)) ~> mark(7) ~> .K
        seq(once(add(1, 2)), go) => 3 ~> go ~> .K
        once(add(1, 2)) => once(add(1, 2)) ~> .K
        pr(go, pair(2, 3)) => pr(done, pair(1, 3)) ~> .K
        check(mark(wrap(go))) => done ~> .K
        check(mark(wrap(done))) => check(mark(wrap ( done ))) ~> .K"]]
    .assert_eq(&printed.join("\n"));
}
