//! Builtin `Bytes` and `Id` literals in rules: `k::bytes!(b"..")` is one
//! constant of the builtin `Bytes` sort and `k::id!("$x")` one of `Id`,
//! wherever they stand, so a rule matches or builds them as a claim does.
//! Each sentence form that holds a term (a readable rule, a `cells!` rule,
//! an equation, a `k::equations!` row, a function's branching body) emits
//! the literal and runs.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const LIBRARY: &str = r#"
use k::builtin::{Bytes, Id, Int, KSequence, List, bytes, int, list};
use k::KResult;

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence(cmd (Push, Pop, Swap, Score, Name, Tag, Named) > right seq (Seq))]
pub enum Cmd {
    #[k::syntax("push")]
    Push(),
    #[k::syntax("pop")]
    Pop(),
    #[k::syntax("swap")]
    Swap(),
    #[k::syntax("score")]
    Score(),
    #[k::syntax("name")]
    Name(),
    #[k::syntax("tag({b})")]
    Tag { b: Bytes },
    #[k::syntax("named({id})")]
    Named { id: Id },
    #[k::syntax("{first} {second}")]
    Seq { first: Stmt, second: Stmt },
}

k::rules! {
    for Stmt;
    use Cmd::*;

    seq: Seq(s1, s2) => k::k![s1, s2];
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub stack: List,
    #[k::cell]
    pub score: Int,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt) -> Self {
        Self { k: k::k![pgm], stack: list::empty(), score: 0 }
    }
}

k::rules! {
    for Machine;
    use Cmd::*;

    push: { k: [Push(), ..], stack: s } => {
        k: [..],
        stack: list::concat(list::item(Tag { b: k::bytes!(b"\x7fELF") }), s),
    };
    pop: { k: [Pop(), ..], stack: list::concat(list::item(Tag { b: k::bytes!(b"\x01") }), s) } => {
        k: [..],
        stack: s,
    };
    name: { k: [Name(), ..], stack: s } => {
        k: [..],
        stack: list::concat(list::item(Named { id: k::id!("$main") }), s),
    };
    score: { k: [Score(), ..], stack: list::concat(list::item(Tag { b }), s), score: _ } => {
        k: [..],
        stack: s,
        score: int::add(int::mul(10, IsElf(b)), int::add(Kind(b), bytes::length(Next(b)))),
    };
}

/// `swap` written as a reference `cells!` rule.
#[k::rule(label = "swap")]
pub fn swap(
    s: k::Term<List>,
    k::cells! {
        k: k::configuration::KCell(crate::Cmd::Swap(), tail @ ..),
        stack: k::configuration::Cell(list::concat(list::item(crate::Cmd::Tag { b: k::bytes!(b"\x7fELF") }), s)),
        state @ ..
    }: crate::Machine,
) -> crate::Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        stack: k::configuration::Cell(list::concat(list::item(crate::Cmd::Tag { b: k::bytes!(b"\x01") }), s)),
        ..state
    }
}

#[k::function(total, syntax = "isElf({b})")]
pub fn IsElf(b: k::Term<Bytes>) -> k::Term<Int>;

#[k::equation]
fn is_elf(IsElf(k::bytes!(b"\x7fELF")): k::Term<Int>) -> k::Term<Int> {
    1
}

#[k::equation(owise)]
fn is_not_elf(b: k::Term<Bytes>, IsElf(b): k::Term<Int>) -> k::Term<Int> {
    0
}

#[k::function(total, syntax = "kind({b})")]
pub fn Kind(b: k::Term<Bytes>) -> k::Term<Int>;

k::equations! {
    for Kind;
    kind_one: k::bytes!(b"\x01") => 5;
    #[k::equation(owise)]
    kind_other: _ => 3;
}

#[k::function(total, internal)]
pub fn Next(b: k::Term<Bytes>) -> k::Term<Bytes> {
    match b {
        k::bytes!(b"\x7fELF") => k::bytes!(b"\x00\x00"),
        _ => k::bytes!(b""),
    }
}
"#;

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

fn package(root: &Path, name: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), LIBRARY).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-LITERALS\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
            krs_path(),
        ),
    )
    .unwrap();
    directory.join("Cargo.toml")
}

fn krs(target: &Path, manifest: &Path, command: &str, extra: &[&str]) -> (bool, String, String) {
    let mut process = krs_command!();
    fixture_build_env(&mut process, target);
    let output = process
        .args([command, "--manifest-path"])
        .arg(manifest)
        .args(["--package", "rule-literals", "--definition", "main"])
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

/// The final `k`, `stack`, and `score` contents after `krs run`.
fn run(target: &Path, manifest: &Path, program: &str) -> String {
    let file = manifest.with_file_name("program.txt");
    fs::write(&file, program).unwrap();
    let (success, stdout, stderr) = krs(target, manifest, "run", &[file.to_str().unwrap()]);
    assert!(success, "`krs run {program}` failed:\n{stdout}\n{stderr}");
    let lines = stdout.lines().map(str::trim).collect::<Vec<_>>();
    let cell = |name: &str| {
        let start = lines
            .iter()
            .position(|line| *line == format!("<{name}>"))
            .unwrap_or_else(|| panic!("no <{name}> cell:\n{stdout}"));
        let end = start
            + lines[start..]
                .iter()
                .position(|line| *line == format!("</{name}>"))
                .unwrap();
        lines[start + 1..end].join(" ")
    };
    format!(
        "{program} => k: {} | stack: {} | score: {}",
        cell("k"),
        cell("stack"),
        cell("score")
    )
}

#[test]
fn rules_match_and_build_bytes_and_id_literals() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "rule-literals");
    let output = manifest.with_file_name("emitted");
    let (success, _, stderr) = krs(
        target.path(),
        &manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    let k = fs::read_to_string(output.join("definition.k")).unwrap();
    for expected in [
        r#"<stack> S:List => ListItem(tag ( b"\x7f\x45\x4c\x46" )) S:List </stack>"#,
        r#"<stack> ListItem(tag ( b"\x01" )) S:List => S:List </stack>"#,
        r#"<stack> S:List => ListItem(named ( #token("$main","Id") )) S:List </stack>"#,
        r#"<stack> ListItem(tag ( b"\x7f\x45\x4c\x46" )) S:List => ListItem(tag ( b"\x01" )) S:List </stack>"#,
        r#"rule isElf ( b"\x7f\x45\x4c\x46" ) => 1"#,
        r#"rule kind ( b"\x01" ) => 5"#,
        r#"rule next ( b"\x7f\x45\x4c\x46" ) => b"\x00\x00""#,
    ] {
        assert!(k.contains(expected), "{expected}\n{k}");
    }
    expect_test::expect![[r"
        push score => k: .K | stack: .List | score: 15
        push swap score => k: .K | stack: .List | score: 5
        push swap pop name => k: .K | stack: ListItem ( named($main) ) | score: 0"]]
    .assert_eq(
        &["push score", "push swap score", "push swap pop name"]
            .map(|program| run(target.path(), &manifest, program))
            .join("\n"),
    );
}
