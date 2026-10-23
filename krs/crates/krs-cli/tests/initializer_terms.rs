//! The terms of a `#[k::init]` initializer are KRS terms, as a rule result's
//! are: constructors (tuple-like or with fields), function applications,
//! builtin calls, and configuration variables, inside a `k::k!` item, a
//! `k::map!` key or value, or a call. rustc checks only what it can check
//! meaningfully: that each name resolves, through the payload's type keys,
//! and that a configuration variable that is a cell's whole content has the
//! cell's Rust type. KRS checks the terms' sorts. Every configuration variable
//! a term names counts as used, so a package that denies warnings builds.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"
use k::builtin::{Bytes, Id, Int, KSequence, List, Map, bytes, list};
use k::{KResult, Term};

k::sorts! {
    Stmt;
    Value: KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence((Skip, Tag, Seq))]
pub enum StmtSyntax {
    #[k::syntax("skip")]
    Skip(),
    #[k::syntax("tag {b}")]
    Tag { b: Bytes },
    #[k::syntax("seq {first} ;")]
    Seq { first: Stmt },
}

#[k::function(total, syntax = "mk({n})")]
pub fn Mk(n: Term<Int>) -> Term<Stmt>;

#[k::equation]
fn mk(n: Term<Int>, Mk(n): Term<Stmt>) -> Term<Stmt> {
    StmtSyntax::Skip()
}

#[k::function(total, syntax = "five()")]
pub fn Five() -> Term<Value>;

#[k::equation]
fn five(Five(): Term<Value>) -> Term<Value> {
    5
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub env: Map<Id, Value>,
    #[k::cell]
    pub stack: List<Stmt>,
    #[k::cell]
    pub acc: Value,
}

"#;

/// The initializer with `k` as its computation cell's value.
fn initializer(k: &str) -> String {
    format!(
        "impl Machine {{\n    #[k::init]\n    pub fn init(#[k::config_var(name = \"PGM\", main)] pgm: Stmt, n: Id, y: Stmt, x: Value) -> Self {{\n        Self {{\n            k: {k},\n            env: k::map![n -> Five()],\n            stack: list::item(y),\n            acc: x,\n        }}\n    }}\n}}\n"
    )
}

const K: &str = "k::k![pgm, StmtSyntax::Tag(bytes::empty()), Mk(1), StmtSyntax::Seq(pgm), Five()]";

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// Writes a one-package workspace whose library is `library`.
fn package(root: &Path, name: &str, library: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), library).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-INIT-TERMS\"\n\n[package.metadata.krs.definitions.main]\n\n[lints.rust]\nwarnings = \"deny\"\n\n[workspace]\nresolver = \"3\"\n",
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

/// The emitted `definition.k`.
fn emit(target: &Path, manifest: &Path) -> String {
    let output = manifest.with_file_name("emitted");
    let (success, _, stderr) = krs(
        target,
        manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    fs::read_to_string(output.join("definition.k")).unwrap()
}

/// The `configuration` declaration's cell lines.
fn configuration(definition: &str) -> String {
    let start = definition.find("configuration").unwrap();
    definition[start..]
        .lines()
        .skip(1)
        .take_while(|line| !line.trim().is_empty())
        .map(str::trim)
        .collect::<Vec<_>>()
        .join("\n")
}

#[test]
fn initializer_terms_are_krs_terms() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(
        temporary.path(),
        "terms",
        &format!("{PREAMBLE}{}", initializer(K)),
    );
    let definition = emit(target.path(), &manifest);
    expect_test::expect![[r"
        <k> $PGM:Stmt ~> tag .Bytes ~> mk ( 1 ) ~> seq $PGM:Stmt ; ~> five ( ) </k>
        <env> $N:Id |-> five ( ) </env>
        <stack> ListItem($Y:Stmt) </stack>
        <acc> $X:Value </acc>"]]
    .assert_eq(&configuration(&definition));

    // The run starts from the configuration with the functions evaluated.
    let program = manifest.with_file_name("program.txt");
    fs::write(&program, "skip").unwrap();
    let (_, stdout, stderr) = krs(
        target.path(),
        &manifest,
        "run",
        &[
            "-c",
            "N=x",
            "-c",
            "Y=skip",
            "-c",
            "X=7",
            program.to_str().unwrap(),
        ],
    );
    let state = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
    for cell in [
        r#"<k> skip ~> tag b"" ~> skip ~> seq skip ; ~> 5 ~> .K </k>"#,
        "<env> x |-> 5 </env>",
        "<stack> ListItem ( skip ) </stack>",
        "<acc> 7 </acc>",
    ] {
        assert!(state.contains(cell), "{cell}\n{stdout}\n{stderr}");
    }

    // The expanded initializer reads back to the same configuration.
    let (success, expanded, stderr) = krs(target.path(), &manifest, "expand", &[]);
    assert!(success, "{stderr}");
    let reference = package(temporary.path(), "expanded", &expanded);
    assert_eq!(
        configuration(&emit(target.path(), &reference)),
        configuration(&definition)
    );
}

#[test]
fn initializer_terms_are_resolved_by_rustc_and_sorted_by_krs() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let cases = [
        (
            "misspelled",
            "k::k![pgm, StmtSyntax::Tag(bytes::empty()), Mkk(1)]",
            "error[E0425]: cannot find type `Mkk` in this scope",
            "Mkk",
        ),
        (
            "ill-sorted",
            "k::k![pgm, StmtSyntax::Tag(bytes::empty()), StmtSyntax::Tag(x)]",
            "error[krs::analysis::invalid-term]: invalid descriptor term for ORG-KRS-INIT-TERMS::Machine (configuration): variable \"x\" has no declared common descendant for occurrence sorts [ORG-KRS-INIT-TERMS::Value (sort), Bytes]",
            "",
        ),
    ];
    for (name, k, headline, marked) in cases {
        let manifest = package(
            temporary.path(),
            name,
            &format!("{PREAMBLE}{}", initializer(k)),
        );
        let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
        assert!(!success, "{name}: {stderr}");
        let lines = stderr.lines().collect::<Vec<_>>();
        let index = lines
            .iter()
            .position(|line| line.starts_with("error"))
            .unwrap_or_else(|| panic!("{name}: {stderr}"));
        assert_eq!(lines[index], headline, "{name}: {stderr}");
        if !marked.is_empty() {
            // `--> path`, ` |`, `N | source`, ` |   ^^^`.
            let source = lines[index + 3].split_once(" | ").unwrap().1;
            let carets = lines[index + 4].split_once(" | ").unwrap().1;
            let start = carets.find('^').unwrap();
            let width = carets[start..].chars().take_while(|c| *c == '^').count();
            assert_eq!(&source[start..start + width], marked, "{name}: {stderr}");
        }
    }
}
