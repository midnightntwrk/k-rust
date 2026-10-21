//! `k::bits!` templates end to end: authored packages through `krs check`
//! and `krs run`, which run the macro and the collector's reparse on the same
//! source, so a template whose long form differs between them fails as a
//! stale anchor.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"
use k::builtin::{Int, KSequence};
use k::{KResult, Term};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((FieldOf, AliasOf, PairOf, SpliceOf, CodeOf))]
pub enum ExpSyntax {
    #[k::syntax("fieldOf({n})")]
    FieldOf { n: Int },
    #[k::syntax("aliasOf({n})")]
    AliasOf { n: Int },
    #[k::syntax("pairOf({a}, {b})")]
    PairOf { a: Int, b: Int },
    #[k::syntax("spliceOf({n})")]
    SpliceOf { n: Int },
    #[k::syntax("codeOf({n})")]
    CodeOf { n: Int },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self { k: k::k![pgm] }
    }
}

#[k::function(total, internal)]
pub fn Code(value: Term<Int>) -> Term<Int>;
"#;

/// Templates beside an authored top-level `||` in a table row and in an
/// `#[k::equation]` fn.
const POSITIVE: &str = r#"
k::rules! {
    for Exp;
    use ExpSyntax::*;

    code_of: CodeOf(n) => crate::Code(n);
}

k::equations! {
    for Code;
    #[k::requires(a.gt::<Int>(2) || a.eq::<Int>(0))]
    code_row: k::bits!("10 aa") => a;
    #[k::equation(owise)]
    code_other: n => 100;
}

#[k::requires(b.eq::<Int>(1) || b.eq::<Int>(2))]
#[k::equation]
fn code_fn(k::term![Code(k::bits!("01 bb"))]: Term<Int>) -> Term<Int> {
    b.add::<Int>(10)
}
"#;

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// Writes a one-package workspace whose library is the preamble and `source`.
fn package(root: &Path, name: &str, source: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), format!("{PREAMBLE}{source}")).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-BITS-{}\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
            krs_path(),
            name.to_ascii_uppercase()
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

/// The head of `<k>` after `krs run` of `program`.
fn run(target: &Path, manifest: &Path, program: &str) -> String {
    let file = manifest.with_file_name("program.txt");
    fs::write(&file, program).unwrap();
    let (_, stdout, stderr) = krs(target, manifest, "run", &[file.to_str().unwrap()]);
    let mut lines = stdout.lines().skip_while(|line| line.trim() != "<k>");
    lines.nth(1).map_or_else(
        || panic!("`krs run {program}` printed no <k> cell:\n{stdout}\n{stderr}"),
        |line| line.trim().trim_end_matches(" ~> .K").to_owned(),
    )
}

#[test]
fn or_conditions_beside_templates_run() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "positive", POSITIVE);
    let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
    assert!(success, "{stderr}");
    let outcomes = [
        "codeOf(8)",
        "codeOf(11)",
        "codeOf(9)",
        "codeOf(5)",
        "codeOf(4)",
    ]
    .map(|program| format!("{program} => {}", run(target.path(), &manifest, program)));
    expect_test::expect![[r#"
        [
            "codeOf(8) => 0",
            "codeOf(11) => 3",
            "codeOf(9) => 100",
            "codeOf(5) => 11",
            "codeOf(4) => 100",
        ]
    "#]]
    .assert_debug_eq(&outcomes);
}
