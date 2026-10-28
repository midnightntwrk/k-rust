//! Rows of the position table (`krs_syntax::positions`) that a parser once decided, end to end:
//! authored packages through `krs check`, each refusal with its class's one code at the
//! construct.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"
use k::builtin::{Int, KSequence, Map};
use k::{KItem, KResult, Term};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Wrap, Pair, Done, Swap))]
pub enum ExpSyntax {
    #[k::syntax("wrap({e})")]
    Wrap { e: Exp },
    #[k::syntax("pair({a}, {b})")]
    Pair { a: Exp, b: Exp },
    #[k::syntax("done")]
    Done(),
    #[k::syntax("swap({e})")]
    Swap { e: Exp },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub env: Map,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Exp) -> Self {
        Self {
            k: k::k![pgm],
            env: k::map![],
        }
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

/// A one-package workspace named `rows` whose library is the preamble and `source`.
fn package(root: &Path, source: &str) -> PathBuf {
    fs::create_dir_all(root.join("src")).unwrap();
    fs::write(root.join("src/lib.rs"), format!("{PREAMBLE}{source}")).unwrap();
    let manifest = root.join("Cargo.toml");
    fs::write(
        &manifest,
        format!(
            "[package]\nname = \"rows\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-POSITION-ROWS\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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
        .args(["--package", "rows", "--definition", "main"])
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

/// `krs check` of the package: whether it passed, and its `error[..]` headlines with the
/// locations they point at.
fn check(target: &Path, manifest: &Path) -> (bool, Vec<String>) {
    let (success, _, stderr) = krs(target, manifest, "check", &[]);
    let directory = format!("{}/", manifest.parent().unwrap().display());
    let errors = stderr
        .lines()
        .filter(|line| line.starts_with("error") || line.trim_start().starts_with("--> "))
        .map(|line| line.trim().replace(&directory, ""))
        .collect();
    (success, errors)
}

/// Each case's package and its `krs check` outcome.
fn outcomes<const N: usize>(
    cases: [(&'static str, &str); N],
) -> [(&'static str, (bool, Vec<String>)); N] {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    cases.map(|(name, source)| {
        let manifest = package(&temporary.path().join(name), source);
        (name, check(target.path(), &manifest))
    })
}

/// A `let` pattern reads its value by one shape, so it takes no alias and no alternatives, in a
/// result as in a condition; the refusal points at the alias and at the `|`.
#[test]
fn a_let_pattern_takes_no_alias_and_no_alternatives() {
    let outcomes = outcomes([
        (
            "alias-in-result",
            "#[k::rule(label = \"unwrap\")]\nfn unwrap(k::term![ExpSyntax::Swap { e }]: Term<Exp>) -> Term<Exp> {\n    let w @ ExpSyntax::Wrap { .. } = e;\n    w\n}\n",
        ),
        (
            "alternatives-in-result",
            "#[k::rule(label = \"unwrap\")]\nfn unwrap(k::term![ExpSyntax::Swap { e }]: Term<Exp>) -> Term<Exp> {\n    let (ExpSyntax::Done() | ExpSyntax::Wrap { .. }) = e;\n    e\n}\n",
        ),
        (
            "alias-in-condition",
            "k::rules! {\n    for Exp;\n    use ExpSyntax::*;\n    #[k::requires({ let w @ Wrap { .. } = e; k::matches!(w, Wrap { .. }) })]\n    unwrap: Swap { e } => e;\n}\n",
        ),
    ]);
    expect_test::expect![[r#"
        [
            (
                "alias-in-result",
                (
                    false,
                    [
                        "error[krs::syntax::invalid-let]: a `let` pattern destructures one value, which a bare name already names whole: write `let p = e; let P = p;` for `p @ P`; here it stands in a `let` pattern in the result of a `#[k::rule]` fn",
                        "--> src/lib.rs:43:9",
                    ],
                ),
            ),
            (
                "alternatives-in-result",
                (
                    false,
                    [
                        "error[krs::syntax::invalid-let]: a `let` reads its value by one pattern, whose names the rest of its block uses: test which shape a value has with `k::matches!`, or match each shape in a sentence of its own; here it stands in a `let` pattern in the result of a `#[k::rule]` fn",
                        "--> src/lib.rs:43:10",
                    ],
                ),
            ),
            (
                "alias-in-condition",
                (
                    false,
                    [
                        "error[krs::syntax::invalid-let]: a `let` pattern destructures one value, which a bare name already names whole: write `let p = e; let P = p;` for `p @ P`; here it stands in a `let` pattern in the `requires` condition of a `k::rules!` sort rule",
                        "--> src/lib.rs:44:25",
                    ],
                ),
            ),
        ]
    "#]]
    .assert_debug_eq(&outcomes);
}

/// `..base` builds a record from a matched one, so a pattern refuses it at the base: a `k::term!`
/// subject, a `for Sort` clause's subject, and a readable record's computation item.
#[test]
fn a_record_update_in_a_pattern_is_refused_at_its_base() {
    let outcomes = outcomes([
        (
            "term-subject",
            "#[k::rule(label = \"open\")]\nfn open(k::term![ExpSyntax::Swap { e: ExpSyntax::Pair { a: x, ..p } }]: Term<Exp>) -> Term<Exp> {\n    x\n}\n",
        ),
        (
            "clause-subject",
            "k::rules! {\n    for Exp;\n    use ExpSyntax::*;\n    open: Swap { e: Pair { a: x, ..p } } => x;\n}\n",
        ),
        (
            "readable-item",
            "k::rules! {\n    for Machine;\n    use ExpSyntax::*;\n    open: { k: [Swap { e: Pair { a: x, ..p } }, ..] } => { k: [x, ..] };\n}\n",
        ),
    ]);
    expect_test::expect![[r#"
        [
            (
                "term-subject",
                (
                    false,
                    [
                        "error[krs::syntax::invalid-record-update]: `..base` builds a record whose unlisted fields are those of the record the alias `base` matched, which only a term a sentence builds can say; a pattern denotes no record by it, and leaves out the fields it does not constrain with `..`; here it stands in the subject of a `#[k::rule]` fn",
                        "--> src/lib.rs:42:65",
                    ],
                ),
            ),
            (
                "clause-subject",
                (
                    false,
                    [
                        "error[krs::syntax::invalid-record-update]: `..base` builds a record whose unlisted fields are those of the record the alias `base` matched, which only a term a sentence builds can say; a pattern denotes no record by it, and leaves out the fields it does not constrain with `..`; here it stands in the subject of a `k::rules!` sort rule",
                        "--> src/lib.rs:44:36",
                    ],
                ),
            ),
            (
                "readable-item",
                (
                    false,
                    [
                        "error[krs::syntax::invalid-record-update]: `..base` builds a record whose unlisted fields are those of the record the alias `base` matched, which only a term a sentence builds can say; a pattern denotes no record by it, and leaves out the fields it does not constrain with `..`; here it stands in the subject of a readable rule",
                        "--> src/lib.rs:44:42",
                    ],
                ),
            ),
        ]
    "#]].assert_debug_eq(&outcomes);
}
