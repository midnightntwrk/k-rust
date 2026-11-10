//! The map from an author's Rust names to the emitted K names: every name rustc accepts either
//! becomes a K name that means what the Rust name means, distinct from every other name of its
//! K namespace, or is refused with an author code whose reason names both Rust names.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const LIBRARY: &str = r#"use k::KResult;
use k::builtin::{Int, KSequence, int};
use k::Term;

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
pub enum StmtSyntax {
    #[k::syntax("skip")]
    Skip(),
    #[k::syntax("wrap({s})")]
    Wrap { s: Stmt },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub acc: Int,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt) -> Self {
        Self { k: k::k![pgm], acc: 0 }
    }
}

#[k::function(total, internal)]
pub fn PickF(b: Term<Int>) -> Term<Int>;

k::equations! {
    for PickF;
    table: (b) => int::add(b, 1);
}

k::rules! {
    for Machine;
    use StmtSyntax::*;
    unwrap: { k: [Wrap { s }, ..], acc: v } => { k: [s, ..], acc: PickF(v) };
}
"#;

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// Writes a one-package workspace named `name`, in the directory `directory`, whose library is
/// `library`.
fn package(root: &Path, directory: &str, name: &str, library: &str) -> PathBuf {
    let directory = root.join(directory);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), library).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-NAME-MAP\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
            krs_path(),
        ),
    )
    .unwrap();
    directory.join("Cargo.toml")
}

/// Runs `krs <command>` on the package `package`'s `main` definition.
fn krs(
    target: &Path,
    manifest: &Path,
    package: &str,
    command: &str,
    extra: &[&str],
) -> (bool, String, String) {
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

/// The emitted `definition.k` without its header line and the package-relative source comments,
/// which name the package.
fn emitted_k(target: &Path, manifest: &Path, package: &str, output: &Path) -> String {
    let (success, _, stderr) = krs(
        target,
        manifest,
        package,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    fs::read_to_string(output.join("definition.k"))
        .unwrap()
        .lines()
        .skip(1)
        .filter(|line| !line.trim_start().starts_with("// KRS "))
        .collect::<Vec<_>>()
        .join("\n")
}

/// A package whose name is a Rust keyword is a crate rustc names by the raw identifier
/// (`module_path!()` writes `r#let`), which is the identifier `let`: its items are the selected
/// target's, so it checks, and its K is the K of the same library under another name.
#[test]
fn a_package_named_by_a_keyword_is_its_crate() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let keyword = package(temporary.path(), "keyword", "let", LIBRARY);
    let plain = package(temporary.path(), "plain", "name_map_plain", LIBRARY);
    let (success, _, stderr) = krs(target.path(), &keyword, "let", "check", &[]);
    assert!(success, "{stderr}");
    assert_eq!(
        emitted_k(
            target.path(),
            &keyword,
            "let",
            &temporary.path().join("keyword-out")
        ),
        emitted_k(
            target.path(),
            &plain,
            "name_map_plain",
            &temporary.path().join("plain-out")
        ),
    );
}
