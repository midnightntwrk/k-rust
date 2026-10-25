//! Doc comments on the fields of production declarations (a constructor or
//! function struct, an enum variant, a syntactic list's cons variant, a
//! token's representation) document the Rust item and nothing else: the
//! package checks, and its K is byte for byte the K of the same package
//! without them. `krs expand` keeps them, and its output checks.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

/// A package with a `{DOC}` placeholder before each documentable field.
const SOURCE: &str = r#"
use k::builtin::{Int, KSequence, int};
use k::Term;

k::sorts! {
    Stmt;
}

/// Statements.
#[k::constructors(sort = Stmt, result = k::KResult)]
pub enum StmtSyntax {
    /// Tag a number.
    #[k::syntax("tag({n})")]
    Tag {
        {DOC}
        n: Int,
    },
}

#[k::constructor(sort = Stmt, syntax = "tag2({n})")]
pub struct Tag2 {
    {DOC}
    pub n: Term<Int>,
}

/// The low byte of an integer.
#[k::function(total, internal, sort = Int, syntax = "byte({value})")]
pub struct Byte {
    {DOC}
    pub value: Term<Int>,
}

#[k::equation]
fn byte(k::term![Byte(value)]: Term<Int>) -> Term<Int> {
    int::add(value, 1)
}

#[k::syntax_list(separator = ",")]
pub enum Ints {
    Cons {
        {DOC}
        head: Int,
        tail: Ints,
    },
    Nil(),
}

#[k::token(regex = "[a-z]+")]
pub struct Label(
    {DOC}
    pub String,
);

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt) -> Self {
        Self { k: k::k![pgm] }
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

/// Writes a one-package workspace that denies warnings.
fn package(root: &Path, name: &str, library: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), library).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-FIELD-DOCS\"\n\n[package.metadata.krs.definitions.main]\n\n[lints.rust]\nwarnings = \"deny\"\n\n[workspace]\nresolver = \"3\"\n",
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
        .output()
        .unwrap();
    (
        output.status.success(),
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

/// The emitted `definition.k` and `symbols.json`.
fn emit(target: &Path, manifest: &Path) -> (String, String) {
    let output = manifest.with_file_name("emitted");
    let (success, _, stderr) = krs(
        target,
        manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    (
        fs::read_to_string(output.join("definition.k")).unwrap(),
        fs::read_to_string(output.join("symbols.json")).unwrap(),
    )
}

#[test]
fn field_doc_comments_document_only_the_rust_item() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    // One package name and the same line for every token, so that the two
    // differ only in the doc comments.
    let documented = package(
        &temporary.path().join("documented"),
        "fields",
        &SOURCE.replace("{DOC}", "/// The argument."),
    );
    let plain = package(
        &temporary.path().join("plain"),
        "fields",
        &SOURCE.replace("{DOC}", ""),
    );
    let (definition, symbols) = emit(target.path(), &documented);
    assert_eq!(emit(target.path(), &plain), (definition.clone(), symbols));
    assert!(definition.contains("// Tag a number."), "{definition}");
    assert!(!definition.contains("The argument."), "{definition}");

    let (success, expanded, stderr) = krs(target.path(), &documented, "expand", &[]);
    assert!(success, "{stderr}");
    assert!(
        expanded.matches("/// The argument.").count() >= 5,
        "{expanded}"
    );
    let reference = package(temporary.path(), "expanded", &expanded);
    assert_eq!(emit(target.path(), &reference).0, definition);
}
