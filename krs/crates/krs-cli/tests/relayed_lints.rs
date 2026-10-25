//! Under `deny(warnings)`, rustc reports as unused an import that only a
//! failed KRS item uses, because the item's expansion was withheld. `krs check`
//! leaves out such an error when the failed item, in the import's module,
//! names the import, and reports every other unused import, one per name.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

/// A definition in which the equation alone uses `bytes`, the `for Machine`
/// table alone uses `int`, and the initializer alone uses `set`.
const DEFINITION: &str = r#"use k::{KResult, Term};
use k::builtin::{Bytes, Int, KSequence, Set, bytes, int, set};

k::sorts! {
    Object: KResult;
}

#[k::constructors(sort = Object, result = KResult)]
pub enum ObjectSyntax {
    #[k::syntax("foo")]
    Foo(),
    #[k::syntax("bar")]
    Bar(),
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub acc: Int,
    #[k::cell]
    pub seen: Set<Int>,
}

impl Machine {
    #[k::init]
    pub fn init() -> Self {
        Self {
            k: k::k![ObjectSyntax::Foo()],
            acc: 0,
            seen: set::empty(),
        }
    }
}

#[k::function(total, internal)]
pub fn Len(b: Term<Bytes>) -> Term<Int>;

#[k::equation]
fn len_bytes(k::term![Len(b)]: Term<Int>) -> Term<Int> {
    bytes::length(b)
}

k::rules! {
    for Machine;
    use ObjectSyntax::*;

    step: { k: [Foo(), ..], acc: n } => { k: [Bar(), ..], acc: int::add(n, 1) } where n: Int;
}
"#;

const GOOD_EQUATION: &str = "bytes::length(b)\n";
const BAD_EQUATION: &str = "bytes::length(k::anonymous!())\n";
const GOOD_ROW: &str = "{ k: [Foo(), ..], acc: n }";
/// `seen: _` has no effect, which KRS rejects.
const BAD_ROW: &str = "{ k: [Foo(), ..], acc: n, seen: _ }";
const GOOD_INIT: &str = "        Self {\n            k:";
const BAD_INIT: &str = "        let x = 1;\n        Self {\n            k:";

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// Writes a one-package workspace with `deny(warnings)` whose library is `library`.
fn package(root: &Path, name: &str, library: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), library).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-RELAYED-LINTS\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n\n[lints.rust]\nwarnings = \"deny\"\n",
            krs_path(),
        ),
    )
    .unwrap();
    directory.join("Cargo.toml")
}

/// The `error[..]` headlines of `krs check` on the package's `main` definition.
fn check(target: &Path, manifest: &Path) -> (Vec<String>, String) {
    let package = manifest
        .parent()
        .and_then(Path::file_name)
        .and_then(|name| name.to_str())
        .unwrap();
    let mut process = krs_command!();
    fixture_build_env(&mut process, target);
    let output = process
        .args(["check", "--manifest-path"])
        .arg(manifest)
        .args(["--package", package, "--definition", "main"])
        .env("NO_COLOR", "1")
        .output()
        .unwrap();
    assert!(!output.status.success());
    let stderr = String::from_utf8(output.stderr).unwrap();
    let errors = stderr
        .lines()
        .filter(|line| line.starts_with("error"))
        .map(|line| {
            // Keep the code and, for an unused import, the message.
            let (code, message) = line.split_once("]: ").unwrap();
            if code == "error[unused_imports" {
                format!("{code}]: {message}")
            } else {
                format!("{code}]")
            }
        })
        .collect();
    (errors, stderr)
}

fn edit(source: &str, from: &str, to: &str) -> String {
    assert_eq!(source.matches(from).count(), 1, "{from}");
    source.replace(from, to)
}

#[test]
fn imports_only_a_failed_item_names_are_not_reported_and_every_other_is() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let equation = edit(DEFINITION, GOOD_EQUATION, BAD_EQUATION);
    let table = edit(DEFINITION, GOOD_ROW, BAD_ROW);
    let both = edit(&equation, GOOD_ROW, BAD_ROW);
    let real = edit(
        &both,
        "use k::builtin::{Bytes",
        "use k::builtin::Map;\nuse k::builtin::set as s;\nuse ObjectSyntax::*;\nuse k::builtin::{Bytes",
    );
    let initializer = edit(DEFINITION, GOOD_INIT, BAD_INIT);
    // `set` is imported and unused everywhere; the failed row binds a `set`.
    let coincidence = edit(
        &edit(
            &edit(
                &table,
                "seen: set::empty()",
                "seen: k::builtin::set::empty()",
            ),
            "acc: n, seen: _ }",
            "acc: set, seen: _ }",
        ),
        "acc: int::add(n, 1) } where n: Int;",
        "acc: int::add(set, 1) } where set: Int;",
    );
    // The failed table is in an inline module: the imports of that module
    // that only it names are left out, the root's `list`, which it also names
    // but cannot see, is reported.
    let module = edit(
        &edit(
            &table,
            "use k::builtin::{Bytes",
            "use k::builtin::list;\nuse k::builtin::{Bytes",
        ),
        "k::rules! {\n    for Machine;\n    use ObjectSyntax::*;\n\n    step: { k: [Foo(), ..], acc: n, seen: _ } => { k: [Bar(), ..], acc: int::add(n, 1) } where n: Int;\n}\n",
        "mod inner {\n    use super::{Int, Machine, ObjectSyntax, int};\n\n    k::rules! {\n        for Machine;\n        use ObjectSyntax::*;\n\n        step: { k: [Foo(), ..], acc: n, seen: _ } => { k: [Bar(), ..], acc: int::add(n, list::size(n)) } where n: Int;\n    }\n}\n",
    );
    let syntax = "error[krs::syntax::rust-syntax]";
    let unused = |name: &str| format!("error[unused_imports]: unused import: `{name}`");
    let cases: [(&str, &str, Vec<String>); 7] = [
        ("equation", &equation, vec![syntax.into()]),
        ("table", &table, vec![syntax.into()]),
        ("both", &both, vec![syntax.into(), syntax.into()]),
        (
            "real",
            &real,
            vec![
                syntax.into(),
                syntax.into(),
                unused("k::builtin::Map"),
                unused("k::builtin::set as s"),
                unused("ObjectSyntax::*"),
            ],
        ),
        (
            "initializer",
            &initializer,
            vec!["error[krs::syntax::unsupported-initializer-body]".into()],
        ),
        (
            "coincidence",
            &coincidence,
            vec![syntax.into(), unused("set")],
        ),
        (
            "module",
            &module,
            vec![syntax.into(), unused("k::builtin::list")],
        ),
    ];
    for (name, library, expected) in cases {
        let manifest = package(temporary.path(), name, library);
        let (errors, stderr) = check(target.path(), &manifest);
        assert_eq!(errors, expected, "{name}:\n{stderr}");
    }
}
