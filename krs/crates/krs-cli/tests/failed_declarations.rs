//! A failed `#[k::constructors]` enum, `#[k::syntax_list]` enum, or
//! `#[k::spec_module]` is reported once, by KRS. The names it declares stay
//! declared through a stand-in the failed expansion leaves, so the imports
//! and references of other items (a rule table's `use Enum::*;`, a
//! module-level `use Enum::{..}`, a spec module's `imports = [name]`, an
//! initializer item, an overload) add no rustc error about a name the
//! program does declare.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

/// A package whose `{RESULT}`, `{SYNTAX}`, `{SEPARATOR}`, and `{SPEC}`
/// placeholders each hold either the correct spelling or one KRS mistake.
const SOURCE: &str = r#"
use k::builtin::{Int, KSequence};
use k::KItem;

k::sorts! {
    ObjectTerm: KItem;
    Special: ObjectTerm;
}

/// Objects.
#[k::constructors(sort = ObjectTerm{RESULT})]
pub enum Object {
    /// The empty object.
    #[k::syntax("foo")]
    Foo(),
    #[k::{SYNTAX}("bar({value})")]
    Bar { value: Int },
}

#[k::constructors(sort = Special, result = k::KResult)]
pub enum SpecialSyntax {
    #[k::syntax("bar({value})", overload = Object::Bar)]
    SpecialBar { value: Int },
}

#[k::syntax_list({SEPARATOR})]
pub enum Objects {
    Cons { head: Int, tail: Objects },
    Nil(),
}

pub use Object::{Bar, Foo};

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: ObjectTerm) -> Self {
        Self { k: k::k![pgm, Object::Foo()] }
    }
}

k::rules! {
    for ObjectTerm;
    use Object::*;

    step: Foo() => Bar { value: 1 };
}

k::rules! {
    for Objects;
    use Objects::*;

    shorten: Cons { head: _, tail: Nil() } => Nil();
}

#[k::spec_module(imports = [crate]{SPEC})]
mod first {}

#[k::spec_module(imports = [first])]
mod second {}
"#;

const CORRECT: [(&str, &str); 4] = [
    ("{RESULT}", ", result = k::KResult"),
    ("{SYNTAX}", "syntax"),
    ("{SEPARATOR}", "separator = \",\""),
    ("{SPEC}", ""),
];

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// Writes a one-package workspace that denies warnings, with `mistake`
/// replacing the correct spelling of its placeholder.
fn package(root: &Path, name: &str, mistake: Option<(&str, &str)>) -> PathBuf {
    let mut library = SOURCE.to_owned();
    for (placeholder, correct) in CORRECT {
        let spelling = match mistake {
            Some((wrong, spelling)) if wrong == placeholder => spelling,
            _ => correct,
        };
        library = library.replace(placeholder, spelling);
    }
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), library).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-FAILED-DECLARATIONS\"\n\n[package.metadata.krs.definitions.main]\n\n[lints.rust]\nwarnings = \"deny\"\n\n[workspace]\nresolver = \"3\"\n",
            krs_path(),
        ),
    )
    .unwrap();
    directory.join("Cargo.toml")
}

/// Runs `krs check` on the package's `main` definition.
fn check(target: &Path, manifest: &Path) -> (bool, String) {
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
    (
        output.status.success(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

#[test]
fn a_failed_declaration_reports_only_its_krs_error() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "correct", None);
    let (success, stderr) = check(target.path(), &manifest);
    assert!(success, "{stderr}");

    let cases = [
        ("family", ("{RESULT}", ""), "Object"),
        ("variant-helper", ("{SYNTAX}", "sintax"), "Object"),
        (
            "syntax-list",
            ("{SEPARATOR}", "separator = \",\", bogus"),
            "Objects",
        ),
        ("spec-module", ("{SPEC}", ", bogus"), "first"),
    ];
    for (name, mistake, declared) in cases {
        let manifest = package(temporary.path(), name, Some(mistake));
        let (success, stderr) = check(target.path(), &manifest);
        assert!(!success, "{name}: {stderr}");
        let errors = stderr
            .lines()
            .filter(|line| line.starts_with("error"))
            .collect::<Vec<_>>();
        assert_eq!(errors.len(), 1, "{name}: {stderr}");
        assert!(errors[0].starts_with("error[krs::"), "{name}: {stderr}");
        assert!(!stderr.contains("E0432"), "{name}: {stderr}");
        assert!(
            !stderr.contains(&format!("`{declared}`")),
            "{name}: {stderr}"
        );
        assert!(!stderr.contains("__krs"), "{name}: {stderr}");
    }
}
