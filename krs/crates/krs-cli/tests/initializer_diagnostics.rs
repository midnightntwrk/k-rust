//! A failed `#[k::init]` is reported once, by KRS: whether its syntax, its
//! body's shape, or one of its terms is rejected, `krs check` prints the KRS
//! error and nothing about the payload function the configuration names,
//! which the failed expansion leaves as a stand-in.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"
use k::builtin::{Id, Int, KSequence, List, Map, list, map};
use k::KResult;

k::sorts! {
    Stmt;
    Value: KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
pub enum StmtSyntax {
    #[k::syntax("skip")]
    Skip(),
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub env: Map<Id, Value>,
    #[k::cell]
    pub stack: List<Value>,
}
"#;

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
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-INIT-DIAGNOSTICS\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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

fn initializer(body: &str) -> String {
    format!(
        "impl Machine {{\n    #[k::init]\n    pub fn init(#[k::config_var(name = \"PGM\", main)] pgm: Stmt, n: Id) -> Self {{\n        {body}\n    }}\n}}\n"
    )
}

#[test]
fn a_failed_initializer_reports_only_its_krs_error() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let cases = [
        (
            "syntax",
            "Self { k: k::k![pgm], env: k::map![n -> 1 2], stack: list::empty() }",
            "krs::syntax::",
        ),
        (
            "body-shape",
            "let x = 1;\n        Self { k: k::k![pgm], env: map::empty(), stack: list::empty() }",
            "error[krs::syntax::unsupported-initializer-body]",
        ),
        (
            "expansion",
            "Self { k: k::k![pgm], env: map::empty(), stack: list::item(k::anonymous!(Value, \"_V\")) }",
            "error[krs::expand::",
        ),
    ];
    for (name, body, expected) in cases {
        let manifest = package(
            temporary.path(),
            name,
            &format!("{PREAMBLE}{}", initializer(body)),
        );
        let (success, stderr) = check(target.path(), &manifest);
        assert!(!success, "{name}: {stderr}");
        let errors = stderr
            .lines()
            .filter(|line| line.starts_with("error"))
            .collect::<Vec<_>>();
        assert_eq!(errors.len(), 1, "{name}: {stderr}");
        assert!(errors[0].contains(expected), "{name}: {stderr}");
        assert!(!stderr.contains("E0599"), "{name}: {stderr}");
        assert!(
            !stderr.contains("__krs_initializer_payload"),
            "{name}: {stderr}"
        );
    }
}

#[test]
fn a_configuration_without_an_initializer_is_reported_at_its_name() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let name = PREAMBLE.find("pub struct Machine").unwrap();
    let line = PREAMBLE[..name].lines().count() + 1;
    let location = format!("lib.rs:{line}:12");
    let removed = format!(
        "{PREAMBLE}\nimpl Machine {{\n    #[cfg(any())]\n    #[k::init]\n    pub fn init() -> Self {{\n        Self {{ k: k::k![], env: map::empty(), stack: list::empty() }}\n    }}\n}}\n"
    );
    let cases = [("missing", PREAMBLE.to_owned()), ("cfg-removed", removed)];
    for (name, library) in cases {
        let manifest = package(temporary.path(), name, &library);
        let (success, stderr) = check(target.path(), &manifest);
        assert!(!success, "{name}: {stderr}");
        let errors = stderr
            .lines()
            .filter(|line| line.starts_with("error"))
            .collect::<Vec<_>>();
        assert_eq!(
            errors,
            [
                "error[krs::expand::missing-initializer]: configuration `Machine` has no `#[k::init]` initializer"
            ],
            "{name}: {stderr}"
        );
        assert!(stderr.contains(&location), "{name}: {stderr}");
        assert!(
            stderr.contains("= note: an initializer gives each cell its initial value"),
            "{name}: {stderr}"
        );
        for internal in ["E0599", "E0277", "__krs", "__Krs"] {
            assert!(!stderr.contains(internal), "{name}: {stderr}");
        }
    }
}
