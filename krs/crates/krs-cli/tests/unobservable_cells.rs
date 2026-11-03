//! `#[k::cell(unobservable)]` states that a cell holds state no use of the definition may
//! observe. It changes nothing the definition computes: KRS emits it as the K cell property
//! `unobservable=""`, k-rust accepts it from the in-process adapter, and a run is unchanged.
//! A cell every run observes cannot carry it: the exit cell, a stream cell, or a cell holding
//! either.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"
use k::builtin::{Int, KSequence, List, list};
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
"#;

/// A nested cell holding an unobservable temporary, and an unobservable top-level cell.
const ACCEPTED: &str = r#"
#[k::cell]
pub struct Temps {
    #[k::cell(unobservable)]
    pub w: Int,
    #[k::cell]
    pub z: Int,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell(nested)]
    pub temps: Temps,
    #[k::cell(unobservable)]
    pub scratch: Int,
    #[k::cell(stream = "stdout")]
    pub output: List,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            temps: Temps { w: 0, z: 0 },
            scratch: 0,
            output: list::empty(),
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

/// Writes a one-package workspace whose library is `library`.
fn package(root: &Path, name: &str, library: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), library).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-UNOBSERVABLE\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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
fn an_unobservable_cell_is_emitted_compiled_and_run() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(
        temporary.path(),
        "unobservable",
        &format!("{PREAMBLE}{ACCEPTED}"),
    );
    let output = manifest.with_file_name("emitted");
    let (success, _, stderr) = krs(
        target.path(),
        &manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    let definition = fs::read_to_string(output.join("definition.k")).unwrap();
    expect_test::expect![[r#"
        <k> $PGM:Stmt </k>
        <temps>
        <w unobservable=""> 0 </w>
        <z> 0 </z>
        </temps>
        <scratch unobservable=""> 0 </scratch>
        <output stream="stdout"> .List </output>"#]]
    .assert_eq(&configuration(&definition));

    // `krs check` compiles the definition through k-rust's structured seam, which reads the
    // property from the adapter's cell property list.
    let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
    assert!(success, "{stderr}");

    let program = manifest.with_file_name("program.txt");
    fs::write(&program, "skip").unwrap();
    let (success, stdout, stderr) = krs(
        target.path(),
        &manifest,
        "run",
        &[program.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    assert!(stdout.contains("<scratch>"), "{stdout}");
}

#[test]
fn a_cell_every_run_observes_cannot_be_unobservable() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let cases = [
        (
            "exit",
            r#"
#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell(exit, unobservable)]
    pub status: Int,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self { k: k::k![pgm], status: 0 }
    }
}
"#,
            "cell `status` cannot be unobservable: its final value is the process exit status",
        ),
        (
            "stream",
            r#"
#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell(stream = "stdout", unobservable)]
    pub output: List,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self { k: k::k![pgm], output: list::empty() }
    }
}
"#,
            "cell `output` cannot be unobservable: its content is console input or output",
        ),
        (
            "holder",
            r#"
#[k::cell]
pub struct Io {
    #[k::cell(stream = "stdout")]
    pub output: List,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell(nested, unobservable)]
    pub io: Io,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self { k: k::k![pgm], io: Io { output: list::empty() } }
    }
}
"#,
            "cell `io` cannot be unobservable: it holds the stream cell `output`, whose content is console input or output",
        ),
    ];
    for (name, configuration, expected) in cases {
        let manifest = package(
            temporary.path(),
            &format!("unobservable-{name}"),
            &format!("{PREAMBLE}{configuration}"),
        );
        let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
        assert!(!success, "{name}: {stderr}");
        let errors = stderr
            .lines()
            .filter(|line| line.starts_with("error"))
            .collect::<Vec<_>>();
        assert_eq!(errors.len(), 1, "{name}: {stderr}");
        assert!(
            errors[0].starts_with("error[krs::analysis::console-cell]"),
            "{name}: {stderr}"
        );
        assert!(errors[0].contains(expected), "{name}: {stderr}");
    }
}
