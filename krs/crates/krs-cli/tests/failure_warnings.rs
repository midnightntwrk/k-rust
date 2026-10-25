//! A failing command reports the warnings of the stages it completed, before
//! its error: a warning states a fact about the definition, which the later
//! failure does not change, and the warning is often what explains it.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Output;

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

/// A `program` production with a `List` field: K has no LIST-SYNTAX module, so
/// lowering places it outside program syntax and warns.
const PROGRAM_WARNING: &str = r#"
use k::builtin::{Bytes, Int, KSequence, List};

k::sorts! {
    LogEntry;
}

#[k::constructors(sort = LogEntry, result = k::KResult)]
pub enum LogRecord {
    #[k::syntax("logEntry({address}, {topics}, {data})", program)]
    Entry {
        address: Int,
        topics: List,
        data: Bytes,
    },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init() -> Self {
        Self { k: k::k![] }
    }
}
"#;

/// An allowed raw K rule that K cannot parse.
const RAW_PARSE_ERROR: &str = r##"
use k::KResult;
use k::builtin::{Int, KSequence};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
pub enum Doubling {
    #[k::syntax("double({value})")]
    #[k::strict]
    Double { value: Exp },
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

k::raw_k!(r#"rule <k> double(I:Int) => I +Int ... </k>"#);
"##;

const NOT_PROGRAM_SYNTAX: &str = "warning[krs::partition::not-program-syntax]: ";

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// Writes a one-package workspace whose library is `library`.
fn package(root: &Path, name: &str, library: &str, metadata: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), library).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-FAILURE-WARNINGS\"\n{metadata}\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
            krs_path(),
        ),
    )
    .unwrap();
    directory.join("Cargo.toml")
}

fn krs(target: &Path, manifest: &Path, arguments: &[&str]) -> Output {
    let name = manifest
        .parent()
        .and_then(Path::file_name)
        .and_then(|name| name.to_str())
        .unwrap();
    let (verb, rest) = arguments.split_first().unwrap();
    let mut process = krs_command!();
    fixture_build_env(&mut process, target);
    process
        .arg(verb)
        .arg("--manifest-path")
        .arg(manifest)
        .args(["--package", name, "--definition", "main"])
        .args(rest)
        .env("NO_COLOR", "1")
        .output()
        .unwrap()
}

/// The `error[..]`/`warning[..]` headlines of a human report, in order.
fn headlines(output: &Output) -> Vec<String> {
    String::from_utf8(output.stderr.clone())
        .unwrap()
        .lines()
        .filter(|line| line.starts_with("error") || line.starts_with("warning"))
        .map(str::to_owned)
        .collect()
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

#[test]
fn a_failed_parse_or_run_reports_the_definition_s_warnings_before_its_error() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "program-warning", PROGRAM_WARNING, "");
    let program = temporary.path().join("log.txt");
    fs::write(&program, "logEntry(1, .List, .Bytes)\n").unwrap();
    let program = program.to_str().unwrap();

    let checked = krs(target.path(), &manifest, &["check"]);
    assert!(checked.status.success(), "{}", stderr(&checked));
    let warnings = headlines(&checked);
    assert_eq!(warnings.len(), 1, "{}", stderr(&checked));
    assert!(warnings[0].starts_with(NOT_PROGRAM_SYNTAX), "{warnings:?}");

    // The parse fails because the production is not program syntax; the
    // warning that says so comes first, the error last.
    let parsed = krs(
        target.path(),
        &manifest,
        &["parse", "--sort", "LogEntry", program],
    );
    assert_eq!(parsed.status.code(), Some(1), "{}", stderr(&parsed));
    let lines = headlines(&parsed);
    assert_eq!(lines.len(), 2, "{}", stderr(&parsed));
    assert_eq!(lines[0], warnings[0]);
    assert!(
        lines[1].starts_with("error[krs::exec::parse]: "),
        "{}",
        stderr(&parsed)
    );

    let json = krs(
        target.path(),
        &manifest,
        &[
            "parse",
            "--message-format",
            "json",
            "--sort",
            "LogEntry",
            program,
        ],
    );
    assert_eq!(json.status.code(), Some(1), "{}", stderr(&json));
    let text = stderr(&json);
    let lines = text.lines().collect::<Vec<_>>();
    assert_eq!(lines.len(), 2, "{text}");
    let warning: serde_json::Value = serde_json::from_str(lines[0]).unwrap();
    assert_eq!(warning["severity"], "warning", "{text}");
    assert_eq!(
        warning["code"], "krs::partition::not-program-syntax",
        "{text}"
    );
    // The failure is an envelope too, though it has no authored range.
    let error: serde_json::Value = serde_json::from_str(lines[1]).unwrap();
    assert_eq!(error["code"], "krs::exec::parse", "{text}");
    assert_eq!(error["authored_range"], serde_json::Value::Null, "{text}");

    // A usage error (exit 2) reports them too: the warnings do not depend on
    // the outcome.
    let ran = krs(target.path(), &manifest, &["run", program]);
    assert_eq!(ran.status.code(), Some(2), "{}", stderr(&ran));
    let lines = headlines(&ran);
    assert_eq!(lines.len(), 2, "{}", stderr(&ran));
    assert_eq!(lines[0], warnings[0]);
    assert!(
        lines[1].starts_with("error[krs::exec::program]: "),
        "{}",
        stderr(&ran)
    );
}

#[test]
fn a_failed_native_build_reports_the_raw_k_warning_before_its_parse_error() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(
        temporary.path(),
        "raw-parse-error",
        RAW_PARSE_ERROR,
        "allow-raw-k = true\n",
    );
    let output = temporary.path().join("native");
    let built = krs(
        target.path(),
        &manifest,
        &["build", "--output", output.to_str().unwrap()],
    );
    assert_eq!(built.status.code(), Some(1), "{}", stderr(&built));
    let lines = headlines(&built);
    assert_eq!(lines.len(), 2, "{}", stderr(&built));
    assert!(
        lines[0].starts_with("warning[krs::semantic::raw-k]: "),
        "{}",
        stderr(&built)
    );
    assert!(
        lines[1].starts_with("error[krs::native::raw-k-parse]: "),
        "{}",
        stderr(&built)
    );
    assert!(!output.exists());
}

#[test]
fn a_failure_before_the_definition_is_collected_reports_no_krs_warning() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let library = format!("{PROGRAM_WARNING}\npub fn broken() -> u8 {{ \"text\" }}\n");
    let manifest = package(temporary.path(), "rustc-error", &library, "");
    let checked = krs(target.path(), &manifest, &["check"]);
    assert!(!checked.status.success(), "{}", stderr(&checked));
    let lines = headlines(&checked);
    assert!(
        lines.iter().any(|line| line.starts_with("error[E0308]")),
        "{}",
        stderr(&checked)
    );
    assert!(
        !lines.iter().any(|line| line.starts_with("warning")),
        "{}",
        stderr(&checked)
    );
}
