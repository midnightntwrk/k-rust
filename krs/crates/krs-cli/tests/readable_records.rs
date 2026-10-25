//! Readable-record notation end to end: the cell shorthand `{ pc, gas }`.
//! Each notation is checked against the long form it stands for, through
//! `krs emit-k` and `krs expand`, which run the macro and the collector's
//! reparse on the same source.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const PREAMBLE: &str = r#"
use k::builtin::{Int, KSequence, List, int, list};
use k::KResult;

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Go, Push, Save, Tag))]
pub enum Cmd {
    #[k::syntax("go")]
    Go(),
    #[k::syntax("push")]
    Push(),
    #[k::syntax("save")]
    Save(),
    #[k::syntax("tag")]
    Tag(),
}

#[k::cell]
pub struct Frame {
    #[k::cell]
    pub depth: Int,
    #[k::cell]
    pub fuel: Int,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub pc: Int,
    #[k::cell]
    pub gas: Int,
    #[k::cell]
    pub stack: List,
    #[k::cell(nested)]
    pub frame: Frame,
    #[k::cell(name = "kind")]
    pub r#type: Int,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self {
            k: k::k![pgm],
            pc: 0,
            gas: 0,
            stack: list::empty(),
            frame: Frame { depth: 0, fuel: 0 },
            r#type: 0,
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

/// Writes a one-package workspace whose library is the preamble and
/// `source`. Every package shares one K namespace, so two spellings of one
/// definition emit the same K.
fn package(root: &Path, name: &str, source: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), format!("{PREAMBLE}{source}")).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-RECORDS\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
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

/// The K source `krs emit-k` writes for the package.
fn emitted_k(target: &Path, manifest: &Path) -> String {
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

/// The reference source `krs expand` writes for the package.
fn expanded(target: &Path, manifest: &Path) -> String {
    let (success, stdout, stderr) = krs(target, manifest, "expand", &[]);
    assert!(success, "{stderr}");
    stdout
}

/// The `error[..]` headlines of `krs check`, without their locations.
fn check_errors(target: &Path, manifest: &Path) -> Vec<String> {
    let (success, _, stderr) = krs(target, manifest, "check", &[]);
    assert!(!success, "krs check unexpectedly passed:\n{stderr}");
    stderr
        .lines()
        .filter(|line| line.starts_with("error"))
        .map(ToOwned::to_owned)
        .collect()
}

const SHORTHAND: &str = r"
k::rules! {
    for Machine;
    use Cmd::*;

    step: { k: [Go(), ..], pc, gas } => { k: [..], pc: int::add(pc, 1), gas };
    save: { k: [Save(), ..], frame, stack } => { k: [..], stack: list::concat(list::item(frame), stack) };
    push: { k: [Push(), ..], gas, stack } => { k: [..], stack: list::concat(list::item(gas), stack) };
    tag: { k: [Tag(), ..], r#type } => { k: [..], r#type: int::add(r#type, 1) };
}
";

const LONG: &str = r"
k::rules! {
    for Machine;
    use Cmd::*;

    step: { k: [Go(), ..], pc: pc, gas: gas } => { k: [..], pc: int::add(pc, 1), gas: gas };
    save: { k: [Save(), ..], frame: frame, stack: stack } => { k: [..], stack: list::concat(list::item(frame), stack) };
    push: { k: [Push(), ..], gas: gas, stack: stack } => { k: [..], stack: list::concat(list::item(gas), stack) };
    tag: { k: [Tag(), ..], r#type: r#type } => { k: [..], r#type: int::add(r#type, 1) };
}
";

/// A lone cell name is the entry `cell: cell` on either side: for a leaf
/// cell, a group cell bound whole, a cell written back unchanged (a read),
/// and a raw identifier. Both spellings emit the same K and expand to the
/// same reference rules.
#[test]
fn a_shorthand_entry_is_the_entry_binding_the_cell_name() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let shorthand = package(temporary.path(), "shorthand", SHORTHAND);
    let long = package(temporary.path(), "long", LONG);
    let shorthand_k = emitted_k(target.path(), &shorthand);
    assert_eq!(shorthand_k, emitted_k(target.path(), &long));
    assert!(
        shorthand_k.contains("<gas> Gas:Int </gas>"),
        "the restated cell is a read:\n{shorthand_k}"
    );
    assert!(
        shorthand_k.contains("<kind> Type:Int => Type:Int +Int 1 </kind>"),
        "{shorthand_k}"
    );
    assert_eq!(
        expanded(target.path(), &shorthand),
        expanded(target.path(), &long)
    );
}

/// A shorthand result entry whose binder the subject does not bind fails
/// as the long entry does.
#[test]
fn an_unbound_shorthand_result_fails_as_the_long_entry() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let rule = |result: &str| {
        format!(
            "k::rules! {{\n    for Machine;\n    use Cmd::*;\n    step: {{ k: [Go(), ..], gas: g }} => {{ k: [..], {result} }};\n}}\n"
        )
    };
    let shorthand = package(temporary.path(), "unbound-shorthand", &rule("gas"));
    let long = package(temporary.path(), "unbound-long", &rule("gas: gas"));
    let errors = check_errors(target.path(), &shorthand);
    assert!(!errors.is_empty());
    assert_eq!(errors, check_errors(target.path(), &long));
}
