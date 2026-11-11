//! A pattern's entry that matches every content its cell can hold and binds nothing, on a cell
//! the sentence keeps as it is, has no effect: the sentence means the same without it. It is
//! legal, and almost always a mistake, so the collector, which knows the cell's kind, reports it
//! as a warning (`krs::analysis::no-effect-entry`) at the entry's value, and every command that
//! collects the definition reports it, `krs check` and `krs build` included, which still succeed:
//! in the human format with its location, and in the JSON format as an envelope of severity
//! `warning`. The warning follows its reason: the same entry on a cell the result writes is
//! what the rewrite starts from, and is not reported.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

/// `tick` matches `pc` and `frame` whatever they hold, binds nothing, and keeps both: each entry
/// has no effect. `tock`'s `pc` entry is the same, but its result writes `pc`.
const DEFINITION: &str = r#"use k::KResult;
use k::builtin::{Int, KSequence};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
pub enum Cmd {
    #[k::syntax("tick")] Tick(),
    #[k::syntax("tock")] Tock(),
}

#[k::cell]
pub struct Frame {
    #[k::cell]
    pub ret: Int,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub pc: Int,
    #[k::cell(nested)]
    pub frame: Frame,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self { k: k::k![pgm], pc: 0, frame: Frame { ret: 0 } }
    }
}

#[k::rule(label = "tick")]
pub fn tick(
    k::cells! {
        k: k::configuration::KCell(crate::Cmd::Tick(), tail @ ..),
        pc: k::configuration::Cell(_),
        frame: _,
        state @ ..
    }: crate::Machine,
) -> crate::Machine {
    k::cells! { k: k::configuration::KCell(..tail), ..state }
}

#[k::rule(label = "tock")]
pub fn tock(
    k::cells! {
        k: k::configuration::KCell(crate::Cmd::Tock(), tail @ ..),
        pc: k::configuration::Cell(_),
        state @ ..
    }: crate::Machine,
) -> crate::Machine {
    k::cells! { k: k::configuration::KCell(..tail), pc: k::configuration::Cell(1), ..state }
}
"#;

const CODE: &str = "krs::analysis::no-effect-entry";

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
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-NO-EFFECT\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
            krs_path(),
        ),
    )
    .unwrap();
    directory.join("Cargo.toml")
}

/// Runs `krs <arguments>` on the package's `main` definition: whether it succeeded, its stdout
/// and its stderr.
fn krs(target: &Path, manifest: &Path, arguments: &[&str]) -> (bool, String, String) {
    let mut process = krs_command!();
    fixture_build_env(&mut process, target);
    let output = process
        .args(arguments)
        .arg("--manifest-path")
        .arg(manifest)
        .args(["--package", "no-effect", "--definition", "main"])
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

/// Each `no-effect-entry` warning of a human-format report, with the location line after it,
/// relative to the package's directory `package`.
fn warnings(stderr: &str, package: &Path) -> Vec<String> {
    let package = format!("{}/", package.display());
    let lines = stderr.lines().collect::<Vec<_>>();
    lines
        .iter()
        .enumerate()
        .filter(|(_, line)| line.starts_with(&format!("warning[{CODE}]")))
        .map(|(at, line)| {
            let location = lines[at + 1..]
                .iter()
                .find(|line| line.trim_start().starts_with("-->"))
                .map_or(String::new(), |line| line.trim().replacen(&package, "", 1));
            format!("{line}\n{location}")
        })
        .collect()
}

#[test]
fn an_entry_with_no_effect_is_a_warning_check_and_build_report_and_still_succeed() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "no-effect", DEFINITION);

    let (success, stdout, stderr) = krs(target.path(), &manifest, &["check"]);
    assert!(success, "{stderr}");
    assert!(stdout.starts_with("KRS check passed"), "{stdout}");
    let directory = manifest.parent().unwrap();
    let reported = warnings(&stderr, directory);
    expect_test::expect![[r#"
        [
            "warning[krs::analysis::no-effect-entry]: the entry of the cell `pc` has no effect: it matches every content the cell can hold and binds nothing, and the sentence keeps the cell as it is, so it means the same without the entry; drop the entry, or bind or constrain the content it matches\n--> src/lib.rs:43:13",
            "warning[krs::analysis::no-effect-entry]: the entry of the cell `frame` has no effect: it matches every content the cell can hold and binds nothing, and the sentence keeps the cell as it is, so it means the same without the entry; drop the entry, or bind or constrain the content it matches\n--> src/lib.rs:44:16",
        ]
    "#]]
    .assert_debug_eq(&reported);

    // The JSON format carries each as an envelope of severity `warning`, at the entry's value.
    let (success, _, json) = krs(
        target.path(),
        &manifest,
        &["check", "--message-format=json"],
    );
    assert!(success, "{json}");
    let envelopes = krs_cli::DiagnosticEnvelope::from_json_lines(&json).unwrap();
    let linted = envelopes
        .iter()
        .filter(|envelope| envelope.code == CODE)
        .map(|envelope| {
            assert_eq!(envelope.severity, krs_cli::DiagnosticSeverity::Warning);
            assert_eq!(envelope.stage, krs_cli::DiagnosticStage::Analysis);
            let range = envelope.authored_range.as_ref().unwrap();
            assert_eq!(range.file.package_relative_path(), "src/lib.rs");
            &DEFINITION[range.start_byte as usize..range.end_byte as usize]
        })
        .collect::<Vec<_>>();
    assert_eq!(linted, ["k::configuration::Cell(_)", "_"], "{json}");

    // `krs build` reports them too, and builds the definition.
    let output = temporary.path().join("native");
    let (success, _, stderr) = krs(
        target.path(),
        &manifest,
        &["build", "--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    assert_eq!(warnings(&stderr, directory), reported, "{stderr}");
    assert!(output.exists());
}

/// CELLS4: a subject record without `..` is the whole state and names every cell, so each of
/// its entries is what names its cell: without `frame: _` the record leaves `frame` out and is
/// refused. The entry has that effect, so neither it nor `pc: Cell(_)` owes the lint, in a rule,
/// a claim and a context alike; the same entries in an open record still do.
#[test]
fn an_exact_subject_s_entries_name_their_cells_and_owe_no_lint() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let exact = "k: k::configuration::KCell(crate::Cmd::Tick(), tail @ ..),\n        pc: k::configuration::Cell(_),\n        frame: _,\n        state @ ..";
    let exact_subject = exact.replace(",\n        state @ ..", "");
    let sentences = [
        (
            "rule",
            DEFINITION.replace(exact, &exact_subject).replace(
                "k::cells! { k: k::configuration::KCell(..tail), ..state }",
                "k::cells! { k: k::configuration::KCell(..tail) }",
            ),
        ),
        (
            "claim",
            DEFINITION
                .replace(exact, &exact_subject)
                .replace(
                    "#[k::rule(label = \"tick\")]\npub fn tick(",
                    "#[k::claim(one_path, label = \"tick\")]\npub fn tick(",
                )
                .replace(
                    "k::cells! { k: k::configuration::KCell(..tail), ..state }",
                    "k::cells! { k: k::configuration::KCell(..tail) }",
                ),
        ),
        (
            "context",
            DEFINITION
                .replace(
                    "    #[k::syntax(\"tock\")] Tock(),\n",
                    "    #[k::syntax(\"tock\")] Tock(),\n    #[k::syntax(\"tack({x})\")] Tack { x: Int },\n",
                )
                .replace(
                    &DEFINITION[DEFINITION.find("#[k::rule(label = \"tick\")]").unwrap()
                        ..DEFINITION.find("#[k::rule(label = \"tock\")]").unwrap()],
                    "#[k::context(hole = h)]\nfn tick(\n    h: Int,\n    k::cells! {\n        k: k::configuration::KCell(crate::Cmd::Tack { x: h }, ..),\n        pc: k::configuration::Cell(_),\n        frame: _\n    }: crate::Machine,\n) {}\n\n",
                ),
        ),
    ];
    let mut lines = Vec::new();
    for (form, library) in &sentences {
        let manifest = package(&temporary.path().join(form), "no-effect", library);
        let (success, _, stderr) = krs(target.path(), &manifest, &["check"]);
        assert!(success, "{form}: {stderr}");
        lines.push(format!(
            "{form}: {:?}",
            warnings(&stderr, manifest.parent().unwrap())
        ));
        // Without the entry, the record leaves `frame` out.
        let dropped = library
            .replace(",\n        frame: _\n", "\n")
            .replace("        frame: _\n    }", "    }");
        let manifest = package(
            &temporary.path().join(format!("{form}-dropped")),
            "no-effect",
            &dropped,
        );
        let (success, _, stderr) = krs(target.path(), &manifest, &["check"]);
        assert!(!success, "{form}: {dropped}");
        lines.push(format!(
            "{form} without `frame: _`: {}",
            stderr
                .lines()
                .find(|line| line.starts_with("error"))
                .unwrap()
        ));
    }
    expect_test::expect![[r"
        rule: []
        rule without `frame: _`: error[krs::analysis::record-missing-children]: the `cells!` subject has no `..` and leaves out `frame`: a `cells!` record without `..` is the whole state, so it names every cell of its configuration, as a Rust struct pattern without `..` names every field; name it, or end the record with `..` to leave it unconstrained
        claim: []
        claim without `frame: _`: error[krs::analysis::record-missing-children]: the `cells!` subject has no `..` and leaves out `frame`: a `cells!` record without `..` is the whole state, so it names every cell of its configuration, as a Rust struct pattern without `..` names every field; name it, or end the record with `..` to leave it unconstrained
        context: []
        context without `frame: _`: error[krs::analysis::record-missing-children]: the `cells!` subject has no `..` and leaves out `frame`: a `cells!` record without `..` is the whole state, so it names every cell of its configuration, as a Rust struct pattern without `..` names every field; name it, or end the record with `..` to leave it unconstrained"]].assert_eq(&lines.join("\n"));
}
