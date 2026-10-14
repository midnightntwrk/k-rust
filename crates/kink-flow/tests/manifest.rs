//! FLOW.toml decoding (flow F-02 deliverable 2): defaults, values, and every error names
//! the offending key or program id.

use kink_corpus::ProgramSource;
use kink_flow::manifest::{
    Budget, DEFAULT_MAX_DEPTH, DEFAULT_TIME_MS, FlowManifest, ManifestError, Program,
};
use std::path::{Path, PathBuf};

fn decode(text: &str) -> Result<FlowManifest, ManifestError> {
    FlowManifest::decode(text, Path::new("corpus"))
}

fn error(text: &str) -> ManifestError {
    decode(text).expect_err("the manifest must be refused")
}

#[track_caller]
fn assert_error(text: &str, key: &str, message: &str) {
    let error = error(text);
    assert_eq!(error.key, key, "{error}");
    assert!(error.message.contains(message), "{error}");
    assert!(error.to_string().starts_with(key), "{error}");
}

const SPEC: &str = "[spec]\nentry = \"calc.k\"\nmain_module = \"CALC\"\n";

#[test]
fn a_minimal_manifest_takes_every_default() {
    let manifest = decode(&format!("{SPEC}[[program]]\nid = \"one\"\ntext = \"1\"\n")).unwrap();
    assert_eq!(manifest.directory, PathBuf::from("corpus"));
    assert_eq!(manifest.spec.entry, "calc.k");
    assert_eq!(manifest.spec.main_module, "CALC");
    assert_eq!(manifest.spec.syntax_module, None);
    assert_eq!(manifest.spec.include_dirs, ["."]);
    assert_eq!(manifest.spec.md_selector, "k");
    assert_eq!(
        manifest.budget,
        Budget {
            time_ms: 10_000,
            max_depth: 100_000
        }
    );
    assert_eq!((DEFAULT_TIME_MS, DEFAULT_MAX_DEPTH), (10_000, 100_000));
    assert_eq!(
        manifest.programs,
        [Program {
            id: "one".into(),
            source: ProgramSource::Text("1".into()),
            start_sort: None,
            variables: vec![],
        }]
    );
    let empty = decode(SPEC).unwrap();
    assert!(empty.programs.is_empty());
    assert_eq!(
        decode(&format!("{SPEC}[budget]\n")).unwrap().budget,
        Budget::default()
    );
}

#[test]
fn every_key_decodes_to_its_value() {
    let manifest = decode(
        r#"
[spec]
entry = "src/../lang.md"
main_module = "LANG"
syntax_module = "LANG-SYNTAX"
include_dirs = ["include", "./lib"]
md_selector = "k | concrete"

[budget]
time_ms = 250
max_depth = 7

[[program]]
id = "from-file"
file = "programs/a.lang"
start_sort = "Stmt"
variables = { Z = "3", A = "true" }

[[program]]
id = "inline"
text = "1 + 2"
"#,
    )
    .unwrap();
    assert_eq!(manifest.spec.entry, "src/../lang.md");
    assert_eq!(manifest.spec.syntax_module.as_deref(), Some("LANG-SYNTAX"));
    assert_eq!(manifest.spec.include_dirs, ["include", "./lib"]);
    assert_eq!(manifest.spec.md_selector, "k | concrete");
    assert_eq!(
        manifest.budget,
        Budget {
            time_ms: 250,
            max_depth: 7
        }
    );
    assert_eq!(
        manifest.programs,
        [
            Program {
                id: "from-file".into(),
                source: ProgramSource::File("programs/a.lang".into()),
                start_sort: Some("Stmt".into()),
                variables: vec![("A".into(), "true".into()), ("Z".into(), "3".into())],
            },
            Program {
                id: "inline".into(),
                source: ProgramSource::Text("1 + 2".into()),
                start_sort: None,
                variables: vec![],
            },
        ]
    );
}

#[test]
fn read_resolves_paths_against_the_manifests_directory() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../testdata/flow/calc");
    let manifest = FlowManifest::read(&root.join("FLOW.toml")).unwrap();
    assert_eq!(manifest.directory, root);
    assert_eq!(
        manifest
            .programs
            .iter()
            .map(|p| p.id.as_str())
            .collect::<Vec<_>>(),
        ["add", "nested", "sub", "inline"]
    );
    let missing = FlowManifest::read(&root.join("MISSING.toml")).unwrap_err();
    assert!(
        missing.message.contains("cannot read the manifest"),
        "{missing}"
    );
}

#[test]
fn unknown_keys_are_errors_naming_the_key() {
    assert_error(&format!("{SPEC}extra = 1\n"), "spec.extra", "unknown key");
    assert_error(&format!("bogus = 1\n{SPEC}"), "bogus", "unknown key");
    assert_error(
        "[spec]\nentyr = \"calc.k\"\nmain_module = \"CALC\"\n",
        "spec.entyr",
        "unknown key",
    );
    assert_error(
        &format!("{SPEC}[budget]\ntime = 5\n"),
        "budget.time",
        "unknown key",
    );
    assert_error(
        &format!("{SPEC}[[program]]\nid = \"p\"\ntext = \"1\"\nstart = \"Exp\"\n"),
        "program \"p\".start",
        "unknown key",
    );
}

#[test]
fn program_ids_must_be_present_nonempty_and_unique() {
    assert_error(
        &format!(
            "{SPEC}[[program]]\nid = \"p\"\ntext = \"1\"\n[[program]]\nid = \"p\"\ntext = \"2\"\n"
        ),
        "program \"p\"",
        "duplicate program id",
    );
    assert_error(
        &format!("{SPEC}[[program]]\nid = \"a\"\ntext = \"1\"\n[[program]]\ntext = \"2\"\n"),
        "program[1].id",
        "missing required key",
    );
    assert_error(
        &format!("{SPEC}[[program]]\nid = \"\"\ntext = \"1\"\n"),
        "program[0].id",
        "must not be empty",
    );
    assert_error(
        &format!("program = 3\n{SPEC}"),
        "program",
        "expected [[program]] tables",
    );
}

#[test]
fn a_program_has_exactly_one_of_file_and_text() {
    assert_error(
        &format!("{SPEC}[[program]]\nid = \"both\"\nfile = \"a\"\ntext = \"1\"\n"),
        "program \"both\"",
        "has both file and text",
    );
    assert_error(
        &format!("{SPEC}[[program]]\nid = \"neither\"\n"),
        "program \"neither\"",
        "has neither file nor text",
    );
    assert_error(
        &format!("{SPEC}[[program]]\nid = \"num\"\ntext = 1\n"),
        "program \"num\".text",
        "expected a string",
    );
}

#[test]
fn paths_that_leave_the_manifests_directory_are_errors() {
    for entry in ["../calc.k", "a/../../calc.k", "/abs/calc.k"] {
        assert_error(
            &format!("[spec]\nentry = {entry:?}\nmain_module = \"CALC\"\n"),
            "spec.entry",
            "leaves the manifest's directory",
        );
    }
    assert_error(
        "[spec]\nentry = \"calc.k\"\nmain_module = \"CALC\"\ninclude_dirs = [\".\", \"..\"]\n",
        "spec.include_dirs[1]",
        "leaves the manifest's directory",
    );
    assert_error(
        &format!("{SPEC}[[program]]\nid = \"up\"\nfile = \"programs/../../x\"\n"),
        "program \"up\".file",
        "leaves the manifest's directory",
    );
    // Inside after normalisation: accepted.
    assert!(decode("[spec]\nentry = \"a/../calc.k\"\nmain_module = \"CALC\"\n").is_ok());
}

#[test]
fn required_keys_types_and_bounds_are_checked() {
    assert_error("", "spec", "missing required key");
    assert_error(
        "[spec]\nmain_module = \"CALC\"\n",
        "spec.entry",
        "missing required key",
    );
    assert_error(
        "[spec]\nentry = \"calc.k\"\n",
        "spec.main_module",
        "missing required key",
    );
    assert_error("spec = 1\n", "spec", "expected a table");
    assert_error(
        "[spec]\nentry = 1\nmain_module = \"CALC\"\n",
        "spec.entry",
        "expected a string",
    );
    assert_error(
        &format!("{SPEC}include_dirs = \"src\"\n"),
        "spec.include_dirs",
        "expected an array of strings",
    );
    assert_error(
        &format!("{SPEC}syntax_module = \"\"\n"),
        "spec.syntax_module",
        "must not be empty",
    );
    assert_error(
        &format!("{SPEC}[budget]\nmax_depth = 0\n"),
        "budget.max_depth",
        "must be positive",
    );
    assert_error(
        &format!("{SPEC}[budget]\ntime_ms = -5\n"),
        "budget.time_ms",
        "must be positive",
    );
    assert_error(
        &format!("{SPEC}[budget]\ntime_ms = \"10\"\n"),
        "budget.time_ms",
        "expected an integer",
    );
    assert_error(
        &format!("{SPEC}[[program]]\nid = \"v\"\ntext = \"1\"\nvariables = {{ N = 42 }}\n"),
        "program \"v\".variables.N",
        "expected a string",
    );
    assert_error(
        &format!("{SPEC}[[program]]\nid = \"v\"\ntext = \"1\"\nvariables = [\"N\"]\n"),
        "program \"v\".variables",
        "expected a table of strings",
    );
    let syntax = error("[spec\nentry = \"calc.k\"\n");
    assert_eq!(syntax.key, "");
    assert!(syntax.message.starts_with("invalid TOML"), "{syntax}");
}
