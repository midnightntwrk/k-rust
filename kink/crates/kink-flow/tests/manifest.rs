//! FLOW.toml decoding (flow F-02 deliverable 2): defaults, values, and every error names
//! the offending key or program id.

use kink_corpus::ProgramSource;
use kink_flow::manifest::{
    Budget, DEFAULT_MAX_DEPTH, DEFAULT_TIME_MS, FlowManifest, KrsSpec, ManifestError, ManifestFile,
    Program, SpecDecl, SpecSection,
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
            max_depth: 100_000,
            work_factor: None,
            baseline_max_work: None,
            smt_resource_limit: kink_native::SMT_RESOURCE_LIMIT,
        }
    );
    assert_eq!(
        manifest.budget.backend_options(),
        kink_native::BACKEND_OPTIONS
    );
    assert_eq!((DEFAULT_TIME_MS, DEFAULT_MAX_DEPTH), (10_000, 100_000));
    assert_eq!(
        manifest.programs,
        [Program {
            id: "one".into(),
            source: Some(ProgramSource::Text("1".into())),
            start_sort: None,
            variables: vec![],
            inputs: toml::Table::new(),
            case: None,
            case_file: None,
            expect: None,
            stop_count: None,
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
work_factor = 3
baseline_max_work = 20000
smt_resource_limit = 50000

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
            max_depth: 7,
            work_factor: Some(3),
            baseline_max_work: Some(20_000),
            smt_resource_limit: std::num::NonZeroU32::new(50_000).unwrap(),
        }
    );
    // `smt_resource_limit` bounds the first attempt of every solver query of a run in Z3
    // resource units; the retries and the clock-free mode are kink's.
    assert_eq!(
        manifest.budget.backend_options(),
        kink_native::backend_options(std::num::NonZeroU32::new(50_000).unwrap())
    );
    assert_eq!(
        manifest.budget.backend_options().smt_retry_limit,
        kink_native::BACKEND_OPTIONS.smt_retry_limit
    );
    // Re-pin L1-1: `work_factor` calibrates the mutants' work budget from each program's
    // baseline work; absent, there is none.
    assert_eq!(
        manifest.budget.work(),
        kink_campaign::WorkBudget::Calibrated {
            factor: 3,
            floor: kink_flow::manifest::WORK_FLOOR
        }
    );
    assert_eq!(
        Budget::default().work(),
        kink_campaign::WorkBudget::Unbounded
    );
    assert_eq!(
        manifest.programs,
        [
            Program {
                id: "from-file".into(),
                source: Some(ProgramSource::File("programs/a.lang".into())),
                start_sort: Some("Stmt".into()),
                variables: vec![("A".into(), "true".into()), ("Z".into(), "3".into())],
                inputs: toml::Table::new(),
                case: None,
                case_file: None,
                expect: None,
                stop_count: None,
            },
            Program {
                id: "inline".into(),
                source: Some(ProgramSource::Text("1 + 2".into())),
                start_sort: None,
                variables: vec![],
                inputs: toml::Table::new(),
                case: None,
                case_file: None,
                expect: None,
                stop_count: None,
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
fn a_program_has_at_most_one_of_file_and_text() {
    assert_error(
        &format!("{SPEC}[[program]]\nid = \"both\"\nfile = \"a\"\ntext = \"1\"\n"),
        "program \"both\"",
        "has both file and text",
    );
    assert_error(
        &format!("{SPEC}[[program]]\nid = \"num\"\ntext = 1\n"),
        "program \"num\".text",
        "expected a string",
    );
}

/// A case of a definition without `$PGM` has no program text: it binds every configuration
/// variable by name. A start sort applies to a program text only, so it is refused without one.
#[test]
fn a_program_without_file_or_text_is_a_program_less_case() {
    let manifest = decode(&format!(
        "{SPEC}[[program]]\nid = \"bare\"\nvariables = {{ ENTRY = \"run\" }}\n"
    ))
    .unwrap();
    assert_eq!(
        manifest.programs,
        [Program {
            id: "bare".into(),
            source: None,
            start_sort: None,
            variables: vec![("ENTRY".into(), "run".into())],
            inputs: toml::Table::new(),
            case: None,
            case_file: None,
            expect: None,
            stop_count: None,
        }]
    );
    assert_error(
        &format!("{SPEC}[[program]]\nid = \"sorted\"\nstart_sort = \"Exp\"\n"),
        "program \"sorted\".start_sort",
        "start_sort applies to a program text; this program has none",
    );
}

/// `inputs` is kept as written, documents by input name, for a front end's decoder; kink-flow
/// does not read it. A value that is not a table is refused naming the key.
#[test]
fn typed_inputs_are_kept_as_written() {
    let manifest = decode(&format!(
        "{SPEC}[[program]]\nid = \"typed\"\n[program.inputs]\nrom = {{ \"$file\" = \"rom.bin\" }}\n\
         memory = {{ \"0x0100\" = 0, \"0x0101\" = 195 }}\n"
    ))
    .unwrap();
    let program = &manifest.programs[0];
    assert_eq!(program.source, None);
    assert_eq!(
        program.inputs.keys().collect::<Vec<_>>(),
        ["memory", "rom"],
        "{program:?}"
    );
    assert_eq!(
        program.inputs["rom"]["$file"].as_str(),
        Some("rom.bin"),
        "{program:?}"
    );
    assert_eq!(
        program.inputs["memory"]["0x0101"].as_integer(),
        Some(195),
        "{program:?}"
    );
    assert_error(
        &format!("{SPEC}[[program]]\nid = \"v\"\ninputs = [\"rom\"]\n"),
        "program \"v\".inputs",
        "expected a table of typed inputs by name",
    );
    // A decoded manifest has no decoder: kink reads K text only.
    assert!(manifest.input_decoder.get().is_none());
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
        &format!("{SPEC}[budget]\nwork_factor = 0\n"),
        "budget.work_factor",
        "must be positive",
    );
    assert_error(
        &format!("{SPEC}[budget]\nwork_factor = 1.5\n"),
        "budget.work_factor",
        "expected an integer",
    );
    assert_error(
        &format!("{SPEC}[budget]\nbaseline_max_work = 0\n"),
        "budget.baseline_max_work",
        "must be positive",
    );
    assert_error(
        &format!("{SPEC}[budget]\nsmt_resource_limit = 0\n"),
        "budget.smt_resource_limit",
        "must be positive",
    );
    for units in ["536870912", "4294967296"] {
        assert_error(
            &format!("{SPEC}[budget]\nsmt_resource_limit = {units}\n"),
            "budget.smt_resource_limit",
            "must be at most 536870911, so that each of the 3 retries doubles it within 4294967295",
        );
    }
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

#[test]
fn result_cells_decode_as_written_and_default_to_none() {
    assert_eq!(decode(SPEC).unwrap().result, None);
    let manifest = decode(&format!("{SPEC}[result]\ncells = [\"regs\", \"k\"]\n")).unwrap();
    assert_eq!(
        manifest.result,
        Some(kink_flow::ResultSection {
            cells: vec!["regs".into(), "k".into()],
        })
    );
}

#[test]
fn result_cells_errors_name_the_key() {
    for (text, message) in [
        ("[result]\n", "missing required key"),
        ("[result]\ncells = []\n", "at least one cell"),
        ("[result]\ncells = \"k\"\n", "expected an array"),
        ("[result]\ncells = [\"k\", \"k\"]\n", "names `k` twice"),
        ("[result]\ncells = [\"\"]\n", "entry 0 is empty"),
        ("[result]\ncells = [\"k\", 3]\n", "entry 1 is not a string"),
    ] {
        assert_error(&format!("{SPEC}{text}"), "result.cells", message);
    }
    assert_error(
        &format!("{SPEC}[result]\ncells = [\"k\"]\nslots = 2\n"),
        "result.slots",
        "unknown key",
    );
    assert_error(&format!("result = 1\n{SPEC}"), "result", "expected a table");
}

// ---------------------------------------------------------------------------------------
// CF-40: one schema, two specification declarations.

const KRS_SPEC: &str =
    "[spec]\nkrs = { definition = \"main\" }\nassume_joined = [\"b\", \"a\", \"b\"]\n";

fn decode_file(text: &str) -> Result<ManifestFile, ManifestError> {
    ManifestFile::decode(text, Path::new("corpus"))
}

#[track_caller]
fn assert_file_error(text: &str, key: &str, message: &str) {
    let error = decode_file(text).expect_err("the manifest must be refused");
    assert_eq!(error.key, key, "{error}");
    assert!(error.message.contains(message), "{error}");
}

/// The specification a front end binds: the K a package emits (CF-14a's shape).
fn emitted() -> SpecSection {
    SpecSection {
        entry: "definition.k".into(),
        main_module: "PLUS".into(),
        syntax_module: None,
        include_dirs: vec![".".into()],
        md_selector: "k".into(),
        assume_joined: Vec::new(),
    }
}

#[test]
fn a_krs_spec_decodes_to_its_declaration() {
    let text = format!("{KRS_SPEC}[budget]\ntime_ms = 7\n[[program]]\nid = \"t1\"\ntext = \"1\"\n");
    let file = decode_file(&text).unwrap();
    assert_eq!(
        file.spec,
        SpecDecl::Krs(KrsSpec {
            definition: "main".into(),
            assume_joined: vec!["a".into(), "b".into()],
        })
    );
    assert_eq!(file.directory, PathBuf::from("corpus"));
    assert_eq!(file.budget.time_ms, 7);
    assert_eq!(file.programs.len(), 1);
    // A K declaration decodes as before.
    assert!(matches!(decode_file(SPEC).unwrap().spec, SpecDecl::K(_)));
}

#[test]
fn a_krs_spec_refuses_every_key_its_front_end_supplies() {
    for key in [
        "entry",
        "main_module",
        "syntax_module",
        "include_dirs",
        "md_selector",
    ] {
        let value = if key == "include_dirs" {
            "[\".\"]"
        } else {
            "\"x\""
        };
        assert_file_error(
            &format!("{KRS_SPEC}{key} = {value}\n"),
            &format!("spec.{key}"),
            "not allowed with spec.krs: the krs front end supplies it",
        );
    }
    assert_file_error(
        "[spec]\nkrs = { definition = \"main\", package = \"p\" }\n",
        "spec.krs.package",
        "unknown key",
    );
    assert_file_error("[spec]\nkrs = {}\n", "spec.krs.definition", "missing");
    assert_file_error(
        "[spec]\nkrs = { definition = \"\" }\n",
        "spec.krs.definition",
        "must not be empty",
    );
    assert_file_error("[spec]\nkrs = \"main\"\n", "spec.krs", "expected a table");
}

#[test]
fn each_front_end_refuses_the_other_declaration() {
    // kink-flow's reading of a KRS corpus names the command to use.
    let error = error(KRS_SPEC);
    assert_eq!(error.key, "spec.krs", "{error}");
    assert!(error.message.contains("krs kink"), "{error}");
    // A K corpus is the specification it declares: no front end binds another.
    let error = decode_file(SPEC)
        .unwrap()
        .bind(Some(emitted()))
        .unwrap_err();
    assert_eq!(error.key, "spec.entry", "{error}");
    assert!(error.message.contains("kink-flow"), "{error}");
}

#[test]
fn binding_a_krs_spec_is_decoding_the_spec_written_out() {
    let programs = "[budget]\ntime_ms = 7\nwork_factor = 2\n\n[result]\ncells = [\"k\"]\n\n\
                    [[program]]\nid = \"t1\"\nfile = \"cases/t1.nat\"\n";
    let bound = decode_file(&format!("{KRS_SPEC}{programs}"))
        .unwrap()
        .bind(Some(emitted()))
        .unwrap();
    let written = decode(&format!(
        "[spec]\nentry = \"definition.k\"\nmain_module = \"PLUS\"\ninclude_dirs = [\".\"]\n\
         md_selector = \"k\"\nassume_joined = [\"a\", \"b\"]\n{programs}"
    ))
    .unwrap();
    assert_eq!(bound, written);
    // The declaration's premises are the corpus's, whatever the front end passes.
    let mut other = emitted();
    other.assume_joined = vec!["z".into()];
    let bound = decode_file(KRS_SPEC).unwrap().bind(Some(other)).unwrap();
    assert_eq!(bound.spec.assume_joined, ["a", "b"]);
}

#[test]
fn a_bound_spec_stays_inside_the_manifest_directory() {
    let mut outside = emitted();
    outside.entry = "../definition.k".into();
    let error = decode_file(KRS_SPEC)
        .unwrap()
        .bind(Some(outside))
        .unwrap_err();
    assert_eq!(error.key, "spec.entry", "{error}");
    let mut include = emitted();
    include.include_dirs = vec!["/abs".into()];
    let error = decode_file(KRS_SPEC)
        .unwrap()
        .bind(Some(include))
        .unwrap_err();
    assert_eq!(error.key, "spec.include_dirs[0]", "{error}");
    let mut module = emitted();
    module.main_module = String::new();
    let error = decode_file(KRS_SPEC)
        .unwrap()
        .bind(Some(module))
        .unwrap_err();
    assert_eq!(error.key, "spec.main_module", "{error}");
}

#[test]
fn a_manifest_error_names_its_key() {
    // `ManifestError::new` is public, so a front end reports its own errors by key.
    let error = ManifestError::new("spec.krs.definition", "differs from --definition");
    assert_eq!(
        error.to_string(),
        "spec.krs.definition: differs from --definition"
    );
}
