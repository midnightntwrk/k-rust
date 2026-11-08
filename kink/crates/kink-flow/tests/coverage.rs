//! Digests, the result cache and `kink-flow coverage` (flow F-03 deliverables 1-6; the coverage
//! families, their targets and renderings).

use kink_campaign::{
    Campaign, CampaignOptions, CampaignReport, ScheduleMode, TestCase, run_campaign_multi,
};
use kink_corpus::ProgramSource;
use kink_corpus::{load_source, runner::all_normal};
use kink_flow::{
    CaseInputs, FlowManifest, Program, SpecSection, admit,
    admit::{admit_spec, corpus_source},
    cli::{EXIT_NO, EXIT_UNANSWERED, EXIT_UNASKED, EXIT_YES, coverage},
    coverage::{CoverageOptions, Tier},
    digest::{
        ExecutionDigest, definition_value, execution_digest, execution_payload, program_digest,
        spec_digest, spec_payload,
    },
    results::{
        BaselineRunner, CACHE_DIRECTORY, RESULT_SCHEMA_VERSION, ResultClass, TIMEOUT_BOUND_BY_WORK,
        TIMEOUT_NOT_CACHED, execution_budget, fixed_oracles, record_final_configuration,
        run_digest,
    },
};
use kink_native::{K_RUST_REVISION, execution::SolverProfile};
use kink_patch::{Discovery, Patch, SelectionPolicy, select, sha256};
use serde_json::{Value, json};
use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
};

fn flow(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../testdata/flow")
        .join(name)
}

/// A fresh directory for one test, under the target's temporary directory.
fn scratch(name: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-coverage-{}", std::process::id()))
        .join(name);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
}

fn copy_dir(from: &Path, to: &Path) {
    fs::create_dir_all(to).unwrap();
    for entry in fs::read_dir(from).unwrap() {
        let entry = entry.unwrap();
        let name = entry.file_name();
        if name == CACHE_DIRECTORY {
            continue;
        }
        if entry.file_type().unwrap().is_dir() {
            copy_dir(&entry.path(), &to.join(&name));
        } else {
            fs::copy(entry.path(), to.join(&name)).unwrap();
        }
    }
}

/// A private copy of a testdata/flow fixture.
fn fixture(name: &str, test: &str) -> PathBuf {
    let dir = scratch(test).join(name);
    copy_dir(&flow(name), &dir);
    dir
}

fn write(path: &Path, text: &str) {
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, text).unwrap();
}

fn append(path: &Path, text: &str) {
    let mut contents = fs::read_to_string(path).unwrap();
    contents.push_str(text);
    fs::write(path, contents).unwrap();
}

#[track_caller]
fn run(manifest: &Path, verify: bool) -> (Value, u8) {
    coverage(
        manifest,
        &CoverageOptions {
            verify,
            ..CoverageOptions::default()
        },
    )
}

/// The rules family's items of a coverage document.
fn rules(document: &Value) -> &Vec<Value> {
    document["families"]["rules"]["items"]
        .as_array()
        .unwrap_or_else(|| panic!("no rules: {document:#}"))
}

/// `(id, class, cached)` of every program row.
fn rows(document: &Value) -> Vec<(String, String, bool)> {
    document["programs"]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| {
            (
                p["id"].as_str().unwrap().to_owned(),
                p["class"].as_str().unwrap().to_owned(),
                p["cached"].as_bool().unwrap(),
            )
        })
        .collect()
}

fn expect(rows: &[(&str, &str, bool)]) -> Vec<(String, String, bool)> {
    rows.iter()
        .map(|(id, class, cached)| ((*id).to_owned(), (*class).to_owned(), *cached))
        .collect()
}

fn program_digests(document: &Value) -> Vec<(String, String)> {
    document["programs"]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| {
            (
                p["id"].as_str().unwrap().to_owned(),
                p["digest"].as_str().unwrap().to_owned(),
            )
        })
        .collect()
}

fn spec_hex(document: &Value) -> String {
    document["spec"]["digest"].as_str().unwrap().to_owned()
}

/// The execution digest a document names, which names the result cache's directory.
fn execution_hex(document: &Value) -> String {
    document["spec"]["execution_digest"]["digest"]
        .as_str()
        .unwrap()
        .to_owned()
}

/// The record of program `id` in the document's cache.
fn record_path(manifest: &Path, document: &Value, id: &str) -> PathBuf {
    let digest = program_digests(document)
        .into_iter()
        .find(|(program, _)| program == id)
        .unwrap()
        .1;
    manifest
        .parent()
        .unwrap()
        .join(CACHE_DIRECTORY)
        .join("results")
        .join(execution_hex(document))
        .join(format!("{digest}.json"))
}

fn read_json(path: &Path) -> Value {
    serde_json::from_str(&fs::read_to_string(path).unwrap()).unwrap()
}

/// The stored record of program `id`, which the result cache wrote in both profiles.
fn stored_record(manifest: &Path, document: &Value, id: &str) -> Value {
    read_json(&record_path(manifest, document, id))
}

fn manifest_spec_digest(manifest: &FlowManifest) -> String {
    let loaded = load_source(&corpus_source(manifest)).unwrap();
    spec_digest(manifest, &loaded.files).to_string()
}

const CALC_FLOW: &str = include_str!("../../../testdata/flow/calc/FLOW.toml");

/// The calc manifest with every value unchanged: other key order, comments, inline tables,
/// and the defaults written out.
const CALC_FLOW_REFORMATTED: &str = r#"
# the same corpus, written differently
[[program]]
file = "programs/add.calc"
id = "add"

[[program]]
id   =   "nested"
file =   "programs/nested.calc"
variables = {}

[spec]
syntax_module = "CALC-SYNTAX"
main_module = "CALC"
md_selector = "k"
include_dirs = [ "." ]
entry = "calc.k"

[budget]
max_depth = 100000
time_ms = 10000

[[program]]
id = "sub"
file = "programs/sub.calc"

[[program]]
text = "2 * 3 + 1"
id = "inline"
"#;

#[test]
fn digests_ignore_formatting_and_program_ids() {
    let dir = fixture("calc", "digests-format");
    let original = FlowManifest::decode(CALC_FLOW, &dir).unwrap();
    let reformatted = FlowManifest::decode(CALC_FLOW_REFORMATTED, &dir).unwrap();
    assert_eq!(
        manifest_spec_digest(&original),
        manifest_spec_digest(&reformatted)
    );
    let digest = |manifest: &FlowManifest, id: &str| {
        let program = manifest.programs.iter().find(|p| p.id == id).unwrap();
        let text = match program.source.as_ref().unwrap() {
            ProgramSource::Text(text) => text.clone(),
            ProgramSource::File(name) => fs::read_to_string(dir.join(name)).unwrap(),
        };
        program_digest(program, &CaseInputs::text(text))
    };
    for id in ["add", "nested", "sub", "inline"] {
        assert_eq!(digest(&original, id), digest(&reformatted, id), "{id}");
    }
    // Renaming a program changes no digest.
    let renamed = FlowManifest::decode(&CALC_FLOW.replace("\"add\"", "\"plus\""), &dir).unwrap();
    assert_eq!(digest(&original, "add"), digest(&renamed, "plus"));
    assert_eq!(
        manifest_spec_digest(&original),
        manifest_spec_digest(&renamed)
    );
}

#[test]
fn the_spec_digest_covers_every_required_file_and_nothing_else() {
    let dir = scratch("digests-spec");
    write(
        &dir.join("main.k"),
        "requires \"lib.k\"\nmodule MAIN\n  imports LIB\n  configuration <k> $PGM:Exp </k>\nendmodule\n",
    );
    write(
        &dir.join("include/lib.k"),
        "module LIB\n  imports INT\n  syntax Exp ::= Int\nendmodule\n",
    );
    write(&dir.join("unrelated.k"), "// not required\n");
    let manifest = FlowManifest::decode(
        "[spec]\nentry = \"main.k\"\nmain_module = \"MAIN\"\ninclude_dirs = [\"include\"]\n\n[[program]]\nid = \"one\"\ntext = \"1\"\n",
        &dir,
    )
    .unwrap();
    // The load reports the required file of the include directory (stop rule of F-03).
    let loaded = load_source(&corpus_source(&manifest)).unwrap();
    assert_eq!(
        loaded
            .files
            .iter()
            .map(|f| f.name.as_str())
            .collect::<Vec<_>>(),
        ["include/lib.k", "main.k"]
    );
    let base = manifest_spec_digest(&manifest);
    write(&dir.join("unrelated.k"), "// still not required\n");
    assert_eq!(manifest_spec_digest(&manifest), base);
    append(&dir.join("include/lib.k"), "// edited\n");
    let after_lib = manifest_spec_digest(&manifest);
    assert_ne!(after_lib, base);
    append(&dir.join("main.k"), "// edited\n");
    let after_main = manifest_spec_digest(&manifest);
    assert_ne!(after_main, after_lib);
    assert_ne!(after_main, base);
    // How the spec is loaded is part of the digest too.
    let mut other_selector = manifest.clone();
    other_selector.spec.md_selector = "k | other".into();
    assert_ne!(manifest_spec_digest(&other_selector), after_main);
    // Re-pin L1-4-tail (review L1-4-2 N1): so is every other field of `[spec]`, over the same
    // files. Two manifests that differ only in their main or syntax module load different
    // definitions from the same files, and the result cache, tier 1 and the resolution and
    // census memos are keyed by this digest: a field it dropped would let one definition's
    // results, outcomes and memos serve the other.
    let files = load_source(&corpus_source(&manifest)).unwrap().files;
    assert_eq!(spec_digest(&manifest, &files).to_string(), after_main);
    let with = |change: &dyn Fn(&mut SpecSection)| {
        let mut other = manifest.clone();
        change(&mut other.spec);
        spec_digest(&other, &files).to_string()
    };
    for (field, digest) in [
        ("entry", with(&|spec| spec.entry = "include/lib.k".into())),
        ("main_module", with(&|spec| spec.main_module = "LIB".into())),
        (
            "syntax_module",
            with(&|spec| spec.syntax_module = Some("LIB".into())),
        ),
        (
            "include_dirs",
            with(&|spec| spec.include_dirs.push("more".into())),
        ),
        (
            "md_selector",
            with(&|spec| spec.md_selector = "k | other".into()),
        ),
    ] {
        assert_ne!(digest, after_main, "the spec digest does not name {field}");
    }
    // The whole payload, built here from the manifest's values and the files' own bytes, also
    // pins the build constants (the k-rust revision, the solver profile), which no manifest
    // varies.
    let expected_files = ["include/lib.k", "main.k"].map(|name| {
        json!({"name": name, "sha256": sha256(&fs::read(dir.join(name)).unwrap()).to_string()})
    });
    assert_eq!(
        spec_payload(&manifest, &files),
        json!({
            "k_rust_revision": K_RUST_REVISION,
            "profile": SolverProfile::BUILD.name(),
            "entry": "main.k",
            "main_module": "MAIN",
            "syntax_module": null,
            "md_selector": manifest.spec.md_selector,
            "include_dirs": ["include"],
            "files": expected_files,
        })
    );
}

#[test]
fn a_program_digest_changes_with_its_text_start_sort_and_variables_only() {
    let program = |id: &str| Program {
        id: id.into(),
        source: Some(ProgramSource::Text(String::new())),
        start_sort: None,
        variables: vec![("A".into(), "1".into()), ("B".into(), "2".into())],
        inputs: toml::Table::new(),
        case: None,
        case_file: None,
        expect: None,
        stop_count: None,
    };
    let base = program_digest(&program("p"), &"1 + 2".into());
    let other = program_digest(&program("q"), &"3".into());
    assert_eq!(program_digest(&program("renamed"), &"1 + 2".into()), base);
    assert_ne!(program_digest(&program("p"), &"1 + 3".into()), base);
    assert_eq!(program_digest(&program("q"), &"3".into()), other);
    let mut sorted = program("p");
    sorted.start_sort = Some("Exp".into());
    assert_ne!(program_digest(&sorted, &"1 + 2".into()), base);
    let mut variable = program("p");
    variable.variables[1].1 = "3".into();
    assert_ne!(program_digest(&variable, &"1 + 2".into()), base);
    let mut fewer = program("p");
    fewer.variables.pop();
    assert_ne!(program_digest(&fewer, &"1 + 2".into()), base);
    let mut reversed = program("p");
    reversed.variables.reverse();
    assert_eq!(program_digest(&reversed, &"1 + 2".into()), base);
    // A program with a program text and no typed inputs keeps the digest it had before typed
    // inputs existed: the v1 payload, byte for byte, so no cached result or outcome is lost.
    let v1 = kink_patch::payload_digest(
        kink_flow::digest::PROGRAM_DOMAIN,
        kink_patch::canonical_json(&json!({
            "program_sha256": sha256(b"1 + 2").to_string(),
            "start_sort": null,
            "variables": [{"name": "A", "text": "1"}, {"name": "B", "text": "2"}],
        }))
        .as_bytes(),
    );
    assert_eq!(base, v1);
    // A program-less case is no program with an empty text.
    let bare = CaseInputs {
        text: None,
        typed: Vec::new(),
        bound: None,
    };
    assert_ne!(
        program_digest(&program("p"), &bare),
        program_digest(&program("p"), &"".into())
    );
}

/// Re-pin R0c-fix-1 deliverable 1: the campaign runner now admits a baseline run that contradicts
/// a trusted claim and makes only its test unknown (decision 2 per test), so `results` reads the
/// run's missing sides itself: the program is `unknown`, never `comparable`, with the exclusion in
/// its cause (before, the runner refused the run and the class was `unknown` too). Another
/// program of the same definition is comparable.
#[test]
fn a_contradicted_baseline_program_is_unknown() {
    let dir = scratch("contradicted-baseline");
    write(
        &dir.join("contra.k"),
        r"module CONTRA-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= tdiv(Int) [symbol(tdiv)]
                | val(Int) [symbol(val)]
  syntax Int ::= td(Int) [function, total, symbol(td)]
endmodule

module CONTRA
  imports CONTRA-SYNTAX
  imports INT
  configuration <k> $PGM:Prog </k>
  rule [tdeq]: td(I) => 10 /Int (I +Int 1)
  rule [tdiv]: <k> tdiv(I) => val(td(I)) </k>
endmodule
",
    );
    write(
        &dir.join("FLOW.toml"),
        "[spec]\nentry = \"contra.k\"\nmain_module = \"CONTRA\"\nsyntax_module = \"CONTRA-SYNTAX\"\n\n\
         [[program]]\nid = \"base\"\ntext = \"tdiv(-1)\"\n\n[[program]]\nid = \"kill\"\ntext = \"tdiv(1)\"\n",
    );
    let (document, status) = run(&dir.join("FLOW.toml"), false);
    assert_eq!(status, EXIT_UNANSWERED, "{document:#}");
    assert_eq!(
        rows(&document),
        expect(&[("base", "unknown", false), ("kill", "comparable", false)])
    );
    let cause = document["programs"][0]["cause"].as_str().unwrap();
    assert!(
        cause.starts_with(
            "the campaign runner gave the baseline run no sides: contradicted-claim; "
        ),
        "{cause}"
    );
}

/// A definition whose short-circuit analysis flags the rule `at`: its successor applies
/// `andThenBool` over `10 /Int I >Int 0`, which is undefined at `I = 0` in k-rust's reading and
/// skipped by a reading that evaluates the deciding `false` alone.
const SCR_K: &str = r"module SCR-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Prog ::= at(Int) [symbol(at)] | res(Bool) [symbol(res)]
endmodule

module SCR
  imports SCR-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Prog </k>
  rule [at]: <k> at(I) => res(false andThenBool 10 /Int I >Int 0) </k>
endmodule
";

/// CF-03: on a definition whose short-circuit analysis flags a rule, each program's baseline run
/// is judged by k-rust's list of that run's short-circuit readings, not the definition as a
/// whole. `at(0)`'s run reads the operand `10 /Int 0 >Int 0` that `andThenBool` skips after the
/// deciding `false`, under the flagged rule `at`, so it is `unknown` and its row names the step
/// (rule, operator, outcome, operand), in its cause and as data; `at(1)`'s run reads a defined
/// operand, lists nothing and is comparable. The document's `spec.exclusion` is null and
/// `spec.short_circuit` names the flagged rule. Both results are functions of their keys, so a
/// second command reads them from the cache with the same rows; and `check` makes no program
/// `excluded` for the flag.
#[test]
fn a_flagged_definition_judges_each_program_by_its_short_circuit_readings() {
    let dir = scratch("short-circuit-readings");
    write(&dir.join("scr.k"), SCR_K);
    write(
        &dir.join("FLOW.toml"),
        "[spec]\nentry = \"scr.k\"\nmain_module = \"SCR\"\nsyntax_module = \"SCR-SYNTAX\"\n\n\
         [[program]]\nid = \"zero\"\ntext = \"at(0)\"\n\n[[program]]\nid = \"one\"\ntext = \"at(1)\"\n",
    );
    let manifest = dir.join("FLOW.toml");
    let (document, status) = run(&manifest, false);
    assert_eq!(status, EXIT_UNANSWERED, "{document:#}");
    assert_eq!(
        rows(&document),
        expect(&[("zero", "unknown", false), ("one", "comparable", false)])
    );
    assert!(document["spec"]["exclusion"].is_null(), "{document:#}");
    let flagged = &document["spec"]["short_circuit"];
    let causes = flagged["causes"].as_array().unwrap();
    assert_eq!(causes.len(), 1, "{flagged:#}");
    assert_eq!(causes[0]["rule"]["label"], "SCR.at", "{flagged:#}");
    let zero = &document["programs"][0];
    let readings = zero["short_circuit_readings"].as_array().unwrap();
    assert!(!readings.is_empty(), "{zero:#}");
    for reading in readings {
        assert_eq!(reading["operator"], "BOOL.andThen", "{reading:#}");
        assert_eq!(reading["outcome"], "undefined", "{reading:#}");
        assert_eq!(reading["rule"]["label"], "SCR.at", "{reading:#}");
        assert_eq!(reading["observed_in"], "run", "{reading:#}");
        assert_eq!(reading["operand"]["rendering"], "kore", "{reading:#}");
        assert!(
            reading["operand"]["text"].as_str().unwrap().contains("Int"),
            "{reading:#}"
        );
    }
    let cause = zero["cause"].as_str().unwrap();
    for part in [
        "the run is excluded (short-circuit-reading)",
        "in the work of rule SCR.at",
        "the operand of BOOL.andThen after its deciding one",
        "undefined",
    ] {
        assert!(cause.contains(part), "{part:?} in {cause}");
    }
    let one = &document["programs"][1];
    assert_eq!(one["short_circuit_readings"], json!([]), "{one:#}");

    let (again, status) = run(&manifest, false);
    assert_eq!(status, EXIT_UNANSWERED, "{again:#}");
    assert_eq!(
        rows(&again),
        expect(&[("zero", "unknown", true), ("one", "comparable", true)])
    );
    for index in 0..2 {
        for key in ["cause", "short_circuit_readings"] {
            assert_eq!(
                again["programs"][index][key], document["programs"][index][key],
                "{key} of program {index}"
            );
        }
    }

    let (checked, status) = std::thread::Builder::new()
        .stack_size(kink_corpus::cli::DEFINITION_STACK_BYTES)
        .spawn(move || kink_flow::cli::check(&manifest))
        .unwrap()
        .join()
        .unwrap();
    assert_eq!(status, EXIT_YES, "{checked:#}");
    assert_eq!(&checked["spec"]["short_circuit"], flagged);
    for program in checked["programs"].as_array().unwrap() {
        assert_eq!(program["outcome"], "ok", "{program:#}");
    }
}

/// The build identity of the executable at `path`, as its records name it.
fn build_of(path: &Path) -> String {
    kink_campaign::identity::build_identity_of(path)
        .unwrap()
        .to_string()
}

/// The empty generation a zero-mutant campaign runs (as kink-corpus `baseline_only`).
fn run_together(
    spec: &kink_flow::AdmittedSpec,
    manifest: &FlowManifest,
    tests: &[TestCase],
) -> Vec<Value> {
    let discovery = Discovery::empty(spec.validator.baseline(), false, false);
    let generation = select(&discovery, SelectionPolicy::Each, 1)
        .unwrap()
        .fold("test", |_| -> Patch { unreachable!() })
        .unwrap();
    let module = k_rust::kast::identifier::encode(&manifest.spec.main_module);
    let campaign = Campaign {
        validator: &spec.validator,
        module: &module,
        observation: &[],
        classify: &all_normal,
        tests,
        budget: execution_budget(manifest.budget),
    };
    let run = run_campaign_multi(
        &campaign,
        &[generation],
        &CampaignOptions {
            schedule: ScheduleMode::FirstKill,
            selection: kink_campaign::SelectionPolicy::None,
            share_evidence: true,
            run: kink_campaign::RunOptions::default(),
            compile_workers: 1,
        },
    )
    .unwrap();
    run.baseline
        .iter()
        .map(CampaignReport::baseline_row)
        .collect()
}

mod kink_tier {
    use super::*;

    /// KINK-guard-coverage: a rule's status names the predicate it tests, and a guarded rule's
    /// row reports its guard per operand. No program halts, so the complementary rules `wake`
    /// and `halted` are matched (their conditions entered) and never fired, with no `held_by`,
    /// and `wake`'s operand `H` is never `true`; `dispatch`'s `notBool H` is never `false` and
    /// its `I` is reached only where `notBool H` is `true`; no program writes a high address, so
    /// the equation `low` is never refuted. The requirements family states each distinct
    /// (node, truth) pair once, the root's outcomes standing for the node truths they are.
    #[test]
    #[ignore = "kink"]
    fn guards_report_each_operand_and_statuses_name_their_predicate() {
        let manifest = fixture("guards", "guards").join("FLOW.toml");
        let (document, status) = run(&manifest, false);
        assert_eq!(status, EXIT_YES, "{document:#}");
        let rule = |label: &str| {
            rules(&document)
                .iter()
                .find(|rule| rule["label"] == format!("GUARDS.{label}"))
                .unwrap_or_else(|| panic!("no rule {label}: {document:#}"))
                .clone()
        };
        let statuses = ["dispatch", "run", "wake", "halted", "low", "writing"]
            .map(|label| (label, rule(label)["status"].as_str().unwrap().to_owned()));
        assert_eq!(
            statuses,
            [
                ("dispatch", "fired".to_owned()),
                ("run", "fired".to_owned()),
                ("wake", "matched".to_owned()),
                ("halted", "matched".to_owned()),
                ("low", "fired".to_owned()),
                ("writing", "fired".to_owned()),
            ]
        );
        for label in ["wake", "halted"] {
            let guard = &rule(label)["guard"];
            assert_eq!(guard["held_by"], json!([]), "{label}: {guard:#}");
            assert_eq!(guard["never"], json!(["held"]), "{label}: {guard:#}");
        }
        let wake = &rule("wake")["guard"];
        let operands = wake["operands"].as_array().unwrap();
        assert_eq!(operands[0]["path"], "0");
        assert_eq!(operands[0]["kind"], "conjunction");
        assert_eq!(operands[0]["connective"], "andThenBool");
        assert_eq!(operands[0]["operands"], json!(["0.0", "0.1"]));
        assert_eq!(operands[1]["path"], "0.0");
        assert_eq!(operands[1]["kind"], "atom");
        assert_eq!(operands[1]["true_by"], json!([]));
        assert_eq!(operands[1]["false_by"], json!(["irq", "idle"]));
        assert_eq!(operands[1]["never"], json!(["true"]));
        // `I` is reached only where `H` is true: never.
        assert_eq!(operands[2]["true_by"], json!([]));
        assert_eq!(operands[2]["false_by"], json!([]));
        let dispatch = &rule("dispatch")["guard"];
        assert_eq!(dispatch["held_by"], json!(["irq"]));
        assert_eq!(dispatch["refuted_by"], json!(["idle"]));
        // A negation restates its operand: `notBool H` never false is `H` never true.
        let not_h = &dispatch["operands"][1];
        assert_eq!(not_h["kind"], "negation");
        assert!(not_h.get("never").is_none(), "{dispatch:#}");
        assert_eq!(not_h["true_by"], json!(["irq", "idle"]));
        let h = &dispatch["operands"][2];
        assert_eq!(h["kind"], "atom");
        assert_eq!(h["never"], json!(["true"]));
        // The conjunction restates its operands too.
        assert!(
            dispatch["operands"][0].get("never").is_none(),
            "{dispatch:#}"
        );
        let i = &dispatch["operands"][3];
        assert_eq!(i["path"], "0.1");
        assert_eq!(i["true_by"], json!(["irq"]));
        assert_eq!(i["false_by"], json!(["idle"]));
        let low = &rule("low")["guard"];
        assert_eq!(low["held_by"], json!(["write"]));
        assert_eq!(low["refuted_by"], json!([]));
        assert_eq!(low["never"], json!(["refuted"]));
        assert_eq!(low["operands"][0]["kind"], "atom");
        assert!(
            low["operands"][0]["text"]
                .as_str()
                .unwrap()
                .contains("32768"),
            "{low:#}"
        );
        // The requirements family: per guarded rule the condition's root and each authored
        // atom, each truth. `wake`'s `H` was seen false only, and its `I` never reached.
        let requirement = |id: &str| {
            document["families"]["requirements"]["items"]
                .as_array()
                .unwrap()
                .iter()
                .find(|item| item["id"] == id)
                .unwrap_or_else(|| panic!("no requirement {id}: {document:#}"))
                .clone()
        };
        let h_text = operands[1]["text"].as_str().unwrap();
        let i_text = operands[2]["text"].as_str().unwrap();
        // `H andThenBool I` holds exactly where `I` is reached true, its last conjunct: one
        // obligation, the root's `held`, with the node.
        let held = requirement("requirement:GUARDS.wake:held");
        assert_eq!(
            (&held["status"], &held["covered_by"]),
            (&json!("open"), &json!([]))
        );
        assert_eq!(held["rule"], "rule:GUARDS.wake");
        assert_eq!(
            (&held["node"], &held["node_truth"]),
            (&json!("0.1"), &json!("true"))
        );
        assert_eq!(held["text"], i_text);
        assert_eq!(held["reaching"], json!([{"text": h_text, "truth": true}]));
        let h_false = requirement(&format!("requirement:GUARDS.wake:{h_text}:false"));
        assert_eq!(h_false["covered_by"], json!(["irq", "idle"]));
        let i_false = requirement(&format!("requirement:GUARDS.wake:{i_text}:false"));
        assert_eq!(i_false["status"], "open");
        assert_eq!(
            i_false["reaching"],
            json!([{"text": h_text, "truth": true}])
        );
        // Each distinct (node, truth) once: `wake` has `held` (I true), `refuted`, H true, H
        // false and I false; `halted` (`H andThenBool notBool I`) holds where I is reached false.
        let of_rule = |rule: &str| {
            document["families"]["requirements"]["items"]
                .as_array()
                .unwrap()
                .iter()
                .filter(|item| item["rule"] == rule)
                .map(|item| item["id"].as_str().unwrap().to_owned())
                .collect::<Vec<_>>()
        };
        assert_eq!(
            of_rule("rule:GUARDS.wake"),
            [
                "requirement:GUARDS.wake:held".to_owned(),
                "requirement:GUARDS.wake:refuted".to_owned(),
                format!("requirement:GUARDS.wake:{h_text}:true"),
                format!("requirement:GUARDS.wake:{h_text}:false"),
                format!("requirement:GUARDS.wake:{i_text}:false"),
            ]
        );
        let halted = requirement("requirement:GUARDS.halted:held");
        assert_eq!(
            (&halted["node"], &halted["node_truth"]),
            (&json!("0.1.0"), &json!("false"))
        );
        assert!(
            !of_rule("rule:GUARDS.halted")
                .contains(&format!("requirement:GUARDS.halted:{i_text}:false")),
            "{document:#}"
        );
        // A condition that is one atom has two obligations, its `held` (the atom true) and its
        // `refuted` (the atom false), not four.
        assert_eq!(
            of_rule("rule:GUARDS.low"),
            [
                "requirement:GUARDS.low:held",
                "requirement:GUARDS.low:refuted"
            ]
        );
        let low = requirement("requirement:GUARDS.low:refuted");
        assert_eq!(low["status"], "open");
        assert_eq!(
            (&low["node"], &low["node_truth"]),
            (&json!("0"), &json!("false"))
        );
        assert_eq!(
            requirement("requirement:GUARDS.low:held")["covered_by"],
            json!(["write"])
        );
        // A matched rule is open, and its target asks for its condition to hold, naming the open
        // requirement and the programs that entered it as fuzz templates.
        let targets = document["targets"].as_array().unwrap();
        let wake_target = targets
            .iter()
            .find(|target| target["item"] == "rule:GUARDS.wake")
            .unwrap();
        assert_eq!(
            wake_target["text"],
            "a case where GUARDS.wake is entered and its condition holds, so that its right-hand \
             side is built on a path (requirement requirement:GUARDS.wake:held is open)"
        );
        assert_eq!(wake_target["programs"], json!(["irq", "idle"]));
        assert_eq!(
            wake_target["fuzz"],
            "kink-flow fuzz FLOW.toml TEMPLATES.toml --template ID --fired GUARDS.wake"
        );
        let held_target = targets
            .iter()
            .find(|target| target["item"] == held["id"])
            .unwrap();
        assert_eq!(
            held_target["text"],
            format!(
                "a case that enters GUARDS.wake with its condition holding ({h_text} true and \
                 {i_text} true)"
            )
        );
        let i_target = targets
            .iter()
            .find(|target| target["item"] == i_false["id"])
            .unwrap();
        assert_eq!(
            i_target["text"],
            format!("a case that enters GUARDS.wake with {h_text} true and {i_text} false")
        );
        // An unmatched rewrite rule's target carries its left-hand side as a pattern; the
        // equation `high` has none (an equation's left-hand side is no configuration).
        let high_target = targets
            .iter()
            .find(|target| target["item"] == "rule:GUARDS.high")
            .unwrap();
        assert_eq!(high_target["pattern"], Value::Null);
        // Targets follow tier, family, then sentence order: every rule target first.
        let families = targets
            .iter()
            .map(|target| target["family"].as_str().unwrap())
            .collect::<Vec<_>>();
        let first_requirement = families.iter().position(|f| *f == "requirements").unwrap();
        assert!(
            families[first_requirement..]
                .iter()
                .all(|f| *f == "requirements")
        );
        // Counts and measures.
        let family = &document["families"]["rules"];
        // No program's run matches `high` (the store of a low address is decided by `low`).
        assert_eq!(family["counts"]["fired"], 4);
        assert_eq!(family["counts"]["matched"], 2);
        assert_eq!(family["counts"]["unmatched"], 1);
        assert_eq!(family["measure"], json!(4.0 / 7.0));
        let requirements = &document["families"]["requirements"];
        let items = requirements["items"].as_array().unwrap();
        let covered = items.iter().filter(|item| item["covered"] == true).count();
        assert_eq!(requirements["obligations"], json!(items.len()));
        assert_eq!(requirements["covered"], json!(covered));
        assert_eq!(requirements["counts"]["open"], json!(items.len() - covered));
        let ratio = covered as f64 / items.len() as f64;
        assert_eq!(requirements["measure"], json!(ratio));
        assert_eq!(
            document["summary"]["open"],
            json!(targets.len()),
            "{document:#}"
        );
        // kink-flow's own front end derives no flips, so the family does not run, and says why.
        assert_eq!(document["families"]["flips"]["run"], false);
        assert_eq!(
            document["families"]["flips"]["reason"],
            kink_flow::flips::DERIVES_NONE
        );
        assert_eq!(document["settings"]["tiers"], json!([1]));
        // The verdicts rendering lists each family's open ids, without program lists.
        let verdicts = kink_flow::verdicts::verdicts(&document).unwrap();
        assert!(
            verdicts.contains(
                "\n[rules]\nopen = [\"rule:GUARDS.wake\", \"rule:GUARDS.halted\", \"rule:GUARDS.high\"]\n"
            ),
            "{verdicts}"
        );
        assert!(
            verdicts.contains("\"requirement:GUARDS.wake:held\""),
            "{verdicts}"
        );
        assert!(verdicts.contains("\n[flips]\nrun = false\n"), "{verdicts}");
        assert!(!verdicts.contains("irq"), "no program list: {verdicts}");
        // The text rendering lists the targets in the document's order.
        let text = kink_flow::coverage::text(&document).unwrap();
        let listed = text
            .lines()
            .skip_while(|line| *line != "targets:")
            .skip(1)
            .filter(|line| !line.starts_with("    "))
            .collect::<Vec<_>>();
        let expected = targets
            .iter()
            .map(|target| {
                format!(
                    "  {} ({}:{}): {}",
                    target["item"].as_str().unwrap(),
                    target["file"].as_str().unwrap(),
                    target["line"],
                    target["text"].as_str().unwrap()
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(listed, expected, "{text}");
    }

    /// An unmatched rewrite rule's target carries its left-hand side as a pattern `query` takes:
    /// the rule's body with each rewrite's left side, each variable with the sort the rule's
    /// parse inferred (here from the right side: `- I1 => 0 -Int I1` makes `I1` an `Int`), in the
    /// main cell where the compile places a cell-free rule. `query` admits each, and no program
    /// reaches it, as the rule's status says.
    #[test]
    #[ignore = "kink"]
    fn an_unmatched_rewrite_rules_target_is_a_pattern_query_takes() {
        let dir = fixture("fuzz/impu", "unmatched-pattern");
        let manifest = dir.join("FLOW.toml");
        let (document, status) = run(&manifest, false);
        assert_eq!(status, EXIT_YES, "{document:#}");
        let patterns = document["targets"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|target| target["family"] == "rules")
            .map(|target| (target["item"].clone(), target["pattern"].clone()))
            .collect::<Vec<_>>();
        assert_eq!(
            patterns,
            [
                (json!("rule:imp.k:47"), json!("<k> - I1:Int ...</k>")),
                (json!("rule:imp.k:50"), json!("<k> ! T:Bool ...</k>")),
                (json!("rule:imp.k:52"), json!("<k> false && _:BExp ...</k>")),
            ]
        );
        let mut list = String::new();
        for (index, (_, pattern)) in patterns.iter().enumerate() {
            list.push_str(&format!(
                "[[pattern]]\nid = \"p{index}\"\npattern = {pattern}\n\n"
            ));
        }
        let list_path = dir.join("PATTERNS.toml");
        write(&list_path, &list);
        let (answers, status) = {
            let (manifest, list_path) = (manifest.clone(), list_path.clone());
            std::thread::Builder::new()
                .stack_size(kink_corpus::cli::DEFINITION_STACK_BYTES)
                .spawn(move || {
                    kink_flow::cli::query(
                        &manifest,
                        &list_path,
                        &kink_flow::query::QueryOptions::default(),
                    )
                })
                .unwrap()
                .join()
                .unwrap()
        };
        assert_eq!(status, EXIT_YES, "{answers:#}");
        for pattern in answers["patterns"].as_array().unwrap() {
            assert_eq!(pattern["outcome"], "valid", "{pattern:#}");
        }
        for row in answers["rows"].as_array().unwrap() {
            assert_eq!(row["answer"], "no", "{row:#}");
        }
    }

    /// A case that covers nothing new leaves the verdicts rendering byte-identical; a case that
    /// closes a gap moves it. `--tier 1`, the only tier this build computes, runs no mutant: the
    /// flips family says so.
    #[test]
    #[ignore = "kink"]
    fn the_verdicts_move_only_when_a_gap_opens_or_closes() {
        let manifest = fixture("guards", "guards-verdicts").join("FLOW.toml");
        let (before, status) = run(&manifest, false);
        assert_eq!(status, EXIT_YES, "{before:#}");
        let before = kink_flow::verdicts::verdicts(&before).unwrap();
        append(
            &manifest,
            "\n[[program]]\nid = \"idle-again\"\nfile = \"programs/idle.guards\"\n",
        );
        let (same, status) = run(&manifest, false);
        assert_eq!(status, EXIT_YES, "{same:#}");
        assert_eq!(same["summary"]["programs"], 4);
        assert_eq!(kink_flow::verdicts::verdicts(&same).unwrap(), before);
        append(
            &manifest,
            "\n[[program]]\nid = \"halting\"\ntext = \"step(true, true)\"\n",
        );
        let (closed, status) = run(&manifest, false);
        assert_eq!(status, EXIT_YES, "{closed:#}");
        let after = kink_flow::verdicts::verdicts(&closed).unwrap();
        assert_ne!(after, before);
        assert!(!after.contains("\"rule:GUARDS.wake\""), "{after}");
        let (tier_one, status) = coverage(
            &manifest,
            &CoverageOptions {
                tier: Tier::One,
                ..CoverageOptions::default()
            },
        );
        assert_eq!(status, EXIT_YES, "{tier_one:#}");
        assert_eq!(tier_one["settings"]["tiers"], json!([1]));
        assert_eq!(
            tier_one["families"]["flips"],
            json!({"tier": 2, "run": false, "obligations": null, "items": [],
                   "reason": kink_flow::flips::DERIVES_NONE})
        );
    }

    /// A simplification is out of scope by status: no obligation, never a target, whatever its
    /// coverage.
    #[test]
    #[ignore = "kink"]
    fn a_simplification_is_out_of_scope() {
        let dir = fixture("guards", "guards-simplification");
        let source = dir.join("guards.k");
        let text = fs::read_to_string(&source).unwrap();
        let anchor = "  rule [writing]:";
        assert!(text.contains(anchor));
        fs::write(
            &source,
            text.replace(
                anchor,
                &format!("  rule [lemma]: store(A) +Int 0 => store(A) [simplification]\n{anchor}"),
            ),
        )
        .unwrap();
        let (document, status) = run(&dir.join("FLOW.toml"), false);
        assert_eq!(status, EXIT_YES, "{document:#}");
        let lemma = rules(&document)
            .iter()
            .find(|rule| rule["label"] == "GUARDS.lemma")
            .unwrap_or_else(|| panic!("{document:#}"));
        assert_eq!(lemma["status"], "out-of-scope");
        assert_eq!(lemma["obligation"], false);
        assert!(lemma["reason"].as_str().unwrap().contains("simplification"));
        assert_eq!(document["families"]["rules"]["counts"]["out_of_scope"], 1);
        assert_eq!(document["families"]["rules"]["obligations"], 7);
        assert!(
            document["targets"]
                .as_array()
                .unwrap()
                .iter()
                .all(|target| target["item"] != "rule:GUARDS.lemma"),
            "{document:#}"
        );
    }

    /// `[coverage]` is decoded by every command and refused by `coverage` where this build cannot
    /// honour it, before anything runs.
    #[test]
    #[ignore = "kink"]
    fn unsupported_coverage_settings_are_refused_with_their_reason() {
        let dir = fixture("guards", "guards-settings");
        let manifest = dir.join("FLOW.toml");
        let text = fs::read_to_string(&manifest).unwrap();
        for (section, reason) in [
            ("[coverage]\ndepth = 2\n", "depth-unsupported"),
            ("[coverage]\nmcdc = [\"GUARDS.wake\"]\n", "mcdc-unsupported"),
        ] {
            write(&manifest, &format!("{section}\n{text}"));
            let (document, status) = run(&manifest, false);
            assert_eq!(status, EXIT_UNASKED, "{document:#}");
            assert_eq!(document["spec"]["stage"], "coverage");
            assert_eq!(document["spec"]["reason"], reason);
            assert_eq!(document["programs"], json!([]));
            assert_eq!(document["families"], Value::Null);
        }
        write(
            &manifest,
            &format!("[coverage]\ndepth = 1\nmax_obligations = 10\n\n{text}"),
        );
        let (document, status) = run(&manifest, false);
        assert_eq!(status, EXIT_YES, "{document:#}");
        assert_eq!(
            document["settings"],
            json!({"tiers": [1], "depth": 1, "mcdc": [], "max_obligations": 10,
                   "source": "manifest"})
        );
        write(&manifest, &format!("[coverage]\nwidth = 1\n\n{text}"));
        let (document, status) = run(&manifest, false);
        assert_eq!(status, EXIT_UNASKED, "{document:#}");
        assert_eq!(document["spec"]["stage"], "manifest");
    }

    /// A rule only a program that is not comparable fires is open, and lists that program as
    /// `touched_only_by`: its target is to make the program comparable.
    #[test]
    #[ignore = "kink"]
    fn an_item_touched_only_by_an_unknown_program_names_it() {
        let dir = scratch("touched-only");
        write(
            &dir.join("contra.k"),
            r"module CONTRA-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= tdiv(Int) [symbol(tdiv)]
                | odd(Int) [symbol(odd)]
                | val(Int) [symbol(val)]
  syntax Int ::= td(Int) [function, total, symbol(td)]
endmodule

module CONTRA
  imports CONTRA-SYNTAX
  imports INT
  configuration <k> $PGM:Prog </k>
  rule [tdeq]: td(I) => 10 /Int (I +Int 1)
  rule [tdiv]: <k> tdiv(I) => val(td(I)) </k>
  rule [odd]: <k> odd(I) => val(td(I)) </k>
endmodule
",
        );
        write(
            &dir.join("FLOW.toml"),
            "[spec]\nentry = \"contra.k\"\nmain_module = \"CONTRA\"\nsyntax_module = \"CONTRA-SYNTAX\"\n\n\
             [[program]]\nid = \"base\"\ntext = \"odd(-1)\"\n\n[[program]]\nid = \"kill\"\ntext = \"tdiv(1)\"\n",
        );
        let (document, status) = run(&dir.join("FLOW.toml"), false);
        assert_eq!(status, EXIT_UNANSWERED, "{document:#}");
        assert_eq!(
            rows(&document),
            expect(&[("base", "unknown", false), ("kill", "comparable", false)])
        );
        let odd = rules(&document)
            .iter()
            .find(|rule| rule["label"] == "CONTRA.odd")
            .unwrap();
        assert_eq!(odd["status"], "unmatched");
        assert_eq!(odd["touched_only_by"], json!(["base"]));
        let tdiv = rules(&document)
            .iter()
            .find(|rule| rule["label"] == "CONTRA.tdiv")
            .unwrap();
        assert_eq!(tdiv["touched_only_by"], json!([]));
        let target = document["targets"]
            .as_array()
            .unwrap()
            .iter()
            .find(|target| target["item"] == "rule:CONTRA.odd")
            .unwrap();
        assert!(
            target["text"]
                .as_str()
                .unwrap()
                .ends_with("; base touches it but is not comparable: make one comparable (its row's cause says why)"),
            "{target:#}"
        );
    }

    /// kink27 R5-BYTES-ENDS: a Bytes domain value has a trusted injective codec (its payload is its
    /// sort's one stored form), so the Bytes-keyed Map the `store` rule leaves is a value and the
    /// program is comparable. Before, TV-01 refused the key's Bytes value (CS-T04), and the oracle
    /// gate left the program `unknown`.
    #[test]
    #[ignore = "kink"]
    fn a_bytes_key_is_comparable() {
        let manifest = fixture("bytes-map", "bytes-map").join("FLOW.toml");
        let (document, status) = run(&manifest, false);
        assert_eq!(status, EXIT_YES, "{document:#}");
        assert_eq!(rows(&document), expect(&[("store", "comparable", false)]));
        assert_eq!(rules(&document)[0]["matched_by"], json!(["store"]));
        let record = stored_record(&manifest, &document, "store");
        assert_eq!(record["class"], "comparable");
        assert!(
            !record["baseline"].is_null() && !record["run_sha256"].is_null(),
            "{record:#}"
        );
        let finals = record_final_configuration(&record).unwrap();
        assert_eq!(finals.len(), 1);
        let text = finals[0];
        assert!(text.contains("\\dv{SortBytes{}}(\"a\")"), "{text}");
    }

    /// fz26 KRUST-ANYWHERE-HEAD: on SIMPLE (TRIAL2's stream-free copy,
    /// `testdata/k/overload/simple.md`), an array declaration leaves `var a[1];` in `main`'s
    /// closure in the store, an `Exps` list holding `a[1]`. Before, `_[_]` rooted `[anywhere]`
    /// rules that are not overload equations, so it was no data head and the program was unknown
    /// (KINK-CAUSE-SUBTERM named that list under `<T>/<store>`, and `_[_]` inside it). Now `_[_]`
    /// is a data head (`anywhere`, `value-production`, plain equations), and no `[anywhere]` rule
    /// of it matches `a[1]` (the receiver is an `Id`, not a `Val`): the application is a normal
    /// form in every context and a value of its sort, the list over it is data, and the program
    /// is comparable.
    #[test]
    #[ignore = "kink"]
    fn an_array_declaration_is_comparable() {
        let dir = scratch("cause-subterm-simple");
        fs::copy(
            Path::new(env!("CARGO_MANIFEST_DIR")).join("../../testdata/k/overload/simple.md"),
            dir.join("simple.md"),
        )
        .unwrap();
        let manifest = dir.join("FLOW.toml");
        write(
            &manifest,
            r#"[spec]
entry = "simple.md"
main_module = "SIMPLE-UNTYPED"
syntax_module = "SIMPLE-UNTYPED-SYNTAX"
[[program]]
id = "arr-decl"
text = 'function main() { var a[1]; }'
"#,
        );
        let (document, status) = run(&manifest, false);
        assert_eq!(status, EXIT_YES, "{document:#}");
        assert_eq!(
            rows(&document),
            expect(&[("arr-decl", "comparable", false)])
        );
    }

    /// fz26 KINK-CAUSE-SUBTERM (P7-SIMPLE-IN, review S7), on an overloaded list (FZ-OVERLIST's
    /// `ov`) that holds `opaque(1)`, a total function's application no equation reduces: its
    /// value is whatever a model makes of `opaque`, so it is not data, and neither is the list
    /// over it. Every node above the list passes its own test, so the cause names that `Exps`
    /// list, a data-head application k-rust does not judge data, under `<s>`, not the root, and,
    /// inside it, the `opaque` application (before KRUST-ANYWHERE-HEAD a SIMPLE array
    /// declaration showed the same, with `_[_]` inside; that program is comparable now).
    #[test]
    #[ignore = "kink"]
    fn an_overloaded_list_names_the_application_inside_it() {
        let dir = scratch("cause-subterm-ov");
        write(
            &dir.join("ovf.k"),
            r#"module OVF-SYNTAX
  imports DOMAINS-SYNTAX
  syntax Exp  ::= Int | Id | opaque(Int) [function, total]
  syntax Ids  ::= List{Id,","}  [overload(Exps)]
  syntax Exps ::= List{Exp,","} [overload(Exps)]
  syntax Exps ::= Ids
  syntax Pgm  ::= "h" "(" Exps ")"
endmodule
module OVF
  imports OVF-SYNTAX
  imports DOMAINS
  configuration <k> $PGM:Pgm </k> <s> .K </s>
  rule <k> h(Es) => .K </k> <s> _ => Es </s>
  rule opaque(0) => 0
endmodule
"#,
        );
        let manifest = dir.join("FLOW.toml");
        write(
            &manifest,
            r#"[spec]
entry = "ovf.k"
main_module = "OVF"
syntax_module = "OVF-SYNTAX"
[[program]]
id = "opaque"
text = 'h(opaque(1), 2)'
"#,
        );
        let (document, status) = run(&manifest, false);
        assert_eq!(status, EXIT_UNANSWERED, "{document:#}");
        assert_eq!(rows(&document), expect(&[("opaque", "unknown", false)]));
        let cause = document["programs"][0]["cause"].as_str().unwrap();
        for part in [
            "every path ended, but a final configuration is not a value kink can compare: in the \
             stuck leaf at depth 1, the first node, in pre-order, that fails its own test is an \
             application of `_,__OVF-SYNTAX_Exps_Exp_Exps` at <s>",
            "it is an application of a data head that k-rust does not judge data",
            "inside it, an application of `opaque(_)_OVF-SYNTAX_Exp_Int` fails its own test: its \
             head is neither a free constructor",
        ] {
            assert!(cause.contains(part), "{part}\n{cause}");
        }
    }

    /// Re-pin L2-1-tail (review L2-1-1, D1): a `non-executable` rule is one k-rust never runs, so no
    /// program can reach it. It has no coverage signal, with its own reason, and is never listed
    /// `unmatched`, the group of the next program to write.
    #[test]
    #[ignore = "kink"]
    fn a_non_executable_rule_has_no_coverage_signal() {
        let dir = fixture("loop", "rules-non-executable");
        let source = dir.join("loop.k");
        let text = fs::read_to_string(&source).unwrap();
        let equation = "  rule double(I) => I *Int 2\n";
        assert!(text.contains(equation));
        fs::write(
            &source,
            text.replace(
                equation,
                &format!("{equation}  rule [neDouble]: double(I) => I +Int I [non-executable]\n"),
            ),
        )
        .unwrap();
        let (document, status) = run(&dir.join("FLOW.toml"), false);
        assert_eq!(status, EXIT_YES, "{document:#}");
        let rules = rules(&document);
        let listed = rules
            .iter()
            .map(|r| (r["label"].clone(), r["status"].clone()))
            .collect::<Vec<_>>();
        assert_eq!(
            listed,
            [
                (json!(null), json!("fired")),
                (json!("LOOP.neDouble"), json!("no-coverage-signal")),
                (json!("LOOP.spin"), json!("unmatched")),
                (json!("LOOP.countdown"), json!("fired")),
                (json!("LOOP.done"), json!("fired")),
                (json!("LOOP.twice"), json!("fired")),
                (json!("LOOP.unused"), json!("unmatched")),
            ]
        );
        let row = &rules[1];
        assert_eq!(row["obligation"], false);
        assert_eq!(row["covered"], Value::Null);
        assert_eq!(row["start_line"], 20);
        assert_eq!(
            (&row["matched_by"], &row["fired_by"]),
            (&json!([]), &json!([]))
        );
        assert_eq!(
            row["reason"],
            "a non-executable rule: k-rust never runs it, so no program can match it"
        );
        let family = &document["families"]["rules"];
        assert_eq!(
            (&family["obligations"], &family["covered"]),
            (&json!(6), &json!(4))
        );
        assert_eq!(
            family["counts"],
            json!({"fired": 4, "matched": 0, "unmatched": 2, "out_of_scope": 0,
                   "claim_helper": 0, "no_coverage_signal": 1})
        );
    }

    /// KINK-R4: a rule's `fired_by` lists a program only when some path of its run takes the
    /// rule's step (k-rust `committed`). On `pick(0)` the candidates `bad` (`10 /Int 0`) and
    /// `good` share a priority; `bad`'s successor is undefined beside `good`'s, so it is rolled
    /// back: applied (the record's `applied_sentences`), but no path takes it, so `bad` is
    /// reached and not fired, while `good` fires. On `pick(5)` both fire. Before result schema
    /// v6 `fired_by` read `applied` and listed `pick(0)` under `bad`. An equation fires when its
    /// instance gives a result (`half`).
    #[test]
    #[ignore = "kink"]
    fn fired_by_lists_only_programs_a_path_of_which_takes_the_step() {
        let dir = scratch("fired-committed");
        write(
            &dir.join("pick.k"),
            "module PICK-SYNTAX\n  imports INT-SYNTAX\n  syntax Pgm ::= pick(Int)\nendmodule\n\n\
             module PICK\n  imports PICK-SYNTAX\n  imports INT\n  \
             configuration <k> $PGM:Pgm </k> <out> 0 </out>\n  \
             syntax Int ::= half(Int) [function, total]\n  rule half(X) => X /Int 2\n  \
             rule [bad]: <k> pick(N) => .K </k> <out> _ => 10 /Int N </out>\n  \
             rule [good]: <k> pick(N) => .K </k> <out> _ => half(N) </out>\nendmodule\n",
        );
        write(
            &dir.join("FLOW.toml"),
            "[spec]\nentry = \"pick.k\"\nmain_module = \"PICK\"\nsyntax_module = \
             \"PICK-SYNTAX\"\n\n[[program]]\nid = \"zero\"\ntext = \"pick(0)\"\n\n\
             [[program]]\nid = \"five\"\ntext = \"pick(5)\"\n",
        );
        let (document, status) = run(&dir.join("FLOW.toml"), false);
        assert_eq!(status, EXIT_YES, "{document:#}");
        assert_eq!(
            rows(&document),
            expect(&[("zero", "comparable", false), ("five", "comparable", false)])
        );
        let rule = |label: &str| {
            rules(&document)
                .iter()
                .find(|rule| rule["label"] == label)
                .cloned()
                .unwrap_or_else(|| panic!("no rule {label}: {document:#}"))
        };
        let lists = |label: &str| {
            let rule = rule(label);
            (rule["matched_by"].clone(), rule["fired_by"].clone())
        };
        assert_eq!(
            lists("PICK.bad"),
            (json!(["zero", "five"]), json!(["five"]))
        );
        assert_eq!(
            lists("PICK.good"),
            (json!(["zero", "five"]), json!(["zero", "five"]))
        );
        let half = rules(&document)
            .iter()
            .find(|rule| rule["label"].is_null())
            .cloned()
            .unwrap();
        assert_eq!(half["fired_by"], json!(["zero", "five"]), "{half:#}");
        let record = stored_record(&dir.join("FLOW.toml"), &document, "zero");
        let holds = |key: &str, label: &str| {
            record["coverage"][key]
                .as_array()
                .unwrap()
                .iter()
                .any(|sentence| sentence["label"] == label)
        };
        assert!(holds("applied_sentences", "PICK.bad"), "{record:#}");
        assert!(!holds("fired_sentences", "PICK.bad"), "{record:#}");
        assert!(holds("fired_sentences", "PICK.good"), "{record:#}");
    }

    #[test]
    #[ignore = "kink"]
    fn editing_one_program_recomputes_exactly_that_one() {
        let manifest = fixture("calc", "edit-program").join("FLOW.toml");
        let (first, _) = run(&manifest, false);
        let old = record_path(&manifest, &first, "sub");
        write(
            &manifest.parent().unwrap().join("programs/sub.calc"),
            "10 - 4\n",
        );
        let (second, status) = run(&manifest, false);
        assert_eq!(status, EXIT_YES);
        assert_eq!(
            rows(&second),
            expect(&[
                ("add", "comparable", true),
                ("nested", "comparable", true),
                ("sub", "comparable", false),
                ("inline", "comparable", true),
            ])
        );
        let (before, after) = (program_digests(&first), program_digests(&second));
        assert_eq!(before[0], after[0]);
        assert_ne!(before[2], after[2]);
        assert_eq!(spec_hex(&first), spec_hex(&second));
        // The new text has a new record; the old record stays and is not used.
        let new = record_path(&manifest, &second, "sub");
        assert_ne!(new, old);
        assert!(old.is_file() && new.is_file());
        assert_ne!(read_json(&new)["run_sha256"], read_json(&old)["run_sha256"]);
    }

    #[test]
    #[ignore = "kink"]
    fn a_fresh_cache_fills_every_program_and_a_second_run_computes_nothing() {
        for (name, ids) in [
            ("calc", &["add", "nested", "sub", "inline"][..]),
            ("register", &["store", "increment", "double"][..]),
        ] {
            let manifest = fixture(name, &format!("fill-{name}")).join("FLOW.toml");
            let (first, status) = run(&manifest, false);
            assert_eq!(status, EXIT_YES, "{first:#}");
            assert_eq!(first["schema"], "kink-flow-coverage");
            assert_eq!(first["result_schema_version"], RESULT_SCHEMA_VERSION);
            assert_eq!(
                rows(&first),
                ids.iter()
                    .map(|id| ((*id).to_owned(), "comparable".to_owned(), false))
                    .collect::<Vec<_>>()
            );
            for id in ids {
                let record = read_json(&record_path(&manifest, &first, id));
                assert_eq!(record["class"], "comparable");
                assert_eq!(record["program_id"], *id);
                assert_eq!(record["key"]["schema_version"], RESULT_SCHEMA_VERSION);
                assert_eq!(
                    record["key"]["execution"],
                    first["spec"]["execution_digest"]
                );
                assert_eq!(record["spec_digest"], first["spec"]["digest"]);
                assert_eq!(
                    first["spec"]["execution_digest"]["kind"],
                    kink_flow::digest::EXECUTION_DOMAIN
                );
                assert_eq!(
                    first["result_cache"],
                    json!({"enabled": true, "reason": null})
                );
                assert_eq!(
                    record["run_sha256"],
                    run_digest(&record["baseline"]).unwrap().to_string()
                );
                assert_eq!(record["baseline"]["test_id"], *id);
                assert_eq!(record_final_configuration(&record).unwrap().len(), 1);
                // The ends are held once: in the baseline row, not again beside it.
                assert!(record["final_configuration"].is_null(), "{record:#}");
                assert_eq!(record["coverage"]["complete"], true);
            }
            let (second, status) = run(&manifest, false);
            assert_eq!(status, EXIT_YES);
            assert_eq!(
                rows(&second),
                ids.iter()
                    .map(|id| ((*id).to_owned(), "comparable".to_owned(), true))
                    .collect::<Vec<_>>()
            );
            assert_eq!(second["summary"]["computed"], 0);
            let mut uncached = second.clone();
            for program in uncached["programs"].as_array_mut().unwrap() {
                program["cached"] = json!(false);
            }
            uncached["summary"]["computed"] = first["summary"]["computed"].clone();
            // F-12: the first command ran each program's baseline live once; the second ran none.
            assert_eq!(
                first["baseline_runs"],
                json!({"live": ids.len(), "reused": 0, "diagnostic": 0})
            );
            assert_eq!(
                second["baseline_runs"],
                json!({"live": 0, "reused": 0, "diagnostic": 0})
            );
            uncached["baseline_runs"] = first["baseline_runs"].clone();
            assert_eq!(uncached, first);
        }
    }

    #[test]
    #[ignore = "kink"]
    fn rules_are_listed_in_sentence_order_and_each_open_one_is_a_target() {
        let manifest = fixture("loop", "rules").join("FLOW.toml");
        let (document, status) = run(&manifest, false);
        assert_eq!(status, EXIT_YES, "{document:#}");
        let listed = rules(&document)
            .iter()
            .map(|r| {
                (
                    r["label"].as_str().unwrap_or("-").to_owned(),
                    r["file"].as_str().unwrap().to_owned(),
                    r["start_line"].as_u64().unwrap(),
                    r["status"].as_str().unwrap().to_owned(),
                    r["matched_by"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .map(|p| p.as_str().unwrap().to_owned())
                        .collect::<Vec<_>>(),
                )
            })
            .collect::<Vec<_>>();
        let rule = |label: &str, line: u64, status: &str, reached: &[&str]| {
            (
                label.to_owned(),
                "loop.k".to_owned(),
                line,
                status.to_owned(),
                reached.iter().map(|p| (*p).to_owned()).collect::<Vec<_>>(),
            )
        };
        // Re-pin L2-1 (coverage v2): the `double` equation, which `twice` evaluates, is reached and
        // fired like a rewrite rule; before, every equation was `not-observable`.
        assert_eq!(
            listed,
            [
                rule("-", 19, "fired", &["twice"]),
                rule("LOOP.spin", 20, "unmatched", &[]),
                rule("LOOP.countdown", 21, "fired", &["countdown"]),
                rule("LOOP.done", 22, "fired", &["countdown"]),
                rule("LOOP.twice", 23, "fired", &["twice"]),
                rule("LOOP.unused", 24, "unmatched", &[]),
            ]
        );
        assert_eq!(rules(&document)[0]["fired_by"], json!(["twice"]));
        assert!(rules(&document)[0]["reason"].is_null());
        // Each open rule is a target, in sentence order, with its id and position; a rewrite rule's
        // target spells the fuzz job that looks for a program matching it.
        let targets = document["targets"].as_array().unwrap();
        let rule_targets = targets
            .iter()
            .filter(|target| target["family"] == "rules")
            .map(|target| target["item"].as_str().unwrap())
            .collect::<Vec<_>>();
        assert_eq!(rule_targets, ["rule:LOOP.spin", "rule:LOOP.unused"]);
        assert_eq!(
            targets[0]["text"],
            "a case whose run reaches a state that LOOP.spin matches"
        );
        assert_eq!(
            (&targets[0]["file"], &targets[0]["line"]),
            (&json!("loop.k"), &json!(20))
        );
        assert_eq!(
            targets[0]["fuzz"],
            "kink-flow fuzz FLOW.toml TEMPLATES.toml --template ID --matched LOOP.spin"
        );
        assert_eq!(rules(&document)[1]["id"], "rule:LOOP.spin");
        assert_eq!(rules(&document)[1]["covered"], false);
        assert_eq!(rules(&document)[0]["id"], "rule:loop.k:19");
        // The coverage document's first version replaced the results document's version 11; its
        // second builds the syntax family; its third runs the flips family where a front end
        // derives the flips; its fourth has the coverage lock and each flip's recorded killer.
        assert_eq!(document["schema"], "kink-flow-coverage");
        assert_eq!(document["version"], 5);
        // GUIDE-USABILITY 5 (KINK-R4 fix round): every kink-flow document names k-rust's build
        // identity, not the version alone.
        assert_eq!(document["k_rust_revision"], k_rust::build_identity());
        let summary = &document["summary"];
        assert_eq!(
            (
                &summary["programs"],
                &summary["comparable"],
                &summary["computed"],
                &summary["mismatches"],
                &summary["argued"],
            ),
            (&json!(2), &json!(2), &json!(2), &json!(0), &json!(0))
        );
        assert_eq!(
            summary["per_family"]["rules"],
            json!({"obligations": 6, "covered": 4, "argued": 0, "open": 2})
        );
        assert_eq!(
            summary["open"],
            json!(targets.len()),
            "one target per open obligation: {document:#}"
        );
        assert_eq!(document["families"]["rules"]["measure"], json!(4.0 / 6.0));
        // calc: every rule fires, the unlabelled one by `sub` alone.
        let (calc, _) = run(&fixture("calc", "rules-calc").join("FLOW.toml"), false);
        assert_eq!(
            rules(&calc)
                .iter()
                .map(|r| (
                    r["label"].clone(),
                    r["status"].clone(),
                    r["matched_by"].clone()
                ))
                .collect::<Vec<_>>(),
            [
                (
                    json!("CALC.add"),
                    json!("fired"),
                    json!(["add", "nested", "inline"])
                ),
                (
                    json!("CALC.mul"),
                    json!("fired"),
                    json!(["nested", "inline"])
                ),
                (json!(null), json!("fired"), json!(["sub"])),
            ]
        );
    }

    /// CF-45: a claim helper (an equation of a function only claims apply, named by the front end
    /// that sees the claims) that no comparable program matched has status `claim-helper` and
    /// leaves the program-coverage denominator; one that some program fired is `fired`.
    /// The loop fixture's `double` equation, which `twice` reaches, stands in for the matched one,
    /// and `unused` and `spin`, which no program reaches, for unmatched ones. A sentence may write
    /// its label bare or as `MODULE.x`, so the unmatched helpers are named once in each form
    /// (`unused` bare, `LOOP.spin` qualified), and each form must reach the `claim-helper` status;
    /// a name that is no sentence's label changes nothing.
    #[test]
    #[ignore = "kink"]
    fn a_claim_helper_leaves_the_denominator() {
        let dir = fixture("loop", "rules-claim-helper");
        let source = dir.join("loop.k");
        let text = fs::read_to_string(&source).unwrap();
        let equation = "  rule double(I) => I *Int 2\n";
        assert!(text.contains(equation));
        fs::write(
            &source,
            text.replace(equation, "  rule [double]: double(I) => I *Int 2\n"),
        )
        .unwrap();
        let manifest = FlowManifest::read(&dir.join("FLOW.toml"))
            .unwrap()
            .with_claim_helpers([
                ("LOOP".to_owned(), "unused".to_owned()),
                ("LOOP".to_owned(), "LOOP.spin".to_owned()),
                ("LOOP".to_owned(), "LOOP.double".to_owned()),
                ("LOOP".to_owned(), "nothing".to_owned()),
            ]);
        let (mut document, ok) =
            kink_flow::coverage::coverage(&manifest, &CoverageOptions::default());
        kink_flow::coverage::derive(&mut document, &kink_flow::KinkFlowSpelling);
        assert!(ok, "{document:#}");
        let listed = rules(&document)
            .iter()
            .map(|r| {
                (
                    r["label"].clone(),
                    r["status"].clone(),
                    r["matched_by"].clone(),
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(
            listed,
            [
                (json!("LOOP.double"), json!("fired"), json!(["twice"])),
                (json!("LOOP.spin"), json!("claim-helper"), json!([])),
                (
                    json!("LOOP.countdown"),
                    json!("fired"),
                    json!(["countdown"])
                ),
                (json!("LOOP.done"), json!("fired"), json!(["countdown"])),
                (json!("LOOP.twice"), json!("fired"), json!(["twice"])),
                (json!("LOOP.unused"), json!("claim-helper"), json!([])),
            ]
        );
        assert_eq!(
            document["summary"]["per_family"]["rules"],
            json!({"obligations": 4, "covered": 4, "argued": 0, "open": 0})
        );
        assert_eq!(document["families"]["rules"]["counts"]["claim_helper"], 2);
        assert!(
            document["targets"]
                .as_array()
                .unwrap()
                .iter()
                .all(|target| target["family"] != "rules"),
            "{document:#}"
        );
    }

    #[test]
    #[ignore = "kink"]
    fn the_run_digest_depends_on_neither_the_program_id_nor_the_other_tests() {
        for name in ["calc", "register"] {
            let manifest = FlowManifest::read(&flow(name).join("FLOW.toml")).unwrap();
            let admission = admit(&manifest);
            let spec = admission.spec.as_ref().unwrap();
            let mut tests = admission
                .programs
                .iter()
                .map(|p| p.outcome.clone().unwrap())
                .collect::<Vec<_>>();
            let runner = BaselineRunner::new(spec, &manifest).unwrap();
            let alone = tests
                .iter()
                .map(|test| {
                    let result = runner.run(test.clone());
                    assert_eq!(result.class, ResultClass::Comparable);
                    result.run_sha256().unwrap()
                })
                .collect::<Vec<_>>();
            // Under another id, the same program has the same run digest (and another row).
            let mut renamed = tests[0].clone();
            renamed.id = "renamed".into();
            let result = runner.run(renamed);
            assert_eq!(result.baseline.as_ref().unwrap()["test_id"], "renamed");
            assert_eq!(result.run_sha256().unwrap(), alone[0]);
            // Every program in one campaign, in both orders: the same run digests.
            for test in &mut tests {
                test.oracles = fixed_oracles();
            }
            let together = run_together(spec, &manifest, &tests);
            assert_eq!(
                together
                    .iter()
                    .map(|row| run_digest(row).unwrap())
                    .collect::<Vec<_>>(),
                alone
            );
            tests.reverse();
            let reversed = run_together(spec, &manifest, &tests);
            let mut expected = alone.clone();
            expected.reverse();
            assert_eq!(
                reversed
                    .iter()
                    .map(|row| run_digest(row).unwrap())
                    .collect::<Vec<_>>(),
                expected
            );
        }
    }

    #[test]
    #[ignore = "kink"]
    fn admit_spec_admits_programs_one_at_a_time_like_admit() {
        let manifest = FlowManifest::read(&flow("calc").join("FLOW-bad-program.toml")).unwrap();
        let whole = admit(&manifest);
        let (record, admitted) = admit_spec(&manifest);
        assert_eq!(record.text(), whole.record.text());
        let (spec, mut inputs) = admitted.unwrap();
        let mut session = inputs.session(&spec);
        // In reverse order through one session, and so also after the refused `bad` program,
        // each program gives what `admit` gave in manifest order.
        for (program, expected) in manifest.programs.iter().zip(&whole.programs).rev() {
            let outcome = session
                .read(program)
                .and_then(|case| session.test_case(program, &case));
            assert_eq!(outcome, expected.outcome, "{}", program.id);
        }
    }

    /// A comment or layout edit of the specification keeps every record: the result cache is
    /// keyed by the execution digest (the loaded definition without positions), which the edit
    /// keeps, while the specification digest, which names the bytes, changes; the rule rows show
    /// the shifted lines, read from the current load. An edit of a rule recomputes every program
    /// under a new execution directory.
    #[test]
    #[ignore = "kink"]
    fn a_layout_edit_keeps_every_record_and_a_rule_edit_recomputes_every_program() {
        let manifest = fixture("calc", "edit-spec").join("FLOW.toml");
        let calc = manifest.parent().unwrap().join("calc.k");
        let (first, _) = run(&manifest, false);
        append(&calc, "// edited\n");
        let text = fs::read_to_string(&calc).unwrap();
        fs::write(&calc, format!("// a comment at the top\n\n\n{text}")).unwrap();
        let (layout, status) = run(&manifest, false);
        assert_eq!(status, EXIT_YES, "{layout:#}");
        assert_ne!(spec_hex(&first), spec_hex(&layout));
        assert_eq!(
            layout["spec"]["execution_digest"],
            first["spec"]["execution_digest"]
        );
        assert!(
            rows(&layout)
                .iter()
                .all(|(_, class, cached)| class == "comparable" && *cached),
            "{layout:#}"
        );
        assert_eq!(layout["summary"]["computed"], 0);
        let line = |document: &Value| {
            rules(document)
                .iter()
                .find(|rule| rule["label"].as_str().is_some_and(|l| l.ends_with("add")))
                .unwrap_or_else(|| panic!("no rule add in {document:#}"))["start_line"]
                .as_u64()
                .unwrap()
        };
        assert_eq!(line(&layout), line(&first) + 3);
        assert_eq!(rules(&layout).len(), rules(&first).len());
        // A record names the bytes it was written under, outside its key.
        assert_eq!(
            read_json(&record_path(&manifest, &layout, "add"))["spec_digest"],
            first["spec"]["digest"]
        );

        fs::write(
            &calc,
            fs::read_to_string(&calc)
                .unwrap()
                .replace("I1 -Int I2", "I2 -Int I1"),
        )
        .unwrap();
        let (second, status) = run(&manifest, false);
        assert_eq!(status, EXIT_YES);
        assert_ne!(execution_hex(&first), execution_hex(&second));
        assert_eq!(program_digests(&first), program_digests(&second));
        assert!(
            rows(&second)
                .iter()
                .all(|(_, class, cached)| class == "comparable" && !cached)
        );
        let results = manifest
            .parent()
            .unwrap()
            .join(CACHE_DIRECTORY)
            .join("results");
        let mut directories = fs::read_dir(&results)
            .unwrap()
            .map(|e| e.unwrap().file_name().into_string().unwrap())
            .collect::<Vec<_>>();
        directories.sort();
        let mut expected = vec![execution_hex(&first), execution_hex(&second)];
        expected.sort();
        assert_eq!(directories, expected);
    }

    #[test]
    #[ignore = "kink"]
    fn a_record_is_used_only_under_its_own_key() {
        let manifest = fixture("calc", "keys").join("FLOW.toml");
        let (first, _) = run(&manifest, false);
        // Another schema version in a record: recomputed and rewritten, never used.
        let add = record_path(&manifest, &first, "add");
        let mut record = read_json(&add);
        record["key"]["schema_version"] = json!("kink-flow/result/v0");
        fs::write(&add, record.to_string()).unwrap();
        // Another program's record at this program's path.
        let nested = record_path(&manifest, &first, "nested");
        fs::copy(record_path(&manifest, &first, "sub"), &nested).unwrap();
        // A file that is not a record.
        fs::write(record_path(&manifest, &first, "inline"), "not json").unwrap();
        let (second, status) = run(&manifest, false);
        assert_eq!(status, EXIT_YES);
        assert_eq!(
            rows(&second),
            expect(&[
                ("add", "comparable", false),
                ("nested", "comparable", false),
                ("sub", "comparable", true),
                ("inline", "comparable", false),
            ])
        );
        assert_eq!(
            read_json(&add)["key"]["schema_version"],
            RESULT_SCHEMA_VERSION
        );
        assert_eq!(read_json(&nested)["program_id"], "nested");
        // Another time bound: no stored class depends on it (a timeout is never stored), so the
        // key names no `time_ms` and every record stays in use.
        let text = fs::read_to_string(&manifest).unwrap();
        fs::write(&manifest, format!("{text}\n[budget]\ntime_ms = 20000\n")).unwrap();
        let (third, status) = run(&manifest, false);
        assert_eq!(status, EXIT_YES);
        assert!(rows(&third).iter().all(|(_, _, cached)| *cached));
        assert_eq!(spec_hex(&third), spec_hex(&first));
        assert_eq!(program_digests(&third), program_digests(&first));
        let mut budget = json!({"max_depth": 100_000, "max_simplification_iterations": 10_000,
                                "max_breadth": null});
        // Under the Z3 profile the key also names the solver: kink's units, retries and Z3 build.
        if let Some(solver) = kink_native::solver_value(kink_native::BACKEND_OPTIONS) {
            budget["smt"] = solver;
        }
        assert_eq!(read_json(&add)["key"]["budget"], budget);
        // Another depth bound: every program is recomputed under the new key.
        fs::write(
            &manifest,
            format!("{text}\n[budget]\ntime_ms = 20000\nmax_depth = 200000\n"),
        )
        .unwrap();
        let (fourth, status) = run(&manifest, false);
        assert_eq!(status, EXIT_YES);
        assert!(rows(&fourth).iter().all(|(_, _, cached)| !cached));
        assert_eq!(read_json(&add)["key"]["budget"]["max_depth"], 200_000);
        let (fifth, _) = run(&manifest, false);
        assert!(rows(&fifth).iter().all(|(_, _, cached)| *cached));
    }

    /// kink27 R3-UNDEF-BRIDGE fix round 1 (review should-fix 1, finding C-10): an undefined step
    /// taken from a configuration holding a ground two-entry Map with distinct Int keys. Without a
    /// collection axiom the configuration is a terminal value and the run is `comparable`, with no
    /// final configuration. With a simplification rooted at the Map element role symbol, which
    /// k-rust neither applies nor reports, kink does not trust what a collection term denotes:
    /// the configuration has no terminal value, and its existence is not read either, because
    /// k-rust's collection obligations read its builtin collection model, which such an axiom may
    /// contradict. The run stays `unknown`, named by the undefined-step cause. Fails if
    /// `configuration_exists` ignores collection trust, or answers `true` for a configuration it
    /// does not show to exist (the end-to-end pin of that direction; review probe 2).
    #[test]
    #[ignore = "kink"]
    fn an_undefined_step_over_a_map_needs_trusted_collections() {
        let flow = |name: &str, axiom: &str| {
            let dir = scratch(name);
            write(
                &dir.join("mu.k"),
                &format!(
                    "module MU-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= go(Int) [symbol(go)]
endmodule

module MU
  imports MU-SYNTAX
  imports INT
  imports MAP
  syntax KItem ::= step(Int) [symbol(step)]
  configuration <k> $PGM:Pgm </k> <store> .Map </store> <out> 0 </out>
  rule [go]:   <k> go(N) => step(N) </k> <store> _ => (1 |-> 10) (2 |-> 20) </store>
  rule [step]: <k> step(N) => .K </k> <out> _ => N /Int 0 </out>
{axiom}endmodule
"
                ),
            );
            write(
                &dir.join("FLOW.toml"),
                "[spec]\nentry = \"mu.k\"\nmain_module = \"MU\"\nsyntax_module = \"MU-SYNTAX\"\n\n\
                 [[program]]\nid = \"one\"\ntext = \"go(1)\"\n",
            );
            let manifest = dir.join("FLOW.toml");
            let (document, status) = run(&manifest, false);
            // Answered; an unknown program has no answer.
            assert_ne!(status, EXIT_UNASKED, "{document:#}");
            assert_eq!(
                status,
                kink_flow::cli::coverage_status(&document),
                "{document:#}"
            );
            (manifest, document)
        };

        let (manifest, trusted) = flow("undefined-map-trusted", "");
        assert_eq!(rows(&trusted), expect(&[("one", "comparable", false)]));
        let record = stored_record(&manifest, &trusted, "one");
        assert_eq!(
            record_final_configuration(&record),
            Some(Vec::new()),
            "{record:#}"
        );

        let (_, distrusted) = flow(
            "undefined-map-distrusted",
            "  rule [rolesimp]: (7 |-> 7) => (8 |-> 8) [simplification]\n",
        );
        assert_eq!(rows(&distrusted), expect(&[("one", "unknown", false)]));
        let cause = distrusted["programs"][0]["cause"].as_str().unwrap();
        assert!(
            cause.contains(
                "every path ended, but the configuration an undefined step is taken from is not \
                 shown to exist: in the trivial leaf at depth 1, k-rust does not show it defined"
            ) && cause.contains(
                "a collection term of a definition with an axiom rooted at a collection role symbol"
            ),
            "{cause}"
        );
    }

    /// kink27 R3-UNDEF-BRIDGE fix round 1 (review probe 1): the halt of an undefined step on a
    /// ground configuration that is not rigid. `go(1)` writes `g(1)` to `<log>`, with `g` total
    /// and no equation for it, so `g(1)` exists but its value is open. From `step(1)`, `bad` is
    /// undefined on every instance (`1 /Int 0`), and `ok` applies on exactly the instances where
    /// `g(1)` is `1`. An undefined step's leaf may complete only where no rule has a defined
    /// successor on any of its instances, so k-rust must not drop `ok` because `g(1)` is not
    /// syntactically `1`: either it splits on `g(1) == 1`, and the undefined step's leaf carries
    /// that path condition, or it stops undecided. Either way the baseline is never `comparable`
    /// with the empty set of final configurations, and the mutant that makes `bad` defined is not
    /// killed by that empty set.
    #[test]
    #[ignore = "kink"]
    fn an_undefined_step_beside_a_rule_on_an_open_value_keeps_that_rule() {
        let dir = scratch("undefined-open-value");
        write(
            &dir.join("ur.k"),
            "module UR-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= go(Int) [symbol(go)]
endmodule

module UR
  imports UR-SYNTAX
  imports INT
  syntax Int ::= g(Int) [function, total, symbol(g)]
  syntax KItem ::= step(Int) [symbol(step)] | \"done\"
  configuration <k> $PGM:Pgm </k> <log> 0 </log> <out> 0 </out>
  rule [go]:  <k> go(N) => step(N) </k> <log> _ => g(N) </log>
  rule [bad]: <k> step(N) => .K </k> <out> _ => N /Int 0 </out>
  rule [ok]:  <k> step(_) => done </k> <log> 1 </log>
endmodule
",
        );
        let manifest = dir.join("FLOW.toml");
        write(
            &manifest,
            "[spec]\nentry = \"ur.k\"\nmain_module = \"UR\"\nsyntax_module = \"UR-SYNTAX\"\n\n\
             [[program]]\nid = \"one\"\ntext = \"go(1)\"\n",
        );
        let mutations = dir.join("MUTATIONS.toml");
        write(
            &mutations,
            "[[mutation]]\nid = \"bad-defined\"\nmisunderstanding = \"a test mutation\"\n[[mutation.edit]]\nrule = \"UR.bad\"\n\
             find = \"N /Int 0\"\nreplace = \"N\"\n",
        );
        let (document, status) = run(&manifest, false);
        assert_eq!(status, EXIT_UNANSWERED, "{document:#}");
        // At this k-rust pin the run stops `indeterminate` at depth 1, so the row is `unknown`.
        if document["programs"][0]["class"] == "comparable" {
            let record = stored_record(&manifest, &document, "one");
            assert_ne!(
                record_final_configuration(&record),
                Some(Vec::new()),
                "{record:#}"
            );
        }
        let (searched, status) = kink_flow::cli::run(
            &manifest,
            &mutations,
            &kink_flow::search::RunOptions::default(),
        );
        assert_ne!(
            searched["mutations"][0]["status"], "killed",
            "{status} {searched:#}"
        );
    }

    #[test]
    #[ignore = "kink"]
    fn a_ground_map_is_comparable_and_covers_its_rule() {
        let manifest = fixture("map-store", "map").join("FLOW.toml");
        let (document, status) = run(&manifest, false);
        assert_eq!(status, EXIT_YES, "{document:#}");
        assert_eq!(rows(&document), expect(&[("store", "comparable", false)]));
        assert!(document["programs"][0]["cause"].is_null());
        assert_eq!(rules(&document)[0]["status"], "fired");
        assert_eq!(rules(&document)[0]["matched_by"], json!(["store"]));
        let path = record_path(&manifest, &document, "store");
        let mut record = stored_record(&manifest, &document, "store");
        assert_eq!(record["class"], "comparable");
        assert!(record["baseline"].is_object() && record["run_sha256"].is_string());
        let finals = record_final_configuration(&record).unwrap();
        assert_eq!(finals.len(), 1);
        let text = finals[0];
        assert!(
            text.contains("Lbl'UndsPipe'-'-GT-Unds'") && text.contains("\\dv{SortInt{}}(\"2\")"),
            "{text}"
        );
        // Re-pin L2-1 (coverage v2): the run also reaches the prelude's map equations, so the
        // rule is one of the reached sentences rather than the only one.
        let reached = |key: &str| {
            record["coverage"][key]
                .as_array()
                .unwrap()
                .iter()
                .any(|sentence| sentence["label"] == "MAP-STORE.store")
        };
        assert!(
            reached("sentences") && reached("applied_sentences") && reached("fired_sentences"),
            "{record:#}"
        );
        // U1: a v1 record is recomputed, never trusted under the v2 value rule.
        // Re-pin R0b: v4, because the exclusions change what counts as comparable. Re-pin
        // adoption A-1: v5, because a record holds the baseline run's specification diagnostics
        // and undecided solver answers, and k-rust's run-level lists exclude a baseline run.
        // KINK-R4: v6, because a record's coverage holds the fired sentences `fired_by` lists.
        // kink27 R1-UNDEF: v7, because an undefined step's pre-step configuration is no final
        // configuration of a record. kink27 R3-UNDEF-BRIDGE: v8. CF-16: v9, because a
        // comparable record holds its ends' summaries. v10, because the key names the execution
        // digest and the bounds a stored class depends on, and no host-dependent class is
        // stored. v11 (CF-03), because a record holds the readings that excluded its run. v12
        // (v12), because a record holds each end once, as KORE text. v13, because a record of a
        // run with a stop holds how its ends were reached. v14 (CF-33), because a record holds
        // kink's own undecided solver answers and records are written under Z3 too. v15, because
        // a run with a stop condition is keyed by the condition. v16, because a record's coverage
        // holds the guard outcomes. v17, because a record's coverage holds the bindings. v18,
        // because a run with an observation declaration may be a comparable prefix program. v19,
        // because a record's bindings hold the alternatives a fired instance took and only the
        // operand heads of variables the axiom reads.
        assert_eq!(RESULT_SCHEMA_VERSION, "kink-flow/result/v19");
        record["key"]["schema_version"] = json!("kink-flow/result/v1");
        fs::write(&path, record.to_string()).unwrap();
        let (recomputed, status) = run(&manifest, false);
        assert_eq!(status, EXIT_YES);
        assert_eq!(rows(&recomputed), expect(&[("store", "comparable", false)]));
        assert_eq!(
            read_json(&path)["key"]["schema_version"],
            RESULT_SCHEMA_VERSION
        );

        let (searched, status) = kink_flow::cli::run(
            &manifest,
            &manifest.parent().unwrap().join("MUTATIONS.toml"),
            &kink_flow::search::RunOptions::default(),
        );
        assert_eq!(status, EXIT_YES, "{searched:#}");
        assert_eq!(
            searched["counts"],
            json!({
                "killed": 3, "survived": 1, "equivalent": 0, "unkillable": 0, "not-admitted": 0,
                "timeout": 0, "unknown": 0, "error": 0, "invalid-mutation": 0,
            })
        );
        let survivor = searched["mutations"]
            .as_array()
            .unwrap()
            .iter()
            .find(|row| row["status"] == "survived")
            .unwrap();
        assert_eq!(survivor["id"], "update-as-concat");
    }

    /// Packet CACHE-ID (re-pin R0-tail review 1, minor): every record key holds kink's semantics
    /// identity (kink-campaign `identity`), so a record written by a build before CACHE-ID (its key
    /// has no `kink`, as at 1ee9955 through 64b56fa) or under any one other component (another
    /// definition-exclusion version among them) is recomputed and rewritten, never used: each forged
    /// record claims `unknown`, and the row is the live `comparable`. Re-pin L1-2-land: so is one
    /// whose key lacks the one-sided rule's component (`one_sided`, as at 830c18e) or names another
    /// version of it.
    #[test]
    #[ignore = "kink"]
    fn a_record_written_under_another_identity_is_recomputed() {
        let manifest = fixture("calc", "identity").join("FLOW.toml");
        let (first, status) = run(&manifest, false);
        assert_eq!(status, EXIT_YES, "{first:#}");
        let programs = ["add", "nested", "sub", "inline"];
        for id in programs {
            assert_eq!(
                read_json(&record_path(&manifest, &first, id))["key"]["kink"],
                kink_campaign::kink_identity(),
                "{id}"
            );
        }
        // (None, _): the key of a build before CACHE-ID; (Some(key), false): that component changed;
        // (Some("one_sided"), true): the key of a build before the one-sided rule was a component
        // (830c18e, re-pin L1-2-land), which lacks it.
        let forgeries = std::iter::once((None, false))
            .chain(
                kink_campaign::KINK_IDENTITY
                    .iter()
                    .map(|c| (Some(c.key), false)),
            )
            .chain(std::iter::once((Some("one_sided"), true)))
            .collect::<Vec<_>>();
        for round in forgeries.chunks(programs.len()) {
            let forged = programs.iter().zip(round).collect::<Vec<_>>();
            for (id, component) in &forged {
                let path = record_path(&manifest, &first, id);
                let mut record = read_json(&path);
                match component {
                    (None, _) => {
                        record["key"].as_object_mut().unwrap().remove("kink");
                    }
                    (Some(key), true) => {
                        record["key"]["kink"]
                            .as_object_mut()
                            .unwrap()
                            .remove(*key)
                            .unwrap();
                    }
                    (Some(key), false) => {
                        let value = record["key"]["kink"][key].as_str().unwrap().to_owned();
                        record["key"]["kink"][key] = json!(format!("{value}-other"));
                    }
                }
                record["class"] = json!("unknown");
                record["cause"] = json!("forged under another kink identity");
                fs::write(&path, record.to_string()).unwrap();
            }
            let (document, status) = run(&manifest, false);
            assert_eq!(status, EXIT_YES, "{round:?}: {document:#}");
            let recomputed = forged.iter().map(|(id, _)| **id).collect::<Vec<_>>();
            assert_eq!(
                rows(&document),
                programs
                    .iter()
                    .map(|id| (
                        (*id).to_owned(),
                        "comparable".to_owned(),
                        !recomputed.contains(id)
                    ))
                    .collect::<Vec<_>>(),
                "{round:?}"
            );
            for (id, component) in &forged {
                let record = read_json(&record_path(&manifest, &first, id));
                assert_eq!(
                    record["key"]["kink"],
                    kink_campaign::kink_identity(),
                    "{component:?}"
                );
                assert_eq!(record["class"], "comparable", "{component:?}");
            }
        }
    }

    #[test]
    #[ignore = "kink"]
    fn the_binarys_coverage_command() {
        let binary = env!("CARGO_BIN_EXE_kink-flow");
        let dir = fixture("calc", "binary");
        let manifest = dir.join("FLOW.toml");
        let cache = scratch("binary-cache");
        let output = Command::new(binary)
            .args(["coverage", manifest.to_str().unwrap(), "--cache"])
            .arg(&cache)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(i32::from(EXIT_YES)));
        let document: Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(document["summary"]["comparable"], 4);
        assert!(
            cache
                .join("results")
                .join(execution_hex(&document))
                .is_dir()
        );
        assert!(!dir.join(CACHE_DIRECTORY).exists());
        let output = Command::new(binary)
            .args([
                "coverage",
                manifest.to_str().unwrap(),
                "--verify",
                "--cache",
            ])
            .arg(&cache)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(i32::from(EXIT_YES)));
        let document: Value = serde_json::from_slice(&output.stdout).unwrap();
        assert!(rows(&document).iter().all(|(_, _, cached)| *cached));

        // The text rendering: one line per family, then the targets.
        let output = Command::new(binary)
            .args([
                "coverage",
                manifest.to_str().unwrap(),
                "--output",
                "text",
                "--cache",
            ])
            .arg(&cache)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(i32::from(EXIT_YES)));
        let text = String::from_utf8(output.stdout).unwrap();
        assert!(
            text.starts_with("coverage: 0 open, 0 argued; 4 programs, 4 comparable\n"),
            "{text}"
        );
        assert!(text.contains("\nrules: 3 of 3 fired (100.0%)"), "{text}");

        // `--tier 2` asks for the flips too: kink-flow's own front end derives none, so the
        // family does not run, says why, and the document computed tier 1 alone. (A cache of its
        // own leaves the default cache as the commands below expect it.)
        let tier_two_cache = dir.join("tier-two-cache");
        let output = Command::new(binary)
            .args([
                "coverage",
                manifest.to_str().unwrap(),
                "--tier",
                "2",
                "--cache",
                tier_two_cache.to_str().unwrap(),
            ])
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(i32::from(EXIT_YES)));
        let document: Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(document["settings"]["tiers"], json!([1]));
        assert_eq!(document["families"]["flips"]["run"], false);
        assert_eq!(
            document["families"]["flips"]["reason"],
            kink_flow::flips::DERIVES_NONE
        );

        // `results` is no verb: the usage error names the verb that replaced it.
        let output = Command::new(binary)
            .args(["results", manifest.to_str().unwrap()])
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(i32::from(EXIT_UNASKED)));
        assert!(output.stdout.is_empty());
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert!(
            stderr.contains("`results` is no longer a verb: `coverage` replaced it"),
            "{stderr}"
        );

        // A refused program is a corpus error; the others still get their rows.
        let output = Command::new(binary)
            .args([
                "coverage",
                dir.join("FLOW-bad-program.toml").to_str().unwrap(),
            ])
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(i32::from(EXIT_UNASKED)));
        let document: Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(
            rows(&document),
            expect(&[
                ("add", "comparable", false),
                ("bad", "refused", false),
                ("sub", "comparable", false),
            ])
        );
        assert!(
            document["programs"][1]["cause"]
                .as_str()
                .unwrap()
                .starts_with("inputs/parse: ")
        );

        // A manifest that does not decode, and a spec that does not compile.
        let broken = dir.join("broken.toml");
        write(&broken, "[spec]\nentry = \"calc.k\"\n");
        let output = Command::new(binary)
            .args(["coverage", broken.to_str().unwrap()])
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(i32::from(EXIT_UNASKED)));
        let document: Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(document["schema"], "kink-flow-coverage");
        assert_eq!(document["spec"]["stage"], "manifest");
        let (document, status) = run(&flow("compile-error").join("FLOW.toml"), false);
        assert_eq!(status, EXIT_UNASKED);
        assert_eq!(document["spec"]["stage"], "compile");
        assert_eq!(document["programs"], json!([]));

        // Usage errors.
        for args in [
            vec!["coverage"],
            vec![
                "coverage",
                manifest.to_str().unwrap(),
                "--verify",
                "--verify",
            ],
            vec!["coverage", manifest.to_str().unwrap(), "--cache"],
            vec!["coverage", manifest.to_str().unwrap(), "--other"],
            vec!["coverage", manifest.to_str().unwrap(), "--tier", "3"],
            vec!["coverage", manifest.to_str().unwrap(), "--output", "kore"],
            vec![
                "coverage",
                manifest.to_str().unwrap(),
                "--mutations",
                "m.toml",
            ],
            vec!["coverage", dir.join("missing.toml").to_str().unwrap()],
        ] {
            let output = Command::new(binary).args(&args).output().unwrap();
            assert_eq!(
                output.status.code(),
                Some(i32::from(EXIT_UNASKED)),
                "{args:?}"
            );
            assert!(output.stdout.is_empty());
        }
    }

    #[test]
    #[ignore = "kink"]
    fn verify_passes_on_an_untouched_cache_and_fails_after_a_hand_edited_record() {
        let manifest = fixture("calc", "verify").join("FLOW.toml");
        let (first, _) = run(&manifest, false);
        let (verified, status) = run(&manifest, true);
        assert_eq!(status, EXIT_YES, "{verified:#}");
        assert!(
            verified["programs"]
                .as_array()
                .unwrap()
                .iter()
                .all(|p| p["verify"] == "match" && p["cached"] == true)
        );
        assert_eq!(verified["mismatches"], json!([]));

        // A record whose run digest was edited by hand.
        let path = record_path(&manifest, &first, "nested");
        let original = fs::read_to_string(&path).unwrap();
        let mut record: Value = serde_json::from_str(&original).unwrap();
        record["run_sha256"] = json!("0".repeat(64));
        let edited = serde_json::to_string_pretty(&record).unwrap();
        fs::write(&path, &edited).unwrap();
        // Without --verify the record is current (its key is unchanged) and is used as it is.
        let (plain, status) = run(&manifest, false);
        assert_eq!(status, EXIT_YES);
        assert!(rows(&plain).iter().all(|(_, _, cached)| *cached));
        let (verified, status) = run(&manifest, true);
        assert_eq!(status, EXIT_NO);
        let verdicts = verified["programs"]
            .as_array()
            .unwrap()
            .iter()
            .map(|p| (p["id"].as_str().unwrap(), p["verify"].as_str().unwrap()))
            .collect::<Vec<_>>();
        assert_eq!(
            verdicts,
            [
                ("add", "match"),
                ("nested", "mismatch"),
                ("sub", "match"),
                ("inline", "match")
            ]
        );
        let mismatches = verified["mismatches"].as_array().unwrap();
        assert_eq!(mismatches.len(), 2, "{mismatches:#?}");
        assert!(mismatches.iter().all(|m| m["program"] == "nested"
            && m["record"]
                == format!(
                    "results/{}/{}",
                    execution_hex(&first),
                    path.file_name().unwrap().to_str().unwrap()
                )));
        assert!(
            mismatches[0]["detail"]
                .as_str()
                .unwrap()
                .contains("is not the digest of its baseline row")
        );
        assert!(
            mismatches[1]["detail"]
                .as_str()
                .unwrap()
                .starts_with("run_sha256: cached 0000")
        );
        // --verify reports; it never rewrites the record.
        assert_eq!(fs::read_to_string(&path).unwrap(), edited);

        // A record whose baseline row was edited by hand, its digest left alone: the end's KORE
        // text `\dv{SortInt{}}("9")`, a JSON string in the row, made to say 10.
        let mut record: Value = serde_json::from_str(&original).unwrap();
        let row = record["baseline"]
            .to_string()
            .replace(r#"\"9\""#, r#"\"10\""#);
        assert_ne!(row, record["baseline"].to_string());
        record["baseline"] = serde_json::from_str(&row).unwrap();
        fs::write(&path, record.to_string()).unwrap();
        let (verified, status) = run(&manifest, true);
        assert_eq!(status, EXIT_NO);
        let mismatches = verified["mismatches"].as_array().unwrap();
        assert_eq!(mismatches.len(), 1, "{mismatches:#?}");
        assert!(
            mismatches[0]["detail"]
                .as_str()
                .unwrap()
                .contains("is not the digest of its baseline row")
        );

        // Restored, it verifies again.
        fs::write(&path, &original).unwrap();
        assert_eq!(run(&manifest, true).1, EXIT_YES);
    }

    /// Packet CACHE-ID-fix-1 (CACHE-ID review 1 major): every record key holds the build that wrote
    /// it (`kink_build`, the executable's digest), so a record another build wrote is recomputed even
    /// when every semantics-identity component is equal; the code that decides a result class mostly
    /// has no version constant. Forged first: each forged record claims `unknown` under another
    /// build, or under none (the key of a build before CACHE-ID-fix-1), and the row is the live
    /// `comparable`. Then two real builds: the `kink-flow` binary and this test binary write the
    /// same cache in turn, and each recomputes every record the other wrote.
    #[test]
    #[ignore = "kink"]
    fn a_record_written_by_another_build_is_recomputed() {
        let manifest = fixture("calc", "build").join("FLOW.toml");
        let programs = ["add", "nested", "sub", "inline"];
        let this_build = build_of(&std::env::current_exe().unwrap());
        let (first, status) = run(&manifest, false);
        assert_eq!(status, EXIT_YES, "{first:#}");
        for id in programs {
            assert_eq!(
                read_json(&record_path(&manifest, &first, id))["key"]["kink_build"],
                this_build,
                "{id}"
            );
        }
        let other = kink_patch::sha256(b"another kink build").to_string();
        for (forged, build) in [
            (&programs[..2], Some(other.as_str())),
            (&programs[2..], None),
        ] {
            for id in forged {
                let path = record_path(&manifest, &first, id);
                let mut record = read_json(&path);
                match build {
                    Some(build) => record["key"]["kink_build"] = json!(build),
                    None => {
                        record["key"].as_object_mut().unwrap().remove("kink_build");
                    }
                }
                record["class"] = json!("unknown");
                record["cause"] = json!("forged under another kink build");
                fs::write(&path, record.to_string()).unwrap();
            }
            let (document, status) = run(&manifest, false);
            assert_eq!(status, EXIT_YES, "{document:#}");
            assert_eq!(
                rows(&document),
                programs
                    .iter()
                    .map(|id| (
                        (*id).to_owned(),
                        "comparable".to_owned(),
                        !forged.contains(id)
                    ))
                    .collect::<Vec<_>>(),
                "{build:?}"
            );
            for id in forged {
                let record = read_json(&record_path(&manifest, &first, id));
                assert_eq!(record["key"]["kink_build"], this_build, "{build:?}");
                assert_eq!(record["class"], "comparable", "{build:?}");
            }
        }
        // Two real builds share the cache.
        let binary = Path::new(env!("CARGO_BIN_EXE_kink-flow"));
        let binary_build = build_of(binary);
        assert_ne!(binary_build, this_build);
        let results_by_binary = || {
            let output = Command::new(binary)
                .arg("coverage")
                .arg(&manifest)
                .output()
                .unwrap();
            assert_eq!(output.status.code(), Some(i32::from(EXIT_YES)));
            serde_json::from_slice::<Value>(&output.stdout).unwrap()
        };
        let all = |cached: bool| {
            programs
                .iter()
                .map(|id| ((*id).to_owned(), "comparable".to_owned(), cached))
                .collect::<Vec<_>>()
        };
        let by_binary = results_by_binary();
        assert_eq!(rows(&by_binary), all(false));
        for id in programs {
            assert_eq!(
                read_json(&record_path(&manifest, &first, id))["key"]["kink_build"],
                binary_build,
                "{id}"
            );
        }
        assert_eq!(rows(&results_by_binary()), all(true));
        let (by_library, _) = run(&manifest, false);
        assert_eq!(rows(&by_library), all(false));
        assert_eq!(rows(&run(&manifest, false).0), all(true));
        assert_eq!(rows(&results_by_binary()), all(false));
    }

    /// A baseline that times out is not a program's class: its record is never written, its row
    /// says why (`not_cached`), and the next command runs it again, while a comparable program is
    /// cached. Bounded by `[budget] baseline_max_work` instead, the same program is `unknown`, a
    /// function of the key, which names the bound: its record is written and read back, with no
    /// diagnostic run. A bound that does not stop a run is the run without it (countdown's run
    /// digest is the one it has without a bound), and another bound recomputes every program.
    #[test]
    #[ignore = "kink"]
    fn a_timeout_is_rerun_by_the_next_command_and_a_work_bound_is_cached_with_its_bound() {
        let dir = fixture("loop", "timeout-work");
        let timeout = dir.join("FLOW-timeout.toml");
        let (first, status) = run(&timeout, false);
        assert_eq!(status, EXIT_UNANSWERED, "{first:#}");
        assert_eq!(
            rows(&first),
            expect(&[
                ("spin", "timeout", false),
                ("countdown", "comparable", false)
            ])
        );
        let (second, status) = run(&timeout, false);
        assert_eq!(status, EXIT_UNANSWERED, "{second:#}");
        assert_eq!(
            rows(&second),
            expect(&[
                ("spin", "timeout", false),
                ("countdown", "comparable", true)
            ])
        );
        assert_eq!(
            second["baseline_runs"],
            json!({"live": 1, "reused": 0, "diagnostic": 0})
        );
        for document in [&first, &second] {
            let spin = &document["programs"][0];
            assert_eq!(
                spin["not_cached"],
                "timeout: the watchdog stopped the run at time_ms = 500; a timeout depends on the \
                 host's load, so the next command runs this program again",
                "{spin:#}"
            );
            let cause = spin["cause"].as_str().unwrap();
            assert!(
                cause.ends_with(&format!("{TIMEOUT_NOT_CACHED}{TIMEOUT_BOUND_BY_WORK}")),
                "{cause}"
            );
            assert!(document["programs"][1].get("not_cached").is_none());
        }
        assert!(!record_path(&timeout, &first, "spin").exists());
        let countdown = read_json(&record_path(&timeout, &first, "countdown"));
        assert_eq!(countdown["class"], "comparable");
        assert!(countdown["key"]["budget"].get("time_ms").is_none());

        // FLOW-timeout.toml bounded by work, with a time bound far longer than either run. It is
        // written here, not kept beside the fixture: every manifest there is a case of the
        // modality differential, which bounds runs by the manifest's time and depth only.
        let work = dir.join("FLOW-work.toml");
        fs::write(
            &work,
            fs::read_to_string(&timeout).unwrap().replace(
                "time_ms = 500\n",
                "time_ms = 600000\nbaseline_max_work = 20000\n",
            ),
        )
        .unwrap();
        let (bounded, status) = run(&work, false);
        assert_eq!(status, EXIT_UNANSWERED, "{bounded:#}");
        assert_eq!(
            rows(&bounded),
            expect(&[
                ("spin", "unknown", false),
                ("countdown", "comparable", false)
            ])
        );
        assert_eq!(execution_hex(&bounded), execution_hex(&first));
        let spin = &bounded["programs"][0];
        let cause = spin["cause"].as_str().unwrap();
        assert!(
            cause.starts_with("the run reached baseline_max_work = 20000; k-rust returned "),
            "{cause}"
        );
        assert!(spin.get("not_cached").is_none(), "{spin:#}");
        assert_eq!(bounded["baseline_runs"]["diagnostic"], 0);
        let record = read_json(&record_path(&work, &bounded, "spin"));
        assert_eq!(record["class"], "unknown");
        assert_eq!(record["key"]["budget"]["baseline_max_work"], 20000);
        let bounded_countdown = read_json(&record_path(&work, &bounded, "countdown"));
        assert_eq!(
            bounded_countdown["key"]["budget"]["baseline_max_work"],
            20000
        );
        assert_eq!(bounded_countdown["run_sha256"], countdown["run_sha256"]);
        let (again, status) = run(&work, false);
        assert_eq!(status, EXIT_UNANSWERED, "{again:#}");
        assert_eq!(
            rows(&again),
            expect(&[("spin", "unknown", true), ("countdown", "comparable", true)])
        );
        assert_eq!(
            again["baseline_runs"],
            json!({"live": 0, "reused": 0, "diagnostic": 0})
        );
        assert_eq!(again["programs"][0]["cause"], spin["cause"]);
        fs::write(
            &work,
            fs::read_to_string(&work)
                .unwrap()
                .replace("baseline_max_work = 20000", "baseline_max_work = 30000"),
        )
        .unwrap();
        let (other, status) = run(&work, false);
        assert_eq!(status, EXIT_UNANSWERED, "{other:#}");
        assert_eq!(
            rows(&other),
            expect(&[
                ("spin", "unknown", false),
                ("countdown", "comparable", false)
            ])
        );
        assert!(
            other["programs"][0]["cause"]
                .as_str()
                .unwrap()
                .starts_with("the run reached baseline_max_work = 30000; ")
        );
    }

    /// The admitted specification of `manifest`'s digests: the specification digest, the
    /// execution digest and k-rust's KORE execution digest of the compiled definition.
    fn admitted_digests(manifest: &FlowManifest) -> (String, ExecutionDigest, String) {
        let (record, admitted) = admit_spec(manifest);
        let (spec, _) = admitted.unwrap_or_else(|| panic!("{}", record.text()));
        let kore = spec
            .compiled
            .artifacts()
            .execution_digest()
            .unwrap()
            .to_string();
        (
            spec_digest(manifest, &spec.loaded.files).to_string(),
            execution_digest(manifest, &spec),
            kore,
        )
    }

    const MEANING_K: &str = "module T-SYNTAX
  imports INT-SYNTAX
  syntax Exp ::= Int | f(Exp) [symbol(f)] | g(Exp) [symbol(g)]
endmodule

module T-SYNTAX2
  imports T-SYNTAX
endmodule

module T
  imports T-SYNTAX
  imports INT
  configuration <k> $PGM:Exp </k>
  rule [f]: f(I:Int) => I +Int 1
  rule [g]: g(I:Int) => I *Int 2
endmodule

module T2
  imports T
endmodule
";

    const MEANING_FLOW: &str = "[spec]\nentry = \"t.k\"\nmain_module = \"T\"\n\
                                syntax_module = \"T-SYNTAX\"\n\n\
                                [[program]]\nid = \"one\"\ntext = \"f(1)\"\n";

    /// The execution digest names what an execution and kink's judgement of it depend on, and
    /// nothing a layout edit changes: a comment, blank lines and indentation keep it, while a
    /// rule's right-hand side, a rule's attribute or label, the order of two rules, the main
    /// module and the syntax module each change it; an equivalent include list keeps it. On the
    /// compared cells, an `unobservable` declaration changes it while k-rust's KORE execution
    /// digest of the compiled definition stays equal, which is why the key is read at the K
    /// level: the declaration is not emitted to KORE, yet it decides which cells a comparison
    /// reads.
    #[test]
    #[ignore = "kink"]
    fn execution_digest_names_meaning() {
        let dir = scratch("execution-digest-meaning");
        fs::create_dir_all(dir.join("extra")).unwrap();
        let digests = |k: &str, flow: &str| {
            write(&dir.join("t.k"), k);
            admitted_digests(&FlowManifest::decode(flow, &dir).unwrap())
        };
        let (base_spec, base, _) = digests(MEANING_K, MEANING_FLOW);
        assert_eq!(base.kind, kink_flow::digest::EXECUTION_DOMAIN);
        let layout = format!(
            "// a comment at the top\n\n\n{}\n// and one at the end\n",
            MEANING_K.replace("  rule [g]:", "      rule   [g]:")
        );
        let (layout_spec, same, _) = digests(&layout, MEANING_FLOW);
        assert_ne!(layout_spec, base_spec);
        assert_eq!(same, base, "a layout edit changed the execution digest");
        let include =
            MEANING_FLOW.replace("[spec]\n", "[spec]\ninclude_dirs = [\".\", \"extra\"]\n");
        let (include_spec, same, _) = digests(MEANING_K, &include);
        assert_ne!(include_spec, base_spec);
        assert_eq!(
            same, base,
            "an equivalent include list changed the execution digest"
        );
        for (what, k, flow) in [
            (
                "a right-hand side",
                MEANING_K.replace("I +Int 1", "I +Int 2"),
                MEANING_FLOW.to_owned(),
            ),
            (
                "an attribute",
                MEANING_K.replace("I *Int 2\n", "I *Int 2 [owise]\n"),
                MEANING_FLOW.to_owned(),
            ),
            (
                "a label",
                MEANING_K.replace("rule [g]:", "rule [h]:"),
                MEANING_FLOW.to_owned(),
            ),
            (
                "the order of two rules",
                MEANING_K.replace(
                    "  rule [f]: f(I:Int) => I +Int 1\n  rule [g]: g(I:Int) => I *Int 2\n",
                    "  rule [g]: g(I:Int) => I *Int 2\n  rule [f]: f(I:Int) => I +Int 1\n",
                ),
                MEANING_FLOW.to_owned(),
            ),
            (
                "the main module",
                MEANING_K.to_owned(),
                MEANING_FLOW.replace("main_module = \"T\"", "main_module = \"T2\""),
            ),
            (
                "the syntax module",
                MEANING_K.to_owned(),
                MEANING_FLOW.replace(
                    "syntax_module = \"T-SYNTAX\"",
                    "syntax_module = \"T-SYNTAX2\"",
                ),
            ),
        ] {
            assert!(k != MEANING_K || flow != MEANING_FLOW, "{what}: no edit");
            let (_, other, _) = digests(&k, &flow);
            assert_eq!(other.kind, kink_flow::digest::EXECUTION_DOMAIN, "{what}");
            assert_ne!(other, base, "the execution digest does not name {what}");
        }
        // The compared cells: the same definition with and without `unobservable` on <scratch>.
        let unobservable = flow("unobservable");
        let (_, declared, declared_kore) =
            admitted_digests(&FlowManifest::read(&unobservable.join("FLOW.toml")).unwrap());
        let (_, plain, plain_kore) =
            admitted_digests(&FlowManifest::read(&unobservable.join("FLOW-plain.toml")).unwrap());
        assert_eq!(declared_kore, plain_kore);
        assert_ne!(declared, plain);
    }

    /// The execution payload is what `digest::execution_payload` documents, built here member by
    /// member from its inputs; a definition with a sentence that has no fingerprint (a context
    /// alias) falls back to the exact specification digest, kind `kink-flow/spec/v1`, and still
    /// caches every program.
    #[test]
    #[ignore = "kink"]
    fn the_execution_payload_is_built_from_its_inputs_and_falls_back_to_the_bytes() {
        let manifest = FlowManifest::read(&flow("calc").join("FLOW.toml")).unwrap();
        let (record, admitted) = admit_spec(&manifest);
        let (spec, _) = admitted.unwrap_or_else(|| panic!("{}", record.text()));
        let mut prefixes = k_rust::kompile::CompileOptions::default().builtin_source_prefixes;
        prefixes.extend(
            spec.compiled
                .compile_options()
                .builtin_source_prefixes
                .clone(),
        );
        prefixes.sort();
        prefixes.dedup();
        let definition = spec.loaded.baseline.definition();
        let value = definition_value(definition, &prefixes).unwrap();
        assert_eq!(value["main_module"], definition.main_module);
        let modules = value["modules"].as_array().unwrap();
        assert_eq!(modules.len(), definition.modules.len());
        for (module, stored) in definition.modules.iter().zip(modules) {
            let sentences = stored["sentences"].as_array().unwrap();
            assert_eq!(
                sentences.len(),
                module.local_sentences.len(),
                "{}",
                module.name
            );
            for (sentence, stored) in module.local_sentences.iter().zip(sentences) {
                let attributes = sentence.attributes();
                assert_eq!(
                    stored,
                    &json!({
                        "fingerprint": kink_patch::SentenceFingerprint::of(sentence)
                            .unwrap()
                            .to_string(),
                        "located": attributes.location().is_some(),
                        "builtin_source": attributes.source().filter(|source| {
                            prefixes.iter().any(|p| source.starts_with(p.as_str()))
                        }),
                    })
                );
            }
        }
        // Some sentences of a loaded definition are builtin, some authored.
        let sources = modules
            .iter()
            .flat_map(|module| module["sentences"].as_array().unwrap())
            .map(|sentence| sentence["builtin_source"].is_string())
            .collect::<std::collections::BTreeSet<_>>();
        assert_eq!(sources, [false, true].into());
        assert_eq!(
            execution_payload(&manifest, &spec).unwrap(),
            json!({
                "k_rust_revision": K_RUST_REVISION,
                "profile": SolverProfile::BUILD.name(),
                "main_module": "CALC",
                "syntax_module": "CALC-SYNTAX",
                "definition": value,
            })
        );
        let digest = execution_digest(&manifest, &spec);
        assert_eq!(
            digest.digest,
            kink_patch::payload_digest(
                kink_flow::digest::EXECUTION_DOMAIN,
                kink_patch::canonical_json(&execution_payload(&manifest, &spec).unwrap())
                    .as_bytes()
            )
        );

        // A context alias has no fingerprint: the digest is the exact specification digest.
        let manifest = fixture("calc", "context-alias").join("FLOW.toml");
        let calc = manifest.parent().unwrap().join("calc.k");
        fs::write(
            &calc,
            fs::read_to_string(&calc).unwrap().replace(
                "  rule I1:Int - I2:Int => I1 -Int I2\n",
                "  rule I1:Int - I2:Int => I1 -Int I2\n  context alias [c]: <k> HERE ... </k>\n",
            ),
        )
        .unwrap();
        let (first, status) = run(&manifest, false);
        assert_eq!(status, EXIT_YES, "{first:#}");
        assert_eq!(
            first["spec"]["execution_digest"],
            json!({"kind": "kink-flow/spec/v1", "digest": first["spec"]["digest"]})
        );
        // The fallback only costs misses: the second command reads every record.
        let (second, status) = run(&manifest, false);
        assert_eq!(status, EXIT_YES, "{second:#}");
        assert!(
            rows(&second)
                .iter()
                .all(|(_, class, cached)| class == "comparable" && *cached)
        );
    }

    /// The result cache is on in both profiles: under Z3 every solver query of a command is
    /// bounded by Z3 resource units, so a class is a function of a key that names the units and
    /// the Z3 build (`budget.smt`). A record holds both undecided-answer counts, a row repeats
    /// them, and a second command reads every record and computes nothing.
    #[test]
    #[ignore = "kink"]
    fn the_result_cache_is_on_in_both_profiles() {
        let manifest = fixture("calc", "z3-on").join("FLOW.toml");
        let (first, status) = run(&manifest, false);
        assert_eq!(status, EXIT_YES, "{first:#}");
        assert_eq!(
            first["result_cache"],
            json!({"enabled": true, "reason": null})
        );
        for program in first["programs"].as_array().unwrap() {
            let id = program["id"].as_str().unwrap();
            let record = stored_record(&manifest, &first, id);
            for count in ["smt_unknowns", "decider_smt_unknowns"] {
                assert!(record[count].is_u64(), "{id}: {record:#}");
                assert_eq!(program[count], record[count], "{id}");
            }
            assert_eq!(
                record["key"]["budget"].get("smt").is_some(),
                SolverProfile::BUILD == SolverProfile::Z3,
                "{id}: {record:#}"
            );
        }
        let (second, _) = run(&manifest, false);
        assert!(
            rows(&second)
                .iter()
                .all(|(_, class, cached)| class == "comparable" && *cached)
        );
        assert_eq!(second["summary"]["computed"], 0);
    }
}

/// The result store is refused exactly for a solver the clock bounds under the Z3 profile,
/// whose answers depend on the host's load ([`kink_flow::results::RESULT_CACHE_Z3`]); kink's
/// own budget is resource-bounded and keeps it on.
#[test]
fn the_result_store_is_off_only_for_a_clock_bounded_solver_under_z3() {
    let resource = kink_native::BACKEND_OPTIONS;
    let clock = k_rust::backend::BackendOptions {
        smt_resource_limit: None,
        ..resource
    };
    let off = |solver| kink_flow::results::result_store(solver).err();
    assert_ne!(off(resource), Some(kink_flow::results::RESULT_CACHE_Z3));
    assert_eq!(
        off(clock) == Some(kink_flow::results::RESULT_CACHE_Z3),
        SolverProfile::BUILD == SolverProfile::Z3 && kink_native::solver_named().is_ok()
    );
}
