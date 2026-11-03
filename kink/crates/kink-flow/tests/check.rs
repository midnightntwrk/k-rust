//! Admission and `kink-flow check` (flow F-02 deliverables 3, 4 and 6).

use kink_flow::{
    FlowManifest,
    admit::{FlowAdmission, admit},
    cli::{CheckOptions, EXIT_CORPUS, EXIT_OK, EXIT_USAGE, check, check_with},
    mutation::InvalidReason,
};
use kink_patch::sha256;
use serde_json::Value;
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

fn admit_manifest(path: &Path) -> FlowAdmission {
    admit(&FlowManifest::read(path).unwrap())
}

/// A fresh directory for one test, under the target's temporary directory.
fn scratch(name: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-check-{}", std::process::id()))
        .join(name);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
}

fn write(path: &Path, text: &str) {
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, text).unwrap();
}

#[track_caller]
fn outcomes(admission: &FlowAdmission) -> Vec<(String, Option<(String, String)>)> {
    admission
        .programs
        .iter()
        .map(|p| {
            (
                p.id.clone(),
                p.outcome
                    .as_ref()
                    .err()
                    .map(|r| (r.stage.clone(), r.reason.clone())),
            )
        })
        .collect()
}

#[track_caller]
fn spec_refusal(admission: &FlowAdmission) -> (String, String, String) {
    let refusal = admission.record.refusal.as_ref().expect("a refused spec");
    assert!(admission.spec.is_none() && admission.programs.is_empty());
    (
        refusal.stage.clone(),
        refusal.reason.clone(),
        refusal.detail.clone(),
    )
}

fn ok(ids: &[&str]) -> Vec<(String, Option<(String, String)>)> {
    ids.iter().map(|id| ((*id).to_owned(), None)).collect()
}

const CALC_K: &str = include_str!("../../../testdata/flow/calc/calc.k");

#[test]
fn calc_is_admitted_with_every_program_ok_and_the_document_is_exact() {
    let manifest = flow("calc/FLOW.toml");
    let (document, status) = check(&manifest);
    assert_eq!(status, EXIT_OK, "{document:#}");
    let keys = |v: &Value| v.as_object().unwrap().keys().cloned().collect::<Vec<_>>();
    assert_eq!(
        keys(&document),
        [
            "coverage",
            "data",
            "k_rust_revision",
            "mutation_list",
            "mutations",
            "profile",
            "programs",
            "result",
            "schema",
            "spec",
            "version"
        ]
    );
    // Nothing is left out: the second slot is the whole term, over calc's one cell.
    assert_eq!(
        document["result"],
        serde_json::json!({
            "slots": ["exit-stop", "whole-term"],
            "compared": ["k"],
            "not_compared": [],
            "unobservable": [],
        })
    );
    assert_eq!(document["schema"], "kink-flow-check");
    assert_eq!(document["version"], 5);
    // Without --mutations no list is checked.
    for key in ["mutation_list", "mutations", "coverage"] {
        assert!(document[key].is_null(), "{key}");
    }
    // GUIDE-USABILITY 5 (KINK-R4 fix round): k-rust's build identity, its version and a digest
    // of its sources, not the version alone.
    assert_eq!(document["k_rust_revision"], k_rust::build_identity());
    assert_eq!(
        document["profile"],
        kink_native::execution::SolverProfile::BUILD.name()
    );
    assert_eq!(
        keys(&document["spec"]),
        [
            "baseline_findings",
            "detail",
            "exclusion",
            "files",
            "outcome",
            "reason",
            "stage"
        ]
    );
    // calc's full critical-pair check has no finding: its baseline has data.
    assert!(document["spec"]["baseline_findings"].is_null());
    assert_eq!(
        document["data"],
        serde_json::json!({"assume_joined": [], "has_data": true, "incomplete": null, "findings": []})
    );
    assert_eq!(document["spec"]["outcome"], "admitted");
    assert!(document["spec"]["stage"].is_null() && document["spec"]["reason"].is_null());
    assert!(
        document["spec"]["exclusion"].is_null(),
        "calc has no exclusion"
    );
    assert_eq!(
        document["spec"]["files"],
        serde_json::json!([{"name": "calc.k", "sha256": sha256(CALC_K.as_bytes()).to_string()}])
    );
    let programs = document["programs"].as_array().unwrap();
    assert_eq!(
        programs
            .iter()
            .map(|p| (p["id"].as_str().unwrap(), p["outcome"].as_str().unwrap()))
            .collect::<Vec<_>>(),
        [
            ("add", "ok"),
            ("nested", "ok"),
            ("sub", "ok"),
            ("inline", "ok")
        ]
    );
    assert_eq!(
        keys(&programs[0]),
        ["detail", "id", "outcome", "reason", "stage"]
    );
    let text = document.to_string();
    let home = std::env::var("HOME").unwrap_or_else(|_| "/home".into());
    assert!(!text.contains(&home), "no absolute path in the document");
}

#[test]
fn register_is_admitted_with_every_program_ok() {
    let admission = admit_manifest(&flow("register/FLOW.toml"));
    assert!(
        admission.record.refusal.is_none(),
        "{}",
        admission.record.text()
    );
    assert_eq!(outcomes(&admission), ok(&["store", "increment", "double"]));
    assert!(admission.all_admitted());
    let spec = admission.spec.as_ref().unwrap();
    assert_eq!(
        spec.loaded
            .files
            .iter()
            .map(|f| f.name.as_str())
            .collect::<Vec<_>>(),
        ["register.k"]
    );
    // Each admitted program is a concrete initial configuration named by its id.
    for program in &admission.programs {
        let test = program.outcome.as_ref().unwrap();
        assert_eq!(test.id, program.id);
        assert!(test.initial_state.free_variables().is_empty());
        assert!(test.oracles.is_empty());
    }
}

#[test]
fn a_program_that_does_not_parse_is_refused_alone() {
    let manifest = flow("calc/FLOW-bad-program.toml");
    let admission = admit_manifest(&manifest);
    assert!(admission.record.refusal.is_none());
    assert_eq!(
        outcomes(&admission),
        [
            ("add".to_owned(), None),
            ("bad".to_owned(), Some(("inputs".into(), "parse".into()))),
            ("sub".to_owned(), None),
        ]
    );
    assert!(!admission.all_admitted());
    let (document, status) = check(&manifest);
    assert_eq!(status, EXIT_CORPUS);
    assert_eq!(document["spec"]["outcome"], "admitted");
    let bad = &document["programs"][1];
    assert_eq!(
        (&bad["id"], &bad["outcome"], &bad["stage"], &bad["reason"]),
        (
            &Value::from("bad"),
            &Value::from("refused"),
            &Value::from("inputs"),
            &Value::from("parse")
        )
    );
    assert!(
        bad["detail"].as_str().unwrap().contains("Parse error"),
        "{bad}"
    );
}

#[test]
fn a_spec_that_does_not_compile_is_refused_at_the_compile_stage() {
    let admission = admit_manifest(&flow("compile-error/FLOW.toml"));
    let (stage, reason, detail) = spec_refusal(&admission);
    assert_eq!(
        (stage.as_str(), reason.as_str()),
        ("compile", "compile-error")
    );
    assert!(detail.contains("hooked sort Bool"), "{detail}");
    // The load ran, so the files read are recorded; the program was never parsed.
    assert_eq!(admission.record.files.len(), 1);
    assert!(admission.record.kompile_warnings.is_none());
    let (document, status) = check(&flow("compile-error/FLOW.toml"));
    assert_eq!(status, EXIT_CORPUS);
    assert_eq!(document["spec"]["stage"], "compile");
    assert_eq!(document["programs"], serde_json::json!([]));
}

#[test]
fn load_and_program_file_errors_name_the_file_relatively() {
    let dir = scratch("load");
    write(
        &dir.join("FLOW.toml"),
        "[spec]\nentry = \"missing.k\"\nmain_module = \"CALC\"\n",
    );
    let (stage, reason, detail) = spec_refusal(&admit_manifest(&dir.join("FLOW.toml")));
    assert_eq!((stage.as_str(), reason.as_str()), ("load", "load-error"));
    assert!(detail.contains("missing.k"), "{detail}");
    assert!(!detail.contains(dir.to_str().unwrap()), "{detail}");

    write(&dir.join("calc.k"), CALC_K);
    write(&dir.join("programs/one.calc"), "1 + 1\n");
    write(&dir.join("outside.calc"), "2 + 2\n");
    std::os::unix::fs::symlink(dir.join("outside.calc"), dir.join("programs/link.calc")).unwrap();
    let elsewhere = scratch("load-elsewhere");
    write(&elsewhere.join("far.calc"), "3\n");
    std::os::unix::fs::symlink(elsewhere.join("far.calc"), dir.join("programs/far.calc")).unwrap();
    write(
        &dir.join("FLOW.toml"),
        r#"[spec]
entry = "calc.k"
main_module = "CALC"
syntax_module = "CALC-SYNTAX"

[[program]]
id = "absent"
file = "programs/absent.calc"

[[program]]
id = "one"
file = "programs/one.calc"

[[program]]
id = "link-inside"
file = "programs/link.calc"

[[program]]
id = "link-outside"
file = "programs/far.calc"
"#,
    );
    let admission = admit_manifest(&dir.join("FLOW.toml"));
    assert_eq!(
        outcomes(&admission),
        [
            (
                "absent".to_owned(),
                Some(("load".into(), "load-error".into()))
            ),
            ("one".to_owned(), None),
            ("link-inside".to_owned(), None),
            (
                "link-outside".to_owned(),
                Some(("load".into(), "load-error".into()))
            ),
        ]
    );
    let details = admission
        .programs
        .iter()
        .filter_map(|p| p.outcome.as_ref().err().map(|r| r.detail.clone()))
        .collect::<Vec<_>>();
    assert!(details[0].contains("programs/absent.calc"), "{details:?}");
    assert!(
        details[1].contains("escapes the manifest's directory"),
        "{details:?}"
    );
    assert!(details.iter().all(|d| !d.contains(dir.to_str().unwrap())));
}

#[test]
fn start_sorts_and_configuration_variables_reach_input_assembly() {
    let dir = scratch("variables");
    write(
        &dir.join("vars.k"),
        "module VARS\n  imports BOOL\n  imports INT\n  imports BASIC-K\n  configuration <k> $PGM:K </k> <n> $N:Int </n>\n  rule true => false\nendmodule\n",
    );
    write(&dir.join("calc.k"), CALC_K);
    write(
        &dir.join("FLOW.toml"),
        r#"[spec]
entry = "vars.k"
main_module = "VARS"

[[program]]
id = "bound"
text = "true"
variables = { N = "42" }

[[program]]
id = "unbound"
text = "true"

[[program]]
id = "ill-sorted"
text = "true"
variables = { N = "true" }
"#,
    );
    let admission = admit_manifest(&dir.join("FLOW.toml"));
    assert!(
        admission.record.refusal.is_none(),
        "{}",
        admission.record.text()
    );
    assert_eq!(
        outcomes(&admission),
        [
            ("bound".to_owned(), None),
            (
                "unbound".to_owned(),
                Some(("inputs".into(), "assemble".into()))
            ),
            (
                "ill-sorted".to_owned(),
                Some(("inputs".into(), "parse".into()))
            ),
        ]
    );

    write(
        &dir.join("CALC.toml"),
        r#"[spec]
entry = "calc.k"
main_module = "CALC"
syntax_module = "CALC-SYNTAX"

[[program]]
id = "as-exp"
text = "1 + 2"
start_sort = "Exp"

[[program]]
id = "as-int"
text = "1 + 2"
start_sort = "Int"
"#,
    );
    let admission = admit_manifest(&dir.join("CALC.toml"));
    assert_eq!(
        outcomes(&admission),
        [
            ("as-exp".to_owned(), None),
            ("as-int".to_owned(), Some(("inputs".into(), "parse".into()))),
        ]
    );
}

#[test]
fn below_floor_paths_are_refused_for_the_entry_and_every_loaded_file() {
    // The entry lies inside a below-floor conformance case directory.
    let dir = scratch("excluded").join("k-distribution/tests/regression-new/let-test/flow");
    write(&dir.join("calc.k"), CALC_K);
    write(
        &dir.join("FLOW.toml"),
        "[spec]\nentry = \"calc.k\"\nmain_module = \"CALC\"\nsyntax_module = \"CALC-SYNTAX\"\n",
    );
    let admission = admit_manifest(&dir.join("FLOW.toml"));
    let (stage, reason, detail) = spec_refusal(&admission);
    assert_eq!(
        (stage.as_str(), reason.as_str()),
        ("refused-case", "below-floor")
    );
    assert_eq!(
        detail,
        kink_corpus::admission::BELOW_FLOOR_CITATION,
        "the corpus manifest's citation"
    );
    assert!(admission.record.files.is_empty(), "refused before the load");

    // Reached only through a link: the resolved path is checked too.
    let alias = scratch("excluded-alias");
    std::os::unix::fs::symlink(&dir, alias.join("spec")).unwrap();
    let (stage, ..) = spec_refusal(&admit_manifest(&alias.join("spec/FLOW.toml")));
    assert_eq!(stage, "refused-case");

    // The entry is clean but requires a file inside a below-floor case directory.
    let dir = scratch("excluded-include");
    write(
        &dir.join("main.k"),
        "requires \"lib.k\"\nmodule MAIN\n  imports LIB\n  configuration <k> $PGM:K </k>\nendmodule\n",
    );
    write(
        &dir.join("vendor/k-distribution/tests/regression-new/checks/inner/lib.k"),
        "module LIB\n  imports BOOL\n  rule true => false\nendmodule\n",
    );
    write(
        &dir.join("FLOW.toml"),
        "[spec]\nentry = \"main.k\"\nmain_module = \"MAIN\"\ninclude_dirs = [\"vendor/k-distribution/tests/regression-new/checks/inner\"]\n",
    );
    let admission = admit_manifest(&dir.join("FLOW.toml"));
    let (stage, reason, _) = spec_refusal(&admission);
    assert_eq!(
        (stage.as_str(), reason.as_str()),
        ("refused-case", "below-floor")
    );
    assert_eq!(
        admission
            .record
            .files
            .iter()
            .map(|f| f.name.as_str())
            .collect::<Vec<_>>(),
        [
            "main.k",
            "vendor/k-distribution/tests/regression-new/checks/inner/lib.k"
        ]
    );
}

/// The programs of one admitted specification share one input grammar and one assembler
/// (`InputSession`): the grammar is built once, on the first program a session assembles, and
/// not at all by a session that assembles none; each program's test case is the one a fresh
/// assembly of the same program gives.
#[test]
fn programs_share_one_input_grammar() {
    let manifest = FlowManifest::read(&flow("calc/FLOW.toml")).unwrap();
    let (_, admitted) = kink_flow::admit_spec(&manifest);
    let (spec, mut inputs) = admitted.expect("calc is admitted");
    let programs = &manifest.programs[..3];
    let builds = kink_corpus::input::input_grammar_builds;

    let before = builds();
    let idle = inputs.session(&spec);
    for program in programs {
        idle.read(program).unwrap();
    }
    drop(idle);
    assert_eq!(builds(), before, "a session that assembles no program");

    let mut session = inputs.session(&spec);
    let shared = programs
        .iter()
        .map(|program| {
            let case = session.read(program).unwrap();
            (session.test_case(program, &case), case)
        })
        .collect::<Vec<_>>();
    assert_eq!(
        builds(),
        before + 1,
        "one grammar for {} programs",
        programs.len()
    );

    for (program, (test, case)) in programs.iter().zip(shared) {
        let test = test.unwrap_or_else(|refusal| panic!("{}: {refusal:?}", program.id));
        let fresh = kink_corpus::assemble_input_with(
            &spec.loaded,
            Some(&spec.compiled),
            &kink_corpus::TestInputSpec {
                program: case.text.map(kink_corpus::ProgramSource::Text),
                start_sort: program.start_sort.clone(),
                variables: program
                    .variables
                    .iter()
                    .map(|(name, text)| (name.clone(), text.as_str().into()))
                    .collect(),
            },
        )
        .unwrap();
        assert_eq!(test.id, program.id);
        assert!(test.oracles.is_empty());
        assert_eq!(test.initial_state, fresh, "{}", program.id);
    }
}

/// Program inputs keep the input grammar of the specification admitted beside them, so they open
/// a session only on that specification (or a clone of it): a session on the specification of
/// another admission, even of the same manifest, is refused before any program is assembled.
#[test]
fn a_session_takes_only_the_specification_admitted_beside_its_inputs() {
    let manifest = FlowManifest::read(&flow("calc/FLOW.toml")).unwrap();
    let (spec, mut inputs) = kink_flow::admit_spec(&manifest)
        .1
        .expect("calc is admitted");
    let clone = spec.clone();
    drop(inputs.session(&clone));
    let (other, _) = kink_flow::admit_spec(&manifest)
        .1
        .expect("calc is admitted");
    let refused = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        drop(inputs.session(&other));
    }))
    .expect_err("a session on another admission's specification");
    let message = refused
        .downcast_ref::<String>()
        .map(String::as_str)
        .unwrap_or_default();
    assert!(
        message.contains("the specification is not the one these inputs were admitted with"),
        "{message}"
    );
}

fn binary(args: &[&std::ffi::OsStr]) -> (Option<i32>, String, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_kink-flow"))
        .args(args)
        .output()
        .unwrap();
    (
        output.status.code(),
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

/// fz26 FZ-REPLAY-WHOLE (final review N6): `--version` prints the build and k-rust's identity
/// and exits 0, as `krust-fuzz --version` does, instead of the usage.
#[test]
fn the_version_flag_names_the_builds() {
    let (code, stdout, stderr) = binary(&["--version".as_ref()]);
    assert_eq!(code, Some(EXIT_OK.into()), "{stderr}");
    assert_eq!(
        stdout,
        format!(
            "kink-flow {} (k-rust {})\n",
            env!("CARGO_PKG_VERSION"),
            k_rust::build_identity()
        )
    );
}

// ---------------------------------------------------------------------------------------
// CF-18: `check --mutations`, the resolve-only check of a mutation list.

/// A copy of calc whose corpus is the one program `1 + 2` (it applies `add`, never `mul`).
fn calc_copy(name: &str) -> PathBuf {
    let dir = scratch(name);
    write(&dir.join("calc.k"), CALC_K);
    write(
        &dir.join("FLOW.toml"),
        "[spec]\nentry = \"calc.k\"\nmain_module = \"CALC\"\nsyntax_module = \"CALC-SYNTAX\"\n\n\
         [[program]]\nid = \"add\"\ntext = \"1 + 2\"\n",
    );
    dir
}

fn one_edit(id: &str, edit: &str) -> String {
    format!(
        "[[mutation]]\nid = \"{id}\"\nmisunderstanding = \"{id}\"\n\n  [[mutation.edit]]\n{edit}\n"
    )
}

fn check_list(manifest: &Path, mutations: &Path, cache: Option<&Path>) -> (Value, u8) {
    check_with(
        manifest,
        &CheckOptions {
            mutations: Some(mutations.to_owned()),
            cache: cache.map(Path::to_path_buf),
        },
    )
}

#[track_caller]
fn row<'d>(document: &'d Value, id: &str) -> &'d Value {
    document["mutations"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["id"] == id)
        .unwrap_or_else(|| panic!("{id}: {document:#}"))
}

#[track_caller]
fn reasons(findings: &Value) -> Vec<&str> {
    findings
        .as_array()
        .unwrap()
        .iter()
        .map(|finding| finding["reason"].as_str().unwrap())
        .collect()
}

const ARITH: &str = "  rule = \"add\"\n  find = \"I1 +Int I2\"\n  replace = \"I1 -Int I2\"";

#[test]
fn check_resolves_every_mutation_and_runs_no_program() {
    let dir = calc_copy("check-mutations");
    let manifest = dir.join("FLOW.toml");
    let mutations = dir.join("mutations");
    write(
        &mutations.join("arith.toml"),
        &[
            one_edit("add-becomes-sub", ARITH),
            one_edit(
                "sub-by-line",
                "  line = 23\n  find = \"I1 -Int I2\"\n  replace = \"I2 -Int I1\"",
            ),
            one_edit(
                "mul-by-text",
                "  find = \"I1 *Int I2\"\n  replace = \"I1 +Int I2\"",
            ),
        ]
        .concat(),
    );
    write(
        &mutations.join("stale.toml"),
        &[
            one_edit(
                "renamed",
                "  rule = \"div\"\n  find = \"/Int\"\n  replace = \"*Int\"",
            ),
            one_edit(
                "no-op",
                "  rule = \"add\"\n  find = \"I1 +Int I2\"\n  replace = \"I1 +Int I2\"",
            ),
            format!(
                "{}  [[mutation.edit]]\n  rule = \"add\"\n  find = \"+Int I2\"\n  replace = \"-Int I2\"\n",
                one_edit(
                    "overlapping",
                    "  rule = \"add\"\n  find = \"I1 +Int\"\n  replace = \"I2 +Int\"",
                )
            ),
            one_edit(
                "syntax",
                "  line = 9\n  find = \"*\"\n  replace = \"x\"",
            ),
            one_edit(
                "no-op-by-line",
                "  line = 21\n  find = \"I1 +Int I2\"\n  replace = \"I1 +Int I2\"",
            ),
        ]
        .concat(),
    );
    let (document, status) = check_list(&manifest, &mutations, None);
    assert_eq!(status, EXIT_CORPUS, "{document:#}");
    assert_eq!(document["version"], 5);
    assert_eq!(document["spec"]["outcome"], "admitted");
    assert_eq!(document["mutation_list"]["outcome"], "ok");
    // Nothing ran and nothing was written: no cache, so no unreached-rule warning.
    assert!(!dir.join(".kink-flow").exists());
    assert_eq!(document["coverage"]["decides"], false);
    assert_eq!(
        document["coverage"]["without_record"],
        serde_json::json!(["add"])
    );
    assert_eq!(
        document["mutations"]
            .as_array()
            .unwrap()
            .iter()
            .map(|row| (
                row["id"].as_str().unwrap(),
                row["outcome"].as_str().unwrap()
            ))
            .collect::<Vec<_>>(),
        [
            ("arith/add-becomes-sub", "ok"),
            ("arith/sub-by-line", "ok"),
            ("arith/mul-by-text", "ok"),
            ("stale/renamed", "refused"),
            ("stale/no-op", "refused"),
            ("stale/overlapping", "refused"),
            ("stale/syntax", "refused"),
            ("stale/no-op-by-line", "refused"),
        ]
    );

    // A resolving mutation: each edited rule's before and after, label, file and lines.
    let ok = row(&document, "arith/add-becomes-sub");
    assert_eq!(ok["misunderstanding"], "add-becomes-sub");
    assert!(ok["digest"].is_string());
    let rule = &ok["rules"][0];
    assert_eq!(
        (&rule["label"], &rule["file"], &rule["start_line"]),
        (
            &Value::from("CALC.add"),
            &Value::from("calc.k"),
            &Value::from(21)
        )
    );
    assert_eq!(rule["before"], "rule [add]: I1:Int + I2:Int => I1 +Int I2");
    assert_eq!(rule["after"], "rule [add]: I1:Int + I2:Int => I1 -Int I2");
    assert_eq!(ok["refusals"], serde_json::json!([]));
    assert_eq!(ok["warnings"], serde_json::json!([]));

    // Anchors that do not name the rule are warned about, with the label to use when it has one.
    let by_line = row(&document, "arith/sub-by-line");
    assert_eq!(reasons(&by_line["warnings"]), ["line-anchor"]);
    assert!(
        by_line["warnings"][0]["next"]
            .as_str()
            .unwrap()
            .contains("give the rule a label")
    );
    let by_text = row(&document, "arith/mul-by-text");
    assert_eq!(reasons(&by_text["warnings"]), ["text-anchor"]);
    assert_eq!(
        by_text["warnings"][0]["next"],
        "address the rule by its label: rule = \"CALC.mul\""
    );

    // Refusals carry the reason, the edit and the next step.
    for (id, reason, edit) in [
        ("stale/renamed", InvalidReason::UnknownLabel, 0),
        ("stale/no-op", InvalidReason::NoChange, 0),
        ("stale/overlapping", InvalidReason::OverlappingEdits, 1),
        ("stale/syntax", InvalidReason::NonRuleSentence, 0),
        ("stale/no-op-by-line", InvalidReason::NoChange, 0),
    ] {
        let refused = row(&document, id);
        assert_eq!(reasons(&refused["refusals"]), [reason.as_str()], "{id}");
        assert_eq!(refused["refusals"][0]["edit"], edit, "{id}");
        assert_eq!(refused["refusals"][0]["next"], reason.next_step(), "{id}");
        assert!(
            refused["rules"].is_null() && refused["digest"].is_null(),
            "{id}"
        );
    }

    // The anchor warning of a refused mutation names the rule its edit is addressed to.
    let refused_by_line = row(&document, "stale/no-op-by-line");
    assert_eq!(reasons(&refused_by_line["warnings"]), ["line-anchor"]);
    assert_eq!(
        refused_by_line["warnings"][0]["next"],
        "address the rule by its label: rule = \"CALC.add\""
    );
    assert_eq!(refused_by_line["warnings"][0]["rule"]["module"], "CALC");

    // A list with no refusal passes, warnings and all; a single file keeps its ids as written.
    let (document, status) = check_list(&manifest, &mutations.join("arith.toml"), None);
    assert_eq!(status, EXIT_OK, "{document:#}");
    assert_eq!(row(&document, "add-becomes-sub")["outcome"], "ok");

    // A list that does not decode is refused, with the specification still admitted.
    write(&dir.join("BAD.toml"), "[[mutation]]\nid = \"m\"\n");
    let (document, status) = check_list(&manifest, &dir.join("BAD.toml"), None);
    assert_eq!(status, EXIT_CORPUS);
    assert_eq!(document["mutation_list"]["outcome"], "refused");
    assert!(document["mutations"].is_null());
}

#[test]
fn the_binary_checks_a_mutations_directory() {
    let dir = calc_copy("check-binary");
    let manifest = dir.join("FLOW.toml");
    write(
        &dir.join("mutations/arith.toml"),
        &one_edit("add-becomes-sub", ARITH),
    );
    let (code, stdout, stderr) = binary(&[
        "check".as_ref(),
        manifest.as_os_str(),
        "--mutations".as_ref(),
        dir.join("mutations").as_os_str(),
    ]);
    assert_eq!(code, Some(EXIT_OK.into()), "{stderr}");
    let document: Value = serde_json::from_str(&stdout).unwrap();
    assert_eq!(row(&document, "arith/add-becomes-sub")["outcome"], "ok");
    for args in [
        vec![
            "check".as_ref(),
            manifest.as_os_str(),
            "--mutations".as_ref(),
        ],
        vec![
            "check".as_ref(),
            manifest.as_os_str(),
            "--mutations".as_ref(),
            dir.join("missing").as_os_str(),
        ],
    ] {
        let (code, _, stderr) = binary(&args);
        assert_eq!(code, Some(EXIT_USAGE.into()), "{args:?}: {stderr}");
    }
}

// ---------------------------------------------------------------------------------------
// CF-02: definition exclusions at admission, their cause chains, and `check`'s rule that it
// fails when a program cannot be judged on the baseline.

const SCFETCH_K: &str = include_str!("../../../testdata/k/r0c/scfetch.k");

/// The 1-based line of `scfetch.k` that holds `text`.
fn scfetch_line(text: &str) -> u64 {
    SCFETCH_K
        .lines()
        .position(|line| line.contains(text))
        .map(|index| index as u64 + 1)
        .unwrap_or_else(|| panic!("scfetch.k holds {text:?}"))
}

/// SM83's shape at a state that still depends on the short-circuit reading (kink-native's
/// fixture `r0c/scfetch.k`): the rules `fetch` and `fetch-halt-bug` apply `decode`, whose
/// condition skips a `bitRangeInt` operand below `andThenBool` under `notBool`. Two programs.
fn scfetch_flow(name: &str) -> PathBuf {
    let dir = scratch(name);
    write(&dir.join("scfetch.k"), SCFETCH_K);
    write(
        &dir.join("FLOW.toml"),
        "[spec]\nentry = \"scfetch.k\"\nmain_module = \"SCFETCH\"\nsyntax_module = \
         \"SCFETCH-SYNTAX\"\n\n[[program]]\nid = \"fetch\"\ntext = \"# fetch\"\n\n\
         [[program]]\nid = \"again\"\ntext = \"# fetch\"\n",
    );
    dir
}

/// A definition with no exclusion of its own whose programs `g1` and `g0` apply `g`, a total
/// function whose value depends on whether `orBool` skips an operand that may be undefined
/// (`1 /Int X`), which no rule applies; the program `plain` does not apply it. k-rust evaluates
/// every operand, so `g(0)` is undefined and its run contradicts `g`'s `total` claim.
fn initial_state_flow(name: &str) -> PathBuf {
    let dir = scratch(name);
    write(
        &dir.join("sc.k"),
        "module SC-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Pgm ::= run(Bool) [symbol(run)]
  syntax Bool ::= g(Int) [function, total, symbol(g)]
endmodule

module SC
  imports SC-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Pgm </k> <out> false </out>
  rule g(X) => true orBool (1 /Int X ==Int 1)
  rule [run]: <k> run(B) => .K </k> <out> _ => B </out>
endmodule
",
    );
    write(
        &dir.join("FLOW.toml"),
        "[spec]\nentry = \"sc.k\"\nmain_module = \"SC\"\nsyntax_module = \"SC-SYNTAX\"\n\n\
         [[program]]\nid = \"g1\"\ntext = \"run(g(1))\"\n\n\
         [[program]]\nid = \"g0\"\ntext = \"run(g(0))\"\n\n\
         [[program]]\nid = \"plain\"\ntext = \"run(true)\"\n",
    );
    dir
}

fn on_stack<T: Send + 'static>(body: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(kink_corpus::cli::DEFINITION_STACK_BYTES)
        .spawn(body)
        .unwrap()
        .join()
        .unwrap()
}

/// The cause in `exclusion` of the rule labelled `label`.
#[track_caller]
fn cause_of<'e>(exclusion: &'e Value, label: &str) -> &'e Value {
    exclusion["causes"]
        .as_array()
        .unwrap()
        .iter()
        .find(|cause| cause["rule"]["label"] == label)
        .unwrap_or_else(|| panic!("{label}: {exclusion:#}"))
}

/// `check` on SM83's shape: admission computes the definition exclusion and admits the
/// specification and both programs, `spec.exclusion` names, for each of `fetch` and
/// `fetch-halt-bug`, the rule, `decode` with the equation and the part of it through which it
/// depends on the reading, `andThenBool` and the `bitRangeInt` operand, each with its module,
/// position and compiled id, and every program is `excluded` at stage `definition`, so `check`
/// exits 1, with and without `--mutations`.
#[test]
fn a_definition_exclusion_names_its_cause_chain_and_fails_check() {
    let dir = scfetch_flow("scfetch");
    let manifest = dir.join("FLOW.toml");
    let (admission, (document, status)) = {
        let manifest = manifest.clone();
        on_stack(move || (admit_manifest(&manifest), check(&manifest)))
    };
    assert!(admission.all_admitted(), "{}", admission.record.text());
    assert!(!admission.all_judgeable());
    assert_eq!(
        admission
            .spec
            .as_ref()
            .unwrap()
            .exclusions
            .static_exclusion(),
        Some(kink_native::exclusion::Exclusion::ShortCircuitReading)
    );
    assert_eq!(status, EXIT_CORPUS, "{document:#}");
    assert_eq!(document["version"], 5);
    assert_eq!(document["spec"]["outcome"], "admitted");
    for program in document["programs"].as_array().unwrap() {
        assert_eq!(
            (&program["outcome"], &program["stage"], &program["reason"]),
            (
                &Value::from("excluded"),
                &Value::from("definition"),
                &Value::from("short-circuit-reading")
            ),
            "{program:#}"
        );
        assert!(
            program["detail"]
                .as_str()
                .unwrap()
                .contains("spec.exclusion"),
            "{program:#}"
        );
    }
    let exclusion = &document["spec"]["exclusion"];
    assert_eq!(
        exclusion["exclusion"], "short-circuit-reading",
        "{exclusion:#}"
    );
    assert_eq!(
        exclusion["causes"].as_array().unwrap().len(),
        2,
        "{exclusion:#}"
    );
    let detail = exclusion["detail"].as_str().unwrap();
    for (label, text) in [
        ("SCFETCH.fetch", "rule [fetch]:"),
        ("SCFETCH.fetch-halt-bug", "rule [fetch-halt-bug]:"),
    ] {
        let cause = cause_of(exclusion, label);
        let rule = &cause["rule"];
        assert_eq!(rule["module"], "SCFETCH");
        assert_eq!(rule["source"], "scfetch.k", "{rule:#}");
        assert_eq!(
            rule["location"]["start_line"],
            scfetch_line(text),
            "{rule:#}"
        );
        assert_eq!(rule["id"].as_str().unwrap().len(), 64, "{rule:#}");
        assert_eq!(cause["effect"], "applicability");
        assert_eq!(cause["part"], serde_json::json!({"part": "right-side"}));
        let links = cause["links"].as_array().unwrap();
        assert_eq!(links.len(), 2, "{cause:#}");
        let (function, operator) = (&links[0], &links[1]);
        assert_eq!(function["link"], "function");
        assert_eq!(function["function"]["id"], "Lbldecode");
        assert_eq!(
            function["function"]["location"]["start_line"],
            scfetch_line("syntax Instr ::= decode"),
        );
        assert_eq!(function["dependence"], "valued");
        let equation = &function["equation"];
        assert_eq!(equation["label"], "SCFETCH.decode-inc", "{equation:#}");
        assert_eq!(equation["source"], "scfetch.k");
        assert_eq!(
            equation["location"]["start_line"],
            scfetch_line("rule [decode-inc]")
        );
        assert_eq!(equation["id"].as_str().unwrap().len(), 64);
        assert_eq!(function["part"]["part"], "condition");
        assert_eq!(operator["link"], "operator");
        assert_eq!(operator["operator"]["hook"], "BOOL.andThen");
        assert!(!operator["operator"]["location"].is_null(), "{operator:#}");
        assert_eq!(operator["position"], 1);
        assert_eq!(operator["operand"]["rendering"], "k", "{operator:#}");
        assert_eq!(
            operator["operand"]["text"],
            "bitRangeInt ( Op:Int , Off:Int , 2 ) ==Int 0"
        );
        assert_eq!(
            operator["term"]["text"],
            "bitRangeInt ( Op:Int , Off:Int , 2 )"
        );
        assert_eq!(operator["term_symbol"]["hook"], "INT.bitRange");
        // The text names the same chain, with positions.
        let line = scfetch_line(text);
        assert!(
            detail.contains(&format!("rule {label} (scfetch.k:{line}:")),
            "{detail}"
        );
    }
    for part in [
        "which applies decode (declared at scfetch.k:",
        "through its equation SCFETCH.decode-inc (scfetch.k:",
        "which applies _andThenBool_ (BOOL.andThen, declared at ",
        "over its operand 1 `bitRangeInt ( Op:Int , Off:Int , 2 ) ==Int 0`",
        "where `bitRangeInt ( Op:Int , Off:Int , 2 )` (bitRangeInt",
    ] {
        assert!(detail.contains(part), "{part:?} in {detail}");
    }

    // With a mutation list that resolves, the rule is the same.
    write(
        &dir.join("MUTATIONS.toml"),
        &one_edit(
            "unknown-op",
            "  rule = \"decode-unknown\"\n  find = \"unknown(Op)\"\n  replace = \"inc(Op)\"",
        ),
    );
    let (document, status) = {
        let mutations = dir.join("MUTATIONS.toml");
        on_stack(move || check_list(&manifest, &mutations, None))
    };
    assert_eq!(status, EXIT_CORPUS, "{document:#}");
    assert_eq!(
        row(&document, "unknown-op")["outcome"],
        "ok",
        "{document:#}"
    );
    assert_eq!(
        document["spec"]["exclusion"]["exclusion"],
        "short-circuit-reading"
    );
}

/// A program whose initial configuration applies a function whose value depends on the
/// short-circuit reading is `excluded` at stage `initial-state`, alone: the definition has no
/// exclusion, the program that does not apply it is `ok`, and `check` exits 1.
#[test]
fn a_program_whose_initial_configuration_is_excluded_fails_check_alone() {
    let manifest = initial_state_flow("initial-state").join("FLOW.toml");
    let (admission, (document, status)) =
        on_stack(move || (admit_manifest(&manifest), check(&manifest)));
    assert!(admission.all_admitted(), "{}", admission.record.text());
    assert!(!admission.all_judgeable());
    assert_eq!(
        admission
            .programs
            .iter()
            .map(|p| (
                p.id.as_str(),
                p.exclusion.map(|e| (e.exclusion.name(), e.scope.name()))
            ))
            .collect::<Vec<_>>(),
        [
            ("g1", Some(("short-circuit-reading", "initial-state"))),
            ("g0", Some(("short-circuit-reading", "initial-state"))),
            ("plain", None)
        ]
    );
    assert_eq!(status, EXIT_CORPUS, "{document:#}");
    assert!(document["spec"]["exclusion"].is_null(), "{document:#}");
    let g1 = &document["programs"][0];
    assert_eq!(
        (&g1["outcome"], &g1["stage"], &g1["reason"]),
        (
            &Value::from("excluded"),
            &Value::from("initial-state"),
            &Value::from("short-circuit-reading")
        ),
        "{g1:#}"
    );
    assert!(
        g1["detail"]
            .as_str()
            .unwrap()
            .contains("initial configuration"),
        "{g1:#}"
    );
    assert_eq!(document["programs"][2]["outcome"], "ok");
}

/// A definition without `$PGM`: its cases bind `$ENTRY`, `$N` and `$ROM` by name. `inverse` has
/// no value at 0 (`1 /Int 0` has none); `onlyZero` is a partial function whose only equation is
/// at 0, so the definition does not say whether it has a value elsewhere.
const CASES_K: &str = "module CASES
  imports INT
  imports BOOL
  imports BYTES
  imports BASIC-K
  syntax KItem ::= \"go\" [symbol(go)]
  syntax Int ::= onlyZero(Int) [function, symbol(onlyZero)]
  rule onlyZero(0) => 0
  syntax Int ::= inverse(Int) [function, symbol(inverse)]
  rule inverse(X) => 1 /Int X
  configuration <k> $ENTRY:K </k> <n> $N:Int </n> <rom> $ROM:Bytes </rom> <out> 0 </out>
  rule [go]: <k> go => .K ... </k> <n> N </n> <rom> R </rom> <out> _ => N +Int lengthBytes(R) </out>
endmodule
";

/// A test front end's decoder of typed inputs: an input's K name is its name in upper case; an
/// integer is an Int, `{"$file" = path}` the file's bytes and `{"$hex" = digits}` the bytes the
/// digits spell (both a Bytes token), and `{"$call" = {label, args}}` the application of the
/// label to Int arguments; `{"$chain" = [first, second]}` is the bytes of the file `second`
/// names relative to `first`. Any other document is refused.
struct TestDecoder;

fn bytes_token(bytes: &[u8]) -> k_rust::kast::Term {
    let escaped = bytes
        .iter()
        .map(|b| format!("\\x{b:02x}"))
        .collect::<String>();
    k_rust::kast::Term::Token {
        token: format!("b\"{escaped}\""),
        sort: k_rust::kast::Sort::new("Bytes"),
    }
}

fn int_token(value: i64) -> k_rust::kast::Term {
    k_rust::kast::Term::Token {
        token: value.to_string(),
        sort: k_rust::kast::Sort::new("Int"),
    }
}

impl kink_flow::InputDecoder for TestDecoder {
    fn decode(
        &self,
        name: &str,
        document: &toml::Value,
        files: &mut dyn kink_flow::InputFiles,
    ) -> Result<(String, k_rust::kast::Term), String> {
        let term = match document {
            toml::Value::Integer(value) => int_token(*value),
            toml::Value::Table(form) if form.len() == 1 => {
                let (tag, value) = form.iter().next().unwrap();
                match (tag.as_str(), value) {
                    ("$file", toml::Value::String(path)) => bytes_token(&files.read(None, path)?.1),
                    // The second file, named relative to the first.
                    ("$chain", toml::Value::Array(paths)) => {
                        let (first, _) = files.read(None, paths[0].as_str().unwrap())?;
                        bytes_token(&files.read(Some(&first), paths[1].as_str().unwrap())?.1)
                    }
                    ("$hex", toml::Value::String(digits)) => bytes_token(
                        &(0..digits.len())
                            .step_by(2)
                            .map(|i| u8::from_str_radix(&digits[i..i + 2], 16).unwrap())
                            .collect::<Vec<_>>(),
                    ),
                    ("$call", toml::Value::Table(call)) => k_rust::kast::Term::Apply {
                        label: k_rust::kast::Label::new(call["label"].as_str().unwrap()),
                        arguments: call["args"]
                            .as_array()
                            .unwrap()
                            .iter()
                            .map(|arg| int_token(arg.as_integer().unwrap()))
                            .collect(),
                    },
                    _ => return Err(format!("no reading of the form {tag}")),
                }
            }
            _ => return Err("the declared type does not decide this document".into()),
        };
        Ok((name.to_uppercase(), term))
    }
}

/// The scratch flow of `CASES_K` with `programs` and the binary file `rom.bin` (bytes 00 ff).
fn cases_flow(name: &str, programs: &str) -> PathBuf {
    let dir = scratch(name);
    write(&dir.join("cases.k"), CASES_K);
    fs::write(dir.join("rom.bin"), [0x00, 0xff]).unwrap();
    write(
        &dir.join("FLOW.toml"),
        &format!("[spec]\nentry = \"cases.k\"\nmain_module = \"CASES\"\n{programs}"),
    );
    dir
}

#[track_caller]
fn refusal_detail(admission: &FlowAdmission, id: &str) -> String {
    let program = admission.programs.iter().find(|p| p.id == id).unwrap();
    program.outcome.as_ref().unwrap_err().detail.clone()
}

/// A case of a definition without `$PGM` binds every configuration variable by name, with no
/// program text. A program text there would bind nothing, so it is refused (`stray-program`),
/// naming `$PGM` and every variable with its sort. A K-level manifest has no decoder of typed
/// inputs, so a program with `inputs` is refused (`typed-inputs`). A case whose initial
/// configuration has no value on the baseline is refused (`initial-undefined`): an input that
/// divides by zero, directly or through a function. An input whose definedness the definition
/// leaves open (`onlyZero(1)`, outside its only equation) is no such case: it is admitted, and
/// its run reports what it finds.
#[test]
fn a_case_binds_every_variable_by_name_without_a_program() {
    let dir = cases_flow(
        "program-less",
        r#"
[[program]]
id = "bare"
variables = { ENTRY = "go", N = "1", ROM = 'b"\x00\xff"' }

[[program]]
id = "stray"
text = "go"
variables = { N = "1", ROM = 'b""' }

[[program]]
id = "typed"
variables = { ENTRY = "go", N = "1" }
inputs = { rom = { "$file" = "rom.bin" } }

[[program]]
id = "undefined"
variables = { ENTRY = "go", N = "1 /Int 0", ROM = 'b""' }

[[program]]
id = "inverse"
variables = { ENTRY = "go", N = "inverse(0)", ROM = 'b""' }

[[program]]
id = "partial"
variables = { ENTRY = "go", N = "onlyZero(1)", ROM = 'b""' }

[[program]]
id = "defined"
variables = { ENTRY = "go", N = "onlyZero(0)", ROM = 'b""' }
"#,
    );
    let manifest = dir.join("FLOW.toml");
    let admission = on_stack(move || admit_manifest(&manifest));
    assert!(
        admission.record.refusal.is_none(),
        "{}",
        admission.record.text()
    );
    let refused = |stage: &str, reason: &str| Some((stage.to_owned(), reason.to_owned()));
    assert_eq!(
        outcomes(&admission),
        [
            ("bare".to_owned(), None),
            ("stray".to_owned(), refused("inputs", "stray-program")),
            ("typed".to_owned(), refused("inputs", "typed-inputs")),
            (
                "undefined".to_owned(),
                refused("inputs", "initial-undefined")
            ),
            ("inverse".to_owned(), refused("inputs", "initial-undefined")),
            ("partial".to_owned(), None),
            ("defined".to_owned(), None),
        ]
    );
    assert_eq!(
        refusal_detail(&admission, "stray"),
        "the definition declares no $PGM, so a program text binds nothing; bind its \
         configuration variables by name: $ENTRY:K, $N:Int, $ROM:Bytes"
    );
    assert_eq!(
        refusal_detail(&admission, "typed"),
        "typed inputs are read by the front end that knows the inputs' declared types (the krs \
         front end, `krs kink`); at the K level bind K text under `variables`"
    );
    assert_eq!(
        refusal_detail(&admission, "undefined"),
        "the initial configuration has no value on the baseline: some input's value is undefined \
         (it applies an operator or a function outside its domain), so the specification \
         computes no start from this case and the case has no expected result; its inputs: \
         $ENTRY = `go`, $N = `1 /Int 0`, $ROM = `b\"\"`"
    );
}

/// A definition whose rule `stepz` gives `$N` no value one step after a start that has one, and
/// whose rule `spin` counts forever through distinct states.
const LATER_K: &str = "module LATER
  imports INT
  imports BASIC-K
  syntax KItem ::= \"stepz\" [symbol(stepz)] | \"spin\" [symbol(spin)]
  configuration <k> $ENTRY:K </k> <n> $N:Int </n>
  rule [stepz]: <k> stepz => .K ... </k> <n> N => N /Int 0 </n>
  rule [spin]: <k> spin ... </k> <n> N => N +Int 1 </n>
endmodule
";

/// The value check reads the start alone: it runs the baseline to depth 0 and no further. A
/// case whose start has a value and whose first step has none is admitted, since that step is
/// the program's behavior, which its run reports as an undefined step (`Trivial`, not the
/// `Vacuous` leaf of a start with no value). A case whose start has no value is refused, naming
/// its inputs. A program that never ends is admitted at once, under a `time_ms` far longer than
/// the test takes, which a check that ran the program further would spend.
#[test]
fn the_value_check_reads_the_start_alone() {
    let dir = scratch("later-undefined");
    write(&dir.join("later.k"), LATER_K);
    write(
        &dir.join("FLOW.toml"),
        r#"[spec]
entry = "later.k"
main_module = "LATER"

[budget]
time_ms = 600000

[[program]]
id = "later"
variables = { ENTRY = "stepz", N = "1" }

[[program]]
id = "start"
variables = { ENTRY = "stepz", N = "1 /Int 0" }

[[program]]
id = "spin"
variables = { ENTRY = "spin", N = "0" }
"#,
    );
    let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
    let (admission, halts, elapsed) = on_stack(move || {
        let started = std::time::Instant::now();
        let admission = admit(&manifest);
        let elapsed = started.elapsed();
        let (_, admitted) = kink_flow::admit_spec(&manifest);
        let (spec, _) = admitted.unwrap();
        let kore =
            k_rust::kore::parser::parse_definition(&spec.compiled.artifacts().definition_kore)
                .unwrap();
        let mut backend = k_rust::backend::Backend::from_definition(
            kore,
            k_rust::kast::identifier::encode("LATER"),
            k_rust::backend::BackendOptions::default(),
        )
        .unwrap();
        let initial = admission.programs[0]
            .outcome
            .as_ref()
            .unwrap()
            .initial_state
            .clone();
        let adapter = kink_native::execution::ExecutionAdapter::new(
            kink_native::execution::SolverProfile::of(&backend),
        );
        let run = adapter
            .execute(
                &mut backend,
                &initial,
                kink_native::execution::ExecutionBudget {
                    time: std::time::Duration::from_secs(10),
                    max_simplification_iterations: kink_flow::results::SIMPLIFICATION_ITERATIONS,
                    max_depth: None,
                    max_breadth: None,
                },
            )
            .unwrap();
        let halts = run
            .leaves()
            .iter()
            .map(|leaf| format!("{:?}", leaf.halt))
            .collect::<Vec<_>>();
        (admission, halts, elapsed)
    });
    let refused = |stage: &str, reason: &str| Some((stage.to_owned(), reason.to_owned()));
    assert_eq!(
        outcomes(&admission),
        [
            ("later".to_owned(), None),
            ("start".to_owned(), refused("inputs", "initial-undefined")),
            ("spin".to_owned(), None),
        ]
    );
    assert!(
        elapsed < std::time::Duration::from_secs(300),
        "admission took {elapsed:?}"
    );
    assert!(
        refusal_detail(&admission, "start")
            .ends_with("its inputs: $ENTRY = `stepz`, $N = `1 /Int 0`"),
        "{}",
        refusal_detail(&admission, "start")
    );
    // The run from the admitted start has no defined end: its first step is undefined.
    assert_eq!(halts, ["Trivial"], "{halts:?}");
}

/// A program on `$PGM` from a typed input, which kink binds as a program built without the
/// parser: it gives the configuration its text gives. A variable bound twice is refused before
/// assembly (`input-value`): `$PGM` by an input and the program text, or one variable by two
/// inputs (the test decoder names `n` and `N` both `$N`).
const PGM_K: &str = "module PGMCASE
  imports INT
  imports BASIC-K
  syntax Pgm ::= run(Int) [symbol(run)]
  configuration <k> $PGM:Pgm </k> <n> $N:Int </n>
  rule [go]: <k> run(X) => .K </k> <n> _ => X </n>
endmodule
";

#[test]
fn a_typed_input_binds_pgm_once() {
    let dir = scratch("typed-pgm");
    write(&dir.join("pgm.k"), PGM_K);
    write(
        &dir.join("FLOW.toml"),
        r#"[spec]
entry = "pgm.k"
main_module = "PGMCASE"

[[program]]
id = "text"
text = "run(1)"
variables = { N = "0" }

[[program]]
id = "typed"
variables = { N = "0" }
inputs = { pgm = { "$call" = { label = "run", args = [1] } } }

[[program]]
id = "both"
text = "run(1)"
variables = { N = "0" }
inputs = { pgm = { "$call" = { label = "run", args = [1] } } }

[[program]]
id = "two"
text = "run(1)"
inputs = { n = 1, N = 2 }
"#,
    );
    let manifest = FlowManifest::read(&dir.join("FLOW.toml"))
        .unwrap()
        .with_input_decoder(std::sync::Arc::new(TestDecoder));
    let admission = on_stack(move || admit(&manifest));
    let refused = |stage: &str, reason: &str| Some((stage.to_owned(), reason.to_owned()));
    assert_eq!(
        outcomes(&admission),
        [
            ("text".to_owned(), None),
            ("typed".to_owned(), None),
            ("both".to_owned(), refused("inputs", "input-value")),
            ("two".to_owned(), refused("inputs", "input-value")),
        ]
    );
    let initial = |id: &str| {
        let program = admission.programs.iter().find(|p| p.id == id).unwrap();
        program.outcome.as_ref().unwrap().initial_state.clone()
    };
    assert_eq!(initial("typed"), initial("text"));
    assert_eq!(
        refusal_detail(&admission, "both"),
        "input `pgm` binds $PGM, which the program text binds too; bind it once"
    );
    // The inputs are named in the manifest table's order.
    let two = refusal_detail(&admission, "two");
    assert!(
        [
            "inputs `N` and `n` both bind $N; bind it once",
            "inputs `n` and `N` both bind $N; bind it once"
        ]
        .contains(&two.as_str()),
        "{two}"
    );
}

/// A file a typed input names is read as a program file is: relative to the manifest's
/// directory, or to the file it is named from; resolved by the operating system, so
/// `deep/../b.bin` through the link `deep` (to `sub/inner`) is `sub/b.bin`; and refused when it
/// is absolute or resolves outside the manifest's directory, by `..` or through a link.
#[cfg(unix)]
#[test]
fn input_files_stay_inside_the_manifest_directory() {
    let programs = |name: &str| -> String {
        let program = |id: &str, rom: &str| {
            format!(
                "\n[[program]]\nid = \"{id}\"\nvariables = {{ ENTRY = \"go\", N = \"1\" }}\n\
                 inputs = {{ rom = {rom} }}\n"
            )
        };
        let outside = format!("{name}-outside.bin");
        [
            program("hex", r#"{ "$hex" = "02" }"#),
            program("chain", r#"{ "$chain" = ["sub/a.bin", "b.bin"] }"#),
            program("through-link", r#"{ "$file" = "deep/../b.bin" }"#),
            program("absolute", "{ \"$file\" = \"/rom.bin\" }"),
            program("parent", &format!("{{ \"$file\" = \"../{outside}\" }}")),
            program(
                "link-escape",
                &format!("{{ \"$file\" = \"escape/{outside}\" }}"),
            ),
            program(
                "chain-escape",
                &format!("{{ \"$chain\" = [\"sub/a.bin\", \"../../{outside}\"] }}"),
            ),
        ]
        .concat()
    };
    let name = "input-files";
    let dir = cases_flow(name, &programs(name));
    let parent = dir.parent().unwrap();
    fs::write(parent.join(format!("{name}-outside.bin")), [0x03]).unwrap();
    fs::create_dir_all(dir.join("sub/inner")).unwrap();
    fs::write(dir.join("sub/a.bin"), [0x01]).unwrap();
    fs::write(dir.join("sub/b.bin"), [0x02]).unwrap();
    std::os::unix::fs::symlink(dir.join("sub/inner"), dir.join("deep")).unwrap();
    std::os::unix::fs::symlink(parent, dir.join("escape")).unwrap();
    let manifest = FlowManifest::read(&dir.join("FLOW.toml"))
        .unwrap()
        .with_input_decoder(std::sync::Arc::new(TestDecoder));
    let admission = on_stack(move || admit(&manifest));
    let refused = || Some(("inputs".to_owned(), "input-value".to_owned()));
    assert_eq!(
        outcomes(&admission),
        [
            ("hex".to_owned(), None),
            ("chain".to_owned(), None),
            ("through-link".to_owned(), None),
            ("absolute".to_owned(), refused()),
            ("parent".to_owned(), refused()),
            ("link-escape".to_owned(), refused()),
            ("chain-escape".to_owned(), refused()),
        ]
    );
    let initial = |id: &str| {
        let program = admission.programs.iter().find(|p| p.id == id).unwrap();
        program.outcome.as_ref().unwrap().initial_state.clone()
    };
    assert_eq!(initial("chain"), initial("hex"));
    assert_eq!(initial("through-link"), initial("hex"));
    assert_eq!(
        refusal_detail(&admission, "absolute"),
        "input `rom`: /rom.bin is absolute: name a file by its path relative to the manifest's \
         directory"
    );
    for (id, shown) in [
        ("parent", format!("../{name}-outside.bin")),
        ("link-escape", format!("escape/{name}-outside.bin")),
        ("chain-escape", format!("sub/../../{name}-outside.bin")),
    ] {
        assert_eq!(
            refusal_detail(&admission, id),
            format!("input `rom`: {shown} escapes the manifest's directory"),
        );
    }
}

/// A front end's decoder reads typed inputs; kink binds the terms it gives. A typed case's
/// initial configuration is the one the same values written as K text give, and its program
/// digest covers the decoded values: two documents of one value share a digest, and editing the
/// binary file the input reads changes it. A document the decoder refuses, a variable bound by
/// both `variables` and `inputs`, and a typed input with no value on the baseline are refused.
#[test]
fn typed_inputs_are_read_by_the_front_ends_decoder() {
    let dir = cases_flow(
        "typed-inputs",
        r#"
[[program]]
id = "typed"
variables = { ENTRY = "go" }
inputs = { n = 1, rom = { "$file" = "rom.bin" } }

[[program]]
id = "hex"
variables = { ENTRY = "go" }
inputs = { n = 1, rom = { "$hex" = "00ff" } }

[[program]]
id = "text"
variables = { ENTRY = "go", N = "1", ROM = 'b"\x00\xff"' }

[[program]]
id = "bad"
variables = { ENTRY = "go", N = "1" }
inputs = { rom = "rom.bin" }

[[program]]
id = "twice"
variables = { ENTRY = "go", N = "1" }
inputs = { n = 1, rom = { "$hex" = "00" } }

[[program]]
id = "undefined"
variables = { ENTRY = "go" }
inputs = { n = { "$call" = { label = "inverse", args = [0] } }, rom = { "$hex" = "" } }
"#,
    );
    let read = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
    let manifest = read
        .clone()
        .with_input_decoder(std::sync::Arc::new(TestDecoder));
    let edited = dir.clone();
    let (admission, digests, edited_digest) = on_stack(move || {
        let admission = admit(&manifest);
        let (_, admitted) = kink_flow::admit_spec(&manifest);
        let (spec, mut inputs) = admitted.unwrap();
        let session = inputs.session(&spec);
        let digest = |id: &str| {
            let program = manifest.programs.iter().find(|p| p.id == id).unwrap();
            kink_flow::digest::program_digest(program, &session.read(program).unwrap())
        };
        let digests = [digest("typed"), digest("hex"), digest("text")];
        fs::write(edited.join("rom.bin"), [0x00, 0xfe]).unwrap();
        let edited_digest = digest("typed");
        (admission, digests, edited_digest)
    });
    let refused = |stage: &str, reason: &str| Some((stage.to_owned(), reason.to_owned()));
    assert_eq!(
        outcomes(&admission),
        [
            ("typed".to_owned(), None),
            ("hex".to_owned(), None),
            ("text".to_owned(), None),
            ("bad".to_owned(), refused("inputs", "input-value")),
            ("twice".to_owned(), refused("inputs", "input-value")),
            (
                "undefined".to_owned(),
                refused("inputs", "initial-undefined")
            ),
        ]
    );
    let initial = |id: &str| {
        let program = admission.programs.iter().find(|p| p.id == id).unwrap();
        program.outcome.as_ref().unwrap().initial_state.clone()
    };
    assert_eq!(initial("typed"), initial("text"));
    assert_eq!(initial("hex"), initial("text"));
    assert_eq!(
        refusal_detail(&admission, "bad"),
        "input `rom`: the declared type does not decide this document"
    );
    assert_eq!(
        refusal_detail(&admission, "twice"),
        "input `n` binds $N, which `variables` binds too; bind it once"
    );
    // One value, two documents: one digest. The text program binds the same values as K text,
    // which the digest covers by their text: another digest.
    assert_eq!(digests[0], digests[1]);
    assert_ne!(digests[0], digests[2]);
    assert_ne!(edited_digest, digests[0]);
    // The K-level manifest reads no typed input.
    let k_level = on_stack(move || admit(&read));
    assert_eq!(
        outcomes(&k_level)[..2],
        [
            ("typed".to_owned(), refused("inputs", "typed-inputs")),
            ("hex".to_owned(), refused("inputs", "typed-inputs")),
        ]
    );
}

mod kink_tier {
    use super::*;

    /// A typed case runs as any other: `results` gives it a comparable baseline record, and `run`
    /// kills a mutation that changes what the case's binary input contributes, with the typed
    /// case as its killer.
    #[test]
    #[ignore = "kink"]
    fn a_typed_case_runs_under_results_and_run() {
        let dir = cases_flow(
            "typed-run",
            r#"
[[program]]
id = "typed"
variables = { ENTRY = "go" }
inputs = { n = 1, rom = { "$file" = "rom.bin" } }
"#,
        );
        write(
            &dir.join("MUTATIONS.toml"),
            "[[mutation]]\nid = \"rom-ignored\"\nnote = \"the binary input's length is not \
             counted\"\n\n  [[mutation.edit]]\n  rule = \"go\"\n  find = \"N +Int \
             lengthBytes(R)\"\n  replace = \"N\"\n",
        );
        let manifest = FlowManifest::read(&dir.join("FLOW.toml"))
            .unwrap()
            .with_input_decoder(std::sync::Arc::new(TestDecoder));
        let list = kink_flow::MutationList::read(&dir.join("MUTATIONS.toml")).unwrap();
        let ((results, results_ok), (run, run_ok)) = on_stack(move || {
            let results = kink_flow::results::results(
                &manifest,
                &kink_flow::results::ResultsOptions {
                    verify: false,
                    cache: None,
                    mutations: None,
                },
            );
            let run = kink_flow::search::run(
                &manifest,
                &list,
                &kink_flow::search::RunOptions {
                    only: Vec::new(),
                    cache: None,
                    order: kink_flow::search::ProgramOrder::Corpus,
                    compile_workers: Some(1),
                    memo: kink_flow::memo::MemoUse::On,
                },
            );
            (results, run)
        });
        assert!(results_ok, "{results:#}");
        assert_eq!(results["programs"][0]["class"], "comparable", "{results:#}");
        assert!(run_ok, "{run:#}");
        let row = &run["mutations"][0];
        assert_eq!(
            (&row["status"], &row["killer"]),
            (&Value::from("killed"), &Value::from("typed")),
            "{run:#}"
        );
    }

    /// `results` and `run` print the definition exclusion as `check` prints it (one formatter),
    /// and each excluded program's cause says why every run of it is excluded, as `check` says it:
    /// for the definition exclusion and for an excluded initial configuration. A reason only the
    /// run shows can come first (`g0`'s run contradicts `g`'s `total` claim): the program is not
    /// judged either way.
    #[test]
    #[ignore = "kink"]
    fn results_and_run_print_the_exclusion_as_check_does() {
        use kink_flow::{
            cli::{results, run},
            results::ResultsOptions,
            search::RunOptions,
        };
        let dir = scfetch_flow("scfetch-results");
        write(
            &dir.join("MUTATIONS.toml"),
            &one_edit(
                "unknown-op",
                "  rule = \"decode-unknown\"\n  find = \"unknown(Op)\"\n  replace = \"inc(Op)\"",
            ),
        );
        let manifest = dir.join("FLOW.toml");
        let (checked, results_document, run_document) = on_stack(move || {
            let (checked, _) = check(&manifest);
            let (results_document, status) = results(
                &manifest,
                &ResultsOptions {
                    cache: Some(dir.join("cache")),
                    ..ResultsOptions::default()
                },
            );
            assert_eq!(
                status, EXIT_OK,
                "an unknown program is no error of results: {results_document:#}"
            );
            let (run_document, _) = run(
                &manifest,
                &dir.join("MUTATIONS.toml"),
                &RunOptions {
                    cache: Some(dir.join("cache")),
                    ..RunOptions::default()
                },
            );
            (checked, results_document, run_document)
        });
        let exclusion = &checked["spec"]["exclusion"];
        assert_eq!(exclusion["exclusion"], "short-circuit-reading");
        assert_eq!(&results_document["spec"]["exclusion"], exclusion);
        assert_eq!(&run_document["spec"]["exclusion"], exclusion);
        let detail = checked["programs"][0]["detail"].as_str().unwrap();
        for program in results_document["programs"].as_array().unwrap() {
            assert_eq!(program["class"], "unknown", "{program:#}");
            let cause = program["cause"].as_str().unwrap();
            assert!(
                cause.contains(&format!(
                    "the run is excluded (short-circuit-reading): {detail}"
                )),
                "{cause}"
            );
        }

        let manifest = initial_state_flow("initial-state-results").join("FLOW.toml");
        let cache = manifest.parent().unwrap().join("cache");
        let (checked, results_document) = on_stack(move || {
            let (checked, _) = check(&manifest);
            let (results_document, _) = results(
                &manifest,
                &ResultsOptions {
                    cache: Some(cache),
                    ..ResultsOptions::default()
                },
            );
            (checked, results_document)
        });
        assert!(results_document["spec"]["exclusion"].is_null());
        let detail = checked["programs"][0]["detail"].as_str().unwrap();
        let g1 = &results_document["programs"][0];
        assert_eq!(g1["class"], "unknown", "{g1:#}");
        assert!(
            g1["cause"].as_str().unwrap().contains(&format!(
                "the run is excluded (short-circuit-reading): {detail}"
            )),
            "{g1:#}"
        );
        let g0 = &results_document["programs"][1];
        assert_eq!(g0["class"], "unknown", "{g0:#}");
        assert!(
            g0["cause"]
                .as_str()
                .unwrap()
                .contains("the run is excluded (contradicted-claim)"),
            "{g0:#}"
        );
        assert_eq!(results_document["programs"][2]["class"], "comparable");
    }

    /// With every program's result cached, `check` warns of an edited rule no comparable
    /// program witnesses; `run` exits 1 when a selected mutation is invalid.
    #[test]
    #[ignore = "kink"]
    fn check_warns_of_an_unwitnessed_rule_and_run_exits_one_on_an_invalid_mutation() {
        use kink_flow::{
            cli::{results, run},
            results::ResultsOptions,
            search::RunOptions,
        };
        let dir = calc_copy("check-unreached");
        let manifest = dir.join("FLOW.toml");
        let list = dir.join("MUTATIONS.toml");
        write(
            &list,
            &[
                one_edit("add-becomes-sub", ARITH),
                one_edit(
                    "mul-becomes-add",
                    "  rule = \"mul\"\n  find = \"I1 *Int I2\"\n  replace = \"I1 +Int I2\"",
                ),
                one_edit(
                    "renamed",
                    "  rule = \"div\"\n  find = \"/Int\"\n  replace = \"*Int\"",
                ),
            ]
            .concat(),
        );
        let (document, _) = check_list(&manifest, &list, None);
        assert_eq!(document["coverage"]["decides"], false, "{document:#}");
        assert_eq!(
            row(&document, "mul-becomes-add")["warnings"],
            serde_json::json!([])
        );

        let (document, status) = results(&manifest, &ResultsOptions::default());
        assert_eq!(status, EXIT_OK, "{document:#}");
        let (document, status) = check_list(&manifest, &list, None);
        assert_eq!(status, EXIT_CORPUS, "{document:#}");
        assert_eq!(document["coverage"]["decides"], true, "{document:#}");
        assert_eq!(
            row(&document, "add-becomes-sub")["warnings"],
            serde_json::json!([])
        );
        let unreached = &row(&document, "mul-becomes-add")["warnings"];
        assert_eq!(reasons(unreached), ["unreached-rule"], "{document:#}");
        assert_eq!(unreached[0]["rule"]["module"], "CALC");
        // Another cache holds no record: the warning is not given.
        let other = scratch("check-unreached-other-cache");
        let (document, _) = check_list(&manifest, &list, Some(&other));
        assert_eq!(document["coverage"]["decides"], false);

        let (document, status) = run(&manifest, &list, &RunOptions::default());
        assert_eq!(status, EXIT_CORPUS, "{document:#}");
        assert_eq!(document["counts"]["invalid-mutation"], 1, "{document:#}");
        let (document, status) = run(
            &manifest,
            &list,
            &RunOptions {
                only: vec!["add-becomes-sub".into(), "mul-becomes-add".into()],
                ..RunOptions::default()
            },
        );
        assert_eq!(status, EXIT_OK, "{document:#}");
    }

    #[test]
    #[ignore = "kink"]
    fn the_binarys_exit_codes() {
        let path = |name: &str| flow(name).into_os_string();
        let (code, stdout, _) = binary(&["check".as_ref(), &path("calc/FLOW.toml")]);
        assert_eq!(code, Some(EXIT_OK.into()));
        let document: Value = serde_json::from_str(&stdout).unwrap();
        assert_eq!(document["spec"]["outcome"], "admitted");
        assert_eq!(
            document["programs"]
                .as_array()
                .unwrap()
                .iter()
                .filter(|p| p["outcome"] == "ok")
                .count(),
            4
        );

        let (code, stdout, _) = binary(&["check".as_ref(), &path("register/FLOW.toml")]);
        assert_eq!(code, Some(EXIT_OK.into()), "{stdout}");

        let (code, stdout, _) = binary(&["check".as_ref(), &path("calc/FLOW-bad-program.toml")]);
        assert_eq!(code, Some(EXIT_CORPUS.into()));
        let document: Value = serde_json::from_str(&stdout).unwrap();
        let refused = document["programs"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|p| p["outcome"] == "refused")
            .map(|p| p["id"].as_str().unwrap())
            .collect::<Vec<_>>();
        assert_eq!(refused, ["bad"]);

        let (code, stdout, _) = binary(&["check".as_ref(), &path("compile-error/FLOW.toml")]);
        assert_eq!(code, Some(EXIT_CORPUS.into()));
        let document: Value = serde_json::from_str(&stdout).unwrap();
        assert_eq!(document["spec"]["stage"], "compile");

        let dir = scratch("binary");
        write(
            &dir.join("FLOW.toml"),
            "[spec]\nentry = \"calc.k\"\nmain_module = \"CALC\"\nmode = 1\n",
        );
        let (code, stdout, _) = binary(&["check".as_ref(), dir.join("FLOW.toml").as_os_str()]);
        assert_eq!(code, Some(EXIT_CORPUS.into()));
        let document: Value = serde_json::from_str(&stdout).unwrap();
        assert_eq!(
            (&document["spec"]["stage"], &document["spec"]["reason"]),
            (&Value::from("manifest"), &Value::from("invalid-manifest"))
        );
        assert_eq!(document["spec"]["detail"], "spec.mode: unknown key");

        for args in [
            vec![],
            vec!["check".as_ref()],
            vec!["run".as_ref(), path("calc/FLOW.toml").as_os_str()],
            vec!["check".as_ref(), dir.join("MISSING.toml").as_os_str()],
            vec![
                "check".as_ref(),
                path("calc/FLOW.toml").as_os_str(),
                "extra".as_ref(),
            ],
        ] {
            let (code, stdout, stderr) = binary(&args);
            assert_eq!(code, Some(EXIT_USAGE.into()), "{args:?}");
            assert!(stdout.is_empty(), "{args:?}");
            assert!(
                stderr.contains("usage: kink-flow --version | kink-flow check FLOW.toml"),
                "{stderr}"
            );
        }
    }
}
