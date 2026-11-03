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
            "k_rust_revision",
            "mutation_list",
            "mutations",
            "profile",
            "programs",
            "schema",
            "spec",
            "version"
        ]
    );
    assert_eq!(document["schema"], "kink-flow-check");
    assert_eq!(document["version"], 3);
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
        ["detail", "exclusion", "files", "outcome", "reason", "stage"]
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
        idle.text(program).unwrap();
    }
    drop(idle);
    assert_eq!(builds(), before, "a session that assembles no program");

    let mut session = inputs.session(&spec);
    let shared = programs
        .iter()
        .map(|program| {
            let text = session.text(program).unwrap();
            (session.test_case(program, text.clone()), text)
        })
        .collect::<Vec<_>>();
    assert_eq!(
        builds(),
        before + 1,
        "one grammar for {} programs",
        programs.len()
    );

    for (program, (test, text)) in programs.iter().zip(shared) {
        let test = test.unwrap_or_else(|refusal| panic!("{}: {refusal:?}", program.id));
        let fresh = kink_corpus::assemble_input_with(
            &spec.loaded,
            Some(&spec.compiled),
            &kink_corpus::TestInputSpec {
                program: kink_corpus::ProgramSource::Text(text),
                start_sort: program.start_sort.clone(),
                variables: program.variables.clone(),
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
    assert_eq!(document["version"], 3);
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
            .definition_exclusion(),
        Some(kink_native::exclusion::Exclusion::ShortCircuitReading)
    );
    assert_eq!(status, EXIT_CORPUS, "{document:#}");
    assert_eq!(document["version"], 3);
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

mod kink_tier {
    use super::*;

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
