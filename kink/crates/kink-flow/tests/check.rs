//! Admission and `kink-flow check` (flow F-02 deliverables 3, 4 and 6).

use kink_flow::{
    FlowManifest,
    admit::{FlowAdmission, admit},
    cli::{
        CheckOptions, EXIT_NO, EXIT_UNANSWERED, EXIT_UNASKED, EXIT_YES, Verb, check, check_with,
    },
    mutation::InvalidReason,
};
use kink_patch::sha256;
use serde_json::Value;

mod flow_support;
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
    assert_eq!(status, EXIT_YES, "{document:#}");
    let keys = |v: &Value| v.as_object().unwrap().keys().cloned().collect::<Vec<_>>();
    // Under the Z3 profile the document also names the Z3 build (`z3`, version 14).
    let mut expected = vec![
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
        "version",
    ];
    if flow_support::z3_member().is_some() {
        expected.push("z3");
    }
    assert_eq!(keys(&document), expected);
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
    assert_eq!(document["version"], 21);
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
            "short_circuit",
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
    assert!(
        document["spec"]["short_circuit"].is_null(),
        "calc's short-circuit analysis flags no rule"
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

/// Under the Z3 profile the check document names the Z3 build (`z3`): its expectations and
/// coverage warnings are read from result records the build decided. So does the document every
/// verb gives for a manifest that does not decode, which is built from the check document's
/// header. Under the portable profile none of them names a Z3 build.
#[test]
fn the_check_document_names_the_z3_build_under_the_z3_profile() {
    let z3 = flow_support::z3_member();
    let (document, status) = check(&flow("calc/FLOW.toml"));
    assert_eq!(status, EXIT_YES, "{document:#}");
    assert_eq!(document.get("z3"), z3.as_ref(), "{document:#}");
    let error = FlowManifest::read(&flow("calc/calc.k")).unwrap_err();
    for verb in [
        Verb::Check,
        Verb::Coverage,
        Verb::Run,
        Verb::Report,
        Verb::Query,
        Verb::Fuzz,
    ] {
        let refused = verb.manifest_refused(&error);
        assert_eq!(refused.get("z3"), z3.as_ref(), "{verb:?}: {refused:#}");
    }
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
    assert_eq!(status, EXIT_UNASKED);
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
    assert_eq!(status, EXIT_UNASKED);
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

/// PJ-30, PJ-31: `kink-flow check FLOW.toml FLOW.toml...` names the other flows on the corpus
/// root by their manifests. A flow given twice is one flow, checked once, whose `with` names the
/// other path; two flows are each checked, in one document (`flows`, each with its `flow`), and
/// one that reads its cases from another tree is refused in the other's `with`, exit 2; a path
/// that is no file, and `--mutations` with several flows, are usage errors.
#[test]
fn check_reads_the_flows_the_command_line_names() {
    let calc = flow("calc/FLOW.toml");
    let (code, stdout, stderr) = binary(&["check".as_ref(), calc.as_os_str(), calc.as_os_str()]);
    assert_eq!(code, Some(EXIT_YES.into()), "{stdout}{stderr}");
    let document: Value = serde_json::from_str(&stdout).unwrap();
    assert_eq!(
        document["with"],
        serde_json::json!([{
            "flow": calc.display().to_string(),
            "outcome": "ok",
            "definition": "CALC",
            "detail": null,
        }]),
        "{document:#}"
    );
    assert_eq!(document.get("flows"), None, "{document:#}");
    let other = flow("loop/FLOW.toml");
    let (code, stdout, stderr) = binary(&["check".as_ref(), calc.as_os_str(), other.as_os_str()]);
    assert_eq!(code, Some(EXIT_UNASKED.into()), "{stdout}{stderr}");
    let document: Value = serde_json::from_str(&stdout).unwrap();
    assert_eq!(document["schema"], "kink-flow-check", "{document:#}");
    assert_eq!(document["version"], 21, "{document:#}");
    let flows = document["flows"].as_array().unwrap();
    assert_eq!(flows.len(), 2, "{document:#}");
    assert_eq!(flows[0]["flow"], calc.display().to_string(), "{document:#}");
    assert_eq!(
        flows[1]["flow"],
        other.display().to_string(),
        "{document:#}"
    );
    assert_eq!(flows[0]["with"][0]["outcome"], "refused", "{document:#}");
    assert_eq!(flows[0]["spec"]["outcome"], "admitted", "{document:#}");
    assert_eq!(flows[1]["with"][0]["flow"], calc.display().to_string());
    let missing = flow("calc/NO-SUCH-FLOW.toml");
    let (code, stdout, stderr) = binary(&["check".as_ref(), calc.as_os_str(), missing.as_os_str()]);
    assert_eq!(code, Some(EXIT_UNASKED.into()), "{stdout}{stderr}");
    assert!(stdout.is_empty(), "{stdout}");
    assert!(
        stderr.contains(&format!("{} is not a file", missing.display())),
        "{stderr}"
    );
    let (code, stdout, stderr) = binary(&[
        "check".as_ref(),
        calc.as_os_str(),
        other.as_os_str(),
        "--mutations".as_ref(),
        calc.as_os_str(),
    ]);
    assert_eq!(code, Some(EXIT_UNASKED.into()), "{stdout}{stderr}");
    assert!(stdout.is_empty(), "{stdout}");
    assert!(stderr.contains("a check of several flows"), "{stderr}");
    let (code, _, stderr) = binary(&[
        "check".as_ref(),
        calc.as_os_str(),
        "--with".as_ref(),
        calc.as_os_str(),
    ]);
    assert_eq!(code, Some(EXIT_UNASKED.into()), "{stderr}");
    assert!(stderr.contains("invalid option '--with'"), "{stderr}");
}

/// fz26 FZ-REPLAY-WHOLE (final review N6): `--version` prints the build and k-rust's identity
/// and exits 0, as `krust-fuzz --version` does, instead of the usage.
#[test]
fn the_version_flag_names_the_builds() {
    let (code, stdout, stderr) = binary(&["--version".as_ref()]);
    assert_eq!(code, Some(EXIT_YES.into()), "{stderr}");
    assert_eq!(
        stdout,
        format!(
            "kink-flow {} (k-rust {})\n",
            env!("CARGO_PKG_VERSION"),
            k_rust::build_identity()
        )
    );
    // With anything after it, the flag is a usage error that says so, not an unknown verb.
    let (code, stdout, stderr) = binary(&["--version".as_ref(), "extra".as_ref()]);
    assert_eq!(code, Some(EXIT_UNASKED.into()), "{stderr}");
    assert!(stdout.is_empty(), "{stdout}");
    assert!(
        stderr.starts_with(
            "kink-flow: --version takes no operand or option\nusage: kink-flow --version"
        ),
        "{stderr}"
    );
}

/// Asking for help is a question the tool answers: `--help` and `-h` alone print the usage line,
/// the loop, the mutation format and the exit statuses on stdout, and exit 0; after a verb,
/// anywhere among its operands and options, they print the verb's usage line and every option
/// of the verb's, which the general help does not explain.
#[test]
fn the_help_flag_answers_on_stdout() {
    for flag in ["--help", "-h"] {
        let (code, stdout, stderr) = binary(&[flag.as_ref()]);
        assert_eq!(code, Some(EXIT_YES.into()), "{flag}: {stderr}");
        assert!(stderr.is_empty(), "{flag}: {stderr}");
        assert!(stdout.starts_with("usage: kink-flow --version"), "{stdout}");
        assert!(stdout.contains("[[mutation.edit]]"), "{stdout}");
        assert!(stdout.contains("`kink-flow VERB --help`"), "{stdout}");
    }
    let manifest = flow("calc/FLOW.toml");
    for (args, verb) in [
        (vec!["run".as_ref(), "--help".as_ref()], Verb::Run),
        (
            vec!["check".as_ref(), manifest.as_os_str(), "-h".as_ref()],
            Verb::Check,
        ),
        (vec!["fuzz".as_ref(), "--help".as_ref()], Verb::Fuzz),
    ] {
        let (code, stdout, stderr) = binary(&args);
        assert_eq!(code, Some(EXIT_YES.into()), "{args:?}: {stderr}");
        assert!(stderr.is_empty(), "{args:?}: {stderr}");
        assert_eq!(stdout, kink_flow::cli::verb_help(verb));
        assert!(
            stdout.starts_with(&format!("usage: kink-flow {}\n", verb.synopsis())),
            "{stdout}"
        );
        for option in verb.options() {
            assert!(stdout.contains(option.spelling), "{stdout}");
        }
    }
    let (_, fuzz, _) = binary(&["fuzz".as_ref(), "--help".as_ref()]);
    for option in ["--cases N", "--work W", "--seed S", "--no-confirm"] {
        assert!(fuzz.contains(&format!("  {option} ")), "{fuzz}");
    }
    // Each verb's usage line is the one the general usage line lists.
    for verb in Verb::ALL {
        assert!(
            kink_flow::cli::USAGE.contains(&format!("kink-flow {}", verb.synopsis())),
            "{verb:?}"
        );
    }
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
            ..CheckOptions::default()
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
    assert_eq!(status, EXIT_UNASKED, "{document:#}");
    assert_eq!(document["version"], 21);
    assert_eq!(document["spec"]["outcome"], "admitted");
    assert_eq!(document["mutation_list"]["outcome"], "ok");
    // Nothing ran and nothing was written: no cache, so no unmatched-rule warning.
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
            ("stale/syntax", "ok"),
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

    // PJ-34: a grammar edit resolves and is shown as a rule edit is: the production the line lies
    // in, its whole declaration before and after, and `kind = "grammar"`; the anchor warning names
    // the production's name.
    let syntax = row(&document, "stale/syntax");
    let rule = &syntax["rules"][0];
    assert_eq!(rule["kind"], "grammar", "{syntax:#}");
    assert_eq!(
        (
            &rule["label"],
            &rule["file"],
            &rule["start_line"],
            &rule["end_line"]
        ),
        (
            &Value::from("mul"),
            &Value::from("calc.k"),
            &Value::from(6),
            &Value::from(12)
        )
    );
    assert!(
        rule["before"]
            .as_str()
            .unwrap()
            .contains("Exp \"*\" Exp [strict, symbol(mul)]")
            && rule["after"]
                .as_str()
                .unwrap()
                .contains("Exp \"x\" Exp [strict, symbol(mul)]"),
        "{rule:#}"
    );
    assert_eq!(reasons(&syntax["warnings"]), ["line-anchor"]);
    assert_eq!(
        syntax["warnings"][0]["next"],
        "address the production by its name: production = \"mul\""
    );
    // A rule entry has no `kind`.
    assert!(ok["rules"][0].get("kind").is_none(), "{ok:#}");

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
    assert_eq!(status, EXIT_YES, "{document:#}");
    assert_eq!(row(&document, "add-becomes-sub")["outcome"], "ok");

    // A list that does not decode is refused, with the specification still admitted.
    write(&dir.join("BAD.toml"), "[[mutation]]\nid = \"m\"\n");
    let (document, status) = check_list(&manifest, &dir.join("BAD.toml"), None);
    assert_eq!(status, EXIT_UNASKED);
    assert_eq!(document["mutation_list"]["outcome"], "refused");
    assert!(document["mutations"].is_null());
}

/// The members of a grammar mutation's row a warm run must repeat.
fn grammar_verdict(row: &Value) -> Value {
    serde_json::json!({
        "status": row["status"],
        "reason": row["reason"],
        "killer": row["killer"],
        "killer_source": row["killer_source"],
        "direction": row["direction"],
        "grammar": row["grammar"],
    })
}

/// A row's `[status, killer, direction]`.
fn killed_as(row: &Value) -> Value {
    serde_json::json!([row["status"], row["killer"], row["direction"]])
}

/// A row's `grammar` member: each case's `[program, reparse, verdict]`.
fn reparsed(row: &Value) -> Value {
    row["grammar"]
        .as_array()
        .unwrap()
        .iter()
        .map(|case| serde_json::json!([case["program"], case["reparse"], case["verdict"]]))
        .collect()
}

/// PJ-34 (U34c): `run` parses every case again under a grammar mutant's grammar. In calc, which
/// declares no end and no `[stop]`, the baseline's acceptance of `1 + 2` is not decided, so a
/// mutant that rejects it at parse is `unknown` (acceptance ignores the stage, README.md D2),
/// never killed by the parse alone; a mutant every case parses alike is judged by its runs of
/// the baseline's test cases (here `survived`); a warm run gives the cold run's rows; the rule
/// mutation of the list is judged as before; `run --full` still refuses the grammar mutations.
#[test]
fn run_parses_each_case_again_under_a_grammar_mutant() {
    let dir = calc_copy("run-grammar");
    let manifest = dir.join("FLOW.toml");
    let mutations = dir.join("MUTATIONS.toml");
    write(
        &mutations,
        &[
            one_edit("add-becomes-sub", ARITH),
            one_edit(
                "plus-literal",
                "  production = \"add\"\n  find = \"\\\"+\\\"\"\n  replace = \"\\\"plus\\\"\"",
            ),
            one_edit(
                "minus-literal",
                "  production = \"sub\"\n  find = \"\\\"-\\\"\"\n  replace = \"\\\"minus\\\"\"",
            ),
        ]
        .concat(),
    );
    let (check, _) = check_list(&manifest, &mutations, None);
    assert_eq!(row(&check, "plus-literal")["outcome"], "ok", "{check:#}");
    let (document, _) = flow_support::corpus_run(&manifest, &mutations);
    assert_eq!(document["version"], 46, "{document:#}");
    let plus = row(&document, "plus-literal");
    assert_eq!(
        (&plus["status"], &plus["reason"], &plus["direction"]),
        (
            &Value::from("unknown"),
            &Value::from("grammar-acceptance-not-decided"),
            &Value::Null
        ),
        "{plus:#}"
    );
    let case = &plus["grammar"][0];
    assert_eq!(
        (&case["program"], &case["reparse"], &case["verdict"]),
        (
            &Value::from("add"),
            &Value::from("rejected"),
            &Value::from("unknown")
        ),
        "{plus:#}"
    );
    assert!(plus["calls"].as_array().unwrap().is_empty(), "{plus:#}");
    let minus = row(&document, "minus-literal");
    assert_eq!(minus["grammar"][0]["reparse"], "same", "{minus:#}");
    assert_eq!(minus["status"], "survived", "{minus:#}");
    assert_eq!(minus["direction"], Value::Null, "{minus:#}");
    assert!(!minus["rules"].is_null(), "{minus:#}");
    assert_eq!(
        row(&document, "add-becomes-sub")["status"],
        "killed",
        "{document:#}"
    );
    assert!(
        row(&document, "add-becomes-sub").get("grammar").is_none(),
        "{document:#}"
    );
    // The survivor is the run's one grammar target (U34d), with its declaration before and after
    // and the grammar survivor's action; the `unknown` row and the rule mutation are not targets.
    let targets = document["grammar_targets"].as_array().unwrap();
    assert_eq!(
        targets
            .iter()
            .map(|target| &target["mutation"])
            .collect::<Vec<_>>(),
        ["minus-literal"],
        "{document:#}"
    );
    let declaration = &targets[0]["declarations"][0];
    assert_eq!(declaration["label"], "sub", "{document:#}");
    assert!(
        declaration["after"].as_str().unwrap().contains("\"minus\""),
        "{document:#}"
    );
    assert_eq!(
        targets[0]["rejected"],
        serde_json::json!([]),
        "{document:#}"
    );
    assert_eq!(minus["action"], targets[0]["action"], "{minus:#}");
    assert!(
        minus["action"]
            .as_str()
            .unwrap()
            .contains("tells the two grammars apart"),
        "{minus:#}"
    );
    let (warm, _) = flow_support::corpus_run(&manifest, &mutations);
    for id in ["plus-literal", "minus-literal"] {
        assert_eq!(
            grammar_verdict(row(&warm, id)),
            grammar_verdict(row(&document, id)),
            "{id}: {warm:#}"
        );
    }
    assert_eq!(
        warm["grammar_targets"], document["grammar_targets"],
        "{warm:#}"
    );
    let full = kink_flow::search::run(
        &FlowManifest::read(&manifest).unwrap(),
        &kink_flow::MutationList::read(&mutations).unwrap(),
        &kink_flow::search::RunOptions {
            legacy_lock: None,
            only: Vec::new(),
            cache: None,
            compile_workers: None,
            memo: kink_flow::memo::MemoUse::On,
            schedule: kink_campaign::ScheduleMode::Full,
            lock: None,
            locked: false,
        },
    )
    .0;
    let refused = row(&full, "plus-literal");
    assert_eq!(
        (&refused["status"], &refused["reason"]),
        (&Value::from("error"), &Value::from("grammar-not-run")),
        "{refused:#}"
    );
    // No row of the full run is a judged grammar mutation, so it has no grammar targets.
    assert!(full.get("grammar_targets").is_none(), "{full:#}");
    assert!(
        refused["action"].as_str().unwrap().contains("first-kill"),
        "{refused:#}"
    );
}

/// PJ-34 (U34c2): a case the mutant's grammar parses to another term runs on the mutant from
/// that term, its baseline side from the baseline's: `+` and `-` made right-associative parse
/// `10 - 4 - 3` as `10 - (4 - 3)`, whose run ends at 9 where the baseline's ends at 3, so the
/// case kills, direction `parses-differently`; `*` made right-associative parses `2 * 3 * 4`
/// apart too, but both runs end at 24, so every case agrees and the mutant survives. A warm run
/// gives the cold rows, and the rule mutation of the list is judged as before.
#[test]
fn a_grammar_mutant_that_parses_a_case_differently_is_killed_by_its_run() {
    use serde_json::json;
    let dir = scratch("run-grammar-differently");
    write(&dir.join("calc.k"), CALC_K);
    write(
        &dir.join("FLOW.toml"),
        "[spec]\nentry = \"calc.k\"\nmain_module = \"CALC\"\nsyntax_module = \"CALC-SYNTAX\"\n\n\
         [[program]]\nid = \"add\"\ntext = \"1 + 2\"\n\n\
         [[program]]\nid = \"sub\"\ntext = \"10 - 4 - 3\"\n\n\
         [[program]]\nid = \"chain\"\ntext = \"2 * 3 * 4\"\n\n\
         [[program]]\nid = \"bad\"\ntext = \"1 + * 2\"\nexpect = { rejected = \"parse\" }\n",
    );
    let manifest = dir.join("FLOW.toml");
    let mutations = dir.join("MUTATIONS.toml");
    write(
        &mutations,
        &[
            one_edit("add-becomes-sub", ARITH),
            one_edit(
                "right-plus",
                "  production = \"add\"\n  find = \"> left:\\n                 Exp \\\"+\\\"\"\n  \
                 replace = \"> right:\\n                 Exp \\\"+\\\"\"",
            ),
            one_edit(
                "right-mul",
                "  production = \"mul\"\n  find = \"> left:\\n                 Exp \\\"*\\\"\"\n  \
                 replace = \"> right:\\n                 Exp \\\"*\\\"\"",
            ),
        ]
        .concat(),
    );
    let (check, _) = check_list(&manifest, &mutations, None);
    for id in ["right-plus", "right-mul"] {
        assert_eq!(row(&check, id)["outcome"], "ok", "{id}: {check:#}");
    }
    let (document, _) = flow_support::corpus_run(&manifest, &mutations);
    let plus = row(&document, "right-plus");
    assert_eq!(
        killed_as(plus),
        json!(["killed", "sub", "parses-differently"]),
        "{plus:#}"
    );
    assert_eq!(
        reparsed(plus),
        json!([
            ["add", "same", "run"],
            ["sub", "different", "run"],
            ["chain", "same", "run"],
            ["bad", "rejected", "agree"]
        ]),
        "{plus:#}"
    );
    let mul = row(&document, "right-mul");
    assert_eq!(killed_as(mul), json!(["survived", null, null]), "{mul:#}");
    assert_eq!(
        reparsed(mul),
        json!([
            ["add", "same", "run"],
            ["sub", "same", "run"],
            ["chain", "different", "run"],
            ["bad", "rejected", "agree"]
        ]),
        "{mul:#}"
    );
    let rule = row(&document, "add-becomes-sub");
    assert_eq!(rule["status"], "killed", "{rule:#}");
    assert!(rule.get("grammar").is_none(), "{rule:#}");
    assert!(rule.get("direction").is_none(), "{rule:#}");
    assert_eq!(plus["killer_source"], "search", "{plus:#}");
    // Warm, the kill is served from the outcome cache (keyed by the pinned patch and the
    // program, which fix the mutant's term), with the cold run's verdict.
    let (warm, _) = flow_support::corpus_run(&manifest, &mutations);
    assert_eq!(
        row(&warm, "right-plus")["killer_source"],
        "outcome-cache",
        "{warm:#}"
    );
    for id in ["right-plus", "right-mul"] {
        let verdict = |document: &Value| {
            let mut verdict = grammar_verdict(row(document, id));
            verdict.as_object_mut().unwrap().remove("killer_source");
            verdict
        };
        assert_eq!(verdict(&warm), verdict(&document), "{id}: {warm:#}");
    }
    assert_eq!(
        row(&warm, "add-becomes-sub")["status"],
        "killed",
        "{warm:#}"
    );
    // The cache names the program's text, which the mutant's term is parsed from: with `sub`
    // bracketed, the baseline's term (and its run) is unchanged, the mutant parses it alike, and
    // the cached kill of the old text is not served.
    let flow = std::fs::read_to_string(&manifest).unwrap();
    write(
        &manifest,
        &flow.replace("\"10 - 4 - 3\"", "\"(10 - 4) - 3\""),
    );
    let (bracketed, _) = flow_support::corpus_run(&manifest, &mutations);
    let plus = row(&bracketed, "right-plus");
    assert_eq!(killed_as(plus), json!(["survived", null, null]), "{plus:#}");
    assert_eq!(plus["grammar"][1]["reparse"], "same", "{plus:#}");
    // The other records are still served: the edit moved no context, only `sub`'s key.
    assert_eq!(
        row(&bracketed, "add-becomes-sub")["killer_source"],
        "outcome-cache",
        "{bracketed:#}"
    );
}

/// A mutation of two edits, each a TOML edit body.
fn two_edits(id: &str, first: &str, second: &str) -> String {
    format!(
        "[[mutation]]\nid = \"{id}\"\nmisunderstanding = \"{id}\"\n\n  [[mutation.edit]]\n{first}\n\n  \
         [[mutation.edit]]\n{second}\n"
    )
}

const RIGHT_PLUS: &str = "  production = \"add\"\n  find = \"> left:\\n                 Exp \\\"+\\\"\"\n  \
                          replace = \"> right:\\n                 Exp \\\"+\\\"\"";
const RIGHT_MUL: &str = "  production = \"mul\"\n  find = \"> left:\\n                 Exp \\\"*\\\"\"\n  \
                         replace = \"> right:\\n                 Exp \\\"*\\\"\"";
const MINUS_LITERAL: &str =
    "  production = \"sub\"\n  find = \"\\\"-\\\"\"\n  replace = \"\\\"minus\\\"\"";

/// PJ-35 (U35a): one judgement for every mutant, and a mutation may edit rules beside grammar
/// declarations. A case both grammars parse alike that kills is a kill, direction
/// `runs-differently`: `*` made right-associative with the `add` rule made a subtraction parses
/// `1 + 2` alike and runs it to -1, where the baseline runs it to 3. A joint mutant whose grammar
/// edit parses a case apart is killed by its run, `parses-differently` (`+` and `-` made
/// right-associative, with a rule edit that changes no value). An edited rule is parsed under the
/// mutant's grammar: written in the edited syntax (`minus`) it resolves beside the edit that makes
/// that syntax, is refused as a rule mutation alone (`edited-load-failed`), and written in the old
/// syntax beside the grammar edit is refused too. The rule mutation's row is the one a list of
/// rule mutations alone gives, with no `grammar` or `direction`; warm rows equal the cold ones;
/// `run --verify` judges the grammar mutations and finds no mismatch.
#[test]
fn joint_grammar_and_rule_mutants_are_judged_by_the_one_judgement() {
    use serde_json::json;
    let dir = scratch("run-joint");
    write(&dir.join("calc.k"), CALC_K);
    write(
        &dir.join("FLOW.toml"),
        "[spec]\nentry = \"calc.k\"\nmain_module = \"CALC\"\nsyntax_module = \"CALC-SYNTAX\"\n\n\
         [[program]]\nid = \"add\"\ntext = \"1 + 2\"\n\n\
         [[program]]\nid = \"sub\"\ntext = \"10 - 4 - 3\"\n\n\
         [[program]]\nid = \"chain\"\ntext = \"2 * 3 * 4\"\n\n\
         [[program]]\nid = \"bad\"\ntext = \"1 + * 2\"\nexpect = { rejected = \"parse\" }\n",
    );
    let manifest = dir.join("FLOW.toml");
    let mutations = dir.join("MUTATIONS.toml");
    let rules_only = dir.join("RULES.toml");
    let new_syntax_rule = "  line = 23\n  find = \"I1:Int - I2:Int => I1 -Int I2\"\n  \
                           replace = \"I1:Int minus I2:Int => I2 -Int I1\"";
    let same_meaning_rule =
        "  line = 23\n  find = \"I1:Int - I2:Int\"\n  replace = \"I1:Int minus I2:Int\"";
    let old_syntax_rule = "  line = 23\n  find = \"I1 -Int I2\"\n  replace = \"I2 -Int I1\"";
    write(&rules_only, &one_edit("add-becomes-sub", ARITH));
    write(
        &mutations,
        &[
            one_edit("add-becomes-sub", ARITH),
            two_edits("joint-runs-differently", RIGHT_MUL, ARITH),
            two_edits(
                "joint-parses-differently",
                RIGHT_PLUS,
                "  rule = \"mul\"\n  find = \"I1 *Int I2\"\n  replace = \"I1 *Int I2 +Int 0\"",
            ),
            two_edits("joint-new-syntax", MINUS_LITERAL, new_syntax_rule),
            one_edit("new-syntax-alone", new_syntax_rule),
            two_edits("joint-old-syntax", MINUS_LITERAL, old_syntax_rule),
            two_edits("joint-same-meaning", MINUS_LITERAL, same_meaning_rule),
        ]
        .concat(),
    );
    let (check, _) = check_list(&manifest, &mutations, None);
    for id in [
        "joint-runs-differently",
        "joint-parses-differently",
        "joint-new-syntax",
    ] {
        assert_eq!(row(&check, id)["outcome"], "ok", "{id}: {check:#}");
    }
    // The joint mutation's rows: the grammar declaration and the edited rule, in sentence order
    // (module `CALC` before `CALC-SYNTAX`); the rule's row is a rule mutation's.
    let joint = row(&check, "joint-new-syntax");
    let rules = joint["rules"].as_array().unwrap();
    assert_eq!(rules.len(), 2, "{joint:#}");
    assert_eq!(
        (&rules[0]["kind"], &rules[1]["kind"]),
        (&Value::Null, &Value::from("grammar")),
        "{joint:#}"
    );
    assert!(
        rules[0]["after"]
            .as_str()
            .unwrap()
            .contains("I1:Int minus I2:Int => I2 -Int I1"),
        "{joint:#}"
    );
    let refused = |id: &str| {
        let row = row(&check, id);
        assert_eq!(row["outcome"], "refused", "{id}: {row:#}");
        row["refusals"][0]["reason"].as_str().unwrap().to_owned()
    };
    assert_eq!(refused("new-syntax-alone"), "edited-load-failed");
    assert_eq!(refused("joint-old-syntax"), "edited-load-failed");
    // The rule written in the edited syntax with its meaning kept is the same rule: the same
    // constructor applied to the same arguments.
    assert_eq!(refused("joint-same-meaning"), "no-change");

    let (document, _) = flow_support::corpus_run(&manifest, &mutations);
    let runs = row(&document, "joint-runs-differently");
    assert_eq!(
        killed_as(runs),
        json!(["killed", "add", "runs-differently"]),
        "{runs:#}"
    );
    assert_eq!(
        reparsed(runs),
        json!([
            ["add", "same", "run"],
            ["sub", "same", "run"],
            ["chain", "different", "run"],
            ["bad", "rejected", "agree"]
        ]),
        "{runs:#}"
    );
    assert_eq!(runs["killer_source"], "search", "{runs:#}");
    let parses = row(&document, "joint-parses-differently");
    assert_eq!(
        killed_as(parses),
        json!(["killed", "sub", "parses-differently"]),
        "{parses:#}"
    );
    // The new syntax rejects `10 - 4 - 3` at parse; calc declares no end and no `[stop]`, so
    // whether the baseline accepts it is not decided (README.md D2).
    let syntax = row(&document, "joint-new-syntax");
    assert_eq!(
        (&syntax["status"], &syntax["reason"]),
        (
            &Value::from("unknown"),
            &Value::from("grammar-acceptance-not-decided")
        ),
        "{syntax:#}"
    );
    // The rule mutation's row is the one a list of rule mutations alone gives.
    let (alone, _) = flow_support::corpus_run(&manifest, &rules_only);
    let rule_verdict = |document: &Value| {
        let row = row(document, "add-becomes-sub");
        assert!(row.get("grammar").is_none(), "{row:#}");
        assert!(row.get("direction").is_none(), "{row:#}");
        json!({
            "status": row["status"],
            "reason": row["reason"],
            "killer": row["killer"],
            "killed_by": row["killed_by"],
            "executed": row["executed"]
                .as_array()
                .unwrap()
                .iter()
                .map(|entry| json!([entry["program"], entry["outcome"]]))
                .collect::<Vec<_>>(),
            "removed_claims": row["removed_claims"],
            "witnesses": row["witnesses"],
        })
    };
    assert_eq!(
        rule_verdict(&document),
        rule_verdict(&alone),
        "{document:#}"
    );
    let (warm, _) = flow_support::corpus_run(&manifest, &mutations);
    for id in [
        "joint-runs-differently",
        "joint-parses-differently",
        "joint-new-syntax",
    ] {
        let verdict = |document: &Value| {
            let mut verdict = grammar_verdict(row(document, id));
            verdict.as_object_mut().unwrap().remove("killer_source");
            verdict
        };
        assert_eq!(verdict(&warm), verdict(&document), "{id}: {warm:#}");
    }
    // `run --verify` judges a grammar mutation: its calls start each case parsed apart from the
    // mutant's configuration, so the records agree with the live runs.
    let (verified, _) = kink_flow::search::run_with(
        &FlowManifest::read(&manifest).unwrap(),
        &kink_flow::MutationList::read(&mutations).unwrap(),
        &kink_flow::search::RunOptions {
            legacy_lock: None,
            only: Vec::new(),
            cache: None,
            compile_workers: None,
            memo: kink_flow::memo::MemoUse::On,
            schedule: kink_campaign::ScheduleMode::FirstKill,
            lock: None,
            locked: false,
        },
        kink_flow::search::RunMode::Verify,
    );
    assert_eq!(verified["mismatches"], json!([]), "{verified:#}");
    for id in ["joint-runs-differently", "joint-parses-differently"] {
        assert_eq!(
            killed_as(row(&verified, id)),
            killed_as(row(&document, id)),
            "{id}: {verified:#}"
        );
    }
}

const MACRO_K: &str = "module MAC-SYNTAX
  imports INT-SYNTAX
  syntax Exp ::= Int
               | Exp \"+\" Exp [left, strict, symbol(plus)]
               | \"twice\" \"(\" Exp \")\" [macro, symbol(twice)]
endmodule

module MAC
  imports MAC-SYNTAX
  imports INT
  configuration <k> $PGM:Exp </k>

  syntax KResult ::= Int
  rule [twice]: twice(E:Exp) => E + E
  rule [plus]: I1:Int + I2:Int => I1 +Int I2
endmodule
";

/// PJ-35 (U35a, Q1): a rule mutation that edits a rule program macro expansion reads has its
/// cases parsed again, since k-rust's assembly expands a program's macros with the mutant's own
/// macro rules. `twice(E)` made `E + E + E` assembles `twice(3)` as `3 + 3 + 3`, whose run ends at
/// 9 where the baseline's `3 + 3` ends at 6: killed, `parses-differently`. Run from the
/// specification's configuration, as before, the mutant (whose compiled rules hold no macro)
/// ends at 6 too and would survive. `1 + 2` parses alike. The row carries `grammar` and is no
/// grammar target; the commands that do not parse the cases again refuse it (`grammar-not-run`);
/// a rule mutation of a rule no macro expansion reads keeps its row, with no `grammar`.
#[test]
fn a_rule_mutation_of_a_macro_rule_is_judged_on_its_own_expansion() {
    use serde_json::json;
    let dir = scratch("run-macro-rule");
    write(&dir.join("mac.k"), MACRO_K);
    write(
        &dir.join("FLOW.toml"),
        "[spec]\nentry = \"mac.k\"\nmain_module = \"MAC\"\nsyntax_module = \"MAC-SYNTAX\"\n\n\
         [[program]]\nid = \"add\"\ntext = \"1 + 2\"\n\n\
         [[program]]\nid = \"twice\"\ntext = \"twice(3)\"\n",
    );
    let manifest = dir.join("FLOW.toml");
    let mutations = dir.join("MUTATIONS.toml");
    write(
        &mutations,
        &[
            one_edit(
                "thrice",
                "  rule = \"twice\"\n  find = \"E + E\"\n  replace = \"E + E + E\"",
            ),
            one_edit(
                "plus-becomes-minus",
                "  rule = \"plus\"\n  find = \"I1 +Int I2\"\n  replace = \"I1 -Int I2\"",
            ),
        ]
        .concat(),
    );
    let (check, _) = check_list(&manifest, &mutations, None);
    assert_eq!(row(&check, "thrice")["outcome"], "ok", "{check:#}");
    let (document, _) = flow_support::corpus_run(&manifest, &mutations);
    let thrice = row(&document, "thrice");
    assert_eq!(
        killed_as(thrice),
        json!(["killed", "twice", "parses-differently"]),
        "{thrice:#}"
    );
    assert_eq!(
        reparsed(thrice),
        json!([["add", "same", "run"], ["twice", "different", "run"]]),
        "{thrice:#}"
    );
    let rule = row(&document, "plus-becomes-minus");
    assert_eq!(rule["status"], "killed", "{rule:#}");
    assert!(rule.get("grammar").is_none(), "{rule:#}");
    assert!(rule.get("direction").is_none(), "{rule:#}");
    let (warm, _) = flow_support::corpus_run(&manifest, &mutations);
    assert_eq!(
        killed_as(row(&warm, "thrice")),
        killed_as(thrice),
        "{warm:#}"
    );
    let full = kink_flow::search::run(
        &FlowManifest::read(&manifest).unwrap(),
        &kink_flow::MutationList::read(&mutations).unwrap(),
        &kink_flow::search::RunOptions {
            legacy_lock: None,
            only: Vec::new(),
            cache: None,
            compile_workers: None,
            memo: kink_flow::memo::MemoUse::On,
            schedule: kink_campaign::ScheduleMode::Full,
            lock: None,
            locked: false,
        },
    )
    .0;
    let refused = row(&full, "thrice");
    assert_eq!(
        (&refused["status"], &refused["reason"]),
        (&Value::from("error"), &Value::from("grammar-not-run")),
        "{refused:#}"
    );
    assert!(
        refused["detail"].as_str().unwrap().contains("macro"),
        "{refused:#}"
    );
    assert_eq!(
        row(&full, "plus-becomes-minus")["status"],
        "killed",
        "{full:#}"
    );
}

/// PJ-34 (U34c): under a `[stop]` the baseline's run of `1 + 2` reaches, the baseline accepts
/// the case, so a mutant that rejects it at parse is killed by it, direction `mutant-rejects`,
/// with no run (`killer_source` `reparse`); an ambiguous text is a rejection (dropping `left`
/// from the group of `+` makes `1 + 2 + 3` ambiguous); a case stating that it is
/// rejected at parse is parsed: still rejected, it agrees, and parsed by the mutant (a new
/// alternative `plus`), it is left to the mutant's run alone (U34c3), which this mutant does not
/// make: its fresh constructor leaves claims unbacked (`unsupported-claims`), so it runs no
/// program, of O or alone, and the row is `unknown` with that reason; where the reparse already
/// kills, the stated case is not run; a mutant that resolves and does not compile is
/// `not-admitted`, as for a rule mutation, even where a case's reparse would kill it.
#[test]
fn a_grammar_mutant_that_rejects_an_accepted_case_is_killed() {
    use serde_json::json;
    let dir = scratch("run-grammar-stop");
    write(&dir.join("calc.k"), CALC_K);
    write(
        &dir.join("FLOW.toml"),
        "[spec]\nentry = \"calc.k\"\nmain_module = \"CALC\"\nsyntax_module = \"CALC-SYNTAX\"\n\n\
         [stop]\nbefore = [\"CALC.add\"]\n\n\
         [[program]]\nid = \"add\"\ntext = \"1 + 2\"\n\n\
         [[program]]\nid = \"inline\"\ntext = \"1 + 2 + 3\"\n\n\
         [[program]]\nid = \"bad\"\ntext = \"1 plus 2\"\nexpect = { rejected = \"parse\" }\n",
    );
    let manifest = dir.join("FLOW.toml");
    let mutations = dir.join("MUTATIONS.toml");
    write(
        &mutations,
        &[
            one_edit(
                "plus-literal",
                "  production = \"add\"\n  find = \"\\\"+\\\"\"\n  replace = \"\\\"plus\\\"\"",
            ),
            one_edit(
                "merge-groups",
                "  production = \"mul\"\n  find = \"> left:\\n                 Exp \\\"+\\\"\"\n  \
                 replace = \"| Exp \\\"+\\\"\"",
            ),
            one_edit(
                "plus-broken",
                "  production = \"add\"\n  find = \"\\\"+\\\" Exp [strict, symbol(add)]\"\n  \
                 replace = \"\\\"plus\\\" Exp [strict(3), symbol(add)]\"",
            ),
            one_edit(
                "drop-left",
                "  production = \"add\"\n  find = \"> left:\\n                 Exp \\\"+\\\"\"\n  \
                 replace = \">\\n                 Exp \\\"+\\\"\"",
            ),
            one_edit(
                "plus-alternative",
                "  production = \"add\"\n  find = \"Exp \\\"+\\\" Exp [strict, symbol(add)]\"\n  \
                 replace = \"Exp \\\"+\\\" Exp [strict, symbol(add)]\\n               | Exp \
                 \\\"plus\\\" Exp [strict, symbol(plus)]\"",
            ),
        ]
        .concat(),
    );
    let (check, _) = check_list(&manifest, &mutations, None);
    for id in [
        "plus-literal",
        "plus-broken",
        "merge-groups",
        "drop-left",
        "plus-alternative",
    ] {
        assert_eq!(row(&check, id)["outcome"], "ok", "{id}: {check:#}");
    }
    let (document, _) = flow_support::corpus_run(&manifest, &mutations);
    // A mutant that does not compile is `not-admitted`, whatever its cases parse to.
    let broken = row(&document, "plus-broken");
    assert_eq!(
        (&broken["status"], &broken["reason"], &broken["killer"]),
        (&json!("not-admitted"), &json!("rejected"), &Value::Null),
        "{broken:#}"
    );
    let plus = row(&document, "plus-literal");
    assert_eq!(
        killed_as(plus),
        json!(["killed", "add", "mutant-rejects"]),
        "{plus:#}"
    );
    assert_eq!(plus["killer_source"], "reparse", "{plus:#}");
    // The stated case parses under this mutant too; the kill does not need it.
    assert_eq!(
        reparsed(plus),
        json!([
            ["add", "rejected", "killed"],
            ["inline", "rejected", "killed"],
            ["bad", "different", "run"]
        ]),
        "{plus:#}"
    );
    assert_eq!(plus["grammar"][2]["stated"], "parse", "{plus:#}");
    assert!(plus["executed"].as_array().unwrap().is_empty(), "{plus:#}");
    // Merging the groups of `*` and `+` keeps both texts' terms (the merged group is `left`):
    // every case parses alike, and the mutant's runs of them agree.
    let merged = row(&document, "merge-groups");
    assert_eq!(
        killed_as(merged),
        json!(["survived", null, null]),
        "{merged:#}"
    );
    assert_eq!(
        reparsed(merged),
        json!([
            ["add", "same", "run"],
            ["inline", "same", "run"],
            ["bad", "rejected", "agree"]
        ]),
        "{merged:#}"
    );
    // Without `left`, `1 + 2 + 3` is ambiguous: a rejection.
    let dropped = row(&document, "drop-left");
    assert_eq!(
        killed_as(dropped),
        json!(["killed", "inline", "mutant-rejects"]),
        "{dropped:#}"
    );
    assert_eq!(
        reparsed(dropped),
        json!([
            ["add", "same", "run"],
            ["inline", "rejected", "killed"],
            ["bad", "rejected", "agree"]
        ]),
        "{dropped:#}"
    );
    let detail = dropped["grammar"][1]["detail"].as_str().unwrap();
    assert!(detail.contains("Parsing ambiguity"), "{dropped:#}");
    let alternative = row(&document, "plus-alternative");
    assert_eq!(
        (&alternative["status"], &alternative["reason"]),
        (&json!("unknown"), &json!("unsupported-claims")),
        "{alternative:#}"
    );
    assert_eq!(
        alternative["grammar"][2]["reason"], "grammar-mutant-acceptance-not-decided",
        "{alternative:#}"
    );
    let detail = alternative["grammar"][2]["detail"].as_str().unwrap();
    assert!(detail.contains("`unsupported-claims`"), "{alternative:#}");
    assert!(
        alternative["executed"].as_array().unwrap().is_empty(),
        "{alternative:#}"
    );
    assert_eq!(
        reparsed(alternative),
        json!([
            ["add", "same", "run"],
            ["inline", "same", "run"],
            ["bad", "different", "unknown"]
        ]),
        "{alternative:#}"
    );
    // The survivor is the one grammar target; the stated case it rejects too is named.
    assert_eq!(
        document["grammar_targets"]
            .as_array()
            .unwrap()
            .iter()
            .map(|target| (&target["mutation"], &target["rejected"]))
            .collect::<Vec<_>>(),
        [(&json!("merge-groups"), &json!(["bad"]))],
        "{document:#}"
    );
    let (warm, _) = flow_support::corpus_run(&manifest, &mutations);
    for id in [
        "plus-literal",
        "merge-groups",
        "drop-left",
        "plus-alternative",
    ] {
        assert_eq!(
            grammar_verdict(row(&warm, id)),
            grammar_verdict(row(&document, id)),
            "{id}: {warm:#}"
        );
    }
    assert_eq!(
        warm["grammar_targets"], document["grammar_targets"],
        "{warm:#}"
    );
}

/// `kink-flow run` through the library with the lock `lock` (written unless `locked`).
fn locked_run(manifest: &Path, mutations: &Path, lock: &Path, locked: bool) -> (Value, bool) {
    kink_flow::search::run(
        &FlowManifest::read(manifest).unwrap(),
        &kink_flow::MutationList::read(mutations).unwrap(),
        &kink_flow::search::RunOptions {
            legacy_lock: None,
            only: Vec::new(),
            cache: None,
            compile_workers: None,
            memo: kink_flow::memo::MemoUse::On,
            schedule: kink_campaign::ScheduleMode::FirstKill,
            lock: Some(lock.to_owned()),
            locked,
        },
    )
}

/// PJ-34 (U34c3): a case stating that the specification rejects it at parse, which a grammar
/// mutant parses, is run on the mutant alone from the mutant's term, and kills it, direction
/// `mutant-accepts`, where the mutant's whole pipeline accepts it: under `[stop] before
/// CALC.add`, the mutant that spells `+` as `plus` parses `1 plus 2` to `1 + 2`, whose run
/// stops before `add`, an accepted end. No program of O (`2 * 3`, parsed alike, runs and
/// agrees) kills it, so the stated case is the killer (`killer_source` `alone`), with an
/// executed entry of its run alone. Without the `[stop]` the same run ends on its own, an end
/// calc declares no class of, so whether the mutant accepts it is not decided: `unknown`. A warm
/// run gives the cold run's rows. With `1 + 2` in O, the reparse kills first (`mutant-rejects`,
/// O before the stated cases), unless the lock records the stated case as the killer, which is
/// kept while it kills; the lock then converges (`--locked`).
#[test]
fn a_grammar_mutant_that_accepts_a_rejected_case_is_killed_by_its_run_alone() {
    use serde_json::json;
    let dir = scratch("run-grammar-accepts");
    write(&dir.join("calc.k"), CALC_K);
    let flow = |stop: &str, programs: &str| {
        format!(
            "[spec]\nentry = \"calc.k\"\nmain_module = \"CALC\"\nsyntax_module = \"CALC-SYNTAX\"\n\n\
             {stop}{programs}[[program]]\nid = \"bad\"\ntext = \"1 plus 2\"\n\
             expect = {{ rejected = \"parse\" }}\n"
        )
    };
    let stop = "[stop]\nbefore = [\"CALC.add\"]\n\n";
    let mul = "[[program]]\nid = \"mul\"\ntext = \"2 * 3\"\n\n";
    let manifest = dir.join("FLOW.toml");
    write(&manifest, &flow(stop, mul));
    let mutations = dir.join("MUTATIONS.toml");
    write(
        &mutations,
        &one_edit(
            "plus-literal",
            "  production = \"add\"\n  find = \"\\\"+\\\"\"\n  replace = \"\\\"plus\\\"\"",
        ),
    );
    let (check, _) = check_list(&manifest, &mutations, None);
    assert_eq!(row(&check, "plus-literal")["outcome"], "ok", "{check:#}");
    let (document, _) = flow_support::corpus_run(&manifest, &mutations);
    let plus = row(&document, "plus-literal");
    assert_eq!(
        killed_as(plus),
        json!(["killed", "bad", "mutant-accepts"]),
        "{plus:#}"
    );
    assert_eq!(plus["killer_source"], "alone", "{plus:#}");
    assert_eq!(plus["rules"], Value::Null, "{plus:#}");
    assert_eq!(
        reparsed(plus),
        json!([["mul", "same", "run"], ["bad", "different", "killed"]]),
        "{plus:#}"
    );
    assert_eq!(
        plus["grammar"][1]["direction"], "mutant-accepts",
        "{plus:#}"
    );
    let entries = plus["executed"].as_array().unwrap();
    let alone = entries.iter().find(|entry| entry["alone"] == true).unwrap();
    assert_eq!(
        (&alone["program"], &alone["outcome"], &alone["acceptance"]),
        (&json!("bad"), &json!("distinguish"), &json!("accepted")),
        "{plus:#}"
    );
    assert!(
        entries
            .iter()
            .any(|entry| entry["program"] == "mul" && entry["outcome"] == "agree"),
        "{plus:#}"
    );
    let calls = plus["calls"].as_array().unwrap();
    assert_eq!(
        calls.last().unwrap(),
        &json!({"programs": ["bad"], "status": "killed", "alone": true}),
        "{plus:#}"
    );
    assert_eq!(
        plus["calls"].as_array().unwrap().len(),
        plus["call_wall_ms"].as_array().unwrap().len()
    );
    // Warm, O is served from the outcome cache and the stated case runs alone again.
    let (warm, _) = flow_support::corpus_run(&manifest, &mutations);
    assert_eq!(
        grammar_verdict(row(&warm, "plus-literal")),
        grammar_verdict(plus),
        "{warm:#}"
    );
    // Without the stop, the run alone ends on its own: not decided.
    write(&manifest, &flow("", mul));
    let (unstopped, _) = flow_support::corpus_run(&manifest, &mutations);
    let open = row(&unstopped, "plus-literal");
    assert_eq!(
        (&open["status"], &open["reason"], &open["killer"]),
        (
            &json!("unknown"),
            &json!("grammar-mutant-acceptance-not-decided"),
            &Value::Null
        ),
        "{open:#}"
    );
    assert_eq!(
        reparsed(open),
        json!([["mul", "same", "run"], ["bad", "different", "unknown"]]),
        "{open:#}"
    );
    // O before the stated cases, the recorded killer first.
    let add = "[[program]]\nid = \"add\"\ntext = \"1 + 2\"\n\n";
    write(&manifest, &flow(stop, add));
    let lock = dir.join("kink.lock");
    let (first, _) = locked_run(&manifest, &mutations, &lock, false);
    let plus = row(&first, "plus-literal");
    assert_eq!(
        killed_as(plus),
        json!(["killed", "add", "mutant-rejects"]),
        "{plus:#}"
    );
    assert_eq!(plus["grammar"][1]["verdict"], "run", "{plus:#}");
    let written = std::fs::read_to_string(&lock).unwrap();
    let recorded = "id = \"plus-literal\"\nstatus = \"killed\"\nkiller = \"add\"";
    assert!(written.contains(recorded), "{written}");
    write(
        &lock,
        &written.replace(
            recorded,
            "id = \"plus-literal\"\nstatus = \"killed\"\nkiller = \"bad\"",
        ),
    );
    let (kept, _) = locked_run(&manifest, &mutations, &lock, false);
    let plus = row(&kept, "plus-literal");
    assert_eq!(
        killed_as(plus),
        json!(["killed", "bad", "mutant-accepts"]),
        "{plus:#}"
    );
    assert_eq!(
        (
            &plus["killer_source"],
            &plus["recorded_killer"],
            &plus["killer_change"]
        ),
        (&json!("alone"), &json!("bad"), &Value::Null),
        "{plus:#}"
    );
    assert_eq!(plus["unusable_killer"], Value::Null, "{plus:#}");
    let (locked, _) = locked_run(&manifest, &mutations, &lock, true);
    assert_eq!(
        locked["lock"]["status"], "unchanged",
        "{:#}",
        locked["lock"]
    );
    // A recorded stated killer that no longer kills (no stop: not decided) gives way, and the
    // row names why.
    write(&manifest, &flow("", add));
    let (gone, _) = locked_run(&manifest, &mutations, &lock, false);
    let plus = row(&gone, "plus-literal");
    assert_eq!(plus["killer"], Value::Null, "{plus:#}");
    assert_eq!(plus["killer_change"], "no-longer-kills", "{plus:#}");
}

const GRAMMAR_K: &str = include_str!("../../../testdata/k/grammar.k");

const GRAMMAR_SET: &str = "[[mutation]]\nid = \"grammar\"\ngrammar = \"default\"\n";

/// The ids of the rows of `document` a generated set gave, in row order.
#[track_caller]
fn generated_ids(document: &Value) -> Vec<String> {
    document["mutations"]
        .as_array()
        .unwrap_or_else(|| panic!("{document:#}"))
        .iter()
        .filter(|row| row.get("generated").is_some())
        .map(|row| row["id"].as_str().unwrap().to_owned())
        .collect()
}

/// PJ-34 (U34h): `grammar = "default"` expands, in `check`, into one row per patch the default
/// grammar operator set generates over grammar.k's syntax module, after the written mutations:
/// each resolves (a `grammar` rules entry, its site's text before and a description after), has
/// its `generated` member and an id built from the form and the site, never from a sentence
/// index. The set's summary lists the forms in the default set's order with their rows, and the
/// syntax module's import closure: a production of the main module, which no program text is
/// parsed with, gives no row. Checking again gives the same rows; an edit elsewhere (a
/// production of a new sort first in the syntax module, which moves every sentence index of
/// the module, and a rule) keeps every earlier id, and adds the new sort's rows.
#[test]
fn a_generated_grammar_set_expands_into_rows_whose_ids_survive_an_edit_elsewhere() {
    use serde_json::json;
    let dir = scratch("grammar-set-check");
    // A production in a module the syntax module imports gives rows; one in the main module,
    // which the syntax module does not import, gives none.
    let definition = GRAMMAR_K
        .replace(
            "  rule [run]:",
            "  syntax Val ::= \"nil\" \"!\" [symbol(nil)]\n  rule [run]:",
        )
        .replace(
            "module GRAMMAR-SYNTAX\n",
            "module GRAMMAR-EXTRA\n  syntax Word ::= \"w\" \"?\" [symbol(word)]\nendmodule\n\n\
             module GRAMMAR-SYNTAX\n  imports GRAMMAR-EXTRA\n",
        );
    write(&dir.join("grammar.k"), &definition);
    write(
        &dir.join("FLOW.toml"),
        "[spec]\nentry = \"grammar.k\"\nmain_module = \"GRAMMAR\"\n\
         syntax_module = \"GRAMMAR-SYNTAX\"\n\n[[program]]\nid = \"print\"\n\
         text = \"print 1 + 2 ;\"\n",
    );
    let manifest = dir.join("FLOW.toml");
    let mutations = dir.join("MUTATIONS.toml");
    write(
        &mutations,
        &[
            one_edit(
                "plus-literal",
                "  production = \"add\"\n  find = \"\\\"+\\\"\"\n  replace = \"\\\"plus\\\"\"",
            ),
            GRAMMAR_SET.to_owned(),
        ]
        .concat(),
    );
    let (check, _) = check_list(&manifest, &mutations, None);
    assert_eq!(check["version"], 21, "{check:#}");
    let rows = check["mutations"]
        .as_array()
        .unwrap_or_else(|| panic!("{check:#}"));
    assert_eq!(rows[0]["id"], "plus-literal", "{check:#}");
    assert!(rows[0].get("generated").is_none(), "{check:#}");
    let ids = generated_ids(&check);
    assert_eq!(ids.len(), rows.len() - 1, "{check:#}");
    for id in [
        "grammar/alternative-without-terminal/GRAMMAR-SYNTAX/add/1",
        "grammar/alternative-without-terminal/GRAMMAR-SYNTAX/print/0",
        "grammar/alternative-without-terminal/GRAMMAR-EXTRA/word/0",
        "grammar/alternative-without-terminal/GRAMMAR-EXTRA/word/1",
    ] {
        assert!(ids.iter().any(|row| row == id), "{id}: {ids:#?}");
    }
    assert!(
        ids.iter().any(
            |id| id.starts_with("grammar/drop-anchor/GRAMMAR-SYNTAX/Tag-token-")
                && id.ends_with("/end")
        ),
        "{ids:#?}"
    );
    assert!(
        ids.iter()
            .any(|id| id.starts_with("grammar/loosen-regex/GRAMMAR-SYNTAX/lexical-Digit/")),
        "{ids:#?}"
    );
    assert!(
        !ids.iter().any(|id| id.contains("/GRAMMAR/")),
        "no row outside the syntax module's closure: {ids:#?}"
    );
    let distinct = ids.iter().collect::<std::collections::BTreeSet<_>>();
    assert_eq!(distinct.len(), ids.len(), "{ids:#?}");
    let add = row(
        &check,
        "grammar/alternative-without-terminal/GRAMMAR-SYNTAX/add/1",
    );
    assert_eq!(add["outcome"], "ok", "{add:#}");
    assert_eq!(add["rules"][0]["kind"], "grammar", "{add:#}");
    assert_eq!(add["rules"][0]["label"], "add", "{add:#}");
    assert_eq!(
        add["rules"][0]["before"], "Exp \"+\" Exp [left, symbol(add)]",
        "{add:#}"
    );
    assert_eq!(
        add["rules"][0]["after"],
        "Exp \"+\" Exp [left, symbol(add)]\n\
         syntax Exp ::= Exp Exp [symbol(add-kink-without-1), macro]\n\
         rule `add-kink-without-1`(X0:Exp, X1:Exp) => `add`(X0:Exp, X1:Exp)",
        "{add:#}"
    );
    assert_eq!(
        add["generated"],
        json!({
            "set": "grammar",
            "grammar": "default",
            "version": "kink-flow/grammar-set/v2",
            "form": "alternative-without-terminal",
            "effect": "widening",
            "site": "add",
            "variant": "1",
        }),
        "{add:#}"
    );
    assert!(
        add["misunderstanding"]
            .as_str()
            .unwrap()
            .contains("without its literal \"+\" also parses, as a macro of the production"),
        "{add:#}"
    );
    let sets = check["grammar_sets"].as_array().unwrap();
    assert_eq!(sets.len(), 1, "{check:#}");
    assert_eq!(
        (&sets[0]["id"], &sets[0]["modules"], &sets[0]["refusal"]),
        (
            &json!("grammar"),
            &json!(["GRAMMAR-EXTRA", "GRAMMAR-SYNTAX"]),
            &Value::Null
        ),
        "{check:#}"
    );
    let forms = sets[0]["forms"].as_array().unwrap();
    assert_eq!(
        forms.iter().map(|form| &form["form"]).collect::<Vec<_>>(),
        [
            "alternative-without-terminal",
            "loosen-regex",
            "narrow-regex",
            "drop-anchor"
        ],
        "{check:#}"
    );
    assert!(
        !ids.iter().any(|id| id.contains("merge-alternative")),
        "{ids:#?}"
    );
    let summarised = forms
        .iter()
        .flat_map(|form| form["rows"].as_array().unwrap())
        .map(|id| id.as_str().unwrap().to_owned())
        .collect::<Vec<_>>();
    assert_eq!(summarised, ids, "{check:#}");
    // Deterministic: the same rows again.
    let (again, _) = check_list(&manifest, &mutations, None);
    assert_eq!(again["mutations"], check["mutations"], "{again:#}");
    // An edit elsewhere keeps every id.
    let edited = definition
        .replace(
            "  imports GRAMMAR-EXTRA\n",
            "  imports GRAMMAR-EXTRA\n  syntax Decl ::= \"let\" Exp \"!\" [symbol(decl)]\n",
        )
        .replace("  rule [run]:", "  rule [nop]: tag _T => .K\n  rule [run]:");
    assert_ne!(edited, definition);
    write(&dir.join("grammar.k"), &edited);
    let (after, _) = check_list(&manifest, &mutations, None);
    let kept = generated_ids(&after);
    for id in &ids {
        assert!(kept.contains(id), "{id} is kept: {kept:#?}");
        assert_eq!(row(&after, id)["outcome"], "ok", "{after:#}");
    }
    assert!(
        kept.iter()
            .any(|id| id == "grammar/alternative-without-terminal/GRAMMAR-SYNTAX/decl/2"),
        "{kept:#?}"
    );
}

/// PJ-34 (U34h): `run` judges every row a generated set expands into by the grammar search, as
/// a written grammar mutation (calc's three productions with a literal, each given an
/// alternative without it, a macro of the production inserted after it): each row is a
/// judged grammar row (`grammar`, its `generated` member), none refused, and the lock records each
/// under its id, which a warm `--locked` run confirms. `--only` names the set (every row) or one
/// row; the command line accepts both before the specification is admitted.
#[test]
fn run_judges_each_row_of_a_generated_grammar_set_and_locks_it() {
    let dir = calc_copy("grammar-set-run");
    let manifest = dir.join("FLOW.toml");
    let mutations = dir.join("MUTATIONS.toml");
    write(
        &mutations,
        &[one_edit("add-becomes-sub", ARITH), GRAMMAR_SET.to_owned()].concat(),
    );
    let expected = [
        "grammar/alternative-without-terminal/CALC-SYNTAX/mul/1",
        "grammar/alternative-without-terminal/CALC-SYNTAX/add/1",
        "grammar/alternative-without-terminal/CALC-SYNTAX/sub/1",
    ];
    let lock = dir.join("kink.lock");
    let (document, _) = locked_run(&manifest, &mutations, &lock, false);
    assert_eq!(generated_ids(&document), expected, "{document:#}");
    assert_eq!(
        row(&document, "add-becomes-sub")["status"],
        "killed",
        "{document:#}"
    );
    // Each row reached the grammar search (its cases were parsed again), past the supplied
    // generation an anchored insertion needs, and a verdict of its runs: an inserted
    // constructor's affected labels that calc does not compile (the prelude's stream cells) are
    // left out of the consistency check, not refused (FX2, U34h Q1).
    for id in expected {
        let generated = row(&document, id);
        assert!(generated["grammar"].is_array(), "{generated:#}");
        assert!(
            matches!(
                generated["status"].as_str(),
                Some("killed" | "survived" | "unknown")
            ),
            "{generated:#}"
        );
        assert_eq!(generated["generated"]["set"], "grammar", "{generated:#}");
    }
    let text = std::fs::read_to_string(&lock).unwrap();
    for id in expected {
        assert!(text.contains(&format!("id = \"{id}\"")), "{id}: {text}");
    }
    let (warm, _) = locked_run(&manifest, &mutations, &lock, true);
    assert_eq!(warm["lock"]["status"], "unchanged", "{warm:#}");
    for id in expected {
        assert_eq!(
            grammar_verdict(row(&warm, id)),
            grammar_verdict(row(&document, id)),
            "{id}: {warm:#}"
        );
    }
    let only = |ids: &[&str]| {
        kink_flow::search::run(
            &FlowManifest::read(&manifest).unwrap(),
            &kink_flow::MutationList::read(&mutations).unwrap(),
            &kink_flow::search::RunOptions {
                legacy_lock: None,
                only: ids.iter().map(|id| (*id).to_owned()).collect(),
                cache: None,
                compile_workers: None,
                memo: kink_flow::memo::MemoUse::On,
                schedule: kink_campaign::ScheduleMode::FirstKill,
                lock: Some(lock.clone()),
                locked: true,
            },
        )
        .0
    };
    let set = only(&["grammar"]);
    assert_eq!(generated_ids(&set), expected, "{set:#}");
    assert_eq!(set["mutations"].as_array().unwrap().len(), 3, "{set:#}");
    assert_eq!(set["lock"]["changes"], serde_json::json!([]), "{set:#}");
    let one = only(&[expected[1]]);
    assert_eq!(generated_ids(&one), [expected[1]], "{one:#}");
    // The command line accepts the set's id and a row's id under it, and refuses another.
    let parse = |only: &str| {
        kink_flow::FlowCommand::parse(
            "run",
            kink_flow::cli::CommandFiles {
                mutations: Some(mutations.clone()),
                ..kink_flow::cli::CommandFiles::default()
            },
            &["--only".to_owned(), only.to_owned()],
        )
    };
    for id in ["grammar", expected[0]] {
        assert!(parse(id).is_ok(), "{id}");
    }
    assert!(parse("grammar-x").is_err());
}

/// PJ-34 (U34h): a generated token narrowing is killed as a written one would be. grammar.k's
/// default set narrows `Num`'s regex `{Digit}+([.]{Digit}*)?` to `{Digit}+([.]{Digit}+)?`, so
/// `print 1. ;`, which the specification parses (its run stops before `run`, an accepted end),
/// no longer parses under the mutant: killed, `mutant-rejects`, by that case. `--only` names it
/// and an inserted alternative, and only they run.
#[test]
fn a_generated_token_narrowing_is_killed_by_the_case_it_no_longer_parses() {
    let dir = scratch("grammar-set-narrow");
    write(&dir.join("grammar.k"), GRAMMAR_K);
    let manifest = dir.join("FLOW.toml");
    write(
        &manifest,
        "[spec]\nentry = \"grammar.k\"\nmain_module = \"GRAMMAR\"\n\
         syntax_module = \"GRAMMAR-SYNTAX\"\n\n[stop]\nbefore = [\"GRAMMAR.run\"]\n\n\
         [[program]]\nid = \"sum\"\ntext = \"print 1 + 2 ;\"\n\n\
         [[program]]\nid = \"dot\"\ntext = \"print 1. ;\"\n",
    );
    let mutations = dir.join("MUTATIONS.toml");
    write(&mutations, GRAMMAR_SET);
    let narrow = "grammar/narrow-regex/GRAMMAR-SYNTAX/Num-token-0f0238bc/6.0";
    let inserted = "grammar/alternative-without-terminal/GRAMMAR-SYNTAX/print/2";
    let (document, _) = kink_flow::search::run(
        &FlowManifest::read(&manifest).unwrap(),
        &kink_flow::MutationList::read(&mutations).unwrap(),
        &kink_flow::search::RunOptions {
            legacy_lock: None,
            only: vec![narrow.to_owned(), inserted.to_owned()],
            cache: None,
            compile_workers: None,
            memo: kink_flow::memo::MemoUse::On,
            schedule: kink_campaign::ScheduleMode::FirstKill,
            lock: None,
            locked: false,
        },
    );
    assert_eq!(generated_ids(&document), [inserted, narrow], "{document:#}");
    // The inserted alternative reaches the grammar search too, and a verdict (FX2, U34h Q1).
    let insertion = row(&document, inserted);
    assert!(insertion["grammar"].is_array(), "{insertion:#}");
    assert!(
        matches!(
            insertion["status"].as_str(),
            Some("killed" | "survived" | "unknown")
        ),
        "{insertion:#}"
    );
    let row = row(&document, narrow);
    assert_eq!(
        killed_as(row),
        serde_json::json!(["killed", "dot", "mutant-rejects"]),
        "{row:#}"
    );
    assert_eq!(row["generated"]["effect"], "token-narrowing", "{row:#}");
}

/// `run --only ID` over a flow and a list, with no lock.
fn run_only(manifest: &Path, mutations: &Path, only: &[&str]) -> Value {
    kink_flow::search::run(
        &FlowManifest::read(manifest).unwrap(),
        &kink_flow::MutationList::read(mutations).unwrap(),
        &kink_flow::search::RunOptions {
            legacy_lock: None,
            only: only.iter().map(|id| (*id).to_owned()).collect(),
            cache: None,
            compile_workers: None,
            memo: kink_flow::memo::MemoUse::On,
            schedule: kink_campaign::ScheduleMode::FirstKill,
            lock: None,
            locked: false,
        },
    )
    .0
}

/// PJ-35 (U35d): `alternative-without-terminal` inserts the copy of `print Exp ;` without its `;`
/// as a macro of `print`, so `print 1 + 2` parses to `print 1 + 2 ;`'s own configuration once
/// macros are expanded. The case written with the `;` reparses `same` (the reparse compares
/// configurations after expansion). Under `[stop] before GRAMMAR.run` acceptance is decided, so
/// the malformed case `print 1 + 2`, which the specification rejects at parse and which is the
/// whole program (executed), kills the mutant: its run alone reaches the stop, accepted,
/// direction `mutant-accepts`, `killer_source` `alone`. Without the `[stop]` the same row is
/// `unknown`: plain K declares no accepted end.
#[test]
fn a_macro_alternative_is_killed_by_an_executed_malformed_case_where_acceptance_is_decided() {
    use serde_json::json;
    let dir = scratch("grammar-set-macro");
    write(&dir.join("grammar.k"), GRAMMAR_K);
    let manifest = dir.join("FLOW.toml");
    let flow = |stop: &str| {
        format!(
            "[spec]\nentry = \"grammar.k\"\nmain_module = \"GRAMMAR\"\n\
             syntax_module = \"GRAMMAR-SYNTAX\"\n\n{stop}\
             [[program]]\nid = \"sum\"\ntext = \"print 1 + 2 ;\"\n\n\
             [[program]]\nid = \"no-semicolon\"\ntext = \"print 1 + 2\"\n\
             expect = {{ rejected = \"parse\" }}\n"
        )
    };
    write(&manifest, &flow("[stop]\nbefore = [\"GRAMMAR.run\"]\n\n"));
    let mutations = dir.join("MUTATIONS.toml");
    write(&mutations, GRAMMAR_SET);
    let semicolon = "grammar/alternative-without-terminal/GRAMMAR-SYNTAX/print/2";
    let document = run_only(&manifest, &mutations, &[semicolon]);
    let killed = row(&document, semicolon);
    assert_eq!(
        killed_as(killed),
        json!(["killed", "no-semicolon", "mutant-accepts"]),
        "{killed:#}"
    );
    assert_eq!(killed["killer_source"], "alone", "{killed:#}");
    assert_eq!(
        reparsed(killed),
        json!([
            ["sum", "same", "run"],
            ["no-semicolon", "different", "killed"]
        ]),
        "{killed:#}"
    );
    assert_eq!(
        killed["removed_claims"],
        json!({"removed": [], "unsupported": []}),
        "{killed:#}"
    );
    // Plain K without `[stop]`: whether the mutant's run accepts is not decided.
    write(&manifest, &flow(""));
    let document = run_only(&manifest, &mutations, &[semicolon]);
    let open = row(&document, semicolon);
    assert_eq!(
        (&open["status"], &open["reason"], &open["killer"]),
        (
            &json!("unknown"),
            &json!("grammar-mutant-acceptance-not-decided"),
            &Value::Null
        ),
        "{open:#}"
    );
}

/// PJ-35 (U35d): `grammar = { forms = [...] }` names the forms a set generates, here the seven
/// the default leaves out, so grammar.k gives rows of each and none of the default's. Every row
/// resolves; the relation sites and the literal and associativity variants are keyed by their
/// content (`priority-<hex>`, `<assoc>-<hex>`, `<item>.<literal>`, the associativity set,
/// `whole` for a deletion), so an edit elsewhere that adds a literal of the sort and moves every
/// sentence index of the syntax module keeps every id. `generated.grammar` and the summary's
/// `grammar` repeat the value as written.
#[test]
fn a_set_names_its_forms_and_their_ids_are_kept_by_an_edit_elsewhere() {
    use serde_json::json;
    let dir = scratch("grammar-set-forms");
    write(&dir.join("grammar.k"), GRAMMAR_K);
    let manifest = dir.join("FLOW.toml");
    write(
        &manifest,
        "[spec]\nentry = \"grammar.k\"\nmain_module = \"GRAMMAR\"\n\
         syntax_module = \"GRAMMAR-SYNTAX\"\n\n[[program]]\nid = \"print\"\n\
         text = \"print 1 + 2 ;\"\n",
    );
    let mutations = dir.join("MUTATIONS.toml");
    let off = [
        "drop-terminal",
        "change-terminal",
        "delete-production",
        "merge-priority-groups",
        "swap-priority-groups",
        "change-associativity",
        "delete-relation",
    ];
    // Written in another order: the forms are taken in kink-patch's order.
    let mut written = off.to_vec();
    written.reverse();
    write(
        &mutations,
        &format!(
            "[[mutation]]\nid = \"g\"\ngrammar = {{ forms = [{}] }}\n",
            written
                .iter()
                .map(|form| format!("\"{form}\""))
                .collect::<Vec<_>>()
                .join(", ")
        ),
    );
    let (check, _) = check_list(&manifest, &mutations, None);
    let set = &check["grammar_sets"][0];
    assert_eq!(set["grammar"], json!({ "forms": off }), "{check:#}");
    assert_eq!(
        set["forms"]
            .as_array()
            .unwrap()
            .iter()
            .map(|form| form["form"].as_str().unwrap())
            .collect::<Vec<_>>(),
        off,
        "{check:#}"
    );
    let ids = generated_ids(&check);
    for form in off {
        assert!(
            ids.iter().any(|id| id.starts_with(&format!("g/{form}/"))),
            "{form}: {ids:#?}"
        );
    }
    for row in check["mutations"].as_array().unwrap() {
        assert_eq!(row["outcome"], "ok", "{row:#}");
        assert_eq!(
            row["generated"]["grammar"],
            json!({ "forms": off }),
            "{row:#}"
        );
        assert!(
            !row["id"].as_str().unwrap().contains("sentence-"),
            "{row:#}"
        );
    }
    for id in [
        "g/drop-terminal/GRAMMAR-SYNTAX/print/2",
        "g/change-terminal/GRAMMAR-SYNTAX/print/0.tag",
        "g/delete-production/GRAMMAR-SYNTAX/tag/whole",
    ] {
        assert!(ids.iter().any(|row| row == id), "{id}: {ids:#?}");
    }
    let keyed = |prefix: &str| {
        ids.iter()
            .filter(|id| id.starts_with(prefix))
            .cloned()
            .collect::<Vec<_>>()
    };
    let associativity = keyed("g/change-associativity/GRAMMAR-SYNTAX/left-");
    assert!(
        associativity.iter().any(|id| id.ends_with("/right"))
            && associativity.iter().any(|id| id.ends_with("/non-assoc")),
        "{ids:#?}"
    );
    assert_eq!(
        keyed("g/delete-relation/GRAMMAR-SYNTAX/priority-").len(),
        2,
        "the block's priority and `syntax priority mul > neg`: {ids:#?}"
    );
    let swap = row(&check, &keyed("g/swap-priority-groups/")[0]);
    assert!(
        swap["rules"][0]["after"]
            .as_str()
            .unwrap()
            .starts_with("syntax priority "),
        "{swap:#}"
    );
    let deleted = row(&check, "g/delete-production/GRAMMAR-SYNTAX/tag/whole");
    assert_eq!(deleted["rules"][0]["after"], "(deleted)", "{deleted:#}");
    // An edit elsewhere: a production first in the syntax module (every sentence index moves)
    // with a literal of Stmt, which kink-patch's choice index of `change-terminal` counts.
    write(
        &dir.join("grammar.k"),
        &GRAMMAR_K.replace(
            "module GRAMMAR-SYNTAX\n",
            "module GRAMMAR-SYNTAX\n  syntax Stmt ::= \"skip\" \"!\" [symbol(skip)]\n",
        ),
    );
    let (after, _) = check_list(&manifest, &mutations, None);
    let kept = generated_ids(&after);
    for id in &ids {
        assert!(kept.contains(id), "{id} is kept: {kept:#?}");
    }
    assert!(
        kept.iter()
            .any(|id| id == "g/change-terminal/GRAMMAR-SYNTAX/print/0.skip"),
        "{kept:#?}"
    );
}

/// PJ-34 (FX2, U34h Q1): a written insertion of a fresh constructor over a definition that
/// imports the prelude reaches a verdict. calc imports INT, so the prelude's stream modules
/// (`STDIN-STREAM`, `STDOUT-STREAM`) are loaded but not imported: kink-patch's affected labels
/// for `syntax Exp ::= Exp Exp [symbol(juxt)]` include their `initStdinCell` and
/// `initStdoutCell`, which the compiled definition does not declare. They head no compiled
/// equation, so kink-native's admission leaves them out of the checked heads instead of
/// refusing the mutant (`not-admitted`, `inconsistent-mutant`).
#[test]
fn a_written_insertion_over_the_prelude_reaches_a_verdict() {
    let dir = calc_copy("grammar-insertion");
    let manifest = dir.join("FLOW.toml");
    let mutations = dir.join("MUTATIONS.toml");
    write(
        &mutations,
        &one_edit(
            "juxt",
            "  production = \"sub\"\n  find = \"Exp \\\"-\\\" Exp [strict, symbol(sub)]\"\n  \
             replace = \"Exp \\\"-\\\" Exp [strict, symbol(sub)]\\n               | Exp Exp \
             [symbol(juxt)]\"",
        ),
    );
    let (check, _) = check_list(&manifest, &mutations, None);
    assert_eq!(row(&check, "juxt")["outcome"], "ok", "{check:#}");
    let (document, _) = flow_support::corpus_run(&manifest, &mutations);
    let juxt = row(&document, "juxt");
    assert!(juxt["grammar"].is_array(), "{juxt:#}");
    assert!(
        matches!(
            juxt["status"].as_str(),
            Some("killed" | "survived" | "unknown")
        ),
        "{juxt:#}"
    );
    assert_ne!(juxt["reason"], "inconsistent-mutant", "{juxt:#}");
}

/// PJ-34 (FX2): a written deletion of a production a rule still applies leaves the rule's term
/// naming a production the mutant does not declare. Compilation refuses such a mutant (under
/// debug assertions, k-rust's dangling-identity check panics), so the grammar search refuses it
/// first: `not-admitted`, reason `rejected`, the detail naming the application, and nothing
/// compiles or runs.
#[test]
fn a_deleted_production_a_rule_applies_is_not_admitted() {
    use serde_json::json;
    let dir = calc_copy("grammar-delete-applied");
    let manifest = dir.join("FLOW.toml");
    let mutations = dir.join("MUTATIONS.toml");
    write(
        &mutations,
        &one_edit(
            "no-sub",
            "  production = \"sub\"\n  find = \"\\n               | Exp \\\"-\\\" Exp \
             [strict, symbol(sub)]\"\n  replace = \"\"",
        ),
    );
    let (check, _) = check_list(&manifest, &mutations, None);
    assert_eq!(row(&check, "no-sub")["outcome"], "ok", "{check:#}");
    let (document, _) = flow_support::corpus_run(&manifest, &mutations);
    let deleted = row(&document, "no-sub");
    assert_eq!(
        (&deleted["status"], &deleted["reason"], &deleted["killer"]),
        (&json!("not-admitted"), &json!("rejected"), &Value::Null),
        "{deleted:#}"
    );
    let detail = deleted["detail"].as_str().unwrap_or_default();
    assert!(detail.contains("sub"), "{deleted:#}");
    assert!(deleted["grammar"].is_array(), "{deleted:#}");
    assert!(
        deleted["calls"].as_array().unwrap().is_empty(),
        "{deleted:#}"
    );
}

/// PJ-34 (U34h): a KRS flow (one that names a definition, whose front end judges written
/// production edits only) gets no generated row: the set is one refused row, `grammar-set-not-judged`; and a set
/// one of whose rows takes a written mutation's id is one refused row,
/// `grammar-set-id-collision`. Either refusal is in the set's summary.
#[test]
fn a_generated_grammar_set_is_refused_in_a_krs_flow_and_on_an_id_collision() {
    let dir = calc_copy("grammar-set-refused");
    let mut manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
    let loaded =
        kink_corpus::resolver::load_source(&kink_flow::admit::corpus_source(&manifest)).unwrap();
    let taken = "grammar/alternative-without-terminal/CALC-SYNTAX/add/1";
    let list = kink_flow::MutationList::decode(&format!("{}{GRAMMAR_SET}", one_edit(taken, ARITH)))
        .unwrap();
    let refusal = |manifest: &FlowManifest| {
        let check = kink_flow::check_mutations(manifest, &loaded, &list, None);
        let rows = check.value();
        let set = rows
            .as_array()
            .unwrap()
            .iter()
            .find(|row| row["id"] == "grammar")
            .cloned()
            .unwrap_or_else(|| panic!("{rows:#}"));
        assert_eq!(
            rows.as_array().unwrap().len(),
            2,
            "the written mutation and the set's one row: {rows:#}"
        );
        assert_eq!(set["outcome"], "refused", "{set:#}");
        assert_eq!(
            set["refusals"][0]["reason"], check.grammar_sets[0]["refusal"]["reason"],
            "{set:#}"
        );
        set["refusals"][0]["reason"].as_str().unwrap().to_owned()
    };
    assert_eq!(refusal(&manifest), "grammar-set-id-collision");
    manifest.definition = Some("calc:definition".to_owned());
    assert_eq!(refusal(&manifest), "grammar-set-not-judged");
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
    assert_eq!(code, Some(EXIT_YES.into()), "{stderr}");
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
        assert_eq!(code, Some(EXIT_UNASKED.into()), "{args:?}: {stderr}");
    }
}

/// A source edit that changes no behaviour (a rule's variables respelled, a label renamed) leaves
/// authored mutations stale: `run` refuses them, exit 2, and its rendering (the lock's text)
/// keeps each refusal's reason alone, while the detail names what the K says now, so that each
/// edit is re-anchored in one look.
#[test]
fn a_stale_mutation_names_the_current_text_and_the_near_labels() {
    let dir = calc_copy("reanchor");
    let manifest = dir.join("FLOW.toml");
    write(
        &dir.join("calc.k"),
        &CALC_K
            .replace(
                "rule [add]: I1:Int + I2:Int => I1 +Int I2",
                "rule [add]: X1:Int + X2:Int => X1 +Int X2",
            )
            .replace("rule [mul]:", "rule [multiply]:"),
    );
    let mutations = dir.join("stale.toml");
    write(
        &mutations,
        &[
            one_edit("respelled", ARITH),
            one_edit(
                "renamed",
                "  rule = \"mul\"\n  find = \"I1 *Int I2\"\n  replace = \"I1 +Int I2\"",
            ),
        ]
        .concat(),
    );
    let (code, stdout, stderr) = binary(&[
        "run".as_ref(),
        manifest.as_os_str(),
        mutations.as_os_str(),
        "--output".as_ref(),
        "verdicts".as_ref(),
    ]);
    assert_eq!(code, Some(EXIT_UNASKED.into()), "{stdout}{stderr}");
    assert!(
        stdout.ends_with(
            "[[run.mutation]]\nid = \"respelled\"\nstatus = \"invalid-mutation\"\n\
             reason = \"find-not-found\"\n\n[[run.mutation]]\nid = \"renamed\"\n\
             status = \"invalid-mutation\"\nreason = \"unknown-label\"\n"
        ),
        "{stdout}"
    );
    assert!(
        stderr.contains(
            "mutation respelled: invalid-mutation find-not-found: \"I1 +Int I2\" does not occur \
             in CALC.add (calc.k:21); nearest text, 2 edits from find, at calc.k:21: \
             \"X1 +Int X2\"; the rule's text now: \"rule [add]: X1:Int + X2:Int => X1 +Int X2\"\n"
        ),
        "{stderr}"
    );
    assert!(
        stderr.contains(
            "mutation renamed: invalid-mutation unknown-label: no rule is labelled \"mul\", and \
             no label ends with it as a whole component; near labels: CALC.multiply\n"
        ),
        "{stderr}"
    );
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
/// every operand, so `g(0)` is undefined and its run contradicts `g`'s `total` claim. With
/// `flagged`, one more rule that no program applies and the short-circuit analysis flags (`at`,
/// whose result applies `andThenBool` over `10 /Int I`).
fn initial_state_flow_of(name: &str, flagged: bool) -> PathBuf {
    let dir = scratch(name);
    let at = if flagged {
        "  syntax Pgm ::= at(Int) [symbol(at)]\n  \
         rule [at]: <k> at(I) => run(false andThenBool 10 /Int I >Int 0) </k>\n"
    } else {
        ""
    };
    write(
        &dir.join("sc.k"),
        &format!(
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
{at}endmodule
"
        ),
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

/// `check` on SM83's shape: admission reads the short-circuit analysis, which flags `fetch` and
/// `fetch-halt-bug`, and admits the specification and both programs; `spec.short_circuit` names,
/// for each, the rule, `decode` with the equation and the part of it through which it depends on
/// the reading, `andThenBool` and the `bitRangeInt` operand, each with its module, position and
/// compiled id. A flagged rule is no definition exclusion: the campaign runner judges each run of
/// the definition by k-rust's list of that run's short-circuit readings, so whether a program's
/// run is excluded is known only once it runs. So `spec.exclusion` is null, every program is
/// `ok`, and `check` exits 0, with and without `--mutations` (before CF-03 every program was
/// `excluded` at stage `definition` and `check` exited 1).
#[test]
fn a_flagged_definition_names_its_cause_chains_and_passes_check() {
    let dir = scfetch_flow("scfetch");
    let manifest = dir.join("FLOW.toml");
    let (admission, (document, status)) = {
        let manifest = manifest.clone();
        on_stack(move || (admit_manifest(&manifest), check(&manifest)))
    };
    assert!(admission.all_admitted(), "{}", admission.record.text());
    assert!(admission.all_judgeable());
    let exclusions = &admission.spec.as_ref().unwrap().exclusions;
    assert!(exclusions.short_circuit_flagged());
    assert_eq!(exclusions.definition_exclusion(), None);
    assert_eq!(status, EXIT_YES, "{document:#}");
    assert_eq!(document["version"], 21);
    assert_eq!(document["spec"]["outcome"], "admitted");
    assert!(document["spec"]["exclusion"].is_null(), "{document:#}");
    for program in document["programs"].as_array().unwrap() {
        assert_eq!(program["outcome"], "ok", "{program:#}");
    }
    let exclusion = &document["spec"]["short_circuit"];
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
    assert_eq!(status, EXIT_YES, "{document:#}");
    assert_eq!(
        row(&document, "unknown-op")["outcome"],
        "ok",
        "{document:#}"
    );
    assert!(document["spec"]["exclusion"].is_null(), "{document:#}");
    assert_eq!(&document["spec"]["short_circuit"], exclusion);
}

/// A program whose initial configuration applies a function whose value depends on the
/// short-circuit reading is judged by its run's list of short-circuit readings, whatever the
/// analysis flags elsewhere. Admission runs each program to depth 0, the normalization of its
/// initial configuration, which every run of it on the baseline starts with: `g0`'s lists the
/// undefined `1 /Int 0` that `orBool` may skip, so `g0` is `excluded` at stage `initial-state`,
/// alone, and `check` exits 1, a finding; `g1`'s lists nothing (`1 /Int 1` is defined), so `g1` is `ok`, as
/// is `plain`, which does not apply `g`. A rule the analysis flags, which no program applies,
/// changes none of this.
#[test]
fn a_program_whose_initial_configuration_is_excluded_fails_check_alone() {
    for flagged in [false, true] {
        let name = if flagged {
            "initial-state-flagged"
        } else {
            "initial-state"
        };
        let manifest = initial_state_flow_of(name, flagged).join("FLOW.toml");
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
                ("g1", None),
                ("g0", Some(("short-circuit-reading", "initial-state"))),
                ("plain", None)
            ],
            "flagged: {flagged}"
        );
        assert_eq!(status, EXIT_NO, "{document:#}");
        assert!(document["spec"]["exclusion"].is_null(), "{document:#}");
        assert_eq!(
            document["spec"]["short_circuit"].is_object(),
            flagged,
            "{document:#}"
        );
        assert_eq!(document["programs"][0]["outcome"], "ok", "{document:#}");
        let g0 = &document["programs"][1];
        assert_eq!(
            (&g0["outcome"], &g0["stage"], &g0["reason"]),
            (
                &Value::from("excluded"),
                &Value::from("initial-state"),
                &Value::from("short-circuit-reading")
            ),
            "{g0:#}"
        );
        assert!(
            g0["detail"]
                .as_str()
                .unwrap()
                .contains("initial configuration"),
            "{g0:#}"
        );
        assert_eq!(document["programs"][2]["outcome"], "ok");
    }
}

/// On a definition whose short-circuit analysis flags a rule (`at`, whose result applies
/// `andThenBool` over `10 /Int I`), a program whose initial configuration has no value is refused
/// as on any other definition (`initial-undefined`): `at(1 /Int 0)` applies no function whose
/// value depends on the reading, and its depth-0 run lists no short-circuit reading, so the
/// configuration has no value in either reading. Before CF-03 every program of such a definition
/// was admitted as `excluded` at stage `definition`, and the depth-0 run was not made. The syntax
/// module imports `INT`, not `INT-SYNTAX` alone, so that the program text can apply `/Int`.
#[test]
fn a_start_with_no_value_on_a_flagged_definition_is_refused() {
    let dir = scratch("short-circuit-vacuous");
    write(
        &dir.join("scr.k"),
        "module SCR-SYNTAX
  imports INT
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
",
    );
    write(
        &dir.join("FLOW.toml"),
        "[spec]\nentry = \"scr.k\"\nmain_module = \"SCR\"\nsyntax_module = \"SCR-SYNTAX\"\n\n\
         [[program]]\nid = \"vacuous\"\ntext = \"at(1 /Int 0)\"\n\n\
         [[program]]\nid = \"one\"\ntext = \"at(1)\"\n",
    );
    let manifest = dir.join("FLOW.toml");
    let (document, status) = on_stack(move || check(&manifest));
    assert_eq!(status, EXIT_UNASKED, "{document:#}");
    assert!(
        document["spec"]["short_circuit"].is_object(),
        "{document:#}"
    );
    let vacuous = &document["programs"][0];
    assert_eq!(
        (&vacuous["outcome"], &vacuous["stage"], &vacuous["reason"]),
        (
            &Value::from("refused"),
            &Value::from("inputs"),
            &Value::from("initial-undefined")
        ),
        "{vacuous:#}"
    );
    assert_eq!(document["programs"][1]["outcome"], "ok", "{document:#}");
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
            let results = kink_flow::coverage::coverage(
                &manifest,
                &kink_flow::coverage::CoverageOptions {
                    verify: false,
                    cache: None,
                    ..kink_flow::coverage::CoverageOptions::default()
                },
            );
            let run = kink_flow::search::run(
                &manifest,
                &list,
                &kink_flow::search::RunOptions {
                    legacy_lock: None,
                    only: Vec::new(),
                    cache: None,
                    compile_workers: Some(1),
                    memo: kink_flow::memo::MemoUse::On,
                    schedule: kink_campaign::ScheduleMode::FirstKill,
                    lock: None,
                    locked: false,
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

    /// `results` and `run` print the definition exclusion and the rules the short-circuit
    /// analysis flags as `check` prints them (one formatter). On scfetch, whose analysis flags
    /// `fetch` and `fetch-halt-bug`, each run is judged by its own short-circuit readings. A
    /// program whose initial configuration applies a reading-dependent function is judged by its
    /// run's list too, whether or not the analysis flags a rule: `g0`'s run reads the undefined
    /// `1 /Int 0` that `orBool` may skip, and a reason only the run shows comes first (`g0`'s run
    /// contradicts `g`'s `total` claim); `g1`'s reads the defined `1 /Int 1`, so a rule the
    /// analysis flags elsewhere does not change `g1`'s class.
    #[test]
    #[ignore = "kink"]
    fn results_and_run_print_the_exclusion_as_check_does() {
        use kink_flow::{
            cli::{coverage, run},
            coverage::CoverageOptions,
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
            let (results_document, status) = coverage(
                &manifest,
                &CoverageOptions {
                    cache: Some(dir.join("cache")),
                    ..CoverageOptions::default()
                },
            );
            assert_eq!(
                status, EXIT_YES,
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
        assert!(checked["spec"]["exclusion"].is_null(), "{checked:#}");
        assert!(results_document["spec"]["exclusion"].is_null());
        assert!(run_document["spec"]["exclusion"].is_null());
        let flagged = &checked["spec"]["short_circuit"];
        assert_eq!(
            flagged["causes"].as_array().unwrap().len(),
            2,
            "{flagged:#}"
        );
        assert_eq!(&results_document["spec"]["short_circuit"], flagged);
        // Re-pin CF-03 (reviewed by Sebastien, 2026-11-04): unknown to judged. Each program's
        // run of `# fetch` reads no skipped operand (its `shortCircuitReadings` list is empty), so
        // the strict and the short-circuiting readings give the same run and it is judged. Before:
        // excluded by the definition-wide exclusion. The mutation then survives: it edits
        // `decode-unknown`, which no program reaches, and every program agrees.
        for program in results_document["programs"].as_array().unwrap() {
            assert_eq!(program["class"], "comparable", "{program:#}");
            assert!(program["cause"].is_null(), "{program:#}");
        }
        let row = &run_document["mutations"][0];
        assert_eq!(row["id"], "unknown-op", "{row:#}");
        assert_eq!(row["status"], "survived", "{row:#}");
        // The edit of an `owise` equation is not site-local (its condition is the negation of its
        // competitors'), so every program witnesses the compiled edit, though none reaches the
        // rule. Before the witness was read from the compiled mutant: `[]`, from the rule's text.
        assert_eq!(
            row["witnesses"],
            serde_json::json!(["fetch", "again"]),
            "{row:#}"
        );

        let classes = |flagged: bool| {
            let name = if flagged {
                "initial-state-results-flagged"
            } else {
                "initial-state-results"
            };
            let manifest = initial_state_flow_of(name, flagged).join("FLOW.toml");
            let cache = manifest.parent().unwrap().join("cache");
            on_stack(move || {
                let (checked, _) = check(&manifest);
                let (results_document, _) = coverage(
                    &manifest,
                    &CoverageOptions {
                        cache: Some(cache),
                        ..CoverageOptions::default()
                    },
                );
                (checked, results_document)
            })
        };
        let (checked, results_document) = classes(false);
        let (flagged_checked, flagged_results) = classes(true);
        assert!(results_document["spec"]["exclusion"].is_null());
        assert!(results_document["spec"]["short_circuit"].is_null());
        assert!(flagged_results["spec"]["short_circuit"].is_object());
        for (checked, results_document) in [
            (&checked, &results_document),
            (&flagged_checked, &flagged_results),
        ] {
            assert_eq!(checked["programs"][0]["outcome"], "ok", "{checked:#}");
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
        // The same program and the same function have one class whatever else the analysis flags.
        let g1 = &results_document["programs"][0];
        assert_eq!(g1["class"], flagged_results["programs"][0]["class"]);
        // Re-pin CF-03 (reviewed by Sebastien, 2026-11-04): unknown to comparable. `g1`'s run
        // lists no short-circuit reading (`1 /Int 1` is defined), so it is the same run under a
        // skipping reading and is judged. Before: excluded by the initial-state check, which
        // judged the function's definition rather than the run.
        assert_eq!(g1["class"], "comparable", "{g1:#}");
        assert!(g1["cause"].is_null(), "{g1:#}");
    }

    /// With every program's result cached, `check` warns of an edited rule no comparable
    /// program witnesses; `run` exits 2 when a selected mutation is invalid. Under Z3 the result
    /// cache is off, so no program has a record and the warning is never given.
    #[test]
    #[ignore = "kink"]
    fn check_warns_of_an_unwitnessed_rule_and_run_refuses_an_invalid_mutation() {
        use kink_flow::{
            cli::{coverage, run},
            coverage::CoverageOptions,
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

        let (document, status) = coverage(&manifest, &CoverageOptions::default());
        assert_eq!(status, EXIT_YES, "{document:#}");
        let (document, status) = check_list(&manifest, &list, None);
        assert_eq!(status, EXIT_UNASKED, "{document:#}");
        unreached_rule_from_the_cached_results(&dir, &manifest, &list, &document);

        let (document, status) = run(&manifest, &list, &RunOptions::default());
        assert_eq!(status, EXIT_UNASKED, "{document:#}");
        assert_eq!(document["counts"]["invalid-mutation"], 1, "{document:#}");
        let (document, status) = run(
            &manifest,
            &list,
            &RunOptions {
                only: vec!["add-becomes-sub".into(), "mul-becomes-add".into()],
                ..RunOptions::default()
            },
        );
        assert_eq!(status, EXIT_YES, "{document:#}");
    }

    /// The check document of the test above once every program's result is cached: the coverage
    /// decides and gives the warning, a layout edit keeps it, and another cache gives none.
    fn unreached_rule_from_the_cached_results(
        dir: &Path,
        manifest: &Path,
        list: &Path,
        document: &Value,
    ) {
        assert_eq!(document["coverage"]["decides"], true, "{document:#}");
        assert_eq!(
            row(document, "add-becomes-sub")["warnings"],
            serde_json::json!([])
        );
        let unreached = &row(document, "mul-becomes-add")["warnings"];
        assert_eq!(reasons(unreached), ["unmatched-rule"], "{document:#}");
        assert_eq!(unreached[0]["rule"]["module"], "CALC");
        // A comment and blank lines at the top of the specification keep every record: coverage
        // still decides, from the same records, and gives the same warning.
        let calc = dir.join("calc.k");
        let text = fs::read_to_string(&calc).unwrap();
        fs::write(&calc, format!("// a comment at the top\n\n{text}")).unwrap();
        let (commented, status) = check_list(manifest, list, None);
        assert_eq!(status, EXIT_UNASKED, "{commented:#}");
        assert_eq!(commented["coverage"], document["coverage"], "{commented:#}");
        assert_eq!(
            reasons(&row(&commented, "mul-becomes-add")["warnings"]),
            ["unmatched-rule"]
        );
        // Another cache holds no record: the warning is not given.
        let other = scratch("check-unreached-other-cache");
        let (document, _) = check_list(manifest, list, Some(&other));
        assert_eq!(document["coverage"]["decides"], false);
    }

    /// A timeout is never cached, so a corpus with a program that times out has no record of it
    /// and `check` gives no unmatched-rule warning, however often `results` runs; its detail says
    /// why and names the remedy. Bounded by `[budget] baseline_max_work` instead, the program is a
    /// cached `unknown`, which is not comparable, and the coverage decides from the comparable
    /// programs' records.
    #[test]
    #[ignore = "kink"]
    fn a_timeout_keeps_check_from_deciding_coverage_until_it_is_bounded_by_work() {
        use kink_flow::{cli::coverage, coverage::CoverageOptions};
        let dir = scratch("check-timeout");
        for name in ["loop.k", "FLOW-timeout.toml"] {
            fs::copy(flow("loop").join(name), dir.join(name)).unwrap();
        }
        fs::create_dir_all(dir.join("programs")).unwrap();
        for name in ["spin.loop", "countdown.loop"] {
            fs::copy(
                flow("loop").join("programs").join(name),
                dir.join("programs").join(name),
            )
            .unwrap();
        }
        let list = dir.join("MUTATIONS.toml");
        write(
            &list,
            &one_edit(
                "unused-adds-one",
                "  rule = \"unused\"\n  find = \"=> I\"\n  replace = \"=> I +Int 1\"",
            ),
        );
        let classes = |document: &Value| {
            document["programs"]
                .as_array()
                .unwrap()
                .iter()
                .map(|p| (p["id"].as_str().unwrap().to_owned(), p["class"].clone()))
                .collect::<Vec<_>>()
        };
        let timeout = dir.join("FLOW-timeout.toml");
        for _ in 0..2 {
            let (document, status) = coverage(&timeout, &CoverageOptions::default());
            assert_eq!(status, EXIT_UNANSWERED, "{document:#}");
            assert_eq!(
                classes(&document),
                [
                    ("spin".to_owned(), serde_json::json!("timeout")),
                    ("countdown".to_owned(), serde_json::json!("comparable")),
                ]
            );
            let (checked, status) = check_list(&timeout, &list, None);
            assert_eq!(status, EXIT_YES, "{checked:#}");
            assert_eq!(checked["coverage"]["decides"], false, "{checked:#}");
            assert_eq!(
                checked["coverage"]["without_record"],
                serde_json::json!(["spin"])
            );
            let detail = checked["coverage"]["detail"].as_str().unwrap();
            assert!(
                detail.contains("its result is never cached")
                    && detail.contains("[budget] baseline_max_work"),
                "{detail}"
            );
            assert_eq!(
                row(&checked, "unused-adds-one")["warnings"],
                serde_json::json!([])
            );
        }

        let work = dir.join("FLOW-work.toml");
        write(
            &work,
            &fs::read_to_string(&timeout).unwrap().replace(
                "time_ms = 500\n",
                "time_ms = 600000\nbaseline_max_work = 20000\n",
            ),
        );
        let (document, status) = coverage(&work, &CoverageOptions::default());
        assert_eq!(status, EXIT_UNANSWERED, "{document:#}");
        assert_eq!(
            classes(&document),
            [
                ("spin".to_owned(), serde_json::json!("unknown")),
                ("countdown".to_owned(), serde_json::json!("comparable")),
            ]
        );
        let (checked, status) = check_list(&work, &list, None);
        assert_eq!(status, EXIT_YES, "{checked:#}");
        assert_eq!(checked["coverage"]["decides"], true, "{checked:#}");
        assert_eq!(
            reasons(&row(&checked, "unused-adds-one")["warnings"]),
            ["unmatched-rule"],
            "{checked:#}"
        );
    }

    /// `unapplied-rule`: in a corpus whose one program, `1 / 0`, reaches the division rule and
    /// refutes its guard, no program applies the rule, so no program can kill an edit of its
    /// right-hand side alone. The warning is given for every edit of the rule (it reads the rule,
    /// not the edit), and once a program applies the rule it is gone.
    #[test]
    #[ignore = "kink"]
    fn check_warns_of_a_rule_every_program_refutes() {
        use kink_flow::{cli::coverage, coverage::CoverageOptions};
        let dir = scratch("check-unapplied");
        fs::copy(flow("divide").join("divide.k"), dir.join("divide.k")).unwrap();
        let header = "[spec]\nentry = \"divide.k\"\nmain_module = \"DIVIDE\"\n\
                      syntax_module = \"DIVIDE-SYNTAX\"\n\n";
        let by_zero = "[[program]]\nid = \"by-zero\"\ntext = \"1 / 0\"\n";
        let manifest = dir.join("FLOW.toml");
        write(&manifest, &format!("{header}{by_zero}"));
        let list = dir.join("MUTATIONS.toml");
        write(
            &list,
            &[
                one_edit(
                    "operands-swapped",
                    "  rule = \"div\"\n  find = \"I1 /Int I2\"\n  replace = \"I2 /Int I1\"",
                ),
                one_edit(
                    "guard-dropped",
                    "  rule = \"div\"\n  find = \" requires I2 =/=Int 0\"\n  replace = \"\"",
                ),
            ]
            .concat(),
        );
        let (document, status) = coverage(&manifest, &CoverageOptions::default());
        assert_eq!(status, EXIT_YES, "{document:#}");
        let (document, status) = check_list(&manifest, &list, None);
        assert_eq!(status, EXIT_YES, "{document:#}");
        assert_eq!(document["coverage"]["decides"], true, "{document:#}");
        for id in ["operands-swapped", "guard-dropped"] {
            let warnings = &row(&document, id)["warnings"];
            assert_eq!(reasons(warnings), ["unapplied-rule"], "{id}: {document:#}");
            assert_eq!(warnings[0]["rule"]["module"], "DIVIDE", "{id}");
        }
        // With a program that applies the rule, neither edit is warned about.
        write(
            &manifest,
            &format!("{header}{by_zero}\n[[program]]\nid = \"quotient\"\ntext = \"7 / 2\"\n"),
        );
        let (document, status) = coverage(&manifest, &CoverageOptions::default());
        assert_eq!(status, EXIT_YES, "{document:#}");
        let (document, status) = check_list(&manifest, &list, None);
        assert_eq!(status, EXIT_YES, "{document:#}");
        assert_eq!(document["coverage"]["decides"], true, "{document:#}");
        for id in ["operands-swapped", "guard-dropped"] {
            assert_eq!(
                row(&document, id)["warnings"],
                serde_json::json!([]),
                "{id}: {document:#}"
            );
        }
    }

    #[test]
    #[ignore = "kink"]
    fn the_binarys_exit_codes() {
        let path = |name: &str| flow(name).into_os_string();
        let (code, stdout, _) = binary(&["check".as_ref(), &path("calc/FLOW.toml")]);
        assert_eq!(code, Some(EXIT_YES.into()));
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
        assert_eq!(code, Some(EXIT_YES.into()), "{stdout}");

        let (code, stdout, _) = binary(&["check".as_ref(), &path("calc/FLOW-bad-program.toml")]);
        assert_eq!(code, Some(EXIT_UNASKED.into()));
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
        assert_eq!(code, Some(EXIT_UNASKED.into()));
        let document: Value = serde_json::from_str(&stdout).unwrap();
        assert_eq!(document["spec"]["stage"], "compile");

        let dir = scratch("binary");
        write(
            &dir.join("FLOW.toml"),
            "[spec]\nentry = \"calc.k\"\nmain_module = \"CALC\"\nmode = 1\n",
        );
        let (code, stdout, _) = binary(&["check".as_ref(), dir.join("FLOW.toml").as_os_str()]);
        assert_eq!(code, Some(EXIT_UNASKED.into()));
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
            assert_eq!(code, Some(EXIT_UNASKED.into()), "{args:?}");
            assert!(stdout.is_empty(), "{args:?}");
            // The message, then the usage line of the verb named (every command line's shape
            // when none is) and where the rest is: never the whole help.
            let lines = stderr.lines().collect::<Vec<_>>();
            assert_eq!(lines.len(), 3, "{stderr}");
            assert!(lines[0].starts_with("kink-flow: "), "{stderr}");
            match args
                .first()
                .and_then(|verb| Verb::parse(verb.to_str().unwrap()))
            {
                Some(verb) => {
                    assert_eq!(lines[1], format!("usage: kink-flow {}", verb.synopsis()));
                    assert_eq!(
                        lines[2],
                        format!("`kink-flow {} --help` lists its options", verb.as_str())
                    );
                }
                None => assert!(
                    lines[1].starts_with("usage: kink-flow --version | kink-flow VERB"),
                    "{stderr}"
                ),
            }
        }
    }
}

/// A `[[program]]` or `files` entry may state that its programs must be rejected before they run
/// (PJ-32): a text that does not parse meets `expect = { rejected = "parse" }` and is `rejected`
/// in the check document, with the refusal; one that parses is `accepted`, its statement unmet; a
/// `files` entry's statement applies to every text it matches. Neither is refused, so `check`
/// passes as on the same flow without them; one refused at another stage (typed inputs at the K
/// level) is refused, naming the statement.
#[test]
fn check_reports_a_program_rejected_at_the_stage_it_states() {
    let dir = scratch("rejected-stage");
    fs::copy(flow("calc/calc.k"), dir.join("calc.k")).unwrap();
    write(&dir.join("bad/a.calc"), "1 +");
    write(&dir.join("bad/b.calc"), "2 * 3");
    let flow_text = |extra: &str| {
        format!(
            "[spec]\nentry = \"calc.k\"\nmain_module = \"CALC\"\nsyntax_module = \"CALC-SYNTAX\"\n\n\
             [[program]]\nid = \"inline\"\ntext = \"2 * 3 + 1\"\n{extra}"
        )
    };
    let manifest = dir.join("FLOW.toml");
    write(
        &manifest,
        &flow_text(
            "\n[[program]]\nid = \"bad-inline\"\ntext = \"+ +\"\nexpect = { rejected = \"parse\" }\n\n\
             [[program]]\nfiles = \"bad/*.calc\"\nexpect = { rejected = \"parse\" }\n",
        ),
    );
    let (document, status) = on_stack({
        let manifest = manifest.clone();
        move || check(&manifest)
    });
    assert_eq!(status, EXIT_YES, "{document:#}");
    assert_eq!(document["version"], 21);
    let rows = document["programs"].as_array().unwrap();
    let outcome = |id: &str| {
        let row = rows.iter().find(|row| row["id"] == id).unwrap();
        (
            row["outcome"].as_str().unwrap().to_owned(),
            row["reason"].clone(),
            row.get("expectation").map(|e| e["verdict"].clone()),
        )
    };
    let met = (
        "rejected".to_owned(),
        Value::from("parse"),
        Some(Value::from("met")),
    );
    assert_eq!(outcome("inline"), ("ok".to_owned(), Value::Null, None));
    assert_eq!(outcome("bad-inline"), met);
    assert_eq!(outcome("bad/a.calc"), met);
    assert_eq!(
        outcome("bad/b.calc"),
        (
            "accepted".to_owned(),
            Value::Null,
            Some(Value::from("unmet"))
        )
    );
    let unmet = rows.iter().find(|row| row["id"] == "bad/b.calc").unwrap();
    assert!(
        unmet["expectation"]["detail"]
            .as_str()
            .unwrap()
            .contains("every K text it binds parses"),
        "{unmet:#}"
    );

    // A statement whose program is refused at another stage is refused with that refusal.
    write(
        &manifest,
        &flow_text(
            "\n[[program]]\nid = \"typed\"\ntext = \"1\"\ninputs = { n = 1 }\nexpect = { rejected = \"parse\" }\n",
        ),
    );
    let (document, status) = on_stack({
        let manifest = manifest.clone();
        move || check(&manifest)
    });
    assert_eq!(status, EXIT_UNASKED, "{document:#}");
    let typed = &document["programs"][1];
    assert_eq!(typed["outcome"], "refused", "{document:#}");
    assert_eq!(typed["reason"], "typed-inputs", "{document:#}");
    assert!(
        typed["detail"]
            .as_str()
            .unwrap()
            .starts_with("the program states `expect = { rejected = \"parse\" }`"),
        "{document:#}"
    );
    assert_eq!(typed.get("expectation"), None, "{document:#}");

    // A program text read at a start sort no module declares fails to parse whatever the text:
    // that refusal rejects nothing at `parse`, so the program is refused, naming the statement,
    // while the same text that does not parse at a declared sort meets it.
    write(
        &manifest,
        &flow_text(
            "\n[[program]]\nid = \"undeclared\"\ntext = \"1 + 2\"\nstart_sort = \"Pgmm\"\n\
             expect = { rejected = \"parse\" }\n\n\
             [[program]]\nid = \"declared\"\ntext = \"+ +\"\nstart_sort = \"Exp\"\n\
             expect = { rejected = \"parse\" }\n",
        ),
    );
    let (document, status) = on_stack(move || check(&manifest));
    assert_eq!(status, EXIT_UNASKED, "{document:#}");
    let undeclared = &document["programs"][1];
    assert_eq!(undeclared["outcome"], "refused", "{document:#}");
    assert_eq!(undeclared["reason"], "parse", "{document:#}");
    assert!(
        undeclared["detail"]
            .as_str()
            .unwrap()
            .starts_with("the program states `expect = { rejected = \"parse\" }`"),
        "{document:#}"
    );
    assert_eq!(
        document["programs"][2]["outcome"], "rejected",
        "{document:#}"
    );
}

/// PJ-22: `kink-flow admit FLOW.toml FILE...` as a command line gives it. At the K level, which
/// has no decoder, a candidate with typed inputs is refused by today's admission
/// (`inputs`/`typed-inputs`): an answer about the candidate, exit 0, with no fragment, and
/// nothing is written beside the flow (no cache directory appears). No FILE, an empty
/// `--found-by` and a FILE that is no file are usage errors.
#[test]
fn admit_reads_its_candidates_from_the_command_line() {
    let dir = scratch("admit");
    for file in ["FLOW.toml", "calc.k"] {
        fs::copy(flow(&format!("calc/{file}")), dir.join(file)).unwrap();
    }
    for program in fs::read_dir(flow("calc/programs")).unwrap() {
        let program = program.unwrap().path();
        let target = dir.join("programs").join(program.file_name().unwrap());
        fs::create_dir_all(target.parent().unwrap()).unwrap();
        fs::copy(&program, target).unwrap();
    }
    write(&dir.join("cand/typed.toml"), "[inputs]\npgm = 1\n");
    let manifest = dir.join("FLOW.toml");
    let candidate = dir.join("cand/typed.toml");
    let (code, stdout, stderr) = binary(&[
        "admit".as_ref(),
        manifest.as_os_str(),
        candidate.as_os_str(),
        "--found-by".as_ref(),
        "a person".as_ref(),
    ]);
    assert_eq!(code, Some(EXIT_YES.into()), "{stdout}{stderr}");
    let document: Value = serde_json::from_str(&stdout).unwrap();
    let row = &document["candidates"][0];
    assert_eq!(row["id"], "cand/typed.toml", "{document:#}");
    assert_eq!(
        (&row["outcome"], &row["stage"], &row["reason"]),
        (
            &Value::from("refused"),
            &Value::from("inputs"),
            &Value::from("typed-inputs")
        ),
        "{document:#}"
    );
    assert!(row.get("fragment").is_none(), "{document:#}");
    assert!(!dir.join(".kink-flow").exists(), "admit wrote a cache");

    for (args, message) in [
        (vec![], "admit needs a FILE"),
        (
            vec![candidate.as_os_str(), "--found-by".as_ref(), "".as_ref()],
            "--found-by needs a nonempty text",
        ),
        (vec!["no-such.toml".as_ref()], "no-such.toml is not a file"),
    ] {
        let mut line = vec!["admit".as_ref(), manifest.as_os_str()];
        line.extend(args);
        let (code, stdout, stderr) = binary(&line);
        assert_eq!(code, Some(EXIT_UNASKED.into()), "{stdout}{stderr}");
        assert!(stderr.contains(message), "{stderr}");
    }
    let (code, help, _) = binary(&["admit".as_ref(), "--help".as_ref()]);
    assert_eq!(code, Some(EXIT_YES.into()));
    for option in Verb::Admit.options() {
        assert!(help.contains(option.spelling), "{help}");
    }
}

/// PJ-20: `kink-flow accept FLOW.toml --projection NAME` as a command line gives it. kink-flow's
/// own front end has no cell vocabulary, so the comparison `accept` runs is refused
/// (`unsupported-front-end`, exit 2) and no snapshot is written; an unknown projection is
/// refused before anything runs. A missing `--projection`, an `--output` other than json or text
/// and an unlisted flag are usage errors; the verb's help lists its options.
#[test]
fn accept_reads_its_projection_from_the_command_line() {
    let dir = scratch("accept");
    for file in ["FLOW.toml", "calc.k"] {
        fs::copy(flow(&format!("calc/{file}")), dir.join(file)).unwrap();
    }
    for program in fs::read_dir(flow("calc/programs")).unwrap() {
        let program = program.unwrap().path();
        let target = dir.join("programs").join(program.file_name().unwrap());
        fs::create_dir_all(target.parent().unwrap()).unwrap();
        fs::copy(&program, target).unwrap();
    }
    let manifest = dir.join("FLOW.toml");
    let mut text = fs::read_to_string(&manifest).unwrap();
    text.push_str(
        "\n[[projection]]\nname = \"msg\"\nkind = \"accepts\"\nrelation = \"snapshot\"\n\n\
         [[implementation]]\nname = \"diag\"\ngiven = \"inputs\"\nprotocol = \
         \"kink-implementation/3\"\ncommand = [\"true\"]\nviews = [{ projection = \"msg\" }]\n",
    );
    fs::write(&manifest, text).unwrap();
    let accept = |extra: &[&str]| {
        let mut line = vec!["accept".as_ref(), manifest.as_os_str()];
        line.extend(extra.iter().map(std::ffi::OsStr::new));
        binary(&line)
    };
    let (code, stdout, stderr) = accept(&["--projection", "msg"]);
    assert_eq!(code, Some(EXIT_UNASKED.into()), "{stdout}{stderr}");
    let document: Value = serde_json::from_str(&stdout).unwrap();
    assert_eq!(document["schema"], "kink-flow-accept", "{document:#}");
    assert_eq!(
        document["refusal"]["reason"], "unsupported-front-end",
        "{document:#}"
    );
    assert!(!dir.join("snapshots").exists(), "accept wrote a snapshot");
    let (code, stdout, stderr) = accept(&["--projection", "nope", "--output", "text"]);
    assert_eq!(code, Some(EXIT_UNASKED.into()), "{stdout}{stderr}");
    assert!(
        stdout.starts_with("accept nope: refused (accept/unknown-projection): --projection nope"),
        "{stdout}"
    );
    for (args, message) in [
        (&[][..], "accept needs --projection NAME"),
        (
            &["--projection", "msg", "--output", "verdicts"][..],
            "--output \"verdicts\": expected json or text",
        ),
        (
            &["--projection", "msg", "--bogus"][..],
            "invalid option '--bogus'",
        ),
    ] {
        let (code, stdout, stderr) = accept(args);
        assert_eq!(code, Some(EXIT_UNASKED.into()), "{stdout}{stderr}");
        assert!(stderr.contains(message), "{stderr}");
    }
    let (code, help, _) = binary(&["accept".as_ref(), "--help".as_ref()]);
    assert_eq!(code, Some(EXIT_YES.into()));
    for option in Verb::Accept.options() {
        assert!(help.contains(option.spelling), "{help}");
    }
}

const IMP_K: &str = include_str!("../../../examples/imp/imp.k");

/// PJ-35 (U35b): a strictness edit is judged on IMP and killed by a run difference on a case
/// both grammars parse alike (`runs-differently`). Its claim removal withdraws nothing and
/// refuses nothing (it redefines no symbol, kink-patch `strictness_only`), and its mutant compiles
/// with the heating and cooling rules of its own strictness: `&&` made strict in both operands
/// evaluates `1 / 0 <= 1` beside a false left operand and gets stuck, an end holding the freezer
/// of `&&`'s second position, which only the mutant declares and the comparison reads as a free
/// constructor (kink-native `Freezers`); `+` made strict in its first operand only gets stuck on
/// `1 + (2 + 3)`; `<=` made `strict` evaluates its right operand first (an undeclared variable)
/// where `seqstrict` gets stuck on `1 / 0`; `+` made `seqstrict` no longer reaches the undeclared
/// variable of `1 / 0 + y`; and `+` made strict in its first operand only is killed by
/// `x = 1 + 1 / 0;`, whose specification end holds the freezer of `+`'s second position, which
/// only the specification declares. The programs are this test's, not examples/imp's corpus.
#[test]
fn a_strictness_edit_on_imp_is_killed_by_a_run_difference() {
    use serde_json::json;
    let dir = scratch("imp-strictness");
    write(&dir.join("imp.k"), IMP_K);
    write(
        &dir.join("FLOW.toml"),
        "[spec]\nentry = \"imp.k\"\nmain_module = \"IMP\"\nsyntax_module = \"IMP-SYNTAX\"\n\n\
         [budget]\ntime_ms = 10000\nmax_depth = 100000\nwork_factor = 4\n\n\
         [[program]]\nid = \"short-circuit\"\ntext = \"int x; if (2 <= 1 && 1 / 0 <= 1) {} else {}\"\n\n\
         [[program]]\nid = \"nested-sum\"\ntext = \"int x; x = 1 + (2 + 3);\"\n\n\
         [[program]]\nid = \"order\"\ntext = \"int x; if (1 / 0 <= y) {} else {}\"\n\n\
         [[program]]\nid = \"both-stuck\"\ntext = \"int x; x = 1 / 0 + y;\"\n",
    );
    let plus = |from: &str, to: &str| {
        format!(
            "  production = \"_+__IMP-SYNTAX_AExp_AExp_AExp\"\n  \
             find = \"AExp \\\"+\\\" AExp              [left, {from}]\"\n  \
             replace = \"AExp \\\"+\\\" AExp              [left, {to}]\""
        )
    };
    let mutations = dir.join("MUTATIONS.toml");
    write(
        &mutations,
        &[
            one_edit(
                "and-strict-both",
                "  production = \"_&&__IMP-SYNTAX_BExp_BExp_BExp\"\n  find = \"strict(1)\"\n  \
                 replace = \"strict\"",
            ),
            one_edit("plus-strict-first", &plus("strict", "strict(1)")),
            one_edit(
                "leq-strict",
                "  production = \"_<=__IMP-SYNTAX_BExp_AExp_AExp\"\n  find = \"seqstrict\"\n  \
                 replace = \"strict\"",
            ),
            one_edit("plus-seqstrict", &plus("strict", "seqstrict")),
        ]
        .concat(),
    );
    let manifest = dir.join("FLOW.toml");
    let (check, _) = check_list(&manifest, &mutations, None);
    for id in [
        "and-strict-both",
        "plus-strict-first",
        "leq-strict",
        "plus-seqstrict",
    ] {
        assert_eq!(row(&check, id)["outcome"], "ok", "{id}: {check:#}");
    }
    let (document, _) = flow_support::corpus_run(&manifest, &mutations);
    for (id, killer) in [
        ("and-strict-both", "short-circuit"),
        ("plus-strict-first", "nested-sum"),
        ("leq-strict", "order"),
        ("plus-seqstrict", "both-stuck"),
    ] {
        let row = row(&document, id);
        assert_eq!(
            killed_as(row),
            json!(["killed", killer, "runs-differently"]),
            "{row:#}"
        );
        assert_eq!(
            row["removed_claims"],
            json!({"removed": [], "unsupported": []}),
            "{id}"
        );
        assert!(
            row["grammar"]
                .as_array()
                .unwrap()
                .iter()
                .all(|case| case["reparse"] == "same"),
            "{row:#}"
        );
    }
    // The other direction: the specification's end holds the freezer of `+`'s second position,
    // which the mutant does not declare, and is read as a value under the mutant's definition.
    let spec_side = dir.join("SPEC-SIDE.toml");
    write(
        &spec_side,
        "[spec]\nentry = \"imp.k\"\nmain_module = \"IMP\"\nsyntax_module = \"IMP-SYNTAX\"\n\n\
         [[program]]\nid = \"spec-freezer\"\ntext = \"int x; x = 1 + 1 / 0;\"\n",
    );
    let plus_only = dir.join("PLUS.toml");
    write(
        &plus_only,
        &one_edit("plus-strict-first", &plus("strict", "strict(1)")),
    );
    let (document, _) = flow_support::corpus_run(&spec_side, &plus_only);
    let row = row(&document, "plus-strict-first");
    assert_eq!(
        killed_as(row),
        json!(["killed", "spec-freezer", "runs-differently"]),
        "{row:#}"
    );
}
