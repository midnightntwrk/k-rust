//! Admission and `kink-flow check` (flow F-02 deliverables 3, 4 and 6).

use kink_flow::{
    FlowManifest,
    admit::{FlowAdmission, admit},
    cli::{EXIT_CORPUS, EXIT_OK, EXIT_USAGE, check},
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
            "k_rust_revision",
            "profile",
            "programs",
            "schema",
            "spec",
            "version"
        ]
    );
    assert_eq!(document["schema"], "kink-flow-check");
    assert_eq!(document["version"], 1);
    assert_eq!(document["k_rust_revision"], kink_native::K_RUST_REVISION);
    assert_eq!(
        document["profile"],
        kink_native::execution::SolverProfile::BUILD.name()
    );
    assert_eq!(
        keys(&document["spec"]),
        ["detail", "files", "outcome", "reason", "stage"]
    );
    assert_eq!(document["spec"]["outcome"], "admitted");
    assert!(document["spec"]["stage"].is_null() && document["spec"]["reason"].is_null());
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
fn below_floor_paths_are_excluded_for_the_entry_and_every_loaded_file() {
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
        ("exclusion", "below-floor")
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
    assert_eq!(stage, "exclusion");

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
        ("exclusion", "below-floor")
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

#[test]
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
            stderr.contains("usage: kink-flow check FLOW.toml"),
            "{stderr}"
        );
    }
}
