use kink_corpus::{
    CorpusSource,
    admission::{AdmissionResult, admit_definition, check_semantic_input},
    load_source,
    manifest::CorpusManifest,
};
use kink_native::execution::SolverProfile;
use kink_patch::{SemanticInput, canonical_json, sha256};
use serde_json::{Value, json};
use std::{
    fs,
    path::{Path, PathBuf},
};
fn workspace() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .unwrap()
}
fn fixture() -> PathBuf {
    workspace().join("testdata/corpus/admission-v1")
}
fn clean() -> Value {
    serde_json::from_str(include_str!(
        "../../../testdata/corpus/admission-v1/clean.json"
    ))
    .unwrap()
}
fn run(v: &Value) -> AdmissionResult {
    let m = CorpusManifest::from_canonical_json(&canonical_json(v)).unwrap();
    admit_definition(
        &m,
        v["definitions"][0]["id"].as_str().unwrap(),
        &workspace(),
    )
}
fn named(file: &str, main: &str) -> Value {
    let mut v = clean();
    let d = &mut v["definitions"][0];
    d["entry"] = json!(file);
    d["main_module"] = json!(main);
    d["files"] = json!([{"name":file,"sha256":sha256(&fs::read(fixture().join(file)).unwrap()).to_string()}]);
    v
}
fn refused(v: &Value, stage: &str, reason: &str) -> AdmissionResult {
    let r = run(v);
    assert!(r.admitted.is_none(), "{}", r.record.text());
    let f = r.record.refusal.as_ref().unwrap();
    assert_eq!(
        (&*f.stage, &*f.reason),
        (stage, reason),
        "{}",
        r.record.text()
    );
    assert!(!r.record.text().contains(workspace().to_str().unwrap()));
    assert!(!r.record.text().contains("/home"));
    r
}
#[test]
fn clean_is_admitted_and_records_are_canonical_and_deterministic() {
    let a = run(&clean());
    let b = run(&clean());
    assert!(a.admitted.is_some(), "{}", a.record.text());
    assert_eq!(a.record.text(), b.record.text());
    assert_eq!(a.record.text(), canonical_json(&a.record.value()));
    let keys = a
        .record
        .value()
        .as_object()
        .unwrap()
        .keys()
        .cloned()
        .collect::<Vec<_>>();
    assert_eq!(
        keys,
        [
            "census",
            "definition",
            "detail",
            "files",
            "kompile_warnings",
            "outcome",
            "reason",
            "representation",
            "stage"
        ]
    );
    assert_eq!(
        a.record.value()["kompile_warnings"],
        json!([{ "code":"MissingSyntaxModule", "message":"Could not find main syntax module with name CS12-CLEAN-SYNTAX in definition.  Use --syntax-module to specify one. Using CS12-CLEAN as default." }])
    );
    assert_eq!(a.record.value()["representation"], "admitted");
    assert_eq!(
        a.record.value()["files"],
        clean()["definitions"][0]["files"]
    );
    assert_eq!(a.record.value()["census"]["verdict"], "natural");
    assert!(!a.record.text().contains(workspace().to_str().unwrap()));
    assert!(!a.record.text().contains("/home"));
    assert_eq!(a.admitted.unwrap().tests.len(), 2);
}
#[test]
fn committed_refusal_manifests_have_exact_stages_and_reasons() {
    for (file, stage, reason) in [
        ("excluded-id.json", "exclusion", "below-floor"),
        ("wrong-source-pin.json", "load", "source-pin"),
    ] {
        let text = fs::read_to_string(fixture().join(file)).unwrap();
        let m = CorpusManifest::from_canonical_json(&text).unwrap();
        let r = admit_definition(&m, &m.definitions()[0].id, &workspace());
        assert!(r.admitted.is_none(), "{}", r.record.text());
        let f = r.record.refusal.as_ref().unwrap();
        assert_eq!(
            (&*f.stage, &*f.reason),
            (stage, reason),
            "{}",
            r.record.text()
        );
        assert!(r.record.value()["kompile_warnings"].is_null());
        assert!(!r.record.text().contains(workspace().to_str().unwrap()));
        assert!(!r.record.text().contains("/home"));
    }
}
#[test]
fn every_refusal_stage_and_first_failure() {
    let mut v = named("float.k", "TB02FLOAT");
    refused(&v, "representation", "G-F");
    v["definitions"][0]["id"] = json!("let-test");
    let r = refused(&v, "exclusion", "below-floor");
    assert!(r.record.kompile_warnings.is_none());
    let mut v = clean();
    v["definitions"][0]["requires_profile"] = json!("z3");
    if SolverProfile::BUILD == SolverProfile::NoZ3 {
        refused(&v, "profile", "profile");
    } else {
        assert!(run(&v).admitted.is_some());
    }
    refused(
        &named("load-error.k", "CS12-LOAD-ERROR"),
        "load",
        "load-error",
    );
    refused(
        &named("compile-error.k", "CS12-COMPILE-ERROR"),
        "compile",
        "compile-error",
    );
    let r = refused(&named("t13owk.k", "T13OWK"), "declaration-census", "vi-t13");
    assert_eq!(r.record.value()["census"]["verdict"], "flagged");
    v = clean();
    v["definitions"][0]["tests"][0]["input"]["program"]["text"] = json!("???");
    refused(&v, "inputs", "parse");
    refused(
        &named("map.k", "CS12-MAP"),
        "baseline",
        "baseline-oracle-failed",
    );
    v = clean();
    v["definitions"][0]["root"]["path"] =
        json!("testdata/corpus/admission-v1/k-distribution/tests/regression-new/let-test");
    v["definitions"][0]["id"] = json!("renamed");
    refused(&v, "exclusion", "below-floor");
    v["definitions"][0]["root"]["path"] =
        json!("testdata/corpus/admission-v1/k-distribution/tests/regression-new/let-test/inner/..");
    refused(&v, "exclusion", "below-floor");
}
#[test]
fn semantic_input_stage_rejects_decodable_noncanonical_text() {
    let loaded = load_source(&CorpusSource {
        root: fixture(),
        entry: "clean.k".into(),
        include_dirs: vec![],
        main_module: "CS12-CLEAN".into(),
        syntax_module: None,
        md_selector: None,
    })
    .unwrap();
    let input = SemanticInput::of(&loaded.baseline).unwrap();
    check_semantic_input(input.text()).unwrap();
    let value: Value = serde_json::from_str(input.text()).unwrap();
    let text = serde_json::to_string_pretty(&value).unwrap();
    assert!(k_rust::definition::json::from_provenance_str(&text).is_ok());
    let f = check_semantic_input(&text).unwrap_err();
    assert_eq!((&*f.stage, &*f.reason), ("semantic-input", "non-canonical"));
    assert!(f.detail.contains("NonCanonical"));
    let f = check_semantic_input("invalid").unwrap_err();
    assert_eq!((&*f.stage, &*f.reason), ("semantic-input", "non-canonical"));
    assert!(f.detail.contains("Decode"));
}
#[test]
fn modified_and_unlisted_sources_refuse_at_load_before_parsing() {
    let mut v = clean();
    v["definitions"][0]["files"][0]["sha256"] = json!("0".repeat(64));
    let r = refused(&v, "load", "source-pin");
    assert!(r.record.kompile_warnings.is_none());
    let dir =
        Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("cs12-pins-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    fs::copy(fixture().join("clean.k"), dir.join("clean.k")).unwrap();
    let mut v = clean();
    v["definitions"][0]["root"]["path"] = json!(".");
    let m = CorpusManifest::from_canonical_json(&canonical_json(&v)).unwrap();
    fs::write(dir.join("clean.k"), "unparseable modified bytes").unwrap();
    let r = admit_definition(&m, "clean", &dir);
    assert_eq!(r.record.refusal.unwrap().reason, "source-pin");
    let text = format!(
        "requires \"unlisted.k\"\n{}",
        fs::read_to_string(fixture().join("clean.k")).unwrap()
    );
    fs::write(dir.join("clean.k"), &text).unwrap();
    fs::write(dir.join("unlisted.k"), "invalid bytes").unwrap();
    v["definitions"][0]["files"][0]["sha256"] = json!(sha256(text.as_bytes()).to_string());
    let m = CorpusManifest::from_canonical_json(&canonical_json(&v)).unwrap();
    let r = admit_definition(&m, "clean", &dir);
    assert_eq!(r.record.refusal.unwrap().reason, "source-pin");
    fs::remove_dir_all(dir).unwrap();
}
#[test]
fn compile_warnings_are_fidelity_only_sorted_and_deduplicated() {
    let r = run(&named("warning.k", "CS12-WARNING"));
    assert!(r.admitted.is_some(), "{}", r.record.text());
    assert!(!r.record.text().contains(workspace().to_str().unwrap()));
    assert!(!r.record.text().contains("/home"));
    let a = r.admitted.as_ref().unwrap();
    let expected = a
        .compiled
        .artifacts()
        .diagnostics
        .iter()
        .map(|d| (format!("{:?}", d.code), d.message.clone()))
        .collect::<std::collections::BTreeSet<_>>();
    assert!(!expected.is_empty());
    let value = expected
        .into_iter()
        .map(|(code, message)| json!({"code":code,"message":message}))
        .collect::<Vec<_>>();
    assert_eq!(r.record.value()["kompile_warnings"], json!(value));
    assert!(
        r.record.value()["kompile_warnings"]
            .as_array()
            .unwrap()
            .iter()
            .any(|d| d["code"] == "UnadmittedHookNamespace")
    );
}
#[cfg(unix)]
#[test]
fn symlink_cannot_hide_a_below_floor_path() {
    let dir =
        Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("cs12-link-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    std::os::unix::fs::symlink(
        fixture().join("k-distribution/tests/regression-new/let-test"),
        dir.join("alias"),
    )
    .unwrap();
    let mut v = clean();
    v["definitions"][0]["root"]["path"] = json!("alias");
    let m = CorpusManifest::from_canonical_json(&canonical_json(&v)).unwrap();
    let r = admit_definition(&m, "clean", &dir);
    assert_eq!(r.record.refusal.unwrap().stage, "exclusion");
    fs::remove_dir_all(dir).unwrap();
}
#[test]
fn admission_has_no_status_type() {
    assert!(!include_str!("../src/admission.rs").contains("MutantStatus"));
}

#[test]
fn pinned_loader_preserves_cs02_source_identity() {
    let source = CorpusSource {
        root: workspace().join("testdata/corpus/relative"),
        entry: "definition/main.k".into(),
        include_dirs: vec!["include".into()],
        main_module: "CORPUS".into(),
        syntax_module: Some("CORPUS-SYNTAX".into()),
        md_selector: None,
    };
    let loaded = load_source(&source).unwrap();
    let mut v = clean();
    let d = &mut v["definitions"][0];
    d["root"]["path"] = json!("testdata/corpus/relative");
    d["entry"] = json!(source.entry);
    d["include_dirs"] = json!(source.include_dirs);
    d["main_module"] = json!(source.main_module);
    d["syntax_module"] = json!(source.syntax_module);
    d["files"] = json!(
        loaded
            .files
            .iter()
            .map(|f| json!({"name":f.name,"sha256":f.sha256.to_string()}))
            .collect::<Vec<_>>()
    );
    let result = run(&v);
    assert!(result.admitted.is_some(), "{}", result.record.text());
    assert_eq!(
        result.admitted.unwrap().semantic_input,
        SemanticInput::of(&loaded.baseline).unwrap()
    );
    v["definitions"][0]["files"].as_array_mut().unwrap().pop();
    refused(&v, "load", "source-pin");
}

#[test]
fn program_file_bytes_are_pinned_and_reused_and_pattern_admission_works() {
    let dir =
        Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("cs12-program-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    fs::copy(fixture().join("clean.k"), dir.join("clean.k")).unwrap();
    fs::write(dir.join("program.test"), "true").unwrap();
    let mut v = clean();
    v["definitions"][0]["root"]["path"] = json!(".");
    v["definitions"][0]["tests"][0]["input"]["program"] = json!({"file":"program.test"});
    let parse = |v: &Value| CorpusManifest::from_canonical_json(&canonical_json(v)).unwrap();
    let r = admit_definition(&parse(&v), "clean", &dir);
    assert_eq!(r.record.refusal.unwrap().reason, "source-pin");
    v["definitions"][0]["files"]
        .as_array_mut()
        .unwrap()
        .push(json!({"name":"program.test","sha256":sha256(b"true").to_string()}));
    let r = admit_definition(&parse(&v), "clean", &dir);
    assert!(r.admitted.is_some(), "{}", r.record.text());
    assert_eq!(r.record.files.len(), 2);
    fs::remove_dir_all(dir).unwrap();
    let mut v = clean();
    let pre = k_rust::kore::codec::to_value(
        &k_rust::kore::parser::parse_pattern("X:SortGeneratedTopCell{}").unwrap(),
    )
    .unwrap();
    v["definitions"][0]["observation"] =
        json!([{"constructor":"tick","pre":pre,"post":null,"payload":[]}]);
    v["definitions"][0]["tests"][0]["oracles"] = json!([{"crash_policy":"reject","projection":{"pattern":{"plan":{"variables":[],"arms":[{"atoms":[{"constructor":"tick","payload":[]}],"relations":[]}],"side_condition":null},"with_bindings":false}}}]);
    let r = run(&v);
    assert!(r.admitted.is_some(), "{}", r.record.text());
}

#[test]
fn corpus_v1_refuses_symbolic_kore_inputs_at_the_input_gate() {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("cs12-concrete-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    fs::copy(fixture().join("clean.k"), dir.join("clean.k")).unwrap();
    let pattern = k_rust::kore::parser::parse_pattern("X:SortGeneratedTopCell{}").unwrap();
    let text = canonical_json(&k_rust::kore::codec::to_value(&pattern).unwrap());
    fs::write(dir.join("initial.json"), &text).unwrap();
    let mut v = clean();
    v["definitions"][0]["root"]["path"] = json!(".");
    v["definitions"][0]["tests"][0]["input"] =
        json!({"kore_state":{"file":"initial.json","sha256":sha256(text.as_bytes()).to_string()}});
    let m = CorpusManifest::from_canonical_json(&canonical_json(&v)).unwrap();
    let result = admit_definition(&m, "clean", &dir);
    let refusal = result.record.refusal.unwrap();
    assert_eq!(
        (&*refusal.stage, &*refusal.reason),
        ("inputs", "input-gate")
    );
    assert!(refusal.detail.contains("concrete"));
    fs::remove_dir_all(dir).unwrap();
}
