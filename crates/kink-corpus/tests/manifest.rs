use kink_corpus::manifest::{
    BELOW_FLOOR, CORPUS_MANIFEST_DOMAIN, CorpusManifest, ManifestError, exclusion_applies,
};
use kink_native::{K_RUST_REVISION, execution::SolverProfile};
use kink_patch::{canonical_json, payload_digest};
use serde_json::{Value, json};

fn clean() -> Value {
    serde_json::from_str(include_str!(
        "../../../testdata/corpus/admission-v1/clean.json"
    ))
    .unwrap()
}
fn read(v: &Value) -> Result<CorpusManifest, ManifestError> {
    CorpusManifest::from_canonical_json(&canonical_json(v))
}
fn failure(v: &Value, expected: ManifestError) {
    assert_eq!(read(v).unwrap_err(), expected);
}
fn keys(v: &Value, expected: &[&str]) {
    let mut expected = expected.to_vec();
    expected.sort_unstable();
    assert_eq!(
        v.as_object()
            .unwrap()
            .keys()
            .map(String::as_str)
            .collect::<Vec<_>>(),
        expected
    );
}
#[test]
fn exact_keys_canonical_bytes_and_profile() {
    let v = clean();
    let m = read(&v).unwrap();
    assert_eq!(
        m.text(),
        include_str!("../../../testdata/corpus/admission-v1/clean.json")
    );
    assert_eq!(m.value(), v);
    assert_eq!(
        m.digest(),
        payload_digest(CORPUS_MANIFEST_DOMAIN, m.text().as_bytes())
    );
    keys(
        &v,
        &[
            "schema",
            "version",
            "corpus",
            "k_rust",
            "profiles",
            "campaign",
            "universe",
            "operators",
            "exclusions",
            "definitions",
        ],
    );
    keys(
        &v["campaign"],
        &[
            "schedule",
            "selection",
            "classifier",
            "max_candidates_per_spec",
            "budget",
            "budget_mutants",
        ],
    );
    keys(
        &v["campaign"]["budget"],
        &[
            "time_ms",
            "max_simplification_iterations",
            "max_depth",
            "max_breadth",
        ],
    );
    keys(
        &v["definitions"][0],
        &[
            "id",
            "root",
            "entry",
            "include_dirs",
            "main_module",
            "syntax_module",
            "md_selector",
            "files",
            "requires_profile",
            "max_depth",
            "observation",
            "tests",
        ],
    );
    keys(
        &v["definitions"][0]["tests"][0],
        &["id", "input", "oracles"],
    );
    keys(
        &v["definitions"][0]["tests"][0]["input"],
        &["program", "start_sort", "variables"],
    );
    for p in [SolverProfile::NoZ3, SolverProfile::Z3] {
        m.check_profile(p).unwrap();
    }
    let mut single = v.clone();
    single["profiles"] = json!([if SolverProfile::BUILD == SolverProfile::Z3 {
        "no-z3"
    } else {
        "z3"
    }]);
    failure(&single, ManifestError::ProfileMismatch);
    let mut wrong = v;
    wrong["k_rust"]["revision"] = json!("wrong");
    failure(&wrong, ManifestError::RevisionMismatch);
    assert_eq!(m.value()["k_rust"]["revision"], K_RUST_REVISION);
    assert_eq!(
        CorpusManifest::from_canonical_json(&format!(" {}", m.text())).unwrap_err(),
        ManifestError::NonCanonical
    );
    let mut unknown = m.value();
    unknown["extra"] = json!(true);
    assert!(matches!(read(&unknown), Err(ManifestError::Schema(_))));
    unknown = m.value();
    unknown["definitions"][0]["tests"][0]["input"]["extra"] = json!(true);
    assert!(matches!(read(&unknown), Err(ManifestError::Schema(_))));
}
#[test]
fn campaign_budget_mutants() {
    let v = clean();
    let m = read(&v).unwrap();
    assert_eq!(m.campaign().budget_mutants, None);
    assert_eq!(m.text(), canonical_json(&v));

    let mut v = v;
    v["campaign"]["budget_mutants"] = json!({"per_spec_max":2,"total_max":3,"seed":"00ff"});
    let m = read(&v).unwrap();
    assert_eq!(
        m.campaign().budget_mutants,
        Some(kink_campaign::BudgetMutants {
            per_spec_max: 2,
            total_max: 3,
            seed: vec![0, 255],
        })
    );
    assert_eq!(m.text(), canonical_json(&v));
    assert_eq!(read(&m.value()).unwrap().text(), m.text());

    let mut invalid = v.clone();
    invalid["campaign"]
        .as_object_mut()
        .unwrap()
        .remove("budget_mutants");
    assert!(matches!(read(&invalid), Err(ManifestError::Schema(_))));
    invalid = v.clone();
    invalid["campaign"]["budget_mutants"]["extra"] = json!(true);
    assert!(matches!(read(&invalid), Err(ManifestError::Schema(_))));
    for (key, value) in [
        ("per_spec_max", json!(0)),
        ("total_max", json!(0)),
        ("seed", json!("")),
        ("seed", json!("0F")),
        ("seed", json!("abc")),
        ("seed", json!(7)),
        ("per_spec_max", json!("2")),
        ("total_max", json!(-1)),
        ("seed", json!("gg")),
    ] {
        let mut invalid = v.clone();
        invalid["campaign"]["budget_mutants"][key] = value;
        assert!(
            matches!(read(&invalid), Err(ManifestError::Schema(_))),
            "{invalid}"
        );
    }
    for value in [json!(7), json!([]), json!(true), json!("00ff")] {
        let mut invalid = v.clone();
        invalid["campaign"]["budget_mutants"] = value;
        assert!(matches!(read(&invalid), Err(ManifestError::Schema(_))));
    }
}
#[test]
fn mandatory_bounds_classifier_and_exclusions() {
    for remove in [false, true] {
        let mut v = clean();
        if remove {
            v["campaign"]["budget"]
                .as_object_mut()
                .unwrap()
                .remove("max_depth");
        } else {
            v["campaign"]["budget"]["max_depth"] = Value::Null;
        }
        failure(&v, ManifestError::MissingMaxDepth);
        let mut v = clean();
        if remove {
            v["campaign"]
                .as_object_mut()
                .unwrap()
                .remove("max_candidates_per_spec");
        } else {
            v["campaign"]["max_candidates_per_spec"] = json!(0);
        }
        failure(&v, ManifestError::MissingCandidateMaximum);
    }
    let mut v = clean();
    v["definitions"][0]["max_depth"] = json!(21);
    failure(&v, ManifestError::InvalidMaxDepth);
    v["definitions"][0]["max_depth"] = json!(20);
    read(&v).unwrap();
    v = clean();
    v["campaign"]["classifier"] = json!("closure");
    failure(&v, ManifestError::UnknownClassifier);
    for case in BELOW_FLOOR {
        let mut v = clean();
        v["exclusions"]
            .as_array_mut()
            .unwrap()
            .retain(|e| e["case"] != case);
        failure(&v, ManifestError::MissingBelowFloorExclusion);
    }
    for (file, expected) in [
        ("max-depth-null.json", ManifestError::MissingMaxDepth),
        (
            "missing-candidate-maximum.json",
            ManifestError::MissingCandidateMaximum,
        ),
        ("code-classifier.json", ManifestError::UnknownClassifier),
        ("pattern-no-observation.json", ManifestError::PatternOracle),
    ] {
        let text = std::fs::read_to_string(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../testdata/corpus/admission-v1")
                .join(file),
        )
        .unwrap();
        assert_eq!(
            CorpusManifest::from_canonical_json(&text).unwrap_err(),
            expected,
            "{file}"
        );
    }
}
fn pattern() -> Value {
    json!({"crash_policy":"reject","projection":{"pattern":{"plan":{"variables":[],"arms":[{"atoms":[{"constructor":"tick","payload":[]}],"relations":[]}],"side_condition":null},"with_bindings":false}}})
}
fn observation() -> Value {
    let pre =
        k_rust::kore::codec::to_value(&k_rust::kore::parser::parse_pattern("X:SortK{}").unwrap())
            .unwrap();
    json!({"constructor":"tick","pre":pre,"post":null,"payload":[]})
}
#[test]
fn data_patterns_are_validated_against_the_observation_vocabulary() {
    let mut v = clean();
    v["definitions"][0]["tests"][0]["oracles"] = json!([pattern()]);
    failure(&v, ManifestError::PatternOracle);
    v["definitions"][0]["observation"] = json!([observation()]);
    let m = read(&v).unwrap();
    assert_eq!(m.value(), v);
    v["definitions"][0]["tests"][0]["oracles"][0]["projection"]["pattern"]["plan"]["side_condition"] =
        json!({"name":"code","input_variables":[]});
    failure(&v, ManifestError::PatternOracle);
    v = m.value();
    v["definitions"][0]["tests"][0]["oracles"][0]["projection"]["pattern"]["plan"]["arms"][0]["atoms"]
        [0]["constructor"] = json!("other");
    failure(&v, ManifestError::PatternOracle);
    v = m.value();
    v["definitions"][0]["tests"][0]["oracles"][0]["projection"]["pattern"]["plan"]["arms"][0]["atoms"] =
        json!([]);
    failure(&v, ManifestError::PatternOracle);
    v = m.value();
    v["definitions"][0]["observation"][0]["pre"]["extra"] = json!(1);
    assert!(matches!(read(&v), Err(ManifestError::Observation(_))));
    v = m.value();
    v["definitions"][0]["observation"][0]["payload"] = json!(["missing"]);
    assert!(matches!(read(&v), Err(ManifestError::Observation(_))));
}
#[test]
fn exclusions_match_full_case_paths_with_parent_normalization() {
    let m = read(&clean()).unwrap();
    let mut d = m.definitions()[0].clone();
    let e = m
        .exclusions()
        .iter()
        .find(|e| e.case == "let-test")
        .unwrap();
    d.root.path = "some/k-distribution/tests/regression-new/let-test/inner/..".into();
    assert!(exclusion_applies(&d, e));
    d.root.path = "some/k-distribution/tests/regression-new/let-test-extra".into();
    assert!(!exclusion_applies(&d, e));
    d.id = "let-test".into();
    assert!(exclusion_applies(&d, e));
}
