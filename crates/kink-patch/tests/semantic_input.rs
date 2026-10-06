#[path = "../../../testdata/k/support.rs"]
mod support;

use kink_patch::{SemanticInput, SemanticInputError, structure_sha256};

fn artifact_has_no_paths_or_measurements(value: &serde_json::Value, key: &str) {
    match value {
        serde_json::Value::Object(object) => {
            for (key, value) in object {
                assert!(!key.ends_with("_ms"));
                artifact_has_no_paths_or_measurements(value, key);
            }
        }
        serde_json::Value::Array(array) => {
            for value in array {
                artifact_has_no_paths_or_measurements(value, key);
            }
        }
        serde_json::Value::String(text)
            if matches!(key, "logical" | "org.kframework.attributes.Source") =>
        {
            assert!(
                !std::path::Path::new(text).is_absolute(),
                "absolute source path: {text}"
            );
        }
        _ => {}
    }
}

#[test]
fn literal_digests() {
    for (name, artifact, structure) in [
        (
            "counter.k",
            "f997509eac63f303e54f078c721ca0e2bf9f7d780b82f60c88b39cfda9accb3d",
            "4af7e670c3bdec82d0997ef284611fcff09d1ae538546dbea4abc9f047013373",
        ),
        (
            "symmem.k",
            "a554dcedd4b0bd2dcdfb65edfd24b207de4899acc68e26345caf5175e869cad3",
            "87957ecd07877afe84beee0893c4aa7fbe3e0e714e0b4cb453604da7ce485f58",
        ),
    ] {
        let baseline = support::load(name);
        assert_eq!(
            SemanticInput::of(&baseline).unwrap().digest().to_string(),
            artifact,
            "{name}"
        );
        assert_eq!(
            structure_sha256(baseline.definition()).unwrap().to_string(),
            structure,
            "{name}"
        );
    }
}

#[test]
fn corpus_round_trip_is_canonical() {
    let mut paths = std::fs::read_dir(support::DIR)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|ext| ext == "k"))
        .collect::<Vec<_>>();
    paths.sort();
    for path in paths {
        let source = std::fs::read_to_string(&path).unwrap();
        let module = source
            .lines()
            .filter_map(|l| l.trim().strip_prefix("module "))
            .next_back()
            .unwrap()
            .split_whitespace()
            .next()
            .unwrap();
        let original = support::load_path(&path, module);
        let input = SemanticInput::of(&original).unwrap();
        assert!(!input.text().contains(env!("CARGO_MANIFEST_DIR")));
        artifact_has_no_paths_or_measurements(&serde_json::from_str(input.text()).unwrap(), "");
        let (read, baseline) = SemanticInput::read(input.text()).unwrap();
        assert_eq!(input, read);
        assert_eq!(input, SemanticInput::of(&baseline).unwrap());
        assert_eq!(original.definition(), baseline.definition());
        assert_eq!(
            original.loaded().source_table(),
            baseline.loaded().source_table()
        );
        let table = |b: &kink_patch::Baseline| {
            b.authored_sentences()
                .map(|(at, _)| {
                    let fingerprint = b.fingerprint(&at).unwrap();
                    (at, fingerprint)
                })
                .collect::<Vec<_>>()
        };
        assert_eq!(table(&original), table(&baseline));
    }
}

#[test]
fn checks_canonical_form_and_changed_token_identity() {
    let baseline = support::load("counter.k");
    let pretty = k_rust::definition::json::to_provenance_string_pretty(
        baseline.definition(),
        baseline.loaded().source_table(),
    )
    .unwrap();
    assert_eq!(
        SemanticInput::read(&pretty).unwrap_err(),
        SemanticInputError::NonCanonical
    );
    let input = SemanticInput::of(&baseline).unwrap();
    let unknown_node = input
        .text()
        .replacen(r#""node":"KToken""#, r#""node":"KTokn""#, 1);
    assert_ne!(unknown_node, input.text());
    assert!(matches!(
        SemanticInput::read(&unknown_node),
        Err(SemanticInputError::Decode(_) | SemanticInputError::NonCanonical)
    ));
    let changed = input
        .text()
        .replacen(r#""token":"true""#, r#""token":"false""#, 1);
    assert_ne!(changed, input.text());
    let (changed_input, _) = SemanticInput::read(&changed).unwrap();
    assert_ne!(changed_input.digest(), input.digest());
}

#[test]
fn read_back_compilation_is_equal() {
    for name in ["counter.k", "symmem.k", "guardedmem.k"] {
        let original = support::load(name);
        let (_, read) = SemanticInput::read(SemanticInput::of(&original).unwrap().text()).unwrap();
        assert_eq!(
            support::compile(original.loaded()).unwrap(),
            support::compile(read.loaded()).unwrap()
        );
    }
}

#[test]
fn canonical_json_keys_are_sorted() {
    assert_eq!(
        serde_json::to_string(&serde_json::json!({"b":1,"a":2})).unwrap(),
        r#"{"a":2,"b":1}"#
    );
}
