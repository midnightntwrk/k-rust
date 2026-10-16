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

/// Re-pin R0a (finding E-07; k-rust 67b9f5c54 "write KRUST-PROVENANCE version 8"): the semantic
/// input is KRUST-PROVENANCE version 8 at k-rust 501f18b9 (version 7 at 927b9ce6: an `anchors`
/// table and interned origin-set sources), so its digests moved: counter.k from f997509e...,
/// symmem.k from a554dced.... The structure digests (the KAST definition JSON) moved too, from
/// 4af7e670... and 87957ecd...: measured against 927b9ce6, the two JSON documents are equal except
/// for source positions of the builtin Markdown sentences (locations, sentence offsets, content
/// starts and origin ranges: the extraction's offset map is the identity, k-rust 50c5812cb,
/// bdad0af15, 760930379, finding E-09) and the two default-layout regexes of builtin kast.md
/// (k-rust df11bc569, 4df229f70); the user modules are equal. The compiled KORE is unchanged
/// (`compiled_kore_is_unchanged_by_the_provenance_move`).
#[test]
fn literal_digests() {
    for (name, artifact, structure) in [
        (
            "counter.k",
            "a7181f8fe5cad482a4b76e0bfb506e1eb00b55f354f87a1b1684442cd740bb49",
            "f71bf625e0ba7b96ef9377c0b9bf550b57210b0422ce294df7146bd334649e2a",
        ),
        (
            "symmem.k",
            "31458cc30035f03ed69d43a180358989867e952b570b81a031c4fb4fe4d03fe4",
            "149d73dc878819b0974b7aabcad4402ada7f0ef90b6d1531e16b5ed92ef7d8af",
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

/// Re-pin R0a (finding E-07): the semantic-input digests moved with the provenance format, but
/// what compilation emits did not. These are the SHA-256 digests of `definition_kore` measured at
/// k-rust 927b9ce6 (stage-1 trial, scratch-E/dump-old); 501f18b9 compiles the same bytes.
#[test]
fn compiled_kore_is_unchanged_by_the_provenance_move() {
    for (name, kore) in [
        (
            "counter.k",
            "aafd92147714ace030b35666daed4c0fa0646dc9ee91fa89e49765f448debc52",
        ),
        (
            "symmem.k",
            "fc4fb79cdfa2d2426fa89547b2c57defacbcace95c7aee64baceae935a1a17b8",
        ),
        (
            "guardedmem.k",
            "6554be06977a8fb574a60d3eb5daf8fff91c9db675f26121ac74361a35b5941a",
        ),
    ] {
        let baseline = support::load(name);
        let artifacts = support::compile(baseline.loaded()).expect("compiles");
        assert_eq!(
            kink_patch::sha256(artifacts.definition_kore.as_bytes()).to_string(),
            kore,
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
