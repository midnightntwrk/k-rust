use std::fs;
use std::path::PathBuf;

use k_rust::kore::printer::Printer;
use k_rust::kore::{json, parser};
use serde_json::Value;

#[test]
fn upstream_kore_json_v1_corpus() {
    let directory = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/kore/json");
    let mut files: Vec<_> = fs::read_dir(directory)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .collect();
    files.sort();
    assert_eq!(files.len(), 41);

    let mut terms = 0;
    for file in files {
        let input = fs::read_to_string(&file).unwrap();
        let envelopes: Vec<Value> = serde_json::from_str(&input).unwrap();
        for envelope in envelopes {
            terms += 1;
            let pattern = json::from_str(&envelope.to_string()).unwrap_or_else(|error| {
                panic!("{}: {error}", file.display());
            });
            let text = Printer::compact().print_pattern(&pattern);
            let reparsed = parser::parse_pattern(&text).unwrap_or_else(|error| {
                panic!("{}: {error}\n{text}", file.display());
            });
            assert_eq!(reparsed, pattern, "{}", file.display());

            let encoded = json::to_string(&pattern).unwrap();
            assert_eq!(json::from_str(&encoded).unwrap(), pattern);
            assert_eq!(serde_json::from_str::<Value>(&encoded).unwrap(), envelope);
        }
    }
    assert_eq!(terms, 68);
}

#[test]
fn rejects_wrong_format_and_version() {
    assert!(json::from_str(r#"{"format":"other","version":1,"term":{"tag":"Top","sort":{"tag":"SortVar","name":"S"}}}"#).is_err());
    assert!(json::from_str(r#"{"format":"KORE","version":2,"term":{"tag":"Top","sort":{"tag":"SortVar","name":"S"}}}"#).is_err());
}

#[test]
fn reference_print_pattern_json_pins_set_variable_names() {
    let root =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/reference/kore-syntax/json");
    let source = fs::read_to_string(root.join("mu-svar.json")).unwrap();
    let value: Value = serde_json::from_str(&source).unwrap();
    assert_eq!(value["term"]["var"], "@X");
    assert_eq!(value["term"]["arg"]["name"], "@X");

    let pattern = json::from_str(&source).unwrap();
    assert_eq!(
        pattern,
        parser::parse_pattern(r"\mu{}(@X:S{}, @X:S{})").unwrap()
    );
}

#[test]
fn reference_multi_or_json_expands_to_binary_or() {
    let source = fs::read_to_string(
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/reference/kore-syntax/json/multi-or-right.json"),
    )
    .unwrap();
    let pattern = json::from_str(&source).unwrap();
    assert_eq!(
        pattern,
        parser::parse_pattern(r"\or{S{}}(a{}(), \or{S{}}(b{}(), c{}()))").unwrap()
    );
}

#[test]
fn reference_shaped_deep_app_chain_decodes() {
    // reference: shape emitted by kore-parser --print-pattern-json; the fixture is the harvested
    // B3-02 depth-148 JSON document from draft/fable51-review/fixtures/b3-probe/deep.json.
    let source = include_str!("fixtures/reference/kore-syntax/json/deep-148.json");
    assert!(json::from_str(source).is_err());
    assert!(json::from_str_unbounded(source).is_ok());
}
