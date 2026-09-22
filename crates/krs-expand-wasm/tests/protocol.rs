//! The expander protocol over tour-minimal and the BL-005/BL-006 probes.
//!
//! With `KRS_IR11_EVIDENCE` set to a directory, the tour-minimal test writes
//! `request.json`, `response.json` (native), and `expanded.rs` there, and the
//! invalid-probe test writes `invalid-request.json` and
//! `invalid-response.json`, and the lookup test writes `lookup-request.json`
//! and `lookup-response.json`; `tests/run-wasm.mjs` replays the requests
//! through the Wasm module.

use std::path::PathBuf;

use krs_expand_wasm::protocol::{self, SCHEMA};
use serde_json::{Value, json};

const TOUR_MINIMAL: &str = include_str!("../../../tests/tour-minimal/src/lib.rs");

fn request(source: &str, mode: &Value) -> Value {
    json!({
        "schema": SCHEMA,
        "mode": mode,
        "file": {
            "virtual_path": "/workspace/tour-minimal/src/lib.rs",
            "display_file": "src/lib.rs",
            "source": source,
        },
        "package": {
            "cargo_name": "krs-tour-minimal",
            "cargo_version": "0.0.0",
            "manifest_dir": "/workspace/tour-minimal",
            "crate_name": "krs_tour_minimal",
        },
        "module_path": ["krs_tour_minimal"],
        "facade": { "alias": "k", "path": "::k" },
        "generated_file": "/work/expanded/tour-minimal/src/lib.rs",
        "policy": { "version": 1, "editable_files": ["src/lib.rs"], "facade_alias": "k" },
    })
}

fn run(request: &Value) -> (Vec<u8>, Vec<u8>, Value) {
    let bytes = serde_json::to_vec_pretty(request).unwrap();
    let response = protocol::run_json(&bytes);
    let value = serde_json::from_slice(&response).unwrap();
    (bytes, response, value)
}

fn evidence_dir() -> Option<PathBuf> {
    std::env::var_os("KRS_IR11_EVIDENCE").map(PathBuf::from)
}

#[test]
fn tour_minimal_expands_through_the_protocol() {
    let (bytes, response, value) = run(&request(TOUR_MINIMAL, &json!("whole-file")));
    assert_eq!(value["ok"], true, "{value}");
    assert_eq!(value["diagnostics"], json!([]));
    let text = value["expanded"]["text"].as_str().unwrap();
    assert_eq!(
        value["expanded"]["generated_file"],
        "/work/expanded/tour-minimal/src/lib.rs"
    );
    assert_eq!(
        value["evidence"]["text_sha256"],
        protocol::sha256(text.as_bytes())
    );
    assert_eq!(
        value["evidence"]["request_sha256"],
        protocol::sha256(&bytes)
    );
    assert_eq!(
        value["evidence"]["authored_sha256"],
        "57e64bdc8371c2dd65df2b94e0f6fce12753b16df14aece71ae9c6ddea5644f5"
    );
    assert_eq!(value["requests_framework"], true);
    assert_eq!(value["registrations"].as_array().unwrap().len(), 7);
    let map = &value["source_map"];
    assert_eq!(map["authored_file"], "src/lib.rs");
    assert_eq!(map["invocations"].as_array().unwrap().len(), 6);
    assert_eq!(map["invocations"][4]["parent"], 3);
    let segments = map["segments"].as_array().unwrap();
    assert_eq!(segments.last().unwrap()["class"], "generated-only");
    assert_eq!(
        segments.last().unwrap()["generated"][1].as_u64().unwrap(),
        u64::try_from(text.len()).unwrap()
    );
    // Deterministic: a second run is byte-identical.
    let (_, again, _) = run(&request(TOUR_MINIMAL, &json!("whole-file")));
    assert_eq!(response, again);
    if let Some(directory) = evidence_dir() {
        std::fs::create_dir_all(&directory).unwrap();
        std::fs::write(directory.join("request.json"), &bytes).unwrap();
        std::fs::write(directory.join("response.json"), &response).unwrap();
        std::fs::write(directory.join("expanded.rs"), text).unwrap();
    }
}

#[test]
fn lookup_maps_authored_generated_and_table_ranges() {
    let (_, _, value) = run(&request(TOUR_MINIMAL, &json!("whole-file")));
    let text = value["expanded"]["text"].as_str().unwrap();
    let map = value["source_map"].clone();
    let segments = map["segments"].as_array().unwrap();
    let m2obj = segments
        .iter()
        .find(|segment| segment["authored"] == json!([303, 308]))
        .expect("M2Obj is copied verbatim");
    let table = segments.last().unwrap()["generated"].clone();
    let lookup = json!({
        "schema": SCHEMA,
        "authored_source": TOUR_MINIMAL,
        "text": text,
        "source_map": map,
        "ranges": [m2obj["generated"], [287, 290], table],
    });
    let response: Value = serde_json::from_slice(&protocol::lookup_json(
        &serde_json::to_vec(&lookup).unwrap(),
    ))
    .unwrap();
    assert_eq!(response["ok"], true, "{response}");
    if let Some(directory) = evidence_dir() {
        std::fs::create_dir_all(&directory).unwrap();
        let bytes = serde_json::to_vec(&lookup).unwrap();
        std::fs::write(directory.join("lookup-request.json"), &bytes).unwrap();
        std::fs::write(
            directory.join("lookup-response.json"),
            protocol::lookup_json(&bytes),
        )
        .unwrap();
    }
    assert_eq!(
        response["mappings"],
        json!([
            { "class": "exact-authored", "authored": [303, 308], "invocation": 0 },
            { "class": "invocation-level", "authored": [287, 320], "invocation": 0 },
            { "class": "generated-only", "authored": null, "invocation": null },
        ])
    );

    let mut stale = lookup;
    stale["authored_source"] = json!("fn main() {}\n");
    let response: Value =
        serde_json::from_slice(&protocol::lookup_json(&serde_json::to_vec(&stale).unwrap()))
            .unwrap();
    assert_eq!(response["ok"], false);
    assert_eq!(response["diagnostics"][0]["code"], protocol::PROTOCOL_ERROR);
}

#[test]
fn bl005_invalid_sorts_reports_expected_identifier() {
    let source = "k::sorts! { M2Obj: ; }\n";
    let expected = json!([{
        "origin": "expander",
        "code": null,
        "severity": "error",
        "message": "expected identifier",
        "class": "exact-authored",
        "file": "src/lib.rs",
        "authored": [19, 20],
        "invocation": 0,
        "notes": [],
    }]);
    for mode in [
        json!("whole-file"),
        json!({ "invocations": [{ "kind": "sorts", "replaced": [0, 22] }] }),
    ] {
        let request = request(source, &mode);
        let (bytes, response, value) = run(&request);
        assert_eq!(value["ok"], false);
        assert_eq!(value["expanded"], Value::Null);
        assert_eq!(value["source_map"], Value::Null);
        assert_eq!(value["diagnostics"], expected);
        if mode == json!("whole-file")
            && let Some(directory) = evidence_dir()
        {
            std::fs::create_dir_all(&directory).unwrap();
            std::fs::write(directory.join("invalid-request.json"), &bytes).unwrap();
            std::fs::write(directory.join("invalid-response.json"), &response).unwrap();
        }
    }
}

#[test]
fn policy_diagnostics_stop_before_expansion() {
    // BL-006 D007: an external derive, rejected at 9..25.
    let source = "#[derive(serde::Serialize)]\npub struct S;\n";
    let (_, _, value) = run(&request(source, &json!("whole-file")));
    assert_eq!(value["ok"], false);
    assert_eq!(value["diagnostics"][0]["origin"], "policy");
    assert_eq!(
        value["diagnostics"][0]["code"],
        "krs::policy::non-krs-proc-macro"
    );
    assert_eq!(value["diagnostics"][0]["authored"], json!([9, 25]));
    assert_eq!(value["evidence"]["policy_version"], 1);
}

#[test]
fn inconsistent_requests_are_protocol_errors() {
    let mut cases = Vec::new();
    let mut wrong_path = request(TOUR_MINIMAL, &json!("whole-file"));
    wrong_path["file"]["virtual_path"] = json!("/workspace/other/src/lib.rs");
    cases.push(wrong_path);
    let mut wrong_module = request(TOUR_MINIMAL, &json!("whole-file"));
    wrong_module["module_path"] = json!(["other"]);
    cases.push(wrong_module);
    let mut wrong_alias = request(TOUR_MINIMAL, &json!("whole-file"));
    wrong_alias["facade"]["alias"] = json!("krs");
    cases.push(wrong_alias);
    let mut wrong_schema = request(TOUR_MINIMAL, &json!("whole-file"));
    wrong_schema["schema"] = json!(2);
    cases.push(wrong_schema);
    let mut unknown_field = request(TOUR_MINIMAL, &json!("whole-file"));
    unknown_field["extra"] = json!(true);
    cases.push(unknown_field);
    for case in cases {
        let (_, _, value) = run(&case);
        assert_eq!(value["ok"], false);
        assert_eq!(value["diagnostics"][0]["origin"], "protocol", "{case}");
        assert_eq!(value["diagnostics"][0]["code"], protocol::PROTOCOL_ERROR);
    }
}
