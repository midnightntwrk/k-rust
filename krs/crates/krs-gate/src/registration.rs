//! Whole-file expansions from the product's renderer: explicit registration
//! tables, and the digest of a file's macro output.

use krs_expand::whole_file::{self, ExpandDiagnostic, FileExpansion, FileRequest, Selection};
use krs_ir::ByteRange;
use quote::ToTokens;
use serde::Deserialize;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::{error::Error, fs};

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct TableRequest {
    #[serde(rename = "id")]
    _id: String,
    #[serde(rename = "operation")]
    _operation: String,
    source: String,
    display_file: String,
    crate_name: String,
    facade_alias: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct DigestRequest {
    #[serde(rename = "id")]
    _id: String,
    #[serde(rename = "operation")]
    _operation: String,
    source: String,
    display_file: String,
    module_path: Vec<String>,
    facade_alias: String,
}

/// Dispatch `registration.table` or `expansion.digest`.
///
/// # Errors
///
/// Returns an error for an unknown operation or unknown fields, unreadable
/// UTF-8 source, an invalid facade path, or, for `registration.table`, any
/// whole-file expansion diagnostic.
pub fn dispatch(request: &Value) -> Result<Value, Box<dyn Error>> {
    let operation = request
        .get("operation")
        .and_then(Value::as_str)
        .unwrap_or_default();
    match operation {
        "registration.table" => table(serde_json::from_value(request.clone())?),
        "expansion.digest" => digest(serde_json::from_value(request.clone())?),
        _ => Err(format!("unsupported registration operation `{operation}`").into()),
    }
}

/// Expand an authored crate root and return its explicit registration table.
fn table(request: TableRequest) -> Result<Value, Box<dyn Error>> {
    let TableRequest {
        source,
        display_file,
        crate_name,
        facade_alias,
        ..
    } = request;
    let (expansion, facade) = expand(&source, &display_file, &[crate_name], &facade_alias)?;
    let expansion = expansion.map_err(|diagnostics| {
        diagnostics
            .iter()
            .map(|diagnostic| format!("{}: {}", diagnostic.code, diagnostic.message))
            .collect::<Vec<_>>()
            .join("\n")
    })?;
    let table = whole_file::registration_table(&facade, &expansion.registrations);
    if !expansion.generated.text.ends_with(&table) {
        return Err("the rendered registration table is not the one the expansion appends".into());
    }
    let registrations = expansion
        .registrations
        .iter()
        .map(|registration| {
            json!({
                "module_path": registration.module_path,
                "factory": registration.factory,
                "cfg": registration.cfg,
            })
        })
        .collect::<Vec<_>>();
    Ok(json!({
        "table": table,
        "registrations": registrations,
    }))
}

/// Expand an authored file and digest what the expander produces for it: the
/// generated text and its source map, with every invocation and classified
/// segment, or the diagnostics with which it refuses the file.
fn digest(request: DigestRequest) -> Result<Value, Box<dyn Error>> {
    let DigestRequest {
        source,
        display_file,
        module_path,
        facade_alias,
        ..
    } = request;
    if module_path.is_empty() {
        return Err("`module_path` must start with the crate name".into());
    }
    let range = |range: ByteRange| json!([range.start(), range.end()]);
    let sha256 = |text: &str| format!("{:x}", Sha256::digest(text.as_bytes()));
    let expansion = match expand(&source, &display_file, &module_path, &facade_alias)?.0 {
        Ok(expansion) => expansion,
        Err(diagnostics) => {
            let refusal = diagnostics
                .iter()
                .map(|diagnostic| {
                    json!({
                        "code": diagnostic.code.as_str(),
                        "message": diagnostic.message,
                        "class": diagnostic.class.name(),
                        "authored": diagnostic.authored.map(range),
                        "invocation": diagnostic.invocation.map(|invocation| invocation.0),
                    })
                })
                .collect::<Vec<_>>();
            return Ok(json!({
                "refusal_sha256": sha256(&serde_json::to_string(&refusal)?),
                "diagnostics": diagnostics.len(),
            }));
        }
    };
    let generated = &expansion.generated;
    let map = json!({
        "version": generated.map.version,
        "generated_file": generated.map.generated_file,
        "authored_file": generated.map.authored_file,
        "invocations": generated.map.invocations.iter().map(|invocation| json!({
            "kind": invocation.kind,
            "call_site": range(invocation.call_site),
            "replaced": range(invocation.replaced),
            "parent": invocation.parent.map(|parent| parent.0),
        })).collect::<Vec<_>>(),
        "segments": generated.map.segments.iter().map(|segment| json!({
            "generated": range(segment.generated),
            "class": segment.class.name(),
            "authored": segment.authored.map(range),
            "owner": segment.owner.map(|owner| owner.0),
            "respanned": segment.respanned.map(range),
        })).collect::<Vec<_>>(),
    });
    Ok(json!({
        "text_sha256": sha256(&generated.text),
        "source_map_sha256": sha256(&serde_json::to_string(&map)?),
        "invocations": generated.map.invocations.len(),
        "segments": generated.map.segments.len(),
    }))
}

/// The whole-file expansion of `source` as the module `module_path` of its
/// crate, or the expander's diagnostics, and the facade path spelled as the
/// registration table spells it.
type Expanded = (Result<FileExpansion, Vec<ExpandDiagnostic>>, String);

/// Expand `source` whole, as the module `module_path` of its crate.
fn expand(
    source: &str,
    display_file: &str,
    module_path: &[String],
    facade_alias: &str,
) -> Result<Expanded, Box<dyn Error>> {
    let source = fs::read_to_string(source)?;
    let facade_path: syn::Path = syn::parse_str(&format!("::{facade_alias}"))?;
    let facade = facade_path.to_token_stream().to_string().replace(' ', "");
    let expansion = whole_file::expand_file(&FileRequest {
        display_file,
        source: &source,
        generated_file: display_file,
        facade_alias,
        facade_path,
        module_path,
        selection: &Selection::WholeFile,
    });
    Ok((expansion, facade))
}

#[cfg(test)]
mod tests {
    use crate::session::Session;
    use krs_expand::whole_file::REGISTRATION_SCOPE;
    use serde_json::{Value, json};

    fn request(source: &std::path::Path) -> Value {
        json!({
            "id": "table", "operation": "registration.table",
            "source": source, "display_file": "src/lib.rs",
            "crate_name": "lesson", "facade_alias": "k",
        })
    }

    #[test]
    fn table_preserves_false_cfg_and_uses_the_product_renderer() {
        let directory = krs_test_support::temp_dir();
        let source = directory.path().join("lib.rs");
        std::fs::write(
            &source,
            r"
#[k::sort(alias = Visible)]
pub trait VisibleSort {}
#[k::sort(alias = Hidden)]
#[cfg(any())]
pub trait HiddenSort {}
",
        )
        .unwrap();
        let response = Session::new().dispatch(&request(&source)).unwrap();
        let result = &response["result"];
        let registrations = result["registrations"].as_array().unwrap();
        assert_eq!(registrations.len(), 2);
        assert_eq!(registrations[0]["module_path"], json!(["lesson"]));
        assert_eq!(registrations[0]["cfg"], json!([]));
        assert_eq!(registrations[1]["module_path"], json!(["lesson"]));
        assert_eq!(registrations[1]["cfg"], json!(["#[cfg (any ())]"]));
        let table = result["table"].as_str().unwrap();
        assert!(table.contains("::k::__private::RegistrationTable"));
        let hidden = registrations[1]["factory"].as_str().unwrap();
        assert!(table.contains(&format!(
            "#[cfg (any ())] registrar.factory(crate::{hidden});"
        )));
    }

    fn digest(source: &std::path::Path, text: &str, module_path: &Value) -> Value {
        std::fs::write(source, text).unwrap();
        Session::new()
            .dispatch(&json!({
                "id": "digest", "operation": "expansion.digest",
                "source": source, "display_file": "src/lib.rs",
                "module_path": module_path, "facade_alias": "k",
            }))
            .unwrap()
    }

    #[test]
    fn digest_pins_the_generated_text_and_its_source_map() {
        let directory = krs_test_support::temp_dir();
        let source = directory.path().join("lib.rs");
        let crate_root = json!(["lesson"]);
        let base = digest(&source, "k::sorts! { A; B; }\n", &crate_root)["result"].clone();
        assert_eq!(
            base,
            digest(&source, "k::sorts! { A; B; }\n", &crate_root)["result"]
        );
        assert!(base["invocations"].as_u64().unwrap() >= 1);
        // The same invocation one byte later moves its authored ranges.
        let moved = digest(&source, "\nk::sorts! { A; B; }\n", &crate_root)["result"].clone();
        assert_ne!(base["source_map_sha256"], moved["source_map_sha256"]);
        let renamed = digest(&source, "k::sorts! { A; C; }\n", &crate_root)["result"].clone();
        assert_ne!(base["text_sha256"], renamed["text_sha256"]);
        let nested = digest(
            &source,
            "k::sorts! { A; B; }\n",
            &json!(["lesson", "inner"]),
        );
        assert_ne!(base["text_sha256"], nested["result"]["text_sha256"]);
    }

    #[test]
    fn digest_pins_a_refusal_by_its_diagnostics() {
        let directory = krs_test_support::temp_dir();
        let source = directory.path().join("lib.rs");
        let nested = "mod inner { k::sorts! { A; B; } }";
        let refused = digest(&source, nested, &json!(["lesson"]))["result"].clone();
        assert_eq!(refused["diagnostics"], json!(2));
        assert!(refused.get("text_sha256").is_none());
        let renamed = digest(
            &source,
            "mod inner { k::sorts! { A; C; } }",
            &json!(["lesson"]),
        );
        assert_ne!(
            refused["refusal_sha256"],
            renamed["result"]["refusal_sha256"]
        );
    }

    #[test]
    fn digest_needs_a_module_path() {
        let directory = krs_test_support::temp_dir();
        let source = directory.path().join("lib.rs");
        let response = digest(&source, "fn ordinary() {}", &json!([]));
        assert!(
            response["error"]["message"]
                .as_str()
                .unwrap()
                .contains("must start with the crate name")
        );
    }

    #[test]
    fn unknown_fields_are_response_errors() {
        let mut request = request(std::path::Path::new("unused.rs"));
        request["extra"] = json!(true);
        let response = Session::new().dispatch(&request).unwrap();
        assert!(
            response["error"]["message"]
                .as_str()
                .unwrap()
                .contains("unknown field `extra`")
        );
    }

    #[test]
    fn non_root_factories_report_the_product_scope_diagnostic() {
        let directory = krs_test_support::temp_dir();
        let source = directory.path().join("lib.rs");
        std::fs::write(&source, "mod inner { k::sorts! { A; B; } }").unwrap();
        let response = Session::new().dispatch(&request(&source)).unwrap();
        let message = response["error"]["message"].as_str().unwrap();
        assert!(message.contains(REGISTRATION_SCOPE.as_str()));
        assert_eq!(message.matches(REGISTRATION_SCOPE.as_str()).count(), 2);
        assert!(message.contains("not defined at the crate root"));
    }

    #[test]
    fn table_remains_available_after_a_failed_load() {
        let directory = krs_test_support::temp_dir();
        let source = directory.path().join("lib.rs");
        std::fs::write(&source, "fn ordinary() {}").unwrap();
        let mut session = Session::new();
        let failed = session
            .dispatch(&json!({
                "id": "load", "operation": "definition.load", "module": "MAIN",
                "definition_ir": directory.path().join("missing.json"),
            }))
            .unwrap();
        assert!(failed.get("error").is_some());
        let response = session.dispatch(&request(&source)).unwrap();
        assert_eq!(response["result"]["registrations"], json!([]));
        assert!(response["result"].get("requests_framework").is_none());
        assert!(
            response["result"]["table"]
                .as_str()
                .unwrap()
                .contains("let _ = registrar;")
        );
    }
}
