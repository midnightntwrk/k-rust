//! Explicit registration tables from the product's whole-file renderer.

use krs_expand::whole_file::{self, FileRequest, Selection};
use quote::ToTokens;
use serde::Deserialize;
use serde_json::{Value, json};
use std::{error::Error, fs};

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Request {
    #[serde(rename = "id")]
    _id: String,
    operation: String,
    source: String,
    display_file: String,
    crate_name: String,
    facade_alias: String,
}

/// Expand an authored crate root and return its explicit registration table.
///
/// # Errors
///
/// Returns an error for unknown fields, unreadable UTF-8 source, an invalid
/// facade path, or any whole-file expansion diagnostic.
pub fn dispatch(request: &Value) -> Result<Value, Box<dyn Error>> {
    let request: Request = serde_json::from_value(request.clone())?;
    let Request {
        _id: _,
        operation,
        source,
        display_file,
        crate_name,
        facade_alias,
    } = request;
    if operation != "registration.table" {
        return Err(format!("unsupported registration operation `{operation}`").into());
    }
    let source = fs::read_to_string(source)?;
    let facade_path: syn::Path = syn::parse_str(&format!("::{facade_alias}"))?;
    let facade = facade_path.to_token_stream().to_string().replace(' ', "");
    let expansion = whole_file::expand_file(&FileRequest {
        display_file: &display_file,
        source: &source,
        generated_file: &display_file,
        facade_alias: &facade_alias,
        facade_path,
        module_path: &[crate_name],
        selection: &Selection::WholeFile,
    })
    .map_err(|diagnostics| {
        diagnostics
            .iter()
            .map(|diagnostic| format!("{}: {}", diagnostic.code, diagnostic.message))
            .collect::<Vec<_>>()
            .join("\n")
    })?;
    let table = whole_file::registration_table(
        &facade,
        expansion.requests_framework,
        &expansion.registrations,
    );
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
        "requests_framework": expansion.requests_framework,
        "registrations": registrations,
    }))
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
        assert_eq!(response["result"]["requests_framework"], false);
        assert!(
            response["result"]["table"]
                .as_str()
                .unwrap()
                .contains("let _ = registrar;")
        );
    }
}
