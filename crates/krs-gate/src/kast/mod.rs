//! Lossless KAST readers and policy-driven oracle operations.

mod canonical;
mod frontier;
mod inspect;
mod normalize;
mod policy;
mod project;
mod reader;

pub use canonical::canonical_json;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

fn string<'a>(request: &'a Value, key: &str) -> Result<&'a str, String> {
    request
        .get(key)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("request field `{key}` must be a string"))
}

fn input(request: &Value) -> Result<reader::Document, String> {
    let count = ["value", "text", "path"]
        .iter()
        .filter(|key| request.get(**key).is_some())
        .count();
    if count != 1 {
        return Err("KAST input requires exactly one of `value`, `text`, or `path`".into());
    }
    if let Some(value) = request.get("value") {
        return reader::from_value(value);
    }
    let text = if request.get("path").is_some() {
        std::fs::read_to_string(string(request, "path")?).map_err(|error| error.to_string())?
    } else {
        string(request, "text")?.to_owned()
    };
    reader::read(
        &text,
        request
            .get("allow_prefix")
            .and_then(Value::as_bool)
            .unwrap_or(false),
    )
}

fn present(value: Value, request: &Value) -> Result<Value, String> {
    match request
        .get("representation")
        .and_then(Value::as_str)
        .unwrap_or("value")
    {
        "value" => Ok(value),
        "canonical" => Ok(Value::String(canonical_json(&value))),
        "sha256" => Ok(Value::String(format!(
            "{:x}",
            Sha256::digest(canonical_json(&value).as_bytes())
        ))),
        "all" => {
            let canonical = canonical_json(&value);
            let sha256 = format!("{:x}", Sha256::digest(canonical.as_bytes()));
            Ok(json!({"value":value,"canonical":canonical,"sha256":sha256}))
        }
        other => Err(format!("unknown KAST result representation `{other}`")),
    }
}

pub(crate) fn dispatch(operation: &str, request: &Value) -> Result<Value, String> {
    let empty = json!({});
    let policy = request.get("policy").unwrap_or(&empty);
    let result = match operation {
        "kast.normalize" => normalize::normalize(
            &input(request)?,
            string(request, "variant")?,
            policy,
            request.get("label").and_then(Value::as_str),
        )?,
        "kast.project" => {
            if request.get("action").is_some() {
                return Err("kast.project accepts comparison requests without action".into());
            }
            let reference = input(request.get("reference").ok_or("missing reference input")?)?;
            let actual = input(request.get("actual").ok_or("missing actual input")?)?;
            let reference_policy = project::ProjectionPolicy::read(
                request
                    .get("reference_policy")
                    .ok_or("missing reference_policy")?,
            )?;
            let actual_policy = project::ProjectionPolicy::read(
                request
                    .get("actual_policy")
                    .ok_or("missing actual_policy")?,
            )?;
            project::compare_definitions(
                reference.definition()?,
                actual.definition()?,
                &reference_policy,
                &actual_policy,
                request
                    .get("compatible_sentence_pairs")
                    .unwrap_or(&json!([])),
            )?
        }
        "kast.frontier" => frontier::handle(request, &input(request)?)?,
        "kast.inspect" => inspect::handle(request, &input(request)?)?,
        _ => return Err(format!("unsupported KAST operation `{operation}`")),
    };
    present(result, request)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::session::Session;
    #[test]
    fn public_requests_are_independent_and_fail_closed() {
        let mut session = Session::new();
        let variable = json!({"node":"KVariable","name":"X"});
        let policy = json!({"label_map":{},"identity_labels":[],"sort_map":{},"identity_sorts":[]});
        let valid = session.dispatch(&json!({"id":"good","operation":"kast.normalize","value":variable,"variant":"behavior","policy":policy,"representation":"all"})).unwrap();
        let expected = json!({"node":"KVariable","name":"V0"});
        assert_eq!(valid["result"]["value"], expected);
        assert_eq!(valid["result"]["canonical"], canonical_json(&expected));
        assert_eq!(
            valid["result"]["sha256"],
            format!("{:x}", Sha256::digest(canonical_json(&expected).as_bytes()))
        );
        for value in [
            json!({"node":"Future"}),
            json!({"node":"KVariable","name":"X","extra":0}),
            json!({"node":"KApply","label":{"node":"KLabel","name":"f","params":[]},"args":[],"arity":1}),
        ] {
            assert!(session.dispatch(&json!({"id":"bad","operation":"kast.normalize","value":value,"variant":"behavior","policy":policy})).unwrap()["error"].is_object());
        }
        for operation in ["kast.read", "kast.policy"] {
            assert!(
                session
                    .dispatch(&json!({"id":"removed","operation":operation,"value":variable}))
                    .is_err()
            );
        }
        assert!(session.dispatch(&json!({"id":"shape","operation":"kast.normalize","value":variable,"text":"{}","variant":"behavior","policy":policy})).unwrap()["error"].is_object());
        let top = json!({"node":"KApply","label":{"node":"KLabel","name":"#Top","params":[]},"args":[],"arity":0});
        assert_eq!(session.dispatch(&json!({"id":"proof","operation":"kast.frontier","value":top,"returncode":0,"stderr":""})).unwrap()["result"]["status"], "proved");
    }
    #[test]
    fn deep_inline_terms_reach_the_lossless_reader() {
        let mut term = json!({"node":"KVariable","name":"X"});
        for _ in 0..140 {
            term = json!({"node":"KApply","label":{"node":"KLabel","name":"f","params":[]},"args":[term],"arity":1});
        }
        let request =
            json!({"id":"deep","operation":"kast.normalize","variant":"static_proof","value":term});
        let mut output = Vec::new();
        crate::session::serve(std::io::Cursor::new(format!("{request}\n")), &mut output).unwrap();
        let response = reader::json_value(std::str::from_utf8(&output).unwrap()).unwrap();
        assert!(
            response["error"]["message"]
                .as_str()
                .unwrap()
                .contains("sort")
        );
    }
    #[test]
    fn failed_load_keeps_inspection_available() {
        let mut session = Session::new();
        assert!(session.dispatch(&json!({"id":"load","operation":"definition.load","definition_ir":"/nonexistent","module":"M"})).unwrap()["error"].is_object());
        let value = json!({"node":"KSequence","arity":0,"items":[]});
        assert_eq!(session.dispatch(&json!({"id":"inspect","operation":"kast.inspect","action":"envelope","value":value,"policy":{}})).unwrap()["result"],reader::envelope(value));
    }
    fn claim_spec(labels: &[&str]) -> Value {
        let variable =
            json!({"node":"KVariable","name":"X","sort":{"node":"KSort","name":"Int","params":[]}});
        let claims = labels.iter().map(|label| json!({"node":"KClaim","body":variable,"requires":variable,"ensures":variable,"att":{"node":"KAtt","att":{"label":label,"digest":"removed"}}})).collect::<Vec<_>>();
        reader::envelope(
            json!({"node":"KFlatModuleList","mainModule":"SPEC","term":[{"node":"KFlatModule","name":"SPEC","imports":[],"localSentences":claims,"att":{"node":"KAtt","att":{}}}]}),
        )
    }

    #[test]
    fn claim_requests_select_and_validate_labels_before_normalization() {
        let mut session = Session::new();
        let spec = claim_spec(&["case"]);
        let result = session.dispatch(&json!({"id":"claim","operation":"kast.normalize","variant":"static_claim","value":spec,"label":"case"})).unwrap();
        assert_eq!(
            result["result"]["term"]["term"][0]["localSentences"][0]["body"]["name"],
            "V0"
        );
        assert_eq!(
            result["result"]["term"]["term"][0]["localSentences"][0]["att"]["att"],
            json!({"label":"case"})
        );
        for (value, label) in [
            (spec.clone(), "other"),
            (claim_spec(&["case", "other"]), "case"),
        ] {
            assert!(session.dispatch(&json!({"id":"invalid","operation":"kast.normalize","variant":"static_claim","value":value,"label":label})).unwrap()["error"].is_object());
        }
        let policy = json!({"identity_labels":["case"],"identity_sorts":["Int"],"known_attributes":["label","digest"],"metadata_attributes":["digest"]});
        let result = session.dispatch(&json!({"id":"selected","operation":"kast.normalize","variant":"proof_claim","value":spec,"label":"case","policy":policy})).unwrap();
        assert_eq!(result["result"]["format"], "KRS-IMP-CLAIM");
        assert_eq!(result["result"]["term"]["body"]["name"], "O0");
    }

    #[test]
    fn projection_request_compares_two_definitions_with_closed_policies() {
        let mut session = Session::new();
        let value = reader::envelope(
            json!({"node":"KDefinition","mainModule":"MAIN","modules":[{"node":"KFlatModule","name":"MAIN","imports":[],"localSentences":[],"att":{"node":"KAtt","att":{}}}],"att":{"node":"KAtt","att":{}}}),
        );
        let policy = json!({"module_origins":{"MAIN":"origin"},"identity_names":["MAIN"]});
        let request = json!({"id":"compare","operation":"kast.project","reference":{"value":value},"actual":{"value":value},"reference_policy":policy,"actual_policy":policy});
        let result = session.dispatch(&request).unwrap();
        assert_eq!(
            result["result"]["baseline_sha256"],
            result["result"]["actual_sha256"]
        );
        assert_eq!(result["result"]["sentence_count"], 0);
        let mut invalid = request;
        invalid["actual_policy"]["identity_names"] = json!([]);
        assert!(
            session.dispatch(&invalid).unwrap()["error"]["message"]
                .as_str()
                .unwrap()
                .contains("unknown name")
        );
    }
}
