//! Read KAST once and verify the typed writer preserves all input fields.
//!
//! upstream k-rust/kast-definition-json-completeness: k-rust's typed definition reader omits
//! `badsentence` nodes and its model has no `KFlatModuleList` envelope, so this module
//! re-inserts each omitted sentinel and writes the module-list wrapper itself.

use std::{collections::BTreeMap, sync::Arc};

use k_rust::{
    definition::{Attributes, Definition, FlatModule, Sentence},
    kast::Term,
};
use serde_json::{Value, json};

#[derive(Clone, Debug)]
pub(crate) struct DefinitionDocument {
    pub(crate) definition: Definition,
    pub(crate) bad_sentences: BTreeMap<usize, BTreeMap<usize, Value>>,
}

#[derive(Clone, Debug)]
pub(crate) enum Document {
    Term(Term),
    Definition(DefinitionDocument),
    ModuleList {
        main_module: String,
        modules: Vec<FlatModule>,
    },
}

impl Document {
    pub(crate) fn term(&self) -> Result<&Term, String> {
        match self {
            Self::Term(term) => Ok(term),
            _ => Err("KAST input must be a term".into()),
        }
    }
    pub(crate) fn definition(&self) -> Result<&DefinitionDocument, String> {
        match self {
            Self::Definition(definition) => Ok(definition),
            _ => Err("KAST input must be a definition".into()),
        }
    }
    pub(crate) fn to_value(&self) -> Result<Value, String> {
        match self {
            Self::Term(term) => Ok(envelope(term_value(term)?)),
            Self::Definition(definition) => definition_value(definition),
            Self::ModuleList {
                main_module,
                modules,
            } => Ok(envelope(
                // upstream k-rust/kast-definition-json-completeness: KRS writes this wrapper.
                json!({"node":"KFlatModuleList","mainModule":main_module,"term":modules.iter().map(module_value).collect::<Result<Vec<_>,_>>()?}),
            )),
        }
    }
}

pub(crate) fn envelope(term: Value) -> Value {
    let mut value =
        json!({"format":k_rust::kast::json::FORMAT,"version":k_rust::kast::json::VERSION});
    value
        .as_object_mut()
        .expect("envelope object")
        .insert("term".into(), term);
    value
}

pub(crate) fn read(text: &str, allow_prefix: bool) -> Result<Document, String> {
    let text = if allow_prefix {
        &text[text.find('{').ok_or("KAST output has no JSON envelope")?..]
    } else {
        text
    };
    let value = json_value(text)?;
    check_envelope(&value)?;
    from_value(&value)
}

pub(crate) fn check_envelope(value: &Value) -> Result<(), String> {
    let object = value.as_object().ok_or("KAST envelope is not an object")?;
    if object.len() != 3
        || !object.contains_key("term")
        || value["format"] != "KAST"
        || value["version"] != k_rust::kast::json::VERSION
    {
        return Err(format!(
            "output is not exactly a KAST v{} envelope",
            k_rust::kast::json::VERSION
        ));
    }
    Ok(())
}

pub(crate) fn json_value(text: &str) -> Result<Value, String> {
    let mut decoder = serde_json::Deserializer::from_str(text);
    decoder.disable_recursion_limit();
    let value = serde::Deserialize::deserialize(&mut decoder)
        .map_err(|error| format!("invalid KAST JSON: {error}"))?;
    decoder
        .end()
        .map_err(|error| format!("invalid KAST JSON: {error}"))?;
    Ok(value)
}

fn equal(input: &Value, output: &str) -> Result<(), String> {
    unchanged(input, &json_value(output)?)
}

fn unchanged(input: &Value, output: &Value) -> Result<(), String> {
    if output == input {
        Ok(())
    } else {
        Err(
            "KAST typed round trip changed input; unknown fields or unsupported representation"
                .into(),
        )
    }
}

pub(crate) fn term(value: &Value) -> Result<Term, String> {
    let input = envelope(value.clone());
    let typed = k_rust::kast::json::from_str(&input.to_string()).map_err(|e| e.to_string())?;
    equal(
        &input,
        &k_rust::kast::json::to_string(&typed).map_err(|e| e.to_string())?,
    )?;
    Ok(typed)
}

pub(crate) fn term_value(term: &Term) -> Result<Value, String> {
    Ok(
        json_value(&k_rust::kast::json::to_string(term).map_err(|e| e.to_string())?)?["term"]
            .take(),
    )
}

/// The sentinel K's KAST v4 writer leaves in place of a sentence it cannot represent (a context alias).
/// upstream k-rust/kast-definition-json-completeness: k-rust's reader omits it, so KRS restores it.
fn bad_sentence() -> Value {
    json!({"node":"badsentence"})
}

pub(crate) fn definition_document(value: &Value) -> Result<DefinitionDocument, String> {
    check_envelope(value)?;
    let (definition, omitted) =
        k_rust::definition::json::from_str_omitting_unrepresentable(&value.to_string())
            .map_err(|e| e.to_string())?;
    let mut bad_sentences = BTreeMap::<usize, BTreeMap<usize, Value>>::new();
    for sentence in omitted {
        bad_sentences
            .entry(sentence.module_index)
            .or_default()
            .insert(sentence.index, bad_sentence());
    }
    let document = DefinitionDocument {
        definition,
        bad_sentences,
    };
    // The lossy reader skips a badsentence node whatever its fields; the round trip restores only the exact sentinel.
    unchanged(value, &definition_value(&document)?)?;
    Ok(document)
}

pub(crate) fn from_value(value: &Value) -> Result<Document, String> {
    let bare = if value.get("format").is_some() {
        check_envelope(value)?;
        &value["term"]
    } else {
        value
    };
    match bare["node"].as_str() {
        Some("KDefinition") => Ok(Document::Definition(definition_document(&envelope(
            bare.clone(),
        ))?)),
        Some("KFlatModuleList") => {
            let input = envelope(bare.clone());
            let list = k_rust::definition::json::module_list_from_str(&input.to_string())
                .map_err(|e| e.to_string())?;
            let document = Document::ModuleList {
                main_module: list.main_module,
                modules: list.modules,
            };
            unchanged(&input, &document.to_value()?)?;
            Ok(document)
        }
        _ => Ok(Document::Term(term(bare)?)),
    }
}

pub(crate) fn definition_value(document: &DefinitionDocument) -> Result<Value, String> {
    let mut value = json_value(
        &k_rust::definition::json::to_string(&document.definition).map_err(|e| e.to_string())?,
    )?;
    for (index, positions) in &document.bad_sentences {
        let sentences = value["term"]["modules"][*index]["localSentences"]
            .as_array_mut()
            .ok_or("writer omitted module sentences")?;
        for (position, sentinel) in positions {
            sentences.insert(*position, sentinel.clone());
        }
    }
    Ok(value)
}

pub(crate) fn module_value(module: &FlatModule) -> Result<Value, String> {
    let definition = Definition {
        main_module: module.name.clone(),
        modules: vec![module.clone()],
        attributes: Attributes::default(),
    };
    Ok(
        json_value(&k_rust::definition::json::to_string(&definition).map_err(|e| e.to_string())?)?
            ["term"]["modules"][0]
            .take(),
    )
}

pub(crate) fn sentence_value(sentence: &Sentence) -> Result<Value, String> {
    Ok(module_value(&FlatModule {
        name: "MAIN".into(),
        imports: vec![],
        local_sentences: vec![Arc::new(sentence.clone())],
        attributes: Attributes::default(),
    })?["localSentences"][0]
        .take())
}

pub(crate) fn payload_sentence(value: &Value) -> Result<Sentence, String> {
    let document = definition_document(&envelope(
        json!({"node":"KDefinition","mainModule":"MAIN","modules":[{"node":"KFlatModule","name":"MAIN","imports":[],"localSentences":[value],"att":{"node":"KAtt","att":{}}}],"att":{"node":"KAtt","att":{}}}),
    ))?;
    document.definition.modules[0]
        .local_sentences
        .first()
        .map(|sentence| sentence.as_ref().clone())
        .ok_or_else(|| "attribute payload is not a typed sentence".into())
}

pub(crate) fn payload_module(value: &Value) -> Result<FlatModule, String> {
    let main = value["name"]
        .as_str()
        .ok_or("attribute module name must be a string")?;
    let document = definition_document(&envelope(
        json!({"node":"KDefinition","mainModule":main,"modules":[value],"att":{"node":"KAtt","att":{}}}),
    ))?;
    if !document.bad_sentences.is_empty() {
        return Err("attribute module contains badsentence".into());
    }
    document
        .definition
        .modules
        .into_iter()
        .next()
        .ok_or_else(|| "attribute module is missing".into())
}

pub(crate) fn payload_attributes(value: &Value) -> Result<Attributes, String> {
    let document = definition_document(&envelope(
        json!({"node":"KDefinition","mainModule":"MAIN","modules":[{"node":"KFlatModule","name":"MAIN","imports":[],"localSentences":[],"att":value}],"att":{"node":"KAtt","att":{}}}),
    ))?;
    Ok(document.definition.modules[0].attributes.clone())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn reader_version_matches_lock() {
        let lock = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../Krs.lock"));
        let schemas = lock
            .split("[schemas]")
            .nth(1)
            .unwrap()
            .split('[')
            .next()
            .unwrap();
        let pin = schemas
            .lines()
            .find_map(|line| line.trim().strip_prefix("kast_json = "))
            .unwrap()
            .parse::<u32>()
            .unwrap();
        assert_eq!(k_rust::kast::json::VERSION, pin);
    }
    #[test]
    fn lossless_and_prefix_checks() {
        let value = envelope(json!({"node":"KVariable","name":"X"}));
        assert!(read(&format!("Steps: 3\n{value}"), false).is_err());
        assert_eq!(
            read(&format!("Steps: 3\n{value}"), true)
                .unwrap()
                .to_value()
                .unwrap(),
            value
        );
        let mut unknown = value;
        unknown["term"]["future"] = true.into();
        assert!(from_value(&unknown).is_err());
        unknown["version"] = 5.into();
        assert!(from_value(&unknown).is_err());
        assert!(from_value(&json!({"node":"Future"})).is_err());
        assert!(from_value(&json!({"node":"KApply","label":{"node":"KLabel","name":"f","params":[]},"args":[],"arity":1})).is_err());
    }
    #[test]
    fn fallback_sentinel_is_exact() {
        let value = envelope(
            json!({"node":"KDefinition","mainModule":"MAIN","modules":[{"node":"KFlatModule","name":"MAIN","imports":[],"localSentences":[{"node":"badsentence"}],"att":{"node":"KAtt","att":{}}}],"att":{"node":"KAtt","att":{}}}),
        );
        assert_eq!(from_value(&value).unwrap().to_value().unwrap(), value);
        let mut bad = value;
        bad["term"]["modules"][0]["localSentences"][0]["body"] = Value::Null;
        assert!(from_value(&bad).is_err());
    }
    #[test]
    fn module_list_wrapper_and_typed_contents_are_lossless() {
        let value = envelope(
            json!({"node":"KFlatModuleList","mainModule":"SPEC","term":[{"node":"KFlatModule","name":"SPEC","imports":[],"localSentences":[],"att":{"node":"KAtt","att":{}}}]}),
        );
        assert_eq!(from_value(&value).unwrap().to_value().unwrap(), value);
        let mut invalid = value.clone();
        invalid["term"]["extra"] = true.into();
        assert!(from_value(&invalid).is_err());
        invalid = value;
        invalid["term"]["term"][0]["extra"] = true.into();
        assert!(from_value(&invalid).is_err());
        assert!(read(r#"{"node":"KVariable","name":"X"}"#, false).is_err());
        let unlisted_main =
            envelope(json!({"node":"KFlatModuleList","mainModule":"SPEC","term":[]}));
        assert!(from_value(&unlisted_main).is_err());
    }
}
