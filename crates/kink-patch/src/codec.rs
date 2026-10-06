//! Canonical patch v1, using metadata-free k-rust KAST values.

use crate::{
    CANONICAL_PATCH_DOMAIN, Edit, InsertPosition, Patch, PatchModelError, SentenceFingerprint,
    SentenceRef, Sha256Digest, TermRef, canonical_json, payload_digest,
};
use k_rust::{
    definition::{Attributes, Definition, FlatModule, Sentence},
    kast::Term,
};
use serde_json::{Value, json};
use std::sync::Arc;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CodecError {
    Unpinned,
    ContextAlias,
    Encode(String),
    Decode(String),
    NonCanonical,
    Model(PatchModelError),
}
impl std::fmt::Display for CodecError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::error::Error for CodecError {}

impl Patch {
    pub fn canonical_value(&self) -> Result<Value, CodecError> {
        if !self.is_pinned() {
            return Err(CodecError::Unpinned);
        }
        let edits = self
            .edits()
            .iter()
            .map(encode_edit)
            .collect::<Result<Vec<_>, _>>()?;
        let pins = self.pins().iter().map(|(at, fingerprint)| json!({"module":at.module,"index":at.index,"fingerprint":fingerprint.to_string()})).collect::<Vec<_>>();
        Ok(json!({"version":1,"edits":edits,"pins":pins}))
    }
    pub fn canonical_json(&self) -> Result<String, CodecError> {
        Ok(canonical_json(&self.canonical_value()?))
    }
    pub fn digest(&self) -> Result<Sha256Digest, CodecError> {
        Ok(payload_digest(
            CANONICAL_PATCH_DOMAIN,
            self.canonical_json()?.as_bytes(),
        ))
    }
    pub fn from_canonical_json(text: &str) -> Result<Self, CodecError> {
        let value: Value =
            serde_json::from_str(text).map_err(|e| CodecError::Decode(e.to_string()))?;
        exact(&value, &["version", "edits", "pins"])?;
        if value["version"].as_u64() != Some(1) {
            return Err(decode("unknown patch version"));
        }
        let edits = array(&value["edits"])?
            .iter()
            .map(decode_edit)
            .collect::<Result<Vec<_>, _>>()?;
        let pins = array(&value["pins"])?
            .iter()
            .map(|pin| {
                exact(pin, &["module", "index", "fingerprint"])?;
                let at = SentenceRef::new(string(&pin["module"])?, u32_value(&pin["index"])?);
                let fingerprint = SentenceFingerprint::parse(string(&pin["fingerprint"])?)
                    .ok_or_else(|| decode("fingerprint"))?;
                Ok((at, fingerprint))
            })
            .collect::<Result<Vec<_>, CodecError>>()?;
        let patch = Self::with_pins(edits, pins).map_err(CodecError::Model)?;
        if patch.canonical_json()? != text {
            return Err(CodecError::NonCanonical);
        }
        Ok(patch)
    }
}

fn reference(at: &SentenceRef) -> Value {
    json!({"module":at.module,"index":at.index})
}
fn position(at: &InsertPosition) -> Value {
    match at {
        InsertPosition::Before(at) => json!({"before":reference(at)}),
        InsertPosition::After(at) => json!({"after":reference(at)}),
        InsertPosition::ModuleStart(module) => json!({"module-start":module}),
        InsertPosition::ModuleEnd(module) => json!({"module-end":module}),
    }
}
fn term(term: &Term) -> Result<Value, CodecError> {
    let text =
        k_rust::kast::json::to_string(term).map_err(|e| CodecError::Encode(e.to_string()))?;
    serde_json::from_str(&text).map_err(|e| CodecError::Encode(e.to_string()))
}
fn sentence(sentence: &Sentence) -> Result<Value, CodecError> {
    if matches!(sentence, Sentence::ContextAlias { .. }) {
        return Err(CodecError::ContextAlias);
    }
    let definition = Definition {
        main_module: String::new(),
        modules: vec![FlatModule {
            name: String::new(),
            imports: Vec::new(),
            local_sentences: vec![Arc::new(sentence.clone())],
            attributes: Attributes::default(),
        }],
        attributes: Attributes::default(),
    };
    let text = k_rust::definition::json::to_string(&definition)
        .map_err(|e| CodecError::Encode(e.to_string()))?;
    serde_json::from_str(&text).map_err(|e| CodecError::Encode(e.to_string()))
}
fn encode_edit(edit: &Edit) -> Result<Value, CodecError> {
    Ok(match edit {
        Edit::ReplaceTerm {
            at,
            expected,
            replacement,
        } => {
            json!({"op":"replace-term","sentence":reference(&at.sentence),"path":at.path.0,"expected":term(expected)?,"replacement":term(replacement)?})
        }
        Edit::ReplaceSentence { at, replacement } => {
            json!({"op":"replace-sentence","sentence":reference(at),"replacement":sentence(replacement)?})
        }
        Edit::DeleteSentence { at } => json!({"op":"delete-sentence","sentence":reference(at)}),
        Edit::InsertSentence {
            position: at,
            ordinal,
            sentence: s,
        } => {
            json!({"op":"insert-sentence","position":position(at),"ordinal":ordinal,"sentence":sentence(s)?})
        }
        Edit::AddAttribute { at, key, value } => {
            json!({"op":"add-attribute","sentence":reference(at),"key":key,"value":value})
        }
        Edit::RemoveAttribute { at, key, expected } => {
            json!({"op":"remove-attribute","sentence":reference(at),"key":key,"expected":expected})
        }
        Edit::ReplaceAttribute {
            at,
            key,
            expected,
            replacement,
        } => {
            json!({"op":"replace-attribute","sentence":reference(at),"key":key,"expected":expected,"replacement":replacement})
        }
    })
}
fn decode(detail: &str) -> CodecError {
    CodecError::Decode(detail.to_owned())
}
fn exact(value: &Value, keys: &[&str]) -> Result<(), CodecError> {
    let object = value.as_object().ok_or_else(|| decode("expected object"))?;
    if object.len() != keys.len() || keys.iter().any(|key| !object.contains_key(*key)) {
        return Err(decode("unexpected object keys"));
    }
    Ok(())
}
fn string(value: &Value) -> Result<&str, CodecError> {
    value.as_str().ok_or_else(|| decode("expected string"))
}
fn array(value: &Value) -> Result<&Vec<Value>, CodecError> {
    value.as_array().ok_or_else(|| decode("expected array"))
}
fn u32_value(value: &Value) -> Result<u32, CodecError> {
    value
        .as_u64()
        .and_then(|v| u32::try_from(v).ok())
        .ok_or_else(|| decode("expected u32"))
}
fn decode_reference(value: &Value) -> Result<SentenceRef, CodecError> {
    exact(value, &["module", "index"])?;
    Ok(SentenceRef::new(
        string(&value["module"])?,
        u32_value(&value["index"])?,
    ))
}
fn decode_position(value: &Value) -> Result<InsertPosition, CodecError> {
    let object = value.as_object().ok_or_else(|| decode("position object"))?;
    if object.len() != 1 {
        return Err(decode("position keys"));
    }
    let (key, value) = object.iter().next().expect("one key");
    match key.as_str() {
        "before" => Ok(InsertPosition::Before(decode_reference(value)?)),
        "after" => Ok(InsertPosition::After(decode_reference(value)?)),
        "module-start" => Ok(InsertPosition::ModuleStart(string(value)?.into())),
        "module-end" => Ok(InsertPosition::ModuleEnd(string(value)?.into())),
        _ => Err(decode("position kind")),
    }
}
fn decode_term(value: &Value) -> Result<Term, CodecError> {
    k_rust::kast::json::from_str(&canonical_json(value))
        .map_err(|e| CodecError::Decode(e.to_string()))
}
fn decode_sentence(value: &Value) -> Result<Sentence, CodecError> {
    let definition = k_rust::definition::json::from_str(&canonical_json(value))
        .map_err(|e| CodecError::Decode(e.to_string()))?;
    let [module] = definition.modules.as_slice() else {
        return Err(decode("one sentence module required"));
    };
    let [sentence] = module.local_sentences.as_slice() else {
        return Err(decode("one sentence required"));
    };
    if !definition.main_module.is_empty()
        || !module.name.is_empty()
        || !module.imports.is_empty()
        || definition.attributes != Attributes::default()
        || module.attributes != Attributes::default()
    {
        return Err(decode("nonempty sentence envelope"));
    }
    if matches!(**sentence, Sentence::ContextAlias { .. }) {
        return Err(CodecError::ContextAlias);
    }
    Ok((**sentence).clone())
}
fn decode_edit(value: &Value) -> Result<Edit, CodecError> {
    let op = string(&value["op"])?;
    let keys: &[&str] = match op {
        "replace-term" => &["op", "sentence", "path", "expected", "replacement"],
        "replace-sentence" => &["op", "sentence", "replacement"],
        "delete-sentence" => &["op", "sentence"],
        "insert-sentence" => &["op", "position", "ordinal", "sentence"],
        "add-attribute" => &["op", "sentence", "key", "value"],
        "remove-attribute" => &["op", "sentence", "key", "expected"],
        "replace-attribute" => &["op", "sentence", "key", "expected", "replacement"],
        _ => return Err(decode("edit operation")),
    };
    exact(value, keys)?;
    if op == "insert-sentence" {
        return Ok(Edit::InsertSentence {
            position: decode_position(&value["position"])?,
            ordinal: u32_value(&value["ordinal"])?,
            sentence: decode_sentence(&value["sentence"])?,
        });
    }
    let at = decode_reference(&value["sentence"])?;
    Ok(match op {
        "replace-term" => Edit::ReplaceTerm {
            at: TermRef::new(
                at,
                array(&value["path"])?
                    .iter()
                    .map(u32_value)
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            expected: decode_term(&value["expected"])?,
            replacement: decode_term(&value["replacement"])?,
        },
        "replace-sentence" => Edit::ReplaceSentence {
            at,
            replacement: decode_sentence(&value["replacement"])?,
        },
        "delete-sentence" => Edit::DeleteSentence { at },
        "add-attribute" => Edit::AddAttribute {
            at,
            key: string(&value["key"])?.into(),
            value: value["value"].clone(),
        },
        "remove-attribute" => Edit::RemoveAttribute {
            at,
            key: string(&value["key"])?.into(),
            expected: value["expected"].clone(),
        },
        "replace-attribute" => Edit::ReplaceAttribute {
            at,
            key: string(&value["key"])?.into(),
            expected: value["expected"].clone(),
            replacement: value["replacement"].clone(),
        },
        _ => return Err(decode("edit operation")),
    })
}
