//! Canonical patch v1, using metadata-free k-rust KAST values.
//!
//! k-rust's KAST JSON of an edited term or sentence, and a canonical patch's text, are read with
//! [`parse_json`] (re-pin L1-3-fix-1; serde_json's limit of 128 refused every term more than
//! about 55 levels deep). A patch whose document would nest deeper than [`MAX_JSON_DEPTH`] has
//! no encoding: [`CodecError::TooDeep`], kink's limit, named as such (re-pin L1-3-fix-2). Within
//! it, [`Patch::canonical_json`], [`Patch::digest`] and [`Patch::from_canonical_json`] build,
//! serialize and drop their documents on a stack sized from the document's own depth
//! ([`Patch::document_depth`], counted before any document is built; re-pin L1-3-tail), so they
//! give the same result on any thread; [`Patch::canonical_value`] returns its document to the
//! caller, which drops it on its own stack. When the system refuses that stack the patch is
//! [`CodecError::Stack`]: the host's limit, not a fault of the patch.

use crate::digest::{JsonError, check_json_depth, json_depth, value_depth, with_document_stack};
use crate::stack::StackRefusal;
use crate::{
    CANONICAL_PATCH_DOMAIN, Edit, InsertPosition, MAX_JSON_DEPTH, Patch, PatchModelError,
    SentenceFingerprint, SentenceRef, Sha256Digest, TermRef, canonical_json, parse_json,
    payload_digest,
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
    /// The patch's document nests `depth` levels deep, more than kink's limit `limit`
    /// ([`MAX_JSON_DEPTH`]): an edit this deep has no encoding in this build.
    TooDeep {
        depth: usize,
        limit: usize,
    },
    /// The stack segment the patch's document depth needs was refused ([`StackRefusal`]): by the
    /// system (an address-space or memory limit of the host, `StackRefusal::Refused`), or as
    /// larger than the largest segment kink maps. A fact about the host or kink, not the patch.
    Stack(StackRefusal),
}
impl std::fmt::Display for CodecError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::error::Error for CodecError {}

/// The levels of a canonical patch document above a value one of its edits holds: the document
/// (`{"version", "edits", "pins"}`), its `edits` array and the edit's object. A pin is an object
/// at that third level.
const EDIT_LEVELS: usize = 3;

/// The KAST JSON text of each term and sentence one edit holds, written on the calling thread:
/// k-rust writes KAST and definition JSON with explicit work stacks (its `json_tree`), so the text
/// of a term of any depth takes no native stack per level. The text is what the codec parses
/// into the patch's document, so its depth ([`json_depth`], exact for JSON) is that value's.
enum Rendered {
    Nothing,
    Terms {
        expected: String,
        replacement: String,
    },
    Sentence(String),
}

impl Patch {
    /// The patch's canonical document.
    ///
    /// # Errors
    /// [`CodecError::TooDeep`] when the document would nest deeper than [`MAX_JSON_DEPTH`].
    pub fn canonical_value(&self) -> Result<Value, CodecError> {
        let rendered = self.rendered_pinned()?;
        within_limit(document_depth(self.edits(), &rendered))?;
        self.value_of(&rendered)
    }

    /// The nesting depth of the patch's canonical document, as [`crate::value_depth`] counts it,
    /// counted from the KAST JSON text of its terms and sentences without building the document
    /// (re-pin L1-3-tail). It is that depth exactly, so [`Patch::canonical_json`] sizes its stack
    /// from it and refuses a patch past [`MAX_JSON_DEPTH`] as [`CodecError::TooDeep`] before it
    /// builds any of it. An unpinned patch has the depth it will have once pinned (a pin is an
    /// object at an edit's level).
    ///
    /// # Errors
    /// A context alias, or a term or sentence k-rust cannot write.
    pub fn document_depth(&self) -> Result<usize, CodecError> {
        Ok(document_depth(self.edits(), &self.rendered()?))
    }

    /// The canonical JSON text, built, serialized and dropped on a stack sized from
    /// [`Patch::document_depth`]: on the calling thread when enough of it remains, else on a
    /// segment of that size (re-pin L1-3-tail; at L1-3-fix-2 every patch more than 48 term levels
    /// deep took a segment sized for [`MAX_JSON_DEPTH`], 768 MB in a release build, which an
    /// address-space limit refuses).
    ///
    /// # Errors
    /// [`CodecError::TooDeep`] past [`MAX_JSON_DEPTH`]; [`CodecError::Stack`] when the stack the
    /// depth needs is refused; those of [`Patch::canonical_value`].
    pub fn canonical_json(&self) -> Result<String, CodecError> {
        let rendered = self.rendered_pinned()?;
        let depth = within_limit(document_depth(self.edits(), &rendered))?;
        with_document_stack(depth, || Ok(canonical_json(&self.value_of(&rendered)?)))
            .map_err(CodecError::Stack)?
    }
    pub fn digest(&self) -> Result<Sha256Digest, CodecError> {
        Ok(payload_digest(
            CANONICAL_PATCH_DOMAIN,
            self.canonical_json()?.as_bytes(),
        ))
    }
    pub fn from_canonical_json(text: &str) -> Result<Self, CodecError> {
        let depth = within_limit(json_depth(text))?;
        with_document_stack(depth, || Self::decode(text)).map_err(CodecError::Stack)?
    }

    /// The text of every term and sentence the edits hold, in edit order.
    fn rendered(&self) -> Result<Vec<Rendered>, CodecError> {
        self.edits().iter().map(render_edit).collect()
    }

    /// [`Self::rendered`] of a pinned patch: only a pinned patch has a canonical document.
    fn rendered_pinned(&self) -> Result<Vec<Rendered>, CodecError> {
        if !self.is_pinned() {
            return Err(CodecError::Unpinned);
        }
        self.rendered()
    }

    /// The document of the patch whose edits' texts are `rendered`.
    fn value_of(&self, rendered: &[Rendered]) -> Result<Value, CodecError> {
        let edits = self
            .edits()
            .iter()
            .zip(rendered)
            .map(|(edit, rendered)| encode_edit(edit, rendered))
            .collect::<Result<Vec<_>, _>>()?;
        let pins = self.pins().iter().map(|(at, fingerprint)| json!({"module":at.module,"index":at.index,"fingerprint":fingerprint.to_string()})).collect::<Vec<_>>();
        let value = json!({"version":1,"edits":edits,"pins":pins});
        check_json_depth(&value).map_err(json_error(CodecError::Encode))?;
        Ok(value)
    }

    fn decode(text: &str) -> Result<Self, CodecError> {
        let value: Value = parse_json(text).map_err(json_error(CodecError::Decode))?;
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

/// `depth` when a document that deep is within [`MAX_JSON_DEPTH`], else [`CodecError::TooDeep`].
fn within_limit(depth: usize) -> Result<usize, CodecError> {
    if depth > MAX_JSON_DEPTH {
        return Err(CodecError::TooDeep {
            depth,
            limit: MAX_JSON_DEPTH,
        });
    }
    Ok(depth)
}

/// A refusal of [`parse_json`] or [`check_json_depth`] as the codec's: kink's depth limit as
/// [`CodecError::TooDeep`], a refused stack as [`CodecError::Stack`] (never as a fault of the
/// patch), malformed text as `malformed` (an encoding or a decoding error).
fn json_error(malformed: fn(String) -> CodecError) -> impl Fn(JsonError) -> CodecError {
    move |error| match error {
        JsonError::TooDeep { depth, limit } => CodecError::TooDeep { depth, limit },
        JsonError::Stack(refusal) => CodecError::Stack(refusal),
        JsonError::Syntax(error) => malformed(error.to_string()),
    }
}

/// The nesting depth of the canonical document of `edits`, whose terms' and sentences' texts are
/// `rendered`, counted without building it: [`EDIT_LEVELS`] above the deepest value an edit holds.
/// Every edit holds a value at least one level deep: a sentence reference (`{"module", "index"}`),
/// an insertion's position (`{"before": {"module", "index"}}`, two levels, or
/// `{"module-start": name}`), a term path (an array), a KAST document (its text's [`json_depth`])
/// or an attribute value ([`value_depth`]).
/// A pin is an object at the edit's level, and `edits` is never empty, so neither can be deeper.
fn document_depth(edits: &[Edit], rendered: &[Rendered]) -> usize {
    let deepest_held = |edit: &Edit, rendered: &Rendered| -> usize {
        let text = match rendered {
            Rendered::Nothing => 0,
            Rendered::Terms {
                expected,
                replacement,
            } => json_depth(expected).max(json_depth(replacement)),
            Rendered::Sentence(text) => json_depth(text),
        };
        let own = match edit {
            Edit::InsertSentence { position, .. } => match position {
                InsertPosition::Before(_) | InsertPosition::After(_) => 2,
                InsertPosition::ModuleStart(_) | InsertPosition::ModuleEnd(_) => 1,
            },
            Edit::AddAttribute { value, .. } => value_depth(value),
            Edit::RemoveAttribute { expected, .. } => value_depth(expected),
            Edit::ReplaceAttribute {
                expected,
                replacement,
                ..
            } => value_depth(expected).max(value_depth(replacement)),
            Edit::ReplaceTerm { .. }
            | Edit::ReplaceSentence { .. }
            | Edit::DeleteSentence { .. } => 1,
        };
        text.max(own).max(1)
    };
    EDIT_LEVELS
        + edits
            .iter()
            .zip(rendered)
            .map(|(edit, rendered)| deepest_held(edit, rendered))
            .max()
            .unwrap_or(0)
}

fn render_edit(edit: &Edit) -> Result<Rendered, CodecError> {
    Ok(match edit {
        Edit::ReplaceTerm {
            expected,
            replacement,
            ..
        } => Rendered::Terms {
            expected: term_text(expected)?,
            replacement: term_text(replacement)?,
        },
        Edit::ReplaceSentence {
            replacement: sentence,
            ..
        }
        | Edit::InsertSentence { sentence, .. } => Rendered::Sentence(sentence_text(sentence)?),
        Edit::DeleteSentence { .. }
        | Edit::AddAttribute { .. }
        | Edit::RemoveAttribute { .. }
        | Edit::ReplaceAttribute { .. } => Rendered::Nothing,
    })
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
fn term_text(term: &Term) -> Result<String, CodecError> {
    k_rust::kast::json::to_string(term).map_err(|e| CodecError::Encode(e.to_string()))
}
fn sentence_text(sentence: &Sentence) -> Result<String, CodecError> {
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
    k_rust::definition::json::to_string(&definition).map_err(|e| CodecError::Encode(e.to_string()))
}
/// The document of a term's or sentence's KAST JSON text.
fn held(text: &str) -> Result<Value, CodecError> {
    parse_json(text).map_err(json_error(CodecError::Encode))
}
fn encode_edit(edit: &Edit, rendered: &Rendered) -> Result<Value, CodecError> {
    let (terms, sentence) = match rendered {
        Rendered::Terms {
            expected,
            replacement,
        } => (Some((expected, replacement)), None),
        Rendered::Sentence(text) => (None, Some(text)),
        Rendered::Nothing => (None, None),
    };
    let missing = || CodecError::Encode("an edit's text was not rendered".to_owned());
    Ok(match edit {
        Edit::ReplaceTerm { at, .. } => {
            let (expected, replacement) = terms.ok_or_else(missing)?;
            json!({"op":"replace-term","sentence":reference(&at.sentence),"path":at.path.0,"expected":held(expected)?,"replacement":held(replacement)?})
        }
        Edit::ReplaceSentence { at, .. } => {
            json!({"op":"replace-sentence","sentence":reference(at),"replacement":held(sentence.ok_or_else(missing)?)?})
        }
        Edit::DeleteSentence { at } => json!({"op":"delete-sentence","sentence":reference(at)}),
        Edit::InsertSentence {
            position: at,
            ordinal,
            ..
        } => {
            json!({"op":"insert-sentence","position":position(at),"ordinal":ordinal,"sentence":held(sentence.ok_or_else(missing)?)?})
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
