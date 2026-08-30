//! KAST JSON version 4 serialization for flat K definitions.

use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use serde::{Deserialize, Serialize};
use serde_json::Value;

use super::ast::{
    Associativity, Attributes, Definition, FlatImport, FlatModule, ProductionItem,
    SOURCE_ID_ATTRIBUTE, Sentence,
};
use crate::kast::json::{self as term_json, JsonLabel, JsonSort, JsonTerm};
use crate::{
    kast::{ResolvedProductionId, Term, TermMetadata, TermSpan},
    provenance::{
        DestinationAnchor, GeneratingPass, LogicalSourceId, ORIGIN_ATTRIBUTE, OriginRecord,
        ProvenanceLink, SourceId, SourceTable,
    },
};

/// Wire-format discriminator for definitions that retain compiler provenance.
pub const PROVENANCE_FORMAT: &str = "KRUST-PROVENANCE";
/// Current [`PROVENANCE_FORMAT`] schema version.
pub const PROVENANCE_VERSION: u32 = 1;

#[derive(Debug)]
pub enum Error {
    Json(serde_json::Error),
    Term(term_json::Error),
    UnsupportedFormat(String),
    UnsupportedVersion(u32),
    UnsupportedSentence(&'static str),
    MissingMainModule(String),
    DuplicateMainModule(String),
    InvalidProvenance(String),
}

impl std::fmt::Display for Error {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Json(error) => error.fmt(formatter),
            Self::Term(error) => error.fmt(formatter),
            Self::UnsupportedFormat(format) => {
                write!(formatter, "unsupported KAST format {format:?}")
            }
            Self::UnsupportedVersion(version) => {
                write!(formatter, "unsupported KAST version {version}")
            }
            Self::UnsupportedSentence(node) => {
                write!(
                    formatter,
                    "{node} is not representable in KAST JSON version 4"
                )
            }
            Self::MissingMainModule(name) => {
                write!(formatter, "main module {name:?} was not found")
            }
            Self::DuplicateMainModule(name) => {
                write!(formatter, "main module {name:?} is not unique")
            }
            Self::InvalidProvenance(message) => formatter.write_str(message),
        }
    }
}

impl std::error::Error for Error {}

impl From<serde_json::Error> for Error {
    fn from(error: serde_json::Error) -> Self {
        Self::Json(error)
    }
}

impl From<term_json::Error> for Error {
    fn from(error: term_json::Error) -> Self {
        Self::Term(error)
    }
}

#[derive(Serialize, Deserialize)]
struct Envelope {
    format: String,
    version: u32,
    term: JsonDefinition,
}

pub fn from_str(input: &str) -> Result<Definition, Error> {
    let envelope: Envelope = serde_json::from_str(input)?;
    if envelope.format != term_json::FORMAT {
        return Err(Error::UnsupportedFormat(envelope.format));
    }
    if envelope.version != term_json::VERSION {
        return Err(Error::UnsupportedVersion(envelope.version));
    }

    let definition: Definition = envelope.term.try_into()?;
    let main_module_count = definition
        .modules
        .iter()
        .filter(|module| module.name == definition.main_module)
        .count();
    match main_module_count {
        0 => Err(Error::MissingMainModule(definition.main_module)),
        1 => Ok(definition),
        _ => Err(Error::DuplicateMainModule(definition.main_module)),
    }
}

pub fn to_string(definition: &Definition) -> Result<String, Error> {
    serialize(definition, serde_json::to_string)
}

pub fn to_string_pretty(definition: &Definition) -> Result<String, Error> {
    serialize(definition, serde_json::to_string_pretty)
}

fn serialize(
    definition: &Definition,
    serializer: impl FnOnce(&Envelope) -> Result<String, serde_json::Error>,
) -> Result<String, Error> {
    serializer(&Envelope {
        format: term_json::FORMAT.into(),
        version: term_json::VERSION,
        term: definition.try_into()?,
    })
    .map_err(Into::into)
}

/// A definition and its logical-source table decoded from `KRUST-PROVENANCE`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProvenanceDefinition {
    pub definition: Definition,
    pub source_table: SourceTable,
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ProvenanceEnvelope {
    format: String,
    version: u32,
    term: JsonDefinition,
    sources: Vec<JsonLogicalSource>,
    term_metadata: Vec<JsonTermMetadataEntry>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct JsonLogicalSource {
    logical: String,
    content_hash: String,
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct JsonTermMetadataEntry {
    module_index: u32,
    sentence_index: u32,
    field: u32,
    path: Vec<u32>,
    metadata: JsonTermMetadata,
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct JsonTermMetadata {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    span: Option<JsonTermSpan>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    production: Option<usize>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    sort: Option<JsonSort>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    origin: Option<JsonOriginRecord>,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct JsonTermSpan {
    source: JsonLogicalSource,
    start: usize,
    end: usize,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct JsonOriginRecord {
    pass: String,
    origins: Vec<JsonProvenanceLink>,
    destination: Option<JsonDestinationAnchor>,
}

#[derive(Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case", deny_unknown_fields)]
enum JsonProvenanceLink {
    Source {
        source: JsonLogicalSource,
        start: usize,
        end: usize,
    },
    Sentence {
        #[serde(rename = "uniqueId")]
        unique_id: String,
    },
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct JsonDestinationAnchor {
    module: String,
    sentence: String,
    sentence_index: u32,
    path: Vec<u32>,
}

/// Encode a definition and its provenance as compact `KRUST-PROVENANCE` JSON.
pub fn to_provenance_string(
    definition: &Definition,
    source_table: &SourceTable,
) -> Result<String, Error> {
    serialize_provenance(definition, source_table, serde_json::to_string)
}

/// Encode a definition and its provenance as pretty-printed `KRUST-PROVENANCE` JSON.
pub fn to_provenance_string_pretty(
    definition: &Definition,
    source_table: &SourceTable,
) -> Result<String, Error> {
    serialize_provenance(definition, source_table, serde_json::to_string_pretty)
}

fn serialize_provenance(
    definition: &Definition,
    source_table: &SourceTable,
    serializer: impl FnOnce(&ProvenanceEnvelope) -> Result<String, serde_json::Error>,
) -> Result<String, Error> {
    let mut wire_definition = definition.clone();
    map_definition_attributes(&mut wire_definition, |attributes| {
        encode_attribute_sources(attributes, source_table)
    })?;
    let mut term_metadata = Vec::new();
    collect_definition_metadata(definition, source_table, &mut term_metadata)?;
    let sources = source_table.iter().map(JsonLogicalSource::from).collect();
    let envelope = ProvenanceEnvelope {
        format: PROVENANCE_FORMAT.into(),
        version: PROVENANCE_VERSION,
        term: (&wire_definition).try_into()?,
        sources,
        term_metadata,
    };
    serializer(&envelope).map_err(Into::into)
}

/// Decode a `KRUST-PROVENANCE` document and restore its source-indexed metadata.
pub fn from_provenance_str(input: &str) -> Result<ProvenanceDefinition, Error> {
    let envelope: ProvenanceEnvelope = serde_json::from_str(input)?;
    if envelope.format != PROVENANCE_FORMAT {
        return Err(Error::UnsupportedFormat(envelope.format));
    }
    if envelope.version != PROVENANCE_VERSION {
        return Err(Error::UnsupportedVersion(envelope.version));
    }
    let mut source_table = SourceTable::default();
    for (index, source) in envelope.sources.into_iter().enumerate() {
        let id = source_table.intern(source.try_into()?);
        if id.0 != index {
            return Err(Error::InvalidProvenance(
                "provenance source table contains a duplicate identity".into(),
            ));
        }
    }
    let mut definition: Definition = envelope.term.try_into()?;
    map_definition_attributes(&mut definition, |attributes| {
        decode_attribute_sources(attributes, &source_table)
    })?;
    let mut addresses = BTreeSet::new();
    for entry in envelope.term_metadata {
        let address = (
            entry.module_index,
            entry.sentence_index,
            entry.field,
            entry.path.clone(),
        );
        if !addresses.insert(address) {
            return Err(Error::InvalidProvenance(
                "duplicate term-metadata address".into(),
            ));
        }
        let term = addressed_term_mut(&mut definition, &entry)?;
        let metadata = decode_term_metadata(entry.metadata, &source_table)?;
        let taken = std::mem::replace(term, Term::Sequence(Vec::new()));
        *term = taken.with_metadata(metadata);
    }
    validate_main_module(&definition)?;
    Ok(ProvenanceDefinition {
        definition,
        source_table,
    })
}

fn validate_main_module(definition: &Definition) -> Result<(), Error> {
    match definition
        .modules
        .iter()
        .filter(|module| module.name == definition.main_module)
        .count()
    {
        0 => Err(Error::MissingMainModule(definition.main_module.clone())),
        1 => Ok(()),
        _ => Err(Error::DuplicateMainModule(definition.main_module.clone())),
    }
}

fn map_definition_attributes(
    definition: &mut Definition,
    mut map: impl FnMut(&mut Attributes) -> Result<(), Error>,
) -> Result<(), Error> {
    map(&mut definition.attributes)?;
    for module in &mut definition.modules {
        map(&mut module.attributes)?;
        for sentence in &mut module.local_sentences {
            map(sentence.attributes_mut())?;
        }
    }
    Ok(())
}

fn encode_attribute_sources(
    attributes: &mut Attributes,
    source_table: &SourceTable,
) -> Result<(), Error> {
    if let Some(source) = attributes.get(SOURCE_ID_ATTRIBUTE) {
        let source = source
            .as_u64()
            .and_then(|source| usize::try_from(source).ok())
            .map(SourceId)
            .ok_or_else(|| Error::InvalidProvenance("source id is not a valid index".into()))?;
        attributes.insert(
            SOURCE_ID_ATTRIBUTE,
            serde_json::to_value(json_source(source_table, source)?)?,
        );
    }
    if let Some(mut origin) = attributes.get(ORIGIN_ATTRIBUTE).cloned() {
        map_origin_attribute_sources(&mut origin, |value| {
            let source = value
                .as_u64()
                .and_then(|value| usize::try_from(value).ok())
                .map(SourceId)
                .ok_or_else(|| Error::InvalidProvenance("origin source is not an index".into()))?;
            Ok(serde_json::to_value(json_source(source_table, source)?)?)
        })?;
        let origin = decode_origin(serde_json::from_value(origin)?, source_table)?;
        attributes.insert(
            ORIGIN_ATTRIBUTE,
            serde_json::to_value(encode_origin(&origin, source_table)?)?,
        );
    }
    Ok(())
}

fn decode_attribute_sources(
    attributes: &mut Attributes,
    source_table: &SourceTable,
) -> Result<(), Error> {
    if let Some(source) = attributes.get(SOURCE_ID_ATTRIBUTE).cloned() {
        attributes.insert(
            SOURCE_ID_ATTRIBUTE,
            Value::from(source_id_from_value(source, source_table)?.0),
        );
    }
    if let Some(origin) = attributes.get(ORIGIN_ATTRIBUTE).cloned() {
        let origin = decode_origin(serde_json::from_value(origin)?, source_table)?;
        attributes.insert(ORIGIN_ATTRIBUTE, origin.to_value());
    }
    Ok(())
}

fn map_origin_attribute_sources(
    origin: &mut Value,
    mut map: impl FnMut(&Value) -> Result<Value, Error>,
) -> Result<(), Error> {
    let origins = origin
        .get_mut("origins")
        .and_then(Value::as_array_mut)
        .ok_or_else(|| Error::InvalidProvenance("origin attribute has no origins array".into()))?;
    for link in origins {
        if link.get("kind").and_then(Value::as_str) != Some("source") {
            continue;
        }
        let source = link
            .get("source")
            .ok_or_else(|| Error::InvalidProvenance("source origin has no source".into()))?;
        let mapped = map(source)?;
        link.as_object_mut()
            .expect("origin link was accessed as an object")
            .insert("source".into(), mapped);
    }
    Ok(())
}

fn source_id_from_value(value: Value, source_table: &SourceTable) -> Result<SourceId, Error> {
    let source: JsonLogicalSource = serde_json::from_value(value)?;
    source_id(source_table, &source)
}

fn collect_definition_metadata(
    definition: &Definition,
    source_table: &SourceTable,
    output: &mut Vec<JsonTermMetadataEntry>,
) -> Result<(), Error> {
    for (module_index, module) in definition.modules.iter().enumerate() {
        for (sentence_index, sentence) in module.local_sentences.iter().enumerate() {
            for (field, term) in sentence_terms(sentence) {
                collect_term_metadata(
                    term,
                    source_table,
                    u32::try_from(module_index).expect("module count fits u32"),
                    u32::try_from(sentence_index).expect("sentence count fits u32"),
                    field,
                    &mut Vec::new(),
                    output,
                )?;
            }
        }
    }
    Ok(())
}

fn collect_term_metadata(
    term: &Term,
    source_table: &SourceTable,
    module_index: u32,
    sentence_index: u32,
    field: u32,
    path: &mut Vec<u32>,
    output: &mut Vec<JsonTermMetadataEntry>,
) -> Result<(), Error> {
    if let Some(metadata) = term.metadata() {
        output.push(JsonTermMetadataEntry {
            module_index,
            sentence_index,
            field,
            path: path.clone(),
            metadata: encode_term_metadata(metadata, source_table)?,
        });
    }
    match term.unannotated() {
        Term::Rewrite { left, right } => {
            collect_metadata_child(
                left,
                0,
                source_table,
                module_index,
                sentence_index,
                field,
                path,
                output,
            )?;
            collect_metadata_child(
                right,
                1,
                source_table,
                module_index,
                sentence_index,
                field,
                path,
                output,
            )?;
        }
        Term::As { pattern, alias } => {
            collect_metadata_child(
                pattern,
                0,
                source_table,
                module_index,
                sentence_index,
                field,
                path,
                output,
            )?;
            collect_metadata_child(
                alias,
                1,
                source_table,
                module_index,
                sentence_index,
                field,
                path,
                output,
            )?;
        }
        Term::Sequence(items)
        | Term::Apply {
            arguments: items, ..
        } => {
            for (index, item) in items.iter().enumerate() {
                collect_metadata_child(
                    item,
                    u32::try_from(index).expect("term arity fits u32"),
                    source_table,
                    module_index,
                    sentence_index,
                    field,
                    path,
                    output,
                )?;
            }
        }
        Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => {}
        Term::Annotated { .. } => unreachable!(),
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn collect_metadata_child(
    term: &Term,
    child: u32,
    source_table: &SourceTable,
    module_index: u32,
    sentence_index: u32,
    field: u32,
    path: &mut Vec<u32>,
    output: &mut Vec<JsonTermMetadataEntry>,
) -> Result<(), Error> {
    path.push(child);
    let result = collect_term_metadata(
        term,
        source_table,
        module_index,
        sentence_index,
        field,
        path,
        output,
    );
    path.pop();
    result
}

fn sentence_terms(sentence: &Sentence) -> Vec<(u32, &Term)> {
    match sentence {
        Sentence::Rule {
            body,
            requires,
            ensures,
            ..
        }
        | Sentence::Claim {
            body,
            requires,
            ensures,
            ..
        } => vec![(0, body), (1, requires), (2, ensures)],
        Sentence::Context { body, requires, .. }
        | Sentence::ContextAlias { body, requires, .. } => vec![(0, body), (1, requires)],
        Sentence::Configuration { body, ensures, .. } => vec![(0, body), (1, ensures)],
        _ => Vec::new(),
    }
}

fn encode_term_metadata(
    metadata: &TermMetadata,
    source_table: &SourceTable,
) -> Result<JsonTermMetadata, Error> {
    Ok(JsonTermMetadata {
        span: metadata
            .span
            .map(|span| encode_span(span, source_table))
            .transpose()?,
        production: metadata.production.map(|production| production.0),
        sort: metadata.sort.as_ref().map(Into::into),
        origin: metadata
            .origin
            .as_deref()
            .map(|origin| encode_origin(origin, source_table))
            .transpose()?,
    })
}

fn decode_term_metadata(
    metadata: JsonTermMetadata,
    source_table: &SourceTable,
) -> Result<TermMetadata, Error> {
    Ok(TermMetadata {
        span: metadata
            .span
            .map(|span| decode_span(span, source_table))
            .transpose()?,
        production: metadata.production.map(ResolvedProductionId),
        sort: metadata.sort.map(Into::into),
        origin: metadata
            .origin
            .map(|origin| decode_origin(origin, source_table).map(Arc::new))
            .transpose()?,
    })
}

fn encode_span(span: TermSpan, source_table: &SourceTable) -> Result<JsonTermSpan, Error> {
    Ok(JsonTermSpan {
        source: json_source(source_table, span.source)?,
        start: span.start,
        end: span.end,
    })
}

fn decode_span(span: JsonTermSpan, source_table: &SourceTable) -> Result<TermSpan, Error> {
    Ok(TermSpan {
        source: source_id(source_table, &span.source)?,
        start: span.start,
        end: span.end,
    })
}

fn encode_origin(
    origin: &OriginRecord,
    source_table: &SourceTable,
) -> Result<JsonOriginRecord, Error> {
    Ok(JsonOriginRecord {
        pass: origin.pass.as_str().into(),
        origins: origin
            .origins
            .iter()
            .map(|link| match link {
                ProvenanceLink::Source { span } => Ok(JsonProvenanceLink::Source {
                    source: json_source(source_table, span.source)?,
                    start: span.start,
                    end: span.end,
                }),
                ProvenanceLink::Sentence { unique_id } => Ok(JsonProvenanceLink::Sentence {
                    unique_id: unique_id.clone(),
                }),
            })
            .collect::<Result<_, Error>>()?,
        destination: origin
            .destination
            .as_ref()
            .map(|destination| JsonDestinationAnchor {
                module: destination.module.clone(),
                sentence: destination.sentence.clone(),
                sentence_index: destination.sentence_index,
                path: destination.path.clone(),
            }),
    })
}

fn decode_origin(
    origin: JsonOriginRecord,
    source_table: &SourceTable,
) -> Result<OriginRecord, Error> {
    let pass = GeneratingPass::from_name(&origin.pass).ok_or_else(|| {
        Error::InvalidProvenance(format!("unknown generating pass {:?}", origin.pass))
    })?;
    Ok(OriginRecord {
        pass,
        origins: origin
            .origins
            .into_iter()
            .map(|link| match link {
                JsonProvenanceLink::Source { source, start, end } => Ok(ProvenanceLink::Source {
                    span: TermSpan {
                        source: source_id(source_table, &source)?,
                        start,
                        end,
                    },
                }),
                JsonProvenanceLink::Sentence { unique_id } => {
                    Ok(ProvenanceLink::Sentence { unique_id })
                }
            })
            .collect::<Result<_, Error>>()?,
        destination: origin.destination.map(|destination| DestinationAnchor {
            module: destination.module,
            sentence: destination.sentence,
            sentence_index: destination.sentence_index,
            path: destination.path,
        }),
    })
}

fn json_source(source_table: &SourceTable, source: SourceId) -> Result<JsonLogicalSource, Error> {
    source_table
        .get(source)
        .map(JsonLogicalSource::from)
        .ok_or_else(|| Error::InvalidProvenance(format!("source id {} is not interned", source.0)))
}

fn source_id(source_table: &SourceTable, source: &JsonLogicalSource) -> Result<SourceId, Error> {
    let identity = LogicalSourceId::try_from(source.clone())?;
    source_table
        .iter()
        .position(|candidate| candidate == &identity)
        .map(SourceId)
        .ok_or_else(|| {
            Error::InvalidProvenance(format!(
                "logical source {:?} is absent from the source table",
                identity.logical
            ))
        })
}

impl From<&LogicalSourceId> for JsonLogicalSource {
    fn from(source: &LogicalSourceId) -> Self {
        Self {
            logical: source.logical.clone(),
            content_hash: encode_hash(&source.content_hash),
        }
    }
}

impl TryFrom<JsonLogicalSource> for LogicalSourceId {
    type Error = Error;

    fn try_from(source: JsonLogicalSource) -> Result<Self, Self::Error> {
        Ok(Self {
            logical: source.logical,
            content_hash: decode_hash(&source.content_hash)?,
        })
    }
}

fn encode_hash(hash: &[u8; 32]) -> String {
    hash.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn decode_hash(hash: &str) -> Result<[u8; 32], Error> {
    if hash.len() != 64 || !hash.is_ascii() {
        return Err(Error::InvalidProvenance(
            "logical-source contentHash must contain 64 hexadecimal characters".into(),
        ));
    }
    let mut decoded = [0; 32];
    for (index, byte) in decoded.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&hash[index * 2..index * 2 + 2], 16).map_err(|_| {
            Error::InvalidProvenance(
                "logical-source contentHash must contain 64 hexadecimal characters".into(),
            )
        })?;
    }
    Ok(decoded)
}

fn addressed_term_mut<'a>(
    definition: &'a mut Definition,
    entry: &JsonTermMetadataEntry,
) -> Result<&'a mut Term, Error> {
    let module = definition
        .modules
        .get_mut(usize::try_from(entry.module_index).expect("u32 fits usize"))
        .ok_or_else(|| Error::InvalidProvenance("term metadata names no module".into()))?;
    let sentence = module
        .local_sentences
        .get_mut(usize::try_from(entry.sentence_index).expect("u32 fits usize"))
        .ok_or_else(|| Error::InvalidProvenance("term metadata names no sentence".into()))?;
    let mut term = sentence_term_mut(sentence, entry.field)
        .ok_or_else(|| Error::InvalidProvenance("term metadata names no sentence field".into()))?;
    for child in &entry.path {
        term = term_child_mut(term, *child)
            .ok_or_else(|| Error::InvalidProvenance("term metadata path is invalid".into()))?;
    }
    Ok(term)
}

fn sentence_term_mut(sentence: &mut Sentence, field: u32) -> Option<&mut Term> {
    match (sentence, field) {
        (
            Sentence::Rule { body, .. }
            | Sentence::Claim { body, .. }
            | Sentence::Context { body, .. }
            | Sentence::ContextAlias { body, .. }
            | Sentence::Configuration { body, .. },
            0,
        ) => Some(body),
        (
            Sentence::Rule { requires, .. }
            | Sentence::Claim { requires, .. }
            | Sentence::Context { requires, .. }
            | Sentence::ContextAlias { requires, .. },
            1,
        ) => Some(requires),
        (Sentence::Configuration { ensures, .. }, 1)
        | (Sentence::Rule { ensures, .. } | Sentence::Claim { ensures, .. }, 2) => Some(ensures),
        _ => None,
    }
}

fn term_child_mut(term: &mut Term, child: u32) -> Option<&mut Term> {
    let term = unannotated_mut(term);
    let child = usize::try_from(child).expect("u32 fits usize");
    match term {
        Term::Rewrite { left, right } => match child {
            0 => Some(left),
            1 => Some(right),
            _ => None,
        },
        Term::As { pattern, alias } => match child {
            0 => Some(pattern),
            1 => Some(alias),
            _ => None,
        },
        Term::Sequence(items)
        | Term::Apply {
            arguments: items, ..
        } => items.get_mut(child),
        Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => None,
        Term::Annotated { .. } => unreachable!(),
    }
}

fn unannotated_mut(mut term: &mut Term) -> &mut Term {
    loop {
        match term {
            Term::Annotated { term: inner, .. } => term = inner,
            term => return term,
        }
    }
}

#[derive(Clone, Serialize, Deserialize)]
struct JsonAttributes {
    node: AttributeNode,
    att: BTreeMap<String, Value>,
}

#[derive(Clone, Copy, Serialize, Deserialize)]
enum AttributeNode {
    KAtt,
}

impl From<&Attributes> for JsonAttributes {
    fn from(attributes: &Attributes) -> Self {
        Self {
            node: AttributeNode::KAtt,
            att: attributes.entries().clone(),
        }
    }
}

impl From<JsonAttributes> for Attributes {
    fn from(attributes: JsonAttributes) -> Self {
        Self::new(attributes.att)
    }
}

#[derive(Serialize, Deserialize)]
struct JsonDefinition {
    node: DefinitionNode,
    #[serde(rename = "mainModule")]
    main_module: String,
    modules: Vec<JsonFlatModule>,
    att: JsonAttributes,
}

#[derive(Clone, Copy, Serialize, Deserialize)]
enum DefinitionNode {
    KDefinition,
}

impl TryFrom<&Definition> for JsonDefinition {
    type Error = Error;

    fn try_from(definition: &Definition) -> Result<Self, Self::Error> {
        Ok(Self {
            node: DefinitionNode::KDefinition,
            main_module: definition.main_module.clone(),
            modules: definition
                .modules
                .iter()
                .map(TryInto::try_into)
                .collect::<Result<_, _>>()?,
            att: (&definition.attributes).into(),
        })
    }
}

impl TryFrom<JsonDefinition> for Definition {
    type Error = Error;

    fn try_from(definition: JsonDefinition) -> Result<Self, Self::Error> {
        Ok(Self {
            main_module: definition.main_module,
            modules: definition
                .modules
                .into_iter()
                .map(TryInto::try_into)
                .collect::<Result<_, _>>()?,
            attributes: definition.att.into(),
        })
    }
}

#[derive(Serialize, Deserialize)]
struct JsonFlatModule {
    node: FlatModuleNode,
    name: String,
    imports: Vec<JsonImport>,
    #[serde(rename = "localSentences")]
    local_sentences: Vec<JsonSentence>,
    att: JsonAttributes,
}

#[derive(Clone, Copy, Serialize, Deserialize)]
enum FlatModuleNode {
    KFlatModule,
}

impl TryFrom<&FlatModule> for JsonFlatModule {
    type Error = Error;

    fn try_from(module: &FlatModule) -> Result<Self, Self::Error> {
        Ok(Self {
            node: FlatModuleNode::KFlatModule,
            name: module.name.clone(),
            imports: module.imports.iter().map(Into::into).collect(),
            local_sentences: module
                .local_sentences
                .iter()
                .map(TryInto::try_into)
                .collect::<Result<_, _>>()?,
            att: (&module.attributes).into(),
        })
    }
}

impl TryFrom<JsonFlatModule> for FlatModule {
    type Error = Error;

    fn try_from(module: JsonFlatModule) -> Result<Self, Self::Error> {
        Ok(Self {
            name: module.name,
            imports: module.imports.into_iter().map(Into::into).collect(),
            local_sentences: module
                .local_sentences
                .into_iter()
                .map(TryInto::try_into)
                .collect::<Result<_, _>>()?,
            attributes: module.att.into(),
        })
    }
}

#[derive(Serialize, Deserialize)]
struct JsonImport {
    node: ImportNode,
    name: String,
    #[serde(rename = "isPublic")]
    public: bool,
}

#[derive(Clone, Copy, Serialize, Deserialize)]
enum ImportNode {
    KImport,
}

impl From<&FlatImport> for JsonImport {
    fn from(import: &FlatImport) -> Self {
        Self {
            node: ImportNode::KImport,
            name: import.name.clone(),
            public: import.public,
        }
    }
}

impl From<JsonImport> for FlatImport {
    fn from(import: JsonImport) -> Self {
        Self {
            name: import.name,
            public: import.public,
        }
    }
}

#[derive(Clone, Copy, Serialize, Deserialize)]
enum JsonAssociativity {
    Left,
    Right,
    NonAssoc,
    Unspecified,
}

impl From<Associativity> for JsonAssociativity {
    fn from(associativity: Associativity) -> Self {
        match associativity {
            Associativity::Left => Self::Left,
            Associativity::Right => Self::Right,
            Associativity::NonAssoc => Self::NonAssoc,
            Associativity::Unspecified => Self::Unspecified,
        }
    }
}

impl From<JsonAssociativity> for Associativity {
    fn from(associativity: JsonAssociativity) -> Self {
        match associativity {
            JsonAssociativity::Left => Self::Left,
            JsonAssociativity::Right => Self::Right,
            JsonAssociativity::NonAssoc => Self::NonAssoc,
            JsonAssociativity::Unspecified => Self::Unspecified,
        }
    }
}

#[derive(Serialize, Deserialize)]
#[serde(tag = "node")]
#[allow(clippy::enum_variant_names)] // Variant names mirror the external KAST schema.
enum JsonProductionItem {
    KNonTerminal {
        sort: JsonSort,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        name: Option<String>,
    },
    KRegexTerminal {
        #[serde(
            rename = "precedeRegex",
            default,
            skip_serializing_if = "Option::is_none"
        )]
        precede_regex: Option<String>,
        regex: String,
        #[serde(
            rename = "followRegex",
            default,
            skip_serializing_if = "Option::is_none"
        )]
        follow_regex: Option<String>,
    },
    KTerminal {
        value: String,
    },
}

impl From<&ProductionItem> for JsonProductionItem {
    fn from(item: &ProductionItem) -> Self {
        match item {
            ProductionItem::NonTerminal { sort, name } => Self::KNonTerminal {
                sort: sort.into(),
                name: name.clone(),
            },
            ProductionItem::RegexTerminal {
                precede_regex,
                regex,
                follow_regex,
            } => Self::KRegexTerminal {
                precede_regex: precede_regex.clone(),
                regex: regex.clone(),
                follow_regex: follow_regex.clone(),
            },
            ProductionItem::Terminal(value) => Self::KTerminal {
                value: value.clone(),
            },
        }
    }
}

impl From<JsonProductionItem> for ProductionItem {
    fn from(item: JsonProductionItem) -> Self {
        match item {
            JsonProductionItem::KNonTerminal { sort, name } => Self::NonTerminal {
                sort: sort.into(),
                name,
            },
            JsonProductionItem::KRegexTerminal {
                precede_regex,
                regex,
                follow_regex,
            } => Self::RegexTerminal {
                precede_regex,
                regex,
                follow_regex,
            },
            JsonProductionItem::KTerminal { value } => Self::Terminal(value),
        }
    }
}

#[derive(Serialize, Deserialize)]
#[serde(tag = "node")]
#[allow(clippy::enum_variant_names)] // Variant names mirror the external KAST schema.
enum JsonSentence {
    KSyntaxSort {
        sort: JsonSort,
        params: Vec<JsonSort>,
        att: JsonAttributes,
    },
    KSortSynonym {
        #[serde(rename = "newSort")]
        new_sort: JsonSort,
        #[serde(rename = "oldSort")]
        old_sort: JsonSort,
        att: JsonAttributes,
    },
    KSyntaxLexical {
        name: String,
        regex: String,
        att: JsonAttributes,
    },
    KProduction {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        klabel: Option<JsonLabel>,
        #[serde(rename = "productionItems")]
        production_items: Vec<JsonProductionItem>,
        params: Vec<JsonSort>,
        sort: JsonSort,
        att: JsonAttributes,
    },
    KSyntaxAssociativity {
        assoc: JsonAssociativity,
        tags: Vec<String>,
        att: JsonAttributes,
    },
    KSyntaxPriority {
        priorities: Vec<Vec<String>>,
        att: JsonAttributes,
    },
    KContext {
        body: JsonTerm,
        requires: JsonTerm,
        att: JsonAttributes,
    },
    KRule {
        body: JsonTerm,
        requires: JsonTerm,
        ensures: JsonTerm,
        att: JsonAttributes,
    },
    KClaim {
        body: JsonTerm,
        requires: JsonTerm,
        ensures: JsonTerm,
        att: JsonAttributes,
    },
    KConfiguration {
        body: JsonTerm,
        ensures: JsonTerm,
        att: JsonAttributes,
    },
    KBubble {
        #[serde(rename = "sentenceType")]
        sentence_type: String,
        contents: String,
        att: JsonAttributes,
    },
}

impl TryFrom<&Sentence> for JsonSentence {
    type Error = Error;

    fn try_from(sentence: &Sentence) -> Result<Self, Self::Error> {
        Ok(match sentence {
            Sentence::SyntaxSort {
                parameters,
                sort,
                attributes,
            } => Self::KSyntaxSort {
                sort: sort.into(),
                params: parameters.iter().map(Into::into).collect(),
                att: attributes.into(),
            },
            Sentence::SortSynonym {
                new_sort,
                old_sort,
                attributes,
            } => Self::KSortSynonym {
                new_sort: new_sort.into(),
                old_sort: old_sort.into(),
                att: attributes.into(),
            },
            Sentence::SyntaxLexical {
                name,
                regex,
                attributes,
            } => Self::KSyntaxLexical {
                name: name.clone(),
                regex: regex.clone(),
                att: attributes.into(),
            },
            Sentence::Production {
                label,
                parameters,
                sort,
                items,
                attributes,
            } => Self::KProduction {
                klabel: label.as_ref().map(Into::into),
                production_items: items.iter().map(Into::into).collect(),
                params: parameters.iter().map(Into::into).collect(),
                sort: sort.into(),
                att: attributes.into(),
            },
            Sentence::SyntaxAssociativity {
                associativity,
                tags,
                attributes,
            } => Self::KSyntaxAssociativity {
                assoc: (*associativity).into(),
                tags: tags.clone(),
                att: attributes.into(),
            },
            Sentence::SyntaxPriority {
                priorities,
                attributes,
            } => Self::KSyntaxPriority {
                priorities: priorities.clone(),
                att: attributes.into(),
            },
            Sentence::ContextAlias { .. } => {
                return Err(Error::UnsupportedSentence("KContextAlias"));
            }
            Sentence::Context {
                body,
                requires,
                attributes,
            } => Self::KContext {
                body: body.into(),
                requires: requires.into(),
                att: attributes.into(),
            },
            Sentence::Rule {
                body,
                requires,
                ensures,
                attributes,
            } => Self::KRule {
                body: body.into(),
                requires: requires.into(),
                ensures: ensures.into(),
                att: attributes.into(),
            },
            Sentence::Claim {
                body,
                requires,
                ensures,
                attributes,
            } => Self::KClaim {
                body: body.into(),
                requires: requires.into(),
                ensures: ensures.into(),
                att: attributes.into(),
            },
            Sentence::Configuration {
                body,
                ensures,
                attributes,
            } => Self::KConfiguration {
                body: body.into(),
                ensures: ensures.into(),
                att: attributes.into(),
            },
            Sentence::Bubble {
                sentence_type,
                contents,
                attributes,
            } => Self::KBubble {
                sentence_type: sentence_type.clone(),
                contents: contents.clone(),
                att: attributes.into(),
            },
        })
    }
}

impl TryFrom<JsonSentence> for Sentence {
    type Error = Error;

    fn try_from(sentence: JsonSentence) -> Result<Self, Self::Error> {
        Ok(match sentence {
            JsonSentence::KSyntaxSort { sort, params, att } => Self::SyntaxSort {
                parameters: params.into_iter().map(Into::into).collect(),
                sort: sort.into(),
                attributes: att.into(),
            },
            JsonSentence::KSortSynonym {
                new_sort,
                old_sort,
                att,
            } => Self::SortSynonym {
                new_sort: new_sort.into(),
                old_sort: old_sort.into(),
                attributes: att.into(),
            },
            JsonSentence::KSyntaxLexical { name, regex, att } => Self::SyntaxLexical {
                name,
                regex,
                attributes: att.into(),
            },
            JsonSentence::KProduction {
                klabel,
                production_items,
                params,
                sort,
                att,
            } => Self::Production {
                label: klabel.map(Into::into),
                parameters: params.into_iter().map(Into::into).collect(),
                sort: sort.into(),
                items: production_items.into_iter().map(Into::into).collect(),
                attributes: att.into(),
            },
            JsonSentence::KSyntaxAssociativity { assoc, tags, att } => Self::SyntaxAssociativity {
                associativity: assoc.into(),
                tags,
                attributes: att.into(),
            },
            JsonSentence::KSyntaxPriority { priorities, att } => Self::SyntaxPriority {
                priorities,
                attributes: att.into(),
            },
            JsonSentence::KContext {
                body,
                requires,
                att,
            } => Self::Context {
                body: body.try_into()?,
                requires: requires.try_into()?,
                attributes: att.into(),
            },
            JsonSentence::KRule {
                body,
                requires,
                ensures,
                att,
            } => Self::Rule {
                body: body.try_into()?,
                requires: requires.try_into()?,
                ensures: ensures.try_into()?,
                attributes: att.into(),
            },
            JsonSentence::KClaim {
                body,
                requires,
                ensures,
                att,
            } => Self::Claim {
                body: body.try_into()?,
                requires: requires.try_into()?,
                ensures: ensures.try_into()?,
                attributes: att.into(),
            },
            JsonSentence::KConfiguration { body, ensures, att } => Self::Configuration {
                body: body.try_into()?,
                ensures: ensures.try_into()?,
                attributes: att.into(),
            },
            JsonSentence::KBubble {
                sentence_type,
                contents,
                att,
            } => Self::Bubble {
                sentence_type,
                contents,
                attributes: att.into(),
            },
        })
    }
}
