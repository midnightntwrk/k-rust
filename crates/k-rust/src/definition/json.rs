//! ```toml algorithm
//! id = "definition.json.encode"
//! name = "KAST JSON encoding of flat definitions"
//! sites = ["to_string", "to_string_pretty", "to_provenance_string", "to_provenance_string_pretty", "serialize_provenance"]
//! variable = "N = encoded definition nodes; L = links of the distinct origin-set allocations the receipts share"
//! counters = ["ProvenanceReceiptRenders"]
//! constrains = [{ id = "definition.provenance.record", site = "serialize_provenance", via = "AttributeKey::Origin records generated origins and is excluded from semantic comparison before provenance serialization" }]
//!
//! [[cost]]
//! mode = "one definition"
//! bound = "O(N + L)"
//! ```
//!
//! This definition-layer algorithm scans or transforms its model in deterministic declaration order.
//! Complexity: O(N + L): each receipt is encoded once and names its origin set by index into the provenance envelope's table, which holds each distinct set once; a set shared by many receipts is looked up by its allocation after its first encounter, so its links are hashed and written once.
//! Cost is linear in visited syntax unless its local documentation states another bound; `ProvenanceReceiptRenders` counts origin receipts rendered during provenance encoding.
//!
//! KAST JSON version 4 and KRUST-PROVENANCE serialization for flat K definitions.

use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    sync::Arc,
};

use k_rust_kore::measure::{self, Counter};
use serde::{Deserialize, Serialize};
use serde_json::Value;

use super::ast::{
    Associativity, Attributes, Definition, FlatImport, FlatModule, ProductionItem, Sentence,
};
use crate::definition::AttributeKey;
use crate::kast::json::{self as term_json, JsonLabel, JsonSort, JsonTerm};
use crate::{
    kast::{Label, ProductionIdentity, Term, TermMetadata, TermSpan},
    provenance::{
        DestinationAnchor, GeneratingPass, LogicalSourceId, OriginRecord, ProvenanceLink, SourceId,
        SourceOffsetMap, SourceOffsetSegment, SourceTable,
    },
};

pub(crate) fn label_json(label: &Label) -> Value {
    serde_json::to_value(JsonLabel::from(label)).expect("K labels serialize to JSON")
}

/// Wire-format discriminator for definitions that retain compiler provenance.
pub const PROVENANCE_FORMAT: &str = "KRUST-PROVENANCE";
/// Current [`PROVENANCE_FORMAT`] schema version.
///
/// Version 3 writes each distinct origin set once, in the envelope's `originSets` table, and a
/// receipt's `origins` is an index into that table. Version 4 adds `KContextAlias` sentences.
/// Version 5 lets the source table hold one logical source once per distinct offset map (one
/// entry per Markdown extraction), and a source reference names its entry by `extraction`.
/// Version 6 writes each sentence's input-address carrier under
/// `org.krust.provenance.InputAddresses`; a version 5 reader would take that key for an ordinary
/// attribute.
pub const PROVENANCE_VERSION: u32 = 6;

#[derive(Clone, Copy, Eq, PartialEq)]
enum DefinitionEnvelopeKind {
    KastV4,
    Provenance,
}

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
                if *node == "badsentence" {
                    formatter.write_str(
                        "KAST JSON version 4 document contains badsentence: its writer could not represent a sentence",
                    )
                } else {
                    write!(
                        formatter,
                        "KAST JSON version 4 document contains unsupported sentence node {node}"
                    )
                }
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
    let mut deserializer = serde_json::Deserializer::from_str(input);
    deserializer.disable_recursion_limit();
    let envelope = Envelope::deserialize(&mut deserializer)?;
    deserializer.end()?;
    if envelope.format != term_json::FORMAT {
        return Err(Error::UnsupportedFormat(envelope.format));
    }
    if envelope.version != term_json::VERSION {
        return Err(Error::UnsupportedVersion(envelope.version));
    }

    let definition = envelope.term.decode(DefinitionEnvelopeKind::KastV4)?;
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
        term: JsonDefinition::encode(
            definition,
            DefinitionEnvelopeKind::KastV4,
            &mut |attributes| Ok(attributes.into()),
        )?,
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
    sources: Vec<JsonSourceRecord>,
    /// Distinct origin sets in first-encounter order; receipts refer to them by index.
    origin_sets: Vec<Vec<JsonProvenanceLink>>,
    term_metadata: Vec<JsonTermMetadataEntry>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct JsonLogicalSource {
    logical: String,
    content_hash: String,
    /// Which of the source table's extractions of this logical source is meant, counted in table
    /// order; omitted for the first.
    #[serde(default, skip_serializing_if = "is_zero")]
    extraction: usize,
}

fn is_zero(value: &usize) -> bool {
    *value == 0
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct JsonSourceRecord {
    logical: String,
    content_hash: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    offset_map: Option<JsonSourceOffsetMap>,
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct JsonSourceOffsetMap {
    semantic_length: usize,
    raw_length: usize,
    segments: Vec<JsonSourceOffsetSegment>,
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct JsonSourceOffsetSegment {
    semantic_start: usize,
    raw_start: usize,
    length: usize,
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
    production: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    sort: Option<JsonSort>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    origin: Option<JsonOriginReceipt>,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct JsonTermSpan {
    source: JsonLogicalSource,
    start: usize,
    end: usize,
}

/// Wire form of one origin receipt: `origins` indexes the envelope's `originSets` table, so an
/// origin set shared by many receipts is written once per document.
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct JsonOriginReceipt {
    pass: String,
    origins: u32,
    destination: Option<JsonDestinationAnchor>,
}

/// In-memory JSON form of a receipt held as a raw attribute value (`OriginRecord::to_value`):
/// its source links name a [`SourceId`] of the definition's source table.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct MemoryOriginRecord {
    pass: String,
    origins: Vec<MemoryProvenanceLink>,
    destination: Option<JsonDestinationAnchor>,
}

#[derive(Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case", deny_unknown_fields)]
enum MemoryProvenanceLink {
    Source {
        source: usize,
        start: usize,
        end: usize,
    },
    Sentence {
        #[serde(rename = "uniqueId")]
        unique_id: String,
    },
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
    let mut encoder = ProvenanceEncoder::new(source_table);
    // The wire definition is built from the borrowed definition: attributes are encoded as they
    // are visited, so no receipt is rendered into the in-memory JSON form and no copy of the
    // definition is made.
    let term = JsonDefinition::encode(
        definition,
        DefinitionEnvelopeKind::Provenance,
        &mut |attributes| encoder.attributes(attributes),
    )?;
    let mut term_metadata = Vec::new();
    collect_definition_metadata(definition, &mut encoder, &mut term_metadata)?;
    let sources = source_table
        .iter()
        .enumerate()
        .map(|(index, source)| JsonSourceRecord {
            logical: source.logical.clone(),
            content_hash: encode_hash(&source.content_hash),
            offset_map: source_table
                .offset_map(SourceId(index))
                .map(JsonSourceOffsetMap::from),
        })
        .collect();
    let envelope = ProvenanceEnvelope {
        format: PROVENANCE_FORMAT.into(),
        version: PROVENANCE_VERSION,
        term,
        sources,
        origin_sets: encoder.origin_sets,
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
        let id = source_table.intern_extraction(
            JsonLogicalSource {
                logical: source.logical,
                content_hash: source.content_hash,
                extraction: 0,
            }
            .try_into()?,
            source.offset_map.map(TryInto::try_into).transpose()?,
        );
        if id.0 != index {
            return Err(Error::InvalidProvenance(
                "provenance source table contains a duplicate identity".into(),
            ));
        }
    }
    let origin_sets = decode_origin_sets(envelope.origin_sets, &source_table)?;
    let mut definition = envelope.term.decode(DefinitionEnvelopeKind::Provenance)?;
    map_definition_attributes(&mut definition, |attributes| {
        decode_attribute_sources(attributes, &source_table, &origin_sets)
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
        let metadata = decode_term_metadata(entry.metadata, &source_table, &origin_sets)?;
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
            map(crate::definition::sentence_mut(sentence).attributes_mut())?;
        }
    }
    Ok(())
}

/// Encoder state of one `KRUST-PROVENANCE` document: the wire references of the source table the
/// definition's source ids index, and the table of distinct origin sets written so far.
struct ProvenanceEncoder {
    // The wire reference of every source id, indexed by id.
    source_references: Vec<JsonLogicalSource>,
    origin_sets: Vec<Vec<JsonProvenanceLink>>,
    // Table index of every origin set already written, keyed by its links.
    by_links: HashMap<Arc<[ProvenanceLink]>, u32>,
    // Table index of every shared allocation already looked up, keyed by its address. The entry
    // holds the allocation, so the address cannot be reused by another set while encoding.
    by_allocation: HashMap<*const ProvenanceLink, (u32, Arc<[ProvenanceLink]>)>,
}

impl ProvenanceEncoder {
    fn new(source_table: &SourceTable) -> Self {
        let source_references = (0..source_table.iter().len())
            .map(|index| {
                let id = SourceId(index);
                let mut reference = JsonLogicalSource::from(
                    source_table
                        .get(id)
                        .expect("every index below the length is interned"),
                );
                reference.extraction = source_table
                    .extraction_ordinal(id)
                    .expect("every index below the length is interned");
                reference
            })
            .collect();
        Self {
            source_references,
            origin_sets: Vec::new(),
            by_links: HashMap::new(),
            by_allocation: HashMap::new(),
        }
    }

    /// The table index of `origins`, adding the set on its first encounter.
    ///
    /// Equal sets receive one index whether or not they share an allocation. A shared allocation
    /// is resolved by its address after its first lookup, so the links of a set shared by many
    /// receipts are compared and encoded once.
    fn origin_set(&mut self, origins: &Arc<[ProvenanceLink]>) -> Result<u32, Error> {
        let allocation = Arc::as_ptr(origins).cast::<ProvenanceLink>();
        if let Some((index, _)) = self.by_allocation.get(&allocation) {
            return Ok(*index);
        }
        let index = match self.by_links.get(origins) {
            Some(index) => *index,
            None => {
                let index = u32::try_from(self.origin_sets.len())
                    .map_err(|_| Error::InvalidProvenance("too many origin sets".into()))?;
                let links = origins
                    .iter()
                    .map(|link| encode_link(link, &self.source_references))
                    .collect::<Result<_, _>>()?;
                self.origin_sets.push(links);
                self.by_links.insert(Arc::clone(origins), index);
                index
            }
        };
        self.by_allocation
            .insert(allocation, (index, Arc::clone(origins)));
        Ok(index)
    }

    fn receipt(&mut self, origin: &OriginRecord) -> Result<JsonOriginReceipt, Error> {
        measure::bump(Counter::ProvenanceReceiptRenders);
        Ok(JsonOriginReceipt {
            pass: origin.pass.as_str().into(),
            origins: self.origin_set(&origin.origins)?,
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

    /// The wire attributes: the source id becomes its logical identity and the origin receipt
    /// refers to its origin set by table index.
    fn attributes(&mut self, attributes: &Attributes) -> Result<JsonAttributes, Error> {
        let mut att = attributes.semantic_entries().clone();
        if let Some(source) = att.get_mut(AttributeKey::SourceId.as_str()) {
            let id = source
                .as_u64()
                .and_then(|source| usize::try_from(source).ok())
                .map(SourceId)
                .ok_or_else(|| Error::InvalidProvenance("source id is not a valid index".into()))?;
            *source = serde_json::to_value(json_source(&self.source_references, id)?)?;
        }
        if let Some(receipt) = attributes.origin_receipt() {
            let receipt = match receipt.record() {
                Some(record) => self.receipt(record)?,
                None => self.receipt(&memory_origin_record(receipt.value())?)?,
            };
            att.insert(
                AttributeKey::Origin.as_str().into(),
                serde_json::to_value(receipt)?,
            );
        }
        if let Some(inputs) = attributes.input_addresses_value() {
            att.insert(AttributeKey::InputAddresses.as_str().into(), inputs.clone());
        }
        Ok(JsonAttributes {
            node: AttributeNode::KAtt,
            att,
        })
    }

    fn term_metadata(&mut self, metadata: &TermMetadata) -> Result<JsonTermMetadata, Error> {
        Ok(JsonTermMetadata {
            span: metadata
                .span
                .map(|span| encode_span(span, &self.source_references))
                .transpose()?,
            production: metadata.production.map(ProductionIdentity::to_hex),
            sort: metadata.sort.as_ref().map(Into::into),
            origin: metadata
                .origin
                .as_deref()
                .map(|origin| self.receipt(origin))
                .transpose()?,
        })
    }
}

/// Read a receipt stored as a raw attribute value in its in-memory JSON form.
fn memory_origin_record(value: &Value) -> Result<OriginRecord, Error> {
    let record = MemoryOriginRecord::deserialize(value)?;
    Ok(OriginRecord {
        pass: decode_pass(&record.pass)?,
        origins: record
            .origins
            .into_iter()
            .map(|link| match link {
                MemoryProvenanceLink::Source { source, start, end } => ProvenanceLink::Source {
                    span: TermSpan {
                        source: SourceId(source),
                        start,
                        end,
                    },
                },
                MemoryProvenanceLink::Sentence { unique_id } => {
                    ProvenanceLink::Sentence { unique_id }
                }
            })
            .collect::<Vec<_>>()
            .into(),
        destination: record.destination.map(decode_destination),
    })
}

/// Decode the origin-set table; each entry becomes one shared allocation.
fn decode_origin_sets(
    origin_sets: Vec<Vec<JsonProvenanceLink>>,
    source_table: &SourceTable,
) -> Result<Vec<Arc<[ProvenanceLink]>>, Error> {
    let decoded = origin_sets
        .into_iter()
        .map(|links| {
            links
                .into_iter()
                .map(|link| decode_link(link, source_table))
                .collect::<Result<Vec<_>, _>>()
                .map(Arc::from)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut distinct = HashSet::with_capacity(decoded.len());
    if !decoded.iter().all(|origins| distinct.insert(origins)) {
        return Err(Error::InvalidProvenance(
            "provenance origin-set table contains a duplicate set".into(),
        ));
    }
    Ok(decoded)
}

fn decode_attribute_sources(
    attributes: &mut Attributes,
    source_table: &SourceTable,
    origin_sets: &[Arc<[ProvenanceLink]>],
) -> Result<(), Error> {
    if let Some(source) = attributes.value(AttributeKey::SourceId).cloned() {
        attributes.set(
            AttributeKey::SourceId,
            Value::from(source_id_from_value(source, source_table)?.0),
        );
    }
    if let Some(origin) = attributes.value(AttributeKey::Origin) {
        let origin = decode_receipt(JsonOriginReceipt::deserialize(origin)?, origin_sets)?;
        attributes.set_origin_record(origin);
    }
    if attributes.has(AttributeKey::InputAddresses) && attributes.input_addresses().is_empty() {
        return Err(Error::InvalidProvenance(
            "input addresses are not a non-empty list of distinct {input, module, index} objects"
                .into(),
        ));
    }
    Ok(())
}

fn source_id_from_value(value: Value, source_table: &SourceTable) -> Result<SourceId, Error> {
    let source: JsonLogicalSource = serde_json::from_value(value)?;
    source_id(source_table, &source)
}

fn collect_definition_metadata(
    definition: &Definition,
    encoder: &mut ProvenanceEncoder,
    output: &mut Vec<JsonTermMetadataEntry>,
) -> Result<(), Error> {
    for (module_index, module) in definition.modules.iter().enumerate() {
        for (sentence_index, sentence) in module.local_sentences.iter().enumerate() {
            for (field, term) in sentence_terms(sentence) {
                collect_term_metadata(
                    term,
                    encoder,
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

// Invariant: `path` holds the child indices from the root of sentence term `field` to `term`, and each recursive call through `collect_metadata_child` pushes one index and descends into a strict subterm of `term`, so the size of `term` bounds the calls.
fn collect_term_metadata(
    term: &Term,
    encoder: &mut ProvenanceEncoder,
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
            metadata: encoder.term_metadata(metadata)?,
        });
    }
    match term.unannotated() {
        Term::Rewrite { left, right } => {
            collect_metadata_child(
                left,
                0,
                encoder,
                module_index,
                sentence_index,
                field,
                path,
                output,
            )?;
            collect_metadata_child(
                right,
                1,
                encoder,
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
                encoder,
                module_index,
                sentence_index,
                field,
                path,
                output,
            )?;
            collect_metadata_child(
                alias,
                1,
                encoder,
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
                    encoder,
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
    encoder: &mut ProvenanceEncoder,
    module_index: u32,
    sentence_index: u32,
    field: u32,
    path: &mut Vec<u32>,
    output: &mut Vec<JsonTermMetadataEntry>,
) -> Result<(), Error> {
    path.push(child);
    let result = collect_term_metadata(
        term,
        encoder,
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

fn decode_term_metadata(
    metadata: JsonTermMetadata,
    source_table: &SourceTable,
    origin_sets: &[Arc<[ProvenanceLink]>],
) -> Result<TermMetadata, Error> {
    Ok(TermMetadata {
        span: metadata
            .span
            .map(|span| decode_span(span, source_table))
            .transpose()?,
        production: metadata
            .production
            .map(|production| {
                ProductionIdentity::from_hex(&production).ok_or_else(|| {
                    Error::InvalidProvenance(format!(
                        "invalid production identity {production:?}; expected 32 lowercase hexadecimal characters"
                    ))
                })
            })
            .transpose()?,
        sort: metadata.sort.map(Into::into),
        origin: metadata
            .origin
            .map(|origin| decode_receipt(origin, origin_sets).map(Arc::new))
            .transpose()?,
    })
}

fn encode_span(span: TermSpan, sources: &[JsonLogicalSource]) -> Result<JsonTermSpan, Error> {
    Ok(JsonTermSpan {
        source: json_source(sources, span.source)?,
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

fn encode_link(
    link: &ProvenanceLink,
    sources: &[JsonLogicalSource],
) -> Result<JsonProvenanceLink, Error> {
    Ok(match link {
        ProvenanceLink::Source { span } => JsonProvenanceLink::Source {
            source: json_source(sources, span.source)?,
            start: span.start,
            end: span.end,
        },
        ProvenanceLink::Sentence { unique_id } => JsonProvenanceLink::Sentence {
            unique_id: unique_id.clone(),
        },
    })
}

fn decode_link(
    link: JsonProvenanceLink,
    source_table: &SourceTable,
) -> Result<ProvenanceLink, Error> {
    Ok(match link {
        JsonProvenanceLink::Source { source, start, end } => ProvenanceLink::Source {
            span: TermSpan {
                source: source_id(source_table, &source)?,
                start,
                end,
            },
        },
        JsonProvenanceLink::Sentence { unique_id } => ProvenanceLink::Sentence { unique_id },
    })
}

/// Decode a receipt; its origin set is the table entry's allocation, shared rather than copied.
fn decode_receipt(
    origin: JsonOriginReceipt,
    origin_sets: &[Arc<[ProvenanceLink]>],
) -> Result<OriginRecord, Error> {
    let origins = usize::try_from(origin.origins)
        .ok()
        .and_then(|index| origin_sets.get(index))
        .ok_or_else(|| {
            Error::InvalidProvenance(format!(
                "origin receipt names origin set {}, which the table does not contain",
                origin.origins
            ))
        })?;
    Ok(OriginRecord {
        pass: decode_pass(&origin.pass)?,
        origins: Arc::clone(origins),
        destination: origin.destination.map(decode_destination),
    })
}

fn decode_pass(pass: &str) -> Result<GeneratingPass, Error> {
    GeneratingPass::from_name(pass)
        .ok_or_else(|| Error::InvalidProvenance(format!("unknown generating pass {pass:?}")))
}

fn decode_destination(destination: JsonDestinationAnchor) -> DestinationAnchor {
    DestinationAnchor {
        module: destination.module,
        sentence: destination.sentence,
        sentence_index: destination.sentence_index,
        path: destination.path,
    }
}

fn json_source(
    sources: &[JsonLogicalSource],
    source: SourceId,
) -> Result<JsonLogicalSource, Error> {
    sources
        .get(source.0)
        .cloned()
        .ok_or_else(|| Error::InvalidProvenance(format!("source id {} is not interned", source.0)))
}

fn source_id(source_table: &SourceTable, source: &JsonLogicalSource) -> Result<SourceId, Error> {
    let extraction = source.extraction;
    let identity = LogicalSourceId::try_from(source.clone())?;
    source_table
        .find_extraction(&identity, extraction)
        .ok_or_else(|| {
            Error::InvalidProvenance(format!(
                "logical source {:?} extraction {extraction} is absent from the source table",
                identity.logical
            ))
        })
}

impl From<&LogicalSourceId> for JsonLogicalSource {
    fn from(source: &LogicalSourceId) -> Self {
        Self {
            logical: source.logical.clone(),
            content_hash: encode_hash(&source.content_hash),
            extraction: 0,
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

impl From<&SourceOffsetMap> for JsonSourceOffsetMap {
    fn from(offset_map: &SourceOffsetMap) -> Self {
        Self {
            semantic_length: offset_map.semantic_length(),
            raw_length: offset_map.raw_length(),
            segments: offset_map
                .segments()
                .iter()
                .map(|segment| JsonSourceOffsetSegment {
                    semantic_start: segment.semantic_start,
                    raw_start: segment.raw_start,
                    length: segment.length,
                })
                .collect(),
        }
    }
}

impl TryFrom<JsonSourceOffsetMap> for SourceOffsetMap {
    type Error = Error;

    fn try_from(offset_map: JsonSourceOffsetMap) -> Result<Self, Self::Error> {
        SourceOffsetMap::new(
            offset_map.semantic_length,
            offset_map.raw_length,
            offset_map
                .segments
                .into_iter()
                .map(|segment| SourceOffsetSegment {
                    semantic_start: segment.semantic_start,
                    raw_start: segment.raw_start,
                    length: segment.length,
                })
                .collect(),
        )
        .map_err(Error::InvalidProvenance)
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
    let mut term = sentence_term_mut(crate::definition::sentence_mut(sentence), entry.field)
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
    /// KAST v4 is an interchange vocabulary: the input-address carrier names sentences of one
    /// compilation's input and is not part of it.
    fn from(attributes: &Attributes) -> Self {
        let mut att = attributes.wire_map();
        att.remove(AttributeKey::InputAddresses.as_str());
        Self {
            node: AttributeNode::KAtt,
            att,
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

/// Wire encoder of one attribute map; KAST JSON copies the map, provenance encoding also
/// rewrites source identities and origin receipts.
type EncodeAttributes<'a> = dyn FnMut(&Attributes) -> Result<JsonAttributes, Error> + 'a;

impl JsonDefinition {
    fn encode(
        definition: &Definition,
        kind: DefinitionEnvelopeKind,
        attributes: &mut EncodeAttributes<'_>,
    ) -> Result<Self, Error> {
        Ok(Self {
            node: DefinitionNode::KDefinition,
            main_module: definition.main_module.clone(),
            modules: definition
                .modules
                .iter()
                .map(|module| JsonFlatModule::encode(module, kind, attributes))
                .collect::<Result<_, _>>()?,
            att: attributes(&definition.attributes)?,
        })
    }
    fn decode(self, kind: DefinitionEnvelopeKind) -> Result<Definition, Error> {
        let definition = self;
        Ok(Definition {
            main_module: definition.main_module,
            modules: definition
                .modules
                .into_iter()
                .map(|module| module.decode(kind))
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

impl JsonFlatModule {
    fn encode(
        module: &FlatModule,
        kind: DefinitionEnvelopeKind,
        attributes: &mut EncodeAttributes<'_>,
    ) -> Result<Self, Error> {
        Ok(Self {
            node: FlatModuleNode::KFlatModule,
            name: module.name.clone(),
            imports: module.imports.iter().map(Into::into).collect(),
            local_sentences: module
                .local_sentences
                .iter()
                .map(|sentence| JsonSentence::encode(sentence, kind, attributes))
                .collect::<Result<_, _>>()?,
            att: attributes(&module.attributes)?,
        })
    }
    fn decode(self, kind: DefinitionEnvelopeKind) -> Result<FlatModule, Error> {
        let module = self;
        Ok(FlatModule {
            name: module.name,
            imports: module.imports.into_iter().map(Into::into).collect(),
            local_sentences: module
                .local_sentences
                .into_iter()
                .map(|sentence| sentence.decode(kind).map(Arc::new))
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
#[allow(clippy::enum_variant_names)] // Variant names match the serialized sentence tags.
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
    #[serde(rename = "badsentence")]
    KBadsentence,
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
    KContextAlias {
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

impl JsonSentence {
    fn encode(
        sentence: &Sentence,
        kind: DefinitionEnvelopeKind,
        att: &mut EncodeAttributes<'_>,
    ) -> Result<Self, Error> {
        Ok(match sentence {
            Sentence::SyntaxSort {
                parameters,
                sort,
                attributes,
            } => Self::KSyntaxSort {
                sort: sort.into(),
                params: parameters.iter().map(Into::into).collect(),
                att: att(attributes)?,
            },
            Sentence::SortSynonym {
                new_sort,
                old_sort,
                attributes,
            } => Self::KSortSynonym {
                new_sort: new_sort.into(),
                old_sort: old_sort.into(),
                att: att(attributes)?,
            },
            Sentence::SyntaxLexical {
                name,
                regex,
                attributes,
            } => Self::KSyntaxLexical {
                name: name.clone(),
                regex: regex.clone(),
                att: att(attributes)?,
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
                att: att(attributes)?,
            },
            Sentence::SyntaxAssociativity {
                associativity,
                tags,
                attributes,
            } => Self::KSyntaxAssociativity {
                assoc: (*associativity).into(),
                tags: tags.clone(),
                att: att(attributes)?,
            },
            Sentence::SyntaxPriority {
                priorities,
                attributes,
            } => Self::KSyntaxPriority {
                priorities: priorities.clone(),
                att: att(attributes)?,
            },
            Sentence::ContextAlias {
                body,
                requires,
                attributes,
            } => match kind {
                DefinitionEnvelopeKind::KastV4 => Self::KBadsentence,
                DefinitionEnvelopeKind::Provenance => Self::KContextAlias {
                    body: body.into(),
                    requires: requires.into(),
                    att: att(attributes)?,
                },
            },
            Sentence::Context {
                body,
                requires,
                attributes,
            } => Self::KContext {
                body: body.into(),
                requires: requires.into(),
                att: att(attributes)?,
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
                att: att(attributes)?,
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
                att: att(attributes)?,
            },
            Sentence::Configuration {
                body,
                ensures,
                attributes,
            } => Self::KConfiguration {
                body: body.into(),
                ensures: ensures.into(),
                att: att(attributes)?,
            },
            Sentence::Bubble {
                sentence_type,
                contents,
                attributes,
            } => Self::KBubble {
                sentence_type: sentence_type.clone(),
                contents: contents.clone(),
                att: att(attributes)?,
            },
        })
    }
}

impl JsonSentence {
    fn decode(self, kind: DefinitionEnvelopeKind) -> Result<Sentence, Error> {
        let sentence = self;
        Ok(match sentence {
            JsonSentence::KBadsentence => {
                return Err(match kind {
                    DefinitionEnvelopeKind::KastV4 => Error::UnsupportedSentence("badsentence"),
                    DefinitionEnvelopeKind::Provenance => Error::InvalidProvenance(
                        "badsentence is not a KRUST-PROVENANCE sentence".into(),
                    ),
                });
            }
            JsonSentence::KSyntaxSort { sort, params, att } => Sentence::SyntaxSort {
                parameters: params.into_iter().map(Into::into).collect(),
                sort: sort.into(),
                attributes: att.into(),
            },
            JsonSentence::KSortSynonym {
                new_sort,
                old_sort,
                att,
            } => Sentence::SortSynonym {
                new_sort: new_sort.into(),
                old_sort: old_sort.into(),
                attributes: att.into(),
            },
            JsonSentence::KSyntaxLexical { name, regex, att } => Sentence::SyntaxLexical {
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
            } => Sentence::Production {
                label: klabel.map(Into::into),
                parameters: params.into_iter().map(Into::into).collect(),
                sort: sort.into(),
                items: production_items.into_iter().map(Into::into).collect(),
                attributes: att.into(),
            },
            JsonSentence::KSyntaxAssociativity { assoc, tags, att } => {
                Sentence::SyntaxAssociativity {
                    associativity: assoc.into(),
                    tags,
                    attributes: att.into(),
                }
            }
            JsonSentence::KSyntaxPriority { priorities, att } => Sentence::SyntaxPriority {
                priorities,
                attributes: att.into(),
            },
            JsonSentence::KContext {
                body,
                requires,
                att,
            } => Sentence::Context {
                body: body.try_into()?,
                requires: requires.try_into()?,
                attributes: att.into(),
            },
            JsonSentence::KContextAlias {
                body,
                requires,
                att,
            } => {
                if kind == DefinitionEnvelopeKind::KastV4 {
                    return Err(Error::UnsupportedSentence("KContextAlias"));
                }
                Sentence::ContextAlias {
                    body: body.try_into()?,
                    requires: requires.try_into()?,
                    attributes: att.into(),
                }
            }
            JsonSentence::KRule {
                body,
                requires,
                ensures,
                att,
            } => Sentence::Rule {
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
            } => Sentence::Claim {
                body: body.try_into()?,
                requires: requires.try_into()?,
                ensures: ensures.try_into()?,
                attributes: att.into(),
            },
            JsonSentence::KConfiguration { body, ensures, att } => Sentence::Configuration {
                body: body.try_into()?,
                ensures: ensures.try_into()?,
                attributes: att.into(),
            },
            JsonSentence::KBubble {
                sentence_type,
                contents,
                att,
            } => Sentence::Bubble {
                sentence_type,
                contents,
                attributes: att.into(),
            },
        })
    }
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;

    use super::*;
    use crate::{definition::FlatModule, kast::Sort, provenance::ORIGIN_ATTRIBUTE};

    #[derive(Clone, Debug)]
    enum Stored {
        Record,
        Value,
    }

    #[derive(Clone, Debug)]
    struct SentencePlan {
        receipt: Option<(usize, usize, Stored, bool)>,
        body_receipt: Option<(usize, usize)>,
        child_receipt: Option<(usize, usize)>,
    }

    fn link((sentence, value): (bool, u8)) -> ProvenanceLink {
        if sentence {
            ProvenanceLink::Sentence {
                unique_id: format!("s{value}"),
            }
        } else {
            ProvenanceLink::Source {
                span: TermSpan {
                    source: SourceId(usize::from(value % 2)),
                    start: usize::from(value),
                    end: usize::from(value) + 1,
                },
            }
        }
    }

    fn record(
        pool: &[Arc<[ProvenanceLink]>],
        set: usize,
        pass: usize,
        anchored: bool,
    ) -> OriginRecord {
        OriginRecord {
            pass: GeneratingPass::ALL[pass % GeneratingPass::ALL.len()],
            origins: Arc::clone(&pool[set % pool.len()]),
            destination: anchored.then(|| DestinationAnchor {
                module: "MAIN".into(),
                sentence: format!("rule:{set}"),
                sentence_index: u32::try_from(set).unwrap(),
                path: vec![0, u32::try_from(pass).unwrap()],
            }),
        }
    }

    fn metadata(pool: &[Arc<[ProvenanceLink]>], receipt: Option<(usize, usize)>) -> TermMetadata {
        TermMetadata {
            origin: receipt.map(|(set, pass)| Arc::new(record(pool, set, pass, true))),
            ..TermMetadata::default()
        }
    }

    /// Every origin set of a definition in traversal order: the sentence receipt, then the
    /// receipts of the body root and its child.
    fn origin_sets(definition: &Definition) -> Vec<Option<Arc<[ProvenanceLink]>>> {
        let mut sets = Vec::new();
        for sentence in &definition.modules[0].local_sentences {
            sets.push(
                sentence
                    .attributes()
                    .origin_record()
                    .map(|record| Arc::clone(&record.origins)),
            );
            let Sentence::Rule { body, .. } = &**sentence else {
                unreachable!()
            };
            let Term::Apply { arguments, .. } = body.unannotated() else {
                unreachable!()
            };
            for term in [body, &arguments[0]] {
                sets.push(
                    term.metadata()
                        .and_then(|metadata| metadata.origin.as_deref())
                        .map(|origin| Arc::clone(&origin.origins)),
                );
            }
        }
        sets
    }

    fn sentence_plan() -> impl Strategy<Value = SentencePlan> {
        let stored = prop_oneof![Just(Stored::Record), Just(Stored::Value)];
        (
            proptest::option::of((0_usize..8, 0_usize..32, stored, any::<bool>())),
            proptest::option::of((0_usize..8, 0_usize..32)),
            proptest::option::of((0_usize..8, 0_usize..32)),
        )
            .prop_map(|(receipt, body_receipt, child_receipt)| SentencePlan {
                receipt,
                body_receipt,
                child_receipt,
            })
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(256))]

        /// Decoding the encoded document gives receipts equal to the encoded ones, and two
        /// receipts share one decoded origin-set allocation exactly when their sets are equal;
        /// in particular receipts that shared one allocation before encoding share one after
        /// decoding. Each distinct set is written once.
        #[test]
        fn origin_set_table_round_trips_receipts_and_sharing(
            pool in prop::collection::vec(
                prop::collection::vec((any::<bool>(), 0_u8..4), 0..5),
                1..6,
            ),
            plans in prop::collection::vec(sentence_plan(), 1..8),
        ) {
            let pool = pool
                .into_iter()
                .map(|links| links.into_iter().map(link).collect::<Vec<_>>().into())
                .collect::<Vec<Arc<[ProvenanceLink]>>>();
            let mut sources = SourceTable::default();
            sources.intern(LogicalSourceId::new("a.k", b"a"));
            sources.intern(LogicalSourceId::new("b.k", b"b"));
            let mut raw_receipts = Vec::new();
            let sentences = plans
                .iter()
                .map(|plan| {
                    let mut attributes = Attributes::default();
                    match &plan.receipt {
                        Some((set, pass, Stored::Record, anchored)) => {
                            attributes.set_origin_record(record(&pool, *set, *pass, *anchored));
                            raw_receipts.push(None);
                        }
                        Some((set, pass, Stored::Value, anchored)) => {
                            let value = record(&pool, *set, *pass, *anchored).to_value();
                            attributes.insert(ORIGIN_ATTRIBUTE, value.clone());
                            raw_receipts.push(Some(value));
                        }
                        None => raw_receipts.push(None),
                    }
                    let child = Term::variable("X").with_metadata(metadata(&pool, plan.child_receipt));
                    Arc::new(Sentence::Rule {
                        body: Term::apply("f", vec![child])
                            .with_metadata(metadata(&pool, plan.body_receipt)),
                        requires: Term::Token { token: "true".into(), sort: Sort::new("Bool") },
                        ensures: Term::Token { token: "true".into(), sort: Sort::new("Bool") },
                        attributes,
                    })
                })
                .collect();
            let definition = Definition {
                main_module: "MAIN".into(),
                modules: vec![FlatModule {
                    name: "MAIN".into(),
                    imports: Vec::new(),
                    local_sentences: sentences,
                    attributes: Attributes::default(),
                }],
                attributes: Attributes::default(),
            };

            let encoded = to_provenance_string(&definition, &sources).unwrap();
            let decoded = from_provenance_str(&encoded).unwrap();
            prop_assert_eq!(&decoded.source_table, &sources);
            prop_assert_eq!(&decoded.definition, &definition);

            for ((before, after), raw) in definition.modules[0]
                .local_sentences
                .iter()
                .zip(&decoded.definition.modules[0].local_sentences)
                .zip(&raw_receipts)
            {
                let decoded_record = after.attributes().origin_record();
                match raw {
                    Some(value) => prop_assert_eq!(&decoded_record.unwrap().to_value(), value),
                    None => prop_assert_eq!(decoded_record, before.attributes().origin_record()),
                }
                let (Sentence::Rule { body: before, .. }, Sentence::Rule { body: after, .. }) =
                    (&**before, &**after)
                else {
                    unreachable!()
                };
                prop_assert_eq!(after.metadata(), before.metadata());
                let (Term::Apply { arguments: before, .. }, Term::Apply { arguments: after, .. }) =
                    (before.unannotated(), after.unannotated())
                else {
                    unreachable!()
                };
                prop_assert_eq!(after[0].metadata(), before[0].metadata());
            }

            let before = origin_sets(&definition);
            let after = origin_sets(&decoded.definition);
            for (left, decoded_left) in before.iter().zip(&after) {
                for (right, decoded_right) in before.iter().zip(&after) {
                    let (Some(decoded_left), Some(decoded_right)) = (decoded_left, decoded_right)
                    else {
                        continue;
                    };
                    if let (Some(left), Some(right)) = (left, right)
                        && Arc::ptr_eq(left, right)
                    {
                        prop_assert!(Arc::ptr_eq(decoded_left, decoded_right));
                    }
                    prop_assert_eq!(
                        Arc::ptr_eq(decoded_left, decoded_right),
                        decoded_left == decoded_right
                    );
                }
            }

            let distinct = after.iter().flatten().collect::<HashSet<_>>();
            let envelope: Value = serde_json::from_str(&encoded).unwrap();
            let table = envelope["originSets"].as_array().unwrap();
            prop_assert_eq!(table.len(), distinct.len());
            prop_assert_eq!(
                table.iter().map(|set| set.as_array().unwrap().len()).sum::<usize>(),
                distinct.iter().map(|set| set.len()).sum::<usize>()
            );
        }
    }

    #[test]
    fn input_addresses_and_extraction_ordinals_round_trip_together() {
        use crate::provenance::{InputAddress, InputSpace, LogicalSourceId, SourceOffsetMap};

        let logical = LogicalSourceId::new("test.md", b"ab");
        let mut source_table = SourceTable::default();
        let first =
            source_table.intern_extraction(logical.clone(), Some(SourceOffsetMap::identity(1)));
        let second = source_table.intern_extraction(logical, Some(SourceOffsetMap::identity(2)));
        assert_ne!(first, second);
        let addresses = vec![
            InputAddress::new(InputSpace::Compile, "MAIN", 1),
            InputAddress::new(InputSpace::Structured, "MAIN", 0),
        ];
        let mut attributes = Attributes::default();
        attributes.set(AttributeKey::SourceId, serde_json::json!(second.0));
        attributes.set_input_addresses(addresses.clone());
        let definition = Definition {
            main_module: "MAIN".into(),
            modules: vec![FlatModule {
                name: "MAIN".into(),
                imports: Vec::new(),
                local_sentences: vec![Arc::new(Sentence::SyntaxSort {
                    parameters: Vec::new(),
                    sort: Sort::new("Exp"),
                    attributes,
                })],
                attributes: Attributes::default(),
            }],
            attributes: Attributes::default(),
        };

        let encoded = to_provenance_string(&definition, &source_table).unwrap();
        let wire: Value = serde_json::from_str(&encoded).unwrap();
        assert_eq!(wire["version"], PROVENANCE_VERSION);
        let decoded = from_provenance_str(&encoded).unwrap();
        assert_eq!(decoded.source_table, source_table);
        let sentence = &decoded.definition.modules[0].local_sentences[0];
        assert_eq!(sentence.attributes().source_id(), Some(second));
        assert_eq!(sentence.attributes().input_addresses(), addresses);
    }

    #[test]
    fn input_addresses_reach_krust_provenance_but_not_kast_v4() {
        use crate::provenance::{INPUT_ADDRESSES_ATTRIBUTE, InputAddress, InputSpace};

        let addresses = vec![
            InputAddress::new(InputSpace::Structured, "MAIN", 3),
            InputAddress::new(InputSpace::Compile, "MAIN", 0),
        ];
        let mut attributes = Attributes::default();
        attributes.set_input_addresses(addresses.clone());
        let definition = Definition {
            main_module: "MAIN".into(),
            modules: vec![FlatModule {
                name: "MAIN".into(),
                imports: Vec::new(),
                local_sentences: vec![Arc::new(Sentence::SyntaxSort {
                    parameters: Vec::new(),
                    sort: Sort::new("Exp"),
                    attributes,
                })],
                attributes: Attributes::default(),
            }],
            attributes: Attributes::default(),
        };

        let kast = to_string(&definition).unwrap();
        assert!(!kast.contains(INPUT_ADDRESSES_ATTRIBUTE), "{kast}");

        let encoded = to_provenance_string(&definition, &SourceTable::default()).unwrap();
        let decoded = from_provenance_str(&encoded).unwrap();
        let sentence = &decoded.definition.modules[0].local_sentences[0];
        assert_eq!(sentence.attributes().input_addresses(), addresses);

        let malformed = encoded.replace("\"structured\"", "\"elsewhere\"");
        assert!(matches!(
            from_provenance_str(&malformed),
            Err(Error::InvalidProvenance(_))
        ));
    }
}
