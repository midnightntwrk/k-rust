//! ```toml algorithm
//! id = "definition.json.encode"
//! name = "KAST JSON encoding of flat definitions"
//! sites = ["to_string", "to_string_pretty", "to_provenance_string", "to_provenance_string_pretty", "serialize_provenance", "ProvenanceEncoder::node_index", "ProvenanceEncoder::anchor", "collect_definition_metadata", "from_provenance_str", "decode_origin_sets", "decode_anchors", "attach_term_metadata"]
//! variable = "N = encoded definition nodes; L = parts of the distinct origin-set allocations the receipts reach; A = distinct destination-path step allocations the receipts reach"
//! counters = ["ProvenanceReceiptRenders", "ProvenanceEncoderSetKeys", "ProvenanceEncoderAnchorInternings", "ProvenanceEncoderAnchorRoots", "ProvenanceNormalPartComparisons", "ProvenanceEncoderPreorderSteps", "ProvenanceDecoderSteps"]
//! tests = ["crates/k-rust/tests/provenance_linearity.rs", "crates/k-rust/tests/provenance_routes.rs"]
//! constrains = [{ id = "definition.provenance.record", site = "serialize_provenance", via = "AttributeKey::Origin records generated origins and is excluded from semantic comparison before provenance serialization" }]
//!
//! [[cost]]
//! mode = "one definition, encoded or decoded"
//! bound = "O(N + L + A) expected"
//! ```
//!
//! This definition-layer algorithm scans or transforms its model in deterministic declaration order.
//! Complexity: O(N + L + A). In `KRUST-PROVENANCE`, each receipt names its origin set by index into the `originSets` table and its destination by index into the `anchors` table, and each annotated node's metadata is addressed by its field and preorder index. The encoder computes each distinct set allocation's normal key once (a post-order walk memoised by allocation, `ProvenanceEncoderSetKeys`) and resolves each destination by walking its path up to the first step already resolved under its root (`ProvenanceEncoderAnchorInternings`), its root found by the names' allocations and interned by value once per pair of allocations (`ProvenanceEncoderAnchorRoots`), so a set or path reached along many paths of a shared DAG costs its own parts once. A key's parts are checked for repeats directly up to sixteen parts and through a hash set above (`ProvenanceNormalPartComparisons`), so a long flat sentence set costs linear time. The encoder addresses metadata by one preorder walk per field, which expands each node once (`ProvenanceEncoderPreorderSteps`). The reader reads the format and version first, skipping the body, then checks and builds each table entry and attaches metadata in one preorder walk per field (`ProvenanceDecoderSteps`).
//! Cost is linear in visited syntax unless its local documentation states another bound; `ProvenanceReceiptRenders` counts origin receipts rendered during provenance encoding.
//!
//! KAST JSON version 4 and KRUST-PROVENANCE serialization for flat K definitions.

use std::{
    collections::{BTreeMap, HashMap, HashSet},
    sync::Arc,
};

use k_rust_kore::measure::{self, Counter};
use serde::{
    Deserialize, Deserializer, Serialize,
    de::{DeserializeSeed, MapAccess, Visitor, value::StringDeserializer},
};
use serde_json::{Value, value::RawValue};

use super::ast::{
    Associativity, Attributes, Definition, FlatImport, FlatModule, ProductionItem, Sentence,
};
use crate::definition::AttributeKey;
use crate::kast::json::{self as term_json, JsonLabel, JsonSort, JsonTerm};
use crate::{
    kast::{Label, ProductionIdentity, Term, TermMetadata, TermSpan},
    provenance::{
        AnchorPath, DestinationAnchor, GeneratingPass, LogicalSourceId, OriginPart, OriginRecord,
        OriginSet, ProvenanceLink, SourceId, SourceOffsetMap, SourceOffsetSegment, SourceTable,
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
/// attribute. Version 7 holds rule-like sentences whose labels carry no sort parameters, which
/// compilation now rejects; a version 6 document holds the parser's own instances there.
///
/// Version 8 makes a document linear in the definition it holds. An `originSets` entry is a
/// node in normal form whose parts are links and references to earlier entries, so a receipt
/// that unites other sets names them instead of copying their links; receipts name their
/// destination in an `anchors` table of roots (module, sentence, sentence index) and steps (an
/// earlier anchor and one child step); `termMetadata` addresses a node by its field and its
/// preorder index instead of its path; and every source reference is the index of its entry in
/// `sources`. The bytes are a function of each receipt's normal form, not of how the writer's
/// memory shares sets or paths. A version 7 document is refused: every writer of one can write
/// it again, and a reader of version 7 would keep the quadratic decoding version 8 replaces.
pub const PROVENANCE_VERSION: u32 = 8;

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
    /// A `KRUST-PROVENANCE` document of a version this build does not read.
    UnsupportedProvenanceVersion(u32),
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
            Self::UnsupportedProvenanceVersion(version) => write!(
                formatter,
                "{PROVENANCE_FORMAT} version {version} is not supported; this build reads version {PROVENANCE_VERSION}"
            ),
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
struct Envelope<T = JsonDefinition> {
    format: String,
    version: u32,
    term: T,
}

/// A sentence that a KAST JSON version 4 document holds only as a `badsentence` node, which its
/// writer emits for a sentence the version 4 vocabulary cannot express (a context alias); the
/// node has no body, so the sentence cannot be recovered from the document.
#[derive(Clone, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub struct OmittedSentence {
    /// Position of the enclosing module in the decoded `modules` vector. Module names are not
    /// checked for uniqueness, so this, not [`Self::module`], identifies the module.
    pub module_index: usize,
    /// Name of the enclosing module.
    pub module: String,
    /// Position of the node in that module's wire `localSentences` array, counting every entry
    /// including earlier omitted ones; it is not a position in the decoded `local_sentences`.
    pub index: usize,
}

/// A KAST JSON version 4 `KFlatModuleList` document: a main module together with other flat
/// modules, carrying no definition attributes.
///
/// The list is not a closed definition. Imports may name modules outside it, and its order
/// carries no meaning, so compare lists by module name rather than by position.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ModuleList {
    pub main_module: String,
    pub modules: Vec<FlatModule>,
}

#[derive(Serialize, Deserialize)]
struct JsonModuleList<S = JsonSentence> {
    node: ModuleListNode,
    #[serde(rename = "mainModule")]
    main_module: String,
    term: Vec<JsonFlatModule<S>>,
}

#[derive(Clone, Copy, Serialize, Deserialize)]
enum ModuleListNode {
    KFlatModuleList,
}

/// Where `badsentence` nodes go while decoding a KAST JSON version 4 document: rejected, or
/// skipped with their positions recorded.
type Omissions<'a> = Option<&'a mut Vec<OmittedSentence>>;

/// Deserialize a KAST JSON version 4 envelope and check its format and version.
///
/// serde's recursion limit stays on outside the sentences' terms, which are read as raw text and
/// decoded with explicit work stacks ([`ReadSentence`]). The rest of a definition k-rust accepts
/// is shallow (its sort checks reject nested parametric sorts, so a declaration's sort nests at
/// most two levels), and anything there nested past the limit is an ordinary error.
fn kast_v4_envelope<T: serde::de::DeserializeOwned>(input: &str) -> Result<T, Error> {
    let envelope: Envelope<T> = serde_json::from_str(input)?;
    if envelope.format != term_json::FORMAT {
        return Err(Error::UnsupportedFormat(envelope.format));
    }
    if envelope.version != term_json::VERSION {
        return Err(Error::UnsupportedVersion(envelope.version));
    }
    Ok(envelope.term)
}

fn check_main_module(main_module: &str, modules: &[FlatModule]) -> Result<(), Error> {
    match modules
        .iter()
        .filter(|module| module.name == main_module)
        .count()
    {
        0 => Err(Error::MissingMainModule(main_module.to_owned())),
        1 => Ok(()),
        _ => Err(Error::DuplicateMainModule(main_module.to_owned())),
    }
}

fn read_definition(input: &str, omitted: Omissions<'_>) -> Result<Definition, Error> {
    let definition = kast_v4_envelope::<JsonDefinition<ReadSentence>>(input)?
        .decode(DefinitionEnvelopeKind::KastV4, omitted)?;
    check_main_module(&definition.main_module, &definition.modules)?;
    Ok(definition)
}

/// Decode a KAST JSON version 4 `KDefinition` document.
///
/// A `badsentence` node is an [`Error::UnsupportedSentence`]: the definition it belongs to cannot
/// be reconstructed. [`from_str_omitting_unrepresentable`] reads such documents lossily.
pub fn from_str(input: &str) -> Result<Definition, Error> {
    read_definition(input, None)
}

/// Decode a KAST JSON version 4 `KDefinition` document, skipping `badsentence` nodes and
/// returning their positions.
///
/// When the returned omissions are non-empty, the definition is not the one that was written: it
/// lacks those sentences. It is suitable for inspecting or comparing the rest of the document,
/// but must not be compiled or resolved, since other sentences (for example a `strict`
/// attribute naming a context alias) may depend on what was omitted. Every other node is decoded
/// exactly as by [`from_str`].
pub fn from_str_omitting_unrepresentable(
    input: &str,
) -> Result<(Definition, Vec<OmittedSentence>), Error> {
    let mut omitted = Vec::new();
    let definition = read_definition(input, Some(&mut omitted))?;
    Ok((definition, omitted))
}

/// Decode a KAST JSON version 4 `KFlatModuleList` document, such as a specification module with
/// the modules it needs beyond a definition. `mainModule` must name exactly one listed module.
///
/// A `badsentence` node is an [`Error::UnsupportedSentence`], as in [`from_str`]. There is no
/// lossy variant: the only sentence without a version 4 form is a context alias, which extends
/// the semantics a claim is proved against, so a list of claim modules has none to omit.
pub fn module_list_from_str(input: &str) -> Result<ModuleList, Error> {
    let list = kast_v4_envelope::<JsonModuleList<ReadSentence>>(input)?;
    let mut decoded = ModuleList {
        main_module: list.main_module,
        modules: Vec::with_capacity(list.term.len()),
    };
    for (index, module) in list.term.into_iter().enumerate() {
        module.decode_into(
            DefinitionEnvelopeKind::KastV4,
            index,
            None,
            &mut decoded.modules,
        )?;
    }
    check_main_module(&decoded.main_module, &decoded.modules)?;
    Ok(decoded)
}

pub fn to_string(definition: &Definition) -> Result<String, Error> {
    serialize(definition, serde_json::to_string)
}

pub fn to_string_pretty(definition: &Definition) -> Result<String, Error> {
    serialize(definition, serde_json::to_string_pretty)
}

/// Write the pretty-printed JSON of [`to_string_pretty`] to the file at `path`, streaming the
/// text so the document is never held whole in memory. The definition is encoded before the
/// file is created, so an encoding error leaves no file behind, as with writing the string.
pub fn write_pretty_file(definition: &Definition, path: &std::path::Path) -> Result<(), Error> {
    use std::io::Write as _;
    let envelope = envelope(definition)?;
    let mut writer =
        std::io::BufWriter::new(std::fs::File::create(path).map_err(serde_json::Error::io)?);
    serde_json::to_writer_pretty(&mut writer, &envelope)?;
    writer
        .flush()
        .map_err(|error| Error::Json(serde_json::Error::io(error)))
}

fn serialize(
    definition: &Definition,
    serializer: impl FnOnce(&Envelope) -> Result<String, serde_json::Error>,
) -> Result<String, Error> {
    serializer(&envelope(definition)?).map_err(Into::into)
}

fn envelope(definition: &Definition) -> Result<Envelope, Error> {
    Ok(Envelope {
        format: term_json::FORMAT.into(),
        version: term_json::VERSION,
        term: JsonDefinition::encode(
            definition,
            DefinitionEnvelopeKind::KastV4,
            &mut |attributes| Ok(attributes.into()),
        )?,
    })
}

/// A definition and its logical-source table decoded from `KRUST-PROVENANCE`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProvenanceDefinition {
    pub definition: Definition,
    pub source_table: SourceTable,
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ProvenanceEnvelope<S = JsonSentence> {
    format: String,
    version: u32,
    term: JsonDefinition<S>,
    sources: Vec<JsonSourceRecord>,
    /// Origin-set nodes in normal form, each written once and after every entry it names;
    /// receipts and later entries refer to them by index.
    origin_sets: Vec<Vec<JsonOriginPart>>,
    /// Destination anchors: roots naming a sentence, and steps extending an earlier anchor by
    /// one child step; receipts refer to them by index.
    anchors: Vec<JsonAnchor>,
    /// Term metadata, addressed by field and preorder node index, in increasing address order.
    term_metadata: Vec<JsonTermMetadataEntry>,
}

/// The members of a `KRUST-PROVENANCE` envelope that every version has written, read before
/// anything else: every other member is skipped unread (serde ignores unknown keys, and
/// serde_json skips a value with an explicit stack, without recursion), so a document of any
/// version, whatever the shape of its body, is classified by its format and version.
#[derive(Deserialize)]
struct ProvenanceHeader {
    format: String,
    version: u32,
}

/// The identity of one entry of the envelope's `sources` table.
struct JsonLogicalSource {
    logical: String,
    content_hash: String,
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
    /// The node's index in the preorder walk of the field's term: annotations are not nodes,
    /// and children are taken in order (`Rewrite` left then right, `As` pattern then alias,
    /// sequence items and application arguments in order). The writer and the reader both walk
    /// by `push_children_in_preorder!`.
    node: u32,
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
    /// The index of the span's source in the envelope's `sources` table.
    source: usize,
    start: usize,
    end: usize,
}

/// Wire form of one origin receipt: `origins` indexes the envelope's `originSets` table and
/// `destination` its `anchors` table, so a set or a path shared by many receipts is written once
/// per document.
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct JsonOriginReceipt {
    pass: String,
    origins: u32,
    destination: Option<u32>,
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

/// One part of an origin-set entry: a link, or a reference to an earlier entry.
#[derive(Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case", deny_unknown_fields)]
enum JsonOriginPart {
    Source {
        /// The index of the link's source in the envelope's `sources` table.
        source: usize,
        start: usize,
        end: usize,
    },
    Sentence {
        #[serde(rename = "uniqueId")]
        unique_id: String,
    },
    Set {
        set: u32,
    },
}

/// One entry of the anchor table: a root denotes the empty path of a sentence, and a step
/// denotes an earlier entry's path extended by one child step.
#[derive(Serialize, Deserialize)]
#[serde(untagged)]
enum JsonAnchor {
    Root(JsonAnchorRoot),
    Step(JsonAnchorStep),
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct JsonAnchorRoot {
    module: String,
    sentence: String,
    sentence_index: u32,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct JsonAnchorStep {
    parent: u32,
    step: u32,
}

/// The full destination anchor of a receipt's in-memory JSON form.
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
        anchors: encoder.anchors,
        term_metadata,
    };
    serializer(&envelope).map_err(Into::into)
}

/// Decode a `KRUST-PROVENANCE` document and restore its source-indexed metadata.
///
/// As for KAST JSON ([`from_str`]), serde's recursion limit stays on outside the sentences'
/// terms, which are decoded with explicit work stacks, so a definition whose terms nest to any
/// depth is read or refused on any thread. The origin-set and anchor tables are flat arrays whose
/// entries refer to earlier entries, and term metadata is attached by one preorder walk per
/// field, so every part of the reader is linear in the document and none recurses.
///
/// The format and version are read first, by a header that skips every other member, and the
/// body is parsed only as version 8: a document of another version is refused by its version
/// whatever the shape of its body, rather than by the first member version 8 shapes otherwise.
pub fn from_provenance_str(input: &str) -> Result<ProvenanceDefinition, Error> {
    let header: ProvenanceHeader = serde_json::from_str(input)?;
    if header.format != PROVENANCE_FORMAT {
        return Err(Error::UnsupportedFormat(header.format));
    }
    if header.version != PROVENANCE_VERSION {
        return Err(Error::UnsupportedProvenanceVersion(header.version));
    }
    let envelope: ProvenanceEnvelope<ReadSentence> = serde_json::from_str(input)?;
    let mut source_table = SourceTable::default();
    for (index, source) in envelope.sources.into_iter().enumerate() {
        let id = source_table.intern_extraction(
            JsonLogicalSource {
                logical: source.logical,
                content_hash: source.content_hash,
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
    let tables = DecodedTables {
        origin_sets: decode_origin_sets(envelope.origin_sets, &source_table)?,
        anchors: decode_anchors(envelope.anchors)?,
    };
    let mut definition = envelope
        .term
        .decode(DefinitionEnvelopeKind::Provenance, None)?;
    map_definition_attributes(&mut definition, |attributes| {
        decode_attribute_sources(attributes, &source_table, &tables)
    })?;
    attach_term_metadata(
        &mut definition,
        envelope.term_metadata,
        &source_table,
        &tables,
    )?;
    check_main_module(&definition.main_module, &definition.modules)?;
    Ok(ProvenanceDefinition {
        definition,
        source_table,
    })
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

/// One part of an origin-set entry's normal key: a link, or the index of the entry it names.
#[derive(Clone, Eq, Hash, PartialEq)]
enum NormalPart {
    Link(ProvenanceLink),
    Set(u32),
}

/// The parts of a normal key kept so far, for the repeated-part rules (N2, N3): a node of a term
/// receipt has at most five parts, compared directly; a longer one (a flat sentence set) is
/// checked through a hash set, so that a key costs time linear in its parts either way.
struct KeptParts(Option<HashSet<NormalPart>>);

impl KeptParts {
    const DIRECT: usize = 16;

    fn new(parts: usize) -> Self {
        Self((parts > Self::DIRECT).then(|| HashSet::with_capacity(parts)))
    }

    /// Whether `part` is not among `key`'s parts, recording it.
    fn insert(&mut self, key: &[NormalPart], part: &NormalPart) -> bool {
        match &mut self.0 {
            Some(kept) => {
                measure::bump(Counter::ProvenanceNormalPartComparisons);
                kept.insert(part.clone())
            }
            None => {
                measure::add(Counter::ProvenanceNormalPartComparisons, key.len() as u64);
                !key.contains(part)
            }
        }
    }
}

/// Encoder state of one `KRUST-PROVENANCE` document: the wire references of the source table the
/// definition's source ids index, and the origin-set and anchor tables written so far.
///
/// Both tables are hash-consed on values that do not depend on how memory is shared: an origin
/// set on its normal key (its links, and the indices of the sets it names, after the rules
/// N1-N4), an anchor on its root triple or on `(parent index, step)`. Two receipts whose sets
/// unfold to the same normal form, or whose destinations are equal, receive the same index
/// whatever allocations they hold, so the bytes are a function of the definition's values. The
/// memos keyed by allocation only avoid recomputing an index already known, which keeps the
/// encoder linear in the number of distinct allocations however many paths reach them.
struct ProvenanceEncoder {
    // The number of entries of the source table: a source id is written as itself, an index
    // below it.
    sources: usize,
    origin_sets: Vec<Vec<JsonOriginPart>>,
    // Table index of every origin-set entry, keyed by its normal key.
    set_keys: HashMap<Vec<NormalPart>, u32>,
    // Table index of every set allocation already encoded, keyed by its address, `None` for a
    // set whose normal key is empty: such a set is written (as the entry with no parts) only as
    // a receipt's own set, never as a part (N1). The entry holds the allocation, so the address
    // cannot be reused by another set while encoding.
    set_memo: HashMap<usize, (Option<u32>, OriginSet)>,
    anchors: Vec<JsonAnchor>,
    // Table index of every root entry, keyed by its value.
    roots: HashMap<RootNames, u32>,
    // Root index of every pair of name allocations already resolved, keyed by their addresses
    // and the sentence index; the entry holds both names.
    root_memo: HashMap<(usize, usize, u32), (u32, RootNames)>,
    // Table index of every step entry, keyed by its value.
    steps: HashMap<(u32, u32), u32>,
    // Table index of every path allocation already resolved under a root, keyed by the root's
    // index and the allocation's address; the entry holds the path. The root is part of the key
    // because one path allocation may extend different roots, and denotes a different anchor
    // under each.
    step_memo: HashMap<(u32, usize), (u32, AnchorPath)>,
}

/// The names and sentence index of a root anchor, the names shared.
type RootNames = (Arc<str>, Arc<str>, u32);

fn table_index(length: usize, table: &str) -> Result<u32, Error> {
    u32::try_from(length).map_err(|_| Error::InvalidProvenance(format!("too many {table}")))
}

fn str_address(name: &Arc<str>) -> usize {
    Arc::as_ptr(name).cast::<u8>() as usize
}

impl ProvenanceEncoder {
    fn new(source_table: &SourceTable) -> Self {
        Self {
            sources: source_table.iter().len(),
            origin_sets: Vec::new(),
            set_keys: HashMap::new(),
            set_memo: HashMap::new(),
            anchors: Vec::new(),
            roots: HashMap::new(),
            root_memo: HashMap::new(),
            steps: HashMap::new(),
            step_memo: HashMap::new(),
        }
    }

    /// The table index of `origins`, adding the entries of its nodes not written yet.
    ///
    /// A post-order walk over the set's nodes: a node's index is computed once the sets it names
    /// have theirs, from its normal key, and memoised by allocation, so each reachable
    /// allocation is keyed once whatever the number of paths that reach it.
    fn origin_set(&mut self, origins: &OriginSet) -> Result<u32, Error> {
        match self.node_index(origins)? {
            Some(index) => Ok(index),
            None => self.intern_key(Vec::new()),
        }
    }

    /// The table index of the set node `origins`, `None` when its normal key is empty.
    fn node_index(&mut self, origins: &OriginSet) -> Result<Option<u32>, Error> {
        if let Some((index, _)) = self.set_memo.get(&origins.address()) {
            return Ok(*index);
        }
        let mut pending = vec![(origins, false)];
        // Invariant: every node below a node popped with `true` is memoised.
        while let Some((node, expanded)) = pending.pop() {
            if self.set_memo.contains_key(&node.address()) {
                continue;
            }
            if !expanded {
                pending.push((node, true));
                for part in node.parts().iter().rev() {
                    if let OriginPart::Set(set) = part
                        && !self.set_memo.contains_key(&set.address())
                    {
                        pending.push((set, false));
                    }
                }
                continue;
            }
            let index = self.intern_set(node)?;
            self.set_memo.insert(node.address(), (index, node.clone()));
        }
        Ok(self.set_memo[&origins.address()].0)
    }

    /// The index of `node`, whose named sets are all memoised: its normal key keeps a part
    /// unless it names a set with an empty key (N1) or repeats a part already kept (N2, N3); a
    /// key that is exactly one reference is that entry (N4); an empty key has no index here;
    /// any other key is the entry with that key, written on its first occurrence.
    fn intern_set(&mut self, node: &OriginSet) -> Result<Option<u32>, Error> {
        measure::bump(Counter::ProvenanceEncoderSetKeys);
        let parts = node.parts();
        let mut key = Vec::with_capacity(parts.len());
        let mut kept = KeptParts::new(parts.len());
        for part in parts {
            let normal = match part {
                OriginPart::Link(link) => NormalPart::Link(link.clone()),
                OriginPart::Set(set) => match self.set_memo[&set.address()].0 {
                    Some(index) => NormalPart::Set(index),
                    None => continue,
                },
            };
            if kept.insert(&key, &normal) {
                key.push(normal);
            }
        }
        match key.as_slice() {
            [] => Ok(None),
            [NormalPart::Set(index)] => Ok(Some(*index)),
            [_, ..] => self.intern_key(key).map(Some),
        }
    }

    /// The index of the entry whose normal key is `key`, written on its first occurrence.
    fn intern_key(&mut self, key: Vec<NormalPart>) -> Result<u32, Error> {
        if let Some(index) = self.set_keys.get(&key) {
            return Ok(*index);
        }
        let index = table_index(self.origin_sets.len(), "origin sets")?;
        let entry = key
            .iter()
            .map(|part| match part {
                NormalPart::Link(link) => encode_link(link, self.sources),
                NormalPart::Set(set) => Ok(JsonOriginPart::Set { set: *set }),
            })
            .collect::<Result<_, _>>()?;
        self.origin_sets.push(entry);
        self.set_keys.insert(key, index);
        Ok(index)
    }

    /// The anchor-table index of `destination`, adding the entries of its root and of the steps
    /// of its path not written yet.
    ///
    /// The root is found by the names' allocations, else interned by value. The path is walked
    /// up from its last step until a step already resolved under this root, or the root itself;
    /// the steps passed are then interned top down, each by `(parent index, step)`, and memoised
    /// under the root. A path allocation is resolved once per root it extends.
    fn anchor(&mut self, destination: &DestinationAnchor) -> Result<u32, Error> {
        measure::bump(Counter::ProvenanceEncoderAnchorInternings);
        let names = (
            str_address(&destination.module),
            str_address(&destination.sentence),
            destination.sentence_index,
        );
        let root = match self.root_memo.get(&names) {
            Some((root, _)) => *root,
            None => {
                measure::bump(Counter::ProvenanceEncoderAnchorRoots);
                let value = (
                    Arc::clone(&destination.module),
                    Arc::clone(&destination.sentence),
                    destination.sentence_index,
                );
                let root = match self.roots.get(&value) {
                    Some(root) => *root,
                    None => {
                        let root = table_index(self.anchors.len(), "anchors")?;
                        self.anchors.push(JsonAnchor::Root(JsonAnchorRoot {
                            module: destination.module.to_string(),
                            sentence: destination.sentence.to_string(),
                            sentence_index: destination.sentence_index,
                        }));
                        self.roots.insert(value.clone(), root);
                        root
                    }
                };
                self.root_memo.insert(names, (root, value));
                root
            }
        };
        let mut unresolved = Vec::new();
        let mut path = &destination.path;
        let mut parent = root;
        // Invariant: `unresolved` holds the steps from the last one up to `path`, exclusive, none
        // of them memoised under `root`.
        while let Some((up, step)) = path.split_last() {
            if let Some((index, _)) = self.step_memo.get(&(root, path.address())) {
                parent = *index;
                break;
            }
            unresolved.push((path, step));
            path = up;
        }
        while let Some((path, step)) = unresolved.pop() {
            measure::bump(Counter::ProvenanceEncoderAnchorInternings);
            let index = match self.steps.get(&(parent, step)) {
                Some(index) => *index,
                None => {
                    let index = table_index(self.anchors.len(), "anchors")?;
                    self.anchors
                        .push(JsonAnchor::Step(JsonAnchorStep { parent, step }));
                    self.steps.insert((parent, step), index);
                    index
                }
            };
            self.step_memo
                .insert((root, path.address()), (index, path.clone()));
            parent = index;
        }
        Ok(parent)
    }

    fn receipt(&mut self, origin: &OriginRecord) -> Result<JsonOriginReceipt, Error> {
        measure::bump(Counter::ProvenanceReceiptRenders);
        Ok(JsonOriginReceipt {
            pass: origin.pass.as_str().into(),
            origins: self.origin_set(&origin.origins)?,
            destination: origin
                .destination
                .as_ref()
                .map(|destination| self.anchor(destination))
                .transpose()?,
        })
    }

    /// The wire attributes: the source id stays the index of its source-table entry, checked,
    /// and the origin receipt refers to its origin set and anchor by table index.
    fn attributes(&mut self, attributes: &Attributes) -> Result<JsonAttributes, Error> {
        let mut att = attributes.semantic_entries().clone();
        if let Some(source) = att.get_mut(AttributeKey::SourceId.as_str()) {
            let id = source
                .as_u64()
                .and_then(|source| usize::try_from(source).ok())
                .map(SourceId)
                .ok_or_else(|| Error::InvalidProvenance("source id is not a valid index".into()))?;
            *source = Value::from(source_index(self.sources, id)?);
        }
        if let Some(receipt) = attributes.origin_receipt() {
            // Every sentence-level set is built from flat link lists (the flat-sentence
            // invariant). The reader refuses a sentence receipt naming a set that names other
            // sets, so the writer refuses to write one rather than write a document its own
            // reader would refuse.
            let receipt = match receipt.record() {
                Some(record) => {
                    if !record.origins.is_flat() {
                        return Err(invalid(
                            "a sentence receipt names an origin set that names other sets",
                        ));
                    }
                    self.receipt(record)?
                }
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
                .map(|span| encode_span(span, self.sources))
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

/// The decoded origin-set and anchor tables of a document.
struct DecodedTables {
    /// One set per entry, and whether the entry names another set.
    origin_sets: Vec<(OriginSet, bool)>,
    anchors: DecodedAnchors,
}

/// The anchor table: each entry's path, and the root entry it extends.
struct DecodedAnchors {
    paths: Vec<AnchorPath>,
    root_of: Vec<usize>,
    /// The names and sentence index of each root entry, by entry index.
    roots: Vec<Option<RootNames>>,
}

fn invalid(message: impl Into<String>) -> Error {
    Error::InvalidProvenance(message.into())
}

/// Decode the origin-set table; each entry becomes one shared allocation, whose `set` parts are
/// the allocations of the earlier entries they name.
///
/// The reader checks what the encoder guarantees, entry by entry: every reference names an
/// earlier entry (which also excludes cycles), and the entry is in normal form, so that a table
/// has one reading and the bytes of a document stay a function of its sets' normal forms: no
/// reference to the entry with no parts (N1), no part twice (N2, N3), not exactly one reference
/// (N4), and no entry equal to another.
fn decode_origin_sets(
    origin_sets: Vec<Vec<JsonOriginPart>>,
    source_table: &SourceTable,
) -> Result<Vec<(OriginSet, bool)>, Error> {
    let mut decoded = Vec::<(OriginSet, bool)>::with_capacity(origin_sets.len());
    let mut keys = HashSet::<Vec<NormalPart>>::with_capacity(origin_sets.len());
    for (index, entry) in origin_sets.into_iter().enumerate() {
        measure::add(Counter::ProvenanceDecoderSteps, entry.len() as u64 + 1);
        let mut parts = Vec::with_capacity(entry.len());
        let mut key = Vec::with_capacity(entry.len());
        let mut kept = KeptParts::new(entry.len());
        let mut nested = false;
        for part in entry {
            let (part, normal) = match part {
                JsonOriginPart::Set { set } => {
                    let named = usize::try_from(set)
                        .ok()
                        .filter(|named| *named < index)
                        .ok_or_else(|| {
                            invalid(format!(
                                "origin set {index} names origin set {set}, which is not an earlier entry"
                            ))
                        })?;
                    let (named_set, _) = &decoded[named];
                    if named_set.is_empty() {
                        return Err(invalid(format!(
                            "origin set {index} names the empty origin set {set}"
                        )));
                    }
                    nested = true;
                    (OriginPart::Set(named_set.clone()), NormalPart::Set(set))
                }
                link @ (JsonOriginPart::Source { .. } | JsonOriginPart::Sentence { .. }) => {
                    let link = decode_link(link, source_table)?;
                    (OriginPart::Link(link.clone()), NormalPart::Link(link))
                }
            };
            if !kept.insert(&key, &normal) {
                return Err(invalid(format!("origin set {index} repeats a part")));
            }
            parts.push(part);
            key.push(normal);
        }
        if let [NormalPart::Set(set)] = key.as_slice() {
            return Err(invalid(format!(
                "origin set {index} consists of one reference to origin set {set}"
            )));
        }
        if !keys.insert(key) {
            return Err(invalid(
                "provenance origin-set table contains a duplicate set",
            ));
        }
        let set = if parts.is_empty() {
            OriginSet::new()
        } else {
            OriginSet::from_normal_parts(parts)
        };
        decoded.push((set, nested));
    }
    Ok(decoded)
}

/// Decode the anchor table: a root starts the empty path of its sentence, and a step extends an
/// earlier entry's path by one step, sharing it. No entry may repeat another.
fn decode_anchors(anchors: Vec<JsonAnchor>) -> Result<DecodedAnchors, Error> {
    let mut decoded = DecodedAnchors {
        paths: Vec::with_capacity(anchors.len()),
        root_of: Vec::with_capacity(anchors.len()),
        roots: Vec::with_capacity(anchors.len()),
    };
    let mut roots = HashSet::new();
    let mut steps = HashSet::new();
    for (index, anchor) in anchors.into_iter().enumerate() {
        measure::bump(Counter::ProvenanceDecoderSteps);
        match anchor {
            JsonAnchor::Root(root) => {
                if !roots.insert((
                    root.module.clone(),
                    root.sentence.clone(),
                    root.sentence_index,
                )) {
                    return Err(invalid("provenance anchor table contains a duplicate root"));
                }
                decoded.paths.push(AnchorPath::new());
                decoded.root_of.push(index);
                decoded.roots.push(Some((
                    root.module.into(),
                    root.sentence.into(),
                    root.sentence_index,
                )));
            }
            JsonAnchor::Step(JsonAnchorStep { parent, step }) => {
                let parent_index = usize::try_from(parent)
                    .ok()
                    .filter(|parent| *parent < index)
                    .ok_or_else(|| {
                        invalid(format!(
                            "anchor {index} extends anchor {parent}, which is not an earlier entry"
                        ))
                    })?;
                if !steps.insert((parent, step)) {
                    return Err(invalid("provenance anchor table contains a duplicate step"));
                }
                let path = decoded.paths[parent_index].child(step);
                decoded.paths.push(path);
                decoded.root_of.push(decoded.root_of[parent_index]);
                decoded.roots.push(None);
            }
        }
    }
    Ok(decoded)
}

impl DecodedAnchors {
    /// The destination anchor entry `index` denotes: its root's names, shared, and its path.
    fn destination(&self, index: u32) -> Result<DestinationAnchor, Error> {
        let entry = usize::try_from(index)
            .ok()
            .filter(|entry| *entry < self.paths.len())
            .ok_or_else(|| {
                invalid(format!(
                    "origin receipt names anchor {index}, which the table does not contain"
                ))
            })?;
        let (module, sentence, sentence_index) = self.roots[self.root_of[entry]]
            .as_ref()
            .expect("every anchor extends a root");
        Ok(DestinationAnchor {
            module: Arc::clone(module),
            sentence: Arc::clone(sentence),
            sentence_index: *sentence_index,
            path: self.paths[entry].clone(),
        })
    }
}

fn decode_attribute_sources(
    attributes: &mut Attributes,
    source_table: &SourceTable,
    tables: &DecodedTables,
) -> Result<(), Error> {
    if let Some(source) = attributes.value(AttributeKey::SourceId).cloned() {
        attributes.set(
            AttributeKey::SourceId,
            Value::from(source_id_from_value(source, source_table)?.0),
        );
    }
    if let Some(origin) = attributes.value(AttributeKey::Origin) {
        let origin = JsonOriginReceipt::deserialize(origin)?;
        // Every sentence-level set is flat; a sentence receipt naming a set that names other
        // sets would make each sentence-level union flatten a DAG.
        if usize::try_from(origin.origins)
            .ok()
            .and_then(|index| tables.origin_sets.get(index))
            .is_some_and(|(_, nested)| *nested)
        {
            return Err(invalid(format!(
                "a sentence receipt names origin set {}, which names other sets",
                origin.origins
            )));
        }
        let origin = decode_receipt(origin, tables)?;
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
    let index = value
        .as_u64()
        .and_then(|index| usize::try_from(index).ok())
        .ok_or_else(|| invalid("a source id is not an index of the source table"))?;
    source_id(source_table, index)
}

/// The preorder child order of term metadata addresses, stated once for both walks.
///
/// A node's `node` index is its position in the preorder walk of its field: annotations are not
/// nodes, `Rewrite` is followed by its left then its right side, `As` by its pattern then its
/// alias, and a sequence or an application by its items in order. The writer numbers nodes and
/// the reader finds them by this one statement, expanded for shared and for mutable borrows
/// (`$items` is `iter` or `iter_mut`), so the two cannot disagree; changing it changes the
/// format. Children are pushed last first, so that popping visits them in order.
macro_rules! push_children_in_preorder {
    ($term:expr, $stack:expr, $items:ident) => {
        match $term {
            Term::Rewrite { left, right } => {
                $stack.push(right);
                $stack.push(left);
            }
            Term::As { pattern, alias } => {
                $stack.push(alias);
                $stack.push(pattern);
            }
            Term::Sequence(items)
            | Term::Apply {
                arguments: items, ..
            } => $stack.extend(items.$items().rev()),
            Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => {}
            Term::Annotated { .. } => unreachable!("unannotated strips annotations"),
        }
    };
}

/// The children of `term`, its annotations removed, pushed onto `stack` in preorder
/// (`push_children_in_preorder!`).
///
/// Every walk of the encoder that numbers nodes expands them here, so the measure of its work,
/// `provenance.encoder_preorder_steps`, counts one per node expanded wherever the walk is
/// written: one walk per field expands each node once, and a walk restarted from the field root
/// to find a node's index expands every node before it again.
fn push_children<'a>(term: &'a Term, stack: &mut Vec<&'a Term>) {
    measure::bump(Counter::ProvenanceEncoderPreorderSteps);
    push_children_in_preorder!(term.unannotated(), stack, iter);
}

/// The mutable counterpart of [`push_children`], from the same statement of the order.
fn push_children_mut<'a>(term: &'a mut Term, stack: &mut Vec<&'a mut Term>) {
    push_children_in_preorder!(unannotated_mut(term), stack, iter_mut);
}

/// Write the metadata of every annotated node, addressed by its field and its preorder index,
/// in increasing address order: one iterative preorder walk per field.
fn collect_definition_metadata(
    definition: &Definition,
    encoder: &mut ProvenanceEncoder,
    output: &mut Vec<JsonTermMetadataEntry>,
) -> Result<(), Error> {
    for (module_index, module) in definition.modules.iter().enumerate() {
        let module_index = u32::try_from(module_index).expect("module count fits u32");
        for (sentence_index, sentence) in module.local_sentences.iter().enumerate() {
            let sentence_index = u32::try_from(sentence_index).expect("sentence count fits u32");
            for (field, term) in sentence.terms() {
                let mut pending = vec![term];
                let mut node = 0u32;
                // Invariant: `node` is the preorder index of the next node popped.
                while let Some(term) = pending.pop() {
                    if let Some(metadata) = term.metadata() {
                        output.push(JsonTermMetadataEntry {
                            module_index,
                            sentence_index,
                            field,
                            node,
                            metadata: encoder.term_metadata(metadata)?,
                        });
                    }
                    node = node
                        .checked_add(1)
                        .ok_or_else(|| invalid("a sentence field has too many nodes"))?;
                    push_children(term, &mut pending);
                }
            }
        }
    }
    Ok(())
}

/// Attach every metadata entry to the node it addresses.
///
/// The entries must be strictly increasing by `(module, sentence, field, node)`, which makes each
/// address unique with one comparison per entry. Each field that has entries is walked once in
/// preorder, until its last entry: the node whose index is the next entry's receives its
/// metadata before its children are pushed, so no borrow of a child is outstanding when the
/// node is rewrapped. One check refuses every misplaced entry: the groups of entries must have
/// strictly increasing fields, and an entry its field's walk does not consume (out of order,
/// repeated, or past the end of the field) starts another group of the same field.
fn attach_term_metadata(
    definition: &mut Definition,
    entries: Vec<JsonTermMetadataEntry>,
    source_table: &SourceTable,
    tables: &DecodedTables,
) -> Result<(), Error> {
    let mut entries = entries.into_iter().peekable();
    let mut previous_field = None;
    while let Some(first) = entries.peek() {
        let field = (first.module_index, first.sentence_index, first.field);
        if previous_field.is_some_and(|previous| previous >= field) {
            return Err(invalid(
                "term-metadata entries are not in strictly increasing address order, or one \
                 addresses a node past the end of its field",
            ));
        }
        previous_field = Some(field);
        let sentence = definition
            .modules
            .get_mut(usize::try_from(field.0).expect("u32 fits usize"))
            .ok_or_else(|| invalid("term metadata names no module"))?
            .local_sentences
            .get_mut(usize::try_from(field.1).expect("u32 fits usize"))
            .ok_or_else(|| invalid("term metadata names no sentence"))?;
        let term = crate::definition::sentence_mut(sentence)
            .term_mut(field.2)
            .ok_or_else(|| invalid("term metadata names no sentence field"))?;
        let mut pending = vec![term];
        let mut node = 0u32;
        // Invariant: `node` is the preorder index of the next node popped, and every entry of
        // this field addressing an earlier node has been attached.
        while let Some(term) = pending.pop() {
            let in_field = |entry: &JsonTermMetadataEntry| {
                (entry.module_index, entry.sentence_index, entry.field) == field
            };
            if !entries.peek().is_some_and(in_field) {
                break;
            }
            measure::bump(Counter::ProvenanceDecoderSteps);
            if let Some(entry) = entries.next_if(|entry| in_field(entry) && entry.node == node) {
                measure::bump(Counter::ProvenanceDecoderSteps);
                let metadata = decode_term_metadata(entry.metadata, source_table, tables)?;
                let taken = std::mem::replace(term, Term::Sequence(Vec::new()));
                *term = taken.with_metadata(metadata);
            }
            node = node.saturating_add(1);
            push_children_mut(term, &mut pending);
        }
    }
    Ok(())
}

fn decode_term_metadata(
    metadata: JsonTermMetadata,
    source_table: &SourceTable,
    tables: &DecodedTables,
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
            .map(|origin| decode_receipt(origin, tables).map(Arc::new))
            .transpose()?,
    })
}

fn encode_span(span: TermSpan, sources: usize) -> Result<JsonTermSpan, Error> {
    Ok(JsonTermSpan {
        source: source_index(sources, span.source)?,
        start: span.start,
        end: span.end,
    })
}

fn decode_span(span: JsonTermSpan, source_table: &SourceTable) -> Result<TermSpan, Error> {
    Ok(TermSpan {
        source: source_id(source_table, span.source)?,
        start: span.start,
        end: span.end,
    })
}

fn encode_link(link: &ProvenanceLink, sources: usize) -> Result<JsonOriginPart, Error> {
    Ok(match link {
        ProvenanceLink::Source { span } => JsonOriginPart::Source {
            source: source_index(sources, span.source)?,
            start: span.start,
            end: span.end,
        },
        ProvenanceLink::Sentence { unique_id } => JsonOriginPart::Sentence {
            unique_id: unique_id.clone(),
        },
    })
}

/// The link a part that is not a set reference denotes.
fn decode_link(link: JsonOriginPart, source_table: &SourceTable) -> Result<ProvenanceLink, Error> {
    Ok(match link {
        JsonOriginPart::Source { source, start, end } => ProvenanceLink::Source {
            span: TermSpan {
                source: source_id(source_table, source)?,
                start,
                end,
            },
        },
        JsonOriginPart::Sentence { unique_id } => ProvenanceLink::Sentence { unique_id },
        JsonOriginPart::Set { .. } => unreachable!("set references are decoded by the table"),
    })
}

/// Decode a receipt; its origin set and destination path are the table entries' allocations,
/// shared rather than copied.
fn decode_receipt(
    origin: JsonOriginReceipt,
    tables: &DecodedTables,
) -> Result<OriginRecord, Error> {
    let (origins, _) = usize::try_from(origin.origins)
        .ok()
        .and_then(|index| tables.origin_sets.get(index))
        .ok_or_else(|| {
            Error::InvalidProvenance(format!(
                "origin receipt names origin set {}, which the table does not contain",
                origin.origins
            ))
        })?;
    Ok(OriginRecord {
        pass: decode_pass(&origin.pass)?,
        origins: origins.clone(),
        destination: origin
            .destination
            .map(|anchor| tables.anchors.destination(anchor))
            .transpose()?,
    })
}

fn decode_pass(pass: &str) -> Result<GeneratingPass, Error> {
    GeneratingPass::from_name(pass)
        .ok_or_else(|| Error::InvalidProvenance(format!("unknown generating pass {pass:?}")))
}

fn decode_destination(destination: JsonDestinationAnchor) -> DestinationAnchor {
    DestinationAnchor {
        module: destination.module.into(),
        sentence: destination.sentence.into(),
        sentence_index: destination.sentence_index,
        path: destination.path.into(),
    }
}

/// The wire form of `source`: its index, which must name an entry of a table of `sources`.
fn source_index(sources: usize, source: SourceId) -> Result<usize, Error> {
    if source.0 < sources {
        Ok(source.0)
    } else {
        Err(invalid(format!("source id {} is not interned", source.0)))
    }
}

/// The source id a wire index names, which must be an entry of `source_table`.
fn source_id(source_table: &SourceTable, index: usize) -> Result<SourceId, Error> {
    if index < source_table.iter().len() {
        Ok(SourceId(index))
    } else {
        Err(invalid(format!(
            "source {index} is absent from the source table"
        )))
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

#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "Term is not a sentence kind; only the listed variants are special here"
)]
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
    ///
    /// The encoded map is the only copy the caller needs, so an origin receipt not rendered yet
    /// is rendered into it directly rather than cached on the shared receipt and then cloned.
    fn from(attributes: &Attributes) -> Self {
        let att = attributes
            .transient_wire_entries()
            .filter(|(key, _)| *key != AttributeKey::InputAddresses.as_str())
            .map(|(key, value)| (key.to_owned(), value.get().into_owned()))
            .collect();
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
struct JsonDefinition<S = JsonSentence> {
    node: DefinitionNode,
    #[serde(rename = "mainModule")]
    main_module: String,
    modules: Vec<JsonFlatModule<S>>,
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
}

impl JsonDefinition<ReadSentence> {
    fn decode(
        self,
        kind: DefinitionEnvelopeKind,
        mut omitted: Omissions<'_>,
    ) -> Result<Definition, Error> {
        let mut decoded = Definition {
            main_module: self.main_module,
            modules: Vec::with_capacity(self.modules.len()),
            attributes: self.att.into(),
        };
        for (index, module) in self.modules.into_iter().enumerate() {
            module.decode_into(kind, index, omitted.as_deref_mut(), &mut decoded.modules)?;
        }
        Ok(decoded)
    }
}

#[derive(Serialize, Deserialize)]
struct JsonFlatModule<S = JsonSentence> {
    node: FlatModuleNode,
    name: String,
    imports: Vec<JsonImport>,
    #[serde(rename = "localSentences")]
    local_sentences: Vec<S>,
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
}

impl JsonFlatModule<ReadSentence> {
    /// Decode the module at `module_index` of its document onto the end of `modules`. With
    /// `omitted`, a KAST v4 `badsentence` is skipped and its wire position recorded instead of
    /// being an error.
    fn decode_into(
        self,
        kind: DefinitionEnvelopeKind,
        module_index: usize,
        mut omitted: Omissions<'_>,
        modules: &mut Vec<FlatModule>,
    ) -> Result<(), Error> {
        modules.push(FlatModule {
            name: self.name,
            imports: self.imports.into_iter().map(Into::into).collect(),
            local_sentences: Vec::with_capacity(self.local_sentences.len()),
            attributes: self.att.into(),
        });
        let module = modules.last_mut().expect("the module was just pushed");
        for (index, ReadSentence(sentence)) in self.local_sentences.into_iter().enumerate() {
            if let (JsonSentence::KBadsentence, DefinitionEnvelopeKind::KastV4, Some(omitted)) =
                (&sentence, kind, omitted.as_deref_mut())
            {
                omitted.push(OmittedSentence {
                    module_index,
                    module: module.name.clone(),
                    index,
                });
                continue;
            }
            module
                .local_sentences
                .push(Arc::new(sentence.decode(kind)?));
        }
        Ok(())
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

/// A sentence on the wire, whose term fields are `T`: the [`JsonTerm`] form of a term when it
/// is written, and its raw JSON text ([`TermText`]) when it is read ([`ReadSentence`]).
#[derive(Serialize, Deserialize)]
#[serde(tag = "node")]
#[allow(clippy::enum_variant_names)] // Variant names mirror the external KAST schema.
enum JsonSentence<T = JsonTerm> {
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
        body: T,
        requires: T,
        att: JsonAttributes,
    },
    KContextAlias {
        body: T,
        requires: T,
        att: JsonAttributes,
    },
    KRule {
        body: T,
        requires: T,
        ensures: T,
        att: JsonAttributes,
    },
    KClaim {
        body: T,
        requires: T,
        ensures: T,
        att: JsonAttributes,
    },
    KConfiguration {
        body: T,
        ensures: T,
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

/// The keys of the sentence fields that hold terms, in every sentence kind that has them.
const TERM_FIELDS: [&str; 3] = ["body", "requires", "ensures"];

/// The raw JSON text of a term field of a sentence that is being read.
///
/// serde_json scans a value it keeps as raw text with an explicit stack, so a term of any depth
/// reaches [`term_json::term_from_str`], which decodes it with explicit work stacks.
#[derive(Deserialize)]
#[serde(transparent)]
struct TermText(String);

/// Decode the terms of one sentence, in order.
fn decode_terms<const N: usize>(texts: [TermText; N]) -> Result<[Term; N], Error> {
    let mut terms = Vec::with_capacity(N);
    for text in texts {
        terms.push(term_json::term_from_str(&text.0)?);
    }
    Ok(terms
        .try_into()
        .unwrap_or_else(|_| unreachable!("one term is decoded per text")))
}

/// A sentence as it is read.
///
/// A sentence's kind is named by its `node` member, which may come after the others, so serde
/// reads a sentence as it reads any tagged enum: it first gathers every member as a value of
/// its own, which recurses once per level of what the member holds. The members that hold
/// terms ([`TERM_FIELDS`]) are therefore handed to it as their raw text ([`TermText`]), which
/// serde_json scans with an explicit stack; the others are read as written, under serde's
/// recursion limit ([`SentenceMembers`]).
struct ReadSentence(JsonSentence<TermText>);

impl<'de> Deserialize<'de> for ReadSentence {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct Sentence;

        impl<'de> Visitor<'de> for Sentence {
            type Value = ReadSentence;

            fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                formatter.write_str("a KAST sentence object")
            }

            fn visit_map<A: MapAccess<'de>>(self, map: A) -> Result<ReadSentence, A::Error> {
                JsonSentence::deserialize(SentenceMembers { map, term: false }).map(ReadSentence)
            }
        }

        deserializer.deserialize_map(Sentence)
    }
}

/// The members of a sentence, read from `map` as they are written, except that the value of a
/// term member ([`TERM_FIELDS`]) is its raw JSON text, read as a string. `term` records whether
/// the member whose key was read last is a term member.
struct SentenceMembers<A> {
    map: A,
    term: bool,
}

/// The members are read only as a [`JsonSentence`], a tagged enum, which serde reads as a map
/// of whatever its members hold, so every request is answered as a map.
impl<'de, A: MapAccess<'de>> Deserializer<'de> for SentenceMembers<A> {
    type Error = A::Error;

    fn deserialize_any<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, A::Error> {
        visitor.visit_map(self)
    }

    serde::forward_to_deserialize_any! {
        bool i8 i16 i32 i64 i128 u8 u16 u32 u64 u128 f32 f64 char str string bytes byte_buf
        option unit unit_struct newtype_struct seq tuple tuple_struct map struct enum identifier
        ignored_any
    }
}

impl<'de, A: MapAccess<'de>> MapAccess<'de> for SentenceMembers<A> {
    type Error = A::Error;

    fn next_key_seed<K: DeserializeSeed<'de>>(
        &mut self,
        seed: K,
    ) -> Result<Option<K::Value>, A::Error> {
        let Some(key) = self.map.next_key::<String>()? else {
            return Ok(None);
        };
        self.term = TERM_FIELDS.contains(&key.as_str());
        seed.deserialize(StringDeserializer::new(key)).map(Some)
    }

    fn next_value_seed<V: DeserializeSeed<'de>>(&mut self, seed: V) -> Result<V::Value, A::Error> {
        if self.term {
            let text: Box<str> = self.map.next_value::<Box<RawValue>>()?.into();
            seed.deserialize(StringDeserializer::new(String::from(text)))
        } else {
            self.map.next_value_seed(seed)
        }
    }

    fn size_hint(&self) -> Option<usize> {
        self.map.size_hint()
    }
}

impl JsonSentence<TermText> {
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
            } => {
                let [body, requires] = decode_terms([body, requires])?;
                Sentence::Context {
                    body,
                    requires,
                    attributes: att.into(),
                }
            }
            JsonSentence::KContextAlias {
                body,
                requires,
                att,
            } => {
                if kind == DefinitionEnvelopeKind::KastV4 {
                    return Err(Error::UnsupportedSentence("KContextAlias"));
                }
                let [body, requires] = decode_terms([body, requires])?;
                Sentence::ContextAlias {
                    body,
                    requires,
                    attributes: att.into(),
                }
            }
            JsonSentence::KRule {
                body,
                requires,
                ensures,
                att,
            } => {
                let [body, requires, ensures] = decode_terms([body, requires, ensures])?;
                Sentence::Rule {
                    body,
                    requires,
                    ensures,
                    attributes: att.into(),
                }
            }
            JsonSentence::KClaim {
                body,
                requires,
                ensures,
                att,
            } => {
                let [body, requires, ensures] = decode_terms([body, requires, ensures])?;
                Sentence::Claim {
                    body,
                    requires,
                    ensures,
                    attributes: att.into(),
                }
            }
            JsonSentence::KConfiguration { body, ensures, att } => {
                let [body, ensures] = decode_terms([body, ensures])?;
                Sentence::Configuration {
                    body,
                    ensures,
                    attributes: att.into(),
                }
            }
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
    use crate::{
        definition::FlatModule,
        kast::Sort,
        provenance::{ORIGIN_ATTRIBUTE, record_generated_origins},
    };

    #[derive(Clone, Debug)]
    enum Stored {
        Record,
        Value,
    }

    /// A receipt to place: the index of its set in its pool, its pass, and the index of its
    /// destination in the anchor pool (none for a receipt without one).
    type ReceiptPlan = (usize, usize, Option<usize>);

    #[derive(Clone, Debug)]
    struct SentencePlan {
        /// The sentence receipt, whose set comes from the flat pool.
        receipt: Option<(ReceiptPlan, Stored)>,
        body_receipt: Option<ReceiptPlan>,
        child_receipt: Option<ReceiptPlan>,
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

    /// A part of a random origin-set DAG: a link, or one of the earlier sets.
    type PartSpec = (bool, (bool, u8), prop::sample::Index);

    /// An anchor of the pool: the root's module, sentence and index, and its path as an earlier
    /// pool path (or the root) extended by one step.
    type AnchorSpec = ((u8, u8, u32), Option<prop::sample::Index>, u32);

    /// How the receipts of a plan are allocated.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum Sharing {
        /// Sets and paths built once and shared, names shared per pool entry.
        Shared,
        /// Every receipt with its own copy of every set node, path and name.
        Copied,
        /// Sets built keeping every part (no drop, no collapse), shared.
        Raw,
    }

    struct Pools {
        flat: Vec<OriginSet>,
        dag: Vec<OriginSet>,
        anchors: Vec<DestinationAnchor>,
    }

    fn pools(
        flat: &[Vec<(bool, u8)>],
        dag: &[Vec<PartSpec>],
        anchors: &[AnchorSpec],
        sharing: Sharing,
    ) -> Pools {
        let flat = flat
            .iter()
            .map(|links| links.iter().copied().map(link).collect::<Vec<_>>().into())
            .collect();
        let mut sets = Vec::<OriginSet>::new();
        for parts in dag {
            let parts = parts
                .iter()
                .map(|(is_set, value, pick)| {
                    if *is_set && !sets.is_empty() {
                        OriginPart::Set(sets[pick.index(sets.len())].clone())
                    } else {
                        OriginPart::Link(link(*value))
                    }
                })
                .collect::<Vec<_>>();
            let set = if sharing == Sharing::Raw {
                OriginSet::from_raw_parts(parts)
            } else {
                OriginSet::from_parts(parts)
            };
            sets.push(set);
        }
        let mut paths = Vec::<AnchorPath>::new();
        let mut built = Vec::new();
        // One allocation per distinct name, shared by every pool anchor that uses it, so that
        // anchors sharing a name pair may differ in their sentence index alone (design §14.2).
        let mut names = HashMap::<String, Arc<str>>::new();
        let mut name =
            |text: String| Arc::clone(names.entry(text.clone()).or_insert_with(|| text.into()));
        for ((module, sentence, index), parent, step) in anchors {
            let base = parent
                .as_ref()
                .filter(|_| !paths.is_empty())
                .map_or_else(AnchorPath::new, |pick| {
                    paths[pick.index(paths.len())].clone()
                });
            let path = base.child(*step);
            paths.push(path.clone());
            built.push(DestinationAnchor {
                module: name(format!("M{}", module % 2)),
                sentence: name(format!("rule:{}", sentence % 2)),
                sentence_index: index % 2,
                path,
            });
        }
        Pools {
            flat,
            dag: sets,
            anchors: built,
        }
    }

    /// A copy of `set` in which every node is a new allocation.
    fn deep_copy(set: &OriginSet) -> OriginSet {
        if set.is_empty() {
            return OriginSet::new();
        }
        OriginSet::from_raw_parts(
            set.parts()
                .iter()
                .map(|part| match part {
                    OriginPart::Link(link) => OriginPart::Link(link.clone()),
                    OriginPart::Set(set) => OriginPart::Set(deep_copy(set)),
                })
                .collect(),
        )
    }

    fn record(
        sets: &[OriginSet],
        anchors: &[DestinationAnchor],
        (set, pass, anchor): ReceiptPlan,
        sharing: Sharing,
    ) -> OriginRecord {
        let origins = &sets[set % sets.len()];
        let destination = anchor.map(|anchor| anchors[anchor % anchors.len()].clone());
        match sharing {
            Sharing::Shared | Sharing::Raw => OriginRecord {
                pass: GeneratingPass::ALL[pass % GeneratingPass::ALL.len()],
                origins: origins.clone(),
                destination,
            },
            Sharing::Copied => OriginRecord {
                pass: GeneratingPass::ALL[pass % GeneratingPass::ALL.len()],
                origins: deep_copy(origins),
                destination: destination.map(|destination| DestinationAnchor {
                    module: destination.module.to_string().into(),
                    sentence: destination.sentence.to_string().into(),
                    sentence_index: destination.sentence_index,
                    path: destination.path.to_vec().into(),
                }),
            },
        }
    }

    fn sources() -> SourceTable {
        let mut sources = SourceTable::default();
        sources.intern(LogicalSourceId::new("a.k", b"a"));
        sources.intern(LogicalSourceId::new("b.k", b"b"));
        sources
    }

    /// The definition of `plans` with its receipts allocated as `sharing` says, and the raw
    /// in-memory JSON form of each sentence receipt stored as a value.
    fn planned_definition(
        plans: &[SentencePlan],
        flat: &[Vec<(bool, u8)>],
        dag: &[Vec<PartSpec>],
        anchors: &[AnchorSpec],
        sharing: Sharing,
    ) -> (Definition, Vec<Option<Value>>) {
        let pools = pools(flat, dag, anchors, sharing);
        let mut raw_receipts = Vec::new();
        let term_metadata = |receipt: &Option<ReceiptPlan>| TermMetadata {
            origin: receipt
                .map(|receipt| Arc::new(record(&pools.dag, &pools.anchors, receipt, sharing))),
            ..TermMetadata::default()
        };
        let sentences = plans
            .iter()
            .map(|plan| {
                let mut attributes = Attributes::default();
                match &plan.receipt {
                    Some((receipt, Stored::Record)) => {
                        attributes.set_origin_record(record(
                            &pools.flat,
                            &pools.anchors,
                            *receipt,
                            sharing,
                        ));
                        raw_receipts.push(None);
                    }
                    Some((receipt, Stored::Value)) => {
                        let value =
                            record(&pools.flat, &pools.anchors, *receipt, sharing).to_value();
                        attributes.insert(ORIGIN_ATTRIBUTE, value.clone());
                        raw_receipts.push(Some(value));
                    }
                    None => raw_receipts.push(None),
                }
                let child = Term::variable("X").with_metadata(term_metadata(&plan.child_receipt));
                Arc::new(Sentence::Rule {
                    body: Term::apply("f", vec![child])
                        .with_metadata(term_metadata(&plan.body_receipt)),
                    requires: Term::Token {
                        token: "true".into(),
                        sort: Sort::new("Bool"),
                    },
                    ensures: Term::Token {
                        token: "true".into(),
                        sort: Sort::new("Bool"),
                    },
                    attributes,
                })
            })
            .collect();
        (
            Definition {
                main_module: "MAIN".into(),
                modules: vec![FlatModule {
                    name: "MAIN".into(),
                    imports: Vec::new(),
                    local_sentences: sentences,
                    attributes: Attributes::default(),
                }],
                attributes: Attributes::default(),
            },
            raw_receipts,
        )
    }

    /// Every term receipt's set of a definition in traversal order: the body root's, then its
    /// child's.
    fn term_sets(definition: &Definition) -> Vec<Option<OriginSet>> {
        let mut sets = Vec::new();
        for sentence in &definition.modules[0].local_sentences {
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
                        .map(|origin| origin.origins.clone()),
                );
            }
        }
        sets
    }

    fn sentence_plan() -> impl Strategy<Value = SentencePlan> {
        let stored = prop_oneof![Just(Stored::Record), Just(Stored::Value)];
        let receipt = || (0_usize..8, 0_usize..32, proptest::option::of(0_usize..8));
        (
            proptest::option::of((receipt(), stored)),
            proptest::option::of(receipt()),
            proptest::option::of(receipt()),
        )
            .prop_map(|(receipt, body_receipt, child_receipt)| SentencePlan {
                receipt,
                body_receipt,
                child_receipt,
            })
    }

    fn flat_specs() -> impl Strategy<Value = Vec<Vec<(bool, u8)>>> {
        prop::collection::vec(prop::collection::vec((any::<bool>(), 0_u8..4), 0..5), 1..5)
    }

    fn dag_specs() -> impl Strategy<Value = Vec<Vec<PartSpec>>> {
        prop::collection::vec(
            prop::collection::vec(
                (
                    any::<bool>(),
                    (any::<bool>(), 0_u8..4),
                    any::<prop::sample::Index>(),
                ),
                0..5,
            ),
            1..7,
        )
    }

    fn anchor_specs() -> impl Strategy<Value = Vec<AnchorSpec>> {
        prop::collection::vec(
            (
                (0_u8..4, 0_u8..4, 0_u32..4),
                proptest::option::of(any::<prop::sample::Index>()),
                0_u32..3,
            ),
            1..6,
        )
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(256))]

        /// Decoding the encoded document gives receipts equal to the encoded ones (pass,
        /// flattened links, full destination), re-encoding the decoded definition gives the
        /// same bytes (the canonical fixed point), and receipts that shared one set allocation
        /// before encoding share one after decoding. The sets are random DAGs whose nodes are
        /// reached along several paths, and the destinations random paths that share prefixes.
        #[test]
        fn origin_set_table_round_trips_receipts_and_sharing(
            flat in flat_specs(),
            dag in dag_specs(),
            anchors in anchor_specs(),
            plans in prop::collection::vec(sentence_plan(), 1..8),
        ) {
            let sources = sources();
            let (definition, raw_receipts) =
                planned_definition(&plans, &flat, &dag, &anchors, Sharing::Shared);

            let encoded = to_provenance_string(&definition, &sources).unwrap();
            let decoded = from_provenance_str(&encoded).unwrap();
            prop_assert_eq!(&decoded.source_table, &sources);
            prop_assert_eq!(&decoded.definition, &definition);
            prop_assert_eq!(
                to_provenance_string(&decoded.definition, &decoded.source_table).unwrap(),
                encoded.clone()
            );

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

            let before = term_sets(&definition);
            let after = term_sets(&decoded.definition);
            for (left, decoded_left) in before.iter().zip(&after) {
                for (right, decoded_right) in before.iter().zip(&after) {
                    if let (Some(left), Some(right), Some(decoded_left), Some(decoded_right)) =
                        (left, right, decoded_left, decoded_right)
                        && left.ptr_eq(right)
                    {
                        prop_assert!(decoded_left.ptr_eq(decoded_right));
                    }
                }
            }
        }

        /// The bytes are a function of the receipts' normal forms, not of how memory is shared
        /// (design theorem B, V2b): the same receipts with every set node, path and name copied
        /// per receipt, or with the sets built keeping every part the construction would drop
        /// or collapse, encode to the same document.
        #[test]
        fn encoding_does_not_depend_on_sharing(
            flat in flat_specs(),
            dag in dag_specs(),
            anchors in anchor_specs(),
            plans in prop::collection::vec(sentence_plan(), 1..8),
        ) {
            let sources = sources();
            let encode = |sharing| {
                let (definition, _) = planned_definition(&plans, &flat, &dag, &anchors, sharing);
                to_provenance_string(&definition, &sources).unwrap()
            };
            let shared = encode(Sharing::Shared);
            prop_assert_eq!(&encode(Sharing::Copied), &shared);
            prop_assert_eq!(&encode(Sharing::Raw), &shared);
        }

        /// Recording a pass over a definition decoded from its document gives the same document
        /// as recording it over the definition itself (design corollary C, V2c): a rule body
        /// carrying spans is changed by two generating passes, so that its receipts name the
        /// sets of earlier passes, and then by a third; the third pass meets other allocations
        /// on the decoded route but the same normal forms.
        #[test]
        fn recording_after_a_round_trip_writes_the_same_document(
            body in route_term(),
            edits in prop::collection::vec((0_u8..3, any::<bool>(), 0_usize..25), 3),
        ) {
            let mut sources = SourceTable::default();
            sources.intern(LogicalSourceId::new("a.k", b"a"));
            let mut definition = route_definition(body.clone(), &Attributes::default());
            for (pass, edit) in edits.iter().take(2).enumerate() {
                definition = record_generated_origins(
                    &definition,
                    edited(&definition, *edit),
                    GeneratingPass::ALL[pass + 1],
                );
            }
            let third = |definition: &Definition| {
                let after = record_generated_origins(
                    definition,
                    edited(definition, edits[2]),
                    GeneratingPass::AddSortInjections,
                );
                to_provenance_string(&after, &sources).unwrap()
            };
            let decoded = from_provenance_str(&to_provenance_string(&definition, &sources).unwrap())
                .unwrap()
                .definition;
            prop_assert_eq!(third(&decoded), third(&definition));
        }
    }

    /// Random rule bodies: an application at the root, and below it terms of up to three more
    /// levels in which every constructor occurs (rewrites, aliases, sequences, applications,
    /// variables and tokens), some nodes carrying a span.
    fn route_term() -> impl Strategy<Value = Term> {
        let span = || proptest::option::of(0_usize..20);
        let leaf = (0_u8..3, 0_u8..3, span()).prop_map(|(kind, label, span)| {
            let leaf = match kind {
                0 => Term::apply(format!("l{label}"), Vec::new()),
                1 => Term::variable(format!("X{label}")),
                _ => Term::Token {
                    token: label.to_string(),
                    sort: Sort::new("Int"),
                },
            };
            spanned(leaf, span)
        });
        let inner = leaf.prop_recursive(3, 24, 3, move |inner| {
            (0_u8..4, 0_u8..3, span(), prop::collection::vec(inner, 2..4)).prop_map(
                |(kind, label, span, mut children)| {
                    let node = match kind {
                        0 | 1 => {
                            let second = Box::new(children.swap_remove(1));
                            let first = Box::new(children.swap_remove(0));
                            if kind == 0 {
                                Term::Rewrite {
                                    left: first,
                                    right: second,
                                }
                            } else {
                                Term::As {
                                    pattern: first,
                                    alias: second,
                                }
                            }
                        }
                        2 => Term::Sequence(children),
                        _ => Term::apply(format!("n{label}"), children),
                    };
                    spanned(node, span)
                },
            )
        });
        (0_u8..3, span(), prop::collection::vec(inner, 1..4)).prop_map(|(label, span, children)| {
            spanned(Term::apply(format!("n{label}"), children), span)
        })
    }

    fn spanned(term: Term, span: Option<usize>) -> Term {
        term.with_metadata(TermMetadata {
            span: span.map(|start| TermSpan {
                source: SourceId(0),
                start,
                end: start + 1,
            }),
            ..TermMetadata::default()
        })
    }

    fn route_definition(body: Term, attributes: &Attributes) -> Definition {
        Definition {
            main_module: "MAIN".into(),
            modules: vec![FlatModule {
                name: "MAIN".into(),
                imports: Vec::new(),
                local_sentences: vec![Arc::new(Sentence::Rule {
                    body,
                    requires: Term::Token {
                        token: "true".into(),
                        sort: Sort::new("Bool"),
                    },
                    ensures: Term::Token {
                        token: "true".into(),
                        sort: Sort::new("Bool"),
                    },
                    attributes: attributes.clone(),
                })],
                attributes: Attributes::default(),
            }],
            attributes: Attributes::default(),
        }
    }

    /// `definition` with its rule body changed as a pass might change it, the rule's attributes
    /// (its receipt among them) kept: `(0, _, _)` wraps the body in a new node, `(1, keep, _)`
    /// rebuilds the root under a new label (keeping its metadata or not), and `(2, _, n)`
    /// replaces the `n`th node of the leftmost path with a new leaf.
    fn edited(definition: &Definition, (kind, keep, depth): (u8, bool, usize)) -> Definition {
        let sentence = &definition.modules[0].local_sentences[0];
        let Sentence::Rule {
            body, attributes, ..
        } = &**sentence
        else {
            unreachable!()
        };
        let body = match kind {
            0 => Term::apply("wrap", vec![body.clone()]),
            1 => {
                let Term::Apply { arguments, .. } = body.unannotated() else {
                    unreachable!()
                };
                let rebuilt = Term::apply("rebuilt", arguments.clone());
                if keep {
                    rebuilt.with_metadata(body.metadata().cloned().unwrap_or_default())
                } else {
                    rebuilt
                }
            }
            _ => {
                let mut body = body.clone();
                replace_leftmost(&mut body, depth, "replaced");
                body
            }
        };
        route_definition(body, attributes)
    }

    /// Replace the node `depth` levels down the leftmost path of `term` (or its leaf, when the
    /// path is shorter) with a new leaf labelled `label`; the leftmost child of a rewrite is its
    /// left side and of an alias its pattern.
    fn replace_leftmost(term: &mut Term, depth: usize, label: &str) {
        let first = match unannotated_mut(term) {
            Term::Rewrite { left: first, .. } | Term::As { pattern: first, .. } => {
                Some(&mut **first)
            }
            Term::Sequence(items)
            | Term::Apply {
                arguments: items, ..
            } => items.first_mut(),
            Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => None,
            Term::Annotated { .. } => unreachable!("unannotated strips annotations"),
        };
        match first {
            Some(first) if depth > 0 => replace_leftmost(first, depth - 1, label),
            _ => *term = Term::apply(label, Vec::new()),
        }
    }

    /// The preorder of term-metadata addresses on a term holding every constructor, against a
    /// list written from the format's statement of it (`JsonTermMetadataEntry::node`): each node
    /// carries a sort naming it, and the entry with index k must carry the k-th name. Both walks
    /// built from `push_children_in_preorder!` visit the same list.
    #[test]
    fn metadata_addresses_number_every_constructor_in_preorder() {
        let named = |term: Term, name: &str| {
            term.with_metadata(TermMetadata {
                sort: Some(Sort::new(name)),
                ..TermMetadata::default()
            })
        };
        let body = named(
            Term::apply(
                "r",
                vec![named(
                    Term::Rewrite {
                        left: Box::new(named(
                            Term::As {
                                pattern: Box::new(named(
                                    Term::apply(
                                        "f",
                                        vec![
                                            named(Term::variable("X"), "X"),
                                            named(
                                                Term::Token {
                                                    token: "1".into(),
                                                    sort: Sort::new("Int"),
                                                },
                                                "one",
                                            ),
                                        ],
                                    ),
                                    "f",
                                )),
                                alias: Box::new(named(Term::variable("Y"), "Y")),
                            },
                            "as",
                        )),
                        right: Box::new(named(
                            Term::Sequence(vec![
                                named(Term::apply("g", Vec::new()), "g"),
                                named(Term::InjectedLabel(crate::kast::Label::new("h")), "h"),
                            ]),
                            "seq",
                        )),
                    },
                    "rewrite",
                )],
            ),
            "r",
        );
        let expected = ["r", "rewrite", "as", "f", "X", "one", "Y", "seq", "g", "h"];
        let name = |term: &Term| {
            term.metadata()
                .and_then(|metadata| metadata.sort.as_ref())
                .map(|sort| sort.name.clone())
                .expect("every node is named")
        };
        let mut visited = Vec::new();
        let mut pending = vec![&body];
        while let Some(term) = pending.pop() {
            visited.push(name(term));
            push_children(term, &mut pending);
        }
        assert_eq!(visited, expected);
        let mut copy = body.clone();
        let mut visited = Vec::new();
        let mut pending = vec![&mut copy];
        while let Some(term) = pending.pop() {
            visited.push(name(term));
            push_children_mut(term, &mut pending);
        }
        assert_eq!(visited, expected);

        let definition = route_definition(body, &Attributes::default());
        let document: Value = serde_json::from_str(
            &to_provenance_string(&definition, &SourceTable::default()).unwrap(),
        )
        .unwrap();
        let written = document["termMetadata"]
            .as_array()
            .unwrap()
            .iter()
            .map(|entry| {
                (
                    entry["node"].as_u64().unwrap(),
                    entry["metadata"]["sort"]["name"]
                        .as_str()
                        .unwrap()
                        .to_owned(),
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(
            written,
            (0..).zip(expected.map(String::from)).collect::<Vec<_>>()
        );
    }

    /// One sentence of each term-bearing kind (rule, claim, context, context alias,
    /// configuration), its fields taken from `terms` in order, each node given metadata drawn
    /// from `seeds`: a span in either of two sources, a production, a sort and a receipt, each
    /// present or not.
    fn shapes_definition(terms: &[Term], seeds: &[u32]) -> Definition {
        let mut next = 0usize;
        let mut metadata = || {
            let bits = seeds[next % seeds.len()];
            next += 1;
            let start = ((bits >> 4) & 63) as usize;
            let metadata = TermMetadata {
                span: (bits & 1 << 2 != 0).then(|| TermSpan {
                    source: SourceId(((bits >> 3) & 1) as usize),
                    start,
                    end: start + 1 + ((bits >> 10) & 3) as usize,
                }),
                production: (bits & 1 << 12 != 0)
                    .then(|| ProductionIdentity::from_digest([((bits >> 13) & 0xff) as u8; 16])),
                sort: (bits & 1 << 21 != 0).then(|| Sort::new(format!("S{}", (bits >> 22) & 3))),
                origin: (bits & 1 << 24 != 0).then(|| {
                    Arc::new(OriginRecord {
                        pass: GeneratingPass::ALL
                            [((bits >> 25) & 31) as usize % GeneratingPass::ALL.len()],
                        origins: vec![link((bits & 1 << 30 != 0, ((bits >> 4) & 3) as u8))].into(),
                        destination: Some(DestinationAnchor {
                            module: "MAIN".into(),
                            sentence: "s".into(),
                            sentence_index: (bits >> 31) & 1,
                            path: AnchorPath::from(vec![(bits >> 27) & 3]),
                        }),
                    })
                }),
            };
            (metadata != TermMetadata::default()).then_some(metadata)
        };
        let mut terms = terms
            .iter()
            .map(|term| crate::kast::test_terms::decorated(term, &mut metadata));
        let mut term = || terms.next().expect("one term per field");
        let sentences = vec![
            Sentence::Rule {
                body: term(),
                requires: term(),
                ensures: term(),
                attributes: Attributes::default(),
            },
            Sentence::Claim {
                body: term(),
                requires: term(),
                ensures: term(),
                attributes: Attributes::default(),
            },
            Sentence::Context {
                body: term(),
                requires: term(),
                attributes: Attributes::default(),
            },
            Sentence::ContextAlias {
                body: term(),
                requires: term(),
                attributes: Attributes::default(),
            },
            Sentence::Configuration {
                body: term(),
                ensures: term(),
                attributes: Attributes::default(),
            },
        ];
        Definition {
            main_module: "MAIN".into(),
            modules: vec![FlatModule {
                name: "MAIN".into(),
                imports: Vec::new(),
                local_sentences: sentences.into_iter().map(Arc::new).collect(),
                attributes: Attributes::default(),
            }],
            attributes: Attributes::default(),
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(256))]

        /// The metadata of a term in any field of any term-bearing sentence kind, decoded from
        /// its document, is the metadata of the node it was written for, and re-encoding the
        /// decoded definition gives the same bytes. The terms hold every constructor, and
        /// decoded and written nodes are paired by the constructors' fields
        /// (`test_terms::paired`), not by the walk that numbers them, so a reader that walks any
        /// arm in another order than the writer attaches metadata to a node it does not match
        /// (design §14.1, G4c for C1, C2, C5, C6 and C10).
        #[test]
        fn term_metadata_round_trips_on_every_constructor_and_field(
            terms in prop::collection::vec(crate::kast::test_terms::every_constructor(), 12),
            seeds in prop::collection::vec(any::<u32>(), 1..48),
        ) {
            let sources = sources();
            let definition = shapes_definition(&terms, &seeds);
            let encoded = to_provenance_string(&definition, &sources).unwrap();
            let decoded = from_provenance_str(&encoded).unwrap().definition;
            prop_assert_eq!(&decoded, &definition);
            for (written, read) in definition.modules[0]
                .local_sentences
                .iter()
                .zip(&decoded.modules[0].local_sentences)
            {
                for ((field, written), (read_field, read)) in written.terms().zip(read.terms()) {
                    prop_assert_eq!(field, read_field);
                    for (written, read) in crate::kast::test_terms::paired(written, read) {
                        prop_assert_eq!(read.metadata(), written.metadata(), "field {}", field);
                    }
                }
            }
            prop_assert_eq!(to_provenance_string(&decoded, &sources).unwrap(), encoded);
        }
    }

    /// The sizes of what the receipts of `definition` reach: distinct set allocations, their
    /// parts, receipts, distinct path-step allocations, and term nodes of every field; counted
    /// here independently of the code under test.
    struct Reach {
        sets: usize,
        parts: usize,
        receipts: usize,
        steps: usize,
        nodes: usize,
        /// Distinct `(module, sentence, sentence index)` destination roots by name allocation.
        root_triples: usize,
        /// Distinct name allocations (modules and sentences) of the destinations.
        names: usize,
        /// Distinct `(sentence, pass)` pairs of the receipts that have a destination.
        sentence_passes: usize,
    }

    fn reach(definition: &Definition) -> Reach {
        let mut sets = HashSet::new();
        let mut steps = HashSet::new();
        let mut root_triples = HashSet::new();
        let mut names = HashSet::new();
        let mut sentence_passes = HashSet::new();
        let mut reach = Reach {
            sets: 0,
            parts: 0,
            receipts: 0,
            steps: 0,
            nodes: 0,
            root_triples: 0,
            names: 0,
            sentence_passes: 0,
        };
        let mut receipt = |record: &OriginRecord, sentence: (usize, usize), reach: &mut Reach| {
            reach.receipts += 1;
            if let Some(destination) = &record.destination {
                let (module, name) = (
                    str_address(&destination.module),
                    str_address(&destination.sentence),
                );
                reach.root_triples +=
                    usize::from(root_triples.insert((module, name, destination.sentence_index)));
                reach.names += usize::from(names.insert(module)) + usize::from(names.insert(name));
                reach.sentence_passes +=
                    usize::from(sentence_passes.insert((sentence, record.pass.as_str())));
            }
            let mut pending = vec![record.origins.clone()];
            while let Some(set) = pending.pop() {
                if set.is_empty() || !sets.insert(set.address()) {
                    continue;
                }
                reach.sets += 1;
                reach.parts += set.parts().len();
                for part in set.parts() {
                    if let OriginPart::Set(set) = part {
                        pending.push(set.clone());
                    }
                }
            }
            if let Some(destination) = &record.destination {
                let mut path = destination.path.clone();
                while let Some((up, _)) = path.split_last() {
                    if !steps.insert(path.address()) {
                        break;
                    }
                    reach.steps += 1;
                    path = up.clone();
                }
            }
        };
        for (module_index, module) in definition.modules.iter().enumerate() {
            for (sentence_index, sentence) in module.local_sentences.iter().enumerate() {
                let at = (module_index, sentence_index);
                if let Some(record) = sentence.attributes().origin_record() {
                    receipt(record, at, &mut reach);
                }
                for (_, term) in sentence.terms() {
                    let mut pending = vec![term];
                    while let Some(term) = pending.pop() {
                        reach.nodes += 1;
                        if let Some(record) = term.metadata().and_then(|m| m.origin.as_deref()) {
                            receipt(record, at, &mut reach);
                        }
                        push_children(term, &mut pending);
                    }
                }
            }
        }
        reach
    }

    /// The rule `s(s(...(leaf)))`, `depth` levels with a span each, and the same rule with its
    /// leaf replaced, every other node keeping its metadata.
    fn chain_with_leaf(previous: Option<&Definition>, depth: usize, leaf: &str) -> Definition {
        let body = match previous {
            Some(previous) => {
                let mut body = previous.modules[0].local_sentences[0]
                    .term(0)
                    .expect("a rule has a body")
                    .clone();
                replace_leftmost(&mut body, usize::MAX, leaf);
                body
            }
            None => (1..depth).fold(Term::apply(leaf, Vec::new()), |term, level| {
                spanned(Term::apply("s", vec![term]), Some(level))
            }),
        };
        let attributes = previous.map_or_else(Attributes::default, |previous| {
            previous.modules[0].local_sentences[0].attributes().clone()
        });
        route_definition(body, &attributes)
    }

    /// The writer refuses, in every build, a sentence receipt naming a set that names other
    /// sets: its reader refuses such a document, and the writer writes nothing its reader
    /// refuses.
    #[test]
    fn a_sentence_receipt_naming_nested_sets_is_not_written() {
        let mut attributes = Attributes::default();
        attributes.set_origin_record(OriginRecord {
            pass: GeneratingPass::MacroExpansion,
            origins: OriginSet::from_parts([
                OriginPart::Link(link((false, 0))),
                OriginPart::Set(OriginSet::from(vec![link((false, 1)), link((false, 2))])),
            ]),
            destination: None,
        });
        let definition = route_definition(Term::variable("X"), &attributes);
        let result = to_provenance_string(&definition, &sources());
        assert!(
            matches!(&result, Err(Error::InvalidProvenance(message)) if message.contains("names other sets")),
            "{result:?}"
        );
    }

    /// The grid of design V6g: three passes each rebuild every node of a 2,000-level chain, each
    /// node naming its counterpart's set and the set of the node above it, so the sets of the
    /// last pass reach those of every earlier one along about C(2003, 3) paths. The work of
    /// flattening, encoding and decoding is bounded by the sizes of the structures, which the
    /// test counts itself: a walk without its visited-node memo, or keyed wrongly, exceeds its
    /// bound by orders of magnitude.
    ///
    /// The encoder's numbering of metadata addresses expands at most the nodes of the sentence
    /// fields, as the decoder's walk to attach them is bounded by the same nodes.
    ///
    /// Sharing that the bytes cannot show (design §13.2, B2) is bounded structurally: the
    /// recorder holds one pair of name allocations per sentence and pass and the decoder one per
    /// root entry, the encoder interns each pair of name allocations by value once, and decoding
    /// creates one path step per step entry of the anchor table.
    #[test]
    fn provenance_work_is_bounded_by_the_structures_it_walks() {
        const DEPTH: usize = 2_000;
        let mut sources = SourceTable::default();
        sources.intern(LogicalSourceId::new("a.k", b"a"));
        let mut definition = chain_with_leaf(None, DEPTH, "z0");
        for (pass, leaf) in ["z1", "z2", "z3"].into_iter().enumerate() {
            let after = chain_with_leaf(Some(&definition), DEPTH, leaf);
            definition =
                record_generated_origins(&definition, after, GeneratingPass::ALL[pass + 1]);
        }
        let reach = reach(&definition);
        assert!(
            reach.names <= 2 * reach.sentence_passes,
            "{} name allocations for {} (sentence, pass) pairs of {} receipts",
            reach.names,
            reach.sentence_passes,
            reach.receipts
        );
        // The deepest receipt: its set names its counterpart's and its parent's, so it reaches
        // the set of every node of every pass, along the most paths. (The root's set names only
        // the root's earlier sets and the flat sentence set, which no walk can make expensive.)
        let mut node = definition.modules[0].local_sentences[0]
            .term(0)
            .expect("a rule has a body");
        let mut deepest = None;
        loop {
            if let Some(origin) = node.metadata().and_then(|metadata| metadata.origin.clone()) {
                deepest = Some(origin);
            }
            if let Term::Apply { arguments, .. } = node.unannotated()
                && let Some(first) = arguments.first()
            {
                node = first;
            } else {
                break;
            }
        }
        let deepest = deepest.expect("the rebuilt chain has receipts");
        assert!(!deepest.origins.is_flat());

        let counted = |counter: Counter, work: &mut dyn FnMut()| {
            let start = measure::snapshot();
            work();
            measure::snapshot().delta(&start).get(counter)
        };
        let flattened = counted(Counter::ProvenanceLinksSteps, &mut || {
            // The spans of levels 1 to DEPTH - 1; the leaf has none.
            assert_eq!(deepest.origins.links().len(), DEPTH - 1);
        });
        assert!(
            flattened <= (reach.sets + reach.parts) as u64,
            "flattening the deepest set took {flattened} steps over {} sets of {} parts",
            reach.sets,
            reach.parts
        );

        let start = measure::snapshot();
        let encoded = to_provenance_string(&definition, &sources).unwrap();
        let encoding = measure::snapshot().delta(&start);
        assert_eq!(
            encoding.get(Counter::ProvenanceEncoderSetKeys),
            reach.sets as u64,
            "set keys computed"
        );
        assert_eq!(
            encoding.get(Counter::ProvenanceEncoderAnchorRoots),
            reach.root_triples as u64,
            "roots interned by value"
        );
        // The encoder reads a path's steps through `split_last`, which counts each: one per step
        // not yet resolved under its root, and one per receipt for the step its walk stops at.
        assert!(
            encoding.get(Counter::ProvenanceAnchorPathSteps)
                <= (reach.steps + reach.receipts) as u64,
            "{} path steps walked to encode {} step allocations of {} receipts",
            encoding.get(Counter::ProvenanceAnchorPathSteps),
            reach.steps,
            reach.receipts
        );
        let internings = encoding.get(Counter::ProvenanceEncoderAnchorInternings);
        assert!(
            internings <= (reach.receipts + reach.steps) as u64,
            "{internings} anchor internings for {} receipts and {} step allocations",
            reach.receipts,
            reach.steps
        );
        // Metadata addresses are numbered by one walk per field, which expands each node of the
        // fields once; recomputing an annotated node's index by walking from its field's root
        // expands about DEPTH^2 / 2 nodes per pass on this chain.
        let expanded = encoding.get(Counter::ProvenanceEncoderPreorderSteps);
        assert!(
            expanded <= reach.nodes as u64,
            "{expanded} nodes expanded to number {} nodes of the sentence fields",
            reach.nodes
        );

        // The tables the document holds, rebuilt by the encoder's own walk: the document's term
        // nests deeper than a JSON value can be parsed.
        let mut encoder = ProvenanceEncoder::new(&sources);
        JsonDefinition::encode(
            &definition,
            DefinitionEnvelopeKind::Provenance,
            &mut |attributes| encoder.attributes(attributes),
        )
        .unwrap();
        let mut metadata = Vec::new();
        collect_definition_metadata(&definition, &mut encoder, &mut metadata).unwrap();
        let bound = encoder.origin_sets.len()
            + encoder.origin_sets.iter().map(Vec::len).sum::<usize>()
            + encoder.anchors.len()
            + metadata.len()
            + reach.nodes;
        let step_entries = encoder
            .anchors
            .iter()
            .filter(|anchor| matches!(anchor, JsonAnchor::Step(_)))
            .count();
        let root_entries = encoder.anchors.len() - step_entries;
        let start = measure::snapshot();
        let decoded = from_provenance_str(&encoded).unwrap().definition;
        let decoding = measure::snapshot().delta(&start);
        let steps = decoding.get(Counter::ProvenanceDecoderSteps);
        assert!(
            steps <= bound as u64,
            "{steps} decoder steps, bound {bound}"
        );
        assert!(
            decoding.get(Counter::ProvenanceAnchorPathSteps) <= step_entries as u64,
            "{} path steps created or walked to decode {step_entries} step entries",
            decoding.get(Counter::ProvenanceAnchorPathSteps)
        );
        let decoded_reach = self::reach(&decoded);
        assert!(
            decoded_reach.names <= 2 * root_entries,
            "{} name allocations decoded from {root_entries} root entries",
            decoded_reach.names
        );
        assert_eq!(decoded, definition);
    }

    /// Every walk of the provenance writer and reader is iterative: a 100,000-level field whose
    /// every node holds a receipt (each naming a set that names the one below, and a path one
    /// step longer than the one above) has its sets, anchors and metadata written, and the
    /// tables and metadata read back, on a 256 KiB thread.
    #[test]
    fn provenance_tables_and_metadata_of_any_depth_on_a_small_stack() {
        const LEVELS: u32 = 100_000;
        let sources = sources();
        let mut sets = Vec::with_capacity(LEVELS as usize);
        let mut set = OriginSet::new();
        for level in 0..LEVELS {
            set = OriginSet::from_parts([
                OriginPart::Link(link((false, (level % 200) as u8))),
                OriginPart::Link(ProvenanceLink::Sentence {
                    unique_id: format!("u{level}"),
                }),
                OriginPart::Set(set),
            ]);
            sets.push(set.clone());
        }
        let (module, sentence): (Arc<str>, Arc<str>) = ("MAIN".into(), "rule".into());
        let mut paths = Vec::with_capacity(LEVELS as usize);
        let mut path = AnchorPath::new().child(0);
        for _ in 0..LEVELS {
            paths.push(path.clone());
            path = path.child(0);
        }
        let receipt = |level: usize| TermMetadata {
            origin: Some(Arc::new(OriginRecord {
                pass: GeneratingPass::MacroExpansion,
                origins: sets[level].clone(),
                destination: Some(DestinationAnchor {
                    module: Arc::clone(&module),
                    sentence: Arc::clone(&sentence),
                    sentence_index: 0,
                    path: paths[level].clone(),
                }),
            })),
            ..TermMetadata::default()
        };
        // The root holds the receipt of level 0 and the leaf that of the last level.
        let mut annotated = Term::variable("X").with_metadata(receipt(LEVELS as usize - 1));
        let mut plain = Term::variable("X");
        for level in (0..LEVELS as usize - 1).rev() {
            annotated = Term::apply("s", vec![annotated]).with_metadata(receipt(level));
            plain = Term::apply("s", vec![plain]);
        }
        let annotated = route_definition(annotated, &Attributes::default());
        let mut plain = route_definition(plain, &Attributes::default());
        std::thread::scope(|scope| {
            std::thread::Builder::new()
                .stack_size(256 << 10)
                .spawn_scoped(scope, || {
                    let mut encoder = ProvenanceEncoder::new(&sources);
                    let mut metadata = Vec::new();
                    collect_definition_metadata(&annotated, &mut encoder, &mut metadata).unwrap();
                    assert_eq!(metadata.len(), LEVELS as usize);
                    assert_eq!(encoder.origin_sets.len(), LEVELS as usize);
                    // The root, then one step per level.
                    assert_eq!(encoder.anchors.len(), LEVELS as usize + 1);
                    let tables = DecodedTables {
                        origin_sets: decode_origin_sets(encoder.origin_sets, &sources).unwrap(),
                        anchors: decode_anchors(encoder.anchors).unwrap(),
                    };
                    attach_term_metadata(&mut plain, metadata, &sources, &tables).unwrap();
                    let mut node = plain.modules[0].local_sentences[0].term(0).unwrap();
                    let mut level = 0;
                    loop {
                        let origin = node.metadata().unwrap().origin.as_deref().unwrap();
                        let destination = origin.destination.as_ref().unwrap();
                        assert_eq!(destination.path.len(), level + 1);
                        let Term::Apply { arguments, .. } = node.unannotated() else {
                            break;
                        };
                        node = &arguments[0];
                        level += 1;
                    }
                    assert_eq!(level, LEVELS as usize - 1);
                    let deepest = &tables.origin_sets.last().unwrap().0;
                    assert_eq!(deepest.links().len(), 200 + LEVELS as usize);
                    drop(tables);
                })
                .expect("the worker should spawn")
                .join()
                .expect("the worker should finish");
        });
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
