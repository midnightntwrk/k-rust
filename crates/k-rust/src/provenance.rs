//! ```toml algorithm
//! id = "definition.provenance.record"
//! name = "recording of generation-origin receipts"
//! sites = ["record_generated_origins", "sentence_counterparts", "annotate_term", "insert_link", "CarrierOrigins::origins"]
//! variable = "N = sentences and changed term nodes; k = origin links per visited node; M = modules; D = total size of the local sentences cloned and compared; s = maximum semantic sentence size"
//! counters = ["ProvenanceLinkDedupProbes", "KompileSentenceCopies"]
//!
//! [[cost]]
//! mode = "one order-preserving generating pass with distinct fallback bucket keys"
//! bound = "O(M^2 + D + N + sum k) expected"
//!
//! [[cost]]
//! mode = "one generating pass with adversarial fallback buckets"
//! bound = "O(M^2 + D + N^2 x s + sum k)"
//! ```
//!
//! ```toml algorithm
//! id = "definition.provenance.source_identity"
//! name = "interning and offset mapping of logical source identities"
//! sites = ["LogicalSourceId::new", "SourceTable::intern_extraction", "SourceOffsetMap::new"]
//! variable = "B = source bytes; S = offset-map segments; F = sources already in the table"
//! counters = []
//! no_counter = "logical source interning and offset mapping have no dedicated counter"
//!
//! [[cost]]
//! mode = "one source"
//! bound = "O(B + S)"
//!
//! [[cost]]
//! mode = "SourceTable::intern_extraction"
//! bound = "O(F) LogicalSourceId and offset-map comparisons"
//! ```
//!
//! Provenance records before/after sentence counterparts and recursively annotates changed terms with first-encounter-ordered origin unions.
//! Complexity: the ordered equality walk is linear in sentence size; fallback buckets are linear with distinct keys and O(N^2 x s) in the worst case when equal-key sentences differ; origin unions O(k) expected per visited node.
//! Annotation is linear in visited nodes and link insertions; `ProvenanceLinkDedupProbes` measures those insertions.
//! The former linear `push_unique` union was the largest KEVM self frame at the audit base. Source identities hash each source once, intern it by a linear scan of the table, and validate offset-map segments in one pass.
//!
//! Stable source identities and provenance shared by the semantic frontend.
//!
//! Two compiler-only records ride on every sentence's attributes, both excluded from sentence
//! equality, `UNIQUE_ID` digests, KORE, and KAST v4, and both written to KRUST-PROVENANCE.
//!
//! The input-address carrier ([`INPUT_ADDRESSES_ATTRIBUTE`]) is the ordered, duplicate-free list of
//! [`InputAddress`]es a sentence derives from: a module name and a local sentence index in the
//! definition the caller handed to k-rust, tagged with that definition's [`InputSpace`].
//! `outer::load_structured` stamps each sentence of its `definition` argument with its
//! [`InputSpace::Structured`] address before configurations are expanded;
//! `kompile::compile_loaded_definition` stamps every other sentence of
//! `LoadedDefinition::definition` with its [`InputSpace::Compile`] address, replacing any
//! carrier it did not stamp itself. Structured addresses are kept only while the loaded
//! resolution is the one `load_structured` returned. An address therefore always names, in its
//! space, the sentence it was stamped on for this compilation: a carrier restored from
//! KRUST-PROVENANCE or copied into a rearranged definition is restamped, never trusted.
//! Passes derive sentences by copying attributes, which copies the carrier; a pass that builds a
//! sentence with fresh attributes from input sentences adds their carriers, and a pass that merges
//! equal sentences unites their carriers in first-occurrence order.
//! A sentence with an empty carrier is generated without an input author (a sort predicate, a
//! projection), never attributed to a guessed one.
//! `kompile::CompiledKoreArtifacts::sentence_provenance` groups the emitted rules and claims by
//! their backend `UNIQUE_ID`. It unions carriers across equal-content sentences in emission
//! order, retains the original kinds of addressed input sentences, and
//! reports the generating pass when an identity has no input address.
//!
//! The origin receipt ([`OriginRecord`]) records the generating pass and the source spans or
//! `UNIQUE_ID`s a changed sentence derives from. After each generating pass a sentence is paired
//! with its counterpart before the pass by equality, then by a carrier value, `UNIQUE_ID`, or label
//! that names exactly one sentence on each side, and never by position. An unpaired sentence is
//! generated from its own stored receipt, else from the receipts of the sentences before the pass
//! that share an input address with it, else from its source spans, else from the module-wide
//! origin set.

use std::{
    collections::{BTreeMap, HashMap},
    ops::Range,
    path::{Path, PathBuf},
    sync::{Arc, OnceLock},
};

use indexmap::IndexSet;
use k_rust_kore::measure::{self, Counter};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

use crate::{
    definition::{AttributeKey, Definition, Sentence},
    kast::{InternalLabel, Term, TermMetadata, TermSpan},
};

pub const ORIGIN_ATTRIBUTE: &str = AttributeKey::Origin.as_str();
pub const INPUT_ADDRESSES_ATTRIBUTE: &str = AttributeKey::InputAddresses.as_str();

/// Generated leaf categories whose derivation is represented by their nearest parent receipt.
pub const DECLARED_ORIGIN_FREE_NODE_KINDS: [&str; 3] =
    ["primitive-token", "structural-dot", "truth-value"];

/// Relocation-stable identity for one logical source and exact contents.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct LogicalSourceId {
    pub logical: String,
    pub content_hash: [u8; 32],
}

impl LogicalSourceId {
    pub fn new(logical: impl Into<String>, contents: &[u8]) -> Self {
        Self {
            logical: logical.into(),
            content_hash: Sha256::digest(contents).into(),
        }
    }

    /// Resolve a project-relative logical name inside one concrete checkout.
    pub fn resolve_under(&self, project_root: impl AsRef<Path>) -> PathBuf {
        project_root.as_ref().join(&self.logical)
    }
}

/// Definition-local index into a [`SourceTable`].
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SourceId(pub usize);

/// One contiguous run of semantic-source bytes retained from a raw source.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SourceOffsetSegment {
    pub semantic_start: usize,
    pub raw_start: usize,
    pub length: usize,
}

/// Relates byte ranges in parsed semantic text to their raw source ranges.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceOffsetMap {
    semantic_length: usize,
    raw_length: usize,
    segments: Vec<SourceOffsetSegment>,
}

impl SourceOffsetMap {
    pub fn identity(length: usize) -> Self {
        let segments = (length != 0)
            .then_some(SourceOffsetSegment {
                semantic_start: 0,
                raw_start: 0,
                length,
            })
            .into_iter()
            .collect();
        Self {
            semantic_length: length,
            raw_length: length,
            segments,
        }
    }

    pub fn new(
        semantic_length: usize,
        raw_length: usize,
        segments: Vec<SourceOffsetSegment>,
    ) -> Result<Self, String> {
        let mut semantic_end = 0;
        let mut raw_end = 0;
        for segment in &segments {
            if segment.length == 0
                || segment.semantic_start != semantic_end
                || segment.raw_start < raw_end
            {
                return Err("source offset-map segments are not contiguous and ordered".into());
            }
            semantic_end = segment
                .semantic_start
                .checked_add(segment.length)
                .ok_or_else(|| "source offset-map semantic range overflows usize".to_owned())?;
            raw_end = segment
                .raw_start
                .checked_add(segment.length)
                .ok_or_else(|| "source offset-map raw range overflows usize".to_owned())?;
            if raw_end > raw_length {
                return Err("source offset-map segment exceeds the raw source".into());
            }
        }
        if semantic_end != semantic_length {
            return Err("source offset-map segments do not cover the semantic text".into());
        }
        Ok(Self {
            semantic_length,
            raw_length,
            segments,
        })
    }

    pub fn semantic_length(&self) -> usize {
        self.semantic_length
    }

    pub fn raw_length(&self) -> usize {
        self.raw_length
    }

    pub fn segments(&self) -> &[SourceOffsetSegment] {
        &self.segments
    }

    /// Map one semantic byte boundary to the next retained raw byte boundary.
    pub fn raw_offset(&self, semantic_offset: usize) -> Option<usize> {
        if semantic_offset > self.semantic_length {
            return None;
        }
        if semantic_offset == self.semantic_length {
            return self.segments.last().map_or(Some(0), |segment| {
                segment.raw_start.checked_add(segment.length)
            });
        }
        self.segments.iter().find_map(|segment| {
            let end = segment.semantic_start + segment.length;
            (semantic_offset >= segment.semantic_start && semantic_offset < end)
                .then(|| segment.raw_start + semantic_offset - segment.semantic_start)
        })
    }

    /// Map a half-open semantic range to the minimal half-open raw range containing it.
    pub fn raw_range(&self, semantic: Range<usize>) -> Option<Range<usize>> {
        if semantic.start > semantic.end || semantic.end > self.semantic_length {
            return None;
        }
        let raw_start = self.raw_offset(semantic.start)?;
        if semantic.is_empty() {
            return Some(raw_start..raw_start);
        }
        let final_byte = semantic.end.checked_sub(1)?;
        let segment = self.segments.iter().find(|segment| {
            final_byte >= segment.semantic_start
                && final_byte < segment.semantic_start + segment.length
        })?;
        let raw_end = segment.raw_start + semantic.end - segment.semantic_start;
        Some(raw_start..raw_end)
    }
}

/// Interned source extractions referenced by semantic metadata.
///
/// A [`SourceId`] names one extraction of one raw source: the raw source's [`LogicalSourceId`]
/// and the offset map from the extracted semantic text, which spans index, back to the raw bytes.
/// Two Markdown selectors can extract different text from the same raw file, so the same
/// logical source can appear once per distinct offset map.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SourceTable {
    sources: Vec<LogicalSourceId>,
    offset_maps: BTreeMap<SourceId, SourceOffsetMap>,
    // Structured input can be removed by loading, while its stamped address survives on derived
    // sentences. Keep its original kind with the other loading provenance.
    input_sentence_kinds: BTreeMap<InputAddress, InputSentenceKind>,
}

impl SourceTable {
    pub(crate) fn set_input_sentence_kinds(
        &mut self,
        kinds: BTreeMap<InputAddress, InputSentenceKind>,
    ) {
        self.input_sentence_kinds = kinds;
    }

    pub(crate) fn input_sentence_kinds(&self) -> &BTreeMap<InputAddress, InputSentenceKind> {
        &self.input_sentence_kinds
    }

    /// Intern a source whose spans index its raw bytes directly.
    pub fn intern(&mut self, source: LogicalSourceId) -> SourceId {
        self.intern_extraction(source, None)
    }

    /// Intern one extraction of `source`; `offset_map` is `None` when spans index raw bytes.
    pub fn intern_extraction(
        &mut self,
        source: LogicalSourceId,
        offset_map: Option<SourceOffsetMap>,
    ) -> SourceId {
        // Invariant: the entries of `self.sources` paired with their offset maps are pairwise distinct and indexed by `SourceId`; `position` compares the pair against each entry in order, so one call is O(|sources|) and interning F sources is O(F^2).
        if let Some(index) = self
            .sources
            .iter()
            .enumerate()
            .position(|(index, candidate)| {
                candidate == &source
                    && self.offset_maps.get(&SourceId(index)) == offset_map.as_ref()
            })
        {
            return SourceId(index);
        }
        let id = SourceId(self.sources.len());
        self.sources.push(source);
        if let Some(offset_map) = offset_map {
            self.offset_maps.insert(id, offset_map);
        }
        id
    }

    /// The ordinal of `id` among the table's extractions of the same logical source, in table
    /// order; `None` when `id` is not interned.
    pub fn extraction_ordinal(&self, id: SourceId) -> Option<usize> {
        let source = self.get(id)?;
        Some(
            self.sources[..id.0]
                .iter()
                .filter(|candidate| *candidate == source)
                .count(),
        )
    }

    /// The `ordinal`-th extraction of `source` in table order.
    pub fn find_extraction(&self, source: &LogicalSourceId, ordinal: usize) -> Option<SourceId> {
        self.sources
            .iter()
            .enumerate()
            .filter(|(_, candidate)| *candidate == source)
            .nth(ordinal)
            .map(|(index, _)| SourceId(index))
    }

    pub fn get(&self, id: SourceId) -> Option<&LogicalSourceId> {
        self.sources.get(id.0)
    }

    pub fn iter(&self) -> impl ExactSizeIterator<Item = &LogicalSourceId> {
        self.sources.iter()
    }

    pub fn is_empty(&self) -> bool {
        self.sources.is_empty()
    }

    pub fn offset_map(&self, source: SourceId) -> Option<&SourceOffsetMap> {
        self.offset_maps.get(&source)
    }

    pub fn raw_range(&self, span: TermSpan) -> Option<Range<usize>> {
        self.get(span.source)?;
        if span.start > span.end {
            return None;
        }
        self.offset_map(span.source).map_or_else(
            || Some(span.start..span.end),
            |map| map.raw_range(span.start..span.end),
        )
    }
}

/// Frontend transformation responsible for a generated semantic node.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum GeneratingPass {
    ConfigurationExpansion,
    ResolveComm,
    ResolveIo,
    ResolveFun,
    ResolveFunctionWithConfig,
    ResolveStrict,
    ResolveAnonymousVariables,
    ResolveContexts,
    ResolveHeatCool,
    SemanticCasts,
    SubsortKItem,
    ConstantFolding,
    GuardOrPatterns,
    ResolveFreshConfigConstants,
    GenerateSortPredicateSyntax,
    GenerateSortProjections,
    MacroExpansion,
    AddImplicitComputationCell,
    ResolveFreshConstants,
    ConcretizeCells,
    GenerateSortPredicateRules,
    AddSortInjections,
    RemoveUnit,
    MinimizeTermConstruction,
    ModuleToKoreMapCeil,
}

impl GeneratingPass {
    pub const ALL: [Self; 25] = [
        Self::ConfigurationExpansion,
        Self::ResolveComm,
        Self::ResolveIo,
        Self::ResolveFun,
        Self::ResolveFunctionWithConfig,
        Self::ResolveStrict,
        Self::ResolveAnonymousVariables,
        Self::ResolveContexts,
        Self::ResolveHeatCool,
        Self::SemanticCasts,
        Self::SubsortKItem,
        Self::ConstantFolding,
        Self::GuardOrPatterns,
        Self::ResolveFreshConfigConstants,
        Self::GenerateSortPredicateSyntax,
        Self::GenerateSortProjections,
        Self::MacroExpansion,
        Self::AddImplicitComputationCell,
        Self::ResolveFreshConstants,
        Self::ConcretizeCells,
        Self::GenerateSortPredicateRules,
        Self::AddSortInjections,
        Self::RemoveUnit,
        Self::MinimizeTermConstruction,
        Self::ModuleToKoreMapCeil,
    ];

    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ConfigurationExpansion => "configuration-expansion",
            Self::ResolveComm => "resolve-comm",
            Self::ResolveIo => "resolve-io",
            Self::ResolveFun => "resolve-fun",
            Self::ResolveFunctionWithConfig => "resolve-function-with-config",
            Self::ResolveStrict => "resolve-strict",
            Self::ResolveAnonymousVariables => "resolve-anonymous-variables",
            Self::ResolveContexts => "resolve-contexts",
            Self::ResolveHeatCool => "resolve-heat-cool",
            Self::SemanticCasts => "semantic-casts",
            Self::SubsortKItem => "subsort-kitem",
            Self::ConstantFolding => "constant-folding",
            Self::GuardOrPatterns => "guard-or-patterns",
            Self::ResolveFreshConfigConstants => "resolve-fresh-config-constants",
            Self::GenerateSortPredicateSyntax => "generate-sort-predicate-syntax",
            Self::GenerateSortProjections => "generate-sort-projections",
            Self::MacroExpansion => "macro-expansion",
            Self::AddImplicitComputationCell => "add-implicit-computation-cell",
            Self::ResolveFreshConstants => "resolve-fresh-constants",
            Self::ConcretizeCells => "concretize-cells",
            Self::GenerateSortPredicateRules => "generate-sort-predicate-rules",
            Self::AddSortInjections => "add-sort-injections",
            Self::RemoveUnit => "remove-unit",
            Self::MinimizeTermConstruction => "minimize-term-construction",
            Self::ModuleToKoreMapCeil => "module-to-kore-map-ceil",
        }
    }

    /// Resolve the stable wire name of a generating pass.
    pub fn from_name(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|pass| pass.as_str() == name)
    }
}

/// Stable input edge for one generated node.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ProvenanceLink {
    Source { span: TermSpan },
    Sentence { unique_id: String },
}

/// The definition whose sentences an [`InputAddress`] indexes.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum InputSpace {
    /// The `Definition` argument of `outer::load_structured`, before loading prepends the
    /// implicit modules and expands configurations.
    Structured,
    /// `LoadedDefinition::definition` as passed to `kompile::compile_loaded_definition`.
    Compile,
}

impl InputSpace {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Structured => "structured",
            Self::Compile => "compile",
        }
    }

    pub fn from_name(name: &str) -> Option<Self> {
        [Self::Structured, Self::Compile]
            .into_iter()
            .find(|space| space.as_str() == name)
    }
}

/// One sentence of a caller's definition: its module and its index in that module's
/// `local_sentences`, in the definition named by `input`.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct InputAddress {
    pub input: InputSpace,
    pub module: String,
    pub index: u32,
}

/// Kind of a sentence in the caller's input definition, before loading or compilation changes it.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum InputSentenceKind {
    SyntaxSort,
    SortSynonym,
    SyntaxLexical,
    Production,
    SyntaxAssociativity,
    SyntaxPriority,
    ContextAlias,
    Context,
    Rule,
    Claim,
    Configuration,
    Bubble,
}

impl InputSentenceKind {
    pub fn of(sentence: &Sentence) -> Self {
        match sentence {
            Sentence::SyntaxSort { .. } => Self::SyntaxSort,
            Sentence::SortSynonym { .. } => Self::SortSynonym,
            Sentence::SyntaxLexical { .. } => Self::SyntaxLexical,
            Sentence::Production { .. } => Self::Production,
            Sentence::SyntaxAssociativity { .. } => Self::SyntaxAssociativity,
            Sentence::SyntaxPriority { .. } => Self::SyntaxPriority,
            Sentence::ContextAlias { .. } => Self::ContextAlias,
            Sentence::Context { .. } => Self::Context,
            Sentence::Rule { .. } => Self::Rule,
            Sentence::Claim { .. } => Self::Claim,
            Sentence::Configuration { .. } => Self::Configuration,
            Sentence::Bubble { .. } => Self::Bubble,
        }
    }

    pub const fn as_str(self) -> &'static str {
        match self {
            Self::SyntaxSort => "syntax-sort",
            Self::SortSynonym => "sort-synonym",
            Self::SyntaxLexical => "syntax-lexical",
            Self::Production => "production",
            Self::SyntaxAssociativity => "syntax-associativity",
            Self::SyntaxPriority => "syntax-priority",
            Self::ContextAlias => "context-alias",
            Self::Context => "context",
            Self::Rule => "rule",
            Self::Claim => "claim",
            Self::Configuration => "configuration",
            Self::Bubble => "bubble",
        }
    }
}

/// Snapshot the kinds at the same boundary that assigns input addresses.
pub(crate) fn input_sentence_kinds(
    definition: &Definition,
    input: InputSpace,
) -> BTreeMap<InputAddress, InputSentenceKind> {
    definition
        .modules
        .iter()
        .flat_map(|module| {
            module
                .local_sentences
                .iter()
                .enumerate()
                .map(move |(index, sentence)| {
                    (
                        InputAddress::new(
                            input,
                            module.name.clone(),
                            u32::try_from(index).expect("sentence index fits in u32"),
                        ),
                        InputSentenceKind::of(sentence),
                    )
                })
        })
        .collect()
}

impl InputAddress {
    pub fn new(input: InputSpace, module: impl Into<String>, index: u32) -> Self {
        Self {
            input,
            module: module.into(),
            index,
        }
    }

    fn to_value(&self) -> Value {
        json!({
            "input": self.input.as_str(),
            "module": self.module,
            "index": self.index,
        })
    }

    fn from_value(value: &Value) -> Option<Self> {
        let object = value.as_object()?;
        if object.len() != 3 {
            return None;
        }
        Some(Self {
            input: InputSpace::from_name(object.get("input")?.as_str()?)?,
            module: object.get("module")?.as_str()?.to_owned(),
            index: u32::try_from(object.get("index")?.as_u64()?).ok()?,
        })
    }
}

/// A sentence's compiler-only carrier: the ordered, duplicate-free input addresses it derives
/// from.
///
/// Like the origin receipt it is held outside the semantic attribute map, shared between the
/// clones the pipeline makes, and rendered to its wire form at most once.
#[derive(Debug)]
pub(crate) struct InputAddresses {
    addresses: Box<[InputAddress]>,
    value: OnceLock<Value>,
}

impl InputAddresses {
    /// `None` for an empty list: a sentence without input addresses carries no carrier.
    pub(crate) fn new(addresses: Vec<InputAddress>) -> Option<Self> {
        (!addresses.is_empty()).then(|| Self {
            addresses: unique_addresses(addresses).into_boxed_slice(),
            value: OnceLock::new(),
        })
    }

    /// Decode the wire form, a non-empty array of distinct `{input, module, index}` objects.
    pub(crate) fn from_value(value: &Value) -> Option<Self> {
        let values = value.as_array()?;
        let addresses = values
            .iter()
            .map(InputAddress::from_value)
            .collect::<Option<Vec<_>>>()?;
        let carrier = Self::new(addresses)?;
        (carrier.addresses.len() == values.len()).then(|| {
            let _ = carrier.value.set(value.clone());
            carrier
        })
    }

    pub(crate) fn addresses(&self) -> &[InputAddress] {
        &self.addresses
    }

    pub(crate) fn value(&self) -> &Value {
        self.value.get_or_init(|| self.render())
    }

    /// The wire form for one read: the cached form when present, otherwise a rendering the
    /// caller drops, so a transient reader does not grow the shared carrier.
    pub(crate) fn transient_value(&self) -> std::borrow::Cow<'_, Value> {
        match self.value.get() {
            Some(value) => std::borrow::Cow::Borrowed(value),
            None => std::borrow::Cow::Owned(self.render()),
        }
    }

    fn render(&self) -> Value {
        Value::Array(self.addresses.iter().map(InputAddress::to_value).collect())
    }

    /// The first-occurrence union of two carriers; `None` when `right` adds nothing to `left`.
    pub(crate) fn union(left: &[InputAddress], right: &[InputAddress]) -> Option<Self> {
        if right.iter().all(|address| left.contains(address)) {
            return None;
        }
        Self::new(left.iter().chain(right).cloned().collect())
    }
}

impl PartialEq for InputAddresses {
    fn eq(&self, other: &Self) -> bool {
        self.addresses == other.addresses
    }
}

impl Eq for InputAddresses {}

fn unique_addresses(addresses: Vec<InputAddress>) -> Vec<InputAddress> {
    if addresses.len() < 2 {
        return addresses;
    }
    addresses
        .into_iter()
        .collect::<IndexSet<_>>()
        .into_iter()
        .collect()
}

/// Give every sentence of `definition` its own address in `input`, replacing whatever it carried.
///
/// With `keep_structured`, a sentence whose carrier names only [`InputSpace::Structured`]
/// addresses keeps it: those were stamped by the `load_structured` call that produced this
/// definition. Every other carrier, including a compile address restored from an earlier
/// compilation, is replaced, so an address always names the sentence it was stamped on in the
/// definition being compiled.
pub(crate) fn stamp_input_addresses(
    definition: &mut Definition,
    input: InputSpace,
    keep_structured: bool,
) {
    for module in &mut definition.modules {
        for (index, sentence) in module.local_sentences.iter_mut().enumerate() {
            let inputs = sentence.attributes().input_addresses();
            if keep_structured
                && !inputs.is_empty()
                && inputs
                    .iter()
                    .all(|address| address.input == InputSpace::Structured)
            {
                continue;
            }
            let address = InputAddress::new(
                input,
                module.name.clone(),
                u32::try_from(index).expect("module sentence count fits u32"),
            );
            if inputs == std::slice::from_ref(&address) {
                continue;
            }
            crate::definition::sentence_mut(sentence)
                .attributes_mut()
                .set_input_addresses(vec![address]);
        }
    }
}

/// Append each addition that no sentence of `target` equals; an addition equal to a retained
/// sentence adds its input addresses to that sentence instead of being dropped with them.
pub(crate) fn extend_unique_sentences(
    target: &mut Vec<Sentence>,
    additions: impl IntoIterator<Item = Sentence>,
) {
    // Invariant: `target` holds its original sentences plus each earlier addition it did not already contain, and every earlier addition's input addresses are carried by its equal in `target`; each iteration consumes one addition, and the linear `position` scan makes the loop O(`additions` * `target`).
    for sentence in additions {
        match target.iter().position(|existing| *existing == sentence) {
            Some(index) => target[index]
                .attributes_mut()
                .union_input_addresses(sentence.attributes()),
            None => target.push(sentence),
        }
    }
}

/// Stable location of a generated value in its destination sentence.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct DestinationAnchor {
    pub module: String,
    pub sentence: String,
    pub sentence_index: u32,
    pub path: Vec<u32>,
}

/// Structured provenance attached to a generated term or sentence.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct OriginRecord {
    pub pass: GeneratingPass,
    /// Immutable derivation links shared by generated descendants with the same origin set.
    pub origins: Arc<[ProvenanceLink]>,
    pub destination: Option<DestinationAnchor>,
}

impl OriginRecord {
    pub fn to_value(&self) -> Value {
        json!({
            "pass": self.pass.as_str(),
            "origins": self.origins.iter().map(link_value).collect::<Vec<_>>(),
            "destination": self.destination.as_ref().map(|destination| json!({
                "module": destination.module,
                "sentence": destination.sentence,
                "sentenceIndex": destination.sentence_index,
                "path": destination.path,
            })),
        })
    }
}

fn link_value(link: &ProvenanceLink) -> Value {
    match link {
        ProvenanceLink::Source { span } => json!({
            "kind": "source",
            "source": span.source.0,
            "start": span.start,
            "end": span.end,
        }),
        ProvenanceLink::Sentence { unique_id } => json!({
            "kind": "sentence",
            "uniqueId": unique_id,
        }),
    }
}

/// A sentence's compiler-only origin receipt.
///
/// Kompile passes store the structured record, so every generated sentence of one module shares
/// one origin set instead of materializing its own JSON copy; definitions loaded from JSON keep
/// the raw receipt value. Either form derives the other lazily, once, for the lifetime of the
/// shared receipt.
#[derive(Debug)]
pub struct OriginReceipt {
    record: Option<OriginRecord>,
    value: OnceLock<Value>,
    text: OnceLock<Box<str>>,
}

impl OriginReceipt {
    pub fn from_record(record: OriginRecord) -> Self {
        Self {
            record: Some(record),
            value: OnceLock::new(),
            text: OnceLock::new(),
        }
    }

    pub fn from_value(value: Value) -> Self {
        Self {
            record: None,
            value: OnceLock::from(value),
            text: OnceLock::new(),
        }
    }

    pub fn record(&self) -> Option<&OriginRecord> {
        self.record.as_ref()
    }

    /// Compare receipts without rendering a structured receipt into JSON.
    pub(crate) fn identical(&self, other: &Self) -> bool {
        // Cross-representation comparison necessarily materializes one side, but this is a
        // structural comparison rather than a wire emission; keep it out of the render counter.
        measure::without_counting(|| match (&self.record, &other.record) {
            (Some(left), Some(right)) => left == right,
            (None, None) => self.value == other.value,
            (Some(record), None) => record.to_value() == *other.value(),
            (None, Some(record)) => *self.value() == record.to_value(),
        })
    }

    /// The JSON form of the receipt, rendered at most once per shared receipt.
    pub fn value(&self) -> &Value {
        self.value.get_or_init(|| {
            measure::bump(Counter::ProvenanceReceiptRenders);
            self.expect_record().to_value()
        })
    }

    /// The JSON form of the receipt for one read: the cached form when some caller already
    /// rendered it, otherwise a fresh rendering that the caller drops.
    ///
    /// A shared receipt lives as long as any sentence that carries it, so caching a rendering
    /// requested by a reader that only looks at it once (production text for diagnostics) would
    /// keep the whole JSON tree resident for the rest of the compile.
    pub fn transient_value(&self) -> std::borrow::Cow<'_, Value> {
        match self.value.get() {
            Some(value) => std::borrow::Cow::Borrowed(value),
            None => {
                measure::bump(Counter::ProvenanceReceiptRenders);
                std::borrow::Cow::Owned(self.expect_record().to_value())
            }
        }
    }

    /// The compact JSON text of [`Self::value`], rendered at most once per shared receipt.
    ///
    /// Readers that only print the receipt, such as production text, use this rather than the
    /// JSON tree: the text is an order of magnitude smaller than the tree, so caching it keeps
    /// one rendering per receipt without keeping the tree resident for the rest of the compile.
    pub fn text(&self) -> &str {
        self.text.get_or_init(|| match self.value.get() {
            Some(value) => value.to_string().into_boxed_str(),
            None => {
                measure::bump(Counter::ProvenanceReceiptRenders);
                self.expect_record().to_value().to_string().into_boxed_str()
            }
        })
    }

    pub fn into_value(self) -> Value {
        let Self { record, value, .. } = self;
        match value.into_inner() {
            Some(value) => value,
            None => record
                .expect("an origin receipt holds a record or a value")
                .to_value(),
        }
    }

    /// The derivation links the receipt records, in stored order.
    pub fn origin_links(&self) -> Vec<ProvenanceLink> {
        match &self.record {
            Some(record) => record.origins.to_vec(),
            None => origin_links_from_value(self.value()),
        }
    }

    /// The origin set of a structured receipt, shared rather than copied.
    pub(crate) fn shared_origins(&self) -> Option<Arc<[ProvenanceLink]>> {
        self.record
            .as_ref()
            .map(|record| Arc::clone(&record.origins))
    }

    fn expect_record(&self) -> &OriginRecord {
        self.record
            .as_ref()
            .expect("an origin receipt holds a record or a value")
    }
}

impl PartialEq for OriginReceipt {
    fn eq(&self, other: &Self) -> bool {
        match (&self.record, &other.record) {
            (Some(left), Some(right)) => left == right,
            _ => self.value() == other.value(),
        }
    }
}

impl Eq for OriginReceipt {}

/// Attach one pass's receipts without changing semantic term equality or ordering.
pub fn record_generated_origins(
    before: &Definition,
    after: Definition,
    pass: GeneratingPass,
) -> Definition {
    record_generated_origins_inner(before, after, pass, true)
}

fn record_generated_origins_inner(
    before: &Definition,
    mut after: Definition,
    pass: GeneratingPass,
    skip_unchanged: bool,
) -> Definition {
    // Invariant: every module of `after.modules` before `module` has had its generated sentences stamped with `pass` origin records and its terms annotated, unless it was skipped as unchanged under `skip_unchanged`; each iteration handles one module, and its counterpart lookup is a linear `find` over `before.modules`, so the lookups cost O(modules^2) name comparisons.
    for module in &mut after.modules {
        let before_sentences = before
            .modules
            .iter()
            .find(|candidate| candidate.name == module.name)
            .map(|candidate| {
                candidate
                    .local_sentences
                    .iter()
                    .map(|sentence| (**sentence).clone())
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        let after_snapshot = module
            .local_sentences
            .iter()
            .map(|sentence| (**sentence).clone())
            .collect::<Vec<_>>();
        if skip_unchanged && before_sentences == after_snapshot {
            continue;
        }
        // One module-wide origin set per pass, shared by every generated sentence that has no
        // narrower derivation of its own.
        let module_origins: Arc<[ProvenanceLink]> =
            module_origin_links(&before_sentences, pass).into();
        let counterparts = sentence_counterparts(&before_sentences, &after_snapshot);
        let mut carrier_origins = CarrierOrigins::new(&before_sentences);
        for (sentence_offset, sentence) in module.local_sentences.iter_mut().enumerate() {
            let sentence_index =
                u32::try_from(sentence_offset).expect("module sentence count fits u32");
            let before_sentence =
                counterparts[sentence_offset].map(|index| &before_sentences[index]);
            let sentence = crate::definition::sentence_mut(sentence);
            let generated = before_sentence.is_none_or(|candidate| candidate != sentence);
            let sentence_name = sentence_name(sentence, sentence_offset);
            let origins = sentence_origins(
                before_sentence,
                sentence,
                &mut carrier_origins,
                &module_origins,
            );
            if generated {
                let record = OriginRecord {
                    pass,
                    origins: Arc::clone(&origins),
                    destination: Some(DestinationAnchor {
                        module: module.name.clone(),
                        sentence: sentence_name.clone(),
                        sentence_index,
                        path: Vec::new(),
                    }),
                };
                sentence.attributes_mut().set_origin_record(record);
            }
            annotate_sentence_terms(
                sentence,
                before_sentence,
                pass,
                &origins,
                &module.name,
                &sentence_name,
                sentence_index,
            );
        }
    }
    after
}

/// The origin set of one sentence after a pass: its counterpart's derivation when there is one,
/// else its own stored receipt, else the origins of the sentences before the pass that its
/// input-address carrier names, else its source spans, else the module-wide set. Stored sets are
/// shared, not copied, so a receipt carried through many passes stays one allocation.
fn sentence_origins(
    before: Option<&Sentence>,
    after: &Sentence,
    carrier_origins: &mut CarrierOrigins<'_>,
    module_origins: &Arc<[ProvenanceLink]>,
) -> Arc<[ProvenanceLink]> {
    if let Some(shared) = before.and_then(stored_sentence_origins) {
        return shared;
    }
    let mut origins = before.map(sentence_origin_links).unwrap_or_default();
    if origins.is_empty() {
        if let Some(shared) = stored_sentence_origins(after) {
            return shared;
        }
        origins = stored_sentence_origin_links(after);
    }
    if origins.is_empty()
        && let Some(shared) = carrier_origins.origins(after.attributes().input_addresses())
    {
        return shared;
    }
    if origins.is_empty() {
        origins = sentence_source_links(after);
    }
    if origins.is_empty() {
        return Arc::clone(module_origins);
    }
    origins.into()
}

fn sentence_counterparts(before: &[Sentence], after: &[Sentence]) -> Vec<Option<usize>> {
    let mut counterparts = vec![None; after.len()];
    let mut used = vec![false; before.len()];
    let mut before_index = 0;
    let mut after_index = 0;
    let mut first_gap = None;
    // Most passes preserve order. Compare each aligned pair once, stepping over a single
    // insertion or removal when an adjacent sentence restores alignment.
    while before_index < before.len() && after_index < after.len() {
        if before[before_index] == after[after_index] {
            counterparts[after_index] = Some(before_index);
            used[before_index] = true;
            before_index += 1;
            after_index += 1;
        } else {
            first_gap.get_or_insert(after_index);
            if before
                .get(before_index + 1)
                .is_some_and(|candidate| candidate == &after[after_index])
            {
                before_index += 1;
            } else {
                after_index += 1;
            }
        }
    }
    if after_index < after.len() {
        first_gap.get_or_insert(after_index);
    }
    if let Some(first_gap) = first_gap {
        // Release the suffix found by the walk: a skipped earlier duplicate may belong to
        // an earlier after-sentence. Reassigning the suffix in after order preserves the
        // first-occurrence pairing of equal duplicates on both sides.
        for counterpart in &mut counterparts[first_gap..] {
            if let Some(index) = counterpart.take() {
                used[index] = false;
            }
        }
        let mut buckets = HashMap::<SentenceBucketKey, Vec<usize>>::new();
        for (index, sentence) in before.iter().enumerate() {
            if !used[index] {
                buckets
                    .entry(sentence_bucket_key(sentence))
                    .or_default()
                    .push(index);
            }
        }
        for (index, sentence) in after.iter().enumerate().skip(first_gap) {
            if let Some(candidates) = buckets.get_mut(&sentence_bucket_key(sentence))
                && let Some(position) = candidates
                    .iter()
                    .position(|candidate| before[*candidate] == *sentence)
            {
                let before_index = candidates.remove(position);
                counterparts[index] = Some(before_index);
                used[before_index] = true;
            }
        }
    }
    // A carrier names the input sentences a sentence derives from. Two sentences with one carrier
    // value unique on both sides are the same derivation before and after the pass, whatever the
    // pass changed; this is the only key that survives a change before UNIQUE_ID exists.
    let after_by_inputs = sentences_by_inputs(after);
    let before_by_inputs = sentences_by_inputs(before);
    for (after_index, sentence) in after.iter().enumerate() {
        if counterparts[after_index].is_some() {
            continue;
        }
        let inputs = sentence.attributes().input_addresses();
        if inputs.is_empty()
            || after_by_inputs
                .get(inputs)
                .is_none_or(|indices| indices.len() != 1)
        {
            continue;
        }
        if let Some([before_index]) = before_by_inputs.get(inputs).map(Vec::as_slice)
            && !used[*before_index]
        {
            counterparts[after_index] = Some(*before_index);
            used[*before_index] = true;
        }
    }
    // Invariant: counterparts already assigned by a stronger key remain fixed and each `before`
    // index marked in `used` is paired exactly once.
    for key in [AttributeKey::UniqueId, AttributeKey::Label] {
        let after_by_value = sentences_by_attribute(after, key);
        let before_by_value = sentences_by_attribute(before, key);
        for (after_index, sentence) in after.iter().enumerate() {
            if counterparts[after_index].is_some() {
                continue;
            }
            let Some(value) = sentence.attributes().string(key) else {
                continue;
            };
            if after_by_value
                .get(value)
                .is_none_or(|indices| indices.len() != 1)
            {
                continue;
            }
            if let Some([before_index]) = before_by_value.get(value).map(Vec::as_slice)
                && !used[*before_index]
            {
                counterparts[after_index] = Some(*before_index);
                used[*before_index] = true;
            }
        }
    }
    // No rule pairs by position: a pass that removes or inserts a sentence shifts positions, and a
    // positional pair would name a neighbour that did not contribute. An unpaired sentence is
    // recorded as generated from the origins its own carrier names.
    counterparts
}

fn sentences_by_inputs(sentences: &[Sentence]) -> HashMap<&[InputAddress], Vec<usize>> {
    let mut by_inputs = HashMap::<&[InputAddress], Vec<usize>>::new();
    for (index, sentence) in sentences.iter().enumerate() {
        let inputs = sentence.attributes().input_addresses();
        if !inputs.is_empty() {
            by_inputs.entry(inputs).or_default().push(index);
        }
    }
    by_inputs
}

/// The origins of the sentences before a pass that share an input address with a sentence after
/// it, computed once per carrier value and shared by every sentence that carries it.
struct CarrierOrigins<'a> {
    before: &'a [Sentence],
    by_address: Option<HashMap<&'a InputAddress, Vec<usize>>>,
    by_carrier: HashMap<Vec<InputAddress>, Option<Arc<[ProvenanceLink]>>>,
}

impl<'a> CarrierOrigins<'a> {
    fn new(before: &'a [Sentence]) -> Self {
        Self {
            before,
            by_address: None,
            by_carrier: HashMap::new(),
        }
    }

    fn origins(&mut self, inputs: &[InputAddress]) -> Option<Arc<[ProvenanceLink]>> {
        if inputs.is_empty() {
            return None;
        }
        if let Some(origins) = self.by_carrier.get(inputs) {
            return origins.clone();
        }
        let before = self.before;
        let by_address = self.by_address.get_or_insert_with(|| {
            let mut by_address = HashMap::<&InputAddress, Vec<usize>>::new();
            for (index, sentence) in before.iter().enumerate() {
                for address in sentence.attributes().input_addresses() {
                    by_address.entry(address).or_default().push(index);
                }
            }
            by_address
        });
        let mut indices = inputs
            .iter()
            .filter_map(|address| by_address.get(address))
            .flatten()
            .copied()
            .collect::<Vec<_>>();
        indices.sort_unstable();
        indices.dedup();
        let origins = match indices.as_slice() {
            [] => None,
            [index] => {
                let sentence = &before[*index];
                stored_sentence_origins(sentence).or_else(|| {
                    let links = sentence_origin_links(sentence);
                    (!links.is_empty()).then(|| links.into())
                })
            }
            indices => {
                let mut links = IndexSet::new();
                let mut shared = Vec::<Arc<[ProvenanceLink]>>::new();
                for index in indices {
                    let sentence = &before[*index];
                    if let Some(stored) = stored_sentence_origins(sentence) {
                        if shared.iter().any(|seen| Arc::ptr_eq(seen, &stored)) {
                            continue;
                        }
                        for link in stored.iter() {
                            insert_link(&mut links, link.clone());
                        }
                        shared.push(stored);
                    } else {
                        for link in sentence_origin_links(sentence) {
                            insert_link(&mut links, link);
                        }
                    }
                }
                (!links.is_empty()).then(|| links.into_iter().collect::<Vec<_>>().into())
            }
        };
        self.by_carrier.insert(inputs.to_vec(), origins.clone());
        origins
    }
}

#[derive(Eq, Hash, PartialEq)]
struct SentenceBucketKey {
    kind: &'static str,
    unique_id: Option<String>,
    label: Option<String>,
    discriminator: Option<String>,
}

fn sentence_bucket_key(sentence: &Sentence) -> SentenceBucketKey {
    // Equality implies an equal key; collisions are resolved by Sentence equality in the bucket.
    let discriminator = match sentence {
        Sentence::ContextAlias { body, .. }
        | Sentence::Context { body, .. }
        | Sentence::Rule { body, .. }
        | Sentence::Claim { body, .. }
        | Sentence::Configuration { body, .. } => Some(body.to_string()),
        Sentence::Production { sort, label, .. } => Some(format!("{sort:?}:{label:?}")),
        Sentence::SyntaxSort { sort, .. } => Some(format!("{sort:?}")),
        Sentence::SortSynonym { new_sort, .. } => Some(format!("{new_sort:?}")),
        Sentence::SyntaxLexical { name, .. } => Some(name.clone()),
        Sentence::Bubble { sentence_type, .. } => Some(sentence_type.clone()),
        Sentence::SyntaxAssociativity { .. } | Sentence::SyntaxPriority { .. } => None,
    };
    SentenceBucketKey {
        kind: sentence_kind(sentence),
        unique_id: sentence
            .attributes()
            .string(AttributeKey::UniqueId)
            .map(str::to_owned),
        label: sentence
            .attributes()
            .string(AttributeKey::Label)
            .map(str::to_owned),
        discriminator,
    }
}

fn sentences_by_attribute(sentences: &[Sentence], key: AttributeKey) -> BTreeMap<&str, Vec<usize>> {
    let mut by_value = BTreeMap::new();
    for (index, sentence) in sentences.iter().enumerate() {
        if let Some(value) = sentence.attributes().string(key) {
            by_value.entry(value).or_insert_with(Vec::new).push(index);
        }
    }
    by_value
}

fn sentence_name(sentence: &Sentence, index: usize) -> String {
    sentence
        .attributes()
        .string(AttributeKey::UniqueId)
        .or_else(|| sentence.attributes().string(AttributeKey::Label))
        .map(str::to_owned)
        .unwrap_or_else(|| format!("{}:{index}", sentence_kind(sentence)))
}

fn sentence_kind(sentence: &Sentence) -> &'static str {
    InputSentenceKind::of(sentence).as_str()
}

pub(crate) fn sentence_source_links(sentence: &Sentence) -> Vec<ProvenanceLink> {
    let mut links = IndexSet::new();
    for_each_term(sentence, &mut |term| collect_source_links(term, &mut links));
    links.into_iter().collect()
}

pub(crate) fn sentence_origin_links(sentence: &Sentence) -> Vec<ProvenanceLink> {
    let stored = stored_sentence_origin_links(sentence);
    if !stored.is_empty() {
        stored
    } else if let Some(unique_id) = sentence.attributes().string(AttributeKey::UniqueId) {
        vec![ProvenanceLink::Sentence {
            unique_id: unique_id.into(),
        }]
    } else if sentence_is_termless(sentence)
        && let Some(span) = sentence_source_span(sentence)
    {
        vec![ProvenanceLink::Source { span }]
    } else {
        sentence_source_links(sentence)
    }
}

fn sentence_is_termless(sentence: &Sentence) -> bool {
    matches!(
        sentence,
        Sentence::SyntaxSort { .. }
            | Sentence::SortSynonym { .. }
            | Sentence::SyntaxLexical { .. }
            | Sentence::Production { .. }
            | Sentence::SyntaxAssociativity { .. }
            | Sentence::SyntaxPriority { .. }
            | Sentence::Bubble { .. }
    )
}

fn sentence_source_span(sentence: &Sentence) -> Option<TermSpan> {
    let attributes = sentence.attributes();
    let start = attributes
        .value(AttributeKey::SentenceStartOffset)?
        .as_u64()
        .and_then(|value| usize::try_from(value).ok())?;
    let end = attributes
        .value(AttributeKey::SentenceEndOffset)?
        .as_u64()
        .and_then(|value| usize::try_from(value).ok())?;
    (start <= end).then_some(TermSpan {
        source: attributes.source_id()?,
        start,
        end,
    })
}

fn stored_sentence_origin_links(sentence: &Sentence) -> Vec<ProvenanceLink> {
    sentence
        .attributes()
        .origin_receipt()
        .map(OriginReceipt::origin_links)
        .unwrap_or_default()
}

/// The non-empty shared origin set of a structured stored receipt.
fn stored_sentence_origins(sentence: &Sentence) -> Option<Arc<[ProvenanceLink]>> {
    sentence
        .attributes()
        .origin_receipt()
        .and_then(OriginReceipt::shared_origins)
        .filter(|origins| !origins.is_empty())
}

fn origin_links_from_value(record: &Value) -> Vec<ProvenanceLink> {
    record
        .get("origins")
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .filter_map(|link| match link.get("kind").and_then(Value::as_str) {
            Some("source") => Some(ProvenanceLink::Source {
                span: TermSpan {
                    source: SourceId(usize::try_from(link.get("source")?.as_u64()?).ok()?),
                    start: usize::try_from(link.get("start")?.as_u64()?).ok()?,
                    end: usize::try_from(link.get("end")?.as_u64()?).ok()?,
                },
            }),
            Some("sentence") => Some(ProvenanceLink::Sentence {
                unique_id: link.get("uniqueId")?.as_str()?.into(),
            }),
            _ => None,
        })
        .collect()
}

pub(crate) fn seed_generated_sentence_origin(
    sentence: &mut Sentence,
    pass: GeneratingPass,
    origins: Vec<ProvenanceLink>,
) {
    sentence.attributes_mut().set_origin_record(OriginRecord {
        pass,
        origins: origins.into(),
        destination: None,
    });
}

fn module_origin_links(before_sentences: &[Sentence], pass: GeneratingPass) -> Vec<ProvenanceLink> {
    let configuration_sources = unique_links(
        before_sentences
            .iter()
            .filter(|sentence| matches!(sentence, Sentence::Configuration { .. }))
            .flat_map(sentence_origin_links),
    );
    if pass == GeneratingPass::ConfigurationExpansion && !configuration_sources.is_empty() {
        return configuration_sources;
    }
    unique_links(before_sentences.iter().flat_map(sentence_origin_links))
}

fn unique_links(links: impl IntoIterator<Item = ProvenanceLink>) -> Vec<ProvenanceLink> {
    links
        .into_iter()
        .collect::<IndexSet<_>>()
        .into_iter()
        .collect()
}

fn collect_source_links(term: &Term, links: &mut IndexSet<ProvenanceLink>) {
    // Invariant: `links` contains distinct source links for the term prefix already traversed in
    // first-encounter order; recursive calls visit proper subterms.
    if let Some(span) = term.metadata().and_then(|metadata| metadata.span) {
        insert_link(links, ProvenanceLink::Source { span });
    }
    match term {
        Term::Annotated { term, .. } => collect_source_links(term, links),
        Term::Rewrite { left, right } => {
            collect_source_links(left, links);
            collect_source_links(right, links);
        }
        Term::As { pattern, alias } => {
            collect_source_links(pattern, links);
            collect_source_links(alias, links);
        }
        Term::Sequence(items)
        | Term::Apply {
            arguments: items, ..
        } => {
            for item in items {
                collect_source_links(item, links);
            }
        }
        Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => {}
    }
}

fn insert_link(links: &mut IndexSet<ProvenanceLink>, link: ProvenanceLink) {
    measure::bump(Counter::ProvenanceLinkDedupProbes);
    links.insert(link);
}

fn for_each_term(sentence: &Sentence, visitor: &mut impl FnMut(&Term)) {
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
        } => {
            visitor(body);
            visitor(requires);
            visitor(ensures);
        }
        Sentence::Context { body, requires, .. }
        | Sentence::ContextAlias { body, requires, .. } => {
            visitor(body);
            visitor(requires);
        }
        Sentence::Configuration { body, ensures, .. } => {
            visitor(body);
            visitor(ensures);
        }
        _ => {}
    }
}

#[derive(Clone, Copy)]
struct AnnotationContext<'a> {
    pass: GeneratingPass,
    module: &'a str,
    sentence: &'a str,
    sentence_index: u32,
}

fn annotate_sentence_terms(
    sentence: &mut Sentence,
    before: Option<&Sentence>,
    pass: GeneratingPass,
    origins: &Arc<[ProvenanceLink]>,
    module: &str,
    sentence_name: &str,
    sentence_index: u32,
) {
    let context = AnnotationContext {
        pass,
        module,
        sentence: sentence_name,
        sentence_index,
    };
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
        } => {
            annotate_term(body, sentence_term(before, 0), context, origins, vec![0]);
            annotate_term(
                requires,
                sentence_term(before, 1),
                context,
                origins,
                vec![1],
            );
            annotate_term(ensures, sentence_term(before, 2), context, origins, vec![2]);
        }
        Sentence::Context { body, requires, .. }
        | Sentence::ContextAlias { body, requires, .. } => {
            annotate_term(body, sentence_term(before, 0), context, origins, vec![0]);
            annotate_term(
                requires,
                sentence_term(before, 1),
                context,
                origins,
                vec![1],
            );
        }
        Sentence::Configuration { body, ensures, .. } => {
            annotate_term(body, sentence_term(before, 0), context, origins, vec![0]);
            annotate_term(ensures, sentence_term(before, 1), context, origins, vec![1]);
        }
        _ => {}
    }
}

fn sentence_term(sentence: Option<&Sentence>, field: u32) -> Option<&Term> {
    match (sentence?, field) {
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

fn annotate_term(
    term: &mut Term,
    before: Option<&Term>,
    context: AnnotationContext<'_>,
    inherited_origins: &Arc<[ProvenanceLink]>,
    path: Vec<u32>,
) {
    if before.is_some_and(|candidate| term == candidate) {
        return;
    }
    let own_origins = term_origin_links(before, term, inherited_origins);
    if !declared_origin_free(term) {
        let taken = std::mem::replace(term, Term::Sequence(Vec::new()));
        *term = taken.with_metadata(TermMetadata {
            origin: Some(Arc::new(OriginRecord {
                pass: context.pass,
                origins: Arc::clone(&own_origins),
                destination: Some(DestinationAnchor {
                    module: context.module.into(),
                    sentence: context.sentence.into(),
                    sentence_index: context.sentence_index,
                    path: path.clone(),
                }),
            })),
            ..TermMetadata::default()
        });
    }

    if let Some(before) = before
        && let Some(child) = only_child_mut(term)
        && child == before
    {
        annotate_child(child, Some(before), 0, context, &own_origins, &path);
        return;
    }

    let before = before.map(Term::unannotated);
    match (unannotated_mut(term), before) {
        (
            Term::Rewrite { left, right },
            Some(Term::Rewrite {
                left: before_left,
                right: before_right,
            }),
        ) => {
            annotate_child(left, Some(before_left), 0, context, &own_origins, &path);
            annotate_child(right, Some(before_right), 1, context, &own_origins, &path);
        }
        (
            Term::As { pattern, alias },
            Some(Term::As {
                pattern: before_pattern,
                alias: before_alias,
            }),
        ) => {
            annotate_child(
                pattern,
                Some(before_pattern),
                0,
                context,
                &own_origins,
                &path,
            );
            annotate_child(alias, Some(before_alias), 1, context, &own_origins, &path);
        }
        (Term::Sequence(items), Some(Term::Sequence(before_items)))
        | (
            Term::Apply {
                arguments: items, ..
            },
            Some(Term::Apply {
                arguments: before_items,
                ..
            }),
        ) => {
            for (index, item) in items.iter_mut().enumerate() {
                annotate_child(
                    item,
                    before_items.get(index),
                    u32::try_from(index).expect("term arity fits u32"),
                    context,
                    &own_origins,
                    &path,
                );
            }
        }
        (Term::Rewrite { left, right }, _) => {
            annotate_child(left, None, 0, context, &own_origins, &path);
            annotate_child(right, None, 1, context, &own_origins, &path);
        }
        (Term::As { pattern, alias }, _) => {
            annotate_child(pattern, None, 0, context, &own_origins, &path);
            annotate_child(alias, None, 1, context, &own_origins, &path);
        }
        (
            Term::Sequence(items)
            | Term::Apply {
                arguments: items, ..
            },
            _,
        ) => {
            for (index, item) in items.iter_mut().enumerate() {
                annotate_child(
                    item,
                    None,
                    u32::try_from(index).expect("term arity fits u32"),
                    context,
                    &own_origins,
                    &path,
                );
            }
        }
        (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }, _) => {}
        (Term::Annotated { .. }, _) => unreachable!(),
    }
}

fn term_origin_links(
    before: Option<&Term>,
    after: &Term,
    inherited: &Arc<[ProvenanceLink]>,
) -> Arc<[ProvenanceLink]> {
    let before_metadata = before.and_then(Term::metadata);
    let after_metadata = after.metadata();
    let mut links = IndexSet::new();
    // Invariant: `links` contains the distinct prior and current origin links already scanned in
    // first-encounter order.
    for link in before_metadata
        .and_then(|metadata| metadata.origin.as_deref())
        .into_iter()
        .flat_map(|origin| origin.origins.iter())
        .chain(
            after_metadata
                .and_then(|metadata| metadata.origin.as_deref())
                .into_iter()
                .flat_map(|origin| origin.origins.iter()),
        )
        .cloned()
    {
        insert_link(&mut links, link);
    }
    // Invariant: source spans are appended once after inherited origin records.
    for span in [
        before_metadata.and_then(|metadata| metadata.span),
        after_metadata.and_then(|metadata| metadata.span),
    ]
    .into_iter()
    .flatten()
    {
        insert_link(&mut links, ProvenanceLink::Source { span });
    }
    if links.is_empty() {
        return Arc::clone(inherited);
    }
    // Invariant: inherited links not already present are appended in inherited order.
    for link in inherited.iter() {
        insert_link(&mut links, link.clone());
    }
    if links.iter().eq(inherited.iter()) {
        Arc::clone(inherited)
    } else {
        links.into_iter().collect::<Vec<_>>().into()
    }
}

fn only_child_mut(term: &mut Term) -> Option<&mut Term> {
    match unannotated_mut(term) {
        Term::Sequence(items)
        | Term::Apply {
            arguments: items, ..
        } if items.len() == 1 => items.first_mut(),
        _ => None,
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

fn annotate_child(
    term: &mut Term,
    before: Option<&Term>,
    child: u32,
    context: AnnotationContext<'_>,
    origins: &Arc<[ProvenanceLink]>,
    parent_path: &[u32],
) {
    let mut path = parent_path.to_vec();
    path.push(child);
    annotate_term(term, before, context, origins, path);
}

/// Primitive tokens and structural dots are deliberately origin-free.
pub fn declared_origin_free(term: &Term) -> bool {
    match term.unannotated() {
        Term::Token { .. } => true,
        Term::Apply { label, arguments }
            if arguments.is_empty()
                && [InternalLabel::Dots, InternalLabel::NoDots]
                    .iter()
                    .any(|internal| label.is(*internal)) =>
        {
            true
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;

    use super::*;
    use crate::{
        definition::{Attributes, FlatImport, FlatModule, json as definition_json},
        kast::{Sort, TermMetadata},
    };

    fn rule(body: Term) -> Sentence {
        let truth = Term::Token {
            token: "true".into(),
            sort: Sort::new("Bool"),
        };
        Sentence::Rule {
            body,
            requires: truth.clone(),
            ensures: truth,
            attributes: Attributes::new([("label".into(), "MAIN.rule".into())].into()),
        }
    }

    fn definition(body: Term) -> Definition {
        Definition {
            main_module: "MAIN".into(),
            modules: vec![FlatModule {
                name: "MAIN".into(),
                imports: Vec::new(),
                local_sentences: vec![Arc::new(rule(body))],
                attributes: Attributes::default(),
            }],
            attributes: Attributes::default(),
        }
    }

    fn definition_with_rules(rules: Vec<Sentence>) -> Definition {
        Definition {
            main_module: "MAIN".into(),
            modules: vec![FlatModule {
                name: "MAIN".into(),
                imports: Vec::new(),
                local_sentences: rules.into_iter().map(Arc::new).collect(),
                attributes: Attributes::default(),
            }],
            attributes: Attributes::default(),
        }
    }

    fn counterpart_sentence(
        (unique_id, label, inputs, is_claim): (Option<u8>, Option<u8>, Option<u8>, bool),
    ) -> Sentence {
        let mut attributes = Attributes::from_pairs(
            unique_id
                .map(|value| {
                    (
                        AttributeKey::UniqueId,
                        Value::String(format!("id{}", value % 4)),
                    )
                })
                .into_iter()
                .chain(label.map(|value| {
                    (
                        AttributeKey::Label,
                        Value::String(format!("label{}", value % 4)),
                    )
                })),
        );
        if let Some(value) = inputs {
            attributes.set_input_addresses(vec![InputAddress::new(
                InputSpace::Compile,
                "MAIN",
                u32::from(value % 4),
            )]);
        }
        let body = Term::apply("body", Vec::new());
        let truth = Term::Token {
            token: "true".into(),
            sort: Sort::new("Bool"),
        };
        if is_claim {
            Sentence::Claim {
                body,
                requires: truth.clone(),
                ensures: truth,
                attributes,
            }
        } else {
            Sentence::Rule {
                body,
                requires: truth.clone(),
                ensures: truth,
                attributes,
            }
        }
    }

    type SentenceKey = dyn Fn(&Sentence) -> Option<String>;

    fn linear_sentence_counterparts(before: &[Sentence], after: &[Sentence]) -> Vec<Option<usize>> {
        let mut counterparts = vec![None; after.len()];
        let mut used = vec![false; before.len()];
        for (after_index, sentence) in after.iter().enumerate() {
            for (before_index, candidate) in before.iter().enumerate() {
                if !used[before_index] && sentence == candidate {
                    counterparts[after_index] = Some(before_index);
                    used[before_index] = true;
                    break;
                }
            }
        }
        // Specification after equality: a carrier value, then UNIQUE_ID, then label, each only
        // when the value names exactly one sentence on both sides; never position.
        let keys: [&SentenceKey; 3] = [
            &|sentence| {
                let inputs = sentence.attributes().input_addresses();
                (!inputs.is_empty()).then(|| format!("{inputs:?}"))
            },
            &|sentence| {
                sentence
                    .attributes()
                    .string(AttributeKey::UniqueId)
                    .map(str::to_owned)
            },
            &|sentence| {
                sentence
                    .attributes()
                    .string(AttributeKey::Label)
                    .map(str::to_owned)
            },
        ];
        for key in keys {
            for (after_index, sentence) in after.iter().enumerate() {
                if counterparts[after_index].is_some() {
                    continue;
                }
                let Some(value) = key(sentence) else {
                    continue;
                };
                if after
                    .iter()
                    .filter(|candidate| key(candidate).as_ref() == Some(&value))
                    .count()
                    != 1
                {
                    continue;
                }
                let matching_before = before
                    .iter()
                    .enumerate()
                    .filter(|(_, candidate)| key(candidate).as_ref() == Some(&value))
                    .map(|(index, _)| index)
                    .collect::<Vec<_>>();
                if let [before_index] = matching_before.as_slice()
                    && !used[*before_index]
                {
                    counterparts[after_index] = Some(*before_index);
                    used[*before_index] = true;
                }
            }
        }
        counterparts
    }

    #[test]
    fn unchanged_sentences_pair_across_removed_alias_before_generated_sentence() {
        let alias = Sentence::ContextAlias {
            body: Term::variable("HERE"),
            requires: Term::apply("true", Vec::new()),
            attributes: Attributes::default(),
        };
        let first = rule(Term::apply("first", Vec::new()));
        let second = rule(Term::apply("second", Vec::new()));
        let generated = counterpart_sentence((None, None, None, true));
        let before = vec![alias, first.clone(), second.clone()];
        let after = vec![first, second, generated];
        assert_eq!(
            sentence_counterparts(&before, &after),
            [Some(1), Some(2), None]
        );
    }

    #[test]
    fn equal_duplicate_sentences_pair_in_occurrence_order() {
        let repeated = rule(Term::apply("repeated", Vec::new()));
        let other = rule(Term::apply("other", Vec::new()));
        let before = vec![repeated.clone(), other.clone(), repeated.clone()];
        let after = vec![other, repeated.clone(), repeated];
        assert_eq!(
            sentence_counterparts(&before, &after),
            [Some(1), Some(0), Some(2)]
        );
    }

    #[test]
    fn reordered_sentences_pair_before_an_inserted_sentence() {
        let repeated = rule(Term::apply("repeated", Vec::new()));
        let other = rule(Term::apply("other", Vec::new()));
        let inserted = counterpart_sentence((None, None, None, true));
        let before = vec![repeated.clone(), other.clone(), repeated.clone()];
        let after = vec![other, inserted, repeated.clone(), repeated];
        assert_eq!(
            sentence_counterparts(&before, &after),
            [Some(1), None, Some(0), Some(2)]
        );
    }

    fn address(index: u32) -> InputAddress {
        InputAddress::new(InputSpace::Compile, "MAIN", index)
    }

    /// An unlabeled rule whose body `label` spans `start..start + 1`, carrying `inputs`.
    fn addressed_rule(label: &str, start: usize, inputs: &[u32]) -> Sentence {
        let truth = Term::Token {
            token: "true".into(),
            sort: Sort::new("Bool"),
        };
        let mut attributes = Attributes::default();
        attributes.set_input_addresses(inputs.iter().copied().map(address).collect());
        Sentence::Rule {
            body: Term::apply(label, Vec::new()).with_metadata(TermMetadata {
                span: Some(TermSpan {
                    source: SourceId(0),
                    start,
                    end: start + 1,
                }),
                ..TermMetadata::default()
            }),
            requires: truth.clone(),
            ensures: truth,
            attributes,
        }
    }

    fn receipt_links(sentence: &Sentence) -> Vec<ProvenanceLink> {
        sentence
            .attributes()
            .origin_record()
            .expect("changed sentence has a receipt")
            .origins
            .to_vec()
    }

    #[test]
    fn removing_the_first_of_three_changed_unlabeled_sentences_keeps_every_author() {
        let before = [
            addressed_rule("a", 10, &[0]),
            addressed_rule("b", 20, &[1]),
            addressed_rule("c", 30, &[2]),
        ];
        let after = [
            addressed_rule("b2", 21, &[1]),
            addressed_rule("c2", 31, &[2]),
        ];
        assert_eq!(sentence_counterparts(&before, &after), [Some(1), Some(2)]);

        let recorded = record_generated_origins(
            &definition_with_rules(before.to_vec()),
            definition_with_rules(after.to_vec()),
            GeneratingPass::MacroExpansion,
        );
        let sentences = &recorded.main_module().unwrap().local_sentences;
        let span = |start| ProvenanceLink::Source {
            span: TermSpan {
                source: SourceId(0),
                start,
                end: start + 1,
            },
        };
        assert_eq!(receipt_links(&sentences[0]), [span(20)]);
        assert_eq!(receipt_links(&sentences[1]), [span(30)]);
    }

    #[test]
    fn changed_sentences_without_a_key_are_never_paired_by_position() {
        let before = [
            addressed_rule("a", 10, &[]),
            addressed_rule("b", 20, &[]),
            addressed_rule("c", 30, &[]),
        ];
        let after = [addressed_rule("b2", 21, &[]), addressed_rule("c2", 31, &[])];
        assert_eq!(sentence_counterparts(&before, &after), [None, None]);
    }

    #[test]
    fn carrier_shared_by_several_sentences_does_not_pair_but_names_its_origins() {
        let before = [addressed_rule("a", 10, &[0]), addressed_rule("b", 20, &[1])];
        // A pass split the first rule in two; neither half is the rule's unique counterpart.
        let after = [
            addressed_rule("a1", 11, &[0]),
            addressed_rule("a2", 12, &[0]),
            addressed_rule("b", 20, &[1]),
        ];
        assert_eq!(
            sentence_counterparts(&before, &after),
            [None, None, Some(1)]
        );
        let recorded = record_generated_origins(
            &definition_with_rules(before.to_vec()),
            definition_with_rules(after.to_vec()),
            GeneratingPass::GuardOrPatterns,
        );
        let sentences = &recorded.main_module().unwrap().local_sentences;
        let origin = ProvenanceLink::Source {
            span: TermSpan {
                source: SourceId(0),
                start: 10,
                end: 11,
            },
        };
        assert_eq!(receipt_links(&sentences[0]), std::slice::from_ref(&origin));
        assert_eq!(receipt_links(&sentences[1]), [origin]);
        assert!(sentences[2].attributes().origin_record().is_none());
    }

    #[test]
    fn equal_additions_unite_their_input_addresses_in_first_occurrence_order() {
        let mut target = vec![addressed_rule("a", 10, &[2])];
        extend_unique_sentences(
            &mut target,
            [
                addressed_rule("a", 10, &[0, 2]),
                addressed_rule("b", 20, &[1]),
                addressed_rule("b", 20, &[3]),
            ],
        );
        assert_eq!(target.len(), 2);
        assert_eq!(
            target[0].attributes().input_addresses(),
            [address(2), address(0)]
        );
        assert_eq!(
            target[1].attributes().input_addresses(),
            [address(1), address(3)]
        );
    }

    #[test]
    fn input_addresses_are_provenance_only_and_round_trip_their_wire_form() {
        let mut attributes = Attributes::default();
        attributes.set_input_addresses(vec![address(1), address(0)]);
        assert_eq!(attributes, Attributes::default());
        assert!(!attributes.identical(&Attributes::default()));
        let wire = attributes.wire_map();
        assert_eq!(
            wire[INPUT_ADDRESSES_ATTRIBUTE],
            json!([
                {"input": "compile", "module": "MAIN", "index": 1},
                {"input": "compile", "module": "MAIN", "index": 0},
            ])
        );
        let decoded = Attributes::new(wire);
        assert_eq!(decoded.input_addresses(), [address(1), address(0)]);
        assert!(decoded.identical(&attributes));

        let merged = Attributes::merge([&attributes, &{
            let mut other = Attributes::default();
            other.set_input_addresses(vec![address(0), address(2)]);
            other
        }])
        .unwrap();
        assert_eq!(
            merged.input_addresses(),
            [address(1), address(0), address(2)]
        );

        // A malformed carrier names no input and keeps its wire value.
        let malformed =
            Attributes::new([(INPUT_ADDRESSES_ATTRIBUTE.to_owned(), json!([{"index": 0}]))].into());
        assert!(malformed.input_addresses().is_empty());
        assert_eq!(
            malformed.get(INPUT_ADDRESSES_ATTRIBUTE),
            Some(&json!([{"index": 0}]))
        );
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(256))]

        #[test]
        fn provenance_union_preserves_first_encounter_order_and_is_idempotent(
            values in prop::collection::vec(0_u8..16, 0..64),
        ) {
            let links = values
                .into_iter()
                .map(|value| ProvenanceLink::Sentence {
                    unique_id: format!("s{}", value % 8),
                })
                .collect::<Vec<_>>();
            let mut actual = IndexSet::new();
            for link in links.iter().cloned() {
                insert_link(&mut actual, link);
            }
            let mut oracle = Vec::new();
            for link in links.iter().cloned() {
                if !oracle.contains(&link) {
                    oracle.push(link);
                }
            }
            prop_assert!(actual.iter().eq(oracle.iter()));

            for link in links {
                insert_link(&mut actual, link);
            }
            prop_assert!(actual.iter().eq(oracle.iter()));
        }

        #[test]
        fn term_origin_union_matches_the_linear_receipt_oracle(
            before_values in prop::collection::vec(0_u8..16, 0..32),
            after_values in prop::collection::vec(0_u8..16, 0..32),
            inherited_values in prop::collection::vec(0_u8..16, 0..32),
        ) {
            let links = |values: Vec<u8>| {
                values
                    .into_iter()
                    .map(|value| ProvenanceLink::Sentence {
                        unique_id: format!("s{}", value % 8),
                    })
                    .collect::<Vec<_>>()
            };
            let term = |origins: Vec<ProvenanceLink>| {
                Term::apply("node", Vec::new()).with_metadata(TermMetadata {
                    origin: Some(Arc::new(OriginRecord {
                        pass: GeneratingPass::MacroExpansion,
                        origins: origins.into(),
                        destination: None,
                    })),
                    ..TermMetadata::default()
                })
            };
            let before_links = links(before_values);
            let after_links = links(after_values);
            let inherited: Arc<[ProvenanceLink]> = links(inherited_values).into();
            let before = term(before_links.clone());
            let after = term(after_links.clone());

            let mut expected = Vec::new();
            for link in before_links.into_iter().chain(after_links) {
                if !expected.contains(&link) {
                    expected.push(link);
                }
            }
            if expected.is_empty() {
                expected.extend(inherited.iter().cloned());
            } else {
                for link in inherited.iter().cloned() {
                    if !expected.contains(&link) {
                        expected.push(link);
                    }
                }
            }
            let actual = term_origin_links(Some(&before), &after, &inherited);
            prop_assert_eq!(actual.as_ref(), expected.as_slice());
        }

        #[test]
        fn indexed_sentence_counterparts_match_the_linear_oracle(
            before_specs in prop::collection::vec(
                (
                    prop::option::of(any::<u8>()),
                    prop::option::of(any::<u8>()),
                    prop::option::of(any::<u8>()),
                    any::<bool>(),
                ),
                0..24,
            ),
            after_specs in prop::collection::vec(
                (
                    prop::option::of(any::<u8>()),
                    prop::option::of(any::<u8>()),
                    prop::option::of(any::<u8>()),
                    any::<bool>(),
                ),
                0..24,
            ),
        ) {
            let before = before_specs.into_iter().map(counterpart_sentence).collect::<Vec<_>>();
            let after = after_specs.into_iter().map(counterpart_sentence).collect::<Vec<_>>();
            prop_assert_eq!(
                sentence_counterparts(&before, &after),
                linear_sentence_counterparts(&before, &after),
            );
        }
    }

    #[test]
    fn module_origins_preserve_first_encounter_order_and_configuration_scope() {
        let link = |id: &str| ProvenanceLink::Sentence {
            unique_id: id.into(),
        };
        let mut first = rule(Term::apply("first", Vec::new()));
        seed_generated_sentence_origin(
            &mut first,
            GeneratingPass::MacroExpansion,
            vec![link("z"), link("a"), link("z")],
        );
        let mut second = rule(Term::apply("second", Vec::new()));
        seed_generated_sentence_origin(
            &mut second,
            GeneratingPass::MacroExpansion,
            vec![link("a"), link("m")],
        );
        let rules = vec![first, second];
        for pass in [
            GeneratingPass::MacroExpansion,
            GeneratingPass::ConfigurationExpansion,
        ] {
            assert_eq!(
                module_origin_links(&rules, pass),
                vec![link("z"), link("a"), link("m")]
            );
        }
        let mut configuration = Sentence::Configuration {
            body: Term::apply("config", Vec::new()),
            ensures: Term::apply("true", Vec::new()),
            attributes: Attributes::default(),
        };
        seed_generated_sentence_origin(
            &mut configuration,
            GeneratingPass::ConfigurationExpansion,
            vec![link("c"), link("b"), link("c")],
        );
        let mut sentences = rules;
        sentences.push(configuration);
        assert_eq!(
            module_origin_links(&sentences, GeneratingPass::ConfigurationExpansion),
            vec![link("c"), link("b")]
        );
        assert_eq!(
            module_origin_links(&sentences, GeneratingPass::MacroExpansion),
            vec![link("z"), link("a"), link("m"), link("c"), link("b")]
        );
    }

    #[test]
    fn changed_node_with_inherited_span_records_the_generating_pass() {
        let span = TermSpan {
            source: SourceId(0),
            start: 10,
            end: 20,
        };
        let annotated = |label| {
            Term::apply(label, Vec::new()).with_metadata(TermMetadata {
                span: Some(span),
                ..TermMetadata::default()
            })
        };
        let before = definition(annotated("before"));
        let after = record_generated_origins(
            &before,
            definition(annotated("after")),
            GeneratingPass::MacroExpansion,
        );
        let Sentence::Rule { body, .. } = &*after.main_module().unwrap().local_sentences[0] else {
            panic!("expected rule");
        };
        let metadata = body.metadata().unwrap();
        let origin = metadata
            .origin
            .as_deref()
            .expect("changed node has an origin");

        assert_eq!(metadata.span, Some(span));
        assert_eq!(origin.pass, GeneratingPass::MacroExpansion);
        assert_eq!(origin.origins.as_ref(), [ProvenanceLink::Source { span }]);
        assert_eq!(
            origin.destination,
            Some(DestinationAnchor {
                module: "MAIN".into(),
                sentence: "MAIN.rule".into(),
                sentence_index: 0,
                path: vec![0],
            }),
        );
    }

    #[test]
    fn generated_descendants_share_identical_origin_link_storage() {
        let span = TermSpan {
            source: SourceId(0),
            start: 10,
            end: 20,
        };
        let before = definition(
            Term::apply("before", Vec::new()).with_metadata(TermMetadata {
                span: Some(span),
                ..TermMetadata::default()
            }),
        );
        let after = record_generated_origins(
            &before,
            definition(Term::apply(
                "after",
                vec![Term::apply("generated-child", Vec::new())],
            )),
            GeneratingPass::MacroExpansion,
        );
        let Sentence::Rule { body, .. } = &*after.main_module().unwrap().local_sentences[0] else {
            panic!("expected rule");
        };
        let parent = body
            .metadata()
            .and_then(|metadata| metadata.origin.as_deref())
            .expect("generated parent has an origin");
        let Term::Apply { arguments, .. } = body.unannotated() else {
            panic!("expected application");
        };
        let child = arguments[0]
            .metadata()
            .and_then(|metadata| metadata.origin.as_deref())
            .expect("generated child has an origin");

        assert_eq!(parent.origins.as_ref(), [ProvenanceLink::Source { span }]);
        assert_eq!(child.origins, parent.origins);
        assert_eq!(
            child.origins.as_ptr(),
            parent.origins.as_ptr(),
            "identical inherited origin sets must not be cloned into every generated term",
        );
    }

    #[test]
    fn unchanged_bare_node_is_not_claimed_by_a_later_pass() {
        let before = definition(Term::apply("unchanged", vec![Term::variable("X")]));
        let after =
            record_generated_origins(&before, before.clone(), GeneratingPass::AddSortInjections);
        let Sentence::Rule { body, .. } = &*after.main_module().unwrap().local_sentences[0] else {
            panic!("expected rule");
        };

        assert_eq!(body.metadata(), None);
        let Term::Apply { arguments, .. } = body else {
            panic!("expected application");
        };
        assert_eq!(arguments[0].metadata(), None);
    }

    #[test]
    fn unchanged_module_guard_matches_the_full_walk_for_every_generating_pass() {
        let module = |name: &str, imports: &[&str], body: &str| FlatModule {
            name: name.into(),
            imports: imports
                .iter()
                .map(|name| FlatImport {
                    name: (*name).into(),
                    public: true,
                })
                .collect(),
            local_sentences: vec![Arc::new(rule(Term::apply(body, Vec::new())))],
            attributes: Attributes::default(),
        };
        let before = Definition {
            main_module: "IMP".into(),
            modules: vec![
                module("IMP-COMMON", &[], "common"),
                module("IMP-SYNTAX", &["IMP-COMMON"], "syntax"),
                module("IMP", &["IMP-SYNTAX"], "before"),
            ],
            attributes: Attributes::default(),
        };
        let mut after = before.clone();
        let Sentence::Rule { body, .. } =
            crate::definition::sentence_mut(&mut after.modules[2].local_sentences[0])
        else {
            unreachable!()
        };
        *body = Term::apply("after", vec![Term::variable("X")]);
        let sources = SourceTable::default();

        for pass in GeneratingPass::ALL {
            let guarded = record_generated_origins(&before, after.clone(), pass);
            let full = record_generated_origins_inner(&before, after.clone(), pass, false);
            assert_eq!(
                definition_json::to_provenance_string(&guarded, &sources).unwrap(),
                definition_json::to_provenance_string(&full, &sources).unwrap(),
                "unchanged-module guard changed {pass:?} receipts",
            );
        }
    }

    #[test]
    fn changed_node_retains_prior_origin_links_under_the_current_pass() {
        let source = ProvenanceLink::Sentence {
            unique_id: "upstream-rule".into(),
        };
        let prior = Arc::new(OriginRecord {
            pass: GeneratingPass::ConfigurationExpansion,
            origins: vec![source.clone()].into(),
            destination: Some(DestinationAnchor {
                module: "MAIN".into(),
                sentence: "MAIN.rule".into(),
                sentence_index: 0,
                path: vec![0],
            }),
        });
        let with_prior_origin = |label| {
            Term::apply(label, Vec::new()).with_metadata(TermMetadata {
                origin: Some(prior.clone()),
                ..TermMetadata::default()
            })
        };
        let before = definition(with_prior_origin("before"));
        let after = record_generated_origins(
            &before,
            definition(with_prior_origin("after")),
            GeneratingPass::MacroExpansion,
        );
        let Sentence::Rule { body, .. } = &*after.main_module().unwrap().local_sentences[0] else {
            panic!("expected rule");
        };
        let origin = body
            .metadata()
            .and_then(|metadata| metadata.origin.as_deref())
            .expect("changed node has an origin");

        assert_eq!(origin.pass, GeneratingPass::MacroExpansion);
        assert_eq!(origin.origins.as_ref(), [source]);
        assert_eq!(
            origin.destination,
            Some(DestinationAnchor {
                module: "MAIN".into(),
                sentence: "MAIN.rule".into(),
                sentence_index: 0,
                path: vec![0],
            }),
        );
    }

    #[test]
    fn term_links_combine_prior_spans_and_inherited_origins_in_order() {
        let sentence = |unique_id: &str| ProvenanceLink::Sentence {
            unique_id: unique_id.into(),
        };
        let before_span = TermSpan {
            source: SourceId(0),
            start: 10,
            end: 20,
        };
        let after_span = TermSpan {
            source: SourceId(0),
            start: 30,
            end: 40,
        };
        let shared = sentence("shared");
        let origin = |links: Vec<ProvenanceLink>| {
            Arc::new(OriginRecord {
                pass: GeneratingPass::ConfigurationExpansion,
                origins: links.into(),
                destination: None,
            })
        };
        let before = Term::apply("before", Vec::new()).with_metadata(TermMetadata {
            span: Some(before_span),
            origin: Some(origin(vec![sentence("before"), shared.clone()])),
            ..TermMetadata::default()
        });
        let after = Term::apply("after", Vec::new()).with_metadata(TermMetadata {
            span: Some(after_span),
            origin: Some(origin(vec![sentence("after"), shared.clone()])),
            ..TermMetadata::default()
        });

        let inherited = vec![shared, sentence("inherited")].into();
        assert_eq!(
            term_origin_links(Some(&before), &after, &inherited).as_ref(),
            [
                sentence("before"),
                sentence("shared"),
                sentence("after"),
                ProvenanceLink::Source { span: before_span },
                ProvenanceLink::Source { span: after_span },
                sentence("inherited"),
            ],
        );
    }

    #[test]
    fn every_generating_pass_has_a_production_emission_site() {
        let emitter_sources = [
            include_str!("definition/configuration.rs"),
            include_str!("kompile/passes.rs"),
            include_str!("kompile/passes/resolve_io.rs"),
            include_str!("kompile/passes/resolve_fun.rs"),
            include_str!("kompile/passes/resolve_function_with_config.rs"),
            include_str!("kompile/passes/resolve_strict.rs"),
            include_str!("kompile/passes/resolve_anon_vars.rs"),
            include_str!("kompile/passes/resolve_contexts.rs"),
            include_str!("kompile/passes/resolve_heat_cool.rs"),
            include_str!("kompile/passes/resolve_semantic_casts.rs"),
            include_str!("kompile/passes/subsort_kitem.rs"),
            include_str!("kompile/passes/constant_folding.rs"),
            include_str!("kompile/passes/guard_or_patterns.rs"),
            include_str!("kompile/passes/resolve_fresh_config_constants.rs"),
            include_str!("kompile/passes/generate_sort_helpers.rs"),
            include_str!("kompile/passes/expand_macros.rs"),
            include_str!("kompile/passes/add_implicit_computation_cell.rs"),
            include_str!("kompile/passes/resolve_fresh_constants.rs"),
            include_str!("kompile/passes/concretize_cells.rs"),
            include_str!("kompile/passes/finalize.rs"),
            include_str!("kompile/sort_injections.rs"),
            include_str!("kompile/passes/remove_unit.rs"),
            include_str!("kompile/passes/minimize_term_construction.rs"),
            include_str!("kompile/module_to_kore.rs"),
        ]
        .map(|source| source.split("\n#[cfg(test)]").next().unwrap())
        .join("\n");

        for pass in GeneratingPass::ALL {
            let variant = format!("GeneratingPass::{pass:?}");
            assert!(
                emitter_sources.contains(&variant),
                "{pass:?} has no production emission site",
            );
        }
    }

    #[test]
    fn duplicate_sentence_keys_do_not_reuse_a_before_counterpart() {
        for key in ["label", "UNIQUE_ID"] {
            let duplicate_attributes = || {
                let mut attributes = Attributes::default();
                attributes.insert(key, Value::String("duplicate".into()));
                attributes
            };
            let make_rule = |body| {
                let mut sentence = rule(Term::apply(body, Vec::new()));
                *sentence.attributes_mut() = duplicate_attributes();
                sentence
            };
            let before = definition_with_rules(vec![make_rule("before"), make_rule("unchanged")]);
            let after = record_generated_origins(
                &before,
                definition_with_rules(vec![make_rule("after"), make_rule("unchanged")]),
                GeneratingPass::MacroExpansion,
            );
            let [changed, unchanged] = after.main_module().unwrap().local_sentences.as_slice()
            else {
                panic!("expected two rules");
            };
            let Sentence::Rule {
                body: changed_body, ..
            } = changed.as_ref()
            else {
                panic!("expected changed rule");
            };
            let Sentence::Rule {
                body: unchanged_body,
                ..
            } = unchanged.as_ref()
            else {
                panic!("expected unchanged rule");
            };

            assert!(
                changed_body
                    .metadata()
                    .and_then(|metadata| metadata.origin.as_ref())
                    .is_some(),
                "changed node with duplicate {key} has an origin",
            );
            assert_eq!(
                unchanged_body.metadata(),
                None,
                "unchanged node with duplicate {key} is not claimed",
            );
        }
    }

    #[test]
    fn equal_generated_terms_in_duplicate_key_sentences_have_distinct_destinations() {
        for key in ["label", "UNIQUE_ID"] {
            let make_rule = || {
                let mut sentence = rule(Term::apply("generated", Vec::new()));
                sentence
                    .attributes_mut()
                    .insert(key, Value::String("duplicate".into()));
                sentence
            };
            let before = definition_with_rules(Vec::new());
            let after = record_generated_origins(
                &before,
                definition_with_rules(vec![make_rule(), make_rule()]),
                GeneratingPass::ConcretizeCells,
            );
            let destinations = after
                .main_module()
                .unwrap()
                .local_sentences
                .iter()
                .filter_map(|sentence| match &**sentence {
                    Sentence::Rule { body, .. } => body
                        .metadata()
                        .and_then(|metadata| metadata.origin.as_deref())
                        .and_then(|origin| origin.destination.as_ref()),
                    _ => None,
                })
                .collect::<Vec<_>>();

            assert_eq!(destinations.len(), 2);
            assert_ne!(
                destinations[0], destinations[1],
                "duplicate {key} sentences have distinct destination occurrences",
            );
        }
    }

    #[test]
    fn duplicate_labels_across_modules_keep_distinct_source_and_destination_identities() {
        let make_rule = |body: Term| {
            let mut sentence = rule(body);
            sentence
                .attributes_mut()
                .insert("label", Value::String("duplicate".into()));
            sentence
        };
        let span = |source, start| TermSpan {
            source: SourceId(source),
            start,
            end: start + 4,
        };
        let module = |name: &str, body| FlatModule {
            name: name.into(),
            imports: Vec::new(),
            local_sentences: vec![Arc::new(make_rule(body))],
            attributes: Attributes::default(),
        };
        let before = Definition {
            main_module: "FIRST".into(),
            modules: vec![
                module(
                    "FIRST",
                    Term::apply("before", Vec::new()).with_metadata(TermMetadata {
                        span: Some(span(0, 10)),
                        ..TermMetadata::default()
                    }),
                ),
                module(
                    "SECOND",
                    Term::apply("before", Vec::new()).with_metadata(TermMetadata {
                        span: Some(span(1, 30)),
                        ..TermMetadata::default()
                    }),
                ),
            ],
            attributes: Attributes::default(),
        };
        let after = Definition {
            main_module: "FIRST".into(),
            modules: vec![
                module("FIRST", Term::apply("generated", Vec::new())),
                module("SECOND", Term::apply("generated", Vec::new())),
            ],
            attributes: Attributes::default(),
        };
        let after = record_generated_origins(&before, after, GeneratingPass::MacroExpansion);
        let receipts = after
            .modules
            .iter()
            .map(|module| {
                let Sentence::Rule { body, .. } = &*module.local_sentences[0] else {
                    unreachable!()
                };
                assert_eq!(body, &Term::apply("generated", Vec::new()));
                body.metadata()
                    .and_then(|metadata| metadata.origin.as_deref())
                    .expect("generated term has a receipt")
            })
            .collect::<Vec<_>>();

        assert_eq!(
            receipts[0].origins.as_ref(),
            [ProvenanceLink::Source { span: span(0, 10) }]
        );
        assert_eq!(
            receipts[1].origins.as_ref(),
            [ProvenanceLink::Source { span: span(1, 30) }]
        );
        assert_ne!(receipts[0].origins, receipts[1].origins);
        assert_ne!(receipts[0].destination, receipts[1].destination);
        assert_eq!(receipts[0].destination.as_ref().unwrap().module, "FIRST");
        assert_eq!(receipts[1].destination.as_ref().unwrap().module, "SECOND");
        assert_eq!(receipts[0].destination.as_ref().unwrap().path, [0]);
        assert_eq!(receipts[1].destination.as_ref().unwrap().path, [0]);
    }
}
