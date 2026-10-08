use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt;

use krs_ir::{
    ByteRange, CellAttribute, CellContentFrame, CellPost, ConfigurationRoot, DisplayPath,
    FixedCell, FixedCellContent, FixedConfiguration, FixedInitializerCell, FixedInitializerContent,
    LineIndex, ModuleId, NodeOrigin, OriginFrame, OriginStack, SourceMapKey, SourceRange,
    StableItemId,
};
use krs_ir_levels::{
    DefinitionIr, DefinitionSentence, DefinitionSortRef, DefinitionTerm, DefinitionTermKind,
    LabelId, RuleBodyRef, SymbolId, SymbolKind,
};
use serde::{Deserialize, Serialize};

/// Version of the compiler-owned symbol/source sidecar encoding.
const SIDECAR_SCHEMA_VERSION: u32 = 2;

fn deserialize_schema_version<'de, D: serde::Deserializer<'de>>(
    deserializer: D,
) -> Result<u32, D::Error> {
    let version = u32::deserialize(deserializer)?;
    if version != SIDECAR_SCHEMA_VERSION {
        return Err(serde::de::Error::custom(format!(
            "unsupported compiler sidecar schema version {version}; expected {SIDECAR_SCHEMA_VERSION}"
        )));
    }
    Ok(version)
}

/// A typed Definition IR identity mapped to generated source spelling.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(tag = "identity_kind", content = "identity", rename_all = "snake_case")]
pub enum MappedIdentity {
    /// A generated K module.
    Module(ModuleId),
    /// A sort, production, cell, or initializer symbol.
    Symbol(SymbolId),
    /// A rule label.
    Label(LabelId),
    /// A source-level context-alias declaration.
    ContextAlias(StableItemId),
}

impl fmt::Display for MappedIdentity {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Module(id) => write!(formatter, "module {id}"),
            Self::Symbol(id) => write!(formatter, "symbol {id}"),
            Self::Label(id) => write!(formatter, "label {id}"),
            Self::ContextAlias(id) => write!(formatter, "context alias {id}"),
        }
    }
}

/// One deterministic symbol-map row.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SymbolMapEntry {
    identity: MappedIdentity,
    emitted_name: String,
    source_map_key: SourceMapKey,
    #[serde(skip_serializing_if = "Option::is_none")]
    symbol_kind: Option<SymbolKind>,
}

impl SymbolMapEntry {
    /// Returns the Definition IR identity.
    #[must_use]
    pub const fn identity(&self) -> &MappedIdentity {
        &self.identity
    }

    /// Returns the sole emitted spelling chosen by lowering.
    #[must_use]
    pub fn emitted_name(&self) -> &str {
        &self.emitted_name
    }

    /// Returns the source-map key of the declaration.
    #[must_use]
    pub const fn source_map_key(&self) -> &SourceMapKey {
        &self.source_map_key
    }

    /// Returns the symbol role for symbol rows.
    #[must_use]
    pub const fn symbol_kind(&self) -> Option<SymbolKind> {
        self.symbol_kind
    }
}

/// Canonically ordered, target-neutral symbol sidecar.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SymbolMap {
    #[serde(deserialize_with = "deserialize_schema_version")]
    schema_version: u32,
    entries: Vec<SymbolMapEntry>,
    /// Backend capabilities the definition needs (V8), when any.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    capability_requirements: Vec<crate::capability::CapabilityRequirement>,
}

impl SymbolMap {
    pub(crate) fn from_definition(definition: &DefinitionIr) -> Result<Self, SidecarError> {
        let mut entries = Vec::new();
        let mut identities = BTreeSet::new();
        for module in definition.modules() {
            push_symbol(
                &mut entries,
                &mut identities,
                SymbolMapEntry {
                    identity: MappedIdentity::Module(module.id().clone()),
                    emitted_name: module.id().as_str().to_owned(),
                    source_map_key: module.origin().key().clone(),
                    symbol_kind: None,
                },
            )?;
            for sentence in module.sentences() {
                match sentence {
                    DefinitionSentence::SyntaxSort(sentence) => push_symbol(
                        &mut entries,
                        &mut identities,
                        SymbolMapEntry {
                            identity: MappedIdentity::Symbol(sentence.symbol().id().clone()),
                            emitted_name: sentence.symbol().emitted_name().to_owned(),
                            source_map_key: sentence.origin().key().clone(),
                            symbol_kind: Some(SymbolKind::Sort),
                        },
                    )?,
                    DefinitionSentence::Production(sentence) => push_symbol(
                        &mut entries,
                        &mut identities,
                        SymbolMapEntry {
                            identity: MappedIdentity::Symbol(sentence.symbol().id().clone()),
                            emitted_name: sentence.symbol().emitted_name().to_owned(),
                            source_map_key: sentence.origin().key().clone(),
                            symbol_kind: Some(SymbolKind::Production),
                        },
                    )?,
                    DefinitionSentence::Configuration(configuration) => {
                        push_fixed_cell_symbols(
                            configuration.cells(),
                            &mut entries,
                            &mut identities,
                        )?;
                    }
                    DefinitionSentence::Rule(sentence) => push_symbol(
                        &mut entries,
                        &mut identities,
                        SymbolMapEntry {
                            identity: MappedIdentity::Label(sentence.label().id().clone()),
                            emitted_name: sentence.label().emitted_name().to_owned(),
                            source_map_key: sentence.origin().key().clone(),
                            symbol_kind: None,
                        },
                    )?,
                    DefinitionSentence::ContextAlias(sentence) => push_symbol(
                        &mut entries,
                        &mut identities,
                        SymbolMapEntry {
                            identity: MappedIdentity::ContextAlias(sentence.id().clone()),
                            emitted_name: sentence.name().to_owned(),
                            source_map_key: sentence.name_origin().key().clone(),
                            symbol_kind: None,
                        },
                    )?,
                    DefinitionSentence::Subsort(_)
                    | DefinitionSentence::Precedence(_)
                    | DefinitionSentence::Associativity(_)
                    | DefinitionSentence::Lexical(_)
                    | DefinitionSentence::Layout(_)
                    | DefinitionSentence::Raw(_) => {}
                }
            }
        }
        entries.sort();
        let map = Self {
            schema_version: SIDECAR_SCHEMA_VERSION,
            entries,
            capability_requirements: crate::capability::capability_requirements(definition),
        };
        map.reject_path_leaks()?;
        Ok(map)
    }

    /// Returns entries in canonical identity order.
    #[must_use]
    pub fn entries(&self) -> &[SymbolMapEntry] {
        &self.entries
    }

    /// Returns the backend capabilities the definition needs, by feature and sentence name.
    #[must_use]
    pub fn capability_requirements(&self) -> &[crate::capability::CapabilityRequirement] {
        &self.capability_requirements
    }

    /// Serializes stable pretty JSON with one trailing newline.
    ///
    /// # Errors
    ///
    /// Returns a JSON encoding error if the serde data model cannot be encoded.
    pub fn to_canonical_json(&self) -> serde_json::Result<String> {
        canonical_json(self)
    }

    fn reject_path_leaks(&self) -> Result<(), SidecarError> {
        for entry in &self.entries {
            if DisplayPath::is_absolute_spelling(&entry.emitted_name) {
                return Err(SidecarError::AbsolutePath(entry.emitted_name.clone()));
            }
        }
        Ok(())
    }
}

/// Stable structural role of a Definition node in a source-map sidecar.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SourceMapNodeKind {
    /// Definition module.
    Module,
    /// Syntax sort declaration.
    SyntaxSort,
    /// Direct subsort sentence.
    Subsort,
    /// Constructor production.
    Production,
    /// Nested object-grammar item.
    ProductionItem,
    /// Classified production metadata.
    ProductionAttribute,
    /// Compiler-owned production-group identity.
    ProductionGroup,
    /// Production-group precedence relation.
    Precedence,
    /// Production-group associativity relation.
    Associativity,
    /// Configuration sentence.
    Configuration,
    /// Configuration cell declaration.
    Cell,
    /// Configuration initializer declaration.
    Initializer,
    /// Authored named configuration root.
    ConfigurationRoot,
    /// Classified cell metadata value.
    CellAttribute,
    /// External configuration variable declaration.
    ConfigurationVariable,
    /// One node in a structured initializer tree.
    InitializerCell,
    /// One simultaneous configuration rewrite body.
    ConfigurationRewrite,
    /// One mentioned fixed-cell clause.
    CellClause,
    /// One explicit K-sequence or Map frame.
    CellFrame,
    /// Rule sentence.
    Rule,
    /// Reachability-claim sentence.
    Claim,
    /// Claim reachability modality.
    ClaimModality,
    /// Claim circularity marker.
    ClaimCircularity,
    /// Typed universal or existential claim binder component.
    ClaimBinder,
    /// Complete object-language Boolean claim postcondition.
    ClaimEnsures,
    /// One-sided context-alias sentence.
    ContextAlias,
    /// Complete object-language Boolean rule condition.
    RuleCondition,
    /// Explicit equation-priority metadata.
    RulePriority,
    /// Simplification marker metadata.
    Simplification,
    /// Numeric simplification ordering hint.
    SimplificationPriority,
    /// Nested structured term.
    Term,
    /// Named lexical sentence.
    Lexical,
    /// Layout regex sentence.
    Layout,
    /// One `k::raw_k!` sentence, opaque to KRS.
    RawSentence,
}

/// Byte ranges rendered for each Definition node in one generated artifact.
pub(crate) type GeneratedRanges = BTreeMap<SourceMapKey, ByteRange>;

/// Half-open range in one canonical generated `.k` artifact.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GeneratedRange {
    artifact: String,
    start_byte: u64,
    end_byte: u64,
    start_line: u32,
    start_column: u32,
    end_line: u32,
    end_column: u32,
}

impl GeneratedRange {
    pub(crate) fn new(
        artifact: &str,
        source: &str,
        index: &LineIndex,
        range: ByteRange,
    ) -> Result<Self, SidecarError> {
        let start = range.start();
        let end = range.end();
        if end > source.len() || !source.is_char_boundary(start) || !source.is_char_boundary(end) {
            return Err(SidecarError::InvalidGeneratedRange);
        }
        let start_position = index
            .byte_to_position(start)
            .map_err(|_| SidecarError::RangeOverflow)?;
        let end_position = index
            .byte_to_position(end)
            .map_err(|_| SidecarError::RangeOverflow)?;
        Ok(Self {
            artifact: artifact.to_owned(),
            start_byte: u64::try_from(start).map_err(|_| SidecarError::RangeOverflow)?,
            end_byte: u64::try_from(end).map_err(|_| SidecarError::RangeOverflow)?,
            start_line: start_position.line(),
            start_column: start_position.scalar_column(),
            end_line: end_position.line(),
            end_column: end_position.scalar_column(),
        })
    }

    /// Returns the package-relative generated artifact name.
    #[must_use]
    pub fn artifact(&self) -> &str {
        &self.artifact
    }

    /// Returns the inclusive generated UTF-8 byte offset.
    #[must_use]
    pub const fn start_byte(&self) -> u64 {
        self.start_byte
    }

    /// Returns the one-based start line coordinate.
    #[must_use]
    pub const fn start_line(&self) -> u32 {
        self.start_line
    }

    /// Returns the one-based start column coordinate.
    #[must_use]
    pub const fn start_column(&self) -> u32 {
        self.start_column
    }

    /// Returns the one-based end line coordinate.
    #[must_use]
    pub const fn end_line(&self) -> u32 {
        self.end_line
    }

    /// Returns the one-based end column coordinate.
    #[must_use]
    pub const fn end_column(&self) -> u32 {
        self.end_column
    }

    /// Returns the exclusive generated UTF-8 byte offset.
    #[must_use]
    pub const fn end_byte(&self) -> u64 {
        self.end_byte
    }
}

/// One Definition node's honest authored provenance and optional generated range.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SourceMapEntry {
    key: SourceMapKey,
    node_kind: SourceMapNodeKind,
    origin: OriginStack,
    #[serde(skip_serializing_if = "Option::is_none")]
    generated: Option<GeneratedRange>,
}

impl SourceMapEntry {
    /// Returns the stable Definition node key.
    #[must_use]
    pub const fn key(&self) -> &SourceMapKey {
        &self.key
    }

    /// Returns the structural node role.
    #[must_use]
    pub const fn node_kind(&self) -> SourceMapNodeKind {
        self.node_kind
    }

    /// Returns authored-to-Definition provenance.
    #[must_use]
    pub const fn origin(&self) -> &OriginStack {
        &self.origin
    }

    /// Returns the generated source range when this node has a direct rendering.
    #[must_use]
    pub const fn generated(&self) -> Option<&GeneratedRange> {
        self.generated.as_ref()
    }
}

/// Canonically ordered Definition-node source-map sidecar.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SourceMap {
    #[serde(deserialize_with = "deserialize_schema_version")]
    schema_version: u32,
    entries: Vec<SourceMapEntry>,
}

impl SourceMap {
    /// Returns a typed selection preserving schema, entry order, and multiplicity.
    #[must_use]
    pub fn filtered(&self, select: impl Fn(&SourceMapEntry) -> bool) -> Self {
        Self {
            schema_version: self.schema_version,
            entries: self
                .entries
                .iter()
                .filter(|entry| select(entry))
                .cloned()
                .collect(),
        }
    }

    #[expect(
        clippy::too_many_lines,
        reason = "Collects every definition node kind into one source map traversal."
    )]
    pub(crate) fn from_definition(definition: &DefinitionIr) -> Result<Self, SidecarError> {
        let mut entries = BTreeMap::new();
        for module in definition.modules() {
            insert_origin(&mut entries, module.origin(), SourceMapNodeKind::Module)?;
            for group in module.production_groups() {
                insert_origin(
                    &mut entries,
                    group.origin(),
                    SourceMapNodeKind::ProductionGroup,
                )?;
            }
            for sentence in module.sentences() {
                let kind = match sentence {
                    DefinitionSentence::SyntaxSort(_) => SourceMapNodeKind::SyntaxSort,
                    DefinitionSentence::Subsort(_) => SourceMapNodeKind::Subsort,
                    DefinitionSentence::Production(_) => SourceMapNodeKind::Production,
                    DefinitionSentence::Precedence(_) => SourceMapNodeKind::Precedence,
                    DefinitionSentence::Associativity(_) => SourceMapNodeKind::Associativity,
                    DefinitionSentence::Configuration(_) => SourceMapNodeKind::Configuration,
                    DefinitionSentence::ContextAlias(_) => SourceMapNodeKind::ContextAlias,
                    DefinitionSentence::Rule(rule)
                        if rule.kind() == krs_ir::SentenceKind::Claim =>
                    {
                        SourceMapNodeKind::Claim
                    }
                    DefinitionSentence::Rule(_) => SourceMapNodeKind::Rule,
                    DefinitionSentence::Lexical(_) => SourceMapNodeKind::Lexical,
                    DefinitionSentence::Layout(_) => SourceMapNodeKind::Layout,
                    DefinitionSentence::Raw(_) => SourceMapNodeKind::RawSentence,
                };
                insert_origin(&mut entries, sentence.origin(), kind)?;
                match sentence {
                    DefinitionSentence::Production(sentence) => {
                        for item in sentence.items() {
                            insert_origin(
                                &mut entries,
                                item.origin(),
                                SourceMapNodeKind::ProductionItem,
                            )?;
                        }
                        for attribute in sentence.attributes() {
                            insert_origin(
                                &mut entries,
                                attribute.origin(),
                                SourceMapNodeKind::ProductionAttribute,
                            )?;
                            if let krs_ir_levels::DefinitionProductionAttribute::Strictness {
                                using,
                                fields,
                                result_sort,
                                ..
                            } = attribute
                            {
                                if let Some(using) = using {
                                    insert_origin(
                                        &mut entries,
                                        using.origin(),
                                        SourceMapNodeKind::ProductionAttribute,
                                    )?;
                                }
                                for field in fields {
                                    insert_origin(
                                        &mut entries,
                                        field.origin(),
                                        SourceMapNodeKind::ProductionAttribute,
                                    )?;
                                }
                                insert_origin(
                                    &mut entries,
                                    result_sort.origin(),
                                    SourceMapNodeKind::ProductionAttribute,
                                )?;
                            }
                        }
                    }
                    DefinitionSentence::Configuration(configuration) => {
                        insert_fixed_configuration(&mut entries, configuration)?;
                    }
                    DefinitionSentence::Rule(sentence) => {
                        insert_rule_body(&mut entries, sentence.relational_body())?;
                        if let Some(priority) = sentence.priority() {
                            insert_origin(
                                &mut entries,
                                priority.origin(),
                                SourceMapNodeKind::RulePriority,
                            )?;
                        }
                        if let Some(simplification) = sentence.simplification() {
                            insert_origin(
                                &mut entries,
                                simplification.origin(),
                                SourceMapNodeKind::Simplification,
                            )?;
                            if let Some(priority) = simplification.priority() {
                                insert_origin(
                                    &mut entries,
                                    priority.origin(),
                                    SourceMapNodeKind::SimplificationPriority,
                                )?;
                            }
                        }
                        if let Some(condition) = sentence.requires() {
                            insert_origin(
                                &mut entries,
                                condition.origin(),
                                SourceMapNodeKind::RuleCondition,
                            )?;
                            insert_term(&mut entries, condition.term())?;
                        }
                        if let Some(claim) = sentence.claim() {
                            insert_origin(
                                &mut entries,
                                claim.modality_origin(),
                                SourceMapNodeKind::ClaimModality,
                            )?;
                            if let Some(origin) = claim.circularity_origin() {
                                insert_origin(
                                    &mut entries,
                                    origin,
                                    SourceMapNodeKind::ClaimCircularity,
                                )?;
                            }
                            for binder in claim.universals().iter().chain(claim.existentials()) {
                                for origin in
                                    [binder.origin(), binder.name_origin(), binder.sort_origin()]
                                {
                                    insert_origin(
                                        &mut entries,
                                        origin,
                                        SourceMapNodeKind::ClaimBinder,
                                    )?;
                                }
                            }
                            if let Some(ensures) = claim.ensures() {
                                insert_origin(
                                    &mut entries,
                                    ensures.origin(),
                                    SourceMapNodeKind::ClaimEnsures,
                                )?;
                                insert_term(&mut entries, ensures.term())?;
                            }
                        }
                    }
                    DefinitionSentence::ContextAlias(sentence) => {
                        insert_origin(
                            &mut entries,
                            sentence.name_origin(),
                            SourceMapNodeKind::ContextAlias,
                        )?;
                        insert_origin(
                            &mut entries,
                            sentence.here_origin(),
                            SourceMapNodeKind::ContextAlias,
                        )?;
                        for cell in sentence.body().cells() {
                            insert_origin(
                                &mut entries,
                                cell.origin(),
                                SourceMapNodeKind::CellClause,
                            )?;
                            insert_term(&mut entries, cell.pattern())?;
                            if let CellContentFrame::KSequenceTail { origin, .. }
                            | CellContentFrame::MapRemainder { origin, .. }
                            | CellContentFrame::ListRemainder { origin } = cell.frame()
                            {
                                insert_origin(&mut entries, origin, SourceMapNodeKind::CellFrame)?;
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        let map = Self {
            schema_version: SIDECAR_SCHEMA_VERSION,
            entries: entries.into_values().collect(),
        };
        map.reject_path_leaks()?;
        Ok(map)
    }

    /// Returns the sole exact authored range for a Definition source-map key.
    /// Missing keys and multiple authored frames must not be replaced with an inferred range.
    #[must_use]
    pub fn exact_authored_range(&self, key: &SourceMapKey) -> Option<SourceRange> {
        self.entries()
            .iter()
            .find(|entry| entry.key() == key)?
            .origin()
            .exact_authored_range()
    }

    /// Returns entries in canonical source-map-key order.
    #[must_use]
    pub fn entries(&self) -> &[SourceMapEntry] {
        &self.entries
    }

    /// Serializes stable pretty JSON with one trailing newline.
    ///
    /// # Errors
    ///
    /// Returns a JSON encoding error if the serde data model cannot be encoded.
    pub fn to_canonical_json(&self) -> serde_json::Result<String> {
        canonical_json(self)
    }

    /// Attaches each artifact's ranges; `artifacts` holds `(name, source, ranges)`
    /// and a key must be rendered in at most one artifact.
    pub(crate) fn with_generated_ranges(
        mut self,
        artifacts: &[(&str, &str, &GeneratedRanges)],
    ) -> Result<Self, SidecarError> {
        let indexes: Vec<_> = artifacts
            .iter()
            .map(|(_, source, _)| LineIndex::new(source))
            .collect();
        for entry in &mut self.entries {
            for ((artifact, source, ranges), index) in artifacts.iter().zip(&indexes) {
                if let Some(range) = ranges.get(&entry.key) {
                    if entry.generated.is_some() {
                        return Err(SidecarError::DuplicateSourceMapKey(entry.key.clone()));
                    }
                    entry.generated = Some(GeneratedRange::new(artifact, source, index, *range)?);
                }
            }
        }
        self.reject_path_leaks()?;
        Ok(self)
    }

    fn reject_path_leaks(&self) -> Result<(), SidecarError> {
        for entry in &self.entries {
            for frame in entry.origin.frames() {
                match frame {
                    OriginFrame::Ranged {
                        range, item, label, ..
                    } => {
                        if DisplayPath::is_absolute_spelling(range.file.package_relative_path())
                            || package_has_path_leak(range.file.package())
                            || item.as_ref().is_some_and(item_has_path_leak)
                            || label
                                .as_deref()
                                .is_some_and(DisplayPath::is_absolute_spelling)
                        {
                            return Err(SidecarError::AbsolutePath(entry.key.as_str().to_owned()));
                        }
                    }
                    OriginFrame::Transformation { item, label, .. } => {
                        if item.as_ref().is_some_and(item_has_path_leak)
                            || label
                                .as_deref()
                                .is_some_and(DisplayPath::is_absolute_spelling)
                        {
                            return Err(SidecarError::AbsolutePath(entry.key.as_str().to_owned()));
                        }
                    }
                }
            }
            if entry
                .generated
                .as_ref()
                .is_some_and(|range| DisplayPath::is_absolute_spelling(&range.artifact))
            {
                return Err(SidecarError::AbsolutePath(entry.key.as_str().to_owned()));
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum SidecarError {
    DuplicateIdentity(Box<MappedIdentity>),
    DuplicateSourceMapKey(SourceMapKey),
    AbsolutePath(String),
    InvalidGeneratedRange,
    RangeOverflow,
}

impl fmt::Display for SidecarError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DuplicateIdentity(identity) => {
                write!(formatter, "duplicate sidecar identity {identity}")
            }
            Self::DuplicateSourceMapKey(key) => write!(
                formatter,
                "duplicate sidecar source-map key {}",
                key.as_str()
            ),
            Self::AbsolutePath(value) => write!(
                formatter,
                "absolute path leaked into sidecar near {value:?}"
            ),
            Self::InvalidGeneratedRange => formatter.write_str("invalid generated source range"),
            Self::RangeOverflow => {
                formatter.write_str("generated source range exceeds sidecar integer limits")
            }
        }
    }
}

impl Error for SidecarError {}

fn push_symbol(
    entries: &mut Vec<SymbolMapEntry>,
    identities: &mut BTreeSet<MappedIdentity>,
    entry: SymbolMapEntry,
) -> Result<(), SidecarError> {
    if !identities.insert(entry.identity.clone()) {
        return Err(SidecarError::DuplicateIdentity(Box::new(entry.identity)));
    }
    entries.push(entry);
    Ok(())
}

fn push_fixed_cell_symbols(
    cells: &[FixedCell<DefinitionSortRef, SymbolId>],
    entries: &mut Vec<SymbolMapEntry>,
    identities: &mut BTreeSet<MappedIdentity>,
) -> Result<(), SidecarError> {
    for cell in cells {
        push_symbol(
            entries,
            identities,
            SymbolMapEntry {
                identity: MappedIdentity::Symbol(cell.id().clone()),
                emitted_name: cell.name().to_owned(),
                source_map_key: cell.origin().key().clone(),
                symbol_kind: Some(SymbolKind::Cell),
            },
        )?;
        if let FixedCellContent::Children { children } = cell.content() {
            push_fixed_cell_symbols(children, entries, identities)?;
        }
    }
    Ok(())
}

fn insert_fixed_configuration(
    entries: &mut BTreeMap<SourceMapKey, SourceMapEntry>,
    configuration: &FixedConfiguration<DefinitionSortRef, SymbolId, DefinitionTerm>,
) -> Result<(), SidecarError> {
    fn cells(
        entries: &mut BTreeMap<SourceMapKey, SourceMapEntry>,
        values: &[FixedCell<DefinitionSortRef, SymbolId>],
    ) -> Result<(), SidecarError> {
        for cell in values {
            insert_origin(entries, cell.origin(), SourceMapNodeKind::Cell)?;
            for attribute in cell.attributes() {
                match attribute {
                    CellAttribute::Color { origin, .. }
                    | CellAttribute::Multiplicity { origin, .. }
                    | CellAttribute::CollectionType { origin, .. }
                    | CellAttribute::Stream { origin, .. }
                    | CellAttribute::Exit { origin } => {
                        insert_origin(entries, origin, SourceMapNodeKind::CellAttribute)?;
                    }
                }
            }
            if let FixedCellContent::Children { children } = cell.content() {
                cells(entries, children)?;
            }
        }
        Ok(())
    }
    fn initializer(
        entries: &mut BTreeMap<SourceMapKey, SourceMapEntry>,
        values: &[FixedInitializerCell<SymbolId, DefinitionTerm>],
    ) -> Result<(), SidecarError> {
        for cell in values {
            insert_origin(entries, cell.origin(), SourceMapNodeKind::InitializerCell)?;
            match cell.content() {
                FixedInitializerContent::Term { term } => insert_term(entries, term)?,
                FixedInitializerContent::Children { children } => {
                    initializer(entries, children)?;
                }
            }
        }
        Ok(())
    }

    if let ConfigurationRoot::Named { origin, .. } = configuration.root() {
        insert_origin(entries, origin, SourceMapNodeKind::ConfigurationRoot)?;
    }
    insert_origin(
        entries,
        configuration.initializer_origin(),
        SourceMapNodeKind::Initializer,
    )?;
    for variable in configuration.variables() {
        insert_origin(
            entries,
            variable.origin(),
            SourceMapNodeKind::ConfigurationVariable,
        )?;
    }
    cells(entries, configuration.cells())?;
    initializer(entries, configuration.initializer())
}

fn insert_rule_body(
    entries: &mut BTreeMap<SourceMapKey, SourceMapEntry>,
    body: RuleBodyRef<'_, krs_ir_levels::DefinitionLevel>,
) -> Result<(), SidecarError> {
    match body {
        RuleBodyRef::Term(body) => {
            insert_origin(entries, body.origin(), SourceMapNodeKind::Term)?;
            insert_term(entries, body.from())?;
            insert_term(entries, body.to())
        }
        RuleBodyRef::Configuration { body, .. } => {
            insert_origin(
                entries,
                body.origin(),
                SourceMapNodeKind::ConfigurationRewrite,
            )?;
            for clause in body.clauses() {
                insert_origin(entries, clause.origin(), SourceMapNodeKind::CellClause)?;
                insert_term(entries, clause.before())?;
                if let CellPost::Replace { term } = clause.after() {
                    insert_term(entries, term)?;
                }
                match clause.frame() {
                    CellContentFrame::Exact => {}
                    CellContentFrame::KSequenceTail { origin, .. }
                    | CellContentFrame::MapRemainder { origin, .. }
                    | CellContentFrame::ListRemainder { origin } => {
                        insert_origin(entries, origin, SourceMapNodeKind::CellFrame)?;
                    }
                }
            }
            Ok(())
        }
    }
}

fn insert_origin(
    entries: &mut BTreeMap<SourceMapKey, SourceMapEntry>,
    origin: &NodeOrigin,
    kind: SourceMapNodeKind,
) -> Result<(), SidecarError> {
    let entry = SourceMapEntry {
        key: origin.key().clone(),
        node_kind: kind,
        origin: origin.origin().clone(),
        generated: None,
    };
    if entries.insert(entry.key.clone(), entry).is_some() {
        return Err(SidecarError::DuplicateSourceMapKey(origin.key().clone()));
    }
    Ok(())
}

fn insert_term(
    entries: &mut BTreeMap<SourceMapKey, SourceMapEntry>,
    term: &DefinitionTerm,
) -> Result<(), SidecarError> {
    insert_origin(entries, term.origin(), SourceMapNodeKind::Term)?;
    match term.kind() {
        DefinitionTermKind::Map(operands) => {
            for operand in operands.operands() {
                insert_term(entries, operand)?;
            }
        }
        DefinitionTermKind::List(operands) => {
            for operand in operands.operands() {
                insert_term(entries, operand)?;
            }
        }
        DefinitionTermKind::Set(operands) => {
            for operand in operands.operands() {
                insert_term(entries, operand)?;
            }
        }
        DefinitionTermKind::Application { arguments, .. }
        | DefinitionTermKind::KSequence {
            items: arguments, ..
        }
        | DefinitionTermKind::Cell {
            children: arguments,
            ..
        } => {
            for argument in arguments {
                insert_term(entries, argument)?;
            }
        }
        DefinitionTermKind::Rewrite { from, to } => {
            insert_term(entries, from)?;
            insert_term(entries, to)?;
        }
        DefinitionTermKind::Variable { .. } | DefinitionTermKind::Token { .. } => {}
    }
    Ok(())
}

fn canonical_json(value: &impl Serialize) -> serde_json::Result<String> {
    let mut json = serde_json::to_string_pretty(value)?;
    json.push('\n');
    Ok(json)
}

fn item_has_path_leak(item: &krs_ir::StableItemId) -> bool {
    package_has_path_leak(item.package())
        || item
            .module_path()
            .iter()
            .any(|value| DisplayPath::is_absolute_spelling(value))
        || DisplayPath::is_absolute_spelling(item.item_name())
        || DisplayPath::is_absolute_spelling(item.disambiguator())
}

fn package_has_path_leak(package: &krs_ir::PackageId) -> bool {
    DisplayPath::is_absolute_spelling(package.k_namespace())
        || DisplayPath::is_absolute_spelling(package.cargo_name())
        || DisplayPath::is_absolute_spelling(package.cargo_version())
}

#[cfg(test)]
mod reader_tests {
    use super::*;

    #[test]
    fn sidecar_readers_require_the_current_version() {
        for version in [0, 1, 3] {
            let input = serde_json::json!({"schema_version": version, "entries": []});
            assert!(serde_json::from_value::<SymbolMap>(input.clone()).is_err());
            assert!(serde_json::from_value::<SourceMap>(input).is_err());
        }
        let valid = serde_json::json!({"schema_version": SIDECAR_SCHEMA_VERSION, "entries": []});
        assert!(serde_json::from_value::<SymbolMap>(valid.clone()).is_ok());
        assert!(serde_json::from_value::<SourceMap>(valid).is_ok());
    }
}
