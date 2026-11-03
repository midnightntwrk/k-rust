use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt;

use krs_ir::{
    ByteRange, CellAttribute, CellContentFrame, ConfigurationRoot, DisplayPath, FixedCell,
    FixedCellContent, FixedConfiguration, FixedInitializerCell, FixedInitializerContent, LineIndex,
    ModuleId, NodeOrigin, OriginFrame, OriginStack, SourceMapKey, SourceRange, StableItemId,
};
use krs_ir_levels::{
    DefinitionIr, DefinitionSentence, DefinitionSortRef, DefinitionTerm, DefinitionTermKind,
    LabelId, RuleBodyRef, SymbolId, SymbolKind,
};
use serde::{Deserialize, Serialize};

/// Version of the compiler-owned symbol/source sidecar encoding.
const SIDECAR_SCHEMA_VERSION: u32 = 3;

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

    /// Serializes stable compact JSON with one trailing newline ([`krs_ir::json::write_canonical`]).
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
    /// Typed existential binder component of a transition (`#[k::exists]`).
    RuleExistentialBinder,
    /// Complete object-language Boolean postcondition of a transition (`#[k::ensures]`).
    RuleEnsures,
    /// Typed fresh binder component of a transition (`#[k::fresh]`).
    RuleFreshBinder,
    /// Claim trusted marker: the claim is assumed without proof.
    ClaimTrusted,
    /// `concrete`, `symbolic`, or `smt_lemma` key of an equation or simplification, or one binder it names.
    MatchRestriction,
    /// The `[[ .. ]]` configuration context of an equation (KF-025).
    FunctionContext,
    /// One matching-logic connective of a predicate (KF-039).
    MlPredicate,
    /// One `ml::exists` binder component (KF-039).
    MlBinder,
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
    /// The node's nesting in the rendering of the Definition IR: a module 0,
    /// its sentences 1, and each child one more than the node that holds it,
    /// except in a configuration, whose cell declarations and initializer
    /// are rendered as one text (`insert_fixed_configuration`), and for a
    /// node rendered at a term's occurrence (a configuration variable, a
    /// context alias's `HERE`), one deeper than that term. Within one
    /// artifact a node whose generated range strictly holds another's is
    /// shallower, and nodes of one range have distinct depths, so depth
    /// orders them and names the deepest owner of each byte.
    depth: u32,
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

    /// Returns the node's nesting depth in the Definition IR.
    #[must_use]
    pub const fn depth(&self) -> u32 {
        self.depth
    }

    /// Returns authored-to-Definition provenance.
    #[must_use]
    pub const fn origin(&self) -> &OriginStack {
        &self.origin
    }

    /// The insertion that produced the node, with the authored range of the
    /// construct it serves when that differs from its own; `None` for a
    /// node that renders authored syntax.
    #[must_use]
    pub fn inserted(&self) -> Option<(krs_ir::InsertedNode, Option<&krs_ir::SourceRange>)> {
        self.origin.inserted()
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
            insert_origin(&mut entries, module.origin(), SourceMapNodeKind::Module, 0)?;
            for group in module.production_groups() {
                insert_origin(
                    &mut entries,
                    group.origin(),
                    SourceMapNodeKind::ProductionGroup,
                    1,
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
                insert_origin(&mut entries, sentence.origin(), kind, 1)?;
                match sentence {
                    DefinitionSentence::Production(sentence) => {
                        for item in sentence.items() {
                            insert_origin(
                                &mut entries,
                                item.origin(),
                                SourceMapNodeKind::ProductionItem,
                                2,
                            )?;
                        }
                        for attribute in sentence.attributes() {
                            insert_origin(
                                &mut entries,
                                attribute.origin(),
                                SourceMapNodeKind::ProductionAttribute,
                                2,
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
                                        3,
                                    )?;
                                }
                                for field in fields {
                                    insert_origin(
                                        &mut entries,
                                        field.origin(),
                                        SourceMapNodeKind::ProductionAttribute,
                                        3,
                                    )?;
                                }
                                insert_origin(
                                    &mut entries,
                                    result_sort.origin(),
                                    SourceMapNodeKind::ProductionAttribute,
                                    3,
                                )?;
                            }
                        }
                    }
                    DefinitionSentence::Configuration(configuration) => {
                        insert_fixed_configuration(&mut entries, configuration, 2)?;
                    }
                    DefinitionSentence::Rule(sentence) => {
                        insert_rule_body(&mut entries, sentence.relational_body(), 2)?;
                        if let Some(priority) = sentence.priority() {
                            insert_origin(
                                &mut entries,
                                priority.origin(),
                                SourceMapNodeKind::RulePriority,
                                2,
                            )?;
                        }
                        if let Some(simplification) = sentence.simplification() {
                            insert_origin(
                                &mut entries,
                                simplification.origin(),
                                SourceMapNodeKind::Simplification,
                                2,
                            )?;
                            if let Some(priority) = simplification.priority() {
                                insert_origin(
                                    &mut entries,
                                    priority.origin(),
                                    SourceMapNodeKind::SimplificationPriority,
                                    3,
                                )?;
                            }
                        }
                        if let Some(restriction) = sentence.restriction() {
                            for origin in restriction.origins() {
                                insert_origin(
                                    &mut entries,
                                    origin,
                                    SourceMapNodeKind::MatchRestriction,
                                    2,
                                )?;
                            }
                        }
                        if let Some(context) = sentence.function_context() {
                            insert_origin(
                                &mut entries,
                                context.origin(),
                                SourceMapNodeKind::FunctionContext,
                                2,
                            )?;
                            for cell in context.cells().cells() {
                                insert_origin(
                                    &mut entries,
                                    cell.origin(),
                                    SourceMapNodeKind::CellClause,
                                    3,
                                )?;
                                insert_term(&mut entries, cell.pattern(), 4)?;
                                if let Some(origin) = cell.frame().origin() {
                                    insert_origin(
                                        &mut entries,
                                        origin,
                                        SourceMapNodeKind::CellFrame,
                                        4,
                                    )?;
                                }
                            }
                        }
                        if let Some(condition) = sentence.requires() {
                            insert_condition(
                                &mut entries,
                                condition,
                                SourceMapNodeKind::RuleCondition,
                                2,
                            )?;
                        }
                        if let Some(claim) = sentence.claim() {
                            insert_origin(
                                &mut entries,
                                claim.modality_origin(),
                                SourceMapNodeKind::ClaimModality,
                                2,
                            )?;
                            if let Some(origin) = claim.circularity_origin() {
                                insert_origin(
                                    &mut entries,
                                    origin,
                                    SourceMapNodeKind::ClaimCircularity,
                                    2,
                                )?;
                            }
                            if let Some(origin) = claim.trusted_origin() {
                                insert_origin(
                                    &mut entries,
                                    origin,
                                    SourceMapNodeKind::ClaimTrusted,
                                    2,
                                )?;
                            }
                            for binder in claim.universals() {
                                insert_binder(
                                    &mut entries,
                                    binder,
                                    SourceMapNodeKind::ClaimBinder,
                                    2,
                                )?;
                            }
                        }
                        let (binder_kind, ensures_kind) =
                            if sentence.kind() == krs_ir::SentenceKind::Claim {
                                (
                                    SourceMapNodeKind::ClaimBinder,
                                    SourceMapNodeKind::ClaimEnsures,
                                )
                            } else {
                                (
                                    SourceMapNodeKind::RuleExistentialBinder,
                                    SourceMapNodeKind::RuleEnsures,
                                )
                            };
                        for binder in sentence.existentials() {
                            insert_binder(&mut entries, binder, binder_kind, 2)?;
                        }
                        for binder in sentence.fresh() {
                            insert_binder(
                                &mut entries,
                                binder,
                                SourceMapNodeKind::RuleFreshBinder,
                                2,
                            )?;
                        }
                        if let Some(ensures) = sentence.ensures() {
                            insert_condition(&mut entries, ensures, ensures_kind, 2)?;
                        }
                    }
                    DefinitionSentence::ContextAlias(sentence) => {
                        insert_origin(
                            &mut entries,
                            sentence.name_origin(),
                            SourceMapNodeKind::ContextAlias,
                            2,
                        )?;
                        let mut holes = Vec::new();
                        for cell in sentence.body().cells() {
                            insert_origin(
                                &mut entries,
                                cell.origin(),
                                SourceMapNodeKind::CellClause,
                                2,
                            )?;
                            insert_term(&mut entries, cell.pattern(), 3)?;
                            variable_occurrences(cell.pattern(), sentence.here(), &mut holes);
                            if let Some(origin) = cell.frame().origin() {
                                insert_origin(
                                    &mut entries,
                                    origin,
                                    SourceMapNodeKind::CellFrame,
                                    3,
                                )?;
                            }
                        }
                        // `HERE` is rendered at the hole's occurrence.
                        let here = below_deepest(&entries, &holes).unwrap_or(2);
                        insert_origin(
                            &mut entries,
                            sentence.here_origin(),
                            SourceMapNodeKind::ContextAlias,
                            here,
                        )?;
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

    /// Serializes stable compact JSON with one trailing newline ([`krs_ir::json::write_canonical`]).
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
                    // An inserted frame's anchor is a source range, checked
                    // as a ranged frame's is.
                    OriginFrame::Inserted { anchor, .. } => {
                        if anchor.as_ref().is_some_and(|range| {
                            DisplayPath::is_absolute_spelling(range.file.package_relative_path())
                                || package_has_path_leak(range.file.package())
                        }) {
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

/// Records a configuration's nodes at their nesting in the configuration's
/// one rendering; `depth` is that of its root, initializer and top-level
/// cells. The Definition IR holds the cells' declarations and their
/// initializer as two parallel trees, which the emitter renders as one
/// text: a cell's declaration and its initializer cell both span the cell
/// from `<name` to `</name>`. So the declaration is at the cell's depth,
/// its initializer cell one deeper, and the cell's attributes, value and
/// child cells below both. A named root holds the top-level cells. A
/// configuration variable is rendered at its first occurrence in the
/// initializer, so it is one deeper than its deepest occurrence, and below
/// every node that holds the occurrence it shares its bytes with.
fn insert_fixed_configuration(
    entries: &mut BTreeMap<SourceMapKey, SourceMapEntry>,
    configuration: &FixedConfiguration<DefinitionSortRef, SymbolId, DefinitionTerm>,
    depth: u32,
) -> Result<(), SidecarError> {
    fn cells<'a>(
        entries: &mut BTreeMap<SourceMapKey, SourceMapEntry>,
        values: &'a [FixedCell<DefinitionSortRef, SymbolId>],
        depth: u32,
        depths: &mut BTreeMap<&'a SymbolId, u32>,
    ) -> Result<(), SidecarError> {
        for cell in values {
            insert_origin(entries, cell.origin(), SourceMapNodeKind::Cell, depth)?;
            depths.insert(cell.id(), depth);
            for attribute in cell.attributes() {
                match attribute {
                    CellAttribute::Color { origin, .. }
                    | CellAttribute::Multiplicity { origin, .. }
                    | CellAttribute::CollectionType { origin, .. }
                    | CellAttribute::Stream { origin, .. }
                    | CellAttribute::Exit { origin }
                    | CellAttribute::Initial { origin }
                    | CellAttribute::Unobservable { origin } => {
                        insert_origin(
                            entries,
                            origin,
                            SourceMapNodeKind::CellAttribute,
                            depth + 2,
                        )?;
                    }
                }
            }
            if let FixedCellContent::Children { children } = cell.content() {
                cells(entries, children, depth + 2, depths)?;
            }
        }
        Ok(())
    }
    /// `depth` is where an initializer cell whose declaration is missing
    /// would stand, one below its holder; the emitter refuses that shape.
    fn initializer(
        entries: &mut BTreeMap<SourceMapKey, SourceMapEntry>,
        values: &[FixedInitializerCell<SymbolId, DefinitionTerm>],
        depth: u32,
        depths: &BTreeMap<&SymbolId, u32>,
    ) -> Result<(), SidecarError> {
        for cell in values {
            let depth = depths
                .get(cell.cell())
                .map_or(depth, |declared| declared + 1);
            insert_origin(
                entries,
                cell.origin(),
                SourceMapNodeKind::InitializerCell,
                depth,
            )?;
            match cell.content() {
                FixedInitializerContent::Term { term } => insert_term(entries, term, depth + 1)?,
                FixedInitializerContent::Children { children } => {
                    initializer(entries, children, depth + 1, depths)?;
                }
            }
        }
        Ok(())
    }
    let cell_depth = if let ConfigurationRoot::Named { origin, .. } = configuration.root() {
        insert_origin(entries, origin, SourceMapNodeKind::ConfigurationRoot, depth)?;
        depth + 1
    } else {
        depth
    };
    // Rendered as an empty range after the configuration's text.
    insert_origin(
        entries,
        configuration.initializer_origin(),
        SourceMapNodeKind::Initializer,
        depth,
    )?;
    let mut depths = BTreeMap::new();
    cells(entries, configuration.cells(), cell_depth, &mut depths)?;
    initializer(
        entries,
        configuration.initializer(),
        cell_depth + 1,
        &depths,
    )?;
    for variable in configuration.variables() {
        let mut found = Vec::new();
        initializer_occurrences(configuration.initializer(), variable.id(), &mut found);
        let rendered = below_deepest(entries, &found).unwrap_or(depth);
        insert_origin(
            entries,
            variable.origin(),
            SourceMapNodeKind::ConfigurationVariable,
            rendered,
        )?;
    }
    Ok(())
}

/// Every occurrence of `variable` in the initializer `cells`.
fn initializer_occurrences<'a>(
    cells: &'a [FixedInitializerCell<SymbolId, DefinitionTerm>],
    variable: &krs_ir::SemanticId,
    found: &mut Vec<&'a DefinitionTerm>,
) {
    for cell in cells {
        match cell.content() {
            FixedInitializerContent::Term { term } => {
                variable_occurrences(term, variable, found);
            }
            FixedInitializerContent::Children { children } => {
                initializer_occurrences(children, variable, found);
            }
        }
    }
}

/// Every occurrence of `variable` in `term`.
fn variable_occurrences<'a>(
    term: &'a DefinitionTerm,
    variable: &krs_ir::SemanticId,
    found: &mut Vec<&'a DefinitionTerm>,
) {
    if matches!(term.kind(), DefinitionTermKind::Variable { variable: name } if name == variable) {
        found.push(term);
    }
    for child in term.children() {
        variable_occurrences(child, variable, found);
    }
}

/// One more than the deepest recorded of `occurrences`: the depth of a
/// node the emitter renders at one of them, which falls below every node
/// that holds that occurrence.
fn below_deepest(
    entries: &BTreeMap<SourceMapKey, SourceMapEntry>,
    occurrences: &[&DefinitionTerm],
) -> Option<u32> {
    occurrences
        .iter()
        .filter_map(|occurrence| entries.get(occurrence.origin().key()))
        .map(|entry| entry.depth + 1)
        .max()
}

/// Records one condition: a Bool condition under `kind` with its term, or
/// a predicate's connectives, binders, and terms (KF-039).
fn insert_condition(
    entries: &mut BTreeMap<SourceMapKey, SourceMapEntry>,
    condition: &krs_ir_levels::DefinitionCondition,
    kind: SourceMapNodeKind,
    depth: u32,
) -> Result<(), SidecarError> {
    match condition {
        krs_ir_levels::IrCondition::Bool(condition) => {
            insert_origin(entries, condition.origin(), kind, depth)?;
            insert_term(entries, condition.term(), depth + 1)
        }
        krs_ir_levels::IrCondition::Predicate(predicate) => {
            insert_predicate(entries, predicate, depth)
        }
    }
}

/// Records a predicate's connectives, `ml::exists` binders, and terms, each
/// one deeper than the connective that holds it.
fn insert_predicate(
    entries: &mut BTreeMap<SourceMapKey, SourceMapEntry>,
    predicate: &krs_ir_levels::DefinitionMlPredicate,
    depth: u32,
) -> Result<(), SidecarError> {
    use krs_ir_levels::IrMlKind;
    insert_origin(
        entries,
        predicate.origin(),
        SourceMapNodeKind::MlPredicate,
        depth,
    )?;
    match predicate.kind() {
        IrMlKind::Top | IrMlKind::Bottom => Ok(()),
        IrMlKind::Not { operand } => insert_predicate(entries, operand, depth + 1),
        IrMlKind::And { left, right }
        | IrMlKind::Or { left, right }
        | IrMlKind::Implies { left, right } => {
            insert_predicate(entries, left, depth + 1)?;
            insert_predicate(entries, right, depth + 1)
        }
        IrMlKind::Equals { left, right, .. } => {
            insert_term(entries, left, depth + 1)?;
            insert_term(entries, right, depth + 1)
        }
        IrMlKind::Ceil { term, .. } => insert_term(entries, term, depth + 1),
        IrMlKind::Exists { binder, body } => {
            insert_binder(entries, binder, SourceMapNodeKind::MlBinder, depth + 1)?;
            insert_predicate(entries, body, depth + 1)
        }
    }
}

/// Records a scoped binder at `depth` and its name and sort below it.
fn insert_binder(
    entries: &mut BTreeMap<SourceMapKey, SourceMapEntry>,
    binder: &krs_ir_levels::IrScopedBinder<krs_ir_levels::DefinitionLevel>,
    kind: SourceMapNodeKind,
    depth: u32,
) -> Result<(), SidecarError> {
    insert_origin(entries, binder.origin(), kind, depth)?;
    insert_origin(entries, binder.name_origin(), kind, depth + 1)?;
    insert_origin(entries, binder.sort_origin(), kind, depth + 1)
}

fn insert_rule_body(
    entries: &mut BTreeMap<SourceMapKey, SourceMapEntry>,
    body: RuleBodyRef<'_, krs_ir_levels::DefinitionLevel>,
    depth: u32,
) -> Result<(), SidecarError> {
    match body {
        RuleBodyRef::Predicate(body) => {
            insert_origin(entries, body.origin(), SourceMapNodeKind::Term, depth)?;
            insert_predicate(entries, body.lhs(), depth + 1)?;
            insert_predicate(entries, body.rhs(), depth + 1)
        }
        // A single-body rule (KF-011) maps its authored term once.
        RuleBodyRef::Term(body) => {
            if let Some(local) = body.local_term() {
                return insert_term(entries, local, depth);
            }
            insert_origin(entries, body.origin(), SourceMapNodeKind::Term, depth)?;
            insert_term(entries, body.from(), depth + 1)?;
            insert_term(entries, body.to(), depth + 1)
        }
        RuleBodyRef::Configuration { body, .. } => {
            insert_origin(
                entries,
                body.origin(),
                SourceMapNodeKind::ConfigurationRewrite,
                depth,
            )?;
            for clause in body.clauses() {
                insert_origin(
                    entries,
                    clause.origin(),
                    SourceMapNodeKind::CellClause,
                    depth + 1,
                )?;
                // A collection clause's instances and their children are
                // nodes too (KF-023).
                if let krs_ir::ConfigurationClause::Instances(instances) = clause {
                    for instance in instances.instances() {
                        insert_origin(
                            entries,
                            instance.origin(),
                            SourceMapNodeKind::CellClause,
                            depth + 2,
                        )?;
                        match instance {
                            krs_ir::InstanceClause::Kept { children, .. } => {
                                for child in children {
                                    insert_origin(
                                        entries,
                                        child.origin(),
                                        SourceMapNodeKind::CellClause,
                                        depth + 3,
                                    )?;
                                }
                            }
                            krs_ir::InstanceClause::Removed { children, .. }
                            | krs_ir::InstanceClause::Created { children, .. } => {
                                for child in children {
                                    insert_origin(
                                        entries,
                                        child.origin(),
                                        SourceMapNodeKind::CellClause,
                                        depth + 3,
                                    )?;
                                }
                            }
                        }
                    }
                }
                // A fixed clause's terms and frame are its children; a
                // collection clause's parts are those of an instance's
                // mentioned children.
                let part_depth = if matches!(clause, krs_ir::ConfigurationClause::Instances(_)) {
                    depth + 4
                } else {
                    depth + 2
                };
                for part in clause.parts() {
                    let depth = part_depth;
                    for term in part.terms() {
                        insert_term(entries, term, depth)?;
                    }
                    if let Some(origin) = part.frame().and_then(CellContentFrame::origin) {
                        insert_origin(entries, origin, SourceMapNodeKind::CellFrame, depth)?;
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
    depth: u32,
) -> Result<(), SidecarError> {
    let entry = SourceMapEntry {
        key: origin.key().clone(),
        node_kind: kind,
        depth,
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
    depth: u32,
) -> Result<(), SidecarError> {
    insert_origin(entries, term.origin(), SourceMapNodeKind::Term, depth)?;
    match term.kind() {
        DefinitionTermKind::Map(operands) => {
            for operand in operands.operands() {
                insert_term(entries, operand, depth + 1)?;
            }
        }
        DefinitionTermKind::List(operands) => {
            for operand in operands.operands() {
                insert_term(entries, operand, depth + 1)?;
            }
        }
        DefinitionTermKind::Set(operands) => {
            for operand in operands.operands() {
                insert_term(entries, operand, depth + 1)?;
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
                insert_term(entries, argument, depth + 1)?;
            }
        }
        DefinitionTermKind::Rewrite { from, to } => {
            insert_term(entries, from, depth + 1)?;
            insert_term(entries, to, depth + 1)?;
        }
        DefinitionTermKind::As { pattern, .. } => insert_term(entries, pattern, depth + 1)?,
        DefinitionTermKind::Or { alternatives } => {
            for alternative in alternatives {
                insert_term(entries, alternative, depth + 1)?;
            }
        }
        DefinitionTermKind::Matches {
            subject, pattern, ..
        } => {
            insert_term(entries, subject, depth + 1)?;
            insert_term(entries, pattern, depth + 1)?;
        }
        DefinitionTermKind::Let {
            pattern,
            value,
            body,
            ..
        } => {
            insert_term(entries, pattern, depth + 1)?;
            insert_term(entries, value, depth + 1)?;
            insert_term(entries, body, depth + 1)?;
        }
        DefinitionTermKind::Variable { .. } | DefinitionTermKind::Token { .. } => {}
    }
    Ok(())
}

fn canonical_json(value: &impl Serialize) -> serde_json::Result<String> {
    krs_ir::json::to_canonical_string(value)
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
        for version in [0, 1, 2, 4] {
            let input = serde_json::json!({"schema_version": version, "entries": []});
            assert!(serde_json::from_value::<SymbolMap>(input.clone()).is_err());
            assert!(serde_json::from_value::<SourceMap>(input).is_err());
        }
        let valid = serde_json::json!({"schema_version": SIDECAR_SCHEMA_VERSION, "entries": []});
        assert!(serde_json::from_value::<SymbolMap>(valid.clone()).is_ok());
        assert!(serde_json::from_value::<SourceMap>(valid).is_ok());
    }
}
