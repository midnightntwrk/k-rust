#![allow(clippy::result_large_err)]

use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt;

use krs_ir::{
    CellAttribute, CellContentFrame, CellPost, ConfigurationRoot, ConfigurationSentence,
    DefinitionIr, DefinitionRuleBody, DefinitionSentence, DefinitionSortRef, DefinitionTerm,
    DefinitionTermKind, FixedCell, FixedCellContent, FixedConfiguration, FixedInitializerCell,
    FixedInitializerContent, LabelId, ModuleId, NodeOrigin, OriginFrame, OriginStack, SourceMapKey,
    StableItemId, SymbolId, SymbolKind,
};
use serde::{Deserialize, Serialize};

/// Version of the compiler-owned symbol/source sidecar encoding.
const SIDECAR_SCHEMA_VERSION: u32 = 2;

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
    schema_version: u32,
    entries: Vec<SymbolMapEntry>,
}

impl SymbolMap {
    #[allow(clippy::too_many_lines)]
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
                    DefinitionSentence::Configuration(sentence) => match sentence {
                        ConfigurationSentence::Legacy(_) => {
                            if let (Some(cell), Some(initializer)) =
                                (sentence.cell(), sentence.initializer())
                            {
                                for (symbol, origin) in [
                                    (cell.symbol(), cell.origin()),
                                    (initializer.symbol(), initializer.origin()),
                                ] {
                                    push_symbol(
                                        &mut entries,
                                        &mut identities,
                                        SymbolMapEntry {
                                            identity: MappedIdentity::Symbol(symbol.id().clone()),
                                            emitted_name: symbol.emitted_name().to_owned(),
                                            source_map_key: origin.key().clone(),
                                            symbol_kind: Some(symbol.kind()),
                                        },
                                    )?;
                                }
                            }
                        }
                        ConfigurationSentence::Fixed(configuration) => {
                            push_fixed_cell_symbols(
                                configuration.cells(),
                                &mut entries,
                                &mut identities,
                            )?;
                        }
                    },
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
                    | DefinitionSentence::Associativity(_) => {}
                }
            }
        }
        entries.sort();
        let map = Self {
            schema_version: SIDECAR_SCHEMA_VERSION,
            entries,
        };
        map.reject_path_leaks()?;
        Ok(map)
    }

    /// Returns entries in canonical identity order.
    #[must_use]
    pub fn entries(&self) -> &[SymbolMapEntry] {
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

    fn reject_path_leaks(&self) -> Result<(), SidecarError> {
        for entry in &self.entries {
            if looks_absolute_path(&entry.emitted_name) {
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
}

/// Half-open range in the canonical generated `.k` artifact.
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
    pub(crate) fn new(source: &str, start: usize, end: usize) -> Result<Self, SidecarError> {
        if start > end
            || end > source.len()
            || !source.is_char_boundary(start)
            || !source.is_char_boundary(end)
        {
            return Err(SidecarError::InvalidGeneratedRange);
        }
        let (start_line, start_column) = line_column(source, start)?;
        let (end_line, end_column) = line_column(source, end)?;
        Ok(Self {
            artifact: "definition.k".to_owned(),
            start_byte: u64::try_from(start).map_err(|_| SidecarError::RangeOverflow)?,
            end_byte: u64::try_from(end).map_err(|_| SidecarError::RangeOverflow)?,
            start_line,
            start_column,
            end_line,
            end_column,
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
    schema_version: u32,
    entries: Vec<SourceMapEntry>,
}

impl SourceMap {
    #[allow(clippy::too_many_lines)]
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
                            if let krs_ir::DefinitionProductionAttribute::Strictness {
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
                    DefinitionSentence::Configuration(sentence) => match sentence {
                        ConfigurationSentence::Legacy(_) => {
                            if let (Some(cell), Some(initializer)) =
                                (sentence.cell(), sentence.initializer())
                            {
                                insert_origin(
                                    &mut entries,
                                    cell.origin(),
                                    SourceMapNodeKind::Cell,
                                )?;
                                insert_origin(
                                    &mut entries,
                                    initializer.origin(),
                                    SourceMapNodeKind::Initializer,
                                )?;
                                insert_term(&mut entries, initializer.body())?;
                            }
                        }
                        ConfigurationSentence::Fixed(configuration) => {
                            insert_fixed_configuration(&mut entries, configuration)?;
                        }
                    },
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
                            | CellContentFrame::MapRemainder { origin, .. } = cell.frame()
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

    pub(crate) fn with_generated_ranges(
        mut self,
        source: &str,
        ranges: &BTreeMap<SourceMapKey, (usize, usize)>,
    ) -> Result<Self, SidecarError> {
        for entry in &mut self.entries {
            if let Some((start, end)) = ranges.get(&entry.key) {
                entry.generated = Some(GeneratedRange::new(source, *start, *end)?);
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
                        if looks_absolute_path(range.file.package_relative_path())
                            || range.file.package().cargo_source().starts_with("file:")
                            || package_has_path_leak(range.file.package())
                            || item.as_ref().is_some_and(item_has_path_leak)
                            || label.as_deref().is_some_and(looks_absolute_path)
                        {
                            return Err(SidecarError::AbsolutePath(entry.key.as_str().to_owned()));
                        }
                    }
                    OriginFrame::Transformation { item, label, .. } => {
                        if item.as_ref().is_some_and(item_has_path_leak)
                            || label.as_deref().is_some_and(looks_absolute_path)
                        {
                            return Err(SidecarError::AbsolutePath(entry.key.as_str().to_owned()));
                        }
                    }
                }
            }
            if entry
                .generated
                .as_ref()
                .is_some_and(|range| looks_absolute_path(&range.artifact))
            {
                return Err(SidecarError::AbsolutePath(entry.key.as_str().to_owned()));
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum SidecarError {
    DuplicateIdentity(MappedIdentity),
    DuplicateSourceMapKey(SourceMapKey),
    AbsolutePath(String),
    InvalidGeneratedRange,
    RangeOverflow,
}

impl fmt::Display for SidecarError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DuplicateIdentity(identity) => {
                write!(formatter, "duplicate sidecar identity {identity:?}")
            }
            Self::DuplicateSourceMapKey(key) => write!(
                formatter,
                "duplicate sidecar source-map key {:?}",
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
        return Err(SidecarError::DuplicateIdentity(entry.identity));
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
                    | CellAttribute::CollectionType { origin, .. } => {
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
    body: &DefinitionRuleBody,
) -> Result<(), SidecarError> {
    match body {
        DefinitionRuleBody::Term(body) => insert_term(entries, body),
        DefinitionRuleBody::Configuration(body) => {
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
                    | CellContentFrame::MapRemainder { origin, .. } => {
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
        DefinitionTermKind::Application { arguments, .. }
        | DefinitionTermKind::Map { arguments, .. }
        | DefinitionTermKind::List { arguments, .. }
        | DefinitionTermKind::Set { arguments, .. }
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

fn line_column(source: &str, offset: usize) -> Result<(u32, u32), SidecarError> {
    let prefix = &source[..offset];
    let line = u32::try_from(prefix.bytes().filter(|byte| *byte == b'\n').count() + 1)
        .map_err(|_| SidecarError::RangeOverflow)?;
    let column_source = prefix
        .rsplit_once('\n')
        .map_or(prefix, |(_, suffix)| suffix);
    let column = u32::try_from(column_source.chars().count() + 1)
        .map_err(|_| SidecarError::RangeOverflow)?;
    Ok((line, column))
}

fn looks_absolute_path(value: &str) -> bool {
    value.starts_with('/')
        || value.starts_with("file:")
        || (value.len() >= 3
            && value.as_bytes()[0].is_ascii_alphabetic()
            && value.as_bytes()[1] == b':'
            && matches!(value.as_bytes()[2], b'/' | b'\\'))
}

fn item_has_path_leak(item: &krs_ir::StableItemId) -> bool {
    package_has_path_leak(item.package())
        || item
            .module_path()
            .iter()
            .any(|value| looks_absolute_path(value))
        || looks_absolute_path(item.item_name())
        || looks_absolute_path(item.disambiguator())
}

fn package_has_path_leak(package: &krs_ir::PackageId) -> bool {
    looks_absolute_path(package.k_namespace())
        || looks_absolute_path(package.cargo_name())
        || looks_absolute_path(package.cargo_version())
        || package.cargo_source().starts_with("file:")
}
