//! Target-neutral, source-level K Definition IR.
//!
//! Generated K symbol and label names are declared exactly once here. Terms
//! refer to stable IDs, so neither the textual emitter nor a native frontend
//! adapter can independently invent identities or attach adapter metadata.

use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt;

use serde::{Deserialize, Deserializer, Serialize};

use crate::ir::validated_id;
use crate::{
    ApplicationRef, BuiltinOperation, BuiltinSort, FormatFragment, GrammarProductionItem,
    GrammarProductionItemKind, GroupAssociativitySentence, IrIdentityError, IrSchemaVersion,
    ItemKind, ListOperation, MapOperation, ModuleId, NodeOrigin, PrecedenceRelation,
    ProductionAttribute, ProductionFieldId, ProductionGroupId, SemanticId, SentenceKind,
    SourceMapKey, StableItemId,
};
use crate::{
    CellContentFrame, CellPost, FixedCell, FixedCellClause, FixedCellContent, FixedConfiguration,
    FixedConfigurationPattern, FixedConfigurationRewrite, FixedInitializerCell,
    FixedInitializerContent,
};

/// Authored or compiler-provided Definition application reference.
pub type DefinitionApplicationRef = ApplicationRef<SymbolId>;

/// Definition grammar item carrying typed sort references.
pub type ProductionItem = GrammarProductionItem<DefinitionSortRef>;

/// Classified Definition production metadata.
pub type DefinitionProductionAttribute = ProductionAttribute<DefinitionSortRef>;

/// Stable generated symbol identity.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(transparent)]
pub struct SymbolId(String);

impl SymbolId {
    /// Creates a nonempty, path-free identity.
    ///
    /// # Errors
    ///
    /// Returns [`IrIdentityError`] for blank or path-shaped input.
    pub fn new(value: impl Into<String>) -> Result<Self, IrIdentityError> {
        validated_id("symbol_id", value.into()).map(Self)
    }
    /// Returns the identity.
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl<'de> Deserialize<'de> for SymbolId {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Self::new(String::deserialize(deserializer)?).map_err(serde::de::Error::custom)
    }
}

/// A sort reference in source-level Definition IR.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(tag = "sort_source", content = "sort", rename_all = "snake_case")]
pub enum DefinitionSortRef {
    /// Generated or imported declared sort symbol.
    Declared(SymbolId),
    /// Sort intrinsic to the K language.
    Builtin(BuiltinSort),
}

impl DefinitionSortRef {
    /// Refers to a declared sort symbol.
    #[must_use]
    pub const fn declared(sort: SymbolId) -> Self {
        Self::Declared(sort)
    }

    /// Refers to the builtin K computation-sequence sort.
    #[must_use]
    pub const fn k_sequence() -> Self {
        Self::Builtin(BuiltinSort::KSequence)
    }

    /// Refers to the compiler-provided integer sort.
    #[must_use]
    pub const fn int() -> Self {
        Self::Builtin(BuiltinSort::Int)
    }

    /// Refers to the compiler-provided Boolean sort.
    #[must_use]
    pub const fn bool() -> Self {
        Self::Builtin(BuiltinSort::Bool)
    }

    /// Stable identifier-token sort from `ID-SYNTAX`.
    #[must_use]
    pub const fn id() -> Self {
        Self::Builtin(BuiltinSort::Id)
    }

    /// Stable finite-map sort from `MAP`.
    #[must_use]
    pub const fn map() -> Self {
        Self::Builtin(BuiltinSort::Map)
    }

    /// Stable associative-list sort from `LIST`.
    #[must_use]
    pub const fn list() -> Self {
        Self::Builtin(BuiltinSort::List)
    }
}

/// Stable generated rule-label identity.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(transparent)]
pub struct LabelId(String);

impl LabelId {
    /// Creates a nonempty, path-free identity.
    ///
    /// # Errors
    ///
    /// Returns [`IrIdentityError`] for blank or path-shaped input.
    pub fn new(value: impl Into<String>) -> Result<Self, IrIdentityError> {
        validated_id("label_id", value.into()).map(Self)
    }
    /// Returns the identity.
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl<'de> Deserialize<'de> for LabelId {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Self::new(String::deserialize(deserializer)?).map_err(serde::de::Error::custom)
    }
}

/// The semantic role of a generated symbol.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SymbolKind {
    /// K syntax sort.
    Sort,
    /// Constructor or function production.
    Production,
    /// Generated configuration cell label.
    Cell,
    /// Generated initializer label.
    Initializer,
}

/// The sole declaration of a generated symbol's ID and emitted K name.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SymbolIdentity {
    id: SymbolId,
    emitted_name: String,
    kind: SymbolKind,
}

impl SymbolIdentity {
    /// Creates a target-neutral symbol declaration.
    ///
    /// # Errors
    ///
    /// Returns [`DefinitionValidationError`] for blank or path-shaped names.
    pub fn new(
        id: SymbolId,
        emitted_name: impl Into<String>,
        kind: SymbolKind,
    ) -> Result<Self, DefinitionValidationError> {
        let emitted_name = emitted_name.into();
        if emitted_name.trim().is_empty() {
            return Err(DefinitionValidationError::EmptyText("symbol name"));
        }
        if emitted_name.contains(['/', '\\']) {
            return Err(DefinitionValidationError::AdapterSpecificValue(
                "symbol name",
            ));
        }
        Ok(Self {
            id,
            emitted_name,
            kind,
        })
    }
    /// Returns the stable identity.
    #[must_use]
    pub const fn id(&self) -> &SymbolId {
        &self.id
    }
    /// Returns the generated K name chosen by shared lowering.
    #[must_use]
    pub fn emitted_name(&self) -> &str {
        &self.emitted_name
    }
    /// Returns the symbol role.
    #[must_use]
    pub const fn kind(&self) -> SymbolKind {
        self.kind
    }
}

/// The sole declaration of a rule label's ID and emitted K name.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LabelIdentity {
    id: LabelId,
    emitted_name: String,
}

impl LabelIdentity {
    /// Creates a generated label declaration.
    ///
    /// # Errors
    ///
    /// Returns [`DefinitionValidationError`] for blank or path-shaped names.
    pub fn new(
        id: LabelId,
        emitted_name: impl Into<String>,
    ) -> Result<Self, DefinitionValidationError> {
        let emitted_name = emitted_name.into();
        if emitted_name.trim().is_empty() {
            return Err(DefinitionValidationError::EmptyText("label name"));
        }
        if emitted_name.contains(['/', '\\']) {
            return Err(DefinitionValidationError::AdapterSpecificValue(
                "label name",
            ));
        }
        Ok(Self { id, emitted_name })
    }
    /// Returns the stable identity.
    #[must_use]
    pub const fn id(&self) -> &LabelId {
        &self.id
    }
    /// Returns the generated K label chosen by shared lowering.
    #[must_use]
    pub fn emitted_name(&self) -> &str {
        &self.emitted_name
    }
}

/// A checked source-level Definition IR.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct DefinitionIr {
    schema_version: IrSchemaVersion,
    main_module: ModuleId,
    modules: Vec<DefinitionModule>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct DefinitionIrWire {
    schema_version: IrSchemaVersion,
    main_module: ModuleId,
    modules: Vec<DefinitionModule>,
}

impl<'de> Deserialize<'de> for DefinitionIr {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = DefinitionIrWire::deserialize(deserializer)?;
        if wire.schema_version != IrSchemaVersion::CURRENT {
            return Err(serde::de::Error::custom(format_args!(
                "unsupported Definition IR schema {}; expected {}",
                wire.schema_version.0,
                IrSchemaVersion::CURRENT.0
            )));
        }
        Self::new(wire.main_module, wire.modules).map_err(serde::de::Error::custom)
    }
}

impl DefinitionIr {
    /// Validates modules, symbols, labels, origins, references, and the sole
    /// M2 configuration.
    ///
    /// # Errors
    ///
    /// Returns [`DefinitionValidationError`] for any invalid invariant.
    pub fn new(
        main_module: ModuleId,
        modules: Vec<DefinitionModule>,
    ) -> Result<Self, DefinitionValidationError> {
        let definition = Self {
            schema_version: IrSchemaVersion::CURRENT,
            main_module,
            modules,
        };
        definition.validate()?;
        Ok(definition)
    }
    /// Returns the independent IR schema version.
    #[must_use]
    pub const fn schema_version(&self) -> IrSchemaVersion {
        self.schema_version
    }
    /// Returns the selected main module.
    #[must_use]
    pub const fn main_module(&self) -> &ModuleId {
        &self.main_module
    }
    /// Returns modules in caller order.
    #[must_use]
    pub fn modules(&self) -> &[DefinitionModule] {
        &self.modules
    }
    /// Returns canonical, path-free JSON with one trailing newline.
    ///
    /// # Errors
    ///
    /// Returns a JSON encoding error if the serde data model cannot be encoded.
    pub fn to_canonical_json(&self) -> serde_json::Result<String> {
        let mut canonical = self.clone();
        for module in &mut canonical.modules {
            module.canonicalize();
        }
        canonical
            .modules
            .sort_by(|left, right| left.id.cmp(&right.id));
        let mut json = serde_json::to_string_pretty(&canonical)?;
        json.push('\n');
        Ok(json)
    }

    #[allow(clippy::too_many_lines)]
    fn validate(&self) -> Result<(), DefinitionValidationError> {
        if self.modules.is_empty() {
            return Err(DefinitionValidationError::EmptyDefinition);
        }
        let mut modules = BTreeSet::new();
        let mut nodes = BTreeSet::new();
        let mut symbols = BTreeMap::new();
        let mut symbol_names = BTreeSet::new();
        let mut labels = BTreeSet::new();
        let mut label_names = BTreeSet::new();
        let mut production_signatures = BTreeMap::new();
        let mut functional_productions = BTreeSet::new();
        let mut alias_productions = BTreeSet::new();
        let mut context_aliases = BTreeSet::new();
        let mut subsort_parents: BTreeMap<DefinitionSortRef, Vec<DefinitionSortRef>> =
            BTreeMap::new();
        let mut groups = BTreeSet::new();
        let mut group_names = BTreeSet::new();
        let mut configurations = 0_usize;

        for module in &self.modules {
            if !modules.insert(module.id.clone()) {
                return Err(DefinitionValidationError::DuplicateModule(
                    module.id.clone(),
                ));
            }
            insert_node(&mut nodes, module.origin.key())?;
            for group in &module.production_groups {
                insert_node(&mut nodes, group.origin.key())?;
                if !groups.insert(group.id.clone()) {
                    return Err(DefinitionValidationError::DuplicateProductionGroup(
                        group.id.clone(),
                    ));
                }
                if !group_names.insert(group.emitted_name.clone()) {
                    return Err(DefinitionValidationError::DuplicateEmittedName(
                        group.emitted_name.clone(),
                    ));
                }
            }
            for sentence in &module.sentences {
                insert_node(&mut nodes, sentence.origin().key())?;
                match sentence {
                    DefinitionSentence::SyntaxSort(sentence) => {
                        validate_symbol_text(&sentence.symbol)?;
                        declare_symbol(&sentence.symbol, &mut symbols, &mut symbol_names)?;
                    }
                    DefinitionSentence::Subsort(sentence) => {
                        subsort_parents
                            .entry(sentence.subsort.clone())
                            .or_default()
                            .push(sentence.supersort.clone());
                    }
                    DefinitionSentence::Production(sentence) => {
                        validate_symbol_text(&sentence.symbol)?;
                        declare_symbol(&sentence.symbol, &mut symbols, &mut symbol_names)?;
                        production_signatures.insert(
                            sentence.symbol.id.clone(),
                            (
                                sentence.result_sort.clone(),
                                sentence
                                    .items
                                    .iter()
                                    .filter_map(|item| match item.kind() {
                                        GrammarProductionItemKind::NonTerminal { sort, .. } => {
                                            Some(sort.clone())
                                        }
                                        GrammarProductionItemKind::Terminal { .. }
                                        | GrammarProductionItemKind::RegexTerminal { .. } => None,
                                    })
                                    .collect(),
                            ),
                        );
                        if sentence.attributes.iter().any(|attribute| {
                            matches!(attribute, ProductionAttribute::Function { .. })
                        }) {
                            functional_productions.insert(sentence.symbol.id.clone());
                        }
                        if sentence
                            .attributes
                            .iter()
                            .any(|attribute| matches!(attribute, ProductionAttribute::Alias { .. }))
                        {
                            alias_productions.insert(sentence.symbol.id.clone());
                        }
                        for item in &sentence.items {
                            insert_node(&mut nodes, item.origin().key())?;
                        }
                        for attribute in &sentence.attributes {
                            insert_node(&mut nodes, attribute.origin().key())?;
                            if let ProductionAttribute::Strictness {
                                using,
                                fields,
                                result_sort,
                                ..
                            } = attribute
                            {
                                if let Some(using) = using {
                                    insert_node(&mut nodes, using.origin().key())?;
                                }
                                for field in fields {
                                    insert_node(&mut nodes, field.origin().key())?;
                                }
                                insert_node(&mut nodes, result_sort.origin().key())?;
                            }
                        }
                    }
                    DefinitionSentence::Precedence(_) | DefinitionSentence::Associativity(_) => {}
                    DefinitionSentence::Configuration(sentence) => {
                        configurations += 1;
                        match sentence {
                            ConfigurationSentence::Legacy(sentence) => {
                                validate_symbol_text(&sentence.cell.symbol)?;
                                validate_symbol_text(&sentence.initializer.symbol)?;
                                insert_node(&mut nodes, sentence.cell.origin.key())?;
                                insert_node(&mut nodes, sentence.initializer.origin.key())?;
                                declare_symbol(
                                    &sentence.cell.symbol,
                                    &mut symbols,
                                    &mut symbol_names,
                                )?;
                                declare_symbol(
                                    &sentence.initializer.symbol,
                                    &mut symbols,
                                    &mut symbol_names,
                                )?;
                            }
                            ConfigurationSentence::Fixed(sentence) => {
                                insert_node(&mut nodes, sentence.initializer_origin().key())?;
                                collect_definition_fixed_configuration(
                                    sentence,
                                    &mut symbols,
                                    &mut symbol_names,
                                    &mut nodes,
                                )?;
                            }
                        }
                    }
                    DefinitionSentence::ContextAlias(sentence) => {
                        if sentence.id.item_kind() != ItemKind::ContextAlias
                            || !context_aliases.insert(sentence.id.clone())
                        {
                            return Err(DefinitionValidationError::AdapterSpecificValue(
                                "context alias identity",
                            ));
                        }
                        insert_node(&mut nodes, sentence.name_origin.key())?;
                        insert_node(&mut nodes, sentence.here_origin.key())?;
                    }
                    DefinitionSentence::Rule(sentence) => {
                        validate_label_text(&sentence.label)?;
                        if !labels.insert(sentence.label.id.clone()) {
                            return Err(DefinitionValidationError::DuplicateLabel(
                                sentence.label.id.clone(),
                            ));
                        }
                        if !label_names.insert(sentence.label.emitted_name.clone()) {
                            return Err(DefinitionValidationError::DuplicateEmittedName(
                                sentence.label.emitted_name.clone(),
                            ));
                        }
                    }
                }
            }
        }
        if !modules.contains(&self.main_module) {
            return Err(DefinitionValidationError::DanglingModule(
                self.main_module.clone(),
            ));
        }
        if configurations != 1 {
            return Err(DefinitionValidationError::ConfigurationCount(
                configurations,
            ));
        }
        let fixed_configuration = self.modules.iter().find_map(|module| {
            module.sentences.iter().find_map(|sentence| match sentence {
                DefinitionSentence::Configuration(configuration) => configuration.as_fixed(),
                _ => None,
            })
        });

        for module in &self.modules {
            for import in &module.imports {
                if !modules.contains(import) {
                    return Err(DefinitionValidationError::DanglingModule(import.clone()));
                }
            }
            for sentence in &module.sentences {
                match sentence {
                    DefinitionSentence::SyntaxSort(sentence) => {
                        require_declared_kind(&symbols, sentence.symbol.id(), SymbolKind::Sort)?;
                    }
                    DefinitionSentence::Subsort(sentence) => {
                        require_definition_sort(&symbols, &sentence.subsort)?;
                        require_definition_sort(&symbols, &sentence.supersort)?;
                    }
                    DefinitionSentence::Production(sentence) => {
                        validate_production(sentence, &symbols, &groups, &context_aliases)?;
                    }
                    DefinitionSentence::Precedence(sentence) => {
                        for group in sentence.higher().iter().chain(sentence.lower()) {
                            require_definition_group(&groups, group)?;
                        }
                    }
                    DefinitionSentence::Associativity(sentence) => {
                        for group in sentence.groups() {
                            require_definition_group(&groups, group)?;
                        }
                    }
                    DefinitionSentence::Configuration(sentence) => validate_configuration(
                        sentence,
                        &symbols,
                        &production_signatures,
                        &subsort_parents,
                        &mut nodes,
                    )?,
                    DefinitionSentence::ContextAlias(sentence) => validate_context_alias(
                        sentence,
                        &symbols,
                        &production_signatures,
                        &subsort_parents,
                        &mut nodes,
                    )?,
                    DefinitionSentence::Rule(sentence) => {
                        validate_rule(
                            sentence,
                            fixed_configuration,
                            &symbols,
                            &production_signatures,
                            &functional_productions,
                            &alias_productions,
                            &subsort_parents,
                            &mut nodes,
                        )?;
                    }
                }
            }
        }
        validate_definition_precedence_order(&self.modules)?;
        validate_definition_subsort_order(&subsort_parents)?;
        Ok(())
    }
}

/// One generated K module.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DefinitionModule {
    origin: NodeOrigin,
    id: ModuleId,
    imports: Vec<ModuleId>,
    production_groups: Vec<ProductionGroupIdentity>,
    sentences: Vec<DefinitionSentence>,
}

impl DefinitionModule {
    /// Creates a module. Imports and sentences are set-valued at this stage.
    #[must_use]
    pub const fn new(
        origin: NodeOrigin,
        id: ModuleId,
        imports: Vec<ModuleId>,
        production_groups: Vec<ProductionGroupIdentity>,
        sentences: Vec<DefinitionSentence>,
    ) -> Self {
        Self {
            origin,
            id,
            imports,
            production_groups,
            sentences,
        }
    }
    /// Returns node provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns the generated module ID.
    #[must_use]
    pub const fn id(&self) -> &ModuleId {
        &self.id
    }
    /// Returns imported module IDs.
    #[must_use]
    pub fn imports(&self) -> &[ModuleId] {
        &self.imports
    }
    /// Returns compiler-owned emitted identities for nominal production groups.
    #[must_use]
    pub fn production_groups(&self) -> &[ProductionGroupIdentity] {
        &self.production_groups
    }
    /// Returns source-level K sentences.
    #[must_use]
    pub fn sentences(&self) -> &[DefinitionSentence] {
        &self.sentences
    }
    fn canonicalize(&mut self) {
        self.imports.sort();
        self.imports.dedup();
        self.production_groups
            .sort_by(|left, right| left.id.cmp(&right.id));
        self.sentences
            .sort_by(|left, right| left.origin().key().cmp(right.origin().key()));
    }
}

/// One source-level K sentence.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(tag = "sentence_kind", content = "sentence", rename_all = "snake_case")]
// This is a serialized public sum type. Boxing only the largest sentence would
// change its Rust construction API without reducing any serialized payload.
#[allow(clippy::large_enum_variant)]
pub enum DefinitionSentence {
    /// Syntax sort declaration.
    SyntaxSort(SyntaxSortSentence),
    /// Direct source-level subsort production.
    Subsort(SubsortSentence),
    /// Constructor production.
    Production(ProductionSentence),
    /// One direct production-group precedence edge.
    Precedence(PrecedenceRelation),
    /// Group associativity metadata.
    Associativity(GroupAssociativitySentence),
    /// Fixed configuration and initializer.
    Configuration(ConfigurationSentence),
    /// One-sided reusable context template.
    ContextAlias(ContextAliasSentence),
    /// Rule/equation/claim sentence.
    Rule(RuleSentence),
}

impl DefinitionSentence {
    /// Returns the mandatory sentence origin.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        match self {
            Self::SyntaxSort(value) => &value.origin,
            Self::Subsort(value) => &value.origin,
            Self::Production(value) => &value.origin,
            Self::Precedence(value) => value.origin(),
            Self::Associativity(value) => value.origin(),
            Self::Configuration(value) => value.origin(),
            Self::ContextAlias(value) => &value.origin,
            Self::Rule(value) => &value.origin,
        }
    }
}

/// One source-level reusable one-sided fixed-configuration context template.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ContextAliasSentence {
    origin: NodeOrigin,
    id: StableItemId,
    name_origin: NodeOrigin,
    name: String,
    here_origin: NodeOrigin,
    here: SemanticId,
    variables: Vec<DefinitionVariable>,
    body: FixedConfigurationPattern<SymbolId, DefinitionTerm>,
}

impl ContextAliasSentence {
    /// Creates one already-validated context-alias sentence.
    #[must_use]
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        origin: NodeOrigin,
        id: StableItemId,
        name_origin: NodeOrigin,
        name: String,
        here_origin: NodeOrigin,
        here: SemanticId,
        variables: Vec<DefinitionVariable>,
        body: FixedConfigurationPattern<SymbolId, DefinitionTerm>,
    ) -> Self {
        Self {
            origin,
            id,
            name_origin,
            name,
            here_origin,
            here,
            variables,
            body,
        }
    }
    /// Returns declaration provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns stable declaration identity.
    #[must_use]
    pub const fn id(&self) -> &StableItemId {
        &self.id
    }
    /// Returns alias-name provenance.
    #[must_use]
    pub const fn name_origin(&self) -> &NodeOrigin {
        &self.name_origin
    }
    /// Returns the exact emitted alias name.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }
    /// Returns HERE occurrence provenance.
    #[must_use]
    pub const fn here_origin(&self) -> &NodeOrigin {
        &self.here_origin
    }
    /// Returns the selected HERE binding.
    #[must_use]
    pub const fn here(&self) -> &SemanticId {
        &self.here
    }
    /// Returns typed variables.
    #[must_use]
    pub fn variables(&self) -> &[DefinitionVariable] {
        &self.variables
    }
    /// Returns the one-sided fixed-configuration pattern.
    #[must_use]
    pub const fn body(&self) -> &FixedConfigurationPattern<SymbolId, DefinitionTerm> {
        &self.body
    }
}

/// Compiler-owned emitted identity for one nominal production group.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProductionGroupIdentity {
    origin: NodeOrigin,
    id: ProductionGroupId,
    emitted_name: String,
}

impl ProductionGroupIdentity {
    /// Creates a target-neutral group identity and chosen K tag.
    ///
    /// # Errors
    ///
    /// Returns [`DefinitionValidationError`] for blank or path-shaped names.
    pub fn new(
        origin: NodeOrigin,
        id: ProductionGroupId,
        emitted_name: impl Into<String>,
    ) -> Result<Self, DefinitionValidationError> {
        let emitted_name = emitted_name.into();
        if emitted_name.trim().is_empty() {
            return Err(DefinitionValidationError::EmptyText(
                "production group name",
            ));
        }
        if emitted_name.contains(['/', '\\']) {
            return Err(DefinitionValidationError::AdapterSpecificValue(
                "production group name",
            ));
        }
        Ok(Self {
            origin,
            id,
            emitted_name,
        })
    }
    /// Returns identity provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns the stable group identity.
    #[must_use]
    pub const fn id(&self) -> &ProductionGroupId {
        &self.id
    }
    /// Returns the shared-lowering-selected emitted K tag.
    #[must_use]
    pub fn emitted_name(&self) -> &str {
        &self.emitted_name
    }
}

/// A direct source-level subsort production without a generated term symbol.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SubsortSentence {
    origin: NodeOrigin,
    subsort: DefinitionSortRef,
    supersort: DefinitionSortRef,
}

impl SubsortSentence {
    /// Declares one direct subsort edge.
    #[must_use]
    pub const fn new(
        origin: NodeOrigin,
        subsort: DefinitionSortRef,
        supersort: DefinitionSortRef,
    ) -> Self {
        Self {
            origin,
            subsort,
            supersort,
        }
    }

    /// Returns sentence provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns the smaller sort.
    #[must_use]
    pub const fn subsort(&self) -> &DefinitionSortRef {
        &self.subsort
    }
    /// Returns the larger sort.
    #[must_use]
    pub const fn supersort(&self) -> &DefinitionSortRef {
        &self.supersort
    }
}

/// Syntax sort sentence.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SyntaxSortSentence {
    origin: NodeOrigin,
    symbol: SymbolIdentity,
}
impl SyntaxSortSentence {
    /// Declares a generated sort symbol.
    ///
    /// # Errors
    ///
    /// Returns [`DefinitionValidationError`] when the symbol is not a sort.
    pub fn new(
        origin: NodeOrigin,
        symbol: SymbolIdentity,
    ) -> Result<Self, DefinitionValidationError> {
        expect_symbol_kind(&symbol, SymbolKind::Sort)?;
        Ok(Self { origin, symbol })
    }
    /// Returns sentence provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns the sort symbol declaration.
    #[must_use]
    pub const fn symbol(&self) -> &SymbolIdentity {
        &self.symbol
    }
}

/// Nominal production sentence.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProductionSentence {
    origin: NodeOrigin,
    symbol: SymbolIdentity,
    result_sort: DefinitionSortRef,
    items: Vec<ProductionItem>,
    attributes: Vec<DefinitionProductionAttribute>,
}

impl ProductionSentence {
    /// Creates a production. Item order is preserved.
    ///
    /// # Errors
    ///
    /// Returns [`DefinitionValidationError`] for a wrong-kind symbol or no items.
    pub fn new(
        origin: NodeOrigin,
        symbol: SymbolIdentity,
        result_sort: DefinitionSortRef,
        items: Vec<ProductionItem>,
        attributes: Vec<DefinitionProductionAttribute>,
    ) -> Result<Self, DefinitionValidationError> {
        expect_symbol_kind(&symbol, SymbolKind::Production)?;
        if items.is_empty() {
            return Err(DefinitionValidationError::EmptyProduction(
                symbol.id.clone(),
            ));
        }
        validate_definition_production_shape(symbol.id(), &items, &attributes)?;
        Ok(Self {
            origin,
            symbol,
            result_sort,
            items,
            attributes,
        })
    }
    /// Returns sentence provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns the single symbol declaration.
    #[must_use]
    pub const fn symbol(&self) -> &SymbolIdentity {
        &self.symbol
    }
    /// Returns the result sort reference.
    #[must_use]
    pub const fn result_sort(&self) -> &DefinitionSortRef {
        &self.result_sort
    }
    /// Returns ordered terminals/nonterminals.
    #[must_use]
    pub fn items(&self) -> &[ProductionItem] {
        &self.items
    }
    /// Returns classified production metadata.
    #[must_use]
    pub fn attributes(&self) -> &[DefinitionProductionAttribute] {
        &self.attributes
    }
}

/// Exactly-one fixed computation cell.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CellDeclaration {
    origin: NodeOrigin,
    symbol: SymbolIdentity,
    content_sort: DefinitionSortRef,
}
impl CellDeclaration {
    /// Creates a fixed cell symbol declaration.
    ///
    /// # Errors
    ///
    /// Returns [`DefinitionValidationError`] when the symbol is not a cell.
    pub fn new(
        origin: NodeOrigin,
        symbol: SymbolIdentity,
        content_sort: DefinitionSortRef,
    ) -> Result<Self, DefinitionValidationError> {
        expect_symbol_kind(&symbol, SymbolKind::Cell)?;
        Ok(Self {
            origin,
            symbol,
            content_sort,
        })
    }
    /// Returns its origin.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns its symbol declaration.
    #[must_use]
    pub const fn symbol(&self) -> &SymbolIdentity {
        &self.symbol
    }
    /// Returns the cell content sort.
    #[must_use]
    pub const fn content_sort(&self) -> &DefinitionSortRef {
        &self.content_sort
    }
}

/// Declarative initializer symbol and body.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct InitializerDeclaration {
    origin: NodeOrigin,
    symbol: SymbolIdentity,
    variables: Vec<DefinitionVariable>,
    body: DefinitionTerm,
}
impl InitializerDeclaration {
    /// Creates an initializer; variable order is semantic.
    ///
    /// # Errors
    ///
    /// Returns [`DefinitionValidationError`] when the symbol is not an initializer.
    pub fn new(
        origin: NodeOrigin,
        symbol: SymbolIdentity,
        variables: Vec<DefinitionVariable>,
        body: DefinitionTerm,
    ) -> Result<Self, DefinitionValidationError> {
        expect_symbol_kind(&symbol, SymbolKind::Initializer)?;
        Ok(Self {
            origin,
            symbol,
            variables,
            body,
        })
    }
    /// Returns its origin.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns its generated symbol.
    #[must_use]
    pub const fn symbol(&self) -> &SymbolIdentity {
        &self.symbol
    }
    /// Returns ordered variables.
    #[must_use]
    pub fn variables(&self) -> &[DefinitionVariable] {
        &self.variables
    }
    /// Returns its structured body.
    #[must_use]
    pub const fn body(&self) -> &DefinitionTerm {
        &self.body
    }
}

/// Legacy M2 or general fixed/nested source configuration sentence.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(untagged)]
pub enum ConfigurationSentence {
    /// Compatibility representation for the original one-cell M2 form.
    Legacy(LegacyConfigurationSentence),
    /// General M3B fixed/nested configuration.
    Fixed(FixedConfiguration<DefinitionSortRef, SymbolId, DefinitionTerm>),
}

/// Legacy M2 one-cell source configuration.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LegacyConfigurationSentence {
    origin: NodeOrigin,
    cell: CellDeclaration,
    initializer: InitializerDeclaration,
}
impl ConfigurationSentence {
    /// Creates the M2 one-cell configuration.
    #[must_use]
    pub const fn new(
        origin: NodeOrigin,
        cell: CellDeclaration,
        initializer: InitializerDeclaration,
    ) -> Self {
        Self::Legacy(LegacyConfigurationSentence {
            origin,
            cell,
            initializer,
        })
    }
    /// Wraps one general fixed/nested configuration.
    #[must_use]
    pub const fn fixed(
        configuration: FixedConfiguration<DefinitionSortRef, SymbolId, DefinitionTerm>,
    ) -> Self {
        Self::Fixed(configuration)
    }
    /// Returns sentence provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        match self {
            Self::Legacy(value) => &value.origin,
            Self::Fixed(value) => value.origin(),
        }
    }
    /// Returns the legacy cell, when this is the M2 form.
    #[must_use]
    pub const fn cell(&self) -> Option<&CellDeclaration> {
        match self {
            Self::Legacy(value) => Some(&value.cell),
            Self::Fixed(_) => None,
        }
    }
    /// Returns the legacy initializer, when this is the M2 form.
    #[must_use]
    pub const fn initializer(&self) -> Option<&InitializerDeclaration> {
        match self {
            Self::Legacy(value) => Some(&value.initializer),
            Self::Fixed(_) => None,
        }
    }
    /// Returns the general fixed configuration, when present.
    #[must_use]
    pub const fn as_fixed(
        &self,
    ) -> Option<&FixedConfiguration<DefinitionSortRef, SymbolId, DefinitionTerm>> {
        match self {
            Self::Legacy(_) => None,
            Self::Fixed(value) => Some(value),
        }
    }
}

/// Definition-level variable declaration.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DefinitionVariable {
    id: SemanticId,
    sort: DefinitionSortRef,
}
impl DefinitionVariable {
    /// Declares a variable.
    #[must_use]
    pub const fn new(id: SemanticId, sort: DefinitionSortRef) -> Self {
        Self { id, sort }
    }
    /// Returns its stable ID.
    #[must_use]
    pub const fn id(&self) -> &SemanticId {
        &self.id
    }
    /// Returns its sort.
    #[must_use]
    pub const fn sort(&self) -> &DefinitionSortRef {
        &self.sort
    }
}

/// One provenance-bearing object-language Boolean rule condition.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DefinitionRuleCondition {
    origin: NodeOrigin,
    term: DefinitionTerm,
}

/// One explicitly scoped Definition claim binder.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DefinitionClaimBinder {
    origin: NodeOrigin,
    name_origin: NodeOrigin,
    id: SemanticId,
    sort_origin: NodeOrigin,
    sort: DefinitionSortRef,
}

/// Typed Definition claim adjunct metadata.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DefinitionClaim {
    modality_origin: NodeOrigin,
    modality: crate::ClaimModality,
    #[serde(skip_serializing_if = "Option::is_none")]
    circularity_origin: Option<NodeOrigin>,
    universals: Vec<DefinitionClaimBinder>,
    existentials: Vec<DefinitionClaimBinder>,
    #[serde(skip_serializing_if = "Option::is_none")]
    ensures: Option<DefinitionRuleCondition>,
}

impl DefinitionClaimBinder {
    /// Creates one typed scoped binder.
    #[must_use]
    pub const fn new(
        origin: NodeOrigin,
        name_origin: NodeOrigin,
        id: SemanticId,
        sort_origin: NodeOrigin,
        sort: DefinitionSortRef,
    ) -> Self {
        Self {
            origin,
            name_origin,
            id,
            sort_origin,
            sort,
        }
    }
    /// Declaration provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Name provenance.
    #[must_use]
    pub const fn name_origin(&self) -> &NodeOrigin {
        &self.name_origin
    }
    /// Stable binder identity.
    #[must_use]
    pub const fn id(&self) -> &SemanticId {
        &self.id
    }
    /// Sort provenance.
    #[must_use]
    pub const fn sort_origin(&self) -> &NodeOrigin {
        &self.sort_origin
    }
    /// Definition sort.
    #[must_use]
    pub const fn sort(&self) -> &DefinitionSortRef {
        &self.sort
    }
}

impl DefinitionClaim {
    /// Creates typed claim metadata.
    #[must_use]
    pub const fn new(
        modality_origin: NodeOrigin,
        modality: crate::ClaimModality,
        circularity_origin: Option<NodeOrigin>,
        universals: Vec<DefinitionClaimBinder>,
        existentials: Vec<DefinitionClaimBinder>,
        ensures: Option<DefinitionRuleCondition>,
    ) -> Self {
        Self {
            modality_origin,
            modality,
            circularity_origin,
            universals,
            existentials,
            ensures,
        }
    }
    /// Modality provenance.
    #[must_use]
    pub const fn modality_origin(&self) -> &NodeOrigin {
        &self.modality_origin
    }
    /// Reachability modality.
    #[must_use]
    pub const fn modality(&self) -> crate::ClaimModality {
        self.modality
    }
    /// Circularity provenance.
    #[must_use]
    pub const fn circularity_origin(&self) -> Option<&NodeOrigin> {
        self.circularity_origin.as_ref()
    }
    /// Universal binders.
    #[must_use]
    pub fn universals(&self) -> &[DefinitionClaimBinder] {
        &self.universals
    }
    /// Existential binders.
    #[must_use]
    pub fn existentials(&self) -> &[DefinitionClaimBinder] {
        &self.existentials
    }
    /// Object-Bool postcondition.
    #[must_use]
    pub const fn ensures(&self) -> Option<&DefinitionRuleCondition> {
        self.ensures.as_ref()
    }
}

/// One explicit equation priority.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DefinitionRulePriority {
    origin: NodeOrigin,
    value: u32,
}

/// Simplifier classification and optional ordering hint.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DefinitionSimplification {
    origin: NodeOrigin,
    #[serde(skip_serializing_if = "Option::is_none")]
    priority: Option<DefinitionSimplificationPriority>,
}

/// One numeric simplification ordering hint.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DefinitionSimplificationPriority {
    origin: NodeOrigin,
    value: u32,
}

impl DefinitionSimplification {
    /// Creates typed simplification metadata.
    #[must_use]
    pub const fn new(
        origin: NodeOrigin,
        priority: Option<DefinitionSimplificationPriority>,
    ) -> Self {
        Self { origin, priority }
    }
    /// Returns marker provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns the optional numeric hint.
    #[must_use]
    pub const fn priority(&self) -> Option<&DefinitionSimplificationPriority> {
        self.priority.as_ref()
    }
}

impl DefinitionSimplificationPriority {
    /// Creates a provenance-bearing hint.
    #[must_use]
    pub const fn new(origin: NodeOrigin, value: u32) -> Self {
        Self { origin, value }
    }
    /// Returns hint provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns the numeric hint.
    #[must_use]
    pub const fn value(&self) -> u32 {
        self.value
    }
}

impl DefinitionRulePriority {
    /// Creates a provenance-bearing priority.
    #[must_use]
    pub const fn new(origin: NodeOrigin, value: u32) -> Self {
        Self { origin, value }
    }
    /// Returns priority provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns the explicit numeric priority.
    #[must_use]
    pub const fn value(&self) -> u32 {
        self.value
    }
}

impl DefinitionRuleCondition {
    /// Creates a typed condition while retaining complete payload provenance.
    #[must_use]
    pub const fn new(origin: NodeOrigin, term: DefinitionTerm) -> Self {
        Self { origin, term }
    }
    /// Returns complete condition-payload provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns the structured object-language condition term.
    #[must_use]
    pub const fn term(&self) -> &DefinitionTerm {
        &self.term
    }
}

/// Rule, equation, or claim sentence.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RuleSentence {
    origin: NodeOrigin,
    label: LabelIdentity,
    kind: SentenceKind,
    variables: Vec<DefinitionVariable>,
    #[serde(skip_serializing_if = "Option::is_none")]
    requires: Option<DefinitionRuleCondition>,
    #[serde(skip_serializing_if = "Option::is_none")]
    priority: Option<DefinitionRulePriority>,
    #[serde(skip_serializing_if = "Option::is_none")]
    simplification: Option<DefinitionSimplification>,
    #[serde(skip_serializing_if = "Option::is_none")]
    claim: Option<DefinitionClaim>,
    body: DefinitionRuleBody,
}

/// Structured relational body of one ordinary labeled Definition rule.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(untagged)]
pub enum DefinitionRuleBody {
    /// One ordinary term rewrite.
    Term(DefinitionTerm),
    /// One simultaneous fixed-configuration rewrite.
    Configuration(FixedConfigurationRewrite<SymbolId, DefinitionTerm>),
}
impl RuleSentence {
    /// Creates a sentence whose body must be a structured rewrite.
    ///
    /// # Errors
    ///
    /// Returns [`DefinitionValidationError`] when the body is not a rewrite.
    pub fn new(
        origin: NodeOrigin,
        label: LabelIdentity,
        kind: SentenceKind,
        variables: Vec<DefinitionVariable>,
        body: DefinitionTerm,
    ) -> Result<Self, DefinitionValidationError> {
        if !matches!(body.kind, DefinitionTermKind::Rewrite { .. }) {
            return Err(DefinitionValidationError::RuleBodyNotRewrite(
                label.id.clone(),
            ));
        }
        Ok(Self {
            origin,
            label,
            kind,
            variables,
            requires: None,
            priority: None,
            simplification: None,
            claim: None,
            body: DefinitionRuleBody::Term(body),
        })
    }
    /// Creates an ordinary labeled simultaneous fixed-configuration rule.
    #[must_use]
    pub const fn new_configuration(
        origin: NodeOrigin,
        label: LabelIdentity,
        kind: SentenceKind,
        variables: Vec<DefinitionVariable>,
        body: FixedConfigurationRewrite<SymbolId, DefinitionTerm>,
    ) -> Self {
        Self {
            origin,
            label,
            kind,
            variables,
            requires: None,
            priority: None,
            simplification: None,
            claim: None,
            body: DefinitionRuleBody::Configuration(body),
        }
    }
    /// Returns sentence provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns the single generated label declaration.
    #[must_use]
    pub const fn label(&self) -> &LabelIdentity {
        &self.label
    }
    /// Returns the explicit sentence kind.
    #[must_use]
    pub const fn kind(&self) -> SentenceKind {
        self.kind
    }
    /// Attaches an explicit equation priority.
    ///
    /// # Errors
    ///
    /// Returns [`DefinitionValidationError::InvalidRulePriority`] when
    /// priority metadata is attached to anything other than an equation.
    pub fn with_priority(
        mut self,
        priority: Option<DefinitionRulePriority>,
    ) -> Result<Self, DefinitionValidationError> {
        if priority.is_some() && self.kind != SentenceKind::Equation {
            return Err(DefinitionValidationError::InvalidRulePriority(
                self.label.id.clone(),
            ));
        }
        self.priority = priority;
        Ok(self)
    }
    /// Returns the explicit priority.
    #[must_use]
    pub const fn priority(&self) -> Option<&DefinitionRulePriority> {
        self.priority.as_ref()
    }
    /// Attaches typed simplification metadata.
    #[must_use]
    pub fn with_simplification(mut self, value: Option<DefinitionSimplification>) -> Self {
        self.simplification = value;
        self
    }
    /// Returns typed simplification metadata.
    #[must_use]
    pub const fn simplification(&self) -> Option<&DefinitionSimplification> {
        self.simplification.as_ref()
    }
    /// Attaches typed claim-only metadata.
    #[must_use]
    pub fn with_claim(mut self, claim: Option<DefinitionClaim>) -> Self {
        self.claim = claim;
        self
    }
    /// Returns typed claim-only metadata.
    #[must_use]
    pub const fn claim(&self) -> Option<&DefinitionClaim> {
        self.claim.as_ref()
    }
    /// Returns variables in binder order.
    #[must_use]
    pub fn variables(&self) -> &[DefinitionVariable] {
        &self.variables
    }
    /// Attaches an object-language Boolean applicability condition.
    ///
    /// # Errors
    ///
    /// Returns [`DefinitionValidationError::RuleConditionSortMismatch`] unless
    /// the condition has exactly the builtin `Bool` sort.
    pub fn with_requires(
        mut self,
        requires: Option<DefinitionRuleCondition>,
    ) -> Result<Self, DefinitionValidationError> {
        if requires.as_ref().is_some_and(|condition| {
            condition.term().sort() != &DefinitionSortRef::Builtin(BuiltinSort::Bool)
        }) {
            return Err(DefinitionValidationError::RuleConditionSortMismatch);
        }
        self.requires = requires;
        Ok(self)
    }
    /// Returns the object-language Boolean applicability condition.
    #[must_use]
    pub const fn requires(&self) -> Option<&DefinitionRuleCondition> {
        self.requires.as_ref()
    }
    /// Returns the legacy term rewrite body, when present.
    #[must_use]
    pub const fn body(&self) -> Option<&DefinitionTerm> {
        match &self.body {
            DefinitionRuleBody::Term(value) => Some(value),
            DefinitionRuleBody::Configuration(_) => None,
        }
    }
    /// Returns the typed relational body.
    #[must_use]
    pub const fn relational_body(&self) -> &DefinitionRuleBody {
        &self.body
    }
}

/// Structured K term with mandatory nested provenance.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub struct DefinitionTerm {
    origin: NodeOrigin,
    sort: DefinitionSortRef,
    #[serde(flatten)]
    kind: DefinitionTermKind,
}
impl DefinitionTerm {
    /// Creates a variable reference.
    #[must_use]
    pub const fn variable(
        origin: NodeOrigin,
        sort: DefinitionSortRef,
        variable: SemanticId,
    ) -> Self {
        Self {
            origin,
            sort,
            kind: DefinitionTermKind::Variable { variable },
        }
    }
    /// Creates an application referencing a symbol declared elsewhere.
    #[must_use]
    pub const fn application(
        origin: NodeOrigin,
        sort: DefinitionSortRef,
        application: DefinitionApplicationRef,
        arguments: Vec<Self>,
    ) -> Self {
        Self {
            origin,
            sort,
            kind: DefinitionTermKind::Application {
                application,
                arguments,
            },
        }
    }
    /// Creates a nonempty domain token.
    ///
    /// # Errors
    ///
    /// Returns [`DefinitionValidationError`] for an empty token payload.
    pub fn token(
        origin: NodeOrigin,
        sort: DefinitionSortRef,
        value: impl Into<String>,
    ) -> Result<Self, DefinitionValidationError> {
        let value = value.into();
        if value.is_empty() {
            return Err(DefinitionValidationError::EmptyText("token value"));
        }
        Ok(Self {
            origin,
            sort,
            kind: DefinitionTermKind::Token { value },
        })
    }
    /// Creates a sorted rewrite. Whole-definition validation requires both
    /// endpoint sorts to inject into the declared rewrite sort.
    ///
    /// # Errors
    ///
    /// Returns no local shape error; subsorting is a whole-definition property.
    pub fn rewrite(
        origin: NodeOrigin,
        sort: DefinitionSortRef,
        from: Self,
        to: Self,
    ) -> Result<Self, DefinitionValidationError> {
        Ok(Self {
            origin,
            sort,
            kind: DefinitionTermKind::Rewrite {
                from: Box::new(from),
                to: Box::new(to),
            },
        })
    }
    /// Creates an explicit source-level K computation sequence. Per-item sort
    /// injections remain the responsibility of the K frontend.
    #[must_use]
    pub const fn k_sequence(
        origin: NodeOrigin,
        item_sort: DefinitionSortRef,
        items: Vec<Self>,
    ) -> Self {
        Self {
            origin,
            sort: DefinitionSortRef::Builtin(BuiltinSort::KSequence),
            kind: DefinitionTermKind::KSequence { item_sort, items },
        }
    }
    /// Creates one structured finite-map operation.
    #[must_use]
    pub const fn map(origin: NodeOrigin, operation: MapOperation, arguments: Vec<Self>) -> Self {
        Self {
            origin,
            sort: DefinitionSortRef::Builtin(BuiltinSort::Map),
            kind: DefinitionTermKind::Map {
                operation,
                arguments,
            },
        }
    }
    /// Creates one structured builtin-List operation.
    #[must_use]
    pub const fn list(
        origin: NodeOrigin,
        sort: DefinitionSortRef,
        operation: ListOperation,
        arguments: Vec<Self>,
    ) -> Self {
        Self {
            origin,
            sort,
            kind: DefinitionTermKind::List {
                operation,
                arguments,
            },
        }
    }
    /// Returns mandatory provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns the declared sort reference.
    #[must_use]
    pub const fn sort(&self) -> &DefinitionSortRef {
        &self.sort
    }
    /// Returns the structured form.
    #[must_use]
    pub const fn kind(&self) -> &DefinitionTermKind {
        &self.kind
    }
}

/// Definition term forms. No adapter production IDs, KAST metadata, or KORE
/// nodes can be represented here.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(tag = "term_kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum DefinitionTermKind {
    /// Variable reference.
    Variable {
        /// Stable binder identity.
        variable: SemanticId,
    },
    /// Symbol application with ordered arguments.
    Application {
        /// Referenced authored or compiler-provided application.
        application: DefinitionApplicationRef,
        /// Arguments in declared nonterminal order.
        arguments: Vec<DefinitionTerm>,
    },
    /// Domain token.
    Token {
        /// Exact token payload.
        value: String,
    },
    /// Explicit ordered K computation sequence.
    KSequence {
        /// Declared item sort (`KItem`) used by the sequence.
        item_sort: DefinitionSortRef,
        /// Items in computation order.
        items: Vec<DefinitionTerm>,
    },
    /// Structured finite-map operation or associative item pattern.
    Map {
        /// Exact target-neutral map operation.
        operation: MapOperation,
        /// Ordered operands; key/value terms retain their own sorts.
        arguments: Vec<DefinitionTerm>,
    },
    /// Structured builtin-List operation.
    List {
        /// Exact target-neutral List operation.
        operation: ListOperation,
        /// Ordered operands; item values retain their own sorts.
        arguments: Vec<DefinitionTerm>,
    },
    /// Relational rewrite.
    Rewrite {
        /// Pre-pattern.
        from: Box<DefinitionTerm>,
        /// Post-term.
        to: Box<DefinitionTerm>,
    },
}

/// Typed Definition IR validation failure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DefinitionValidationError {
    /// No module exists.
    EmptyDefinition,
    /// Blank text is not representable.
    EmptyText(&'static str),
    /// A path-shaped or adapter-shaped value attempted to cross the boundary.
    AdapterSpecificValue(&'static str),
    /// A module ID was duplicated.
    DuplicateModule(ModuleId),
    /// A source-map key was duplicated.
    DuplicateSourceMapKey(SourceMapKey),
    /// A generated symbol ID was duplicated.
    DuplicateSymbol(SymbolId),
    /// A generated label ID was duplicated.
    DuplicateLabel(LabelId),
    /// Two declarations chose the same emitted name.
    DuplicateEmittedName(String),
    /// A production group identity was declared twice.
    DuplicateProductionGroup(ProductionGroupId),
    /// A grammar sentence or production references an undeclared group.
    DanglingProductionGroup(ProductionGroupId),
    /// The strict production-group precedence relation contains a cycle.
    PrecedenceCycle(ProductionGroupId),
    /// The strict subsort relation contained a cycle.
    SubsortCycle(DefinitionSortRef),
    /// An import or main-module reference is dangling.
    DanglingModule(ModuleId),
    /// A symbol reference is dangling.
    DanglingSymbol(SymbolId),
    /// A symbol is used in the wrong role.
    WrongSymbolKind {
        /// Referenced symbol.
        id: SymbolId,
        /// Required symbol role.
        expected: SymbolKind,
        /// Declared symbol role.
        actual: SymbolKind,
    },
    /// M2 requires exactly one configuration.
    ConfigurationCount(usize),
    /// A production has no terminal/nonterminal items.
    EmptyProduction(SymbolId),
    /// The same classified attribute family occurred more than once.
    DuplicateProductionAttribute(&'static str),
    /// Token metadata was attached to a non-regex production.
    InvalidTokenProduction,
    /// A regex terminal lacked token metadata.
    RegexWithoutToken,
    /// Strictness named no field or an unknown/repeated field.
    InvalidStrictnessField,
    /// Format metadata was empty or referenced a nonexistent item.
    InvalidFormat,
    /// A bracket production did not contain exactly one nonterminal.
    InvalidBracketProduction,
    /// Total metadata occurred without function metadata.
    InvalidFunctionProduction,
    /// Alias and function metadata occurred on the same production.
    InvalidAliasProduction,
    /// A variable is declared twice.
    DuplicateVariable(SemanticId),
    /// A variable term is unbound.
    DanglingVariable(SemanticId),
    /// A variable term has a mismatched sort.
    VariableSortMismatch(SemanticId),
    /// Declared variables and variables used by a sentence differ.
    VariableClosure,
    /// An application does not match the declared production.
    ApplicationSignature(SymbolId),
    /// A compiler-provided operation application has the wrong signature.
    BuiltinApplicationSignature(BuiltinOperation),
    /// Rewrite endpoint sorts differ.
    RewriteSortMismatch,
    /// A K sequence node did not carry the builtin computation sort.
    SequenceSortMismatch,
    /// A K sequence item is not a subsort of the declared item sort.
    SequenceItemSortMismatch,
    /// A rule body is not a rewrite.
    RuleBodyNotRewrite(LabelId),
    /// An equation left-hand side is not headed by an authored function.
    InvalidEquationRoot(LabelId),
    /// An alias left-hand side is not headed by an authored alias production.
    InvalidAliasRoot(LabelId),
    /// A simplification left-hand side is not headed by a function or builtin function.
    InvalidSimplificationRoot(LabelId),
    /// Simplification metadata disagrees with the sentence kind.
    InvalidSimplificationMetadata(LabelId),
    /// Equation priority metadata occurred on another sentence kind.
    InvalidRulePriority(LabelId),
    /// Claim metadata presence disagrees with the sentence kind.
    InvalidClaimMetadata(LabelId),
    /// A claim used an ordinary term rewrite instead of a configuration rewrite.
    ClaimBodyNotConfiguration(LabelId),
    /// A claim binder is repeated, absent from the sentence scope, or has the wrong sort.
    InvalidClaimBinder(SemanticId),
    /// An existential binder occurs in the claim's left-hand side or `requires` condition.
    ExistentialScopeViolation(SemanticId),
    /// An existential binder is unused in the claim's right-hand side and `ensures` condition.
    UnusedExistential(SemanticId),
    /// A rule condition did not have exactly the builtin `Bool` sort.
    RuleConditionSortMismatch,
    /// A static alias clause carried a runtime condition.
    AliasCondition,
    /// Initializer result differs from cell content sort.
    InitializerSortMismatch,
    /// A structured fixed initializer did not mirror its declaration tree.
    InitializerTreeMismatch,
    /// A structured initializer leaf term has the wrong sort.
    InitializerLeafSortMismatch,
    /// A Map term did not carry builtin Map sort.
    MapSortMismatch,
    /// A Map operation had the wrong arity or Map operand.
    MapOperationSignature(MapOperation),
    /// A List operation had the wrong result sort, arity, or operand sorts.
    ListOperationSignature(ListOperation),
    /// A configuration rule exists without a general fixed configuration.
    ConfigurationRuleWithoutFixedConfiguration(LabelId),
    /// A configuration rule names a different fixed configuration.
    ConfigurationRuleTargetMismatch(LabelId),
    /// A cell rule references a missing/non-leaf cell or incomplete frame.
    InvalidCellFraming,
    /// A cell-content frame is incompatible with its leaf sort.
    CellFrameSortMismatch,
    /// A named sequence/map frame binding is absent or has the wrong sort.
    CellFrameBindingMismatch(SemanticId),
}

impl fmt::Display for DefinitionValidationError {
    #[allow(clippy::too_many_lines)]
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyDefinition => formatter.write_str("Definition IR must contain a module"),
            Self::EmptyText(field) => write!(formatter, "{field} must not be empty"),
            Self::AdapterSpecificValue(field) => {
                write!(formatter, "{field} must be target-neutral and path-free")
            }
            Self::DuplicateModule(id) => write!(formatter, "duplicate module {:?}", id.as_str()),
            Self::DuplicateSourceMapKey(key) => {
                write!(formatter, "duplicate source-map key {:?}", key.as_str())
            }
            Self::DuplicateSymbol(id) => write!(formatter, "duplicate symbol {:?}", id.as_str()),
            Self::DuplicateLabel(id) => write!(formatter, "duplicate label {:?}", id.as_str()),
            Self::DuplicateEmittedName(name) => {
                write!(formatter, "duplicate emitted name {name:?}")
            }
            Self::DuplicateProductionGroup(group) => {
                write!(formatter, "duplicate production group {:?}", group.as_str())
            }
            Self::DanglingProductionGroup(group) => {
                write!(formatter, "dangling production group {:?}", group.as_str())
            }
            Self::PrecedenceCycle(group) => write!(
                formatter,
                "production-group precedence contains a cycle through {:?}",
                group.as_str()
            ),
            Self::SubsortCycle(sort) => {
                write!(
                    formatter,
                    "subsort relation contains a cycle through {sort:?}"
                )
            }
            Self::DanglingModule(id) => write!(formatter, "dangling module {:?}", id.as_str()),
            Self::DanglingSymbol(id) => write!(formatter, "dangling symbol {:?}", id.as_str()),
            Self::WrongSymbolKind {
                id,
                expected,
                actual,
            } => write!(
                formatter,
                "symbol {:?} has kind {actual:?}, expected {expected:?}",
                id.as_str()
            ),
            Self::ConfigurationCount(count) => write!(
                formatter,
                "Definition IR requires exactly one configuration, found {count}"
            ),
            Self::EmptyProduction(id) => write!(
                formatter,
                "production {:?} must contain syntax items",
                id.as_str()
            ),
            Self::DuplicateProductionAttribute(attribute) => {
                write!(formatter, "production repeats {attribute} metadata")
            }
            Self::InvalidTokenProduction => formatter.write_str(
                "token metadata requires exactly one regex item and no other grammar items",
            ),
            Self::RegexWithoutToken => {
                formatter.write_str("regex grammar items require classified token metadata")
            }
            Self::InvalidStrictnessField => formatter
                .write_str("strictness fields must be nonempty, distinct named nonterminals"),
            Self::InvalidFormat => formatter.write_str(
                "format metadata must be nonempty and reference existing production items",
            ),
            Self::InvalidBracketProduction => formatter
                .write_str("bracket metadata requires exactly one nonterminal grammar item"),
            Self::DuplicateVariable(id) => {
                write!(formatter, "duplicate variable {:?}", id.as_str())
            }
            Self::DanglingVariable(id) => write!(formatter, "dangling variable {:?}", id.as_str()),
            Self::VariableSortMismatch(id) => write!(
                formatter,
                "variable {:?} is referenced with the wrong sort",
                id.as_str()
            ),
            Self::VariableClosure => {
                formatter.write_str("declared variables must exactly match sentence uses")
            }
            Self::ApplicationSignature(id) => write!(
                formatter,
                "application does not match production {:?}",
                id.as_str()
            ),
            Self::BuiltinApplicationSignature(operation) => write!(
                formatter,
                "application does not match builtin signature {operation:?}"
            ),
            Self::RewriteSortMismatch => {
                formatter.write_str("rewrite endpoint sorts must equal the rewrite sort")
            }
            Self::SequenceSortMismatch => {
                formatter.write_str("K sequence term must have builtin K-sequence sort")
            }
            Self::SequenceItemSortMismatch => {
                formatter.write_str("K sequence item must be a subsort of its item sort")
            }
            Self::RuleBodyNotRewrite(id) => {
                write!(formatter, "rule {:?} body must be a rewrite", id.as_str())
            }
            Self::InvalidEquationRoot(id) => write!(
                formatter,
                "equation {:?} must be headed by a functional production",
                id.as_str()
            ),
            Self::InvalidAliasRoot(id) => write!(
                formatter,
                "alias clause {:?} must be headed by an alias production",
                id.as_str()
            ),
            Self::InvalidSimplificationRoot(id) => write!(
                formatter,
                "simplification {:?} must be headed by a function or builtin function",
                id.as_str()
            ),
            Self::InvalidSimplificationMetadata(id) => write!(
                formatter,
                "simplification metadata disagrees with sentence {:?}",
                id.as_str()
            ),
            Self::InvalidRulePriority(id) => write!(
                formatter,
                "equation priority cannot occur on non-equation sentence {:?}",
                id.as_str()
            ),
            Self::InvalidClaimMetadata(id) => write!(
                formatter,
                "claim metadata disagrees with sentence {:?}",
                id.as_str()
            ),
            Self::ClaimBodyNotConfiguration(id) => write!(
                formatter,
                "claim {:?} requires a configuration rewrite body",
                id.as_str()
            ),
            Self::InvalidClaimBinder(id) => write!(
                formatter,
                "claim binder {:?} is repeated, unbound, or has the wrong sort",
                id.as_str()
            ),
            Self::ExistentialScopeViolation(id) => write!(
                formatter,
                "existential claim binder {:?} cannot occur in the left-hand side or requires condition",
                id.as_str()
            ),
            Self::UnusedExistential(id) => write!(
                formatter,
                "existential claim binder {:?} must occur in the right-hand side or ensures condition",
                id.as_str()
            ),
            Self::RuleConditionSortMismatch => {
                formatter.write_str("rule condition must have builtin Bool sort")
            }
            Self::AliasCondition => {
                formatter.write_str("static alias clauses cannot carry requires conditions")
            }
            Self::InvalidFunctionProduction => {
                formatter.write_str("total metadata requires function metadata")
            }
            Self::InvalidAliasProduction => {
                formatter.write_str("alias metadata cannot be combined with function metadata")
            }
            Self::InitializerSortMismatch => {
                formatter.write_str("initializer body sort must match the cell sort")
            }
            Self::InitializerTreeMismatch => {
                formatter.write_str("initializer tree must exactly mirror the fixed cell tree")
            }
            Self::InitializerLeafSortMismatch => {
                formatter.write_str("initializer leaf term must match its cell content sort")
            }
            Self::MapSortMismatch => formatter.write_str("Map term must have builtin Map sort"),
            Self::MapOperationSignature(operation) => {
                write!(
                    formatter,
                    "Map operation has invalid signature {operation:?}"
                )
            }
            Self::ListOperationSignature(operation) => {
                write!(
                    formatter,
                    "List operation has invalid signature {operation:?}"
                )
            }
            Self::ConfigurationRuleWithoutFixedConfiguration(id) => write!(
                formatter,
                "configuration rule {:?} requires a general fixed configuration",
                id.as_str()
            ),
            Self::ConfigurationRuleTargetMismatch(id) => write!(
                formatter,
                "configuration rule {:?} names a different fixed configuration",
                id.as_str()
            ),
            Self::InvalidCellFraming => formatter.write_str(
                "configuration rewrite must mention or explicitly omit every fixed leaf cell",
            ),
            Self::CellFrameSortMismatch => {
                formatter.write_str("cell-content frame is incompatible with cell sort")
            }
            Self::CellFrameBindingMismatch(id) => write!(
                formatter,
                "cell-frame binding {:?} is missing or has the wrong sort",
                id.as_str()
            ),
        }
    }
}
impl Error for DefinitionValidationError {}

fn expect_symbol_kind(
    symbol: &SymbolIdentity,
    expected: SymbolKind,
) -> Result<(), DefinitionValidationError> {
    if symbol.kind == expected {
        Ok(())
    } else {
        Err(DefinitionValidationError::WrongSymbolKind {
            id: symbol.id.clone(),
            expected,
            actual: symbol.kind,
        })
    }
}

fn insert_node(
    nodes: &mut BTreeSet<SourceMapKey>,
    key: &SourceMapKey,
) -> Result<(), DefinitionValidationError> {
    if nodes.insert(key.clone()) {
        Ok(())
    } else {
        Err(DefinitionValidationError::DuplicateSourceMapKey(
            key.clone(),
        ))
    }
}

fn declare_symbol(
    symbol: &SymbolIdentity,
    symbols: &mut BTreeMap<SymbolId, SymbolKind>,
    names: &mut BTreeSet<String>,
) -> Result<(), DefinitionValidationError> {
    if symbols.insert(symbol.id.clone(), symbol.kind).is_some() {
        return Err(DefinitionValidationError::DuplicateSymbol(
            symbol.id.clone(),
        ));
    }
    if !names.insert(symbol.emitted_name.clone()) {
        return Err(DefinitionValidationError::DuplicateEmittedName(
            symbol.emitted_name.clone(),
        ));
    }
    Ok(())
}

fn collect_definition_fixed_configuration(
    configuration: &FixedConfiguration<DefinitionSortRef, SymbolId, DefinitionTerm>,
    symbols: &mut BTreeMap<SymbolId, SymbolKind>,
    names: &mut BTreeSet<String>,
    nodes: &mut BTreeSet<SourceMapKey>,
) -> Result<(), DefinitionValidationError> {
    fn cells(
        values: &[FixedCell<DefinitionSortRef, SymbolId>],
        symbols: &mut BTreeMap<SymbolId, SymbolKind>,
        names: &mut BTreeSet<String>,
        nodes: &mut BTreeSet<SourceMapKey>,
    ) -> Result<(), DefinitionValidationError> {
        for cell in values {
            if symbols
                .insert(cell.id().clone(), SymbolKind::Cell)
                .is_some()
            {
                return Err(DefinitionValidationError::DuplicateSymbol(
                    cell.id().clone(),
                ));
            }
            if !names.insert(cell.name().to_owned()) {
                return Err(DefinitionValidationError::DuplicateEmittedName(
                    cell.name().to_owned(),
                ));
            }
            insert_node(nodes, cell.origin().key())?;
            for attribute in cell.attributes() {
                insert_node(nodes, attribute.origin().key())?;
            }
            if let FixedCellContent::Children { children } = cell.content() {
                cells(children, symbols, names, nodes)?;
            }
        }
        Ok(())
    }
    fn initializer(
        values: &[FixedInitializerCell<SymbolId, DefinitionTerm>],
        nodes: &mut BTreeSet<SourceMapKey>,
    ) -> Result<(), DefinitionValidationError> {
        for cell in values {
            insert_node(nodes, cell.origin().key())?;
            if let FixedInitializerContent::Children { children } = cell.content() {
                initializer(children, nodes)?;
            }
        }
        Ok(())
    }

    if let Some(origin) = configuration.root().origin() {
        insert_node(nodes, origin.key())?;
    }
    for variable in configuration.variables() {
        insert_node(nodes, variable.origin().key())?;
    }
    cells(configuration.cells(), symbols, names, nodes)?;
    initializer(configuration.initializer(), nodes)
}

fn validate_symbol_text(symbol: &SymbolIdentity) -> Result<(), DefinitionValidationError> {
    if symbol.emitted_name.trim().is_empty() {
        return Err(DefinitionValidationError::EmptyText("symbol name"));
    }
    if symbol.emitted_name.contains(['/', '\\']) {
        return Err(DefinitionValidationError::AdapterSpecificValue(
            "symbol name",
        ));
    }
    Ok(())
}

fn validate_label_text(label: &LabelIdentity) -> Result<(), DefinitionValidationError> {
    if label.emitted_name.trim().is_empty() {
        return Err(DefinitionValidationError::EmptyText("label name"));
    }
    if label.emitted_name.contains(['/', '\\']) {
        return Err(DefinitionValidationError::AdapterSpecificValue(
            "label name",
        ));
    }
    Ok(())
}

fn require_declared_kind(
    symbols: &BTreeMap<SymbolId, SymbolKind>,
    id: &SymbolId,
    expected: SymbolKind,
) -> Result<(), DefinitionValidationError> {
    match symbols.get(id) {
        None => Err(DefinitionValidationError::DanglingSymbol(id.clone())),
        Some(actual) if *actual == expected => Ok(()),
        Some(actual) => Err(DefinitionValidationError::WrongSymbolKind {
            id: id.clone(),
            expected,
            actual: *actual,
        }),
    }
}

fn require_definition_sort(
    symbols: &BTreeMap<SymbolId, SymbolKind>,
    sort: &DefinitionSortRef,
) -> Result<(), DefinitionValidationError> {
    match sort {
        DefinitionSortRef::Declared(id) => require_declared_kind(symbols, id, SymbolKind::Sort),
        DefinitionSortRef::Builtin(
            BuiltinSort::KSequence
            | BuiltinSort::Int
            | BuiltinSort::Bool
            | BuiltinSort::Map
            | BuiltinSort::Id
            | BuiltinSort::Bytes
            | BuiltinSort::List,
        ) => Ok(()),
    }
}

fn validate_production(
    sentence: &ProductionSentence,
    symbols: &BTreeMap<SymbolId, SymbolKind>,
    groups: &BTreeSet<ProductionGroupId>,
    context_aliases: &BTreeSet<StableItemId>,
) -> Result<(), DefinitionValidationError> {
    require_declared_kind(symbols, sentence.symbol.id(), SymbolKind::Production)?;
    require_definition_sort(symbols, &sentence.result_sort)?;
    if sentence.items.is_empty() {
        return Err(DefinitionValidationError::EmptyProduction(
            sentence.symbol.id.clone(),
        ));
    }
    for item in &sentence.items {
        if let GrammarProductionItemKind::NonTerminal { sort, .. } = item.kind() {
            require_definition_sort(symbols, sort)?;
        }
    }
    for attribute in &sentence.attributes {
        match attribute {
            ProductionAttribute::Group { group, .. } => {
                require_definition_group(groups, group)?;
            }
            ProductionAttribute::Strictness {
                result_sort, using, ..
            } => {
                require_definition_sort(symbols, result_sort.sort())?;
                if using
                    .as_ref()
                    .is_some_and(|alias| !context_aliases.contains(alias.alias()))
                {
                    return Err(DefinitionValidationError::AdapterSpecificValue(
                        "strictness context alias reference",
                    ));
                }
            }
            ProductionAttribute::Documentation { .. }
            | ProductionAttribute::Function { .. }
            | ProductionAttribute::Total { .. }
            | ProductionAttribute::Alias { .. }
            | ProductionAttribute::Token { .. }
            | ProductionAttribute::Bracket { .. }
            | ProductionAttribute::Avoid { .. }
            | ProductionAttribute::Format { .. } => {}
        }
    }
    validate_definition_production_shape(
        sentence.symbol.id(),
        &sentence.items,
        &sentence.attributes,
    )?;
    Ok(())
}

fn validate_context_alias(
    sentence: &ContextAliasSentence,
    symbols: &BTreeMap<SymbolId, SymbolKind>,
    signatures: &BTreeMap<SymbolId, (DefinitionSortRef, Vec<DefinitionSortRef>)>,
    subsort_parents: &BTreeMap<DefinitionSortRef, Vec<DefinitionSortRef>>,
    nodes: &mut BTreeSet<SourceMapKey>,
) -> Result<(), DefinitionValidationError> {
    if sentence.name.trim().is_empty()
        || !sentence
            .variables
            .iter()
            .any(|variable| variable.id() == &sentence.here)
    {
        return Err(DefinitionValidationError::EmptyText(
            "context alias name/HERE",
        ));
    }
    let scope = variable_scope(&sentence.variables, symbols)?;
    for cell in sentence.body.cells() {
        require_declared_kind(symbols, cell.cell(), SymbolKind::Cell)?;
        insert_node(nodes, cell.origin().key())?;
        validate_term(
            cell.pattern(),
            &scope,
            symbols,
            signatures,
            subsort_parents,
            nodes,
        )?;
        if let CellContentFrame::KSequenceTail { origin, .. }
        | CellContentFrame::MapRemainder { origin, .. } = cell.frame()
        {
            insert_node(nodes, origin.key())?;
        }
    }
    Ok(())
}

fn variable_scope(
    variables: &[DefinitionVariable],
    symbols: &BTreeMap<SymbolId, SymbolKind>,
) -> Result<BTreeMap<SemanticId, DefinitionSortRef>, DefinitionValidationError> {
    let mut scope = BTreeMap::new();
    for variable in variables {
        require_definition_sort(symbols, &variable.sort)?;
        if scope
            .insert(variable.id.clone(), variable.sort.clone())
            .is_some()
        {
            return Err(DefinitionValidationError::DuplicateVariable(
                variable.id.clone(),
            ));
        }
    }
    Ok(scope)
}

fn validate_configuration(
    sentence: &ConfigurationSentence,
    symbols: &BTreeMap<SymbolId, SymbolKind>,
    signatures: &BTreeMap<SymbolId, (DefinitionSortRef, Vec<DefinitionSortRef>)>,
    subsort_parents: &BTreeMap<DefinitionSortRef, Vec<DefinitionSortRef>>,
    nodes: &mut BTreeSet<SourceMapKey>,
) -> Result<(), DefinitionValidationError> {
    match sentence {
        ConfigurationSentence::Legacy(sentence) => {
            require_declared_kind(symbols, sentence.cell.symbol.id(), SymbolKind::Cell)?;
            require_definition_sort(symbols, &sentence.cell.content_sort)?;
            require_declared_kind(
                symbols,
                sentence.initializer.symbol.id(),
                SymbolKind::Initializer,
            )?;
            let scope = variable_scope(&sentence.initializer.variables, symbols)?;
            validate_term(
                &sentence.initializer.body,
                &scope,
                symbols,
                signatures,
                subsort_parents,
                nodes,
            )?;
            if sentence.initializer.body.sort != sentence.cell.content_sort {
                return Err(DefinitionValidationError::InitializerSortMismatch);
            }
        }
        ConfigurationSentence::Fixed(sentence) => {
            validate_fixed_configuration(sentence, symbols, signatures, subsort_parents, nodes)?;
        }
    }
    Ok(())
}

fn validate_fixed_configuration(
    configuration: &FixedConfiguration<DefinitionSortRef, SymbolId, DefinitionTerm>,
    symbols: &BTreeMap<SymbolId, SymbolKind>,
    signatures: &BTreeMap<SymbolId, (DefinitionSortRef, Vec<DefinitionSortRef>)>,
    subsort_parents: &BTreeMap<DefinitionSortRef, Vec<DefinitionSortRef>>,
    nodes: &mut BTreeSet<SourceMapKey>,
) -> Result<(), DefinitionValidationError> {
    let mut scope = BTreeMap::new();
    let mut external_names = BTreeSet::new();
    let mut main_count = 0_usize;
    for variable in configuration.variables() {
        require_definition_sort(symbols, variable.sort())?;
        if scope
            .insert(variable.id().clone(), variable.sort().clone())
            .is_some()
        {
            return Err(DefinitionValidationError::DuplicateVariable(
                variable.id().clone(),
            ));
        }
        if !external_names.insert(variable.external_name()) {
            return Err(DefinitionValidationError::EmptyText(
                "duplicate external configuration variable",
            ));
        }
        main_count += usize::from(variable.is_main());
    }
    if main_count > 1 {
        return Err(DefinitionValidationError::EmptyText(
            "multiple main configuration variables",
        ));
    }
    validate_initializer_forest(
        configuration.cells(),
        configuration.initializer(),
        &scope,
        symbols,
        signatures,
        subsort_parents,
        nodes,
    )?;
    let mut used = BTreeSet::new();
    collect_initializer_variables(configuration.initializer(), &mut used);
    if used != scope.keys().cloned().collect() {
        return Err(DefinitionValidationError::VariableClosure);
    }
    Ok(())
}

fn collect_initializer_variables(
    initializer: &[FixedInitializerCell<SymbolId, DefinitionTerm>],
    used: &mut BTreeSet<SemanticId>,
) {
    for cell in initializer {
        match cell.content() {
            FixedInitializerContent::Term { term } => collect_term_variables(term, used),
            FixedInitializerContent::Children { children } => {
                collect_initializer_variables(children, used);
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn validate_initializer_forest(
    cells: &[FixedCell<DefinitionSortRef, SymbolId>],
    initializer: &[FixedInitializerCell<SymbolId, DefinitionTerm>],
    scope: &BTreeMap<SemanticId, DefinitionSortRef>,
    symbols: &BTreeMap<SymbolId, SymbolKind>,
    signatures: &BTreeMap<SymbolId, (DefinitionSortRef, Vec<DefinitionSortRef>)>,
    subsort_parents: &BTreeMap<DefinitionSortRef, Vec<DefinitionSortRef>>,
    nodes: &mut BTreeSet<SourceMapKey>,
) -> Result<(), DefinitionValidationError> {
    if cells.len() != initializer.len() {
        return Err(DefinitionValidationError::InitializerTreeMismatch);
    }
    for (cell, initialized) in cells.iter().zip(initializer) {
        if cell.id() != initialized.cell() {
            return Err(DefinitionValidationError::InitializerTreeMismatch);
        }
        match (cell.content(), initialized.content()) {
            (FixedCellContent::Term { sort }, FixedInitializerContent::Term { term }) => {
                require_definition_sort(symbols, sort)?;
                validate_term(term, scope, symbols, signatures, subsort_parents, nodes)?;
                if term.sort() != sort {
                    return Err(DefinitionValidationError::InitializerLeafSortMismatch);
                }
            }
            (
                FixedCellContent::Children { children },
                FixedInitializerContent::Children {
                    children: initialized_children,
                },
            ) => validate_initializer_forest(
                children,
                initialized_children,
                scope,
                symbols,
                signatures,
                subsort_parents,
                nodes,
            )?,
            _ => return Err(DefinitionValidationError::InitializerTreeMismatch),
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn validate_configuration_rewrite(
    rewrite: &FixedConfigurationRewrite<SymbolId, DefinitionTerm>,
    configuration: &FixedConfiguration<DefinitionSortRef, SymbolId, DefinitionTerm>,
    scope: &BTreeMap<SemanticId, DefinitionSortRef>,
    symbols: &BTreeMap<SymbolId, SymbolKind>,
    signatures: &BTreeMap<SymbolId, (DefinitionSortRef, Vec<DefinitionSortRef>)>,
    subsort_parents: &BTreeMap<DefinitionSortRef, Vec<DefinitionSortRef>>,
    nodes: &mut BTreeSet<SourceMapKey>,
) -> Result<(), DefinitionValidationError> {
    fn leaves(
        cells: &[FixedCell<DefinitionSortRef, SymbolId>],
        output: &mut BTreeMap<SymbolId, DefinitionSortRef>,
    ) -> Result<(), DefinitionValidationError> {
        for cell in cells {
            match cell.content() {
                FixedCellContent::Term { sort } => {
                    if output.insert(cell.id().clone(), sort.clone()).is_some() {
                        return Err(DefinitionValidationError::InvalidCellFraming);
                    }
                }
                FixedCellContent::Children { children } => leaves(children, output)?,
            }
        }
        Ok(())
    }

    let mut leaf_sorts = BTreeMap::new();
    leaves(configuration.cells(), &mut leaf_sorts)?;
    let mentioned = rewrite
        .clauses()
        .iter()
        .map(|clause| clause.cell().clone())
        .collect::<BTreeSet<_>>();
    let omitted = rewrite
        .omitted_siblings()
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>();
    if mentioned.len() != rewrite.clauses().len()
        || omitted.len() != rewrite.omitted_siblings().len()
        || !mentioned.is_disjoint(&omitted)
        || mentioned.union(&omitted).cloned().collect::<BTreeSet<_>>()
            != leaf_sorts.keys().cloned().collect()
    {
        return Err(DefinitionValidationError::InvalidCellFraming);
    }
    insert_node(nodes, rewrite.origin().key())?;
    for clause in rewrite.clauses() {
        let sort = leaf_sorts
            .get(clause.cell())
            .ok_or(DefinitionValidationError::InvalidCellFraming)?;
        insert_node(nodes, clause.origin().key())?;
        validate_term(
            clause.before(),
            scope,
            symbols,
            signatures,
            subsort_parents,
            nodes,
        )?;
        if clause.before().sort() != sort {
            return Err(DefinitionValidationError::CellFrameSortMismatch);
        }
        if let CellPost::Replace { term } = clause.after() {
            validate_term(term, scope, symbols, signatures, subsort_parents, nodes)?;
            if term.sort() != sort {
                return Err(DefinitionValidationError::CellFrameSortMismatch);
            }
        }
        validate_cell_frame(clause, sort, scope, nodes)?;
    }
    Ok(())
}

fn validate_cell_frame(
    clause: &FixedCellClause<SymbolId, DefinitionTerm>,
    sort: &DefinitionSortRef,
    scope: &BTreeMap<SemanticId, DefinitionSortRef>,
    nodes: &mut BTreeSet<SourceMapKey>,
) -> Result<(), DefinitionValidationError> {
    let (origin, binding, required_sort) = match clause.frame() {
        CellContentFrame::Exact => return Ok(()),
        CellContentFrame::KSequenceTail { origin, binding } => (
            origin,
            binding,
            DefinitionSortRef::Builtin(BuiltinSort::KSequence),
        ),
        CellContentFrame::MapRemainder { origin, binding } => (
            origin,
            binding,
            DefinitionSortRef::Builtin(BuiltinSort::Map),
        ),
    };
    insert_node(nodes, origin.key())?;
    if sort != &required_sort {
        return Err(DefinitionValidationError::CellFrameSortMismatch);
    }
    if let Some(binding) = binding
        && scope.get(binding) != Some(&required_sort)
    {
        return Err(DefinitionValidationError::CellFrameBindingMismatch(
            binding.clone(),
        ));
    }
    Ok(())
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn validate_rule(
    sentence: &RuleSentence,
    configuration: Option<&FixedConfiguration<DefinitionSortRef, SymbolId, DefinitionTerm>>,
    symbols: &BTreeMap<SymbolId, SymbolKind>,
    signatures: &BTreeMap<SymbolId, (DefinitionSortRef, Vec<DefinitionSortRef>)>,
    functional_productions: &BTreeSet<SymbolId>,
    alias_productions: &BTreeSet<SymbolId>,
    subsort_parents: &BTreeMap<DefinitionSortRef, Vec<DefinitionSortRef>>,
    nodes: &mut BTreeSet<SourceMapKey>,
) -> Result<(), DefinitionValidationError> {
    let claim = match (sentence.kind, sentence.claim.as_ref()) {
        (SentenceKind::Claim, Some(claim)) => Some(claim),
        (SentenceKind::Claim, None) | (_, Some(_)) => {
            return Err(DefinitionValidationError::InvalidClaimMetadata(
                sentence.label.id.clone(),
            ));
        }
        (_, None) => None,
    };
    if sentence.kind == SentenceKind::Claim {
        if sentence.priority.is_some() || sentence.simplification.is_some() {
            return Err(DefinitionValidationError::InvalidClaimMetadata(
                sentence.label.id.clone(),
            ));
        }
        if !matches!(&sentence.body, DefinitionRuleBody::Configuration(_)) {
            return Err(DefinitionValidationError::ClaimBodyNotConfiguration(
                sentence.label.id.clone(),
            ));
        }
    }
    let scope = variable_scope(&sentence.variables, symbols)?;
    match &sentence.body {
        DefinitionRuleBody::Term(body) => {
            validate_term(body, &scope, symbols, signatures, subsort_parents, nodes)?;
            if !matches!(body.kind, DefinitionTermKind::Rewrite { .. }) {
                return Err(DefinitionValidationError::RuleBodyNotRewrite(
                    sentence.label.id.clone(),
                ));
            }
            if sentence.kind == SentenceKind::Equation {
                let DefinitionTermKind::Rewrite { from, .. } = body.kind() else {
                    unreachable!("rule bodies were checked as rewrites")
                };
                let DefinitionTermKind::Application {
                    application: ApplicationRef::Declared(symbol),
                    ..
                } = from.kind()
                else {
                    return Err(DefinitionValidationError::InvalidEquationRoot(
                        sentence.label.id.clone(),
                    ));
                };
                if !functional_productions.contains(symbol) {
                    return Err(DefinitionValidationError::InvalidEquationRoot(
                        sentence.label.id.clone(),
                    ));
                }
            }
            if sentence.kind == SentenceKind::Alias {
                let DefinitionTermKind::Rewrite { from, .. } = body.kind() else {
                    unreachable!("rule bodies were checked as rewrites")
                };
                let DefinitionTermKind::Application {
                    application: ApplicationRef::Declared(symbol),
                    ..
                } = from.kind()
                else {
                    return Err(DefinitionValidationError::InvalidAliasRoot(
                        sentence.label.id.clone(),
                    ));
                };
                if !alias_productions.contains(symbol) {
                    return Err(DefinitionValidationError::InvalidAliasRoot(
                        sentence.label.id.clone(),
                    ));
                }
            }
            if sentence.kind == SentenceKind::Simplification {
                let DefinitionTermKind::Rewrite { from, .. } = body.kind() else {
                    unreachable!("rule bodies were checked as rewrites")
                };
                match from.kind() {
                    DefinitionTermKind::Application {
                        application: ApplicationRef::Declared(symbol),
                        ..
                    } if functional_productions.contains(symbol) => {}
                    DefinitionTermKind::Application {
                        application: ApplicationRef::Builtin(operation),
                        ..
                    } if operation.is_functional() => {}
                    _ => {
                        return Err(DefinitionValidationError::InvalidSimplificationRoot(
                            sentence.label.id.clone(),
                        ));
                    }
                }
            }
        }
        DefinitionRuleBody::Configuration(body) => {
            if sentence.kind == SentenceKind::Alias {
                return Err(DefinitionValidationError::InvalidAliasRoot(
                    sentence.label.id.clone(),
                ));
            }
            if sentence.kind == SentenceKind::Simplification {
                return Err(DefinitionValidationError::InvalidSimplificationRoot(
                    sentence.label.id.clone(),
                ));
            }
            let configuration = configuration.ok_or_else(|| {
                DefinitionValidationError::ConfigurationRuleWithoutFixedConfiguration(
                    sentence.label.id.clone(),
                )
            })?;
            if body.configuration() != configuration.id() {
                return Err(DefinitionValidationError::ConfigurationRuleTargetMismatch(
                    sentence.label.id.clone(),
                ));
            }
            validate_configuration_rewrite(
                body,
                configuration,
                &scope,
                symbols,
                signatures,
                subsort_parents,
                nodes,
            )?;
        }
    }
    if sentence.kind == SentenceKind::Simplification {
        let Some(simplification) = &sentence.simplification else {
            return Err(DefinitionValidationError::InvalidSimplificationMetadata(
                sentence.label.id.clone(),
            ));
        };
        insert_node(nodes, simplification.origin().key())?;
        if let Some(priority) = simplification.priority() {
            insert_node(nodes, priority.origin().key())?;
        }
    } else if sentence.simplification.is_some() {
        return Err(DefinitionValidationError::InvalidSimplificationMetadata(
            sentence.label.id.clone(),
        ));
    }
    if let Some(priority) = &sentence.priority {
        if sentence.kind != SentenceKind::Equation {
            return Err(DefinitionValidationError::InvalidRulePriority(
                sentence.label.id.clone(),
            ));
        }
        insert_node(nodes, priority.origin().key())?;
    }
    if let Some(condition) = &sentence.requires {
        if sentence.kind == SentenceKind::Alias {
            return Err(DefinitionValidationError::AliasCondition);
        }
        insert_node(nodes, condition.origin().key())?;
        validate_term(
            condition.term(),
            &scope,
            symbols,
            signatures,
            subsort_parents,
            nodes,
        )?;
        if condition.term().sort() != &DefinitionSortRef::Builtin(BuiltinSort::Bool) {
            return Err(DefinitionValidationError::RuleConditionSortMismatch);
        }
    }
    if let Some(claim) = claim {
        validate_claim(
            sentence,
            claim,
            &scope,
            symbols,
            signatures,
            subsort_parents,
            nodes,
        )?;
    }
    let mut used = BTreeSet::new();
    match &sentence.body {
        DefinitionRuleBody::Term(body) => collect_term_variables(body, &mut used),
        DefinitionRuleBody::Configuration(body) => {
            for clause in body.clauses() {
                collect_term_variables(clause.before(), &mut used);
                if let CellPost::Replace { term } = clause.after() {
                    collect_term_variables(term, &mut used);
                }
                match clause.frame() {
                    CellContentFrame::Exact => {}
                    CellContentFrame::KSequenceTail { binding, .. }
                    | CellContentFrame::MapRemainder { binding, .. } => {
                        if let Some(binding) = binding {
                            used.insert(binding.clone());
                        }
                    }
                }
            }
        }
    }
    if let Some(condition) = &sentence.requires {
        collect_term_variables(condition.term(), &mut used);
    }
    if let Some(ensures) = claim.and_then(DefinitionClaim::ensures) {
        collect_term_variables(ensures.term(), &mut used);
    }
    if used != scope.keys().cloned().collect() {
        return Err(DefinitionValidationError::VariableClosure);
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn validate_claim(
    sentence: &RuleSentence,
    claim: &DefinitionClaim,
    scope: &BTreeMap<SemanticId, DefinitionSortRef>,
    symbols: &BTreeMap<SymbolId, SymbolKind>,
    signatures: &BTreeMap<SymbolId, (DefinitionSortRef, Vec<DefinitionSortRef>)>,
    subsort_parents: &BTreeMap<DefinitionSortRef, Vec<DefinitionSortRef>>,
    nodes: &mut BTreeSet<SourceMapKey>,
) -> Result<(), DefinitionValidationError> {
    insert_node(nodes, claim.modality_origin().key())?;
    if let Some(origin) = claim.circularity_origin() {
        insert_node(nodes, origin.key())?;
    }

    let mut binder_ids = BTreeSet::new();
    for binder in claim.universals().iter().chain(claim.existentials()) {
        if !binder_ids.insert(binder.id().clone()) || scope.get(binder.id()) != Some(binder.sort())
        {
            return Err(DefinitionValidationError::InvalidClaimBinder(
                binder.id().clone(),
            ));
        }
        require_definition_sort(symbols, binder.sort())?;
        insert_node(nodes, binder.origin().key())?;
        insert_node(nodes, binder.name_origin().key())?;
        insert_node(nodes, binder.sort_origin().key())?;
    }

    let mut left_uses = BTreeSet::new();
    let mut right_uses = BTreeSet::new();
    let DefinitionRuleBody::Configuration(body) = &sentence.body else {
        return Err(DefinitionValidationError::ClaimBodyNotConfiguration(
            sentence.label.id.clone(),
        ));
    };
    for clause in body.clauses() {
        collect_term_variables(clause.before(), &mut left_uses);
        if let CellPost::Replace { term } = clause.after() {
            collect_term_variables(term, &mut right_uses);
        }
        match clause.frame() {
            CellContentFrame::Exact => {}
            CellContentFrame::KSequenceTail { binding, .. }
            | CellContentFrame::MapRemainder { binding, .. } => {
                if let Some(binding) = binding {
                    left_uses.insert(binding.clone());
                }
            }
        }
    }
    if let Some(requires) = sentence.requires() {
        collect_term_variables(requires.term(), &mut left_uses);
    }
    if let Some(ensures) = claim.ensures() {
        insert_node(nodes, ensures.origin().key())?;
        validate_term(
            ensures.term(),
            scope,
            symbols,
            signatures,
            subsort_parents,
            nodes,
        )?;
        if ensures.term().sort() != &DefinitionSortRef::Builtin(BuiltinSort::Bool) {
            return Err(DefinitionValidationError::RuleConditionSortMismatch);
        }
        collect_term_variables(ensures.term(), &mut right_uses);
    }
    for binder in claim.existentials() {
        if left_uses.contains(binder.id()) {
            return Err(DefinitionValidationError::ExistentialScopeViolation(
                binder.id().clone(),
            ));
        }
        if !right_uses.contains(binder.id()) {
            return Err(DefinitionValidationError::UnusedExistential(
                binder.id().clone(),
            ));
        }
    }
    Ok(())
}

fn collect_term_variables(term: &DefinitionTerm, used: &mut BTreeSet<SemanticId>) {
    match term.kind() {
        DefinitionTermKind::Variable { variable } => {
            used.insert(variable.clone());
        }
        DefinitionTermKind::Application { arguments, .. }
        | DefinitionTermKind::Map { arguments, .. }
        | DefinitionTermKind::List { arguments, .. } => {
            for argument in arguments {
                collect_term_variables(argument, used);
            }
        }
        DefinitionTermKind::KSequence { items, .. } => {
            for item in items {
                collect_term_variables(item, used);
            }
        }
        DefinitionTermKind::Rewrite { from, to } => {
            collect_term_variables(from, used);
            collect_term_variables(to, used);
        }
        DefinitionTermKind::Token { .. } => {}
    }
}

#[allow(clippy::too_many_lines)]
fn validate_term(
    term: &DefinitionTerm,
    scope: &BTreeMap<SemanticId, DefinitionSortRef>,
    symbols: &BTreeMap<SymbolId, SymbolKind>,
    signatures: &BTreeMap<SymbolId, (DefinitionSortRef, Vec<DefinitionSortRef>)>,
    subsort_parents: &BTreeMap<DefinitionSortRef, Vec<DefinitionSortRef>>,
    nodes: &mut BTreeSet<SourceMapKey>,
) -> Result<(), DefinitionValidationError> {
    insert_node(nodes, term.origin.key())?;
    require_definition_sort(symbols, &term.sort)?;
    match &term.kind {
        DefinitionTermKind::Variable { variable } => match scope.get(variable) {
            None => {
                return Err(DefinitionValidationError::DanglingVariable(
                    variable.clone(),
                ));
            }
            Some(sort) if *sort != term.sort => {
                return Err(DefinitionValidationError::VariableSortMismatch(
                    variable.clone(),
                ));
            }
            Some(_) => {}
        },
        DefinitionTermKind::Application {
            application,
            arguments,
        } => {
            let signature = match application {
                ApplicationRef::Declared(symbol) => {
                    require_declared_kind(symbols, symbol, SymbolKind::Production)?;
                    signatures
                        .get(symbol)
                        .cloned()
                        .ok_or_else(|| DefinitionValidationError::DanglingSymbol(symbol.clone()))?
                }
                ApplicationRef::Builtin(operation) => definition_builtin_signature(*operation),
            };
            let (result_sort, argument_sorts) = signature;
            if term.sort != result_sort
                || arguments.len() != argument_sorts.len()
                || arguments
                    .iter()
                    .zip(&argument_sorts)
                    .any(|(argument, sort)| {
                        !is_definition_subsort(&argument.sort, sort, subsort_parents)
                    })
            {
                return match application {
                    ApplicationRef::Declared(symbol) => Err(
                        DefinitionValidationError::ApplicationSignature(symbol.clone()),
                    ),
                    ApplicationRef::Builtin(operation) => Err(
                        DefinitionValidationError::BuiltinApplicationSignature(*operation),
                    ),
                };
            }
            for argument in arguments {
                validate_term(argument, scope, symbols, signatures, subsort_parents, nodes)?;
            }
        }
        DefinitionTermKind::Token { value } => {
            if value.is_empty() {
                return Err(DefinitionValidationError::EmptyText("token value"));
            }
        }
        DefinitionTermKind::KSequence { item_sort, items } => {
            require_definition_sort(symbols, item_sort)?;
            if term.sort != DefinitionSortRef::Builtin(BuiltinSort::KSequence) {
                return Err(DefinitionValidationError::SequenceSortMismatch);
            }
            for item in items {
                validate_term(item, scope, symbols, signatures, subsort_parents, nodes)?;
                if !is_definition_subsort(&item.sort, item_sort, subsort_parents) {
                    return Err(DefinitionValidationError::SequenceItemSortMismatch);
                }
            }
        }
        DefinitionTermKind::Map {
            operation,
            arguments,
        } => {
            if term.sort != DefinitionSortRef::Builtin(BuiltinSort::Map) {
                return Err(DefinitionValidationError::MapSortMismatch);
            }
            let valid_arity = match operation {
                MapOperation::Empty => arguments.is_empty(),
                MapOperation::Item => !arguments.is_empty() && arguments.len().is_multiple_of(2),
                MapOperation::Update => {
                    arguments.len() == 3
                        && arguments[0].sort == DefinitionSortRef::Builtin(BuiltinSort::Map)
                }
            };
            if !valid_arity {
                return Err(DefinitionValidationError::MapOperationSignature(*operation));
            }
            for argument in arguments {
                validate_term(argument, scope, symbols, signatures, subsort_parents, nodes)?;
            }
        }
        DefinitionTermKind::List {
            operation,
            arguments,
        } => {
            let list_sort = DefinitionSortRef::Builtin(BuiltinSort::List);
            let int_sort = DefinitionSortRef::Builtin(BuiltinSort::Int);
            let valid = match operation {
                ListOperation::Empty => term.sort == list_sort && arguments.is_empty(),
                ListOperation::Item => term.sort == list_sort && arguments.len() == 1,
                ListOperation::Concat => {
                    term.sort == list_sort
                        && arguments.len() == 2
                        && arguments.iter().all(|argument| argument.sort == list_sort)
                }
                ListOperation::Get => {
                    arguments.len() == 2
                        && arguments[0].sort == list_sort
                        && arguments[1].sort == int_sort
                }
                ListOperation::Update => {
                    term.sort == list_sort
                        && arguments.len() == 3
                        && arguments[0].sort == list_sort
                        && arguments[1].sort == int_sort
                }
                ListOperation::Size => {
                    term.sort == int_sort && arguments.len() == 1 && arguments[0].sort == list_sort
                }
            };
            if !valid {
                return Err(DefinitionValidationError::ListOperationSignature(
                    *operation,
                ));
            }
            for argument in arguments {
                validate_term(argument, scope, symbols, signatures, subsort_parents, nodes)?;
            }
        }
        DefinitionTermKind::Rewrite { from, to } => {
            validate_term(from, scope, symbols, signatures, subsort_parents, nodes)?;
            validate_term(to, scope, symbols, signatures, subsort_parents, nodes)?;
            if !is_definition_subsort(&from.sort, &term.sort, subsort_parents)
                || !is_definition_subsort(&to.sort, &term.sort, subsort_parents)
            {
                return Err(DefinitionValidationError::RewriteSortMismatch);
            }
        }
    }
    Ok(())
}

fn require_definition_group(
    groups: &BTreeSet<ProductionGroupId>,
    group: &ProductionGroupId,
) -> Result<(), DefinitionValidationError> {
    if groups.contains(group) {
        Ok(())
    } else {
        Err(DefinitionValidationError::DanglingProductionGroup(
            group.clone(),
        ))
    }
}

fn validate_definition_production_shape(
    id: &SymbolId,
    items: &[ProductionItem],
    attributes: &[DefinitionProductionAttribute],
) -> Result<(), DefinitionValidationError> {
    if items.is_empty() {
        return Err(DefinitionValidationError::EmptyProduction(id.clone()));
    }
    let fields = items
        .iter()
        .filter_map(|item| match item.kind() {
            GrammarProductionItemKind::NonTerminal { field, .. } => Some(field.clone()),
            GrammarProductionItemKind::Terminal { .. }
            | GrammarProductionItemKind::RegexTerminal { .. } => None,
        })
        .collect::<Vec<_>>();
    if has_duplicate_definition_fields(&fields) {
        return Err(DefinitionValidationError::InvalidStrictnessField);
    }
    let regexes = items
        .iter()
        .filter(|item| matches!(item.kind(), GrammarProductionItemKind::RegexTerminal { .. }))
        .count();
    let mut token = false;
    let mut function = false;
    let mut total = false;
    let mut alias = false;
    let mut group = false;
    let mut bracket = false;
    let mut avoid = false;
    let mut format = false;
    let mut strictness = false;
    for attribute in attributes {
        let already = match attribute {
            ProductionAttribute::Documentation { .. } => continue,
            ProductionAttribute::Function { .. } => std::mem::replace(&mut function, true),
            ProductionAttribute::Total { .. } => std::mem::replace(&mut total, true),
            ProductionAttribute::Alias { .. } => std::mem::replace(&mut alias, true),
            ProductionAttribute::Token { .. } => std::mem::replace(&mut token, true),
            ProductionAttribute::Group { .. } => std::mem::replace(&mut group, true),
            ProductionAttribute::Bracket { .. } => std::mem::replace(&mut bracket, true),
            ProductionAttribute::Avoid { .. } => std::mem::replace(&mut avoid, true),
            ProductionAttribute::Format { .. } => std::mem::replace(&mut format, true),
            ProductionAttribute::Strictness { .. } => std::mem::replace(&mut strictness, true),
        };
        if already {
            let name = attribute
                .unique_name()
                .expect("repeatable documentation was skipped above");
            return Err(DefinitionValidationError::DuplicateProductionAttribute(
                name,
            ));
        }
        match attribute {
            ProductionAttribute::Strictness {
                fields: selected, ..
            } => {
                if selected.is_empty()
                    || has_duplicate_definition_fields(&selected.iter().map(|field| field.field().clone()).collect::<Vec<_>>())
                    || selected.iter().any(|field| !fields.contains(field.field()))
                {
                    return Err(DefinitionValidationError::InvalidStrictnessField);
                }
            }
            ProductionAttribute::Format { fragments, .. } => {
                if fragments.is_empty()
                    || fragments.iter().any(|fragment| {
                        matches!(fragment, FormatFragment::Item(position) if *position == 0 || usize::from(*position) > items.len())
                    })
                {
                    return Err(DefinitionValidationError::InvalidFormat);
                }
            }
            ProductionAttribute::Documentation { .. }
            | ProductionAttribute::Function { .. }
            | ProductionAttribute::Total { .. }
            | ProductionAttribute::Alias { .. }
            | ProductionAttribute::Token { .. }
            | ProductionAttribute::Group { .. }
            | ProductionAttribute::Bracket { .. }
            | ProductionAttribute::Avoid { .. } => {}
        }
    }
    if total && !function {
        return Err(DefinitionValidationError::InvalidFunctionProduction);
    }
    if alias && function {
        return Err(DefinitionValidationError::InvalidAliasProduction);
    }
    if token && (items.len() != 1 || regexes != 1) {
        return Err(DefinitionValidationError::InvalidTokenProduction);
    }
    if regexes != 0 && !token {
        return Err(DefinitionValidationError::RegexWithoutToken);
    }
    if bracket && fields.len() != 1 {
        return Err(DefinitionValidationError::InvalidBracketProduction);
    }
    Ok(())
}

fn has_duplicate_definition_fields(fields: &[ProductionFieldId]) -> bool {
    let mut unique = BTreeSet::new();
    fields.iter().any(|field| !unique.insert(field))
}

fn definition_builtin_signature(
    operation: BuiltinOperation,
) -> (DefinitionSortRef, Vec<DefinitionSortRef>) {
    (
        DefinitionSortRef::Builtin(operation.result_sort()),
        operation
            .argument_sorts()
            .iter()
            .copied()
            .map(DefinitionSortRef::Builtin)
            .collect(),
    )
}

fn validate_definition_precedence_order(
    modules: &[DefinitionModule],
) -> Result<(), DefinitionValidationError> {
    let mut edges: BTreeMap<ProductionGroupId, BTreeSet<ProductionGroupId>> = BTreeMap::new();
    for relation in modules
        .iter()
        .flat_map(|module| &module.sentences)
        .filter_map(|sentence| match sentence {
            DefinitionSentence::Precedence(relation) => Some(relation),
            DefinitionSentence::SyntaxSort(_)
            | DefinitionSentence::Subsort(_)
            | DefinitionSentence::Production(_)
            | DefinitionSentence::Associativity(_)
            | DefinitionSentence::Configuration(_)
            | DefinitionSentence::ContextAlias(_)
            | DefinitionSentence::Rule(_) => None,
        })
    {
        for higher in relation.higher() {
            for lower in relation.lower() {
                edges
                    .entry(higher.clone())
                    .or_default()
                    .insert(lower.clone());
            }
        }
    }
    for start in edges.keys() {
        let mut pending = edges
            .get(start)
            .into_iter()
            .flatten()
            .cloned()
            .collect::<Vec<_>>();
        let mut visited = BTreeSet::new();
        while let Some(group) = pending.pop() {
            if &group == start {
                return Err(DefinitionValidationError::PrecedenceCycle(start.clone()));
            }
            if visited.insert(group.clone()) {
                pending.extend(edges.get(&group).into_iter().flatten().cloned());
            }
        }
    }
    Ok(())
}

fn validate_definition_subsort_order(
    edges: &BTreeMap<DefinitionSortRef, Vec<DefinitionSortRef>>,
) -> Result<(), DefinitionValidationError> {
    for start in edges.keys() {
        let mut pending = edges
            .get(start)
            .into_iter()
            .flatten()
            .cloned()
            .collect::<Vec<_>>();
        let mut visited = BTreeSet::new();
        while let Some(sort) = pending.pop() {
            if &sort == start {
                return Err(DefinitionValidationError::SubsortCycle(start.clone()));
            }
            if visited.insert(sort.clone()) {
                pending.extend(edges.get(&sort).into_iter().flatten().cloned());
            }
        }
    }
    Ok(())
}

fn is_definition_subsort(
    candidate: &DefinitionSortRef,
    expected: &DefinitionSortRef,
    parents: &BTreeMap<DefinitionSortRef, Vec<DefinitionSortRef>>,
) -> bool {
    let mut pending = vec![candidate];
    let mut visited = BTreeSet::new();
    while let Some(sort) = pending.pop() {
        if sort == expected {
            return true;
        }
        if visited.insert(sort) {
            pending.extend(parents.get(sort).into_iter().flatten());
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ClaimModality, OriginStack, PackageId, Sha256Digest, SourceFileId, SourceRange};

    fn node(key: &str) -> NodeOrigin {
        let package = PackageId::new("ORG-EXAMPLE-CLAIM", "claim", "0.1.0", "workspace")
            .expect("valid package");
        let file = SourceFileId::new(
            package,
            "src/lib.rs",
            Sha256Digest::new("b".repeat(64)).expect("valid digest"),
        )
        .expect("valid source file");
        NodeOrigin::new(
            SourceMapKey::new(key).expect("valid source key"),
            OriginStack::authored(SourceRange::new(file, 0, 1).expect("valid range")),
        )
    }

    fn sid(value: &str) -> SemanticId {
        SemanticId::new(value).expect("valid semantic ID")
    }

    fn int_variable(key: &str, id: &str) -> DefinitionTerm {
        DefinitionTerm::variable(
            node(key),
            DefinitionSortRef::Builtin(BuiltinSort::Int),
            sid(id),
        )
    }

    fn int_token(key: &str) -> DefinitionTerm {
        DefinitionTerm::token(node(key), DefinitionSortRef::Builtin(BuiltinSort::Int), "0")
            .expect("valid token")
    }

    fn claim_sentence(before: DefinitionTerm, after: DefinitionTerm) -> RuleSentence {
        let body = FixedConfigurationRewrite::new(
            node("rewrite"),
            sid("configuration"),
            vec![FixedCellClause::new(
                node("clause"),
                SymbolId::new("cell").expect("valid cell ID"),
                before,
                CellPost::Replace { term: after },
                CellContentFrame::Exact,
            )],
            Vec::new(),
        )
        .expect("valid configuration rewrite");
        let binder = DefinitionClaimBinder::new(
            node("binder"),
            node("binder-name"),
            sid("exists"),
            node("binder-sort"),
            DefinitionSortRef::Builtin(BuiltinSort::Int),
        );
        RuleSentence {
            origin: node("rule"),
            label: LabelIdentity::new(
                LabelId::new("claim").expect("valid label ID"),
                "reachability",
            )
            .expect("valid label"),
            kind: SentenceKind::Claim,
            variables: vec![DefinitionVariable::new(
                sid("exists"),
                DefinitionSortRef::Builtin(BuiltinSort::Int),
            )],
            requires: None,
            priority: None,
            simplification: None,
            claim: Some(DefinitionClaim::new(
                node("modality"),
                ClaimModality::AllPaths,
                None,
                Vec::new(),
                vec![binder],
                None,
            )),
            body: DefinitionRuleBody::Configuration(body),
        }
    }

    fn validate_claim_only(sentence: &RuleSentence) -> Result<(), DefinitionValidationError> {
        let scope = variable_scope(&sentence.variables, &BTreeMap::new())?;
        validate_claim(
            sentence,
            sentence.claim.as_ref().expect("claim metadata"),
            &scope,
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &mut BTreeSet::new(),
        )
    }

    #[test]
    fn definition_claim_repeats_existential_side_checks() {
        let left = claim_sentence(int_variable("before", "exists"), int_token("after"));
        assert_eq!(
            validate_claim_only(&left),
            Err(DefinitionValidationError::ExistentialScopeViolation(sid(
                "exists"
            )))
        );

        let unused = claim_sentence(int_token("before"), int_token("after"));
        assert_eq!(
            validate_claim_only(&unused),
            Err(DefinitionValidationError::UnusedExistential(sid("exists")))
        );
    }

    #[test]
    fn definition_one_path_circular_claim_is_well_formed() {
        let mut sentence = claim_sentence(int_token("before"), int_variable("after", "exists"));
        let claim = sentence.claim.as_mut().expect("claim metadata");
        claim.modality = ClaimModality::OnePath;
        claim.circularity_origin = Some(node("circularity"));
        assert_eq!(validate_claim_only(&sentence), Ok(()));
    }

    #[test]
    fn definition_claim_rejects_non_bool_ensures() {
        let mut sentence = claim_sentence(int_token("before"), int_variable("after", "exists"));
        sentence.claim.as_mut().expect("claim metadata").ensures = Some(
            DefinitionRuleCondition::new(node("ensures"), int_token("post")),
        );
        assert_eq!(
            validate_claim_only(&sentence),
            Err(DefinitionValidationError::RuleConditionSortMismatch)
        );

        let mut unbound = claim_sentence(
            int_token("unbound-before"),
            int_variable("unbound-after", "exists"),
        );
        unbound.claim.as_mut().expect("claim metadata").existentials[0].id = sid("missing");
        assert_eq!(
            validate_claim_only(&unbound),
            Err(DefinitionValidationError::InvalidClaimBinder(sid(
                "missing"
            )))
        );
    }

    #[test]
    fn definition_claim_metadata_is_exclusive_to_claim_sentences() {
        let mut sentence = claim_sentence(int_token("before"), int_variable("after", "exists"));
        sentence.kind = SentenceKind::Transition;
        assert!(matches!(
            validate_rule(
                &sentence,
                None,
                &BTreeMap::new(),
                &BTreeMap::new(),
                &BTreeSet::new(),
                &BTreeSet::new(),
                &BTreeMap::new(),
                &mut BTreeSet::new(),
            ),
            Err(DefinitionValidationError::InvalidClaimMetadata(_))
        ));

        let mut sentence = claim_sentence(
            int_token("missing-before"),
            int_variable("missing-after", "exists"),
        );
        sentence.claim = None;
        assert!(matches!(
            validate_rule(
                &sentence,
                None,
                &BTreeMap::new(),
                &BTreeMap::new(),
                &BTreeSet::new(),
                &BTreeSet::new(),
                &BTreeMap::new(),
                &mut BTreeSet::new(),
            ),
            Err(DefinitionValidationError::InvalidClaimMetadata(_))
        ));
    }

    #[test]
    fn definition_claim_requires_configuration_body() {
        let mut sentence = claim_sentence(int_token("before"), int_variable("after", "exists"));
        sentence.body = DefinitionRuleBody::Term(
            DefinitionTerm::rewrite(
                node("term-rewrite"),
                DefinitionSortRef::Builtin(BuiltinSort::Int),
                int_token("term-before"),
                int_variable("term-after", "exists"),
            )
            .expect("valid rewrite"),
        );
        assert!(matches!(
            validate_rule(
                &sentence,
                None,
                &BTreeMap::new(),
                &BTreeMap::new(),
                &BTreeSet::new(),
                &BTreeSet::new(),
                &BTreeMap::new(),
                &mut BTreeSet::new(),
            ),
            Err(DefinitionValidationError::ClaimBodyNotConfiguration(_))
        ));
    }
}
