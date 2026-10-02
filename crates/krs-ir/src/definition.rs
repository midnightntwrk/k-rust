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
use crate::ir_level::DefinitionLevel;
use crate::ir_validation::{
    collect_configuration_nodes, insert_node, require_kind, require_sort,
    validate_fixed_configuration, validate_precedence_order, validate_production_shape,
    validate_rule, validate_subsort_order, validate_term, variable_scope,
};
use crate::sorted::{SortKey, SortedByKey};
use crate::{
    ApplicationRef, BuiltinOperation, BuiltinSort, GrammarProductionItem,
    GrammarProductionItemKind, GroupAssociativitySentence, HookOperation, HookPointSortSource,
    IrIdentityError, ItemKind, ListOperation, MapOperation, ModuleId, NodeOrigin,
    PrecedenceRelation, ProductionAttribute, ProductionGroupId, SchemaVersion, SemanticId,
    SentenceKind, SetOperation, SourceMapKey, StableItemId,
};
use crate::{CellContentFrame, FixedConfiguration, FixedConfigurationRewrite};

impl SortKey for DefinitionModule {
    type Key = ModuleId;
    fn sort_key(&self) -> &Self::Key {
        &self.id
    }
}

impl SortKey for ProductionGroupIdentity {
    type Key = ProductionGroupId;
    fn sort_key(&self) -> &Self::Key {
        &self.id
    }
}

impl SortKey for DefinitionSentence {
    type Key = SourceMapKey;
    fn sort_key(&self) -> &Self::Key {
        self.origin().key()
    }
}

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
        validated_id(crate::IrIdentityKind::SymbolId, value.into()).map(Self)
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
pub type DefinitionSortRef = crate::IrSortRef<SymbolId>;

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
        validated_id(crate::IrIdentityKind::LabelId, value.into()).map(Self)
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
}

/// The sole declaration of a generated symbol's ID and emitted K name.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SymbolIdentity {
    id: SymbolId,
    emitted_name: String,
    kind: SymbolKind,
}

const GENERATED_PRODUCTION_SYMBOL_PREFIX: &str = "krsGenerated_";

impl SymbolIdentity {
    /// Builds the reserved generated-production symbol name from its owner hash.
    #[must_use]
    pub fn generated_production_name(hash: &str) -> String {
        format!("{GENERATED_PRODUCTION_SYMBOL_PREFIX}{hash}")
    }

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
            return Err(DefinitionValidationError::EmptyText(
                crate::IrField::SymbolName,
            ));
        }
        if emitted_name.contains(['/', '\\']) {
            return Err(DefinitionValidationError::AdapterSpecificValue(
                crate::IrField::SymbolName,
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

const FALLBACK_LABEL_PREFIX: &str = "krsRule_";

impl LabelIdentity {
    /// Builds the reserved fallback label name from its owner hash.
    #[must_use]
    pub fn fallback_name(hash: &str) -> String {
        format!("{FALLBACK_LABEL_PREFIX}{hash}")
    }

    /// Recognizes an emitted label beginning with the reserved fallback prefix.
    #[must_use]
    pub fn is_fallback(&self) -> bool {
        self.emitted_name.starts_with(FALLBACK_LABEL_PREFIX)
    }

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
            return Err(DefinitionValidationError::EmptyText(
                crate::IrField::LabelName,
            ));
        }
        if emitted_name.contains(['/', '\\']) {
            return Err(DefinitionValidationError::AdapterSpecificValue(
                crate::IrField::LabelName,
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
    schema_version: SchemaVersion,
    main_module: ModuleId,
    modules: SortedByKey<DefinitionModule>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct DefinitionIrWire {
    schema_version: SchemaVersion,
    main_module: ModuleId,
    modules: Vec<DefinitionModule>,
}

impl<'de> Deserialize<'de> for DefinitionIr {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = DefinitionIrWire::deserialize(deserializer)?;
        if wire.schema_version != SchemaVersion::CURRENT {
            return Err(serde::de::Error::custom(format_args!(
                "unsupported Definition IR schema {}; expected {}",
                wire.schema_version.0,
                SchemaVersion::CURRENT.0
            )));
        }
        Self::new(wire.main_module, wire.modules).map_err(serde::de::Error::custom)
    }
}

impl DefinitionIr {
    /// Validates modules, symbols, labels, origins, references, and the sole
    /// configuration.
    ///
    /// # Errors
    ///
    /// Returns [`DefinitionValidationError`] for any invalid invariant.
    pub fn new(
        main_module: ModuleId,
        modules: Vec<DefinitionModule>,
    ) -> Result<Self, DefinitionValidationError> {
        let definition = Self {
            schema_version: SchemaVersion::CURRENT,
            main_module,
            modules: SortedByKey::new(modules),
        };
        definition.validate()?;
        Ok(definition)
    }

    /// Rebuilds the definition and its modules from permuted set-like inputs.
    ///
    /// # Panics
    ///
    /// Panics if this validated definition cannot be rebuilt.
    #[cfg(feature = "test-support")]
    #[must_use]
    pub fn permute_sets(&self, seed: u64) -> Self {
        let mut modules = self
            .modules
            .iter()
            .map(|module| module.permute_sets(seed))
            .collect::<Vec<_>>();
        crate::testing::permute(&mut modules, seed);
        Self::new(self.main_module.clone(), modules).unwrap_or_else(|error| {
            panic!("DefinitionIr seed {seed}: permuted rebuild failed: {error}")
        })
    }

    /// Returns the independent IR schema version.
    #[must_use]
    pub const fn schema_version(&self) -> SchemaVersion {
        self.schema_version
    }
    /// Returns the selected main module.
    #[must_use]
    pub const fn main_module(&self) -> &ModuleId {
        &self.main_module
    }
    /// Returns modules in canonical ID order.
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
        let mut json = serde_json::to_string_pretty(self)?;
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
            insert_node::<DefinitionLevel>(&mut nodes, module.origin.key())?;
            for group in &module.production_groups {
                insert_node::<DefinitionLevel>(&mut nodes, group.origin.key())?;
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
                insert_node::<DefinitionLevel>(&mut nodes, sentence.origin().key())?;
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
                            insert_node::<DefinitionLevel>(&mut nodes, item.origin().key())?;
                        }
                        for attribute in &sentence.attributes {
                            insert_node::<DefinitionLevel>(&mut nodes, attribute.origin().key())?;
                            if let ProductionAttribute::Strictness {
                                using,
                                fields,
                                result_sort,
                                ..
                            } = attribute
                            {
                                if let Some(using) = using {
                                    insert_node::<DefinitionLevel>(
                                        &mut nodes,
                                        using.origin().key(),
                                    )?;
                                }
                                for field in fields {
                                    insert_node::<DefinitionLevel>(
                                        &mut nodes,
                                        field.origin().key(),
                                    )?;
                                }
                                insert_node::<DefinitionLevel>(
                                    &mut nodes,
                                    result_sort.origin().key(),
                                )?;
                            }
                        }
                    }
                    DefinitionSentence::Precedence(_) | DefinitionSentence::Associativity(_) => {}
                    DefinitionSentence::Configuration(sentence) => {
                        configurations += 1;
                        insert_node::<DefinitionLevel>(
                            &mut nodes,
                            sentence.initializer_origin().key(),
                        )?;
                        collect_configuration_nodes::<DefinitionLevel>(
                            sentence,
                            &mut (&mut symbols, &mut symbol_names),
                            &mut nodes,
                        )?;
                    }
                    DefinitionSentence::ContextAlias(sentence) => {
                        if sentence.id.item_kind() != ItemKind::ContextAlias
                            || !context_aliases.insert(sentence.id.clone())
                        {
                            return Err(DefinitionValidationError::AdapterSpecificValue(
                                crate::IrField::ContextAliasIdentity,
                            ));
                        }
                        insert_node::<DefinitionLevel>(&mut nodes, sentence.name_origin.key())?;
                        insert_node::<DefinitionLevel>(&mut nodes, sentence.here_origin.key())?;
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
                DefinitionSentence::Configuration(configuration) => Some(configuration),
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
                        require_kind::<DefinitionLevel>(
                            &symbols,
                            sentence.symbol.id(),
                            SymbolKind::Sort,
                        )?;
                    }
                    DefinitionSentence::Subsort(sentence) => {
                        require_sort::<DefinitionLevel>(&symbols, &sentence.subsort)?;
                        require_sort::<DefinitionLevel>(&symbols, &sentence.supersort)?;
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
                    DefinitionSentence::Configuration(sentence) => {
                        validate_fixed_configuration::<DefinitionLevel>(
                            sentence,
                            &symbols,
                            &production_signatures,
                            &subsort_parents,
                            &mut nodes,
                        )?;
                    }
                    DefinitionSentence::ContextAlias(sentence) => validate_context_alias(
                        sentence,
                        &symbols,
                        &production_signatures,
                        &subsort_parents,
                        &mut nodes,
                    )?,
                    DefinitionSentence::Rule(sentence) => {
                        validate_rule::<DefinitionLevel>(
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
        validate_hook_point_constructors(&self.modules)?;
        validate_precedence_order::<DefinitionLevel>(&self.modules)?;
        validate_subsort_order::<DefinitionLevel>(&subsort_parents)?;
        Ok(())
    }
}

/// One generated K module.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DefinitionModule {
    origin: NodeOrigin,
    id: ModuleId,
    imports: BTreeSet<ModuleId>,
    production_groups: SortedByKey<ProductionGroupIdentity>,
    sentences: SortedByKey<DefinitionSentence>,
}

impl DefinitionModule {
    /// Creates a module with canonical production-group and sentence order.
    #[must_use]
    pub fn new(
        origin: NodeOrigin,
        id: ModuleId,
        imports: Vec<ModuleId>,
        production_groups: Vec<ProductionGroupIdentity>,
        sentences: Vec<DefinitionSentence>,
    ) -> Self {
        Self {
            origin,
            id,
            imports: imports.into_iter().collect(),
            production_groups: SortedByKey::new(production_groups),
            sentences: SortedByKey::new(sentences),
        }
    }

    /// Rebuilds every set-like module collection from permuted inputs.
    #[cfg(feature = "test-support")]
    #[must_use]
    pub fn permute_sets(&self, seed: u64) -> Self {
        let mut imports = self.imports.iter().cloned().collect::<Vec<_>>();
        let mut production_groups = self.production_groups.iter().cloned().collect::<Vec<_>>();
        let mut sentences = self.sentences.iter().cloned().collect::<Vec<_>>();
        crate::testing::permute(&mut imports, seed);
        crate::testing::permute(&mut production_groups, seed);
        crate::testing::permute(&mut sentences, seed);
        Self::new(
            self.origin.clone(),
            self.id.clone(),
            imports,
            production_groups,
            sentences,
        )
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
    pub const fn imports(&self) -> &BTreeSet<ModuleId> {
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
pub type ContextAliasSentence = crate::IrContextAlias<crate::DefinitionLevel>;

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
                crate::IrField::ProductionGroupName,
            ));
        }
        if emitted_name.contains(['/', '\\']) {
            return Err(DefinitionValidationError::AdapterSpecificValue(
                crate::IrField::ProductionGroupName,
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
pub type SubsortSentence = crate::IrSubsort<crate::DefinitionLevel>;

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
        validate_production_shape::<DefinitionLevel>(
            symbol.id(),
            &result_sort,
            &items,
            &attributes,
        )?;
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

/// The one fixed, possibly nested, source configuration sentence.
pub type ConfigurationSentence = FixedConfiguration<DefinitionSortRef, SymbolId, DefinitionTerm>;

/// Definition-level variable declaration.
pub type DefinitionVariable = crate::IrVariable<crate::DefinitionLevel>;

/// One provenance-bearing object-language Boolean rule condition.
pub type DefinitionRuleCondition = crate::IrRuleCondition<crate::DefinitionLevel>;

/// One explicitly scoped claim binder declaration.
pub type DefinitionClaimBinder = crate::IrClaimBinder<crate::DefinitionLevel>;

/// Typed reachability metadata present only on claims.
pub type DefinitionClaim = crate::IrClaim<crate::DefinitionLevel>;

/// One explicit equation or transition-rule priority.
pub type DefinitionRulePriority = crate::IrRulePriority;

/// Simplifier classification and optional ordering hint.
pub type DefinitionSimplification = crate::IrSimplification;

/// One numeric simplification ordering hint.
pub type DefinitionSimplificationPriority = crate::IrSimplificationPriority;

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
pub type DefinitionRuleBody = crate::IrRuleBody<crate::DefinitionLevel>;
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
    /// Attaches an explicit equation or transition-rule priority.
    ///
    /// # Errors
    ///
    /// Returns [`DefinitionValidationError::InvalidRulePriority`] when
    /// priority metadata is attached to anything other than an equation or transition.
    pub fn with_priority(
        mut self,
        priority: Option<DefinitionRulePriority>,
    ) -> Result<Self, DefinitionValidationError> {
        if priority.is_some()
            && !matches!(self.kind, SentenceKind::Equation | SentenceKind::Transition)
        {
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
    /// Returns the ordinary term rewrite body, when present.
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

/// A typed Definition IR term whose nested nodes retain their own origins and keys.
pub type DefinitionTerm = crate::IrTerm<crate::DefinitionLevel>;

/// Structured target-neutral Definition term forms.
pub type DefinitionTermKind = crate::IrTermKind<crate::DefinitionLevel>;

/// Typed Definition IR validation failure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DefinitionValidationError {
    /// No module exists.
    EmptyDefinition,
    /// Blank text is not representable.
    EmptyText(crate::IrField),
    /// A path-shaped or adapter-shaped value attempted to cross the boundary.
    AdapterSpecificValue(crate::IrField),
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
    /// A definition requires exactly one configuration.
    ConfigurationCount(usize),
    /// A production has no terminal/nonterminal items.
    EmptyProduction(SymbolId),
    /// The same classified attribute family occurred more than once.
    DuplicateProductionAttribute(crate::ProductionAttributeFamily),
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
    /// A typed hook's declared result or argument sorts did not match its catalog signature.
    InvalidHookSignature(HookOperation),
    /// A BN128 hook lacks a unique constructor for its required point sort.
    InvalidBn128PointConstructor {
        /// The hook requiring the point.
        hook: HookOperation,
        /// The declared sort used by the hook, if any.
        sort: String,
        /// The point signature required by the backend.
        expected_signature: crate::Bn128PointSignature,
        /// Constructors matching that signature in the definition.
        matching_constructors: usize,
    },
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
    /// Rule priority metadata occurred on an unsupported sentence kind.
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
    /// A Set operation had the wrong result sort, arity, or operand sorts.
    SetOperationSignature(SetOperation),
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
            Self::DuplicateModule(id) => write!(formatter, "duplicate module {id}"),
            Self::DuplicateSourceMapKey(key) => {
                write!(formatter, "duplicate source-map key {key}")
            }
            Self::DuplicateSymbol(id) => write!(formatter, "duplicate symbol {id}"),
            Self::DuplicateLabel(id) => write!(formatter, "duplicate label {id}"),
            Self::DuplicateEmittedName(name) => {
                write!(formatter, "duplicate emitted name {name:?}")
            }
            Self::DuplicateProductionGroup(group) => {
                write!(formatter, "duplicate production group {group}")
            }
            Self::DanglingProductionGroup(group) => {
                write!(formatter, "dangling production group {group}")
            }
            Self::PrecedenceCycle(group) => write!(
                formatter,
                "production-group precedence contains a cycle through {group}"
            ),
            Self::SubsortCycle(sort) => {
                write!(
                    formatter,
                    "subsort relation contains a cycle through {sort}"
                )
            }
            Self::DanglingModule(id) => write!(formatter, "dangling module {id}"),
            Self::DanglingSymbol(id) => write!(formatter, "dangling symbol {id}"),
            Self::WrongSymbolKind {
                id,
                expected,
                actual,
            } => write!(
                formatter,
                "symbol {id} has kind {actual}, expected {expected}"
            ),
            Self::ConfigurationCount(count) => write!(
                formatter,
                "Definition IR requires exactly one configuration, found {count}"
            ),
            Self::EmptyProduction(id) => {
                write!(formatter, "production {id} must contain syntax items")
            }
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
                write!(formatter, "duplicate variable {id}")
            }
            Self::DanglingVariable(id) => write!(formatter, "dangling variable {id}"),
            Self::VariableSortMismatch(id) => {
                write!(formatter, "variable {id} is referenced with the wrong sort")
            }
            Self::VariableClosure => {
                formatter.write_str("declared variables must exactly match sentence uses")
            }
            Self::ApplicationSignature(id) => {
                write!(formatter, "application does not match production {id}")
            }
            Self::BuiltinApplicationSignature(operation) => write!(
                formatter,
                "application does not match builtin signature {operation}"
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
                write!(formatter, "rule {id} body must be a rewrite")
            }
            Self::InvalidEquationRoot(id) => write!(
                formatter,
                "equation {id} must be headed by a functional production"
            ),
            Self::InvalidAliasRoot(id) => write!(
                formatter,
                "alias clause {id} must be headed by an alias production"
            ),
            Self::InvalidSimplificationRoot(id) => write!(
                formatter,
                "simplification {id} must be headed by a function or builtin function"
            ),
            Self::InvalidSimplificationMetadata(id) => write!(
                formatter,
                "simplification metadata disagrees with sentence {id}"
            ),
            Self::InvalidRulePriority(id) => write!(
                formatter,
                "rule priority cannot occur on unsupported sentence {id}"
            ),
            Self::InvalidClaimMetadata(id) => {
                write!(formatter, "claim metadata disagrees with sentence {id}")
            }
            Self::ClaimBodyNotConfiguration(id) => write!(
                formatter,
                "claim {id} requires a configuration rewrite body"
            ),
            Self::InvalidClaimBinder(id) => write!(
                formatter,
                "claim binder {id} is repeated, unbound, or has the wrong sort"
            ),
            Self::ExistentialScopeViolation(id) => write!(
                formatter,
                "existential claim binder {id} cannot occur in the left-hand side or requires condition"
            ),
            Self::UnusedExistential(id) => write!(
                formatter,
                "existential claim binder {id} must occur in the right-hand side or ensures condition"
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
            Self::InvalidHookSignature(operation) => {
                write!(
                    formatter,
                    "hook has invalid production signature {operation}"
                )
            }
            Self::InvalidBn128PointConstructor {
                hook,
                sort,
                expected_signature,
                matching_constructors,
            } => write!(
                formatter,
                "hook {hook} requires a unique {expected_signature} constructor; sort {sort} has {matching_constructors} matching constructors"
            ),
            Self::InvalidAliasProduction => {
                formatter.write_str("alias metadata cannot be combined with function metadata")
            }
            Self::InitializerTreeMismatch => {
                formatter.write_str("initializer tree must exactly mirror the fixed cell tree")
            }
            Self::InitializerLeafSortMismatch => {
                formatter.write_str("initializer leaf term must match its cell content sort")
            }
            Self::MapSortMismatch => formatter.write_str("Map term must have builtin Map sort"),
            Self::MapOperationSignature(operation) => {
                write!(formatter, "{operation} has an invalid signature")
            }
            Self::ListOperationSignature(operation) => {
                write!(formatter, "{operation} has an invalid signature")
            }
            Self::SetOperationSignature(operation) => {
                write!(formatter, "{operation} has an invalid signature")
            }
            Self::ConfigurationRuleWithoutFixedConfiguration(id) => write!(
                formatter,
                "configuration rule {id} requires a general fixed configuration"
            ),
            Self::ConfigurationRuleTargetMismatch(id) => write!(
                formatter,
                "configuration rule {id} names a different fixed configuration"
            ),
            Self::InvalidCellFraming => formatter.write_str(
                "configuration rewrite must mention or explicitly omit every fixed leaf cell",
            ),
            Self::CellFrameSortMismatch => {
                formatter.write_str("cell-content frame is incompatible with cell sort")
            }
            Self::CellFrameBindingMismatch(id) => write!(
                formatter,
                "cell-frame binding {id} is missing or has the wrong sort"
            ),
        }
    }
}
impl Error for DefinitionValidationError {}

fn expect_symbol_kind(
    symbol: &SymbolIdentity,
    expected: SymbolKind,
) -> Result<(), DefinitionValidationError> {
    crate::ir_validation::expect_kind::<DefinitionLevel>(&symbol.id, symbol.kind, expected)
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

fn validate_symbol_text(symbol: &SymbolIdentity) -> Result<(), DefinitionValidationError> {
    if symbol.emitted_name.trim().is_empty() {
        return Err(DefinitionValidationError::EmptyText(
            crate::IrField::SymbolName,
        ));
    }
    if symbol.emitted_name.contains(['/', '\\']) {
        return Err(DefinitionValidationError::AdapterSpecificValue(
            crate::IrField::SymbolName,
        ));
    }
    Ok(())
}

fn validate_label_text(label: &LabelIdentity) -> Result<(), DefinitionValidationError> {
    if label.emitted_name.trim().is_empty() {
        return Err(DefinitionValidationError::EmptyText(
            crate::IrField::LabelName,
        ));
    }
    if label.emitted_name.contains(['/', '\\']) {
        return Err(DefinitionValidationError::AdapterSpecificValue(
            crate::IrField::LabelName,
        ));
    }
    Ok(())
}

fn validate_production(
    sentence: &ProductionSentence,
    symbols: &BTreeMap<SymbolId, SymbolKind>,
    groups: &BTreeSet<ProductionGroupId>,
    context_aliases: &BTreeSet<StableItemId>,
) -> Result<(), DefinitionValidationError> {
    require_kind::<DefinitionLevel>(symbols, sentence.symbol.id(), SymbolKind::Production)?;
    require_sort::<DefinitionLevel>(symbols, &sentence.result_sort)?;
    if sentence.items.is_empty() {
        return Err(DefinitionValidationError::EmptyProduction(
            sentence.symbol.id.clone(),
        ));
    }
    for item in &sentence.items {
        if let GrammarProductionItemKind::NonTerminal { sort, .. } = item.kind() {
            require_sort::<DefinitionLevel>(symbols, sort)?;
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
                require_sort::<DefinitionLevel>(symbols, result_sort.sort())?;
                if using
                    .as_ref()
                    .is_some_and(|alias| !context_aliases.contains(alias.alias()))
                {
                    return Err(DefinitionValidationError::AdapterSpecificValue(
                        crate::IrField::StrictnessContextAliasReference,
                    ));
                }
            }
            ProductionAttribute::Documentation { .. }
            | ProductionAttribute::Function { .. }
            | ProductionAttribute::Total { .. }
            | ProductionAttribute::Hook { .. }
            | ProductionAttribute::Alias { .. }
            | ProductionAttribute::Token { .. }
            | ProductionAttribute::Bracket { .. }
            | ProductionAttribute::Avoid { .. }
            | ProductionAttribute::Format { .. } => {}
        }
    }
    validate_production_shape::<DefinitionLevel>(
        sentence.symbol.id(),
        &sentence.result_sort,
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
            crate::IrField::ContextAliasNameHere,
        ));
    }
    let scope = variable_scope::<DefinitionLevel>(&sentence.variables, symbols)?;
    for cell in sentence.body.cells() {
        require_kind::<DefinitionLevel>(symbols, cell.cell(), SymbolKind::Cell)?;
        insert_node::<DefinitionLevel>(nodes, cell.origin().key())?;
        validate_term::<DefinitionLevel>(
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
            insert_node::<DefinitionLevel>(nodes, origin.key())?;
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

fn validate_hook_point_constructors(
    modules: &[DefinitionModule],
) -> Result<(), DefinitionValidationError> {
    let sorts = modules
        .iter()
        .flat_map(|module| &module.sentences)
        .filter_map(|sentence| match sentence {
            DefinitionSentence::SyntaxSort(sort) => {
                Some((sort.symbol.id(), sort.symbol.emitted_name()))
            }
            _ => None,
        })
        .collect::<BTreeMap<_, _>>();
    let productions = modules
        .iter()
        .flat_map(|module| &module.sentences)
        .filter_map(|sentence| match sentence {
            DefinitionSentence::Production(production) => Some(production),
            _ => None,
        })
        .collect::<Vec<_>>();
    let check = |hook,
                 expected_signature: crate::Bn128PointSignature,
                 used_sort: Option<&DefinitionSortRef>| {
        let expected_sort = expected_signature.sort_name();
        let arity = expected_signature.arity();
        let sort = if let Some(used_sort) = used_sort {
            match used_sort {
                DefinitionSortRef::Declared(id) => Some(id),
                DefinitionSortRef::Builtin(_) => None,
            }
        } else {
            sorts
                .iter()
                .find(|(_, name)| **name == expected_sort)
                .map(|(id, _)| *id)
        };
        let sort_name = sort
            .and_then(|id| sorts.get(id).copied())
            .unwrap_or(expected_sort);
        let matching_constructors = productions
            .iter()
            .filter(|production| {
                matches!(production.result_sort(), DefinitionSortRef::Declared(id) if Some(id) == sort)
                    && !production.attributes().iter().any(|attribute| {
                        matches!(attribute, ProductionAttribute::Function { .. }
                            | ProductionAttribute::Alias { .. }
                            | ProductionAttribute::Token { .. }
                            | ProductionAttribute::Bracket { .. })
                    })
                    && production
                        .items()
                        .iter()
                        .filter_map(|item| match item.kind() {
                            GrammarProductionItemKind::NonTerminal { sort, .. } => Some(sort),
                            _ => None,
                        })
                        .collect::<Vec<_>>() == vec![&DefinitionSortRef::int(); arity]
            })
            .count();
        if sort_name == expected_sort && matching_constructors == 1 {
            Ok(())
        } else {
            Err(DefinitionValidationError::InvalidBn128PointConstructor {
                hook,
                sort: sort_name.to_owned(),
                expected_signature,
                matching_constructors,
            })
        }
    };
    for production in &productions {
        let Some(hook) = production
            .attributes()
            .iter()
            .find_map(|attribute| match attribute {
                ProductionAttribute::Hook { operation, .. } => Some(*operation),
                _ => None,
            })
        else {
            continue;
        };
        let first_argument = production
            .items()
            .iter()
            .find_map(|item| match item.kind() {
                GrammarProductionItemKind::NonTerminal { sort, .. } => Some(sort),
                _ => None,
            });
        for constraint in hook.spec().signature.point_constructors() {
            let used_sort = match constraint.source {
                HookPointSortSource::FirstArgument => first_argument,
                HookPointSortSource::Result => Some(production.result_sort()),
                HookPointSortSource::Named => None,
            };
            check(hook, constraint.signature, used_sort)?;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ClaimModality;
    use crate::ir_validation::validate_claim;
    use crate::{CellPost, FixedCellClause};

    #[test]
    fn fallback_label_recognition_preserves_prefix_predicate() {
        let label = |name: &str| LabelIdentity::new(LabelId::new("label").unwrap(), name).unwrap();
        let fallback = LabelIdentity::fallback_name("0123abcdef");
        assert_eq!(fallback, "krsRule_0123abcdef");
        assert!(label(&fallback).is_fallback());
        for name in ["krsRule_", "krsRule_nonhex"] {
            assert!(label(name).is_fallback());
        }
        for name in ["krsRule", "prefix_krsRule_0", "ordinary"] {
            assert!(!label(name).is_fallback());
        }
        assert_eq!(
            SymbolIdentity::generated_production_name("0123abcdef"),
            "krsGenerated_0123abcdef"
        );
    }

    fn node(key: &str) -> NodeOrigin {
        crate::testing::origin_in(
            key,
            crate::testing::package("ORG-EXAMPLE-CLAIM", "claim"),
            "src/lib.rs",
            crate::testing::digest_with("b".repeat(64)),
            0,
            1,
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
        let scope = variable_scope::<DefinitionLevel>(&sentence.variables, &BTreeMap::new())?;
        validate_claim::<DefinitionLevel>(
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
            validate_rule::<DefinitionLevel>(
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
            validate_rule::<DefinitionLevel>(
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
            validate_rule::<DefinitionLevel>(
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
