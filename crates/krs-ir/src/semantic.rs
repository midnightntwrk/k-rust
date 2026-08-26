//! Resolved, target-neutral KRS semantic IR.
//!
//! This representation records KRS meaning after descriptor collection and
//! name resolution. It deliberately contains neither generated K names nor
//! frontend-specific production metadata; those belong to Definition IR and
//! adapters respectively.

use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt;

use serde::{Deserialize, Deserializer, Serialize};

use crate::{
    ApplicationRef, BuiltinOperation, BuiltinSort, CellContentFrame, CellPost, FixedCell,
    FixedCellClause, FixedCellContent, FixedConfiguration, FixedConfigurationPattern,
    FixedConfigurationRewrite, FixedInitializerCell, FixedInitializerContent, FormatFragment,
    GrammarProductionItem, GrammarProductionItemKind, GroupAssociativitySentence, IrSchemaVersion,
    ItemKind, MapOperation, ModuleId, NodeOrigin, PrecedenceRelation, ProductionAttribute,
    ProductionFieldId, ProductionGroupId, SemanticId, SentenceKind, SourceMapKey, StableItemId,
};

/// Authored or compiler-provided semantic application reference.
pub type SemanticApplicationRef = ApplicationRef<StableItemId>;

/// A semantic grammar item carrying typed sort references.
pub type SemanticProductionItem = GrammarProductionItem<SemanticSortRef>;

/// Classified semantic production metadata.
pub type SemanticProductionAttribute = ProductionAttribute<SemanticSortRef>;

/// A resolved sort reference in semantic IR.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(tag = "sort_source", content = "sort", rename_all = "snake_case")]
pub enum SemanticSortRef {
    /// Sort declared by a KRS item or selected dependency.
    Declared(StableItemId),
    /// Sort intrinsic to the K language.
    Builtin(BuiltinSort),
}

impl SemanticSortRef {
    /// Refers to a declared semantic sort.
    #[must_use]
    pub const fn declared(sort: StableItemId) -> Self {
        Self::Declared(sort)
    }

    /// Refers to the builtin K computation-sequence sort.
    #[must_use]
    pub const fn k_sequence() -> Self {
        Self::Builtin(BuiltinSort::KSequence)
    }

    /// Refers to the pinned compiler-provided integer sort.
    #[must_use]
    pub const fn int() -> Self {
        Self::Builtin(BuiltinSort::Int)
    }

    /// Refers to the pinned compiler-provided Boolean sort.
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
}

/// A checked resolved semantic theory.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SemanticTheory {
    schema_version: IrSchemaVersion,
    modules: Vec<SemanticModule>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct SemanticTheoryWire {
    schema_version: IrSchemaVersion,
    modules: Vec<SemanticModule>,
}

impl<'de> Deserialize<'de> for SemanticTheory {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = SemanticTheoryWire::deserialize(deserializer)?;
        if wire.schema_version != IrSchemaVersion::CURRENT {
            return Err(serde::de::Error::custom(format_args!(
                "unsupported semantic IR schema {}; expected {}",
                wire.schema_version.0,
                IrSchemaVersion::CURRENT.0
            )));
        }
        Self::new(wire.modules).map_err(serde::de::Error::custom)
    }
}

impl SemanticTheory {
    /// Validates a complete theory. Exactly one configuration is required by
    /// the M2 contract.
    ///
    /// # Errors
    ///
    /// Returns [`SemanticValidationError`] for any invalid graph invariant.
    pub fn new(modules: Vec<SemanticModule>) -> Result<Self, SemanticValidationError> {
        let theory = Self {
            schema_version: IrSchemaVersion::CURRENT,
            modules,
        };
        theory.validate()?;
        Ok(theory)
    }

    /// Returns the IR schema version.
    #[must_use]
    pub const fn schema_version(&self) -> IrSchemaVersion {
        self.schema_version
    }

    /// Returns modules in caller order. Canonical serialization treats the
    /// module collection as a set.
    #[must_use]
    pub fn modules(&self) -> &[SemanticModule] {
        &self.modules
    }

    /// Returns deterministic, path-free JSON with one trailing newline.
    ///
    /// # Errors
    ///
    /// Returns a JSON encoding error if the serde data model cannot be encoded.
    pub fn to_canonical_json(&self) -> serde_json::Result<String> {
        let mut canonical = self.clone();
        canonical.canonicalize();
        let mut json = serde_json::to_string_pretty(&canonical)?;
        json.push('\n');
        Ok(json)
    }

    fn canonicalize(&mut self) {
        for module in &mut self.modules {
            module.canonicalize();
        }
        self.modules.sort_by(|left, right| left.id.cmp(&right.id));
    }

    #[allow(clippy::too_many_lines)]
    fn validate(&self) -> Result<(), SemanticValidationError> {
        if self.modules.is_empty() {
            return Err(SemanticValidationError::EmptyTheory);
        }

        let mut module_ids = BTreeSet::new();
        let mut node_keys = BTreeSet::new();
        let mut declarations = BTreeMap::new();
        let mut production_signatures = BTreeMap::new();
        let mut functional_productions = BTreeSet::new();
        let mut alias_productions = BTreeSet::new();
        let mut sort_parents: BTreeMap<SemanticSortRef, Vec<SemanticSortRef>> = BTreeMap::new();
        let mut groups = BTreeSet::new();
        let mut semantic_ids = BTreeSet::new();
        let mut configurations = 0_usize;

        for module in &self.modules {
            insert_unique(
                &mut module_ids,
                module.id.clone(),
                "module",
                module.id.as_str(),
            )?;
            insert_node(&mut node_keys, module.origin.key())?;
            for sort in &module.sorts {
                validate_item_kind(&sort.id, ItemKind::Sort)?;
                insert_declaration(&mut declarations, &sort.id)?;
                insert_node(&mut node_keys, sort.origin.key())?;
            }
            for subsort in &module.subsorts {
                insert_node(&mut node_keys, subsort.origin.key())?;
                sort_parents
                    .entry(subsort.subsort.clone())
                    .or_default()
                    .push(subsort.supersort.clone());
            }
            for production in &module.productions {
                validate_item_kind(&production.id, ItemKind::Constructor)?;
                insert_declaration(&mut declarations, &production.id)?;
                insert_node(&mut node_keys, production.origin.key())?;
                validate_semantic_production_shape(
                    &production.id,
                    &production.items,
                    &production.attributes,
                )?;
                if production
                    .attributes
                    .iter()
                    .any(|attribute| matches!(attribute, ProductionAttribute::Function { .. }))
                {
                    functional_productions.insert(production.id.clone());
                }
                if production
                    .attributes
                    .iter()
                    .any(|attribute| matches!(attribute, ProductionAttribute::Alias { .. }))
                {
                    alias_productions.insert(production.id.clone());
                }
                for item in &production.items {
                    insert_node(&mut node_keys, item.origin().key())?;
                }
                for attribute in &production.attributes {
                    insert_node(&mut node_keys, attribute.origin().key())?;
                    if let ProductionAttribute::Strictness {
                        using,
                        fields,
                        result_sort,
                        ..
                    } = attribute
                    {
                        if let Some(using) = using {
                            insert_node(&mut node_keys, using.origin().key())?;
                        }
                        for field in fields {
                            insert_node(&mut node_keys, field.origin().key())?;
                        }
                        insert_node(&mut node_keys, result_sort.origin().key())?;
                    }
                    if let ProductionAttribute::Group { group, .. } = attribute {
                        groups.insert(group.clone());
                    }
                }
                production_signatures.insert(
                    production.id.clone(),
                    (
                        production.result_sort.clone(),
                        production
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
            }
            for precedence in &module.precedences {
                insert_node(&mut node_keys, precedence.origin().key())?;
            }
            for associativity in &module.associativities {
                insert_node(&mut node_keys, associativity.origin().key())?;
            }
            for rule in &module.rules {
                let expected = match rule.kind {
                    SentenceKind::Transition => ItemKind::Rule,
                    SentenceKind::Equation => ItemKind::Equation,
                    SentenceKind::Simplification => ItemKind::Simplification,
                    SentenceKind::Alias => ItemKind::Alias,
                    SentenceKind::Claim => ItemKind::Claim,
                };
                validate_item_kind(&rule.id, expected)?;
                insert_declaration(&mut declarations, &rule.id)?;
                insert_node(&mut node_keys, rule.origin.key())?;
            }
            for alias in &module.context_aliases {
                validate_item_kind(&alias.id, ItemKind::ContextAlias)?;
                insert_declaration(&mut declarations, &alias.id)?;
                insert_node(&mut node_keys, alias.origin.key())?;
                insert_node(&mut node_keys, alias.name_origin.key())?;
                insert_node(&mut node_keys, alias.here_origin.key())?;
            }
            if let Some(configuration) = &module.configuration {
                configurations += 1;
                match configuration {
                    SemanticConfiguration::Legacy(configuration) => {
                        insert_semantic_id(&mut semantic_ids, &configuration.id, "configuration")?;
                        insert_semantic_id(&mut semantic_ids, &configuration.cell.id, "cell")?;
                        insert_semantic_id(
                            &mut semantic_ids,
                            &configuration.initializer.id,
                            "initializer",
                        )?;
                        if configuration.cell.name.trim().is_empty() {
                            return Err(SemanticValidationError::EmptyText("cell name"));
                        }
                        insert_node(&mut node_keys, configuration.origin.key())?;
                        insert_node(&mut node_keys, configuration.cell.origin.key())?;
                        insert_node(&mut node_keys, configuration.initializer.origin.key())?;
                    }
                    SemanticConfiguration::Fixed(configuration) => {
                        insert_semantic_id(&mut semantic_ids, configuration.id(), "configuration")?;
                        insert_semantic_id(
                            &mut semantic_ids,
                            configuration.initializer_id(),
                            "initializer",
                        )?;
                        insert_node(&mut node_keys, configuration.origin().key())?;
                        insert_node(&mut node_keys, configuration.initializer_origin().key())?;
                        collect_fixed_configuration_nodes(
                            configuration,
                            &mut semantic_ids,
                            &mut node_keys,
                        )?;
                    }
                }
            }
        }

        if configurations != 1 {
            return Err(SemanticValidationError::ConfigurationCount(configurations));
        }
        let fixed_configuration = self.modules.iter().find_map(|module| {
            module
                .configuration
                .as_ref()
                .and_then(SemanticConfiguration::as_fixed)
        });

        for module in &self.modules {
            for import in &module.imports {
                if !module_ids.contains(import) {
                    return Err(SemanticValidationError::DanglingModule(import.clone()));
                }
            }
            for subsort in &module.subsorts {
                require_semantic_sort(&declarations, &subsort.subsort)?;
                require_semantic_sort(&declarations, &subsort.supersort)?;
            }
            for production in &module.productions {
                require_semantic_sort(&declarations, &production.result_sort)?;
                for item in &production.items {
                    if let GrammarProductionItemKind::NonTerminal { sort, .. } = item.kind() {
                        require_semantic_sort(&declarations, sort)?;
                    }
                }
                for attribute in &production.attributes {
                    if let ProductionAttribute::Strictness { result_sort, .. } = attribute {
                        require_semantic_sort(&declarations, result_sort.sort())?;
                    }
                    if let ProductionAttribute::Strictness {
                        using: Some(alias), ..
                    } = attribute
                    {
                        require_kind(&declarations, alias.alias(), ItemKind::ContextAlias)?;
                    }
                }
            }
            for precedence in &module.precedences {
                for group in precedence.higher().iter().chain(precedence.lower()) {
                    if !groups.contains(group) {
                        return Err(SemanticValidationError::DanglingProductionGroup(
                            group.clone(),
                        ));
                    }
                }
            }
            for associativity in &module.associativities {
                for group in associativity.groups() {
                    if !groups.contains(group) {
                        return Err(SemanticValidationError::DanglingProductionGroup(
                            group.clone(),
                        ));
                    }
                }
            }
            if let Some(configuration) = &module.configuration {
                match configuration {
                    SemanticConfiguration::Legacy(configuration) => {
                        require_semantic_sort(&declarations, &configuration.cell.sort)?;
                        validate_initializer(
                            &configuration.initializer,
                            &configuration.cell.sort,
                            &declarations,
                            &production_signatures,
                            &sort_parents,
                            &mut node_keys,
                        )?;
                    }
                    SemanticConfiguration::Fixed(configuration) => {
                        validate_fixed_configuration(
                            configuration,
                            &declarations,
                            &production_signatures,
                            &sort_parents,
                            &mut node_keys,
                        )?;
                    }
                }
            }
            for rule in &module.rules {
                validate_rule(
                    rule,
                    fixed_configuration,
                    &declarations,
                    &production_signatures,
                    &functional_productions,
                    &alias_productions,
                    &sort_parents,
                    &mut node_keys,
                )?;
            }
        }
        validate_precedence_order(&self.modules)?;
        validate_semantic_subsort_order(&sort_parents)?;
        Ok(())
    }
}

/// One resolved module. Imports are a set; declaration vectors are sentence
/// sets and are canonically sorted without reordering nested semantic data.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SemanticModule {
    origin: NodeOrigin,
    id: ModuleId,
    imports: Vec<ModuleId>,
    sorts: Vec<SemanticSort>,
    subsorts: Vec<SemanticSubsort>,
    productions: Vec<SemanticProduction>,
    precedences: Vec<PrecedenceRelation>,
    associativities: Vec<GroupAssociativitySentence>,
    #[serde(skip_serializing_if = "Option::is_none")]
    configuration: Option<SemanticConfiguration>,
    context_aliases: Vec<SemanticContextAlias>,
    rules: Vec<SemanticRule>,
}

impl SemanticModule {
    /// Creates a module. Cross-module references are checked by
    /// [`SemanticTheory::new`].
    #[must_use]
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        origin: NodeOrigin,
        id: ModuleId,
        imports: Vec<ModuleId>,
        sorts: Vec<SemanticSort>,
        subsorts: Vec<SemanticSubsort>,
        productions: Vec<SemanticProduction>,
        precedences: Vec<PrecedenceRelation>,
        associativities: Vec<GroupAssociativitySentence>,
        configuration: Option<SemanticConfiguration>,
        rules: Vec<SemanticRule>,
    ) -> Self {
        Self::new_with_context_aliases(
            origin,
            id,
            imports,
            sorts,
            subsorts,
            productions,
            precedences,
            associativities,
            configuration,
            Vec::new(),
            rules,
        )
    }

    /// Creates a module including source-level context aliases.
    #[must_use]
    #[allow(clippy::too_many_arguments)]
    pub fn new_with_context_aliases(
        origin: NodeOrigin,
        id: ModuleId,
        imports: Vec<ModuleId>,
        sorts: Vec<SemanticSort>,
        subsorts: Vec<SemanticSubsort>,
        productions: Vec<SemanticProduction>,
        precedences: Vec<PrecedenceRelation>,
        associativities: Vec<GroupAssociativitySentence>,
        configuration: Option<SemanticConfiguration>,
        context_aliases: Vec<SemanticContextAlias>,
        rules: Vec<SemanticRule>,
    ) -> Self {
        Self {
            origin,
            id,
            imports,
            sorts,
            subsorts,
            productions,
            precedences,
            associativities,
            configuration,
            context_aliases,
            rules,
        }
    }

    /// Returns this module's stable identity.
    #[must_use]
    pub const fn id(&self) -> &ModuleId {
        &self.id
    }
    /// Returns its origin.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns set-valued imports.
    #[must_use]
    pub fn imports(&self) -> &[ModuleId] {
        &self.imports
    }
    /// Returns sort declarations.
    #[must_use]
    pub fn sorts(&self) -> &[SemanticSort] {
        &self.sorts
    }
    /// Returns direct typed subsort edges.
    #[must_use]
    pub fn subsorts(&self) -> &[SemanticSubsort] {
        &self.subsorts
    }
    /// Returns productions.
    #[must_use]
    pub fn productions(&self) -> &[SemanticProduction] {
        &self.productions
    }
    /// Returns direct production-group precedence relations.
    #[must_use]
    pub fn precedences(&self) -> &[PrecedenceRelation] {
        &self.precedences
    }
    /// Returns group-associativity sentences.
    #[must_use]
    pub fn associativities(&self) -> &[GroupAssociativitySentence] {
        &self.associativities
    }
    /// Returns the optional module-local configuration.
    #[must_use]
    pub const fn configuration(&self) -> Option<&SemanticConfiguration> {
        self.configuration.as_ref()
    }
    /// Returns one-sided reusable context templates.
    #[must_use]
    pub fn context_aliases(&self) -> &[SemanticContextAlias] {
        &self.context_aliases
    }
    /// Returns relational sentences.
    #[must_use]
    pub fn rules(&self) -> &[SemanticRule] {
        &self.rules
    }

    fn canonicalize(&mut self) {
        self.imports.sort();
        self.imports.dedup();
        self.sorts.sort_by(|left, right| left.id.cmp(&right.id));
        self.subsorts.sort();
        self.productions
            .sort_by(|left, right| left.id.cmp(&right.id));
        self.precedences.sort();
        self.associativities.sort();
        self.context_aliases
            .sort_by(|left, right| left.id.cmp(&right.id));
        self.rules.sort_by(|left, right| left.id.cmp(&right.id));
    }
}

/// A resolved authored open sort declaration.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SemanticSort {
    origin: NodeOrigin,
    id: StableItemId,
    #[serde(default, skip_serializing_if = "crate::RustVisibility::is_inherited")]
    visibility: crate::RustVisibility,
    #[serde(skip_serializing_if = "Option::is_none")]
    explicit_symbol: Option<crate::ExplicitSymbol>,
}

impl SemanticSort {
    /// Creates a semantic sort declaration.
    #[must_use]
    pub const fn new(origin: NodeOrigin, id: StableItemId) -> Self {
        Self {
            origin,
            id,
            visibility: crate::RustVisibility::Inherited,
            explicit_symbol: None,
        }
    }
    /// Creates a semantic sort with exact author-facing API metadata.
    #[must_use]
    pub const fn with_api(
        origin: NodeOrigin,
        id: StableItemId,
        visibility: crate::RustVisibility,
        explicit_symbol: Option<crate::ExplicitSymbol>,
    ) -> Self {
        Self {
            origin,
            id,
            visibility,
            explicit_symbol,
        }
    }
    /// Returns the authored sort ID.
    #[must_use]
    pub const fn id(&self) -> &StableItemId {
        &self.id
    }
    /// Returns the origin.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns exact authored Rust visibility.
    #[must_use]
    pub const fn visibility(&self) -> &crate::RustVisibility {
        &self.visibility
    }
    /// Returns the optional explicit stable public identity.
    #[must_use]
    pub const fn explicit_symbol(&self) -> Option<&crate::ExplicitSymbol> {
        self.explicit_symbol.as_ref()
    }
}

/// One direct typed subsort edge. Either endpoint may be compiler-provided.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SemanticSubsort {
    origin: NodeOrigin,
    subsort: SemanticSortRef,
    supersort: SemanticSortRef,
}

impl SemanticSubsort {
    /// Creates a direct subsort edge.
    #[must_use]
    pub fn new(origin: NodeOrigin, subsort: SemanticSortRef, supersort: SemanticSortRef) -> Self {
        Self {
            origin,
            subsort,
            supersort,
        }
    }
    /// Returns edge provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns the smaller sort.
    #[must_use]
    pub const fn subsort(&self) -> &SemanticSortRef {
        &self.subsort
    }
    /// Returns the larger sort.
    #[must_use]
    pub const fn supersort(&self) -> &SemanticSortRef {
        &self.supersort
    }
}

/// A resolved nominal production with classified object grammar.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SemanticProduction {
    origin: NodeOrigin,
    id: StableItemId,
    result_sort: SemanticSortRef,
    items: Vec<SemanticProductionItem>,
    attributes: Vec<SemanticProductionAttribute>,
    #[serde(default, skip_serializing_if = "crate::RustVisibility::is_inherited")]
    visibility: crate::RustVisibility,
    #[serde(skip_serializing_if = "Option::is_none")]
    explicit_symbol: Option<crate::ExplicitSymbol>,
}

impl SemanticProduction {
    /// Creates and locally validates a classified production.
    ///
    /// # Errors
    ///
    /// Returns [`SemanticValidationError`] for an invalid production shape.
    pub fn new(
        origin: NodeOrigin,
        id: StableItemId,
        result_sort: SemanticSortRef,
        items: Vec<SemanticProductionItem>,
        attributes: Vec<SemanticProductionAttribute>,
    ) -> Result<Self, SemanticValidationError> {
        validate_semantic_production_shape(&id, &items, &attributes)?;
        Ok(Self {
            origin,
            id,
            result_sort,
            items,
            attributes,
            visibility: crate::RustVisibility::Inherited,
            explicit_symbol: None,
        })
    }
    /// Creates and validates a production with exact author-facing API metadata.
    ///
    /// # Errors
    ///
    /// Returns [`SemanticValidationError`] for an invalid production shape.
    pub fn with_api(
        origin: NodeOrigin,
        id: StableItemId,
        result_sort: SemanticSortRef,
        items: Vec<SemanticProductionItem>,
        attributes: Vec<SemanticProductionAttribute>,
        visibility: crate::RustVisibility,
        explicit_symbol: Option<crate::ExplicitSymbol>,
    ) -> Result<Self, SemanticValidationError> {
        validate_semantic_production_shape(&id, &items, &attributes)?;
        Ok(Self {
            origin,
            id,
            result_sort,
            items,
            attributes,
            visibility,
            explicit_symbol,
        })
    }
    /// Returns the authored production ID.
    #[must_use]
    pub const fn id(&self) -> &StableItemId {
        &self.id
    }
    /// Returns the origin.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns the result sort.
    #[must_use]
    pub const fn result_sort(&self) -> &SemanticSortRef {
        &self.result_sort
    }
    /// Returns ordered grammar items.
    #[must_use]
    pub fn items(&self) -> &[SemanticProductionItem] {
        &self.items
    }
    /// Returns classified production attributes.
    #[must_use]
    pub fn attributes(&self) -> &[SemanticProductionAttribute] {
        &self.attributes
    }
    /// Returns exact authored Rust visibility.
    #[must_use]
    pub const fn visibility(&self) -> &crate::RustVisibility {
        &self.visibility
    }
    /// Returns the optional explicit stable public identity.
    #[must_use]
    pub const fn explicit_symbol(&self) -> Option<&crate::ExplicitSymbol> {
        self.explicit_symbol.as_ref()
    }
}

/// One legacy M2 configuration or general ordered fixed configuration tree.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(untagged)]
pub enum SemanticConfiguration {
    /// Compatibility representation for the original one-cell M2 surface.
    Legacy(Box<SemanticLegacyConfiguration>),
    /// General M3B fixed/nested configuration.
    Fixed(Box<FixedConfiguration<SemanticSortRef, SemanticId, SemanticTerm>>),
}

/// The legacy M2 one-cell representation.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SemanticLegacyConfiguration {
    origin: NodeOrigin,
    id: SemanticId,
    cell: SemanticCell,
    initializer: SemanticInitializer,
}

impl SemanticConfiguration {
    /// Creates one configuration and its initializer.
    #[must_use]
    pub fn new(
        origin: NodeOrigin,
        id: SemanticId,
        cell: SemanticCell,
        initializer: SemanticInitializer,
    ) -> Self {
        Self::Legacy(Box::new(SemanticLegacyConfiguration {
            origin,
            id,
            cell,
            initializer,
        }))
    }

    /// Wraps one general fixed/nested configuration.
    #[must_use]
    pub fn fixed(
        configuration: FixedConfiguration<SemanticSortRef, SemanticId, SemanticTerm>,
    ) -> Self {
        Self::Fixed(Box::new(configuration))
    }
    /// Returns the semantic configuration ID.
    #[must_use]
    pub const fn id(&self) -> &SemanticId {
        match self {
            Self::Legacy(configuration) => &configuration.id,
            Self::Fixed(configuration) => configuration.id(),
        }
    }
    /// Returns the origin.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        match self {
            Self::Legacy(configuration) => &configuration.origin,
            Self::Fixed(configuration) => configuration.origin(),
        }
    }
    /// Returns the sole legacy fixed cell, when this is the M2 form.
    #[must_use]
    pub const fn cell(&self) -> Option<&SemanticCell> {
        match self {
            Self::Legacy(configuration) => Some(&configuration.cell),
            Self::Fixed(_) => None,
        }
    }
    /// Returns the legacy initializer, when this is the M2 form.
    #[must_use]
    pub const fn initializer(&self) -> Option<&SemanticInitializer> {
        match self {
            Self::Legacy(configuration) => Some(&configuration.initializer),
            Self::Fixed(_) => None,
        }
    }

    /// Returns the general fixed configuration, when present.
    #[must_use]
    pub const fn as_fixed(
        &self,
    ) -> Option<&FixedConfiguration<SemanticSortRef, SemanticId, SemanticTerm>> {
        match self {
            Self::Legacy(_) => None,
            Self::Fixed(configuration) => Some(configuration),
        }
    }
}

/// One fixed computation cell.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SemanticCell {
    origin: NodeOrigin,
    id: SemanticId,
    name: String,
    sort: SemanticSortRef,
}

impl SemanticCell {
    /// Creates a cell, rejecting an empty name.
    ///
    /// # Errors
    ///
    /// Returns [`SemanticValidationError`] for a blank cell name.
    pub fn new(
        origin: NodeOrigin,
        id: SemanticId,
        name: impl Into<String>,
        sort: SemanticSortRef,
    ) -> Result<Self, SemanticValidationError> {
        let name = name.into();
        if name.trim().is_empty() {
            return Err(SemanticValidationError::EmptyText("cell name"));
        }
        Ok(Self {
            origin,
            id,
            name,
            sort,
        })
    }
    /// Returns its semantic ID.
    #[must_use]
    pub const fn id(&self) -> &SemanticId {
        &self.id
    }
    /// Returns its origin.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns its exact authored name.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }
    /// Returns its content sort.
    #[must_use]
    pub const fn sort(&self) -> &SemanticSortRef {
        &self.sort
    }
}

/// Declarative configuration initializer.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SemanticInitializer {
    origin: NodeOrigin,
    id: SemanticId,
    variables: Vec<SemanticVariable>,
    body: SemanticTerm,
}

impl SemanticInitializer {
    /// Creates an initializer; variable order is preserved.
    #[must_use]
    pub const fn new(
        origin: NodeOrigin,
        id: SemanticId,
        variables: Vec<SemanticVariable>,
        body: SemanticTerm,
    ) -> Self {
        Self {
            origin,
            id,
            variables,
            body,
        }
    }
    /// Returns its ID.
    #[must_use]
    pub const fn id(&self) -> &SemanticId {
        &self.id
    }
    /// Returns its origin.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns ordered variables.
    #[must_use]
    pub fn variables(&self) -> &[SemanticVariable] {
        &self.variables
    }
    /// Returns the initialized cell content.
    #[must_use]
    pub const fn body(&self) -> &SemanticTerm {
        &self.body
    }
}

/// A resolved rule variable declaration.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SemanticVariable {
    id: SemanticId,
    sort: SemanticSortRef,
}

impl SemanticVariable {
    /// Declares a resolved variable.
    #[must_use]
    pub const fn new(id: SemanticId, sort: SemanticSortRef) -> Self {
        Self { id, sort }
    }
    /// Returns the stable variable ID.
    #[must_use]
    pub const fn id(&self) -> &SemanticId {
        &self.id
    }
    /// Returns its resolved sort.
    #[must_use]
    pub const fn sort(&self) -> &SemanticSortRef {
        &self.sort
    }
}

/// One provenance-bearing explicit emitted K rule label.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SemanticRuleLabel {
    origin: NodeOrigin,
    name: String,
}

/// One provenance-bearing object-language Boolean rule condition.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SemanticRuleCondition {
    origin: NodeOrigin,
    term: SemanticTerm,
}

/// One explicitly scoped claim binder declaration.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SemanticClaimBinder {
    origin: NodeOrigin,
    name_origin: NodeOrigin,
    id: SemanticId,
    sort_origin: NodeOrigin,
    sort: SemanticSortRef,
}

/// Typed reachability metadata which is present only on claims.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SemanticClaim {
    modality_origin: NodeOrigin,
    modality: crate::ClaimModality,
    #[serde(skip_serializing_if = "Option::is_none")]
    circularity_origin: Option<NodeOrigin>,
    universals: Vec<SemanticClaimBinder>,
    existentials: Vec<SemanticClaimBinder>,
    #[serde(skip_serializing_if = "Option::is_none")]
    ensures: Option<SemanticRuleCondition>,
}

impl SemanticClaimBinder {
    /// Creates one provenance-bearing scoped binder.
    #[must_use]
    pub const fn new(
        origin: NodeOrigin,
        name_origin: NodeOrigin,
        id: SemanticId,
        sort_origin: NodeOrigin,
        sort: SemanticSortRef,
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
    /// Resolved sort.
    #[must_use]
    pub const fn sort(&self) -> &SemanticSortRef {
        &self.sort
    }
}

impl SemanticClaim {
    /// Creates typed claim adjunct metadata.
    #[must_use]
    pub const fn new(
        modality_origin: NodeOrigin,
        modality: crate::ClaimModality,
        circularity_origin: Option<NodeOrigin>,
        universals: Vec<SemanticClaimBinder>,
        existentials: Vec<SemanticClaimBinder>,
        ensures: Option<SemanticRuleCondition>,
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
    /// Optional circularity provenance.
    #[must_use]
    pub const fn circularity_origin(&self) -> Option<&NodeOrigin> {
        self.circularity_origin.as_ref()
    }
    /// Universal binders.
    #[must_use]
    pub fn universals(&self) -> &[SemanticClaimBinder] {
        &self.universals
    }
    /// RHS-scoped existential binders.
    #[must_use]
    pub fn existentials(&self) -> &[SemanticClaimBinder] {
        &self.existentials
    }
    /// Object-Bool postcondition.
    #[must_use]
    pub const fn ensures(&self) -> Option<&SemanticRuleCondition> {
        self.ensures.as_ref()
    }
}

/// One explicit equation priority.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SemanticRulePriority {
    origin: NodeOrigin,
    value: u32,
}

/// Simplifier classification and optional ordering hint.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SemanticSimplification {
    origin: NodeOrigin,
    #[serde(skip_serializing_if = "Option::is_none")]
    priority: Option<SemanticSimplificationPriority>,
}

/// One numeric simplification ordering hint.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SemanticSimplificationPriority {
    origin: NodeOrigin,
    value: u32,
}

impl SemanticSimplification {
    /// Creates typed simplification metadata.
    #[must_use]
    pub const fn new(origin: NodeOrigin, priority: Option<SemanticSimplificationPriority>) -> Self {
        Self { origin, priority }
    }
    /// Returns marker provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns an optional numeric hint.
    #[must_use]
    pub const fn priority(&self) -> Option<&SemanticSimplificationPriority> {
        self.priority.as_ref()
    }
}

impl SemanticSimplificationPriority {
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

impl SemanticRulePriority {
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

impl SemanticRuleCondition {
    /// Creates a typed condition while retaining complete payload provenance.
    #[must_use]
    pub const fn new(origin: NodeOrigin, term: SemanticTerm) -> Self {
        Self { origin, term }
    }
    /// Returns complete condition-payload provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns the structured object-language condition term.
    #[must_use]
    pub const fn term(&self) -> &SemanticTerm {
        &self.term
    }
}

impl SemanticRuleLabel {
    /// Creates a portable explicit K rule label.
    ///
    /// # Errors
    ///
    /// Returns [`SemanticValidationError::InvalidRuleLabel`] for invalid text.
    pub fn new(
        origin: NodeOrigin,
        name: impl Into<String>,
    ) -> Result<Self, SemanticValidationError> {
        let name = name.into();
        if !crate::protocol_v6::valid_rule_label_name(&name) {
            return Err(SemanticValidationError::InvalidRuleLabel(name));
        }
        Ok(Self { origin, name })
    }

    /// Returns exact authored label-literal provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }

    /// Returns the exact emitted K label.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }
}

/// One relational semantic sentence.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SemanticRule {
    origin: NodeOrigin,
    id: StableItemId,
    kind: SentenceKind,
    #[serde(skip_serializing_if = "Option::is_none")]
    label: Option<SemanticRuleLabel>,
    #[serde(skip_serializing_if = "Option::is_none")]
    requires: Option<SemanticRuleCondition>,
    #[serde(skip_serializing_if = "Option::is_none")]
    priority: Option<SemanticRulePriority>,
    #[serde(skip_serializing_if = "Option::is_none")]
    simplification: Option<SemanticSimplification>,
    #[serde(skip_serializing_if = "Option::is_none")]
    claim: Option<SemanticClaim>,
    variables: Vec<SemanticVariable>,
    body: SemanticRuleBody,
}

/// One source-level, one-sided reusable fixed-configuration context template.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SemanticContextAlias {
    origin: NodeOrigin,
    id: StableItemId,
    name_origin: NodeOrigin,
    name: String,
    here_origin: NodeOrigin,
    here: SemanticId,
    variables: Vec<SemanticVariable>,
    body: FixedConfigurationPattern<SemanticId, SemanticTerm>,
}

impl SemanticContextAlias {
    /// Creates one one-sided context template.
    #[must_use]
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        origin: NodeOrigin,
        id: StableItemId,
        name_origin: NodeOrigin,
        name: String,
        here_origin: NodeOrigin,
        here: SemanticId,
        variables: Vec<SemanticVariable>,
        body: FixedConfigurationPattern<SemanticId, SemanticTerm>,
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
    /// Returns exact alias-name provenance.
    #[must_use]
    pub const fn name_origin(&self) -> &NodeOrigin {
        &self.name_origin
    }
    /// Returns target-neutral alias name.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }
    /// Returns exact HERE occurrence provenance.
    #[must_use]
    pub const fn here_origin(&self) -> &NodeOrigin {
        &self.here_origin
    }
    /// Returns selected HERE binding.
    #[must_use]
    pub const fn here(&self) -> &SemanticId {
        &self.here
    }
    /// Returns typed/frame variables.
    #[must_use]
    pub fn variables(&self) -> &[SemanticVariable] {
        &self.variables
    }
    /// Returns the one-sided configuration pattern.
    #[must_use]
    pub const fn body(&self) -> &FixedConfigurationPattern<SemanticId, SemanticTerm> {
        &self.body
    }
}

/// Structured relational body of one ordinary labeled semantic rule.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(untagged)]
pub enum SemanticRuleBody {
    /// One ordinary term rewrite.
    Term(Box<SemanticTerm>),
    /// One simultaneous fixed-configuration rewrite.
    Configuration(FixedConfigurationRewrite<SemanticId, SemanticTerm>),
}

impl SemanticRule {
    /// Creates a rule with an explicitly structured rewrite body.
    ///
    /// # Errors
    ///
    /// Returns [`SemanticValidationError`] when the body is not a rewrite.
    pub fn new(
        origin: NodeOrigin,
        id: StableItemId,
        kind: SentenceKind,
        variables: Vec<SemanticVariable>,
        body: SemanticTerm,
    ) -> Result<Self, SemanticValidationError> {
        if !matches!(body.kind, SemanticTermKind::Rewrite { .. }) {
            return Err(SemanticValidationError::RuleBodyNotRewrite(Box::new(id)));
        }
        Ok(Self {
            origin,
            id,
            kind,
            label: None,
            requires: None,
            priority: None,
            simplification: None,
            claim: None,
            variables,
            body: SemanticRuleBody::Term(Box::new(body)),
        })
    }

    /// Creates one labeled simultaneous fixed-configuration rewrite.
    ///
    /// # Errors
    ///
    /// Returns [`SemanticValidationError`] when the stable item kind does not
    /// agree with the sentence kind.
    pub fn new_configuration(
        origin: NodeOrigin,
        id: StableItemId,
        kind: SentenceKind,
        variables: Vec<SemanticVariable>,
        body: FixedConfigurationRewrite<SemanticId, SemanticTerm>,
    ) -> Result<Self, SemanticValidationError> {
        if kind == SentenceKind::Alias {
            return Err(SemanticValidationError::InvalidAliasRoot(Box::new(id)));
        }
        if kind == SentenceKind::Simplification {
            return Err(SemanticValidationError::InvalidSimplificationRoot(
                Box::new(id),
            ));
        }
        let expected = match kind {
            SentenceKind::Transition => ItemKind::Rule,
            SentenceKind::Equation => ItemKind::Equation,
            SentenceKind::Simplification => ItemKind::Simplification,
            SentenceKind::Alias => unreachable!("configuration aliases were rejected above"),
            SentenceKind::Claim => ItemKind::Claim,
        };
        if id.item_kind() != expected {
            return Err(SemanticValidationError::WrongItemKind {
                id: Box::new(id.clone()),
                expected,
                actual: id.item_kind(),
            });
        }
        Ok(Self {
            origin,
            id,
            kind,
            label: None,
            requires: None,
            priority: None,
            simplification: None,
            claim: None,
            variables,
            body: SemanticRuleBody::Configuration(body),
        })
    }
    /// Returns the authored sentence ID.
    #[must_use]
    pub const fn id(&self) -> &StableItemId {
        &self.id
    }
    /// Returns the origin.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
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
    /// Returns [`SemanticValidationError::InvalidRulePriority`] when priority
    /// metadata is attached to anything other than an equation.
    pub fn with_priority(
        mut self,
        priority: Option<SemanticRulePriority>,
    ) -> Result<Self, SemanticValidationError> {
        if priority.is_some() && self.kind != SentenceKind::Equation {
            return Err(SemanticValidationError::InvalidRulePriority(Box::new(
                self.id.clone(),
            )));
        }
        self.priority = priority;
        Ok(self)
    }
    /// Returns the explicit priority.
    #[must_use]
    pub const fn priority(&self) -> Option<&SemanticRulePriority> {
        self.priority.as_ref()
    }
    /// Attaches typed simplification metadata.
    #[must_use]
    pub fn with_simplification(mut self, value: Option<SemanticSimplification>) -> Self {
        self.simplification = value;
        self
    }
    /// Returns simplification metadata.
    #[must_use]
    pub const fn simplification(&self) -> Option<&SemanticSimplification> {
        self.simplification.as_ref()
    }
    /// Attaches typed claim-only metadata.
    #[must_use]
    pub fn with_claim(mut self, claim: Option<SemanticClaim>) -> Self {
        self.claim = claim;
        self
    }
    /// Returns typed claim-only metadata.
    #[must_use]
    pub const fn claim(&self) -> Option<&SemanticClaim> {
        self.claim.as_ref()
    }
    /// Attaches one already-validated explicit emitted K label.
    #[must_use]
    pub fn with_label(mut self, label: Option<SemanticRuleLabel>) -> Self {
        self.label = label;
        self
    }
    /// Returns the explicit emitted K label, when authored.
    #[must_use]
    pub const fn label(&self) -> Option<&SemanticRuleLabel> {
        self.label.as_ref()
    }
    /// Attaches an object-language Boolean applicability condition.
    ///
    /// # Errors
    ///
    /// Returns [`SemanticValidationError::RuleConditionSortMismatch`] unless
    /// the condition has exactly the builtin `Bool` sort.
    pub fn with_requires(
        mut self,
        requires: Option<SemanticRuleCondition>,
    ) -> Result<Self, SemanticValidationError> {
        if requires.as_ref().is_some_and(|condition| {
            condition.term().sort() != &SemanticSortRef::Builtin(BuiltinSort::Bool)
        }) {
            return Err(SemanticValidationError::RuleConditionSortMismatch);
        }
        self.requires = requires;
        Ok(self)
    }
    /// Returns the object-language Boolean applicability condition.
    #[must_use]
    pub const fn requires(&self) -> Option<&SemanticRuleCondition> {
        self.requires.as_ref()
    }
    /// Returns variables in binder order.
    #[must_use]
    pub fn variables(&self) -> &[SemanticVariable] {
        &self.variables
    }
    /// Returns the ordinary term rewrite, when present.
    #[must_use]
    pub fn body(&self) -> Option<&SemanticTerm> {
        match &self.body {
            SemanticRuleBody::Term(body) => Some(body),
            SemanticRuleBody::Configuration(_) => None,
        }
    }

    /// Returns the typed relational body.
    #[must_use]
    pub const fn relational_body(&self) -> &SemanticRuleBody {
        &self.body
    }
}

/// A typed semantic term. Every nested node has its own origin/key.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub struct SemanticTerm {
    origin: NodeOrigin,
    sort: SemanticSortRef,
    #[serde(flatten)]
    kind: SemanticTermKind,
}

impl SemanticTerm {
    /// Creates a variable reference.
    #[must_use]
    pub const fn variable(origin: NodeOrigin, sort: SemanticSortRef, variable: SemanticId) -> Self {
        Self {
            origin,
            sort,
            kind: SemanticTermKind::Variable { variable },
        }
    }
    /// Creates a constructor application. Argument order is semantic.
    #[must_use]
    pub const fn application(
        origin: NodeOrigin,
        sort: SemanticSortRef,
        application: SemanticApplicationRef,
        arguments: Vec<Self>,
    ) -> Self {
        Self {
            origin,
            sort,
            kind: SemanticTermKind::Application {
                application,
                arguments,
            },
        }
    }
    /// Creates a domain token.
    ///
    /// # Errors
    ///
    /// Returns [`SemanticValidationError`] for an empty token payload.
    pub fn token(
        origin: NodeOrigin,
        sort: SemanticSortRef,
        value: impl Into<String>,
    ) -> Result<Self, SemanticValidationError> {
        let value = value.into();
        if value.is_empty() {
            return Err(SemanticValidationError::EmptyText("token value"));
        }
        Ok(Self {
            origin,
            sort,
            kind: SemanticTermKind::Token { value },
        })
    }
    /// Creates a rewrite. Whole-theory validation requires both endpoint sorts
    /// to inject into the declared rewrite sort.
    ///
    /// # Errors
    ///
    /// Returns no local shape error; subsorting is a whole-theory property.
    pub fn rewrite(
        origin: NodeOrigin,
        sort: SemanticSortRef,
        from: Self,
        to: Self,
    ) -> Result<Self, SemanticValidationError> {
        Ok(Self {
            origin,
            sort,
            kind: SemanticTermKind::Rewrite {
                from: Box::new(from),
                to: Box::new(to),
            },
        })
    }
    /// Creates an explicit source-level K computation sequence. The frontend
    /// remains responsible for inserting each item's injection into `KItem`.
    #[must_use]
    pub const fn k_sequence(
        origin: NodeOrigin,
        item_sort: SemanticSortRef,
        items: Vec<Self>,
    ) -> Self {
        Self {
            origin,
            sort: SemanticSortRef::Builtin(BuiltinSort::KSequence),
            kind: SemanticTermKind::KSequence { item_sort, items },
        }
    }
    /// Creates one typed Map-theory operation.
    #[must_use]
    pub const fn map(origin: NodeOrigin, operation: MapOperation, arguments: Vec<Self>) -> Self {
        Self {
            origin,
            sort: SemanticSortRef::Builtin(BuiltinSort::Map),
            kind: SemanticTermKind::Map {
                operation,
                arguments,
            },
        }
    }
    /// Returns node provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns the resolved sort.
    #[must_use]
    pub const fn sort(&self) -> &SemanticSortRef {
        &self.sort
    }
    /// Returns the term form.
    #[must_use]
    pub const fn kind(&self) -> &SemanticTermKind {
        &self.kind
    }
}

/// Structured target-neutral semantic term forms.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(tag = "term_kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum SemanticTermKind {
    /// Reference to a declared rule/initializer variable.
    Variable {
        /// Stable binder identity.
        variable: SemanticId,
    },
    /// Resolved constructor application.
    Application {
        /// Resolved authored or compiler-provided production identity.
        application: SemanticApplicationRef,
        /// Arguments in production order.
        arguments: Vec<SemanticTerm>,
    },
    /// Domain token with its sort on the enclosing term.
    Token {
        /// Exact token payload.
        value: String,
    },
    /// Explicit ordered K computation sequence.
    KSequence {
        /// Declared sort into which sequence items must inject (`KItem`).
        item_sort: SemanticSortRef,
        /// Items in computation order.
        items: Vec<SemanticTerm>,
    },
    /// Structured Map unit/item/update operation with KItem-like operands.
    Map {
        /// Exact compiler-known Map operation.
        operation: MapOperation,
        /// Ordered structured operands.
        arguments: Vec<SemanticTerm>,
    },
    /// Relational pre/post rewrite.
    Rewrite {
        /// Pre-pattern.
        from: Box<SemanticTerm>,
        /// Post-term.
        to: Box<SemanticTerm>,
    },
}

/// Typed failure while constructing or validating semantic IR.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SemanticValidationError {
    /// No module was supplied.
    EmptyTheory,
    /// A textual field was blank.
    EmptyText(&'static str),
    /// A set-like identity was repeated.
    DuplicateId {
        /// Identity namespace.
        kind: &'static str,
        /// Debug-stable identity text.
        id: String,
    },
    /// A source-map key was used by two nodes.
    DuplicateSourceMapKey(SourceMapKey),
    /// An import names no module.
    DanglingModule(ModuleId),
    /// An item reference names no declaration.
    DanglingItem(Box<StableItemId>),
    /// An item is used in a namespace other than its declaration kind.
    WrongItemKind {
        /// Referenced item.
        id: Box<StableItemId>,
        /// Required namespace.
        expected: ItemKind,
        /// Actual namespace.
        actual: ItemKind,
    },
    /// A grammar production contained no items.
    EmptyProduction(Box<StableItemId>),
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
    /// A bracket production did not have exactly one nonterminal.
    InvalidBracketProduction,
    /// Total metadata occurred without function metadata.
    InvalidFunctionProduction,
    /// Alias and function metadata occurred on the same production.
    InvalidAliasProduction,
    /// A precedence or associativity sentence referenced no production group.
    DanglingProductionGroup(ProductionGroupId),
    /// The strict production-group precedence relation contained a cycle.
    PrecedenceCycle(ProductionGroupId),
    /// The strict subsort relation contained a cycle.
    SubsortCycle(Box<SemanticSortRef>),
    /// M2 requires exactly one selected configuration.
    ConfigurationCount(usize),
    /// A variable was declared more than once.
    DuplicateVariable(SemanticId),
    /// A term references no in-scope variable.
    DanglingVariable(SemanticId),
    /// A variable reference carries the wrong resolved sort.
    VariableSortMismatch(SemanticId),
    /// Declared variables and variables used by a sentence differ.
    VariableClosure,
    /// An application references something other than a production.
    DanglingProduction(Box<StableItemId>),
    /// An application's result/argument signature differs from its production.
    ApplicationSignature(Box<StableItemId>),
    /// A compiler-provided operation application has the wrong signature.
    BuiltinApplicationSignature(BuiltinOperation),
    /// A rewrite's endpoints do not share its sort.
    RewriteSortMismatch,
    /// A K sequence node did not carry the builtin computation sort.
    SequenceSortMismatch,
    /// A K sequence item is not a subsort of the declared item sort.
    SequenceItemSortMismatch,
    /// Rule construction was given a non-rewrite term.
    RuleBodyNotRewrite(Box<StableItemId>),
    /// An equation left-hand side is not headed by an authored function.
    InvalidEquationRoot(Box<StableItemId>),
    /// An alias left-hand side is not headed by an authored alias production.
    InvalidAliasRoot(Box<StableItemId>),
    /// A simplification left-hand side is not headed by a function or builtin function.
    InvalidSimplificationRoot(Box<StableItemId>),
    /// Simplification metadata disagrees with the sentence kind.
    InvalidSimplificationMetadata(Box<StableItemId>),
    /// Equation priority metadata occurred on another sentence kind.
    InvalidRulePriority(Box<StableItemId>),
    /// Claim metadata presence disagrees with the sentence kind.
    InvalidClaimMetadata(Box<StableItemId>),
    /// A claim omitted its mandatory explicit authored label.
    ClaimLabelRequired(Box<StableItemId>),
    /// A claim used an ordinary term rewrite instead of a configuration rewrite.
    ClaimBodyNotConfiguration(Box<StableItemId>),
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
    /// An explicit emitted K rule label was invalid.
    InvalidRuleLabel(String),
    /// The initializer result does not match the cell content sort.
    InitializerSortMismatch,
    /// A structured fixed initializer did not mirror its declaration tree.
    InitializerTreeMismatch,
    /// A structured initializer leaf term has the wrong sort.
    InitializerLeafSortMismatch,
    /// A Map term did not carry builtin Map sort.
    MapSortMismatch,
    /// A Map operation had the wrong arity or Map operand.
    MapOperationSignature(MapOperation),
    /// A configuration rule exists without a general fixed configuration.
    ConfigurationRuleWithoutFixedConfiguration(Box<StableItemId>),
    /// A configuration rule names a different fixed configuration.
    ConfigurationRuleTargetMismatch(Box<StableItemId>),
    /// A cell rule references a missing/non-leaf cell or incomplete frame.
    InvalidCellFraming,
    /// A cell-content frame is incompatible with its leaf sort.
    CellFrameSortMismatch,
    /// A named sequence/map frame binding is absent or has the wrong sort.
    CellFrameBindingMismatch(SemanticId),
}

impl fmt::Display for SemanticValidationError {
    #[allow(clippy::too_many_lines)]
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyTheory => formatter.write_str("semantic theory must contain a module"),
            Self::EmptyText(field) => write!(formatter, "{field} must not be empty"),
            Self::DuplicateId { kind, id } => write!(formatter, "duplicate {kind} ID {id:?}"),
            Self::DuplicateSourceMapKey(key) => {
                write!(formatter, "duplicate source-map key {:?}", key.as_str())
            }
            Self::DanglingModule(id) => {
                write!(formatter, "dangling module reference {:?}", id.as_str())
            }
            Self::DanglingItem(id) => write!(formatter, "dangling item reference {id:?}"),
            Self::WrongItemKind {
                id,
                expected,
                actual,
            } => write!(
                formatter,
                "item {id:?} has kind {actual:?}, expected {expected:?}"
            ),
            Self::EmptyProduction(id) => write!(formatter, "production {id:?} has no items"),
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
            Self::ConfigurationCount(count) => write!(
                formatter,
                "semantic theory requires exactly one configuration, found {count}"
            ),
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
            Self::DanglingProduction(id) => {
                write!(formatter, "dangling production reference {id:?}")
            }
            Self::ApplicationSignature(id) => write!(
                formatter,
                "application does not match production signature {id:?}"
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
            Self::RuleBodyNotRewrite(id) => write!(formatter, "rule {id:?} body must be a rewrite"),
            Self::InvalidEquationRoot(id) => write!(
                formatter,
                "equation {id:?} must be headed by a functional production"
            ),
            Self::InvalidAliasRoot(id) => write!(
                formatter,
                "alias clause {id:?} must be headed by an alias production"
            ),
            Self::InvalidSimplificationRoot(id) => write!(
                formatter,
                "simplification `{}` must be rooted at a function or builtin function",
                id.item_name()
            ),
            Self::InvalidSimplificationMetadata(id) => write!(
                formatter,
                "simplification metadata disagrees with sentence `{}`",
                id.item_name()
            ),
            Self::InvalidRulePriority(id) => write!(
                formatter,
                "equation priority cannot occur on {:?} sentence `{}`",
                id.item_kind(),
                id.item_name()
            ),
            Self::InvalidClaimMetadata(id) => write!(
                formatter,
                "claim metadata disagrees with sentence `{}`",
                id.item_name()
            ),
            Self::ClaimLabelRequired(id) => write!(
                formatter,
                "claim `{}` requires an explicit authored label",
                id.item_name()
            ),
            Self::ClaimBodyNotConfiguration(id) => write!(
                formatter,
                "claim `{}` requires a configuration rewrite body",
                id.item_name()
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
            Self::InvalidRuleLabel(label) => {
                write!(formatter, "invalid explicit K rule label {label:?}")
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
            Self::ConfigurationRuleWithoutFixedConfiguration(id) => write!(
                formatter,
                "configuration rule {id:?} requires a general fixed configuration"
            ),
            Self::ConfigurationRuleTargetMismatch(id) => write!(
                formatter,
                "configuration rule {id:?} names a different fixed configuration"
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

impl Error for SemanticValidationError {}

fn validate_item_kind(
    id: &StableItemId,
    expected: ItemKind,
) -> Result<(), SemanticValidationError> {
    if id.item_kind() == expected {
        Ok(())
    } else {
        Err(SemanticValidationError::WrongItemKind {
            id: Box::new(id.clone()),
            expected,
            actual: id.item_kind(),
        })
    }
}

fn insert_unique<T: Ord>(
    set: &mut BTreeSet<T>,
    value: T,
    kind: &'static str,
    display: &str,
) -> Result<(), SemanticValidationError> {
    if set.insert(value) {
        Ok(())
    } else {
        Err(SemanticValidationError::DuplicateId {
            kind,
            id: display.into(),
        })
    }
}

fn insert_node(
    set: &mut BTreeSet<SourceMapKey>,
    key: &SourceMapKey,
) -> Result<(), SemanticValidationError> {
    if set.insert(key.clone()) {
        Ok(())
    } else {
        Err(SemanticValidationError::DuplicateSourceMapKey(key.clone()))
    }
}

fn insert_declaration(
    map: &mut BTreeMap<StableItemId, ItemKind>,
    id: &StableItemId,
) -> Result<(), SemanticValidationError> {
    if map.insert(id.clone(), id.item_kind()).is_some() {
        return Err(SemanticValidationError::DuplicateId {
            kind: "declaration",
            id: format!("{id:?}"),
        });
    }
    Ok(())
}

fn insert_semantic_id(
    set: &mut BTreeSet<SemanticId>,
    id: &SemanticId,
    kind: &'static str,
) -> Result<(), SemanticValidationError> {
    if set.insert(id.clone()) {
        Ok(())
    } else {
        Err(SemanticValidationError::DuplicateId {
            kind,
            id: id.as_str().into(),
        })
    }
}

fn require_kind(
    map: &BTreeMap<StableItemId, ItemKind>,
    id: &StableItemId,
    expected: ItemKind,
) -> Result<(), SemanticValidationError> {
    match map.get(id) {
        None => Err(SemanticValidationError::DanglingItem(Box::new(id.clone()))),
        Some(actual) if *actual == expected => Ok(()),
        Some(actual) => Err(SemanticValidationError::WrongItemKind {
            id: Box::new(id.clone()),
            expected,
            actual: *actual,
        }),
    }
}

fn require_semantic_sort(
    declarations: &BTreeMap<StableItemId, ItemKind>,
    sort: &SemanticSortRef,
) -> Result<(), SemanticValidationError> {
    match sort {
        SemanticSortRef::Declared(id) => require_kind(declarations, id, ItemKind::Sort),
        SemanticSortRef::Builtin(
            BuiltinSort::KSequence
            | BuiltinSort::Int
            | BuiltinSort::Bool
            | BuiltinSort::Map
            | BuiltinSort::Id
            | BuiltinSort::Bytes,
        ) => Ok(()),
    }
}

fn variable_scope(
    variables: &[SemanticVariable],
    declarations: &BTreeMap<StableItemId, ItemKind>,
) -> Result<BTreeMap<SemanticId, SemanticSortRef>, SemanticValidationError> {
    let mut scope = BTreeMap::new();
    for variable in variables {
        require_semantic_sort(declarations, &variable.sort)?;
        if scope
            .insert(variable.id.clone(), variable.sort.clone())
            .is_some()
        {
            return Err(SemanticValidationError::DuplicateVariable(
                variable.id.clone(),
            ));
        }
    }
    Ok(scope)
}

fn collect_fixed_configuration_nodes(
    configuration: &FixedConfiguration<SemanticSortRef, SemanticId, SemanticTerm>,
    semantic_ids: &mut BTreeSet<SemanticId>,
    nodes: &mut BTreeSet<SourceMapKey>,
) -> Result<(), SemanticValidationError> {
    fn cells(
        values: &[FixedCell<SemanticSortRef, SemanticId>],
        semantic_ids: &mut BTreeSet<SemanticId>,
        nodes: &mut BTreeSet<SourceMapKey>,
    ) -> Result<(), SemanticValidationError> {
        for cell in values {
            insert_semantic_id(semantic_ids, cell.id(), "cell")?;
            insert_node(nodes, cell.origin().key())?;
            for attribute in cell.attributes() {
                insert_node(nodes, attribute.origin().key())?;
            }
            if let FixedCellContent::Children { children } = cell.content() {
                cells(children, semantic_ids, nodes)?;
            }
        }
        Ok(())
    }
    fn initializer(
        values: &[FixedInitializerCell<SemanticId, SemanticTerm>],
        nodes: &mut BTreeSet<SourceMapKey>,
    ) -> Result<(), SemanticValidationError> {
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
    cells(configuration.cells(), semantic_ids, nodes)?;
    initializer(configuration.initializer(), nodes)
}

fn validate_fixed_configuration(
    configuration: &FixedConfiguration<SemanticSortRef, SemanticId, SemanticTerm>,
    declarations: &BTreeMap<StableItemId, ItemKind>,
    signatures: &BTreeMap<StableItemId, (SemanticSortRef, Vec<SemanticSortRef>)>,
    sort_parents: &BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
    nodes: &mut BTreeSet<SourceMapKey>,
) -> Result<(), SemanticValidationError> {
    let mut scope = BTreeMap::new();
    let mut external_names = BTreeSet::new();
    let mut main_count = 0_usize;
    for variable in configuration.variables() {
        require_semantic_sort(declarations, variable.sort())?;
        if scope
            .insert(variable.id().clone(), variable.sort().clone())
            .is_some()
        {
            return Err(SemanticValidationError::DuplicateVariable(
                variable.id().clone(),
            ));
        }
        if !external_names.insert(variable.external_name()) {
            return Err(SemanticValidationError::EmptyText(
                "duplicate external configuration variable",
            ));
        }
        main_count += usize::from(variable.is_main());
    }
    if main_count > 1 {
        return Err(SemanticValidationError::EmptyText(
            "multiple main configuration variables",
        ));
    }
    validate_initializer_forest(
        configuration.cells(),
        configuration.initializer(),
        &scope,
        declarations,
        signatures,
        sort_parents,
        nodes,
    )?;
    let mut used = BTreeSet::new();
    collect_initializer_variables(configuration.initializer(), &mut used);
    if used != scope.keys().cloned().collect() {
        return Err(SemanticValidationError::VariableClosure);
    }
    Ok(())
}

fn collect_initializer_variables(
    initializer: &[FixedInitializerCell<SemanticId, SemanticTerm>],
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
    cells: &[FixedCell<SemanticSortRef, SemanticId>],
    initializer: &[FixedInitializerCell<SemanticId, SemanticTerm>],
    scope: &BTreeMap<SemanticId, SemanticSortRef>,
    declarations: &BTreeMap<StableItemId, ItemKind>,
    signatures: &BTreeMap<StableItemId, (SemanticSortRef, Vec<SemanticSortRef>)>,
    sort_parents: &BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
    nodes: &mut BTreeSet<SourceMapKey>,
) -> Result<(), SemanticValidationError> {
    if cells.len() != initializer.len() {
        return Err(SemanticValidationError::InitializerTreeMismatch);
    }
    for (cell, initialized) in cells.iter().zip(initializer) {
        if cell.id() != initialized.cell() {
            return Err(SemanticValidationError::InitializerTreeMismatch);
        }
        match (cell.content(), initialized.content()) {
            (FixedCellContent::Term { sort }, FixedInitializerContent::Term { term }) => {
                require_semantic_sort(declarations, sort)?;
                validate_term(term, scope, declarations, signatures, sort_parents, nodes)?;
                if term.sort() != sort {
                    return Err(SemanticValidationError::InitializerLeafSortMismatch);
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
                declarations,
                signatures,
                sort_parents,
                nodes,
            )?,
            _ => return Err(SemanticValidationError::InitializerTreeMismatch),
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn validate_configuration_rewrite(
    rewrite: &FixedConfigurationRewrite<SemanticId, SemanticTerm>,
    configuration: &FixedConfiguration<SemanticSortRef, SemanticId, SemanticTerm>,
    scope: &BTreeMap<SemanticId, SemanticSortRef>,
    declarations: &BTreeMap<StableItemId, ItemKind>,
    signatures: &BTreeMap<StableItemId, (SemanticSortRef, Vec<SemanticSortRef>)>,
    sort_parents: &BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
    nodes: &mut BTreeSet<SourceMapKey>,
) -> Result<(), SemanticValidationError> {
    fn leaves(
        cells: &[FixedCell<SemanticSortRef, SemanticId>],
        output: &mut BTreeMap<SemanticId, SemanticSortRef>,
    ) -> Result<(), SemanticValidationError> {
        for cell in cells {
            match cell.content() {
                FixedCellContent::Term { sort } => {
                    if output.insert(cell.id().clone(), sort.clone()).is_some() {
                        return Err(SemanticValidationError::InvalidCellFraming);
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
        return Err(SemanticValidationError::InvalidCellFraming);
    }
    insert_node(nodes, rewrite.origin().key())?;
    for clause in rewrite.clauses() {
        let sort = leaf_sorts
            .get(clause.cell())
            .ok_or(SemanticValidationError::InvalidCellFraming)?;
        insert_node(nodes, clause.origin().key())?;
        validate_term(
            clause.before(),
            scope,
            declarations,
            signatures,
            sort_parents,
            nodes,
        )?;
        if clause.before().sort() != sort {
            return Err(SemanticValidationError::CellFrameSortMismatch);
        }
        if let CellPost::Replace { term } = clause.after() {
            validate_term(term, scope, declarations, signatures, sort_parents, nodes)?;
            if term.sort() != sort {
                return Err(SemanticValidationError::CellFrameSortMismatch);
            }
        }
        validate_cell_frame(clause, sort, scope, nodes)?;
    }
    Ok(())
}

fn validate_cell_frame(
    clause: &FixedCellClause<SemanticId, SemanticTerm>,
    sort: &SemanticSortRef,
    scope: &BTreeMap<SemanticId, SemanticSortRef>,
    nodes: &mut BTreeSet<SourceMapKey>,
) -> Result<(), SemanticValidationError> {
    let (origin, binding, required_sort) = match clause.frame() {
        CellContentFrame::Exact => return Ok(()),
        CellContentFrame::KSequenceTail { origin, binding } => (
            origin,
            binding,
            SemanticSortRef::Builtin(BuiltinSort::KSequence),
        ),
        CellContentFrame::MapRemainder { origin, binding } => {
            (origin, binding, SemanticSortRef::Builtin(BuiltinSort::Map))
        }
    };
    insert_node(nodes, origin.key())?;
    if sort != &required_sort {
        return Err(SemanticValidationError::CellFrameSortMismatch);
    }
    if let Some(binding) = binding
        && scope.get(binding) != Some(&required_sort)
    {
        return Err(SemanticValidationError::CellFrameBindingMismatch(
            binding.clone(),
        ));
    }
    Ok(())
}

fn validate_initializer(
    initializer: &SemanticInitializer,
    expected_sort: &SemanticSortRef,
    declarations: &BTreeMap<StableItemId, ItemKind>,
    signatures: &BTreeMap<StableItemId, (SemanticSortRef, Vec<SemanticSortRef>)>,
    sort_parents: &BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
    nodes: &mut BTreeSet<SourceMapKey>,
) -> Result<(), SemanticValidationError> {
    let scope = variable_scope(&initializer.variables, declarations)?;
    validate_term(
        &initializer.body,
        &scope,
        declarations,
        signatures,
        sort_parents,
        nodes,
    )?;
    if &initializer.body.sort != expected_sort {
        return Err(SemanticValidationError::InitializerSortMismatch);
    }
    Ok(())
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn validate_rule(
    rule: &SemanticRule,
    configuration: Option<&FixedConfiguration<SemanticSortRef, SemanticId, SemanticTerm>>,
    declarations: &BTreeMap<StableItemId, ItemKind>,
    signatures: &BTreeMap<StableItemId, (SemanticSortRef, Vec<SemanticSortRef>)>,
    functional_productions: &BTreeSet<StableItemId>,
    alias_productions: &BTreeSet<StableItemId>,
    sort_parents: &BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
    nodes: &mut BTreeSet<SourceMapKey>,
) -> Result<(), SemanticValidationError> {
    let claim = match (rule.kind, rule.claim.as_ref()) {
        (SentenceKind::Claim, Some(claim)) => Some(claim),
        (SentenceKind::Claim, None) | (_, Some(_)) => {
            return Err(SemanticValidationError::InvalidClaimMetadata(Box::new(
                rule.id.clone(),
            )));
        }
        (_, None) => None,
    };
    if rule.kind == SentenceKind::Claim {
        if rule.priority.is_some() || rule.simplification.is_some() {
            return Err(SemanticValidationError::InvalidClaimMetadata(Box::new(
                rule.id.clone(),
            )));
        }
        if rule.label.is_none() {
            return Err(SemanticValidationError::ClaimLabelRequired(Box::new(
                rule.id.clone(),
            )));
        }
        if !matches!(&rule.body, SemanticRuleBody::Configuration(_)) {
            return Err(SemanticValidationError::ClaimBodyNotConfiguration(
                Box::new(rule.id.clone()),
            ));
        }
    }
    if let Some(label) = &rule.label {
        insert_node(nodes, label.origin().key())?;
    }
    let scope = variable_scope(&rule.variables, declarations)?;
    match &rule.body {
        SemanticRuleBody::Term(body) => {
            validate_term(body, &scope, declarations, signatures, sort_parents, nodes)?;
            if !matches!(body.kind, SemanticTermKind::Rewrite { .. }) {
                return Err(SemanticValidationError::RuleBodyNotRewrite(Box::new(
                    rule.id.clone(),
                )));
            }
            if rule.kind == SentenceKind::Equation {
                let SemanticTermKind::Rewrite { from, .. } = body.kind() else {
                    unreachable!("rule bodies were checked as rewrites")
                };
                let SemanticTermKind::Application {
                    application: ApplicationRef::Declared(production),
                    ..
                } = from.kind()
                else {
                    return Err(SemanticValidationError::InvalidEquationRoot(Box::new(
                        rule.id.clone(),
                    )));
                };
                if !functional_productions.contains(production) {
                    return Err(SemanticValidationError::InvalidEquationRoot(Box::new(
                        rule.id.clone(),
                    )));
                }
            }
            if rule.kind == SentenceKind::Alias {
                let SemanticTermKind::Rewrite { from, .. } = body.kind() else {
                    unreachable!("rule bodies were checked as rewrites")
                };
                let SemanticTermKind::Application {
                    application: ApplicationRef::Declared(production),
                    ..
                } = from.kind()
                else {
                    return Err(SemanticValidationError::InvalidAliasRoot(Box::new(
                        rule.id.clone(),
                    )));
                };
                if !alias_productions.contains(production) {
                    return Err(SemanticValidationError::InvalidAliasRoot(Box::new(
                        rule.id.clone(),
                    )));
                }
            }
            if rule.kind == SentenceKind::Simplification {
                let SemanticTermKind::Rewrite { from, .. } = body.kind() else {
                    unreachable!("rule bodies were checked as rewrites")
                };
                match from.kind() {
                    SemanticTermKind::Application {
                        application: ApplicationRef::Declared(production),
                        ..
                    } if functional_productions.contains(production) => {}
                    SemanticTermKind::Application {
                        application: ApplicationRef::Builtin(operation),
                        ..
                    } if operation.is_functional() => {}
                    _ => {
                        return Err(SemanticValidationError::InvalidSimplificationRoot(
                            Box::new(rule.id.clone()),
                        ));
                    }
                }
            }
        }
        SemanticRuleBody::Configuration(body) => {
            if rule.kind == SentenceKind::Alias {
                return Err(SemanticValidationError::InvalidAliasRoot(Box::new(
                    rule.id.clone(),
                )));
            }
            if rule.kind == SentenceKind::Simplification {
                return Err(SemanticValidationError::InvalidSimplificationRoot(
                    Box::new(rule.id.clone()),
                ));
            }
            let configuration = configuration.ok_or_else(|| {
                SemanticValidationError::ConfigurationRuleWithoutFixedConfiguration(Box::new(
                    rule.id.clone(),
                ))
            })?;
            if body.configuration() != configuration.id() {
                return Err(SemanticValidationError::ConfigurationRuleTargetMismatch(
                    Box::new(rule.id.clone()),
                ));
            }
            validate_configuration_rewrite(
                body,
                configuration,
                &scope,
                declarations,
                signatures,
                sort_parents,
                nodes,
            )?;
        }
    }
    if rule.kind == SentenceKind::Simplification {
        let Some(simplification) = &rule.simplification else {
            return Err(SemanticValidationError::InvalidSimplificationMetadata(
                Box::new(rule.id.clone()),
            ));
        };
        insert_node(nodes, simplification.origin().key())?;
        if let Some(priority) = simplification.priority() {
            insert_node(nodes, priority.origin().key())?;
        }
    } else if rule.simplification.is_some() {
        return Err(SemanticValidationError::InvalidSimplificationMetadata(
            Box::new(rule.id.clone()),
        ));
    }
    if let Some(priority) = &rule.priority {
        if rule.kind != SentenceKind::Equation {
            return Err(SemanticValidationError::InvalidRulePriority(Box::new(
                rule.id.clone(),
            )));
        }
        insert_node(nodes, priority.origin().key())?;
    }
    if let Some(condition) = &rule.requires {
        if rule.kind == SentenceKind::Alias {
            return Err(SemanticValidationError::AliasCondition);
        }
        insert_node(nodes, condition.origin().key())?;
        validate_term(
            condition.term(),
            &scope,
            declarations,
            signatures,
            sort_parents,
            nodes,
        )?;
        if condition.term().sort() != &SemanticSortRef::Builtin(BuiltinSort::Bool) {
            return Err(SemanticValidationError::RuleConditionSortMismatch);
        }
    }
    if let Some(claim) = claim {
        validate_claim(
            rule,
            claim,
            &scope,
            declarations,
            signatures,
            sort_parents,
            nodes,
        )?;
    }
    let mut used = BTreeSet::new();
    match &rule.body {
        SemanticRuleBody::Term(body) => collect_term_variables(body, &mut used),
        SemanticRuleBody::Configuration(body) => {
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
    if let Some(condition) = &rule.requires {
        collect_term_variables(condition.term(), &mut used);
    }
    if let Some(ensures) = claim.and_then(SemanticClaim::ensures) {
        collect_term_variables(ensures.term(), &mut used);
    }
    if used != scope.keys().cloned().collect() {
        return Err(SemanticValidationError::VariableClosure);
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn validate_claim(
    rule: &SemanticRule,
    claim: &SemanticClaim,
    scope: &BTreeMap<SemanticId, SemanticSortRef>,
    declarations: &BTreeMap<StableItemId, ItemKind>,
    signatures: &BTreeMap<StableItemId, (SemanticSortRef, Vec<SemanticSortRef>)>,
    sort_parents: &BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
    nodes: &mut BTreeSet<SourceMapKey>,
) -> Result<(), SemanticValidationError> {
    insert_node(nodes, claim.modality_origin().key())?;
    if let Some(origin) = claim.circularity_origin() {
        insert_node(nodes, origin.key())?;
    }

    let mut binder_ids = BTreeSet::new();
    for binder in claim.universals().iter().chain(claim.existentials()) {
        if !binder_ids.insert(binder.id().clone()) || scope.get(binder.id()) != Some(binder.sort())
        {
            return Err(SemanticValidationError::InvalidClaimBinder(
                binder.id().clone(),
            ));
        }
        require_semantic_sort(declarations, binder.sort())?;
        insert_node(nodes, binder.origin().key())?;
        insert_node(nodes, binder.name_origin().key())?;
        insert_node(nodes, binder.sort_origin().key())?;
    }

    let mut left_uses = BTreeSet::new();
    let mut right_uses = BTreeSet::new();
    let SemanticRuleBody::Configuration(body) = &rule.body else {
        return Err(SemanticValidationError::ClaimBodyNotConfiguration(
            Box::new(rule.id.clone()),
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
    if let Some(requires) = rule.requires() {
        collect_term_variables(requires.term(), &mut left_uses);
    }
    if let Some(ensures) = claim.ensures() {
        insert_node(nodes, ensures.origin().key())?;
        validate_term(
            ensures.term(),
            scope,
            declarations,
            signatures,
            sort_parents,
            nodes,
        )?;
        if ensures.term().sort() != &SemanticSortRef::Builtin(BuiltinSort::Bool) {
            return Err(SemanticValidationError::RuleConditionSortMismatch);
        }
        collect_term_variables(ensures.term(), &mut right_uses);
    }
    for binder in claim.existentials() {
        if left_uses.contains(binder.id()) {
            return Err(SemanticValidationError::ExistentialScopeViolation(
                binder.id().clone(),
            ));
        }
        if !right_uses.contains(binder.id()) {
            return Err(SemanticValidationError::UnusedExistential(
                binder.id().clone(),
            ));
        }
    }
    Ok(())
}

fn collect_term_variables(term: &SemanticTerm, used: &mut BTreeSet<SemanticId>) {
    match term.kind() {
        SemanticTermKind::Variable { variable } => {
            used.insert(variable.clone());
        }
        SemanticTermKind::Application { arguments, .. }
        | SemanticTermKind::Map { arguments, .. } => {
            for argument in arguments {
                collect_term_variables(argument, used);
            }
        }
        SemanticTermKind::KSequence { items, .. } => {
            for item in items {
                collect_term_variables(item, used);
            }
        }
        SemanticTermKind::Rewrite { from, to } => {
            collect_term_variables(from, used);
            collect_term_variables(to, used);
        }
        SemanticTermKind::Token { .. } => {}
    }
}

#[allow(clippy::too_many_lines)]
fn validate_term(
    term: &SemanticTerm,
    scope: &BTreeMap<SemanticId, SemanticSortRef>,
    declarations: &BTreeMap<StableItemId, ItemKind>,
    signatures: &BTreeMap<StableItemId, (SemanticSortRef, Vec<SemanticSortRef>)>,
    sort_parents: &BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
    nodes: &mut BTreeSet<SourceMapKey>,
) -> Result<(), SemanticValidationError> {
    insert_node(nodes, term.origin.key())?;
    require_semantic_sort(declarations, &term.sort)?;
    match &term.kind {
        SemanticTermKind::Variable { variable } => match scope.get(variable) {
            None => return Err(SemanticValidationError::DanglingVariable(variable.clone())),
            Some(sort) if *sort != term.sort => {
                return Err(SemanticValidationError::VariableSortMismatch(
                    variable.clone(),
                ));
            }
            Some(_) => {}
        },
        SemanticTermKind::Application {
            application,
            arguments,
        } => {
            let signature = match application {
                ApplicationRef::Declared(production) => {
                    let Some(kind) = declarations.get(production) else {
                        return Err(SemanticValidationError::DanglingProduction(Box::new(
                            production.clone(),
                        )));
                    };
                    if *kind != ItemKind::Constructor {
                        return Err(SemanticValidationError::WrongItemKind {
                            id: Box::new(production.clone()),
                            expected: ItemKind::Constructor,
                            actual: *kind,
                        });
                    }
                    signatures.get(production).cloned().ok_or_else(|| {
                        SemanticValidationError::DanglingProduction(Box::new(production.clone()))
                    })?
                }
                ApplicationRef::Builtin(operation) => builtin_signature(*operation),
            };
            let (result_sort, argument_sorts) = signature;
            if term.sort != result_sort
                || arguments.len() != argument_sorts.len()
                || arguments
                    .iter()
                    .zip(&argument_sorts)
                    .any(|(argument, sort)| !is_subsort(&argument.sort, sort, sort_parents))
            {
                return match application {
                    ApplicationRef::Declared(production) => Err(
                        SemanticValidationError::ApplicationSignature(Box::new(production.clone())),
                    ),
                    ApplicationRef::Builtin(operation) => Err(
                        SemanticValidationError::BuiltinApplicationSignature(*operation),
                    ),
                };
            }
            for argument in arguments {
                validate_term(
                    argument,
                    scope,
                    declarations,
                    signatures,
                    sort_parents,
                    nodes,
                )?;
            }
        }
        SemanticTermKind::Token { value } => {
            if value.is_empty() {
                return Err(SemanticValidationError::EmptyText("token value"));
            }
        }
        SemanticTermKind::KSequence { item_sort, items } => {
            require_semantic_sort(declarations, item_sort)?;
            if term.sort != SemanticSortRef::Builtin(BuiltinSort::KSequence) {
                return Err(SemanticValidationError::SequenceSortMismatch);
            }
            for item in items {
                validate_term(item, scope, declarations, signatures, sort_parents, nodes)?;
                if !is_subsort(&item.sort, item_sort, sort_parents) {
                    return Err(SemanticValidationError::SequenceItemSortMismatch);
                }
            }
        }
        SemanticTermKind::Map {
            operation,
            arguments,
        } => {
            if term.sort != SemanticSortRef::Builtin(BuiltinSort::Map) {
                return Err(SemanticValidationError::MapSortMismatch);
            }
            let valid_arity = match operation {
                MapOperation::Empty => arguments.is_empty(),
                MapOperation::Item => !arguments.is_empty() && arguments.len().is_multiple_of(2),
                MapOperation::Update => {
                    arguments.len() == 3
                        && arguments[0].sort == SemanticSortRef::Builtin(BuiltinSort::Map)
                }
            };
            if !valid_arity {
                return Err(SemanticValidationError::MapOperationSignature(*operation));
            }
            for argument in arguments {
                validate_term(
                    argument,
                    scope,
                    declarations,
                    signatures,
                    sort_parents,
                    nodes,
                )?;
            }
        }
        SemanticTermKind::Rewrite { from, to } => {
            validate_term(from, scope, declarations, signatures, sort_parents, nodes)?;
            validate_term(to, scope, declarations, signatures, sort_parents, nodes)?;
            if !is_subsort(&from.sort, &term.sort, sort_parents)
                || !is_subsort(&to.sort, &term.sort, sort_parents)
            {
                return Err(SemanticValidationError::RewriteSortMismatch);
            }
        }
    }
    Ok(())
}

fn validate_semantic_production_shape(
    id: &StableItemId,
    items: &[SemanticProductionItem],
    attributes: &[SemanticProductionAttribute],
) -> Result<(), SemanticValidationError> {
    if items.is_empty() {
        return Err(SemanticValidationError::EmptyProduction(Box::new(
            id.clone(),
        )));
    }
    let fields = items
        .iter()
        .filter_map(|item| match item.kind() {
            GrammarProductionItemKind::NonTerminal { field, .. } => Some(field.clone()),
            GrammarProductionItemKind::Terminal { .. }
            | GrammarProductionItemKind::RegexTerminal { .. } => None,
        })
        .collect::<Vec<_>>();
    if has_duplicate_fields(&fields) {
        return Err(SemanticValidationError::InvalidStrictnessField);
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
            return Err(SemanticValidationError::DuplicateProductionAttribute(name));
        }
        match attribute {
            ProductionAttribute::Strictness {
                fields: selected, ..
            } => {
                if selected.is_empty()
                    || has_duplicate_fields(&selected.iter().map(|field| field.field().clone()).collect::<Vec<_>>())
                    || selected.iter().any(|field| !fields.contains(field.field()))
                {
                    return Err(SemanticValidationError::InvalidStrictnessField);
                }
            }
            ProductionAttribute::Format { fragments, .. } => {
                if fragments.is_empty()
                    || fragments.iter().any(|fragment| {
                        matches!(fragment, FormatFragment::Item(position) if *position == 0 || usize::from(*position) > items.len())
                    })
                {
                    return Err(SemanticValidationError::InvalidFormat);
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
        return Err(SemanticValidationError::InvalidFunctionProduction);
    }
    if alias && function {
        return Err(SemanticValidationError::InvalidAliasProduction);
    }
    if token && (items.len() != 1 || regexes != 1) {
        return Err(SemanticValidationError::InvalidTokenProduction);
    }
    if regexes != 0 && !token {
        return Err(SemanticValidationError::RegexWithoutToken);
    }
    if bracket && fields.len() != 1 {
        return Err(SemanticValidationError::InvalidBracketProduction);
    }
    Ok(())
}

fn has_duplicate_fields(fields: &[ProductionFieldId]) -> bool {
    let mut unique = BTreeSet::new();
    fields.iter().any(|field| !unique.insert(field))
}

fn builtin_signature(operation: BuiltinOperation) -> (SemanticSortRef, Vec<SemanticSortRef>) {
    (
        SemanticSortRef::Builtin(operation.result_sort()),
        operation
            .argument_sorts()
            .iter()
            .copied()
            .map(SemanticSortRef::Builtin)
            .collect(),
    )
}

fn validate_precedence_order(modules: &[SemanticModule]) -> Result<(), SemanticValidationError> {
    let mut edges: BTreeMap<ProductionGroupId, BTreeSet<ProductionGroupId>> = BTreeMap::new();
    for relation in modules.iter().flat_map(|module| &module.precedences) {
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
                return Err(SemanticValidationError::PrecedenceCycle(start.clone()));
            }
            if visited.insert(group.clone()) {
                pending.extend(edges.get(&group).into_iter().flatten().cloned());
            }
        }
    }
    Ok(())
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
            Sha256Digest::new("a".repeat(64)).expect("valid digest"),
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

    fn claim_id() -> StableItemId {
        StableItemId::new(
            PackageId::new("ORG-EXAMPLE-CLAIM", "claim", "0.1.0", "workspace")
                .expect("valid package"),
            ["claim"],
            "reachability",
            ItemKind::Claim,
            "",
        )
        .expect("valid claim ID")
    }

    fn int_variable(key: &str, id: &str) -> SemanticTerm {
        SemanticTerm::variable(
            node(key),
            SemanticSortRef::Builtin(BuiltinSort::Int),
            sid(id),
        )
    }

    fn int_token(key: &str) -> SemanticTerm {
        SemanticTerm::token(node(key), SemanticSortRef::Builtin(BuiltinSort::Int), "0")
            .expect("valid token")
    }

    fn int_equals(key: &str, left: SemanticTerm, right: SemanticTerm) -> SemanticTerm {
        SemanticTerm::application(
            node(key),
            SemanticSortRef::Builtin(BuiltinSort::Bool),
            ApplicationRef::Builtin(BuiltinOperation::IntEqual),
            vec![left, right],
        )
    }

    fn claim_rule(before: SemanticTerm, after: SemanticTerm) -> SemanticRule {
        let body = FixedConfigurationRewrite::new(
            node("rewrite"),
            sid("configuration"),
            vec![FixedCellClause::new(
                node("clause"),
                sid("cell"),
                before,
                CellPost::Replace { term: after },
                CellContentFrame::Exact,
            )],
            Vec::new(),
        )
        .expect("valid configuration rewrite");
        let binder = SemanticClaimBinder::new(
            node("binder"),
            node("binder-name"),
            sid("exists"),
            node("binder-sort"),
            SemanticSortRef::Builtin(BuiltinSort::Int),
        );
        SemanticRule {
            origin: node("rule"),
            id: claim_id(),
            kind: SentenceKind::Claim,
            label: Some(
                SemanticRuleLabel::new(node("label"), "reachability").expect("valid label"),
            ),
            requires: None,
            priority: None,
            simplification: None,
            claim: Some(SemanticClaim::new(
                node("modality"),
                ClaimModality::AllPaths,
                None,
                Vec::new(),
                vec![binder],
                None,
            )),
            variables: vec![SemanticVariable::new(
                sid("exists"),
                SemanticSortRef::Builtin(BuiltinSort::Int),
            )],
            body: SemanticRuleBody::Configuration(body),
        }
    }

    fn validate_claim_only(rule: &SemanticRule) -> Result<(), SemanticValidationError> {
        let scope = variable_scope(&rule.variables, &BTreeMap::new())?;
        validate_claim(
            rule,
            rule.claim.as_ref().expect("claim metadata"),
            &scope,
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &mut BTreeSet::new(),
        )
    }

    #[test]
    fn semantic_claim_rejects_existential_on_left() {
        let rule = claim_rule(int_variable("before", "exists"), int_token("after"));
        assert_eq!(
            validate_claim_only(&rule),
            Err(SemanticValidationError::ExistentialScopeViolation(sid(
                "exists"
            )))
        );
    }

    #[test]
    fn semantic_claim_requires_each_existential_on_right_or_ensures() {
        let rule = claim_rule(int_token("before"), int_token("after"));
        assert_eq!(
            validate_claim_only(&rule),
            Err(SemanticValidationError::UnusedExistential(sid("exists")))
        );
    }

    #[test]
    fn semantic_claim_rejects_existential_in_requires() {
        let mut rule = claim_rule(int_token("before"), int_variable("after", "exists"));
        rule.requires = Some(SemanticRuleCondition::new(
            node("requires"),
            int_equals(
                "requires-eq",
                int_variable("requires-var", "exists"),
                int_token("requires-zero"),
            ),
        ));
        assert_eq!(
            validate_claim_only(&rule),
            Err(SemanticValidationError::ExistentialScopeViolation(sid(
                "exists"
            )))
        );
    }

    #[test]
    fn semantic_claim_rejects_unbound_claim_binder() {
        let mut rule = claim_rule(int_token("before"), int_variable("after", "exists"));
        rule.claim.as_mut().expect("claim metadata").existentials[0].id = sid("missing");
        assert_eq!(
            validate_claim_only(&rule),
            Err(SemanticValidationError::InvalidClaimBinder(sid("missing")))
        );
    }

    #[test]
    fn semantic_one_path_circular_claim_is_well_formed() {
        let mut rule = claim_rule(int_token("before"), int_variable("after", "exists"));
        let claim = rule.claim.as_mut().expect("claim metadata");
        claim.modality = ClaimModality::OnePath;
        claim.circularity_origin = Some(node("circularity"));
        assert_eq!(validate_claim_only(&rule), Ok(()));
    }

    #[test]
    fn semantic_claim_rejects_non_bool_ensures() {
        let mut rule = claim_rule(int_token("before"), int_variable("after", "exists"));
        rule.claim.as_mut().expect("claim metadata").ensures = Some(SemanticRuleCondition::new(
            node("ensures"),
            int_token("post"),
        ));
        assert_eq!(
            validate_claim_only(&rule),
            Err(SemanticValidationError::RuleConditionSortMismatch)
        );
    }

    #[test]
    fn semantic_claim_metadata_is_exclusive_to_claim_sentences() {
        let mut rule = claim_rule(int_token("before"), int_variable("after", "exists"));
        rule.kind = SentenceKind::Transition;
        assert!(matches!(
            validate_rule(
                &rule,
                None,
                &BTreeMap::new(),
                &BTreeMap::new(),
                &BTreeSet::new(),
                &BTreeSet::new(),
                &BTreeMap::new(),
                &mut BTreeSet::new(),
            ),
            Err(SemanticValidationError::InvalidClaimMetadata(_))
        ));

        let mut rule = claim_rule(
            int_token("missing-before"),
            int_variable("missing-after", "exists"),
        );
        rule.claim = None;
        assert!(matches!(
            validate_rule(
                &rule,
                None,
                &BTreeMap::new(),
                &BTreeMap::new(),
                &BTreeSet::new(),
                &BTreeSet::new(),
                &BTreeMap::new(),
                &mut BTreeSet::new(),
            ),
            Err(SemanticValidationError::InvalidClaimMetadata(_))
        ));
    }

    #[test]
    fn semantic_claim_requires_explicit_label() {
        let mut rule = claim_rule(int_token("before"), int_variable("after", "exists"));
        rule.label = None;
        assert!(matches!(
            validate_rule(
                &rule,
                None,
                &BTreeMap::new(),
                &BTreeMap::new(),
                &BTreeSet::new(),
                &BTreeSet::new(),
                &BTreeMap::new(),
                &mut BTreeSet::new(),
            ),
            Err(SemanticValidationError::ClaimLabelRequired(_))
        ));
    }

    #[test]
    fn semantic_claim_requires_configuration_body() {
        let mut rule = claim_rule(int_token("before"), int_variable("after", "exists"));
        rule.body = SemanticRuleBody::Term(Box::new(
            SemanticTerm::rewrite(
                node("term-rewrite"),
                SemanticSortRef::Builtin(BuiltinSort::Int),
                int_token("term-before"),
                int_variable("term-after", "exists"),
            )
            .expect("valid rewrite"),
        ));
        assert!(matches!(
            validate_rule(
                &rule,
                None,
                &BTreeMap::new(),
                &BTreeMap::new(),
                &BTreeSet::new(),
                &BTreeSet::new(),
                &BTreeMap::new(),
                &mut BTreeSet::new(),
            ),
            Err(SemanticValidationError::ClaimBodyNotConfiguration(_))
        ));
    }

    #[test]
    fn semantic_claim_rejects_equation_or_simplification_metadata() {
        let mut rule = claim_rule(int_token("before"), int_variable("after", "exists"));
        rule.simplification = Some(SemanticSimplification::new(node("simplification"), None));
        assert!(matches!(
            validate_rule(
                &rule,
                None,
                &BTreeMap::new(),
                &BTreeMap::new(),
                &BTreeSet::new(),
                &BTreeSet::new(),
                &BTreeMap::new(),
                &mut BTreeSet::new(),
            ),
            Err(SemanticValidationError::InvalidClaimMetadata(_))
        ));
    }
}

fn validate_semantic_subsort_order(
    edges: &BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
) -> Result<(), SemanticValidationError> {
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
                return Err(SemanticValidationError::SubsortCycle(Box::new(
                    start.clone(),
                )));
            }
            if visited.insert(sort.clone()) {
                pending.extend(edges.get(&sort).into_iter().flatten().cloned());
            }
        }
    }
    Ok(())
}

fn is_subsort(
    candidate: &SemanticSortRef,
    expected: &SemanticSortRef,
    parents: &BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
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
