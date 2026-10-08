//! Resolved, target-neutral KRS semantic IR.
//!
//! This representation records KRS meaning after descriptor collection and
//! name resolution. It deliberately contains neither generated K names nor
//! frontend-specific production metadata; those belong to Definition IR and
//! adapters respectively.

use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt;

use serde::{Deserialize, Deserializer, Serialize};

use crate::ir_level::SemanticLevel;
use crate::ir_validation::{
    collect_configuration_nodes, insert_node, require_kind, require_sort, validate_context_alias,
    validate_context_alias_frames, validate_fixed_configuration,
    validate_initializer_cell_references, validate_precedence_order, validate_production_shape,
    validate_rule, validate_rule_cell_references, validate_subsort_order,
    validate_term_cell_references,
};
use krs_ir::sorted::{SortKey, SortedByKey};
use krs_ir::{
    ApplicationRef, BuiltinOperation, BuiltinSort, FixedConfiguration, FixedConfigurationRewrite,
    GrammarProductionItem, GrammarProductionItemKind, GroupAssociativitySentence, HookOperation,
    ItemKind, ListOperation, MapOperation, ModuleId, NodeOrigin, PrecedenceRelation,
    ProductionAttribute, ProductionGroupId, SchemaVersion, SemanticId, SentenceKind, SetOperation,
    SourceMapKey, StableItemId,
};

impl SortKey for SemanticModule {
    type Key = ModuleId;
    fn sort_key(&self) -> &Self::Key {
        &self.id
    }
}

macro_rules! semantic_id_key {
    ($($type:ty),+ $(,)?) => {$ (
        impl SortKey for $type {
            type Key = StableItemId;
            fn sort_key(&self) -> &Self::Key { &self.id }
        }
    )+};
}

semantic_id_key!(
    SemanticSort,
    SemanticProduction,
    SemanticContextAlias,
    SemanticRule
);

impl SortKey for SemanticSubsort {
    type Key = Self;
    fn sort_key(&self) -> &Self::Key {
        self
    }
}

/// Authored or compiler-provided semantic application reference.
pub type SemanticApplicationRef = ApplicationRef<StableItemId>;

/// A semantic grammar item carrying typed sort references.
pub type SemanticProductionItem = GrammarProductionItem<SemanticSortRef>;

/// Classified semantic production metadata.
pub type SemanticProductionAttribute = ProductionAttribute<SemanticSortRef>;

/// A resolved sort reference in semantic IR.
pub type SemanticSortRef = crate::IrSortRef<StableItemId>;

/// A checked resolved semantic theory.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SemanticTheory {
    schema_version: SchemaVersion,
    modules: SortedByKey<SemanticModule>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct SemanticTheoryWire {
    schema_version: SchemaVersion,
    modules: Vec<SemanticModule>,
}

impl<'de> Deserialize<'de> for SemanticTheory {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = SemanticTheoryWire::deserialize(deserializer)?;
        if wire.schema_version != SchemaVersion::CURRENT {
            return Err(serde::de::Error::custom(format_args!(
                "unsupported Semantic IR schema {}; expected {}",
                wire.schema_version.0,
                SchemaVersion::CURRENT.0
            )));
        }
        Self::new(wire.modules).map_err(serde::de::Error::custom)
    }
}

impl SemanticTheory {
    /// Validates a complete theory. Exactly one configuration is required.
    ///
    /// # Errors
    ///
    /// Returns [`SemanticValidationError`] for any invalid graph invariant.
    pub fn new(modules: Vec<SemanticModule>) -> Result<Self, SemanticValidationError> {
        let theory = Self {
            schema_version: SchemaVersion::CURRENT,
            modules: SortedByKey::new(modules),
        };
        theory.validate()?;
        Ok(theory)
    }

    /// Rebuilds the theory and its modules from permuted set-like inputs.
    ///
    /// # Panics
    ///
    /// Panics if this validated theory cannot be rebuilt.
    #[cfg(feature = "test-support")]
    #[must_use]
    pub fn permute_sets(&self, seed: u64) -> Self {
        let mut modules = self
            .modules
            .iter()
            .map(|module| module.permute_sets(seed))
            .collect::<Vec<_>>();
        krs_ir::testing::permute(&mut modules, seed);
        Self::new(modules).unwrap_or_else(|error| {
            panic!("SemanticTheory seed {seed}: permuted rebuild failed: {error}")
        })
    }

    /// Returns the IR schema version.
    #[must_use]
    pub const fn schema_version(&self) -> SchemaVersion {
        self.schema_version
    }

    /// Returns modules in canonical ID order.
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
        let mut json = serde_json::to_string_pretty(self)?;
        json.push('\n');
        Ok(json)
    }

    #[expect(
        clippy::too_many_lines,
        reason = "One ordered pass checks whole-theory identities, references, and rule invariants."
    )]
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
        let mut cell_ids = BTreeSet::new();
        let mut configurations = 0_usize;

        for module in &self.modules {
            insert_unique(
                &mut module_ids,
                module.id.clone(),
                krs_ir::SemanticIdentityKind::Module,
                module.id.as_str(),
            )?;
            insert_node::<SemanticLevel>(&mut node_keys, module.origin.key())?;
            for sort in &module.sorts {
                validate_item_kind(&sort.id, ItemKind::Sort)?;
                insert_declaration(&mut declarations, &sort.id)?;
                insert_node::<SemanticLevel>(&mut node_keys, sort.origin.key())?;
            }
            for subsort in &module.subsorts {
                insert_node::<SemanticLevel>(&mut node_keys, subsort.origin.key())?;
                sort_parents
                    .entry(subsort.subsort.clone())
                    .or_default()
                    .push(subsort.supersort.clone());
            }
            for production in &module.productions {
                validate_item_kind(&production.id, ItemKind::Constructor)?;
                insert_declaration(&mut declarations, &production.id)?;
                insert_node::<SemanticLevel>(&mut node_keys, production.origin.key())?;
                validate_production_shape::<SemanticLevel>(
                    &production.id,
                    &production.result_sort,
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
                    insert_node::<SemanticLevel>(&mut node_keys, item.origin().key())?;
                }
                for attribute in &production.attributes {
                    insert_node::<SemanticLevel>(&mut node_keys, attribute.origin().key())?;
                    if let ProductionAttribute::Strictness {
                        using,
                        fields,
                        result_sort,
                        ..
                    } = attribute
                    {
                        if let Some(using) = using {
                            insert_node::<SemanticLevel>(&mut node_keys, using.origin().key())?;
                        }
                        for field in fields {
                            insert_node::<SemanticLevel>(&mut node_keys, field.origin().key())?;
                        }
                        insert_node::<SemanticLevel>(&mut node_keys, result_sort.origin().key())?;
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
                insert_node::<SemanticLevel>(&mut node_keys, precedence.origin().key())?;
            }
            for associativity in &module.associativities {
                insert_node::<SemanticLevel>(&mut node_keys, associativity.origin().key())?;
            }
            for rule in &module.rules {
                let expected = rule.kind().item_kind();
                validate_item_kind(&rule.id, expected)?;
                insert_declaration(&mut declarations, &rule.id)?;
                insert_node::<SemanticLevel>(&mut node_keys, rule.origin.key())?;
            }
            for alias in &module.context_aliases {
                validate_item_kind(&alias.id, ItemKind::ContextAlias)?;
                insert_declaration(&mut declarations, &alias.id)?;
                insert_node::<SemanticLevel>(&mut node_keys, alias.origin.key())?;
                insert_node::<SemanticLevel>(&mut node_keys, alias.name_origin.key())?;
                insert_node::<SemanticLevel>(&mut node_keys, alias.here_origin.key())?;
            }
            if let Some(configuration) = &module.configuration {
                configurations += 1;
                insert_semantic_id(
                    &mut semantic_ids,
                    configuration.id(),
                    krs_ir::SemanticIdentityKind::Configuration,
                )?;
                insert_semantic_id(
                    &mut semantic_ids,
                    configuration.initializer_id(),
                    krs_ir::SemanticIdentityKind::Initializer,
                )?;
                insert_node::<SemanticLevel>(&mut node_keys, configuration.origin().key())?;
                insert_node::<SemanticLevel>(
                    &mut node_keys,
                    configuration.initializer_origin().key(),
                )?;
                collect_configuration_nodes::<SemanticLevel>(
                    configuration,
                    &mut (&mut semantic_ids, &mut cell_ids),
                    &mut node_keys,
                )?;
            }
        }

        if configurations != 1 {
            return Err(SemanticValidationError::ConfigurationCount(configurations));
        }
        let fixed_configuration = self
            .modules
            .iter()
            .find_map(|module| module.configuration.as_ref());

        for module in &self.modules {
            for import in &module.imports {
                if !module_ids.contains(import) {
                    return Err(SemanticValidationError::DanglingModule(import.clone()));
                }
            }
            for subsort in &module.subsorts {
                require_sort::<SemanticLevel>(&declarations, &subsort.subsort)?;
                require_sort::<SemanticLevel>(&declarations, &subsort.supersort)?;
            }
            for production in &module.productions {
                require_sort::<SemanticLevel>(&declarations, &production.result_sort)?;
                for item in &production.items {
                    if let GrammarProductionItemKind::NonTerminal { sort, .. } = item.kind() {
                        require_sort::<SemanticLevel>(&declarations, sort)?;
                    }
                }
                for attribute in &production.attributes {
                    if let ProductionAttribute::Strictness { result_sort, .. } = attribute {
                        require_sort::<SemanticLevel>(&declarations, result_sort.sort())?;
                    }
                    if let ProductionAttribute::Strictness {
                        using: Some(alias), ..
                    } = attribute
                    {
                        require_kind::<SemanticLevel>(
                            &declarations,
                            alias.alias(),
                            ItemKind::ContextAlias,
                        )?;
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
                validate_fixed_configuration::<SemanticLevel>(
                    configuration,
                    &declarations,
                    &production_signatures,
                    &sort_parents,
                    &cell_ids,
                    &mut node_keys,
                )?;
            }
            for rule in &module.rules {
                validate_rule::<SemanticLevel>(
                    rule,
                    fixed_configuration,
                    &declarations,
                    &production_signatures,
                    &functional_productions,
                    &alias_productions,
                    &sort_parents,
                    &cell_ids,
                    &mut node_keys,
                )?;
            }
        }
        validate_precedence_order::<SemanticLevel>(&self.modules)?;
        validate_subsort_order::<SemanticLevel>(&sort_parents)?;
        for module in &self.modules {
            if let Some(configuration) = &module.configuration {
                validate_initializer_cell_references::<SemanticLevel>(
                    configuration.initializer(),
                    &declarations,
                    &cell_ids,
                )?;
            }
            for rule in &module.rules {
                validate_rule_cell_references::<SemanticLevel>(rule, &declarations, &cell_ids)?;
            }
            for alias in &module.context_aliases {
                validate_context_alias::<SemanticLevel>(
                    alias,
                    &declarations,
                    &production_signatures,
                    &sort_parents,
                    &cell_ids,
                    &mut node_keys,
                )?;
                for cell in alias.body().cells() {
                    validate_term_cell_references::<SemanticLevel>(
                        cell.pattern(),
                        &declarations,
                        &cell_ids,
                    )?;
                }
                validate_context_alias_frames::<SemanticLevel>(
                    alias,
                    fixed_configuration,
                    &declarations,
                )?;
            }
        }
        let sorts = self
            .modules
            .iter()
            .flat_map(|module| &module.sorts)
            .map(|sort| {
                let name = sort.explicit_symbol.as_ref().map_or_else(
                    || sort.id.item_name(),
                    krs_ir::ExplicitSymbol::final_component,
                );
                (&sort.id, name)
            })
            .collect();
        let productions = self
            .modules
            .iter()
            .flat_map(|module| &module.productions)
            .map(|production| crate::ir_validation::ProductionView {
                result_sort: &production.result_sort,
                items: &production.items,
                attributes: &production.attributes,
            });
        crate::ir_validation::validate_hook_point_constructors::<SemanticLevel>(
            &sorts,
            productions,
        )?;
        Ok(())
    }
}

#[cfg(feature = "test-support")]
impl krs_ir::testing::CanonicalContract for SemanticTheory {
    fn permute_sets(&self, seed: u64) -> Self {
        Self::permute_sets(self, seed)
    }

    fn to_canonical_json(&self) -> serde_json::Result<String> {
        Self::to_canonical_json(self)
    }
}

/// One resolved module. Imports are a set; declaration vectors are sentence
/// collections and are canonically sorted without reordering nested semantic data.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SemanticModule {
    origin: NodeOrigin,
    id: ModuleId,
    imports: BTreeSet<ModuleId>,
    sorts: SortedByKey<SemanticSort>,
    subsorts: SortedByKey<SemanticSubsort>,
    productions: SortedByKey<SemanticProduction>,
    precedences: SortedByKey<PrecedenceRelation>,
    associativities: SortedByKey<GroupAssociativitySentence>,
    #[serde(skip_serializing_if = "Option::is_none")]
    configuration: Option<SemanticConfiguration>,
    context_aliases: SortedByKey<SemanticContextAlias>,
    rules: SortedByKey<SemanticRule>,
    #[serde(default, skip_serializing_if = "is_signed")]
    int_literals: krs_ir::IntLiterals,
}

#[expect(
    clippy::trivially_copy_pass_by_ref,
    reason = "serde's skip_serializing_if passes the field by reference."
)]
fn is_signed(value: &krs_ir::IntLiterals) -> bool {
    *value == krs_ir::IntLiterals::Signed
}

impl SemanticModule {
    /// Creates a module. Cross-module references are checked by
    /// [`SemanticTheory::new`].
    #[must_use]
    #[expect(
        clippy::too_many_arguments,
        reason = "The constructor explicitly supplies every semantic module sentence collection."
    )]
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
    #[expect(
        clippy::too_many_arguments,
        reason = "The constructor explicitly supplies module sentence collections and context aliases."
    )]
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
            imports: imports.into_iter().collect(),
            sorts: SortedByKey::new(sorts),
            subsorts: SortedByKey::new(subsorts),
            productions: SortedByKey::new(productions),
            precedences: SortedByKey::new(precedences),
            associativities: SortedByKey::new(associativities),
            configuration,
            context_aliases: SortedByKey::new(context_aliases),
            rules: SortedByKey::new(rules),
            int_literals: krs_ir::IntLiterals::Signed,
        }
    }

    /// Sets the package's program-syntax integer literal module.
    #[must_use]
    pub const fn with_int_literals(mut self, int_literals: krs_ir::IntLiterals) -> Self {
        self.int_literals = int_literals;
        self
    }

    /// Returns the package's program-syntax integer literal module.
    #[must_use]
    pub const fn int_literals(&self) -> krs_ir::IntLiterals {
        self.int_literals
    }

    /// Rebuilds every set-like module collection from permuted inputs.
    #[cfg(feature = "test-support")]
    #[must_use]
    pub fn permute_sets(&self, seed: u64) -> Self {
        let mut imports = self.imports.iter().cloned().collect::<Vec<_>>();
        let mut sorts = self.sorts.iter().cloned().collect::<Vec<_>>();
        let mut subsorts = self.subsorts.iter().cloned().collect::<Vec<_>>();
        let mut productions = self.productions.iter().cloned().collect::<Vec<_>>();
        let mut precedences = self.precedences.iter().cloned().collect::<Vec<_>>();
        let mut associativities = self.associativities.iter().cloned().collect::<Vec<_>>();
        let mut context_aliases = self.context_aliases.iter().cloned().collect::<Vec<_>>();
        let mut rules = self.rules.iter().cloned().collect::<Vec<_>>();
        krs_ir::testing::permute(&mut imports, seed);
        krs_ir::testing::permute(&mut sorts, seed);
        krs_ir::testing::permute(&mut subsorts, seed);
        krs_ir::testing::permute(&mut productions, seed);
        krs_ir::testing::permute(&mut precedences, seed);
        krs_ir::testing::permute(&mut associativities, seed);
        krs_ir::testing::permute(&mut context_aliases, seed);
        krs_ir::testing::permute(&mut rules, seed);
        Self::new_with_context_aliases(
            self.origin.clone(),
            self.id.clone(),
            imports,
            sorts,
            subsorts,
            productions,
            precedences,
            associativities,
            self.configuration.clone(),
            context_aliases,
            rules,
        )
        .with_int_literals(self.int_literals)
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
    pub const fn imports(&self) -> &BTreeSet<ModuleId> {
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
}

/// A resolved authored open sort declaration.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SemanticSort {
    origin: NodeOrigin,
    id: StableItemId,
    #[serde(default, skip_serializing_if = "krs_ir::RustVisibility::is_inherited")]
    visibility: krs_ir::RustVisibility,
    #[serde(skip_serializing_if = "Option::is_none")]
    explicit_symbol: Option<krs_ir::ExplicitSymbol>,
}

impl SemanticSort {
    /// Creates a semantic sort declaration.
    #[must_use]
    pub const fn new(origin: NodeOrigin, id: StableItemId) -> Self {
        Self {
            origin,
            id,
            visibility: krs_ir::RustVisibility::Inherited,
            explicit_symbol: None,
        }
    }
    /// Creates a semantic sort with exact author-facing API metadata.
    #[must_use]
    pub const fn with_api(
        origin: NodeOrigin,
        id: StableItemId,
        visibility: krs_ir::RustVisibility,
        explicit_symbol: Option<krs_ir::ExplicitSymbol>,
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
    pub const fn visibility(&self) -> &krs_ir::RustVisibility {
        &self.visibility
    }
    /// Returns the optional explicit stable public identity.
    #[must_use]
    pub const fn explicit_symbol(&self) -> Option<&krs_ir::ExplicitSymbol> {
        self.explicit_symbol.as_ref()
    }
}

/// One direct typed subsort edge.
/// Either endpoint may be compiler-provided.
pub type SemanticSubsort = crate::IrSubsort<crate::SemanticLevel>;

/// A resolved nominal production with classified object grammar.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SemanticProduction {
    origin: NodeOrigin,
    id: StableItemId,
    result_sort: SemanticSortRef,
    items: Vec<SemanticProductionItem>,
    attributes: Vec<SemanticProductionAttribute>,
    #[serde(default, skip_serializing_if = "krs_ir::RustVisibility::is_inherited")]
    visibility: krs_ir::RustVisibility,
    #[serde(skip_serializing_if = "Option::is_none")]
    explicit_symbol: Option<krs_ir::ExplicitSymbol>,
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
        validate_production_shape::<SemanticLevel>(&id, &result_sort, &items, &attributes)?;
        Ok(Self {
            origin,
            id,
            result_sort,
            items,
            attributes,
            visibility: krs_ir::RustVisibility::Inherited,
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
        visibility: krs_ir::RustVisibility,
        explicit_symbol: Option<krs_ir::ExplicitSymbol>,
    ) -> Result<Self, SemanticValidationError> {
        validate_production_shape::<SemanticLevel>(&id, &result_sort, &items, &attributes)?;
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
    pub const fn visibility(&self) -> &krs_ir::RustVisibility {
        &self.visibility
    }
    /// Returns the optional explicit stable public identity.
    #[must_use]
    pub const fn explicit_symbol(&self) -> Option<&krs_ir::ExplicitSymbol> {
        self.explicit_symbol.as_ref()
    }
}

/// The one fixed, possibly nested, configuration tree of a semantic theory.
pub type SemanticConfiguration = FixedConfiguration<SemanticSortRef, SemanticId, SemanticTerm>;

/// A resolved rule variable declaration.
pub type SemanticVariable = crate::IrVariable<crate::SemanticLevel>;

/// One provenance-bearing explicit emitted K rule label.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SemanticRuleLabel {
    origin: NodeOrigin,
    name: String,
}

/// One provenance-bearing object-language Boolean rule condition.
pub type SemanticRuleCondition = crate::IrRuleCondition<crate::SemanticLevel>;

/// One explicitly scoped claim binder declaration.
pub type SemanticClaimBinder = crate::IrClaimBinder<crate::SemanticLevel>;

/// Typed reachability metadata present only on claims.
pub type SemanticClaim = crate::IrClaim<crate::SemanticLevel>;

/// One explicit equation or transition-rule priority.
pub type SemanticRulePriority = crate::IrRulePriority;

/// Simplifier classification and optional ordering hint.
pub type SemanticSimplification = crate::IrSimplification;

/// One numeric simplification ordering hint.
pub type SemanticSimplificationPriority = crate::IrSimplificationPriority;

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
        if !krs_ir::transport::grammar::valid_rule_label_name(&name) {
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

/// The check-only `nondet = group` key of a transition.
///
/// Rules of one group may overlap at one priority: the overlap check skips
/// their pairs and validates the group instead. A group is scoped to the
/// package of its rules. It never reaches Definition IR or emitted K.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SemanticNondetGroup {
    origin: NodeOrigin,
    name: String,
}

impl SemanticNondetGroup {
    /// Creates a group key with its authored identifier provenance.
    #[must_use]
    pub fn new(origin: NodeOrigin, name: impl Into<String>) -> Self {
        Self {
            origin,
            name: name.into(),
        }
    }

    /// Returns the authored identifier provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }

    /// Returns the authored group identifier.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }
}

/// One relational semantic sentence.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Deserialize)]
#[serde(
    deny_unknown_fields,
    try_from = "SemanticRuleWire<'static, crate::ir_level::RuleBodyWire<SemanticLevel>>"
)]
pub struct SemanticRule {
    origin: NodeOrigin,
    id: StableItemId,
    label: Option<SemanticRuleLabel>,
    requires: Option<SemanticRuleCondition>,
    priority: Option<SemanticRulePriority>,
    simplification: Option<SemanticSimplification>,
    claim: Option<SemanticClaim>,
    nondet_group: Option<SemanticNondetGroup>,
    anywhere: Option<NodeOrigin>,
    variables: Vec<SemanticVariable>,
    content: crate::ir_level::RuleContent<crate::SemanticLevel>,
}

impl Serialize for SemanticRule {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        SemanticRuleWire {
            origin: Cow::Borrowed(&self.origin),
            id: Cow::Borrowed(&self.id),
            kind: self.kind(),
            label: self.label.as_ref().map(Cow::Borrowed),
            requires: self.requires.as_ref().map(Cow::Borrowed),
            priority: self.priority.as_ref().map(Cow::Borrowed),
            simplification: self.simplification.as_ref().map(Cow::Borrowed),
            claim: self.claim.as_ref().map(Cow::Borrowed),
            nondet_group: self.nondet_group.as_ref().map(Cow::Borrowed),
            anywhere: self.anywhere.as_ref().map(Cow::Borrowed),
            variables: Cow::Borrowed(&self.variables),
            body: self.relational_body(),
        }
        .serialize(serializer)
    }
}

#[derive(Serialize, Deserialize)]
#[serde(rename = "SemanticRule", deny_unknown_fields)]
struct SemanticRuleWire<'a, B> {
    origin: Cow<'a, NodeOrigin>,
    id: Cow<'a, StableItemId>,
    kind: SentenceKind,
    #[serde(skip_serializing_if = "Option::is_none")]
    label: Option<Cow<'a, SemanticRuleLabel>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    requires: Option<Cow<'a, SemanticRuleCondition>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    priority: Option<Cow<'a, SemanticRulePriority>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    simplification: Option<Cow<'a, SemanticSimplification>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    claim: Option<Cow<'a, SemanticClaim>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    nondet_group: Option<Cow<'a, SemanticNondetGroup>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    anywhere: Option<Cow<'a, NodeOrigin>>,
    variables: Cow<'a, [SemanticVariable]>,
    body: B,
}

impl TryFrom<SemanticRuleWire<'static, crate::ir_level::RuleBodyWire<SemanticLevel>>>
    for SemanticRule
{
    type Error = SemanticValidationError;
    fn try_from(
        value: SemanticRuleWire<'static, crate::ir_level::RuleBodyWire<SemanticLevel>>,
    ) -> Result<Self, Self::Error> {
        let content = value.body.refine(value.kind).map_err(|error| match error {
            crate::ir_level::RuleBodyRefinementError::NotRewrite => {
                SemanticValidationError::RuleBodyNotRewrite(Box::new(value.id.as_ref().clone()))
            }
            crate::ir_level::RuleBodyRefinementError::InvalidConfigurationKind => {
                if value.kind == SentenceKind::Alias {
                    SemanticValidationError::InvalidAliasRoot(Box::new(value.id.as_ref().clone()))
                } else {
                    SemanticValidationError::InvalidSimplificationRoot(Box::new(
                        value.id.as_ref().clone(),
                    ))
                }
            }
        })?;
        Ok(Self {
            origin: value.origin.into_owned(),
            id: value.id.into_owned(),
            label: value.label.map(Cow::into_owned),
            requires: value.requires.map(Cow::into_owned),
            priority: value.priority.map(Cow::into_owned),
            simplification: value.simplification.map(Cow::into_owned),
            claim: value.claim.map(Cow::into_owned),
            nondet_group: value.nondet_group.map(Cow::into_owned),
            anywhere: value.anywhere.map(Cow::into_owned),
            variables: value.variables.into_owned(),
            content,
        })
    }
}

/// One source-level, one-sided reusable fixed-configuration context template.
pub type SemanticContextAlias = crate::IrContextAlias<crate::SemanticLevel>;

/// Structured relational body of one ordinary labeled semantic rule.
pub type SemanticRuleBody = crate::IrRuleBody<crate::SemanticLevel>;

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
        let body = body
            .try_into()
            .map_err(|_| SemanticValidationError::RuleBodyNotRewrite(Box::new(id.clone())))?;
        Ok(Self {
            origin,
            id,
            label: None,
            requires: None,
            priority: None,
            simplification: None,
            claim: None,
            nondet_group: None,
            anywhere: None,
            variables,
            content: crate::ir_level::RuleContent::Term { kind, body },
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
        let kind = krs_ir::ConfigurationSentenceKind::try_from(kind).map_err(|_| {
            if kind == SentenceKind::Alias {
                SemanticValidationError::InvalidAliasRoot(Box::new(id.clone()))
            } else {
                SemanticValidationError::InvalidSimplificationRoot(Box::new(id.clone()))
            }
        })?;
        let expected = kind.item_kind();
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
            label: None,
            requires: None,
            priority: None,
            simplification: None,
            claim: None,
            nondet_group: None,
            anywhere: None,
            variables,
            content: crate::ir_level::RuleContent::Configuration { kind, body },
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
        self.content.kind()
    }
    /// Attaches an explicit equation or transition-rule priority.
    ///
    /// # Errors
    ///
    /// Returns [`SemanticValidationError::InvalidRulePriority`] when priority
    /// metadata is attached to anything other than an equation or transition.
    pub fn with_priority(
        mut self,
        priority: Option<SemanticRulePriority>,
    ) -> Result<Self, SemanticValidationError> {
        if priority.is_some()
            && !matches!(
                self.kind(),
                SentenceKind::Equation | SentenceKind::Transition
            )
        {
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
    /// Attaches the check-only nondeterminism group of a transition.
    #[must_use]
    pub fn with_nondet_group(mut self, group: Option<SemanticNondetGroup>) -> Self {
        self.nondet_group = group;
        self
    }
    /// Returns the check-only nondeterminism group.
    #[must_use]
    pub const fn nondet_group(&self) -> Option<&SemanticNondetGroup> {
        self.nondet_group.as_ref()
    }
    /// Marks a term-shaped transition as an anywhere rule, with the marker's provenance.
    #[must_use]
    pub fn with_anywhere(mut self, origin: Option<NodeOrigin>) -> Self {
        self.anywhere = origin;
        self
    }
    /// Returns the `anywhere` marker provenance of an anywhere rule.
    #[must_use]
    pub const fn anywhere(&self) -> Option<&NodeOrigin> {
        self.anywhere.as_ref()
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
    /// Borrows the term rewrite, when present.
    #[must_use]
    pub fn body(&self) -> Option<&crate::IrRewrite<crate::SemanticLevel>> {
        match &self.content {
            crate::ir_level::RuleContent::Term { body, .. } => Some(body),
            crate::ir_level::RuleContent::Configuration { .. } => None,
        }
    }

    /// Returns the typed relational body.
    #[must_use]
    pub const fn relational_body(&self) -> crate::ir_level::RuleBodyRef<'_, crate::SemanticLevel> {
        self.content.body()
    }
}

/// A typed semantic term whose nested nodes retain their own origins and keys.
pub type SemanticTerm = crate::IrTerm<crate::SemanticLevel>;

/// Structured target-neutral semantic term forms.
pub type SemanticTermKind = crate::IrTermKind<crate::SemanticLevel>;

/// Typed failure while constructing or validating semantic IR.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SemanticValidationError {
    /// No module was supplied.
    EmptyTheory,
    /// A textual field was blank.
    EmptyText(krs_ir::IrField),
    /// A set-like identity was repeated.
    DuplicateId {
        /// Identity namespace.
        kind: krs_ir::SemanticIdentityKind,
        /// Debug-stable identity text.
        id: String,
    },
    /// A source-map key was used by two nodes.
    DuplicateSourceMapKey(SourceMapKey),
    /// An import names no module.
    DanglingModule(ModuleId),
    /// An item reference names no declaration.
    DanglingItem(Box<StableItemId>),
    /// A cell reference names no registered fixed cell.
    DanglingCell(SemanticId),
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
    DuplicateProductionAttribute(krs_ir::ProductionAttributeFamily),
    /// Token metadata was attached to a non-regex production.
    InvalidTokenProduction,
    /// A regex terminal lacked token metadata.
    RegexWithoutToken,
    /// Strictness named no field or an unknown/repeated field.
    InvalidStrictnessField,
    /// Format metadata was empty or referenced a nonexistent item.
    InvalidFormat,
    /// Colour metadata was invalid: an empty colour or one containing `,` or
    /// `)`, a `colors` list whose length is not the terminal count plus the
    /// number of `%c`, or `%c`/`%r` without a colour.
    InvalidColors,
    /// A production was marked both `internal` and `program`.
    InternalWithProgram,
    /// A production was marked both `prefer` and `avoid`.
    PreferAndAvoid,
    /// A token or bracket production was marked `prefer`.
    PreferOnParseOnlyProduction,
    /// A bracket production did not have exactly one nonterminal.
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
        expected_signature: krs_ir::Bn128PointSignature,
        /// Constructors matching that signature in the theory.
        matching_constructors: usize,
    },
    /// Alias and function metadata occurred on the same production.
    InvalidAliasProduction,
    /// A precedence or associativity sentence referenced no production group.
    DanglingProductionGroup(ProductionGroupId),
    /// The strict production-group precedence relation contained a cycle.
    PrecedenceCycle(ProductionGroupId),
    /// The strict subsort relation contained a cycle.
    SubsortCycle(Box<SemanticSortRef>),
    /// A theory requires exactly one selected configuration.
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
    /// Rule priority metadata occurred on an unsupported sentence kind.
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
    /// A structured fixed initializer did not mirror its declaration tree.
    InitializerTreeMismatch,
    /// A structured initializer leaf term has the wrong sort.
    InitializerLeafSortMismatch,
    /// A Map term did not carry builtin Map sort.
    MapSortMismatch,
    /// A Map operation had a wrong result or operand sort.
    MapOperationSignature(MapOperation),
    /// A List operation had a wrong result or operand sort.
    ListOperationSignature(ListOperation),
    /// A Set operation had a wrong result or operand sort.
    SetOperationSignature(SetOperation),
    /// A configuration rule exists without a general fixed configuration.
    ConfigurationRuleWithoutFixedConfiguration(Box<StableItemId>),
    /// A configuration rule names a different fixed configuration.
    ConfigurationRuleTargetMismatch(Box<StableItemId>),
    /// A cell rule references a missing/non-leaf cell or incomplete frame.
    InvalidCellFraming,
    /// A cell-content frame is incompatible with its leaf sort.
    CellFrameSortMismatch,
    /// A context-alias frame is incompatible with its leaf-cell sort.
    ContextAliasFrameSortMismatch,
    /// A context-alias frame binding is absent or has the wrong sort.
    ContextAliasFrameBindingMismatch(SemanticId),
    /// Context-alias declarations differ from term and frame uses.
    ContextAliasVariableClosure,
    /// A named sequence/map frame binding is absent or has the wrong sort.
    CellFrameBindingMismatch(SemanticId),
}

impl fmt::Display for SemanticValidationError {
    #[expect(
        clippy::too_many_lines,
        reason = "Exhaustive formatting keeps each semantic validation message with its variant."
    )]
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyTheory => formatter.write_str("semantic theory must contain a module"),
            Self::EmptyText(field) => write!(formatter, "{field} must not be empty"),
            Self::DuplicateId { kind, id } => write!(formatter, "duplicate {kind} ID {id}"),
            Self::DuplicateSourceMapKey(key) => write!(formatter, "duplicate source-map key {key}"),
            Self::DanglingModule(id) => {
                write!(formatter, "dangling module reference {id}")
            }
            Self::DanglingItem(id) => write!(formatter, "dangling item reference {id}"),
            Self::DanglingCell(id) => write!(
                formatter,
                "cell reference `{id}` has no fixed-cell declaration"
            ),
            Self::WrongItemKind {
                id,
                expected,
                actual,
            } => write!(
                formatter,
                "item {id} has kind {actual}, expected {expected}"
            ),
            Self::EmptyProduction(id) => write!(formatter, "production {id} has no items"),
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
            Self::InvalidColors => formatter.write_str(
                "colour metadata must name nonempty colours without `,` or `)`; `colors` needs one colour per terminal and per `%c`, and `%c`/`%r` need a colour",
            ),
            Self::InternalWithProgram => {
                formatter.write_str("a production cannot be both `internal` and `program`")
            }
            Self::PreferAndAvoid => {
                formatter.write_str("a production is either preferred or avoided, not both")
            }
            Self::PreferOnParseOnlyProduction => {
                formatter.write_str("`prefer` applies only to constructor and function productions, not to token or bracket productions")
            }
            Self::InvalidBracketProduction => formatter
                .write_str("bracket metadata requires exactly one nonterminal grammar item"),
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
            Self::ConfigurationCount(count) => write!(
                formatter,
                "semantic theory requires exactly one configuration, found {count}"
            ),
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
            Self::DanglingProduction(id) => {
                write!(formatter, "dangling production reference {id}")
            }
            Self::ApplicationSignature(id) => write!(
                formatter,
                "application does not match production signature {id}"
            ),
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
            Self::RuleBodyNotRewrite(id) => write!(formatter, "rule {id} body must be a rewrite"),
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
                "rule priority cannot occur on {} sentence `{}`",
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
            Self::InvalidRuleLabel(label) => {
                write!(formatter, "invalid explicit K rule label {label}")
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
            Self::ContextAliasFrameSortMismatch => {
                formatter.write_str("context-alias frame is incompatible with its leaf-cell sort")
            }
            Self::ContextAliasFrameBindingMismatch(id) => write!(
                formatter,
                "context-alias frame binding `{id}` is absent or has the wrong sort"
            ),
            Self::ContextAliasVariableClosure => {
                formatter.write_str("context-alias declarations differ from term and frame uses")
            }
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

impl Error for SemanticValidationError {}

fn validate_item_kind(
    id: &StableItemId,
    expected: ItemKind,
) -> Result<(), SemanticValidationError> {
    crate::ir_validation::expect_kind::<SemanticLevel>(id, id.item_kind(), expected)
}

fn insert_unique<T: Ord>(
    set: &mut BTreeSet<T>,
    value: T,
    kind: krs_ir::SemanticIdentityKind,
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

fn insert_declaration(
    map: &mut BTreeMap<StableItemId, ItemKind>,
    id: &StableItemId,
) -> Result<(), SemanticValidationError> {
    if map.insert(id.clone(), id.item_kind()).is_some() {
        return Err(SemanticValidationError::DuplicateId {
            kind: krs_ir::SemanticIdentityKind::Declaration,
            id: id.to_string(),
        });
    }
    Ok(())
}

fn insert_semantic_id(
    set: &mut BTreeSet<SemanticId>,
    id: &SemanticId,
    kind: krs_ir::SemanticIdentityKind,
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir_validation::{validate_claim, variable_scope};
    use krs_ir::ClaimModality;
    use krs_ir::{CellContentFrame, CellPost, FixedCellClause};

    fn node(key: &str) -> NodeOrigin {
        krs_ir::testing::origin_in(
            key,
            krs_ir::testing::package("ORG-EXAMPLE-CLAIM", "claim"),
            "src/lib.rs",
            krs_ir::testing::digest_with("a".repeat(64)),
            0,
            1,
        )
    }

    fn sid(value: &str) -> SemanticId {
        SemanticId::new(value).expect("valid semantic ID")
    }

    fn claim_id() -> StableItemId {
        StableItemId::new(
            krs_ir::testing::package("ORG-EXAMPLE-CLAIM", "claim"),
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
            label: Some(
                SemanticRuleLabel::new(node("label"), "reachability").expect("valid label"),
            ),
            requires: None,
            priority: None,
            simplification: None,
            nondet_group: None,
            anywhere: None,
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
            content: crate::ir_level::RuleContent::Configuration {
                kind: krs_ir::ConfigurationSentenceKind::Claim,
                body,
            },
        }
    }

    #[test]
    fn configuration_rule_round_trip_retains_refined_sentence_kind() {
        for expected in [
            krs_ir::ConfigurationSentenceKind::Transition,
            krs_ir::ConfigurationSentenceKind::Equation,
            krs_ir::ConfigurationSentenceKind::Claim,
        ] {
            let mut rule = claim_rule(int_token("before"), int_token("after"));
            let crate::ir_level::RuleContent::Configuration { kind, .. } = &mut rule.content else {
                panic!("fixture requires a configuration body")
            };
            *kind = expected;
            let json = serde_json::to_value(&rule).unwrap();
            assert_eq!(json["kind"], serde_json::to_value(expected).unwrap());
            assert!(json["body"].get("kind").is_none());
            let decoded: SemanticRule = serde_json::from_value(json).unwrap();
            assert_eq!(decoded, rule);
            assert!(matches!(
                decoded.relational_body(),
                crate::RuleBodyRef::Configuration { kind, .. } if kind == expected
            ));
        }
    }

    #[test]
    fn configuration_rule_boundary_rejects_alias_and_simplification() {
        let rule = claim_rule(int_token("before"), int_token("after"));
        let crate::RuleBodyRef::Configuration { body, .. } = rule.relational_body() else {
            panic!("claim fixture requires a configuration body")
        };
        for (kind, expected) in [
            (
                SentenceKind::Alias,
                SemanticValidationError::InvalidAliasRoot(Box::new(rule.id().clone())),
            ),
            (
                SentenceKind::Simplification,
                SemanticValidationError::InvalidSimplificationRoot(Box::new(rule.id().clone())),
            ),
        ] {
            assert_eq!(
                SemanticRule::new_configuration(
                    rule.origin().clone(),
                    rule.id().clone(),
                    kind,
                    vec![],
                    body.clone(),
                )
                .unwrap_err(),
                expected
            );
            let mut json = serde_json::to_value(&rule).unwrap();
            json["kind"] = serde_json::to_value(kind).unwrap();
            assert!(
                serde_json::from_value::<SemanticRule>(json)
                    .unwrap_err()
                    .to_string()
                    .contains(&expected.to_string())
            );
        }
    }

    fn validate_claim_only(rule: &SemanticRule) -> Result<(), SemanticValidationError> {
        let scope = variable_scope::<SemanticLevel>(&rule.variables, &BTreeMap::new())?;
        validate_claim::<SemanticLevel>(
            rule,
            rule.claim.as_ref().expect("claim metadata"),
            &scope,
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeSet::new(),
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
        if let crate::ir_level::RuleContent::Configuration { kind, .. } = &mut rule.content {
            *kind = krs_ir::ConfigurationSentenceKind::Transition;
        }
        assert!(matches!(
            validate_rule::<SemanticLevel>(
                &rule,
                None,
                &BTreeMap::new(),
                &BTreeMap::new(),
                &BTreeSet::new(),
                &BTreeSet::new(),
                &BTreeMap::new(),
                &BTreeSet::new(),
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
            validate_rule::<SemanticLevel>(
                &rule,
                None,
                &BTreeMap::new(),
                &BTreeMap::new(),
                &BTreeSet::new(),
                &BTreeSet::new(),
                &BTreeMap::new(),
                &BTreeSet::new(),
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
            validate_rule::<SemanticLevel>(
                &rule,
                None,
                &BTreeMap::new(),
                &BTreeMap::new(),
                &BTreeSet::new(),
                &BTreeSet::new(),
                &BTreeMap::new(),
                &BTreeSet::new(),
                &mut BTreeSet::new(),
            ),
            Err(SemanticValidationError::ClaimLabelRequired(_))
        ));
    }

    #[test]
    fn semantic_claim_requires_configuration_body() {
        let mut rule = claim_rule(int_token("before"), int_variable("after", "exists"));
        rule.content = crate::ir_level::RuleContent::Term {
            kind: SentenceKind::Claim,
            body: SemanticTerm::rewrite(
                node("term-rewrite"),
                SemanticSortRef::Builtin(BuiltinSort::Int),
                int_token("term-before"),
                int_variable("term-after", "exists"),
            )
            .expect("valid rewrite")
            .try_into()
            .unwrap(),
        };
        assert!(matches!(
            validate_rule::<SemanticLevel>(
                &rule,
                None,
                &BTreeMap::new(),
                &BTreeMap::new(),
                &BTreeSet::new(),
                &BTreeSet::new(),
                &BTreeMap::new(),
                &BTreeSet::new(),
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
            validate_rule::<SemanticLevel>(
                &rule,
                None,
                &BTreeMap::new(),
                &BTreeMap::new(),
                &BTreeSet::new(),
                &BTreeSet::new(),
                &BTreeMap::new(),
                &BTreeSet::new(),
                &mut BTreeSet::new(),
            ),
            Err(SemanticValidationError::InvalidClaimMetadata(_))
        ));
    }
}
