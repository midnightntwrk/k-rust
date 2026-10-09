//! Target-neutral, source-level K Definition IR.
//!
//! Generated K symbol and label names are declared exactly once here. Terms
//! refer to stable IDs, so neither the textual emitter nor a native frontend
//! adapter can independently invent identities or attach adapter metadata.

use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt;

use serde::{Deserialize, Deserializer, Serialize};

use crate::ir_level::DefinitionLevel;
use crate::ir_validation::{
    collect_configuration_nodes, insert_node, require_kind, require_sort, validate_context_alias,
    validate_context_alias_frames, validate_fixed_configuration, validate_precedence_order,
    validate_production_shape, validate_rule, validate_subsort_order,
};
use krs_ir::ir::validated_id;
use krs_ir::sorted::{SortKey, SortedByKey};
use krs_ir::{
    ApplicationRef, BuiltinOperation, BuiltinSort, GrammarProductionItem,
    GrammarProductionItemKind, GroupAssociativitySentence, HookOperation, IrIdentityError,
    ItemKind, ListOperation, MapOperation, ModuleId, NodeOrigin, PrecedenceRelation,
    ProductionAttribute, ProductionGroupId, SchemaVersion, SemanticId, SentenceKind, SetOperation,
    SourceMapKey, StableItemId,
};
use krs_ir::{FixedConfiguration, FixedConfigurationRewrite};

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
pub type DefinitionApplicationRef = ApplicationRef<SymbolId, DefinitionSortRef>;

/// Definition grammar item carrying typed sort references.
pub type ProductionItem = GrammarProductionItem<DefinitionSortRef>;

/// Classified Definition production metadata.
pub type DefinitionProductionAttribute = ProductionAttribute<DefinitionSortRef, SymbolId>;

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
        validated_id(krs_ir::IrIdentityKind::SymbolId, value.into()).map(Self)
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
        validated_id(krs_ir::IrIdentityKind::LabelId, value.into()).map(Self)
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
                krs_ir::IrField::SymbolName,
            ));
        }
        if emitted_name.contains(['/', '\\']) {
            return Err(DefinitionValidationError::AdapterSpecificValue(
                krs_ir::IrField::SymbolName,
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
                krs_ir::IrField::LabelName,
            ));
        }
        if emitted_name.contains(['/', '\\']) {
            return Err(DefinitionValidationError::AdapterSpecificValue(
                krs_ir::IrField::LabelName,
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
        krs_ir::testing::permute(&mut modules, seed);
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
    /// Returns the main module's program-syntax module `<MAIN>-SYNTAX`, which
    /// both K and k-rust select by default to parse programs.
    #[must_use]
    pub fn syntax_module(&self) -> Option<&DefinitionModule> {
        let name = format!("{}-SYNTAX", self.main_module.as_str());
        self.modules
            .iter()
            .find(|module| module.role == ModuleRole::ProgramSyntax && module.id.as_str() == name)
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

    #[expect(
        clippy::too_many_lines,
        reason = "One ordered pass checks whole-definition identities, references, and sentence invariants."
    )]
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
        let mut desugar_productions = BTreeSet::new();
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
                        if sentence.attributes.iter().any(|attribute| {
                            matches!(attribute, ProductionAttribute::Desugar { .. })
                        }) {
                            desugar_productions.insert(sentence.symbol.id.clone());
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
                    DefinitionSentence::Precedence(_)
                    | DefinitionSentence::Associativity(_)
                    | DefinitionSentence::Lexical(_)
                    | DefinitionSentence::Layout(_)
                    | DefinitionSentence::Raw(_) => {}
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
                                krs_ir::IrField::ContextAliasIdentity,
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
                    DefinitionSentence::Lexical(_) | DefinitionSentence::Layout(_) => {}
                    DefinitionSentence::Raw(sentence) => {
                        if sentence.text.trim().is_empty() {
                            return Err(DefinitionValidationError::EmptyText(
                                krs_ir::IrField::RawSentenceText,
                            ));
                        }
                    }
                    DefinitionSentence::Configuration(sentence) => {
                        validate_fixed_configuration::<DefinitionLevel>(
                            sentence,
                            &symbols,
                            &production_signatures,
                            &subsort_parents,
                            &BTreeSet::new(),
                            &mut nodes,
                        )?;
                    }
                    DefinitionSentence::ContextAlias(sentence) => {
                        validate_context_alias::<DefinitionLevel>(
                            sentence,
                            &symbols,
                            &production_signatures,
                            &subsort_parents,
                            &BTreeSet::new(),
                            &mut nodes,
                        )?;
                    }
                    DefinitionSentence::Rule(sentence) => {
                        validate_rule::<DefinitionLevel>(
                            sentence,
                            fixed_configuration,
                            &symbols,
                            &production_signatures,
                            &functional_productions,
                            &alias_productions,
                            &desugar_productions,
                            &subsort_parents,
                            &BTreeSet::new(),
                            &mut nodes,
                        )?;
                    }
                }
            }
        }
        validate_hook_point_constructors(&self.modules)?;
        validate_precedence_order::<DefinitionLevel>(&self.modules)?;
        validate_subsort_order::<DefinitionLevel>(&subsort_parents)?;
        for module in &self.modules {
            for sentence in &module.sentences {
                if let DefinitionSentence::ContextAlias(alias) = sentence {
                    validate_context_alias_frames::<DefinitionLevel>(
                        alias,
                        fixed_configuration,
                        &symbols,
                    )?;
                }
            }
        }
        Ok(())
    }
}

#[cfg(feature = "test-support")]
impl krs_ir::testing::CanonicalContract for DefinitionIr {
    fn permute_sets(&self, seed: u64) -> Self {
        Self::permute_sets(self, seed)
    }

    fn to_canonical_json(&self) -> serde_json::Result<String> {
        Self::to_canonical_json(self)
    }
}

/// What a generated module is for. Each package emits a program-syntax module
/// `<NS>-SYNTAX` and a semantics module `<NS>` that imports it.
#[derive(
    Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize,
)]
#[serde(rename_all = "snake_case")]
pub enum ModuleRole {
    /// The grammar programs may use: K's default syntax module of the main
    /// module. Builtin sorts are imported only through their `-SYNTAX` modules.
    ProgramSyntax,
    /// Everything rules may use, the configuration, and the rules.
    #[default]
    Semantics,
    /// An author spec module (KF-041): a K proof module emitted into `spec.k`,
    /// outside the definition's import closure, holding claims,
    /// simplification lemmas, and terminal tokens for existing sorts.
    Spec,
}

impl ModuleRole {
    #[expect(
        clippy::trivially_copy_pass_by_ref,
        reason = "serde's skip_serializing_if passes the field by reference."
    )]
    fn is_semantics(&self) -> bool {
        *self == Self::Semantics
    }
}

#[expect(
    clippy::trivially_copy_pass_by_ref,
    reason = "serde's skip_serializing_if passes the field by reference."
)]
fn is_signed(value: &krs_ir::IntLiterals) -> bool {
    *value == krs_ir::IntLiterals::Signed
}

/// One generated K module.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DefinitionModule {
    origin: NodeOrigin,
    id: ModuleId,
    #[serde(default, skip_serializing_if = "ModuleRole::is_semantics")]
    role: ModuleRole,
    #[serde(default, skip_serializing_if = "is_signed")]
    int_literals: krs_ir::IntLiterals,
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
            role: ModuleRole::Semantics,
            int_literals: krs_ir::IntLiterals::Signed,
            imports: imports.into_iter().collect(),
            production_groups: SortedByKey::new(production_groups),
            sentences: SortedByKey::new(sentences),
        }
    }

    /// Rebuilds the module with every sentence replaced by `map(sentence)`.
    #[must_use]
    pub fn map_sentences(self, map: impl FnMut(DefinitionSentence) -> DefinitionSentence) -> Self {
        let sentences = self.sentences.iter().cloned().map(map).collect();
        Self {
            sentences: SortedByKey::new(sentences),
            ..self
        }
    }

    /// Marks this module as a package's program-syntax module, whose integer
    /// literals come from the package's `int-literals` setting.
    #[must_use]
    pub const fn into_program_syntax(mut self, int_literals: krs_ir::IntLiterals) -> Self {
        self.role = ModuleRole::ProgramSyntax;
        self.int_literals = int_literals;
        self
    }

    /// Marks this module as an author spec module (KF-041).
    #[must_use]
    pub const fn into_spec(mut self) -> Self {
        self.role = ModuleRole::Spec;
        self
    }

    /// Whether this is an author spec module (KF-041).
    #[must_use]
    pub const fn is_spec(&self) -> bool {
        matches!(self.role, ModuleRole::Spec)
    }

    /// Rebuilds every set-like module collection from permuted inputs.
    #[cfg(feature = "test-support")]
    #[must_use]
    pub fn permute_sets(&self, seed: u64) -> Self {
        let mut imports = self.imports.iter().cloned().collect::<Vec<_>>();
        let mut production_groups = self.production_groups.iter().cloned().collect::<Vec<_>>();
        let mut sentences = self.sentences.iter().cloned().collect::<Vec<_>>();
        krs_ir::testing::permute(&mut imports, seed);
        krs_ir::testing::permute(&mut production_groups, seed);
        krs_ir::testing::permute(&mut sentences, seed);
        let module = Self::new(
            self.origin.clone(),
            self.id.clone(),
            imports,
            production_groups,
            sentences,
        );
        match self.role {
            ModuleRole::ProgramSyntax => module.into_program_syntax(self.int_literals),
            ModuleRole::Semantics => module,
            ModuleRole::Spec => module.into_spec(),
        }
    }

    /// Returns what the module is for.
    #[must_use]
    pub const fn role(&self) -> ModuleRole {
        self.role
    }
    /// Returns the program-syntax integer literal setting (meaningful for a
    /// [`ModuleRole::ProgramSyntax`] module).
    #[must_use]
    pub const fn int_literals(&self) -> krs_ir::IntLiterals {
        self.int_literals
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
#[expect(
    clippy::large_enum_variant,
    reason = "Boxing only the largest sentence would change the public construction API without reducing any serialized payload."
)]
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
    /// Named regex fragment, `syntax lexical Name = r".."`.
    Lexical(krs_ir::LexicalSentence),
    /// Layout regex, `syntax #Layout ::= r".." [token]`.
    Layout(krs_ir::LayoutSentence),
    /// One `k::raw_k!` sentence, printed verbatim in the package's
    /// semantics module and parsed by K with that module's grammar.
    Raw(krs_ir::RawSentence),
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
            Self::Lexical(value) => value.origin(),
            Self::Layout(value) => value.origin(),
            Self::Raw(value) => &value.origin,
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
                krs_ir::IrField::ProductionGroupName,
            ));
        }
        if emitted_name.contains(['/', '\\']) {
            return Err(DefinitionValidationError::AdapterSpecificValue(
                krs_ir::IrField::ProductionGroupName,
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
pub type DefinitionScopedBinder = crate::IrScopedBinder<crate::DefinitionLevel>;

/// Typed reachability metadata present only on claims.
pub type DefinitionClaim = crate::IrClaim<crate::DefinitionLevel>;

/// One explicit equation or transition-rule priority.
pub type DefinitionRulePriority = crate::IrRulePriority;

/// Simplifier classification and optional ordering hint.
pub type DefinitionSimplification = crate::IrSimplification;

/// One numeric simplification ordering hint.
pub type DefinitionSimplificationPriority = crate::IrSimplificationPriority;

/// Rule, equation, or claim sentence.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Deserialize)]
#[serde(
    deny_unknown_fields,
    try_from = "RuleSentenceWire<'static, crate::ir_level::RuleBodyWire<DefinitionLevel>>"
)]
pub struct RuleSentence {
    origin: NodeOrigin,
    label: LabelIdentity,
    variables: Vec<DefinitionVariable>,
    requires: Option<DefinitionRuleCondition>,
    priority: Option<DefinitionRulePriority>,
    simplification: Option<DefinitionSimplification>,
    claim: Option<DefinitionClaim>,
    anywhere: Option<NodeOrigin>,
    existentials: Vec<DefinitionScopedBinder>,
    ensures: Option<DefinitionRuleCondition>,
    fresh: Vec<DefinitionScopedBinder>,
    restriction: Option<crate::IrMatchRestriction>,
    unbound_variables: Option<crate::IrUnboundVariables>,
    content: crate::ir_level::RuleContent<crate::DefinitionLevel>,
}

impl Serialize for RuleSentence {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        RuleSentenceWire {
            origin: Cow::Borrowed(&self.origin),
            label: Cow::Borrowed(&self.label),
            kind: self.kind(),
            variables: Cow::Borrowed(&self.variables),
            requires: self.requires.as_ref().map(Cow::Borrowed),
            priority: self.priority.as_ref().map(Cow::Borrowed),
            simplification: self.simplification.as_ref().map(Cow::Borrowed),
            claim: self.claim.as_ref().map(Cow::Borrowed),
            anywhere: self.anywhere.as_ref().map(Cow::Borrowed),
            existentials: Cow::Borrowed(&self.existentials),
            ensures: self.ensures.as_ref().map(Cow::Borrowed),
            fresh: Cow::Borrowed(&self.fresh),
            restriction: self.restriction.as_ref().map(Cow::Borrowed),
            unbound_variables: self.unbound_variables.as_ref().map(Cow::Borrowed),
            body: self.relational_body(),
        }
        .serialize(serializer)
    }
}

#[derive(Serialize, Deserialize)]
#[serde(rename = "RuleSentence", deny_unknown_fields)]
struct RuleSentenceWire<'a, B> {
    origin: Cow<'a, NodeOrigin>,
    label: Cow<'a, LabelIdentity>,
    kind: SentenceKind,
    variables: Cow<'a, [DefinitionVariable]>,
    #[serde(skip_serializing_if = "Option::is_none")]
    requires: Option<Cow<'a, DefinitionRuleCondition>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    priority: Option<Cow<'a, DefinitionRulePriority>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    simplification: Option<Cow<'a, DefinitionSimplification>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    claim: Option<Cow<'a, DefinitionClaim>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    anywhere: Option<Cow<'a, NodeOrigin>>,
    #[serde(default, skip_serializing_if = "crate::ir_level::is_empty_slice")]
    existentials: Cow<'a, [DefinitionScopedBinder]>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    ensures: Option<Cow<'a, DefinitionRuleCondition>>,
    #[serde(default, skip_serializing_if = "crate::ir_level::is_empty_slice")]
    fresh: Cow<'a, [DefinitionScopedBinder]>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    restriction: Option<Cow<'a, crate::IrMatchRestriction>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    unbound_variables: Option<Cow<'a, crate::IrUnboundVariables>>,
    body: B,
}

impl TryFrom<RuleSentenceWire<'static, crate::ir_level::RuleBodyWire<DefinitionLevel>>>
    for RuleSentence
{
    type Error = DefinitionValidationError;
    fn try_from(
        value: RuleSentenceWire<'static, crate::ir_level::RuleBodyWire<DefinitionLevel>>,
    ) -> Result<Self, Self::Error> {
        let content = value.body.refine(value.kind).map_err(|error| match error {
            crate::ir_level::RuleBodyRefinementError::NotRewrite => {
                DefinitionValidationError::RuleBodyNotRewrite(value.label.id.clone())
            }
            crate::ir_level::RuleBodyRefinementError::InvalidConfigurationKind => {
                if matches!(value.kind, SentenceKind::Alias | SentenceKind::Desugar) {
                    DefinitionValidationError::InvalidAliasRoot(value.label.id.clone())
                } else {
                    DefinitionValidationError::InvalidSimplificationRoot(value.label.id.clone())
                }
            }
        })?;
        Ok(Self {
            origin: value.origin.into_owned(),
            label: value.label.into_owned(),
            variables: value.variables.into_owned(),
            requires: value.requires.map(Cow::into_owned),
            priority: value.priority.map(Cow::into_owned),
            simplification: value.simplification.map(Cow::into_owned),
            claim: value.claim.map(Cow::into_owned),
            anywhere: value.anywhere.map(Cow::into_owned),
            existentials: value.existentials.into_owned(),
            ensures: value.ensures.map(Cow::into_owned),
            fresh: value.fresh.into_owned(),
            restriction: value.restriction.map(Cow::into_owned),
            unbound_variables: value.unbound_variables.map(Cow::into_owned),
            content,
        })
    }
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
        let body = body
            .try_into()
            .map_err(|_| DefinitionValidationError::RuleBodyNotRewrite(label.id.clone()))?;
        Ok(Self {
            origin,
            label,
            variables,
            requires: None,
            priority: None,
            simplification: None,
            claim: None,
            anywhere: None,
            existentials: Vec::new(),
            ensures: None,
            fresh: Vec::new(),
            restriction: None,
            unbound_variables: None,
            content: crate::ir_level::RuleContent::Term { kind, body },
        })
    }
    /// Creates an ordinary labeled simultaneous fixed-configuration rule.
    #[must_use]
    pub fn new_configuration(
        origin: NodeOrigin,
        label: LabelIdentity,
        kind: krs_ir::ConfigurationSentenceKind,
        variables: Vec<DefinitionVariable>,
        body: FixedConfigurationRewrite<SymbolId, DefinitionTerm>,
    ) -> Self {
        Self {
            origin,
            label,
            variables,
            requires: None,
            priority: None,
            simplification: None,
            claim: None,
            anywhere: None,
            existentials: Vec::new(),
            ensures: None,
            fresh: Vec::new(),
            restriction: None,
            unbound_variables: None,
            content: crate::ir_level::RuleContent::Configuration { kind, body },
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
        self.content.kind()
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
            && !matches!(
                self.kind(),
                SentenceKind::Equation | SentenceKind::Transition
            )
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
    /// Marks a term-shaped transition as an anywhere rule (`[anywhere]` in K).
    ///
    /// # Errors
    ///
    /// Returns [`DefinitionValidationError::InvalidRulePriority`] when the
    /// marker is attached to anything but a term-shaped transition without a
    /// priority, since an anywhere rule is outside rule priority.
    pub fn with_anywhere(
        mut self,
        origin: Option<NodeOrigin>,
    ) -> Result<Self, DefinitionValidationError> {
        if origin.is_some()
            && (self.kind() != SentenceKind::Transition
                || self.priority.is_some()
                || matches!(
                    self.relational_body(),
                    crate::RuleBodyRef::Configuration { .. }
                ))
        {
            return Err(DefinitionValidationError::InvalidRulePriority(
                self.label.id.clone(),
            ));
        }
        self.anywhere = origin;
        Ok(self)
    }
    /// Returns the `anywhere` marker provenance of an anywhere rule.
    #[must_use]
    pub const fn anywhere(&self) -> Option<&NodeOrigin> {
        self.anywhere.as_ref()
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
    /// Attaches result-scoped existential binders (`#[k::exists]`) of a transition or claim.
    #[must_use]
    pub fn with_existentials(mut self, existentials: Vec<DefinitionScopedBinder>) -> Self {
        self.existentials = existentials;
        self
    }
    /// Returns the result-scoped existential binders.
    #[must_use]
    pub fn existentials(&self) -> &[DefinitionScopedBinder] {
        &self.existentials
    }
    /// Attaches the fresh binders (`#[k::fresh]`, K's `!X`) of a transition.
    #[must_use]
    pub fn with_fresh(mut self, fresh: Vec<DefinitionScopedBinder>) -> Self {
        self.fresh = fresh;
        self
    }
    /// Returns the fresh binders.
    #[must_use]
    pub fn fresh(&self) -> &[DefinitionScopedBinder] {
        &self.fresh
    }
    /// Attaches the `concrete`, `symbolic`, and `smt_lemma` keys of an equation or simplification.
    #[must_use]
    pub fn with_restriction(mut self, restriction: Option<crate::IrMatchRestriction>) -> Self {
        self.restriction = restriction;
        self
    }
    /// Returns the `concrete`, `symbolic`, and `smt_lemma` keys.
    #[must_use]
    pub const fn restriction(&self) -> Option<&crate::IrMatchRestriction> {
        self.restriction.as_ref()
    }
    /// Attaches `unbound_variables = [..]` of a desugar clause (KF-046).
    #[must_use]
    pub fn with_unbound_variables(
        mut self,
        unbound_variables: Option<crate::IrUnboundVariables>,
    ) -> Self {
        self.unbound_variables = unbound_variables;
        self
    }
    /// Returns `unbound_variables = [..]` of a desugar clause.
    #[must_use]
    pub const fn unbound_variables(&self) -> Option<&crate::IrUnboundVariables> {
        self.unbound_variables.as_ref()
    }
    /// The wildcards of a term rule's right-hand side, which a desugar
    /// clause's `_` entry of `unbound_variables` stands for (KF-046).
    #[must_use]
    pub fn result_wildcards(&self) -> std::collections::BTreeSet<SemanticId> {
        let mut variables = std::collections::BTreeSet::new();
        if let Some(body) = self.body() {
            crate::ir_validation::collect_term_variables::<crate::DefinitionLevel>(
                body.to(),
                &mut variables,
            );
        }
        variables.retain(|id| id.kind() == krs_ir::SemanticIdKind::Wildcard);
        variables
    }
    /// Attaches the object-Bool postcondition (`#[k::ensures]`) of a transition or claim.
    #[must_use]
    pub fn with_ensures(mut self, ensures: Option<DefinitionRuleCondition>) -> Self {
        self.ensures = ensures;
        self
    }
    /// Returns the object-Bool postcondition.
    #[must_use]
    pub const fn ensures(&self) -> Option<&DefinitionRuleCondition> {
        self.ensures.as_ref()
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
    /// Borrows the term rewrite body, when present.
    #[must_use]
    pub fn body(&self) -> Option<&crate::IrRewrite<crate::DefinitionLevel>> {
        match &self.content {
            crate::ir_level::RuleContent::Term { body, .. } => Some(body),
            crate::ir_level::RuleContent::Configuration { .. } => None,
        }
    }
    /// Returns the typed relational body.
    #[must_use]
    pub const fn relational_body(
        &self,
    ) -> crate::ir_level::RuleBodyRef<'_, crate::DefinitionLevel> {
        self.content.body()
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
    EmptyText(krs_ir::IrField),
    /// A path-shaped or adapter-shaped value attempted to cross the boundary.
    AdapterSpecificValue(krs_ir::IrField),
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
    DuplicateProductionAttribute(krs_ir::ProductionAttributeFamily),
    /// Token metadata was attached to a non-regex production.
    InvalidTokenProduction,
    /// A regex terminal lacked token metadata.
    RegexWithoutToken,
    /// Strictness named no field or an unknown/repeated field.
    InvalidStrictnessField,
    /// Format metadata was empty or referenced a nonexistent item.
    InvalidFormat,
    /// An `smtlib` symbol was not an SMT-LIB simple symbol, or an `smt_hook`
    /// template was empty or named a field the production does not have.
    InvalidSmtMetadata,
    /// Colour metadata was invalid: an empty colour or one containing `,` or
    /// `)`, a `colors` list whose length is not the terminal count plus the
    /// number of `%c`, or `%c`/`%r` without a colour.
    InvalidColors,
    /// A production was marked both `internal` and `program`.
    InternalWithProgram,
    /// A production was marked both `prefer` and `avoid`.
    PreferAndAvoid,
    /// A production was marked both `alias` and `desugar` (KF-028).
    AliasWithDesugar,
    /// A token or bracket production was marked `prefer`.
    PreferOnParseOnlyProduction,
    /// A function, token, or bracket production carried `overload`.
    InvalidOverloadProduction,
    /// A syntactic-list cons or terminator production had the wrong items or
    /// metadata (KF-020).
    InvalidListProduction,
    /// A production kept `internal` or `program`, which lowering consumes when
    /// it places productions in the program-syntax or semantics module.
    SemanticOnlyProductionAttribute(SymbolId),
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
        expected_signature: krs_ir::Bn128PointSignature,
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
    /// A generated sort predicate or projection has the wrong signature.
    GeneratedApplicationSignature,
    /// Rewrite endpoint sorts differ.
    RewriteSortMismatch,
    /// `alias @ pattern` (#as) outside a pre-pattern, or at a sort its alias
    /// variable does not have or its pattern does not inject into.
    InvalidPatternAs,
    /// `A | B` (#Or) outside a pre-pattern, at a sort an alternative does
    /// not inject into, or with alternatives binding different variables.
    InvalidPatternOr,
    /// `k::matches!` (:=K) outside a post-term or condition, at a sort
    /// other than Bool, or with local binders that are not exactly its
    /// pattern's named variables or that occur outside it.
    InvalidMatches,
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
    /// An existential binder occurs in the sentence's left-hand side or `requires` condition.
    ExistentialScopeViolation(SemanticId),
    /// An existential binder is unused in the sentence's right-hand side and `ensures` condition.
    UnusedExistential(SemanticId),
    /// Existential binders or an `ensures` condition occurred on a sentence other than a transition or claim.
    InvalidRuleExistentials(LabelId),
    /// Fresh binders occurred on a sentence other than a transition, or on an anywhere rule.
    InvalidRuleFresh(LabelId),
    /// `concrete`, `symbolic`, or `smt_lemma` occurred on a sentence other than an equation
    /// or simplification, or named a binder that is not a left-hand variable.
    InvalidMatchRestriction(LabelId),
    /// `unbound_variables` occurred on a sentence other than a term-shaped desugar clause,
    /// or listed a variable the left-hand side binds or the right-hand side does not use.
    InvalidUnboundVariables(LabelId),
    /// A fresh binder occurs in the sentence's left-hand side or `requires` condition, or nowhere on its right.
    FreshScopeViolation(SemanticId),
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
    /// A Map operation had a wrong result or operand sort.
    MapOperationSignature(MapOperation),
    /// A List operation had a wrong result or operand sort.
    ListOperationSignature(ListOperation),
    /// A Set operation had a wrong result or operand sort.
    SetOperationSignature(SetOperation),
    /// A configuration rule exists without a general fixed configuration.
    ConfigurationRuleWithoutFixedConfiguration(LabelId),
    /// A configuration rule names a different fixed configuration.
    ConfigurationRuleTargetMismatch(LabelId),
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

impl fmt::Display for DefinitionValidationError {
    #[expect(
        clippy::too_many_lines,
        reason = "Exhaustive formatting keeps each definition validation message with its variant."
    )]
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
                "token metadata requires exactly one regex or terminal item, and `prec` a regex",
            ),
            Self::RegexWithoutToken => {
                formatter.write_str("regex grammar items require classified token metadata")
            }
            Self::InvalidStrictnessField => formatter
                .write_str("strictness fields must be nonempty, distinct named nonterminals"),
            Self::InvalidFormat => formatter.write_str(
                "format metadata must be nonempty and reference existing production items",
            ),
            Self::InvalidSmtMetadata => formatter.write_str(
                "an smtlib symbol must be an SMT-LIB simple symbol, and an smt-hook template must be nonempty and name only nonterminal fields",
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
            Self::AliasWithDesugar => {
                formatter.write_str("a production is an alias or a desugar, not both")
            }
            Self::InvalidOverloadProduction => formatter.write_str(
                "`overload` relates constructor productions; a function, token, or bracket production cannot carry it",
            ),
            Self::InvalidListProduction => formatter.write_str(
                "a syntactic-list cons production has items `[head, separator?, tail]` with the tail of its own sort, and its terminator has the single terminal `.Sort`; neither is a function, token, bracket, or alias",
            ),
            Self::PreferOnParseOnlyProduction => {
                formatter.write_str("`prefer` applies only to constructor and function productions, not to token or bracket productions")
            }
            Self::SemanticOnlyProductionAttribute(id) => write!(
                formatter,
                "production {id} keeps `internal` or `program` metadata, which lowering consumes"
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
            Self::GeneratedApplicationSignature => formatter.write_str(
                "a sort predicate takes one argument and has sort Bool; a sort projection takes one argument and has its target sort",
            ),
            Self::RewriteSortMismatch => {
                formatter.write_str("rewrite endpoint sorts must equal the rewrite sort")
            }
            Self::InvalidPatternAs => formatter.write_str(
                "`alias @ pattern` (#as) occurs only in pre-patterns, at its alias variable's sort, which its pattern's sort must inject into",
            ),
            Self::InvalidPatternOr => formatter.write_str(
                "`A | B` (#Or) occurs only in pre-patterns, at a sort every alternative injects into, and every alternative binds the same variables",
            ),
            Self::InvalidMatches => formatter.write_str(
                "`k::matches!` (:=K) occurs only in post-terms and conditions, at sort Bool, and its local binders are exactly its pattern's named variables, each bound by one pattern and used nowhere else",
            ),
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
                "alias or desugar clause {id} must be headed by a production with the same mode, `alias` or `desugar`"
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
                "existential binder {id} cannot occur in the left-hand side or requires condition"
            ),
            Self::UnusedExistential(id) => write!(
                formatter,
                "existential binder {id} must occur in the right-hand side or ensures condition"
            ),
            Self::InvalidRuleExistentials(id) => write!(
                formatter,
                "existential results and ensures are allowed only on claims and transition rules, not on {id}"
            ),
            Self::InvalidRuleFresh(id) => write!(
                formatter,
                "fresh binders are allowed only on transition rules that are not anywhere rules, not on {id}"
            ),
            Self::InvalidMatchRestriction(id) => write!(
                formatter,
                "concrete, symbolic, and smt_lemma are allowed only on equations and simplifications, naming left-hand binders, not on {id}"
            ),
            Self::InvalidUnboundVariables(id) => write!(
                formatter,
                "unbound_variables is allowed only on desugar clauses, naming right-hand variables the left-hand side does not bind, not on {id}"
            ),
            Self::FreshScopeViolation(id) => write!(
                formatter,
                "fresh binder {id} must occur in the right-hand side or ensures condition, and never in the left-hand side or requires condition"
            ),
            Self::RuleConditionSortMismatch => {
                formatter.write_str("rule condition must have builtin Bool sort")
            }
            Self::AliasCondition => {
                formatter.write_str("static alias and desugar clauses cannot carry requires conditions")
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
            krs_ir::IrField::SymbolName,
        ));
    }
    if symbol.emitted_name.contains(['/', '\\']) {
        return Err(DefinitionValidationError::AdapterSpecificValue(
            krs_ir::IrField::SymbolName,
        ));
    }
    Ok(())
}

fn validate_label_text(label: &LabelIdentity) -> Result<(), DefinitionValidationError> {
    if label.emitted_name.trim().is_empty() {
        return Err(DefinitionValidationError::EmptyText(
            krs_ir::IrField::LabelName,
        ));
    }
    if label.emitted_name.contains(['/', '\\']) {
        return Err(DefinitionValidationError::AdapterSpecificValue(
            krs_ir::IrField::LabelName,
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
                        krs_ir::IrField::StrictnessContextAliasReference,
                    ));
                }
            }
            ProductionAttribute::Documentation { .. }
            | ProductionAttribute::Function { .. }
            | ProductionAttribute::Total { .. }
            | ProductionAttribute::Hook { .. }
            | ProductionAttribute::Alias { .. }
            | ProductionAttribute::Desugar { .. }
            | ProductionAttribute::Token { .. }
            | ProductionAttribute::Bracket { .. }
            | ProductionAttribute::Avoid { .. }
            | ProductionAttribute::Format { .. }
            | ProductionAttribute::Color { .. }
            | ProductionAttribute::Colors { .. }
            | ProductionAttribute::Prefer { .. }
            | ProductionAttribute::Private { .. }
            | ProductionAttribute::Memo { .. }
            | ProductionAttribute::FreshGenerator { .. }
            | ProductionAttribute::Smtlib { .. }
            | ProductionAttribute::SmtHook { .. }
            | ProductionAttribute::RawHook { .. } => {}
            ProductionAttribute::Overload { target, .. }
            | ProductionAttribute::ListCons {
                terminator: target, ..
            }
            | ProductionAttribute::ListTerminator { cons: target, .. } => {
                require_kind::<DefinitionLevel>(symbols, target, SymbolKind::Production)?;
            }
            ProductionAttribute::Internal { .. } | ProductionAttribute::Program { .. } => {
                return Err(DefinitionValidationError::SemanticOnlyProductionAttribute(
                    sentence.symbol.id.clone(),
                ));
            }
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
        .collect();
    let productions = modules
        .iter()
        .flat_map(|module| &module.sentences)
        .filter_map(|sentence| match sentence {
            DefinitionSentence::Production(production) => {
                Some(crate::ir_validation::ProductionView {
                    result_sort: production.result_sort(),
                    items: production.items(),
                    attributes: production.attributes(),
                })
            }
            _ => None,
        });
    crate::ir_validation::validate_hook_point_constructors::<DefinitionLevel>(&sorts, productions)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir_validation::{validate_claim, validate_existentials, variable_scope};
    use krs_ir::CellContentFrame;
    use krs_ir::ClaimModality;
    use krs_ir::{CellPost, FixedCellClause};

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
        krs_ir::testing::origin_in(
            key,
            krs_ir::testing::package("ORG-EXAMPLE-CLAIM", "claim"),
            "src/lib.rs",
            krs_ir::testing::digest_with("b".repeat(64)),
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
        let binder = DefinitionScopedBinder::new(
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
            variables: vec![DefinitionVariable::new(
                sid("exists"),
                DefinitionSortRef::Builtin(BuiltinSort::Int),
            )],
            requires: None,
            priority: None,
            simplification: None,
            anywhere: None,
            claim: Some(DefinitionClaim::new(
                node("modality"),
                ClaimModality::AllPaths,
                None,
                Vec::new(),
            )),
            existentials: vec![binder],
            ensures: None,
            fresh: Vec::new(),
            restriction: None,
            unbound_variables: None,
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
            let mut sentence = claim_sentence(int_token("before"), int_token("after"));
            let crate::ir_level::RuleContent::Configuration { kind, .. } = &mut sentence.content
            else {
                panic!("fixture requires a configuration body")
            };
            *kind = expected;
            let json = serde_json::to_value(&sentence).unwrap();
            assert_eq!(json["kind"], serde_json::to_value(expected).unwrap());
            assert!(json["body"].get("kind").is_none());
            let decoded: RuleSentence = serde_json::from_value(json).unwrap();
            assert_eq!(decoded, sentence);
            assert!(matches!(
                decoded.relational_body(),
                crate::RuleBodyRef::Configuration { kind, .. } if kind == expected
            ));
        }
    }

    #[test]
    fn configuration_rule_boundary_rejects_alias_and_simplification() {
        let sentence = claim_sentence(int_token("before"), int_token("after"));
        for (kind, expected) in [
            (
                SentenceKind::Alias,
                DefinitionValidationError::InvalidAliasRoot(sentence.label().id().clone()),
            ),
            (
                SentenceKind::Simplification,
                DefinitionValidationError::InvalidSimplificationRoot(sentence.label().id().clone()),
            ),
        ] {
            let mut json = serde_json::to_value(&sentence).unwrap();
            json["kind"] = serde_json::to_value(kind).unwrap();
            assert!(
                serde_json::from_value::<RuleSentence>(json)
                    .unwrap_err()
                    .to_string()
                    .contains(&expected.to_string())
            );
        }
    }

    fn validate_claim_only(sentence: &RuleSentence) -> Result<(), DefinitionValidationError> {
        let scope = variable_scope::<DefinitionLevel>(&sentence.variables, &BTreeMap::new())?;
        validate_claim::<DefinitionLevel>(
            sentence,
            sentence.claim.as_ref().expect("claim metadata"),
            &scope,
            &BTreeMap::new(),
            &mut BTreeSet::new(),
        )?;
        validate_existentials::<DefinitionLevel>(
            sentence,
            &scope,
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeSet::new(),
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
        sentence.ensures = Some(DefinitionRuleCondition::new(
            node("ensures"),
            int_token("post"),
        ));
        assert_eq!(
            validate_claim_only(&sentence),
            Err(DefinitionValidationError::RuleConditionSortMismatch)
        );

        let mut unbound = claim_sentence(
            int_token("unbound-before"),
            int_variable("unbound-after", "exists"),
        );
        unbound.existentials[0].id = sid("missing");
        assert_eq!(
            validate_claim_only(&unbound),
            Err(DefinitionValidationError::InvalidClaimBinder(sid(
                "missing"
            )))
        );
    }

    /// A transition (or `kind`) carrying the claim fixture's existential, without claim metadata.
    fn existential_sentence(
        before: DefinitionTerm,
        after: DefinitionTerm,
        kind: krs_ir::ConfigurationSentenceKind,
    ) -> RuleSentence {
        let mut sentence = claim_sentence(before, after);
        sentence.claim = None;
        if let crate::ir_level::RuleContent::Configuration { kind: current, .. } =
            &mut sentence.content
        {
            *current = kind;
        }
        sentence
    }

    fn validate_existentials_only(
        sentence: &RuleSentence,
    ) -> Result<(), DefinitionValidationError> {
        let scope = variable_scope::<DefinitionLevel>(&sentence.variables, &BTreeMap::new())?;
        validate_existentials::<DefinitionLevel>(
            sentence,
            &scope,
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeSet::new(),
            &mut BTreeSet::new(),
        )
    }

    #[test]
    fn definition_transition_existentials_are_result_scoped() {
        let transition = krs_ir::ConfigurationSentenceKind::Transition;
        let valid = existential_sentence(
            int_token("before"),
            int_variable("after", "exists"),
            transition,
        );
        assert_eq!(validate_existentials_only(&valid), Ok(()));
        let json = serde_json::to_value(&valid).unwrap();
        assert!(json.get("existentials").is_some());
        assert_eq!(serde_json::from_value::<RuleSentence>(json).unwrap(), valid);

        let left = existential_sentence(
            int_variable("before", "exists"),
            int_token("after"),
            transition,
        );
        assert_eq!(
            validate_existentials_only(&left),
            Err(DefinitionValidationError::ExistentialScopeViolation(sid(
                "exists"
            )))
        );
        let unused = existential_sentence(int_token("before"), int_token("after"), transition);
        assert_eq!(
            validate_existentials_only(&unused),
            Err(DefinitionValidationError::UnusedExistential(sid("exists")))
        );
        let equation = existential_sentence(
            int_token("before"),
            int_variable("after", "exists"),
            krs_ir::ConfigurationSentenceKind::Equation,
        );
        assert!(matches!(
            validate_existentials_only(&equation),
            Err(DefinitionValidationError::InvalidRuleExistentials(_))
        ));
    }

    /// The existential fixture with its binder moved to the fresh binders.
    fn fresh_sentence(
        before: DefinitionTerm,
        after: DefinitionTerm,
        kind: krs_ir::ConfigurationSentenceKind,
    ) -> RuleSentence {
        let mut sentence = existential_sentence(before, after, kind);
        sentence.fresh = std::mem::take(&mut sentence.existentials);
        sentence
    }

    #[test]
    fn definition_fresh_binders_are_result_scoped_transition_binders() {
        let transition = krs_ir::ConfigurationSentenceKind::Transition;
        let valid = fresh_sentence(
            int_token("before"),
            int_variable("after", "exists"),
            transition,
        );
        assert_eq!(validate_existentials_only(&valid), Ok(()));
        let json = serde_json::to_value(&valid).unwrap();
        assert!(json.get("fresh").is_some());
        assert!(json.get("existentials").is_none());
        assert_eq!(serde_json::from_value::<RuleSentence>(json).unwrap(), valid);

        let left = fresh_sentence(
            int_variable("before", "exists"),
            int_token("after"),
            transition,
        );
        assert_eq!(
            validate_existentials_only(&left),
            Err(DefinitionValidationError::FreshScopeViolation(sid(
                "exists"
            )))
        );
        let unused = fresh_sentence(int_token("before"), int_token("after"), transition);
        assert_eq!(
            validate_existentials_only(&unused),
            Err(DefinitionValidationError::FreshScopeViolation(sid(
                "exists"
            )))
        );
        let claim = fresh_sentence(
            int_token("before"),
            int_variable("after", "exists"),
            krs_ir::ConfigurationSentenceKind::Claim,
        );
        assert!(matches!(
            validate_existentials_only(&claim),
            Err(DefinitionValidationError::InvalidRuleFresh(_))
        ));
    }

    #[test]
    fn definition_claim_metadata_is_exclusive_to_claim_sentences() {
        let mut sentence = claim_sentence(int_token("before"), int_variable("after", "exists"));
        if let crate::ir_level::RuleContent::Configuration { kind, .. } = &mut sentence.content {
            *kind = krs_ir::ConfigurationSentenceKind::Transition;
        }
        assert!(matches!(
            validate_rule::<DefinitionLevel>(
                &sentence,
                None,
                &BTreeMap::new(),
                &BTreeMap::new(),
                &BTreeSet::new(),
                &BTreeSet::new(),
                &BTreeSet::new(),
                &BTreeMap::new(),
                &BTreeSet::new(),
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
                &BTreeSet::new(),
                &BTreeMap::new(),
                &BTreeSet::new(),
                &mut BTreeSet::new(),
            ),
            Err(DefinitionValidationError::InvalidClaimMetadata(_))
        ));
    }

    #[test]
    fn definition_claim_requires_configuration_body() {
        let mut sentence = claim_sentence(int_token("before"), int_variable("after", "exists"));
        sentence.content = crate::ir_level::RuleContent::Term {
            kind: SentenceKind::Claim,
            body: DefinitionTerm::rewrite(
                node("term-rewrite"),
                DefinitionSortRef::Builtin(BuiltinSort::Int),
                int_token("term-before"),
                int_variable("term-after", "exists"),
            )
            .expect("valid rewrite")
            .try_into()
            .unwrap(),
        };
        assert!(matches!(
            validate_rule::<DefinitionLevel>(
                &sentence,
                None,
                &BTreeMap::new(),
                &BTreeMap::new(),
                &BTreeSet::new(),
                &BTreeSet::new(),
                &BTreeSet::new(),
                &BTreeMap::new(),
                &BTreeSet::new(),
                &mut BTreeSet::new(),
            ),
            Err(DefinitionValidationError::ClaimBodyNotConfiguration(_))
        ));
    }
}
