use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt;

use krs_diagnostic::{Diagnostic, Location, ToDiagnostic, codes};
use krs_ir::{
    ApplicationRef, CellAttribute, CellContentFrame, CellPost, ConfigurationRoot, FixedCell,
    FixedCellClause, FixedCellContent, FixedCellPattern, FixedConfiguration,
    FixedConfigurationPattern, FixedConfigurationRewrite, FixedConfigurationVariable,
    FixedInitializerCell, FixedInitializerContent, GrammarProductionItemKind,
    GroupAssociativitySentence, IntLiterals, IrIdentityError, LayoutSentence, LexicalSentence,
    ModuleId, NodeOrigin, OriginFrame, OriginStack, PrecedenceRelation, ProductionAttribute,
    ProductionContextAliasReference, ProductionFieldReference, ProductionGroupId,
    ProductionResultSort, SentenceKind, SourceMapKey, StableItemId, StableText,
    TransformationOriginKind, lower_hex,
};
use krs_ir_levels::ModuleRole;
use krs_ir_levels::{
    ContextAliasSentence, DefinitionClaim, DefinitionIr, DefinitionModule, DefinitionRuleCondition,
    DefinitionRulePriority, DefinitionScopedBinder, DefinitionSentence, DefinitionSimplification,
    DefinitionSimplificationPriority, DefinitionSortRef, DefinitionTerm, DefinitionValidationError,
    LabelId, LabelIdentity, ProductionGroupIdentity, ProductionItem, ProductionSentence,
    RuleBodyRef, RuleSentence, SemanticConfiguration, SemanticModule, SemanticProduction,
    SemanticSortRef, SemanticTerm, SemanticTermKind, SemanticTheory, SemanticVariable,
    SubsortSentence, SymbolId, SymbolIdentity, SymbolKind, SyntaxSortSentence,
    k_surface::{ImportPolicy, builtin_imports},
};
use sha2::{Digest, Sha256};

use crate::partition::{
    ModulePlacement, Partition, PartitionError, is_framework_module, production_display_name,
    program_syntax_module_name,
};
use crate::{SourceMap, SymbolMap};

/// A checked Definition IR and the target-neutral sidecars shared by adapters.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LoweredDefinition {
    definition: DefinitionIr,
    symbol_map: SymbolMap,
    source_map: SourceMap,
    partition: Partition,
}

impl LoweredDefinition {
    /// Returns the sole checked meaning consumed by frontend adapters.
    #[must_use]
    pub const fn definition(&self) -> &DefinitionIr {
        &self.definition
    }

    /// Returns the deterministic map of Definition IR identities to emitted names.
    #[must_use]
    pub const fn symbol_map(&self) -> &SymbolMap {
        &self.symbol_map
    }

    /// Returns the adapter-independent source map. Generated ranges are added by emitters.
    #[must_use]
    pub const fn source_map(&self) -> &SourceMap {
        &self.source_map
    }

    /// Returns the program-syntax partition of every package.
    #[must_use]
    pub const fn partition(&self) -> &Partition {
        &self.partition
    }
}

/// Namespace whose generated identity or emitted name must be unique.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CollisionNamespace {
    /// Semantic modules.
    Module,
    /// Definition symbol identities.
    SymbolId,
    /// Emitted sort, production, and cell names.
    EmittedSymbol,
    /// Emitted rule and context-alias labels.
    EmittedLabel,
    /// Definition label identities.
    LabelId,
}

impl fmt::Display for CollisionNamespace {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::Module => "module",
            Self::SymbolId => "symbol ID",
            Self::EmittedSymbol => "emitted symbol",
            Self::EmittedLabel => "emitted label",
            Self::LabelId => "label ID",
        })
    }
}

/// Typed failure at the semantic-to-Definition boundary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LoweringError {
    /// Lowering does not support this otherwise-valid semantic shape.
    UnsupportedShape {
        /// Stable node family.
        node: &'static str,
        /// Deterministic explanatory detail.
        detail: String,
    },
    /// Authored syntax is not representable by the production-template subset.
    InvalidProductionTemplate {
        /// Constructor whose template failed.
        production: Box<StableItemId>,
        /// Deterministic explanatory detail.
        detail: String,
    },
    /// A semantic name cannot be rendered as parseable canonical K source.
    InvalidEmittedName {
        /// Name role.
        role: &'static str,
        /// Rejected text.
        value: String,
    },
    /// Two semantic declarations selected the same Definition identity or emitted name.
    NameCollision {
        /// Colliding namespace.
        namespace: CollisionNamespace,
        /// Colliding generated value.
        value: String,
        /// First stable owner.
        first: String,
        /// Second stable owner.
        second: String,
        /// Exact parser-owned authored provenance for the second owner.
        second_origin: OriginStack,
    },
    /// A syntactic list's derived cons or terminator symbol collides with
    /// another production's symbol (KF-020, R11).
    ListSymbolCollision {
        /// The `#[k::syntax_list]` enum, which names the derived symbols.
        list: String,
        /// The other production.
        other: String,
        /// Exact parser-owned authored provenance for the second owner.
        second_origin: OriginStack,
    },
    /// Two generated Definition nodes selected the same source-map key.
    SourceMapCollision(SourceMapKey),
    /// A generated path-free IR identity was rejected by the frozen IR API.
    InvalidGeneratedIdentity(String),
    /// Final target-neutral validation rejected the constructed Definition IR.
    InvalidDefinition(DefinitionValidationError),
    /// A sidecar could not be derived honestly from the constructed Definition IR.
    InvalidSidecar(String),
    /// The program-syntax partition is invalid.
    Partition(PartitionError),
}

impl fmt::Display for LoweringError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnsupportedShape { node, detail } => {
                write!(formatter, "unsupported {node} shape: {detail}")
            }
            Self::InvalidProductionTemplate { production, detail } => {
                write!(
                    formatter,
                    "invalid syntax template for {production}: {detail}"
                )
            }
            Self::InvalidEmittedName { role, value } => {
                write!(formatter, "{role} name {value:?} is not canonical K syntax")
            }
            Self::NameCollision {
                namespace,
                value,
                first,
                second,
                ..
            } => write!(
                formatter,
                "{namespace} name collision for {value:?} between {first} and {second}"
            ),
            Self::ListSymbolCollision { list, other, .. } => {
                let base = lower_camel(list);
                write!(
                    formatter,
                    "syntactic list `{list}` derives the symbols `{base}Cons`/`{base}Nil`, which collide with `{other}`; rename the enum or the other production"
                )
            }
            Self::SourceMapCollision(key) => {
                write!(
                    formatter,
                    "generated source-map key collision at {}",
                    key.as_str()
                )
            }
            Self::InvalidGeneratedIdentity(detail) => formatter.write_str(detail),
            Self::InvalidDefinition(error) => {
                write!(formatter, "invalid lowered Definition IR: {error}")
            }
            Self::InvalidSidecar(detail) => write!(formatter, "invalid lowered sidecar: {detail}"),
            Self::Partition(error) => error.fmt(formatter),
        }
    }
}

impl ToDiagnostic for LoweringError {
    fn to_diagnostic(&self) -> Diagnostic {
        let code = match self {
            Self::UnsupportedShape { .. } => codes::analysis::UNSUPPORTED_SHAPE,
            Self::InvalidProductionTemplate { .. } => codes::analysis::INVALID_PRODUCTION_TEMPLATE,
            Self::InvalidEmittedName { .. } => codes::analysis::INVALID_EMITTED_NAME,
            Self::NameCollision { namespace, .. } => match namespace {
                CollisionNamespace::EmittedSymbol => codes::analysis::SYMBOL_NAME_COLLISION,
                CollisionNamespace::Module
                | CollisionNamespace::SymbolId
                | CollisionNamespace::EmittedLabel
                | CollisionNamespace::LabelId => codes::analysis::NAME_COLLISION,
            },
            Self::ListSymbolCollision { .. } => codes::analysis::SYMBOL_NAME_COLLISION,
            Self::SourceMapCollision(_) => codes::analysis::SOURCE_MAP_COLLISION,
            Self::InvalidGeneratedIdentity(_) => codes::analysis::INVALID_GENERATED_IDENTITY,
            Self::InvalidDefinition(_) => codes::analysis::INVALID_DEFINITION,
            Self::InvalidSidecar(_) => codes::analysis::INVALID_SIDECAR,
            Self::Partition(PartitionError::MixedGroup { .. }) => codes::partition::MIXED_GROUP,
            Self::Partition(PartitionError::SignedIntegerLeak { .. }) => {
                codes::partition::SIGNED_INTEGER_LEAK
            }
        };
        let location = match self {
            Self::NameCollision { second_origin, .. }
            | Self::ListSymbolCollision { second_origin, .. } => second_origin
                .exact_authored_range()
                .map_or(Location::None, Location::Source),
            Self::Partition(PartitionError::MixedGroup { origin, .. }) => origin
                .origin()
                .exact_authored_range()
                .map_or(Location::None, Location::Source),
            _ => Location::None,
        };
        Diagnostic::error(code, self.to_string(), location)
    }
}

impl Error for LoweringError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::InvalidDefinition(error) => Some(error),
            _ => None,
        }
    }
}

impl From<DefinitionValidationError> for LoweringError {
    fn from(value: DefinitionValidationError) -> Self {
        Self::InvalidDefinition(value)
    }
}

impl From<IrIdentityError> for LoweringError {
    fn from(value: IrIdentityError) -> Self {
        Self::InvalidGeneratedIdentity(value.to_string())
    }
}

/// Deterministically lowers a semantic theory to Definition IR.
///
/// One preflight pass assigns every module, symbol, and label identity and
/// rejects collisions before [`DefinitionIr`] construction. Every copied node
/// receives a fresh source-map key and an honest range-free `definition_ir`
/// transformation frame.
///
/// # Errors
///
/// Returns [`LoweringError`] for unsupported shapes, invalid templates or
/// names, naming/source-map collisions, or a failed Definition IR invariant.
pub fn lower_semantic_theory(theory: &SemanticTheory) -> Result<LoweredDefinition, LoweringError> {
    let partition = Partition::of(theory).map_err(LoweringError::Partition)?;
    let names = NamingPass::run(theory)?;
    let mut origins = OriginPass::default();
    let mut declared_production_groups = BTreeSet::new();
    let mut lowered_modules = Vec::new();
    let stdin = crate::console::stdin_cells(theory);
    for module in theory.modules() {
        let mut lower = |part| {
            lower_module(
                module,
                part,
                &names,
                &mut origins,
                &mut declared_production_groups,
                &stdin,
            )
        };
        if module.is_spec() {
            lowered_modules.push(lower(ModulePart::Whole)?.into_spec());
        } else if let Some(placement) = partition.module(module.id()) {
            // The program-syntax module is lowered first so that each group
            // with a program-syntax member is declared there.
            let syntax = lower(ModulePart::ProgramSyntax(placement))?
                .into_program_syntax(module.int_literals());
            let semantics = lower(ModulePart::Semantics(placement))?;
            let semantics = with_raw_builtin_sorts(semantics, Some(&syntax));
            lowered_modules.push(syntax);
            lowered_modules.push(semantics);
        } else {
            lowered_modules.push(with_raw_builtin_sorts(lower(ModulePart::Whole)?, None));
        }
    }
    check_signed_integer_leak(&lowered_modules)?;
    let main_module = names.module(select_main_module(theory)?.id())?;
    let definition = DefinitionIr::new(main_module, lowered_modules)?;
    let symbol_map = SymbolMap::from_definition(&definition)
        .map_err(|error| LoweringError::InvalidSidecar(error.to_string()))?;
    let source_map = SourceMap::from_definition(&definition)
        .map_err(|error| LoweringError::InvalidSidecar(error.to_string()))?;
    Ok(LoweredDefinition {
        definition,
        symbol_map,
        source_map,
        partition,
    })
}

/// Records on each raw sentence of `module` every builtin sort its package
/// mentions (in `module` and its program-syntax module `syntax`), so the module
/// imports their full K modules: raw text is opaque and may use any of their
/// operations.
fn with_raw_builtin_sorts(
    module: DefinitionModule,
    syntax: Option<&DefinitionModule>,
) -> DefinitionModule {
    if !module
        .sentences()
        .iter()
        .any(|sentence| matches!(sentence, DefinitionSentence::Raw(_)))
    {
        return module;
    }
    let mut sorts = krs_ir_levels::k_surface::builtin_sorts(&module);
    if let Some(syntax) = syntax {
        sorts.extend(krs_ir_levels::k_surface::builtin_sorts(syntax));
    }
    module.map_sentences(|sentence| match sentence {
        DefinitionSentence::Raw(mut raw) => {
            raw.builtin_sorts.clone_from(&sorts);
            DefinitionSentence::Raw(raw)
        }
        other => other,
    })
}

/// Which part of a package module one Definition module holds.
#[derive(Clone, Copy)]
enum ModulePart<'a> {
    /// The unpartitioned framework module.
    Whole,
    /// `<NS>-SYNTAX`: sort declarations and the program-syntax grammar.
    ProgramSyntax(&'a ModulePlacement),
    /// `<NS>`: the rest of the grammar, the configuration, and the rules.
    Semantics(&'a ModulePlacement),
}

impl ModulePart<'_> {
    const fn has_sorts(self) -> bool {
        !matches!(self, Self::Semantics(_))
    }

    const fn has_semantics(self) -> bool {
        !matches!(self, Self::ProgramSyntax(_))
    }

    fn has(self, is_syntax: impl FnOnce(&ModulePlacement) -> bool) -> bool {
        match self {
            Self::Whole => true,
            Self::ProgramSyntax(placement) => is_syntax(placement),
            Self::Semantics(placement) => !is_syntax(placement),
        }
    }
}

/// Rejects an `int-literals = "unsigned"` program-syntax module that reaches
/// a signed program-syntax module importing `INT-SYNTAX`: K imports are
/// unions, so the signed literal would become program syntax.
fn check_signed_integer_leak(modules: &[DefinitionModule]) -> Result<(), LoweringError> {
    let syntax_modules = modules
        .iter()
        .filter(|module| module.role() == ModuleRole::ProgramSyntax)
        .map(|module| (module.id(), module))
        .collect::<BTreeMap<_, _>>();
    for module in syntax_modules.values() {
        if module.int_literals() != IntLiterals::Unsigned {
            continue;
        }
        let mut pending = module.imports().iter().collect::<Vec<_>>();
        let mut seen = BTreeSet::new();
        while let Some(import) = pending.pop() {
            if !seen.insert(import) {
                continue;
            }
            let Some(imported) = syntax_modules.get(import) else {
                continue;
            };
            if imported.int_literals() == IntLiterals::Signed
                && builtin_imports(imported, ImportPolicy::ProgramSyntax).contains("INT-SYNTAX")
            {
                return Err(LoweringError::Partition(
                    PartitionError::SignedIntegerLeak {
                        module: module.id().as_str().to_owned(),
                        signed: imported.id().as_str().to_owned(),
                    },
                ));
            }
            pending.extend(imported.imports());
        }
    }
    Ok(())
}

#[derive(Default)]
struct NamingPass {
    modules: BTreeMap<ModuleId, ModuleId>,
    syntax_modules: BTreeMap<ModuleId, ModuleId>,
    sorts: BTreeMap<StableItemId, SymbolIdentity>,
    productions: BTreeMap<StableItemId, SymbolIdentity>,
    fixed_cells: BTreeMap<krs_ir::SemanticId, SymbolId>,
    /// Nested cells by nominal declaration, naming group-cell sorts.
    group_cells: BTreeMap<StableItemId, SymbolId>,
    rules: BTreeMap<StableItemId, LabelIdentity>,
    /// The root of every overload family member, including each root itself.
    overload_roots: BTreeMap<StableItemId, StableItemId>,
}

impl NamingPass {
    #[expect(
        clippy::too_many_lines,
        reason = "Keeps naming and collision checks together for all semantic item kinds."
    )]
    fn run(theory: &SemanticTheory) -> Result<Self, LoweringError> {
        let mut pass = Self::default();
        let mut identities = BTreeMap::<String, String>::new();
        let mut emitted = BTreeMap::<String, String>::new();
        let mut labels = BTreeMap::<String, String>::new();
        let mut modules = BTreeMap::<String, String>::new();
        let mut list_owners = BTreeMap::<String, String>::new();
        let mut production_displays = BTreeMap::<String, String>::new();

        for module in theory.modules() {
            validate_module_name(module.id().as_str())?;
            claim(
                &mut modules,
                module.id().as_str().to_owned(),
                format!("semantic module {}", module.id().as_str()),
                CollisionNamespace::Module,
                module.origin(),
            )?;
            pass.modules
                .insert(module.id().clone(), module.id().clone());
            if !is_framework_module(module.id()) && !module.is_spec() {
                let syntax = program_syntax_module_name(module.id().as_str());
                validate_module_name(&syntax)?;
                claim(
                    &mut modules,
                    syntax.clone(),
                    format!("program-syntax module of {}", module.id().as_str()),
                    CollisionNamespace::Module,
                    module.origin(),
                )?;
                pass.syntax_modules
                    .insert(module.id().clone(), ModuleId::new(syntax)?);
            }
            for sort in module.sorts() {
                let owner = stable_symbol_text(sort.id(), sort.explicit_symbol());
                let id = SymbolId::new(format!("sort:{}", lower_hex(owner.as_bytes())))?;
                let name = sort.explicit_symbol().map_or_else(
                    || sort.id().item_name().to_owned(),
                    |symbol| symbol.final_component().to_owned(),
                );
                validate_sort_name(&name)?;
                claim(
                    &mut identities,
                    id.as_str().to_owned(),
                    owner.clone(),
                    CollisionNamespace::SymbolId,
                    sort.origin(),
                )?;
                claim(
                    &mut emitted,
                    name.clone(),
                    owner,
                    CollisionNamespace::EmittedSymbol,
                    sort.origin(),
                )?;
                pass.sorts.insert(
                    sort.id().clone(),
                    SymbolIdentity::new(id, name, SymbolKind::Sort)?,
                );
            }
            for production in module.productions() {
                let owner = stable_symbol_text(production.id(), production.explicit_symbol());
                let id = SymbolId::new(format!("production:{}", lower_hex(owner.as_bytes())))?;
                let name = production_symbol_name(production, &owner);
                validate_label_name("production symbol", &name)?;
                claim(
                    &mut identities,
                    id.as_str().to_owned(),
                    owner.clone(),
                    CollisionNamespace::SymbolId,
                    production.origin(),
                )?;
                let display = production_display_name(production.id());
                let list = list_enum_name(production).map(str::to_owned);
                let claimed = claim(
                    &mut emitted,
                    name.clone(),
                    owner,
                    CollisionNamespace::EmittedSymbol,
                    production.origin(),
                );
                if claimed.is_err() {
                    // R11: name the syntactic list whose derived symbol clashes.
                    let collision = match (&list, list_owners.get(&name)) {
                        (Some(list), _) => Some((
                            list.clone(),
                            production_displays.get(&name).cloned().unwrap_or_default(),
                        )),
                        (None, Some(list)) => Some((list.clone(), display.clone())),
                        (None, None) => None,
                    };
                    if let Some((list, other)) = collision {
                        return Err(LoweringError::ListSymbolCollision {
                            list,
                            other,
                            second_origin: production.origin().origin().clone(),
                        });
                    }
                    claimed?;
                }
                if let Some(list) = list {
                    list_owners.insert(name.clone(), list);
                }
                production_displays.insert(name.clone(), display);
                pass.productions.insert(
                    production.id().clone(),
                    SymbolIdentity::new(id, name, SymbolKind::Production)?,
                );
            }
            if let Some(configuration) = module.configuration() {
                name_fixed_cells(
                    configuration.cells(),
                    &mut pass.fixed_cells,
                    &mut pass.group_cells,
                    &mut identities,
                    &mut emitted,
                )?;
            }
            for alias in module.context_aliases() {
                validate_label_name("context alias", alias.name())?;
                claim(
                    &mut labels,
                    alias.name().to_owned(),
                    stable_item_text(alias.id()),
                    CollisionNamespace::EmittedLabel,
                    alias.origin(),
                )?;
            }
            for rule in module.rules() {
                let owner = stable_item_text(rule.id());
                let id = LabelId::new(format!("rule:{}", lower_hex(owner.as_bytes())))?;
                let name = rule.label().map_or_else(
                    || match rule.relational_body() {
                        RuleBodyRef::Term(_) => LabelIdentity::fallback_name(&short_hash(&owner)),
                        RuleBodyRef::Configuration { .. } => lower_camel(rule.id().item_name()),
                    },
                    |label| label.name().to_owned(),
                );
                validate_label_name("rule label", &name)?;
                claim(
                    &mut labels,
                    id.as_str().to_owned(),
                    owner.clone(),
                    CollisionNamespace::LabelId,
                    rule.origin(),
                )?;
                claim(
                    &mut labels,
                    name.clone(),
                    owner,
                    CollisionNamespace::EmittedLabel,
                    rule.origin(),
                )?;
                pass.rules
                    .insert(rule.id().clone(), LabelIdentity::new(id, name)?);
            }
        }
        pass.overload_roots = overload_roots(theory)?;
        Ok(pass)
    }

    /// Returns the symbol of the overload family root of `id`, when `id`
    /// belongs to a family.
    fn overload_root(&self, id: &StableItemId) -> Result<Option<SymbolId>, LoweringError> {
        self.overload_roots
            .get(id)
            .map(|root| Ok(self.production(root)?.id().clone()))
            .transpose()
    }

    fn sort(&self, id: &StableItemId) -> Result<SymbolIdentity, LoweringError> {
        self.sorts
            .get(id)
            .cloned()
            .ok_or_else(|| LoweringError::UnsupportedShape {
                node: "sort reference",
                detail: format!("no naming entry for {id}"),
            })
    }

    fn sort_id(&self, id: &StableItemId) -> Result<SymbolId, LoweringError> {
        Ok(self.sort(id)?.id().clone())
    }

    fn group_cell(&self, declaration: &StableItemId) -> Result<SymbolId, LoweringError> {
        self.group_cells
            .get(declaration)
            .cloned()
            .ok_or_else(|| LoweringError::UnsupportedShape {
                node: "cell sort reference",
                detail: format!("{declaration} is not the declaration of a configuration cell"),
            })
    }

    fn production(&self, id: &StableItemId) -> Result<SymbolIdentity, LoweringError> {
        self.productions
            .get(id)
            .cloned()
            .ok_or_else(|| LoweringError::UnsupportedShape {
                node: "production reference",
                detail: format!("no naming entry for {id}"),
            })
    }

    fn module(&self, id: &ModuleId) -> Result<ModuleId, LoweringError> {
        self.modules
            .get(id)
            .cloned()
            .ok_or_else(|| LoweringError::UnsupportedShape {
                node: "module reference",
                detail: format!("no naming entry for {id}"),
            })
    }

    /// Returns the module a program-syntax module imports for `id`: its
    /// `<NS>-SYNTAX` module, or the framework module itself.
    fn syntax_module(&self, id: &ModuleId) -> Result<ModuleId, LoweringError> {
        if is_framework_module(id) {
            return self.module(id);
        }
        self.syntax_modules
            .get(id)
            .cloned()
            .ok_or_else(|| LoweringError::UnsupportedShape {
                node: "module reference",
                detail: format!("no program-syntax naming entry for {id}"),
            })
    }
}

fn name_fixed_cells(
    cells: &[FixedCell<SemanticSortRef, krs_ir::SemanticId>],
    lowered: &mut BTreeMap<krs_ir::SemanticId, SymbolId>,
    groups: &mut BTreeMap<StableItemId, SymbolId>,
    identities: &mut BTreeMap<String, String>,
    emitted: &mut BTreeMap<String, String>,
) -> Result<(), LoweringError> {
    for cell in cells {
        let owner = format!("configuration cell {}", cell.id().as_str());
        let id = SymbolId::new(format!("cell:{}", lower_hex(cell.id().as_str().as_bytes())))?;
        validate_cell_name(cell.name())?;
        claim(
            identities,
            id.as_str().to_owned(),
            owner.clone(),
            CollisionNamespace::SymbolId,
            cell.origin(),
        )?;
        claim(
            emitted,
            cell.name().to_owned(),
            owner,
            CollisionNamespace::EmittedSymbol,
            cell.origin(),
        )?;
        if let Some(declaration) = cell.declaration() {
            groups.insert(declaration.clone(), id.clone());
        }
        lowered.insert(cell.id().clone(), id);
        if let FixedCellContent::Children { children } = cell.content() {
            name_fixed_cells(children, lowered, groups, identities, emitted)?;
        }
    }
    Ok(())
}

#[derive(Default)]
struct OriginPass {
    keys: BTreeSet<SourceMapKey>,
}

impl OriginPass {
    fn lower(
        &mut self,
        semantic: &NodeOrigin,
        role: &'static str,
        item: Option<&StableItemId>,
        discriminator: Option<&str>,
    ) -> Result<NodeOrigin, LoweringError> {
        let mut seed = format!("{role}\0{}", semantic.key().as_str());
        if let Some(discriminator) = discriminator {
            seed.push('\0');
            seed.push_str(discriminator);
        }
        let key = SourceMapKey::new(format!("def.{role}.{}", short_hash(&seed)))?;
        if !self.keys.insert(key.clone()) {
            return Err(LoweringError::SourceMapCollision(key));
        }
        let mut stack = semantic.origin().clone();
        stack.push(OriginFrame::Transformation {
            kind: TransformationOriginKind::DefinitionIr,
            item: item.cloned(),
            label: Some(role.to_owned()),
        });
        Ok(NodeOrigin::new(key, stack))
    }
}

#[expect(
    clippy::too_many_lines,
    reason = "Keeps module sentence lowering in source order in one traversal."
)]
fn lower_module(
    module: &SemanticModule,
    part: ModulePart<'_>,
    names: &NamingPass,
    origins: &mut OriginPass,
    declared_production_groups: &mut BTreeSet<ProductionGroupId>,
    stdin: &BTreeSet<krs_ir::SemanticId>,
) -> Result<DefinitionModule, LoweringError> {
    let mut sentences = Vec::new();
    let mut group_origins = BTreeMap::<ProductionGroupId, &NodeOrigin>::new();
    let productions = module
        .productions()
        .iter()
        .filter(|production| part.has(|placement| placement.production_is_syntax(production.id())))
        .collect::<Vec<_>>();
    for production in &productions {
        for attribute in production.attributes() {
            if let ProductionAttribute::Group { origin, group } = attribute {
                group_origins.entry(group.clone()).or_insert(origin);
            }
        }
    }
    let production_groups = group_origins
        .into_iter()
        .filter(|(group, _)| declared_production_groups.insert(group.clone()))
        .map(|(group, origin)| {
            let emitted_name = format!("krsgroup-{}", short_hash(group.as_str()));
            Ok(ProductionGroupIdentity::new(
                origins.lower(origin, "production-group", None, Some(group.as_str()))?,
                group,
                emitted_name,
            )?)
        })
        .collect::<Result<Vec<_>, LoweringError>>()?;
    let sorts = if part.has_sorts() {
        module.sorts()
    } else {
        &[]
    };
    for sort in sorts {
        sentences.push(DefinitionSentence::SyntaxSort(SyntaxSortSentence::new(
            origins.lower(sort.origin(), "syntax-sort", Some(sort.id()), None)?,
            names.sort(sort.id())?,
        )?));
    }
    for (_, subsort) in module
        .subsorts()
        .iter()
        .enumerate()
        .filter(|(index, _)| part.has(|placement| placement.subsort_is_syntax(*index)))
    {
        let item = match subsort.subsort() {
            SemanticSortRef::Declared(item) => Some(item),
            SemanticSortRef::Builtin(_) | SemanticSortRef::Cell(_) => None,
        };
        sentences.push(DefinitionSentence::Subsort(SubsortSentence::new(
            origins.lower(
                subsort.origin(),
                "subsort",
                item,
                Some(&format!(
                    "{}<:{}",
                    subsort.subsort().stable_text(),
                    subsort.supersort().stable_text()
                )),
            )?,
            lower_sort_ref(subsort.subsort(), names)?,
            lower_sort_ref(subsort.supersort(), names)?,
        )));
    }

    for production in productions {
        sentences.push(DefinitionSentence::Production(ProductionSentence::new(
            origins.lower(
                production.origin(),
                "production",
                Some(production.id()),
                None,
            )?,
            names.production(production.id())?,
            lower_sort_ref(production.result_sort(), names)?,
            lower_production_items(production, names, origins)?,
            lower_production_attributes(production, names, origins)?,
        )?));
    }

    for (index, precedence) in module
        .precedences()
        .iter()
        .enumerate()
        .filter(|(index, _)| part.has(|placement| placement.precedence_is_syntax(*index)))
    {
        sentences.push(DefinitionSentence::Precedence(
            PrecedenceRelation::new(
                origins.lower(
                    precedence.origin(),
                    "precedence",
                    None,
                    Some(&index.to_string()),
                )?,
                precedence.higher().to_vec(),
                precedence.lower().to_vec(),
            )
            .map_err(|error| LoweringError::UnsupportedShape {
                node: "precedence",
                detail: error.to_string(),
            })?,
        ));
    }
    for (index, associativity) in module
        .associativities()
        .iter()
        .enumerate()
        .filter(|(index, _)| part.has(|placement| placement.associativity_is_syntax(*index)))
    {
        sentences.push(DefinitionSentence::Associativity(
            GroupAssociativitySentence::new(
                origins.lower(
                    associativity.origin(),
                    "associativity",
                    None,
                    Some(&index.to_string()),
                )?,
                associativity.associativity(),
                associativity.groups().to_vec(),
            )
            .map_err(|error| LoweringError::UnsupportedShape {
                node: "associativity",
                detail: error.to_string(),
            })?,
        ));
    }

    // Lexicals and layout scan programs, so they live with the program
    // syntax (KF-004).
    if part.has_sorts() {
        for lexical in module.lexicals() {
            sentences.push(DefinitionSentence::Lexical(
                LexicalSentence::new(
                    origins.lower(lexical.origin(), "lexical", None, Some(lexical.name()))?,
                    lexical.name(),
                    lexical.regex(),
                )
                .map_err(|error| LoweringError::UnsupportedShape {
                    node: "lexical",
                    detail: error.to_string(),
                })?,
            ));
        }
        for (index, layout) in module.layouts().iter().enumerate() {
            sentences.push(DefinitionSentence::Layout(
                LayoutSentence::new(
                    origins.lower(layout.origin(), "layout", None, Some(&index.to_string()))?,
                    layout.regex(),
                )
                .map_err(|error| LoweringError::UnsupportedShape {
                    node: "layout",
                    detail: error.to_string(),
                })?,
            ));
        }
    }

    if !part.has_semantics() {
        let id = names.syntax_module(module.id())?;
        let imports = module
            .imports()
            .iter()
            .map(|import| names.syntax_module(import))
            .collect::<Result<BTreeSet<_>, _>>()?;
        return Ok(DefinitionModule::new(
            origins.lower(module.origin(), "module", None, Some(id.as_str()))?,
            id,
            imports.into_iter().collect(),
            production_groups,
            sentences,
        ));
    }

    if let Some(configuration) = module.configuration() {
        sentences.push(lower_configuration(configuration, names, origins)?);
    }

    for alias in module.context_aliases() {
        sentences.push(DefinitionSentence::ContextAlias(ContextAliasSentence::new(
            origins.lower(alias.origin(), "context-alias", Some(alias.id()), None)?,
            alias.id().clone(),
            origins.lower(
                alias.name_origin(),
                "context-alias-name",
                Some(alias.id()),
                None,
            )?,
            alias.name().to_owned(),
            origins.lower(
                alias.here_origin(),
                "context-alias-here",
                Some(alias.id()),
                None,
            )?,
            alias.here().clone(),
            lower_variables(alias.variables(), names)?,
            lower_configuration_pattern(alias.body(), names, origins)?,
        )));
    }

    for rule in module.rules() {
        // A claim keeps its stream cells as ordinary List cells (see `crate::console`).
        let stdin = if rule.claim().is_some() {
            &BTreeSet::new()
        } else {
            stdin
        };
        let dropped = match rule.relational_body() {
            RuleBodyRef::Configuration { body, .. } => stdin_read_remainders(body, stdin),
            RuleBodyRef::Term(_) => BTreeSet::new(),
        };
        let kept = rule
            .variables()
            .iter()
            .filter(|variable| !dropped.contains(variable.id()))
            .cloned()
            .collect::<Vec<_>>();
        let variables = lower_variables(&kept, names)?;
        let label =
            names
                .rules
                .get(rule.id())
                .cloned()
                .ok_or_else(|| LoweringError::UnsupportedShape {
                    node: "rule",
                    detail: format!("no naming entry for {}", rule.id()),
                })?;
        let rule_origin = rule.label().map_or(rule.origin(), |value| value.origin());
        let origin = origins.lower(rule_origin, "rule", Some(rule.id()), None)?;
        let sentence = match rule.relational_body() {
            RuleBodyRef::Term(body) => RuleSentence::new(
                origin,
                label,
                rule.kind(),
                variables,
                lower_rule_rewrite(body, names, origins)?,
            )?,
            RuleBodyRef::Configuration { kind, body } => RuleSentence::new_configuration(
                origin,
                label,
                kind,
                variables,
                lower_configuration_rewrite(body, names, origins, stdin)?,
            ),
        };
        sentences.push(DefinitionSentence::Rule(lower_rule_metadata(
            sentence, rule, names, origins,
        )?));
    }

    for raw in module.raw_sentences() {
        sentences.push(DefinitionSentence::Raw(krs_ir::RawSentence {
            origin: origins.lower(&raw.origin, "raw-k", None, None)?,
            kind: raw.kind,
            text: raw.text.clone(),
            line: raw.line,
            column: raw.column,
            builtin_sorts: BTreeSet::new(),
        }));
    }

    let mut imports = module
        .imports()
        .iter()
        .map(|import| names.module(import))
        .collect::<Result<BTreeSet<_>, _>>()?;
    if matches!(part, ModulePart::Semantics(_)) {
        imports.insert(names.syntax_module(module.id())?);
    }
    Ok(DefinitionModule::new(
        origins.lower(module.origin(), "module", None, Some(module.id().as_str()))?,
        names.module(module.id())?,
        imports.into_iter().collect(),
        production_groups,
        sentences,
    ))
}

fn lower_configuration(
    configuration: &SemanticConfiguration,
    names: &NamingPass,
    origins: &mut OriginPass,
) -> Result<DefinitionSentence, LoweringError> {
    Ok(DefinitionSentence::Configuration(
        lower_fixed_configuration(configuration, names, origins)?,
    ))
}

fn lower_fixed_configuration(
    configuration: &FixedConfiguration<SemanticSortRef, krs_ir::SemanticId, SemanticTerm>,
    names: &NamingPass,
    origins: &mut OriginPass,
) -> Result<FixedConfiguration<DefinitionSortRef, SymbolId, DefinitionTerm>, LoweringError> {
    FixedConfiguration::new(
        origins.lower(
            configuration.origin(),
            "configuration",
            None,
            Some(configuration.id().as_str()),
        )?,
        configuration.id().clone(),
        lower_configuration_root(configuration.root(), origins)?,
        lower_fixed_cells(configuration.cells(), names, origins)?,
        origins.lower(
            configuration.initializer_origin(),
            "initializer",
            None,
            Some(configuration.initializer_id().as_str()),
        )?,
        configuration.initializer_id().clone(),
        configuration
            .variables()
            .iter()
            .map(|variable| {
                FixedConfigurationVariable::new(
                    origins.lower(
                        variable.origin(),
                        "configuration-variable",
                        None,
                        Some(variable.id().as_str()),
                    )?,
                    variable.id().clone(),
                    variable.external_name().to_owned(),
                    lower_sort_ref(variable.sort(), names)?,
                    variable.is_main(),
                )
                .map_err(state_shape_error)
            })
            .collect::<Result<Vec<_>, _>>()?,
        lower_initializer_cells(configuration.initializer(), names, origins)?,
    )
    .map_err(state_shape_error)
}

fn lower_configuration_root(
    root: &ConfigurationRoot,
    origins: &mut OriginPass,
) -> Result<ConfigurationRoot, LoweringError> {
    match root {
        ConfigurationRoot::GeneratedTop => Ok(ConfigurationRoot::GeneratedTop),
        ConfigurationRoot::Named { origin, name } => ConfigurationRoot::named(
            origins.lower(origin, "configuration-root", None, Some(name))?,
            name.clone(),
        )
        .map_err(state_shape_error),
    }
}

fn lower_cell_attributes(
    attributes: &[CellAttribute],
    origins: &mut OriginPass,
) -> Result<Vec<CellAttribute>, LoweringError> {
    attributes
        .iter()
        .map(|attribute| match attribute {
            CellAttribute::Color { origin, value } => CellAttribute::color(
                origins.lower(origin, "cell-attribute", None, Some(value.as_str()))?,
                value.as_str(),
            )
            .map_err(state_shape_error),
            CellAttribute::Multiplicity { origin, value } => Ok(CellAttribute::multiplicity(
                origins.lower(origin, "cell-attribute", None, Some(value.as_str()))?,
                *value,
            )),
            CellAttribute::CollectionType { origin, value } => Ok(CellAttribute::collection_type(
                origins.lower(origin, "cell-attribute", None, Some(value.as_str()))?,
                *value,
            )),
            CellAttribute::Stream { origin, value } => Ok(CellAttribute::stream(
                origins.lower(origin, "cell-attribute", None, Some(value.as_str()))?,
                *value,
            )),
            CellAttribute::Exit { origin } => Ok(CellAttribute::exit(origins.lower(
                origin,
                "cell-attribute",
                None,
                Some("exit"),
            )?)),
        })
        .collect()
}

fn lower_fixed_cells(
    cells: &[FixedCell<SemanticSortRef, krs_ir::SemanticId>],
    names: &NamingPass,
    origins: &mut OriginPass,
) -> Result<Vec<FixedCell<DefinitionSortRef, SymbolId>>, LoweringError> {
    cells
        .iter()
        .map(|cell| {
            let symbol = names.fixed_cells.get(cell.id()).cloned().ok_or_else(|| {
                LoweringError::UnsupportedShape {
                    node: "configuration cell",
                    detail: format!("no naming entry for {}", cell.id()),
                }
            })?;
            let origin = origins.lower(cell.origin(), "cell", None, Some(cell.id().as_str()))?;
            let attributes = lower_cell_attributes(cell.attributes(), origins)?;
            match cell.content() {
                FixedCellContent::Term { sort } => FixedCell::leaf(
                    origin,
                    symbol,
                    cell.name(),
                    attributes,
                    lower_sort_ref(sort, names)?,
                )
                .map_err(state_shape_error),
                FixedCellContent::Children { children } => FixedCell::nested(
                    origin,
                    symbol,
                    cell.name(),
                    attributes,
                    lower_fixed_cells(children, names, origins)?,
                )
                .map_err(state_shape_error),
            }
        })
        .collect()
}

fn lower_initializer_cells(
    cells: &[FixedInitializerCell<krs_ir::SemanticId, SemanticTerm>],
    names: &NamingPass,
    origins: &mut OriginPass,
) -> Result<Vec<FixedInitializerCell<SymbolId, DefinitionTerm>>, LoweringError> {
    cells
        .iter()
        .map(|cell| {
            let symbol = lower_cell_id(cell.cell(), names)?;
            let origin = origins.lower(
                cell.origin(),
                "initializer-cell",
                None,
                Some(cell.cell().as_str()),
            )?;
            match cell.content() {
                FixedInitializerContent::Term { term } => Ok(FixedInitializerCell::term(
                    origin,
                    symbol,
                    lower_term(term, names, origins)?,
                )),
                FixedInitializerContent::Children { children } => FixedInitializerCell::children(
                    origin,
                    symbol,
                    lower_initializer_cells(children, names, origins)?,
                )
                .map_err(state_shape_error),
            }
        })
        .collect()
}

fn lower_cell_id(id: &krs_ir::SemanticId, names: &NamingPass) -> Result<SymbolId, LoweringError> {
    names
        .fixed_cells
        .get(id)
        .cloned()
        .ok_or_else(|| LoweringError::UnsupportedShape {
            node: "configuration cell reference",
            detail: format!("no naming entry for {id}"),
        })
}

fn lower_frame(
    frame: &CellContentFrame,
    origins: &mut OriginPass,
) -> Result<CellContentFrame, LoweringError> {
    match frame {
        CellContentFrame::Exact => Ok(CellContentFrame::Exact),
        CellContentFrame::KSequenceTail { origin, binding } => {
            Ok(CellContentFrame::KSequenceTail {
                origin: origins.lower(
                    origin,
                    "cell-frame",
                    None,
                    binding.as_ref().map(krs_ir::SemanticId::as_str),
                )?,
                binding: binding.clone(),
            })
        }
        CellContentFrame::MapRemainder { origin, binding } => Ok(CellContentFrame::MapRemainder {
            origin: origins.lower(
                origin,
                "cell-frame",
                None,
                binding.as_ref().map(krs_ir::SemanticId::as_str),
            )?,
            binding: binding.clone(),
        }),
        CellContentFrame::ListRemainder { origin } => Ok(CellContentFrame::ListRemainder {
            origin: origins.lower(origin, "cell-frame", None, None)?,
        }),
    }
}

fn lower_configuration_pattern(
    pattern: &FixedConfigurationPattern<krs_ir::SemanticId, SemanticTerm>,
    names: &NamingPass,
    origins: &mut OriginPass,
) -> Result<FixedConfigurationPattern<SymbolId, DefinitionTerm>, LoweringError> {
    FixedConfigurationPattern::new(
        origins.lower(
            pattern.origin(),
            "configuration-pattern",
            None,
            Some(pattern.configuration().as_str()),
        )?,
        pattern.configuration().clone(),
        pattern
            .cells()
            .iter()
            .map(|cell| {
                Ok(FixedCellPattern::new(
                    origins.lower(
                        cell.origin(),
                        "cell-clause",
                        None,
                        Some(cell.cell().as_str()),
                    )?,
                    lower_cell_id(cell.cell(), names)?,
                    lower_term(cell.pattern(), names, origins)?,
                    lower_frame(cell.frame(), origins)?,
                ))
            })
            .collect::<Result<Vec<_>, LoweringError>>()?,
        pattern
            .omitted_siblings()
            .iter()
            .map(|cell| lower_cell_id(cell, names))
            .collect::<Result<Vec<_>, _>>()?,
    )
    .map_err(state_shape_error)
}

/// The remainder bindings of the stdin stream reads in `rewrite`, which lowering drops.
fn stdin_read_remainders(
    rewrite: &FixedConfigurationRewrite<krs_ir::SemanticId, SemanticTerm>,
    stdin: &BTreeSet<krs_ir::SemanticId>,
) -> BTreeSet<krs_ir::SemanticId> {
    let clauses = rewrite.clauses();
    (0..clauses.len())
        .filter(|index| stdin.contains(clauses[*index].cell()))
        .filter_map(|index| crate::console::stdin_read(clauses, index))
        .map(|read| read.rest.clone())
        .collect()
}

/// A stdin stream read as K's stream rules unblock it: `ListItem(V) => .List` with an unbound
/// list remainder (`crate::console`).
fn lower_stdin_read(
    clause: &crate::console::SemanticClause,
    item: &SemanticTerm,
    names: &NamingPass,
    origins: &mut OriginPass,
) -> Result<FixedCellClause<SymbolId, DefinitionTerm>, LoweringError> {
    let CellPost::Replace { term: after } = clause.after() else {
        unreachable!("a stdin read replaces the cell's content");
    };
    Ok(FixedCellClause::new(
        origins.lower(
            clause.origin(),
            "cell-clause",
            None,
            Some(clause.cell().as_str()),
        )?,
        lower_cell_id(clause.cell(), names)?,
        lower_term(item, names, origins)?,
        CellPost::Replace {
            term: DefinitionTerm::list(
                origins.lower(after.origin(), "stdin-list-empty", None, None)?,
                DefinitionSortRef::Builtin(krs_ir::BuiltinSort::List),
                krs_ir_levels::ListOperands::Empty,
            ),
        },
        CellContentFrame::ListRemainder {
            origin: origins.lower(clause.origin(), "stdin-list-remainder", None, None)?,
        },
    ))
}

fn lower_configuration_rewrite(
    rewrite: &FixedConfigurationRewrite<krs_ir::SemanticId, SemanticTerm>,
    names: &NamingPass,
    origins: &mut OriginPass,
    stdin: &BTreeSet<krs_ir::SemanticId>,
) -> Result<FixedConfigurationRewrite<SymbolId, DefinitionTerm>, LoweringError> {
    FixedConfigurationRewrite::new(
        origins.lower(
            rewrite.origin(),
            "configuration-rewrite",
            None,
            Some(rewrite.configuration().as_str()),
        )?,
        rewrite.configuration().clone(),
        rewrite
            .clauses()
            .iter()
            .enumerate()
            .map(|(index, clause)| {
                if stdin.contains(clause.cell())
                    && let Some(read) = crate::console::stdin_read(rewrite.clauses(), index)
                {
                    return lower_stdin_read(clause, read.item, names, origins);
                }
                Ok(FixedCellClause::new(
                    origins.lower(
                        clause.origin(),
                        "cell-clause",
                        None,
                        Some(clause.cell().as_str()),
                    )?,
                    lower_cell_id(clause.cell(), names)?,
                    lower_term(clause.before(), names, origins)?,
                    match clause.after() {
                        CellPost::Preserve => CellPost::Preserve,
                        CellPost::Replace { term } => CellPost::Replace {
                            term: lower_term(term, names, origins)?,
                        },
                    },
                    lower_frame(clause.frame(), origins)?,
                )
                .with_kind(clause.kind()))
            })
            .collect::<Result<Vec<_>, LoweringError>>()?,
        rewrite
            .omitted_siblings()
            .iter()
            .map(|cell| lower_cell_id(cell, names))
            .collect::<Result<Vec<_>, _>>()?,
    )
    .map_err(state_shape_error)
}

#[expect(
    clippy::needless_pass_by_value,
    reason = "Matches the owned error argument required by Result::map_err."
)]
fn state_shape_error(error: krs_ir::StateShapeError) -> LoweringError {
    LoweringError::UnsupportedShape {
        node: "fixed state",
        detail: error.to_string(),
    }
}

fn lower_rule_metadata(
    mut sentence: RuleSentence,
    rule: &krs_ir_levels::SemanticRule,
    names: &NamingPass,
    origins: &mut OriginPass,
) -> Result<RuleSentence, LoweringError> {
    sentence = sentence.with_priority(
        rule.priority()
            .map(|priority| -> Result<_, LoweringError> {
                Ok(DefinitionRulePriority::new(
                    origins.lower(priority.origin(), "rule-priority", Some(rule.id()), None)?,
                    priority.value(),
                ))
            })
            .transpose()?,
    )?;
    sentence = sentence.with_anywhere(
        rule.anywhere()
            .map(|origin| origins.lower(origin, "rule-anywhere", Some(rule.id()), None))
            .transpose()?,
    )?;
    sentence = sentence.with_simplification(
        rule.simplification()
            .map(|simplification| -> Result<_, LoweringError> {
                Ok(DefinitionSimplification::new(
                    origins.lower(
                        simplification.origin(),
                        "simplification",
                        Some(rule.id()),
                        None,
                    )?,
                    simplification
                        .priority()
                        .map(|priority| -> Result<_, LoweringError> {
                            Ok(DefinitionSimplificationPriority::new(
                                origins.lower(
                                    priority.origin(),
                                    "simplification-priority",
                                    Some(rule.id()),
                                    None,
                                )?,
                                priority.value(),
                            ))
                        })
                        .transpose()?,
                ))
            })
            .transpose()?,
    );
    sentence = sentence.with_requires(
        rule.requires()
            .map(|condition| {
                lower_rule_condition(condition, rule.id(), names, origins, "rule-condition")
            })
            .transpose()?,
    )?;
    sentence = sentence.with_claim(
        rule.claim()
            .map(|claim| lower_claim(claim, rule.id(), names, origins))
            .transpose()?,
    );
    // A claim keeps its historical origin roles; a transition names its own.
    let (existential_role, ensures_role) = if rule.kind() == SentenceKind::Claim {
        ("claim-existential", "claim-ensures")
    } else {
        ("rule-existential", "rule-ensures")
    };
    sentence = sentence
        .with_existentials(lower_claim_binders(
            rule.existentials(),
            rule.id(),
            names,
            origins,
            existential_role,
        )?)
        .with_ensures(
            rule.ensures()
                .map(|condition| {
                    lower_rule_condition(condition, rule.id(), names, origins, ensures_role)
                })
                .transpose()?,
        )
        .with_fresh(lower_claim_binders(
            rule.fresh(),
            rule.id(),
            names,
            origins,
            "rule-fresh",
        )?)
        .with_restriction(
            rule.restriction()
                .map(|restriction| lower_restriction(restriction, rule.id(), origins))
                .transpose()?,
        )
        .with_unbound_variables(
            rule.unbound_variables()
                .map(|unbound| lower_unbound_variables(unbound, rule.id(), origins))
                .transpose()?,
        );
    Ok(sentence)
}

/// Lowers `unbound_variables = [..]` of a desugar clause (KF-046); variable
/// identities are sentence-local and unchanged.
fn lower_unbound_variables(
    unbound: &krs_ir_levels::IrUnboundVariables,
    item: &StableItemId,
    origins: &mut OriginPass,
) -> Result<krs_ir_levels::IrUnboundVariables, LoweringError> {
    let origin = origins.lower(unbound.origin(), "unbound-variables", Some(item), None)?;
    let variables = unbound
        .variables()
        .iter()
        .enumerate()
        .map(|(ordinal, variable)| {
            Ok(krs_ir_levels::IrUnboundVariable::new(
                origins.lower(
                    variable.origin(),
                    "unbound-variable",
                    Some(item),
                    Some(&ordinal.to_string()),
                )?,
                variable.id().cloned(),
            ))
        })
        .collect::<Result<Vec<_>, LoweringError>>()?;
    Ok(krs_ir_levels::IrUnboundVariables::new(origin, variables))
}

/// Lowers the `concrete`, `symbolic`, and `smt_lemma` keys (KF-043); binder
/// identities are sentence-local and unchanged.
fn lower_restriction(
    restriction: &krs_ir_levels::IrMatchRestriction,
    item: &StableItemId,
    origins: &mut OriginPass,
) -> Result<krs_ir_levels::IrMatchRestriction, LoweringError> {
    let mut ordinal = 0_usize;
    let mut lower_key = |key: Option<&krs_ir_levels::IrRestriction>,
                         role: &'static str|
     -> Result<Option<krs_ir_levels::IrRestriction>, LoweringError> {
        key.map(|key| {
            let origin = origins.lower(key.origin(), role, Some(item), None)?;
            let variables = key
                .variables()
                .iter()
                .map(|variable| {
                    let discriminator = ordinal.to_string();
                    ordinal += 1;
                    Ok(krs_ir_levels::IrRestrictionVariable::new(
                        origins.lower(
                            variable.origin(),
                            "restriction-variable",
                            Some(item),
                            Some(&discriminator),
                        )?,
                        variable.id().clone(),
                    ))
                })
                .collect::<Result<Vec<_>, LoweringError>>()?;
            Ok(krs_ir_levels::IrRestriction::new(origin, variables))
        })
        .transpose()
    };
    let concrete = lower_key(restriction.concrete(), "restriction-concrete")?;
    let symbolic = lower_key(restriction.symbolic(), "restriction-symbolic")?;
    let smt_lemma = restriction
        .smt_lemma()
        .map(|origin| origins.lower(origin, "smt-lemma", Some(item), None))
        .transpose()?;
    Ok(krs_ir_levels::IrMatchRestriction::new(
        concrete, symbolic, smt_lemma,
    ))
}

fn lower_rule_condition(
    condition: &krs_ir_levels::SemanticRuleCondition,
    item: &StableItemId,
    names: &NamingPass,
    origins: &mut OriginPass,
    role: &'static str,
) -> Result<DefinitionRuleCondition, LoweringError> {
    Ok(DefinitionRuleCondition::new(
        origins.lower(condition.origin(), role, Some(item), None)?,
        lower_term(condition.term(), names, origins)?,
    ))
}

fn lower_claim(
    claim: &krs_ir_levels::SemanticClaim,
    item: &StableItemId,
    names: &NamingPass,
    origins: &mut OriginPass,
) -> Result<DefinitionClaim, LoweringError> {
    Ok(DefinitionClaim::new(
        origins.lower(claim.modality_origin(), "claim-modality", Some(item), None)?,
        claim.modality(),
        claim
            .circularity_origin()
            .map(|origin| origins.lower(origin, "claim-circularity", Some(item), None))
            .transpose()?,
        lower_claim_binders(claim.universals(), item, names, origins, "claim-universal")?,
    )
    .with_trusted_origin(
        claim
            .trusted_origin()
            .map(|origin| origins.lower(origin, "claim-trusted", Some(item), None))
            .transpose()?,
    ))
}

fn lower_claim_binders(
    binders: &[krs_ir_levels::SemanticScopedBinder],
    item: &StableItemId,
    names: &NamingPass,
    origins: &mut OriginPass,
    role: &'static str,
) -> Result<Vec<DefinitionScopedBinder>, LoweringError> {
    binders
        .iter()
        .enumerate()
        .map(|(index, binder)| {
            let discriminator = index.to_string();
            Ok(DefinitionScopedBinder::new(
                origins.lower(binder.origin(), role, Some(item), Some(&discriminator))?,
                origins.lower(
                    binder.name_origin(),
                    "claim-binder-name",
                    Some(item),
                    Some(&discriminator),
                )?,
                binder.id().clone(),
                origins.lower(
                    binder.sort_origin(),
                    "claim-binder-sort",
                    Some(item),
                    Some(&discriminator),
                )?,
                lower_sort_ref(binder.sort(), names)?,
            ))
        })
        .collect()
}

fn lower_variables(
    variables: &[SemanticVariable],
    names: &NamingPass,
) -> Result<Vec<krs_ir_levels::DefinitionVariable>, LoweringError> {
    variables
        .iter()
        .map(|variable| {
            Ok(krs_ir_levels::DefinitionVariable::new(
                variable.id().clone(),
                lower_sort_ref(variable.sort(), names)?,
            ))
        })
        .collect()
}

fn lower_sort_ref(
    sort: &SemanticSortRef,
    names: &NamingPass,
) -> Result<DefinitionSortRef, LoweringError> {
    match sort {
        SemanticSortRef::Declared(id) => Ok(DefinitionSortRef::Declared(names.sort_id(id)?)),
        SemanticSortRef::Builtin(sort) => Ok(DefinitionSortRef::Builtin(*sort)),
        SemanticSortRef::Cell(declaration) => {
            Ok(DefinitionSortRef::Cell(names.group_cell(declaration)?))
        }
    }
}

fn lower_production_items(
    production: &SemanticProduction,
    names: &NamingPass,
    origins: &mut OriginPass,
) -> Result<Vec<ProductionItem>, LoweringError> {
    production
        .items()
        .iter()
        .enumerate()
        .map(|(index, item)| {
            let origin = origins.lower(
                item.origin(),
                "production-item",
                Some(production.id()),
                Some(&index.to_string()),
            )?;
            match item.kind() {
                GrammarProductionItemKind::Terminal { text } => {
                    ProductionItem::terminal(origin, text.clone()).map_err(|error| {
                        LoweringError::InvalidProductionTemplate {
                            production: Box::new(production.id().clone()),
                            detail: error.to_string(),
                        }
                    })
                }
                GrammarProductionItemKind::NonTerminal { field, sort } => {
                    Ok(ProductionItem::non_terminal(
                        origin,
                        field.clone(),
                        lower_sort_ref(sort, names)?,
                    ))
                }
                GrammarProductionItemKind::RegexTerminal {
                    precede_regex,
                    regex,
                    follow_regex,
                } => ProductionItem::regex_terminal(
                    origin,
                    precede_regex.clone(),
                    regex.clone(),
                    follow_regex.clone(),
                )
                .map_err(|error| LoweringError::InvalidProductionTemplate {
                    production: Box::new(production.id().clone()),
                    detail: error.to_string(),
                }),
            }
        })
        .collect()
}

fn lower_production_attributes(
    production: &SemanticProduction,
    names: &NamingPass,
    origins: &mut OriginPass,
) -> Result<Vec<krs_ir_levels::DefinitionProductionAttribute>, LoweringError> {
    let mut attributes = lower_authored_production_attributes(production, names, origins)?;
    // A production whose Rust item is not `pub` is K `private`: only its own
    // module, `<NS>`, sees it, so neither programs nor dependents nor proof
    // modules can name it.
    if crate::partition::is_private(production) {
        let origin = origins.lower(
            production.origin(),
            "production-private",
            Some(production.id()),
            None,
        )?;
        let position = attributes
            .iter()
            .position(|attribute| !matches!(attribute, ProductionAttribute::Documentation { .. }))
            .unwrap_or(attributes.len());
        attributes.insert(position, ProductionAttribute::Private { origin });
    }
    // An overload family's root carries the family key too: K identifies a
    // family by the root's symbol, and the root declares it.
    let marked = production
        .attributes()
        .iter()
        .any(|attribute| matches!(attribute, ProductionAttribute::Overload { .. }));
    if !marked && let Some(root) = names.overload_root(production.id())? {
        let origin = origins.lower(
            production.origin(),
            "production-overload-root",
            Some(production.id()),
            None,
        )?;
        let position = attributes
            .iter()
            .position(|attribute| {
                matches!(
                    attribute,
                    ProductionAttribute::Color { .. }
                        | ProductionAttribute::Colors { .. }
                        | ProductionAttribute::Format { .. }
                        | ProductionAttribute::Strictness { .. }
                )
            })
            .unwrap_or(attributes.len());
        attributes.insert(
            position,
            ProductionAttribute::Overload {
                origin,
                target: root,
            },
        );
    }
    Ok(attributes)
}

#[expect(
    clippy::too_many_lines,
    reason = "Keeps exhaustive production attribute lowering in one match."
)]
fn lower_authored_production_attributes(
    production: &SemanticProduction,
    names: &NamingPass,
    origins: &mut OriginPass,
) -> Result<Vec<krs_ir_levels::DefinitionProductionAttribute>, LoweringError> {
    production
        .attributes()
        .iter()
        .enumerate()
        // `internal` and `program` select the module a production is placed
        // in; they are not K attributes.
        .filter(|(_, attribute)| {
            !matches!(
                attribute,
                ProductionAttribute::Internal { .. } | ProductionAttribute::Program { .. }
            )
        })
        .map(|(index, attribute)| {
            let origin = origins.lower(
                attribute.origin(),
                "production-attribute",
                Some(production.id()),
                Some(&index.to_string()),
            )?;
            Ok(match attribute {
                ProductionAttribute::Documentation { text, .. } => {
                    ProductionAttribute::Documentation {
                        origin,
                        text: text.clone(),
                    }
                }
                ProductionAttribute::Function { .. } => ProductionAttribute::Function { origin },
                ProductionAttribute::Total { .. } => ProductionAttribute::Total { origin },
                ProductionAttribute::Hook { operation, .. } => ProductionAttribute::Hook {
                    origin,
                    operation: *operation,
                },
                ProductionAttribute::Alias { recursive, .. } => ProductionAttribute::Alias {
                    origin,
                    recursive: *recursive,
                },
                ProductionAttribute::Desugar { recursive, .. } => ProductionAttribute::Desugar {
                    origin,
                    recursive: *recursive,
                },
                ProductionAttribute::Token {
                    lexical_precedence, ..
                } => ProductionAttribute::Token {
                    origin,
                    lexical_precedence: *lexical_precedence,
                },
                ProductionAttribute::Group { group, .. } => ProductionAttribute::Group {
                    origin,
                    group: group.clone(),
                },
                ProductionAttribute::Bracket { .. } => ProductionAttribute::Bracket { origin },
                ProductionAttribute::Avoid { .. } => ProductionAttribute::Avoid { origin },
                ProductionAttribute::Prefer { .. } => ProductionAttribute::Prefer { origin },
                ProductionAttribute::Memo { .. } => ProductionAttribute::Memo { origin },
                ProductionAttribute::FreshGenerator { .. } => {
                    ProductionAttribute::FreshGenerator { origin }
                }
                ProductionAttribute::Smtlib { symbol, .. } => ProductionAttribute::Smtlib {
                    origin,
                    symbol: symbol.clone(),
                },
                ProductionAttribute::SmtHook { template, .. } => ProductionAttribute::SmtHook {
                    origin,
                    template: template.clone(),
                },
                ProductionAttribute::ListCons {
                    separator,
                    non_empty,
                    terminator,
                    ..
                } => ProductionAttribute::ListCons {
                    origin,
                    separator: separator.clone(),
                    non_empty: *non_empty,
                    terminator: names.production(terminator)?.id().clone(),
                },
                ProductionAttribute::ListTerminator { cons, .. } => {
                    ProductionAttribute::ListTerminator {
                        origin,
                        cons: names.production(cons)?.id().clone(),
                    }
                }
                ProductionAttribute::RawHook {
                    namespace, name, ..
                } => ProductionAttribute::RawHook {
                    origin,
                    namespace: namespace.clone(),
                    name: name.clone(),
                },
                ProductionAttribute::Overload { .. } => ProductionAttribute::Overload {
                    origin,
                    target: names.overload_root(production.id())?.ok_or_else(|| {
                        LoweringError::UnsupportedShape {
                            node: "overload family",
                            detail: format!("{} has no overload root", production.id()),
                        }
                    })?,
                },
                ProductionAttribute::Format { fragments, .. } => ProductionAttribute::Format {
                    origin,
                    fragments: fragments.clone(),
                },
                ProductionAttribute::Color { value, .. } => ProductionAttribute::Color {
                    origin,
                    value: value.clone(),
                },
                ProductionAttribute::Colors { values, .. } => ProductionAttribute::Colors {
                    origin,
                    values: values.clone(),
                },
                ProductionAttribute::Internal { .. } | ProductionAttribute::Program { .. } => {
                    unreachable!("placement attributes are filtered above")
                }
                ProductionAttribute::Private { .. } => {
                    return Err(LoweringError::UnsupportedShape {
                        node: "production attribute",
                        detail: "`private` is derived from Rust visibility, not authored"
                            .to_owned(),
                    });
                }
                ProductionAttribute::Strictness {
                    kind,
                    using,
                    fields,
                    result_sort,
                    ..
                } => ProductionAttribute::Strictness {
                    origin,
                    kind: *kind,
                    using: using
                        .as_ref()
                        .map(|using| -> Result<_, LoweringError> {
                            Ok(ProductionContextAliasReference::new(
                                origins.lower(
                                    using.origin(),
                                    "production-strictness-using",
                                    Some(production.id()),
                                    None,
                                )?,
                                using.alias().clone(),
                            ))
                        })
                        .transpose()?,
                    fields: fields
                        .iter()
                        .enumerate()
                        .map(|(field_index, field)| {
                            Ok(ProductionFieldReference::new(
                                origins.lower(
                                    field.origin(),
                                    "production-strictness-field",
                                    Some(production.id()),
                                    Some(&field_index.to_string()),
                                )?,
                                field.field().clone(),
                            ))
                        })
                        .collect::<Result<Vec<_>, LoweringError>>()?,
                    result_sort: ProductionResultSort::new(
                        origins.lower(
                            result_sort.origin(),
                            "production-result-sort",
                            Some(production.id()),
                            None,
                        )?,
                        lower_sort_ref(result_sort.sort(), names)?,
                    ),
                },
            })
        })
        .collect()
}

fn lower_rule_rewrite(
    body: &krs_ir_levels::IrRewrite<krs_ir_levels::SemanticLevel>,
    names: &NamingPass,
    origins: &mut OriginPass,
) -> Result<DefinitionTerm, LoweringError> {
    let origin = origins.lower(body.origin(), "term", None, None)?;
    Ok(DefinitionTerm::rewrite(
        origin,
        lower_sort_ref(body.sort(), names)?,
        lower_term(body.from(), names, origins)?,
        lower_term(body.to(), names, origins)?,
    )?)
}

fn lower_term(
    term: &SemanticTerm,
    names: &NamingPass,
    origins: &mut OriginPass,
) -> Result<DefinitionTerm, LoweringError> {
    let origin = origins.lower(term.origin(), "term", None, None)?;
    match term.kind() {
        SemanticTermKind::Variable { variable } => Ok(DefinitionTerm::variable(
            origin,
            lower_sort_ref(term.sort(), names)?,
            variable.clone(),
        )),
        SemanticTermKind::Application {
            application,
            arguments,
        } => Ok(DefinitionTerm::application(
            origin,
            lower_sort_ref(term.sort(), names)?,
            match application {
                ApplicationRef::Declared(production) => {
                    ApplicationRef::Declared(names.production(production)?.id().clone())
                }
                ApplicationRef::Builtin(operation) => ApplicationRef::Builtin(*operation),
                ApplicationRef::Generated(operation) => ApplicationRef::Generated(
                    operation.try_map_sort(|sort| lower_sort_ref(sort, names))?,
                ),
            },
            arguments
                .iter()
                .map(|argument| lower_term(argument, names, origins))
                .collect::<Result<Vec<_>, _>>()?,
        )),
        SemanticTermKind::Token { value } => Ok(DefinitionTerm::token(
            origin,
            lower_sort_ref(term.sort(), names)?,
            value.clone(),
        )?),
        SemanticTermKind::KSequence { item_sort, items } => Ok(DefinitionTerm::k_sequence(
            origin,
            lower_sort_ref(item_sort, names)?,
            items
                .iter()
                .map(|item| lower_term(item, names, origins))
                .collect::<Result<Vec<_>, _>>()?,
        )),
        SemanticTermKind::Rewrite { from, to } => Ok(DefinitionTerm::rewrite(
            origin,
            lower_sort_ref(term.sort(), names)?,
            lower_term(from, names, origins)?,
            lower_term(to, names, origins)?,
        )?),
        SemanticTermKind::Map(operands) => Ok(DefinitionTerm::typed_map(
            origin,
            lower_sort_ref(term.sort(), names)?,
            operands.try_map_ref(|operand| lower_term(operand, names, origins))?,
        )),
        SemanticTermKind::List(operands) => Ok(DefinitionTerm::list(
            origin,
            lower_sort_ref(term.sort(), names)?,
            operands.try_map_ref(|operand| lower_term(operand, names, origins))?,
        )),
        SemanticTermKind::Set(operands) => Ok(DefinitionTerm::set(
            origin,
            lower_sort_ref(term.sort(), names)?,
            operands.try_map_ref(|operand| lower_term(operand, names, origins))?,
        )),
        SemanticTermKind::Cell { cell, children } => Ok(DefinitionTerm::cell(
            origin,
            lower_sort_ref(term.sort(), names)?,
            lower_cell_id(cell, names)?,
            children
                .iter()
                .map(|child| lower_term(child, names, origins))
                .collect::<Result<Vec<_>, _>>()?,
        )),
        SemanticTermKind::As { alias, pattern } => Ok(DefinitionTerm::pattern_as(
            origin,
            lower_sort_ref(term.sort(), names)?,
            alias.clone(),
            lower_term(pattern, names, origins)?,
        )),
        SemanticTermKind::Or { alternatives } => Ok(DefinitionTerm::pattern_or(
            origin,
            lower_sort_ref(term.sort(), names)?,
            alternatives.try_map_ref(|alternative| lower_term(alternative, names, origins))?,
        )),
    }
}

/// Maps every overload family member and root to the root its `overload`
/// targets lead to. The semantic pass has rejected dangling targets and
/// cycles; they fail here too rather than loop.
fn overload_roots(
    theory: &SemanticTheory,
) -> Result<BTreeMap<StableItemId, StableItemId>, LoweringError> {
    let targets = theory
        .modules()
        .iter()
        .flat_map(SemanticModule::productions)
        .filter_map(|production| {
            production
                .attributes()
                .iter()
                .find_map(|attribute| match attribute {
                    ProductionAttribute::Overload { target, .. } => {
                        Some((production.id().clone(), target.clone()))
                    }
                    _ => None,
                })
        })
        .collect::<BTreeMap<_, _>>();
    let mut roots = BTreeMap::new();
    for member in targets.keys() {
        let mut root = member;
        let mut seen = BTreeSet::from([member]);
        while let Some(next) = targets.get(root) {
            if !seen.insert(next) {
                return Err(LoweringError::UnsupportedShape {
                    node: "overload family",
                    detail: format!("the overload targets of {member} form a cycle"),
                });
            }
            root = next;
        }
        roots.insert(member.clone(), root.clone());
        roots.insert(root.clone(), root.clone());
    }
    Ok(roots)
}

fn select_main_module(theory: &SemanticTheory) -> Result<&SemanticModule, LoweringError> {
    main_semantic_module(theory.modules()).ok_or_else(|| {
        let configured = theory
            .modules()
            .iter()
            .filter(|module| module.configuration().is_some())
            .count();
        LoweringError::UnsupportedShape {
            node: "main module",
            detail: format!("expected one configured module, found {configured}"),
        }
    })
}

/// The definition's main module: the one module that no other definition
/// module imports, when it imports the configured module transitively (a
/// package that only adds tokens to a language it depends on, such as a
/// verification package, KF-041); otherwise the configured module. Spec
/// modules are never the main module.
pub(crate) fn main_semantic_module(modules: &[SemanticModule]) -> Option<&SemanticModule> {
    let definition = modules
        .iter()
        .filter(|module| !module.is_spec())
        .collect::<Vec<_>>();
    let configured = match definition
        .iter()
        .filter(|module| module.configuration().is_some())
        .collect::<Vec<_>>()
        .as_slice()
    {
        [module] => **module,
        _ => return None,
    };
    let imported = definition
        .iter()
        .flat_map(|module| module.imports())
        .collect::<BTreeSet<_>>();
    let tops = definition
        .iter()
        .filter(|module| !imported.contains(module.id()))
        .collect::<Vec<_>>();
    if let [top] = tops.as_slice() {
        let mut seen = BTreeSet::new();
        let mut stack = vec![top.id()];
        while let Some(id) = stack.pop() {
            if id == configured.id() {
                return Some(top);
            }
            if seen.insert(id)
                && let Some(module) = definition.iter().find(|module| module.id() == id)
            {
                stack.extend(module.imports());
            }
        }
    }
    Some(configured)
}

fn claim(
    names: &mut BTreeMap<String, String>,
    value: String,
    owner: String,
    namespace: CollisionNamespace,
    second_origin: &NodeOrigin,
) -> Result<(), LoweringError> {
    if let Some(first) = names.insert(value.clone(), owner.clone()) {
        return Err(LoweringError::NameCollision {
            namespace,
            value,
            first,
            second: owner,
            second_origin: second_origin.origin().clone(),
        });
    }
    Ok(())
}

fn validate_module_name(value: &str) -> Result<(), LoweringError> {
    let valid = value
        .bytes()
        .next()
        .is_some_and(|byte| byte.is_ascii_uppercase())
        && value
            .bytes()
            .all(|byte| byte.is_ascii_uppercase() || byte.is_ascii_digit() || byte == b'-');
    if valid {
        Ok(())
    } else {
        Err(LoweringError::InvalidEmittedName {
            role: "module",
            value: value.to_owned(),
        })
    }
}

fn validate_sort_name(value: &str) -> Result<(), LoweringError> {
    let valid = value
        .bytes()
        .next()
        .is_some_and(|byte| byte.is_ascii_uppercase())
        && value
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_');
    if valid {
        Ok(())
    } else {
        Err(LoweringError::InvalidEmittedName {
            role: "sort",
            value: value.to_owned(),
        })
    }
}

fn validate_cell_name(value: &str) -> Result<(), LoweringError> {
    let valid = value
        .bytes()
        .next()
        .is_some_and(|byte| byte.is_ascii_lowercase())
        && value.bytes().all(|byte| byte.is_ascii_alphanumeric());
    if valid {
        Ok(())
    } else {
        Err(LoweringError::InvalidEmittedName {
            role: "cell",
            value: value.to_owned(),
        })
    }
}

fn validate_label_name(role: &'static str, value: &str) -> Result<(), LoweringError> {
    let valid = value
        .bytes()
        .next()
        .is_some_and(|byte| byte.is_ascii_alphabetic() || byte == b'_')
        && value
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'-'));
    if valid {
        Ok(())
    } else {
        Err(LoweringError::InvalidEmittedName {
            role,
            value: value.to_owned(),
        })
    }
}

fn stable_item_text(id: &StableItemId) -> String {
    let mut text = String::new();
    push_component(&mut text, id.package().k_namespace());
    for component in id.module_path() {
        push_component(&mut text, component);
    }
    push_component(&mut text, id.item_name());
    push_component(&mut text, &id.item_kind().stable_text());
    push_component(&mut text, id.disambiguator());
    text
}

fn stable_symbol_text(id: &StableItemId, explicit: Option<&krs_ir::ExplicitSymbol>) -> String {
    let Some(explicit) = explicit else {
        return stable_item_text(id);
    };

    let mut text = String::new();
    push_component(&mut text, id.package().k_namespace());
    for component in explicit.as_str().split("::") {
        push_component(&mut text, component);
    }
    push_component(&mut text, &id.item_kind().stable_text());
    push_component(&mut text, id.disambiguator());
    text
}

/// The `#[k::syntax_list]` enum of a list production, which names its
/// symbols: `lowerCamel(Enum) + "Cons"` and `+ "Nil"` (KF-020, R11).
fn list_enum_name(production: &krs_ir_levels::SemanticProduction) -> Option<&str> {
    let is_list = production.attributes().iter().any(|attribute| {
        matches!(
            attribute,
            ProductionAttribute::ListCons { .. } | ProductionAttribute::ListTerminator { .. }
        )
    });
    match production.result_sort() {
        krs_ir_levels::SemanticSortRef::Declared(sort) if is_list => Some(sort.item_name()),
        _ => None,
    }
}

fn production_symbol_name(production: &krs_ir_levels::SemanticProduction, owner: &str) -> String {
    if let Some(list) = list_enum_name(production) {
        let is_cons = production
            .attributes()
            .iter()
            .any(|attribute| matches!(attribute, ProductionAttribute::ListCons { .. }));
        let suffix = if is_cons { "Cons" } else { "Nil" };
        return format!("{}{suffix}", lower_camel(list));
    }
    if let Some(symbol) = production.explicit_symbol() {
        return lower_camel(symbol.final_component());
    }
    if production.id().is_generated_production() {
        SymbolIdentity::generated_production_name(&short_hash(owner))
    } else {
        lower_camel(production.id().item_name())
    }
}

fn push_component(output: &mut String, value: &str) {
    output.push_str(&value.len().to_string());
    output.push(':');
    output.push_str(value);
}

fn short_hash(value: &str) -> String {
    let digest = Sha256::digest(value.as_bytes());
    lower_hex(&digest[..12])
}

fn lower_camel(value: &str) -> String {
    let mut characters = value.chars();
    match characters.next() {
        Some(first) => first.to_lowercase().chain(characters).collect(),
        None => String::new(),
    }
}

#[cfg(test)]
mod tests {
    use krs_ir::{ExplicitSymbol, ItemKind, StableItemId};

    use super::{CollisionNamespace, LoweringError, claim, stable_symbol_text};
    use krs_diagnostic::{Location, ToDiagnostic, codes};
    use std::collections::BTreeMap;

    fn item(module: &str, name: &str, kind: ItemKind) -> StableItemId {
        krs_ir::testing::item_in(
            krs_ir::testing::package("KRS-STABLE-NAMES", "fixture"),
            module,
            name,
            kind,
        )
    }

    #[test]
    fn collision_namespace_selects_the_code_and_preserves_the_second_origin() {
        let origin = krs_ir::NodeOrigin::new(
            krs_ir::SourceMapKey::new("sem.collision").unwrap(),
            krs_ir::testing::authored(3, 8),
        );
        let expected_range = origin.origin().exact_authored_range().unwrap();
        for (namespace, code, text) in [
            (
                CollisionNamespace::EmittedSymbol,
                codes::analysis::SYMBOL_NAME_COLLISION,
                "emitted symbol",
            ),
            (
                CollisionNamespace::EmittedLabel,
                codes::analysis::NAME_COLLISION,
                "emitted label",
            ),
            (
                CollisionNamespace::Module,
                codes::analysis::NAME_COLLISION,
                "module",
            ),
            (
                CollisionNamespace::SymbolId,
                codes::analysis::NAME_COLLISION,
                "symbol ID",
            ),
            (
                CollisionNamespace::LabelId,
                codes::analysis::NAME_COLLISION,
                "label ID",
            ),
        ] {
            let mut names = BTreeMap::new();
            claim(
                &mut names,
                "same".to_owned(),
                "first".to_owned(),
                namespace,
                &origin,
            )
            .unwrap();
            let error = claim(
                &mut names,
                "same".to_owned(),
                "second".to_owned(),
                namespace,
                &origin,
            )
            .unwrap_err();
            assert!(matches!(error, LoweringError::NameCollision { .. }));
            let diagnostic = error.to_diagnostic();
            assert_eq!(diagnostic.code, code);
            assert_eq!(
                diagnostic.message,
                format!("{text} name collision for \"same\" between first and second")
            );
            let Location::Source(actual) = diagnostic.primary.location else {
                panic!("missing second collision owner range");
            };
            assert_eq!(actual, expected_range);
            assert!(diagnostic.notes.is_empty());
        }
    }

    #[test]
    fn explicit_symbol_replaces_the_rust_path_in_stable_identity() {
        let baseline_sort = item("api", "Expr", ItemKind::Sort);
        let moved_sort = item("moved_api", "Expr", ItemKind::Sort);
        let baseline_production = item("api", "PublicValue", ItemKind::Constructor);
        let moved_production = item("moved_api", "PublicValue", ItemKind::Constructor);

        assert_ne!(
            stable_symbol_text(&baseline_sort, None),
            stable_symbol_text(&moved_sort, None),
        );
        assert_eq!(
            stable_symbol_text(&baseline_sort, None),
            stable_symbol_text(
                &moved_sort,
                Some(&ExplicitSymbol::new("api::Expr").unwrap()),
            ),
        );
        assert_eq!(
            stable_symbol_text(&baseline_production, None),
            stable_symbol_text(
                &moved_production,
                Some(&ExplicitSymbol::new("api::PublicValue").unwrap()),
            ),
        );
    }
}
