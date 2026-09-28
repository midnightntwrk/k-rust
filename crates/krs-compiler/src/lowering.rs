use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt;

use krs_ir::{
    ApplicationRef, CellAttribute, CellContentFrame, CellPost, ConfigurationRoot,
    ContextAliasSentence, DefinitionClaim, DefinitionClaimBinder, DefinitionIr, DefinitionModule,
    DefinitionRuleCondition, DefinitionRulePriority, DefinitionSentence, DefinitionSimplification,
    DefinitionSimplificationPriority, DefinitionSortRef, DefinitionTerm, DefinitionTermKind,
    DefinitionValidationError, FixedCell, FixedCellClause, FixedCellContent, FixedCellPattern,
    FixedConfiguration, FixedConfigurationPattern, FixedConfigurationRewrite,
    FixedConfigurationVariable, FixedInitializerCell, FixedInitializerContent,
    GrammarProductionItemKind, GroupAssociativitySentence, IrIdentityError, LabelId, LabelIdentity,
    ModuleId, NodeOrigin, OriginFrame, OriginStack, PrecedenceRelation, ProductionAttribute,
    ProductionContextAliasReference, ProductionFieldReference, ProductionGroupId,
    ProductionGroupIdentity, ProductionItem, ProductionResultSort, ProductionSentence,
    RuleSentence, SemanticConfiguration, SemanticModule, SemanticProduction, SemanticRuleBody,
    SemanticSortRef, SemanticTerm, SemanticTermKind, SemanticTheory, SemanticVariable,
    SourceMapKey, StableItemId, SubsortSentence, SymbolId, SymbolIdentity, SymbolKind,
    SyntaxSortSentence, TransformationOriginKind,
};
use sha2::{Digest, Sha256};

use crate::{SourceMap, SymbolMap};

/// A checked Definition IR and the target-neutral sidecars shared by adapters.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LoweredDefinition {
    definition: DefinitionIr,
    symbol_map: SymbolMap,
    source_map: SourceMap,
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

    /// Consumes the lowering result and returns its checked Definition IR.
    #[must_use]
    pub fn into_definition(self) -> DefinitionIr {
        self.definition
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
        namespace: &'static str,
        /// Colliding generated value.
        value: String,
        /// First stable owner.
        first: String,
        /// Second stable owner.
        second: String,
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
                    "invalid syntax template for {production:?}: {detail}"
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
            Self::SourceMapCollision(key) => {
                write!(
                    formatter,
                    "generated source-map key collision at {:?}",
                    key.as_str()
                )
            }
            Self::InvalidGeneratedIdentity(detail) => formatter.write_str(detail),
            Self::InvalidDefinition(error) => {
                write!(formatter, "invalid lowered Definition IR: {error}")
            }
            Self::InvalidSidecar(detail) => write!(formatter, "invalid lowered sidecar: {detail}"),
        }
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
    let names = NamingPass::run(theory)?;
    let mut origins = OriginPass::default();
    let mut modules = theory.modules().iter().collect::<Vec<_>>();
    modules.sort_by(|left, right| left.id().cmp(right.id()));
    let mut declared_production_groups = BTreeSet::new();
    let lowered_modules = modules
        .into_iter()
        .map(|module| {
            lower_module(
                module,
                &names,
                &mut origins,
                &mut declared_production_groups,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
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
    })
}

#[derive(Default)]
struct NamingPass {
    modules: BTreeMap<ModuleId, ModuleId>,
    sorts: BTreeMap<StableItemId, SymbolIdentity>,
    productions: BTreeMap<StableItemId, SymbolIdentity>,
    fixed_cells: BTreeMap<krs_ir::SemanticId, SymbolId>,
    rules: BTreeMap<StableItemId, LabelIdentity>,
}

impl NamingPass {
    #[allow(clippy::too_many_lines)]
    fn run(theory: &SemanticTheory) -> Result<Self, LoweringError> {
        let mut pass = Self::default();
        let mut identities = BTreeMap::<String, String>::new();
        let mut emitted = BTreeMap::<String, String>::new();
        let mut labels = BTreeMap::<String, String>::new();
        let mut modules = BTreeMap::<String, String>::new();

        for module in theory.modules() {
            validate_module_name(module.id().as_str())?;
            claim(
                &mut modules,
                module.id().as_str().to_owned(),
                format!("semantic module {}", module.id().as_str()),
                "module",
                module.origin(),
            )?;
            pass.modules
                .insert(module.id().clone(), module.id().clone());
            for sort in module.sorts() {
                let owner = stable_symbol_text(sort.id(), sort.explicit_symbol());
                let id = SymbolId::new(format!("sort:{}", hex_encode(owner.as_bytes())))?;
                let name = sort.explicit_symbol().map_or_else(
                    || sort.id().item_name().to_owned(),
                    |symbol| symbol.final_component().to_owned(),
                );
                validate_sort_name(&name)?;
                claim(
                    &mut identities,
                    id.as_str().to_owned(),
                    owner.clone(),
                    "symbol ID",
                    sort.origin(),
                )?;
                claim(
                    &mut emitted,
                    name.clone(),
                    owner,
                    "emitted symbol",
                    sort.origin(),
                )?;
                pass.sorts.insert(
                    sort.id().clone(),
                    SymbolIdentity::new(id, name, SymbolKind::Sort)?,
                );
            }
            for production in module.productions() {
                let owner = stable_symbol_text(production.id(), production.explicit_symbol());
                let id = SymbolId::new(format!("production:{}", hex_encode(owner.as_bytes())))?;
                let name = production_symbol_name(production, &owner);
                validate_label_name("production symbol", &name)?;
                claim(
                    &mut identities,
                    id.as_str().to_owned(),
                    owner.clone(),
                    "symbol ID",
                    production.origin(),
                )?;
                claim(
                    &mut emitted,
                    name.clone(),
                    owner,
                    "emitted symbol",
                    production.origin(),
                )?;
                pass.productions.insert(
                    production.id().clone(),
                    SymbolIdentity::new(id, name, SymbolKind::Production)?,
                );
            }
            if let Some(configuration) = module.configuration() {
                name_fixed_cells(
                    configuration.cells(),
                    &mut pass.fixed_cells,
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
                    "emitted label",
                    alias.origin(),
                )?;
            }
            for rule in module.rules() {
                let owner = stable_item_text(rule.id());
                let id = LabelId::new(format!("rule:{}", hex_encode(owner.as_bytes())))?;
                let name = rule.label().map_or_else(
                    || match rule.relational_body() {
                        SemanticRuleBody::Term(_) => format!("krsRule_{}", short_hash(&owner)),
                        SemanticRuleBody::Configuration(_) => lower_camel(rule.id().item_name()),
                    },
                    |label| label.name().to_owned(),
                );
                validate_label_name("rule label", &name)?;
                claim(
                    &mut labels,
                    id.as_str().to_owned(),
                    owner.clone(),
                    "label ID",
                    rule.origin(),
                )?;
                claim(
                    &mut labels,
                    name.clone(),
                    owner,
                    "emitted label",
                    rule.origin(),
                )?;
                pass.rules
                    .insert(rule.id().clone(), LabelIdentity::new(id, name)?);
            }
        }
        Ok(pass)
    }

    fn sort(&self, id: &StableItemId) -> Result<SymbolIdentity, LoweringError> {
        self.sorts
            .get(id)
            .cloned()
            .ok_or_else(|| LoweringError::UnsupportedShape {
                node: "sort reference",
                detail: format!("no naming entry for {id:?}"),
            })
    }

    fn sort_id(&self, id: &StableItemId) -> Result<SymbolId, LoweringError> {
        Ok(self.sort(id)?.id().clone())
    }

    fn production(&self, id: &StableItemId) -> Result<SymbolIdentity, LoweringError> {
        self.productions
            .get(id)
            .cloned()
            .ok_or_else(|| LoweringError::UnsupportedShape {
                node: "production reference",
                detail: format!("no naming entry for {id:?}"),
            })
    }

    fn module(&self, id: &ModuleId) -> Result<ModuleId, LoweringError> {
        self.modules
            .get(id)
            .cloned()
            .ok_or_else(|| LoweringError::UnsupportedShape {
                node: "module reference",
                detail: format!("no naming entry for {:?}", id.as_str()),
            })
    }
}

fn name_fixed_cells(
    cells: &[FixedCell<SemanticSortRef, krs_ir::SemanticId>],
    lowered: &mut BTreeMap<krs_ir::SemanticId, SymbolId>,
    identities: &mut BTreeMap<String, String>,
    emitted: &mut BTreeMap<String, String>,
) -> Result<(), LoweringError> {
    for cell in cells {
        let owner = format!("configuration cell {}", cell.id().as_str());
        let id = SymbolId::new(format!(
            "cell:{}",
            hex_encode(cell.id().as_str().as_bytes())
        ))?;
        validate_cell_name(cell.name())?;
        claim(
            identities,
            id.as_str().to_owned(),
            owner.clone(),
            "symbol ID",
            cell.origin(),
        )?;
        claim(
            emitted,
            cell.name().to_owned(),
            owner,
            "emitted symbol",
            cell.origin(),
        )?;
        lowered.insert(cell.id().clone(), id);
        if let FixedCellContent::Children { children } = cell.content() {
            name_fixed_cells(children, lowered, identities, emitted)?;
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

#[allow(clippy::too_many_lines)]
fn lower_module(
    module: &SemanticModule,
    names: &NamingPass,
    origins: &mut OriginPass,
    declared_production_groups: &mut BTreeSet<ProductionGroupId>,
) -> Result<DefinitionModule, LoweringError> {
    let mut sentences = Vec::new();
    let mut group_origins = BTreeMap::<ProductionGroupId, &NodeOrigin>::new();
    for production in module.productions() {
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
    let mut sorts = module.sorts().iter().collect::<Vec<_>>();
    sorts.sort_by(|left, right| left.id().cmp(right.id()));
    for sort in sorts {
        sentences.push(DefinitionSentence::SyntaxSort(SyntaxSortSentence::new(
            origins.lower(sort.origin(), "syntax-sort", Some(sort.id()), None)?,
            names.sort(sort.id())?,
        )?));
    }
    let mut subsorts = module.subsorts().iter().collect::<Vec<_>>();
    subsorts.sort();
    for subsort in subsorts {
        let item = match subsort.subsort() {
            SemanticSortRef::Declared(item) => Some(item),
            SemanticSortRef::Builtin(_) => None,
        };
        sentences.push(DefinitionSentence::Subsort(SubsortSentence::new(
            origins.lower(
                subsort.origin(),
                "subsort",
                item,
                Some(&format!(
                    "{:?}<:{:?}",
                    subsort.subsort(),
                    subsort.supersort()
                )),
            )?,
            lower_sort_ref(subsort.subsort(), names)?,
            lower_sort_ref(subsort.supersort(), names)?,
        )));
    }

    let mut productions = module.productions().iter().collect::<Vec<_>>();
    productions.sort_by(|left, right| left.id().cmp(right.id()));
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

    for (index, precedence) in module.precedences().iter().enumerate() {
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
    for (index, associativity) in module.associativities().iter().enumerate() {
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

    let mut rules = module.rules().iter().collect::<Vec<_>>();
    rules.sort_by(|left, right| left.id().cmp(right.id()));
    for rule in rules {
        let variables = lower_variables(rule.variables(), names)?;
        let label =
            names
                .rules
                .get(rule.id())
                .cloned()
                .ok_or_else(|| LoweringError::UnsupportedShape {
                    node: "rule",
                    detail: format!("no naming entry for {:?}", rule.id()),
                })?;
        let rule_origin = rule.label().map_or(rule.origin(), |value| value.origin());
        let origin = origins.lower(rule_origin, "rule", Some(rule.id()), None)?;
        let sentence = match rule.relational_body() {
            SemanticRuleBody::Term(body) => RuleSentence::new(
                origin,
                label,
                rule.kind(),
                variables,
                lower_term(body, names, origins)?,
            )?,
            SemanticRuleBody::Configuration(body) => RuleSentence::new_configuration(
                origin,
                label,
                rule.kind(),
                variables,
                lower_configuration_rewrite(body, names, origins)?,
            ),
        };
        sentences.push(DefinitionSentence::Rule(lower_rule_metadata(
            sentence, rule, names, origins,
        )?));
    }

    let mut imports = module
        .imports()
        .iter()
        .map(|import| names.module(import))
        .collect::<Result<Vec<_>, _>>()?;
    imports.sort();
    imports.dedup();
    Ok(DefinitionModule::new(
        origins.lower(module.origin(), "module", None, Some(module.id().as_str()))?,
        names.module(module.id())?,
        imports,
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
                    detail: format!("no naming entry for {:?}", cell.id().as_str()),
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
            detail: format!("no naming entry for {:?}", id.as_str()),
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

fn lower_configuration_rewrite(
    rewrite: &FixedConfigurationRewrite<krs_ir::SemanticId, SemanticTerm>,
    names: &NamingPass,
    origins: &mut OriginPass,
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
            .map(|clause| {
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
                ))
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

#[allow(clippy::needless_pass_by_value)]
fn state_shape_error(error: krs_ir::StateShapeError) -> LoweringError {
    LoweringError::UnsupportedShape {
        node: "fixed state",
        detail: error.to_string(),
    }
}

fn lower_rule_metadata(
    mut sentence: RuleSentence,
    rule: &krs_ir::SemanticRule,
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
    Ok(sentence)
}

fn lower_rule_condition(
    condition: &krs_ir::SemanticRuleCondition,
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
    claim: &krs_ir::SemanticClaim,
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
        lower_claim_binders(
            claim.existentials(),
            item,
            names,
            origins,
            "claim-existential",
        )?,
        claim
            .ensures()
            .map(|condition| lower_rule_condition(condition, item, names, origins, "claim-ensures"))
            .transpose()?,
    ))
}

fn lower_claim_binders(
    binders: &[krs_ir::SemanticClaimBinder],
    item: &StableItemId,
    names: &NamingPass,
    origins: &mut OriginPass,
    role: &'static str,
) -> Result<Vec<DefinitionClaimBinder>, LoweringError> {
    binders
        .iter()
        .enumerate()
        .map(|(index, binder)| {
            let discriminator = index.to_string();
            Ok(DefinitionClaimBinder::new(
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
) -> Result<Vec<krs_ir::DefinitionVariable>, LoweringError> {
    variables
        .iter()
        .map(|variable| {
            Ok(krs_ir::DefinitionVariable::new(
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

#[allow(clippy::too_many_lines)]
fn lower_production_attributes(
    production: &SemanticProduction,
    names: &NamingPass,
    origins: &mut OriginPass,
) -> Result<Vec<krs_ir::DefinitionProductionAttribute>, LoweringError> {
    production
        .attributes()
        .iter()
        .enumerate()
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
                ProductionAttribute::Alias { .. } => ProductionAttribute::Alias { origin },
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
                ProductionAttribute::Format { fragments, .. } => ProductionAttribute::Format {
                    origin,
                    fragments: fragments.clone(),
                },
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
        SemanticTermKind::Map {
            operation,
            arguments,
        } => Ok(DefinitionTerm::typed_map(
            origin,
            lower_sort_ref(term.sort(), names)?,
            *operation,
            arguments
                .iter()
                .map(|argument| lower_term(argument, names, origins))
                .collect::<Result<Vec<_>, _>>()?,
        )),
        SemanticTermKind::List {
            operation,
            arguments,
        } => Ok(DefinitionTerm::list(
            origin,
            lower_sort_ref(term.sort(), names)?,
            *operation,
            arguments
                .iter()
                .map(|argument| lower_term(argument, names, origins))
                .collect::<Result<Vec<_>, _>>()?,
        )),
        SemanticTermKind::Set {
            operation,
            arguments,
        } => Ok(DefinitionTerm::set(
            origin,
            lower_sort_ref(term.sort(), names)?,
            *operation,
            arguments
                .iter()
                .map(|argument| lower_term(argument, names, origins))
                .collect::<Result<Vec<_>, _>>()?,
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
    }
}

fn select_main_module(theory: &SemanticTheory) -> Result<&SemanticModule, LoweringError> {
    let configured = theory
        .modules()
        .iter()
        .filter(|module| module.configuration().is_some())
        .collect::<Vec<_>>();
    match configured.as_slice() {
        [module] => Ok(*module),
        _ => Err(LoweringError::UnsupportedShape {
            node: "main module",
            detail: format!("expected one configured module, found {}", configured.len()),
        }),
    }
}

fn claim(
    names: &mut BTreeMap<String, String>,
    value: String,
    owner: String,
    namespace: &'static str,
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
    push_component(&mut text, &format!("{:?}", id.item_kind()));
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
    push_component(&mut text, &format!("{:?}", id.item_kind()));
    push_component(&mut text, id.disambiguator());
    text
}

fn production_symbol_name(production: &krs_ir::SemanticProduction, owner: &str) -> String {
    if let Some(symbol) = production.explicit_symbol() {
        return lower_camel(symbol.final_component());
    }
    if production.id().item_name() == "__krs_generated_semantic_production" {
        format!("krsGenerated_{}", short_hash(owner))
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
    hex_encode(&digest[..12])
}

fn hex_encode(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut result = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        result.push(char::from(HEX[usize::from(byte >> 4)]));
        result.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    result
}

fn lower_camel(value: &str) -> String {
    let mut characters = value.chars();
    match characters.next() {
        Some(first) => first.to_lowercase().chain(characters).collect(),
        None => String::new(),
    }
}

#[allow(dead_code)]
fn _term_kind_is_exhaustive(kind: &DefinitionTermKind) -> bool {
    matches!(
        kind,
        DefinitionTermKind::Variable { .. }
            | DefinitionTermKind::Application { .. }
            | DefinitionTermKind::Token { .. }
            | DefinitionTermKind::KSequence { .. }
            | DefinitionTermKind::Map { .. }
            | DefinitionTermKind::List { .. }
            | DefinitionTermKind::Rewrite { .. }
    )
}

#[cfg(test)]
mod tests {
    use krs_ir::{ExplicitSymbol, ItemKind, StableItemId};

    use super::stable_symbol_text;

    fn item(module: &str, name: &str, kind: ItemKind) -> StableItemId {
        krs_ir::testing::item_in(
            krs_ir::testing::package("KRS-STABLE-NAMES", "fixture"),
            module,
            name,
            kind,
        )
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
