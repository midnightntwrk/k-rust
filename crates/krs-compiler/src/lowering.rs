use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt;

use krs_ir::{
    CellDeclaration, ConfigurationSentence, DefinitionIr, DefinitionModule, DefinitionSentence,
    DefinitionSortRef, DefinitionTerm, DefinitionTermKind, DefinitionValidationError,
    InitializerDeclaration, IrIdentityError, LabelId, LabelIdentity, NodeOrigin,
    OriginFrame, ProductionItem, ProductionSentence, RuleSentence, SemanticConfiguration,
    SemanticModule, SemanticProduction, SemanticSortRef, SemanticTerm, SemanticTermKind,
    SemanticTheory, SemanticVariable, SourceMapKey, StableItemId, SubsortSentence, SymbolId,
    SymbolIdentity, SymbolKind, SyntaxSortSentence, TransformationOriginKind,
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
    /// The frozen M2 subset does not contain this otherwise-valid semantic shape.
    UnsupportedShape {
        /// Stable node family.
        node: &'static str,
        /// Deterministic explanatory detail.
        detail: String,
    },
    /// Authored syntax is not representable by the M2 production-template subset.
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
                write!(formatter, "unsupported M2 {node} shape: {detail}")
            }
            Self::InvalidProductionTemplate { production, detail } => {
                write!(formatter, "invalid syntax template for {production:?}: {detail}")
            }
            Self::InvalidEmittedName { role, value } => {
                write!(formatter, "{role} name {value:?} is not canonical K syntax")
            }
            Self::NameCollision {
                namespace,
                value,
                first,
                second,
            } => write!(
                formatter,
                "{namespace} name collision for {value:?} between {first} and {second}"
            ),
            Self::SourceMapCollision(key) => {
                write!(formatter, "generated source-map key collision at {:?}", key.as_str())
            }
            Self::InvalidGeneratedIdentity(detail) => formatter.write_str(detail),
            Self::InvalidDefinition(error) => write!(formatter, "invalid lowered Definition IR: {error}"),
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

/// Deterministically lowers the frozen M2 semantic subset to Definition IR.
///
/// One preflight pass assigns every module, symbol, and label identity and
/// rejects collisions before [`DefinitionIr`] construction. Every copied node
/// receives a fresh source-map key and an honest range-free `definition_ir`
/// transformation frame.
///
/// # Errors
///
/// Returns [`LoweringError`] for unsupported M2 shapes, invalid templates or
/// names, naming/source-map collisions, or a failed Definition IR invariant.
pub fn lower_semantic_theory(theory: &SemanticTheory) -> Result<LoweredDefinition, LoweringError> {
    validate_m2_shape(theory)?;
    let names = NamingPass::run(theory)?;
    let mut origins = OriginPass::default();
    let mut modules = theory.modules().iter().collect::<Vec<_>>();
    modules.sort_by(|left, right| left.id().cmp(right.id()));
    let lowered_modules = modules
        .into_iter()
        .map(|module| lower_module(module, &names, &mut origins))
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
    cells: BTreeMap<String, SymbolIdentity>,
    initializers: BTreeMap<String, SymbolIdentity>,
    rules: BTreeMap<StableItemId, LabelIdentity>,
}

impl NamingPass {
    #[allow(clippy::too_many_lines)]
    fn run(theory: &SemanticTheory) -> Result<Self, LoweringError> {
        let mut pass = Self::default();
        let mut identities = BTreeMap::<String, String>::new();
        let mut emitted = BTreeMap::<String, String>::new();
        let mut modules = BTreeMap::<String, String>::new();

        for module in theory.modules() {
            validate_module_name(module.id().as_str())?;
            claim(
                &mut modules,
                module.id().as_str().to_owned(),
                format!("semantic module {}", module.id().as_str()),
                "module",
            )?;
            pass.modules.insert(module.id().clone(), module.id().clone());
            for sort in module.sorts() {
                let owner = stable_item_text(sort.id());
                let id = SymbolId::new(format!("sort:{}", hex_encode(owner.as_bytes())))?;
                let name = sort.id().item_name().to_owned();
                validate_sort_name(&name)?;
                claim(&mut identities, id.as_str().to_owned(), owner.clone(), "symbol ID")?;
                claim(&mut emitted, name.clone(), owner, "emitted symbol")?;
                pass.sorts.insert(
                    sort.id().clone(),
                    SymbolIdentity::new(id, name, SymbolKind::Sort)?,
                );
            }
            for production in module.productions() {
                // Template validation belongs to this preflight, before any
                // Definition value exists.
                parse_template(production)?;
                let owner = stable_item_text(production.id());
                let id = SymbolId::new(format!("production:{}", hex_encode(owner.as_bytes())))?;
                let name = lower_camel(production.id().item_name());
                validate_label_name("production symbol", &name)?;
                claim(&mut identities, id.as_str().to_owned(), owner.clone(), "symbol ID")?;
                claim(&mut emitted, name.clone(), owner, "emitted symbol")?;
                pass.productions.insert(
                    production.id().clone(),
                    SymbolIdentity::new(id, name, SymbolKind::Production)?,
                );
            }
            if let Some(configuration) = module.configuration() {
                let config_owner = format!("configuration {}", configuration.id().as_str());
                let cell_id = SymbolId::new(format!(
                    "cell:{}",
                    hex_encode(configuration.cell().id().as_str().as_bytes())
                ))?;
                let cell_name = configuration.cell().name().to_owned();
                validate_cell_name(&cell_name)?;
                claim(
                    &mut identities,
                    cell_id.as_str().to_owned(),
                    config_owner.clone(),
                    "symbol ID",
                )?;
                claim(
                    &mut emitted,
                    cell_name.clone(),
                    config_owner.clone(),
                    "emitted symbol",
                )?;
                pass.cells.insert(
                    configuration.id().as_str().to_owned(),
                    SymbolIdentity::new(cell_id, cell_name.clone(), SymbolKind::Cell)?,
                );

                let initializer_id = SymbolId::new(format!(
                    "initializer:{}",
                    hex_encode(configuration.initializer().id().as_str().as_bytes())
                ))?;
                let initializer_name = format!("init{}Cell", upper_camel(&cell_name));
                validate_label_name("initializer", &initializer_name)?;
                claim(
                    &mut identities,
                    initializer_id.as_str().to_owned(),
                    config_owner.clone(),
                    "symbol ID",
                )?;
                claim(
                    &mut emitted,
                    initializer_name.clone(),
                    config_owner,
                    "emitted symbol",
                )?;
                pass.initializers.insert(
                    configuration.id().as_str().to_owned(),
                    SymbolIdentity::new(
                        initializer_id,
                        initializer_name,
                        SymbolKind::Initializer,
                    )?,
                );
            }
            for rule in module.rules() {
                let owner = stable_item_text(rule.id());
                let id = LabelId::new(format!("rule:{}", hex_encode(owner.as_bytes())))?;
                let name = format!("krsRule_{}", short_hash(&owner));
                validate_label_name("rule label", &name)?;
                claim(&mut identities, id.as_str().to_owned(), owner.clone(), "label ID")?;
                claim(&mut emitted, name.clone(), owner, "emitted name")?;
                pass.rules
                    .insert(rule.id().clone(), LabelIdentity::new(id, name)?);
            }
        }
        Ok(pass)
    }

    fn sort(&self, id: &StableItemId) -> Result<SymbolIdentity, LoweringError> {
        self.sorts.get(id).cloned().ok_or_else(|| LoweringError::UnsupportedShape {
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

fn lower_module(
    module: &SemanticModule,
    names: &NamingPass,
    origins: &mut OriginPass,
) -> Result<DefinitionModule, LoweringError> {
    let mut sentences = Vec::new();
    let mut sorts = module.sorts().iter().collect::<Vec<_>>();
    sorts.sort_by(|left, right| left.id().cmp(right.id()));
    for sort in sorts {
        sentences.push(DefinitionSentence::SyntaxSort(SyntaxSortSentence::new(
            origins.lower(sort.origin(), "syntax-sort", Some(sort.id()), None)?,
            names.sort(sort.id())?,
        )?));
        let mut parents = sort.direct_parents().to_vec();
        parents.sort();
        parents.dedup();
        for parent in parents {
            sentences.push(DefinitionSentence::Subsort(SubsortSentence::new(
                origins.lower(
                    sort.origin(),
                    "subsort",
                    Some(sort.id()),
                    Some(&stable_item_text(&parent)),
                )?,
                names.sort_id(sort.id())?,
                names.sort_id(&parent)?,
            )));
        }
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
            names.sort_id(production.result_sort())?,
            parse_template(production)?,
        )?));
    }

    if let Some(configuration) = module.configuration() {
        sentences.push(lower_configuration(configuration, names, origins)?);
    }

    let mut rules = module.rules().iter().collect::<Vec<_>>();
    rules.sort_by(|left, right| left.id().cmp(right.id()));
    for rule in rules {
        let variables = lower_variables(rule.variables(), names)?;
        let body = lower_term(rule.body(), names, origins)?;
        let label = names.rules.get(rule.id()).cloned().ok_or_else(|| {
            LoweringError::UnsupportedShape {
                node: "rule",
                detail: format!("no naming entry for {:?}", rule.id()),
            }
        })?;
        sentences.push(DefinitionSentence::Rule(RuleSentence::new(
            origins.lower(rule.origin(), "rule", Some(rule.id()), None)?,
            label,
            rule.kind(),
            variables,
            body,
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
        sentences,
    ))
}

fn lower_configuration(
    configuration: &SemanticConfiguration,
    names: &NamingPass,
    origins: &mut OriginPass,
) -> Result<DefinitionSentence, LoweringError> {
    let key = configuration.id().as_str();
    let cell_symbol = names.cells.get(key).cloned().ok_or_else(|| {
        LoweringError::UnsupportedShape {
            node: "configuration cell",
            detail: format!("no naming entry for {key:?}"),
        }
    })?;
    let initializer_symbol = names.initializers.get(key).cloned().ok_or_else(|| {
        LoweringError::UnsupportedShape {
            node: "configuration initializer",
            detail: format!("no naming entry for {key:?}"),
        }
    })?;
    let cell = CellDeclaration::new(
        origins.lower(configuration.cell().origin(), "cell", None, Some(key))?,
        cell_symbol,
        lower_sort_ref(configuration.cell().sort(), names)?,
    )?;
    let initializer = InitializerDeclaration::new(
        origins.lower(
            configuration.initializer().origin(),
            "initializer",
            None,
            Some(key),
        )?,
        initializer_symbol,
        lower_variables(configuration.initializer().variables(), names)?,
        lower_term(configuration.initializer().body(), names, origins)?,
    )?;
    Ok(DefinitionSentence::Configuration(ConfigurationSentence::new(
        origins.lower(configuration.origin(), "configuration", None, Some(key))?,
        cell,
        initializer,
    )))
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
                names.sort_id(variable.sort())?,
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

fn lower_term(
    term: &SemanticTerm,
    names: &NamingPass,
    origins: &mut OriginPass,
) -> Result<DefinitionTerm, LoweringError> {
    let origin = origins.lower(term.origin(), "term", None, None)?;
    match term.kind() {
        SemanticTermKind::Variable { variable } => {
            let SemanticSortRef::Declared(sort) = term.sort() else {
                return Err(LoweringError::UnsupportedShape {
                    node: "variable",
                    detail: "variables over builtin KSequence are not in M2".to_owned(),
                });
            };
            Ok(DefinitionTerm::variable(
                origin,
                names.sort_id(sort)?,
                variable.clone(),
            ))
        }
        SemanticTermKind::Application {
            production,
            arguments,
        } => {
            let SemanticSortRef::Declared(sort) = term.sort() else {
                return Err(LoweringError::UnsupportedShape {
                    node: "application",
                    detail: "applications must have a declared result sort".to_owned(),
                });
            };
            Ok(DefinitionTerm::application(
                origin,
                names.sort_id(sort)?,
                names.production(production)?.id().clone(),
                arguments
                    .iter()
                    .map(|argument| lower_term(argument, names, origins))
                    .collect::<Result<Vec<_>, _>>()?,
            ))
        }
        SemanticTermKind::Token { value } => {
            let SemanticSortRef::Declared(sort) = term.sort() else {
                return Err(LoweringError::UnsupportedShape {
                    node: "token",
                    detail: "tokens must have a declared result sort".to_owned(),
                });
            };
            Ok(DefinitionTerm::token(origin, names.sort_id(sort)?, value.clone())?)
        }
        SemanticTermKind::KSequence { item_sort, items } => Ok(DefinitionTerm::k_sequence(
            origin,
            names.sort_id(item_sort)?,
            items
                .iter()
                .map(|item| lower_term(item, names, origins))
                .collect::<Result<Vec<_>, _>>()?,
        )),
        SemanticTermKind::Rewrite { from, to } => {
            let SemanticSortRef::Declared(sort) = term.sort() else {
                return Err(LoweringError::UnsupportedShape {
                    node: "rewrite",
                    detail: "rewrites over builtin KSequence are not in M2".to_owned(),
                });
            };
            Ok(DefinitionTerm::rewrite(
                origin,
                names.sort_id(sort)?,
                lower_term(from, names, origins)?,
                lower_term(to, names, origins)?,
            )?)
        }
    }
}

fn validate_m2_shape(theory: &SemanticTheory) -> Result<(), LoweringError> {
    let sorts = theory
        .modules()
        .iter()
        .flat_map(SemanticModule::sorts)
        .collect::<Vec<_>>();
    if sorts.len() != 3 {
        return Err(LoweringError::UnsupportedShape {
            node: "sort graph",
            detail: format!("expected exactly KItem, KResult, and one object sort; found {}", sorts.len()),
        });
    }
    let named = |name: &str| {
        sorts
            .iter()
            .copied()
            .filter(|sort| sort.id().item_name() == name)
            .collect::<Vec<_>>()
    };
    let k_items = named("KItem");
    let k_results = named("KResult");
    if k_items.len() != 1 || k_results.len() != 1 {
        return Err(LoweringError::UnsupportedShape {
            node: "sort graph",
            detail: "expected unique KItem and KResult declarations".to_owned(),
        });
    }
    let k_item = k_items[0];
    let k_result = k_results[0];
    let objects = sorts
        .iter()
        .copied()
        .filter(|sort| sort.id() != k_item.id() && sort.id() != k_result.id())
        .collect::<Vec<_>>();
    let object = objects[0];
    if !k_item.direct_parents().is_empty()
        || k_result.direct_parents() != [k_item.id().clone()]
        || object.direct_parents() != [k_result.id().clone()]
    {
        return Err(LoweringError::UnsupportedShape {
            node: "sort graph",
            detail: format!(
                "expected exact {} < KResult < KItem chain",
                object.id().item_name()
            ),
        });
    }
    for module in theory.modules() {
        if let Some(configuration) = module.configuration()
            && (configuration.cell().name() != "k"
                || configuration.cell().sort() != &SemanticSortRef::k_sequence()
                || !matches!(
                    configuration.initializer().body().kind(),
                    SemanticTermKind::KSequence { .. }
                ))
        {
            return Err(LoweringError::UnsupportedShape {
                node: "configuration",
                detail: "M2 requires one <k> cell of KSequence initialized by a KSequence"
                    .to_owned(),
            });
        }
        for rule in module.rules() {
            if rule.kind() != krs_ir::SentenceKind::Transition {
                return Err(LoweringError::UnsupportedShape {
                    node: "sentence",
                    detail: format!("only unconditional transition rules are supported, found {:?}", rule.kind()),
                });
            }
        }
    }
    Ok(())
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

fn parse_template(production: &SemanticProduction) -> Result<Vec<ProductionItem>, LoweringError> {
    let mut items = Vec::new();
    let mut holes = BTreeSet::new();
    let mut argument = 0_usize;
    let source = production.syntax();
    let mut index = 0_usize;
    while index < source.len() {
        let character = source[index..].chars().next().expect("index is on character boundary");
        if character.is_whitespace() {
            index += character.len_utf8();
            continue;
        }
        if character == '{' {
            let remainder = &source[index + 1..];
            let Some(close) = remainder.find('}') else {
                return template_error(production, "unclosed `{` placeholder");
            };
            let name = &remainder[..close];
            if !is_field_name(name) {
                return template_error(production, format!("invalid placeholder name {name:?}"));
            }
            if !holes.insert(name.to_owned()) {
                return template_error(production, format!("repeated placeholder {name:?}"));
            }
            let Some(sort) = production.argument_sorts().get(argument) else {
                return template_error(production, "more placeholders than constructor fields");
            };
            items.push(ProductionItem::non_terminal(SymbolId::new(format!(
                "sort:{}",
                hex_encode(stable_item_text(sort).as_bytes())
            ))?));
            argument += 1;
            index += close + 2;
            continue;
        }
        if character == '}' {
            return template_error(production, "unmatched `}` placeholder delimiter");
        }

        let start = index;
        let word = character.is_alphanumeric() || character == '_';
        let singleton = matches!(character, '(' | ')' | '[' | ']' | ',' | ';');
        index += character.len_utf8();
        if !singleton {
            while index < source.len() {
                let next = source[index..].chars().next().expect("character boundary");
                let next_word = next.is_alphanumeric() || next == '_';
                if next.is_whitespace()
                    || matches!(next, '{' | '}' | '(' | ')' | '[' | ']' | ',' | ';')
                    || next_word != word
                {
                    break;
                }
                index += next.len_utf8();
            }
        }
        items.push(ProductionItem::terminal(&source[start..index])?);
    }
    if argument != production.argument_sorts().len() {
        return template_error(
            production,
            format!(
                "template has {argument} placeholders for {} constructor fields",
                production.argument_sorts().len()
            ),
        );
    }
    if items.is_empty() {
        return template_error(production, "template contains no grammar items");
    }
    Ok(items)
}

fn template_error<T>(
    production: &SemanticProduction,
    detail: impl Into<String>,
) -> Result<T, LoweringError> {
    Err(LoweringError::InvalidProductionTemplate {
        production: Box::new(production.id().clone()),
        detail: detail.into(),
    })
}

fn claim(
    names: &mut BTreeMap<String, String>,
    value: String,
    owner: String,
    namespace: &'static str,
) -> Result<(), LoweringError> {
    if let Some(first) = names.insert(value.clone(), owner.clone()) {
        return Err(LoweringError::NameCollision {
            namespace,
            value,
            first,
            second: owner,
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
        && value.bytes().all(|byte| byte.is_ascii_alphanumeric() || byte == b'_');
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
        .is_some_and(|byte| byte.is_ascii_alphabetic())
        && value.bytes().all(|byte| byte.is_ascii_alphanumeric() || byte == b'_');
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

fn upper_camel(value: &str) -> String {
    let mut characters = value.chars();
    match characters.next() {
        Some(first) => first.to_uppercase().chain(characters).collect(),
        None => String::new(),
    }
}

fn is_field_name(value: &str) -> bool {
    value
        .bytes()
        .next()
        .is_some_and(|byte| byte.is_ascii_alphabetic() || byte == b'_')
        && value
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
}

#[allow(dead_code)]
fn _term_kind_is_exhaustive(kind: &DefinitionTermKind) -> bool {
    matches!(
        kind,
        DefinitionTermKind::Variable { .. }
            | DefinitionTermKind::Application { .. }
            | DefinitionTermKind::Token { .. }
            | DefinitionTermKind::KSequence { .. }
            | DefinitionTermKind::Rewrite { .. }
    )
}
