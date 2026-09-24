use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt;

use krs_ir::{
    ApplicationRef, BuiltinOperation, BuiltinSort, CellAttribute, CellCollectionType,
    CellContentFrame, CellMultiplicity, CellPost, ConfigurationRoot, Descriptor,
    DescriptorApplicationRef, DescriptorBundle, DescriptorCellDeclaration, DescriptorCellField,
    DescriptorCellIdentity, DescriptorDeclaration, DescriptorFixedConfiguration,
    DescriptorInitializerCell, DescriptorInitializerStateTerm, DescriptorPayload,
    DescriptorProduction, DescriptorProductionAttribute, DescriptorProductionItem,
    DescriptorProductionOwner, DescriptorRuleCells, DescriptorRuleLabel, DescriptorSortRef,
    DescriptorTerm, DescriptorTermArgument, FixedCell, FixedCellClause, FixedCellPattern,
    FixedConfiguration, FixedConfigurationPattern, FixedConfigurationRewrite,
    FixedConfigurationVariable, FixedInitializerCell, GeneratedProductionKind, GrammarDescriptor,
    GroupAssociativitySentence, IrIdentityError, ItemKind, ListOperation, MapOperation, ModuleId,
    NodeOrigin, OriginFrame, PackageId, PrecedenceRelation, ProductionAttribute, ProductionFieldId,
    ProtocolCellContent, ProtocolContextAliasBindingKind, ProtocolInitializerCellContent,
    ProtocolInitializerStateTerm, ProtocolMapBody, ProtocolRuleBindingKind, ProtocolRuleFrame,
    ProtocolRuleMapBody, ProtocolRuleStateTerm, ProvenanceKey, SemanticConfiguration,
    SemanticContextAlias, SemanticId, SemanticModule, SemanticProduction, SemanticProductionItem,
    SemanticRule, SemanticRuleCondition, SemanticRuleLabel, SemanticRulePriority,
    SemanticSimplification, SemanticSimplificationPriority, SemanticSort, SemanticSortRef,
    SemanticSubsort, SemanticTerm, SemanticTheory, SemanticValidationError, SemanticVariable,
    SetOperation, SourceMapKey, StableItemId, StructuredRuleDescriptor, TransformationOriginKind,
    generated_production_id,
};
use krs_syntax::ProvenanceRole;
use sha2::{Digest, Sha256};

use crate::{AnalysisError, AnalysisErrorKind};

/// Deterministic open-sort relation computed from a stable descriptor bundle.
///
/// Direct edges remain distinct from their transitive closure. Constructor
/// membership includes the directly declared sort and every transitive parent,
/// and diamonds are deduplicated by stable identity.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OpenSortAnalysis {
    direct_parents: BTreeMap<StableItemId, Vec<StableItemId>>,
    transitive_parents: BTreeMap<StableItemId, Vec<StableItemId>>,
    member_sorts: BTreeMap<StableItemId, Vec<StableItemId>>,
    constructors_by_sort: BTreeMap<StableItemId, Vec<StableItemId>>,
}

impl OpenSortAnalysis {
    /// Returns direct `subsort -> supersort` edges in canonical order.
    #[must_use]
    pub const fn direct_parents(&self) -> &BTreeMap<StableItemId, Vec<StableItemId>> {
        &self.direct_parents
    }

    /// Returns strict transitive parents for every sort in canonical order.
    #[must_use]
    pub const fn transitive_parents(&self) -> &BTreeMap<StableItemId, Vec<StableItemId>> {
        &self.transitive_parents
    }

    /// Returns every direct or inherited sort containing each constructor.
    #[must_use]
    pub const fn member_sorts(&self) -> &BTreeMap<StableItemId, Vec<StableItemId>> {
        &self.member_sorts
    }

    /// Returns direct and inherited constructors visible through each sort.
    #[must_use]
    pub const fn constructors_by_sort(&self) -> &BTreeMap<StableItemId, Vec<StableItemId>> {
        &self.constructors_by_sort
    }
}

/// Computes the target-neutral open-sort relation from stable descriptors.
///
/// # Errors
///
/// Rejects duplicate declaration IDs, absent/wrongly-kinded sort references,
/// and direct or indirect subsort cycles. Rules do not participate in this
/// deliberately small analysis.
#[allow(clippy::too_many_lines)]
pub fn analyze_open_sorts(bundle: &DescriptorBundle) -> Result<OpenSortAnalysis, AnalysisError> {
    let mut kinds = BTreeMap::new();
    for descriptor in &bundle.descriptors {
        if kinds
            .insert(descriptor.id.clone(), descriptor.id.item_kind())
            .is_some()
        {
            return Err(AnalysisError::new(
                AnalysisErrorKind::DuplicateItemId,
                format!("duplicate stable item `{}`", display_item(&descriptor.id)),
            ));
        }
    }

    let mut direct_parents: BTreeMap<StableItemId, Vec<StableItemId>> = BTreeMap::new();
    let mut constructors = Vec::new();
    for descriptor in &bundle.descriptors {
        match &descriptor.payload {
            DescriptorPayload::Sort(sort) => {
                require_kind(&descriptor.id, ItemKind::Sort, &kinds)?;
                let mut parents = sort.parents.clone();
                parents.sort();
                parents.dedup();
                for parent in &parents {
                    require_kind(parent, ItemKind::Sort, &kinds)?;
                }
                direct_parents
                    .entry(descriptor.id.clone())
                    .or_default()
                    .extend(parents);
            }
            DescriptorPayload::Constructor(constructor) => {
                require_kind(&descriptor.id, ItemKind::Constructor, &kinds)?;
                if let DescriptorSortRef::Declared(sort) = &constructor.sort {
                    require_kind(sort, ItemKind::Sort, &kinds)?;
                    constructors.push((descriptor.id.clone(), sort.clone()));
                }
            }
            DescriptorPayload::StructuredRule(_)
            | DescriptorPayload::FixedConfiguration(_)
            | DescriptorPayload::Cell(_)
            | DescriptorPayload::ConfigurationRule(_)
            | DescriptorPayload::HeadRule(_)
            | DescriptorPayload::ContextAlias(_) => {}
            DescriptorPayload::Grammar(grammar) => match grammar.as_ref() {
                GrammarDescriptor::Production(production) => {
                    if let DescriptorProductionOwner::Constructor { constructor } =
                        &production.owner
                        && let DescriptorApplicationRef::Declared(id) = &constructor.application
                        && let DescriptorSortRef::Declared(sort) = &production.result_sort.sort
                    {
                        constructors.push((id.clone(), sort.clone()));
                    }
                }
                GrammarDescriptor::Subsort {
                    subsort, supersort, ..
                } => {
                    if let (
                        DescriptorSortRef::Declared(subsort),
                        DescriptorSortRef::Declared(supersort),
                    ) = (&subsort.sort, &supersort.sort)
                    {
                        direct_parents
                            .entry(subsort.clone())
                            .or_default()
                            .push(supersort.clone());
                    }
                }
                GrammarDescriptor::Precedence { .. } | GrammarDescriptor::Associativity { .. } => {}
            },
        }
    }

    for parents in direct_parents.values_mut() {
        parents.sort();
        parents.dedup();
    }

    let mut transitive_parents: BTreeMap<StableItemId, Vec<StableItemId>> = BTreeMap::new();
    for sort in direct_parents.keys() {
        let mut visiting = Vec::new();
        let mut closure = BTreeSet::new();
        visit_parents(sort, sort, &direct_parents, &mut visiting, &mut closure)?;
        transitive_parents.insert(sort.clone(), closure.into_iter().collect());
    }

    constructors.sort();
    let mut member_sorts = BTreeMap::new();
    let mut constructors_by_sort = direct_parents
        .keys()
        .cloned()
        .map(|sort| (sort, Vec::new()))
        .collect::<BTreeMap<_, _>>();
    for (constructor, direct_sort) in constructors {
        let mut memberships = BTreeSet::from([direct_sort.clone()]);
        if let Some(parents) = transitive_parents.get(&direct_sort) {
            memberships.extend(parents.iter().cloned());
        }
        let memberships = memberships.into_iter().collect::<Vec<_>>();
        for sort in &memberships {
            let Some(members) = constructors_by_sort.get_mut(sort) else {
                return Err(AnalysisError::new(
                    AnalysisErrorKind::UnresolvedReference,
                    format!("member sort `{}` has no declaration", display_item(sort)),
                ));
            };
            members.push(constructor.clone());
        }
        member_sorts.insert(constructor, memberships);
    }
    for members in constructors_by_sort.values_mut() {
        members.sort();
        members.dedup();
    }

    Ok(OpenSortAnalysis {
        direct_parents,
        transitive_parents,
        member_sorts,
        constructors_by_sort,
    })
}

/// Typed failure at the sole descriptor-bundle to semantic-theory boundary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DescriptorLoweringError {
    /// Two descriptors claim one stable identity.
    DuplicateItemId(Box<StableItemId>),
    /// Lowering requires exactly one selected configuration descriptor.
    ConfigurationCount(usize),
    /// A descriptor payload and stable item kind disagree.
    WrongItemKind {
        /// Offending stable item.
        id: Box<StableItemId>,
        /// Kind required by the payload.
        expected: ItemKind,
        /// Kind present in the item identity.
        actual: ItemKind,
    },
    /// A stable reference names no selected descriptor.
    DanglingReference(Box<StableItemId>),
    /// A reference or term uses a declaration in the wrong namespace.
    ReferenceKindMismatch {
        /// Referenced stable item.
        id: Box<StableItemId>,
        /// Required namespace.
        expected: ItemKind,
        /// Actual namespace.
        actual: ItemKind,
    },
    /// A required parser-keyed origin or reference was absent or unexpected.
    ParserReferenceDisagreement {
        /// Descriptor being lowered.
        id: Box<StableItemId>,
        /// Stable diagnostic detail.
        detail: String,
    },
    /// The term could not be represented structurally.
    InvalidTerm {
        /// Descriptor containing the term.
        id: Box<StableItemId>,
        /// Stable diagnostic detail.
        detail: String,
    },
    /// The descriptor graph is outside the supported shape.
    UnsupportedShape {
        /// Semantic node family.
        node: &'static str,
        /// Stable diagnostic detail.
        detail: String,
    },
    /// Two readable head-rule patterns can match one configuration state.
    OverlappingRules {
        /// First rule in deterministic stable-identity order.
        first: Box<StableItemId>,
        /// Second rule in deterministic stable-identity order.
        second: Box<StableItemId>,
    },
    /// A compiler-generated module, semantic, or source-map identity was invalid.
    InvalidGeneratedIdentity(String),
    /// Whole-theory validation rejected the constructed graph.
    InvalidSemanticTheory(SemanticValidationError),
}

impl fmt::Display for DescriptorLoweringError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DuplicateItemId(id) => write!(formatter, "duplicate stable descriptor {id:?}"),
            Self::ConfigurationCount(count) => write!(
                formatter,
                "descriptor bundle requires exactly one configuration, found {count}"
            ),
            Self::WrongItemKind {
                id,
                expected,
                actual,
            }
            | Self::ReferenceKindMismatch {
                id,
                expected,
                actual,
            } => write!(
                formatter,
                "descriptor reference {id:?} has kind {actual:?}, expected {expected:?}"
            ),
            Self::DanglingReference(id) => {
                write!(formatter, "dangling descriptor reference {id:?}")
            }
            Self::ParserReferenceDisagreement { id, detail } => write!(
                formatter,
                "parser/reference disagreement for {id:?}: {detail}"
            ),
            Self::InvalidTerm { id, detail } => {
                write!(formatter, "invalid descriptor term for {id:?}: {detail}")
            }
            Self::UnsupportedShape { node, detail } => {
                write!(formatter, "unsupported {node}: {detail}")
            }
            Self::OverlappingRules { first, second } => write!(
                formatter,
                "readable rules {first:?} and {second:?} have overlapping left-hand patterns at the same priority; refine a pattern, add disjoint `where` sorts, or mark the fallback `#[k::rule(owise)]`"
            ),
            Self::InvalidGeneratedIdentity(detail) => formatter.write_str(detail),
            Self::InvalidSemanticTheory(error) => error.fmt(formatter),
        }
    }
}

impl Error for DescriptorLoweringError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::InvalidSemanticTheory(error) => Some(error),
            _ => None,
        }
    }
}

impl From<IrIdentityError> for DescriptorLoweringError {
    fn from(error: IrIdentityError) -> Self {
        Self::InvalidGeneratedIdentity(error.to_string())
    }
}

impl From<SemanticValidationError> for DescriptorLoweringError {
    fn from(error: SemanticValidationError) -> Self {
        Self::InvalidSemanticTheory(error)
    }
}

impl From<krs_ir::StateShapeError> for DescriptorLoweringError {
    fn from(error: krs_ir::StateShapeError) -> Self {
        Self::UnsupportedShape {
            node: "fixed configuration",
            detail: error.to_string(),
        }
    }
}

/// Resolves one descriptor bundle into checked target-neutral IR.
///
/// This boundary performs no Cargo work and has no adapter knowledge. Named
/// paths are joined exclusively through their parser-owned [`ProvenanceKey`];
/// there is no short-name lookup or guessed constructor resolution.
///
/// # Errors
///
/// Returns [`DescriptorLoweringError`] for duplicate or dangling identities,
/// wrong descriptor shapes, parser/reference disagreement, malformed terms,
/// invalid generated identities, or a failed whole-theory invariant.
#[allow(clippy::too_many_lines)]
pub fn lower_descriptor_bundle(
    bundle: &DescriptorBundle,
) -> Result<SemanticTheory, DescriptorLoweringError> {
    let mut descriptors = bundle.descriptors.iter().collect::<Vec<_>>();
    descriptors.sort_by(|left, right| left.id.cmp(&right.id));
    let head_rule_ids = descriptors
        .iter()
        .filter(|descriptor| matches!(descriptor.payload, DescriptorPayload::HeadRule(_)))
        .map(|descriptor| descriptor.id.clone())
        .collect::<BTreeSet<_>>();
    let mut declarations = BTreeMap::new();
    for descriptor in &descriptors {
        descriptor.validate_grammar_contract().map_err(|error| {
            DescriptorLoweringError::ParserReferenceDisagreement {
                id: Box::new(descriptor.id.clone()),
                detail: error.to_string(),
            }
        })?;
        descriptor.validate_state_contract().map_err(|error| {
            DescriptorLoweringError::ParserReferenceDisagreement {
                id: Box::new(descriptor.id.clone()),
                detail: error.to_string(),
            }
        })?;
        if declarations
            .insert(descriptor.id.clone(), *descriptor)
            .is_some()
        {
            return Err(DescriptorLoweringError::DuplicateItemId(Box::new(
                descriptor.id.clone(),
            )));
        }
        require_payload_kind(descriptor)?;
    }
    let configurations = descriptors
        .iter()
        .filter(|descriptor| matches!(descriptor.payload, DescriptorPayload::FixedConfiguration(_)))
        .count();
    if configurations != 1 {
        return Err(DescriptorLoweringError::ConfigurationCount(configurations));
    }

    validate_all_stable_references(&descriptors, &declarations)?;
    let semantic_sort_parents = build_semantic_sort_parents(&descriptors);
    let production_catalog = build_production_catalog(&descriptors)?;
    let mut declaration_metadata = bundle
        .declarations
        .iter()
        .cloned()
        .map(|declaration| (declaration.id().clone(), declaration))
        .collect::<BTreeMap<_, _>>();
    for descriptor in &descriptors {
        declaration_metadata
            .entry(descriptor.id.clone())
            .or_insert_with(|| {
                DescriptorDeclaration::new(
                    descriptor.id.clone(),
                    krs_ir::RustVisibility::Inherited,
                    None,
                )
            });
    }

    let mut packages = BTreeMap::<PackageId, Vec<&Descriptor>>::new();
    for descriptor in descriptors {
        packages
            .entry(descriptor.id.package().clone())
            .or_default()
            .push(descriptor);
    }
    let module_ids = packages
        .keys()
        .map(|package| Ok((package.clone(), ModuleId::new(package.k_namespace())?)))
        .collect::<Result<BTreeMap<_, _>, DescriptorLoweringError>>()?;
    let declaration_catalog = DeclarationCatalog {
        descriptors: &declarations,
        metadata: &declaration_metadata,
    };
    let mut modules = Vec::with_capacity(packages.len());
    for (package, package_descriptors) in packages {
        modules.push(lower_package_module(
            &package,
            &package_descriptors,
            &module_ids,
            &declaration_catalog,
            &semantic_sort_parents,
            &production_catalog,
        )?);
    }
    modules.sort_by(|left, right| left.id().cmp(right.id()));
    if let Some((first, second)) = crate::overlap::first_head_rule_overlap(&modules, &head_rule_ids)
    {
        return Err(DescriptorLoweringError::OverlappingRules {
            first: Box::new(first),
            second: Box::new(second),
        });
    }
    Ok(SemanticTheory::new(modules)?)
}

fn require_payload_kind(descriptor: &Descriptor) -> Result<(), DescriptorLoweringError> {
    let expected = match &descriptor.payload {
        DescriptorPayload::Sort(_) => ItemKind::Sort,
        DescriptorPayload::Constructor(_) => ItemKind::Constructor,
        DescriptorPayload::FixedConfiguration(_) => ItemKind::Configuration,
        DescriptorPayload::Grammar(_) => ItemKind::Grammar,
        DescriptorPayload::StructuredRule(rule) => match rule.sentence_kind {
            krs_ir::SentenceKind::Transition => ItemKind::Rule,
            krs_ir::SentenceKind::Equation => ItemKind::Equation,
            krs_ir::SentenceKind::Simplification => ItemKind::Simplification,
            krs_ir::SentenceKind::Alias => ItemKind::Alias,
            krs_ir::SentenceKind::Claim => ItemKind::Claim,
        },
        DescriptorPayload::Cell(_) => ItemKind::Cell,
        DescriptorPayload::ConfigurationRule(rule) => match rule.sentence_kind {
            krs_ir::SentenceKind::Transition => ItemKind::Rule,
            krs_ir::SentenceKind::Equation => ItemKind::Equation,
            krs_ir::SentenceKind::Simplification => ItemKind::Simplification,
            krs_ir::SentenceKind::Alias => ItemKind::Alias,
            krs_ir::SentenceKind::Claim => ItemKind::Claim,
        },
        DescriptorPayload::HeadRule(rule) => match rule.sentence_kind {
            krs_ir::SentenceKind::Transition => ItemKind::Rule,
            krs_ir::SentenceKind::Equation => ItemKind::Equation,
            krs_ir::SentenceKind::Simplification => ItemKind::Simplification,
            krs_ir::SentenceKind::Alias => ItemKind::Alias,
            krs_ir::SentenceKind::Claim => ItemKind::Claim,
        },
        DescriptorPayload::ContextAlias(_) => ItemKind::ContextAlias,
    };
    let actual = descriptor.id.item_kind();
    if actual == expected {
        Ok(())
    } else {
        Err(DescriptorLoweringError::WrongItemKind {
            id: Box::new(descriptor.id.clone()),
            expected,
            actual,
        })
    }
}

fn validate_all_stable_references(
    descriptors: &[&Descriptor],
    declarations: &BTreeMap<StableItemId, &Descriptor>,
) -> Result<(), DescriptorLoweringError> {
    for descriptor in descriptors {
        match &descriptor.payload {
            DescriptorPayload::Sort(sort) => {
                for parent in &sort.parents {
                    require_descriptor(parent, ItemKind::Sort, declarations)?;
                }
            }
            DescriptorPayload::Constructor(constructor) => {
                validate_sort_ref(&constructor.sort, declarations)?;
                for field in &constructor.fields {
                    let sort = field.sort.as_ref().ok_or_else(|| {
                        DescriptorLoweringError::UnsupportedShape {
                            node: "constructor field",
                            detail: format!(
                                "field {:?} on {:?} has no resolved sort",
                                field.name, descriptor.id
                            ),
                        }
                    })?;
                    validate_sort_ref(sort, declarations)?;
                }
            }
            DescriptorPayload::Grammar(grammar) => {
                validate_grammar_references(grammar, declarations)?;
            }
            DescriptorPayload::StructuredRule(rule) => {
                validate_structured_rule_references(rule, declarations)?;
            }
            DescriptorPayload::FixedConfiguration(configuration) => {
                validate_fixed_configuration_references(configuration, declarations)?;
            }
            DescriptorPayload::Cell(declaration) => {
                validate_cell_declaration_references(declaration, declarations)?;
            }
            DescriptorPayload::ConfigurationRule(rule) => {
                require_descriptor(
                    &rule.subject_configuration.configuration,
                    ItemKind::Configuration,
                    declarations,
                )?;
                require_descriptor(
                    &rule.result_configuration.configuration,
                    ItemKind::Configuration,
                    declarations,
                )?;
                validate_configuration_rule_references(rule, declarations)?;
            }
            DescriptorPayload::HeadRule(rule) => {
                require_descriptor(&rule.configuration, ItemKind::Configuration, declarations)?;
                if let Some(head_sort) = &rule.head_sort {
                    validate_sort_ref(&head_sort.sort, declarations)?;
                }
                for binding in &rule.bindings {
                    if let Some(refinement) = &binding.refinement {
                        validate_sort_ref(&refinement.sort, declarations)?;
                    }
                }
            }
            DescriptorPayload::ContextAlias(alias) => {
                require_descriptor(
                    &alias.configuration.configuration,
                    ItemKind::Configuration,
                    declarations,
                )?;
                validate_rule_cells_references(&alias.pattern, declarations)?;
            }
        }
    }
    Ok(())
}

fn require_descriptor<'a>(
    id: &StableItemId,
    expected: ItemKind,
    declarations: &'a BTreeMap<StableItemId, &Descriptor>,
) -> Result<&'a Descriptor, DescriptorLoweringError> {
    let descriptor = declarations
        .get(id)
        .copied()
        .ok_or_else(|| DescriptorLoweringError::DanglingReference(Box::new(id.clone())))?;
    let actual = descriptor.id.item_kind();
    if actual != expected {
        return Err(DescriptorLoweringError::ReferenceKindMismatch {
            id: Box::new(id.clone()),
            expected,
            actual,
        });
    }
    Ok(descriptor)
}

fn validate_sort_ref(
    sort: &DescriptorSortRef,
    declarations: &BTreeMap<StableItemId, &Descriptor>,
) -> Result<(), DescriptorLoweringError> {
    if let DescriptorSortRef::Declared(id) = sort {
        require_descriptor(id, ItemKind::Sort, declarations)?;
    }
    Ok(())
}

fn validate_application_ref(
    application: &DescriptorApplicationRef,
    declarations: &BTreeMap<StableItemId, &Descriptor>,
) -> Result<(), DescriptorLoweringError> {
    if let DescriptorApplicationRef::Declared(id) = application {
        require_descriptor(id, ItemKind::Constructor, declarations)?;
    }
    Ok(())
}

fn validate_grammar_references(
    grammar: &GrammarDescriptor,
    declarations: &BTreeMap<StableItemId, &Descriptor>,
) -> Result<(), DescriptorLoweringError> {
    match grammar {
        GrammarDescriptor::Production(production) => {
            match &production.owner {
                DescriptorProductionOwner::Constructor { constructor } => {
                    validate_application_ref(&constructor.application, declarations)?;
                }
                DescriptorProductionOwner::TokenSort { sort }
                | DescriptorProductionOwner::BracketSort { sort } => {
                    validate_sort_ref(&sort.sort, declarations)?;
                }
            }
            validate_sort_ref(&production.result_sort.sort, declarations)?;
            for item in &production.items {
                if let DescriptorProductionItem::NonTerminal { sort, .. } = item {
                    validate_sort_ref(&sort.sort, declarations)?;
                }
            }
            for attribute in &production.attributes {
                if let DescriptorProductionAttribute::Strictness { result_sort, .. } = attribute {
                    validate_sort_ref(&result_sort.sort, declarations)?;
                }
            }
        }
        GrammarDescriptor::Subsort {
            subsort, supersort, ..
        } => {
            validate_sort_ref(&subsort.sort, declarations)?;
            validate_sort_ref(&supersort.sort, declarations)?;
        }
        GrammarDescriptor::Precedence { .. } | GrammarDescriptor::Associativity { .. } => {}
    }
    Ok(())
}

fn validate_structured_rule_references(
    rule: &StructuredRuleDescriptor,
    declarations: &BTreeMap<StableItemId, &Descriptor>,
) -> Result<(), DescriptorLoweringError> {
    validate_sort_ref(&rule.subject_sort.sort, declarations)?;
    validate_sort_ref(&rule.result_sort.sort, declarations)?;
    validate_structured_term_references(&rule.subject, declarations)?;
    validate_structured_term_references(&rule.result, declarations)?;
    if let Some(requires) = &rule.requires {
        validate_structured_term_references(&requires.term, declarations)?;
    }
    Ok(())
}

fn validate_structured_term_references(
    term: &DescriptorTerm,
    declarations: &BTreeMap<StableItemId, &Descriptor>,
) -> Result<(), DescriptorLoweringError> {
    if let DescriptorTerm::Application {
        reference,
        arguments,
        ..
    } = term
    {
        validate_application_ref(&reference.application, declarations)?;
        for argument in arguments {
            let value = match argument {
                DescriptorTermArgument::Positional { value }
                | DescriptorTermArgument::Named { value, .. } => value,
            };
            validate_structured_term_references(value, declarations)?;
        }
    }
    Ok(())
}

fn validate_fixed_configuration_references(
    configuration: &DescriptorFixedConfiguration,
    declarations: &BTreeMap<StableItemId, &Descriptor>,
) -> Result<(), DescriptorLoweringError> {
    validate_cell_declaration_references(&configuration.declaration, declarations)?;
    for variable in &configuration.initializer.variables {
        validate_sort_ref(&variable.sort.sort, declarations)?;
    }
    for cell in &configuration.initializer.cells {
        validate_initializer_cell_references(cell, declarations)?;
    }
    Ok(())
}

fn validate_cell_declaration_references(
    declaration: &DescriptorCellDeclaration,
    declarations: &BTreeMap<StableItemId, &Descriptor>,
) -> Result<(), DescriptorLoweringError> {
    for field in &declaration.fields {
        match &field.content {
            ProtocolCellContent::Leaf { sort, .. } => {
                validate_sort_ref(&sort.sort, declarations)?;
            }
            ProtocolCellContent::Nested { declaration } => {
                require_descriptor(&declaration.declaration, ItemKind::Cell, declarations)?;
            }
        }
    }
    Ok(())
}

fn validate_initializer_cell_references(
    cell: &DescriptorInitializerCell,
    declarations: &BTreeMap<StableItemId, &Descriptor>,
) -> Result<(), DescriptorLoweringError> {
    let declared = require_cell_field(&cell.field.cell, declarations)?;
    match (&cell.content, &declared.content) {
        (ProtocolInitializerCellContent::Leaf { value, .. }, ProtocolCellContent::Leaf { .. }) => {
            validate_initializer_state_references(value, declarations)
        }
        (
            ProtocolInitializerCellContent::Nested {
                declaration,
                children,
            },
            ProtocolCellContent::Nested {
                declaration: declared,
            },
        ) => {
            if declaration.declaration != declared.declaration {
                return Err(DescriptorLoweringError::ParserReferenceDisagreement {
                    id: Box::new(cell.field.cell.owner.clone()),
                    detail: "nested initializer declaration disagrees with its cell field".into(),
                });
            }
            let nested =
                require_descriptor(&declaration.declaration, ItemKind::Cell, declarations)?;
            let DescriptorPayload::Cell(nested_declaration) = &nested.payload else {
                unreachable!("kind-checked descriptor has a cell payload")
            };
            if children.len() != nested_declaration.fields.len()
                || children
                    .iter()
                    .zip(&nested_declaration.fields)
                    .any(|(child, field)| child.field.cell != field.reference.cell)
            {
                return Err(DescriptorLoweringError::ParserReferenceDisagreement {
                    id: Box::new(declaration.declaration.clone()),
                    detail: "nested initializer children disagree with the nominal declaration"
                        .into(),
                });
            }
            for child in children {
                validate_initializer_cell_references(child, declarations)?;
            }
            Ok(())
        }
        _ => Err(DescriptorLoweringError::ParserReferenceDisagreement {
            id: Box::new(cell.field.cell.owner.clone()),
            detail: "initializer cell content disagrees with its declaration".into(),
        }),
    }
}

fn validate_initializer_state_references(
    state: &DescriptorInitializerStateTerm,
    declarations: &BTreeMap<StableItemId, &Descriptor>,
) -> Result<(), DescriptorLoweringError> {
    match state {
        ProtocolInitializerStateTerm::Term(term) => {
            validate_structured_term_references(&term.term, declarations)
        }
        ProtocolInitializerStateTerm::KSequence(sequence) => {
            for item in &sequence.items {
                validate_structured_term_references(&item.value.term, declarations)?;
            }
            Ok(())
        }
        ProtocolInitializerStateTerm::Map(map) => {
            match &map.body {
                ProtocolMapBody::Empty { .. } => {}
                ProtocolMapBody::Items { items } => {
                    for item in items {
                        validate_structured_term_references(&item.key.term, declarations)?;
                        validate_structured_term_references(&item.value.term, declarations)?;
                    }
                }
                ProtocolMapBody::Update {
                    base, key, value, ..
                } => {
                    for term in [base, key, value] {
                        validate_structured_term_references(&term.term, declarations)?;
                    }
                }
            }
            Ok(())
        }
    }
}

fn validate_configuration_rule_references(
    rule: &krs_ir::DescriptorConfigurationRule,
    declarations: &BTreeMap<StableItemId, &Descriptor>,
) -> Result<(), DescriptorLoweringError> {
    for binding in &rule.bindings {
        if let ProtocolRuleBindingKind::Term { sort } = &binding.kind {
            validate_sort_ref(&sort.sort, declarations)?;
        }
    }
    validate_rule_cells_references(&rule.subject, declarations)?;
    validate_rule_cells_references(&rule.result, declarations)?;
    if let Some(requires) = &rule.requires {
        validate_structured_term_references(&requires.term, declarations)?;
    }
    Ok(())
}

fn validate_rule_cells_references(
    cells: &DescriptorRuleCells,
    declarations: &BTreeMap<StableItemId, &Descriptor>,
) -> Result<(), DescriptorLoweringError> {
    for cell in &cells.cells {
        require_cell_field(&cell.field.cell, declarations)?;
        match &cell.value {
            ProtocolRuleStateTerm::Term(term) => {
                validate_structured_term_references(term, declarations)?;
            }
            ProtocolRuleStateTerm::KSequence(sequence) => {
                for item in &sequence.items {
                    validate_structured_term_references(&item.value, declarations)?;
                }
            }
            ProtocolRuleStateTerm::Map(map) => match &map.body {
                ProtocolRuleMapBody::Empty { .. } => {}
                ProtocolRuleMapBody::Items { items, .. } => {
                    for item in items {
                        validate_structured_term_references(&item.key, declarations)?;
                        validate_structured_term_references(&item.value, declarations)?;
                    }
                }
                ProtocolRuleMapBody::Update {
                    base, key, value, ..
                } => {
                    for term in [base, key, value] {
                        validate_structured_term_references(term, declarations)?;
                    }
                }
            },
        }
    }
    Ok(())
}

fn require_cell_field<'a>(
    identity: &DescriptorCellIdentity,
    declarations: &'a BTreeMap<StableItemId, &Descriptor>,
) -> Result<&'a DescriptorCellField, DescriptorLoweringError> {
    let descriptor = declarations.get(&identity.owner).copied().ok_or_else(|| {
        DescriptorLoweringError::DanglingReference(Box::new(identity.owner.clone()))
    })?;
    let declaration = match &descriptor.payload {
        DescriptorPayload::FixedConfiguration(configuration) => &configuration.declaration,
        DescriptorPayload::Cell(declaration) => declaration.as_ref(),
        _ => {
            return Err(DescriptorLoweringError::ReferenceKindMismatch {
                id: Box::new(identity.owner.clone()),
                expected: ItemKind::Cell,
                actual: descriptor.id.item_kind(),
            });
        }
    };
    declaration
        .fields
        .iter()
        .find(|field| field.reference.cell == *identity)
        .ok_or_else(|| DescriptorLoweringError::ParserReferenceDisagreement {
            id: Box::new(identity.owner.clone()),
            detail: format!("owner has no declared cell field {:?}", identity.field),
        })
}

#[derive(Clone, Debug)]
struct ProductionSignature {
    result_sort: SemanticSortRef,
    fields: Vec<(ProductionFieldId, SemanticSortRef)>,
    grammar_owned: bool,
}

fn semantic_sort_ref(sort: &DescriptorSortRef) -> SemanticSortRef {
    match sort {
        DescriptorSortRef::Declared(id) => SemanticSortRef::Declared(id.clone()),
        DescriptorSortRef::Builtin(sort) => SemanticSortRef::Builtin(*sort),
    }
}

fn build_semantic_sort_parents(
    descriptors: &[&Descriptor],
) -> BTreeMap<SemanticSortRef, Vec<SemanticSortRef>> {
    let mut parents = BTreeMap::<SemanticSortRef, Vec<SemanticSortRef>>::new();
    for descriptor in descriptors {
        match &descriptor.payload {
            DescriptorPayload::Sort(sort) => {
                parents
                    .entry(SemanticSortRef::Declared(descriptor.id.clone()))
                    .or_default()
                    .extend(sort.parents.iter().cloned().map(SemanticSortRef::Declared));
            }
            DescriptorPayload::Grammar(grammar) => {
                if let GrammarDescriptor::Subsort {
                    subsort, supersort, ..
                } = grammar.as_ref()
                {
                    parents
                        .entry(semantic_sort_ref(&subsort.sort))
                        .or_default()
                        .push(semantic_sort_ref(&supersort.sort));
                }
            }
            DescriptorPayload::Constructor(_)
            | DescriptorPayload::StructuredRule(_)
            | DescriptorPayload::FixedConfiguration(_)
            | DescriptorPayload::Cell(_)
            | DescriptorPayload::ConfigurationRule(_)
            | DescriptorPayload::HeadRule(_)
            | DescriptorPayload::ContextAlias(_) => {}
        }
    }
    for direct in parents.values_mut() {
        direct.sort();
        direct.dedup();
    }
    parents
}

fn semantic_is_subsort(
    candidate: &SemanticSortRef,
    expected: &SemanticSortRef,
    parents: &BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
) -> bool {
    if candidate == expected {
        return true;
    }
    let mut pending = vec![candidate.clone()];
    let mut visited = BTreeSet::new();
    while let Some(sort) = pending.pop() {
        if !visited.insert(sort.clone()) {
            continue;
        }
        for parent in parents.get(&sort).into_iter().flatten() {
            if parent == expected {
                return true;
            }
            pending.push(parent.clone());
        }
    }
    false
}

fn build_production_catalog(
    descriptors: &[&Descriptor],
) -> Result<BTreeMap<StableItemId, ProductionSignature>, DescriptorLoweringError> {
    let mut catalog = BTreeMap::new();
    for descriptor in descriptors {
        let DescriptorPayload::Grammar(grammar) = &descriptor.payload else {
            continue;
        };
        let GrammarDescriptor::Production(production) = grammar.as_ref() else {
            continue;
        };
        let id = match &production.owner {
            DescriptorProductionOwner::Constructor { constructor } => {
                let DescriptorApplicationRef::Declared(id) = &constructor.application else {
                    return Err(DescriptorLoweringError::UnsupportedShape {
                        node: "constructor production owner",
                        detail: "constructor grammar cannot be owned by a builtin operation"
                            .to_owned(),
                    });
                };
                id.clone()
            }
            DescriptorProductionOwner::TokenSort { .. } => {
                generated_production_id(&descriptor.id, GeneratedProductionKind::Token).map_err(
                    |error| DescriptorLoweringError::InvalidGeneratedIdentity(error.to_string()),
                )?
            }
            DescriptorProductionOwner::BracketSort { .. } => {
                generated_production_id(&descriptor.id, GeneratedProductionKind::Bracket).map_err(
                    |error| DescriptorLoweringError::InvalidGeneratedIdentity(error.to_string()),
                )?
            }
        };
        let fields = production
            .items
            .iter()
            .filter_map(|item| match item {
                DescriptorProductionItem::NonTerminal { field, sort, .. } => {
                    Some((field.clone(), semantic_sort_ref(&sort.sort)))
                }
                DescriptorProductionItem::Terminal { .. }
                | DescriptorProductionItem::RegexTerminal { .. } => None,
            })
            .collect();
        if catalog
            .insert(
                id.clone(),
                ProductionSignature {
                    result_sort: semantic_sort_ref(&production.result_sort.sort),
                    fields,
                    grammar_owned: true,
                },
            )
            .is_some()
        {
            return Err(DescriptorLoweringError::UnsupportedShape {
                node: "production catalog",
                detail: format!("more than one grammar descriptor owns {id:?}"),
            });
        }
    }
    for descriptor in descriptors {
        let DescriptorPayload::Constructor(constructor) = &descriptor.payload else {
            continue;
        };
        if catalog.contains_key(&descriptor.id) {
            continue;
        }
        let fields = constructor_field_order(&descriptor.id, constructor)?
            .into_iter()
            .map(|name| {
                let field = constructor
                    .fields
                    .iter()
                    .find(|field| field.name == name)
                    .expect("field order is validated against declarations");
                let sort = field.sort.clone().ok_or_else(|| {
                    DescriptorLoweringError::UnsupportedShape {
                        node: "constructor field",
                        detail: format!(
                            "constructor {:?} field {name:?} has no sort",
                            descriptor.id
                        ),
                    }
                })?;
                Ok((ProductionFieldId::new(name)?, semantic_sort_ref(&sort)))
            })
            .collect::<Result<Vec<_>, DescriptorLoweringError>>()?;
        catalog.insert(
            descriptor.id.clone(),
            ProductionSignature {
                result_sort: semantic_sort_ref(&constructor.sort),
                fields,
                grammar_owned: false,
            },
        );
    }
    Ok(catalog)
}

#[allow(clippy::too_many_arguments)]
fn lower_grammar_descriptor(
    descriptor: &Descriptor,
    grammar: &GrammarDescriptor,
    declaration: &DescriptorDeclaration,
    productions: &mut Vec<SemanticProduction>,
    subsorts: &mut Vec<SemanticSubsort>,
    precedences: &mut Vec<PrecedenceRelation>,
    associativities: &mut Vec<GroupAssociativitySentence>,
) -> Result<(), DescriptorLoweringError> {
    match grammar {
        GrammarDescriptor::Production(production) => {
            productions.push(lower_grammar_production(
                descriptor,
                production,
                declaration,
            )?);
        }
        GrammarDescriptor::Subsort {
            key,
            subsort,
            supersort,
        } => subsorts.push(SemanticSubsort::new(
            semantic_origin(descriptor, key.clone(), "subsort")?,
            semantic_sort_ref(&subsort.sort),
            semantic_sort_ref(&supersort.sort),
        )),
        GrammarDescriptor::Precedence { chains, .. } => {
            for (chain_index, chain) in chains.iter().enumerate() {
                for (edge_index, pair) in chain.groups.windows(2).enumerate() {
                    precedences.push(
                        PrecedenceRelation::new(
                            semantic_origin(
                                descriptor,
                                chain.key.clone(),
                                &format!("precedence-{chain_index}-{edge_index}"),
                            )?,
                            vec![pair[0].group.clone()],
                            vec![pair[1].group.clone()],
                        )
                        .map_err(|error| {
                            DescriptorLoweringError::UnsupportedShape {
                                node: "precedence",
                                detail: error.to_string(),
                            }
                        })?,
                    );
                }
            }
        }
        GrammarDescriptor::Associativity { sentences, .. } => {
            for sentence in sentences {
                associativities.push(
                    GroupAssociativitySentence::new(
                        semantic_origin(descriptor, sentence.key.clone(), "associativity")?,
                        sentence.associativity,
                        sentence
                            .groups
                            .iter()
                            .map(|reference| reference.group.clone())
                            .collect(),
                    )
                    .map_err(|error| {
                        DescriptorLoweringError::UnsupportedShape {
                            node: "associativity",
                            detail: error.to_string(),
                        }
                    })?,
                );
            }
        }
    }
    Ok(())
}

#[allow(clippy::too_many_lines)]
fn lower_grammar_production(
    descriptor: &Descriptor,
    production: &DescriptorProduction,
    declaration: &DescriptorDeclaration,
) -> Result<SemanticProduction, DescriptorLoweringError> {
    let id = match &production.owner {
        DescriptorProductionOwner::Constructor { constructor } => {
            let DescriptorApplicationRef::Declared(id) = &constructor.application else {
                return Err(DescriptorLoweringError::UnsupportedShape {
                    node: "constructor production owner",
                    detail: "builtin operations cannot own authored grammar".to_owned(),
                });
            };
            id.clone()
        }
        DescriptorProductionOwner::TokenSort { .. } => {
            generated_production_id(&descriptor.id, GeneratedProductionKind::Token).map_err(
                |error| DescriptorLoweringError::InvalidGeneratedIdentity(error.to_string()),
            )?
        }
        DescriptorProductionOwner::BracketSort { .. } => {
            generated_production_id(&descriptor.id, GeneratedProductionKind::Bracket).map_err(
                |error| DescriptorLoweringError::InvalidGeneratedIdentity(error.to_string()),
            )?
        }
    };
    let items = production
        .items
        .iter()
        .map(|item| match item {
            DescriptorProductionItem::Terminal { key, text } => SemanticProductionItem::terminal(
                semantic_origin(descriptor, key.clone(), "production-item")?,
                text.clone(),
            )
            .map_err(|error| DescriptorLoweringError::UnsupportedShape {
                node: "production terminal",
                detail: error.to_string(),
            }),
            DescriptorProductionItem::NonTerminal {
                key, field, sort, ..
            } => Ok(SemanticProductionItem::non_terminal(
                semantic_origin(descriptor, key.clone(), "production-item")?,
                field.clone(),
                semantic_sort_ref(&sort.sort),
            )),
            DescriptorProductionItem::RegexTerminal {
                key,
                precede_regex,
                regex,
                follow_regex,
            } => SemanticProductionItem::regex_terminal(
                semantic_origin(descriptor, key.clone(), "production-item")?,
                precede_regex.clone(),
                regex.clone(),
                follow_regex.clone(),
            )
            .map_err(|error| DescriptorLoweringError::UnsupportedShape {
                node: "production regex",
                detail: error.to_string(),
            }),
        })
        .collect::<Result<Vec<_>, _>>()?;
    let attributes = production
        .attributes
        .iter()
        .map(|attribute| {
            Ok(match attribute {
                DescriptorProductionAttribute::Documentation { key, text } => {
                    ProductionAttribute::Documentation {
                        origin: semantic_origin(
                            descriptor,
                            key.clone(),
                            "production-documentation",
                        )?,
                        text: text.clone(),
                    }
                }
                DescriptorProductionAttribute::Function { key } => ProductionAttribute::Function {
                    origin: semantic_origin(descriptor, key.clone(), "production-attribute")?,
                },
                DescriptorProductionAttribute::Total { key } => ProductionAttribute::Total {
                    origin: semantic_origin(descriptor, key.clone(), "production-attribute")?,
                },
                DescriptorProductionAttribute::Hook { key, operation } => {
                    ProductionAttribute::Hook {
                        origin: semantic_origin(descriptor, key.clone(), "production-attribute")?,
                        operation: *operation,
                    }
                }
                DescriptorProductionAttribute::Alias { key } => ProductionAttribute::Alias {
                    origin: semantic_origin(descriptor, key.clone(), "production-attribute")?,
                },
                DescriptorProductionAttribute::Token {
                    key,
                    lexical_precedence,
                } => ProductionAttribute::Token {
                    origin: semantic_origin(descriptor, key.clone(), "production-attribute")?,
                    lexical_precedence: lexical_precedence.as_ref().map(|value| value.value),
                },
                DescriptorProductionAttribute::Group { reference } => ProductionAttribute::Group {
                    origin: semantic_origin(
                        descriptor,
                        reference.key.clone(),
                        "production-attribute",
                    )?,
                    group: reference.group.clone(),
                },
                DescriptorProductionAttribute::Bracket { key } => ProductionAttribute::Bracket {
                    origin: semantic_origin(descriptor, key.clone(), "production-attribute")?,
                },
                DescriptorProductionAttribute::Avoid { key } => ProductionAttribute::Avoid {
                    origin: semantic_origin(descriptor, key.clone(), "production-attribute")?,
                },
                DescriptorProductionAttribute::Format { key, fragments } => {
                    ProductionAttribute::Format {
                        origin: semantic_origin(descriptor, key.clone(), "production-attribute")?,
                        fragments: fragments
                            .iter()
                            .map(|fragment| fragment.fragment.clone())
                            .collect(),
                    }
                }
                DescriptorProductionAttribute::Strictness {
                    key,
                    kind,
                    using,
                    fields,
                    result_sort,
                } => ProductionAttribute::Strictness {
                    origin: semantic_origin(descriptor, key.clone(), "production-attribute")?,
                    kind: *kind,
                    using: using
                        .as_ref()
                        .map(|using| -> Result<_, DescriptorLoweringError> {
                            Ok(krs_ir::ProductionContextAliasReference::new(
                                semantic_origin(descriptor, using.key.clone(), "strictness-using")?,
                                using.alias.clone(),
                            ))
                        })
                        .transpose()?,
                    fields: fields
                        .iter()
                        .map(|field| {
                            Ok(krs_ir::ProductionFieldReference::new(
                                semantic_origin(descriptor, field.key.clone(), "strictness-field")?,
                                field.field.clone(),
                            ))
                        })
                        .collect::<Result<Vec<_>, DescriptorLoweringError>>()?,
                    result_sort: krs_ir::ProductionResultSort::new(
                        semantic_origin(descriptor, result_sort.key.clone(), "strictness-result")?,
                        semantic_sort_ref(&result_sort.sort),
                    ),
                },
            })
        })
        .collect::<Result<Vec<_>, DescriptorLoweringError>>()?;
    Ok(SemanticProduction::with_api(
        semantic_origin(descriptor, production.key.clone(), "production")?,
        id,
        semantic_sort_ref(&production.result_sort.sort),
        items,
        attributes,
        declaration.visibility.clone(),
        declaration.explicit_symbol.clone(),
    )?)
}

struct DeclarationCatalog<'a> {
    descriptors: &'a BTreeMap<StableItemId, &'a Descriptor>,
    metadata: &'a BTreeMap<StableItemId, DescriptorDeclaration>,
}

#[allow(clippy::too_many_lines)]
fn lower_package_module(
    package: &PackageId,
    descriptors: &[&Descriptor],
    module_ids: &BTreeMap<PackageId, ModuleId>,
    declarations: &DeclarationCatalog<'_>,
    semantic_sort_parents: &BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
    production_catalog: &BTreeMap<StableItemId, ProductionSignature>,
) -> Result<SemanticModule, DescriptorLoweringError> {
    let module_id = module_ids.get(package).cloned().ok_or_else(|| {
        DescriptorLoweringError::UnsupportedShape {
            node: "module",
            detail: format!("package {package:?} has no generated module identity"),
        }
    })?;
    let origin_descriptor =
        descriptors
            .first()
            .copied()
            .ok_or_else(|| DescriptorLoweringError::UnsupportedShape {
                node: "module",
                detail: format!("package {package:?} has no semantic descriptors"),
            })?;
    let module_origin = semantic_origin_from_primary(origin_descriptor, "module")?;
    let mut imports = referenced_packages(descriptors)
        .into_iter()
        .filter(|referenced| referenced != package)
        .map(|referenced| {
            module_ids.get(&referenced).cloned().ok_or_else(|| {
                DescriptorLoweringError::UnsupportedShape {
                    node: "module import",
                    detail: format!("referenced package {referenced:?} has no module"),
                }
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    imports.sort();
    imports.dedup();

    let mut sorts = Vec::new();
    let mut subsorts = Vec::new();
    let mut productions = Vec::new();
    let mut precedences = Vec::new();
    let mut associativities = Vec::new();
    let mut configuration = None;
    let mut rules = Vec::new();
    let mut context_aliases = Vec::new();
    for descriptor in descriptors {
        let declaration = declarations.metadata.get(&descriptor.id).ok_or_else(|| {
            DescriptorLoweringError::UnsupportedShape {
                node: "declaration metadata",
                detail: format!("descriptor {:?} has no API metadata", descriptor.id),
            }
        })?;
        match &descriptor.payload {
            DescriptorPayload::Sort(sort) => {
                sorts.push(SemanticSort::with_api(
                    semantic_origin(
                        descriptor,
                        role_key(ProvenanceRole::SortDeclaration, 0)?,
                        "sort",
                    )?,
                    descriptor.id.clone(),
                    declaration.visibility.clone(),
                    declaration.explicit_symbol.clone(),
                ));
                for (ordinal, parent) in sort.parents.iter().enumerate() {
                    let ordinal = u32::try_from(ordinal).map_err(|_| {
                        DescriptorLoweringError::UnsupportedShape {
                            node: "sort parents",
                            detail: "sort has more than u32::MAX direct parents".to_owned(),
                        }
                    })?;
                    subsorts.push(SemanticSubsort::new(
                        semantic_origin(
                            descriptor,
                            role_key(ProvenanceRole::SortParent, ordinal)?,
                            "subsort",
                        )?,
                        SemanticSortRef::Declared(descriptor.id.clone()),
                        SemanticSortRef::Declared(parent.clone()),
                    ));
                }
            }
            DescriptorPayload::Constructor(constructor) => {
                if production_catalog
                    .get(&descriptor.id)
                    .is_some_and(|signature| signature.grammar_owned)
                {
                    continue;
                }
                let syntax = constructor
                    .syntax
                    .clone()
                    .unwrap_or_else(|| lower_camel(descriptor.id.item_name()));
                productions.push(SemanticProduction::with_api(
                    semantic_origin(
                        descriptor,
                        role_key(ProvenanceRole::ConstructorDeclaration, 0)?,
                        "production",
                    )?,
                    descriptor.id.clone(),
                    semantic_sort_ref(&constructor.sort),
                    lower_constructor_grammar(descriptor, constructor, &syntax)?,
                    Vec::new(),
                    declaration.visibility.clone(),
                    declaration.explicit_symbol.clone(),
                )?);
            }
            DescriptorPayload::Grammar(grammar) => lower_grammar_descriptor(
                descriptor,
                grammar,
                declaration,
                &mut productions,
                &mut subsorts,
                &mut precedences,
                &mut associativities,
            )?,
            DescriptorPayload::StructuredRule(rule) => {
                rules.push(lower_structured_rule_descriptor(
                    descriptor,
                    rule,
                    semantic_sort_parents,
                    production_catalog,
                )?);
            }
            DescriptorPayload::FixedConfiguration(value) => {
                if configuration.is_some() {
                    return Err(DescriptorLoweringError::ConfigurationCount(2));
                }
                configuration = Some(lower_fixed_configuration_descriptor(
                    descriptor,
                    value,
                    declarations.descriptors,
                    semantic_sort_parents,
                    production_catalog,
                )?);
            }
            DescriptorPayload::Cell(_) => {}
            DescriptorPayload::ConfigurationRule(rule) => {
                rules.push(lower_configuration_rule_descriptor(
                    descriptor,
                    rule,
                    declarations.descriptors,
                    semantic_sort_parents,
                    production_catalog,
                )?);
            }
            DescriptorPayload::HeadRule(rule) => {
                rules.push(lower_head_rule_descriptor(
                    descriptor,
                    rule,
                    declarations.descriptors,
                    semantic_sort_parents,
                    production_catalog,
                )?);
            }
            DescriptorPayload::ContextAlias(alias) => {
                context_aliases.push(lower_context_alias_descriptor(
                    descriptor,
                    alias,
                    declarations.descriptors,
                    semantic_sort_parents,
                    production_catalog,
                )?);
            }
        }
    }
    sorts.sort_by(|left, right| left.id().cmp(right.id()));
    subsorts.sort();
    productions.sort_by(|left, right| left.id().cmp(right.id()));
    rules.sort_by(|left, right| left.id().cmp(right.id()));
    context_aliases.sort_by(|left, right| left.id().cmp(right.id()));
    precedences.sort();
    associativities.sort();
    Ok(SemanticModule::new_with_context_aliases(
        module_origin,
        module_id,
        imports,
        sorts,
        subsorts,
        productions,
        precedences,
        associativities,
        configuration,
        context_aliases,
        rules,
    ))
}

#[allow(clippy::too_many_lines)]
fn lower_constructor_grammar(
    descriptor: &Descriptor,
    constructor: &krs_ir::ConstructorDescriptor,
    source: &str,
) -> Result<Vec<SemanticProductionItem>, DescriptorLoweringError> {
    let syntax_key = if constructor.syntax.is_some() {
        role_key(ProvenanceRole::ConstructorSyntax, 0)?
    } else {
        role_key(ProvenanceRole::ConstructorDeclaration, 0)?
    };
    let mut items = Vec::new();
    let mut holes = BTreeSet::new();
    let mut terminal_index = 0_u32;
    let mut index = 0_usize;
    while index < source.len() {
        let character = source[index..]
            .chars()
            .next()
            .expect("index is on a character boundary");
        if character.is_whitespace() {
            index += character.len_utf8();
            continue;
        }
        if character == '{' {
            let remainder = &source[index + 1..];
            let Some(close) = remainder.find('}') else {
                return constructor_template_error(descriptor, "unclosed `{` placeholder");
            };
            let name = &remainder[..close];
            if !is_field_name(name) {
                return constructor_template_error(
                    descriptor,
                    format!("invalid placeholder name {name:?}"),
                );
            }
            if !holes.insert(name.to_owned()) {
                return constructor_template_error(
                    descriptor,
                    format!("repeated placeholder {name:?}"),
                );
            }
            let Some((field_index, field)) = constructor
                .fields
                .iter()
                .enumerate()
                .find(|(_, field)| field.name == name)
            else {
                return constructor_template_error(
                    descriptor,
                    format!("placeholder {name:?} names no constructor field"),
                );
            };
            let sort =
                field
                    .sort
                    .clone()
                    .ok_or_else(|| DescriptorLoweringError::UnsupportedShape {
                        node: "constructor field",
                        detail: format!(
                            "field {:?} on {:?} has no resolved sort",
                            field.name, descriptor.id
                        ),
                    })?;
            let ordinal = u32::try_from(field_index).map_err(|_| {
                DescriptorLoweringError::UnsupportedShape {
                    node: "constructor fields",
                    detail: "constructor has more than u32::MAX fields".to_owned(),
                }
            })?;
            items.push(SemanticProductionItem::non_terminal(
                semantic_origin(
                    descriptor,
                    role_key(ProvenanceRole::ConstructorFieldSort, ordinal)?,
                    &format!("production-field-{ordinal}"),
                )?,
                ProductionFieldId::new(field.name.clone())?,
                semantic_sort_ref(&sort),
            ));
            index += close + 2;
            continue;
        }
        if character == '}' {
            return constructor_template_error(descriptor, "unmatched `}` placeholder delimiter");
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
        items.push(
            SemanticProductionItem::terminal(
                semantic_origin(
                    descriptor,
                    syntax_key.clone(),
                    &format!("production-terminal-{terminal_index}"),
                )?,
                &source[start..index],
            )
            .map_err(|error| DescriptorLoweringError::UnsupportedShape {
                node: "constructor syntax",
                detail: error.to_string(),
            })?,
        );
        terminal_index = terminal_index.checked_add(1).ok_or_else(|| {
            DescriptorLoweringError::UnsupportedShape {
                node: "constructor syntax",
                detail: "production has more than u32::MAX terminals".to_owned(),
            }
        })?;
    }
    if holes.len() != constructor.fields.len() {
        return constructor_template_error(
            descriptor,
            format!(
                "template has {} placeholders for {} constructor fields",
                holes.len(),
                constructor.fields.len()
            ),
        );
    }
    if items.is_empty() {
        return constructor_template_error(descriptor, "template contains no grammar items");
    }
    Ok(items)
}

fn constructor_template_error<T>(
    descriptor: &Descriptor,
    detail: impl Into<String>,
) -> Result<T, DescriptorLoweringError> {
    Err(DescriptorLoweringError::UnsupportedShape {
        node: "constructor syntax",
        detail: format!("constructor {:?}: {}", descriptor.id, detail.into()),
    })
}

#[allow(clippy::too_many_lines)]
fn referenced_packages(descriptors: &[&Descriptor]) -> BTreeSet<PackageId> {
    let mut packages = BTreeSet::new();
    for descriptor in descriptors {
        let mut insert = |id: &StableItemId| {
            packages.insert(id.package().clone());
        };
        match &descriptor.payload {
            DescriptorPayload::Sort(sort) => sort.parents.iter().for_each(&mut insert),
            DescriptorPayload::Constructor(constructor) => {
                if let DescriptorSortRef::Declared(sort) = &constructor.sort {
                    insert(sort);
                }
                constructor
                    .fields
                    .iter()
                    .filter_map(|field| field.sort.as_ref())
                    .filter_map(|sort| match sort {
                        DescriptorSortRef::Declared(id) => Some(id),
                        DescriptorSortRef::Builtin(_) => None,
                    })
                    .for_each(&mut insert);
            }
            DescriptorPayload::Grammar(grammar) => match grammar.as_ref() {
                GrammarDescriptor::Production(production) => {
                    if let DescriptorProductionOwner::Constructor { constructor } =
                        &production.owner
                        && let DescriptorApplicationRef::Declared(id) = &constructor.application
                    {
                        insert(id);
                    }
                    match &production.owner {
                        DescriptorProductionOwner::TokenSort { sort }
                        | DescriptorProductionOwner::BracketSort { sort } => {
                            if let DescriptorSortRef::Declared(id) = &sort.sort {
                                insert(id);
                            }
                        }
                        DescriptorProductionOwner::Constructor { .. } => {}
                    }
                    if let DescriptorSortRef::Declared(id) = &production.result_sort.sort {
                        insert(id);
                    }
                    for item in &production.items {
                        if let DescriptorProductionItem::NonTerminal { sort, .. } = item
                            && let DescriptorSortRef::Declared(id) = &sort.sort
                        {
                            insert(id);
                        }
                    }
                    for attribute in &production.attributes {
                        if let DescriptorProductionAttribute::Strictness {
                            using: Some(using),
                            ..
                        } = attribute
                        {
                            insert(&using.alias);
                        }
                        if let DescriptorProductionAttribute::Strictness { result_sort, .. } =
                            attribute
                            && let DescriptorSortRef::Declared(id) = &result_sort.sort
                        {
                            insert(id);
                        }
                    }
                }
                GrammarDescriptor::Subsort {
                    subsort, supersort, ..
                } => {
                    for sort in [&subsort.sort, &supersort.sort] {
                        if let DescriptorSortRef::Declared(id) = sort {
                            insert(id);
                        }
                    }
                }
                GrammarDescriptor::Precedence { .. } | GrammarDescriptor::Associativity { .. } => {}
            },
            DescriptorPayload::StructuredRule(rule) => {
                for sort in [&rule.subject_sort.sort, &rule.result_sort.sort] {
                    if let DescriptorSortRef::Declared(id) = sort {
                        insert(id);
                    }
                }
                collect_term_packages(&rule.subject, &mut packages);
                collect_term_packages(&rule.result, &mut packages);
            }
            DescriptorPayload::FixedConfiguration(configuration) => {
                collect_fixed_configuration_packages(configuration, &mut packages);
            }
            DescriptorPayload::Cell(declaration) => {
                collect_cell_declaration_packages(declaration, &mut packages);
            }
            DescriptorPayload::ConfigurationRule(rule) => {
                packages.insert(rule.subject_configuration.configuration.package().clone());
                packages.insert(rule.result_configuration.configuration.package().clone());
                for binding in &rule.bindings {
                    if let ProtocolRuleBindingKind::Term { sort } = &binding.kind {
                        collect_sort_ref_package(&sort.sort, &mut packages);
                    }
                }
                collect_rule_cells_packages(&rule.subject, &mut packages);
                collect_rule_cells_packages(&rule.result, &mut packages);
            }
            DescriptorPayload::HeadRule(rule) => {
                insert(&rule.configuration);
                if let Some(head_sort) = &rule.head_sort {
                    collect_sort_ref_package(&head_sort.sort, &mut packages);
                }
                for binding in &rule.bindings {
                    if let Some(refinement) = &binding.refinement {
                        collect_sort_ref_package(&refinement.sort, &mut packages);
                    }
                }
                collect_term_packages(&rule.subject, &mut packages);
                match &rule.result {
                    krs_ir::ProtocolHeadRuleResult::Replace(term) => {
                        collect_term_packages(term, &mut packages);
                    }
                    krs_ir::ProtocolHeadRuleResult::Splice(items) => {
                        for term in items {
                            collect_term_packages(term, &mut packages);
                        }
                    }
                    krs_ir::ProtocolHeadRuleResult::Erase => {}
                }
                for extra in &rule.extras {
                    match extra {
                        krs_ir::ProtocolHeadRuleExtra::HaveMap { key, .. } => {
                            collect_term_packages(key, &mut packages);
                        }
                        krs_ir::ProtocolHeadRuleExtra::UpdateMap { update, .. } => {
                            collect_term_packages(update, &mut packages);
                        }
                        krs_ir::ProtocolHeadRuleExtra::RewriteCell { before, after, .. } => {
                            collect_term_packages(before, &mut packages);
                            collect_term_packages(after, &mut packages);
                        }
                    }
                }
                if let Some(requires) = &rule.requires {
                    collect_term_packages(&requires.term, &mut packages);
                }
            }
            DescriptorPayload::ContextAlias(alias) => {
                insert(&alias.configuration.configuration);
                for binding in &alias.bindings {
                    if let ProtocolContextAliasBindingKind::Term { sort } = &binding.kind {
                        collect_sort_ref_package(&sort.sort, &mut packages);
                    }
                }
                collect_rule_cells_packages(&alias.pattern, &mut packages);
            }
        }
    }
    packages
}

fn collect_term_packages(term: &DescriptorTerm, packages: &mut BTreeSet<PackageId>) {
    if let DescriptorTerm::Application {
        reference,
        arguments,
        ..
    } = term
    {
        if let DescriptorApplicationRef::Declared(id) = &reference.application {
            packages.insert(id.package().clone());
        }
        for argument in arguments {
            let value = match argument {
                DescriptorTermArgument::Positional { value }
                | DescriptorTermArgument::Named { value, .. } => value,
            };
            collect_term_packages(value, packages);
        }
    }
}

fn collect_fixed_configuration_packages(
    configuration: &DescriptorFixedConfiguration,
    packages: &mut BTreeSet<PackageId>,
) {
    collect_cell_declaration_packages(&configuration.declaration, packages);
    for variable in &configuration.initializer.variables {
        collect_sort_ref_package(&variable.sort.sort, packages);
    }
    for cell in &configuration.initializer.cells {
        collect_initializer_cell_packages(cell, packages);
    }
}

fn collect_cell_declaration_packages(
    declaration: &DescriptorCellDeclaration,
    packages: &mut BTreeSet<PackageId>,
) {
    for field in &declaration.fields {
        match &field.content {
            ProtocolCellContent::Leaf { sort, .. } => {
                collect_sort_ref_package(&sort.sort, packages);
            }
            ProtocolCellContent::Nested { declaration } => {
                packages.insert(declaration.declaration.package().clone());
            }
        }
    }
}

fn collect_sort_ref_package(sort: &DescriptorSortRef, packages: &mut BTreeSet<PackageId>) {
    if let DescriptorSortRef::Declared(id) = sort {
        packages.insert(id.package().clone());
    }
}

fn collect_initializer_cell_packages(
    cell: &DescriptorInitializerCell,
    packages: &mut BTreeSet<PackageId>,
) {
    packages.insert(cell.field.cell.owner.package().clone());
    match &cell.content {
        ProtocolInitializerCellContent::Leaf { value, .. } => {
            collect_initializer_state_packages(value, packages);
        }
        ProtocolInitializerCellContent::Nested {
            declaration,
            children,
        } => {
            packages.insert(declaration.declaration.package().clone());
            for child in children {
                collect_initializer_cell_packages(child, packages);
            }
        }
    }
}

fn collect_initializer_state_packages(
    state: &DescriptorInitializerStateTerm,
    packages: &mut BTreeSet<PackageId>,
) {
    match state {
        ProtocolInitializerStateTerm::Term(term) => collect_term_packages(&term.term, packages),
        ProtocolInitializerStateTerm::KSequence(sequence) => {
            for item in &sequence.items {
                collect_term_packages(&item.value.term, packages);
            }
        }
        ProtocolInitializerStateTerm::Map(map) => match &map.body {
            ProtocolMapBody::Empty { .. } => {}
            ProtocolMapBody::Items { items } => {
                for item in items {
                    collect_term_packages(&item.key.term, packages);
                    collect_term_packages(&item.value.term, packages);
                }
            }
            ProtocolMapBody::Update {
                base, key, value, ..
            } => {
                for term in [base, key, value] {
                    collect_term_packages(&term.term, packages);
                }
            }
        },
    }
}

fn collect_rule_cells_packages(cells: &DescriptorRuleCells, packages: &mut BTreeSet<PackageId>) {
    for cell in &cells.cells {
        packages.insert(cell.field.cell.owner.package().clone());
        match &cell.value {
            ProtocolRuleStateTerm::Term(term) => collect_term_packages(term, packages),
            ProtocolRuleStateTerm::KSequence(sequence) => {
                for item in &sequence.items {
                    collect_term_packages(&item.value, packages);
                }
            }
            ProtocolRuleStateTerm::Map(map) => match &map.body {
                ProtocolRuleMapBody::Empty { .. } => {}
                ProtocolRuleMapBody::Items { items, .. } => {
                    for item in items {
                        collect_term_packages(&item.key, packages);
                        collect_term_packages(&item.value, packages);
                    }
                }
                ProtocolRuleMapBody::Update {
                    base, key, value, ..
                } => {
                    for term in [base, key, value] {
                        collect_term_packages(term, packages);
                    }
                }
            },
        }
    }
}

fn lower_fixed_configuration_descriptor(
    descriptor: &Descriptor,
    configuration: &DescriptorFixedConfiguration,
    declarations: &BTreeMap<StableItemId, &Descriptor>,
    sort_parents: &BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
) -> Result<SemanticConfiguration, DescriptorLoweringError> {
    let configuration_id = generated_semantic_id("configuration", &descriptor.id, None)?;
    let root = match &configuration.root {
        krs_ir::DescriptorConfigurationRoot::GeneratedTop => ConfigurationRoot::GeneratedTop,
        krs_ir::DescriptorConfigurationRoot::Named { key, name } => ConfigurationRoot::named(
            semantic_origin(descriptor, key.clone(), "configuration-root")?,
            name.clone(),
        )?,
    };
    let mut visiting = BTreeSet::new();
    let cells = lower_cell_declaration(
        descriptor,
        &configuration.declaration,
        declarations,
        &mut visiting,
    )?;

    let mut binding_sorts = BTreeMap::new();
    let mut variables = Vec::with_capacity(configuration.initializer.variables.len());
    for variable in &configuration.initializer.variables {
        let id = SemanticId::new(variable.binding.clone())?;
        let sort = semantic_sort_ref(&variable.sort.sort);
        binding_sorts.insert(variable.binding.clone(), sort.clone());
        variables.push(FixedConfigurationVariable::new(
            semantic_origin(
                descriptor,
                variable.binding_key.clone(),
                "configuration-variable",
            )?,
            id,
            variable.external_name.clone(),
            sort,
            variable.main_key.is_some(),
        )?);
    }
    let initializer = configuration
        .initializer
        .cells
        .iter()
        .map(|cell| {
            lower_initializer_cell(
                descriptor,
                cell,
                declarations,
                sort_parents,
                catalog,
                &binding_sorts,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let initializer_id = SemanticId::new(format!("{}.init", configuration_id.as_str()))?;
    Ok(FixedConfiguration::new(
        semantic_origin(
            descriptor,
            configuration.declaration.key.clone(),
            "fixed-configuration",
        )?,
        configuration_id,
        root,
        cells,
        semantic_origin(
            descriptor,
            configuration.initializer.key.clone(),
            "fixed-initializer",
        )?,
        initializer_id,
        variables,
        initializer,
    )?)
}

fn lower_cell_declaration(
    descriptor: &Descriptor,
    declaration: &DescriptorCellDeclaration,
    declarations: &BTreeMap<StableItemId, &Descriptor>,
    visiting: &mut BTreeSet<StableItemId>,
) -> Result<Vec<FixedCell<SemanticSortRef, SemanticId>>, DescriptorLoweringError> {
    let mut cells = Vec::with_capacity(declaration.fields.len());
    for field in &declaration.fields {
        let id = semantic_cell_id(&field.reference.cell)?;
        let name = field
            .emitted_name
            .as_ref()
            .map_or_else(|| field.rust_field.clone(), |name| name.value.clone());
        let mut attributes = Vec::with_capacity(3);
        if let Some(color) = &field.color {
            attributes.push(CellAttribute::color(
                semantic_origin(descriptor, color.key.clone(), "cell-color")?,
                color.value.clone(),
            )?);
        }
        if let Some(multiplicity) = &field.multiplicity {
            debug_assert_eq!(multiplicity.value, "*");
            attributes.push(CellAttribute::multiplicity(
                semantic_origin(descriptor, multiplicity.key.clone(), "cell-multiplicity")?,
                CellMultiplicity::Star,
            ));
        }
        if let Some(cell_type) = &field.cell_type {
            let value = match cell_type.value.as_str() {
                "Bag" => CellCollectionType::Bag,
                "List" => CellCollectionType::List,
                "Map" => CellCollectionType::Map,
                "Set" => CellCollectionType::Set,
                _ => unreachable!("protocol validation rejects unsupported cell types"),
            };
            attributes.push(CellAttribute::collection_type(
                semantic_origin(descriptor, cell_type.key.clone(), "cell-type")?,
                value,
            ));
        }
        let origin = semantic_origin(
            descriptor,
            field.reference.key.clone(),
            "fixed-cell-declaration",
        )?;
        let cell = match &field.content {
            ProtocolCellContent::Leaf { sort, .. } => {
                FixedCell::leaf(origin, id, name, attributes, semantic_sort_ref(&sort.sort))?
            }
            ProtocolCellContent::Nested { declaration } => {
                if !visiting.insert(declaration.declaration.clone()) {
                    return Err(DescriptorLoweringError::UnsupportedShape {
                        node: "nested cell declaration",
                        detail: format!(
                            "cyclic nominal cell declaration at {:?}",
                            declaration.declaration
                        ),
                    });
                }
                let nested =
                    require_descriptor(&declaration.declaration, ItemKind::Cell, declarations)?;
                let DescriptorPayload::Cell(nested_declaration) = &nested.payload else {
                    unreachable!("kind-checked descriptor has a cell payload")
                };
                let children =
                    lower_cell_declaration(nested, nested_declaration, declarations, visiting)?;
                visiting.remove(&declaration.declaration);
                FixedCell::nested(origin, id, name, attributes, children)?
            }
        };
        cells.push(cell);
    }
    Ok(cells)
}

fn lower_initializer_cell(
    descriptor: &Descriptor,
    cell: &DescriptorInitializerCell,
    declarations: &BTreeMap<StableItemId, &Descriptor>,
    sort_parents: &BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
    binding_sorts: &BTreeMap<String, SemanticSortRef>,
) -> Result<FixedInitializerCell<SemanticId, SemanticTerm>, DescriptorLoweringError> {
    let declared = require_cell_field(&cell.field.cell, declarations)?;
    let id = semantic_cell_id(&cell.field.cell)?;
    let origin = semantic_origin(descriptor, cell.key.clone(), "initializer-cell")?;
    match (&cell.content, &declared.content) {
        (
            ProtocolInitializerCellContent::Leaf { value, .. },
            ProtocolCellContent::Leaf { sort, .. },
        ) => Ok(FixedInitializerCell::term(
            origin,
            id,
            lower_initializer_state(
                descriptor,
                value,
                &semantic_sort_ref(&sort.sort),
                &cell.key,
                sort_parents,
                catalog,
                binding_sorts,
            )?,
        )),
        (
            ProtocolInitializerCellContent::Nested { children, .. },
            ProtocolCellContent::Nested { .. },
        ) => {
            let children = children
                .iter()
                .map(|child| {
                    lower_initializer_cell(
                        descriptor,
                        child,
                        declarations,
                        sort_parents,
                        catalog,
                        binding_sorts,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok(FixedInitializerCell::children(origin, id, children)?)
        }
        _ => Err(DescriptorLoweringError::ParserReferenceDisagreement {
            id: Box::new(cell.field.cell.owner.clone()),
            detail: "initializer content disagrees with the declared cell family".into(),
        }),
    }
}

#[allow(clippy::too_many_arguments)]
#[allow(clippy::too_many_lines)]
fn lower_initializer_state(
    descriptor: &Descriptor,
    state: &DescriptorInitializerStateTerm,
    declared_sort: &SemanticSortRef,
    fallback_key: &ProvenanceKey,
    sort_parents: &BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
    binding_sorts: &BTreeMap<String, SemanticSortRef>,
) -> Result<SemanticTerm, DescriptorLoweringError> {
    match state {
        ProtocolInitializerStateTerm::Term(term) => lower_initializer_term(
            descriptor,
            &term.term,
            Some(declared_sort),
            sort_parents,
            catalog,
            binding_sorts,
        ),
        ProtocolInitializerStateTerm::KSequence(sequence) => {
            if *declared_sort != SemanticSortRef::k_sequence() {
                return Err(DescriptorLoweringError::InvalidTerm {
                    id: Box::new(descriptor.id.clone()),
                    detail: "K sequence initializes a non-KSequence cell".into(),
                });
            }
            let items = sequence
                .items
                .iter()
                .map(|item| {
                    lower_initializer_term(
                        descriptor,
                        &item.value.term,
                        None,
                        sort_parents,
                        catalog,
                        binding_sorts,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?;
            let item_sort = common_sequence_item_sort(descriptor, &items, sort_parents)?;
            let key = sequence
                .payload_key
                .as_ref()
                .or(sequence.dot_k_key.as_ref())
                .unwrap_or(fallback_key);
            Ok(SemanticTerm::k_sequence(
                semantic_origin(descriptor, key.clone(), "initializer-k-sequence")?,
                item_sort,
                items,
            ))
        }
        ProtocolInitializerStateTerm::Map(map) => {
            if *declared_sort != SemanticSortRef::map() {
                return Err(DescriptorLoweringError::InvalidTerm {
                    id: Box::new(descriptor.id.clone()),
                    detail: "map initializes a non-Map cell".into(),
                });
            }
            let key = map.payload_key.as_ref().unwrap_or(fallback_key);
            let (operation, arguments) = match &map.body {
                ProtocolMapBody::Empty { .. } => (MapOperation::Empty, Vec::new()),
                ProtocolMapBody::Items { items } => {
                    let mut arguments = Vec::with_capacity(items.len() * 2);
                    for item in items {
                        arguments.push(lower_initializer_term(
                            descriptor,
                            &item.key.term,
                            None,
                            sort_parents,
                            catalog,
                            binding_sorts,
                        )?);
                        arguments.push(lower_initializer_term(
                            descriptor,
                            &item.value.term,
                            None,
                            sort_parents,
                            catalog,
                            binding_sorts,
                        )?);
                    }
                    (MapOperation::Item, arguments)
                }
                ProtocolMapBody::Update {
                    base, key, value, ..
                } => (
                    MapOperation::Update,
                    vec![
                        lower_initializer_term(
                            descriptor,
                            &base.term,
                            Some(&SemanticSortRef::map()),
                            sort_parents,
                            catalog,
                            binding_sorts,
                        )?,
                        lower_initializer_term(
                            descriptor,
                            &key.term,
                            None,
                            sort_parents,
                            catalog,
                            binding_sorts,
                        )?,
                        lower_initializer_term(
                            descriptor,
                            &value.term,
                            None,
                            sort_parents,
                            catalog,
                            binding_sorts,
                        )?,
                    ],
                ),
            };
            Ok(SemanticTerm::map(
                semantic_origin(descriptor, key.clone(), "initializer-map")?,
                operation,
                arguments,
            ))
        }
    }
}

fn lower_initializer_term(
    descriptor: &Descriptor,
    term: &DescriptorTerm,
    expected_sort: Option<&SemanticSortRef>,
    sort_parents: &BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
    binding_sorts: &BTreeMap<String, SemanticSortRef>,
) -> Result<SemanticTerm, DescriptorLoweringError> {
    let binding_names = binding_sorts.keys().cloned().collect::<BTreeSet<_>>();
    let mut builder = StructuredTermBuilder {
        descriptor,
        catalog,
        declarations: None,
        k_item_sort: None,
        sort_parents,
        binding_names: &binding_names,
        pattern_key: None,
        binding_sorts: BTreeMap::new(),
        binding_constraints: initial_binding_constraints(binding_sorts),
        wildcard_offset: 0,
        wildcards: Vec::new(),
    };
    builder.infer(term, expected_sort, false)?;
    builder.resolve_binding_sorts()?;
    builder.lower(term, expected_sort, false)
}

#[allow(clippy::too_many_arguments)]
fn lower_rule_descriptor_term(
    descriptor: &Descriptor,
    term: &DescriptorTerm,
    expected_sort: Option<&SemanticSortRef>,
    declarations: &BTreeMap<StableItemId, &Descriptor>,
    sort_parents: &BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
    binding_sorts: &BTreeMap<String, SemanticSortRef>,
    subject: bool,
    wildcard_ordinal: &mut usize,
    variables: &mut Vec<SemanticVariable>,
) -> Result<SemanticTerm, DescriptorLoweringError> {
    let binding_names = binding_sorts.keys().cloned().collect::<BTreeSet<_>>();
    let mut builder = StructuredTermBuilder {
        descriptor,
        catalog,
        declarations: Some(declarations),
        k_item_sort: Some(framework_k_item_sort(declarations)?),
        sort_parents,
        binding_names: &binding_names,
        pattern_key: None,
        binding_sorts: BTreeMap::new(),
        binding_constraints: initial_binding_constraints(binding_sorts),
        wildcard_offset: *wildcard_ordinal,
        wildcards: Vec::new(),
    };
    builder.infer(term, expected_sort, subject)?;
    builder.resolve_binding_sorts()?;
    let lowered = builder.lower(term, expected_sort, subject)?;
    *wildcard_ordinal += builder.wildcards.len();
    variables.append(&mut builder.wildcards);
    Ok(lowered)
}

fn common_sequence_item_sort(
    descriptor: &Descriptor,
    items: &[SemanticTerm],
    parents: &BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
) -> Result<SemanticSortRef, DescriptorLoweringError> {
    if items.is_empty() {
        return Ok(SemanticSortRef::k_sequence());
    }
    let mut common = semantic_sort_closure(items[0].sort(), parents);
    for item in &items[1..] {
        let candidates = semantic_sort_closure(item.sort(), parents);
        common.retain(|candidate| candidates.contains(candidate));
    }
    let most_specific = common
        .iter()
        .filter(|candidate| {
            !common
                .iter()
                .any(|other| other != *candidate && semantic_is_subsort(other, candidate, parents))
        })
        .cloned()
        .collect::<Vec<_>>();
    let [item_sort] = most_specific.as_slice() else {
        return Err(DescriptorLoweringError::InvalidTerm {
            id: Box::new(descriptor.id.clone()),
            detail: "K sequence items do not have one most-specific common sort".into(),
        });
    };
    Ok(item_sort.clone())
}

fn semantic_sort_closure(
    start: &SemanticSortRef,
    parents: &BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
) -> BTreeSet<SemanticSortRef> {
    let mut pending = vec![start.clone()];
    let mut closure = BTreeSet::new();
    while let Some(sort) = pending.pop() {
        if !closure.insert(sort.clone()) {
            continue;
        }
        if let Some(direct) = parents.get(&sort) {
            pending.extend(direct.iter().cloned());
        }
    }
    closure
}

fn generated_semantic_id(
    family: &str,
    owner: &StableItemId,
    field: Option<&str>,
) -> Result<SemanticId, DescriptorLoweringError> {
    let mut seed = stable_item_text(owner);
    if let Some(field) = field {
        seed.push('\0');
        seed.push_str(field);
    }
    let digest = Sha256::digest(seed.as_bytes());
    Ok(SemanticId::new(format!(
        "{family}.{}.{}",
        owner.item_name(),
        hex_encode(&digest[..8])
    ))?)
}

fn semantic_cell_id(
    identity: &DescriptorCellIdentity,
) -> Result<SemanticId, DescriptorLoweringError> {
    generated_semantic_id("cell", &identity.owner, Some(&identity.field))
}

fn framework_k_item_sort(
    declarations: &BTreeMap<StableItemId, &Descriptor>,
) -> Result<SemanticSortRef, DescriptorLoweringError> {
    let mut matches = declarations.keys().filter(|id| {
        id.item_kind() == ItemKind::Sort
            && id.item_name() == "KItem"
            && id.package().k_namespace() == "KRS-FRAMEWORK"
            && id.package().cargo_name() == "krs"
            && id.package().cargo_source() == "framework"
    });
    let first = matches
        .next()
        .ok_or_else(|| DescriptorLoweringError::UnsupportedShape {
            node: "complete cell term",
            detail: "fragment! requires the selected framework KItem sort".into(),
        })?;
    if matches.next().is_some() {
        return Err(DescriptorLoweringError::UnsupportedShape {
            node: "complete cell term",
            detail: "fragment! found more than one selected framework KItem sort".into(),
        });
    }
    Ok(SemanticSortRef::Declared(first.clone()))
}

#[allow(clippy::too_many_lines)]
fn lower_head_rule_descriptor(
    descriptor: &Descriptor,
    rule: &krs_ir::DescriptorHeadRule,
    declarations: &BTreeMap<StableItemId, &Descriptor>,
    sort_parents: &BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
) -> Result<SemanticRule, DescriptorLoweringError> {
    if rule.sentence_kind != krs_ir::SentenceKind::Transition {
        return Err(DescriptorLoweringError::UnsupportedShape {
            node: "head-anchored rule",
            detail: "readable head completion currently supports transition rules only".into(),
        });
    }
    let configuration_descriptor =
        require_descriptor(&rule.configuration, ItemKind::Configuration, declarations)?;
    let DescriptorPayload::FixedConfiguration(configuration) = &configuration_descriptor.payload
    else {
        return Err(DescriptorLoweringError::UnsupportedShape {
            node: "head-anchored rule",
            detail: "head completion requires a fixed configuration".into(),
        });
    };
    let computation = require_cell_field(&rule.computation_cell.cell, declarations)?;
    let ProtocolCellContent::Leaf { wrapper, sort, .. } = &computation.content else {
        return Err(DescriptorLoweringError::UnsupportedShape {
            node: "head-anchored rule",
            detail: "resolved computation cell is not a fixed leaf".into(),
        });
    };
    if *wrapper != krs_ir::CellWrapper::KCell
        || sort.sort != DescriptorSortRef::Builtin(BuiltinSort::KSequence)
    {
        return Err(DescriptorLoweringError::UnsupportedShape {
            node: "head-anchored rule",
            detail: "resolved computation cell is not KCell<KSequence>".into(),
        });
    }

    let binding_names = rule
        .bindings
        .iter()
        .map(|binding| binding.name.clone())
        .collect::<BTreeSet<_>>();
    if binding_names.len() != rule.bindings.len() {
        return Err(DescriptorLoweringError::InvalidTerm {
            id: Box::new(descriptor.id.clone()),
            detail: "head-anchored rule has duplicate bindings".into(),
        });
    }
    let mut binding_sorts = BTreeMap::new();
    for binding in &rule.bindings {
        if let Some(refinement) = &binding.refinement {
            binding_sorts.insert(binding.name.clone(), semantic_sort_ref(&refinement.sort));
        }
    }
    let mut map_argument_sorts = BTreeMap::new();
    let mut cell_sorts = BTreeMap::new();
    for extra in &rule.extras {
        let cell = match extra {
            krs_ir::ProtocolHeadRuleExtra::HaveMap { cell, .. }
            | krs_ir::ProtocolHeadRuleExtra::UpdateMap { cell, .. }
            | krs_ir::ProtocolHeadRuleExtra::RewriteCell { cell, .. } => cell,
        };
        let declared = require_cell_field(&cell.cell, declarations)?;
        let ProtocolCellContent::Leaf {
            sort, arguments, ..
        } = &declared.content
        else {
            continue;
        };
        cell_sorts.insert(cell.cell.clone(), semantic_sort_ref(&sort.sort));
        if sort.sort == DescriptorSortRef::Builtin(BuiltinSort::Map)
            && let [key, value] = arguments.as_slice()
        {
            map_argument_sorts.insert(
                cell.cell.clone(),
                (semantic_sort_ref(&key.sort), semantic_sort_ref(&value.sort)),
            );
        }
        if let krs_ir::ProtocolHeadRuleExtra::HaveMap { value_binding, .. } = extra
            && let Some((_, value_sort)) = map_argument_sorts.get(&cell.cell)
        {
            binding_sorts
                .entry(value_binding.clone())
                .or_insert_with(|| value_sort.clone());
        }
        if let krs_ir::ProtocolHeadRuleExtra::UpdateMap { base_binding, .. } = extra {
            let cell_sort = cell_sorts.get(&cell.cell).ok_or_else(|| {
                DescriptorLoweringError::UnsupportedShape {
                    node: "head-anchored rule extra",
                    detail: format!("updated cell {:?} is not a fixed leaf", cell.cell.field),
                }
            })?;
            match binding_sorts.get(base_binding) {
                Some(sort) if sort != cell_sort => {
                    return Err(DescriptorLoweringError::InvalidTerm {
                        id: Box::new(descriptor.id.clone()),
                        detail: format!(
                            "updated-cell binding {base_binding:?} has a refinement other than {cell_sort:?}"
                        ),
                    });
                }
                Some(_) => {}
                None => {
                    binding_sorts.insert(base_binding.clone(), cell_sort.clone());
                }
            }
        }
    }
    let binding_constraints = initial_binding_constraints(&binding_sorts);
    let mut builder = StructuredTermBuilder {
        descriptor,
        catalog,
        declarations: Some(declarations),
        k_item_sort: Some(framework_k_item_sort(declarations)?),
        sort_parents,
        binding_names: &binding_names,
        pattern_key: Some(&rule.pattern_key),
        binding_sorts: BTreeMap::new(),
        binding_constraints,
        wildcard_offset: 0,
        wildcards: Vec::new(),
    };
    let head_sort = rule
        .head_sort
        .as_ref()
        .map(|sort| semantic_sort_ref(&sort.sort));
    builder.infer(&rule.subject, head_sort.as_ref(), true)?;
    match &rule.result {
        krs_ir::ProtocolHeadRuleResult::Replace(term) => {
            builder.infer(term, head_sort.as_ref(), false)?;
        }
        krs_ir::ProtocolHeadRuleResult::Splice(items) => {
            for term in items {
                builder.infer(term, head_sort.as_ref(), false)?;
            }
        }
        krs_ir::ProtocolHeadRuleResult::Erase => {}
    }
    for extra in &rule.extras {
        match extra {
            krs_ir::ProtocolHeadRuleExtra::HaveMap { cell, key, .. } => {
                let expected = map_argument_sorts
                    .get(&cell.cell)
                    .map(|(key_sort, _)| key_sort);
                builder.infer(key, expected, true)?;
            }
            krs_ir::ProtocolHeadRuleExtra::UpdateMap {
                cell,
                base_binding,
                update,
            } => {
                let expected = cell_sorts.get(&cell.cell).ok_or_else(|| {
                    DescriptorLoweringError::UnsupportedShape {
                        node: "head-anchored rule extra",
                        detail: format!("updated cell {:?} is not a fixed leaf", cell.cell.field),
                    }
                })?;
                builder.infer_collection_update(
                    update,
                    base_binding,
                    expected,
                    map_argument_sorts.get(&cell.cell),
                )?;
            }
            krs_ir::ProtocolHeadRuleExtra::RewriteCell {
                cell,
                before,
                after,
                ..
            } => {
                let expected = cell_sorts.get(&cell.cell).ok_or_else(|| {
                    DescriptorLoweringError::UnsupportedShape {
                        node: "head-anchored rule extra",
                        detail: format!("ordinary cell {:?} is not a fixed leaf", cell.cell.field),
                    }
                })?;
                builder.infer(before, Some(expected), true)?;
                builder.infer(after, Some(expected), false)?;
            }
        }
    }
    let bool_sort = SemanticSortRef::Builtin(BuiltinSort::Bool);
    if let Some(requires) = &rule.requires {
        builder.infer(&requires.term, Some(&bool_sort), false)?;
    }
    builder.resolve_binding_sorts()?;
    for binding in &rule.bindings {
        if !builder.binding_sorts.contains_key(&binding.name) {
            return Err(DescriptorLoweringError::InvalidTerm {
                id: Box::new(descriptor.id.clone()),
                detail: format!("binding {:?} has no inferred semantic sort", binding.name),
            });
        }
    }

    let subject_head = builder.lower(&rule.subject, head_sort.as_ref(), true)?;
    let subject_item_sort = subject_head.sort().clone();
    let before_k = SemanticTerm::k_sequence(
        semantic_origin(descriptor, rule.pattern_key.clone(), "completed-k-subject")?,
        subject_item_sort,
        vec![subject_head],
    );
    let result_items = match &rule.result {
        krs_ir::ProtocolHeadRuleResult::Replace(term) => {
            vec![builder.lower(term, head_sort.as_ref(), false)?]
        }
        krs_ir::ProtocolHeadRuleResult::Splice(items) => items
            .iter()
            .map(|term| builder.lower(term, head_sort.as_ref(), false))
            .collect::<Result<Vec<_>, _>>()?,
        krs_ir::ProtocolHeadRuleResult::Erase => Vec::new(),
    };
    let result_item_sort = common_sequence_item_sort(descriptor, &result_items, sort_parents)?;
    let after_k = SemanticTerm::k_sequence(
        semantic_origin(descriptor, rule.result_key.clone(), "completed-k-result")?,
        result_item_sort,
        result_items,
    );
    let mut clauses = vec![FixedCellClause::new(
        semantic_origin(descriptor, rule.pattern_key.clone(), "completed-k-clause")?,
        semantic_cell_id(&rule.computation_cell.cell)?,
        before_k,
        CellPost::Replace { term: after_k },
        CellContentFrame::KSequenceTail {
            origin: semantic_origin(descriptor, rule.pattern_key.clone(), "implicit-k-tail")?,
            binding: None,
        },
    )];
    let mut selected = BTreeSet::from([rule.computation_cell.cell.clone()]);
    for extra in &rule.extras {
        let cell_reference = match extra {
            krs_ir::ProtocolHeadRuleExtra::HaveMap { cell, .. }
            | krs_ir::ProtocolHeadRuleExtra::UpdateMap { cell, .. }
            | krs_ir::ProtocolHeadRuleExtra::RewriteCell { cell, .. } => cell,
        };
        if !selected.insert(cell_reference.cell.clone()) {
            return Err(DescriptorLoweringError::UnsupportedShape {
                node: "head-anchored rule",
                detail: format!(
                    "cell {:?} is mentioned more than once",
                    cell_reference.cell.field
                ),
            });
        }
        let declared = require_cell_field(&cell_reference.cell, declarations)?;
        let ProtocolCellContent::Leaf { wrapper, sort, .. } = &declared.content else {
            return Err(DescriptorLoweringError::UnsupportedShape {
                node: "head-anchored rule extra",
                detail: "extra cell is not a fixed leaf".into(),
            });
        };
        match extra {
            krs_ir::ProtocolHeadRuleExtra::HaveMap {
                cell,
                key,
                value_binding,
            } => {
                if *wrapper != krs_ir::CellWrapper::Cell
                    || sort.sort != DescriptorSortRef::Builtin(BuiltinSort::Map)
                {
                    return Err(DescriptorLoweringError::UnsupportedShape {
                        node: "head-anchored rule extra",
                        detail: format!(
                            "extra cell {:?} is not a Map cell",
                            cell_reference.cell.field
                        ),
                    });
                }
                let key = builder.lower(key, None, true)?;
                let value_sort = builder
                    .binding_sorts
                    .get(value_binding)
                    .cloned()
                    .ok_or_else(|| DescriptorLoweringError::InvalidTerm {
                        id: Box::new(descriptor.id.clone()),
                        detail: format!("map value binding {value_binding:?} has no inferred sort"),
                    })?;
                let value = SemanticTerm::variable(
                    semantic_origin(descriptor, cell.key.clone(), "map-binding-value")?,
                    value_sort,
                    SemanticId::new(value_binding.clone())?,
                );
                clauses.push(FixedCellClause::new(
                    semantic_origin(descriptor, cell.key.clone(), "completed-map-read")?,
                    semantic_cell_id(&cell.cell)?,
                    SemanticTerm::map(
                        semantic_origin(descriptor, cell.key.clone(), "completed-map-item")?,
                        MapOperation::Item,
                        vec![key, value],
                    ),
                    CellPost::Preserve,
                    CellContentFrame::MapRemainder {
                        origin: semantic_origin(
                            descriptor,
                            cell.key.clone(),
                            "implicit-map-remainder",
                        )?,
                        binding: None,
                    },
                ));
            }
            krs_ir::ProtocolHeadRuleExtra::UpdateMap {
                cell,
                base_binding,
                update,
            } => {
                if *wrapper != krs_ir::CellWrapper::Cell
                    || !matches!(
                        sort.sort,
                        DescriptorSortRef::Builtin(BuiltinSort::Map | BuiltinSort::List)
                    )
                {
                    return Err(DescriptorLoweringError::UnsupportedShape {
                        node: "head-anchored rule extra",
                        detail: format!(
                            "updated cell {:?} is not a Map or List cell",
                            cell_reference.cell.field
                        ),
                    });
                }
                let expected = semantic_sort_ref(&sort.sort);
                let (before_role, write_role) =
                    if sort.sort == DescriptorSortRef::Builtin(BuiltinSort::Map) {
                        ("map-update-before", "completed-map-write")
                    } else {
                        ("list-update-before", "completed-list-write")
                    };
                let before = SemanticTerm::variable(
                    semantic_origin(descriptor, cell.key.clone(), before_role)?,
                    expected.clone(),
                    SemanticId::new(base_binding.clone())?,
                );
                let after = builder.lower(update, Some(&expected), false)?;
                clauses.push(FixedCellClause::new(
                    semantic_origin(descriptor, cell.key.clone(), write_role)?,
                    semantic_cell_id(&cell.cell)?,
                    before,
                    CellPost::Replace { term: after },
                    CellContentFrame::Exact,
                ));
            }
            krs_ir::ProtocolHeadRuleExtra::RewriteCell {
                cell,
                result_key,
                before,
                after,
            } => {
                if *wrapper != krs_ir::CellWrapper::Cell {
                    return Err(DescriptorLoweringError::UnsupportedShape {
                        node: "head-anchored rule extra",
                        detail: format!(
                            "ordinary cell {:?} does not use the Cell wrapper",
                            cell_reference.cell.field
                        ),
                    });
                }
                let expected = semantic_sort_ref(&sort.sort);
                let before = builder.lower(before, Some(&expected), true)?;
                let after = builder.lower(after, Some(&expected), false)?;
                clauses.push(FixedCellClause::new(
                    semantic_origin(descriptor, cell.key.clone(), "completed-cell-rewrite")?,
                    semantic_cell_id(&cell.cell)?,
                    before,
                    CellPost::Replace { term: after },
                    CellContentFrame::Exact,
                ));
                let _ = semantic_origin(
                    descriptor,
                    result_key.clone(),
                    "completed-cell-rewrite-result",
                )?;
            }
        }
    }
    let mut all_leaves = Vec::new();
    collect_declared_leaf_identities(
        &configuration.declaration,
        declarations,
        &mut BTreeSet::new(),
        &mut all_leaves,
    )?;
    let omitted_siblings = all_leaves
        .into_iter()
        .filter(|identity| !selected.contains(identity))
        .map(|identity| semantic_cell_id(&identity))
        .collect::<Result<Vec<_>, _>>()?;
    let body = FixedConfigurationRewrite::new(
        semantic_origin(
            descriptor,
            rule.pattern_key.clone(),
            "completed-configuration-rewrite",
        )?,
        generated_semantic_id("configuration", &rule.configuration, None)?,
        clauses,
        omitted_siblings,
    )?;
    let requires = rule
        .requires
        .as_ref()
        .map(|condition| -> Result<_, DescriptorLoweringError> {
            Ok(SemanticRuleCondition::new(
                semantic_origin(descriptor, condition.key.clone(), "rule-requires")?,
                builder.lower(&condition.term, Some(&bool_sort), false)?,
            ))
        })
        .transpose()?;
    let priority = rule
        .priority
        .as_ref()
        .map(|priority| -> Result<_, DescriptorLoweringError> {
            Ok(SemanticRulePriority::new(
                semantic_origin(descriptor, priority.key.clone(), "rule-owise")?,
                priority.value,
            ))
        })
        .transpose()?;
    let mut variables = rule
        .bindings
        .iter()
        .map(|binding| {
            Ok(SemanticVariable::new(
                SemanticId::new(binding.name.clone())?,
                builder
                    .binding_sorts
                    .get(&binding.name)
                    .cloned()
                    .expect("all binding sorts were inferred"),
            ))
        })
        .collect::<Result<Vec<_>, DescriptorLoweringError>>()?;
    variables.append(&mut builder.wildcards);
    Ok(SemanticRule::new_configuration(
        semantic_origin(
            descriptor,
            role_key(ProvenanceRole::RuleDeclaration, 0)?,
            "head-anchored-rule",
        )?,
        descriptor.id.clone(),
        rule.sentence_kind,
        variables,
        body,
    )?
    .with_label(lower_rule_label(descriptor, rule.label.as_ref())?)
    .with_priority(priority)?
    .with_requires(requires)?)
}

#[allow(clippy::too_many_lines)]
fn lower_configuration_rule_descriptor(
    descriptor: &Descriptor,
    rule: &krs_ir::DescriptorConfigurationRule,
    declarations: &BTreeMap<StableItemId, &Descriptor>,
    sort_parents: &BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
) -> Result<SemanticRule, DescriptorLoweringError> {
    let configuration_descriptor = require_descriptor(
        &rule.subject_configuration.configuration,
        ItemKind::Configuration,
        declarations,
    )?;
    let DescriptorPayload::FixedConfiguration(configuration) = &configuration_descriptor.payload
    else {
        return Err(DescriptorLoweringError::UnsupportedShape {
            node: "configuration rule",
            detail: "configuration rules require a fixed configuration".into(),
        });
    };

    let mut binding_sorts = BTreeMap::new();
    let mut variables = Vec::new();
    for binding in &rule.bindings {
        let sort = match &binding.kind {
            ProtocolRuleBindingKind::Term { sort } => semantic_sort_ref(&sort.sort),
            ProtocolRuleBindingKind::KSequenceFrame => SemanticSortRef::k_sequence(),
            ProtocolRuleBindingKind::MapFrame => SemanticSortRef::map(),
            ProtocolRuleBindingKind::ConfigurationFrame => continue,
        };
        if matches!(binding.kind, ProtocolRuleBindingKind::Term { .. }) {
            binding_sorts.insert(binding.name.clone(), sort.clone());
        }
        variables.push(SemanticVariable::new(
            SemanticId::new(binding.name.clone())?,
            sort,
        ));
    }
    let mut result_binding_sorts = binding_sorts.clone();
    if let Some(claim) = &rule.claim {
        for binder in &claim.existentials {
            let sort = semantic_sort_ref(&binder.sort.sort);
            result_binding_sorts.insert(binder.name.clone(), sort.clone());
            variables.push(SemanticVariable::new(
                SemanticId::new(binder.name.clone())?,
                sort,
            ));
        }
    }

    let subject_cells = rule
        .subject
        .cells
        .iter()
        .map(|cell| (&cell.field.cell, cell))
        .collect::<BTreeMap<_, _>>();
    let result_cells = rule
        .result
        .cells
        .iter()
        .map(|cell| (&cell.field.cell, cell))
        .collect::<BTreeMap<_, _>>();
    if result_cells
        .keys()
        .any(|identity| !subject_cells.contains_key(identity))
    {
        return Err(DescriptorLoweringError::UnsupportedShape {
            node: "configuration rule",
            detail: "the result selects a fixed cell absent from the subject".into(),
        });
    }
    validate_frame_pair(
        descriptor,
        &rule.subject.remainder,
        &rule.result.remainder,
        "configuration remainder",
    )?;

    let mut clauses = Vec::with_capacity(rule.subject.cells.len());
    let mut wildcard_ordinal = 0;
    for subject in &rule.subject.cells {
        let declared = require_cell_field(&subject.field.cell, declarations)?;
        let ProtocolCellContent::Leaf { wrapper, sort, .. } = &declared.content else {
            return Err(DescriptorLoweringError::UnsupportedShape {
                node: "configuration rule cell",
                detail: "rules over nominal parent cells are not represented by fixed-cell clauses"
                    .into(),
            });
        };
        let result = result_cells.get(&subject.field.cell).copied();
        if subject.wrapper != *wrapper || result.is_some_and(|result| result.wrapper != *wrapper) {
            return Err(DescriptorLoweringError::ParserReferenceDisagreement {
                id: Box::new(subject.field.cell.owner.clone()),
                detail: format!(
                    "rule wrapper disagrees with declared cell {:?}",
                    subject.field.cell.field
                ),
            });
        }
        let declared_sort = semantic_sort_ref(&sort.sort);
        let before = lower_rule_state_term(
            descriptor,
            &subject.value,
            &declared_sort,
            &subject.field.key,
            declarations,
            sort_parents,
            catalog,
            &binding_sorts,
            true,
            &mut wildcard_ordinal,
            &mut variables,
        )?;
        let subject_frame = rule_state_frame(&subject.value);
        let frame = lower_subject_cell_frame(descriptor, &subject.value)?;
        let post = if let Some(result) = result {
            let after = lower_rule_state_term(
                descriptor,
                &result.value,
                &declared_sort,
                &result.field.key,
                declarations,
                sort_parents,
                catalog,
                &result_binding_sorts,
                false,
                &mut wildcard_ordinal,
                &mut variables,
            )?;
            let result_frame = rule_state_frame(&result.value);
            validate_state_frame_pair(
                descriptor,
                subject_frame,
                result_frame,
                "cell content frame",
            )?;
            if semantic_terms_equivalent(&before, &after) {
                CellPost::Preserve
            } else {
                CellPost::Replace { term: after }
            }
        } else {
            CellPost::Preserve
        };
        clauses.push(FixedCellClause::new(
            semantic_origin(descriptor, subject.field.key.clone(), "rule-cell-clause")?,
            semantic_cell_id(&subject.field.cell)?,
            before,
            post,
            frame,
        ));
    }

    let selected = subject_cells
        .keys()
        .copied()
        .cloned()
        .collect::<BTreeSet<_>>();
    let mut all_leaves = Vec::new();
    collect_declared_leaf_identities(
        &configuration.declaration,
        declarations,
        &mut BTreeSet::new(),
        &mut all_leaves,
    )?;
    let omitted_siblings = all_leaves
        .into_iter()
        .filter(|identity| !selected.contains(identity))
        .map(|identity| semantic_cell_id(&identity))
        .collect::<Result<Vec<_>, _>>()?;
    if matches!(rule.subject.remainder, ProtocolRuleFrame::Exact) && !omitted_siblings.is_empty() {
        return Err(DescriptorLoweringError::UnsupportedShape {
            node: "configuration rule remainder",
            detail: "an exact subject must select every fixed leaf cell".into(),
        });
    }

    let body = FixedConfigurationRewrite::new(
        semantic_origin(
            descriptor,
            rule.pattern_key.clone(),
            "configuration-rewrite",
        )?,
        generated_semantic_id(
            "configuration",
            &rule.subject_configuration.configuration,
            None,
        )?,
        clauses,
        omitted_siblings,
    )?;
    let bool_sort = SemanticSortRef::Builtin(BuiltinSort::Bool);
    let requires = rule
        .requires
        .as_ref()
        .map(|condition| -> Result<_, DescriptorLoweringError> {
            Ok(SemanticRuleCondition::new(
                semantic_origin(descriptor, condition.key.clone(), "rule-requires")?,
                lower_rule_descriptor_term(
                    descriptor,
                    &condition.term,
                    Some(&bool_sort),
                    declarations,
                    sort_parents,
                    catalog,
                    &binding_sorts,
                    false,
                    &mut wildcard_ordinal,
                    &mut variables,
                )?,
            ))
        })
        .transpose()?;
    let priority = rule
        .priority
        .as_ref()
        .map(|priority| -> Result<_, DescriptorLoweringError> {
            Ok(SemanticRulePriority::new(
                semantic_origin(descriptor, priority.key.clone(), "rule-owise")?,
                priority.value,
            ))
        })
        .transpose()?;
    let claim = rule
        .claim
        .as_ref()
        .map(|claim| -> Result<_, DescriptorLoweringError> {
            let universals = claim
                .universals
                .iter()
                .map(|binder| {
                    Ok(krs_ir::SemanticClaimBinder::new(
                        semantic_origin(
                            descriptor,
                            binder.declaration_key.clone(),
                            "claim-universal-binder",
                        )?,
                        semantic_origin(descriptor, binder.name_key.clone(), "claim-binder-name")?,
                        SemanticId::new(binder.name.clone())?,
                        semantic_origin(descriptor, binder.sort.key.clone(), "claim-binder-sort")?,
                        semantic_sort_ref(&binder.sort.sort),
                    ))
                })
                .collect::<Result<Vec<_>, DescriptorLoweringError>>()?;
            let existentials = claim
                .existentials
                .iter()
                .map(|binder| {
                    Ok(krs_ir::SemanticClaimBinder::new(
                        semantic_origin(
                            descriptor,
                            binder.declaration_key.clone(),
                            "claim-existential-binder",
                        )?,
                        semantic_origin(descriptor, binder.name_key.clone(), "claim-binder-name")?,
                        SemanticId::new(binder.name.clone())?,
                        semantic_origin(descriptor, binder.sort.key.clone(), "claim-binder-sort")?,
                        semantic_sort_ref(&binder.sort.sort),
                    ))
                })
                .collect::<Result<Vec<_>, DescriptorLoweringError>>()?;
            let ensures = claim
                .ensures
                .as_ref()
                .map(|condition| -> Result<_, DescriptorLoweringError> {
                    Ok(SemanticRuleCondition::new(
                        semantic_origin(descriptor, condition.key.clone(), "claim-ensures")?,
                        lower_rule_descriptor_term(
                            descriptor,
                            &condition.term,
                            Some(&bool_sort),
                            declarations,
                            sort_parents,
                            catalog,
                            &result_binding_sorts,
                            false,
                            &mut wildcard_ordinal,
                            &mut variables,
                        )?,
                    ))
                })
                .transpose()?;
            Ok(krs_ir::SemanticClaim::new(
                semantic_origin(descriptor, claim.modality_key.clone(), "claim-modality")?,
                claim.modality,
                claim
                    .circularity_key
                    .as_ref()
                    .map(|key| semantic_origin(descriptor, key.clone(), "claim-circularity"))
                    .transpose()?,
                universals,
                existentials,
                ensures,
            ))
        })
        .transpose()?;
    Ok(SemanticRule::new_configuration(
        semantic_origin(
            descriptor,
            role_key(
                if rule.sentence_kind == krs_ir::SentenceKind::Claim {
                    ProvenanceRole::ClaimDeclaration
                } else {
                    ProvenanceRole::RuleDeclaration
                },
                0,
            )?,
            "configuration-rule",
        )?,
        descriptor.id.clone(),
        rule.sentence_kind,
        variables,
        body,
    )?
    .with_label(lower_rule_label(descriptor, rule.label.as_ref())?)
    .with_priority(priority)?
    .with_requires(requires)?
    .with_claim(claim))
}

#[allow(clippy::too_many_lines)]
fn lower_context_alias_descriptor(
    descriptor: &Descriptor,
    alias: &krs_ir::DescriptorContextAlias,
    declarations: &BTreeMap<StableItemId, &Descriptor>,
    sort_parents: &BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
) -> Result<SemanticContextAlias, DescriptorLoweringError> {
    let configuration_descriptor = require_descriptor(
        &alias.configuration.configuration,
        ItemKind::Configuration,
        declarations,
    )?;
    let DescriptorPayload::FixedConfiguration(configuration) = &configuration_descriptor.payload
    else {
        return Err(DescriptorLoweringError::UnsupportedShape {
            node: "context alias",
            detail: "context aliases require a fixed configuration".into(),
        });
    };
    let k_items = declarations
        .keys()
        .filter(|id| id.item_kind() == ItemKind::Sort && id.item_name() == "KItem")
        .collect::<Vec<_>>();
    let [k_item] = k_items.as_slice() else {
        return Err(DescriptorLoweringError::UnsupportedShape {
            node: "context alias",
            detail: "context aliases require exactly one declared KItem sort".into(),
        });
    };
    let mut binding_sorts = BTreeMap::new();
    let mut variables = Vec::new();
    for binding in &alias.bindings {
        let sort = match &binding.kind {
            ProtocolContextAliasBindingKind::Here => SemanticSortRef::Declared((**k_item).clone()),
            ProtocolContextAliasBindingKind::Term { sort } => semantic_sort_ref(&sort.sort),
            ProtocolContextAliasBindingKind::KSequenceFrame => SemanticSortRef::k_sequence(),
            ProtocolContextAliasBindingKind::MapFrame => SemanticSortRef::map(),
            ProtocolContextAliasBindingKind::ConfigurationFrame => continue,
        };
        if matches!(
            binding.kind,
            ProtocolContextAliasBindingKind::Here | ProtocolContextAliasBindingKind::Term { .. }
        ) {
            binding_sorts.insert(binding.name.clone(), sort.clone());
        }
        variables.push(SemanticVariable::new(
            SemanticId::new(binding.name.clone())?,
            sort,
        ));
    }
    let mut cells = Vec::with_capacity(alias.pattern.cells.len());
    let mut wildcard_ordinal = 0;
    for pattern in &alias.pattern.cells {
        let declared = require_cell_field(&pattern.field.cell, declarations)?;
        let ProtocolCellContent::Leaf { wrapper, sort, .. } = &declared.content else {
            return Err(DescriptorLoweringError::UnsupportedShape {
                node: "context alias cell",
                detail: "context aliases select leaf cells only".into(),
            });
        };
        if pattern.wrapper != *wrapper {
            return Err(DescriptorLoweringError::ParserReferenceDisagreement {
                id: Box::new(pattern.field.cell.owner.clone()),
                detail: "context-alias wrapper disagrees with its cell declaration".into(),
            });
        }
        let term = lower_rule_state_term(
            descriptor,
            &pattern.value,
            &semantic_sort_ref(&sort.sort),
            &pattern.field.key,
            declarations,
            sort_parents,
            catalog,
            &binding_sorts,
            true,
            &mut wildcard_ordinal,
            &mut variables,
        )?;
        cells.push(FixedCellPattern::new(
            semantic_origin(descriptor, pattern.field.key.clone(), "context-alias-cell")?,
            semantic_cell_id(&pattern.field.cell)?,
            term,
            lower_subject_cell_frame(descriptor, &pattern.value)?,
        ));
    }
    let selected = alias
        .pattern
        .cells
        .iter()
        .map(|cell| cell.field.cell.clone())
        .collect::<BTreeSet<_>>();
    let mut all_leaves = Vec::new();
    collect_declared_leaf_identities(
        &configuration.declaration,
        declarations,
        &mut BTreeSet::new(),
        &mut all_leaves,
    )?;
    let omitted_siblings = all_leaves
        .into_iter()
        .filter(|identity| !selected.contains(identity))
        .map(|identity| semantic_cell_id(&identity))
        .collect::<Result<Vec<_>, _>>()?;
    if matches!(alias.pattern.remainder, ProtocolRuleFrame::Exact) && !omitted_siblings.is_empty() {
        return Err(DescriptorLoweringError::UnsupportedShape {
            node: "context alias remainder",
            detail: "an exact pattern must select every fixed leaf cell".into(),
        });
    }
    let body = FixedConfigurationPattern::new(
        semantic_origin(
            descriptor,
            alias.pattern_key.clone(),
            "context-alias-pattern",
        )?,
        generated_semantic_id("configuration", &alias.configuration.configuration, None)?,
        cells,
        omitted_siblings,
    )?;
    Ok(SemanticContextAlias::new(
        semantic_origin(descriptor, alias.declaration_key.clone(), "context-alias")?,
        descriptor.id.clone(),
        semantic_origin(descriptor, alias.name_key.clone(), "context-alias-name")?,
        alias.name.clone(),
        semantic_origin(descriptor, alias.here_key.clone(), "context-alias-here")?,
        SemanticId::new(alias.here.clone())?,
        variables,
        body,
    ))
}

#[allow(clippy::too_many_arguments)]
#[allow(clippy::too_many_lines)]
fn lower_rule_state_term(
    descriptor: &Descriptor,
    state: &ProtocolRuleStateTerm<DescriptorTerm>,
    declared_sort: &SemanticSortRef,
    fallback_key: &ProvenanceKey,
    declarations: &BTreeMap<StableItemId, &Descriptor>,
    sort_parents: &BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
    binding_sorts: &BTreeMap<String, SemanticSortRef>,
    subject: bool,
    wildcard_ordinal: &mut usize,
    variables: &mut Vec<SemanticVariable>,
) -> Result<SemanticTerm, DescriptorLoweringError> {
    match state {
        ProtocolRuleStateTerm::Term(term) => lower_rule_descriptor_term(
            descriptor,
            term,
            Some(declared_sort),
            declarations,
            sort_parents,
            catalog,
            binding_sorts,
            subject,
            wildcard_ordinal,
            variables,
        ),
        ProtocolRuleStateTerm::KSequence(sequence) => {
            if *declared_sort != SemanticSortRef::k_sequence() {
                return Err(DescriptorLoweringError::InvalidTerm {
                    id: Box::new(descriptor.id.clone()),
                    detail: "K sequence occurs in a non-KSequence rule cell".into(),
                });
            }
            let items = sequence
                .items
                .iter()
                .map(|item| {
                    lower_rule_descriptor_term(
                        descriptor,
                        &item.value,
                        None,
                        declarations,
                        sort_parents,
                        catalog,
                        binding_sorts,
                        subject,
                        wildcard_ordinal,
                        variables,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?;
            let item_sort = common_sequence_item_sort(descriptor, &items, sort_parents)?;
            let key = sequence
                .payload_key
                .as_ref()
                .or(sequence.dot_k_key.as_ref())
                .unwrap_or(fallback_key);
            Ok(SemanticTerm::k_sequence(
                semantic_origin(descriptor, key.clone(), "rule-k-sequence")?,
                item_sort,
                items,
            ))
        }
        ProtocolRuleStateTerm::Map(map) => {
            if *declared_sort != SemanticSortRef::map() {
                return Err(DescriptorLoweringError::InvalidTerm {
                    id: Box::new(descriptor.id.clone()),
                    detail: "map occurs in a non-Map rule cell".into(),
                });
            }
            let key = map.payload_key.as_ref().unwrap_or(fallback_key);
            let (operation, arguments) = match &map.body {
                ProtocolRuleMapBody::Empty { .. } => (MapOperation::Empty, Vec::new()),
                ProtocolRuleMapBody::Items { items, .. } => {
                    let mut arguments = Vec::with_capacity(items.len() * 2);
                    for item in items {
                        arguments.push(lower_rule_descriptor_term(
                            descriptor,
                            &item.key,
                            None,
                            declarations,
                            sort_parents,
                            catalog,
                            binding_sorts,
                            subject,
                            wildcard_ordinal,
                            variables,
                        )?);
                        arguments.push(lower_rule_descriptor_term(
                            descriptor,
                            &item.value,
                            None,
                            declarations,
                            sort_parents,
                            catalog,
                            binding_sorts,
                            subject,
                            wildcard_ordinal,
                            variables,
                        )?);
                    }
                    (MapOperation::Item, arguments)
                }
                ProtocolRuleMapBody::Update {
                    base, key, value, ..
                } => (
                    MapOperation::Update,
                    vec![
                        lower_rule_descriptor_term(
                            descriptor,
                            base,
                            Some(&SemanticSortRef::map()),
                            declarations,
                            sort_parents,
                            catalog,
                            binding_sorts,
                            subject,
                            wildcard_ordinal,
                            variables,
                        )?,
                        lower_rule_descriptor_term(
                            descriptor,
                            key,
                            None,
                            declarations,
                            sort_parents,
                            catalog,
                            binding_sorts,
                            subject,
                            wildcard_ordinal,
                            variables,
                        )?,
                        lower_rule_descriptor_term(
                            descriptor,
                            value,
                            None,
                            declarations,
                            sort_parents,
                            catalog,
                            binding_sorts,
                            subject,
                            wildcard_ordinal,
                            variables,
                        )?,
                    ],
                ),
            };
            Ok(SemanticTerm::map(
                semantic_origin(descriptor, key.clone(), "rule-map")?,
                operation,
                arguments,
            ))
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum AssociativeStateFamily {
    KSequence,
    Map,
}

#[derive(Clone, Copy, Debug)]
enum RuleStateFrame<'a> {
    // Exactness is independent of surface notation: an ordinary whole-Map
    // term, `.Map`, exact map items, and a functional update all omit no
    // content. The declared cell sort validates their semantic family.
    Exact,
    Framed {
        family: AssociativeStateFamily,
        frame: &'a ProtocolRuleFrame,
    },
}

fn associative_state_frame(
    family: AssociativeStateFamily,
    frame: &ProtocolRuleFrame,
) -> RuleStateFrame<'_> {
    if matches!(frame, ProtocolRuleFrame::Exact) {
        RuleStateFrame::Exact
    } else {
        RuleStateFrame::Framed { family, frame }
    }
}

fn rule_state_frame(state: &ProtocolRuleStateTerm<DescriptorTerm>) -> RuleStateFrame<'_> {
    match state {
        ProtocolRuleStateTerm::Term(_) => RuleStateFrame::Exact,
        ProtocolRuleStateTerm::KSequence(sequence) => {
            associative_state_frame(AssociativeStateFamily::KSequence, &sequence.tail)
        }
        ProtocolRuleStateTerm::Map(map) => match &map.body {
            ProtocolRuleMapBody::Items { remainder, .. } => {
                associative_state_frame(AssociativeStateFamily::Map, remainder)
            }
            ProtocolRuleMapBody::Empty { .. } | ProtocolRuleMapBody::Update { .. } => {
                RuleStateFrame::Exact
            }
        },
    }
}

fn lower_subject_cell_frame(
    descriptor: &Descriptor,
    state: &ProtocolRuleStateTerm<DescriptorTerm>,
) -> Result<CellContentFrame, DescriptorLoweringError> {
    match rule_state_frame(state) {
        RuleStateFrame::Exact => Ok(CellContentFrame::Exact),
        RuleStateFrame::Framed {
            family: AssociativeStateFamily::KSequence,
            frame: ProtocolRuleFrame::Anonymous { key },
        } => Ok(CellContentFrame::KSequenceTail {
            origin: semantic_origin(descriptor, key.clone(), "rule-k-frame")?,
            binding: None,
        }),
        RuleStateFrame::Framed {
            family: AssociativeStateFamily::KSequence,
            frame: ProtocolRuleFrame::Bind { key, binding },
        } => Ok(CellContentFrame::KSequenceTail {
            origin: semantic_origin(descriptor, key.clone(), "rule-k-frame")?,
            binding: Some(SemanticId::new(binding.clone())?),
        }),
        RuleStateFrame::Framed {
            family: AssociativeStateFamily::Map,
            frame: ProtocolRuleFrame::Anonymous { key },
        } => Ok(CellContentFrame::MapRemainder {
            origin: semantic_origin(descriptor, key.clone(), "rule-map-frame")?,
            binding: None,
        }),
        RuleStateFrame::Framed {
            family: AssociativeStateFamily::Map,
            frame: ProtocolRuleFrame::Bind { key, binding },
        } => Ok(CellContentFrame::MapRemainder {
            origin: semantic_origin(descriptor, key.clone(), "rule-map-frame")?,
            binding: Some(SemanticId::new(binding.clone())?),
        }),
        RuleStateFrame::Framed {
            frame: ProtocolRuleFrame::Reuse { .. },
            ..
        } => Err(DescriptorLoweringError::UnsupportedShape {
            node: "subject cell frame",
            detail: "a subject frame cannot reuse a result binding".into(),
        }),
        RuleStateFrame::Framed {
            frame: ProtocolRuleFrame::Exact,
            ..
        } => unreachable!("exact associative frames are normalized"),
    }
}

fn state_frames_compatible(subject: RuleStateFrame<'_>, result: RuleStateFrame<'_>) -> bool {
    match (subject, result) {
        (
            RuleStateFrame::Exact
            | RuleStateFrame::Framed {
                frame: ProtocolRuleFrame::Anonymous { .. },
                ..
            },
            RuleStateFrame::Exact,
        ) => true,
        (
            RuleStateFrame::Framed {
                family: subject_family,
                frame:
                    ProtocolRuleFrame::Bind {
                        binding: subject, ..
                    },
            },
            RuleStateFrame::Framed {
                family: result_family,
                frame:
                    ProtocolRuleFrame::Reuse {
                        binding: result, ..
                    },
            },
        ) => subject_family == result_family && subject == result,
        _ => false,
    }
}

fn validate_state_frame_pair(
    descriptor: &Descriptor,
    subject: RuleStateFrame<'_>,
    result: RuleStateFrame<'_>,
    node: &'static str,
) -> Result<(), DescriptorLoweringError> {
    if state_frames_compatible(subject, result) {
        Ok(())
    } else {
        Err(DescriptorLoweringError::UnsupportedShape {
            node,
            detail: format!(
                "rule {:?} uses incompatible subject/result associative state families or frames",
                descriptor.id
            ),
        })
    }
}

fn validate_frame_pair(
    descriptor: &Descriptor,
    subject: &ProtocolRuleFrame,
    result: &ProtocolRuleFrame,
    node: &'static str,
) -> Result<(), DescriptorLoweringError> {
    let supported = match (subject, result) {
        (
            ProtocolRuleFrame::Exact | ProtocolRuleFrame::Anonymous { .. },
            ProtocolRuleFrame::Exact,
        ) => true,
        (
            ProtocolRuleFrame::Bind {
                binding: subject, ..
            },
            ProtocolRuleFrame::Reuse {
                binding: result, ..
            },
        ) => subject == result,
        _ => false,
    };
    if supported {
        Ok(())
    } else {
        Err(DescriptorLoweringError::UnsupportedShape {
            node,
            detail: format!(
                "rule {:?} uses incompatible subject/result frames",
                descriptor.id
            ),
        })
    }
}

fn collect_declared_leaf_identities(
    declaration: &DescriptorCellDeclaration,
    declarations: &BTreeMap<StableItemId, &Descriptor>,
    visiting: &mut BTreeSet<StableItemId>,
    leaves: &mut Vec<DescriptorCellIdentity>,
) -> Result<(), DescriptorLoweringError> {
    for field in &declaration.fields {
        match &field.content {
            ProtocolCellContent::Leaf { .. } => leaves.push(field.reference.cell.clone()),
            ProtocolCellContent::Nested { declaration } => {
                if !visiting.insert(declaration.declaration.clone()) {
                    return Err(DescriptorLoweringError::UnsupportedShape {
                        node: "nested cell declaration",
                        detail: "cyclic nominal cell declaration".into(),
                    });
                }
                let descriptor =
                    require_descriptor(&declaration.declaration, ItemKind::Cell, declarations)?;
                let DescriptorPayload::Cell(nested) = &descriptor.payload else {
                    unreachable!("kind-checked descriptor has a cell payload")
                };
                collect_declared_leaf_identities(nested, declarations, visiting, leaves)?;
                visiting.remove(&declaration.declaration);
            }
        }
    }
    Ok(())
}

fn semantic_terms_equivalent(left: &SemanticTerm, right: &SemanticTerm) -> bool {
    if left.sort() != right.sort() {
        return false;
    }
    match (left.kind(), right.kind()) {
        (
            krs_ir::SemanticTermKind::Variable { variable: left },
            krs_ir::SemanticTermKind::Variable { variable: right },
        ) => left == right,
        (
            krs_ir::SemanticTermKind::Application {
                application: left_application,
                arguments: left_arguments,
            },
            krs_ir::SemanticTermKind::Application {
                application: right_application,
                arguments: right_arguments,
            },
        ) => {
            left_application == right_application
                && semantic_term_slices_equivalent(left_arguments, right_arguments)
        }
        (
            krs_ir::SemanticTermKind::Token { value: left },
            krs_ir::SemanticTermKind::Token { value: right },
        ) => left == right,
        (
            krs_ir::SemanticTermKind::KSequence {
                item_sort: left_sort,
                items: left_items,
            },
            krs_ir::SemanticTermKind::KSequence {
                item_sort: right_sort,
                items: right_items,
            },
        ) => left_sort == right_sort && semantic_term_slices_equivalent(left_items, right_items),
        (
            krs_ir::SemanticTermKind::Map {
                operation: left_operation,
                arguments: left_arguments,
            },
            krs_ir::SemanticTermKind::Map {
                operation: right_operation,
                arguments: right_arguments,
            },
        ) => {
            left_operation == right_operation
                && semantic_term_slices_equivalent(left_arguments, right_arguments)
        }
        (
            krs_ir::SemanticTermKind::List {
                operation: left_operation,
                arguments: left_arguments,
            },
            krs_ir::SemanticTermKind::List {
                operation: right_operation,
                arguments: right_arguments,
            },
        ) => {
            left_operation == right_operation
                && semantic_term_slices_equivalent(left_arguments, right_arguments)
        }
        (
            krs_ir::SemanticTermKind::Set {
                operation: left_operation,
                arguments: left_arguments,
            },
            krs_ir::SemanticTermKind::Set {
                operation: right_operation,
                arguments: right_arguments,
            },
        ) => {
            left_operation == right_operation
                && semantic_term_slices_equivalent(left_arguments, right_arguments)
        }
        (
            krs_ir::SemanticTermKind::Rewrite {
                from: left_from,
                to: left_to,
            },
            krs_ir::SemanticTermKind::Rewrite {
                from: right_from,
                to: right_to,
            },
        ) => {
            semantic_terms_equivalent(left_from, right_from)
                && semantic_terms_equivalent(left_to, right_to)
        }
        _ => false,
    }
}

fn semantic_term_slices_equivalent(left: &[SemanticTerm], right: &[SemanticTerm]) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(left, right)| semantic_terms_equivalent(left, right))
}

#[allow(clippy::too_many_lines)] // One closed pass performs inference, lowering, and metadata.
fn lower_structured_rule_descriptor(
    descriptor: &Descriptor,
    rule: &StructuredRuleDescriptor,
    sort_parents: &BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
) -> Result<SemanticRule, DescriptorLoweringError> {
    let binding_names = rule.bindings.iter().cloned().collect::<BTreeSet<_>>();
    let mut builder = StructuredTermBuilder {
        descriptor,
        catalog,
        declarations: None,
        k_item_sort: None,
        sort_parents,
        binding_names: &binding_names,
        pattern_key: Some(&rule.pattern_key),
        binding_sorts: BTreeMap::new(),
        binding_constraints: BTreeMap::new(),
        wildcard_offset: 0,
        wildcards: Vec::new(),
    };
    let subject_sort = semantic_sort_ref(&rule.subject_sort.sort);
    let result_sort = semantic_sort_ref(&rule.result_sort.sort);
    let bool_sort = SemanticSortRef::Builtin(BuiltinSort::Bool);
    builder.infer(&rule.subject, Some(&subject_sort), true)?;
    if let Some(requires) = &rule.requires {
        builder.infer(&requires.term, Some(&bool_sort), false)?;
    }
    builder.infer(&rule.result, Some(&result_sort), false)?;
    builder.resolve_binding_sorts()?;
    let subject = builder.lower(&rule.subject, Some(&subject_sort), true)?;
    let result = builder.lower(&rule.result, Some(&result_sort), false)?;
    let requires = rule
        .requires
        .as_ref()
        .map(|condition| -> Result<_, DescriptorLoweringError> {
            Ok(SemanticRuleCondition::new(
                semantic_origin(descriptor, condition.key.clone(), "rule-requires")?,
                builder.lower(&condition.term, Some(&bool_sort), false)?,
            ))
        })
        .transpose()?;
    let priority = rule
        .priority
        .as_ref()
        .map(|priority| -> Result<_, DescriptorLoweringError> {
            Ok(SemanticRulePriority::new(
                semantic_origin(
                    descriptor,
                    priority.key.clone(),
                    if rule.sentence_kind == krs_ir::SentenceKind::Transition {
                        "rule-owise"
                    } else {
                        "equation-priority"
                    },
                )?,
                priority.value,
            ))
        })
        .transpose()?;
    let simplification = rule
        .simplification
        .as_ref()
        .map(|simplification| -> Result<_, DescriptorLoweringError> {
            let priority = simplification
                .priority
                .as_ref()
                .map(|priority| -> Result<_, DescriptorLoweringError> {
                    Ok(SemanticSimplificationPriority::new(
                        semantic_origin(
                            descriptor,
                            priority.key.clone(),
                            "simplification-priority",
                        )?,
                        priority.value,
                    ))
                })
                .transpose()?;
            Ok(SemanticSimplification::new(
                semantic_origin(descriptor, simplification.key.clone(), "simplification")?,
                priority,
            ))
        })
        .transpose()?;
    let mut variables = Vec::new();
    for binding in &rule.bindings {
        let sort = builder.binding_sorts.get(binding).cloned().ok_or_else(|| {
            DescriptorLoweringError::InvalidTerm {
                id: Box::new(descriptor.id.clone()),
                detail: format!("binding {binding:?} has no inferred subject sort"),
            }
        })?;
        variables.push(SemanticVariable::new(
            SemanticId::new(binding.clone())?,
            sort,
        ));
    }
    variables.extend(builder.wildcards);
    let rewrite = SemanticTerm::rewrite(
        semantic_origin_from_primary(descriptor, "rule-rewrite")?,
        result_sort,
        subject,
        result,
    )?;
    let rule_origin_role = if rule.sentence_kind == krs_ir::SentenceKind::Alias {
        ProvenanceRole::AliasClause
    } else {
        ProvenanceRole::RuleDeclaration
    };
    Ok(SemanticRule::new(
        semantic_origin(descriptor, role_key(rule_origin_role, 0)?, "rule")?,
        descriptor.id.clone(),
        rule.sentence_kind,
        variables,
        rewrite,
    )?
    .with_label(lower_rule_label(descriptor, rule.label.as_ref())?)
    .with_priority(priority)?
    .with_simplification(simplification)
    .with_requires(requires)?)
}

struct StructuredTermBuilder<'a> {
    descriptor: &'a Descriptor,
    catalog: &'a BTreeMap<StableItemId, ProductionSignature>,
    declarations: Option<&'a BTreeMap<StableItemId, &'a Descriptor>>,
    k_item_sort: Option<SemanticSortRef>,
    sort_parents: &'a BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
    binding_names: &'a BTreeSet<String>,
    pattern_key: Option<&'a ProvenanceKey>,
    /// Finalized inferred sorts.
    binding_sorts: BTreeMap<String, SemanticSortRef>,
    /// Author-declared and occurrence-derived upper-bound constraints.
    binding_constraints: BTreeMap<String, BTreeSet<SemanticSortRef>>,
    wildcard_offset: usize,
    wildcards: Vec<SemanticVariable>,
}

impl StructuredTermBuilder<'_> {
    #[allow(clippy::too_many_lines)] // Exhaustive inference over the closed descriptor-term grammar.
    fn infer(
        &mut self,
        term: &DescriptorTerm,
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<(), DescriptorLoweringError> {
        match term {
            DescriptorTerm::Variable { name, .. } => {
                if !self.binding_names.contains(name) {
                    return Err(self.invalid_term(format!("unbound variable {name:?}")));
                }
                if let Some(expected) = expected_sort {
                    self.binding_constraints
                        .entry(name.clone())
                        .or_default()
                        .insert(expected.clone());
                }
            }
            DescriptorTerm::Wildcard { .. } => {
                if !subject {
                    return Err(self.invalid_term("wildcard occurs outside the rule subject"));
                }
                if expected_sort.is_none() {
                    return Err(self.invalid_term("wildcard has no expected production-field sort"));
                }
            }
            DescriptorTerm::Literal { literal, .. } => {
                let sort = match literal {
                    krs_ir::DescriptorLiteral::Int(_) => SemanticSortRef::Builtin(BuiltinSort::Int),
                    krs_ir::DescriptorLiteral::Bool(_) => {
                        SemanticSortRef::Builtin(BuiltinSort::Bool)
                    }
                };
                if let Some(expected) = expected_sort
                    && !semantic_is_subsort(&sort, expected, self.sort_parents)
                {
                    return Err(self.invalid_term(format!(
                        "literal of sort {sort:?} is not admissible at sort {expected:?}"
                    )));
                }
            }
            DescriptorTerm::Application {
                reference,
                arguments,
                ..
            } => {
                let signature = match &reference.application {
                    DescriptorApplicationRef::Declared(id) => {
                        self.catalog.get(id).cloned().ok_or_else(|| {
                            self.invalid_term(format!(
                                "declared application {id:?} has no grammar production"
                            ))
                        })?
                    }
                    DescriptorApplicationRef::Builtin(operation) => {
                        builtin_production_signature(*operation)
                    }
                    DescriptorApplicationRef::Map(operation) => {
                        self.infer_map_operation(*operation, arguments, expected_sort, subject)?;
                        return Ok(());
                    }
                    DescriptorApplicationRef::List(operation) => {
                        self.infer_list_operation(*operation, arguments, expected_sort, subject)?;
                        return Ok(());
                    }
                    DescriptorApplicationRef::Set(operation) => {
                        self.infer_set_operation(*operation, arguments, expected_sort, subject)?;
                        return Ok(());
                    }
                };
                if let Some(expected) = expected_sort
                    && !semantic_is_subsort(&signature.result_sort, expected, self.sort_parents)
                {
                    return Err(self.invalid_term(format!(
                        "application result sort {:?} is not admissible at sort {expected:?}",
                        signature.result_sort
                    )));
                }
                let ordered = order_structured_arguments(arguments, &signature.fields, subject)
                    .map_err(|detail| self.invalid_term(detail))?;
                for (argument, (_, sort)) in ordered.into_iter().zip(&signature.fields) {
                    if let Some(argument) = argument {
                        self.infer(argument, Some(sort), subject)?;
                    }
                }
            }
            DescriptorTerm::BuiltinToken { sort, .. } => {
                let sort = SemanticSortRef::Builtin(*sort);
                if let Some(expected) = expected_sort
                    && !semantic_is_subsort(&sort, expected, self.sort_parents)
                {
                    return Err(self.invalid_term("builtin token has an incompatible sort"));
                }
            }
            DescriptorTerm::Anonymous { sort, .. } => {
                if !subject {
                    return Err(self.invalid_term("anonymous occurrence outside claim subject"));
                }
                let sort = semantic_sort_ref(&sort.sort);
                if let Some(expected) = expected_sort
                    && !semantic_is_subsort(&sort, expected, self.sort_parents)
                {
                    return Err(self.invalid_term("anonymous occurrence has an incompatible sort"));
                }
            }
            DescriptorTerm::OrBool { arguments, .. } => {
                if arguments.len() < 2 {
                    return Err(self.invalid_term("or_bool requires at least two operands"));
                }
                let bool_sort = SemanticSortRef::Builtin(BuiltinSort::Bool);
                if let Some(expected) = expected_sort
                    && !semantic_is_subsort(&bool_sort, expected, self.sort_parents)
                {
                    return Err(self.invalid_term("or_bool is not admissible at the expected sort"));
                }
                for argument in arguments {
                    self.infer(argument, Some(&bool_sort), subject)?;
                }
            }
            DescriptorTerm::Cell {
                declaration,
                fields,
                ..
            } => {
                let k_item = self.cell_k_item_sort()?;
                if let Some(expected) = expected_sort
                    && !semantic_is_subsort(&k_item, expected, self.sort_parents)
                {
                    return Err(self.invalid_term(
                        "complete cell term is not admissible at the expected sort",
                    ));
                }
                self.infer_cell_fields(declaration, fields, subject)?;
            }
        }
        Ok(())
    }

    fn infer_map_operation(
        &mut self,
        operation: MapOperation,
        arguments: &[DescriptorTermArgument],
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<(), DescriptorLoweringError> {
        let arguments = ordinary_map_arguments(operation, arguments)
            .map_err(|detail| self.invalid_term(detail))?;
        let map_sort = SemanticSortRef::Builtin(BuiltinSort::Map);
        let bool_sort = SemanticSortRef::Builtin(BuiltinSort::Bool);
        let result_sort = match operation {
            MapOperation::Get => expected_sort
                .cloned()
                .ok_or_else(|| self.invalid_term("map::get requires an expected result sort"))?,
            MapOperation::InKeys => bool_sort.clone(),
            MapOperation::Update => map_sort.clone(),
            MapOperation::Empty | MapOperation::Item => {
                return Err(self.invalid_term("structural Map operation used as an application"));
            }
        };
        if let Some(expected) = expected_sort
            && !semantic_is_subsort(&result_sort, expected, self.sort_parents)
        {
            return Err(self.invalid_term(format!(
                "Map operation result sort {result_sort:?} is not admissible at sort {expected:?}"
            )));
        }
        let operand_sorts: Vec<Option<&SemanticSortRef>> = match operation {
            MapOperation::Update => vec![Some(&map_sort), None, None],
            MapOperation::Get => vec![Some(&map_sort), None],
            MapOperation::InKeys => vec![None, Some(&map_sort)],
            MapOperation::Empty | MapOperation::Item => unreachable!("checked above"),
        };
        for (argument, expected) in arguments.into_iter().zip(operand_sorts) {
            self.infer(argument, expected, subject)?;
        }
        Ok(())
    }

    fn lower_map_operation(
        &mut self,
        reference: &krs_ir::DescriptorApplicationReference,
        operation: MapOperation,
        arguments: &[DescriptorTermArgument],
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let arguments = ordinary_map_arguments(operation, arguments)
            .map_err(|detail| self.invalid_term(detail))?;
        let map_sort = SemanticSortRef::Builtin(BuiltinSort::Map);
        let bool_sort = SemanticSortRef::Builtin(BuiltinSort::Bool);
        let result_sort = match operation {
            MapOperation::Get => expected_sort
                .cloned()
                .ok_or_else(|| self.invalid_term("map::get requires an expected result sort"))?,
            MapOperation::InKeys => bool_sort,
            MapOperation::Update => map_sort.clone(),
            MapOperation::Empty | MapOperation::Item => {
                return Err(self.invalid_term("structural Map operation used as an application"));
            }
        };
        let operand_sorts: Vec<Option<&SemanticSortRef>> = match operation {
            MapOperation::Update => vec![Some(&map_sort), None, None],
            MapOperation::Get => vec![Some(&map_sort), None],
            MapOperation::InKeys => vec![None, Some(&map_sort)],
            MapOperation::Empty | MapOperation::Item => unreachable!("checked above"),
        };
        let lowered = arguments
            .into_iter()
            .zip(operand_sorts)
            .map(|(argument, expected)| self.lower(argument, expected, subject))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(SemanticTerm::typed_map(
            semantic_origin(self.descriptor, reference.key.clone(), "term-map-operation")?,
            result_sort,
            operation,
            lowered,
        ))
    }

    fn infer_collection_update(
        &mut self,
        update: &DescriptorTerm,
        base_binding: &str,
        cell_sort: &SemanticSortRef,
        map_sorts: Option<&(SemanticSortRef, SemanticSortRef)>,
    ) -> Result<(), DescriptorLoweringError> {
        let DescriptorTerm::Application {
            head_class,
            reference,
            arguments,
            ..
        } = update
        else {
            return Err(self.invalid_term("updated-cell replacement is not an application"));
        };
        if *head_class != krs_ir::DescriptorApplicationHeadClass::Applied {
            return Err(self.invalid_term("updated-cell replacement head is not applied"));
        }
        let ordered = match (&reference.application, cell_sort) {
            (
                DescriptorApplicationRef::Map(MapOperation::Update),
                SemanticSortRef::Builtin(BuiltinSort::Map),
            ) => ordinary_map_arguments(MapOperation::Update, arguments)
                .map_err(|detail| self.invalid_term(detail))?,
            (
                DescriptorApplicationRef::List(ListOperation::Update),
                SemanticSortRef::Builtin(BuiltinSort::List),
            ) => ordinary_list_arguments(ListOperation::Update, arguments)
                .map_err(|detail| self.invalid_term(detail))?,
            _ => {
                return Err(self.invalid_term(
                    "updated-cell replacement does not resolve to the registered update operation for its collection sort",
                ));
            }
        };
        let [base, key, value] = ordered.as_slice() else {
            unreachable!("collection update arity is checked")
        };
        let DescriptorTerm::Variable { name, .. } = base else {
            return Err(
                self.invalid_term("updated-cell base is not the matched whole-collection binding")
            );
        };
        if name != base_binding {
            return Err(self.invalid_term(format!(
                "updated-cell base {name:?} does not match {base_binding:?}"
            )));
        }
        self.infer(base, Some(cell_sort), false)?;
        let int_sort = SemanticSortRef::Builtin(BuiltinSort::Int);
        match cell_sort {
            SemanticSortRef::Builtin(BuiltinSort::Map) => {
                self.infer(key, map_sorts.map(|(key_sort, _)| key_sort), false)?;
                self.infer(value, map_sorts.map(|(_, value_sort)| value_sort), false)
            }
            SemanticSortRef::Builtin(BuiltinSort::List) => {
                self.infer(key, Some(&int_sort), false)?;
                self.infer(value, None, false)
            }
            _ => Err(self.invalid_term("only Map and List cells support readable updates")),
        }
    }

    fn infer_list_operation(
        &mut self,
        operation: ListOperation,
        arguments: &[DescriptorTermArgument],
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<(), DescriptorLoweringError> {
        let arguments = ordinary_list_arguments(operation, arguments)
            .map_err(|detail| self.invalid_term(detail))?;
        let list_sort = SemanticSortRef::Builtin(BuiltinSort::List);
        let int_sort = SemanticSortRef::Builtin(BuiltinSort::Int);
        let result_sort = match operation {
            ListOperation::Get => expected_sort
                .cloned()
                .ok_or_else(|| self.invalid_term("list::get requires an expected result sort"))?,
            ListOperation::Size => int_sort.clone(),
            ListOperation::Empty
            | ListOperation::Item
            | ListOperation::Concat
            | ListOperation::Update
            | ListOperation::Make
            | ListOperation::Range
            | ListOperation::UpdateAll => list_sort.clone(),
        };
        if let Some(expected) = expected_sort
            && !semantic_is_subsort(&result_sort, expected, self.sort_parents)
        {
            return Err(self.invalid_term(format!(
                "List operation result sort {result_sort:?} is not admissible at sort {expected:?}"
            )));
        }
        let operand_sorts: Vec<Option<&SemanticSortRef>> = match operation {
            ListOperation::Empty => vec![],
            ListOperation::Item => vec![None],
            ListOperation::Concat => vec![Some(&list_sort), Some(&list_sort)],
            ListOperation::Get => vec![Some(&list_sort), Some(&int_sort)],
            ListOperation::Update => vec![Some(&list_sort), Some(&int_sort), None],
            ListOperation::Size => vec![Some(&list_sort)],
            ListOperation::Make => vec![Some(&int_sort), None],
            ListOperation::Range => vec![Some(&list_sort), Some(&int_sort), Some(&int_sort)],
            ListOperation::UpdateAll => {
                vec![Some(&list_sort), Some(&int_sort), Some(&list_sort)]
            }
        };
        for (argument, expected) in arguments.into_iter().zip(operand_sorts) {
            self.infer(argument, expected, subject)?;
        }
        Ok(())
    }

    fn lower_list_operation(
        &mut self,
        reference: &krs_ir::DescriptorApplicationReference,
        operation: ListOperation,
        arguments: &[DescriptorTermArgument],
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let arguments = ordinary_list_arguments(operation, arguments)
            .map_err(|detail| self.invalid_term(detail))?;
        let list_sort = SemanticSortRef::Builtin(BuiltinSort::List);
        let int_sort = SemanticSortRef::Builtin(BuiltinSort::Int);
        let result_sort = match operation {
            ListOperation::Get => expected_sort
                .cloned()
                .ok_or_else(|| self.invalid_term("list::get requires an expected result sort"))?,
            ListOperation::Size => int_sort.clone(),
            ListOperation::Empty
            | ListOperation::Item
            | ListOperation::Concat
            | ListOperation::Update
            | ListOperation::Make
            | ListOperation::Range
            | ListOperation::UpdateAll => list_sort.clone(),
        };
        let operand_sorts: Vec<Option<&SemanticSortRef>> = match operation {
            ListOperation::Empty => vec![],
            ListOperation::Item => vec![None],
            ListOperation::Concat => vec![Some(&list_sort), Some(&list_sort)],
            ListOperation::Get => vec![Some(&list_sort), Some(&int_sort)],
            ListOperation::Update => vec![Some(&list_sort), Some(&int_sort), None],
            ListOperation::Size => vec![Some(&list_sort)],
            ListOperation::Make => vec![Some(&int_sort), None],
            ListOperation::Range => vec![Some(&list_sort), Some(&int_sort), Some(&int_sort)],
            ListOperation::UpdateAll => {
                vec![Some(&list_sort), Some(&int_sort), Some(&list_sort)]
            }
        };
        let lowered = arguments
            .into_iter()
            .zip(operand_sorts)
            .map(|(argument, expected)| self.lower(argument, expected, subject))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(SemanticTerm::list(
            semantic_origin(
                self.descriptor,
                reference.key.clone(),
                "term-list-operation",
            )?,
            result_sort,
            operation,
            lowered,
        ))
    }

    fn infer_set_operation(
        &mut self,
        operation: SetOperation,
        arguments: &[DescriptorTermArgument],
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<(), DescriptorLoweringError> {
        let arguments = ordinary_set_arguments(operation, arguments)
            .map_err(|detail| self.invalid_term(detail))?;
        let set_sort = SemanticSortRef::Builtin(BuiltinSort::Set);
        let bool_sort = SemanticSortRef::Builtin(BuiltinSort::Bool);
        let result_sort = match operation {
            SetOperation::Contains => bool_sort.clone(),
            SetOperation::Empty | SetOperation::Item | SetOperation::Concat => set_sort.clone(),
        };
        if let Some(expected) = expected_sort
            && !semantic_is_subsort(&result_sort, expected, self.sort_parents)
        {
            return Err(self.invalid_term(format!(
                "Set operation result sort {result_sort:?} is not admissible at sort {expected:?}"
            )));
        }
        let operand_sorts: Vec<Option<&SemanticSortRef>> = match operation {
            SetOperation::Empty => vec![],
            SetOperation::Item => vec![None],
            SetOperation::Concat => vec![Some(&set_sort), Some(&set_sort)],
            SetOperation::Contains => vec![None, Some(&set_sort)],
        };
        for (argument, expected) in arguments.into_iter().zip(operand_sorts) {
            self.infer(argument, expected, subject)?;
        }
        Ok(())
    }

    fn lower_set_operation(
        &mut self,
        reference: &krs_ir::DescriptorApplicationReference,
        operation: SetOperation,
        arguments: &[DescriptorTermArgument],
        _expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let arguments = ordinary_set_arguments(operation, arguments)
            .map_err(|detail| self.invalid_term(detail))?;
        let set_sort = SemanticSortRef::Builtin(BuiltinSort::Set);
        let bool_sort = SemanticSortRef::Builtin(BuiltinSort::Bool);
        let result_sort = match operation {
            SetOperation::Contains => bool_sort,
            SetOperation::Empty | SetOperation::Item | SetOperation::Concat => set_sort.clone(),
        };
        let operand_sorts: Vec<Option<&SemanticSortRef>> = match operation {
            SetOperation::Empty => vec![],
            SetOperation::Item => vec![None],
            SetOperation::Concat => vec![Some(&set_sort), Some(&set_sort)],
            SetOperation::Contains => vec![None, Some(&set_sort)],
        };
        let lowered = arguments
            .into_iter()
            .zip(operand_sorts)
            .map(|(argument, expected)| self.lower(argument, expected, subject))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(SemanticTerm::set(
            semantic_origin(self.descriptor, reference.key.clone(), "term-set-operation")?,
            result_sort,
            operation,
            lowered,
        ))
    }

    fn resolve_binding_sorts(&mut self) -> Result<(), DescriptorLoweringError> {
        for name in self.binding_names {
            if self.binding_sorts.contains_key(name) {
                continue;
            }
            let constraints = self.binding_constraints.get(name).ok_or_else(|| {
                self.invalid_term(format!("variable {name:?} has no expected sort"))
            })?;
            let candidates = most_specific_common_descendants(constraints, self.sort_parents);
            let inferred = match candidates.as_slice() {
                [sort] => sort.clone(),
                [] => {
                    return Err(self.invalid_term(format!(
                        "variable {name:?} has no declared common descendant for occurrence sorts {constraints:?}"
                    )));
                }
                _ => {
                    return Err(self.invalid_term(format!(
                        "variable {name:?} has ambiguous most-specific common descendants {candidates:?} for occurrence sorts {constraints:?}"
                    )));
                }
            };
            self.binding_sorts.insert(name.clone(), inferred);
        }
        Ok(())
    }

    #[allow(clippy::too_many_lines)] // Exhaustive lowering parallel to `infer` above.
    fn lower(
        &mut self,
        term: &DescriptorTerm,
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        match term {
            DescriptorTerm::Variable { key, name, .. } => {
                if !self.binding_names.contains(name) {
                    return Err(self.invalid_term(format!("unbound variable {name:?}")));
                }
                let sort = self.binding_sorts.get(name).cloned().ok_or_else(|| {
                    self.invalid_term(format!("variable {name:?} has no inferred sort"))
                })?;
                debug_assert!(expected_sort.is_none_or(|expected| semantic_is_subsort(
                    &sort,
                    expected,
                    self.sort_parents
                )));
                Ok(SemanticTerm::variable(
                    semantic_origin(self.descriptor, key.clone(), "term-variable")?,
                    sort,
                    SemanticId::new(name.clone())?,
                ))
            }
            DescriptorTerm::Wildcard { key } => {
                if !subject {
                    return Err(self.invalid_term("wildcard occurs outside the rule subject"));
                }
                let sort = expected_sort.cloned().ok_or_else(|| {
                    self.invalid_term("wildcard has no expected production-field sort")
                })?;
                let ordinal = self.wildcard_offset + self.wildcards.len();
                let id = SemanticId::new(format!("__krs_wildcard_{ordinal}"))?;
                self.wildcards
                    .push(SemanticVariable::new(id.clone(), sort.clone()));
                Ok(SemanticTerm::variable(
                    semantic_origin(self.descriptor, key.clone(), "term-wildcard")?,
                    sort,
                    id,
                ))
            }
            DescriptorTerm::Literal { key, literal } => {
                let (sort, value) = match literal {
                    krs_ir::DescriptorLiteral::Int(value) => {
                        (SemanticSortRef::Builtin(BuiltinSort::Int), value.clone())
                    }
                    krs_ir::DescriptorLiteral::Bool(value) => (
                        SemanticSortRef::Builtin(BuiltinSort::Bool),
                        value.to_string(),
                    ),
                };
                Ok(SemanticTerm::token(
                    semantic_origin(self.descriptor, key.clone(), "term-literal")?,
                    sort,
                    value,
                )?)
            }
            DescriptorTerm::Application {
                reference,
                arguments,
                ..
            } => {
                let (application, signature) = match &reference.application {
                    DescriptorApplicationRef::Declared(id) => {
                        let signature = self.catalog.get(id).cloned().ok_or_else(|| {
                            self.invalid_term(format!(
                                "declared application {id:?} has no grammar production"
                            ))
                        })?;
                        (ApplicationRef::Declared(id.clone()), signature)
                    }
                    DescriptorApplicationRef::Builtin(operation) => (
                        ApplicationRef::Builtin(*operation),
                        builtin_production_signature(*operation),
                    ),
                    DescriptorApplicationRef::Map(operation) => {
                        return self.lower_map_operation(
                            reference,
                            *operation,
                            arguments,
                            expected_sort,
                            subject,
                        );
                    }
                    DescriptorApplicationRef::List(operation) => {
                        return self.lower_list_operation(
                            reference,
                            *operation,
                            arguments,
                            expected_sort,
                            subject,
                        );
                    }
                    DescriptorApplicationRef::Set(operation) => {
                        return self.lower_set_operation(
                            reference,
                            *operation,
                            arguments,
                            expected_sort,
                            subject,
                        );
                    }
                };
                let ordered = order_structured_arguments(arguments, &signature.fields, subject)
                    .map_err(|detail| self.invalid_term(detail))?;
                let lowered = ordered
                    .into_iter()
                    .zip(&signature.fields)
                    .map(|(argument, (_, sort))| match argument {
                        Some(argument) => self.lower(argument, Some(sort), subject),
                        None => self.lower_record_rest_wildcard(sort),
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(SemanticTerm::application(
                    semantic_origin(self.descriptor, reference.key.clone(), "term-application")?,
                    signature.result_sort,
                    application,
                    lowered,
                ))
            }
            DescriptorTerm::BuiltinToken { key, sort, value } => SemanticTerm::token(
                semantic_origin(self.descriptor, key.clone(), "claim-builtin-token")?,
                SemanticSortRef::Builtin(*sort),
                value.clone(),
            )
            .map_err(Into::into),
            DescriptorTerm::Anonymous {
                key,
                sort,
                spelling,
            } => {
                if !subject {
                    return Err(self.invalid_term("anonymous occurrence outside claim subject"));
                }
                let sort = semantic_sort_ref(&sort.sort);
                let ordinal = self.wildcard_offset + self.wildcards.len();
                let id = SemanticId::new(format!("{spelling}__krs_{ordinal}"))?;
                self.wildcards
                    .push(SemanticVariable::new(id.clone(), sort.clone()));
                Ok(SemanticTerm::variable(
                    semantic_origin(self.descriptor, key.clone(), "claim-anonymous")?,
                    sort,
                    id,
                ))
            }
            DescriptorTerm::OrBool { key, arguments } => {
                let bool_sort = SemanticSortRef::Builtin(BuiltinSort::Bool);
                let lowered = arguments
                    .iter()
                    .map(|argument| self.lower(argument, Some(&bool_sort), subject))
                    .collect::<Result<Vec<_>, _>>()?;
                let mut iter = lowered.into_iter();
                let mut value = iter.next().expect("validated nonempty");
                for right in iter {
                    value = SemanticTerm::application(
                        semantic_origin(self.descriptor, key.clone(), "claim-or-bool")?,
                        bool_sort.clone(),
                        ApplicationRef::Builtin(BuiltinOperation::BoolOr),
                        vec![value, right],
                    );
                }
                Ok(value)
            }
            DescriptorTerm::Cell {
                key,
                declaration,
                fields,
            } => self.lower_cell_term(key, declaration, fields, subject),
        }
    }

    fn cell_k_item_sort(&self) -> Result<SemanticSortRef, DescriptorLoweringError> {
        self.k_item_sort.clone().ok_or_else(|| {
            self.invalid_term("fragment! requires one selected framework KItem sort")
        })
    }

    fn cell_declaration(
        &self,
        owner: &StableItemId,
    ) -> Result<&krs_ir::DescriptorCellDeclaration, DescriptorLoweringError> {
        let declarations = self.declarations.ok_or_else(|| {
            self.invalid_term("fragment! is supported only where cell declarations are available")
        })?;
        let descriptor = require_descriptor(owner, ItemKind::Cell, declarations)?;
        let DescriptorPayload::Cell(declaration) = &descriptor.payload else {
            unreachable!("kind-checked cell descriptor has cell payload")
        };
        Ok(declaration)
    }

    fn infer_cell_fields(
        &mut self,
        owner: &StableItemId,
        fields: &[krs_ir::DescriptorCellTermField],
        subject: bool,
    ) -> Result<(), DescriptorLoweringError> {
        let declaration = self.cell_declaration(owner)?.clone();
        let supplied = fields
            .iter()
            .map(|field| (field.field.clone(), field))
            .collect::<BTreeMap<_, _>>();
        if supplied.len() != fields.len() || supplied.len() != declaration.fields.len() {
            return Err(self.invalid_term(format!(
                "fragment! for {:?} must provide every child field exactly once",
                owner.item_name()
            )));
        }
        for declared in &declaration.fields {
            let field = supplied
                .get(&ProductionFieldId::new(&declared.rust_field)?)
                .ok_or_else(|| {
                    self.invalid_term(format!(
                        "fragment! for {:?} is missing child field {:?}",
                        owner.item_name(),
                        declared.rust_field
                    ))
                })?;
            match &declared.content {
                ProtocolCellContent::Leaf { sort, .. } => {
                    self.infer(&field.value, Some(&semantic_sort_ref(&sort.sort)), subject)?;
                }
                ProtocolCellContent::Nested {
                    declaration: nested,
                } => {
                    let DescriptorTerm::Cell { declaration, .. } = field.value.as_ref() else {
                        return Err(self.invalid_term(format!(
                            "nested child {:?} must be authored with fragment!",
                            declared.rust_field
                        )));
                    };
                    if declaration != &nested.declaration {
                        return Err(self.invalid_term(format!(
                            "nested child {:?} uses the wrong cell declaration",
                            declared.rust_field
                        )));
                    }
                    self.infer(&field.value, Some(&self.cell_k_item_sort()?), subject)?;
                }
            }
        }
        Ok(())
    }

    fn lower_cell_term(
        &mut self,
        key: &ProvenanceKey,
        owner: &StableItemId,
        fields: &[krs_ir::DescriptorCellTermField],
        subject: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let declaration = self.cell_declaration(owner)?.clone();
        let supplied = fields
            .iter()
            .map(|field| (field.field.clone(), field))
            .collect::<BTreeMap<_, _>>();
        let mut children = Vec::with_capacity(declaration.fields.len());
        for declared in &declaration.fields {
            let field_id = ProductionFieldId::new(&declared.rust_field)?;
            let field = supplied.get(&field_id).ok_or_else(|| {
                self.invalid_term(format!(
                    "fragment! is missing child field {:?}",
                    declared.rust_field
                ))
            })?;
            let child = match &declared.content {
                ProtocolCellContent::Leaf { sort, .. } => {
                    let content_sort = semantic_sort_ref(&sort.sort);
                    let content = self.lower(&field.value, Some(&content_sort), subject)?;
                    SemanticTerm::cell(
                        semantic_origin(self.descriptor, field.key.clone(), "cell-term-child")?,
                        self.cell_k_item_sort()?,
                        semantic_cell_id(&declared.reference.cell)?,
                        vec![content],
                    )
                }
                ProtocolCellContent::Nested { .. } => {
                    self.lower(&field.value, Some(&self.cell_k_item_sort()?), subject)?
                }
            };
            children.push(child);
        }
        let identity = self.cell_identity_for_declaration(owner)?;
        Ok(SemanticTerm::cell(
            semantic_origin(self.descriptor, key.clone(), "cell-term")?,
            self.cell_k_item_sort()?,
            semantic_cell_id(identity)?,
            children,
        ))
    }

    fn cell_identity_for_declaration(
        &self,
        owner: &StableItemId,
    ) -> Result<&krs_ir::DescriptorCellIdentity, DescriptorLoweringError> {
        let declarations = self
            .declarations
            .ok_or_else(|| self.invalid_term("fragment! has no cell-declaration catalog"))?;
        let mut matches = declarations
            .values()
            .flat_map(|descriptor| {
                let declaration = match &descriptor.payload {
                    DescriptorPayload::Cell(value) => Some(value.as_ref()),
                    DescriptorPayload::FixedConfiguration(value) => Some(&value.declaration),
                    _ => None,
                };
                declaration
                    .into_iter()
                    .flat_map(|declaration| declaration.fields.iter())
            })
            .filter(|field| {
                matches!(
                    &field.content,
                    ProtocolCellContent::Nested { declaration } if &declaration.declaration == owner
                )
            });
        let first = matches.next().ok_or_else(|| {
            self.invalid_term(format!(
                "cell declaration {:?} is not attached to the fixed configuration",
                owner.item_name()
            ))
        })?;
        if matches.next().is_some() {
            return Err(self.invalid_term(format!(
                "cell declaration {:?} is attached more than once",
                owner.item_name()
            )));
        }
        Ok(&first.reference.cell)
    }

    fn lower_record_rest_wildcard(
        &mut self,
        sort: &SemanticSortRef,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let pattern_key = self.pattern_key.ok_or_else(|| {
            self.invalid_term("partial named patterns are valid only in structured rule subjects")
        })?;
        let ordinal = self.wildcard_offset + self.wildcards.len();
        let id = SemanticId::new(format!("__krs_wildcard_{ordinal}"))?;
        let role = format!("record-rest-{ordinal}");
        self.wildcards
            .push(SemanticVariable::new(id.clone(), sort.clone()));
        Ok(SemanticTerm::variable(
            semantic_origin(self.descriptor, pattern_key.clone(), &role)?,
            sort.clone(),
            id,
        ))
    }

    fn invalid_term(&self, detail: impl Into<String>) -> DescriptorLoweringError {
        DescriptorLoweringError::InvalidTerm {
            id: Box::new(self.descriptor.id.clone()),
            detail: detail.into(),
        }
    }
}

fn initial_binding_constraints(
    binding_sorts: &BTreeMap<String, SemanticSortRef>,
) -> BTreeMap<String, BTreeSet<SemanticSortRef>> {
    binding_sorts
        .iter()
        .map(|(name, sort)| (name.clone(), BTreeSet::from([sort.clone()])))
        .collect()
}

/// Returns the nearest declared sorts below every occurrence constraint.
///
/// Descendants strictly below another common descendant are redundant: the
/// higher candidate is the greatest lower bound that preserves every value
/// admitted by the occurrence constraints. The stable sort ordering makes an
/// ambiguous result deterministic for diagnostics.
fn most_specific_common_descendants(
    constraints: &BTreeSet<SemanticSortRef>,
    parents: &BTreeMap<SemanticSortRef, Vec<SemanticSortRef>>,
) -> Vec<SemanticSortRef> {
    let universe = parents
        .keys()
        .chain(parents.values().flatten())
        .chain(constraints)
        .cloned()
        .collect::<BTreeSet<_>>();
    let closures = universe
        .into_iter()
        .map(|candidate| {
            let closure = semantic_sort_closure(&candidate, parents);
            (candidate, closure)
        })
        .collect::<BTreeMap<_, _>>();
    let common = closures
        .iter()
        .filter(|(_, closure)| constraints.is_subset(closure))
        .map(|(candidate, _)| candidate.clone())
        .collect::<BTreeSet<_>>();
    common
        .iter()
        .filter(|candidate| {
            !closures[*candidate]
                .iter()
                .any(|ancestor| ancestor != *candidate && common.contains(ancestor))
        })
        .cloned()
        .collect()
}

fn builtin_production_signature(operation: BuiltinOperation) -> ProductionSignature {
    ProductionSignature {
        result_sort: SemanticSortRef::Builtin(operation.result_sort()),
        fields: operation
            .argument_sorts()
            .iter()
            .enumerate()
            .map(|(index, sort)| {
                (
                    ProductionFieldId::new(format!("argument_{index}"))
                        .expect("builtin field identity is valid"),
                    SemanticSortRef::Builtin(*sort),
                )
            })
            .collect(),
        grammar_owned: false,
    }
}

fn ordinary_map_arguments(
    operation: MapOperation,
    arguments: &[DescriptorTermArgument],
) -> Result<Vec<&DescriptorTerm>, String> {
    let expected = match operation {
        MapOperation::Update => 3,
        MapOperation::Get | MapOperation::InKeys => 2,
        MapOperation::Empty | MapOperation::Item => {
            return Err(format!(
                "Map operation {operation:?} is not available as an ordinary term application"
            ));
        }
    };
    if arguments.len() != expected {
        return Err(format!(
            "Map operation {operation:?} expects {expected} positional arguments but received {}",
            arguments.len()
        ));
    }
    arguments
        .iter()
        .map(ordinary_map_positional_argument)
        .collect()
}

fn ordinary_map_positional_argument(
    argument: &DescriptorTermArgument,
) -> Result<&DescriptorTerm, String> {
    match argument {
        DescriptorTermArgument::Positional { value } => Ok(value),
        DescriptorTermArgument::Named { .. } => {
            Err("builtin collection operations accept positional arguments only".to_owned())
        }
    }
}

fn ordinary_set_arguments(
    operation: SetOperation,
    arguments: &[DescriptorTermArgument],
) -> Result<Vec<&DescriptorTerm>, String> {
    let expected = match operation {
        SetOperation::Empty => 0,
        SetOperation::Item => 1,
        SetOperation::Concat | SetOperation::Contains => 2,
    };
    if arguments.len() != expected {
        return Err(format!(
            "Set operation {operation:?} expects {expected} positional arguments but received {}",
            arguments.len()
        ));
    }
    arguments
        .iter()
        .map(ordinary_map_positional_argument)
        .collect()
}

fn ordinary_list_arguments(
    operation: ListOperation,
    arguments: &[DescriptorTermArgument],
) -> Result<Vec<&DescriptorTerm>, String> {
    let expected = match operation {
        ListOperation::Empty => 0,
        ListOperation::Item | ListOperation::Size => 1,
        ListOperation::Concat | ListOperation::Get | ListOperation::Make => 2,
        ListOperation::Update | ListOperation::Range | ListOperation::UpdateAll => 3,
    };
    if arguments.len() != expected {
        return Err(format!(
            "List operation {operation:?} expects {expected} positional arguments but received {}",
            arguments.len()
        ));
    }
    arguments
        .iter()
        .map(ordinary_map_positional_argument)
        .collect()
}

fn order_structured_arguments<'a>(
    arguments: &'a [DescriptorTermArgument],
    fields: &[(ProductionFieldId, SemanticSortRef)],
    allow_missing_named: bool,
) -> Result<Vec<Option<&'a DescriptorTerm>>, String> {
    if arguments.len() != fields.len()
        && (!allow_missing_named
            || arguments.first().is_none_or(|argument| {
                matches!(argument, DescriptorTermArgument::Positional { .. })
            }))
    {
        return Err(format!(
            "application expects {} arguments but received {}",
            fields.len(),
            arguments.len()
        ));
    }
    if arguments
        .first()
        .is_none_or(|argument| matches!(argument, DescriptorTermArgument::Positional { .. }))
    {
        return Ok(arguments
            .iter()
            .map(|argument| match argument {
                DescriptorTermArgument::Positional { value } => Some(value.as_ref()),
                DescriptorTermArgument::Named { .. } => {
                    unreachable!("protocol validation rejects mixed arguments")
                }
            })
            .collect());
    }
    let mut by_name = arguments
        .iter()
        .map(|argument| match argument {
            DescriptorTermArgument::Named { field, value, .. } => (field.clone(), value.as_ref()),
            DescriptorTermArgument::Positional { .. } => {
                unreachable!("protocol validation rejects mixed arguments")
            }
        })
        .collect::<BTreeMap<_, _>>();
    let ordered = fields
        .iter()
        .map(|(field, _)| {
            let value = by_name.remove(field);
            if value.is_none() && !allow_missing_named {
                return Err(format!(
                    "named application lacks field {:?}",
                    field.as_str()
                ));
            }
            Ok(value)
        })
        .collect::<Result<Vec<_>, _>>()?;
    if let Some((field, _)) = by_name.into_iter().next() {
        return Err(format!(
            "named application has unknown field {:?}",
            field.as_str()
        ));
    }
    Ok(ordered)
}

fn constructor_field_order(
    production: &StableItemId,
    constructor: &krs_ir::ConstructorDescriptor,
) -> Result<Vec<String>, DescriptorLoweringError> {
    if constructor.fields.is_empty() {
        return Ok(Vec::new());
    }
    let source = constructor
        .syntax
        .as_deref()
        .unwrap_or_else(|| production.item_name());
    let mut names = Vec::new();
    let mut index = 0_usize;
    while index < source.len() {
        let Some(open) = source[index..].find('{') else {
            break;
        };
        let open = index + open;
        let remainder = &source[open + 1..];
        let Some(close) = remainder.find('}') else {
            return Err(DescriptorLoweringError::UnsupportedShape {
                node: "constructor syntax",
                detail: format!("constructor {production:?} has an unclosed placeholder"),
            });
        };
        names.push(remainder[..close].to_owned());
        index = open + close + 2;
    }
    if names.len() != constructor.fields.len()
        || names.iter().collect::<BTreeSet<_>>().len() != names.len()
        || names
            .iter()
            .any(|name| !constructor.fields.iter().any(|field| &field.name == name))
    {
        return Err(DescriptorLoweringError::UnsupportedShape {
            node: "constructor syntax",
            detail: format!("constructor {production:?} has inconsistent field placeholders"),
        });
    }
    Ok(names)
}

#[allow(clippy::needless_pass_by_value)]
fn semantic_origin(
    descriptor: &Descriptor,
    key: ProvenanceKey,
    role: &str,
) -> Result<NodeOrigin, DescriptorLoweringError> {
    let origin = descriptor.provenance.origin_for(&key).ok_or_else(|| {
        DescriptorLoweringError::ParserReferenceDisagreement {
            id: Box::new(descriptor.id.clone()),
            detail: format!(
                "missing parser origin `{}#{}` for semantic {role}",
                key.role(),
                key.ordinal()
            ),
        }
    })?;
    semantic_origin_from_stack(descriptor, origin, role, Some(&key))
}

fn lower_rule_label(
    descriptor: &Descriptor,
    label: Option<&DescriptorRuleLabel>,
) -> Result<Option<SemanticRuleLabel>, DescriptorLoweringError> {
    label
        .map(|label| {
            Ok(SemanticRuleLabel::new(
                semantic_origin(descriptor, label.key.clone(), "rule-label")?,
                label.name.clone(),
            )?)
        })
        .transpose()
}

fn semantic_origin_from_primary(
    descriptor: &Descriptor,
    role: &str,
) -> Result<NodeOrigin, DescriptorLoweringError> {
    semantic_origin_from_stack(
        descriptor,
        descriptor.provenance.primary_origin(),
        role,
        Some(descriptor.provenance.primary_key()),
    )
}

fn semantic_origin_from_stack(
    descriptor: &Descriptor,
    origin: &krs_ir::OriginStack,
    role: &str,
    key: Option<&ProvenanceKey>,
) -> Result<NodeOrigin, DescriptorLoweringError> {
    let mut seed = stable_item_text(&descriptor.id);
    seed.push('\0');
    seed.push_str(role);
    if let Some(key) = key {
        seed.push('\0');
        seed.push_str(key.role());
        seed.push('\0');
        seed.push_str(&key.ordinal().to_string());
    }
    let digest = Sha256::digest(seed.as_bytes());
    let source_key = SourceMapKey::new(format!("sem.{role}.{}", hex_encode(&digest[..12])))?;
    let mut origin = origin.clone();
    origin.push(OriginFrame::Transformation {
        kind: TransformationOriginKind::SemanticIr,
        item: Some(descriptor.id.clone()),
        label: Some(role.to_owned()),
    });
    Ok(NodeOrigin::new(source_key, origin))
}

fn role_key(role: ProvenanceRole, ordinal: u32) -> Result<ProvenanceKey, DescriptorLoweringError> {
    role.key(ordinal).map_err(|error| {
        DescriptorLoweringError::InvalidGeneratedIdentity(format!(
            "cannot generate parser provenance key: {error}"
        ))
    })
}

fn stable_item_text(id: &StableItemId) -> String {
    let mut text = String::new();
    push_component(&mut text, id.package().k_namespace());
    push_component(&mut text, id.package().cargo_name());
    push_component(&mut text, id.package().cargo_version());
    push_component(&mut text, id.package().cargo_source());
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

fn hex_encode(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        output.push(char::from(HEX[usize::from(byte >> 4)]));
        output.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    output
}

fn lower_camel(value: &str) -> String {
    let mut characters = value.chars();
    match characters.next() {
        Some(first) => first.to_lowercase().chain(characters).collect(),
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

fn visit_parents(
    root: &StableItemId,
    current: &StableItemId,
    graph: &BTreeMap<StableItemId, Vec<StableItemId>>,
    visiting: &mut Vec<StableItemId>,
    closure: &mut BTreeSet<StableItemId>,
) -> Result<(), AnalysisError> {
    if let Some(position) = visiting.iter().position(|item| item == current) {
        let mut cycle = visiting[position..]
            .iter()
            .map(display_item)
            .collect::<Vec<_>>();
        cycle.push(display_item(current));
        return Err(AnalysisError::new(
            AnalysisErrorKind::SortCycle,
            format!("open-sort relation contains cycle: {}", cycle.join(" -> ")),
        ));
    }
    visiting.push(current.clone());
    for parent in graph
        .get(current)
        .expect("resolved sort has a direct-parent entry")
    {
        if parent == root {
            let mut cycle = visiting.iter().map(display_item).collect::<Vec<_>>();
            cycle.push(display_item(root));
            return Err(AnalysisError::new(
                AnalysisErrorKind::SortCycle,
                format!("open-sort relation contains cycle: {}", cycle.join(" -> ")),
            ));
        }
        closure.insert(parent.clone());
        visit_parents(root, parent, graph, visiting, closure)?;
    }
    visiting.pop();
    Ok(())
}

fn require_kind(
    id: &StableItemId,
    expected: ItemKind,
    kinds: &BTreeMap<StableItemId, ItemKind>,
) -> Result<(), AnalysisError> {
    let Some(actual) = kinds.get(id) else {
        return Err(AnalysisError::new(
            AnalysisErrorKind::UnresolvedReference,
            format!("stable reference `{}` has no declaration", display_item(id)),
        ));
    };
    if *actual != expected {
        return Err(AnalysisError::new(
            AnalysisErrorKind::ReferenceKindMismatch,
            format!(
                "stable reference `{}` has kind {actual:?}, but {expected:?} is required",
                display_item(id)
            ),
        ));
    }
    Ok(())
}

fn display_item(id: &StableItemId) -> String {
    let module = if id.module_path().is_empty() {
        String::new()
    } else {
        format!("{}::", id.module_path().join("::"))
    };
    format!(
        "{}::{module}{}#{:?}",
        id.package().k_namespace(),
        id.item_name(),
        id.item_kind()
    )
}

#[cfg(test)]
mod state_frame_tests {
    use super::*;

    fn key(role: &str) -> ProvenanceKey {
        ProvenanceKey::new(role, 0).unwrap()
    }

    fn variable(role: &str) -> DescriptorTerm {
        DescriptorTerm::Variable {
            key: key(role),
            path_key: key(role),
            name: "M".into(),
        }
    }

    fn map(body: ProtocolRuleMapBody<DescriptorTerm>) -> ProtocolRuleStateTerm<DescriptorTerm> {
        ProtocolRuleStateTerm::Map(krs_ir::ProtocolRuleMap {
            payload_key: Some(key("map_payload")),
            body,
        })
    }

    fn exact_map_items() -> ProtocolRuleStateTerm<DescriptorTerm> {
        map(ProtocolRuleMapBody::Items {
            items: vec![krs_ir::ProtocolRuleMapItem {
                key_key: key("map_key"),
                key: variable("key_reference"),
                value_key: key("map_value"),
                value: variable("value_reference"),
            }],
            remainder: ProtocolRuleFrame::Exact,
        })
    }

    #[test]
    fn all_exact_map_forms_share_one_associative_family() {
        let empty = map(ProtocolRuleMapBody::Empty { explicit_dot: true });
        let items = exact_map_items();
        let update = map(ProtocolRuleMapBody::Update {
            base_key: key("map_update_base"),
            base: variable("base_reference"),
            key_key: key("map_update_key"),
            key: variable("update_key_reference"),
            value_key: key("map_update_value"),
            value: variable("update_value_reference"),
        });
        let whole_map_term = ProtocolRuleStateTerm::Term(variable("whole_map_reference"));

        assert!(state_frames_compatible(
            rule_state_frame(&empty),
            rule_state_frame(&items)
        ));
        assert!(state_frames_compatible(
            rule_state_frame(&items),
            rule_state_frame(&empty)
        ));
        assert!(state_frames_compatible(
            rule_state_frame(&items),
            rule_state_frame(&update)
        ));
        assert!(state_frames_compatible(
            rule_state_frame(&whole_map_term),
            rule_state_frame(&update)
        ));
    }

    #[test]
    fn exact_forms_do_not_admit_a_frame_and_framed_families_remain_typed() {
        let empty = map(ProtocolRuleMapBody::Empty { explicit_dot: true });
        let framed_k = ProtocolRuleStateTerm::KSequence(krs_ir::ProtocolRuleKSequence {
            payload_key: Some(key("k_payload")),
            dot_k_key: None,
            notation: krs_ir::DescriptorKSequenceNotation::Comma,
            items: Vec::new(),
            tail: ProtocolRuleFrame::Bind {
                key: key("k_remainder"),
                binding: "REST".into(),
            },
        });
        let framed_map = map(ProtocolRuleMapBody::Items {
            items: vec![krs_ir::ProtocolRuleMapItem {
                key_key: key("map_key"),
                key: variable("key_reference"),
                value_key: key("map_value"),
                value: variable("value_reference"),
            }],
            remainder: ProtocolRuleFrame::Reuse {
                key: key("map_remainder"),
                binding: "REST".into(),
            },
        });

        assert!(!state_frames_compatible(
            rule_state_frame(&empty),
            rule_state_frame(&framed_map)
        ));
        assert!(!state_frames_compatible(
            rule_state_frame(&framed_k),
            rule_state_frame(&framed_map)
        ));
    }
}
