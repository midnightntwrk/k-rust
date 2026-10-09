use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    Descriptor, DescriptorApplicationRef, DescriptorCellDeclaration, DescriptorDeclaration,
    DescriptorFixedConfiguration, DescriptorInitializerCell, DescriptorInitializerStateTerm,
    DescriptorPayload, DescriptorProductionAttribute, DescriptorProductionItem,
    DescriptorProductionOwner, DescriptorRuleCells, DescriptorSortRef, DescriptorTerm,
    GrammarDescriptor, GroupAssociativitySentence, LayoutSentence, LexicalSentence, ModuleId,
    PackageId, PrecedenceRelation, ProtocolCellContent, ProtocolContextAliasBindingKind,
    ProtocolInitializerCellContent, ProtocolInitializerStateTerm, ProtocolMapBody,
    ProtocolRuleBindingKind, ProtocolRuleMapBody, ProtocolRuleStateTerm, SortDescriptor,
    StableItemId,
};
use krs_ir_levels::{
    SemanticConfiguration, SemanticContextAlias, SemanticModule, SemanticProduction, SemanticRule,
    SemanticSort, SemanticSortRef, SemanticSubsort,
};
use krs_syntax::ProvenanceRole;

use super::catalog::{DeclarationCatalog, ProductionSignature};
use super::configuration::lower_fixed_configuration_descriptor;
use super::configuration_rules::{
    lower_configuration_rule_descriptor, lower_context_alias_descriptor,
};
use super::error::DescriptorLoweringError;
use super::grammar::lower_grammar_descriptor;
use super::origin::{role_key, semantic_origin, semantic_origin_from_primary};
use super::rules::{lower_head_rule_descriptor, lower_structured_rule_descriptor};

/// Sentences of one package module, accumulated in descriptor order and
/// sorted canonically when the module is built.
#[derive(Default)]
pub(super) struct ModuleSentences {
    pub(super) sorts: Vec<SemanticSort>,
    pub(super) subsorts: Vec<SemanticSubsort>,
    pub(super) productions: Vec<SemanticProduction>,
    pub(super) precedences: Vec<PrecedenceRelation>,
    pub(super) associativities: Vec<GroupAssociativitySentence>,
    pub(super) configuration: Option<SemanticConfiguration>,
    pub(super) rules: Vec<SemanticRule>,
    pub(super) context_aliases: Vec<SemanticContextAlias>,
    pub(super) lexicals: Vec<LexicalSentence>,
    pub(super) layouts: Vec<LayoutSentence>,
    pub(super) raw_sentences: Vec<krs_ir::RawSentence>,
}

/// Lowers a package's definition module from `descriptors`. Its imports
/// follow the references of every descriptor in `referencing`, which includes
/// the package's spec modules (KF-041): a spec module imports the definition
/// through `crate`, so the definition must import what the spec module names.
pub(super) fn lower_package_module(
    package: &PackageId,
    descriptors: &[&Descriptor],
    referencing: &[&Descriptor],
    module_ids: &BTreeMap<PackageId, ModuleId>,
    declarations: &DeclarationCatalog<'_>,
    semantic_sort_parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
    production_catalog: &BTreeMap<StableItemId, ProductionSignature>,
) -> Result<SemanticModule, DescriptorLoweringError> {
    let module_id = module_ids.get(package).cloned().ok_or_else(|| {
        DescriptorLoweringError::UnsupportedShape {
            node: "module",
            detail: format!("package {package} has no generated module identity"),
        }
    })?;
    let origin_descriptor =
        descriptors
            .first()
            .copied()
            .ok_or_else(|| DescriptorLoweringError::UnsupportedShape {
                node: "module",
                detail: format!("package {package} has no semantic descriptors"),
            })?;
    let module_origin = semantic_origin_from_primary(origin_descriptor, "module")?;
    let imports = referenced_packages(referencing)
        .into_iter()
        .filter(|referenced| referenced != package)
        .map(|referenced| {
            module_ids.get(&referenced).cloned().ok_or_else(|| {
                DescriptorLoweringError::UnsupportedShape {
                    node: "module import",
                    detail: format!("referenced package {referenced} has no module"),
                }
            })
        })
        .collect::<Result<BTreeSet<_>, _>>()?;
    build_module(
        module_origin,
        module_id,
        imports.into_iter().collect(),
        descriptors,
        declarations,
        semantic_sort_parents,
        production_catalog,
    )
}

/// Lowers one author spec module (KF-041) with its resolved imports.
pub(super) fn lower_spec_module(
    spec: &super::spec_modules::SpecDeclaration<'_>,
    imports: Vec<ModuleId>,
    descriptors: &[&Descriptor],
    declarations: &DeclarationCatalog<'_>,
    semantic_sort_parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
    production_catalog: &BTreeMap<StableItemId, ProductionSignature>,
) -> Result<SemanticModule, DescriptorLoweringError> {
    Ok(build_module(
        semantic_origin_from_primary(spec.descriptor, "spec-module")?,
        spec.name.clone(),
        imports,
        descriptors,
        declarations,
        semantic_sort_parents,
        production_catalog,
    )?
    .into_spec())
}

fn build_module(
    module_origin: krs_ir::NodeOrigin,
    module_id: ModuleId,
    imports: Vec<ModuleId>,
    descriptors: &[&Descriptor],
    declarations: &DeclarationCatalog<'_>,
    semantic_sort_parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
    production_catalog: &BTreeMap<StableItemId, ProductionSignature>,
) -> Result<SemanticModule, DescriptorLoweringError> {
    let mut sentences = ModuleSentences::default();
    for descriptor in descriptors {
        lower_module_descriptor(
            descriptor,
            declarations,
            semantic_sort_parents,
            production_catalog,
            &mut sentences,
        )?;
    }
    let ModuleSentences {
        mut sorts,
        mut subsorts,
        mut productions,
        mut precedences,
        mut associativities,
        configuration,
        mut rules,
        mut context_aliases,
        lexicals,
        layouts,
        raw_sentences,
    } = sentences;
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
    )
    .with_lexicals(lexicals)
    .with_layouts(layouts)
    .with_raw_sentences(raw_sentences))
}

/// Lowers one descriptor into the sentences of its package module.
fn lower_module_descriptor(
    descriptor: &Descriptor,
    declarations: &DeclarationCatalog<'_>,
    semantic_sort_parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
    production_catalog: &BTreeMap<StableItemId, ProductionSignature>,
    sentences: &mut ModuleSentences,
) -> Result<(), DescriptorLoweringError> {
    let declaration = declarations.metadata.get(descriptor.id()).ok_or_else(|| {
        DescriptorLoweringError::UnsupportedShape {
            node: "declaration metadata",
            detail: format!("descriptor {} has no API metadata", descriptor.id()),
        }
    })?;
    match descriptor.payload() {
        DescriptorPayload::Sort(sort) => {
            lower_sort_descriptor(descriptor, sort, declaration, sentences)?;
        }
        DescriptorPayload::Grammar(grammar) => {
            lower_grammar_descriptor(descriptor, grammar, declaration, sentences)?;
        }
        DescriptorPayload::StructuredRule(rule) => {
            sentences.rules.push(lower_structured_rule_descriptor(
                descriptor,
                rule,
                semantic_sort_parents,
                production_catalog,
            )?);
        }
        DescriptorPayload::FixedConfiguration(value) => {
            if sentences.configuration.is_some() {
                return Err(DescriptorLoweringError::ConfigurationCount(2));
            }
            sentences.configuration = Some(lower_fixed_configuration_descriptor(
                descriptor,
                value,
                declarations.descriptors,
                semantic_sort_parents,
                production_catalog,
            )?);
        }
        DescriptorPayload::Constructor(_) | DescriptorPayload::Cell(_) => {}
        DescriptorPayload::ConfigurationRule(rule) => {
            sentences.rules.push(lower_configuration_rule_descriptor(
                descriptor,
                rule,
                declarations.descriptors,
                semantic_sort_parents,
                production_catalog,
            )?);
        }
        DescriptorPayload::HeadRule(rule) => {
            sentences.rules.push(lower_head_rule_descriptor(
                descriptor,
                rule,
                declarations.descriptors,
                semantic_sort_parents,
                production_catalog,
            )?);
        }
        DescriptorPayload::ContextAlias(alias) => {
            sentences
                .context_aliases
                .push(lower_context_alias_descriptor(
                    descriptor,
                    alias,
                    declarations.descriptors,
                    semantic_sort_parents,
                    production_catalog,
                )?);
        }
    }
    Ok(())
}

/// Lowers a sort declaration and one subsort per direct parent.
fn lower_sort_descriptor(
    descriptor: &Descriptor,
    sort: &SortDescriptor,
    declaration: &DescriptorDeclaration,
    sentences: &mut ModuleSentences,
) -> Result<(), DescriptorLoweringError> {
    sentences.sorts.push(SemanticSort::with_api(
        semantic_origin(
            descriptor,
            role_key(ProvenanceRole::SortDeclaration, 0),
            "sort",
        )?,
        descriptor.id().clone(),
        declaration.visibility.clone(),
        declaration.explicit_symbol.clone(),
    ));
    for (ordinal, parent) in sort.parents.iter().enumerate() {
        let ordinal =
            u32::try_from(ordinal).map_err(|_| DescriptorLoweringError::UnsupportedShape {
                node: "sort parents",
                detail: "sort has more than u32::MAX direct parents".to_owned(),
            })?;
        sentences.subsorts.push(SemanticSubsort::new(
            semantic_origin(
                descriptor,
                role_key(ProvenanceRole::SortParent, ordinal),
                "subsort",
            )?,
            SemanticSortRef::Declared(descriptor.id().clone()),
            SemanticSortRef::Declared(parent.clone()),
        ));
    }
    Ok(())
}

fn referenced_packages(descriptors: &[&Descriptor]) -> BTreeSet<PackageId> {
    let mut packages = BTreeSet::new();
    for descriptor in descriptors {
        match descriptor.payload() {
            DescriptorPayload::Sort(sort) => {
                for parent in &sort.parents {
                    collect_item_package(parent, &mut packages);
                }
            }
            DescriptorPayload::Constructor(constructor) => {
                collect_sort_ref_package(&constructor.sort, &mut packages);
                for sort in constructor
                    .fields
                    .iter()
                    .filter_map(|field| field.sort.as_ref())
                {
                    collect_sort_ref_package(sort, &mut packages);
                }
            }
            DescriptorPayload::Grammar(grammar) => {
                collect_grammar_packages(grammar, &mut packages);
            }
            DescriptorPayload::StructuredRule(rule) => {
                collect_sort_ref_package(&rule.subject_sort.sort, &mut packages);
                collect_sort_ref_package(&rule.result_sort.sort, &mut packages);
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
                collect_item_package(&rule.subject_configuration.configuration, &mut packages);
                collect_item_package(&rule.result_configuration.configuration, &mut packages);
                for binding in &rule.bindings {
                    if let ProtocolRuleBindingKind::Term { sort } = &binding.kind {
                        collect_sort_ref_package(&sort.sort, &mut packages);
                    }
                }
                collect_rule_cells_packages(&rule.subject, &mut packages);
                collect_rule_cells_packages(&rule.result, &mut packages);
            }
            DescriptorPayload::HeadRule(rule) => collect_head_rule_packages(rule, &mut packages),
            DescriptorPayload::ContextAlias(alias) => {
                collect_item_package(&alias.configuration.configuration, &mut packages);
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

fn collect_item_package(id: &StableItemId, packages: &mut BTreeSet<PackageId>) {
    packages.insert(id.package().clone());
}

fn collect_production_packages(
    production: &krs_ir::DescriptorProduction,
    packages: &mut BTreeSet<PackageId>,
) {
    match &production.owner {
        DescriptorProductionOwner::Constructor { constructor } => {
            if let DescriptorApplicationRef::Declared(id) = &constructor.application {
                collect_item_package(id, packages);
            }
        }
        DescriptorProductionOwner::TokenSort { sort }
        | DescriptorProductionOwner::BracketSort { sort } => {
            collect_sort_ref_package(&sort.sort, packages);
        }
    }
    collect_sort_ref_package(&production.result_sort.sort, packages);
    for item in &production.items {
        if let DescriptorProductionItem::NonTerminal { sort, .. } = item {
            collect_sort_ref_package(&sort.sort, packages);
        }
    }
    for attribute in &production.attributes {
        if let DescriptorProductionAttribute::Strictness {
            using, result_sort, ..
        } = attribute
        {
            if let Some(using) = using {
                collect_item_package(&using.alias, packages);
            }
            collect_sort_ref_package(&result_sort.sort, packages);
        }
    }
}

fn collect_grammar_packages(grammar: &GrammarDescriptor, packages: &mut BTreeSet<PackageId>) {
    match grammar {
        GrammarDescriptor::Production(production) => {
            collect_production_packages(production, packages);
        }
        GrammarDescriptor::Tokens { productions } => {
            for production in productions {
                collect_production_packages(production, packages);
            }
        }
        GrammarDescriptor::Subsort {
            subsort, supersort, ..
        } => {
            collect_sort_ref_package(&subsort.sort, packages);
            collect_sort_ref_package(&supersort.sort, packages);
        }
        GrammarDescriptor::Precedence { .. }
        | GrammarDescriptor::Associativity { .. }
        | GrammarDescriptor::Lexical { .. }
        | GrammarDescriptor::Layout { .. }
        | GrammarDescriptor::RawSentence { .. }
        | GrammarDescriptor::SpecModule { .. } => {}
    }
}

fn collect_head_rule_packages(
    rule: &krs_ir::DescriptorHeadRule,
    packages: &mut BTreeSet<PackageId>,
) {
    collect_item_package(&rule.configuration, packages);
    if let Some(head_sort) = &rule.head_sort {
        collect_sort_ref_package(&head_sort.sort, packages);
    }
    for binding in &rule.bindings {
        if let Some(refinement) = &binding.refinement {
            collect_sort_ref_package(&refinement.sort, packages);
        }
    }
    if let Some(head) = &rule.head {
        collect_term_packages(&head.subject, packages);
        match &head.result {
            krs_ir::ProtocolHeadRuleResult::Replace(term) => {
                collect_term_packages(term, packages);
            }
            krs_ir::ProtocolHeadRuleResult::Splice(items) => {
                for term in items {
                    collect_term_packages(term, packages);
                }
            }
            krs_ir::ProtocolHeadRuleResult::Erase => {}
        }
    }
    for extra in &rule.extras {
        match extra {
            krs_ir::ProtocolHeadRuleExtra::HaveMap { key, .. } => {
                collect_term_packages(key, packages);
            }
            krs_ir::ProtocolHeadRuleExtra::UpdateMap { update, .. } => {
                collect_term_packages(update, packages);
            }
            krs_ir::ProtocolHeadRuleExtra::RewriteCell { before, after, .. } => {
                collect_term_packages(before, packages);
                collect_term_packages(after, packages);
            }
        }
    }
    if let Some(requires) = &rule.requires {
        collect_term_packages(&requires.term, packages);
    }
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
                krs_ir::TermArgumentRef::Positional { value }
                | krs_ir::TermArgumentRef::Named { value, .. } => value,
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
            ProtocolRuleStateTerm::Term(term) | ProtocolRuleStateTerm::Group(term) => {
                collect_term_packages(term, packages);
            }
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
