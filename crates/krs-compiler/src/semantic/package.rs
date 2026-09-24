use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    Descriptor, DescriptorApplicationRef, DescriptorCellDeclaration, DescriptorFixedConfiguration,
    DescriptorInitializerCell, DescriptorInitializerStateTerm, DescriptorPayload,
    DescriptorProductionAttribute, DescriptorProductionItem, DescriptorProductionOwner,
    DescriptorRuleCells, DescriptorSortRef, DescriptorTerm, DescriptorTermArgument,
    GrammarDescriptor, ModuleId, PackageId, ProtocolCellContent, ProtocolContextAliasBindingKind,
    ProtocolInitializerCellContent, ProtocolInitializerStateTerm, ProtocolMapBody,
    ProtocolRuleBindingKind, ProtocolRuleMapBody, ProtocolRuleStateTerm, SemanticModule,
    SemanticProduction, SemanticSort, SemanticSortRef, SemanticSubsort, StableItemId,
};
use krs_syntax::ProvenanceRole;

use super::catalog::{DeclarationCatalog, ProductionSignature, semantic_sort_ref};
use super::configuration::lower_fixed_configuration_descriptor;
use super::configuration_rules::{
    lower_configuration_rule_descriptor, lower_context_alias_descriptor,
};
use super::error::DescriptorLoweringError;
use super::grammar::{lower_constructor_grammar, lower_grammar_descriptor};
use super::origin::{role_key, semantic_origin, semantic_origin_from_primary};
use super::rules::{lower_head_rule_descriptor, lower_structured_rule_descriptor};

#[allow(clippy::too_many_lines)]
pub(super) fn lower_package_module(
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

fn lower_camel(value: &str) -> String {
    let mut characters = value.chars();
    match characters.next() {
        Some(first) => first.to_lowercase().chain(characters).collect(),
        None => String::new(),
    }
}
