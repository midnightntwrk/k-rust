use std::collections::BTreeMap;

use krs_ir::{
    Descriptor, DescriptorApplicationRef, DescriptorCellDeclaration, DescriptorCellField,
    DescriptorCellIdentity, DescriptorFixedConfiguration, DescriptorInitializerCell,
    DescriptorInitializerStateTerm, DescriptorPayload, DescriptorProductionAttribute,
    DescriptorProductionItem, DescriptorProductionOwner, DescriptorRuleCells, DescriptorSortRef,
    DescriptorTerm, DescriptorTermArgument, GrammarDescriptor, ItemKind, ProtocolCellContent,
    ProtocolInitializerCellContent, ProtocolInitializerStateTerm, ProtocolMapBody,
    ProtocolRuleBindingKind, ProtocolRuleMapBody, ProtocolRuleStateTerm, StableItemId,
    StructuredRuleDescriptor,
};

use super::error::DescriptorLoweringError;

pub(super) fn validate_all_stable_references(
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
                                "field {:?} on {} has no resolved sort",
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

pub(super) fn require_descriptor<'a>(
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

pub(super) fn require_cell_field<'a>(
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
