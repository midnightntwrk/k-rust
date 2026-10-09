use krs_ir::{
    Descriptor, DescriptorApplicationRef, DescriptorCellDeclaration, DescriptorCellField,
    DescriptorCellIdentity, DescriptorFixedConfiguration, DescriptorIndex,
    DescriptorInitializerCell, DescriptorInitializerStateTerm, DescriptorPayload,
    DescriptorProductionAttribute, DescriptorProductionItem, DescriptorProductionOwner,
    DescriptorRuleCells, DescriptorSortRef, DescriptorTerm, GrammarDescriptor, ProtocolCellContent,
    ProtocolInitializerCellContent, ProtocolInitializerStateTerm, ProtocolMapBody,
    ProtocolRuleBindingKind, ProtocolRuleMapBody, ProtocolRuleStateTerm, StructuredRuleDescriptor,
};

use super::error::DescriptorLoweringError;

pub(super) fn validate_all_stable_references(
    descriptors: &[&Descriptor],
    declarations: &DescriptorIndex<'_>,
) -> Result<(), DescriptorLoweringError> {
    for descriptor in descriptors {
        match descriptor.payload() {
            DescriptorPayload::Sort(sort) => {
                for parent in &sort.parents {
                    declarations.sort(parent)?;
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
                                field.name,
                                descriptor.id()
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
                declarations.configuration(&rule.subject_configuration.configuration)?;
                if let Some(result_configuration) = &rule.result_configuration {
                    declarations.configuration(&result_configuration.configuration)?;
                }
                validate_configuration_rule_references(rule, declarations)?;
            }
            DescriptorPayload::HeadRule(rule) => {
                declarations.configuration(&rule.configuration)?;
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
                declarations.configuration(&alias.configuration.configuration)?;
                validate_rule_cells_references(&alias.pattern, declarations)?;
            }
        }
    }
    Ok(())
}

fn validate_sort_ref(
    sort: &DescriptorSortRef,
    declarations: &DescriptorIndex<'_>,
) -> Result<(), DescriptorLoweringError> {
    if let DescriptorSortRef::Declared(id) = sort {
        declarations.sort(id)?;
    }
    Ok(())
}

fn validate_application_ref(
    application: &DescriptorApplicationRef,
    declarations: &DescriptorIndex<'_>,
) -> Result<(), DescriptorLoweringError> {
    if let DescriptorApplicationRef::Declared(id) = application {
        declarations.constructor(id)?;
    }
    Ok(())
}

fn validate_production_references(
    production: &krs_ir::DescriptorProduction,
    declarations: &DescriptorIndex<'_>,
) -> Result<(), DescriptorLoweringError> {
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
        if let DescriptorProductionAttribute::Overload { target }
        | DescriptorProductionAttribute::ListCons {
            terminator: target, ..
        }
        | DescriptorProductionAttribute::ListTerminator { cons: target } = attribute
        {
            validate_application_ref(&target.application, declarations)?;
        }
    }
    Ok(())
}

fn validate_grammar_references(
    grammar: &GrammarDescriptor,
    declarations: &DescriptorIndex<'_>,
) -> Result<(), DescriptorLoweringError> {
    match grammar {
        GrammarDescriptor::Production(production) => {
            validate_production_references(production, declarations)?;
        }
        GrammarDescriptor::Tokens { productions } => {
            for production in productions {
                validate_production_references(production, declarations)?;
            }
        }
        GrammarDescriptor::Subsort {
            subsort, supersort, ..
        } => {
            validate_sort_ref(&subsort.sort, declarations)?;
            validate_sort_ref(&supersort.sort, declarations)?;
        }
        GrammarDescriptor::Precedence { .. }
        | GrammarDescriptor::Associativity { .. }
        | GrammarDescriptor::Lexical { .. }
        | GrammarDescriptor::Layout { .. }
        | GrammarDescriptor::RawSentence { .. }
        | GrammarDescriptor::SpecModule { .. } => {}
    }
    Ok(())
}

fn validate_structured_rule_references(
    rule: &StructuredRuleDescriptor,
    declarations: &DescriptorIndex<'_>,
) -> Result<(), DescriptorLoweringError> {
    validate_sort_ref(&rule.subject_sort.sort, declarations)?;
    if let Some(result_sort) = &rule.result_sort {
        validate_sort_ref(&result_sort.sort, declarations)?;
    }
    validate_structured_term_references(&rule.subject, declarations)?;
    if let Some(result) = &rule.result {
        validate_structured_term_references(result, declarations)?;
    }
    if let Some(requires) = &rule.requires {
        validate_structured_term_references(&requires.term, declarations)?;
    }
    Ok(())
}

fn validate_structured_term_references(
    term: &DescriptorTerm,
    declarations: &DescriptorIndex<'_>,
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
                krs_ir::TermArgumentRef::Positional { value }
                | krs_ir::TermArgumentRef::Named { value, .. } => value,
            };
            validate_structured_term_references(value, declarations)?;
        }
    }
    Ok(())
}

fn validate_fixed_configuration_references(
    configuration: &DescriptorFixedConfiguration,
    declarations: &DescriptorIndex<'_>,
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
    declarations: &DescriptorIndex<'_>,
) -> Result<(), DescriptorLoweringError> {
    for field in &declaration.fields {
        match &field.content {
            ProtocolCellContent::Leaf { sort, .. } => {
                validate_sort_ref(&sort.sort, declarations)?;
            }
            ProtocolCellContent::Nested { declaration } => {
                declarations.cell(&declaration.declaration)?;
            }
        }
    }
    Ok(())
}

fn validate_initializer_cell_references(
    cell: &DescriptorInitializerCell,
    declarations: &DescriptorIndex<'_>,
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
            let nested_declaration = declarations.cell(&declaration.declaration)?;
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
    declarations: &DescriptorIndex<'_>,
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
    declarations: &DescriptorIndex<'_>,
) -> Result<(), DescriptorLoweringError> {
    for binding in &rule.bindings {
        if let ProtocolRuleBindingKind::Term { sort } = &binding.kind {
            validate_sort_ref(&sort.sort, declarations)?;
        }
    }
    validate_rule_cells_references(&rule.subject, declarations)?;
    if let Some(result) = &rule.result {
        validate_rule_cells_references(result, declarations)?;
    }
    if let Some(requires) = &rule.requires {
        validate_structured_term_references(&requires.term, declarations)?;
    }
    Ok(())
}

fn validate_rule_cells_references(
    cells: &DescriptorRuleCells,
    declarations: &DescriptorIndex<'_>,
) -> Result<(), DescriptorLoweringError> {
    for cell in &cells.cells {
        require_cell_field(&cell.field.cell, declarations)?;
        match &cell.value {
            ProtocolRuleStateTerm::Term(term) | ProtocolRuleStateTerm::Group(term) => {
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
    declarations: &'a DescriptorIndex<'_>,
) -> Result<&'a DescriptorCellField, DescriptorLoweringError> {
    let declaration = declarations.cell_owner(&identity.owner)?;
    declaration
        .fields
        .iter()
        .find(|field| field.reference.cell == *identity)
        .ok_or_else(|| DescriptorLoweringError::ParserReferenceDisagreement {
            id: Box::new(identity.owner.clone()),
            detail: format!("owner has no declared cell field {:?}", identity.field),
        })
}
