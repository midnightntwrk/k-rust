use krs_ir::{
    Descriptor, DescriptorApplicationRef, DescriptorDeclaration, DescriptorProduction,
    DescriptorProductionAttribute, DescriptorProductionItem, DescriptorProductionOwner,
    GeneratedProductionKind, GrammarDescriptor, GroupAssociativitySentence, PrecedenceRelation,
    ProductionAttribute, StableItemId, generated_production_id,
};
use krs_ir_levels::{SemanticProduction, SemanticProductionItem, SemanticSortRef, SemanticSubsort};

use super::catalog::semantic_sort_ref;
use super::error::DescriptorLoweringError;
use super::origin::semantic_origin;
use super::package::ModuleSentences;

pub(super) fn lower_grammar_descriptor(
    descriptor: &Descriptor,
    grammar: &GrammarDescriptor,
    declaration: &DescriptorDeclaration,
    module: &mut ModuleSentences,
) -> Result<(), DescriptorLoweringError> {
    match grammar {
        GrammarDescriptor::Production(production) => {
            module.productions.push(lower_grammar_production(
                descriptor,
                production,
                declaration,
            )?);
        }
        GrammarDescriptor::Subsort {
            key,
            subsort,
            supersort,
        } => module.subsorts.push(SemanticSubsort::new(
            semantic_origin(descriptor, key.clone(), "subsort")?,
            semantic_sort_ref(&subsort.sort),
            semantic_sort_ref(&supersort.sort),
        )),
        GrammarDescriptor::Precedence { chains, .. } => {
            for (chain_index, chain) in chains.iter().enumerate() {
                for (edge_index, (tighter, looser)) in
                    chain.groups.iter().zip(chain.groups.tail()).enumerate()
                {
                    module.precedences.push(
                        PrecedenceRelation::new(
                            semantic_origin(
                                descriptor,
                                chain.key.clone(),
                                &format!("precedence-{chain_index}-{edge_index}"),
                            )?,
                            vec![tighter.group.clone()],
                            vec![looser.group.clone()],
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
                module.associativities.push(
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

fn lower_grammar_production(
    descriptor: &Descriptor,
    production: &DescriptorProduction,
    declaration: &DescriptorDeclaration,
) -> Result<SemanticProduction, DescriptorLoweringError> {
    let id = production_owner_id(descriptor, production)?;
    let items = production
        .items
        .iter()
        .map(|item| lower_production_item(descriptor, item))
        .collect::<Result<Vec<_>, _>>()?;
    let attributes = production
        .attributes
        .iter()
        .map(|attribute| lower_production_attribute(descriptor, attribute))
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

/// Returns the production identity: the owning constructor, or the generated
/// token or bracket production of the owning sort.
fn production_owner_id(
    descriptor: &Descriptor,
    production: &DescriptorProduction,
) -> Result<StableItemId, DescriptorLoweringError> {
    Ok(match &production.owner {
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
            generated_production_id(descriptor.id(), GeneratedProductionKind::Token).map_err(
                |error| DescriptorLoweringError::InvalidGeneratedIdentity(error.to_string()),
            )?
        }
        DescriptorProductionOwner::BracketSort { .. } => {
            generated_production_id(descriptor.id(), GeneratedProductionKind::Bracket).map_err(
                |error| DescriptorLoweringError::InvalidGeneratedIdentity(error.to_string()),
            )?
        }
    })
}

fn lower_production_item(
    descriptor: &Descriptor,
    item: &DescriptorProductionItem,
) -> Result<SemanticProductionItem, DescriptorLoweringError> {
    match item {
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
    }
}

fn lower_production_attribute(
    descriptor: &Descriptor,
    attribute: &DescriptorProductionAttribute,
) -> Result<ProductionAttribute<SemanticSortRef>, DescriptorLoweringError> {
    Ok(match attribute {
        DescriptorProductionAttribute::Documentation { key, text } => {
            ProductionAttribute::Documentation {
                origin: semantic_origin(descriptor, key.clone(), "production-documentation")?,
                text: text.clone(),
            }
        }
        DescriptorProductionAttribute::Function { key } => ProductionAttribute::Function {
            origin: semantic_origin(descriptor, key.clone(), "production-attribute")?,
        },
        DescriptorProductionAttribute::Total { key } => ProductionAttribute::Total {
            origin: semantic_origin(descriptor, key.clone(), "production-attribute")?,
        },
        DescriptorProductionAttribute::Hook { key, operation } => ProductionAttribute::Hook {
            origin: semantic_origin(descriptor, key.clone(), "production-attribute")?,
            operation: *operation,
        },
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
            origin: semantic_origin(descriptor, reference.key.clone(), "production-attribute")?,
            group: reference.group.clone(),
        },
        DescriptorProductionAttribute::Bracket { key } => ProductionAttribute::Bracket {
            origin: semantic_origin(descriptor, key.clone(), "production-attribute")?,
        },
        DescriptorProductionAttribute::Avoid { key } => ProductionAttribute::Avoid {
            origin: semantic_origin(descriptor, key.clone(), "production-attribute")?,
        },
        DescriptorProductionAttribute::Format { key, fragments } => ProductionAttribute::Format {
            origin: semantic_origin(descriptor, key.clone(), "production-attribute")?,
            fragments: fragments
                .iter()
                .map(|fragment| fragment.fragment.clone())
                .collect(),
        },
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
        DescriptorProductionAttribute::Internal { key } => ProductionAttribute::Internal {
            origin: semantic_origin(descriptor, key.clone(), "production-attribute")?,
        },
        DescriptorProductionAttribute::Program { key } => ProductionAttribute::Program {
            origin: semantic_origin(descriptor, key.clone(), "production-attribute")?,
        },
        DescriptorProductionAttribute::Color { key, value } => ProductionAttribute::Color {
            origin: semantic_origin(descriptor, key.clone(), "production-attribute")?,
            value: value.clone(),
        },
        DescriptorProductionAttribute::Colors { key, values } => ProductionAttribute::Colors {
            origin: semantic_origin(descriptor, key.clone(), "production-attribute")?,
            values: values.iter().map(|entry| entry.value.clone()).collect(),
        },
    })
}
