use krs_ir::{
    Descriptor, DescriptorApplicationRef, DescriptorDeclaration, DescriptorProduction,
    DescriptorProductionAttribute, DescriptorProductionItem, DescriptorProductionOwner,
    GeneratedProductionKind, GrammarDescriptor, GroupAssociativitySentence, LayoutSentence,
    LexicalSentence, PrecedenceRelation, ProductionAttribute, StableItemId, TokenProductionContent,
    generated_production_id,
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
        GrammarDescriptor::Tokens { productions } => {
            for production in productions {
                module.productions.push(lower_grammar_production(
                    descriptor,
                    production,
                    declaration,
                )?);
            }
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
        GrammarDescriptor::Lexical { .. } | GrammarDescriptor::Layout { .. } => {
            lower_lexing_descriptor(descriptor, grammar, module)?;
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
        GrammarDescriptor::RawSentence {
            key,
            kind,
            text,
            line,
            column,
        } => {
            module.raw_sentences.push(krs_ir::RawSentence {
                origin: semantic_origin(descriptor, key.clone(), "raw-k")?,
                kind: *kind,
                text: text.clone(),
                line: *line,
                column: *column,
                builtin_sorts: std::collections::BTreeSet::new(),
            });
        }
    }
    Ok(())
}

/// Lowers the entries of one `k::lexical!` or `k::layout!` block (KF-004).
fn lower_lexing_descriptor(
    descriptor: &Descriptor,
    grammar: &GrammarDescriptor,
    module: &mut ModuleSentences,
) -> Result<(), DescriptorLoweringError> {
    let shape = |node: &'static str| {
        move |error: krs_ir::GrammarShapeError| DescriptorLoweringError::UnsupportedShape {
            node,
            detail: error.to_string(),
        }
    };
    match grammar {
        GrammarDescriptor::Lexical { lexicals } => {
            for lexical in lexicals {
                module.lexicals.push(
                    LexicalSentence::new(
                        semantic_origin(descriptor, lexical.key.clone(), "lexical")?,
                        lexical.name.clone(),
                        lexical.regex.clone(),
                    )
                    .map_err(shape("lexical"))?,
                );
            }
        }
        GrammarDescriptor::Layout { regexes } => {
            for regex in regexes {
                module.layouts.push(
                    LayoutSentence::new(
                        semantic_origin(descriptor, regex.key.clone(), "layout")?,
                        regex.regex.clone(),
                    )
                    .map_err(shape("layout"))?,
                );
            }
        }
        _ => {}
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
pub(super) fn production_owner_id(
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
            // Each production of a token carrier is keyed by its content, so
            // reordering stacked attributes keeps every identity (F3.4).
            let content = match production.items.as_slice() {
                [DescriptorProductionItem::RegexTerminal { regex, .. }] => {
                    TokenProductionContent::Regex(regex)
                }
                [DescriptorProductionItem::Terminal { text, .. }] => {
                    TokenProductionContent::Terminal(text)
                }
                _ => {
                    return Err(DescriptorLoweringError::UnsupportedShape {
                        node: "token production",
                        detail: "a token production has exactly one regex or terminal".to_owned(),
                    });
                }
            };
            generated_production_id(descriptor.id(), GeneratedProductionKind::Token { content })
                .map_err(|error| {
                    DescriptorLoweringError::InvalidGeneratedIdentity(error.to_string())
                })?
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

#[expect(
    clippy::too_many_lines,
    reason = "Keeps exhaustive production attribute lowering in one match."
)]
fn lower_production_attribute(
    descriptor: &Descriptor,
    attribute: &DescriptorProductionAttribute,
) -> Result<ProductionAttribute<SemanticSortRef, StableItemId>, DescriptorLoweringError> {
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
        DescriptorProductionAttribute::Alias { key, recursive } => ProductionAttribute::Alias {
            origin: semantic_origin(descriptor, key.clone(), "production-attribute")?,
            recursive: recursive.is_some(),
        },
        DescriptorProductionAttribute::Desugar { key, recursive } => ProductionAttribute::Desugar {
            origin: semantic_origin(descriptor, key.clone(), "production-attribute")?,
            recursive: recursive.is_some(),
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
        DescriptorProductionAttribute::Prefer { key } => ProductionAttribute::Prefer {
            origin: semantic_origin(descriptor, key.clone(), "production-attribute")?,
        },
        DescriptorProductionAttribute::FreshGenerator { key } => {
            ProductionAttribute::FreshGenerator {
                origin: semantic_origin(descriptor, key.clone(), "production-attribute")?,
            }
        }
        DescriptorProductionAttribute::Memo { key } => ProductionAttribute::Memo {
            origin: semantic_origin(descriptor, key.clone(), "production-attribute")?,
        },
        DescriptorProductionAttribute::Smtlib { key, symbol } => ProductionAttribute::Smtlib {
            origin: semantic_origin(descriptor, key.clone(), "production-attribute")?,
            symbol: symbol.clone(),
        },
        DescriptorProductionAttribute::SmtHook { key, template } => ProductionAttribute::SmtHook {
            origin: semantic_origin(descriptor, key.clone(), "production-attribute")?,
            template: template
                .iter()
                .map(|fragment| fragment.fragment.clone())
                .collect(),
        },
        DescriptorProductionAttribute::ListCons {
            key,
            separator,
            non_empty,
            terminator,
            ..
        } => ProductionAttribute::ListCons {
            origin: semantic_origin(descriptor, key.clone(), "production-attribute")?,
            separator: separator.clone(),
            non_empty: non_empty.is_some(),
            terminator: list_partner(descriptor, terminator)?,
        },
        DescriptorProductionAttribute::ListTerminator { cons } => {
            ProductionAttribute::ListTerminator {
                origin: semantic_origin(descriptor, cons.key.clone(), "production-attribute")?,
                cons: list_partner(descriptor, cons)?,
            }
        }
        DescriptorProductionAttribute::RawHook {
            key,
            namespace,
            name,
        } => ProductionAttribute::RawHook {
            origin: semantic_origin(descriptor, key.clone(), "production-attribute")?,
            namespace: namespace.clone(),
            name: name.clone(),
        },
        DescriptorProductionAttribute::Overload { target } => {
            let origin = semantic_origin(descriptor, target.key.clone(), "production-attribute")?;
            let DescriptorApplicationRef::Declared(id) = &target.application else {
                return Err(DescriptorLoweringError::InvalidOverload {
                    production: Box::new(descriptor.id().clone()),
                    reason: "the target is a builtin operation; `overload` relates constructor productions".to_owned(),
                    range: origin.origin().exact_authored_range().map(Box::new),
                });
            };
            ProductionAttribute::Overload {
                origin,
                target: id.clone(),
            }
        }
    })
}

/// Resolves the other production of a syntactic list: a variant of the same
/// `#[k::syntax_list]` enum.
fn list_partner(
    descriptor: &Descriptor,
    partner: &krs_ir::DescriptorApplicationReference,
) -> Result<StableItemId, DescriptorLoweringError> {
    let DescriptorApplicationRef::Declared(id) = &partner.application else {
        return Err(DescriptorLoweringError::UnsupportedShape {
            node: "syntactic list",
            detail: format!(
                "{} names a builtin operation as its list partner",
                descriptor.id()
            ),
        });
    };
    Ok(id.clone())
}
