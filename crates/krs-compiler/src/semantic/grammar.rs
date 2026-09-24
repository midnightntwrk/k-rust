use std::collections::BTreeSet;

use krs_ir::{
    Descriptor, DescriptorApplicationRef, DescriptorDeclaration, DescriptorProduction,
    DescriptorProductionAttribute, DescriptorProductionItem, DescriptorProductionOwner,
    GeneratedProductionKind, GrammarDescriptor, GroupAssociativitySentence, PrecedenceRelation,
    ProductionAttribute, ProductionFieldId, SemanticProduction, SemanticProductionItem,
    SemanticSubsort, generated_production_id,
};
use krs_syntax::ProvenanceRole;

use super::catalog::semantic_sort_ref;
use super::error::DescriptorLoweringError;
use super::origin::{role_key, semantic_origin};

#[allow(clippy::too_many_arguments)]
pub(super) fn lower_grammar_descriptor(
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

#[allow(clippy::too_many_lines)]
pub(super) fn lower_constructor_grammar(
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

fn is_field_name(value: &str) -> bool {
    value
        .bytes()
        .next()
        .is_some_and(|byte| byte.is_ascii_alphabetic() || byte == b'_')
        && value
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
}
