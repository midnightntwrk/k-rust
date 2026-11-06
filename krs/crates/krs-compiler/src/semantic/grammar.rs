use std::collections::BTreeMap;

use krs_ir::{
    CellSortArgument, Descriptor, DescriptorApplicationRef, DescriptorDeclaration, DescriptorIndex,
    DescriptorProduction, DescriptorProductionAttribute, DescriptorProductionItem,
    DescriptorProductionOwner, GeneratedProductionKind, GrammarDescriptor,
    GroupAssociativitySentence, LayoutSentence, LexicalSentence, PrecedenceRelation,
    ProductionAttribute, ProductionFieldId, StableItemId, TokenProductionContent,
    generated_production_id,
};
use krs_ir_levels::{SemanticProduction, SemanticProductionItem, SemanticSortRef, SemanticSubsort};

use super::catalog::semantic_sort_ref;
use super::collection_types::SortType;
use super::error::DescriptorLoweringError;
use super::origin::semantic_origin;
use super::package::ModuleSentences;

pub(super) fn lower_grammar_descriptor(
    descriptor: &Descriptor,
    grammar: &GrammarDescriptor,
    declaration: &DescriptorDeclaration,
    descriptors: &DescriptorIndex<'_>,
    module: &mut ModuleSentences,
) -> Result<(), DescriptorLoweringError> {
    match grammar {
        GrammarDescriptor::Production(production) => {
            module.productions.push(lower_grammar_production(
                descriptor,
                production,
                declaration,
                descriptors,
            )?);
        }
        GrammarDescriptor::Tokens { productions } => {
            for production in productions {
                module.productions.push(lower_grammar_production(
                    descriptor,
                    production,
                    declaration,
                    descriptors,
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
                            DescriptorLoweringError::unsupported_shape(
                                "precedence",
                                error.to_string(),
                            )
                        })?,
                    );
                }
            }
        }
        GrammarDescriptor::Lexical { .. } | GrammarDescriptor::Layout { .. } => {
            lower_lexing_descriptor(descriptor, grammar, module)?;
        }
        // A spec-module declaration is not a sentence; `spec_modules` reads it.
        GrammarDescriptor::SpecModule { .. } => {}
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
                        DescriptorLoweringError::unsupported_shape(
                            "associativity",
                            error.to_string(),
                        )
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
        move |error: krs_ir::GrammarShapeError| {
            DescriptorLoweringError::unsupported_shape(node, error.to_string())
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
    descriptors: &DescriptorIndex<'_>,
) -> Result<SemanticProduction, DescriptorLoweringError> {
    let id = production_owner_id(descriptor, production)?;
    check_strict_positions(descriptor, production, &id)?;
    let (field_arguments, result_arguments) = declared_arguments(descriptors, production, &id);
    let items = production
        .items
        .iter()
        .map(|item| lower_production_item(descriptor, item))
        .collect::<Result<Vec<_>, _>>()?;
    // `#[k::cons_list]` is notation for terms, which semantic lowering has
    // already replaced by constructors: the production itself is unchanged.
    let attributes = production
        .attributes
        .iter()
        .filter(|attribute| !matches!(attribute, DescriptorProductionAttribute::ConsList { .. }))
        .map(|attribute| lower_production_attribute(descriptor, attribute))
        .collect::<Result<Vec<_>, DescriptorLoweringError>>()?;
    let parameters = production
        .parameters
        .iter()
        .map(|parameter| match &parameter.sort {
            krs_ir::DescriptorSortRef::Parameter(name) => {
                Ok(krs_ir_levels::SortParameterId::new(name.clone()))
            }
            _ => Err(DescriptorLoweringError::unsupported_shape(
                "sort parameter",
                "a production's sort parameter resolves to a sort",
            )),
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(SemanticProduction::with_api(
        semantic_origin(descriptor, production.key.clone(), "production")?,
        id,
        semantic_sort_ref(&production.result_sort.sort),
        items,
        attributes,
        declaration.visibility.clone(),
        declaration.explicit_symbol.clone(),
    )?
    .with_parameters(parameters)
    .with_arguments(field_arguments, result_arguments))
}

/// The element types of one typed collection position, in order.
type ElementTypes = Vec<CellSortArgument<SemanticSortRef>>;

/// The element types a constructor's or function's declaration states for its typed collection
/// fields and result (`Reg8` and `Int` of `regs: Map<Reg8, Int>`), keyed by the production's
/// fields. K erases them, so the production keeps them for every reader that types a value at one
/// of those positions; a field declared without them has no entry. A token production has no
/// constructor declaration and none.
fn declared_arguments(
    descriptors: &DescriptorIndex<'_>,
    production: &DescriptorProduction,
    id: &StableItemId,
) -> (BTreeMap<ProductionFieldId, ElementTypes>, ElementTypes) {
    let DescriptorProductionOwner::Constructor { .. } = &production.owner else {
        return (BTreeMap::new(), Vec::new());
    };
    let Ok(constructor) = descriptors.constructor(id) else {
        return (BTreeMap::new(), Vec::new());
    };
    let fields = production
        .items
        .iter()
        .filter_map(|item| match item {
            DescriptorProductionItem::NonTerminal { field, .. } => Some(field),
            _ => None,
        })
        .collect::<Vec<_>>();
    let field_arguments = constructor
        .fields
        .iter()
        .filter(|field| !field.arguments.is_empty())
        .filter_map(|field| {
            let name = fields
                .iter()
                .find(|production_field| production_field.as_str() == field.name)?;
            Some((
                (*name).clone(),
                SortType::of_production(&field.sort.sort, &field.arguments).ir_arguments(),
            ))
        })
        .collect();
    let result_arguments =
        SortType::of_production(&constructor.sort, &constructor.arguments).ir_arguments();
    (field_arguments, result_arguments)
}

/// Rejects what K and k-rust do not accept on a parametric production
/// (KF-027): a parameter named like a sort, and strictness, an alias or
/// desugar marker, a hook, a token, or a bracket.
pub(super) fn check_parametric_production(
    descriptor: &Descriptor,
    production: &DescriptorProduction,
    sort_parents: &std::collections::BTreeMap<
        SemanticSortRef,
        std::collections::BTreeSet<SemanticSortRef>,
    >,
) -> Result<(), DescriptorLoweringError> {
    if production.parameters.is_empty() {
        return Ok(());
    }
    let error = |key: &krs_ir::ProvenanceKey, reason: String| {
        DescriptorLoweringError::InvalidParametricProduction {
            item: Box::new(descriptor.id().clone()),
            reason,
            range: descriptor
                .provenance()
                .origin_for(key)
                .and_then(krs_ir::OriginStack::exact_authored_range)
                .map(Box::new),
        }
    };
    let sort_names = sort_parents
        .iter()
        .flat_map(|(sort, parents)| std::iter::once(sort).chain(parents))
        .filter_map(|sort| match sort {
            SemanticSortRef::Declared(id) => Some(id.item_name().to_owned()),
            _ => None,
        })
        .chain(
            krs_ir::BuiltinSort::ALL
                .iter()
                .map(|sort| sort.k_name().to_owned()),
        )
        .chain(["K", "KItem", "KResult", "Bag", "KConfigVar"].map(str::to_owned))
        .collect::<std::collections::BTreeSet<_>>();
    for parameter in &production.parameters {
        if let krs_ir::DescriptorSortRef::Parameter(name) = &parameter.sort
            && sort_names.contains(name)
        {
            return Err(error(
                &parameter.key,
                format!(
                    "the sort parameter `{name}` has the name of a sort, so K would read `syntax {{{name}}}` as that sort; rename the parameter, such as `S`"
                ),
            ));
        }
    }
    for attribute in &production.attributes {
        let marker = match attribute {
            DescriptorProductionAttribute::Strictness { .. } => {
                "`#[k::strict]` or `#[k::seqstrict]`: k-rust rejects strictness on a parametric production (InvalidStrictness)"
            }
            DescriptorProductionAttribute::Alias { .. }
            | DescriptorProductionAttribute::Desugar { .. } => {
                "`#[k::alias]` or `#[k::desugar]`: a static rewrite of a parametric production is not supported"
            }
            DescriptorProductionAttribute::Hook { .. }
            | DescriptorProductionAttribute::RawHook { .. } => {
                "a hook: KRS's hooked operations are fixed builtin signatures"
            }
            DescriptorProductionAttribute::Token { .. } => {
                "a token: a token production has a fixed sort"
            }
            DescriptorProductionAttribute::Bracket { .. } => {
                "a bracket: a bracket production has a fixed sort"
            }
            _ => continue,
        };
        return Err(error(
            &production.key,
            format!("a parametric production (K's `syntax {{S}}`) cannot carry {marker}"),
        ));
    }
    Ok(())
}

/// Rejects a `#[k::strict]` or `#[k::seqstrict]` position whose field has sort
/// `KSequence`, at the position's field reference.
///
/// Heating a strict position moves the argument there to the front of the
/// computation as one item, `HOLE ~> f(□)`, and cooling puts it back once it
/// is a result. A `KSequence` value is a sequence of items, possibly the empty
/// `.K`, so it is not an item: there is no term the step could move, and no
/// heating step exists for the position. Every other sort a field can have
/// (a declared sort, a builtin domain, `KItem`, `KResult`) is a sort of single
/// items, so `KSequence` is the one sort refused; a sort parameter, which could
/// stand for it, never reaches here, since a parametric production takes no
/// strictness at all ([`check_parametric_production`]). A position evaluated
/// through a context alias (`using`) is heated by the alias's context at the
/// same argument, so it is refused alike.
fn check_strict_positions(
    descriptor: &Descriptor,
    production: &DescriptorProduction,
    id: &StableItemId,
) -> Result<(), DescriptorLoweringError> {
    for attribute in &production.attributes {
        let DescriptorProductionAttribute::Strictness { fields, .. } = attribute else {
            continue;
        };
        for field in fields {
            let sequence = production.items.iter().any(|item| {
                matches!(
                    item,
                    DescriptorProductionItem::NonTerminal { field: name, sort, .. }
                        if *name == field.field
                            && sort.sort == krs_ir::DescriptorSortRef::Builtin(krs_ir::BuiltinSort::KSequence)
                )
            });
            if !sequence {
                continue;
            }
            return Err(DescriptorLoweringError::InvalidStrictness {
                item: Box::new(id.clone()),
                reason: format!(
                    "the strict position `{}` of `{}` has sort `KSequence`: heating moves the argument at a strict position to the front of the computation as one item, and a `KSequence` is a sequence of items, so the position has no heating step; give the field a sort of single items, such as `k::KItem` or a declared sort, or leave it out of the strictness",
                    field.field.as_str(),
                    id.item_name(),
                ),
                range: descriptor
                    .provenance()
                    .origin_for(&field.key)
                    .and_then(krs_ir::OriginStack::exact_authored_range)
                    .map(Box::new),
            });
        }
    }
    Ok(())
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
                return Err(DescriptorLoweringError::unsupported_shape(
                    "constructor production owner",
                    "builtin operations cannot own authored grammar",
                ));
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
                    return Err(DescriptorLoweringError::unsupported_shape(
                        "token production",
                        "a token production has exactly one regex or terminal",
                    ));
                }
            };
            generated_production_id(descriptor.id(), GeneratedProductionKind::Token { content })
                .map_err(|error| DescriptorLoweringError::InvalidGeneratedIdentity {
                    detail: error.to_string(),
                    range: None,
                    item: None,
                })?
        }
        DescriptorProductionOwner::BracketSort { .. } => {
            generated_production_id(descriptor.id(), GeneratedProductionKind::Bracket).map_err(
                |error| DescriptorLoweringError::InvalidGeneratedIdentity {
                    detail: error.to_string(),
                    range: None,
                    item: None,
                },
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
        .map_err(|error| {
            DescriptorLoweringError::unsupported_shape("production terminal", error.to_string())
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
        .map_err(|error| {
            DescriptorLoweringError::unsupported_shape("production regex", error.to_string())
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
        DescriptorProductionAttribute::Underspecified { key, reason } => {
            ProductionAttribute::Underspecified {
                origin: semantic_origin(descriptor, key.clone(), "production-attribute")?,
                reason: reason.clone(),
            }
        }
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
        DescriptorProductionAttribute::ConsList { .. } => {
            unreachable!("cons-list notation metadata is filtered before lowering")
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
        return Err(DescriptorLoweringError::unsupported_shape(
            "syntactic list",
            format!(
                "{} names a builtin operation as its list partner",
                descriptor.id()
            ),
        ));
    };
    Ok(id.clone())
}
