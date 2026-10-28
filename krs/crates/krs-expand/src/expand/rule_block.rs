//! Readable rule blocks: `rules!`.

use crate::ExpandError;
use krs_diagnostic::codes::expand;
use krs_syntax::KrsSyntax;
use krs_syntax::TokenRange;
use krs_syntax::positions::Form;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::ext::IdentExt;

use super::existentials::{ensures_condition, existential_binders, fresh_binders};
use super::factory::{DescriptorFactory, FactoryPayload};
use super::ledger::KeyLedger;
use super::nonce::expansion_nonce;
use super::terms::{KeyedTerm, TermBuilder, TermSide, WireSlots};
use super::tokens::{call_site_cfg_attributes, spelling};
use crate::environment::MacroEnvironment;
use crate::provenance::host_provenance;

/// Expands a readable block into independent ordinary rule declarations.
pub(crate) fn rules(env: &dyn MacroEnvironment, input: TokenStream) -> crate::Result<TokenStream> {
    let block = krs_syntax::RuleBlock::parse_tokens(input)?;
    expand_block(env, &block)
}

/// Expands a readable claim block (F7) into independent claims: each clause
/// is a readable record clause whose descriptor is a claim.
pub(crate) fn claims(env: &dyn MacroEnvironment, input: TokenStream) -> crate::Result<TokenStream> {
    let block = krs_syntax::ClaimBlock::parse_tokens(input)?;
    expand_block(env, block.block())
}

fn expand_block(
    env: &dyn MacroEnvironment,
    block: &krs_syntax::RuleBlock,
) -> crate::Result<TokenStream> {
    let imports = block.imports();
    let import_checks = imports.iter().map(|item| {
        quote! {
            const _: () = {
                #[allow(unused_imports)]
                #item
            };
        }
    });
    // The `for` path names the sort (or configuration) every clause is
    // over. It reaches rustc once, at its authored tokens, as this alias's
    // definition; every generated mention of the block's sort names the
    // alias, so a path that resolves to nothing is one error, at the path.
    let sort = block.sort();
    let sort_ident = &sort
        .sort()
        .segments
        .last()
        .expect("a readable sort path has a segment")
        .ident;
    let sort_nonce = expansion_nonce(
        env,
        "rule_block_sort",
        sort_ident,
        TokenRange::for_tokens(sort.ty())?,
    );
    let authored_sort = sort.ty();
    let sort_alias = format_ident!(
        "__KrsBlockSort_{sort_nonce:016x}",
        span = syn::spanned::Spanned::span(authored_sort)
    );
    let mut clauses = Vec::with_capacity(block.clauses().len());
    for clause in block.clauses() {
        clauses.push(expand_head_rule(
            env,
            clause,
            imports,
            block.is_configuration(),
            &sort_alias,
        )?);
    }
    Ok(quote! {
        #(#import_checks)*
        #[doc(hidden)]
        #[allow(dead_code, non_camel_case_types)]
        type #sort_alias = #authored_sort;
        #(#clauses)*
    })
}

#[expect(
    clippy::too_many_lines,
    reason = "The complete rule clause is lowered in one ordered pass."
)]
fn expand_head_rule(
    env: &dyn MacroEnvironment,
    clause: &krs_syntax::RuleClause,
    imports: &[syn::ItemUse],
    configuration_owned: bool,
    sort_alias: &syn::Ident,
) -> crate::Result<TokenStream> {
    let facade = env.facade_path()?;
    let rule = clause.rule();
    let anchors = clause.descriptor_provenance()?;
    let fallback = TokenRange::for_tokens(rule.item())?;
    let provenance = host_provenance(env, &facade, fallback, &anchors);
    let ledger = KeyLedger::new(
        &anchors,
        &[
            krs_syntax::ProvenanceRole::RuleDeclaration,
            krs_syntax::ProvenanceRole::ClaimDeclaration,
        ],
    );
    let nonce = expansion_nonce(env, "head_rule", &rule.item().sig.ident, fallback);
    let factory = format_ident!("__krs_head_rule_descriptor_{nonce:016x}");
    let sort_key = format_ident!("__krs_head_rule_sort_{nonce:016x}");
    let cfg = call_site_cfg_attributes(&rule.item().attrs)?;
    let sort_spelling = rule.parameter().term_sort.sort_token_text();
    let mut slots = WireSlots::new(&facade);
    let sort_slot = slots.type_slot(quote!(#facade::HostTypeKey(#sort_key)));
    // Existentials are visible to every term; the parser has already
    // rejected a use in the subject, a read cell, or `requires`.
    let binding_idents = clause
        .bindings()
        .iter()
        .cloned()
        .chain(rule.existentials().names())
        .collect::<Vec<_>>();
    let form = if clause.claim().is_some() {
        Form::ReadableClaim
    } else if configuration_owned {
        Form::ReadableRule
    } else {
        Form::SortRule
    };
    let mut builder = TermBuilder::new(&facade, &ledger, nonce, &cfg, &binding_idents, form)
        .with_lexical_imports((!imports.is_empty()).then_some(imports));
    let mut refinement_functions = Vec::new();
    let mut bindings = Vec::new();
    let mut binding_checks = Vec::new();
    for binding in clause.bindings() {
        let name = binding.unraw().to_string();
        // A bit template's hidden binder is no name an author wrote or can
        // use, so tooling is not shown one at the template.
        if !krs_syntax::is_hidden_binder(&name) {
            binding_checks.push(quote! {
                let #binding = ();
            });
        }
        let refinement = if let Some((ordinal, narrowing)) = clause
            .narrowings()
            .iter()
            .enumerate()
            .find(|(_, narrowing)| narrowing.binding().unraw() == binding.unraw())
        {
            let key_fn = format_ident!("__krs_head_rule_refinement_{nonce:016x}_{ordinal}");
            // Keep the authored narrowing path visible to language tooling.
            let path = narrowing.sort();
            let authored = spelling(narrowing.sort());
            binding_checks.push(quote! {
                let _: ::core::marker::PhantomData<#path> = ::core::marker::PhantomData;
            });
            refinement_functions.push(quote! {
                #(#cfg)*
                #[doc(hidden)]
                fn #key_fn() -> ::core::any::TypeId {
                    ::core::any::TypeId::of::<#path>()
                }
            });
            let slot = slots.type_slot(quote!(#facade::HostTypeKey(#key_fn)));
            Some(krs_ir::wire::WireSortReference {
                key: ledger.define(narrowing.sort_key())?,
                target: krs_ir::wire::WireTypeReference {
                    slot,
                    authored_path: authored,
                },
            })
        } else {
            None
        };
        bindings.push(krs_ir::wire::WireHeadRuleBinding { name, refinement });
    }

    // A head that also reads as a List collection's front record lets rustc
    // resolve its record roots, which may name the instance struct (KF-023).
    let alternative = clause.bracket_alternative();
    let mut items = Vec::new();
    if clause.head().is_some_and(krs_syntax::RuleHead::subject) {
        items.push(builder.expand_wire(
            KeyedTerm::pattern(&rule.parameter().pattern, rule.subject_tree()),
            TermSide::Left,
            &mut slots,
        )?);
    }
    // The computation items after the first are the head's, before the
    // other cells.
    for item in clause.head().iter().flat_map(|head| head.following()) {
        items.push(builder.expand_wire(
            KeyedTerm::pattern(item.pattern(), item.tree()),
            TermSide::Left,
            &mut slots,
        )?);
    }

    let mut have_extras = Vec::new();
    let mut rewrite_befores = Vec::new();
    let mut state_befores = Vec::new();
    let mut list_befores = Vec::new();
    for (extra, extra_keys) in clause.extras().iter().zip(clause.extra_keys()) {
        match extra {
            krs_syntax::RuleExtra::HaveMap { cell, entries } => {
                let cell_name = cell.unraw().to_string();
                let entries = entries
                    .iter()
                    .map(|entry| {
                        Ok(krs_ir::wire::WireHeadRuleMapEntry {
                            key_key: ledger.define(entry.key.keys().payload())?,
                            key: builder.expand_key_wire(
                                KeyedTerm::of(&entry.key),
                                TermSide::Left,
                                &mut slots,
                            )?,
                            value_key: ledger.define(entry.value_key())?,
                            value_binding: entry.value.unraw().to_string(),
                        })
                    })
                    .collect::<Result<Vec<_>, ExpandError>>()?;
                have_extras.push(krs_ir::wire::WireHeadRuleExtra::HaveMap {
                    cell: krs_ir::wire::WireHeadRuleCellReference {
                        key: ledger.define(extra_keys.cell())?,
                        name: cell_name,
                    },
                    entries,
                });
            }
            krs_syntax::RuleExtra::RewriteCell {
                cell,
                before,
                before_tree,
                ..
            } => {
                let before = builder.expand_wire(
                    KeyedTerm::pattern(before, before_tree),
                    TermSide::Left,
                    &mut slots,
                )?;
                rewrite_befores.push((
                    cell.unraw().to_string(),
                    ledger.define(extra_keys.cell())?,
                    before,
                ));
            }
            krs_syntax::RuleExtra::RewriteState { cell, before, .. } => {
                let before = readable_state_wire(
                    before,
                    &mut ReadableStateContext {
                        builder: &mut builder,
                        slots: &mut slots,
                        side: krs_syntax::RuleSide::Left,
                    },
                )?;
                state_befores.push((
                    cell.unraw().to_string(),
                    ledger.define(extra_keys.cell())?,
                    before,
                ));
            }
            krs_syntax::RuleExtra::RewriteList { cell, before, .. } => {
                let mut items = Vec::with_capacity(before.items().len());
                for item in before.items() {
                    items.push(builder.expand_entry_wire(
                        KeyedTerm::pattern(item.pattern(), item.tree()),
                        TermSide::Left,
                        &mut slots,
                    )?);
                }
                let rest = match before.rest() {
                    krs_syntax::RuleListRest::Exact => krs_ir::ProtocolHeadRuleListRest::Exact,
                    krs_syntax::RuleListRest::Shared(_) => krs_ir::ProtocolHeadRuleListRest::Shared,
                    krs_syntax::RuleListRest::Named(rest) => {
                        krs_ir::ProtocolHeadRuleListRest::Term(builder.expand_wire(
                            KeyedTerm::pattern(rest.pattern(), rest.tree()),
                            TermSide::Left,
                            &mut slots,
                        )?)
                    }
                };
                let mut back = Vec::with_capacity(before.back().len());
                for item in before.back() {
                    back.push(builder.expand_entry_wire(
                        KeyedTerm::pattern(item.pattern(), item.tree()),
                        TermSide::Left,
                        &mut slots,
                    )?);
                }
                list_befores.push((
                    cell.unraw().to_string(),
                    ledger.define(extra_keys.cell())?,
                    krs_ir::wire::WireHeadRuleList { items, rest, back },
                ));
            }
            krs_syntax::RuleExtra::UpdateMap { .. } => {}
        }
    }

    let result = match clause.head_result() {
        None => None,
        Some(krs_syntax::RuleHeadResult::Replace(term)) => {
            let term = builder.expand_wire(KeyedTerm::of(term), TermSide::Right, &mut slots)?;
            Some(krs_ir::wire::WireHeadRuleResult::Replace(term))
        }
        Some(krs_syntax::RuleHeadResult::Splice { items, .. }) => {
            let payload_key = Some(ledger.define(clause.splice_key())?);
            let items = items
                .iter()
                .map(|item| {
                    Ok(krs_ir::ProtocolHeadRuleSpliceItem {
                        key: Some(ledger.define(item.keys().payload())?),
                        value: builder.expand_wire(
                            KeyedTerm::of(item),
                            TermSide::Right,
                            &mut slots,
                        )?,
                    })
                })
                .collect::<crate::Result<Vec<_>>>()?;
            Some(krs_ir::wire::WireHeadRuleResult::Splice(
                krs_ir::ProtocolHeadRuleSplice { payload_key, items },
            ))
        }
        Some(krs_syntax::RuleHeadResult::Erase(_)) => Some(krs_ir::wire::WireHeadRuleResult::Erase),
    };
    let head = clause.head().map(|head| krs_ir::wire::WireHeadRuleHead {
        items,
        exact: head.exact(),
        result,
    });
    let mut update_extras = Vec::new();
    let mut rewrite_index = 0_usize;
    let mut state_index = 0_usize;
    let mut list_index = 0_usize;
    for (extra, extra_keys) in clause.extras().iter().zip(clause.extra_keys()) {
        match extra {
            krs_syntax::RuleExtra::RewriteState {
                cell,
                result_cell,
                after,
                ..
            } => {
                let (cell_name, left_key, before) = &state_befores[state_index];
                state_index += 1;
                debug_assert_eq!(cell_name, &cell.unraw().to_string());
                let (result_key, after) = match (result_cell, after) {
                    (Some(_), Some(after)) => {
                        let after = readable_state_wire(
                            after,
                            &mut ReadableStateContext {
                                builder: &mut builder,
                                slots: &mut slots,
                                side: krs_syntax::RuleSide::Right,
                            },
                        )?;
                        (Some(ledger.define(extra_keys.result_cell())?), Some(after))
                    }
                    _ => (None, None),
                };
                update_extras.push(krs_ir::wire::WireHeadRuleExtra::RewriteState {
                    cell: krs_ir::wire::WireHeadRuleCellReference {
                        key: left_key.clone(),
                        name: cell_name.clone(),
                    },
                    result_key,
                    before: before.clone(),
                    after,
                });
            }
            krs_syntax::RuleExtra::UpdateMap { cell, base, update } => {
                let cell_name = cell.unraw().to_string();
                let base_binding = base.unraw().to_string();
                let update = builder.expand_wire(
                    KeyedTerm::of(update.term()),
                    TermSide::Right,
                    &mut slots,
                )?;
                update_extras.push(krs_ir::wire::WireHeadRuleExtra::UpdateMap {
                    cell: krs_ir::wire::WireHeadRuleCellReference {
                        key: ledger.define(extra_keys.result_cell())?,
                        name: cell_name,
                    },
                    base_binding,
                    update,
                });
            }
            krs_syntax::RuleExtra::RewriteCell { cell, after, .. } => {
                let (cell_name, left_key, before) = &rewrite_befores[rewrite_index];
                rewrite_index += 1;
                debug_assert_eq!(cell_name, &cell.unraw().to_string());
                // A cell the result leaves out is read only: it has no
                // result term and no result-field key.
                let (result_key, after) = if let Some(after) = after {
                    let after =
                        builder.expand_wire(KeyedTerm::of(after), TermSide::Right, &mut slots)?;
                    (Some(ledger.define(extra_keys.result_cell())?), Some(after))
                } else {
                    (None, None)
                };
                update_extras.push(krs_ir::wire::WireHeadRuleExtra::RewriteCell {
                    cell: krs_ir::wire::WireHeadRuleCellReference {
                        key: left_key.clone(),
                        name: cell_name.clone(),
                    },
                    result_key,
                    before: before.clone(),
                    after,
                });
            }
            krs_syntax::RuleExtra::RewriteList {
                cell,
                result_cell,
                after,
                ..
            } => {
                let (cell_name, left_key, before) = &list_befores[list_index];
                list_index += 1;
                debug_assert_eq!(cell_name, &cell.unraw().to_string());
                let (result_key, after) = match (result_cell, after) {
                    (Some(_), Some(after)) => {
                        let mut items = Vec::with_capacity(after.items().len());
                        for item in after.items() {
                            items.push(builder.expand_entry_wire(
                                KeyedTerm::of(item),
                                TermSide::Right,
                                &mut slots,
                            )?);
                        }
                        let rest = match after.rest() {
                            krs_syntax::RuleListRest::Exact => {
                                krs_ir::ProtocolHeadRuleListRest::Exact
                            }
                            krs_syntax::RuleListRest::Shared(_) => {
                                krs_ir::ProtocolHeadRuleListRest::Shared
                            }
                            krs_syntax::RuleListRest::Named(rest) => {
                                krs_ir::ProtocolHeadRuleListRest::Term(builder.expand_wire(
                                    KeyedTerm::of(rest),
                                    TermSide::Right,
                                    &mut slots,
                                )?)
                            }
                        };
                        let mut back = Vec::with_capacity(after.back().len());
                        for item in after.back() {
                            back.push(builder.expand_entry_wire(
                                KeyedTerm::of(item),
                                TermSide::Right,
                                &mut slots,
                            )?);
                        }
                        (
                            Some(ledger.define(extra_keys.result_cell())?),
                            Some(krs_ir::wire::WireHeadRuleList { items, rest, back }),
                        )
                    }
                    _ => (None, None),
                };
                update_extras.push(krs_ir::wire::WireHeadRuleExtra::RewriteList {
                    cell: krs_ir::wire::WireHeadRuleCellReference {
                        key: left_key.clone(),
                        name: cell_name.clone(),
                    },
                    result_key,
                    before: before.clone(),
                    after,
                });
            }
            krs_syntax::RuleExtra::HaveMap { .. } => {}
        }
    }
    // The List reading of a bracketed value stands beside the reading the
    // clause took: the computation cell's head, or the cell's list elements.
    let bracket_alternative = match alternative {
        None => None,
        Some(alternative) => {
            let name = alternative.cell().unraw().to_string();
            // The parser attaches an alternative only beside a reading that
            // holds its records: the cell read as a list's elements, which
            // is a `RewriteList` extra of the cell, or the cell read as the
            // computation cell, which is the head. Without either, the
            // alternative's nodes would reach no wire node.
            let records = update_extras
                .iter()
                .find_map(|extra| match extra {
                    krs_ir::wire::WireHeadRuleExtra::RewriteList {
                        cell,
                        before,
                        after,
                        ..
                    } if cell.name == name => {
                        Some(AlternativeRecords::list(before, after.as_ref()))
                    }
                    _ => None,
                })
                .or_else(|| head.as_ref().map(AlternativeRecords::head))
                .ok_or_else(|| {
                    ExpandError::new(
                        expand::UNCONSUMED_PROVENANCE_KEY,
                        alternative.cell().span(),
                        "the List reading of this bracketed cell value stands beside no head and no list reading of the cell, so the descriptor would drop it; this is a bug in KRS, not in the definition",
                    )
                })?;
            Some(bracket_alternative_wire(
                &ledger,
                alternative,
                &records,
                &bindings,
            )?)
        }
    };
    let mut extras = have_extras;
    extras.extend(update_extras);
    let requires = if let Some(condition) = rule.requires() {
        let term = builder.expand_wire(
            KeyedTerm::of(condition.term()),
            TermSide::Requires,
            &mut slots,
        )?;
        Some(krs_ir::wire::WireRuleCondition {
            key: ledger.define(condition.term().keys().payload())?,
            term,
        })
    } else {
        None
    };
    let ensures = ensures_condition(rule.existentials(), &mut builder, &mut slots)?;
    let (existentials, existential_key_functions) = existential_binders(
        rule.existentials(),
        (&facade, &ledger),
        nonce,
        &cfg,
        &mut slots,
    )?;
    let (fresh, fresh_key_functions) = fresh_binders(
        rule.existentials(),
        (&facade, &ledger),
        nonce,
        &cfg,
        &mut slots,
    )?;
    let (evaluation, evaluation_key_function) = super::existentials::evaluation_step(
        clause.attribute(),
        rule.existentials(),
        (&facade, &ledger, nonce, &cfg),
        &mut slots,
    )?;
    let mut key_functions = builder.key_functions;
    key_functions.extend(existential_key_functions);
    key_functions.extend(fresh_key_functions);
    key_functions.extend(evaluation_key_function);
    let tooling_binding_references = builder
        .tooling_binding_references
        .into_iter()
        .filter(|path| {
            !path
                .get_ident()
                .is_some_and(|ident| krs_syntax::is_hidden_binder(&ident.to_string()))
        })
        .collect::<Vec<_>>();
    for existential in rule.existentials().names() {
        binding_checks.push(quote! {
            let #existential = ();
        });
    }
    binding_checks.push(quote! {
        #(let _ = &#tooling_binding_references;)*
    });

    // A claim clause is labelled by its name, which its `#[k::claim(..)]`
    // carries (F7).
    let label = Some(match clause.claim() {
        Some(claim) => krs_ir::DescriptorRuleLabel {
            key: ledger.define(claim.label_key())?,
            name: claim.label().value(),
        },
        // The clause's name, or its `#[k::rule(label = ..)]`.
        None => krs_ir::DescriptorRuleLabel {
            key: ledger.define(
                clause
                    .label_key()
                    .or_else(|| clause.attribute().label_key()),
            )?,
            name: clause.attribute().label().map_or_else(
                || rule.item().sig.ident.unraw().to_string().replace('_', "-"),
                syn::LitStr::value,
            ),
        },
    });
    let (sentence_kind, item_kind, claim) = match clause.claim() {
        Some(claim) => (
            krs_ir::SentenceKind::Claim,
            quote!(#facade::ItemKind::Claim),
            Some(krs_ir::HeadRuleClaim {
                modality_key: ledger.define(claim.modality_key())?,
                modality: match claim.modality() {
                    krs_syntax::ClaimModality::AllPaths => krs_ir::ClaimModality::AllPaths,
                    krs_syntax::ClaimModality::OnePath => krs_ir::ClaimModality::OnePath,
                },
                circularity_key: claim
                    .circularity()
                    .then(|| ledger.define(claim.circularity_key()))
                    .transpose()?,
                trusted_key: claim
                    .trusted()
                    .then(|| ledger.define(claim.trusted_key()))
                    .transpose()?,
            }),
        ),
        None => (
            krs_ir::SentenceKind::Transition,
            quote!(#facade::ItemKind::Rule),
            None,
        ),
    };
    let priority = clause
        .attribute()
        .transition_priority()
        .map(|(_, value)| -> crate::Result<_> {
            Ok(krs_ir::DescriptorRulePriority {
                key: ledger.define(
                    clause
                        .attribute()
                        .owise_key()
                        .or_else(|| clause.attribute().priority_key()),
                )?,
                value,
            })
        })
        .transpose()?;
    let original = rule.item();
    let attrs = &original.attrs;
    let visibility = &original.vis;
    let fn_token = original.sig.fn_token;
    let name_ident = &original.sig.ident;
    let name = name_ident.unraw().to_string();
    // A clause's one sort is its subject's and its result's: the sentence
    // keys the authored sort as both types.
    let result_type_key = ledger.define(rule.result_type_key())?;
    let (head_sort, configuration, computation_cell) = if configuration_owned {
        let computation_cell = match (clause.computation_cell(), &head) {
            (Some(cell), Some(_)) => {
                let keys = clause.computation_cell_keys();
                Some(krs_ir::HeadRuleComputationCell {
                    key: ledger.define(keys.cell())?,
                    name: cell.unraw().to_string(),
                    result_key: keys
                        .result_cell()
                        .map(|key| ledger.define(Some(key)))
                        .transpose()?,
                })
            }
            (None, None) => None,
            _ => {
                return Err(ExpandError::new(
                    expand::MISSING_COMPUTATION_CELL,
                    rule.item().sig.ident.span(),
                    "a configuration-owned rule is missing its computation-cell field",
                ));
            }
        };
        (
            None,
            Some(krs_ir::wire::WireConfigurationReference {
                key: ledger.define(rule.parameter().type_key())?,
                configuration: krs_ir::wire::WireTypeReference {
                    slot: sort_slot,
                    authored_path: sort_spelling,
                },
            }),
            computation_cell,
        )
    } else {
        (
            Some(krs_ir::wire::WireSortReference {
                key: ledger.define(rule.parameter().type_key())?,
                target: krs_ir::wire::WireTypeReference {
                    slot: sort_slot,
                    authored_path: sort_spelling,
                },
            }),
            None,
            None,
        )
    };

    let nondet = clause
        .attribute()
        .nondet()
        .map(|group| -> crate::Result<_> {
            Ok(krs_ir::DescriptorNondetGroup {
                key: ledger.define(clause.attribute().nondet_key())?,
                name: group.unraw().to_string(),
            })
        })
        .transpose()?;
    let wire = krs_ir::wire::WirePayload::HeadRule(Box::new(krs_ir::wire::WireHeadRule {
        sentence_kind,
        label,
        priority,
        nondet,
        // The whole subject record, or the computation item's pattern.
        pattern_key: ledger.define(
            clause
                .pattern_key()
                .or_else(|| rule.parameter().pattern_key()),
        )?,
        result_key: ledger.define(clause.result_key())?,
        head_sort,
        configuration,
        result_type_key,
        computation_cell,
        bindings,
        head,
        requires,
        extras,
        existentials,
        ensures,
        fresh,
        evaluation,
        bracket_alternative,
        claim,
    }));
    ledger.finish()?;
    let wire = serde_json::to_string(&wire).expect("head-rule wire is serializable");
    let slot_tokens = slots.tokens();

    let factory_tokens = DescriptorFactory {
        facade: &facade,
        factory: &factory,
        name: quote!(#name),
        item_kind,
        disambiguator: quote!(""),
        identity_label: "Cargo and Rust macro context form a valid host identity",
        declared_type: quote!(::core::option::Option::None),
        payload: FactoryPayload::wire(wire, slot_tokens),
        cfg: quote!(::core::default::Default::default()),
        attributes: quote!(#(#cfg)*),
        provenance: quote!(#provenance),
        prelude: TokenStream::new(),
    }
    .render();

    let scoped_binders = super::rules::scoped_binder_check(&cfg, imports, clause.bindings());
    Ok(quote! {
        #scoped_binders

        #(#attrs)*
        #visibility #fn_token #name_ident(__krs_symbolic_subject: #sort_alias) -> #sort_alias {
            let _krs_binding_check = || { #(#binding_checks)* };
            let _ = __krs_symbolic_subject;
            ::core::panic!("KRS rule declarations have no runtime implementation")
        }

        #(#cfg)*
        #[doc(hidden)]
        fn #sort_key() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#sort_alias>()
        }
        #(#refinement_functions)*
        #(#key_functions)*

        #factory_tokens
    })
}

struct ReadableStateContext<'a, 'b> {
    builder: &'a mut TermBuilder<'b>,
    slots: &'a mut WireSlots,
    side: krs_syntax::RuleSide,
}

/// The wire form of a readable optional or collection state (KF-023): its
/// terms come from the shared term builder, and its sequence and instance
/// nodes hold their keys.
#[expect(
    clippy::too_many_lines,
    reason = "One match maps every readable state shape to the wire in the expansion order the anchors follow."
)]
fn readable_state_wire(
    state: &krs_syntax::StateTerm,
    context: &mut ReadableStateContext<'_, '_>,
) -> crate::Result<krs_ir::ProtocolRuleStateTerm<krs_ir::wire::WireTerm>> {
    use krs_ir::ProtocolRuleStateTerm as State;
    use krs_syntax::{StateMacroRemainder, StateTerm};
    let ledger = context.builder.ledger;
    let term_side = match context.side {
        krs_syntax::RuleSide::Left => TermSide::Left,
        krs_syntax::RuleSide::Right => TermSide::Right,
    };
    Ok(match state {
        StateTerm::Present(inner) => State::Present {
            value: Box::new(readable_state_wire(inner, context)?),
        },
        StateTerm::Absent(_) => State::Absent,
        StateTerm::Term(term) | StateTerm::Group(term) => State::Term(
            context
                .builder
                .expand_wire(KeyedTerm::of(term), term_side, context.slots)?,
        ),
        StateTerm::KSequence(sequence) => {
            // Every `[..]` has its payload key: an empty one is anchored at
            // its brackets.
            let payload_key = ledger.define(sequence.payload_key())?;
            let mut items = Vec::new();
            for item in sequence.items() {
                let key = ledger.define(item.keys().payload())?;
                items.push(krs_ir::ProtocolRuleKSequenceItem {
                    key,
                    value: context.builder.expand_wire(
                        KeyedTerm::of(item),
                        term_side,
                        context.slots,
                    )?,
                });
            }
            let tail = match sequence.tail() {
                StateMacroRemainder::Anonymous(_) => krs_ir::ProtocolRuleFrame::Anonymous {
                    key: ledger.define(sequence.tail_key())?,
                },
                _ => krs_ir::ProtocolRuleFrame::Exact,
            };
            State::KSequence(krs_ir::ProtocolRuleKSequence {
                payload_key,
                dot_k_key: None,
                notation: krs_ir::DescriptorKSequenceNotation::Comma,
                items,
                tail,
            })
        }
        StateTerm::Map(map) => {
            return Err(ExpandError::new_spanned(
                expand::CELL_COLLECTION_PLACEMENT,
                map.tokens(),
                "a readable collection instance holds terms and `[..]` sequences; write a map child with `cells!`",
            ));
        }
        StateTerm::Instances(list) => {
            let instance = |item: &krs_syntax::InstanceItem,
                            context: &mut ReadableStateContext<'_, '_>|
             -> crate::Result<
                krs_ir::ProtocolRuleInstance<krs_ir::wire::WireTerm>,
            > {
                let key = ledger.define(item.key())?;
                let mut fields = Vec::new();
                for field in item.fields() {
                    let key = ledger.define(field.name_key())?;
                    fields.push(krs_ir::ProtocolRuleInstanceField {
                        key,
                        field: field.name().to_string(),
                        value: readable_state_wire(field.value(), context)?,
                    });
                }
                Ok(krs_ir::ProtocolRuleInstance {
                    key,
                    label: item.label().map(ToString::to_string),
                    fields,
                    rest: super::state_rules::instance_rest(item.rest()),
                })
            };
            let front = list
                .front()
                .iter()
                .map(|item| instance(item, context))
                .collect::<crate::Result<Vec<_>>>()?;
            let rest = match list.rest() {
                StateMacroRemainder::Exact => krs_ir::ProtocolRuleFrame::Exact,
                _ => krs_ir::ProtocolRuleFrame::Anonymous {
                    key: ledger.define(list.rest_key())?,
                },
            };
            let back = list
                .back()
                .iter()
                .map(|item| instance(item, context))
                .collect::<crate::Result<Vec<_>>>()?;
            State::Instances(krs_ir::ProtocolRuleInstances {
                delimiter: match list.delimiter() {
                    krs_syntax::InstanceListDelimiter::Brace => krs_ir::InstanceDelimiter::Brace,
                    krs_syntax::InstanceListDelimiter::Bracket => {
                        krs_ir::InstanceDelimiter::Bracket
                    }
                },
                front,
                rest,
                back,
            })
        }
    })
}

/// The records a bracket alternative's instances take their children from:
/// the terms of the reading the clause took, before and after the rest, on
/// each side.
struct AlternativeRecords<'t> {
    subject: (
        Vec<&'t krs_ir::wire::WireTerm>,
        Vec<&'t krs_ir::wire::WireTerm>,
    ),
    result: (
        Vec<&'t krs_ir::wire::WireTerm>,
        Vec<&'t krs_ir::wire::WireTerm>,
    ),
}

impl<'t> AlternativeRecords<'t> {
    /// A computation-cell head's items and result, all before its rest.
    fn head(head: &'t krs_ir::wire::WireHeadRuleHead) -> Self {
        let result = match &head.result {
            Some(krs_ir::ProtocolHeadRuleResult::Replace(term)) => vec![term],
            Some(krs_ir::ProtocolHeadRuleResult::Splice(splice)) => splice.terms().collect(),
            Some(krs_ir::ProtocolHeadRuleResult::Erase) | None => Vec::new(),
        };
        Self {
            subject: (head.items.iter().collect(), Vec::new()),
            result: (result, Vec::new()),
        }
    }

    /// A list cell's elements before and after its rest.
    fn list(
        before: &'t krs_ir::wire::WireHeadRuleList,
        after: Option<&'t krs_ir::wire::WireHeadRuleList>,
    ) -> Self {
        let (result_front, result_back) = after.map_or_else(
            || (Vec::new(), Vec::new()),
            |after| (after.items.iter().collect(), after.back.iter().collect()),
        );
        Self {
            subject: (before.items.iter().collect(), before.back.iter().collect()),
            result: (result_front, result_back),
        }
    }
}

/// The wire form of a clause's List-collection reading (KF-023): the cell's
/// instance lists, keyed after every other extra as the parser anchors them,
/// whose children are the already-expanded terms of the reading the clause
/// took, the computation cell's head or the cell's list elements.
fn bracket_alternative_wire(
    ledger: &KeyLedger<'_>,
    alternative: &krs_syntax::BracketAlternative,
    records: &AlternativeRecords<'_>,
    bindings: &[krs_ir::wire::WireHeadRuleBinding],
) -> crate::Result<krs_ir::wire::WireHeadRuleBracketAlternative> {
    let mismatch = || {
        ExpandError::new(
            expand::CELL_STATE_FAMILY_MISMATCH,
            alternative.cell().span(),
            "the List reading of a bracketed cell value does not match its other reading",
        )
    };
    let children = |terms: &[&krs_ir::wire::WireTerm]| {
        terms
            .iter()
            .map(|term| record_children(term).ok_or_else(mismatch))
            .collect::<crate::Result<Vec<_>>>()
    };
    let subject = (children(&records.subject.0)?, children(&records.subject.1)?);
    let results = (children(&records.result.0)?, children(&records.result.1)?);
    let before =
        alternative_instances(ledger, alternative.before(), subject)?.ok_or_else(mismatch)?;
    let (result_key, after) = match alternative.after() {
        Some(after) => (
            Some(ledger.define(alternative.result_cell_key())?),
            Some(alternative_instances(ledger, after, results)?.ok_or_else(mismatch)?),
        ),
        None => (None, None),
    };
    let bindings = alternative
        .bindings()
        .iter()
        .map(|binding| {
            bindings
                .iter()
                .find(|candidate| binding.unraw() == candidate.name)
                .cloned()
                .ok_or_else(mismatch)
        })
        .collect::<crate::Result<Vec<_>>>()?;
    Ok(krs_ir::wire::WireHeadRuleBracketAlternative {
        bindings,
        extra: krs_ir::wire::WireHeadRuleExtra::RewriteState {
            cell: krs_ir::wire::WireHeadRuleCellReference {
                key: ledger.define(alternative.cell_key())?,
                name: alternative.cell().unraw().to_string(),
            },
            result_key,
            before,
            after,
        },
    })
}

/// The named children of a record root, under its `label @` if any.
fn record_children(term: &krs_ir::wire::WireTerm) -> Option<Vec<krs_ir::wire::WireTerm>> {
    match term {
        krs_ir::Term::As { pattern, .. } => record_children(pattern),
        krs_ir::Term::Application { arguments, .. } => match arguments {
            krs_ir::Arguments::Named(arguments) => Some(
                arguments
                    .iter()
                    .map(|argument| (*argument.value).clone())
                    .collect(),
            ),
            krs_ir::Arguments::Positional(arguments) if arguments.is_empty() => Some(Vec::new()),
            krs_ir::Arguments::Positional(_) => None,
        },
        _ => None,
    }
}

/// One side's instance list of a bracket alternative, whose records before
/// and after its rest take their children from `records` in order; `None`
/// when the list's shape does not match the records.
fn alternative_instances(
    ledger: &KeyLedger<'_>,
    state: &krs_syntax::StateTerm,
    records: (
        Vec<Vec<krs_ir::wire::WireTerm>>,
        Vec<Vec<krs_ir::wire::WireTerm>>,
    ),
) -> crate::Result<Option<krs_ir::ProtocolRuleStateTerm<krs_ir::wire::WireTerm>>> {
    use krs_syntax::{StateMacroRemainder, StateTerm};
    let StateTerm::Instances(list) = state else {
        return Ok(None);
    };
    let (front_records, back_records) = records;
    if list.front().len() != front_records.len()
        || list.back().len() != back_records.len()
        || list
            .front()
            .iter()
            .zip(&front_records)
            .chain(list.back().iter().zip(&back_records))
            .any(|(item, children)| item.fields().len() != children.len())
    {
        return Ok(None);
    }
    let instances = |items: &[krs_syntax::InstanceItem],
                     records: Vec<Vec<krs_ir::wire::WireTerm>>| {
        items
            .iter()
            .zip(records)
            .map(|(item, children)| {
                let fields = item
                    .fields()
                    .iter()
                    .zip(children)
                    .map(|(field, value)| {
                        Ok(krs_ir::ProtocolRuleInstanceField {
                            key: ledger.define(field.name_key())?,
                            field: field.name().to_string(),
                            value: krs_ir::ProtocolRuleStateTerm::Term(value),
                        })
                    })
                    .collect::<crate::Result<_>>()?;
                Ok(krs_ir::ProtocolRuleInstance {
                    key: ledger.define(item.key())?,
                    label: item.label().map(ToString::to_string),
                    fields,
                    rest: super::state_rules::instance_rest(item.rest()),
                })
            })
            .collect::<crate::Result<Vec<_>>>()
    };
    let front = instances(list.front(), front_records)?;
    let back = instances(list.back(), back_records)?;
    let rest = match list.rest() {
        StateMacroRemainder::Exact => krs_ir::ProtocolRuleFrame::Exact,
        _ => krs_ir::ProtocolRuleFrame::Anonymous {
            key: ledger.define(list.rest_key())?,
        },
    };
    Ok(Some(krs_ir::ProtocolRuleStateTerm::Instances(
        krs_ir::ProtocolRuleInstances {
            delimiter: krs_ir::InstanceDelimiter::Bracket,
            front,
            rest,
            back,
        },
    )))
}
