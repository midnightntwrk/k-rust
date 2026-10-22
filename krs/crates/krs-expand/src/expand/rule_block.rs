//! Readable rule blocks: `rules!`.

use crate::ExpandError;
use krs_diagnostic::codes::expand;
use krs_syntax::KrsSyntax;
use krs_syntax::{ProvenanceRole, TokenRange};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::ext::IdentExt;

use super::existentials::{ensures_condition, existential_binders, fresh_binders};
use super::factory::{DescriptorFactory, FactoryPayload};
use super::nonce::expansion_nonce;
use super::terms::{TermBuilder, TermSide, WireSlots};
use super::tokens::{call_site_cfg_attributes, call_site_path, sort_type_tokens, spelling};
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
    let enum_import_item = block.imports().first().map(krs_syntax::RuleImport::item);
    let import_checks = block.imports().iter().map(|import| {
        let item = import.item();
        quote! {
            const _: () = {
                #[allow(unused_imports)]
                #item
            };
        }
    });
    let mut clauses = Vec::with_capacity(block.clauses().len());
    for clause in block.clauses() {
        clauses.push(expand_head_rule(
            env,
            clause,
            enum_import_item,
            block.is_configuration(),
        )?);
    }
    Ok(quote! {
        #(#import_checks)*
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
    enum_import_item: Option<&syn::ItemUse>,
    configuration_owned: bool,
) -> crate::Result<TokenStream> {
    let rule_left_cells_field_role = ProvenanceRole::RuleLeftCellsField;
    let rule_right_cells_field_role = ProvenanceRole::RuleRightCellsField;
    let rule_requires_role = ProvenanceRole::RuleRequires;
    let rule_label_role = ProvenanceRole::RuleLabel;
    let rule_type_role = ProvenanceRole::RuleType;
    let rule_pattern_role = ProvenanceRole::RulePattern;
    let rule_result_role = ProvenanceRole::RuleResult;
    let facade = env.facade_path()?;
    let rule = clause.rule();
    let mut anchors = clause.provenance()?;
    anchors.extend(clause.attribute_provenance()?);
    let fallback = TokenRange::for_tokens(rule.item())?;
    let provenance = host_provenance(env, &facade, fallback, &anchors);
    let nonce = expansion_nonce(env, "head_rule", &rule.item().sig.ident, fallback);
    let factory = format_ident!("__krs_head_rule_descriptor_{nonce:016x}");
    let sort_key = format_ident!("__krs_head_rule_sort_{nonce:016x}");
    let cfg = call_site_cfg_attributes(&rule.item().attrs)?;
    let sort_path = call_site_path(rule.parameter().term_sort.sort())?;
    let sort_type = sort_type_tokens(&facade, &sort_path, rule.parameter().term_sort.is_dynamic());
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
    let mut builder = TermBuilder::new(&facade, nonce, &cfg, &binding_idents)
        .with_enum_import_item(enum_import_item)
        .with_lexical_rule_head(enum_import_item.is_none())
        .with_readable_instances();
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
            let ordinal = u32::try_from(ordinal).map_err(|_| {
                ExpandError::new(
                    expand::DESCRIPTOR_CAPACITY,
                    binding.span(),
                    "too many rule refinements",
                )
            })?;
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
                key: ProvenanceRole::RuleBindingType.key(ordinal),
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
        items.push(builder.expand_wire(rule.subject_tree(), TermSide::Left, &mut slots)?);
    }
    // The computation items after the first are expanded before the other
    // cells, as the parser numbers their anchors.
    for item in clause.head().iter().flat_map(|head| head.following()) {
        items.push(builder.expand_wire(item.tree(), TermSide::Left, &mut slots)?);
    }

    let mut have_ordinal = 0_u32;
    let mut update_ordinal = 0_u32;
    let mut have_extras = Vec::new();
    let mut rewrite_befores = Vec::new();
    let mut state_befores = Vec::new();
    let mut list_befores = Vec::new();
    // Optional and collection states (KF-023) number their sequence and
    // instance keys per side, as the parser numbers their anchors.
    let mut left_states = krs_syntax::ReadableStateCounters::default();
    let mut right_states = krs_syntax::ReadableStateCounters::after_head(clause.head_result());
    for extra in clause.extras() {
        match extra {
            krs_syntax::RuleExtra::HaveMap { cell, entries } => {
                let cell_name = cell.unraw().to_string();
                let entries = entries
                    .iter()
                    .map(|entry| {
                        Ok(krs_ir::wire::WireHeadRuleMapEntry {
                            key: builder.expand_wire(
                                entry.key.tree(),
                                TermSide::Left,
                                &mut slots,
                            )?,
                            value_binding: entry.value.unraw().to_string(),
                        })
                    })
                    .collect::<Result<Vec<_>, ExpandError>>()?;
                let ordinal = have_ordinal;
                have_ordinal = have_ordinal.checked_add(1).ok_or_else(|| {
                    ExpandError::new(
                        expand::DESCRIPTOR_CAPACITY,
                        cell.span(),
                        "too many readable cell reads",
                    )
                })?;
                have_extras.push(krs_ir::wire::WireHeadRuleExtra::HaveMap {
                    cell: krs_ir::wire::WireHeadRuleCellReference {
                        key: rule_left_cells_field_role.key(ordinal),
                        name: cell_name,
                    },
                    entries,
                });
            }
            krs_syntax::RuleExtra::RewriteCell {
                cell, before_tree, ..
            } => {
                let before = builder.expand_wire(before_tree, TermSide::Left, &mut slots)?;
                let ordinal = have_ordinal;
                have_ordinal = have_ordinal.checked_add(1).ok_or_else(|| {
                    ExpandError::new(
                        expand::DESCRIPTOR_CAPACITY,
                        cell.span(),
                        "too many readable cell reads",
                    )
                })?;
                rewrite_befores.push((cell.unraw().to_string(), ordinal, before));
            }
            krs_syntax::RuleExtra::RewriteState { cell, before, .. } => {
                let before = readable_state_wire(
                    before,
                    &mut ReadableStateContext {
                        builder: &mut builder,
                        slots: &mut slots,
                        counters: &mut left_states,
                        side: krs_syntax::RuleSide::Left,
                    },
                )?;
                let ordinal = have_ordinal;
                have_ordinal = have_ordinal.checked_add(1).ok_or_else(|| {
                    ExpandError::new(
                        expand::DESCRIPTOR_CAPACITY,
                        cell.span(),
                        "too many readable cell reads",
                    )
                })?;
                state_befores.push((cell.unraw().to_string(), ordinal, before));
            }
            krs_syntax::RuleExtra::RewriteList { cell, before, .. } => {
                let mut items = Vec::with_capacity(before.items().len());
                for item in before.items() {
                    items.push(builder.expand_wire(item.tree(), TermSide::Left, &mut slots)?);
                }
                let rest = match before.rest() {
                    krs_syntax::RuleListRest::Exact => krs_ir::ProtocolHeadRuleListRest::Exact,
                    krs_syntax::RuleListRest::Shared(_) => krs_ir::ProtocolHeadRuleListRest::Shared,
                    krs_syntax::RuleListRest::Named(rest) => {
                        krs_ir::ProtocolHeadRuleListRest::Term(builder.expand_wire(
                            rest.tree(),
                            TermSide::Left,
                            &mut slots,
                        )?)
                    }
                };
                let ordinal = have_ordinal;
                have_ordinal = have_ordinal.checked_add(1).ok_or_else(|| {
                    ExpandError::new(
                        expand::DESCRIPTOR_CAPACITY,
                        cell.span(),
                        "too many readable cell reads",
                    )
                })?;
                list_befores.push((
                    cell.unraw().to_string(),
                    ordinal,
                    krs_ir::wire::WireHeadRuleList { items, rest },
                ));
            }
            krs_syntax::RuleExtra::UpdateMap { .. } => {}
        }
    }

    builder.reset_side();
    let result = match clause.head_result() {
        None => None,
        Some(krs_syntax::RuleHeadResult::Replace(term)) => {
            let term = builder.expand_wire(term.tree(), TermSide::Right, &mut slots)?;
            Some(krs_ir::wire::WireHeadRuleResult::Replace(term))
        }
        Some(krs_syntax::RuleHeadResult::Splice { items, .. }) => {
            let items = items
                .iter()
                .map(|item| builder.expand_wire(item.tree(), TermSide::Right, &mut slots))
                .collect::<Result<Vec<_>, _>>()?;
            Some(krs_ir::wire::WireHeadRuleResult::Splice(items))
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
    for extra in clause.extras() {
        match extra {
            krs_syntax::RuleExtra::RewriteState {
                cell,
                result_cell,
                after,
                ..
            } => {
                let (cell_name, left_ordinal, before) = &state_befores[state_index];
                state_index += 1;
                debug_assert_eq!(cell_name, &cell.unraw().to_string());
                let (result_key, after) = match (result_cell, after) {
                    (Some(result_cell), Some(after)) => {
                        let after = readable_state_wire(
                            after,
                            &mut ReadableStateContext {
                                builder: &mut builder,
                                slots: &mut slots,
                                counters: &mut right_states,
                                side: krs_syntax::RuleSide::Right,
                            },
                        )?;
                        let right_ordinal = update_ordinal;
                        update_ordinal = update_ordinal.checked_add(1).ok_or_else(|| {
                            ExpandError::new(
                                expand::DESCRIPTOR_CAPACITY,
                                result_cell.span(),
                                "too many readable cell updates",
                            )
                        })?;
                        (
                            Some(rule_right_cells_field_role.key(right_ordinal)),
                            Some(after),
                        )
                    }
                    _ => (None, None),
                };
                update_extras.push(krs_ir::wire::WireHeadRuleExtra::RewriteState {
                    cell: krs_ir::wire::WireHeadRuleCellReference {
                        key: rule_left_cells_field_role.key(*left_ordinal),
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
                let update =
                    builder.expand_wire(update.term().tree(), TermSide::Right, &mut slots)?;
                let ordinal = update_ordinal;
                update_ordinal = update_ordinal.checked_add(1).ok_or_else(|| {
                    ExpandError::new(
                        expand::DESCRIPTOR_CAPACITY,
                        cell.span(),
                        "too many readable cell updates",
                    )
                })?;
                update_extras.push(krs_ir::wire::WireHeadRuleExtra::UpdateMap {
                    cell: krs_ir::wire::WireHeadRuleCellReference {
                        key: rule_right_cells_field_role.key(ordinal),
                        name: cell_name,
                    },
                    base_binding,
                    update,
                });
            }
            krs_syntax::RuleExtra::RewriteCell { cell, after, .. } => {
                let (cell_name, left_ordinal, before) = &rewrite_befores[rewrite_index];
                rewrite_index += 1;
                debug_assert_eq!(cell_name, &cell.unraw().to_string());
                // A cell the result leaves out is read only: it has no
                // result term and no result-field key.
                let (result_key, after) = if let Some(after) = after {
                    let after = builder.expand_wire(after.tree(), TermSide::Right, &mut slots)?;
                    let right_ordinal = update_ordinal;
                    update_ordinal = update_ordinal.checked_add(1).ok_or_else(|| {
                        ExpandError::new(
                            expand::DESCRIPTOR_CAPACITY,
                            cell.span(),
                            "too many readable cell updates",
                        )
                    })?;
                    (
                        Some(rule_right_cells_field_role.key(right_ordinal)),
                        Some(after),
                    )
                } else {
                    (None, None)
                };
                update_extras.push(krs_ir::wire::WireHeadRuleExtra::RewriteCell {
                    cell: krs_ir::wire::WireHeadRuleCellReference {
                        key: rule_left_cells_field_role.key(*left_ordinal),
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
                let (cell_name, left_ordinal, before) = &list_befores[list_index];
                list_index += 1;
                debug_assert_eq!(cell_name, &cell.unraw().to_string());
                let (result_key, after) = match (result_cell, after) {
                    (Some(result_cell), Some(after)) => {
                        let mut items = Vec::with_capacity(after.items().len());
                        for item in after.items() {
                            items.push(builder.expand_wire(
                                item.tree(),
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
                                    rest.tree(),
                                    TermSide::Right,
                                    &mut slots,
                                )?)
                            }
                        };
                        let right_ordinal = update_ordinal;
                        update_ordinal = update_ordinal.checked_add(1).ok_or_else(|| {
                            ExpandError::new(
                                expand::DESCRIPTOR_CAPACITY,
                                result_cell.span(),
                                "too many readable cell updates",
                            )
                        })?;
                        (
                            Some(rule_right_cells_field_role.key(right_ordinal)),
                            Some(krs_ir::wire::WireHeadRuleList { items, rest }),
                        )
                    }
                    _ => (None, None),
                };
                update_extras.push(krs_ir::wire::WireHeadRuleExtra::RewriteList {
                    cell: krs_ir::wire::WireHeadRuleCellReference {
                        key: rule_left_cells_field_role.key(*left_ordinal),
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
    let bracket_alternative = match (alternative, &head) {
        (Some(alternative), Some(head)) => Some(bracket_alternative_wire(
            alternative,
            head,
            &bindings,
            &mut BracketCounters {
                left: &mut left_states,
                right: &mut right_states,
                left_cell: have_ordinal,
                right_cell: update_ordinal,
            },
        )?),
        _ => None,
    };
    let mut extras = have_extras;
    extras.extend(update_extras);
    builder.reset_side();
    let requires = if let Some(condition) = rule.requires() {
        let term = builder.expand_wire(condition.term().tree(), TermSide::Requires, &mut slots)?;
        Some(krs_ir::wire::WireRuleCondition {
            key: rule_requires_role.key(0),
            term,
        })
    } else {
        None
    };
    builder.reset_side();
    let ensures = ensures_condition(rule.existentials(), &mut builder, &mut slots)?;
    let (existentials, existential_key_functions) =
        existential_binders(rule.existentials(), &facade, nonce, &cfg, &mut slots)?;
    let (fresh, fresh_key_functions) =
        fresh_binders(rule.existentials(), &facade, nonce, &cfg, &mut slots)?;
    let (evaluation, evaluation_key_function) = super::existentials::evaluation_step(
        clause.attribute(),
        rule.existentials(),
        (&facade, nonce, &cfg),
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
            key: ProvenanceRole::ClaimLabel.key(0),
            name: claim.label().value(),
        },
        None => krs_ir::DescriptorRuleLabel {
            key: rule_label_role.key(0),
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
                modality_key: ProvenanceRole::ClaimModality.key(0),
                modality: match claim.modality() {
                    krs_syntax::ClaimModality::AllPaths => krs_ir::ClaimModality::AllPaths,
                    krs_syntax::ClaimModality::OnePath => krs_ir::ClaimModality::OnePath,
                },
                circularity_key: claim
                    .circularity()
                    .then(|| ProvenanceRole::ClaimCircularity.key(0)),
                trusted_key: claim.trusted().then(|| ProvenanceRole::ClaimTrusted.key(0)),
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
        .map(|(role, value)| krs_ir::DescriptorRulePriority {
            key: role.key(0),
            value,
        });
    let original = rule.item();
    let attrs = &original.attrs;
    let visibility = &original.vis;
    let fn_token = original.sig.fn_token;
    let name_ident = &original.sig.ident;
    let name = name_ident.unraw().to_string();
    let parameter_type = rule.parameter().term_sort.ty();
    let (head_sort, configuration, computation_cell_name) = if configuration_owned {
        let computation_cell = match (clause.computation_cell(), &head) {
            (Some(cell), Some(_)) => Some(cell.unraw().to_string()),
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
                key: rule_type_role.key(0),
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
                key: rule_type_role.key(0),
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
        .map(|group| krs_ir::DescriptorNondetGroup {
            key: ProvenanceRole::RuleNondetGroup.key(0),
            name: group.unraw().to_string(),
        });
    let wire = krs_ir::wire::WirePayload::HeadRule(Box::new(krs_ir::wire::WireHeadRule {
        sentence_kind,
        label,
        priority,
        nondet,
        pattern_key: rule_pattern_role.key(0),
        result_key: rule_result_role.key(0),
        head_sort,
        configuration,
        computation_cell_name,
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

    let scoped_binders = super::rules::scoped_binder_check(
        &cfg,
        enum_import_item
            .map(std::slice::from_ref)
            .unwrap_or_default(),
        clause.bindings(),
    );
    Ok(quote! {
        #scoped_binders

        #(#attrs)*
        #visibility #fn_token #name_ident(__krs_symbolic_subject: #parameter_type) -> #parameter_type {
            let _krs_binding_check = || { #(#binding_checks)* };
            let _ = __krs_symbolic_subject;
            ::core::panic!("KRS rule declarations have no runtime implementation")
        }

        #(#cfg)*
        #[doc(hidden)]
        fn #sort_key() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#sort_type>()
        }
        #(#refinement_functions)*
        #(#key_functions)*

        #factory_tokens
    })
}

struct ReadableStateContext<'a, 'b> {
    builder: &'a mut TermBuilder<'b>,
    slots: &'a mut WireSlots,
    counters: &'a mut krs_syntax::ReadableStateCounters,
    side: krs_syntax::RuleSide,
}

impl ReadableStateContext<'_, '_> {
    fn key(
        role: krs_syntax::RuleRole,
        side: krs_syntax::RuleSide,
        counter: &mut usize,
    ) -> crate::Result<krs_ir::ProvenanceKey> {
        let ordinal = u32::try_from(*counter).map_err(|_| {
            ExpandError::new(
                expand::DESCRIPTOR_CAPACITY,
                proc_macro2::Span::call_site(),
                "too many readable state keys",
            )
        })?;
        *counter += 1;
        Ok(role.on_side(side).key(ordinal))
    }
}

/// The wire form of a readable optional or collection state (KF-023): its
/// terms come from the shared term builder and its sequence and instance keys
/// follow `krs_syntax::ReadableStateCounters`.
#[expect(
    clippy::too_many_lines,
    reason = "One match maps every readable state shape to the wire in the expansion order the anchors follow."
)]
fn readable_state_wire(
    state: &krs_syntax::StateTerm,
    context: &mut ReadableStateContext<'_, '_>,
) -> crate::Result<krs_ir::ProtocolRuleStateTerm<krs_ir::wire::WireTerm>> {
    use krs_ir::ProtocolRuleStateTerm as State;
    use krs_syntax::{RuleRole, StateMacroRemainder, StateTerm};
    let term_side = match context.side {
        krs_syntax::RuleSide::Left => TermSide::Left,
        krs_syntax::RuleSide::Right => TermSide::Right,
    };
    let side = context.side;
    Ok(match state {
        StateTerm::Present(inner) => State::Present {
            value: Box::new(readable_state_wire(inner, context)?),
        },
        StateTerm::Absent(_) => State::Absent,
        StateTerm::Term(term) | StateTerm::Group(term) => State::Term(
            context
                .builder
                .expand_wire(term.tree(), term_side, context.slots)?,
        ),
        StateTerm::KSequence(sequence) => {
            let payload_key = if sequence.items().is_empty()
                && matches!(sequence.tail(), StateMacroRemainder::Exact)
            {
                None
            } else {
                Some(ReadableStateContext::key(
                    RuleRole::KSequencePayload,
                    side,
                    &mut context.counters.k_payload,
                )?)
            };
            let mut items = Vec::new();
            for item in sequence.items() {
                let key = ReadableStateContext::key(
                    RuleRole::KSequenceItem,
                    side,
                    &mut context.counters.k_item,
                )?;
                items.push(krs_ir::ProtocolRuleKSequenceItem {
                    key,
                    value: context
                        .builder
                        .expand_wire(item.tree(), term_side, context.slots)?,
                });
            }
            let tail = match sequence.tail() {
                StateMacroRemainder::Anonymous(_) => krs_ir::ProtocolRuleFrame::Anonymous {
                    key: ReadableStateContext::key(
                        RuleRole::KSequenceTail,
                        side,
                        &mut context.counters.k_tail,
                    )?,
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
            let _ = map;
            return Err(ExpandError::new(
                expand::CELL_COLLECTION_PLACEMENT,
                proc_macro2::Span::call_site(),
                "a readable collection instance holds terms and `[..]` sequences; write a map child with `cells!`",
            ));
        }
        StateTerm::Instances(list) => {
            let instance = |item: &krs_syntax::InstanceItem,
                            context: &mut ReadableStateContext<'_, '_>|
             -> crate::Result<
                krs_ir::ProtocolRuleInstance<krs_ir::wire::WireTerm>,
            > {
                let key = ReadableStateContext::key(
                    RuleRole::CellsInstance,
                    side,
                    &mut context.counters.instance,
                )?;
                let mut fields = Vec::new();
                for field in item.fields() {
                    let key = ReadableStateContext::key(
                        RuleRole::CellsInstanceField,
                        side,
                        &mut context.counters.instance_field,
                    )?;
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
                    key: ReadableStateContext::key(
                        RuleRole::CellsInstancesRest,
                        side,
                        &mut context.counters.instances_rest,
                    )?,
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

/// The counters a bracket alternative continues: the per-side state
/// counters and the next left and right cell-name ordinals after every other
/// extra of the clause.
struct BracketCounters<'a> {
    left: &'a mut krs_syntax::ReadableStateCounters,
    right: &'a mut krs_syntax::ReadableStateCounters,
    left_cell: u32,
    right_cell: u32,
}

/// The wire form of a clause's List-collection reading (KF-023): the cell's
/// instance lists, keyed after every other extra as the parser anchors them,
/// whose children are the head records' already-expanded terms.
fn bracket_alternative_wire(
    alternative: &krs_syntax::BracketAlternative,
    head: &krs_ir::wire::WireHeadRuleHead,
    bindings: &[krs_ir::wire::WireHeadRuleBinding],
    counters: &mut BracketCounters<'_>,
) -> crate::Result<krs_ir::wire::WireHeadRuleBracketAlternative> {
    let mismatch = || {
        ExpandError::new(
            expand::CELL_STATE_FAMILY_MISMATCH,
            alternative.cell().span(),
            "the List reading of a bracketed cell value does not match its computation-cell reading",
        )
    };
    let subject = head
        .items
        .iter()
        .map(|item| record_children(item).ok_or_else(mismatch))
        .collect::<crate::Result<Vec<_>>>()?;
    let results = match &head.result {
        Some(krs_ir::ProtocolHeadRuleResult::Replace(term)) => {
            vec![record_children(term).ok_or_else(mismatch)?]
        }
        Some(krs_ir::ProtocolHeadRuleResult::Splice(terms)) => terms
            .iter()
            .map(|term| record_children(term).ok_or_else(mismatch))
            .collect::<crate::Result<Vec<_>>>()?,
        Some(krs_ir::ProtocolHeadRuleResult::Erase) | None => Vec::new(),
    };
    let before = alternative_instances(
        alternative.before(),
        krs_syntax::RuleSide::Left,
        counters.left,
        subject,
    )
    .ok_or_else(mismatch)?;
    let (result_key, after) = match alternative.after() {
        Some(after) => (
            Some(ProvenanceRole::RuleRightCellsField.key(counters.right_cell)),
            Some(
                alternative_instances(after, krs_syntax::RuleSide::Right, counters.right, results)
                    .ok_or_else(mismatch)?,
            ),
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
                key: ProvenanceRole::RuleLeftCellsField.key(counters.left_cell),
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

/// One side's instance list of a bracket alternative, whose records take
/// their children from `records` in order.
fn alternative_instances(
    state: &krs_syntax::StateTerm,
    side: krs_syntax::RuleSide,
    counters: &mut krs_syntax::ReadableStateCounters,
    records: Vec<Vec<krs_ir::wire::WireTerm>>,
) -> Option<krs_ir::ProtocolRuleStateTerm<krs_ir::wire::WireTerm>> {
    use krs_syntax::{RuleRole, StateMacroRemainder, StateTerm};
    let StateTerm::Instances(list) = state else {
        return None;
    };
    if !list.back().is_empty() || list.front().len() != records.len() {
        return None;
    }
    let key =
        |role: RuleRole, counter: &mut usize| ReadableStateContext::key(role, side, counter).ok();
    let mut front = Vec::with_capacity(records.len());
    for (item, children) in list.front().iter().zip(records) {
        if item.fields().len() != children.len() {
            return None;
        }
        let instance = key(RuleRole::CellsInstance, &mut counters.instance)?;
        let mut fields = Vec::with_capacity(children.len());
        for (field, value) in item.fields().iter().zip(children) {
            fields.push(krs_ir::ProtocolRuleInstanceField {
                key: key(RuleRole::CellsInstanceField, &mut counters.instance_field)?,
                field: field.name().to_string(),
                value: krs_ir::ProtocolRuleStateTerm::Term(value),
            });
        }
        front.push(krs_ir::ProtocolRuleInstance {
            key: instance,
            label: item.label().map(ToString::to_string),
            fields,
            rest: super::state_rules::instance_rest(item.rest()),
        });
    }
    let rest = match list.rest() {
        StateMacroRemainder::Exact => krs_ir::ProtocolRuleFrame::Exact,
        _ => krs_ir::ProtocolRuleFrame::Anonymous {
            key: key(RuleRole::CellsInstancesRest, &mut counters.instances_rest)?,
        },
    };
    Some(krs_ir::ProtocolRuleStateTerm::Instances(
        krs_ir::ProtocolRuleInstances {
            delimiter: krs_ir::InstanceDelimiter::Bracket,
            front,
            rest,
            back: Vec::new(),
        },
    ))
}
