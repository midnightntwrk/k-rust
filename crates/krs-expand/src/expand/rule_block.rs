//! Readable rule blocks: `rules!`.

use krs_syntax::{ProvenanceRole, TokenRange, parse_rule_block};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::ext::IdentExt;
use syn::{Ident, Path};

use super::nonce::expansion_nonce;
use super::terms::{TermBuilder, TermSide, WireSlots};
use super::tokens::{call_site_cfg_attributes, call_site_path, sort_type_tokens, spelling};
use crate::environment::MacroEnvironment;
use crate::provenance::host_provenance_static;

/// Expands a readable block into independent ordinary rule declarations.
pub(crate) fn rules(env: &dyn MacroEnvironment, input: TokenStream) -> syn::Result<TokenStream> {
    let block = parse_rule_block(input)?;
    let enum_owner = block.imports().first().map(krs_syntax::RuleImport::owner);
    let enum_variant = block
        .imports()
        .first()
        .and_then(krs_syntax::RuleImport::variant);
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
            enum_owner,
            enum_variant,
            block.is_configuration(),
        )?);
    }
    Ok(quote! {
        #(#import_checks)*
        #(#clauses)*
    })
}

#[allow(clippy::too_many_lines)]
fn expand_head_rule(
    env: &dyn MacroEnvironment,
    clause: &krs_syntax::RuleClause,
    enum_owner: Option<&Path>,
    enum_variant: Option<&Ident>,
    configuration_owned: bool,
) -> syn::Result<TokenStream> {
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
    anchors.extend(clause.attribute().provenance()?);
    let fallback = TokenRange::for_tokens(rule.item())?;
    let provenance = host_provenance_static(env, &facade, fallback, &anchors);
    let nonce = expansion_nonce(env, "head_rule", &rule.item().sig.ident, fallback);
    let factory = format_ident!("__krs_head_rule_descriptor_{nonce:016x}");
    let sort_key = format_ident!("__krs_head_rule_sort_{nonce:016x}");
    let cfg = call_site_cfg_attributes(&rule.item().attrs)?;
    let sort_path = call_site_path(rule.parameter().term_sort.sort())?;
    let sort_type = sort_type_tokens(&sort_path, rule.parameter().term_sort.is_dynamic());
    let sort_spelling = rule.parameter().term_sort.sort_spelling();
    let mut slots = WireSlots::new(&facade);
    let sort_slot = slots.type_slot(quote!(#facade::HostTypeKey(#sort_key)));
    let binding_idents = clause.bindings().to_vec();
    let mut builder = TermBuilder::new(&facade, nonce, &cfg, &binding_idents)
        .with_enum_import(enum_owner, enum_variant)
        .with_lexical_rule_head(enum_owner.is_none());
    let mut refinement_functions = Vec::new();
    let mut bindings = Vec::new();
    let mut binding_checks = Vec::new();
    for binding in clause.bindings() {
        let name = binding.unraw().to_string();
        binding_checks.push(quote! {
            let #binding = ();
        });
        let refinement = if let Some((ordinal, narrowing)) = clause
            .narrowings()
            .iter()
            .enumerate()
            .find(|(_, narrowing)| narrowing.binding().unraw() == binding.unraw())
        {
            let ordinal = u32::try_from(ordinal)
                .map_err(|_| syn::Error::new(binding.span(), "too many rule refinements"))?;
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

    let subject = builder.expand_wire(rule.subject_tree(), TermSide::Left, &mut slots)?;

    let mut have_ordinal = 0_u32;
    let mut update_ordinal = 0_u32;
    let mut have_extras = Vec::new();
    let mut rewrite_befores = Vec::new();
    for extra in clause.extras() {
        match extra {
            krs_syntax::RuleExtra::HaveMap { cell, key, value } => {
                let cell_name = cell.unraw().to_string();
                let value_binding = value.unraw().to_string();
                let key = builder.expand_wire(key.tree(), TermSide::Left, &mut slots)?;
                let ordinal = have_ordinal;
                have_ordinal = have_ordinal
                    .checked_add(1)
                    .ok_or_else(|| syn::Error::new(cell.span(), "too many readable cell reads"))?;
                have_extras.push(krs_ir::wire::WireHeadRuleExtra::HaveMap {
                    cell: krs_ir::wire::WireHeadRuleCellReference {
                        key: rule_left_cells_field_role.key(ordinal),
                        name: cell_name,
                    },
                    key,
                    value_binding,
                });
            }
            krs_syntax::RuleExtra::RewriteCell {
                cell, before_tree, ..
            } => {
                let before = builder.expand_wire(before_tree, TermSide::Left, &mut slots)?;
                let ordinal = have_ordinal;
                have_ordinal = have_ordinal
                    .checked_add(1)
                    .ok_or_else(|| syn::Error::new(cell.span(), "too many readable cell reads"))?;
                rewrite_befores.push((cell.unraw().to_string(), ordinal, before));
            }
            krs_syntax::RuleExtra::UpdateMap { .. } => {}
        }
    }

    builder.reset_side();
    let result = match clause.head_result() {
        krs_syntax::RuleHeadResult::Replace(term) => {
            let term = builder.expand_wire(term.tree(), TermSide::Right, &mut slots)?;
            krs_ir::wire::WireHeadRuleResult::Replace(term)
        }
        krs_syntax::RuleHeadResult::Splice { items, .. } => {
            let items = items
                .iter()
                .map(|item| builder.expand_wire(item.tree(), TermSide::Right, &mut slots))
                .collect::<Result<Vec<_>, _>>()?;
            krs_ir::wire::WireHeadRuleResult::Splice(items)
        }
        krs_syntax::RuleHeadResult::Erase(_) => krs_ir::wire::WireHeadRuleResult::Erase,
    };
    let mut update_extras = Vec::new();
    let mut rewrite_index = 0_usize;
    for extra in clause.extras() {
        match extra {
            krs_syntax::RuleExtra::UpdateMap { cell, base, update } => {
                let cell_name = cell.unraw().to_string();
                let base_binding = base.unraw().to_string();
                let update = builder.expand_wire(update.tree(), TermSide::Right, &mut slots)?;
                let ordinal = update_ordinal;
                update_ordinal = update_ordinal.checked_add(1).ok_or_else(|| {
                    syn::Error::new(cell.span(), "too many readable cell updates")
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
                let after = builder.expand_wire(after.tree(), TermSide::Right, &mut slots)?;
                let right_ordinal = update_ordinal;
                update_ordinal = update_ordinal.checked_add(1).ok_or_else(|| {
                    syn::Error::new(cell.span(), "too many readable cell updates")
                })?;
                update_extras.push(krs_ir::wire::WireHeadRuleExtra::RewriteCell {
                    cell: krs_ir::wire::WireHeadRuleCellReference {
                        key: rule_left_cells_field_role.key(*left_ordinal),
                        name: cell_name.clone(),
                    },
                    result_key: rule_right_cells_field_role.key(right_ordinal),
                    before: before.clone(),
                    after,
                });
            }
            krs_syntax::RuleExtra::HaveMap { .. } => {}
        }
    }
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
    let key_functions = builder.key_functions;
    let tooling_binding_references = builder.tooling_binding_references;
    binding_checks.push(quote! {
        #(let _ = &#tooling_binding_references;)*
    });

    let label = Some(krs_ir::DescriptorRuleLabel {
        key: rule_label_role.key(0),
        name: clause.attribute().label().map_or_else(
            || rule.item().sig.ident.unraw().to_string().replace('_', "-"),
            syn::LitStr::value,
        ),
    });
    let priority = clause
        .attribute()
        .is_owise()
        .then(|| krs_ir::DescriptorRulePriority {
            key: ProvenanceRole::RuleOwise.key(0),
            value: 200,
        });
    let original = rule.item();
    let attrs = &original.attrs;
    let visibility = &original.vis;
    let fn_token = original.sig.fn_token;
    let name_ident = &original.sig.ident;
    let name = name_ident.unraw().to_string();
    let parameter_type = rule.parameter().term_sort.ty();
    let (head_sort, configuration, computation_cell_name) = if configuration_owned {
        let computation_cell = clause.computation_cell().ok_or_else(|| {
            syn::Error::new(
                rule.item().sig.ident.span(),
                "a configuration-owned rule is missing its computation-cell field",
            )
        })?;
        let computation_cell = computation_cell.unraw().to_string();
        (
            None,
            Some(krs_ir::wire::WireConfigurationReference {
                key: rule_type_role.key(0),
                configuration: krs_ir::wire::WireTypeReference {
                    slot: sort_slot,
                    authored_path: sort_spelling,
                },
            }),
            Some(computation_cell),
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

    let wire = krs_ir::wire::WirePayload::HeadRule(Box::new(krs_ir::wire::WireHeadRule {
        sentence_kind: krs_ir::SentenceKind::Transition,
        label,
        priority,
        pattern_key: rule_pattern_role.key(0),
        result_key: rule_result_role.key(0),
        head_sort,
        configuration,
        computation_cell_name,
        bindings,
        subject,
        result,
        requires,
        extras,
    }));
    let wire = serde_json::to_string(&wire).expect("head-rule wire is serializable");
    let slot_tokens = slots.tokens();

    Ok(quote! {
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

        #(#cfg)*
        #[doc(hidden)]
        fn #factory() -> #facade::HostDescriptor {
            #facade::HostDescriptor {
                protocol_version: #facade::SchemaVersion::CURRENT,
                id: #facade::HostItemId::from_macro_context(
                    env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"), env!("CARGO_MANIFEST_DIR"),
                    module_path!(), #name, #facade::ItemKind::Rule, "",
                ).expect("Cargo and Rust macro context form a valid host identity"),
                declared_type: ::core::option::Option::None,
                payload: #facade::__krs_host_payload(#wire, #slot_tokens),
                cfg: ::core::default::Default::default(),
                provenance: #provenance,
            }
        }
        #(#cfg)*
        #facade::__register_host_descriptor!(#factory);
    })
}
