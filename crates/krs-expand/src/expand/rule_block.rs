//! Readable rule blocks: `rules!`.

use krs_syntax::{ProvenanceRole, TokenRange, parse_rule_block};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::ext::IdentExt;
use syn::{Ident, Path};

use super::nonce::expansion_nonce;
use super::rules::{rule_label_tokens, rule_owise_tokens};
use super::terms::{TermBuilder, TermSide};
use super::tokens::{
    call_site_cfg_attributes, call_site_path, host_sort_reference, sort_type_tokens, spelling,
};
use crate::environment::MacroEnvironment;
use crate::provenance::host_provenance;

/// Expands a readable block into independent ordinary rule declarations.
pub(crate) fn rules(env: &dyn MacroEnvironment, input: TokenStream) -> syn::Result<TokenStream> {
    let block = parse_rule_block(input).map_err(krs_syntax::SyntaxError::into_syn_error)?;
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
    let mut anchors = clause
        .provenance()
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    anchors.extend(
        clause
            .attribute()
            .provenance()
            .map_err(krs_syntax::SyntaxError::into_syn_error)?,
    );
    let fallback =
        TokenRange::for_tokens(rule.item()).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let provenance = host_provenance(env, &facade, fallback, &anchors)?;
    let nonce = expansion_nonce(env, "head_rule", &rule.item().sig.ident, fallback);
    let factory = format_ident!("__krs_head_rule_descriptor_{nonce:016x}");
    let sort_key = format_ident!("__krs_head_rule_sort_{nonce:016x}");
    let cfg = call_site_cfg_attributes(&rule.item().attrs)?;
    let sort_path = call_site_path(rule.parameter().term_sort.sort())?;
    let sort_type = sort_type_tokens(&sort_path, rule.parameter().term_sort.is_dynamic());
    let sort_spelling = rule.parameter().term_sort.sort_spelling();
    let head_sort = host_sort_reference(
        &facade,
        ProvenanceRole::RuleType,
        0,
        &sort_key,
        &sort_spelling,
    );
    let binding_idents = clause.bindings().to_vec();
    let mut builder = TermBuilder::new(&facade, nonce, &cfg, &binding_idents)
        .with_enum_import(enum_owner, enum_variant)
        .with_lexical_rule_head(enum_owner.is_none());
    let subject = builder.expand(rule.subject_tree(), TermSide::Left)?;

    let mut have_ordinal = 0_u32;
    let mut update_ordinal = 0_u32;
    let mut have_extras = Vec::new();
    let mut rewrite_befores = Vec::new();
    for extra in clause.extras() {
        match extra {
            krs_syntax::RuleExtra::HaveMap { cell, key, value } => {
                let cell_name = cell.unraw().to_string();
                let value_binding = value.unraw().to_string();
                let key = builder.expand(key.tree(), TermSide::Left)?;
                let ordinal = have_ordinal;
                have_ordinal = have_ordinal
                    .checked_add(1)
                    .ok_or_else(|| syn::Error::new(cell.span(), "too many readable cell reads"))?;
                have_extras.push(quote! {
                    #facade::ProtocolHeadRuleExtra::HaveMap {
                        cell: #facade::HostHeadRuleCellReference {
                            key: #facade::ProvenanceKey::new(#rule_left_cells_field_role, #ordinal).unwrap(),
                            name: #cell_name.to_owned(),
                        },
                        key: #key,
                        value_binding: #value_binding.to_owned(),
                    }
                });
            }
            krs_syntax::RuleExtra::RewriteCell {
                cell, before_tree, ..
            } => {
                let before = builder.expand(before_tree, TermSide::Left)?;
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
            let term = builder.expand(term.tree(), TermSide::Right)?;
            quote!(#facade::ProtocolHeadRuleResult::Replace(#term))
        }
        krs_syntax::RuleHeadResult::Splice { items, .. } => {
            let items = items
                .iter()
                .map(|item| builder.expand(item.tree(), TermSide::Right))
                .collect::<Result<Vec<_>, _>>()?;
            quote!(#facade::ProtocolHeadRuleResult::Splice(::std::vec![#(#items),*]))
        }
        krs_syntax::RuleHeadResult::Erase(_) => {
            quote!(#facade::ProtocolHeadRuleResult::Erase)
        }
    };
    let mut update_extras = Vec::new();
    let mut rewrite_index = 0_usize;
    for extra in clause.extras() {
        match extra {
            krs_syntax::RuleExtra::UpdateMap { cell, base, update } => {
                let cell_name = cell.unraw().to_string();
                let base_binding = base.unraw().to_string();
                let update = builder.expand(update.tree(), TermSide::Right)?;
                let ordinal = update_ordinal;
                update_ordinal = update_ordinal.checked_add(1).ok_or_else(|| {
                    syn::Error::new(cell.span(), "too many readable cell updates")
                })?;
                update_extras.push(quote! {
                    #facade::ProtocolHeadRuleExtra::UpdateMap {
                        cell: #facade::HostHeadRuleCellReference {
                            key: #facade::ProvenanceKey::new(#rule_right_cells_field_role, #ordinal).unwrap(),
                            name: #cell_name.to_owned(),
                        },
                        base_binding: #base_binding.to_owned(),
                        update: #update,
                    }
                });
            }
            krs_syntax::RuleExtra::RewriteCell { cell, after, .. } => {
                let (cell_name, left_ordinal, before) = &rewrite_befores[rewrite_index];
                rewrite_index += 1;
                debug_assert_eq!(cell_name, &cell.unraw().to_string());
                let after = builder.expand(after.tree(), TermSide::Right)?;
                let right_ordinal = update_ordinal;
                update_ordinal = update_ordinal.checked_add(1).ok_or_else(|| {
                    syn::Error::new(cell.span(), "too many readable cell updates")
                })?;
                update_extras.push(quote! {
                    #facade::ProtocolHeadRuleExtra::RewriteCell {
                        cell: #facade::HostHeadRuleCellReference {
                            key: #facade::ProvenanceKey::new(#rule_left_cells_field_role, #left_ordinal).unwrap(),
                            name: #cell_name.to_owned(),
                        },
                        result_key: #facade::ProvenanceKey::new(#rule_right_cells_field_role, #right_ordinal).unwrap(),
                        before: #before,
                        after: #after,
                    }
                });
            }
            krs_syntax::RuleExtra::HaveMap { .. } => {}
        }
    }
    let mut extras = have_extras;
    extras.extend(update_extras);
    builder.reset_side();
    let requires = if let Some(condition) = rule.requires() {
        let term = builder.expand(condition.term().tree(), TermSide::Requires)?;
        quote! {
            ::core::option::Option::Some(#facade::HostRuleCondition {
                key: #facade::ProvenanceKey::new(#rule_requires_role, 0).unwrap(),
                term: #term,
            })
        }
    } else {
        quote!(::core::option::Option::None)
    };
    let key_functions = builder.key_functions;
    let tooling_binding_references = builder.tooling_binding_references;

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
            let reference = host_sort_reference(
                &facade,
                ProvenanceRole::RuleBindingType,
                ordinal,
                &key_fn,
                &authored,
            );
            quote!(::core::option::Option::Some(#reference))
        } else {
            quote!(::core::option::Option::None)
        };
        bindings.push(quote! {
            #facade::ProtocolHeadRuleBinding {
                name: #name.to_owned(),
                refinement: #refinement,
            }
        });
    }
    binding_checks.push(quote! {
        #(let _ = &#tooling_binding_references;)*
    });
    let label = clause.attribute().label().map_or_else(
        || {
            let name = rule.item().sig.ident.unraw().to_string().replace('_', "-");
            quote! {
                ::core::option::Option::Some(#facade::DescriptorRuleLabel {
                    key: #facade::ProvenanceKey::new(#rule_label_role, 0)
                        .expect("KRS parser roles are nonempty"),
                    name: #name.to_owned(),
                })
            }
        },
        |_| rule_label_tokens(&facade, clause.attribute()),
    );
    let priority = rule_owise_tokens(&facade, clause.attribute());
    let original = rule.item();
    let attrs = &original.attrs;
    let visibility = &original.vis;
    let fn_token = original.sig.fn_token;
    let name_ident = &original.sig.ident;
    let name = name_ident.unraw().to_string();
    let parameter_type = rule.parameter().term_sort.ty();
    let header = if configuration_owned {
        let computation_cell = clause.computation_cell().ok_or_else(|| {
            syn::Error::new(
                rule.item().sig.ident.span(),
                "a configuration-owned rule is missing its computation-cell field",
            )
        })?;
        let computation_cell = computation_cell.unraw().to_string();
        quote! {
            head_sort: ::core::option::Option::None,
            configuration: ::core::option::Option::Some(#facade::HostConfigurationReference {
                key: #facade::ProvenanceKey::new(#rule_type_role, 0).unwrap(),
                configuration: #facade::HostTypeReference {
                    key: #facade::HostTypeKey(#sort_key),
                    authored_path: #sort_spelling.to_owned(),
                },
            }),
            computation_cell_name: ::core::option::Option::Some(#computation_cell.to_owned()),
        }
    } else {
        quote! {
            head_sort: ::core::option::Option::Some(#head_sort),
            configuration: ::core::option::Option::None,
            computation_cell_name: ::core::option::Option::None,
        }
    };

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
                payload: #facade::HostDescriptorPayload::HeadRule(::std::boxed::Box::new(
                    #facade::HostHeadRule {
                        sentence_kind: #facade::SentenceKind::Transition,
                        label: #label,
                        priority: #priority,
                        pattern_key: #facade::ProvenanceKey::new(#rule_pattern_role, 0).unwrap(),
                        result_key: #facade::ProvenanceKey::new(#rule_result_role, 0).unwrap(),
                        #header
                        bindings: ::std::vec![#(#bindings),*],
                        subject: #subject,
                        result: #result,
                        requires: #requires,
                        extras: ::std::vec![#(#extras),*],
                    }
                )),
                cfg: ::core::default::Default::default(),
                provenance: #provenance,
            }
        }
        #(#cfg)*
        #facade::__register_host_descriptor!(#factory);
    })
}
