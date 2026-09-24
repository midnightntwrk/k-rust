//! Function-form sentences: `#[k::rule]`, `#[k::equation]`, `#[k::simplification]`, `#[k::alias]`, `#[k::priority]`, and orphan rule helpers.

use krs_syntax::surface::{AttributeMacro, helper_entry};
use krs_syntax::{
    ProvenanceAnchor, ProvenanceRole, TokenRange, parse_alias_attribute, parse_equation_attribute,
    parse_priority_attribute, parse_rule_attribute, parse_rule_item,
    parse_simplification_attribute,
};
use proc_macro2::{Span, TokenStream};
use quote::{ToTokens, format_ident, quote};
use syn::ext::IdentExt;
use syn::{Attribute, FnArg, ItemFn, Pat, Path};

use super::nonce::expansion_nonce;
use super::state_rules::configuration_rule;
use super::terms::{TermBuilder, TermSide};
use super::tokens::{
    call_site_cfg_attributes, call_site_ident, call_site_path, host_sort_reference,
    sort_type_tokens,
};
use crate::environment::MacroEnvironment;
use crate::provenance::host_provenance;

pub(super) fn rule_label_tokens(
    facade: &Path,
    attribute: &krs_syntax::RuleAttribute,
) -> TokenStream {
    let rule_label_role = ProvenanceRole::RuleLabel;
    attribute.label().map_or_else(
        || quote!(::core::option::Option::None),
        |label| {
            let name = label.value();
            quote! {
                ::core::option::Option::Some(#facade::DescriptorRuleLabel {
                    key: #facade::ProvenanceKey::new(#rule_label_role, 0)
                        .expect("KRS parser roles are nonempty"),
                    name: #name.to_owned(),
                })
            }
        },
    )
}

pub(super) fn rule_owise_tokens(
    facade: &Path,
    attribute: &krs_syntax::RuleAttribute,
) -> TokenStream {
    let rule_owise_role = ProvenanceRole::RuleOwise;
    if attribute.is_owise() {
        quote!(::core::option::Option::Some(#facade::DescriptorRulePriority {
            key: #facade::ProvenanceKey::new(#rule_owise_role, 0)
                .expect("KRS parser roles are nonempty"),
            value: 200,
        }))
    } else {
        quote!(::core::option::Option::None)
    }
}

#[allow(clippy::too_many_lines)]
pub(crate) fn rule(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> syn::Result<TokenStream> {
    let attribute =
        parse_rule_attribute(attributes).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let parsed: ItemFn = syn::parse2(item.clone())?;
    let is_cells_rule = parsed.sig.inputs.last().is_some_and(|argument| {
        let FnArg::Typed(argument) = argument else {
            return false;
        };
        let Pat::Macro(pattern) = &*argument.pat else {
            return false;
        };
        pattern
            .mac
            .path
            .segments
            .last()
            .is_some_and(|segment| segment.ident == "cells")
    });
    if is_cells_rule {
        return configuration_rule(env, item, &attribute);
    }
    ordinary_rule(
        env,
        item,
        &attribute,
        krs_ir::SentenceKind::Transition,
        None,
        None,
    )
}

pub(crate) fn equation(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> syn::Result<TokenStream> {
    parse_equation_attribute(attributes).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let attribute = krs_syntax::RuleAttribute::default();
    ordinary_rule(
        env,
        item,
        &attribute,
        krs_ir::SentenceKind::Equation,
        None,
        None,
    )
}

pub(crate) fn simplification(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> syn::Result<TokenStream> {
    let attribute = parse_simplification_attribute(attributes)
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    ordinary_rule(
        env,
        item,
        &krs_syntax::RuleAttribute::default(),
        krs_ir::SentenceKind::Simplification,
        None,
        Some(&attribute),
    )
}

pub(crate) fn alias(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> syn::Result<TokenStream> {
    parse_alias_attribute(attributes).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    if syn::parse2::<ItemFn>(item.clone()).is_ok() {
        return ordinary_rule(
            env,
            item,
            &krs_syntax::RuleAttribute::default(),
            krs_ir::SentenceKind::Alias,
            None,
            None,
        );
    }
    Err(syn::Error::new(
        Span::call_site(),
        "`#[k::alias]` on a production is a constructor helper; place `#[k::constructor(...)]` before it",
    ))
}

pub(crate) fn priority(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> syn::Result<TokenStream> {
    let priority =
        parse_priority_attribute(attributes).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let mut function: ItemFn = syn::parse2(item)?;
    let Some(index) = function
        .attrs
        .iter()
        .position(|attribute| helper_entry(attribute.path()) == Some(AttributeMacro::Equation))
    else {
        return Err(syn::Error::new(
            Span::call_site(),
            "`#[k::priority]` is an equation helper; place it immediately before `#[k::equation]`",
        ));
    };
    function.attrs.remove(index);
    ordinary_rule(
        env,
        function.to_token_stream(),
        &krs_syntax::RuleAttribute::default(),
        krs_ir::SentenceKind::Equation,
        Some(&priority),
        None,
    )
}

#[allow(clippy::too_many_lines)]
fn ordinary_rule(
    env: &dyn MacroEnvironment,
    item: TokenStream,
    attribute: &krs_syntax::RuleAttribute,
    sentence_kind: krs_ir::SentenceKind,
    priority: Option<&krs_syntax::PriorityAttribute>,
    simplification: Option<&krs_syntax::SimplificationAttribute>,
) -> syn::Result<TokenStream> {
    let rule = parse_rule_item(item).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    expand_ordinary_rule(
        env,
        &rule,
        attribute,
        sentence_kind,
        priority,
        simplification,
        None,
        &[],
    )
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn expand_ordinary_rule(
    env: &dyn MacroEnvironment,
    rule: &krs_syntax::RuleItem,
    attribute: &krs_syntax::RuleAttribute,
    sentence_kind: krs_ir::SentenceKind,
    priority: Option<&krs_syntax::PriorityAttribute>,
    simplification: Option<&krs_syntax::SimplificationAttribute>,
    enum_glob: Option<&Path>,
    narrowings: &[krs_syntax::RuleNarrowing],
) -> syn::Result<TokenStream> {
    let rule_requires_role = ProvenanceRole::RuleRequires;
    let equation_priority_role = ProvenanceRole::EquationPriority;
    let simplification_priority_role = ProvenanceRole::SimplificationPriority;
    let simplification_marker_role = ProvenanceRole::SimplificationMarker;
    let rule_pattern_role = ProvenanceRole::RulePattern;
    let rule_result_role = ProvenanceRole::RuleResult;
    let facade = env.facade_path()?;
    let mut anchors = rule
        .full_provenance()
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    anchors.extend(
        attribute
            .provenance()
            .map_err(krs_syntax::SyntaxError::into_syn_error)?,
    );
    if sentence_kind == krs_ir::SentenceKind::Alias {
        anchors.push(ProvenanceAnchor::new(
            ProvenanceRole::AliasClause,
            0,
            TokenRange::for_tokens(&rule.item().sig.ident)
                .map_err(krs_syntax::SyntaxError::into_syn_error)?,
        ));
    }
    if let Some(priority) = priority {
        anchors.extend(
            priority
                .provenance()
                .map_err(krs_syntax::SyntaxError::into_syn_error)?,
        );
    }
    if let Some(simplification) = simplification {
        anchors.push(ProvenanceAnchor::new(
            ProvenanceRole::SimplificationMarker,
            0,
            TokenRange::for_tokens(&rule.item().sig.ident)
                .map_err(krs_syntax::SyntaxError::into_syn_error)?,
        ));
        anchors.extend(
            simplification
                .provenance()
                .map_err(krs_syntax::SyntaxError::into_syn_error)?,
        );
    }
    let fallback = krs_syntax::TokenRange::for_tokens(rule.item())
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let provenance = host_provenance(env, &facade, fallback, &anchors)?;
    let sentence_name = match sentence_kind {
        krs_ir::SentenceKind::Transition => "rule",
        krs_ir::SentenceKind::Equation => "equation",
        krs_ir::SentenceKind::Simplification => "simplification",
        krs_ir::SentenceKind::Alias => "alias",
        krs_ir::SentenceKind::Claim => unreachable!("claims have a separate authoring form"),
    };
    let nonce = expansion_nonce(env, sentence_name, &rule.item().sig.ident, fallback);
    let factory = format_ident!(
        "__krs_rule_descriptor_{nonce:016x}",
        span = Span::call_site()
    );
    let cfg = call_site_cfg_attributes(&rule.item().attrs)?;
    let parameter_key = format_ident!("__krs_rule_subject_sort_{nonce:016x}");
    let result_key = format_ident!("__krs_rule_result_sort_{nonce:016x}");
    let parameter_sort_path = call_site_path(rule.parameter().term_sort.sort())?;
    let result_sort_path = call_site_path(rule.result_sort().sort())?;
    let parameter_sort_type = sort_type_tokens(
        &parameter_sort_path,
        rule.parameter().term_sort.is_dynamic(),
    );
    let result_sort_type = sort_type_tokens(&result_sort_path, rule.result_sort().is_dynamic());

    let original = rule.item();
    let attrs = &original.attrs;
    let visibility = &original.vis;
    let fn_token = original.sig.fn_token;
    let name_ident = &original.sig.ident;
    let parameter_type = rule.parameter().term_sort.ty();
    let result_type = rule.result_sort().ty();
    let name = name_ident.unraw().to_string();
    let label = rule_label_tokens(&facade, attribute);
    let parameter_sort_spelling = rule.parameter().term_sort.sort_spelling();
    let result_sort_spelling = rule.result_sort().sort_spelling();
    let bindings = rule
        .parameter()
        .pattern
        .bindings()
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>();
    let mut binding_checks = Vec::new();
    for binding in rule.parameter().pattern.bindings() {
        let generated = call_site_ident(binding)?;
        binding_checks.push(quote! {
            let #binding = ();
            let _ = &#generated;
        });
    }
    for narrowing in narrowings {
        let sort = call_site_path(narrowing.sort())?;
        binding_checks.push(quote! {
            let _: ::core::marker::PhantomData<#sort> = ::core::marker::PhantomData;
        });
    }
    let parameter_reference = host_sort_reference(
        &facade,
        ProvenanceRole::RuleType,
        0,
        &parameter_key,
        &parameter_sort_spelling,
    );
    let result_reference = host_sort_reference(
        &facade,
        ProvenanceRole::RuleResultType,
        0,
        &result_key,
        &result_sort_spelling,
    );
    let binding_idents = rule.parameter().pattern.bindings().to_vec();
    let mut term_builder =
        TermBuilder::new(&facade, nonce, &cfg, &binding_idents).with_enum_glob(enum_glob);
    let subject = term_builder.expand(rule.subject_tree(), TermSide::Left)?;
    term_builder.reset_side();
    let result = term_builder.expand(rule.result().tree(), TermSide::Right)?;
    term_builder.reset_side();
    let requires = if let Some(condition) = rule.requires() {
        let term = term_builder.expand(condition.term().tree(), TermSide::Requires)?;
        quote! {
            ::core::option::Option::Some(#facade::HostRuleCondition {
                key: #facade::ProvenanceKey::new(#rule_requires_role, 0)
                    .expect("KRS parser roles are nonempty"),
                term: #term,
            })
        }
    } else {
        quote!(::core::option::Option::None)
    };
    let term_key_functions = term_builder.key_functions;
    let priority = if attribute.is_owise() {
        rule_owise_tokens(&facade, attribute)
    } else {
        priority.map_or_else(
            || quote!(::core::option::Option::None),
            |priority| {
                let value = priority.value();
                quote!(::core::option::Option::Some(#facade::DescriptorRulePriority {
                    key: #facade::ProvenanceKey::new(#equation_priority_role, 0)
                        .expect("KRS parser roles are nonempty"),
                    value: #value,
                }))
            },
        )
    };
    let simplification = simplification.map_or_else(
        || quote!(::core::option::Option::None),
        |simplification| {
            let priority = simplification.priority().map_or_else(
                || quote!(::core::option::Option::None),
                |value| {
                    quote!(::core::option::Option::Some(
                        #facade::DescriptorSimplificationPriority {
                            key: #facade::ProvenanceKey::new(#simplification_priority_role, 0)
                                .expect("KRS parser roles are nonempty"),
                            value: #value,
                        }
                    ))
                },
            );
            quote!(::core::option::Option::Some(#facade::DescriptorSimplification {
                key: #facade::ProvenanceKey::new(#simplification_marker_role, 0)
                    .expect("KRS parser roles are nonempty"),
                priority: #priority,
            }))
        },
    );
    let (sentence_kind, item_kind) = match sentence_kind {
        krs_ir::SentenceKind::Transition => (
            quote!(#facade::SentenceKind::Transition),
            quote!(#facade::ItemKind::Rule),
        ),
        krs_ir::SentenceKind::Equation => (
            quote!(#facade::SentenceKind::Equation),
            quote!(#facade::ItemKind::Equation),
        ),
        krs_ir::SentenceKind::Simplification => (
            quote!(#facade::SentenceKind::Simplification),
            quote!(#facade::ItemKind::Simplification),
        ),
        krs_ir::SentenceKind::Alias => (
            quote!(#facade::SentenceKind::Alias),
            quote!(#facade::ItemKind::Alias),
        ),
        krs_ir::SentenceKind::Claim => unreachable!("claims have a separate authoring form"),
    };

    Ok(quote! {
        #(#attrs)*
        #visibility #fn_token #name_ident(
            __krs_symbolic_subject: #parameter_type,
        ) -> #result_type {
            let _krs_binding_check = || {
                #(#binding_checks)*
            };
            let _ = __krs_symbolic_subject;
            ::core::panic!("KRS rule declarations have no runtime implementation")
        }

        #(#cfg)*
        #[doc(hidden)]
        fn #parameter_key() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#parameter_sort_type>()
        }

        #(#cfg)*
        #[doc(hidden)]
        fn #result_key() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#result_sort_type>()
        }

        #(#term_key_functions)*

        #(#cfg)*
        #[doc(hidden)]
        fn #factory() -> #facade::HostDescriptor {
            let rule = #facade::HostStructuredRuleDescriptor {
                sentence_kind: #sentence_kind,
                label: #label,
                requires: #requires,
                priority: #priority,
                simplification: #simplification,
                pattern_key: #facade::ProvenanceKey::new(#rule_pattern_role, 0)
                    .expect("KRS parser roles are nonempty"),
                result_key: #facade::ProvenanceKey::new(#rule_result_role, 0)
                    .expect("KRS parser roles are nonempty"),
                subject_sort: #parameter_reference,
                result_sort: #result_reference,
                bindings: ::std::vec![#(#bindings.to_owned()),*],
                subject: #subject,
                result: #result,
            };
            #facade::HostDescriptor {
                protocol_version: #facade::ProtocolVersion::CURRENT,
                id: #facade::HostItemId::from_macro_context(
                    env!("CARGO_PKG_NAME"),
                    env!("CARGO_PKG_VERSION"),
                    env!("CARGO_MANIFEST_DIR"),
                    module_path!(),
                    #name,
                    #item_kind,
                    "",
                )
                .expect("Cargo and Rust macro context form a valid host identity"),
                declared_type: ::core::option::Option::None,
                payload: #facade::HostDescriptorPayload::StructuredRule(::std::boxed::Box::new(rule)),
                cfg: ::core::default::Default::default(),
                provenance: #provenance,
            }
        }

        #(#cfg)*
        #facade::__register_host_descriptor!(#factory);
    })
}

#[allow(clippy::needless_pass_by_value)]
pub(crate) fn orphan_rule_helper(
    env: &dyn MacroEnvironment,
    entry: AttributeMacro,
    attributes: TokenStream,
    item: TokenStream,
) -> syn::Result<TokenStream> {
    let name = entry.name();
    if entry == AttributeMacro::Requires {
        let mut function: ItemFn = syn::parse2(item)?;
        if let Some((index, outer)) =
            function
                .attrs
                .iter()
                .enumerate()
                .find_map(|(index, attribute)| {
                    let helper = helper_entry(attribute.path())?;
                    matches!(
                        helper,
                        AttributeMacro::Equation | AttributeMacro::Simplification
                    )
                    .then_some((index, helper))
                })
        {
            function.attrs.remove(index);
            let helper: Attribute = syn::parse_quote!(#[k::requires(#attributes)]);
            function.attrs.insert(0, helper);
            return if outer == AttributeMacro::Equation {
                equation(env, TokenStream::new(), function.to_token_stream())
            } else {
                simplification(env, TokenStream::new(), function.to_token_stream())
            };
        }
    }
    Err(syn::Error::new(
        Span::call_site(),
        if matches!(entry, AttributeMacro::Exists | AttributeMacro::Ensures) {
            format!("`#[k::{name}]` is a claim helper; place `#[k::claim(...)]` before it")
        } else {
            format!("`#[k::{name}]` is a rule helper; place `#[k::rule]` before it")
        },
    ))
}
