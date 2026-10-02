//! Function-form sentences: `#[k::rule]`, `#[k::equation]`, `#[k::simplification]`, `#[k::alias]`, `#[k::priority]`, and orphan rule helpers.

use crate::ExpandError;
use krs_diagnostic::codes::expand;
use krs_ir::wire::{
    WirePayload, WireRuleCondition, WireSortReference, WireStructuredRule, WireTypeReference,
};
use krs_ir::{
    DescriptorRuleLabel, DescriptorRulePriority, DescriptorSimplification,
    DescriptorSimplificationPriority, StableText,
};
use krs_syntax::KrsSyntax;
use krs_syntax::surface::{AttributeMacro, helper_entry};
use krs_syntax::{ProvenanceAnchor, ProvenanceRole, TokenRange};
use proc_macro2::{Span, TokenStream};
use quote::{ToTokens, format_ident, quote};
use syn::ext::IdentExt;
use syn::{Attribute, FnArg, ItemFn, Pat, Path};

use super::factory::{DescriptorFactory, FactoryPayload};
use super::nonce::expansion_nonce;
use super::state_rules::configuration_rule;
use super::terms::{TermBuilder, TermSide, WireSlots, wire_key};
use super::tokens::{call_site_cfg_attributes, call_site_ident, call_site_path, sort_type_tokens};
use crate::environment::MacroEnvironment;
use crate::provenance::host_provenance_static;

pub(crate) fn rule(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> crate::Result<TokenStream> {
    let attribute = krs_syntax::RuleAttribute::parse_tokens(attributes)?;
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
) -> crate::Result<TokenStream> {
    krs_syntax::EquationAttribute::parse_tokens(attributes)?;
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
) -> crate::Result<TokenStream> {
    let attribute = krs_syntax::SimplificationAttribute::parse_tokens(attributes)?;
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
) -> crate::Result<TokenStream> {
    krs_syntax::AliasAttribute::parse_tokens(attributes)?;
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
    Err(ExpandError::new(
        expand::ORPHAN_HELPER,
        Span::call_site(),
        "`#[k::alias]` on a production is a constructor helper; place `#[k::constructor(...)]` before it",
    ))
}

pub(crate) fn priority(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> crate::Result<TokenStream> {
    let priority = krs_syntax::PriorityAttribute::parse_tokens(attributes)?;
    let mut function: ItemFn = syn::parse2(item)?;
    let Some(index) = function
        .attrs
        .iter()
        .position(|attribute| helper_entry(attribute.path()) == Some(AttributeMacro::Equation))
    else {
        return Err(ExpandError::new(
            expand::ORPHAN_HELPER,
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

fn ordinary_rule(
    env: &dyn MacroEnvironment,
    item: TokenStream,
    attribute: &krs_syntax::RuleAttribute,
    sentence_kind: krs_ir::SentenceKind,
    priority: Option<&krs_syntax::PriorityAttribute>,
    simplification: Option<&krs_syntax::SimplificationAttribute>,
) -> crate::Result<TokenStream> {
    let rule = krs_syntax::RuleItem::parse_tokens(item)?;
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
) -> crate::Result<TokenStream> {
    let rule_requires_role = ProvenanceRole::RuleRequires;
    let equation_priority_role = ProvenanceRole::EquationPriority;
    let simplification_priority_role = ProvenanceRole::SimplificationPriority;
    let simplification_marker_role = ProvenanceRole::SimplificationMarker;
    let rule_pattern_role = ProvenanceRole::RulePattern;
    let rule_result_role = ProvenanceRole::RuleResult;
    let facade = env.facade_path()?;
    let mut anchors = rule.full_provenance()?;
    anchors.extend(attribute.provenance()?);
    if sentence_kind == krs_ir::SentenceKind::Alias {
        anchors.push(ProvenanceAnchor::new(
            ProvenanceRole::AliasClause,
            0,
            TokenRange::for_tokens(&rule.item().sig.ident)?,
        ));
    }
    if let Some(priority) = priority {
        anchors.extend(priority.provenance()?);
    }
    if let Some(simplification) = simplification {
        anchors.push(ProvenanceAnchor::new(
            ProvenanceRole::SimplificationMarker,
            0,
            TokenRange::for_tokens(&rule.item().sig.ident)?,
        ));
        anchors.extend(simplification.provenance()?);
    }
    let fallback = krs_syntax::TokenRange::for_tokens(rule.item())?;
    let provenance = host_provenance_static(env, &facade, fallback, &anchors);
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
    let label = attribute.label().map(|label| DescriptorRuleLabel {
        key: wire_key(ProvenanceRole::RuleLabel, 0),
        name: label.value().clone(),
    });
    let parameter_sort_spelling = rule.parameter().term_sort.sort_token_text();
    let result_sort_spelling = rule.result_sort().sort_token_text();
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
    let binding_idents = rule.parameter().pattern.bindings().to_vec();
    let mut term_builder =
        TermBuilder::new(&facade, nonce, &cfg, &binding_idents).with_enum_glob(enum_glob);
    let mut slots = WireSlots::new(&facade);
    let subject_sort = WireSortReference {
        key: wire_key(ProvenanceRole::RuleType, 0),
        target: WireTypeReference {
            slot: slots.type_slot(quote!(#facade::HostTypeKey(#parameter_key))),
            authored_path: parameter_sort_spelling,
        },
    };
    let result_sort = WireSortReference {
        key: wire_key(ProvenanceRole::RuleResultType, 0),
        target: WireTypeReference {
            slot: slots.type_slot(quote!(#facade::HostTypeKey(#result_key))),
            authored_path: result_sort_spelling,
        },
    };
    let subject = term_builder.expand_wire(rule.subject_tree(), TermSide::Left, &mut slots)?;
    term_builder.reset_side();
    let result = term_builder.expand_wire(rule.result().tree(), TermSide::Right, &mut slots)?;
    term_builder.reset_side();
    let requires = if let Some(condition) = rule.requires() {
        let term =
            term_builder.expand_wire(condition.term().tree(), TermSide::Requires, &mut slots)?;
        Some(WireRuleCondition {
            key: wire_key(rule_requires_role, 0),
            term,
        })
    } else {
        None
    };
    let term_key_functions = term_builder.key_functions;
    let priority = if attribute.is_owise() {
        Some(DescriptorRulePriority {
            key: wire_key(ProvenanceRole::RuleOwise, 0),
            value: 200,
        })
    } else {
        priority.map(|priority| DescriptorRulePriority {
            key: wire_key(equation_priority_role, 0),
            value: priority.value(),
        })
    };
    let simplification = simplification.map(|simplification| DescriptorSimplification {
        key: wire_key(simplification_marker_role, 0),
        priority: simplification
            .priority()
            .map(|value| DescriptorSimplificationPriority {
                key: wire_key(simplification_priority_role, 0),
                value,
            }),
    });
    let item_kind_variant = format_ident!("{}", sentence_kind.item_kind().stable_text());
    let item_kind = quote!(#facade::ItemKind::#item_kind_variant);
    let wire = WirePayload::StructuredRule(Box::new(WireStructuredRule {
        sentence_kind,
        label,
        requires,
        priority,
        simplification,
        pattern_key: wire_key(rule_pattern_role, 0),
        result_key: wire_key(rule_result_role, 0),
        subject_sort,
        result_sort,
        bindings,
        subject,
        result,
    }));
    let wire = serde_json::to_string(&wire).expect("KRS wire values serialize");
    let slot_tokens = slots.tokens();

    let factory_tokens = DescriptorFactory {
        facade: &facade,
        factory: &factory,
        name: quote!(#name),
        item_kind: quote!(#item_kind),
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

        #factory_tokens
    })
}

#[allow(clippy::needless_pass_by_value)]
pub(crate) fn orphan_rule_helper(
    env: &dyn MacroEnvironment,
    entry: AttributeMacro,
    attributes: TokenStream,
    item: TokenStream,
) -> crate::Result<TokenStream> {
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
    Err(ExpandError::new(
        expand::ORPHAN_HELPER,
        Span::call_site(),
        if matches!(entry, AttributeMacro::Exists | AttributeMacro::Ensures) {
            format!("`#[k::{name}]` is a claim helper; place `#[k::claim(...)]` before it")
        } else {
            format!("`#[k::{name}]` is a rule helper; place `#[k::rule]` before it")
        },
    ))
}
