//! Function-form sentences: `#[k::rule]`, `#[k::equation]`, `#[k::simplification]`, `#[k::alias]`, the retired `#[k::priority]`, and orphan rule helpers.

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

use super::existentials::{ensures_condition, evaluation_step, existential_binders, fresh_binders};
use super::factory::{DescriptorFactory, FactoryPayload};
use super::island_checks::{consumed_state_island_import_checks, wrapper_type_check};
use super::nonce::expansion_nonce;
use super::state_rules::{StateRuleBuilder, configuration_rule};
use super::terms::{TermBuilder, TermSide, WireSlots, wire_key, wire_sort_reference};
use super::tokens::{
    call_site_cfg_attributes, call_site_ident, call_site_path, sort_type_tokens, spelling,
};
use crate::environment::MacroEnvironment;
use crate::provenance::host_provenance;

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
        // A term subject followed by `cells!` is an equation's function
        // context (KF-025), which K rejects on a transition.
        let inputs = parsed.sig.inputs.iter().collect::<Vec<_>>();
        if let [.., FnArg::Typed(subject), last] = inputs.as_slice()
            && !matches!(&*subject.pat, Pat::Ident(_))
        {
            return Err(krs_syntax::SyntaxError::new(
                krs_syntax::SyntaxErrorKind::InvalidFunctionContext {
                    reason: krs_syntax::FUNCTION_CONTEXT_ONLY_ON_EQUATIONS.to_owned(),
                },
                syn::spanned::Spanned::span(last),
            )
            .into());
        }
        if let Some(anywhere) = attribute.anywhere() {
            return Err(krs_syntax::SyntaxError::new(
                krs_syntax::SyntaxErrorKind::InvalidRuleKey {
                    reason: krs_syntax::ANYWHERE_NOT_TERM_SHAPED,
                },
                anywhere.span(),
            )
            .into());
        }
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
    let equation = krs_syntax::EquationAttribute::parse_tokens(attributes)?;
    let attribute = krs_syntax::RuleAttribute::default();
    ordinary_rule(
        env,
        item,
        &attribute,
        krs_ir::SentenceKind::Equation,
        Some(&equation),
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

/// `#[k::desugar]`: a desugar clause fn (KF-028). The production marker is a
/// constructor helper consumed by `#[k::constructor]` or `#[k::constructors]`.
pub(crate) fn desugar(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> crate::Result<TokenStream> {
    let desugar = krs_syntax::DesugarAttribute::parse_tokens(attributes)?;
    if let Ok(function) = syn::parse2::<ItemFn>(item.clone()) {
        if let Some(requires) = function
            .attrs
            .iter()
            .find(|attribute| helper_entry(attribute.path()) == Some(AttributeMacro::Requires))
        {
            let name = requires
                .path()
                .segments
                .last()
                .expect("helper attributes have a final path segment");
            return Err(requires_on_desugar(name.ident.span()));
        }
        let rule = krs_syntax::RuleItem::parse_desugar_tokens(item, &desugar)?;
        return expand_ordinary_rule(
            env,
            &rule,
            &krs_syntax::RuleAttribute::default(),
            krs_ir::SentenceKind::Desugar,
            OrdinaryRuleKeys {
                desugar: Some(&desugar),
                ..OrdinaryRuleKeys::default()
            },
            None,
            &[],
        );
    }
    Err(ExpandError::new(
        expand::ORPHAN_HELPER,
        Span::call_site(),
        "`#[k::desugar]` on a production is a constructor helper; place `#[k::constructor(...)]` before it",
    ))
}

/// `#[k::requires]` on a desugar clause (KF-028).
fn requires_on_desugar(span: Span) -> ExpandError {
    krs_syntax::SyntaxError::new(
        krs_syntax::SyntaxErrorKind::InvalidRuleKey {
            reason: krs_syntax::REQUIRES_ON_DESUGAR_CLAUSE,
        },
        span,
    )
    .into()
}

pub(crate) fn priority(
    _env: &dyn MacroEnvironment,
    attributes: TokenStream,
    _item: TokenStream,
) -> crate::Result<TokenStream> {
    krs_syntax::PriorityAttribute::parse_tokens(attributes)?;
    unreachable!("the retired priority attribute never parses")
}

fn ordinary_rule(
    env: &dyn MacroEnvironment,
    item: TokenStream,
    attribute: &krs_syntax::RuleAttribute,
    sentence_kind: krs_ir::SentenceKind,
    equation: Option<&krs_syntax::EquationAttribute>,
    simplification: Option<&krs_syntax::SimplificationAttribute>,
) -> crate::Result<TokenStream> {
    let rule = if sentence_kind == krs_ir::SentenceKind::Equation {
        krs_syntax::RuleItem::parse_equation_tokens(item)?
    } else {
        krs_syntax::RuleItem::parse_tokens(item)?
    };
    expand_ordinary_rule(
        env,
        &rule,
        attribute,
        sentence_kind,
        OrdinaryRuleKeys {
            equation,
            simplification,
            desugar: None,
        },
        None,
        &[],
    )
}

/// The sentence-kind keys of an ordinary rule fn beyond `#[k::rule(..)]`.
#[derive(Clone, Copy, Default)]
struct OrdinaryRuleKeys<'a> {
    equation: Option<&'a krs_syntax::EquationAttribute>,
    simplification: Option<&'a krs_syntax::SimplificationAttribute>,
    /// `#[k::desugar(..)]` of a desugar clause (KF-046).
    desugar: Option<&'a krs_syntax::DesugarAttribute>,
}

#[expect(
    clippy::too_many_lines,
    reason = "Rule lowering keeps the declaration context and both sides together."
)]
fn expand_ordinary_rule(
    env: &dyn MacroEnvironment,
    rule: &krs_syntax::RuleItem,
    attribute: &krs_syntax::RuleAttribute,
    sentence_kind: krs_ir::SentenceKind,
    keys: OrdinaryRuleKeys<'_>,
    enum_glob: Option<&Path>,
    narrowings: &[krs_syntax::RuleNarrowing],
) -> crate::Result<TokenStream> {
    let OrdinaryRuleKeys {
        equation,
        simplification,
        desugar,
    } = keys;
    // A single-body rule (KF-011) is a transition that is not an anywhere
    // rule: its subject's `k::rewrite!` islands say what changes.
    if rule.result().is_none()
        && (sentence_kind != krs_ir::SentenceKind::Transition || attribute.anywhere().is_some())
    {
        return Err(krs_syntax::SyntaxError::new(
            krs_syntax::SyntaxErrorKind::InvalidLocalRewrite {
                reason: "a single-body rule (one that returns `()`) is a `#[k::rule]` transition, never an anywhere rule, an equation, a simplification, an alias, or a desugar clause; return the result instead".to_owned(),
            },
            rule.item().sig.ident.span(),
        )
        .into());
    }
    if let Some(binder) = rule.existentials().fresh().first()
        && (sentence_kind != krs_ir::SentenceKind::Transition || attribute.anywhere().is_some())
    {
        return Err(misplaced_fresh(binder.name().span()));
    }
    if sentence_kind != krs_ir::SentenceKind::Transition
        && let Some(helper) = rule.existentials().attributes().first()
    {
        return Err(misplaced_existential(syn::spanned::Spanned::span(
            helper.path(),
        )));
    }
    let rule_requires_role = ProvenanceRole::RuleRequires;
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
    if sentence_kind == krs_ir::SentenceKind::Desugar {
        anchors.push(ProvenanceAnchor::new(
            ProvenanceRole::DesugarClause,
            0,
            TokenRange::for_tokens(&rule.item().sig.ident)?,
        ));
    }
    if let Some(equation) = equation {
        anchors.extend(equation.provenance()?);
    }
    if let Some(desugar) = desugar {
        anchors.extend(desugar.provenance()?);
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
    let provenance = host_provenance(env, &facade, fallback, &anchors);
    let sentence_name = match sentence_kind {
        krs_ir::SentenceKind::Transition => "rule",
        krs_ir::SentenceKind::Equation => "equation",
        krs_ir::SentenceKind::Simplification => "simplification",
        krs_ir::SentenceKind::Alias => "alias",
        krs_ir::SentenceKind::Desugar => "desugar",
        krs_ir::SentenceKind::Claim => unreachable!("claims have a separate authoring form"),
    };
    let nonce = expansion_nonce(env, sentence_name, &rule.item().sig.ident, fallback);
    let factory = format_ident!(
        "__krs_rule_descriptor_{nonce:016x}",
        span = Span::call_site()
    );
    let cfg = call_site_cfg_attributes(&rule.item().attrs)?;
    let predicate = predicate_rule(rule, sentence_kind)?;
    let parameter_key = format_ident!("__krs_rule_subject_sort_{nonce:016x}");
    let result_key = format_ident!("__krs_rule_result_sort_{nonce:016x}");
    let parameter_sort_path = call_site_path(rule.parameter().term_sort.sort())?;
    let result_sort_path = rule
        .result_sort()
        .map(|sort| call_site_path(sort.sort()))
        .transpose()?;
    // A predicate simplification's `ml::Predicate` types are no sorts: the
    // descriptor carries Bool placeholders, and rustc checks that both
    // types are the facade's `ml::Predicate` (KF-039). A single-body rule
    // (KF-011) has no result type.
    let (parameter_sort_type, result_sort_type, predicate_checks) = if predicate {
        (
            quote!(#facade::builtin::Bool),
            Some(quote!(#facade::builtin::Bool)),
            quote! {
                #(#cfg)*
                const _: fn(#parameter_sort_path) -> #facade::ml::Predicate = |predicate| predicate;
                #(#cfg)*
                const _: fn(#result_sort_path) -> #facade::ml::Predicate = |predicate| predicate;
            },
        )
    } else {
        (
            sort_type_tokens(
                &parameter_sort_path,
                rule.parameter().term_sort.is_dynamic(),
            ),
            rule.result_sort()
                .zip(result_sort_path.as_ref())
                .map(|(sort, path)| sort_type_tokens(path, sort.is_dynamic())),
            TokenStream::new(),
        )
    };

    let original = rule.item();
    let attrs = &original.attrs;
    let visibility = &original.vis;
    let fn_token = original.sig.fn_token;
    let name_ident = &original.sig.ident;
    let parameter_type = rule.parameter().term_sort.ty();
    let result_type = rule.result_sort().map(krs_syntax::TermSort::ty);
    let name = name_ident.unraw().to_string();
    let label = attribute.label().map(|label| DescriptorRuleLabel {
        key: wire_key(ProvenanceRole::RuleLabel, 0),
        name: label.value().clone(),
    });
    let parameter_sort_spelling = rule.parameter().term_sort.sort_token_text();
    let result_sort_spelling = rule
        .result_sort()
        .map(krs_syntax::TermSort::sort_token_text);
    let bindings = rule
        .parameter()
        .pattern
        .bindings()
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>();
    let mut binding_checks = Vec::new();
    for binding in &rule.condition_bindings() {
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
    // The result and the ensures condition also see the existentials; the
    // subject and requires never do (the parser rejects such a use).
    let binding_idents = rule.result_bindings();
    let mut term_builder =
        TermBuilder::new(&facade, nonce, &cfg, &binding_idents).with_enum_glob(enum_glob);
    let mut slots = WireSlots::new(&facade);
    let (existentials, existential_key_functions) =
        existential_binders(rule.existentials(), &facade, nonce, &cfg, &mut slots)?;
    let (fresh, fresh_key_functions) =
        fresh_binders(rule.existentials(), &facade, nonce, &cfg, &mut slots)?;
    let (evaluation, evaluation_key_function) = evaluation_step(
        attribute,
        rule.existentials(),
        (&facade, nonce, &cfg),
        &mut slots,
    )?;
    let subject_sort = WireSortReference {
        key: wire_key(ProvenanceRole::RuleType, 0),
        target: WireTypeReference {
            slot: slots.type_slot(quote!(#facade::HostTypeKey(#parameter_key))),
            authored_path: parameter_sort_spelling,
        },
    };
    let result_sort = result_sort_spelling.map(|authored_path| WireSortReference {
        key: wire_key(ProvenanceRole::RuleResultType, 0),
        target: WireTypeReference {
            slot: slots.type_slot(quote!(#facade::HostTypeKey(#result_key))),
            authored_path,
        },
    });
    let (typed_bindings, binder_key_functions) =
        typed_binders(rule, &facade, nonce, &cfg, &mut slots)?;
    term_builder.set_rewrites(rule.result().is_none());
    let subject = term_builder.expand_wire(rule.subject_tree(), TermSide::Left, &mut slots)?;
    term_builder.set_rewrites(false);
    let context_bindings = rule.condition_bindings();
    let function_context = rule
        .function_context()
        .map(|context| {
            function_context(
                rule,
                context,
                &mut term_builder,
                &context_bindings,
                FunctionContextExpansion {
                    facade: &facade,
                    nonce,
                    cfg: &cfg,
                },
                &mut slots,
            )
        })
        .transpose()?;
    let (function_context, context_tokens) = function_context.unzip();
    term_builder.reset_side();
    let result = rule
        .result()
        .map(|result| term_builder.expand_wire(result.tree(), TermSide::Right, &mut slots))
        .transpose()?;
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
    term_builder.reset_side();
    let ensures = ensures_condition(rule.existentials(), &mut term_builder, &mut slots)?;
    let mut term_key_functions = term_builder.key_functions;
    term_key_functions.extend(existential_key_functions);
    term_key_functions.extend(fresh_key_functions);
    term_key_functions.extend(evaluation_key_function);
    let priority = attribute
        .transition_priority()
        .or_else(|| equation.and_then(krs_syntax::EquationAttribute::equation_priority))
        .map(|(role, value)| DescriptorRulePriority {
            key: wire_key(role, 0),
            value,
        });
    let simplification = simplification.map(|simplification| DescriptorSimplification {
        key: wire_key(simplification_marker_role, 0),
        priority: simplification
            .priority()
            .map(|value| DescriptorSimplificationPriority {
                key: wire_key(simplification_priority_role, 0),
                value,
            }),
        restriction: match_restriction(simplification.restriction()),
    });
    let equation_attributes = equation
        .and_then(|equation| match_restriction(equation.restriction()))
        .map(|restriction| krs_ir::DescriptorEquationAttributes { restriction });
    let item_kind_variant = format_ident!("{}", sentence_kind.item_kind().stable_text());
    let item_kind = quote!(#facade::ItemKind::#item_kind_variant);
    let nondet = attribute
        .nondet()
        .map(|group| krs_ir::DescriptorNondetGroup {
            key: ProvenanceRole::RuleNondetGroup.key(0),
            name: group.unraw().to_string(),
        });
    let anywhere = attribute
        .anywhere()
        .map(|_| wire_key(ProvenanceRole::RuleAnywhere, 0));
    let wire = WirePayload::StructuredRule(Box::new(WireStructuredRule {
        sentence_kind,
        label,
        requires,
        priority,
        nondet,
        anywhere,
        simplification,
        pattern_key: wire_key(rule_pattern_role, 0),
        typed_bindings,
        result_key: result.is_some().then(|| wire_key(rule_result_role, 0)),
        subject_sort,
        result_sort,
        bindings,
        subject,
        result,
        existentials,
        ensures,
        fresh,
        equation: equation_attributes,
        unbound_variables: desugar
            .and_then(krs_syntax::DesugarAttribute::unbound_variables)
            .map(unbound_variables),
        function_context,
        predicate,
        evaluation,
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

    let ContextTokens {
        parameter: context_parameter,
        checks: context_checks,
        items: context_items,
    } = context_tokens.unwrap_or_default();
    let output_type = result_type.map(|result_type| quote!(-> #result_type));
    let result_key_function = result_sort_type.map(|result_sort_type| {
        quote! {
            #(#cfg)*
            #[doc(hidden)]
            fn #result_key() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<#result_sort_type>()
            }
        }
    });
    Ok(quote! {
        #(#attrs)*
        #visibility #fn_token #name_ident(
            __krs_symbolic_subject: #parameter_type,
            #context_parameter
        ) #output_type {
            let _krs_binding_check = || {
                #(#binding_checks)*
                #(#context_checks)*
            };
            let _ = __krs_symbolic_subject;
            ::core::panic!("KRS rule declarations have no runtime implementation")
        }

        #(#cfg)*
        #[doc(hidden)]
        fn #parameter_key() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#parameter_sort_type>()
        }

        #result_key_function

        #predicate_checks

        #(#binder_key_functions)*

        #(#term_key_functions)*

        #(#context_items)*

        #factory_tokens
    })
}

/// Whether a term-shaped rule fn is a predicate simplification (KF-039):
/// its subject and result types are both `ml::Predicate`, which only a
/// simplification may have.
fn predicate_rule(
    rule: &krs_syntax::RuleItem,
    sentence_kind: krs_ir::SentenceKind,
) -> crate::Result<bool> {
    let subject = &rule.parameter().term_sort;
    // A single-body rule (KF-011) has no result type.
    let Some(result) = rule.result_sort() else {
        if subject.is_predicate() {
            return Err(ExpandError::new(
                expand::ML_PLACEMENT,
                syn::spanned::Spanned::span(subject.ty()),
                "a predicate simplification states its `ml::Predicate` result; a single-body rule (`k::rewrite!`) rewrites object terms, `Term<S>`",
            ));
        }
        return Ok(false);
    };
    if !subject.is_predicate() && !result.is_predicate() {
        return Ok(false);
    }
    let span = |sort: &krs_syntax::TermSort| syn::spanned::Spanned::span(sort.ty());
    if sentence_kind != krs_ir::SentenceKind::Simplification {
        let sort = if subject.is_predicate() {
            subject
        } else {
            result
        };
        return Err(ExpandError::new(
            expand::ML_PLACEMENT,
            span(sort),
            "an `ml::Predicate` subject and result make a predicate simplification; they are allowed only on `#[k::simplification]` (a rule or equation rewrites object terms, `Term<S>`)",
        ));
    }
    if subject.is_predicate() != result.is_predicate() {
        let (sort, other) = if subject.is_predicate() {
            (result, "subject")
        } else {
            (subject, "result")
        };
        return Err(ExpandError::new(
            expand::ML_PLACEMENT,
            span(sort),
            format!(
                "a predicate simplification's parameter and result types disagree: the {other} is `ml::Predicate`, so this type must be `ml::Predicate` too; a simplification of object terms uses `Term<S>` on both sides"
            ),
        ));
    }
    Ok(true)
}

/// The shared expansion inputs of an equation's function context.
#[derive(Clone, Copy)]
struct FunctionContextExpansion<'a> {
    facade: &'a Path,
    nonce: u64,
    cfg: &'a [Attribute],
}

/// The generated Rust of an equation's function context: its parameter of
/// the generated fn, its path checks, and its key functions.
#[derive(Default)]
struct ContextTokens {
    parameter: TokenStream,
    checks: Vec<TokenStream>,
    items: Vec<TokenStream>,
}

/// Expands an equation's function context (KF-025): its configuration
/// reference, its bindings the subject does not bind, and its one-sided cells,
/// whose left-hand ordinals continue after the subject's.
fn function_context(
    rule: &krs_syntax::RuleItem,
    context: &krs_syntax::FunctionContext,
    term_builder: &mut TermBuilder<'_>,
    bindings: &[syn::Ident],
    expansion: FunctionContextExpansion<'_>,
    slots: &mut WireSlots,
) -> crate::Result<(krs_ir::wire::WireFunctionContext, ContextTokens)> {
    let FunctionContextExpansion { facade, nonce, cfg } = expansion;
    let configuration_type = call_site_path(context.configuration_type())?;
    let configuration_key = format_ident!("__krs_function_context_configuration_{nonce:016x}");
    let subject = rule.parameter().pattern.bindings();
    let mut context_bindings = Vec::new();
    for binding in context.bindings() {
        if subject.contains(binding.name()) {
            continue;
        }
        let kind = match binding.kind() {
            krs_syntax::StateRuleBindingKind::Term => {
                let index = rule
                    .binders()
                    .iter()
                    .position(|binder| binder.name() == binding.name())
                    .expect("the binder list declares every context term binder");
                let ordinal = u32::try_from(index).map_err(|_| {
                    ExpandError::new(
                        expand::DESCRIPTOR_CAPACITY,
                        binding.name().span(),
                        "too many typed binders",
                    )
                })?;
                let sort = rule.binders()[index].term_sort();
                let key_fn = format_ident!("__krs_rule_binder_sort_{nonce:016x}_{ordinal}");
                krs_ir::ProtocolRuleBindingKind::Term {
                    sort: wire_sort_reference(
                        slots,
                        facade,
                        ProvenanceRole::RuleBindingType,
                        ordinal,
                        &key_fn,
                        &sort.sort_token_text(),
                    ),
                }
            }
            krs_syntax::StateRuleBindingKind::KSequenceFrame => {
                krs_ir::ProtocolRuleBindingKind::KSequenceFrame
            }
            krs_syntax::StateRuleBindingKind::MapFrame => krs_ir::ProtocolRuleBindingKind::MapFrame,
            krs_syntax::StateRuleBindingKind::ConfigurationFrame => {
                unreachable!("the parser rejects a bound configuration remainder")
            }
        };
        context_bindings.push(krs_ir::ProtocolRuleBinding {
            name: binding.name().to_string(),
            kind,
        });
    }
    let mut builder =
        StateRuleBuilder::new(facade, nonce, cfg, bindings, krs_syntax::RuleSide::Left);
    builder.continue_subject(term_builder);
    let cells = builder.expand_cells(context.pattern(), &configuration_type, slots)?;
    term_builder.continue_ordinals(&builder.terms);
    term_builder.next_key = builder.terms.next_key;
    let mut items = std::mem::take(&mut builder.terms.key_functions);
    items.push(quote! {
        #(#cfg)*
        #[doc(hidden)]
        fn #configuration_key() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#configuration_type>()
        }
    });
    let mut checks = context
        .wrapper_paths()
        .into_iter()
        .map(|path| call_site_path(path).map(|path| wrapper_type_check(&path)))
        .collect::<crate::Result<Vec<_>>>()?;
    checks.extend(consumed_state_island_import_checks(rule.item()));
    let wire = krs_ir::wire::WireFunctionContext {
        key: wire_key(ProvenanceRole::FunctionContext, 0),
        configuration: krs_ir::wire::WireConfigurationReference {
            key: wire_key(ProvenanceRole::FunctionContextType, 0),
            configuration: WireTypeReference {
                slot: slots.type_slot(quote!(#facade::HostTypeKey(#configuration_key))),
                authored_path: spelling(context.configuration_type()),
            },
        },
        bindings: context_bindings,
        cells,
    };
    Ok((
        wire,
        ContextTokens {
            parameter: quote!(__krs_function_context: #configuration_type,),
            checks,
            items,
        },
    ))
}

/// Transports the declared typed binders of a term-shaped rule fn (KF-009):
/// each sort resolves through its own type slot, keyed like a `cells!` rule's.
fn typed_binders(
    rule: &krs_syntax::RuleItem,
    facade: &Path,
    nonce: u64,
    cfg: &[Attribute],
    slots: &mut WireSlots,
) -> crate::Result<(Vec<krs_ir::wire::WireTypedBinding>, Vec<TokenStream>)> {
    let mut bindings = Vec::new();
    let mut key_functions = Vec::new();
    for (index, binder) in rule.binders().iter().enumerate() {
        let ordinal = u32::try_from(index).map_err(|_| {
            ExpandError::new(
                expand::DESCRIPTOR_CAPACITY,
                binder.name().span(),
                "too many typed binders",
            )
        })?;
        let sort = binder.term_sort();
        let path = call_site_path(sort.sort())?;
        let ty = sort_type_tokens(&path, sort.is_dynamic());
        let key_fn = format_ident!("__krs_rule_binder_sort_{nonce:016x}_{ordinal}");
        key_functions.push(quote! {
            #(#cfg)*
            #[doc(hidden)]
            fn #key_fn() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<#ty>()
            }
        });
        bindings.push(krs_ir::wire::WireTypedBinding {
            key: wire_key(ProvenanceRole::RuleBindingParameter, ordinal),
            name: binder.name().to_string(),
            sort: wire_sort_reference(
                slots,
                facade,
                ProvenanceRole::RuleBindingType,
                ordinal,
                &key_fn,
                &sort.sort_token_text(),
            ),
        });
    }
    Ok((bindings, key_functions))
}

/// The descriptor form of an equation's or simplification's `concrete`,
/// `symbolic`, and `smt_lemma` keys (KF-043), or `None` when none is authored.
fn match_restriction(
    restriction: &krs_syntax::MatchRestriction,
) -> Option<krs_ir::DescriptorMatchRestriction> {
    if restriction.is_empty() {
        return None;
    }
    let mut ordinal = 0_u32;
    let mut key = |restriction: Option<&krs_syntax::RestrictionKey>, role: ProvenanceRole| {
        restriction.map(|restriction| krs_ir::DescriptorRestriction {
            key: wire_key(role, 0),
            variables: restriction
                .variables()
                .unwrap_or_default()
                .iter()
                .map(|variable| {
                    let key = wire_key(ProvenanceRole::RestrictionVariable, ordinal);
                    ordinal += 1;
                    krs_ir::DescriptorRestrictionVariable {
                        key,
                        name: variable.to_string(),
                    }
                })
                .collect(),
        })
    };
    let concrete = key(restriction.concrete(), ProvenanceRole::RestrictionConcrete);
    let symbolic = key(restriction.symbolic(), ProvenanceRole::RestrictionSymbolic);
    Some(krs_ir::DescriptorMatchRestriction {
        concrete,
        symbolic,
        smt_lemma: restriction
            .smt_lemma()
            .map(|_| wire_key(ProvenanceRole::SmtLemma, 0)),
    })
}

/// The descriptor form of `unbound_variables = [..]` (KF-046).
fn unbound_variables(unbound: &krs_syntax::UnboundVariables) -> krs_ir::DescriptorUnboundVariables {
    krs_ir::DescriptorUnboundVariables {
        key: wire_key(ProvenanceRole::UnboundVariables, 0),
        variables: (0_u32..)
            .zip(unbound.variables())
            .map(|(ordinal, variable)| krs_ir::DescriptorUnboundVariable {
                key: wire_key(ProvenanceRole::UnboundVariable, ordinal),
                name: match variable {
                    krs_syntax::UnboundVariable::Named(name) => name.to_string(),
                    krs_syntax::UnboundVariable::Wildcard(_) => {
                        krs_ir::DescriptorUnboundVariable::WILDCARD.to_owned()
                    }
                },
            })
            .collect(),
    }
}

pub(crate) fn orphan_rule_helper(
    env: &dyn MacroEnvironment,
    entry: AttributeMacro,
    attributes: TokenStream,
    item: TokenStream,
) -> crate::Result<TokenStream> {
    let name = entry.name();
    if matches!(
        entry,
        AttributeMacro::Exists | AttributeMacro::Ensures | AttributeMacro::Fresh
    ) {
        return orphan_result_helper(env, entry, attributes, item);
    }
    if entry == AttributeMacro::Requires {
        let mut function: ItemFn = syn::parse2(item)?;
        if function
            .attrs
            .iter()
            .any(|attribute| helper_entry(attribute.path()) == Some(AttributeMacro::Desugar))
        {
            return Err(requires_on_desugar(Span::call_site()));
        }
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
            let sentence = function.attrs.remove(index);
            // The sentence attribute's own keys, such as `priority = N`, travel with it.
            let sentence_payload = match &sentence.meta {
                syn::Meta::List(list) => list.tokens.clone(),
                _ => TokenStream::new(),
            };
            let helper: Attribute = syn::parse_quote!(#[k::requires(#attributes)]);
            function.attrs.insert(0, helper);
            return if outer == AttributeMacro::Equation {
                equation(env, sentence_payload, function.to_token_stream())
            } else {
                simplification(env, sentence_payload, function.to_token_stream())
            };
        }
    }
    Err(ExpandError::new(
        expand::ORPHAN_HELPER,
        Span::call_site(),
        format!("`#[k::{name}]` is a rule helper; place `#[k::rule]` before it"),
    ))
}

/// `#[k::exists]`, `#[k::ensures]`, or `#[k::fresh]` written before its
/// sentence attribute: handed to a following `#[k::rule]`, rejected before
/// any other sentence.
#[expect(
    clippy::needless_pass_by_value,
    reason = "Attribute macro entry points own their input token streams."
)]
fn orphan_result_helper(
    env: &dyn MacroEnvironment,
    entry: AttributeMacro,
    attributes: TokenStream,
    item: TokenStream,
) -> crate::Result<TokenStream> {
    let name = entry.name();
    let mut function: ItemFn = syn::parse2(item)?;
    let outer = function
        .attrs
        .iter()
        .enumerate()
        .find_map(|(index, attribute)| {
            let helper = helper_entry(attribute.path())?;
            matches!(
                helper,
                AttributeMacro::Rule
                    | AttributeMacro::Claim
                    | AttributeMacro::Equation
                    | AttributeMacro::Simplification
                    | AttributeMacro::Alias
                    | AttributeMacro::ContextAlias
                    | AttributeMacro::Desugar
            )
            .then_some((index, helper))
        });
    match outer {
        Some((index, AttributeMacro::Rule)) => {
            // `#[k::exists]`/`#[k::fresh]`/`#[k::ensures]` before
            // `#[k::rule]`, as a readable clause expands: hand the helper
            // to the rule.
            let sentence = function.attrs.remove(index);
            let sentence_payload = match &sentence.meta {
                syn::Meta::List(list) => list.tokens.clone(),
                _ => TokenStream::new(),
            };
            let helper_name = format_ident!("{name}");
            let helper: Attribute = syn::parse_quote!(#[k::#helper_name(#attributes)]);
            function.attrs.insert(0, helper);
            return rule(env, sentence_payload, function.to_token_stream());
        }
        Some((_, AttributeMacro::Claim | AttributeMacro::ContextAlias))
            if entry == AttributeMacro::Fresh =>
        {
            return Err(misplaced_fresh(Span::call_site()));
        }
        Some((
            _,
            AttributeMacro::Equation
            | AttributeMacro::Simplification
            | AttributeMacro::Alias
            | AttributeMacro::Desugar,
        )) => {
            return Err(if entry == AttributeMacro::Fresh {
                misplaced_fresh(Span::call_site())
            } else {
                misplaced_existential(Span::call_site())
            });
        }
        _ => {}
    }
    if entry == AttributeMacro::Fresh {
        return Err(ExpandError::new(
            expand::ORPHAN_HELPER,
            Span::call_site(),
            "`#[k::fresh]` is a rule helper; place `#[k::rule(...)]` before it",
        ));
    }
    Err(ExpandError::new(
        expand::ORPHAN_HELPER,
        Span::call_site(),
        format!(
            "`#[k::{name}]` is a rule or claim helper; place `#[k::rule(...)]` or `#[k::claim(...)]` before it"
        ),
    ))
}

/// `#[k::fresh]` on a sentence other than a transition step: an equation,
/// simplification, alias, claim, context alias, anywhere rule (KF-022), or
/// heat or cool rule (KF-014).
pub(super) fn misplaced_fresh(span: Span) -> ExpandError {
    ExpandError::new(
        expand::FRESH_PLACEMENT,
        span,
        "fresh values are drawn from the generated counter only by a transition step of the configuration; `#[k::fresh]` is not allowed on an equation, simplification, alias, claim, context alias, anywhere rule, or heat or cool rule",
    )
}

/// Rejects a `#[k::fresh]` helper on a claim or context-alias item (KF-022).
pub(super) fn reject_fresh_helper(item: &TokenStream) -> crate::Result<()> {
    let Ok(function) = syn::parse2::<ItemFn>(item.clone()) else {
        return Ok(());
    };
    if let Some(helper) = function
        .attrs
        .iter()
        .find(|attribute| helper_entry(attribute.path()) == Some(AttributeMacro::Fresh))
    {
        let span = helper
            .path()
            .segments
            .last()
            .map_or_else(Span::call_site, |segment| segment.ident.span());
        return Err(misplaced_fresh(span));
    }
    Ok(())
}

/// `#[k::exists]` or `#[k::ensures]` on an equation, simplification, or alias.
fn misplaced_existential(span: Span) -> ExpandError {
    ExpandError::new(
        expand::EXISTENTIAL_PLACEMENT,
        span,
        "existential results and ensures are allowed on claims and transition rules, not on equations, simplifications, or aliases",
    )
}
