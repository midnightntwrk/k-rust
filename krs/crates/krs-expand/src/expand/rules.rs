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
use krs_syntax::positions::Form;
use krs_syntax::surface::{AttributeMacro, helper_entry, path_text};
use proc_macro2::{Span, TokenStream};
use quote::{ToTokens, format_ident, quote};
use std::iter::repeat;
use syn::ext::IdentExt;
use syn::{Attribute, FnArg, ItemFn, Pat, Path};

use super::existentials::{ensures_condition, evaluation_step, existential_binders, fresh_binders};
use super::factory::{DescriptorFactory, FactoryPayload};
use super::island_checks::{consumed_state_island_import_checks, wrapper_type_check};
use super::ledger::KeyLedger;
use super::nonce::expansion_nonce;
use super::state_rules::{StateRuleBuilder, configuration_rule};
use super::terms::{KeyedTerm, TermBuilder, TermSide, WireSlots, wire_sort_reference};
use super::tokens::{call_site_cfg_attributes, call_site_ident, sort_type_tokens, spelling};
use crate::environment::MacroEnvironment;
use crate::provenance::host_provenance;

pub(crate) fn rule(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> crate::Result<TokenStream> {
    let attribute = krs_syntax::RuleAttribute::parse_tokens(attributes.clone())?;
    // The body may hold a term no Rust block holds (`name @ pattern`), which the rule's own parse
    // reads and the position table judges.
    let parsed = krs_syntax::parse_fn_item(item.clone())?;
    if has_cells_subject(&parsed) {
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
        return configuration_rule(env, item, krs_syntax::RuleSentence::Transition(&attribute));
    }
    transition_rule(env, item, &attribute, attributes)
}

/// Expands a `#[k::rule]` fn whose sides are terms. A single-body rule whose
/// subject marks no change is told after the subject's constructs are judged
/// where they stand (`expand_ordinary_rule`). A whole subject `_`, alias or
/// island is refused with the clause to write instead (decision D3), unless
/// the rule is an `anywhere` rule, which has no such form.
fn transition_rule(
    env: &dyn MacroEnvironment,
    item: TokenStream,
    attribute: &krs_syntax::RuleAttribute,
    attribute_tokens: TokenStream,
) -> crate::Result<TokenStream> {
    let rule = krs_syntax::RuleItem::parse_rule_tokens(item.clone()).map_err(move |error| {
        if !error.refuses_whole_subject() {
            error
        } else if attribute.anywhere().is_some() {
            error.with_help(ANYWHERE_WHOLE_SUBJECT)
        } else {
            error.with_help(for_sort_clause_help(&item, &attribute_tokens))
        }
    })?;
    expand_ordinary_rule(
        env,
        &rule,
        krs_syntax::RuleSentence::Transition(attribute),
        None,
        &[],
    )
}

/// Why an `anywhere` rule's whole subject is no `_`, alias or island.
const ANYWHERE_WHOLE_SUBJECT: &str = "an `anywhere` rule rewrites the application its subject's root names wherever that application occurs, so no form writes one for any term of a sort";

/// `#[k::context(hole = h, result = S, label = "l")]` (KF-021): a context
/// is expanded as a rule without a result, whose evaluation step names the
/// hole and whose keys carry the context roles.
pub(crate) fn context(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> crate::Result<TokenStream> {
    let context = krs_syntax::ContextAttribute::parse_tokens(attributes)?;
    reject_fresh_helper(&item)?;
    let parsed: ItemFn = syn::parse2(item.clone())?;
    if has_cells_subject(&parsed) {
        return configuration_rule(env, item, krs_syntax::RuleSentence::Context(&context));
    }
    let rule = krs_syntax::RuleItem::parse_context_tokens(item)?;
    expand_ordinary_rule(
        env,
        &rule,
        krs_syntax::RuleSentence::Context(&context),
        None,
        &[],
    )
}

/// Whether the fn's last parameter is a `cells!` subject.
fn has_cells_subject(item: &ItemFn) -> bool {
    item.sig.inputs.last().is_some_and(|argument| {
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
    })
}

pub(crate) fn equation(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> crate::Result<TokenStream> {
    let equation = krs_syntax::EquationAttribute::parse_tokens(attributes)?;
    ordinary_rule(env, item, krs_syntax::RuleSentence::Equation(&equation))
}

/// An equation the shared parser synthesized from authored tokens: one a
/// function shorthand's body defines, whose only `#[k::equation]` key is
/// the `owise` of a catch-all arm.
pub(crate) fn equation_item(
    env: &dyn MacroEnvironment,
    shorthand: &krs_syntax::ShorthandEquation,
) -> crate::Result<TokenStream> {
    let equation = krs_syntax::EquationAttribute::parse_tokens(shorthand.equation_keys())?;
    let rule = shorthand.rule()?;
    expand_ordinary_rule(
        env,
        &rule,
        krs_syntax::RuleSentence::Equation(&equation),
        None,
        &[],
    )
}

/// What a `k::equations!` row shares with its table: the `use` items,
/// through which rustc resolves the row's one-segment paths, and the alias
/// that names the header's function. The header path is written once, so it
/// reaches rustc once, as the alias's definition; the row's signature, the
/// head of its subject and its arity check name the alias.
#[derive(Clone, Copy)]
pub(crate) struct TableRow<'a> {
    pub(crate) imports: &'a [syn::ItemUse],
    pub(crate) function: &'a syn::Ident,
}

/// One `k::equations!` row: an equation whose one-segment paths rustc
/// resolves through the table's `use` items, and the check of its argument
/// count against the function's.
pub(crate) fn equation_row(
    env: &dyn MacroEnvironment,
    row: &krs_syntax::EquationRow,
    table: TableRow<'_>,
) -> crate::Result<TokenStream> {
    let TableRow { imports, function } = table;
    let equation = expand_ordinary_rule(
        env,
        row.rule(),
        krs_syntax::RuleSentence::Equation(row.equation()),
        Some(table),
        &[],
    )?;
    let facade = env.facade_path()?;
    let cfg = call_site_cfg_attributes(&row.rule().item().attrs)?;
    let arguments = (0..row.arity()).map(|_| quote!(#facade::__krs_argument()));
    let arity = quote::quote_spanned! {row.arguments().span()=>
        #(#cfg)*
        const _: () = {
            #[allow(clippy::unused_unit)]
            fn __krs_row_arity() {
                let _: <#function as #facade::__KrsFunction>::Arguments = (#(#arguments,)*);
            }
        };
    };
    let binder_check =
        scoped_binder_check(&cfg, imports, row.rule().parameter().pattern.bindings());
    Ok(quote! {
        #equation
        #arity
        #binder_check
    })
}

/// Checks the binders of a readable table's clause or row with the block's
/// `use` items in scope. A bare identifier in a KRS pattern is a binder;
/// where the block's imports make it a unit variant or a constant, which
/// Rust would read instead, `let A = ();` is a refutable pattern of another
/// type and rustc reports E0308 at the name, so the clause cannot silently
/// bind everything. The variant is written `A()` or `Enum::A`. Imports of
/// the module are already in scope of the sentence fn's own binding check.
pub(super) fn scoped_binder_check(
    cfg: &[Attribute],
    imports: &[syn::ItemUse],
    binders: &[syn::Ident],
) -> Option<TokenStream> {
    // A bit template's hidden binder cannot name a unit variant.
    let binders = binders
        .iter()
        .filter(|binder| !krs_syntax::is_hidden_binder(&binder.to_string()))
        .collect::<Vec<_>>();
    (!imports.is_empty() && !binders.is_empty()).then(|| {
        quote! {
            #(#cfg)*
            const _: () = {
                #(
                    #[allow(unused_imports, clippy::enum_glob_use)]
                    #imports
                )*
                #[allow(unused_variables, clippy::let_unit_value, clippy::no_effect_underscore_binding)]
                fn __krs_scoped_binders() {
                    #(let #binders = ();)*
                }
            };
        }
    })
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
        krs_syntax::RuleSentence::Simplification(&attribute),
    )
}

pub(crate) fn alias(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> crate::Result<TokenStream> {
    krs_syntax::AliasAttribute::parse_tokens(attributes)?;
    if syn::parse2::<ItemFn>(item.clone()).is_ok() {
        return ordinary_rule(env, item, krs_syntax::RuleSentence::Alias);
    }
    // The misplaced helper is the invocation itself.
    Err(ExpandError::at_invocation(
        expand::ORPHAN_HELPER,
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
            return Err(requires_on_desugar(Some(name.ident.span())));
        }
        let rule = krs_syntax::RuleItem::parse_desugar_tokens(item, &desugar)?;
        return expand_ordinary_rule(
            env,
            &rule,
            krs_syntax::RuleSentence::Desugar(&desugar),
            None,
            &[],
        );
    }
    // The misplaced helper is the invocation itself.
    Err(ExpandError::at_invocation(
        expand::ORPHAN_HELPER,
        "`#[k::desugar]` on a production is a constructor helper; place `#[k::constructor(...)]` before it",
    ))
}

/// `#[k::requires]` on a desugar clause (KF-028).
/// `span` is the `#[k::requires]` attribute; `None` when it is the invocation being expanded.
fn requires_on_desugar(span: Option<Span>) -> ExpandError {
    let error = krs_diagnostic::ToDiagnostic::to_diagnostic(&krs_syntax::SyntaxError::new(
        krs_syntax::SyntaxErrorKind::InvalidRuleKey {
            reason: krs_syntax::REQUIRES_ON_DESUGAR_CLAUSE,
        },
        span.unwrap_or_else(Span::call_site),
    ));
    match span {
        Some(_) => ExpandError::from_diagnostic(error),
        None => ExpandError::at_invocation(error.code, error.message),
    }
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
    sentence: krs_syntax::RuleSentence<'_>,
) -> crate::Result<TokenStream> {
    let rule = if matches!(sentence, krs_syntax::RuleSentence::Equation(_)) {
        krs_syntax::RuleItem::parse_equation_tokens(item)?
    } else {
        krs_syntax::RuleItem::parse_tokens(item)?
    };
    expand_ordinary_rule(env, &rule, sentence, None, &[])
}

/// The error a rule's walk met, unless the rule's own sentence mistakes come
/// first ([`krs_syntax::RuleItem::check_sentence`]): a construct the position
/// table refused where it stands (`refused_by_position`) is told before them,
/// and any other error, a name or a sort the walk meets, after them.
fn sentence_first(
    rule: &krs_syntax::RuleItem,
    refused_by_position: bool,
    error: ExpandError,
) -> ExpandError {
    if refused_by_position {
        error
    } else {
        rule.check_sentence().map_or_else(Into::into, |()| error)
    }
}

/// What a rule fn that refuses `_`, an alias or an island for its whole subject should be
/// written as (decision D3): a fn's subject is its parameter, whose root names the constructor
/// the rule matches, and a rule for any term of a sort is a `for Sort` clause, whose root binds
/// the whole subject with a bare name and holds `_`, an alias or an island. The clause keeps
/// the fn's rule attribute (an `owise` rule for any term must stay `owise`, or it applies
/// everywhere first), its other KRS helpers, its subject and its result; a clause takes every
/// rule attribute but `anywhere` (`transition_rule`).
fn for_sort_clause_help(item: &TokenStream, attribute_tokens: &TokenStream) -> String {
    let parsed = syn::parse2::<ItemFn>(item.clone()).ok();
    let name = parsed.as_ref().map_or_else(
        || "name".to_owned(),
        |item| item.sig.ident.unraw().to_string(),
    );
    let subject = parsed
        .as_ref()
        .and_then(|item| match item.sig.inputs.last()? {
            FnArg::Typed(argument) => Some(argument),
            FnArg::Receiver(_) => None,
        });
    let sort = subject
        .and_then(|argument| term_sort_spelling(&argument.ty))
        .unwrap_or_else(|| "Sort".to_owned());
    let root = subject.map_or_else(|| "_".to_owned(), |argument| clause_root(&argument.pat));
    let result = parsed
        .as_ref()
        .and_then(|item| match item.block.stmts.as_slice() {
            [syn::Stmt::Expr(expression, None)] => Some(compact(expression)),
            _ => None,
        })
        .unwrap_or_else(|| "<result>".to_owned());
    let mut attributes = Vec::new();
    if !attribute_tokens.is_empty() {
        attributes.push(format!("#[k::rule({})] ", compact(attribute_tokens)));
    }
    for attribute in parsed.iter().flat_map(|item| &item.attrs) {
        if attribute
            .path()
            .segments
            .first()
            .is_some_and(|segment| segment.ident == "k")
        {
            attributes.push(format!("{} ", compact(attribute)));
        }
    }
    format!(
        "a rule for any term of a sort is a `for Sort` clause, whose root may be a bare name for the whole subject, `_`, an alias or an island: `k::rules! {{ for {sort}; {}{name}: {root} => {result}; }}`",
        attributes.concat(),
    )
}

/// The root of the clause [`for_sort_clause_help`] suggests: the fn's subject as written, with
/// or without `k::term![..]`, except for root alternatives one of which is `_`, which match any
/// term, as `_` alone does at a clause's root (each alternative of a root is a whole subject,
/// where `_` stands only below the root).
fn clause_root(subject: &Pat) -> String {
    fn wildcard_alternative(pattern: &Pat) -> bool {
        match pattern {
            Pat::Paren(paren) => wildcard_alternative(&paren.pat),
            Pat::Or(or) => or
                .cases
                .iter()
                .any(|case| matches!(case, Pat::Wild(_)) || wildcard_alternative(case)),
            _ => false,
        }
    }
    let payload = match subject {
        Pat::Macro(wrapper)
            if wrapper
                .mac
                .path
                .segments
                .last()
                .is_some_and(|last| last.ident == "term") =>
        {
            syn::parse::Parser::parse2(Pat::parse_multi, wrapper.mac.tokens.clone()).ok()
        }
        _ => None,
    };
    if wildcard_alternative(payload.as_ref().unwrap_or(subject)) {
        "_".to_owned()
    } else {
        compact(subject)
    }
}

/// `tokens` as an author writes them: no space around `::`, `.` or inside
/// brackets, none before `,` or `:`, and none before `(` after a name or
/// around a macro's `!`.
fn compact(tokens: &impl ToTokens) -> String {
    let spaced = tokens.to_token_stream().to_string();
    let text = spaced
        .replace(" :: ", "::")
        .replace(":: ", "::")
        .replace("# [", "#[")
        .replace(" ! [", "![")
        .replace(" ! (", "!(")
        .replace("! [", "![")
        .replace("! (", "!(")
        .replace(" : ", ": ")
        .replace(" ,", ",")
        .replace("( ", "(")
        .replace(" )", ")")
        .replace("[ ", "[")
        .replace(" ]", "]")
        .replace(" . ", ".");
    // A call's or a constructor's parentheses follow its name.
    let mut compacted = String::with_capacity(text.len());
    let mut characters = text.chars().peekable();
    while let Some(character) = characters.next() {
        let follows_name = compacted
            .chars()
            .last()
            .is_some_and(|last| last.is_alphanumeric() || last == '_' || last == '>');
        if character == ' ' && characters.peek() == Some(&'(') && follows_name {
            continue;
        }
        compacted.push(character);
    }
    compacted
}

/// The sort `Term<S>` names, when `S` is a plain path.
fn term_sort_spelling(ty: &syn::Type) -> Option<String> {
    let syn::Type::Path(path) = ty else {
        return None;
    };
    let segment = path.path.segments.last()?;
    let syn::PathArguments::AngleBracketed(arguments) = &segment.arguments else {
        return None;
    };
    let Some(syn::GenericArgument::Type(syn::Type::Path(sort))) = arguments.args.first() else {
        return None;
    };
    sort.path
        .segments
        .iter()
        .all(|segment| segment.arguments.is_none())
        .then(|| path_text(&sort.path))
}

/// Expands a rule fn whose sides are terms, as the sentence its attribute
/// makes it; `table` is what a `k::equations!` row shares with its table.
#[expect(
    clippy::too_many_lines,
    reason = "Rule lowering keeps the declaration context and both sides together."
)]
fn expand_ordinary_rule(
    env: &dyn MacroEnvironment,
    rule: &krs_syntax::RuleItem,
    sentence: krs_syntax::RuleSentence<'_>,
    table: Option<TableRow<'_>>,
    narrowings: &[krs_syntax::RuleNarrowing],
) -> crate::Result<TokenStream> {
    use krs_ir::SentenceKind;
    use krs_syntax::RuleSentence;
    let lexical_imports = table.map(|table| table.imports);
    // Only `#[k::rule]` and `#[k::context]` carry rule metadata; a
    // context's is its rule-attribute view.
    let no_metadata = krs_syntax::RuleAttribute::default();
    let context_metadata;
    let (mut equation, mut simplification, mut desugar) = (None, None, None);
    let (sentence_kind, sentence_name, attribute) = match sentence {
        RuleSentence::Transition(attribute) => (SentenceKind::Transition, "rule", attribute),
        RuleSentence::Context(context) => {
            context_metadata = context.rule_attribute(&rule.item().sig.ident);
            (SentenceKind::Context, "context", &context_metadata)
        }
        RuleSentence::Equation(attribute) => {
            equation = Some(attribute);
            (SentenceKind::Equation, "equation", &no_metadata)
        }
        RuleSentence::Simplification(attribute) => {
            simplification = Some(attribute);
            (SentenceKind::Simplification, "simplification", &no_metadata)
        }
        RuleSentence::Alias => (SentenceKind::Alias, "alias", &no_metadata),
        RuleSentence::Desugar(attribute) => {
            desugar = Some(attribute);
            (SentenceKind::Desugar, "desugar", &no_metadata)
        }
    };
    // A single-body rule (KF-011) is a transition that is not an anywhere
    // rule: its subject's `k::rewrite!` islands say what changes.
    if rule.result().is_none()
        && sentence_kind != krs_ir::SentenceKind::Context
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
        return Err(misplaced_fresh(Some(binder.name().span())));
    }
    if sentence_kind != krs_ir::SentenceKind::Transition
        && let Some(helper) = rule.existentials().attributes().first()
    {
        return Err(misplaced_existential(Some(syn::spanned::Spanned::span(
            helper.path(),
        ))));
    }
    let facade = env.facade_path()?;
    let descriptor = krs_syntax::RuleDescriptor::new(rule, sentence)?;
    let fallback = krs_syntax::TokenRange::for_tokens(rule.item())?;
    let provenance = host_provenance(env, &facade, fallback, descriptor.anchors());
    let ledger = KeyLedger::new(descriptor.anchors(), &fixed_rule_keys(sentence_kind));
    let nonce = expansion_nonce(env, sentence_name, &rule.item().sig.ident, fallback);
    let factory = format_ident!(
        "__krs_rule_descriptor_{nonce:016x}",
        span = Span::call_site()
    );
    let cfg = call_site_cfg_attributes(&rule.item().attrs)?;
    let predicate = predicate_rule(rule, sentence_kind)?;
    let parameter_key = format_ident!("__krs_rule_subject_sort_{nonce:016x}");
    let result_key = format_ident!("__krs_rule_result_sort_{nonce:016x}");
    let parameter_sort_path = rule.parameter().term_sort.sort();
    let result_sort_path = rule.result_sort().map(krs_syntax::TermSort::sort);
    // A predicate simplification's `ml::Predicate` types are no sorts: the
    // descriptor carries Bool placeholders, and rustc checks that both
    // types are the facade's `ml::Predicate` (KF-039). A single-body rule
    // (KF-011) has no result type.
    let (parameter_sort_type, result_sort_type, predicate_checks) = if let Some(table) = table {
        // A `k::equations!` row: the header names the function, whose
        // result sort is the equation's.
        let function = table.function;
        let sort = quote!(<#function as #facade::__KrsFunction>::Result);
        (sort.clone(), Some(sort), TokenStream::new())
    } else if predicate {
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
                &facade,
                parameter_sort_path,
                rule.parameter().term_sort.is_dynamic(),
            ),
            rule.result_sort()
                .zip(result_sort_path.as_ref())
                .map(|(sort, path)| sort_type_tokens(&facade, path, sort.is_dynamic())),
            TokenStream::new(),
        )
    };

    let original = rule.item();
    let attrs = &original.attrs;
    let visibility = &original.vis;
    let fn_token = original.sig.fn_token;
    let name_ident = &original.sig.ident;
    // A row's signature names the header's function through the table's
    // alias; every other rule's signature is its authored types.
    let (parameter_type, result_type) = match table {
        Some(table) => {
            let function = table.function;
            (quote!(#function), Some(quote!(#function)))
        }
        None => (
            rule.parameter().term_sort.ty().to_token_stream(),
            rule.result_sort().map(|sort| sort.ty().to_token_stream()),
        ),
    };
    let name = name_ident.unraw().to_string();
    let label = attribute
        .label()
        .map(|label| -> crate::Result<_> {
            Ok(DescriptorRuleLabel {
                key: ledger.define(attribute.label_key())?,
                name: label.value().clone(),
            })
        })
        .transpose()?;
    let parameter_sort_spelling = rule.parameter().term_sort.sort_token_text();
    let result_sort_spelling = rule
        .result_sort()
        .map(krs_syntax::TermSort::sort_token_text);
    let bindings = rule
        .parameter()
        .pattern
        .bindings()
        .iter()
        .map(|binding| binding.unraw().to_string())
        .collect::<Vec<_>>();
    let mut binding_checks = Vec::new();
    for binding in &rule.condition_bindings() {
        // A bit template's hidden binder is no name an author wrote or can
        // use, so tooling is not shown one at the template.
        if krs_syntax::is_hidden_binder(&binding.to_string()) {
            continue;
        }
        let generated = call_site_ident(binding)?;
        binding_checks.push(quote! {
            let #binding = ();
            let _ = &#generated;
        });
    }
    for narrowing in narrowings {
        let sort = narrowing.sort();
        binding_checks.push(quote! {
            let _: ::core::marker::PhantomData<#sort> = ::core::marker::PhantomData;
        });
    }
    // The result and the ensures condition also see the existentials; the
    // subject and requires never do (the parser rejects such a use).
    let binding_idents = rule.result_bindings();
    let form = match sentence {
        // A single-body rule (KF-011): its subject's `k::rewrite!` islands
        // say what changes.
        RuleSentence::Transition(_) if rule.result().is_none() => Form::LocalRule,
        RuleSentence::Transition(_) => Form::RuleFn,
        RuleSentence::Context(_) => Form::Context,
        RuleSentence::Equation(_) if lexical_imports.is_some() => Form::EquationTable,
        RuleSentence::Equation(_) => Form::EquationFn,
        RuleSentence::Simplification(_) => Form::Simplification,
        RuleSentence::Alias => Form::Alias,
        RuleSentence::Desugar(_) => Form::Desugar,
    };
    let mut term_builder = TermBuilder::new(&facade, &ledger, nonce, &cfg, &binding_idents, form)
        .with_lexical_imports(lexical_imports)
        .with_subject_head(table.map(|table| table.function));
    let mut slots = WireSlots::new(&facade);
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
    let (evaluation, evaluation_key_function) = evaluation_step(
        attribute,
        rule.existentials(),
        (&facade, &ledger, nonce, &cfg),
        &mut slots,
    )?;
    let subject_sort = WireSortReference {
        key: ledger.define(rule.parameter().type_key())?,
        target: WireTypeReference {
            slot: slots.type_slot(quote!(#facade::HostTypeKey(#parameter_key))),
            authored_path: parameter_sort_spelling,
        },
    };
    let result_sort = result_sort_spelling
        .map(|authored_path| -> crate::Result<_> {
            Ok(WireSortReference {
                key: ledger.define(rule.result_type_key())?,
                target: WireTypeReference {
                    slot: slots.type_slot(quote!(#facade::HostTypeKey(#result_key))),
                    authored_path,
                },
            })
        })
        .transpose()?;
    // The sentence's own mistakes (a single-body rule that marks no change,
    // a binder list that names other names than the subject binds) are told
    // after each construct of the subject, the result and the conditions is
    // judged where it stands, which the position table tells by spelling and position
    // alone, and instead of any other error the walk meets
    // (`sentence_first`), then once the conditions are walked.
    let (typed_bindings, binder_key_functions) =
        typed_binders(rule, (&facade, &ledger), nonce, &cfg, &mut slots)
            .map_err(|error| sentence_first(rule, false, error))?;
    let subject = term_builder
        .expand_wire(
            KeyedTerm::pattern(&rule.parameter().pattern, rule.subject_tree()),
            TermSide::Left,
            &mut slots,
        )
        .map_err(|error| sentence_first(rule, term_builder.refused_by_position(), error))?;
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
    let result = rule
        .result()
        .map(|result| term_builder.expand_wire(KeyedTerm::of(result), TermSide::Right, &mut slots))
        .transpose()
        .map_err(|error| sentence_first(rule, term_builder.refused_by_position(), error))?;
    let requires = if let Some(condition) = rule.requires() {
        let term = term_builder
            .expand_wire(
                KeyedTerm::of(condition.term()),
                TermSide::Requires,
                &mut slots,
            )
            .map_err(|error| sentence_first(rule, term_builder.refused_by_position(), error))?;
        Some(WireRuleCondition {
            key: ledger.define(condition.term().keys().payload())?,
            term,
        })
    } else {
        None
    };
    let ensures = ensures_condition(rule.existentials(), &mut term_builder, &mut slots)
        .map_err(|error| sentence_first(rule, term_builder.refused_by_position(), error))?;
    rule.check_sentence()?;
    let mut term_key_functions = term_builder.key_functions;
    term_key_functions.extend(existential_key_functions);
    term_key_functions.extend(fresh_key_functions);
    term_key_functions.extend(evaluation_key_function);
    let priority = attribute
        .transition_priority()
        .or_else(|| equation.and_then(krs_syntax::EquationAttribute::equation_priority))
        .map(|(_, value)| -> crate::Result<_> {
            Ok(DescriptorRulePriority {
                key: ledger.define(priority_key(attribute, equation))?,
                value,
            })
        })
        .transpose()?;
    let simplification = simplification
        .map(|simplification| -> crate::Result<_> {
            Ok(DescriptorSimplification {
                key: ledger.define(descriptor.marker_key())?,
                priority: simplification
                    .priority()
                    .map(|value| -> crate::Result<_> {
                        Ok(DescriptorSimplificationPriority {
                            key: ledger.define(simplification.priority_key())?,
                            value,
                        })
                    })
                    .transpose()?,
                restriction: match_restriction(&ledger, simplification.restriction())?,
            })
        })
        .transpose()?;
    let equation_attributes = equation
        .map(|equation| match_restriction(&ledger, equation.restriction()))
        .transpose()?
        .flatten()
        .map(|restriction| krs_ir::DescriptorEquationAttributes { restriction });
    let item_kind_variant = format_ident!("{}", sentence_kind.item_kind().stable_text());
    let item_kind = quote!(#facade::ItemKind::#item_kind_variant);
    let nondet = attribute
        .nondet()
        .map(|group| -> crate::Result<_> {
            Ok(krs_ir::DescriptorNondetGroup {
                key: ledger.define(attribute.nondet_key())?,
                name: group.unraw().to_string(),
            })
        })
        .transpose()?;
    let anywhere = attribute
        .anywhere()
        .map(|_| ledger.define(attribute.anywhere_key()))
        .transpose()?;
    let wire = WirePayload::StructuredRule(Box::new(WireStructuredRule {
        sentence_kind,
        label,
        requires,
        priority,
        nondet,
        anywhere,
        simplification,
        pattern_key: ledger.define(rule.parameter().pattern_key())?,
        typed_bindings,
        result_key: rule
            .result()
            .map(|result| ledger.define(result.keys().payload()))
            .transpose()?,
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
            .map(|variables| unbound_variables(&ledger, variables))
            .transpose()?,
        function_context,
        predicate,
        evaluation,
    }));
    ledger.finish()?;
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

/// The keys a rule descriptor's kind names by itself, which no wire field
/// carries: the rule's own declaration, and the clause keyword of an alias
/// or a desugar rule, which its sentence kind states.
fn fixed_rule_keys(sentence_kind: krs_ir::SentenceKind) -> Vec<krs_syntax::ProvenanceRole> {
    use krs_syntax::ProvenanceRole as Role;
    let mut fixed = vec![Role::RuleDeclaration];
    match sentence_kind {
        krs_ir::SentenceKind::Alias => fixed.push(Role::AliasClause),
        krs_ir::SentenceKind::Desugar => fixed.push(Role::DesugarClause),
        _ => {}
    }
    fixed
}

/// The key of the priority [`krs_syntax::RuleAttribute::transition_priority`]
/// or else [`krs_syntax::EquationAttribute::equation_priority`] reads: an
/// `owise` marker before a `priority = N` literal.
fn priority_key<'a>(
    attribute: &'a krs_syntax::RuleAttribute,
    equation: Option<&'a krs_syntax::EquationAttribute>,
) -> Option<&'a krs_ir::ProvenanceKey> {
    attribute
        .owise_key()
        .or_else(|| attribute.priority_key())
        .or_else(|| equation.and_then(|equation| equation.owise_key().or(equation.priority_key())))
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
/// reference, its bindings the subject does not bind, and its one-sided
/// cells.
fn function_context(
    rule: &krs_syntax::RuleItem,
    context: &krs_syntax::FunctionContext,
    term_builder: &mut TermBuilder<'_>,
    bindings: &[syn::Ident],
    expansion: FunctionContextExpansion<'_>,
    slots: &mut WireSlots,
) -> crate::Result<(krs_ir::wire::WireFunctionContext, ContextTokens)> {
    let FunctionContextExpansion { facade, nonce, cfg } = expansion;
    let configuration_type = context.configuration_type();
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
                let binder = &rule.binders()[index];
                let key_fn = format_ident!("__krs_rule_binder_sort_{nonce:016x}_{index}");
                // The binder's declared sort, which its typed binding
                // defines.
                krs_ir::ProtocolRuleBindingKind::Term {
                    sort: wire_sort_reference(
                        slots,
                        facade,
                        term_builder.ledger.refer(binder.sort_key())?,
                        &key_fn,
                        &binder.term_sort().sort_token_text(),
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
            krs_syntax::StateRuleBindingKind::InstancesFrame => {
                return Err(collection_placement(binding.name().span()));
            }
        };
        context_bindings.push(krs_ir::ProtocolRuleBinding {
            name: binding.name().unraw().to_string(),
            kind,
        });
    }
    let mut builder = StateRuleBuilder::new(
        facade,
        term_builder.ledger,
        nonce,
        cfg,
        bindings,
        krs_syntax::RuleSide::Left,
        Form::EquationFn,
    );
    builder.continue_subject(term_builder);
    let cells = builder.expand_cells(context.pattern(), configuration_type, slots)?;
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
        .map(wrapper_type_check)
        .collect::<Vec<_>>();
    checks.extend(consumed_state_island_import_checks(
        rule.item(),
        &[context.pattern()],
    ));
    let wire = krs_ir::wire::WireFunctionContext {
        key: term_builder.ledger.define(context.key())?,
        configuration: krs_ir::wire::WireConfigurationReference {
            key: term_builder.ledger.define(context.type_key())?,
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
    (facade, ledger): (&Path, &KeyLedger<'_>),
    nonce: u64,
    cfg: &[Attribute],
    slots: &mut WireSlots,
) -> crate::Result<(Vec<krs_ir::wire::WireTypedBinding>, Vec<TokenStream>)> {
    let mut bindings = Vec::new();
    let mut key_functions = Vec::new();
    for (index, binder) in rule.binders().iter().enumerate() {
        let sort = binder.term_sort();
        let path = sort.sort();
        let ty = sort_type_tokens(facade, path, sort.is_dynamic());
        let key_fn = format_ident!("__krs_rule_binder_sort_{nonce:016x}_{index}");
        key_functions.push(quote! {
            #(#cfg)*
            #[doc(hidden)]
            fn #key_fn() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<#ty>()
            }
        });
        bindings.push(krs_ir::wire::WireTypedBinding {
            key: ledger.define(binder.parameter_key())?,
            name: binder.name().unraw().to_string(),
            sort: wire_sort_reference(
                slots,
                facade,
                ledger.define(binder.sort_key())?,
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
    ledger: &KeyLedger<'_>,
    restriction: &krs_syntax::MatchRestriction,
) -> crate::Result<Option<krs_ir::DescriptorMatchRestriction>> {
    if restriction.is_empty() {
        return Ok(None);
    }
    let key = |restriction: Option<&krs_syntax::RestrictionKey>| {
        restriction
            .map(|restriction| -> crate::Result<_> {
                // The listed binders hold their keys in order.
                let variables = restriction
                    .variables()
                    .unwrap_or_default()
                    .iter()
                    .zip(
                        restriction
                            .variable_keys()
                            .iter()
                            .map(Some)
                            .chain(repeat(None)),
                    )
                    .map(|(variable, read)| {
                        Ok(krs_ir::DescriptorRestrictionVariable {
                            key: ledger.define(read)?,
                            name: variable.to_string(),
                        })
                    })
                    .collect::<crate::Result<_>>()?;
                Ok(krs_ir::DescriptorRestriction {
                    key: ledger.define(restriction.provenance_key())?,
                    variables,
                })
            })
            .transpose()
    };
    Ok(Some(krs_ir::DescriptorMatchRestriction {
        concrete: key(restriction.concrete())?,
        symbolic: key(restriction.symbolic())?,
        smt_lemma: restriction
            .smt_lemma()
            .map(|_| ledger.define(restriction.smt_lemma_key()))
            .transpose()?,
    }))
}

/// The descriptor form of `unbound_variables = [..]` (KF-046).
fn unbound_variables(
    ledger: &KeyLedger<'_>,
    unbound: &krs_syntax::UnboundVariables,
) -> crate::Result<krs_ir::DescriptorUnboundVariables> {
    // The keys of the `unbound_variables` identifier, then of each entry.
    let keys = unbound.provenance_keys();
    Ok(krs_ir::DescriptorUnboundVariables {
        key: ledger.define(keys.first())?,
        variables: unbound
            .variables()
            .iter()
            .zip(keys.iter().skip(1).map(Some).chain(repeat(None)))
            .map(|(variable, read)| {
                Ok(krs_ir::DescriptorUnboundVariable {
                    key: ledger.define(read)?,
                    name: match variable {
                        krs_syntax::UnboundVariable::Named(name) => name.to_string(),
                        krs_syntax::UnboundVariable::Wildcard(_) => {
                            krs_ir::DescriptorUnboundVariable::WILDCARD.to_owned()
                        }
                    },
                })
            })
            .collect::<crate::Result<_>>()?,
    })
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
    if entry == AttributeMacro::Requires
        && let Ok(mut shorthand) = syn::parse2::<krs_syntax::ShorthandItem>(item.clone())
        && let Some(index) = shorthand
            .attrs
            .iter()
            .position(|attribute| helper_entry(attribute.path()) == Some(AttributeMacro::Function))
    {
        // `#[k::requires]` above a function shorthand guards its equation.
        let function = shorthand.attrs.remove(index);
        let payload = match &function.meta {
            syn::Meta::List(list) => list.tokens.clone(),
            _ => TokenStream::new(),
        };
        let helper: Attribute = syn::parse_quote!(#[k::requires(#attributes)]);
        shorthand.attrs.insert(0, helper);
        return super::constructors::function(env, payload, shorthand.to_token_stream());
    }
    if entry == AttributeMacro::Requires {
        let mut function: ItemFn = syn::parse2(item)?;
        if function
            .attrs
            .iter()
            .any(|attribute| helper_entry(attribute.path()) == Some(AttributeMacro::Desugar))
        {
            // The misplaced `#[k::requires]` is the invocation itself.
            return Err(requires_on_desugar(None));
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
    // The misplaced helper is the invocation itself.
    Err(ExpandError::at_invocation(
        expand::ORPHAN_HELPER,
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
        // The misplaced helper is the invocation itself.
        Some((_, AttributeMacro::Claim | AttributeMacro::ContextAlias))
            if entry == AttributeMacro::Fresh =>
        {
            return Err(misplaced_fresh(None));
        }
        Some((
            _,
            AttributeMacro::Equation
            | AttributeMacro::Simplification
            | AttributeMacro::Alias
            | AttributeMacro::Desugar,
        )) => {
            return Err(if entry == AttributeMacro::Fresh {
                misplaced_fresh(None)
            } else {
                misplaced_existential(None)
            });
        }
        _ => {}
    }
    // The misplaced helper is the invocation itself.
    if entry == AttributeMacro::Fresh {
        return Err(ExpandError::at_invocation(
            expand::ORPHAN_HELPER,
            "`#[k::fresh]` is a rule helper; place `#[k::rule(...)]` before it",
        ));
    }
    Err(ExpandError::at_invocation(
        expand::ORPHAN_HELPER,
        format!(
            "`#[k::{name}]` is a rule or claim helper; place `#[k::rule(...)]` or `#[k::claim(...)]` before it"
        ),
    ))
}

/// `#[k::fresh]` on a sentence other than a transition step: an equation,
/// simplification, alias, claim, context, context alias, anywhere rule (KF-022), or
/// heat or cool rule (KF-014).
/// An optional or collection entry outside a configuration rule or claim.
pub(super) fn collection_placement(span: Span) -> ExpandError {
    ExpandError::new(
        expand::CELL_COLLECTION_PLACEMENT,
        span,
        "an equation's function context and a context alias read fixed cells only; optional `Some`/`None` and collection entries belong in rules and claims",
    )
}

/// `span` is the misplaced binder or helper; `None` when the helper is the invocation being
/// expanded.
pub(super) fn misplaced_fresh(span: Option<Span>) -> ExpandError {
    let message = "fresh values are drawn from the generated counter only by a transition step of the configuration; `#[k::fresh]` is not allowed on an equation, simplification, alias, claim, context, context alias, anywhere rule, or heat or cool rule";
    match span {
        Some(span) => ExpandError::new(expand::FRESH_PLACEMENT, span, message),
        None => ExpandError::at_invocation(expand::FRESH_PLACEMENT, message),
    }
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
        return Err(misplaced_fresh(Some(span)));
    }
    Ok(())
}

/// `#[k::exists]` or `#[k::ensures]` on an equation, simplification, or alias.
/// `span` is the misplaced binder or helper; `None` when the helper is the invocation being
/// expanded.
fn misplaced_existential(span: Option<Span>) -> ExpandError {
    let message = "existential results and ensures are allowed on claims and transition rules, not on equations, simplifications, or aliases";
    match span {
        Some(span) => ExpandError::new(expand::EXISTENTIAL_PLACEMENT, span, message),
        None => ExpandError::at_invocation(expand::EXISTENTIAL_PLACEMENT, message),
    }
}
