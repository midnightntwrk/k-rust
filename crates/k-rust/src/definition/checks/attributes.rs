//! This definition check traverses module sentences and terms linearly; callers supply derived catalogs and no dedicated counter is recorded.
//!
//! Attribute well-formedness checks: which attributes each kind of sentence may carry, and what
//! their values and the productions that carry them must satisfy (including `bracket`).

use super::Sentence;
use crate::definition::AttributeKey;
use crate::definition::production_kind::ResultSorts;
use crate::definition::{
    Attributes, LabelHead, OverloadOrder, ProductionCatalog, ProductionItem, ResolvedModule,
    SortCatalog, SortHead,
    attribute_keys::{
        BUBBLE, CLAIM, CONFIGURATION, CONTEXT, CONTEXT_ALIAS, MODULE, PRODUCTION, RULE,
        SORT_SYNONYM, SYNTAX_ASSOCIATIVITY, SYNTAX_LEXICAL, SYNTAX_PRIORITY, SYNTAX_SORT,
        builtin_key, is_internal_key,
    },
    match_rule_label, sentence_equivalent,
};
use crate::diagnostic::{Diagnostic, DiagnosticCode};
use crate::kast::{FrontendSort, InternalLabel, Term};
use crate::names::BuiltinSort;
use k_rust_kore::names::{OWISE_RULE_PRIORITY, rule_priority};

#[derive(Clone, Copy)]
struct Target {
    bit: u16,
    name: &'static str,
}

/// Validate module and local-sentence attribute names and placement.
pub fn check_attributes(module: &ResolvedModule) -> Vec<Diagnostic> {
    let mut diagnostics = check_attribute_map(
        &module.attributes,
        Target {
            bit: MODULE,
            name: "Module",
        },
        None,
    );
    for sentence in &module.local_sentences {
        let target = sentence_target(sentence);
        diagnostics.extend(check_attribute_map(
            sentence.attributes(),
            target,
            Some(sentence),
        ));
        if let Some(label) = sentence.attributes().string(AttributeKey::Label)
            && (label.contains('`') || label.chars().any(char::is_whitespace))
        {
            diagnostics.push(Diagnostic::error(
                DiagnosticCode::InvalidAttribute,
                format!("Label '{label}' cannot contain whitespace or backticks."),
                sentence,
            ));
        }
    }
    diagnostics
}

/// Validate semantic interactions between rule and production attributes.
pub fn check_attribute_semantics(
    sentences: &[&Sentence],
    productions: &ProductionCatalog<'_>,
    sorts: &SortCatalog<'_>,
) -> Vec<Diagnostic> {
    check_attribute_semantics_with_overloads(sentences, productions, sorts, None)
}

pub(super) fn check_attribute_semantics_with_overloads(
    sentences: &[&Sentence],
    productions: &ProductionCatalog<'_>,
    sorts: &SortCatalog<'_>,
    overloads: Option<&OverloadOrder<'_>>,
) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for sentence in sentences {
        match sentence {
            Sentence::Rule { .. } => check_rule(sentence, productions, &mut diagnostics),
            Sentence::Production { .. } => {
                check_production(sentence, productions, sorts, overloads, &mut diagnostics)
            }
            Sentence::SyntaxSort { .. }
            | Sentence::SortSynonym { .. }
            | Sentence::SyntaxLexical { .. }
            | Sentence::SyntaxAssociativity { .. }
            | Sentence::SyntaxPriority { .. }
            | Sentence::ContextAlias { .. }
            | Sentence::Context { .. }
            | Sentence::Claim { .. }
            | Sentence::Configuration { .. }
            | Sentence::Bubble { .. } => {}
        }
        check_rule_ranks(sentence, productions, &mut diagnostics);
    }
    diagnostics
}

/// Reject a `priority` or `simplification` value that names no rank of the rules it ranks.
///
/// A rule's priority ranks it among the rules of its group: it applies only where no rule of a
/// smaller rank does. A rank is a natural number that the compiled definition carries as the
/// attribute's string, and the backend reads it in a byte (`k_rust_kore::names::rule_priority`):
/// a decimal natural number below the rank of `owise` rules (255), or the empty string for the
/// default. Any other value (`-1`, `abc`, `300`) ranks nothing the definition can run, so it is
/// an error at the sentence rather than when the backend loads the definition. The `owise` rank
/// itself is no explicit rank: an `owise` rule must come strictly after every rule it yields to,
/// and a rule of the same rank would be its alternative instead.
///
/// The value is judged where it ranks emitted rules: on a rule, a context and a context alias
/// (whose generated rules carry it), and on a strict production (whose strictness rules carry
/// it). A macro or alias rule is exempt: its priority orders macro expansion, which compilation
/// performs itself over any integer, and the rule is not among the rules the backend runs.
fn check_rule_ranks(
    sentence: &Sentence,
    productions: &ProductionCatalog<'_>,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let attributes = sentence.attributes();
    let ranked = match sentence {
        Sentence::Rule { .. } => !is_macro_rule(sentence, productions),
        Sentence::Context { .. } | Sentence::ContextAlias { .. } => true,
        Sentence::Production { .. } => {
            attributes.has_any(&[AttributeKey::Strict, AttributeKey::Seqstrict])
        }
        Sentence::SyntaxSort { .. }
        | Sentence::SortSynonym { .. }
        | Sentence::SyntaxLexical { .. }
        | Sentence::SyntaxAssociativity { .. }
        | Sentence::SyntaxPriority { .. }
        | Sentence::Claim { .. }
        | Sentence::Configuration { .. }
        | Sentence::Bubble { .. } => false,
    };
    if !ranked {
        return;
    }
    for key in [AttributeKey::Priority, AttributeKey::Simplification] {
        let Some(value) = attributes.value(key) else {
            continue;
        };
        let value = crate::kompile::attribute_value_string(key.as_str(), value);
        if rule_priority(&value).is_none() {
            diagnostics.push(invalid_attribute(
                format!(
                    "Invalid value for {key} attribute: {value}. A rule priority is a natural number from 0 to {max}; {owise} is the rank of owise rules.",
                    key = key.as_str(),
                    max = OWISE_RULE_PRIORITY - 1,
                    owise = OWISE_RULE_PRIORITY,
                ),
                sentence,
            ));
        }
    }
}

/// Whether `rule` defines a macro or an alias: it is not a simplification and the production its
/// left-hand side applies is macro-like.
fn is_macro_rule(rule: &Sentence, productions: &ProductionCatalog<'_>) -> bool {
    !rule.attributes().has(AttributeKey::Simplification)
        && productions
            .attributes_for(&LabelHead::from(&match_rule_label(rule)))
            .is_some_and(|attributes| attributes.has_any(&AttributeKey::MACRO_LIKE))
}

fn check_attribute_map(
    attributes: &Attributes,
    target: Target,
    sentence: Option<&Sentence>,
) -> Vec<Diagnostic> {
    let mut unknown = Vec::new();
    let mut restricted = Vec::new();
    for key in attributes.semantic_entries().keys() {
        let allowed = if let Some(key) = builtin_key(key) {
            key.targets
        } else if is_internal_key(key) {
            continue;
        } else {
            unknown.push(key.clone());
            continue;
        };
        if allowed & target.bit == 0 {
            restricted.push(key.clone());
        }
    }
    let mut diagnostics = Vec::new();
    if !unknown.is_empty() {
        diagnostics.push(attribute_diagnostic(
            DiagnosticCode::UnrecognizedAttribute,
            format!("Unrecognized attributes: [{}]", unknown.join(", ")),
            attributes,
            sentence,
        ));
    }
    if !restricted.is_empty() {
        diagnostics.push(attribute_diagnostic(
            DiagnosticCode::InvalidAttribute,
            format!(
                "{} cannot have the following attributes: [{}]",
                target.name,
                restricted.join(", ")
            ),
            attributes,
            sentence,
        ));
    }
    diagnostics
}

fn attribute_diagnostic(
    code: DiagnosticCode,
    message: String,
    attributes: &Attributes,
    sentence: Option<&Sentence>,
) -> Diagnostic {
    match sentence {
        Some(sentence) => Diagnostic::error(code, message, sentence),
        None => Diagnostic::error_at(code, message, attributes),
    }
}

fn check_rule(
    rule: &Sentence,
    productions: &ProductionCatalog<'_>,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let attributes = rule.attributes();
    if attributes.has(AttributeKey::NonExecutable) {
        let label = match_rule_label(rule);
        let is_function = productions
            .attributes_for(&LabelHead::from(&label))
            .is_some_and(|attributes| attributes.has(AttributeKey::Function));
        if !is_function {
            diagnostics.push(invalid_attribute(
                "non-executable attribute is only supported on function rules.",
                rule,
            ));
        }
    }
    if attributes.has(AttributeKey::Simplification) {
        for (attribute, message) in [
            (
                AttributeKey::Owise,
                "owise attribute is not supported on simplification rules.",
            ),
            (
                AttributeKey::Priority,
                "priority attribute is not supported on simplification rules.",
            ),
            (
                AttributeKey::Anywhere,
                "anywhere attribute is not supported on simplification rules.",
            ),
        ] {
            if attributes.has(attribute) {
                diagnostics.push(invalid_attribute(message, rule));
            }
        }
    }
    // `owise` is itself a priority (the rule applies only where no rule of its group with a
    // higher priority does), so with `priority` the rule states its rank twice: two different
    // ranks contradict each other, and equal ones say nothing the single attribute does not.
    // Every consumer reads one rank per rule, so the pair is rejected whatever the value. On a
    // simplification rule both are already rejected above.
    if attributes.has(AttributeKey::Owise)
        && attributes.has(AttributeKey::Priority)
        && !attributes.has(AttributeKey::Simplification)
    {
        diagnostics.push(invalid_attribute(
            "owise attribute cannot be combined with a priority attribute: owise already gives the rule its priority.",
            rule,
        ));
    }
    if attributes.has(AttributeKey::Anywhere) && attributes.has(AttributeKey::Symbolic) {
        diagnostics.push(invalid_attribute(
            "anywhere attribute is not supported on symbolic rules.",
            rule,
        ));
    }
    if attributes.has(AttributeKey::Anywhere) {
        check_anywhere_context(rule, diagnostics);
    }
    if attributes.has(AttributeKey::Syntactic) && !attributes.has(AttributeKey::Simplification) {
        diagnostics.push(invalid_attribute(
            "syntactic attribute is only supported on simplification rules.",
            rule,
        ));
    }
}

fn check_production(
    production: &Sentence,
    productions: &ProductionCatalog<'_>,
    sorts: &SortCatalog<'_>,
    overloads: Option<&OverloadOrder<'_>>,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let Sentence::Production {
        label,
        sort,
        items,
        attributes,
        ..
    } = production
    else {
        unreachable!()
    };
    let nonterminals = items
        .iter()
        .filter_map(|item| match item {
            ProductionItem::NonTerminal { sort, .. } => Some(sort),
            ProductionItem::RegexTerminal { .. } | ProductionItem::Terminal(_) => None,
        })
        .collect::<Vec<_>>();
    check_hooked_sort_constructor(
        production,
        label,
        sort,
        attributes,
        is_subsort(items),
        productions,
        sorts,
        diagnostics,
    );
    check_binder(production, &nonterminals, sorts, diagnostics);
    check_format(production, items, nonterminals.len(), diagnostics);
    check_bracket(production, sort, &nonterminals, diagnostics);

    if attributes.has(AttributeKey::Functional) {
        diagnostics.push(deprecated_attribute(
            "The attribute 'functional' has been deprecated on symbols. Use the combination of attributes 'function' and 'total' instead.",
            production,
        ));
    }
    if attributes.has(AttributeKey::Total) && !attributes.has(AttributeKey::Function) {
        diagnostics.push(invalid_attribute(
            "The attribute 'total' cannot be applied to a production which does not have the 'function' attribute.",
            production,
        ));
    }
    if attributes.has(AttributeKey::TerminatorSymbol) && !attributes.has(AttributeKey::UserList) {
        diagnostics.push(invalid_attribute(
            "The attribute 'terminator-symbol' cannot be applied to a production that does not declare a syntactic list.",
            production,
        ));
    }
    if attributes.has(AttributeKey::Latex) {
        diagnostics.push(deprecated_attribute(
            "The attribute 'latex' has been deprecated and all of its functionality has been removed. Using it will be an error in the future.",
            production,
        ));
    }
    // Invariant: no entry of `overloads.productions()` before `candidate` is both equivalent to `production` and a member of `overloads.order()`; the scan consumes one production per step and stops at the first match.
    let marks_overload = overloads.is_some_and(|overloads| {
        overloads.productions().any(|(id, candidate)| {
            sentence_equivalent(candidate, production) && overloads.order().contains(&id)
        })
    });
    check_symbol_attributes(
        production,
        label.is_some(),
        marks_overload,
        attributes,
        diagnostics,
    );
}

/// The hooked-sort constructor check of [`check_attribute_semantics`] alone, for judging
/// productions against a view other than their own module's.
pub(super) fn check_hooked_sort_constructors(
    sentences: &[&Sentence],
    productions: &ProductionCatalog<'_>,
    sorts: &SortCatalog<'_>,
) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for production in sentences {
        let Sentence::Production {
            label,
            sort,
            items,
            attributes,
            ..
        } = production
        else {
            continue;
        };
        check_hooked_sort_constructor(
            production,
            label,
            sort,
            attributes,
            is_subsort(items),
            productions,
            sorts,
            &mut diagnostics,
        );
    }
    diagnostics
}

/// Whether a production's items are one nonterminal: a subsort declaration.
fn is_subsort(items: &[ProductionItem]) -> bool {
    matches!(items, [ProductionItem::NonTerminal { .. }])
}

#[allow(clippy::too_many_arguments)]
fn check_hooked_sort_constructor(
    production: &Sentence,
    label: &Option<crate::kast::Label>,
    sort: &crate::kast::Sort,
    attributes: &Attributes,
    is_subsort: bool,
    productions: &ProductionCatalog<'_>,
    sorts: &SortCatalog<'_>,
    diagnostics: &mut Vec<Diagnostic>,
) {
    match ResultSorts::of(production) {
        ResultSorts::Every => return,
        ResultSorts::Head(_) => {}
    }
    if sort.name == BuiltinSort::KItem.k_name() {
        return;
    }
    let Some(sort_attributes) = sorts.attributes_for(&SortHead::from(sort)) else {
        return;
    };
    if !sort_attributes.has(AttributeKey::Hook) {
        return;
    }
    let macro_label = label
        .as_ref()
        .is_some_and(|label| productions.macro_labels().contains(&LabelHead::from(label)));
    let constructor_exempt = attributes.has_any(&[
        AttributeKey::Function,
        AttributeKey::Bracket,
        AttributeKey::Token,
        AttributeKey::Macro,
    ]) || macro_label;
    let k_exempt = sort.name == BuiltinSort::K.k_name()
        && (label.as_ref().is_some_and(|label| {
            [InternalLabel::EmptyK, InternalLabel::KSequence]
                .iter()
                .any(|internal| label.is(*internal))
        }) || is_subsort);
    let cell_collection_exempt = sort_attributes.has(AttributeKey::CellCollection) && is_subsort;
    if !constructor_exempt && !k_exempt && !cell_collection_exempt {
        diagnostics.push(invalid_attribute(
            format!("Cannot add new constructors to hooked sort {sort}"),
            production,
        ));
    }
}

fn check_binder(
    production: &Sentence,
    nonterminals: &[&crate::kast::Sort],
    sorts: &SortCatalog<'_>,
    diagnostics: &mut Vec<Diagnostic>,
) {
    if !production.attributes().has(AttributeKey::Binder) {
        return;
    }
    if nonterminals.len() < 2 {
        diagnostics.push(invalid_attribute(
            "Binder productions must have at least two nonterminals.",
            production,
        ));
        return;
    }
    let first_hook = sorts
        .attributes_for(&SortHead::from(nonterminals[0]))
        .and_then(|attributes| attributes.string(AttributeKey::Hook));
    if first_hook != Some("KVAR.KVar") {
        diagnostics.push(invalid_attribute(
            "First child of binder must have a sort with the 'KVAR.KVar' hook attribute.",
            production,
        ));
    }
}

fn check_format(
    production: &Sentence,
    items: &[ProductionItem],
    nonterminal_count: usize,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let attributes = production.attributes();
    let colors = attributes
        .string(AttributeKey::Colors)
        .map(|colors| colors.split(',').count());
    let mut color_escapes = 0;
    if let Some(format) = attributes.string(AttributeKey::Format) {
        let bytes = format.as_bytes();
        let mut index = 0;
        while index < bytes.len() {
            if bytes[index] != b'%' {
                index += 1;
                continue;
            }
            index += 1;
            if index == bytes.len() {
                diagnostics.push(invalid_attribute(
                    "Invalid format attribute: unfinished escape sequence.",
                    production,
                ));
                break;
            }
            match bytes[index] {
                b'c' => color_escapes += 1,
                b'0'..=b'9' => {
                    let start = index;
                    index += 1;
                    while index < bytes.len() && bytes[index].is_ascii_digit() {
                        index += 1;
                    }
                    let digits = std::str::from_utf8(&bytes[start..index]).expect("ASCII digits");
                    let item = digits.parse::<usize>().unwrap_or(usize::MAX);
                    if item == 0 || item > items.len() {
                        diagnostics.push(invalid_attribute(
                            format!(
                                "Invalid format escape sequence '%{digits}'. Expected a number between 1 and {}",
                                items.len()
                            ),
                            production,
                        ));
                    } else if matches!(items[item - 1], ProductionItem::RegexTerminal { .. }) {
                        diagnostics.push(invalid_attribute(
                            format!(
                                "Invalid format escape sequence referring to regular expression terminal '{:?}'.",
                                items[item - 1]
                            ),
                            production,
                        ));
                    }
                    continue;
                }
                _ => {}
            }
            index += 1;
        }
    } else if !attributes.has(AttributeKey::Token)
        && !matches!(
            production,
            Sentence::Production { sort, .. }
                if [FrontendSort::Layout, FrontendSort::LineMarker]
                    .iter()
                    .any(|frontend| sort.is_frontend(*frontend))
        )
    {
        for _ in items
            .iter()
            .filter(|item| matches!(item, ProductionItem::RegexTerminal { .. }))
        {
            let message = if items.len() == 1 {
                "Expected format attribute on production with regular expression terminal. Did you forget the 'token' attribute?"
            } else {
                "Expected format attribute on production with regular expression terminal."
            };
            diagnostics.push(invalid_attribute(message, production));
        }
    }
    if let Some(colors) = colors {
        let expected = color_escapes + items.len() - nonterminal_count;
        if colors != expected {
            diagnostics.push(invalid_attribute(
                format!(
                    "Invalid colors attribute: expected {expected} colors, found {colors} colors instead."
                ),
                production,
            ));
        }
    }
}

fn check_bracket(
    production: &Sentence,
    result: &crate::kast::Sort,
    nonterminals: &[&crate::kast::Sort],
    diagnostics: &mut Vec<Diagnostic>,
) {
    if production.attributes().has(AttributeKey::Bracket)
        && (nonterminals.len() != 1 || nonterminals[0] != result)
    {
        diagnostics.push(Diagnostic::error(
            DiagnosticCode::InvalidBracketProduction,
            "bracket productions should have exactly one non-terminal of the same sort as the production.",
            production,
        ));
    }
}

fn check_symbol_attributes(
    production: &Sentence,
    has_label: bool,
    marks_overload: bool,
    attributes: &Attributes,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let klabel = attributes.string(AttributeKey::Klabel);
    let symbol = attributes.string(AttributeKey::Symbol);
    if let Some(klabel) = klabel {
        match symbol {
            Some("") => diagnostics.push(deprecated_attribute(
                format!(
                    "The zero-argument form of `symbol` is deprecated. Replace `klabel({klabel}), symbol` by `symbol({klabel})`."
                ),
                production,
            )),
            Some(_) => diagnostics.push(invalid_attribute(
                "The 1-argument form of the `symbol(_)` attribute cannot be combined with `klabel(_)`.",
                production,
            )),
            None if marks_overload => diagnostics.push(deprecated_attribute(
                format!(
                    "Attribute `klabel({klabel}) is deprecated, but marks an overload. Add `overload({klabel})`."
                ),
                production,
            )),
            None => diagnostics.push(deprecated_attribute(
                format!(
                    "Attribute `klabel(_)` is deprecated. Either remove `klabel({klabel})`, or replace it by `symbol({klabel})`."
                ),
                production,
            )),
        }
        if attributes.has(AttributeKey::Overload) {
            diagnostics.push(invalid_attribute(
                format!(
                    "The attributes `klabel` and `overload` may not occur together. Either remove `klabel({klabel})`, or replace it by `symbol({klabel})`"
                ),
                production,
            ));
        }
    }
    if !has_label && attributes.has(AttributeKey::Overload) {
        diagnostics.push(invalid_attribute(
            "Production would not be a KORE symbol and therefore cannot be overloaded. Add a `symbol(_)` attribute to the production.",
            production,
        ));
    }
    if symbol == Some("") && klabel.is_none() {
        diagnostics.push(deprecated_attribute(
            "Zero-argument `symbol` attribute used without a corresponding `klabel(_)`. Either remove `symbol`, or supply an argument.",
            production,
        ));
    }
}

/// Reject an `anywhere` rule whose left-hand side is not a term.
///
/// An anywhere rule is an equation on the head of its left-hand side: it applies wherever that
/// term occurs, inside any context, so it sees nothing of the configuration beyond the term. A
/// left-hand side made of several cells is a fragment of their parent cell's children rather
/// than a term with a head, so it occurs at no position on its own, and has no lowering as such
/// an equation. The parent cell written around them is such a term. (A fresh variable needs the
/// configuration too; `fresh_variables` rejects it in every sentence applied without one.)
fn check_anywhere_context(rule: &Sentence, diagnostics: &mut Vec<Diagnostic>) {
    let Sentence::Rule { body, .. } = rule else {
        return;
    };
    let mut left = body.unannotated();
    if let Term::Rewrite {
        left: rewritten, ..
    } = left
    {
        left = rewritten.unannotated();
    }
    if let Term::Apply { label, arguments } = left
        && label.is(InternalLabel::Cells)
        && arguments.len() > 1
    {
        diagnostics.push(invalid_attribute(
            "An anywhere rule must rewrite a single term, but the left-hand side of this rule is several cells; write their parent cell around them.",
            rule,
        ));
    }
}

fn invalid_attribute(message: impl Into<String>, sentence: &Sentence) -> Diagnostic {
    Diagnostic::error(DiagnosticCode::InvalidAttribute, message, sentence)
}

fn deprecated_attribute(message: impl Into<String>, sentence: &Sentence) -> Diagnostic {
    Diagnostic::warning(DiagnosticCode::DeprecatedAttribute, message, sentence)
}

fn sentence_target(sentence: &Sentence) -> Target {
    match sentence {
        Sentence::SyntaxSort { .. } => Target {
            bit: SYNTAX_SORT,
            name: "SyntaxSort",
        },
        Sentence::SortSynonym { .. } => Target {
            bit: SORT_SYNONYM,
            name: "SortSynonym",
        },
        Sentence::SyntaxLexical { .. } => Target {
            bit: SYNTAX_LEXICAL,
            name: "SyntaxLexical",
        },
        Sentence::Production { .. } => Target {
            bit: PRODUCTION,
            name: "Production",
        },
        Sentence::SyntaxAssociativity { .. } => Target {
            bit: SYNTAX_ASSOCIATIVITY,
            name: "SyntaxAssociativity",
        },
        Sentence::SyntaxPriority { .. } => Target {
            bit: SYNTAX_PRIORITY,
            name: "SyntaxPriority",
        },
        Sentence::ContextAlias { .. } => Target {
            bit: CONTEXT_ALIAS,
            name: "ContextAlias",
        },
        Sentence::Context { .. } => Target {
            bit: CONTEXT,
            name: "Context",
        },
        Sentence::Rule { .. } => Target {
            bit: RULE,
            name: "Rule",
        },
        Sentence::Claim { .. } => Target {
            bit: CLAIM,
            name: "Claim",
        },
        Sentence::Configuration { .. } => Target {
            bit: CONFIGURATION,
            name: "Configuration",
        },
        Sentence::Bubble { .. } => Target {
            bit: BUBBLE,
            name: "Bubble",
        },
    }
}
