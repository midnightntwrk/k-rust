//! Attribute well-formedness checks ported from Java `CheckAtt` and `CheckBracket`.

use super::Sentence;
use crate::definition::{
    Attributes, LabelHead, ProductionCatalog, ProductionItem, ResolvedModule,
    SENTENCE_END_OFFSET_ATTRIBUTE, SENTENCE_START_OFFSET_ATTRIBUTE, SortCatalog, SortHead,
    match_rule_label,
};
use crate::diagnostic::{Diagnostic, DiagnosticCode};

const MODULE: u16 = 1 << 0;
const SYNTAX_SORT: u16 = 1 << 1;
const SORT_SYNONYM: u16 = 1 << 2;
const SYNTAX_LEXICAL: u16 = 1 << 3;
const PRODUCTION: u16 = 1 << 4;
const SYNTAX_ASSOCIATIVITY: u16 = 1 << 5;
const SYNTAX_PRIORITY: u16 = 1 << 6;
const CONTEXT_ALIAS: u16 = 1 << 7;
const CONTEXT: u16 = 1 << 8;
const RULE: u16 = 1 << 9;
const CLAIM: u16 = 1 << 10;
const CONFIGURATION: u16 = 1 << 11;
const BUBBLE: u16 = 1 << 12;
const ALL_SENTENCES: u16 = !MODULE;

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
        if let Some(label) = sentence.attributes().get_str("label")
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
    let mut diagnostics = Vec::new();
    for sentence in sentences {
        match sentence {
            Sentence::Rule { .. } => check_rule(sentence, productions, &mut diagnostics),
            Sentence::Production { .. } => {
                check_production(sentence, productions, sorts, &mut diagnostics)
            }
            _ => {}
        }
    }
    diagnostics
}

fn check_attribute_map(
    attributes: &Attributes,
    target: Target,
    sentence: Option<&Sentence>,
) -> Vec<Diagnostic> {
    let mut unknown = Vec::new();
    let mut restricted = Vec::new();
    for key in attributes.entries().keys() {
        let allowed = if let Some(allowed) = builtin_allowed_targets(key) {
            allowed
        } else if is_internal_attribute(key) {
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
    if attributes.get("non-executable").is_some() {
        let label = match_rule_label(rule);
        let is_function = productions
            .attributes_for(&LabelHead::from(&label))
            .is_some_and(|attributes| attributes.get("function").is_some());
        if !is_function {
            diagnostics.push(invalid_attribute(
                "non-executable attribute is only supported on function rules.",
                rule,
            ));
        }
    }
    if attributes.get("simplification").is_some() {
        for (attribute, message) in [
            (
                "owise",
                "owise attribute is not supported on simplification rules.",
            ),
            (
                "priority",
                "priority attribute is not supported on simplification rules.",
            ),
            (
                "anywhere",
                "anywhere attribute is not supported on simplification rules.",
            ),
        ] {
            if attributes.get(attribute).is_some() {
                diagnostics.push(invalid_attribute(message, rule));
            }
        }
    }
    if attributes.get("anywhere").is_some() && attributes.get("symbolic").is_some() {
        diagnostics.push(invalid_attribute(
            "anywhere attribute is not supported on symbolic rules.",
            rule,
        ));
    }
    if attributes.get("syntactic").is_some() && attributes.get("simplification").is_none() {
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
    let is_subsort = items.len() == 1 && nonterminals.len() == 1;

    check_hooked_sort_constructor(
        production,
        label,
        sort,
        attributes,
        is_subsort,
        productions,
        sorts,
        diagnostics,
    );
    check_binder(production, &nonterminals, sorts, diagnostics);
    check_format(production, items, nonterminals.len(), diagnostics);
    check_bracket(production, sort, &nonterminals, diagnostics);

    if attributes.get("functional").is_some() {
        diagnostics.push(deprecated_attribute(
            "The attribute 'functional' has been deprecated on symbols. Use the combination of attributes 'function' and 'total' instead.",
            production,
        ));
    }
    if attributes.get("total").is_some() && attributes.get("function").is_none() {
        diagnostics.push(invalid_attribute(
            "The attribute 'total' cannot be applied to a production which does not have the 'function' attribute.",
            production,
        ));
    }
    if attributes.get("terminator-symbol").is_some() && attributes.get("userList").is_none() {
        diagnostics.push(invalid_attribute(
            "The attribute 'terminator-symbol' cannot be applied to a production that does not declare a syntactic list.",
            production,
        ));
    }
    if attributes.get("latex").is_some() {
        diagnostics.push(deprecated_attribute(
            "The attribute 'latex' has been deprecated and all of its functionality has been removed. Using it will be an error in the future.",
            production,
        ));
    }
    check_symbol_attributes(production, label.is_some(), attributes, diagnostics);
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
    if sort.name == "KItem" {
        return;
    }
    let Some(sort_attributes) = sorts.attributes_for(&SortHead::from(sort)) else {
        return;
    };
    if sort_attributes.get("hook").is_none() {
        return;
    }
    let macro_label = label
        .as_ref()
        .is_some_and(|label| productions.macro_labels().contains(label));
    let constructor_exempt = ["function", "bracket", "token", "macro"]
        .iter()
        .any(|attribute| attributes.get(attribute).is_some())
        || macro_label;
    let k_exempt = sort.name == "K"
        && (label
            .as_ref()
            .is_some_and(|label| matches!(label.name.as_str(), "#EmptyK" | "#KSequence"))
            || is_subsort);
    let cell_collection_exempt = sort_attributes.get("cellCollection").is_some() && is_subsort;
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
    if production.attributes().get("binder").is_none() {
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
        .and_then(|attributes| attributes.get_str("hook"));
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
        .get_str("colors")
        .map(|colors| colors.split(',').count());
    let mut color_escapes = 0;
    if let Some(format) = attributes.get_str("format") {
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
    } else if attributes.get("token").is_none()
        && !matches!(
            production,
            Sentence::Production { sort, .. }
                if matches!(sort.name.as_str(), "#Layout" | "#LineMarker")
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
    if production.attributes().get("bracket").is_some()
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
    attributes: &Attributes,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let klabel = attributes.get_str("klabel");
    let symbol = attributes.get_str("symbol");
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
            None => diagnostics.push(deprecated_attribute(
                format!(
                    "Attribute `klabel(_)` is deprecated. Either remove `klabel({klabel})`, or replace it by `symbol({klabel})`."
                ),
                production,
            )),
        }
        if attributes.get("overload").is_some() {
            diagnostics.push(invalid_attribute(
                format!(
                    "The attributes `klabel` and `overload` may not occur together. Either remove `klabel({klabel})`, or replace it by `symbol({klabel})`"
                ),
                production,
            ));
        }
    }
    if !has_label && attributes.get("overload").is_some() {
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

pub(crate) fn is_builtin_attribute(key: &str) -> bool {
    builtin_allowed_targets(key).is_some()
}

fn builtin_allowed_targets(key: &str) -> Option<u16> {
    let allowed = match key {
        "group" | "label" => ALL_SENTENCES,
        "all-path" | "one-path" => CLAIM | MODULE,
        "concrete" | "symbolic" => MODULE | PRODUCTION | RULE,
        "cellCollection" | "hook" | "token" => PRODUCTION | SYNTAX_SORT,
        "comm" | "initializer" => PRODUCTION | RULE,
        "priority" | "result" => CONTEXT | CONTEXT_ALIAS | PRODUCTION | RULE,
        "private" | "public" => MODULE | PRODUCTION,
        "stream" => PRODUCTION | RULE,
        "unboundVariables" => CONTEXT | CONTEXT_ALIAS | PRODUCTION | RULE | CLAIM,
        "circularity" | "depends" | "trusted" => CLAIM,
        "context" => CONTEXT_ALIAS,
        "cool"
        | "heat"
        | "non-executable"
        | "owise"
        | "preserves-definedness"
        | "simplification"
        | "smt-lemma"
        | "syntactic"
        | "anywhere" => RULE,
        "haskell" | "not-lr1" => MODULE,
        "locations" => SYNTAX_SORT,
        "alias" | "alias-rec" | "applyPriority" | "assoc" | "avoid" | "bag" | "binder"
        | "bracket" | "cell" | "cellName" | "color" | "colors" | "constructor" | "deprecated"
        | "element" | "exit" | "format" | "freshGenerator" | "function" | "functional"
        | "hybrid" | "idem" | "impure" | "index" | "initial" | "injective" | "internal"
        | "klabel" | "latex" | "left" | "macro" | "macro-rec" | "maincell" | "memo"
        | "mlBinder" | "mlOp" | "multiplicity" | "non-assoc" | "no-evaluators" | "overload"
        | "parser" | "prec" | "prefer" | "returnsUnit" | "right" | "seqstrict" | "smtlib"
        | "smt-hook" | "strict" | "symbol" | "terminator-symbol" | "total" | "type" | "unit"
        | "unparseAvoid" | "unused" | "update" | "wrapElement" => PRODUCTION,
        _ => return None,
    };
    Some(allowed)
}

fn is_internal_attribute(key: &str) -> bool {
    matches!(
        key,
        "anonymous"
            | "bracketLabel"
            | "cellFragment"
            | "cellOptAbsent"
            | "cellSort"
            | "concat"
            | "contentStartColumn"
            | "contentStartLine"
            | "contentStartOffset"
            | "cool-like"
            | "denormal"
            | "digest"
            | "dummy_cell"
            | "filterElement"
            | "fresh"
            | "hasDomainValues"
            | "left"
            | "nat"
            | "notInjection"
            | "not-lr1-modules"
            | "originalPrd"
            | "predicate"
            | "prettyPrintWithSortAnnotation"
            | "priorities"
            | "org.kframework.definition.Production"
            | "projection"
            | "recordPrd"
            | "recordPrd-zero"
            | "recordPrd-one"
            | "recordPrd-main"
            | "recordPrd-empty"
            | "recordPrd-subsort"
            | "recordPrd-repeat"
            | "recordPrd-item"
            | "refreshed"
            | "right"
            | "smt-prelude"
            | "org.kframework.kore.Sort"
            | "sortParams"
            | "org.kframework.attributes.Source"
            | "org.kframework.attributes.SourceId"
            | "org.krust.provenance.Origin"
            | SENTENCE_START_OFFSET_ATTRIBUTE
            | SENTENCE_END_OFFSET_ATTRIBUTE
            | "org.kframework.attributes.Location"
            | "symbol-overload"
            | "syntaxModule"
            | "temporary-cell-sort-decl"
            | "terminals"
            | "UNIQUE_ID"
            | "userList"
            | "userListTerminator"
            | "withConfig"
    )
}
