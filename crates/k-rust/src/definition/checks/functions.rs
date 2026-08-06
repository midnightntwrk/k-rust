//! Function-symbol matching checks ported from Java `CheckFunctions`.

use std::collections::BTreeSet;

use super::Sentence;
use super::term_position::{TermPosition, positioned_children};
use crate::definition::{LabelHead, ProductionCatalog, ProductionItem, SortCatalog};
use crate::diagnostic::{Diagnostic, DiagnosticCode};
use crate::kast::Term;

const COLLECTION_HOOKS: [&str; 13] = [
    "LIST.element",
    "LIST.concat",
    "LIST.unit",
    "LIST.update",
    "SET.element",
    "SET.concat",
    "SET.unit",
    "MAP.element",
    "MAP.concat",
    "MAP.unit",
    "BAG.element",
    "BAG.concat",
    "BAG.unit",
];

const FIXED_INTERNAL_LABELS: [&str; 12] = [
    "#cells",
    "#dots",
    "#noDots",
    "#Or",
    "#fun2",
    "#fun3",
    "#let",
    "#withConfig",
    "<generatedTop>",
    "#SemanticCastToBag",
    "_:=K_",
    "_:/=K_",
];

pub fn check_functions(
    sentences: &[&Sentence],
    productions: &ProductionCatalog<'_>,
    sorts: &SortCatalog<'_>,
) -> Vec<Diagnostic> {
    let internal_labels = internal_labels(productions, sorts);
    let mut diagnostics = Vec::new();
    for sentence in sentences {
        let body = match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get("simplification").is_none() => body,
            Sentence::Context { body, .. } | Sentence::ContextAlias { body, .. } => body,
            _ => continue,
        };
        let mut at_top = true;
        visit_term(
            body,
            TermPosition::BODY,
            &mut at_top,
            &internal_labels,
            productions,
            sentence,
            &mut diagnostics,
        );
    }
    diagnostics
}

#[allow(clippy::too_many_arguments)]
fn visit_term(
    term: &Term,
    position: TermPosition,
    at_top: &mut bool,
    internal_labels: &BTreeSet<String>,
    productions: &ProductionCatalog<'_>,
    sentence: &Sentence,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let Term::Apply { label, arguments } = term else {
        for (child, child_position) in positioned_children(term, position) {
            visit_term(
                child,
                child_position,
                at_top,
                internal_labels,
                productions,
                sentence,
                diagnostics,
            );
        }
        return;
    };

    if label.name == "#withConfig" {
        visit_arguments(
            term,
            position,
            at_top,
            internal_labels,
            productions,
            sentence,
            diagnostics,
        );
        return;
    }

    let attributes = productions.attributes_for(&LabelHead::from(label));
    if internal_labels.contains(&label.name) || attributes.is_none() {
        *at_top = false;
        visit_arguments(
            term,
            position,
            at_top,
            internal_labels,
            productions,
            sentence,
            diagnostics,
        );
        return;
    }

    let attributes = attributes.expect("checked above");
    let hook = attributes.get_str("hook").unwrap_or("");
    if attributes.get("function").is_some()
        && position.lhs
        && !*at_top
        && !COLLECTION_HOOKS.contains(&hook)
    {
        diagnostics.push(Diagnostic::error(
            DiagnosticCode::IllegalFunctionOnLhs,
            format!(
                "Illegal function symbol {} on LHS of rule. Consider adding `simplification` attribute to the rule if this is intended.",
                label.name
            ),
            sentence,
        ));
    }
    *at_top = false;

    match hook {
        "SET.element" => {}
        "MAP.element" => {
            if let Some(argument) = arguments.get(1) {
                visit_term(
                    argument,
                    position,
                    at_top,
                    internal_labels,
                    productions,
                    sentence,
                    diagnostics,
                );
            }
        }
        "LIST.update" => {
            for index in [0, 2] {
                if let Some(argument) = arguments.get(index) {
                    visit_term(
                        argument,
                        position,
                        at_top,
                        internal_labels,
                        productions,
                        sentence,
                        diagnostics,
                    );
                }
            }
        }
        _ => visit_arguments(
            term,
            position,
            at_top,
            internal_labels,
            productions,
            sentence,
            diagnostics,
        ),
    }
}

#[allow(clippy::too_many_arguments)]
fn visit_arguments(
    term: &Term,
    position: TermPosition,
    at_top: &mut bool,
    internal_labels: &BTreeSet<String>,
    productions: &ProductionCatalog<'_>,
    sentence: &Sentence,
    diagnostics: &mut Vec<Diagnostic>,
) {
    for (child, child_position) in positioned_children(term, position) {
        visit_term(
            child,
            child_position,
            at_top,
            internal_labels,
            productions,
            sentence,
            diagnostics,
        );
    }
}

fn internal_labels(
    productions: &ProductionCatalog<'_>,
    sorts: &SortCatalog<'_>,
) -> BTreeSet<String> {
    let mut labels: BTreeSet<String> = FIXED_INTERNAL_LABELS
        .map(str::to_owned)
        .into_iter()
        .collect();
    for sort in sorts.all_sorts() {
        labels.insert(format!("#SemanticCastTo{sort}"));
        labels.insert(format!("project:{sort}"));
        labels.insert(format!("is{sort}"));
    }
    for id in productions.ids() {
        let Sentence::Production {
            label: Some(label),
            items,
            ..
        } = productions.production(id)
        else {
            continue;
        };
        for item in items {
            if let ProductionItem::NonTerminal {
                name: Some(name), ..
            } = item
            {
                labels.insert(format!("project:{}:{name}", label.name));
            }
        }
    }
    labels
}
