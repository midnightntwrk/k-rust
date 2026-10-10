//! This definition check traverses module sentences and terms linearly; callers supply derived catalogs and no dedicated counter is recorded.
//!
//! Function-symbol matching checks: where a rule's left-hand side may contain a function symbol.

use std::collections::BTreeSet;

use super::Sentence;
use super::labels::internal_labels;
use super::term_position::{TermPosition, positioned_children};
use crate::definition::AttributeKey;
use crate::definition::{LabelHead, ProductionCatalog, SortCatalog};
use crate::diagnostic::{Diagnostic, DiagnosticCode};
use crate::kast::{GeneratedLabel, InternalLabel, Term};

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

pub fn check_functions(
    sentences: &[&Sentence],
    productions: &ProductionCatalog<'_>,
    sorts: &SortCatalog<'_>,
) -> Vec<Diagnostic> {
    check_functions_with_internal_labels(
        sentences,
        productions,
        &internal_labels(productions, sorts),
    )
}

/// [`check_functions`] against the internal labels of the module whose catalogs are supplied,
/// for a caller that checks one module's sentences in several calls and computes them once.
pub(crate) fn check_functions_with_internal_labels(
    sentences: &[&Sentence],
    productions: &ProductionCatalog<'_>,
    internal_labels: &BTreeSet<String>,
) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for sentence in sentences {
        let body = match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if !attributes.has(AttributeKey::Simplification) => body,
            Sentence::Context { body, .. } | Sentence::ContextAlias { body, .. } => body,
            Sentence::SyntaxSort { .. }
            | Sentence::SortSynonym { .. }
            | Sentence::SyntaxLexical { .. }
            | Sentence::Production { .. }
            | Sentence::SyntaxAssociativity { .. }
            | Sentence::SyntaxPriority { .. }
            | Sentence::Rule { .. }
            | Sentence::Claim { .. }
            | Sentence::Configuration { .. }
            | Sentence::Bubble { .. } => continue,
        };
        let mut at_top = true;
        visit_term(
            body,
            TermPosition::BODY,
            &mut at_top,
            internal_labels,
            productions,
            sentence,
            &mut diagnostics,
        );
    }
    diagnostics
}

#[allow(clippy::too_many_arguments)]
// Invariant: `position` is the `TermPosition` of `term`, and `at_top` stays true only until the first application other than `WithConfig` is visited; each recursive call, directly or through `visit_arguments`, receives a strict subterm of `term`, so the size of the rule body bounds the calls.
fn visit_term(
    term: &Term,
    position: TermPosition,
    at_top: &mut bool,
    internal_labels: &BTreeSet<String>,
    productions: &ProductionCatalog<'_>,
    sentence: &Sentence,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let Term::Apply { label, arguments } = term.unannotated() else {
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

    if label.is(InternalLabel::WithConfig) {
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

    // A sort projection `project:S`, written `{T}:>S`, is a function compilation declares for
    // every sort that has one: it computes the value of its operand read in `S`, and is defined
    // only where that value is in `S`. It is judged like any other function symbol, whether the
    // definition declares its production yet or not.
    let sort_projection = matches!(label.generated(), Some(GeneratedLabel::Projection { .. }));
    let attributes = productions.attributes_for(&LabelHead::from(label));
    if !sort_projection && (internal_labels.contains(&label.name) || attributes.is_none()) {
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

    let hook = attributes
        .and_then(|attributes| attributes.string(AttributeKey::Hook))
        .unwrap_or("");
    let function = sort_projection
        || attributes.is_some_and(|attributes| attributes.has(AttributeKey::Function));
    if function && position.lhs && !*at_top && !COLLECTION_HOOKS.contains(&hook) {
        let message = if sort_projection {
            format!(
                "Illegal sort projection {} on LHS of rule: `{{T}}:>S` computes the value of T read in S, and a left-hand side is matched; a variable `X:S` matches the terms of sort S. Consider adding `simplification` attribute to the rule if this is intended.",
                label.name
            )
        } else {
            format!(
                "Illegal function symbol {} on LHS of rule. Consider adding `simplification` attribute to the rule if this is intended.",
                label.name
            )
        };
        diagnostics.push(Diagnostic::error(
            DiagnosticCode::IllegalFunctionOnLhs,
            message,
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
