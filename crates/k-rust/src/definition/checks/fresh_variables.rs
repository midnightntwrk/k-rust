//! This definition check traverses each rule, claim and context once; callers supply the production catalog and no dedicated counter is recorded.
//!
//! Where a fresh variable `!X` has a value.
//!
//! A fresh variable stands for a value the sentence allocates when it applies: the rewrite step
//! that applies the rule reads the configuration's counter cell, builds the value from it, and
//! advances the counter. Only a rewrite step of the configuration has that cell to read and
//! advance. Every other sentence that may mention `!X` is applied without the configuration:
//!
//! - a function rule is an equation evaluated wherever the function is applied, in any term;
//! - a simplification rule is an equation on the term its left-hand side matches;
//! - an anywhere rule applies to its left-hand side wherever that term occurs;
//! - a macro or alias rule is expanded wherever its left-hand side occurs, programs and the
//!   initial configuration included;
//! - a claim states which configurations a path reaches and allocates nothing itself.
//!
//! In each of them `!X` would be a variable that nothing binds, so each is rejected at the
//! sentence.
//!
//! Within a rewrite rule, the value of `!X` exists only once the step applies: the rule relates
//! the configurations its left-hand side and `requires` clause describe, before the step, to the
//! ones its right-hand side and `ensures` clause describe, after it. So `!X` may occur only where
//! the rule builds the result, on the right-hand side of a rewrite and in `ensures`. A term the
//! rule matches, on the left-hand side of a rewrite or outside every rewrite, would compare the
//! subject with a value nothing in it holds yet, and a `requires` clause would ask about a value
//! before the step that allocates it decides to apply; both are rejected at the sentence.
//!
//! A context has no such place. It is lowered to two steps: one heats the term the context
//! describes, and the other matches the heated term again, once evaluated, to cool it back. Every
//! part of the context is therefore matched by one of them, the right-hand side of a rewrite in
//! it included, and a value one step allocates is not one the other can match; `!X` is rejected
//! anywhere in a context.

use std::collections::BTreeSet;

use super::Sentence;
use super::term_position::{TermPosition, positioned_children};
use crate::definition::{AttributeKey, LabelHead, ProductionCatalog, match_rule_label};
use crate::diagnostic::{Diagnostic, DiagnosticCode};
use crate::kast::Term;

/// Reject each fresh variable of a rule or claim that is not applied as a rewrite step of the
/// configuration (module docs).
pub(super) fn check_fresh_variables(
    sentences: &[&Sentence],
    productions: &ProductionCatalog<'_>,
) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for sentence in sentences {
        let (body, requires, ensures) = match sentence {
            Sentence::Rule {
                body,
                requires,
                ensures,
                ..
            }
            | Sentence::Claim {
                body,
                requires,
                ensures,
                ..
            } => (body, requires, ensures),
            Sentence::Context { body, requires, .. } => {
                for name in fresh_variables([body, requires]) {
                    diagnostics.push(Diagnostic::error(
                        DiagnosticCode::InvalidFreshConstant,
                        format!(
                            "Fresh variable {name} cannot occur in a context: the context is lowered to a step that heats its term and a step that matches the heated term again to cool it, and a value one step allocates is not one the other can match."
                        ),
                        sentence,
                    ));
                }
                continue;
            }
            Sentence::SyntaxSort { .. }
            | Sentence::SortSynonym { .. }
            | Sentence::SyntaxLexical { .. }
            | Sentence::Production { .. }
            | Sentence::SyntaxAssociativity { .. }
            | Sentence::SyntaxPriority { .. }
            | Sentence::ContextAlias { .. }
            | Sentence::Configuration { .. }
            | Sentence::Bubble { .. } => continue,
        };
        let fresh = fresh_variables([body, requires, ensures]);
        if fresh.is_empty() {
            continue;
        }
        let Some((kind, reason)) = configuration_less(sentence, productions) else {
            check_rewrite_rule_positions(sentence, body, requires, &mut diagnostics);
            continue;
        };
        for name in fresh {
            let hint = if matches!(sentence, Sentence::Claim { .. }) {
                format!("; write ?{} for a value the path produces", &name[1..])
            } else {
                String::new()
            };
            diagnostics.push(Diagnostic::error(
                DiagnosticCode::InvalidFreshConstant,
                format!(
                    "Fresh variable {name} is not supported in {kind}: a fresh value is allocated from the configuration's counter cell by the rewrite step that introduces it, and {reason}{hint}."
                ),
                sentence,
            ));
        }
    }
    diagnostics
}

/// The kind of `sentence` and why it has no counter cell, when it is not applied as a rewrite
/// step of the configuration.
fn configuration_less(
    sentence: &Sentence,
    productions: &ProductionCatalog<'_>,
) -> Option<(&'static str, &'static str)> {
    if matches!(sentence, Sentence::Claim { .. }) {
        return Some((
            "a claim",
            "a claim states which configurations a path reaches without taking a step of its own",
        ));
    }
    let attributes = sentence.attributes();
    let head = LabelHead::from(&match_rule_label(sentence));
    let production_attributes = productions.attributes_for(&head);
    let declared = |key: AttributeKey| {
        attributes.has(key) || production_attributes.is_some_and(|attributes| attributes.has(key))
    };
    if AttributeKey::MACRO_LIKE.into_iter().any(declared) {
        Some((
            "a macro or alias rule",
            "the rule is expanded wherever its left-hand side occurs, programs and the initial configuration included, without the configuration",
        ))
    } else if attributes.has(AttributeKey::Anywhere) {
        Some((
            "an anywhere rule",
            "the rule applies to its left-hand side wherever that term occurs, without the configuration",
        ))
    } else if attributes.has(AttributeKey::Simplification) {
        Some((
            "a simplification rule",
            "the rule is an equation on the term its left-hand side matches, without the configuration",
        ))
    } else if productions.function_labels().contains(&head) {
        Some((
            "a function rule",
            "the rule is an equation evaluated wherever the function is applied, without the configuration",
        ))
    } else {
        None
    }
}

/// Reject each fresh variable of a rewrite rule that the rule matches or that its `requires`
/// clause mentions (module docs).
fn check_rewrite_rule_positions(
    sentence: &Sentence,
    body: &Term,
    requires: &Term,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let mut matched = BTreeSet::new();
    matched_fresh_variables(body, TermPosition::BODY, &mut matched);
    let required = fresh_variables([requires]);
    let places = [
        (
            matched,
            "where a rule matches (the left-hand side of a rewrite, or outside every rewrite)",
        ),
        (
            required,
            "in the requires clause of a rule, which decides whether the step applies",
        ),
    ];
    for (names, place) in places {
        for name in names {
            diagnostics.push(Diagnostic::error(
                DiagnosticCode::InvalidFreshConstant,
                format!(
                    "Fresh variable {name} cannot occur {place}: its value is allocated by the step that applies the rule, so it may occur only on the right-hand side of a rewrite or in the ensures clause."
                ),
                sentence,
            ));
        }
    }
}

/// The fresh variables of `term` at positions it matches, `term` being at `position`.
// Invariant: each recursive call receives a child of `term` with its position, so the size of
// `term` bounds the calls.
fn matched_fresh_variables(term: &Term, position: TermPosition, matched: &mut BTreeSet<String>) {
    if let Term::Variable { name, .. } = term.unannotated() {
        if position.lhs && name.starts_with('!') {
            matched.insert(name.clone());
        }
        return;
    }
    for (child, child_position) in positioned_children(term, position) {
        matched_fresh_variables(child, child_position, matched);
    }
}

fn fresh_variables<'a>(roots: impl IntoIterator<Item = &'a Term>) -> BTreeSet<String> {
    let mut fresh = BTreeSet::new();
    for root in roots {
        root.visit_preorder(&mut |term| {
            if let Term::Variable { name, .. } = term
                && name.starts_with('!')
            {
                fresh.insert(name.clone());
            }
        });
    }
    fresh
}
