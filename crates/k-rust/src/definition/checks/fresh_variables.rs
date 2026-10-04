//! This definition check traverses each rule and claim once; callers supply the production catalog and no dedicated counter is recorded.
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

use std::collections::BTreeSet;

use super::Sentence;
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
            Sentence::SyntaxSort { .. }
            | Sentence::SortSynonym { .. }
            | Sentence::SyntaxLexical { .. }
            | Sentence::Production { .. }
            | Sentence::SyntaxAssociativity { .. }
            | Sentence::SyntaxPriority { .. }
            | Sentence::ContextAlias { .. }
            | Sentence::Context { .. }
            | Sentence::Configuration { .. }
            | Sentence::Bubble { .. } => continue,
        };
        let fresh = fresh_variables([body, requires, ensures]);
        if fresh.is_empty() {
            continue;
        }
        let Some((kind, reason)) = configuration_less(sentence, productions) else {
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
