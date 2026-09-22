//! This Java-compatible definition check traverses module sentences and terms linearly; callers supply derived catalogs and no dedicated counter is recorded.
//!
//! Warnings for terms parsed through deprecated productions.

use super::{Sentence, checked_terms};
use crate::definition::AttributeKey;
use crate::definition::{LabelHead, ProductionCatalog};
use crate::diagnostic::{Diagnostic, DiagnosticCode};
use crate::kast::Term;

pub fn check_deprecated_productions(
    sentences: &[&Sentence],
    productions: &ProductionCatalog<'_>,
) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for sentence in sentences {
        for term in checked_terms(sentence) {
            visit_with_metadata(term, &mut |term| {
                if !uses_deprecated_production(term, productions) {
                    return;
                }
                diagnostics.push(Diagnostic::warning(
                    DiagnosticCode::DeprecatedProduction,
                    "Use of deprecated production found; this syntax may be removed in the future.",
                    sentence,
                ));
            });
        }
    }
    diagnostics
}

fn uses_deprecated_production(term: &Term, productions: &ProductionCatalog<'_>) -> bool {
    if let Some(resolved) = term.metadata().and_then(|metadata| metadata.production)
        && let Some(production_id) = productions.lookup(&resolved)
    {
        let production = productions.production(production_id);
        let metadata_matches = match (term.unannotated(), production) {
            (
                Term::Apply { label, .. },
                Sentence::Production {
                    label: Some(production_label),
                    ..
                },
            ) => LabelHead::from(label) == LabelHead::from(production_label),
            (Term::Apply { .. }, _) => false,
            _ => true,
        };
        if metadata_matches {
            return production.attributes().has(AttributeKey::Deprecated);
        }
    }
    let Term::Apply { label, .. } = term.unannotated() else {
        return false;
    };
    let candidates = productions.productions_for(&LabelHead::from(label));
    matches!(candidates, [production]
        if productions.production(*production).attributes().has(AttributeKey::Deprecated))
}

// Invariant: `visitor` has been applied to `term` before any of its subterms, and each recursive call descends into a strict subterm of `term`, so the size of `term` bounds the calls.
fn visit_with_metadata(term: &Term, visitor: &mut impl FnMut(&Term)) {
    visitor(term);
    match term.unannotated() {
        Term::Rewrite { left, right } => {
            visit_with_metadata(left, visitor);
            visit_with_metadata(right, visitor);
        }
        Term::As { pattern, alias } => {
            visit_with_metadata(pattern, visitor);
            visit_with_metadata(alias, visitor);
        }
        Term::Sequence(items)
        | Term::Apply {
            arguments: items, ..
        } => {
            for item in items {
                visit_with_metadata(item, visitor);
            }
        }
        Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => {}
        Term::Annotated { .. } => unreachable!(),
    }
}
