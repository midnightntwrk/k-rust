//! Warnings for terms parsed through deprecated productions.

use super::{Sentence, checked_terms};
use crate::definition::{ProductionCatalog, ProductionId};
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
                let Some(resolved) = term.metadata().and_then(|metadata| metadata.production)
                else {
                    return;
                };
                if resolved.0 >= productions.len()
                    || productions
                        .production(ProductionId(resolved.0))
                        .attributes()
                        .get("deprecated")
                        .is_none()
                {
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
