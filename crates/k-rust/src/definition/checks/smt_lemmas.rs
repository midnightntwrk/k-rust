//! This Java-compatible definition check traverses module sentences and terms linearly; callers supply derived catalogs and no dedicated counter is recorded.
//!
//! SMT-lemma symbol validation ported from Java `CheckSmtLemmas`.

use super::Sentence;
use crate::definition::AttributeKey;
use crate::definition::{LabelHead, ProductionCatalog};
use crate::diagnostic::{Diagnostic, DiagnosticCode};
use crate::kast::Term;

pub fn check_smt_lemmas(
    sentences: &[&Sentence],
    productions: &ProductionCatalog<'_>,
) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    // Invariant: `diagnostics` holds an error for every label application in the `smt-lemma` rules before `sentence` none of whose productions carries `smt-hook` or `smtlib`; each iteration consumes one entry of `sentences`.
    for sentence in sentences {
        let Sentence::Rule {
            body, attributes, ..
        } = sentence
        else {
            continue;
        };
        if !attributes.has(AttributeKey::SmtLemma) {
            continue;
        }
        body.visit_preorder(&mut |term| {
            let Term::Apply { label, .. } = term else {
                return;
            };
            let ids = productions.productions_for(&LabelHead::from(label));
            if ids.is_empty() {
                return;
            }
            if ids.iter().all(|id| {
                let attributes = productions.production(*id).attributes();
                !attributes.has(AttributeKey::SmtHook) && !attributes.has(AttributeKey::Smtlib)
            }) {
                diagnostics.push(Diagnostic::error(
                    DiagnosticCode::InvalidSmtLemma,
                    "Invalid term in smt-lemma detected. All terms in smt-lemma rules require smt-hook or smtlib labels",
                    sentence,
                ));
            }
        });
    }
    diagnostics
}
