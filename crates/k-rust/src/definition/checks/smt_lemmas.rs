//! SMT-lemma symbol validation ported from Java `CheckSmtLemmas`.

use super::Sentence;
use crate::definition::{LabelHead, ProductionCatalog};
use crate::diagnostic::{Diagnostic, DiagnosticCode};
use crate::kast::Term;

pub fn check_smt_lemmas(
    sentences: &[&Sentence],
    productions: &ProductionCatalog<'_>,
) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for sentence in sentences {
        let Sentence::Rule {
            body, attributes, ..
        } = sentence
        else {
            continue;
        };
        if attributes.get("smt-lemma").is_none() {
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
                attributes.get("smt-hook").is_none() && attributes.get("smtlib").is_none()
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
