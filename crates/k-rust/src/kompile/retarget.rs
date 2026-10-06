//! ```toml algorithm
//! id = "kompile.metadata.retarget"
//! name = "production-metadata retargeting after deliberate identity changes"
//! sites = ["retarget_production_identities", "retarget_sentence", "retarget_term"]
//! variable = "N = definition-local term nodes; R = replacement identities"
//! counters = ["KompileSentenceCopies"]
//!
//! [[cost]]
//! mode = "one pass-owned replacement map"
//! bound = "O(N log R)"
//! ```
//!
//! Retarget compiler metadata when a pass deliberately changes a production.

use std::collections::BTreeMap;

use crate::definition::{Definition, Sentence};
use crate::kast::{ProductionIdentity, Term, TermParts};

/// Replace production identities in all definition-local terms according to a pass-owned map.
///
/// Production identities are catalog-independent, so ordinary catalog changes need no walk.
/// The only remaining update is an explicit identity change at the construction site of a
/// production that a pass rewrites (for example, adding a generated top-cell argument).
pub(crate) fn retarget_production_identities(
    definition: &mut Definition,
    replacements: &BTreeMap<ProductionIdentity, ProductionIdentity>,
) {
    if replacements.is_empty() {
        return;
    }
    for module in &mut definition.modules {
        for sentence in &mut module.local_sentences {
            retarget_sentence(crate::definition::sentence_mut(sentence), replacements);
        }
    }
}

fn retarget_sentence(
    sentence: &mut Sentence,
    replacements: &BTreeMap<ProductionIdentity, ProductionIdentity>,
) {
    for (_, term) in sentence.terms_mut() {
        let taken = std::mem::replace(term, Term::Sequence(Vec::new()));
        *term = retarget_term(taken, replacements);
    }
}

// Invariant: every recursive call consumes one child of the finite term tree.
fn retarget_term(
    term: Term,
    replacements: &BTreeMap<ProductionIdentity, ProductionIdentity>,
) -> Term {
    let mut metadata = term.metadata().cloned().unwrap_or_default();
    if let Some(identity) = metadata.production
        && let Some(replacement) = replacements.get(&identity)
    {
        metadata.production = Some(*replacement);
    }
    let rebuilt = match term.into_unannotated().into_parts() {
        TermParts::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(retarget_term(*left, replacements)),
            right: Box::new(retarget_term(*right, replacements)),
        },
        TermParts::As { pattern, alias } => Term::As {
            pattern: Box::new(retarget_term(*pattern, replacements)),
            alias: Box::new(retarget_term(*alias, replacements)),
        },
        TermParts::Sequence(items) => Term::Sequence(
            items
                .into_iter()
                .map(|item| retarget_term(item, replacements))
                .collect(),
        ),
        TermParts::Apply { label, arguments } => Term::Apply {
            label,
            arguments: arguments
                .into_iter()
                .map(|argument| retarget_term(argument, replacements))
                .collect(),
        },
        leaf @ (TermParts::InjectedLabel(_)
        | TermParts::Variable { .. }
        | TermParts::Token { .. }) => Term::from(leaf),
        TermParts::Annotated { .. } => unreachable!(),
    };
    rebuilt.with_metadata(metadata)
}
