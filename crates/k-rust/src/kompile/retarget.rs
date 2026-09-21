//! Retarget compiler metadata when a pass deliberately changes a production.

use std::collections::BTreeMap;

use crate::definition::{Definition, Sentence};
use crate::kast::{ProductionIdentity, Term};

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
            retarget_sentence(sentence, replacements);
        }
    }
}

fn retarget_sentence(
    sentence: &mut Sentence,
    replacements: &BTreeMap<ProductionIdentity, ProductionIdentity>,
) {
    let retarget = |term: &mut Term| {
        let taken = std::mem::replace(term, Term::Sequence(Vec::new()));
        *term = retarget_term(taken, replacements);
    };
    match sentence {
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
        } => {
            retarget(body);
            retarget(requires);
            retarget(ensures);
        }
        Sentence::Context { body, requires, .. }
        | Sentence::ContextAlias { body, requires, .. } => {
            retarget(body);
            retarget(requires);
        }
        Sentence::Configuration { body, ensures, .. } => {
            retarget(body);
            retarget(ensures);
        }
        _ => {}
    }
}

// Invariant: every recursive call consumes one child of the finite term tree.
fn retarget_term(
    term: Term,
    replacements: &BTreeMap<ProductionIdentity, ProductionIdentity>,
) -> Term {
    let mut metadata = term.metadata().cloned().unwrap_or_default();
    if let Some(identity) = metadata.production {
        if let Some(replacement) = replacements.get(&identity) {
            metadata.production = Some(*replacement);
        }
    }
    let rebuilt = match term.into_unannotated() {
        Term::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(retarget_term(*left, replacements)),
            right: Box::new(retarget_term(*right, replacements)),
        },
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(retarget_term(*pattern, replacements)),
            alias: Box::new(retarget_term(*alias, replacements)),
        },
        Term::Sequence(items) => Term::Sequence(
            items
                .into_iter()
                .map(|item| retarget_term(item, replacements))
                .collect(),
        ),
        Term::Apply { label, arguments } => Term::Apply {
            label,
            arguments: arguments
                .into_iter()
                .map(|argument| retarget_term(argument, replacements))
                .collect(),
        },
        leaf @ (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }) => leaf,
        Term::Annotated { .. } => unreachable!(),
    };
    rebuilt.with_metadata(metadata)
}
