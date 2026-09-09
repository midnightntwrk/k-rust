//! Give every anonymous variable occurrence a collision-free sentence-local name.

use std::collections::BTreeSet;

use crate::{
    definition::{Definition, Sentence},
    kast::Term,
    kompile::fresh_names::{FreshNames, GeneratedVariableIdentity},
    provenance::{GeneratingPass, record_generated_origins},
};

/// Apply Java's `ResolveAnonVar` transformation to rules, claims, and contexts.
pub fn resolve_anon_vars(definition: &Definition) -> Definition {
    let mut output = definition.clone();
    for module in &mut output.modules {
        for sentence in &mut module.local_sentences {
            resolve_anon_vars_in_sentence_mut(sentence);
        }
    }
    record_generated_origins(
        definition,
        output,
        GeneratingPass::ResolveAnonymousVariables,
    )
}

/// Resolve anonymous variables in one sentence and return exactly the identities minted.
pub fn resolve_anon_vars_in_sentence(
    mut sentence: Sentence,
) -> (Sentence, BTreeSet<GeneratedVariableIdentity>) {
    let generated = resolve_anon_vars_in_sentence_mut(&mut sentence);
    (sentence, generated)
}

fn resolve_anon_vars_in_sentence_mut(
    sentence: &mut Sentence,
) -> BTreeSet<GeneratedVariableIdentity> {
    let mut fresh = FreshNames::for_sentence(sentence);
    let mut generated = BTreeSet::new();
    let roots = match sentence {
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
        } => vec![body, requires, ensures],
        Sentence::Context { body, requires, .. }
        | Sentence::ContextAlias { body, requires, .. } => vec![body, requires],
        _ => return generated,
    };
    for root in roots {
        let taken = std::mem::replace(root, Term::Sequence(Vec::new()));
        *root = transform(taken, &mut fresh, &mut generated);
    }
    generated
}

fn transform(
    term: Term,
    fresh: &mut FreshNames,
    generated: &mut BTreeSet<GeneratedVariableIdentity>,
) -> Term {
    match term {
        Term::Annotated { term, metadata } => {
            transform(*term, fresh, generated).with_metadata(metadata)
        }
        Term::Variable { name, sort } if anonymous_prefix(&name).is_some() => {
            let prefix = anonymous_prefix(&name).expect("guard checked the prefix");
            let name = fresh.mint(&format!("{prefix}_Gen"));
            generated.insert(if prefix == "@" {
                GeneratedVariableIdentity::set(name.clone())
            } else {
                GeneratedVariableIdentity::element(name.clone())
            });
            Term::Variable { name, sort }
        }
        Term::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(transform(*left, fresh, generated)),
            right: Box::new(transform(*right, fresh, generated)),
        },
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(transform(*pattern, fresh, generated)),
            alias: Box::new(transform(*alias, fresh, generated)),
        },
        Term::Sequence(items) => Term::Sequence(
            items
                .into_iter()
                .map(|item| transform(item, fresh, generated))
                .collect(),
        ),
        Term::Apply { label, arguments } => Term::Apply {
            label,
            arguments: arguments
                .into_iter()
                .map(|argument| transform(argument, fresh, generated))
                .collect(),
        },
        leaf @ (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }) => leaf,
    }
}

fn anonymous_prefix(name: &str) -> Option<&'static str> {
    match name {
        "_" => Some(""),
        "?_" => Some("?"),
        "!_" => Some("!"),
        "@_" => Some("@"),
        _ => None,
    }
}
