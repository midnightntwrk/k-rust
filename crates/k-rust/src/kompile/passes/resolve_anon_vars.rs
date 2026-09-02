//! Give every anonymous variable occurrence a collision-free sentence-local name.

use crate::{
    definition::{Definition, Sentence},
    kast::Term,
    kompile::fresh_names::FreshNames,
    provenance::{GeneratingPass, record_generated_origins},
};

/// Apply Java's `ResolveAnonVar` transformation to rules, claims, and contexts.
pub fn resolve_anon_vars(definition: &Definition) -> Definition {
    let mut output = definition.clone();
    for module in &mut output.modules {
        for sentence in &mut module.local_sentences {
            resolve_sentence(sentence);
        }
    }
    record_generated_origins(
        definition,
        output,
        GeneratingPass::ResolveAnonymousVariables,
    )
}

fn resolve_sentence(sentence: &mut Sentence) {
    let mut fresh = FreshNames::for_sentence(sentence);
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
        _ => return,
    };
    for root in roots {
        let taken = std::mem::replace(root, Term::Sequence(Vec::new()));
        *root = transform(taken, &mut fresh);
    }
}

fn transform(term: Term, fresh: &mut FreshNames) -> Term {
    match term {
        Term::Annotated { term, metadata } => transform(*term, fresh).with_metadata(metadata),
        Term::Variable { name, sort } if anonymous_prefix(&name).is_some() => {
            let prefix = anonymous_prefix(&name).expect("guard checked the prefix");
            Term::Variable {
                name: fresh.mint(&format!("{prefix}_Gen")),
                sort,
            }
        }
        Term::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(transform(*left, fresh)),
            right: Box::new(transform(*right, fresh)),
        },
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(transform(*pattern, fresh)),
            alias: Box::new(transform(*alias, fresh)),
        },
        Term::Sequence(items) => Term::Sequence(
            items
                .into_iter()
                .map(|item| transform(item, fresh))
                .collect(),
        ),
        Term::Apply { label, arguments } => Term::Apply {
            label,
            arguments: arguments
                .into_iter()
                .map(|argument| transform(argument, fresh))
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
