//! Give every anonymous variable occurrence a collision-free sentence-local name.

use std::collections::BTreeSet;

use crate::{
    definition::{Definition, Sentence},
    kast::Term,
};

/// Apply Java's `ResolveAnonVar` transformation to rules, claims, and contexts.
pub fn resolve_anon_vars(definition: &Definition) -> Definition {
    let mut output = definition.clone();
    for module in &mut output.modules {
        for sentence in &mut module.local_sentences {
            resolve_sentence(sentence);
        }
    }
    output
}

fn resolve_sentence(sentence: &mut Sentence) {
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
    let mut used = BTreeSet::new();
    for root in &roots {
        root.visit_preorder(&mut |term| {
            if let Term::Variable { name, .. } = term.unannotated() {
                used.insert(name.clone());
            }
        });
    }
    let mut counter = 0usize;
    for root in roots {
        let taken = std::mem::replace(root, Term::Sequence(Vec::new()));
        *root = transform(taken, &mut used, &mut counter);
    }
}

fn transform(term: Term, used: &mut BTreeSet<String>, counter: &mut usize) -> Term {
    match term {
        Term::Annotated { term, metadata } => {
            transform(*term, used, counter).with_metadata(metadata)
        }
        Term::Variable { name, sort } if anonymous_prefix(&name).is_some() => {
            let prefix = anonymous_prefix(&name).expect("guard checked the prefix");
            loop {
                let candidate = format!("{prefix}_Gen{counter}");
                *counter += 1;
                if used.insert(candidate.clone()) {
                    return Term::Variable {
                        name: candidate,
                        sort,
                    };
                }
            }
        }
        Term::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(transform(*left, used, counter)),
            right: Box::new(transform(*right, used, counter)),
        },
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(transform(*pattern, used, counter)),
            alias: Box::new(transform(*alias, used, counter)),
        },
        Term::Sequence(items) => Term::Sequence(
            items
                .into_iter()
                .map(|item| transform(item, used, counter))
                .collect(),
        ),
        Term::Apply { label, arguments } => Term::Apply {
            label,
            arguments: arguments
                .into_iter()
                .map(|argument| transform(argument, used, counter))
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
