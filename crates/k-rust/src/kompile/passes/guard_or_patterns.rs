//! Give matching-logic disjunctions explicit aliases.

use std::collections::BTreeSet;

use crate::{
    definition::{Definition, ResolvedDefinition, Sentence},
    kast::{Sort, Term},
    kompile::SortInjector,
    provenance::{GeneratingPass, record_generated_origins},
};

/// Apply Java's `GuardOrPatterns` transformation to rules and contexts.
pub fn guard_or_patterns(definition: &Definition) -> Result<Definition, String> {
    let resolved = ResolvedDefinition::resolve(definition).map_err(|error| error.to_string())?;
    let mut output = definition.clone();
    let mut counter = 0usize;
    for module in &mut output.modules {
        let injector =
            SortInjector::new(&resolved, &module.name).map_err(|error| error.to_string())?;
        for sentence in &mut module.local_sentences {
            let roots = match sentence {
                Sentence::Rule {
                    body,
                    requires,
                    ensures,
                    ..
                } => vec![body, requires, ensures],
                Sentence::Context { body, requires, .. } => vec![body, requires],
                _ => continue,
            };
            let mut variables = BTreeSet::new();
            for root in &roots {
                root.visit_preorder(&mut |term| {
                    if let Term::Variable { name, .. } = term.unannotated() {
                        variables.insert(name.clone());
                    }
                });
            }
            for root in roots {
                let taken = std::mem::replace(root, Term::Sequence(Vec::new()));
                *root = transform(taken, &injector, &mut variables, &mut counter);
            }
        }
    }
    Ok(record_generated_origins(
        definition,
        output,
        GeneratingPass::GuardOrPatterns,
    ))
}

fn transform(
    term: Term,
    injector: &SortInjector<'_>,
    variables: &mut BTreeSet<String>,
    counter: &mut usize,
) -> Term {
    let metadata = term.metadata().cloned();
    let rebuilt = match term.into_unannotated() {
        Term::Apply { label, arguments } if label.name == "#Or" => {
            let application = Term::Apply { label, arguments };
            let sort = injector
                .term_sort(&application, None)
                .unwrap_or_else(|_| Sort::new("K"));
            let name = loop {
                let name = format!("_Gen{counter}");
                *counter += 1;
                if variables.insert(name.clone()) {
                    break name;
                }
            };
            Term::As {
                pattern: Box::new(application),
                alias: Box::new(Term::Variable {
                    name,
                    sort: Some(sort),
                }),
            }
        }
        // Java deliberately treats aliases and rewrites as traversal boundaries.
        boundary @ (Term::As { .. } | Term::Rewrite { .. }) => boundary,
        Term::Apply { label, arguments } => Term::Apply {
            label,
            arguments: arguments
                .into_iter()
                .map(|argument| transform(argument, injector, variables, counter))
                .collect(),
        },
        Term::Sequence(items) => Term::Sequence(
            items
                .into_iter()
                .map(|item| transform(item, injector, variables, counter))
                .collect(),
        ),
        leaf @ (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }) => leaf,
        Term::Annotated { .. } => unreachable!("into_unannotated strips metadata"),
    };
    metadata.map_or(rebuilt.clone(), |metadata| rebuilt.with_metadata(metadata))
}
