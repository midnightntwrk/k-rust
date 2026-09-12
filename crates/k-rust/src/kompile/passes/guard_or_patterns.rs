//! Give matching-logic disjunctions explicit aliases.

use crate::{
    definition::{Definition, ResolvedDefinition, Sentence},
    kast::Term,
    kompile::{SortInjector, fresh_names::FreshNames},
    provenance::{GeneratingPass, record_generated_origins},
};

/// Apply Java's `GuardOrPatterns` transformation to rules and contexts.
pub fn guard_or_patterns(definition: &Definition) -> Result<Definition, String> {
    let resolved = ResolvedDefinition::resolve(definition).map_err(|error| error.to_string())?;
    let mut output = definition.clone();
    for module in &mut output.modules {
        let injector =
            SortInjector::new(&resolved, &module.name).map_err(|error| error.to_string())?;
        for sentence in &mut module.local_sentences {
            let mut fresh = FreshNames::for_sentence(sentence);
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
            for root in roots {
                let taken = std::mem::replace(root, Term::Sequence(Vec::new()));
                *root =
                    transform(taken, &injector, &mut fresh).map_err(|error| error.to_string())?;
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
    fresh: &mut FreshNames,
) -> Result<Term, crate::kompile::SortInjectionError> {
    let metadata = term.metadata().cloned();
    let rebuilt = match term.into_unannotated() {
        Term::Apply { label, arguments } if label.name == "#Or" => {
            let application = Term::Apply { label, arguments };
            let application = match metadata.clone() {
                Some(metadata) => application.with_metadata(metadata),
                None => application,
            };
            let sort = injector.term_sort_before_shape_normalization(&application, None)?;
            Term::As {
                pattern: Box::new(application),
                alias: Box::new(Term::Variable {
                    name: fresh.mint("_Gen"),
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
                .map(|argument| transform(argument, injector, fresh))
                .collect::<Result<Vec<_>, _>>()?,
        },
        Term::Sequence(items) => Term::Sequence(
            items
                .into_iter()
                .map(|item| transform(item, injector, fresh))
                .collect::<Result<Vec<_>, _>>()?,
        ),
        leaf @ (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }) => leaf,
        Term::Annotated { .. } => unreachable!("into_unannotated strips metadata"),
    };
    Ok(metadata.map_or(rebuilt.clone(), |metadata| rebuilt.with_metadata(metadata)))
}
