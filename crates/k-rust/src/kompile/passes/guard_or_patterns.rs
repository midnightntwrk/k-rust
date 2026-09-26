//! This transformation pass resolves required views, transforms sentences and terms, records origins, and retargets metadata when needed.
//! Its named `--timings` phase measures total cost; the shared pass scaffolding counts resolutions (`KompileResolveCalls`), copied sentences (`KompileSentenceCopies`), and partial orders built (`KompilePartialOrdersBuilt`), and `KompileSentencesTransformed` is added once per compile in `compile.rs`.
//!
//! Give matching-logic disjunctions explicit aliases.

use std::fmt;

use crate::{
    definition::{Definition, Sentence},
    diagnostic::{Diagnostic, DiagnosticCode, Severity},
    kast::{InternalLabel, Term},
    kompile::{SortInjector, fresh_names::FreshNames},
    provenance::GeneratingPass,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GuardOrPatternsError {
    pub diagnostics: Vec<Diagnostic>,
}

impl fmt::Display for GuardOrPatternsError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "or-pattern guarding produced {} errors",
            self.diagnostics.len()
        )
    }
}

impl std::error::Error for GuardOrPatternsError {}

/// Apply Java's `GuardOrPatterns` transformation to rules and contexts.
pub fn guard_or_patterns(definition: &Definition) -> Result<Definition, GuardOrPatternsError> {
    super::super::pipeline::run_standalone(
        definition,
        guard_or_patterns_pass,
        Some(GeneratingPass::GuardOrPatterns),
    )
}

pub(crate) fn guard_or_patterns_pass(
    input: &super::super::pipeline::PassInput<'_>,
    _: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, GuardOrPatternsError> {
    let resolved = input.resolved_raw().map_err(|error| GuardOrPatternsError {
        diagnostics: vec![plain_error(error.to_string())],
    })?;
    let views = resolved.views();
    let mut output = input.definition.clone();
    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let injector =
            SortInjector::with_views(&views, module_id).map_err(|error| GuardOrPatternsError {
                diagnostics: vec![plain_error(error.to_string())],
            })?;
        for sentence in &mut module.local_sentences {
            let sentence = crate::definition::sentence_mut(sentence);
            let attributes = sentence.attributes().clone();
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
                *root = transform(taken, &injector, &mut fresh).map_err(|error| {
                    GuardOrPatternsError {
                        diagnostics: vec![Diagnostic::error_at(
                            DiagnosticCode::InvalidOrPattern,
                            error.to_string(),
                            &attributes,
                        )],
                    }
                })?;
            }
        }
    }
    Ok(output)
}

fn plain_error(message: impl Into<String>) -> Diagnostic {
    Diagnostic {
        severity: Severity::Error,
        code: DiagnosticCode::InvalidOrPattern,
        message: message.into(),
        source: None,
        location: None,
        input_addresses: Vec::new(),
    }
}

// Invariant: each call rewrites an internal `Or` application into an `As` pattern with a fresh `_Gen` alias, returns `As` and `Rewrite` terms unchanged, and otherwise recurses into `Apply` arguments and `Sequence` items; the finite depth of `term` bounds the recursion.
fn transform(
    term: Term,
    injector: &SortInjector<'_, '_>,
    fresh: &mut FreshNames,
) -> Result<Term, crate::kompile::SortInjectionError> {
    let metadata = term.metadata().cloned();
    let rebuilt = match term.into_unannotated() {
        Term::Apply { label, arguments } if label.is(InternalLabel::Or) => {
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
