//! Ordered frontend compilation passes that transform flat definitions.

use std::fmt;

use crate::{
    definition::{Definition, LabelHead, ResolvedDefinition, Sentence},
    diagnostic::{Diagnostic, DiagnosticCode},
    kast::Term,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolveCommError {
    pub diagnostics: Vec<Diagnostic>,
}

impl fmt::Display for ResolveCommError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "commutative simplification resolution produced {} errors",
            self.diagnostics.len()
        )
    }
}

impl std::error::Error for ResolveCommError {}

/// Duplicate commutative simplification rules with the matched LHS arguments reversed.
///
/// This is Java's first KORE backend pass. The rule-level `comm` attribute is removed because the
/// backend assigns it a different meaning; the production itself must also carry `comm`.
pub fn resolve_comm(definition: &Definition) -> Result<Definition, ResolveCommError> {
    let resolved = ResolvedDefinition::resolve(definition).map_err(|error| ResolveCommError {
        diagnostics: vec![Diagnostic {
            severity: crate::diagnostic::Severity::Error,
            code: DiagnosticCode::InvalidCommutativeSimplification,
            message: error.to_string(),
            source: None,
            location: None,
        }],
    })?;
    let mut output = definition.clone();
    let mut diagnostics = Vec::new();

    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let productions = resolved.production_catalog(module_id);
        let mut sentences = Vec::with_capacity(module.local_sentences.len());
        for sentence in &module.local_sentences {
            let Sentence::Rule {
                body,
                requires,
                ensures,
                attributes,
            } = sentence
            else {
                sentences.push(sentence.clone());
                continue;
            };
            if attributes.get("simplification").is_none() || attributes.get("comm").is_none() {
                sentences.push(sentence.clone());
                continue;
            }

            let mut attributes = attributes.clone();
            attributes.remove("comm");
            let swapped = commute_lhs(body, true, &productions, sentence, &mut diagnostics);
            if swapped != *body {
                sentences.push(Sentence::Rule {
                    body: swapped,
                    requires: requires.clone(),
                    ensures: ensures.clone(),
                    attributes: attributes.clone(),
                });
            }
            sentences.push(Sentence::Rule {
                body: body.clone(),
                requires: requires.clone(),
                ensures: ensures.clone(),
                attributes,
            });
        }
        module.local_sentences = sentences;
    }

    if diagnostics.is_empty() {
        Ok(output)
    } else {
        diagnostics.sort();
        Err(ResolveCommError { diagnostics })
    }
}

fn commute_lhs(
    term: &Term,
    on_lhs: bool,
    productions: &crate::definition::ProductionCatalog<'_>,
    sentence: &Sentence,
    diagnostics: &mut Vec<Diagnostic>,
) -> Term {
    match term {
        Term::Annotated { term, metadata } => {
            commute_lhs(term, on_lhs, productions, sentence, diagnostics)
                .with_metadata(metadata.clone())
        }
        Term::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(commute_lhs(left, true, productions, sentence, diagnostics)),
            right: Box::new(commute_lhs(
                right,
                false,
                productions,
                sentence,
                diagnostics,
            )),
        },
        Term::Apply { label, arguments } if label.name == "#withConfig" => Term::Apply {
            label: label.clone(),
            arguments: arguments
                .iter()
                .map(|argument| commute_lhs(argument, on_lhs, productions, sentence, diagnostics))
                .collect(),
        },
        Term::Apply { .. } if !on_lhs => term.clone(),
        Term::Apply { label, arguments } => {
            let Some(attributes) = productions.attributes_for(&LabelHead::from(label)) else {
                return term.clone();
            };
            if attributes.get("comm").is_some() {
                if let [left, right] = arguments.as_slice() {
                    Term::Apply {
                        label: label.clone(),
                        arguments: vec![right.clone(), left.clone()],
                    }
                } else {
                    term.clone()
                }
            } else {
                diagnostics.push(Diagnostic::error(
                    DiagnosticCode::InvalidCommutativeSimplification,
                    format!(
                        "Used 'comm' attribute on simplification rule but {} is not comm.",
                        label.name
                    ),
                    sentence,
                ));
                term.clone()
            }
        }
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(commute_lhs(
                pattern,
                on_lhs,
                productions,
                sentence,
                diagnostics,
            )),
            alias: Box::new(commute_lhs(
                alias,
                on_lhs,
                productions,
                sentence,
                diagnostics,
            )),
        },
        Term::Sequence(items) => Term::Sequence(
            items
                .iter()
                .map(|item| commute_lhs(item, on_lhs, productions, sentence, diagnostics))
                .collect(),
        ),
        Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => term.clone(),
    }
}
