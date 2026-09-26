//! This transformation pass resolves required views, transforms sentences and terms, records origins, and retargets metadata when needed.
//! Its named `--timings` phase measures total cost; the shared pass scaffolding counts resolutions (`KompileResolveCalls`), copied sentences (`KompileSentenceCopies`), and partial orders built (`KompilePartialOrdersBuilt`), and `KompileSentencesTransformed` is added once per compile in `compile.rs`.
//!
//! Remove unit applications from associative collection terms before KORE emission.

use std::fmt;

use crate::definition::AttributeKey;
use crate::{
    definition::{Definition, LabelHead, Sentence},
    diagnostic::{Diagnostic, DiagnosticCode, Severity},
    kast::Term,
    provenance::GeneratingPass,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RemoveUnitError {
    pub diagnostics: Vec<Diagnostic>,
}

impl fmt::Display for RemoveUnitError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "unit removal produced {} errors",
            self.diagnostics.len()
        )
    }
}

impl std::error::Error for RemoveUnitError {}

/// Apply Java's final `RemoveUnit` transformation to rules.
pub fn remove_unit(definition: &Definition) -> Result<Definition, RemoveUnitError> {
    super::super::pipeline::run_standalone(
        definition,
        remove_unit_pass,
        Some(GeneratingPass::RemoveUnit),
    )
}

pub(crate) fn remove_unit_pass(
    input: &super::super::pipeline::PassInput<'_>,
    _: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, RemoveUnitError> {
    let resolved = input.resolved_raw().map_err(|error| RemoveUnitError {
        diagnostics: vec![plain_error(error.to_string())],
    })?;
    let views = resolved.views();
    let mut output = input.definition.clone();
    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let productions = views.production_catalog(module_id);
        for sentence in &mut module.local_sentences {
            // Only rules change; taking a mutable sentence copies a shared one.
            if !matches!(&**sentence, Sentence::Rule { .. }) {
                continue;
            }
            let sentence = crate::definition::sentence_mut(sentence);
            let Sentence::Rule {
                body,
                requires,
                ensures,
                ..
            } = sentence
            else {
                continue;
            };
            *body = transform(body, productions).map_err(|diagnostic| RemoveUnitError {
                diagnostics: vec![diagnostic],
            })?;
            *requires = transform(requires, productions).map_err(|diagnostic| RemoveUnitError {
                diagnostics: vec![diagnostic],
            })?;
            *ensures = transform(ensures, productions).map_err(|diagnostic| RemoveUnitError {
                diagnostics: vec![diagnostic],
            })?;
        }
    }
    Ok(output)
}

// Invariant: each call rebuilds an application of a label with a `unit` attribute as a left-nested binary chain of its flattened non-unit operands (the unit itself when none remain), and otherwise recurses into the immediate subterms of `term`; the finite `term` bounds the recursion.
fn transform(
    term: &Term,
    productions: &crate::definition::ProductionCatalog<'_>,
) -> Result<Term, Diagnostic> {
    let metadata = term.metadata().cloned();
    let transformed = match term.unannotated() {
        Term::Apply { label, arguments } => {
            let ids = productions.productions_for(&LabelHead::from(label));
            let attributes = match ids {
                [id] => match productions.production(*id) {
                    Sentence::Production { attributes, .. } => Some(attributes),
                    _ => unreachable!(),
                },
                _ => None,
            };
            let optional_cell = attributes.is_some_and(|attributes| {
                attributes.has(AttributeKey::Cell)
                    && attributes.string(AttributeKey::Multiplicity) == Some("?")
            });
            if !optional_cell
                && let Some(unit) =
                    attributes.and_then(|attributes| attributes.string(AttributeKey::Unit))
            {
                if attributes.is_none_or(|attributes| !attributes.has(AttributeKey::Assoc)) {
                    return Err(Diagnostic::error_at(
                        DiagnosticCode::InvalidUnitAttribute,
                        format!(
                            "production for {} has a unit attribute but is not associative",
                            label.name
                        ),
                        attributes.expect("unit attribute must be present"),
                    ));
                }
                let mut items = Vec::new();
                flatten(label, unit, arguments, &mut items);
                let Some(transformed) = items.into_iter().reduce(|left, right| Term::Apply {
                    label: label.clone(),
                    arguments: vec![left, right],
                }) else {
                    return Ok(Term::apply(unit, vec![]));
                };
                transformed
            } else {
                Term::Apply {
                    label: label.clone(),
                    arguments: arguments
                        .iter()
                        .map(|argument| transform(argument, productions))
                        .collect::<Result<Vec<_>, _>>()?,
                }
            }
        }
        Term::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(transform(left, productions)?),
            right: Box::new(transform(right, productions)?),
        },
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(transform(pattern, productions)?),
            alias: Box::new(transform(alias, productions)?),
        },
        Term::Sequence(items) => Term::Sequence(
            items
                .iter()
                .map(|item| transform(item, productions))
                .collect::<Result<Vec<_>, _>>()?,
        ),
        leaf @ (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }) => {
            leaf.clone()
        }
        Term::Annotated { .. } => unreachable!(),
    };
    Ok(match metadata {
        Some(metadata) => transformed.with_metadata(metadata),
        None => transformed,
    })
}

fn plain_error(message: impl Into<String>) -> Diagnostic {
    Diagnostic {
        severity: Severity::Error,
        code: DiagnosticCode::InvalidUnitAttribute,
        message: message.into(),
        source: None,
        location: None,
        input_addresses: Vec::new(),
    }
}

// Invariant: `output` holds, in order, every non-unit operand reached so far from `terms` through nested applications of `label`; each iteration consumes one element of `terms`, and each recursive call descends into the `arguments` of one nested `label` application.
fn flatten(label: &crate::kast::Label, unit: &str, terms: &[Term], output: &mut Vec<Term>) {
    for term in terms {
        match term.unannotated() {
            Term::Apply {
                label: nested,
                arguments,
            } if nested == label => flatten(label, unit, arguments, output),
            Term::Apply {
                label: nested,
                arguments,
            } if nested.name == unit && arguments.is_empty() => {}
            _ => output.push(term.clone()),
        }
    }
}
