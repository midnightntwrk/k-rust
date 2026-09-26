//! This transformation pass resolves required views, transforms sentences and terms, records origins, and retargets metadata when needed.
//! Its named `--timings` phase measures total cost; the shared pass scaffolding counts resolutions (`KompileResolveCalls`), copied sentences (`KompileSentenceCopies`), and partial orders built (`KompilePartialOrdersBuilt`), and `KompileSentencesTransformed` is added once per compile in `compile.rs`.
//!
//! Allocate compile-time integer constants for fresh configuration variables.

use std::{collections::BTreeMap, fmt};

use crate::definition::AttributeKey;
use crate::names::BuiltinSort;
use crate::{
    definition::{Definition, Sentence},
    diagnostic::{Diagnostic, DiagnosticCode},
    kast::{Sort, Term},
    provenance::{GeneratingPass, record_generated_origins},
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolveFreshConfigConstantsError {
    pub diagnostics: Vec<Diagnostic>,
}

impl fmt::Display for ResolveFreshConfigConstantsError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "fresh configuration constant resolution produced {} errors",
            self.diagnostics.len()
        )
    }
}

impl std::error::Error for ResolveFreshConfigConstantsError {}

/// Apply Java's `ResolveFreshConfigConstants` pass and return the next unused counter value.
pub fn resolve_fresh_config_constants(
    definition: &Definition,
) -> Result<(Definition, usize), ResolveFreshConfigConstantsError> {
    let (output, count) = super::super::pipeline::run_standalone_raw(
        definition,
        resolve_fresh_config_constants_pass,
    )?;
    Ok((
        record_generated_origins(
            definition,
            output,
            GeneratingPass::ResolveFreshConfigConstants,
        ),
        count,
    ))
}

pub(crate) fn resolve_fresh_config_constants_pass(
    input: &super::super::pipeline::PassInput<'_>,
    state: &mut super::super::pipeline::PipelineState,
) -> Result<(Definition, usize), ResolveFreshConfigConstantsError> {
    let mut output = input.definition.clone();
    let mut counter = 0usize;
    let mut named = BTreeMap::<String, usize>::new();
    let mut diagnostics = Vec::new();
    for module in &mut output.modules {
        for sentence in &mut module.local_sentences {
            // Only initializer rules change; taking a mutable sentence copies a shared one.
            if !matches!(&**sentence, Sentence::Rule { attributes, .. }
                if attributes.has(AttributeKey::Initializer))
            {
                continue;
            }
            let sentence = crate::definition::sentence_mut(sentence);
            let Sentence::Rule {
                body, attributes, ..
            } = sentence
            else {
                continue;
            };
            if !attributes.has(AttributeKey::Initializer) {
                continue;
            }
            let taken = std::mem::replace(body, Term::Sequence(Vec::new()));
            *body = transform(
                taken,
                true,
                attributes,
                &mut counter,
                &mut named,
                &mut diagnostics,
            );
        }
    }
    if diagnostics.is_empty() {
        state.fresh_config_count = Some(counter);
        Ok((output, counter))
    } else {
        diagnostics.sort();
        Err(ResolveFreshConfigConstantsError { diagnostics })
    }
}

// Invariant: `*counter` is the next unused fresh value, `named` maps each named `!` variable met so far on a right side to its value, and each `!_Gen` occurrence takes a new value; each call recurses into the immediate subterms of `term`, leaving rewrite left sides unchanged.
fn transform(
    term: Term,
    on_rhs: bool,
    sentence_attributes: &crate::definition::Attributes,
    counter: &mut usize,
    named: &mut BTreeMap<String, usize>,
    diagnostics: &mut Vec<Diagnostic>,
) -> Term {
    let metadata = term.metadata().cloned();
    let rebuilt = match term.into_unannotated() {
        Term::Variable { name, sort } if on_rhs && name.starts_with('!') => {
            if !sort
                .as_ref()
                .is_some_and(|sort| sort.is_builtin(BuiltinSort::Int))
            {
                diagnostics.push(Diagnostic::error_at(
                    DiagnosticCode::InvalidFreshConstant,
                    "Can't resolve fresh configuration variable not of sort Int",
                    sentence_attributes,
                ));
                Term::Variable { name, sort }
            } else {
                let value = if name.starts_with("!_Gen") {
                    let value = *counter;
                    *counter += 1;
                    value
                } else {
                    *named.entry(name).or_insert_with(|| {
                        let value = *counter;
                        *counter += 1;
                        value
                    })
                };
                Term::Token {
                    token: value.to_string(),
                    sort: Sort::builtin(BuiltinSort::Int),
                }
            }
        }
        Term::Rewrite { left, right } => Term::Rewrite {
            left,
            right: Box::new(transform(
                *right,
                true,
                sentence_attributes,
                counter,
                named,
                diagnostics,
            )),
        },
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(transform(
                *pattern,
                on_rhs,
                sentence_attributes,
                counter,
                named,
                diagnostics,
            )),
            alias: Box::new(transform(
                *alias,
                on_rhs,
                sentence_attributes,
                counter,
                named,
                diagnostics,
            )),
        },
        Term::Sequence(items) => Term::Sequence(
            items
                .into_iter()
                .map(|item| {
                    transform(
                        item,
                        on_rhs,
                        sentence_attributes,
                        counter,
                        named,
                        diagnostics,
                    )
                })
                .collect(),
        ),
        Term::Apply { label, arguments } => Term::Apply {
            label,
            arguments: arguments
                .into_iter()
                .map(|argument| {
                    transform(
                        argument,
                        on_rhs,
                        sentence_attributes,
                        counter,
                        named,
                        diagnostics,
                    )
                })
                .collect(),
        },
        leaf @ (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }) => leaf,
        Term::Annotated { .. } => unreachable!("into_unannotated strips metadata"),
    };
    metadata.map_or(rebuilt.clone(), |metadata| rebuilt.with_metadata(metadata))
}
