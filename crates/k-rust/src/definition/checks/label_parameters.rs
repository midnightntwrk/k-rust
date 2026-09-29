//! This definition check traverses the terms of rule-like sentences once, linearly, and records no dedicated counter.
//!
//! Rejection of sort parameters written on the labels of rule-like sentences.
//!
//! Every sort parameter a label of a rule-like sentence carries after loading was written by the
//! caller: the source parser writes none, and compiler passes write theirs later. Two consumers
//! cannot take a written one. Sort injection instantiates each parametric label from its
//! arguments and position, which casts fix, so a written parameter is either redundant or would
//! be silently replaced. Configuration expansion recognizes cell wrappers by label name and
//! moves configuration content into generated sentences, so it would drop a parameter on a
//! configuration's labels or attach it to a sentence the caller did not write. The check
//! therefore runs on the caller's sentences, before either consumer.

use std::fmt;

use crate::definition::{Definition, Location, Sentence};
use crate::kast::{Sort, Term};
use crate::provenance::GeneratingPass;

/// A label of a rule-like sentence that carries written sort parameters.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct LabelParameterError {
    pub(crate) label: String,
    pub(crate) parameters: Vec<Sort>,
}

impl fmt::Display for LabelParameterError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "KLabel {:?} carries the sort parameters {{{}}}",
            self.label,
            self.parameters
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

/// A [`LabelParameterError`] located at a sentence of a definition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct SentenceLabelParameterError {
    /// The module whose local sentence carries the label.
    pub(crate) module: String,
    /// The sentence's index among the module's local sentences.
    pub(crate) sentence: usize,
    pub(crate) source: Option<String>,
    pub(crate) location: Option<Location>,
    /// The pass that generated the sentence, when a pass did.
    pub(crate) origin: Option<GeneratingPass>,
    pub(crate) error: Box<LabelParameterError>,
}

impl SentenceLabelParameterError {
    fn at(
        module: &str,
        sentence_index: usize,
        sentence: &Sentence,
        error: LabelParameterError,
    ) -> Self {
        let attributes = sentence.attributes();
        Self {
            module: module.to_owned(),
            sentence: sentence_index,
            source: attributes.source().map(str::to_owned),
            location: attributes.location(),
            origin: attributes.origin_record().map(|record| record.pass),
            error: Box::new(error),
        }
    }
}

/// Reject the first label of a rule-like sentence (rule, claim, context, context alias,
/// configuration) that carries sort parameters.
pub(crate) fn reject_label_parameters(sentence: &Sentence) -> Result<(), LabelParameterError> {
    let terms: &[&Term] = match sentence {
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
        } => &[body, requires, ensures],
        Sentence::Context { body, requires, .. }
        | Sentence::ContextAlias { body, requires, .. } => &[body, requires],
        Sentence::Configuration { body, ensures, .. } => &[body, ensures],
        _ => &[],
    };
    let mut found = None;
    for term in terms {
        term.visit_preorder(&mut |term| {
            if found.is_some() {
                return;
            }
            if let Term::Apply { label, .. } | Term::InjectedLabel(label) = term
                && !label.parameters.is_empty()
            {
                found = Some(LabelParameterError {
                    label: label.name.clone(),
                    parameters: label.parameters.clone(),
                });
            }
        });
    }
    found.map_or(Ok(()), Err)
}

/// [`reject_label_parameters`] over every sentence of `definition`, reporting the first one
/// with its module, index and source location.
pub(crate) fn reject_label_parameters_in_definition(
    definition: &Definition,
) -> Result<(), SentenceLabelParameterError> {
    for module in &definition.modules {
        for (sentence_index, sentence) in module.local_sentences.iter().enumerate() {
            reject_label_parameters(sentence).map_err(|error| {
                SentenceLabelParameterError::at(&module.name, sentence_index, sentence, error)
            })?;
        }
    }
    Ok(())
}
