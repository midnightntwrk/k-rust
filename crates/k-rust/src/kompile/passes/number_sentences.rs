//! ```toml algorithm
//! id = "kompile.sentences.number"
//! name = "stable numbering of sentences by normalized digest"
//! sites = ["number_sentences", "number_sentences_pass", "number_sentence", "unique_id_text"]
//! variable = "N = normalized sentence and term nodes; h = term height"
//! counters = ["KompileSentenceCopies"]
//!
//! [[cost]]
//! mode = "one definition"
//! bound = "O(N x h)"
//! ```
//!
//! This transformation pass assigns UNIQUE_ID attributes to rules and claims and records no origins.
//! Its named `--timings` phase measures total cost; the shared pass scaffolding counts resolutions (`KompileResolveCalls`), copied sentences (`KompileSentenceCopies`), and partial orders built (`KompilePartialOrdersBuilt`), and `KompileSentencesTransformed` is added once per compile in `compile.rs`.
//!
//! Assign stable `UNIQUE_ID` identifiers to rules and claims.
//!
//! An identifier is a digest of the sentence's text in the identifier format of K's `kompile`, so
//! that a definition compiled by either compiler names a sentence alike; the comments below that
//! describe the hashed text describe that format.
#![deny(clippy::wildcard_enum_match_arm)]

use std::{collections::BTreeMap, convert::Infallible, fmt::Write};

use serde_json::Value;
use sha3::{Digest, Sha3_256};

use crate::definition::AttributeKey;
use crate::{
    definition::{Attributes, Definition, Sentence},
    kast::Term,
};

const PRESERVED_ATTRIBUTES: [AttributeKey; 7] = [
    AttributeKey::Concrete,
    AttributeKey::Symbolic,
    AttributeKey::Owise,
    AttributeKey::Priority,
    AttributeKey::Simplification,
    AttributeKey::Anywhere,
    AttributeKey::NonExecutable,
];

/// Give every rule and claim its `UNIQUE_ID` attribute.
pub fn number_sentences(definition: &Definition) -> Definition {
    super::super::pipeline::run_standalone(definition, number_sentences_pass, None)
        .unwrap_or_else(|error| match error {})
}

pub(crate) fn number_sentences_pass(
    input: &super::super::pipeline::PassInput<'_>,
    _: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, Infallible> {
    let mut output = input.definition.clone();
    for module in &mut output.modules {
        for sentence in &mut module.local_sentences {
            // Only rules and claims without an identifier change. The kind is decided before
            // taking a mutable sentence, which copies a shared one, so every other sentence stays
            // shared.
            match &**sentence {
                Sentence::Rule { attributes, .. } | Sentence::Claim { attributes, .. }
                    if !attributes.has(AttributeKey::UniqueId) =>
                {
                    number_sentence(crate::definition::sentence_mut(sentence));
                }
                Sentence::SyntaxSort { .. }
                | Sentence::SortSynonym { .. }
                | Sentence::SyntaxLexical { .. }
                | Sentence::Production { .. }
                | Sentence::SyntaxAssociativity { .. }
                | Sentence::SyntaxPriority { .. }
                | Sentence::ContextAlias { .. }
                | Sentence::Context { .. }
                | Sentence::Rule { .. }
                | Sentence::Claim { .. }
                | Sentence::Configuration { .. }
                | Sentence::Bubble { .. } => {}
            }
        }
    }
    Ok(output)
}

pub(crate) fn number_sentence(sentence: &mut Sentence) {
    let (Sentence::Rule { attributes, .. } | Sentence::Claim { attributes, .. }) = sentence else {
        return;
    };
    if attributes.has(AttributeKey::UniqueId) {
        return;
    }

    let semantic_attributes = Attributes::from_pairs(
        PRESERVED_ATTRIBUTES
            .into_iter()
            .filter_map(|key| attributes.value(key).map(|value| (key, value.clone()))),
    );
    let text = unique_id_text(sentence, &semantic_attributes);
    let digest = Sha3_256::digest(text.as_bytes());
    let mut id = String::with_capacity(digest.len() * 2);
    for byte in digest {
        write!(id, "{byte:02x}").expect("writing to a string cannot fail");
    }
    match sentence {
        Sentence::Rule { attributes, .. } | Sentence::Claim { attributes, .. } => {
            attributes.set(AttributeKey::UniqueId, Value::String(id));
        }
        Sentence::SyntaxSort { .. }
        | Sentence::SortSynonym { .. }
        | Sentence::SyntaxLexical { .. }
        | Sentence::Production { .. }
        | Sentence::SyntaxAssociativity { .. }
        | Sentence::SyntaxPriority { .. }
        | Sentence::ContextAlias { .. }
        | Sentence::Context { .. }
        | Sentence::Configuration { .. }
        | Sentence::Bubble { .. } => unreachable!("guard selected a rule or claim"),
    }
}

pub(crate) fn unique_id_text(sentence: &Sentence, attributes: &Attributes) -> String {
    match sentence {
        Sentence::Rule {
            body,
            requires,
            ensures,
            ..
        } => {
            let [body, requires, ensures] = normalize_rule_variables(body, requires, ensures);
            format!(
                "rule {body} requires {requires} ensures {ensures} {}",
                format_attributes(attributes)
            )
        }
        // A claim's text is hashed without variable normalization, unlike a rule's, so its
        // identifier changes with its variable names; this is part of the identifier format.
        Sentence::Claim {
            body,
            requires,
            ensures,
            ..
        } => format!(
            "claim {body} requires {requires} ensures {ensures} {}",
            format_attributes(attributes)
        ),
        Sentence::SyntaxSort { .. }
        | Sentence::SortSynonym { .. }
        | Sentence::SyntaxLexical { .. }
        | Sentence::Production { .. }
        | Sentence::SyntaxAssociativity { .. }
        | Sentence::SyntaxPriority { .. }
        | Sentence::ContextAlias { .. }
        | Sentence::Context { .. }
        | Sentence::Configuration { .. }
        | Sentence::Bubble { .. } => unreachable!("only rules and claims are numbered"),
    }
}

fn normalize_rule_variables(body: &Term, requires: &Term, ensures: &Term) -> [Term; 3] {
    // Variables are normalized by name alone: a name denotes one variable of the sentence
    // whatever sorts its occurrences are annotated with.
    let mut variables = BTreeMap::<String, String>::new();
    let mut counter = 0usize;
    [body, requires, ensures].map(|term| normalize_term(term, &mut variables, &mut counter))
}

// Invariant: `variables` maps each variable name met so far to `_<n>`, where `n` is its first-occurrence rank, and `*counter` equals `variables.len()`; each call recurses into the immediate subterms of `term`.
fn normalize_term(
    term: &Term,
    variables: &mut BTreeMap<String, String>,
    counter: &mut usize,
) -> Term {
    let normalized = match term.unannotated() {
        Term::Variable { name, sort } => {
            let name = variables
                .entry(name.clone())
                .or_insert_with(|| {
                    let name = format!("_{counter}");
                    *counter += 1;
                    name
                })
                .clone();
            Term::Variable {
                name,
                sort: sort.clone(),
            }
        }
        Term::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(normalize_term(left, variables, counter)),
            right: Box::new(normalize_term(right, variables, counter)),
        },
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(normalize_term(pattern, variables, counter)),
            alias: Box::new(normalize_term(alias, variables, counter)),
        },
        Term::Sequence(items) => Term::Sequence(
            items
                .iter()
                .map(|item| normalize_term(item, variables, counter))
                .collect(),
        ),
        Term::Apply { label, arguments } => Term::Apply {
            label: normalize_label(label),
            arguments: arguments
                .iter()
                .map(|argument| normalize_term(argument, variables, counter))
                .collect(),
        },
        Term::InjectedLabel(label) => Term::InjectedLabel(normalize_label(label)),
        Term::Token { token, sort } => Term::Token {
            token: token.clone(),
            sort: sort.clone(),
        },
        Term::Annotated { .. } => unreachable!("unannotated strips metadata"),
    };
    match term.metadata().cloned() {
        Some(metadata) => normalized.with_metadata(metadata),
        None => normalized,
    }
}

fn normalize_label(label: &crate::kast::Label) -> crate::kast::Label {
    // The hashed text omits instantiated production parameters, but keeps the explicit
    // polymorphic placeholder carried by generated subsort and ML sentences.
    if label.parameters.iter().any(|sort| sort.is_rigid_variable()) {
        crate::kast::Label::with_parameters(
            label.name.clone(),
            label
                .parameters
                .iter()
                .map(|sort| crate::kast::Sort::new(sort.name.clone()))
                .collect(),
        )
    } else {
        crate::kast::Label::new(label.name.clone())
    }
}

fn format_attributes(attributes: &Attributes) -> String {
    if attributes.is_empty() {
        return String::new();
    }
    let values = attributes
        .wire_entries()
        .map(|(key, value)| match value {
            Value::String(value) if value.is_empty() => key.to_owned(),
            Value::String(value) => format!("{key}({value})"),
            Value::Null => key.to_owned(),
            value @ Value::Bool(_)
            | value @ Value::Number(_)
            | value @ Value::Array(_)
            | value @ Value::Object(_) => format!("{key}({value})"),
        })
        .collect::<Vec<_>>();
    format!("[{}]", values.join(", "))
}

#[cfg(test)]
#[allow(clippy::wildcard_enum_match_arm)]
mod tests {
    use super::*;
    use crate::kast::{Label, Sort};

    fn truth() -> Term {
        Term::Token {
            token: "true".into(),
            sort: Sort::new("Bool"),
        }
    }

    #[test]
    fn alpha_equivalent_rules_have_the_same_hash_text() {
        let make = |name: &str| Sentence::Rule {
            body: Term::apply("f", vec![Term::variable(name)]),
            requires: truth(),
            ensures: truth(),
            attributes: Attributes::default(),
        };
        assert_eq!(
            unique_id_text(&make("X"), &Attributes::default()),
            unique_id_text(&make("Y"), &Attributes::default())
        );
    }

    #[test]
    fn unique_id_text_numbers_rule_variables_by_first_occurrence() {
        let sentence = Sentence::Rule {
            body: Term::Rewrite {
                left: Box::new(Term::Apply {
                    label: Label::new("f"),
                    arguments: vec![Term::variable("X")],
                }),
                right: Box::new(Term::variable("X")),
            },
            requires: truth(),
            ensures: truth(),
            attributes: Attributes::default(),
        };
        assert_eq!(
            unique_id_text(&sentence, &Attributes::default()),
            "rule f(_0)=>_0 requires #token(\"true\",\"Bool\") ensures #token(\"true\",\"Bool\") "
        );
    }
}
