//! Assign Java-compatible stable identifiers to rules and claims.

use std::collections::BTreeMap;

use serde_json::Value;
use sha3::{Digest, Sha3_256};

use crate::{
    definition::{Attributes, Definition, Sentence},
    kast::Term,
};

const PRESERVED_ATTRIBUTES: &[&str] = &[
    "concrete",
    "symbolic",
    "owise",
    "priority",
    "simplification",
    "anywhere",
    "non-executable",
];

/// Apply Java's `NumberSentences` transformation to every rule and claim.
pub fn number_sentences(definition: &Definition) -> Definition {
    let mut output = definition.clone();
    for module in &mut output.modules {
        for sentence in &mut module.local_sentences {
            number_sentence(sentence);
        }
    }
    output
}

fn number_sentence(sentence: &mut Sentence) {
    let (Sentence::Rule { attributes, .. } | Sentence::Claim { attributes, .. }) = sentence else {
        return;
    };
    if attributes.get("UNIQUE_ID").is_some() {
        return;
    }

    let semantic_attributes = Attributes::new(
        PRESERVED_ATTRIBUTES
            .iter()
            .filter_map(|key| {
                attributes
                    .get(key)
                    .map(|value| ((*key).to_owned(), value.clone()))
            })
            .collect::<BTreeMap<_, _>>(),
    );
    let text = sentence_hash_text(sentence, &semantic_attributes);
    let id = format!("{:x}", Sha3_256::digest(text.as_bytes()));
    match sentence {
        Sentence::Rule { attributes, .. } | Sentence::Claim { attributes, .. } => {
            attributes.insert("UNIQUE_ID", Value::String(id));
        }
        _ => unreachable!("guard selected a rule or claim"),
    }
}

fn sentence_hash_text(sentence: &Sentence, attributes: &Attributes) -> String {
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
        // `NormalizeVariables.normalize(Sentence)` handles Rule and Context but not Claim in the
        // pinned Java frontend. Preserve that observable quirk for compatible identifiers.
        Sentence::Claim {
            body,
            requires,
            ensures,
            ..
        } => format!(
            "claim {body} requires {requires} ensures {ensures} {}",
            format_attributes(attributes)
        ),
        _ => unreachable!("only rules and claims are numbered"),
    }
}

fn normalize_rule_variables(body: &Term, requires: &Term, ensures: &Term) -> [Term; 3] {
    // Scala's KVariable equality is name-only; its sort lives in attributes and does not
    // distinguish normalization identities.
    let mut variables = BTreeMap::<String, String>::new();
    let mut counter = 0usize;
    [body, requires, ensures].map(|term| normalize_term(term, &mut variables, &mut counter))
}

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
            label: label.clone(),
            arguments: arguments
                .iter()
                .map(|argument| normalize_term(argument, variables, counter))
                .collect(),
        },
        Term::InjectedLabel(label) => Term::InjectedLabel(label.clone()),
        Term::Token { token, sort } => Term::Token {
            token: token.clone(),
            sort: sort.clone(),
        },
        Term::Annotated { .. } => unreachable!("unannotated strips metadata"),
    };
    term.metadata()
        .cloned()
        .map_or(normalized.clone(), |metadata| {
            normalized.with_metadata(metadata)
        })
}

fn format_attributes(attributes: &Attributes) -> String {
    if attributes.is_empty() {
        return String::new();
    }
    let values = attributes
        .entries()
        .iter()
        .map(|(key, value)| match value {
            Value::String(value) if value.is_empty() => key.clone(),
            Value::String(value) => format!("{key}({value})"),
            Value::Null => key.clone(),
            value => format!("{key}({value})"),
        })
        .collect::<Vec<_>>();
    format!("[{}]", values.join(", "))
}

#[cfg(test)]
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
            sentence_hash_text(&make("X"), &Attributes::default()),
            sentence_hash_text(&make("Y"), &Attributes::default())
        );
    }

    #[test]
    fn matches_reference_sentence_spelling() {
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
            sentence_hash_text(&sentence, &Attributes::default()),
            "rule f(_0)=>_0 requires #token(\"true\",\"Bool\") ensures #token(\"true\",\"Bool\") "
        );
    }
}
