//! Scala-compatible equality and ordering for K definition sentences.

use std::cmp::Ordering;
use std::collections::BTreeSet;

use serde_json::Value;

use super::ast::{
    Associativity, Attributes, LOCATION_ATTRIBUTE, ProductionItem, SOURCE_ATTRIBUTE, Sentence,
};
use crate::kast::Term;

const STRING_CLASS: &str = "java.lang.String";
const INTEGER_CLASS: &str = "java.lang.Integer";
const PRODUCTION_CLASS: &str = "org.kframework.definition.Production";
const SORT_CLASS: &str = "org.kframework.kore.Sort";
const LABEL_CLASS: &str = "org.kframework.kore.KLabel";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Error {
    UnorderableSentence(&'static str),
}

impl std::fmt::Display for Error {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnorderableSentence(node) => {
                write!(
                    formatter,
                    "Scala does not define sentence ordering for {node}"
                )
            }
        }
    }
}

impl std::error::Error for Error {}

/// Compare K terms using `org.kframework.kore.K.ord`.
pub fn compare_terms(left: &Term, right: &Term) -> Ordering {
    let left = left.unannotated();
    let right = right.unannotated();
    let rank = |term: &Term| match term {
        Term::InjectedLabel(_) => 0,
        Term::Rewrite { .. } => 1,
        Term::As { .. } => 2,
        Term::Variable { .. } => 3,
        Term::Sequence(_) => 4,
        Term::Apply { .. } => 5,
        Term::Token { .. } => 6,
        Term::Annotated { .. } => unreachable!(),
    };

    match rank(left).cmp(&rank(right)) {
        Ordering::Equal => {}
        ordering => return ordering,
    }

    match (left, right) {
        (Term::InjectedLabel(left), Term::InjectedLabel(right)) => left.cmp(right),
        (
            Term::Rewrite {
                left: left_lhs,
                right: left_rhs,
            },
            Term::Rewrite {
                left: right_lhs,
                right: right_rhs,
            },
        ) => compare_pair(
            (left_lhs, left_rhs),
            (right_lhs, right_rhs),
            |left, right| compare_terms(left, right),
        ),
        (
            Term::As {
                pattern: left_pattern,
                alias: left_alias,
            },
            Term::As {
                pattern: right_pattern,
                alias: right_alias,
            },
        ) => compare_pair(
            (left_pattern, left_alias),
            (right_pattern, right_alias),
            |left, right| compare_terms(left, right),
        ),
        (Term::Variable { name: left, .. }, Term::Variable { name: right, .. }) => left.cmp(right),
        (Term::Sequence(left), Term::Sequence(right)) => compare_slices(left, right, compare_terms),
        (
            Term::Apply {
                label: left_label,
                arguments: left_arguments,
            },
            Term::Apply {
                label: right_label,
                arguments: right_arguments,
            },
        ) => left_label
            .cmp(right_label)
            .then_with(|| compare_slices(left_arguments, right_arguments, compare_terms)),
        (
            Term::Token {
                token: left_token,
                sort: left_sort,
            },
            Term::Token {
                token: right_token,
                sort: right_sort,
            },
        ) => left_token.cmp(right_token).then(left_sort.cmp(right_sort)),
        _ => unreachable!("equal term ranks have matching variants"),
    }
}

/// Compare attributes using Scala's sorted `(key, class, value.toString)` triples.
pub fn compare_attributes(left: &Attributes, right: &Attributes) -> Ordering {
    attribute_triples(left).cmp(&attribute_triples(right))
}

/// Compare sentences using `org.kframework.definition.Sentence.ord`.
///
/// `Configuration` intentionally returns an error because Scala's ordering has
/// no case for that sentence type and throws if one reaches `sortedLocalSentences`.
pub fn compare_sentences(left: &Sentence, right: &Sentence) -> Result<Ordering, Error> {
    let left_rank = sentence_rank(left)?;
    let right_rank = sentence_rank(right)?;
    match left_rank.cmp(&right_rank) {
        Ordering::Equal => {}
        ordering => return Ok(ordering),
    }

    Ok(match (left, right) {
        (
            Sentence::SyntaxSort {
                parameters: left_parameters,
                sort: left_sort,
                attributes: left_attributes,
            },
            Sentence::SyntaxSort {
                parameters: right_parameters,
                sort: right_sort,
                attributes: right_attributes,
            },
        ) => compare_slices(left_parameters, right_parameters, |left, right| {
            left.name.cmp(&right.name)
        })
        .then(left_sort.name.cmp(&right_sort.name))
        .then_with(|| compare_attributes(left_attributes, right_attributes)),
        (
            Sentence::SortSynonym {
                new_sort: left_new,
                old_sort: left_old,
                attributes: left_attributes,
            },
            Sentence::SortSynonym {
                new_sort: right_new,
                old_sort: right_old,
                attributes: right_attributes,
            },
        ) => left_new
            .name
            .cmp(&right_new.name)
            .then(left_old.name.cmp(&right_old.name))
            .then_with(|| compare_attributes(left_attributes, right_attributes)),
        (
            Sentence::SyntaxLexical {
                name: left_name,
                regex: left_regex,
                attributes: left_attributes,
            },
            Sentence::SyntaxLexical {
                name: right_name,
                regex: right_regex,
                attributes: right_attributes,
            },
        ) => left_name
            .cmp(right_name)
            .then(left_regex.cmp(right_regex))
            .then_with(|| compare_attributes(left_attributes, right_attributes)),
        (
            Sentence::Production {
                label: left_label,
                attributes: left_attributes,
                ..
            },
            Sentence::Production {
                label: right_label,
                attributes: right_attributes,
                ..
            },
        ) => left_label
            .as_ref()
            .map(|label| &label.name)
            .cmp(&right_label.as_ref().map(|label| &label.name))
            .then_with(|| compare_attributes(left_attributes, right_attributes)),
        (
            Sentence::SyntaxAssociativity {
                associativity: left_associativity,
                tags: left_tags,
                attributes: left_attributes,
            },
            Sentence::SyntaxAssociativity {
                associativity: right_associativity,
                tags: right_tags,
                attributes: right_attributes,
            },
        ) => associativity_rank(*left_associativity)
            .cmp(&associativity_rank(*right_associativity))
            .then_with(|| sorted_tags(left_tags).cmp(&sorted_tags(right_tags)))
            .then_with(|| compare_attributes(left_attributes, right_attributes)),
        (
            Sentence::SyntaxPriority {
                priorities: left_priorities,
                attributes: left_attributes,
            },
            Sentence::SyntaxPriority {
                priorities: right_priorities,
                attributes: right_attributes,
            },
        ) => sorted_priorities(left_priorities)
            .cmp(&sorted_priorities(right_priorities))
            .then_with(|| compare_attributes(left_attributes, right_attributes)),
        (
            Sentence::ContextAlias {
                body: left_body,
                requires: left_requires,
                attributes: left_attributes,
            },
            Sentence::ContextAlias {
                body: right_body,
                requires: right_requires,
                attributes: right_attributes,
            },
        )
        | (
            Sentence::Context {
                body: left_body,
                requires: left_requires,
                attributes: left_attributes,
            },
            Sentence::Context {
                body: right_body,
                requires: right_requires,
                attributes: right_attributes,
            },
        ) => compare_terms(left_body, right_body)
            .then_with(|| compare_terms(left_requires, right_requires))
            .then_with(|| compare_attributes(left_attributes, right_attributes)),
        (
            Sentence::Rule {
                body: left_body,
                requires: left_requires,
                ensures: left_ensures,
                attributes: left_attributes,
            },
            Sentence::Rule {
                body: right_body,
                requires: right_requires,
                ensures: right_ensures,
                attributes: right_attributes,
            },
        )
        | (
            Sentence::Claim {
                body: left_body,
                requires: left_requires,
                ensures: left_ensures,
                attributes: left_attributes,
            },
            Sentence::Claim {
                body: right_body,
                requires: right_requires,
                ensures: right_ensures,
                attributes: right_attributes,
            },
        ) => compare_terms(left_body, right_body)
            .then_with(|| compare_terms(left_requires, right_requires))
            .then_with(|| compare_terms(left_ensures, right_ensures))
            .then_with(|| compare_attributes(left_attributes, right_attributes)),
        (
            Sentence::Bubble {
                sentence_type: left_type,
                contents: left_contents,
                attributes: left_attributes,
            },
            Sentence::Bubble {
                sentence_type: right_type,
                contents: right_contents,
                attributes: right_attributes,
            },
        ) => left_type
            .cmp(right_type)
            .then(left_contents.cmp(right_contents))
            .then_with(|| compare_attributes(left_attributes, right_attributes)),
        _ => unreachable!("equal sentence ranks have matching variants"),
    })
}

pub fn sort_sentences(sentences: &mut [Sentence]) -> Result<(), Error> {
    for sentence in sentences.iter() {
        sentence_rank(sentence)?;
    }
    sentences.sort_by(|left, right| {
        compare_sentences(left, right).expect("sentence kinds were prevalidated")
    });
    Ok(())
}

/// Scala sentence equality, including `Production`'s custom equality override.
pub fn sentence_equivalent(left: &Sentence, right: &Sentence) -> bool {
    match (left, right) {
        (
            Sentence::SyntaxSort {
                parameters: left_parameters,
                sort: left_sort,
                attributes: left_attributes,
            },
            Sentence::SyntaxSort {
                parameters: right_parameters,
                sort: right_sort,
                attributes: right_attributes,
            },
        ) => {
            left_parameters == right_parameters
                && left_sort == right_sort
                && left_attributes == right_attributes
        }
        (
            Sentence::SortSynonym {
                new_sort: left_new,
                old_sort: left_old,
                attributes: left_attributes,
            },
            Sentence::SortSynonym {
                new_sort: right_new,
                old_sort: right_old,
                attributes: right_attributes,
            },
        ) => left_new == right_new && left_old == right_old && left_attributes == right_attributes,
        (
            Sentence::SyntaxLexical {
                name: left_name,
                regex: left_regex,
                attributes: left_attributes,
            },
            Sentence::SyntaxLexical {
                name: right_name,
                regex: right_regex,
                attributes: right_attributes,
            },
        ) => {
            left_name == right_name
                && left_regex == right_regex
                && left_attributes == right_attributes
        }
        (
            Sentence::Production {
                label: left_label,
                parameters: left_parameters,
                sort: left_sort,
                items: left_items,
                attributes: left_attributes,
            },
            Sentence::Production {
                label: right_label,
                parameters: right_parameters,
                sort: right_sort,
                items: right_items,
                attributes: right_attributes,
            },
        ) => {
            left_label == right_label
                && left_parameters == right_parameters
                && left_sort == right_sort
                && production_items_equivalent(left_items, right_items)
                && production_label_attribute(left_label.as_ref(), left_attributes)
                    == production_label_attribute(right_label.as_ref(), right_attributes)
                && left_attributes.get_str("function") == right_attributes.get_str("function")
                && left_attributes.get_str("symbol") == right_attributes.get_str("symbol")
        }
        (
            Sentence::SyntaxAssociativity {
                associativity: left_associativity,
                tags: left_tags,
                attributes: left_attributes,
            },
            Sentence::SyntaxAssociativity {
                associativity: right_associativity,
                tags: right_tags,
                attributes: right_attributes,
            },
        ) => {
            left_associativity == right_associativity
                && tag_set(left_tags) == tag_set(right_tags)
                && left_attributes == right_attributes
        }
        (
            Sentence::SyntaxPriority {
                priorities: left_priorities,
                attributes: left_attributes,
            },
            Sentence::SyntaxPriority {
                priorities: right_priorities,
                attributes: right_attributes,
            },
        ) => {
            priority_sets(left_priorities) == priority_sets(right_priorities)
                && left_attributes == right_attributes
        }
        (
            Sentence::ContextAlias {
                body: left_body,
                requires: left_requires,
                attributes: left_attributes,
            },
            Sentence::ContextAlias {
                body: right_body,
                requires: right_requires,
                attributes: right_attributes,
            },
        )
        | (
            Sentence::Context {
                body: left_body,
                requires: left_requires,
                attributes: left_attributes,
            },
            Sentence::Context {
                body: right_body,
                requires: right_requires,
                attributes: right_attributes,
            },
        ) => {
            term_equivalent(left_body, right_body)
                && term_equivalent(left_requires, right_requires)
                && left_attributes == right_attributes
        }
        (
            Sentence::Rule {
                body: left_body,
                requires: left_requires,
                ensures: left_ensures,
                attributes: left_attributes,
            },
            Sentence::Rule {
                body: right_body,
                requires: right_requires,
                ensures: right_ensures,
                attributes: right_attributes,
            },
        )
        | (
            Sentence::Claim {
                body: left_body,
                requires: left_requires,
                ensures: left_ensures,
                attributes: left_attributes,
            },
            Sentence::Claim {
                body: right_body,
                requires: right_requires,
                ensures: right_ensures,
                attributes: right_attributes,
            },
        ) => {
            term_equivalent(left_body, right_body)
                && term_equivalent(left_requires, right_requires)
                && term_equivalent(left_ensures, right_ensures)
                && left_attributes == right_attributes
        }
        (
            Sentence::Configuration {
                body: left_body,
                ensures: left_ensures,
                attributes: left_attributes,
            },
            Sentence::Configuration {
                body: right_body,
                ensures: right_ensures,
                attributes: right_attributes,
            },
        ) => {
            term_equivalent(left_body, right_body)
                && term_equivalent(left_ensures, right_ensures)
                && left_attributes == right_attributes
        }
        (
            Sentence::Bubble {
                sentence_type: left_type,
                contents: left_contents,
                attributes: left_attributes,
            },
            Sentence::Bubble {
                sentence_type: right_type,
                contents: right_contents,
                attributes: right_attributes,
            },
        ) => {
            left_type == right_type
                && left_contents == right_contents
                && left_attributes == right_attributes
        }
        _ => false,
    }
}

fn sentence_rank(sentence: &Sentence) -> Result<u8, Error> {
    Ok(match sentence {
        Sentence::SyntaxSort { .. } => 0,
        Sentence::SortSynonym { .. } => 1,
        Sentence::SyntaxLexical { .. } => 2,
        Sentence::Production { .. } => 3,
        Sentence::SyntaxAssociativity { .. } => 4,
        Sentence::SyntaxPriority { .. } => 5,
        Sentence::ContextAlias { .. } => 6,
        Sentence::Context { .. } => 7,
        Sentence::Rule { .. } => 8,
        Sentence::Claim { .. } => 9,
        Sentence::Bubble { .. } => 10,
        Sentence::Configuration { .. } => {
            return Err(Error::UnorderableSentence("KConfiguration"));
        }
    })
}

fn associativity_rank(associativity: Associativity) -> u8 {
    match associativity {
        Associativity::Left => 0,
        Associativity::Right => 1,
        Associativity::NonAssoc => 2,
        Associativity::Unspecified => 3,
    }
}

fn compare_pair<T>(
    left: (&T, &T),
    right: (&T, &T),
    compare: impl Fn(&T, &T) -> Ordering,
) -> Ordering {
    compare(left.0, right.0).then_with(|| compare(left.1, right.1))
}

fn compare_slices<T>(left: &[T], right: &[T], compare: impl Fn(&T, &T) -> Ordering) -> Ordering {
    for (left, right) in left.iter().zip(right) {
        match compare(left, right) {
            Ordering::Equal => {}
            ordering => return ordering,
        }
    }
    left.len().cmp(&right.len())
}

fn sorted_tags(tags: &[String]) -> Vec<&str> {
    tag_set(tags).into_iter().collect()
}

fn tag_set(tags: &[String]) -> BTreeSet<&str> {
    tags.iter().map(String::as_str).collect()
}

fn sorted_priorities(priorities: &[Vec<String>]) -> Vec<Vec<&str>> {
    priorities.iter().map(|tags| sorted_tags(tags)).collect()
}

fn priority_sets(priorities: &[Vec<String>]) -> Vec<BTreeSet<&str>> {
    priorities.iter().map(|tags| tag_set(tags)).collect()
}

fn production_label_attribute<'a>(
    label: Option<&'a crate::kast::Label>,
    attributes: &'a Attributes,
) -> Option<&'a str> {
    attributes
        .get_str("klabel")
        .or_else(|| label.map(|label| label.name.as_str()))
}

fn production_items_equivalent(left: &[ProductionItem], right: &[ProductionItem]) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(left, right)| match (left, right) {
                (
                    ProductionItem::NonTerminal {
                        sort: left_sort,
                        name: left_name,
                    },
                    ProductionItem::NonTerminal {
                        sort: right_sort,
                        name: right_name,
                    },
                ) => left_sort == right_sort && left_name == right_name,
                (
                    ProductionItem::RegexTerminal {
                        regex: left_regex, ..
                    },
                    ProductionItem::RegexTerminal {
                        regex: right_regex, ..
                    },
                ) => left_regex == right_regex,
                (ProductionItem::Terminal(left), ProductionItem::Terminal(right)) => left == right,
                _ => false,
            })
}

fn term_equivalent(left: &Term, right: &Term) -> bool {
    compare_terms(left, right) == Ordering::Equal
}

fn attribute_triples(attributes: &Attributes) -> Vec<(String, String, String)> {
    attributes
        .entries()
        .iter()
        .map(|(key, value)| {
            (
                key.clone(),
                attribute_class(key).into(),
                attribute_value_string(key, value),
            )
        })
        .collect()
}

fn attribute_class(key: &str) -> &str {
    match key {
        LOCATION_ATTRIBUTE => LOCATION_ATTRIBUTE,
        SOURCE_ATTRIBUTE => SOURCE_ATTRIBUTE,
        PRODUCTION_CLASS => PRODUCTION_CLASS,
        SORT_CLASS | "predicate" | "cellOptAbsent" | "cellFragment" | "sortParams" => SORT_CLASS,
        "bracketLabel" => LABEL_CLASS,
        "contentStartColumn" | "contentStartLine" => INTEGER_CLASS,
        _ => STRING_CLASS,
    }
}

fn attribute_value_string(key: &str, value: &Value) -> String {
    if key == LOCATION_ATTRIBUTE
        && let Some(values) = value.as_array()
        && values.len() == 4
    {
        return format!(
            "Location({},{},{},{})",
            values[0], values[1], values[2], values[3]
        );
    }
    if key == SOURCE_ATTRIBUTE
        && let Some(source) = value.as_str()
    {
        return format!("Source({source})");
    }
    if matches!(
        key,
        SORT_CLASS | "predicate" | "cellOptAbsent" | "cellFragment" | "sortParams"
    ) && let Some(sort) = json_sort_string(value)
    {
        return sort;
    }
    if key == "bracketLabel"
        && let Some(label) = json_label_string(value)
    {
        return label;
    }
    if key == PRODUCTION_CLASS
        && let Some(production) = json_production_string(value)
    {
        return production;
    }
    match value {
        Value::String(value) => value.clone(),
        value => value.to_string(),
    }
}

fn json_sort_string(value: &Value) -> Option<String> {
    let object = value.as_object()?;
    if object.get("node")?.as_str()? != "KSort" {
        return None;
    }
    let name = object.get("name")?.as_str()?;
    let parameters = object.get("params")?.as_array()?;
    if parameters.is_empty() {
        return Some(name.into());
    }
    Some(format!(
        "{name}{{{}}}",
        parameters
            .iter()
            .map(json_sort_string)
            .collect::<Option<Vec<_>>>()?
            .join(",")
    ))
}

fn json_label_string(value: &Value) -> Option<String> {
    let object = value.as_object()?;
    if object.get("node")?.as_str()? != "KLabel" {
        return None;
    }
    let name = object.get("name")?.as_str()?;
    let parameters = object.get("params")?.as_array()?;
    if parameters.is_empty() {
        return Some(name.into());
    }
    Some(format!(
        "{name}{{{}}}",
        parameters
            .iter()
            .map(json_sort_string)
            .collect::<Option<Vec<_>>>()?
            .join(",")
    ))
}

fn json_production_string(value: &Value) -> Option<String> {
    let object = value.as_object()?;
    if object.get("node")?.as_str()? != "KProduction" {
        return None;
    }
    let parameters = object
        .get("params")?
        .as_array()?
        .iter()
        .map(json_sort_string)
        .collect::<Option<Vec<_>>>()?;
    let sort = json_sort_string(object.get("sort")?)?;
    let items = object
        .get("productionItems")?
        .as_array()?
        .iter()
        .map(json_production_item_string)
        .collect::<Option<Vec<_>>>()?;
    let attributes = json_attributes_postfix(object.get("att")?, true)?;
    let parameters = if parameters.is_empty() {
        String::new()
    } else {
        format!("{{{}}} ", parameters.join(", "))
    };
    Some(format!(
        "syntax {parameters}{sort} ::= {}{attributes}",
        items.join(" ")
    ))
}

fn json_production_item_string(value: &Value) -> Option<String> {
    let object = value.as_object()?;
    match object.get("node")?.as_str()? {
        "KNonTerminal" => {
            let sort = json_sort_string(object.get("sort")?)?;
            Some(match object.get("name").and_then(Value::as_str) {
                Some(name) => format!("{name}:{sort}"),
                None => sort,
            })
        }
        "KRegexTerminal" => Some(format!(
            "r{}",
            crate::kore::string::quote(object.get("regex")?.as_str()?)
        )),
        "KTerminal" => Some(crate::kore::string::quote(object.get("value")?.as_str()?)),
        _ => None,
    }
}

fn json_attributes_postfix(value: &Value, omit_source: bool) -> Option<String> {
    let object = value.as_object()?;
    if object.get("node")?.as_str()? != "KAtt" {
        return None;
    }
    let entries = object.get("att")?.as_object()?;
    let mut rendered = entries
        .iter()
        .filter(|(key, _)| {
            !omit_source || (key.as_str() != SOURCE_ATTRIBUTE && key.as_str() != LOCATION_ATTRIBUTE)
        })
        .map(|(key, value)| {
            if value.as_str() == Some("") && attribute_class(key) == STRING_CLASS {
                key.clone()
            } else {
                format!("{key}({})", attribute_value_string(key, value))
            }
        })
        .collect::<Vec<_>>();
    rendered.sort();
    if rendered.is_empty() {
        Some(String::new())
    } else {
        Some(format!(" [{}]", rendered.join(", ")))
    }
}
