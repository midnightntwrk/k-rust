//! K sentence equality for deduplication, including `Production`'s custom equality override.

use std::collections::BTreeSet;

use super::ast::{Attributes, ProductionItem, Sentence};
use crate::definition::AttributeKey;
use crate::kast::Term;

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
                && left_attributes.string(AttributeKey::Function)
                    == right_attributes.string(AttributeKey::Function)
                && left_attributes.string(AttributeKey::Symbol)
                    == right_attributes.string(AttributeKey::Symbol)
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

fn tag_set(tags: &[String]) -> BTreeSet<&str> {
    tags.iter().map(String::as_str).collect()
}

fn priority_sets(priorities: &[Vec<String>]) -> Vec<BTreeSet<&str>> {
    priorities.iter().map(|tags| tag_set(tags)).collect()
}

fn production_label_attribute<'a>(
    label: Option<&'a crate::kast::Label>,
    attributes: &'a Attributes,
) -> Option<&'a str> {
    attributes
        .string(AttributeKey::Klabel)
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

/// Structural term equality that ignores annotations and variable sorts.
///
/// K compares rule bodies as `K` terms, whose variable equality ignores the sort and
/// which never carry the parser's metadata annotations.
pub fn term_equivalent(left: &Term, right: &Term) -> bool {
    match (left.unannotated(), right.unannotated()) {
        (Term::InjectedLabel(left), Term::InjectedLabel(right)) => left == right,
        (
            Term::Rewrite {
                left: left_lhs,
                right: left_rhs,
            },
            Term::Rewrite {
                left: right_lhs,
                right: right_rhs,
            },
        ) => term_equivalent(left_lhs, right_lhs) && term_equivalent(left_rhs, right_rhs),
        (
            Term::As {
                pattern: left_pattern,
                alias: left_alias,
            },
            Term::As {
                pattern: right_pattern,
                alias: right_alias,
            },
        ) => {
            term_equivalent(left_pattern, right_pattern) && term_equivalent(left_alias, right_alias)
        }
        (Term::Variable { name: left, .. }, Term::Variable { name: right, .. }) => left == right,
        (Term::Sequence(left), Term::Sequence(right)) => terms_equivalent(left, right),
        (
            Term::Apply {
                label: left_label,
                arguments: left_arguments,
            },
            Term::Apply {
                label: right_label,
                arguments: right_arguments,
            },
        ) => left_label == right_label && terms_equivalent(left_arguments, right_arguments),
        (
            Term::Token {
                token: left_token,
                sort: left_sort,
            },
            Term::Token {
                token: right_token,
                sort: right_sort,
            },
        ) => left_token == right_token && left_sort == right_sort,
        _ => false,
    }
}

fn terms_equivalent(left: &[Term], right: &[Term]) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(left, right)| term_equivalent(left, right))
}
