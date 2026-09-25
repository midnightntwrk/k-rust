//! ```toml algorithm
//! id = "definition.equivalence.sentence"
//! name = "structural sentence equivalence"
//! sites = ["sentence_equivalent", "production_identity", "canonical_production_payload"]
//! variable = "N = compared or encoded sentence and term nodes"
//! counters = ["KompileSentenceEquivalenceChecks", "KompileProductionIdentityDigests"]
//!
//! [[cost]]
//! mode = "one comparison or identity"
//! bound = "O(N)"
//! ```
//!
//! ```toml algorithm
//! id = "definition.equivalence.deduplicate"
//! name = "order-preserving deduplication by sentence equivalence"
//! sites = ["dedup_by_equivalence", "EquivalenceAccumulator", "push_if_inequivalent"]
//! variable = "n = sentences; eq = sentence-equivalence cost; k_i = retained sentences in SentenceKey bucket i"
//! counters = ["KompileSentenceEquivalenceChecks"]
//!
//! [[cost]]
//! mode = "one sentence collection"
//! bound = "O(n^2 x eq)"
//!
//! [[cost]]
//! mode = "one sentence collection, bucketed by SentenceKey"
//! bound = "O(n log n + sum k_i^2 x eq)"
//! ```
//!
//! Structural sentence and term equivalence powers declaration-order deduplication.
//! The shared accumulator costs O(n^2 * eq); `Counter::KompileSentenceEquivalenceChecks` measures equivalence calls after CQ-12's counter commit.
//!
//! K sentence equality for deduplication, including `Production`'s custom equality override.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use k_rust_kore::measure::{self, Counter};
use sha2::{Digest, Sha256};

use super::ast::{Attributes, ProductionItem, Sentence};
use super::resolve::SentenceKey;
use crate::definition::AttributeKey;
use crate::kast::{Label, ProductionIdentity, Sort, Term};

/// Return the canonical byte payload for a production.
///
/// Payload equality is exactly production equivalence. Sorts and labels use their structural
/// fields rather than their display forms so arbitrary names cannot make the encoding ambiguous.
pub fn canonical_production_payload(sentence: &Sentence) -> Option<Vec<u8>> {
    let Sentence::Production {
        label,
        parameters,
        sort,
        items,
        attributes,
    } = sentence
    else {
        return None;
    };

    let mut payload = b"k-rust-production-identity\0\x01".to_vec();
    encode_option(&mut payload, label.as_ref(), encode_label);
    encode_sequence(&mut payload, parameters, encode_sort);
    encode_sort(&mut payload, sort);
    encode_sequence(&mut payload, items, |payload, item| match item {
        ProductionItem::NonTerminal { sort, name } => {
            payload.push(b'N');
            encode_sort(payload, sort);
            encode_option(payload, name.as_deref(), encode_string);
        }
        ProductionItem::RegexTerminal { regex, .. } => {
            payload.push(b'R');
            encode_string(payload, regex);
        }
        ProductionItem::Terminal(text) => {
            payload.push(b'T');
            encode_string(payload, text);
        }
    });
    encode_option(
        &mut payload,
        production_label_attribute(label.as_ref(), attributes),
        encode_string,
    );
    encode_option(
        &mut payload,
        attributes.string(AttributeKey::Function),
        encode_string,
    );
    encode_option(
        &mut payload,
        attributes.string(AttributeKey::Symbol),
        encode_string,
    );
    Some(payload)
}

/// Compute the 128-bit content identity of a production.
///
/// Equivalent productions have equal identities. Treating the converse as true relies on the
/// collision resistance of the truncated SHA-256 digest rather than a mathematical guarantee.
pub fn production_identity(sentence: &Sentence) -> Option<ProductionIdentity> {
    let payload = canonical_production_payload(sentence)?;
    measure::bump(Counter::KompileProductionIdentityDigests);
    let digest = Sha256::digest(payload);
    let mut identity = [0; 16];
    identity.copy_from_slice(&digest[..16]);
    Some(ProductionIdentity::from_digest(identity))
}

fn encode_label(payload: &mut Vec<u8>, label: &Label) {
    encode_string(payload, &label.name);
    encode_sequence(payload, &label.parameters, encode_sort);
}

fn encode_sort(payload: &mut Vec<u8>, sort: &Sort) {
    encode_string(payload, &sort.name);
    encode_sequence(payload, &sort.parameters, encode_sort);
}

fn encode_sequence<T>(
    payload: &mut Vec<u8>,
    items: &[T],
    encode: impl Copy + Fn(&mut Vec<u8>, &T),
) {
    encode_length(payload, items.len());
    for item in items {
        encode(payload, item);
    }
}

fn encode_option<T: ?Sized>(
    payload: &mut Vec<u8>,
    value: Option<&T>,
    encode: impl FnOnce(&mut Vec<u8>, &T),
) {
    match value {
        Some(value) => {
            payload.push(1);
            encode(payload, value);
        }
        None => payload.push(0),
    }
}

fn encode_string(payload: &mut Vec<u8>, text: &str) {
    encode_length(payload, text.len());
    payload.extend_from_slice(text.as_bytes());
}

fn encode_length(payload: &mut Vec<u8>, length: usize) {
    let length = u64::try_from(length).expect("usize fits in u64 on supported targets");
    payload.extend_from_slice(&length.to_be_bytes());
}

/// Scala sentence equality, including `Production`'s custom equality override.
pub fn sentence_equivalent(left: &Sentence, right: &Sentence) -> bool {
    measure::bump(Counter::KompileSentenceEquivalenceChecks);
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

/// Retain the first sentence from each structural-equivalence class.
pub(crate) fn dedup_by_equivalence<'a>(
    sentences: impl IntoIterator<Item = &'a Sentence>,
) -> Vec<&'a Sentence> {
    let mut unique = EquivalenceAccumulator::new();
    for sentence in sentences {
        push_if_inequivalent(&mut unique, sentence);
    }
    unique.into_sentences()
}

/// Declaration-ordered representatives with candidate indexes by [`SentenceKey`].
pub(crate) struct EquivalenceAccumulator<'a> {
    sentences: Vec<&'a Sentence>,
    by_key: BTreeMap<SentenceKey<'a>, Vec<usize>>,
}

impl<'a> EquivalenceAccumulator<'a> {
    pub(crate) fn new() -> Self {
        Self {
            sentences: Vec::new(),
            by_key: BTreeMap::new(),
        }
    }

    pub(crate) fn from_sentences(sentences: impl IntoIterator<Item = &'a Sentence>) -> Self {
        let mut accumulator = Self::new();
        for sentence in sentences {
            accumulator.push(sentence);
        }
        accumulator
    }

    pub(crate) fn push(&mut self, sentence: &'a Sentence) -> bool {
        self.push_or_find(sentence).is_none()
    }

    /// Append `sentence` and return `None`, or return the index of the retained sentence it is
    /// equivalent to.
    pub(crate) fn push_or_find(&mut self, sentence: &'a Sentence) -> Option<usize> {
        let key = SentenceKey::of(sentence);
        if let Some(existing) = self.by_key.get(&key).and_then(|candidates| {
            candidates
                .iter()
                .copied()
                .find(|&index| sentence_equivalent(self.sentences[index], sentence))
        }) {
            return Some(existing);
        }
        let index = self.sentences.len();
        self.sentences.push(sentence);
        self.by_key.entry(key).or_default().push(index);
        None
    }

    fn into_sentences(self) -> Vec<&'a Sentence> {
        self.sentences
    }
}

/// Append `sentence` when no retained sentence is structurally equivalent.
pub(crate) fn push_if_inequivalent<'a>(
    sentences: &mut EquivalenceAccumulator<'a>,
    sentence: &'a Sentence,
) -> bool {
    sentences.push(sentence)
}

/// Append to `sentences` the candidates absent by exact structural equality from it and from
/// earlier candidates. A discarded candidate adds its input addresses to the sentence it equals,
/// which derives from both.
pub(crate) fn extend_with_new_sentences(
    sentences: &mut Vec<Arc<Sentence>>,
    candidates: Vec<Sentence>,
) {
    enum Equal {
        Existing(usize),
        Candidate(usize),
    }
    let equals = {
        let mut existing_by_key = BTreeMap::<SentenceKey<'_>, Vec<usize>>::new();
        for (index, sentence) in sentences.iter().enumerate() {
            existing_by_key
                .entry(SentenceKey::of(sentence))
                .or_default()
                .push(index);
        }
        let mut accepted_by_key = BTreeMap::<SentenceKey<'_>, Vec<usize>>::new();
        let mut equals = Vec::with_capacity(candidates.len());
        for (index, candidate) in candidates.iter().enumerate() {
            let key = SentenceKey::of(candidate);
            let equal = existing_by_key
                .get(&key)
                .and_then(|bucket| bucket.iter().find(|&&i| *sentences[i] == *candidate))
                .map(|&i| Equal::Existing(i))
                .or_else(|| {
                    accepted_by_key
                        .get(&key)
                        .and_then(|bucket| bucket.iter().find(|&&i| candidates[i] == *candidate))
                        .map(|&i| Equal::Candidate(i))
                });
            if equal.is_none() {
                accepted_by_key.entry(key).or_default().push(index);
            }
            equals.push(equal);
        }
        equals
    };
    let mut position = vec![0; candidates.len()];
    for ((index, candidate), equal) in candidates.into_iter().enumerate().zip(equals) {
        let target = match equal {
            None => {
                position[index] = sentences.len();
                sentences.push(Arc::new(candidate));
                continue;
            }
            Some(Equal::Existing(existing)) => existing,
            Some(Equal::Candidate(earlier)) => position[earlier],
        };
        let carried = sentences[target].attributes().input_addresses();
        if !candidate
            .attributes()
            .input_addresses()
            .iter()
            .all(|address| carried.contains(address))
        {
            super::sentence_mut(&mut sentences[target])
                .attributes_mut()
                .union_input_addresses(candidate.attributes());
        }
    }
}

/// Retain candidates absent by exact structural equality from `existing` and earlier candidates.
pub(crate) fn retain_new_sentences<'a>(
    existing: impl IntoIterator<Item = &'a Sentence>,
    candidates: Vec<Sentence>,
) -> Vec<Sentence> {
    let mut existing_by_key = BTreeMap::<SentenceKey<'a>, Vec<&'a Sentence>>::new();
    for sentence in existing {
        existing_by_key
            .entry(SentenceKey::of(sentence))
            .or_default()
            .push(sentence);
    }

    let mut accepted_by_key = BTreeMap::<SentenceKey<'_>, Vec<usize>>::new();
    let mut accepted = Vec::new();
    for (index, sentence) in candidates.iter().enumerate() {
        let absent_from_existing = existing_by_key
            .get(&SentenceKey::of(sentence))
            .is_none_or(|bucket| !bucket.contains(&sentence));
        let absent_from_accepted =
            accepted_by_key
                .get(&SentenceKey::of(sentence))
                .is_none_or(|bucket| {
                    !bucket
                        .iter()
                        .any(|&accepted_index| candidates[accepted_index] == *sentence)
                });
        if absent_from_existing && absent_from_accepted {
            accepted_by_key
                .entry(SentenceKey::of(sentence))
                .or_default()
                .push(index);
            accepted.push(index);
        }
    }

    let mut accepted = accepted.into_iter().peekable();
    candidates
        .into_iter()
        .enumerate()
        .filter_map(|(index, sentence)| {
            (accepted.peek() == Some(&index)).then(|| {
                accepted.next();
                sentence
            })
        })
        .collect()
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
// Invariant: each recursive call, directly or through `terms_equivalent`, compares a pair of strict subterms of `left` and `right`, so the size of `left` bounds the calls.
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

#[cfg(test)]
mod tests {
    use proptest::prelude::*;

    use super::*;
    use crate::kast::{Label, Sort};

    fn production((label, sort, first, second): (u8, u8, u8, u8)) -> Sentence {
        Sentence::Production {
            label: Some(Label::new(format!("label{label}"))),
            parameters: Vec::new(),
            sort: Sort::new(format!("Sort{sort}")),
            items: vec![
                ProductionItem::Terminal(first.to_string()),
                ProductionItem::Terminal(second.to_string()),
            ],
            attributes: Attributes::default(),
        }
    }

    proptest! {
        #[test]
        fn indexed_dedup_matches_the_linear_first_representative_oracle(
            specs in prop::collection::vec(
                (any::<u8>(), any::<u8>(), any::<u8>(), any::<u8>()),
                0..80,
            ),
        ) {
            let sentences = specs.into_iter().map(production).collect::<Vec<_>>();
            let mut expected: Vec<&Sentence> = Vec::new();
            for sentence in &sentences {
                if !expected
                    .iter()
                    .any(|existing| sentence_equivalent(existing, sentence))
                {
                    expected.push(sentence);
                }
            }

            let actual = dedup_by_equivalence(&sentences);
            prop_assert_eq!(actual, expected);
        }

        #[test]
        fn indexed_exact_membership_matches_vec_contains(
            existing_specs in prop::collection::vec(
                (any::<u8>(), any::<u8>(), any::<u8>(), any::<u8>()),
                0..40,
            ),
            candidate_specs in prop::collection::vec(
                (any::<u8>(), any::<u8>(), any::<u8>(), any::<u8>()),
                0..40,
            ),
        ) {
            let existing = existing_specs.into_iter().map(production).collect::<Vec<_>>();
            let candidates = candidate_specs.into_iter().map(production).collect::<Vec<_>>();
            let mut expected = Vec::new();
            for sentence in &candidates {
                if !existing.contains(sentence) && !expected.contains(sentence) {
                    expected.push(sentence.clone());
                }
            }

            let actual = retain_new_sentences(existing.iter(), candidates);
            prop_assert_eq!(actual, expected);
        }
    }
}
