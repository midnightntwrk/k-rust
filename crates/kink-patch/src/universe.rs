//! Declared rule universes and deterministic, explicitly listed exclusions.

use crate::typing::CompilationTyping;
use crate::{Baseline, SentenceRef, Sha256Digest, canonical_json, payload_digest};
use k_rust::definition::{AttributeKey, Sentence};
use k_rust::kast::Term;
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};

/// The predicates defining a v1 rule universe.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Universe {
    /// V1 discovery requires an authored-rule declaration.
    pub authored: bool,
    pub typed: bool,
    pub exclude_attributes: Vec<String>,
    pub exclude_macro_rules: bool,
}

impl Universe {
    #[must_use]
    pub fn v1() -> Self {
        Self {
            authored: true,
            typed: true,
            exclude_attributes: vec!["simplification".to_owned(), "smt-lemma".to_owned()],
            exclude_macro_rules: true,
        }
    }
}

/// The first applicable reason a rule is outside the declared universe.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ExclusionReason {
    Untyped,
    Attribute(String),
    MacroRule,
}

impl ExclusionReason {
    fn text(&self) -> String {
        match self {
            Self::Untyped => "untyped".to_owned(),
            Self::Attribute(key) => format!("attribute:{key}"),
            Self::MacroRule => "macro-rule".to_owned(),
        }
    }
}

/// A resolved declaration, with both partitions in sentence order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedUniverse {
    declaration: Universe,
    included: Vec<SentenceRef>,
    excluded: Vec<(SentenceRef, ExclusionReason)>,
}

impl ResolvedUniverse {
    #[must_use]
    pub fn included(&self) -> &[SentenceRef] {
        &self.included
    }

    #[must_use]
    pub fn excluded(&self) -> &[(SentenceRef, ExclusionReason)] {
        &self.excluded
    }

    fn excluded_value(&self) -> Value {
        Value::Array(
            self.excluded
                .iter()
                .map(|(at, reason)| {
                    json!({"module": at.module, "index": at.index, "reason": reason.text()})
                })
                .collect(),
        )
    }

    #[must_use]
    pub fn excluded_digest(&self) -> Sha256Digest {
        payload_digest(
            "kink/universe-excluded/v1",
            canonical_json(&self.excluded_value()).as_bytes(),
        )
    }

    #[must_use]
    pub fn value(&self) -> Value {
        json!({
            "kinds": ["rule"],
            "authored": self.declaration.authored,
            "typed": self.declaration.typed,
            "exclude_attributes": self.declaration.exclude_attributes,
            "exclude_macro_rules": self.declaration.exclude_macro_rules,
            "excluded": self.excluded_value(),
            "excluded_sha256": self.excluded_digest().to_string(),
        })
    }

    pub(crate) fn matches_baseline(&self, baseline: &Baseline) -> bool {
        self.declaration.authored && *self == resolve_universe(baseline, &self.declaration)
    }
}

/// Resolves the declaration. A rule is `Untyped` when compilation's typing view (one
/// `SentenceTyper::for_compilation` of the baseline, `typing_in` its declaring module) gives it
/// no typing: a `CellCompletion` shape, or a rule outside the main module's import closure, which
/// compilation never emits. A rule that types only in that view (its own module lacks `K`,
/// overloads or helpers compilation sees) is in the universe.
#[must_use]
pub fn resolve_universe(baseline: &Baseline, universe: &Universe) -> ResolvedUniverse {
    let typing = universe
        .typed
        .then(|| CompilationTyping::new(baseline.loaded().resolved()));
    let mut macro_heads = BTreeMap::new();
    let mut included = Vec::new();
    let mut excluded = Vec::new();
    for (at, sentence) in baseline.authored_sentences() {
        let Sentence::Rule {
            body, attributes, ..
        } = sentence
        else {
            continue;
        };
        let untyped = typing
            .as_ref()
            .is_some_and(|typing| !matches!(typing.typing(sentence, &at.module), Some(Ok(_))));
        let reason = if untyped {
            Some(ExclusionReason::Untyped)
        } else if let Some(key) = universe
            .exclude_attributes
            .iter()
            .find(|key| attributes.get(key).is_some())
        {
            Some(ExclusionReason::Attribute(key.clone()))
        } else if universe.exclude_macro_rules && {
            let heads = macro_heads
                .entry(at.module.clone())
                .or_insert_with(|| macro_labels(baseline, &at.module));
            let left = match body.unannotated() {
                Term::Rewrite { left, .. } => left,
                body => body,
            };
            head(left).is_some_and(|head| heads.contains(head))
        } {
            Some(ExclusionReason::MacroRule)
        } else {
            None
        };
        if let Some(reason) = reason {
            excluded.push((at, reason));
        } else {
            included.push(at);
        }
    }
    included.sort();
    excluded.sort_by(|left, right| left.0.cmp(&right.0));
    ResolvedUniverse {
        declaration: universe.clone(),
        included,
        excluded,
    }
}

fn macro_labels(baseline: &Baseline, module: &str) -> BTreeSet<String> {
    let resolved = baseline.loaded().resolved();
    let Some(module) = resolved.module_id(module) else {
        return BTreeSet::new();
    };
    resolved
        .signature_sentences(module)
        .into_iter()
        .filter_map(|sentence| match sentence {
            Sentence::Production {
                label: Some(label),
                attributes,
                ..
            } if attributes.has_any(&AttributeKey::MACRO_LIKE) => Some(label.name.clone()),
            _ => None,
        })
        .collect()
}

fn head(term: &Term) -> Option<&str> {
    match term.unannotated() {
        Term::As { pattern, .. } => head(pattern),
        Term::Apply { label, arguments } if label.semantic_cast_sort().is_some() => {
            head(arguments.first()?)
        }
        Term::Apply { label, .. } => Some(&label.name),
        _ => None,
    }
}
