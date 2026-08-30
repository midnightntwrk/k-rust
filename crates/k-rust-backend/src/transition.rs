//! Stable transition identities and opt-in structured observation contracts.

use std::{collections::BTreeMap, collections::BTreeSet, fmt};

use sha2::{Digest, Sha256};

use crate::{
    builtin::BuiltinEffect, definition::BackendDefinition, externalize, rewrite::Pattern,
    rule::Predicate, substitution::Substitution,
};

/// A stable SHA-256 digest of a constrained pattern's canonical compact KORE form.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PatternDigest([u8; 32]);

impl PatternDigest {
    pub fn of(pattern: &Pattern) -> Self {
        let canonical = externalize::constrained_pattern(pattern).to_string();
        Self(Sha256::digest(canonical.as_bytes()).into())
    }

    pub const fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }

    pub const fn into_bytes(self) -> [u8; 32] {
        self.0
    }
}

impl fmt::Display for PatternDigest {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        for byte in self.0 {
            write!(formatter, "{byte:02x}")?;
        }
        Ok(())
    }
}

/// Definition-derived identity for a committed transition and its successor.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TransitionId {
    pub rule: String,
    pub target: PatternDigest,
}

/// The semantic activity represented by a transition observation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TransitionClass {
    Rewrite,
    Remainder,
    FunctionEquation,
    Simplification,
    Builtin,
    Claim,
}

/// Structured evidence for one retained semantic transition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TransitionObservation {
    pub id: TransitionId,
    pub class: TransitionClass,
    pub rule_label: Option<String>,
    pub bindings: Substitution,
    pub introduced_predicates: Vec<Predicate>,
    pub before: Pattern,
    pub after: Pattern,
    pub effects: Vec<BuiltinEffect>,
}

/// Why an attempted transition was not committed to a surviving branch.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UncommittedReason {
    RolledBack,
}

/// Structured evidence retained outside a committed branch stream.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UncommittedObservation {
    pub id: TransitionId,
    pub rule_label: Option<String>,
    pub effects: Vec<BuiltinEffect>,
    pub reason: UncommittedReason,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ObservationEvent {
    Transition(TransitionObservation),
    Uncommitted(UncommittedObservation),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ObservationOptions {
    rules: Option<BTreeSet<String>>,
}

impl ObservationOptions {
    /// Observe every supported activity.
    pub const fn all() -> Self {
        Self { rules: None }
    }

    /// Construct an immutable rewrite-rule allowlist.
    ///
    /// Validation is atomic: every id must identify exactly one executable rewrite rule.
    pub fn with_rules<I, S>(
        definition: &BackendDefinition,
        rules: I,
    ) -> Result<Self, ObservationFilterError>
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let mut available = BTreeMap::<String, usize>::new();
        for priorities in definition.rewrite_theory.values() {
            for rules in priorities.values() {
                for rule in rules {
                    *available
                        .entry(rule.attributes.unique_id.clone())
                        .or_default() += 1;
                }
            }
        }

        let mut selected = BTreeSet::new();
        for rule in rules.into_iter().map(Into::into) {
            if !selected.insert(rule.clone()) {
                return Err(ObservationFilterError::DuplicateRule(rule));
            }
            match available.get(&rule).copied() {
                None => return Err(ObservationFilterError::UnknownRule(rule)),
                Some(1) => {}
                Some(_) => return Err(ObservationFilterError::AmbiguousRule(rule)),
            }
        }
        Ok(Self {
            rules: Some(selected),
        })
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ObservationFilterError {
    UnknownRule(String),
    DuplicateRule(String),
    AmbiguousRule(String),
}
