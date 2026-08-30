//! Stable transition identities and opt-in structured observation contracts.

use std::{collections::BTreeMap, collections::BTreeSet, fmt};

use sha2::{Digest, Sha256};

use crate::{
    builtin::BuiltinEffect,
    definition::BackendDefinition,
    externalize,
    rewrite::Pattern,
    rewrite::{AppliedRule, RemainderBranch},
    rule::Predicate,
    substitution::Substitution,
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

    pub(crate) fn observes(&self, rule: &str) -> bool {
        self.rules
            .as_ref()
            .is_none_or(|selected| selected.contains(rule))
    }

    pub(crate) const fn rules_are_unfiltered(&self) -> bool {
        self.rules.is_none()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ObservationFilterError {
    UnknownRule(String),
    DuplicateRule(String),
    AmbiguousRule(String),
}

#[derive(Clone, Copy)]
pub(crate) struct ObservationNodeId(usize);

pub(crate) type ObservationHead = Option<ObservationNodeId>;

struct ObservationNode {
    parent: ObservationHead,
    transition: Option<TransitionId>,
    event: Option<ObservationEvent>,
}

#[derive(Default)]
pub(crate) struct ObservationLog {
    nodes: Vec<ObservationNode>,
}

impl ObservationLog {
    pub(crate) fn append_applied(
        &mut self,
        parent: ObservationHead,
        applied: &AppliedRule,
        options: Option<&ObservationOptions>,
    ) -> ObservationHead {
        let options = options?;
        let id = TransitionId {
            rule: applied.unique_id.clone(),
            target: PatternDigest::of(&applied.pattern),
        };
        let event = options.observes(&applied.unique_id).then(|| {
            ObservationEvent::Transition(TransitionObservation {
                id: id.clone(),
                class: TransitionClass::Rewrite,
                rule_label: applied.label.clone(),
                bindings: applied.rule_substitution.clone(),
                introduced_predicates: applied.rule_predicates.clone(),
                before: applied.before.clone(),
                after: applied.pattern.clone(),
                effects: applied.effects.clone(),
            })
        });
        Some(self.push(ObservationNode {
            parent,
            transition: Some(id),
            event,
        }))
    }

    pub(crate) fn append_remainder(
        &mut self,
        parent: ObservationHead,
        before: Pattern,
        remainder: &RemainderBranch,
        options: Option<&ObservationOptions>,
    ) -> ObservationHead {
        let options = options?;
        let id = TransitionId {
            rule: format!("remainder:{}", remainder.rule_ids.join(",")),
            target: PatternDigest::of(&remainder.pattern),
        };
        let event = options.rules_are_unfiltered().then(|| {
            ObservationEvent::Transition(TransitionObservation {
                id: id.clone(),
                class: TransitionClass::Remainder,
                rule_label: None,
                bindings: Substitution::new(),
                introduced_predicates: Vec::new(),
                before,
                after: remainder.pattern.clone(),
                effects: Vec::new(),
            })
        });
        Some(self.push(ObservationNode {
            parent,
            transition: Some(id),
            event,
        }))
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn append_simplification(
        &mut self,
        mut parent: ObservationHead,
        definition: &BackendDefinition,
        before: Pattern,
        after: &Pattern,
        applied_rules: &[String],
        effects: &[BuiltinEffect],
        options: Option<&ObservationOptions>,
    ) -> ObservationHead {
        let options = options?;
        let mut effects = effects.iter();
        for rule in applied_rules {
            let class = transition_class(definition, rule);
            let attributed_effects =
                if class == TransitionClass::Builtin && rule == "builtin:IO.logString" {
                    effects.next().cloned().into_iter().collect()
                } else {
                    Vec::new()
                };
            if !options.observes(rule) {
                continue;
            }
            let id = TransitionId {
                rule: rule.clone(),
                target: PatternDigest::of(after),
            };
            parent = Some(self.push(ObservationNode {
                parent,
                transition: None,
                event: Some(ObservationEvent::Transition(TransitionObservation {
                    id,
                    class,
                    rule_label: equation_label(definition, rule),
                    bindings: Substitution::new(),
                    introduced_predicates: Vec::new(),
                    before: before.clone(),
                    after: after.clone(),
                    effects: attributed_effects,
                })),
            }));
        }
        parent
    }

    pub(crate) fn materialize(
        &self,
        mut head: ObservationHead,
    ) -> (Vec<TransitionId>, Vec<ObservationEvent>) {
        let mut branch = Vec::new();
        let mut events = Vec::new();
        while let Some(id) = head {
            let node = &self.nodes[id.0];
            if let Some(transition) = &node.transition {
                branch.push(transition.clone());
            }
            if let Some(event) = &node.event {
                events.push(event.clone());
            }
            head = node.parent;
        }
        branch.reverse();
        events.reverse();
        (branch, events)
    }

    fn push(&mut self, node: ObservationNode) -> ObservationNodeId {
        let id = ObservationNodeId(self.nodes.len());
        self.nodes.push(node);
        id
    }
}

fn transition_class(definition: &BackendDefinition, rule_id: &str) -> TransitionClass {
    if rule_id.starts_with("builtin:") {
        return TransitionClass::Builtin;
    }
    if theory_contains_rule(&definition.function_theory, rule_id) {
        TransitionClass::FunctionEquation
    } else {
        TransitionClass::Simplification
    }
}

fn equation_label(definition: &BackendDefinition, rule_id: &str) -> Option<String> {
    [
        &definition.function_theory,
        &definition.simplification_theory,
    ]
    .into_iter()
    .flat_map(|theory| theory.values())
    .flat_map(|priorities| priorities.values())
    .flatten()
    .find(|rule| rule.attributes.unique_id == rule_id)
    .and_then(|rule| rule.attributes.label.clone())
}

fn theory_contains_rule(theory: &crate::rule::Theory, rule_id: &str) -> bool {
    theory
        .values()
        .flat_map(|priorities| priorities.values())
        .flatten()
        .any(|rule| rule.attributes.unique_id == rule_id)
}
