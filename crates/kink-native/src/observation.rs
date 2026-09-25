//! Atomic source-position observation installation and branch-local event adaptation.
//!
//! Events name the written baseline rule that emitted them and retain the backend
//! identity of its committed transition.

use std::collections::{BTreeMap, BTreeSet};

use k_rust::backend::{
    BindingOutput, EffectOutput, ObservationEventOutput, TraceEntry, TransitionClassOutput,
    TransitionIdOutput, UncommittedReasonOutput,
};
use kink_patch::SentenceRef;
use serde_json::Value;

/// One written baseline rule and its manifest-ordered emissions.
#[derive(Clone, Debug, PartialEq)]
pub struct RuleObservationSpec {
    pub rule: SentenceRef,
    pub label: Option<String>,
    /// Exact backend identity passed to the public observed execution selector.
    pub backend_rule_identity: String,
    pub emit_rule_applied: bool,
    pub domain_events: Vec<DomainEventSpec>,
}

/// One domain event derived without interpreting pretty text or backend diagnostics.
#[derive(Clone, Debug, PartialEq)]
pub struct DomainEventSpec {
    pub constructor: String,
    pub payload: Vec<PayloadSource>,
}

/// Closed payload sources exposed by the k-rust transition wire contract.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PayloadSource {
    BeforeState,
    AfterState,
    BindingVariable(usize),
    BindingValue(usize),
    IntroducedPredicate(usize),
    Effect(usize),
}

/// An immutable, atomically validated observation manifest.
#[derive(Clone, Debug, PartialEq)]
pub struct InstalledObservationManifest {
    rules: Vec<InstalledRule>,
    by_identity: BTreeMap<String, usize>,
}

impl InstalledObservationManifest {
    /// Validates the local manifest atomically without mutating a backend.
    ///
    /// Definition membership and module visibility are validated atomically by the public
    /// `Backend::*_observed` operation before execution starts.
    pub fn install(specs: Vec<RuleObservationSpec>) -> Result<Self, ObservationFailure> {
        let mut selected_rules = BTreeSet::new();
        let mut selected_identities = BTreeSet::new();
        for spec in &specs {
            if !selected_rules.insert(spec.rule.clone()) {
                return Err(ObservationFailure::DuplicateSelector(spec.rule.clone()));
            }
            if spec.backend_rule_identity.is_empty() {
                return Err(ObservationFailure::InvalidManifest(
                    "backend rule identity must not be empty".into(),
                ));
            }
            if !selected_identities.insert(spec.backend_rule_identity.clone()) {
                return Err(ObservationFailure::DuplicateRuleIdentity(
                    spec.backend_rule_identity.clone(),
                ));
            }
            let mut constructors = BTreeSet::new();
            for event in &spec.domain_events {
                if event.constructor.is_empty() {
                    return Err(ObservationFailure::InvalidManifest(
                        "domain event constructor must not be empty".into(),
                    ));
                }
                if !constructors.insert(event.constructor.clone()) {
                    return Err(ObservationFailure::DuplicateManifestEvent {
                        rule: spec.rule.clone(),
                        constructor: event.constructor.clone(),
                    });
                }
            }
        }
        let rules = specs
            .into_iter()
            .map(|spec| InstalledRule {
                identity: spec.backend_rule_identity.clone(),
                spec,
            })
            .collect::<Vec<_>>();
        let by_identity = rules
            .iter()
            .enumerate()
            .map(|(ordinal, rule)| (rule.identity.clone(), ordinal))
            .collect();
        Ok(Self { rules, by_identity })
    }

    /// Exact backend rule identities in selector/manifest order.
    #[must_use]
    pub fn backend_rule_ids(&self) -> Vec<String> {
        self.rules
            .iter()
            .map(|rule| rule.identity.clone())
            .collect()
    }

    /// Written baseline rules in manifest order.
    pub fn rules(&self) -> impl Iterator<Item = &SentenceRef> {
        self.rules.iter().map(|rule| &rule.spec.rule)
    }
}

#[derive(Clone, Debug, PartialEq)]
struct InstalledRule {
    identity: String,
    spec: RuleObservationSpec,
}

/// One branch-local adapted execution state.
#[derive(Clone, Debug, PartialEq)]
pub struct AdaptedBranch {
    pub identity: Vec<TransitionIdOutput>,
    pub state: Value,
    pub depth: u64,
    pub trace: Vec<TraceEntry>,
    pub events: Vec<NativeEvent>,
    pub rollbacks: Vec<RollbackEvent>,
}

/// Observation-erased state. The semantic state, branch identity, depth, and trace remain.
#[derive(Clone, Debug, PartialEq)]
pub struct ErasedBranch {
    pub identity: Vec<TransitionIdOutput>,
    pub state: Value,
    pub depth: u64,
    pub trace: Vec<TraceEntry>,
}

impl AdaptedBranch {
    /// Erases only adapter observation state.
    #[must_use]
    pub fn erase_observations(&self) -> ErasedBranch {
        ErasedBranch {
            identity: self.identity.clone(),
            state: self.state.clone(),
            depth: self.depth,
            trace: self.trace.clone(),
        }
    }
}

/// Closed native event union. Generic events precede domain events for each transition.
#[derive(Clone, Debug, PartialEq)]
pub enum NativeEvent {
    RuleApplied(RuleAppliedEvent),
    Domain(DomainEvent),
}

/// Generic evidence for one committed transition.
#[derive(Clone, Debug, PartialEq)]
pub struct RuleAppliedEvent {
    pub event_ordinal: usize,
    pub transition_ordinal: usize,
    pub emission_ordinal: usize,
    pub transition: TransitionIdOutput,
    pub class: TransitionClassOutput,
    pub rule: SentenceRef,
    pub label: Option<String>,
    pub bindings: Vec<BindingOutput>,
    pub introduced_predicates: Vec<Value>,
    pub before: Value,
    pub after: Value,
    pub effects: Vec<EffectOutput>,
}

/// Manifest-derived domain event retaining its complete committed transition context.
#[derive(Clone, Debug, PartialEq)]
pub struct DomainEvent {
    pub event_ordinal: usize,
    pub transition_ordinal: usize,
    pub emission_ordinal: usize,
    pub constructor: String,
    pub transition: TransitionIdOutput,
    pub rule: SentenceRef,
    pub payload: Vec<DomainPayload>,
}

/// Closed domain payload values.
#[derive(Clone, Debug, PartialEq)]
pub enum DomainPayload {
    Term(Value),
    Effect(EffectOutput),
}

/// An upstream transition explicitly retained as uncommitted/rolled back.
#[derive(Clone, Debug, PartialEq)]
pub struct RollbackEvent {
    pub transition_ordinal: usize,
    pub transition: TransitionIdOutput,
    pub rule_label: Option<String>,
    pub effects: Vec<EffectOutput>,
    pub reason: UncommittedReasonOutput,
}

pub(crate) fn adapt_branch(
    manifest: Option<&InstalledObservationManifest>,
    identity: Vec<TransitionIdOutput>,
    state: Value,
    depth: u64,
    trace: Vec<TraceEntry>,
    observations: Vec<ObservationEventOutput>,
) -> Result<AdaptedBranch, ObservationFailure> {
    let mut events = Vec::new();
    let mut rollbacks = Vec::new();
    let mut next_branch_ordinal = 0;
    for (observation_ordinal, observation) in observations.into_iter().enumerate() {
        match observation {
            ObservationEventOutput::Transition {
                id,
                class,
                rule_label,
                bindings,
                introduced_predicates,
                before,
                after,
                effects,
            } => {
                inventory_transition_class(class);
                inventory_effects(&effects);
                let transition_ordinal = identity[next_branch_ordinal..]
                    .iter()
                    .position(|candidate| candidate == &id)
                    .map(|offset| next_branch_ordinal + offset)
                    .ok_or_else(|| {
                        if identity[..next_branch_ordinal]
                            .iter()
                            .any(|candidate| candidate == &id)
                        {
                            ObservationFailure::CommittedTransitionOutOfOrderOrDuplicate {
                                transition: id.clone(),
                                next_branch_ordinal,
                            }
                        } else {
                            ObservationFailure::CommittedTransitionAbsent {
                                transition: id.clone(),
                            }
                        }
                    })?;
                next_branch_ordinal = transition_ordinal + 1;
                let manifest = manifest.ok_or(ObservationFailure::MissingInstallation)?;
                let selected = manifest
                    .by_identity
                    .get(&id.rule)
                    .and_then(|ordinal| manifest.rules.get(*ordinal))
                    .ok_or_else(|| ObservationFailure::UnselectedObservation(id.rule.clone()))?;
                if rule_label.as_ref() != selected.spec.label.as_ref() {
                    return Err(ObservationFailure::RuleLabelMismatch {
                        identity: id.rule,
                        expected: selected.spec.label.clone(),
                        actual: rule_label,
                    });
                }
                let mut emission_ordinal = 0;
                if selected.spec.emit_rule_applied {
                    let event_ordinal = events.len();
                    events.push(NativeEvent::RuleApplied(RuleAppliedEvent {
                        event_ordinal,
                        transition_ordinal,
                        emission_ordinal,
                        transition: id.clone(),
                        class,
                        rule: selected.spec.rule.clone(),
                        label: selected.spec.label.clone(),
                        bindings: bindings.clone(),
                        introduced_predicates: introduced_predicates.clone(),
                        before: before.clone(),
                        after: after.clone(),
                        effects: effects.clone(),
                    }));
                    emission_ordinal += 1;
                }
                for spec in &selected.spec.domain_events {
                    let payload = spec
                        .payload
                        .iter()
                        .map(|source| {
                            payload_value(
                                *source,
                                &before,
                                &after,
                                &bindings,
                                &introduced_predicates,
                                &effects,
                            )
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    let event_ordinal = events.len();
                    events.push(NativeEvent::Domain(DomainEvent {
                        event_ordinal,
                        transition_ordinal,
                        emission_ordinal,
                        constructor: spec.constructor.clone(),
                        transition: id.clone(),
                        rule: selected.spec.rule.clone(),
                        payload,
                    }));
                    emission_ordinal += 1;
                }
            }
            ObservationEventOutput::Uncommitted {
                id,
                rule_label,
                effects,
                reason,
            } => {
                inventory_uncommitted_reason(reason);
                inventory_effects(&effects);
                rollbacks.push(RollbackEvent {
                    transition_ordinal: observation_ordinal,
                    transition: id,
                    rule_label,
                    effects,
                    reason,
                });
            }
        }
    }
    Ok(AdaptedBranch {
        identity,
        state,
        depth,
        trace,
        events,
        rollbacks,
    })
}

fn inventory_transition_class(class: TransitionClassOutput) {
    match class {
        TransitionClassOutput::Rewrite
        | TransitionClassOutput::Remainder
        | TransitionClassOutput::FunctionEquation
        | TransitionClassOutput::Simplification
        | TransitionClassOutput::Builtin
        | TransitionClassOutput::Claim => {}
    }
}

fn inventory_uncommitted_reason(reason: UncommittedReasonOutput) {
    match reason {
        UncommittedReasonOutput::RolledBack => {}
    }
}

fn inventory_effects(effects: &[EffectOutput]) {
    for effect in effects {
        match effect {
            EffectOutput::UserLog { .. } => {}
        }
    }
}

fn payload_value(
    source: PayloadSource,
    before: &Value,
    after: &Value,
    bindings: &[BindingOutput],
    predicates: &[Value],
    effects: &[EffectOutput],
) -> Result<DomainPayload, ObservationFailure> {
    Ok(match source {
        PayloadSource::BeforeState => DomainPayload::Term(before.clone()),
        PayloadSource::AfterState => DomainPayload::Term(after.clone()),
        PayloadSource::BindingVariable(index) => DomainPayload::Term(
            bindings
                .get(index)
                .ok_or(ObservationFailure::MissingPayloadSource(source))?
                .variable
                .clone(),
        ),
        PayloadSource::BindingValue(index) => DomainPayload::Term(
            bindings
                .get(index)
                .ok_or(ObservationFailure::MissingPayloadSource(source))?
                .value
                .clone(),
        ),
        PayloadSource::IntroducedPredicate(index) => DomainPayload::Term(
            predicates
                .get(index)
                .ok_or(ObservationFailure::MissingPayloadSource(source))?
                .clone(),
        ),
        PayloadSource::Effect(index) => DomainPayload::Effect(
            effects
                .get(index)
                .ok_or(ObservationFailure::MissingPayloadSource(source))?
                .clone(),
        ),
    })
}

/// Closed installation/adaptation failures. Failure publishes no branch or event DTO.
#[derive(Clone, Debug, PartialEq)]
pub enum ObservationFailure {
    InvalidManifest(String),
    DuplicateSelector(SentenceRef),
    DuplicateManifestEvent {
        rule: SentenceRef,
        constructor: String,
    },
    DuplicateRuleIdentity(String),
    MissingInstallation,
    CommittedTransitionAbsent {
        transition: TransitionIdOutput,
    },
    CommittedTransitionOutOfOrderOrDuplicate {
        transition: TransitionIdOutput,
        next_branch_ordinal: usize,
    },
    UnselectedObservation(String),
    RuleLabelMismatch {
        identity: String,
        expected: Option<String>,
        actual: Option<String>,
    },
    MissingPayloadSource(PayloadSource),
}

#[cfg(test)]
mod tests {
    use super::*;
    use k_rust::backend::ObservationEventOutput;

    fn spec(label: &str) -> RuleObservationSpec {
        RuleObservationSpec {
            rule: SentenceRef::new("TEST", if label == "first" { 0 } else { 1 }),
            label: Some(label.into()),
            backend_rule_identity: format!("{label}-id"),
            emit_rule_applied: true,
            domain_events: Vec::new(),
        }
    }

    fn installed() -> InstalledObservationManifest {
        InstalledObservationManifest::install(vec![spec("first"), spec("second")]).unwrap()
    }

    fn transition(rule: &str, label: &str, marker: i64) -> ObservationEventOutput {
        ObservationEventOutput::Transition {
            id: transition_id(rule, marker),
            class: TransitionClassOutput::Rewrite,
            rule_label: Some(label.into()),
            bindings: Vec::new(),
            introduced_predicates: Vec::new(),
            before: Value::from(marker),
            after: Value::from(marker + 1),
            effects: Vec::new(),
        }
    }

    fn transition_id(rule: &str, marker: i64) -> TransitionIdOutput {
        TransitionIdOutput {
            rule: rule.into(),
            target: format!("target-{marker}"),
        }
    }

    #[test]
    fn selectors_validate_atomically_in_manifest_order() {
        let prior = installed();
        let duplicate = InstalledObservationManifest::install(vec![spec("first"), spec("first")]);
        assert_eq!(
            duplicate,
            Err(ObservationFailure::DuplicateSelector(SentenceRef::new(
                "TEST", 0
            )))
        );
        assert_eq!(prior.backend_rule_ids(), ["first-id", "second-id"]);
        assert_eq!(
            prior.rules().cloned().collect::<Vec<_>>(),
            [SentenceRef::new("TEST", 0), SentenceRef::new("TEST", 1)]
        );
    }

    #[test]
    fn duplicate_backend_identity_rejects_the_whole_manifest() {
        let mut second = spec("second");
        second.backend_rule_identity = "first-id".into();
        assert_eq!(
            InstalledObservationManifest::install(vec![spec("first"), second]),
            Err(ObservationFailure::DuplicateRuleIdentity("first-id".into()))
        );
    }

    #[test]
    fn branch_isolation_and_event_order_are_preserved() {
        let manifest = installed();
        let first = adapt_branch(
            Some(&manifest),
            vec![TransitionIdOutput {
                rule: "first-id".into(),
                target: "target-0".into(),
            }],
            Value::from(1),
            1,
            Vec::new(),
            vec![transition("first-id", "first", 0)],
        )
        .unwrap();
        let second = adapt_branch(
            Some(&manifest),
            vec![TransitionIdOutput {
                rule: "second-id".into(),
                target: "target-10".into(),
            }],
            Value::from(11),
            1,
            Vec::new(),
            vec![transition("second-id", "second", 10)],
        )
        .unwrap();
        assert_ne!(first.identity, second.identity);
        assert_eq!(first.events.len(), 1);
        assert_eq!(second.events.len(), 1);
    }

    #[test]
    fn generic_then_domain_manifest_order_and_payloads_are_exact() {
        let mut first = spec("first");
        first.domain_events = vec![
            DomainEventSpec {
                constructor: "before".into(),
                payload: vec![PayloadSource::BeforeState],
            },
            DomainEventSpec {
                constructor: "after".into(),
                payload: vec![PayloadSource::AfterState],
            },
        ];
        let manifest = InstalledObservationManifest::install(vec![first]).unwrap();
        let branch = adapt_branch(
            Some(&manifest),
            vec![transition_id("first-id", 0)],
            Value::from(1),
            1,
            Vec::new(),
            vec![transition("first-id", "first", 0)],
        )
        .unwrap();
        assert!(matches!(branch.events[0], NativeEvent::RuleApplied(_)));
        assert!(matches!(
            &branch.events[1],
            NativeEvent::Domain(event) if event.constructor == "before" && event.emission_ordinal == 1
        ));
        assert!(matches!(
            &branch.events[2],
            NativeEvent::Domain(event) if event.constructor == "after" && event.emission_ordinal == 2
        ));
    }

    #[test]
    fn selected_events_use_actual_branch_positions_across_unselected_transitions() {
        let manifest = installed();
        let branch = adapt_branch(
            Some(&manifest),
            vec![
                transition_id("unselected-prefix", -1),
                transition_id("first-id", 0),
                transition_id("unselected-middle", 5),
                transition_id("second-id", 10),
            ],
            Value::Null,
            4,
            Vec::new(),
            vec![
                transition("first-id", "first", 0),
                transition("second-id", "second", 10),
            ],
        )
        .unwrap();
        let NativeEvent::RuleApplied(first) = &branch.events[0] else {
            panic!("expected first generic event")
        };
        let NativeEvent::RuleApplied(second) = &branch.events[1] else {
            panic!("expected second generic event")
        };
        assert_eq!(first.transition_ordinal, 1);
        assert_eq!(second.transition_ordinal, 3);
    }

    /// One O2 emission row: selected rules as (label, emits `RuleApplied`, domain
    /// constructors), the branch as backend rule identities (unselected ones end in
    /// `-unselected`), and the expected (event, event ordinal, transition ordinal, emission
    /// ordinal) sequence.
    struct EmissionRow {
        id: &'static str,
        rules: &'static [(&'static str, bool, &'static [&'static str])],
        branch: &'static [&'static str],
        events: &'static [(&'static str, usize, usize, usize)],
    }

    fn event_clock(event: &NativeEvent) -> (&str, usize, usize, usize) {
        match event {
            NativeEvent::RuleApplied(event) => (
                "RuleApplied",
                event.event_ordinal,
                event.transition_ordinal,
                event.emission_ordinal,
            ),
            NativeEvent::Domain(event) => (
                event.constructor.as_str(),
                event.event_ordinal,
                event.transition_ordinal,
                event.emission_ordinal,
            ),
        }
    }

    #[test]
    fn event_clock_rows_are_dense_and_independent_of_transition_adjacency() {
        let rows = [
            EmissionRow {
                id: "one-transition-multiple-events",
                rules: &[("write", true, &["memoryWrite", "auditWrite"])],
                branch: &["write-id"],
                events: &[
                    ("RuleApplied", 0, 0, 0),
                    ("memoryWrite", 1, 0, 1),
                    ("auditWrite", 2, 0, 2),
                ],
            },
            // Adjacent events from non-adjacent transitions: next-event holds on the event
            // clock although a next-transition reading would not.
            EmissionRow {
                id: "unobserved-transition-does-not-advance-event-clock",
                rules: &[
                    ("write", false, &["memoryWrite"]),
                    ("load", false, &["memoryLoad"]),
                ],
                branch: &["write-id", "middle-unselected", "load-id"],
                events: &[("memoryWrite", 0, 0, 0), ("memoryLoad", 1, 2, 0)],
            },
            EmissionRow {
                id: "rule-applied-interrupts-domain-adjacency",
                rules: &[
                    ("write", false, &["memoryWrite"]),
                    ("middle", true, &[]),
                    ("load", false, &["memoryLoad"]),
                ],
                branch: &["write-id", "middle-id", "load-id"],
                events: &[
                    ("memoryWrite", 0, 0, 0),
                    ("RuleApplied", 1, 1, 0),
                    ("memoryLoad", 2, 2, 0),
                ],
            },
        ];
        for row in rows {
            let manifest = InstalledObservationManifest::install(
                row.rules
                    .iter()
                    .map(|(label, generic, domain)| RuleObservationSpec {
                        rule: SentenceRef::new(
                            "TEST",
                            match *label {
                                "write" => 0,
                                "middle" => 1,
                                _ => 2,
                            },
                        ),
                        label: Some((*label).into()),
                        backend_rule_identity: format!("{label}-id"),
                        emit_rule_applied: *generic,
                        domain_events: domain
                            .iter()
                            .map(|constructor| DomainEventSpec {
                                constructor: (*constructor).into(),
                                payload: vec![PayloadSource::AfterState],
                            })
                            .collect(),
                    })
                    .collect(),
            )
            .unwrap();
            let identity = row
                .branch
                .iter()
                .zip(0..)
                .map(|(rule, marker)| transition_id(rule, marker))
                .collect::<Vec<_>>();
            let observations = row
                .branch
                .iter()
                .zip(0..)
                .filter(|(rule, _)| !rule.ends_with("-unselected"))
                .map(|(rule, marker)| transition(rule, rule.trim_end_matches("-id"), marker))
                .collect();
            let branch = adapt_branch(
                Some(&manifest),
                identity,
                Value::Null,
                u64::try_from(row.branch.len()).unwrap(),
                Vec::new(),
                observations,
            )
            .unwrap_or_else(|failure| panic!("{}: {failure:?}", row.id));
            assert_eq!(
                branch.events.iter().map(event_clock).collect::<Vec<_>>(),
                row.events,
                "{}",
                row.id
            );
        }
    }

    #[test]
    fn fabricated_misordered_and_duplicate_observation_occurrences_fail_closed() {
        let manifest = installed();
        let identity = vec![transition_id("first-id", 0), transition_id("second-id", 10)];
        let fabricated = adapt_branch(
            Some(&manifest),
            identity.clone(),
            Value::Null,
            2,
            Vec::new(),
            vec![transition("first-id", "first", 99)],
        );
        assert!(matches!(
            fabricated,
            Err(ObservationFailure::CommittedTransitionAbsent { .. })
        ));

        let misordered = adapt_branch(
            Some(&manifest),
            identity.clone(),
            Value::Null,
            2,
            Vec::new(),
            vec![
                transition("second-id", "second", 10),
                transition("first-id", "first", 0),
            ],
        );
        assert!(matches!(
            misordered,
            Err(ObservationFailure::CommittedTransitionOutOfOrderOrDuplicate { .. })
        ));

        let duplicate = adapt_branch(
            Some(&manifest),
            identity,
            Value::Null,
            2,
            Vec::new(),
            vec![
                transition("first-id", "first", 0),
                transition("first-id", "first", 0),
            ],
        );
        assert!(matches!(
            duplicate,
            Err(ObservationFailure::CommittedTransitionOutOfOrderOrDuplicate { .. })
        ));
    }

    #[test]
    fn runtime_payload_cardinality_mismatch_returns_no_branch() {
        let mut first = spec("first");
        first.domain_events = vec![DomainEventSpec {
            constructor: "binding".into(),
            payload: vec![PayloadSource::BindingValue(0)],
        }];
        let manifest = InstalledObservationManifest::install(vec![first]).unwrap();
        let result = adapt_branch(
            Some(&manifest),
            vec![transition_id("first-id", 0)],
            Value::Null,
            1,
            Vec::new(),
            vec![transition("first-id", "first", 0)],
        );
        assert_eq!(
            result,
            Err(ObservationFailure::MissingPayloadSource(
                PayloadSource::BindingValue(0)
            ))
        );
    }

    #[test]
    fn rollback_is_distinct_and_erasure_preserves_semantic_branch() {
        let branch = adapt_branch(
            None,
            Vec::new(),
            Value::from(7),
            2,
            Vec::new(),
            vec![ObservationEventOutput::Uncommitted {
                id: TransitionIdOutput {
                    rule: "discarded".into(),
                    target: "target".into(),
                },
                rule_label: Some("discarded-label".into()),
                effects: Vec::new(),
                reason: UncommittedReasonOutput::RolledBack,
            }],
        )
        .unwrap();
        assert!(branch.events.is_empty());
        assert_eq!(branch.rollbacks.len(), 1);
        assert_eq!(branch.erase_observations().state, Value::from(7));
    }
}
