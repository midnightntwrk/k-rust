//! Atomic source-position observation installation and branch-local event adaptation.
//!
//! A compiled rule can have several written authors. A committed transition is
//! attributed to an authored position only when every author has the same
//! observation specification. Otherwise the relevant event candidates carry a
//! typed unknown attribution and cannot become pattern witnesses.

use std::collections::{BTreeMap, BTreeSet};

use k_rust::backend::{
    BindingOutput, EffectOutput, EvaluationClassOutput, ObservationEventOutput, TraceEntry,
    TransitionClassOutput, TransitionIdOutput, UncommittedReasonOutput,
};
use k_rust::kore::{ast::Pattern, codec};
use kink_patch::SentenceRef;
use kink_pattern::AttributionUnknownReason;
use serde_json::Value;

/// One written baseline rule and its manifest-ordered emissions.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RuleObservationSpec {
    pub rule: SentenceRef,
    pub label: Option<String>,
    /// Exact backend identity passed to the public observed execution selector.
    pub backend_rule_identity: String,
    pub emit_rule_applied: bool,
    pub domain_events: Vec<DomainEventSpec>,
}

/// One domain event derived without interpreting pretty text or backend diagnostics.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DomainEventSpec {
    pub constructor: String,
    pub payload: Vec<PayloadSource>,
}

/// Closed payload sources exposed by the k-rust transition wire contract.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PayloadSource {
    BeforeState,
    AfterState,
    BindingVariable(usize),
    BindingValue(usize),
    /// The value bound to the uniquely named variable on the transition wire.
    BindingValueNamed(String),
    IntroducedPredicate(usize),
    Effect(usize),
}

/// An immutable, atomically validated observation manifest.
#[derive(Clone, Debug, PartialEq)]
pub struct InstalledObservationManifest {
    rules: Vec<InstalledRule>,
    by_identity: BTreeMap<String, usize>,
    selected_rules: Vec<SentenceRef>,
}

/// One source author of a compiled identity. `None` means that author is unobserved.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct AuthorObservation {
    pub rule: SentenceRef,
    pub spec: Option<RuleObservationSpec>,
}

impl InstalledObservationManifest {
    /// Synthetic manifest installer for branch-adapter unit tests.
    #[cfg(test)]
    fn install(specs: Vec<RuleObservationSpec>) -> Result<Self, ObservationFailure> {
        let mut authors = BTreeMap::<String, Vec<AuthorObservation>>::new();
        for spec in &specs {
            authors
                .entry(spec.backend_rule_identity.clone())
                .or_default()
                .push(AuthorObservation {
                    rule: spec.rule.clone(),
                    spec: Some(spec.clone()),
                });
        }
        Self::install_with_authors(specs, authors)
    }

    /// Installs selected positions with the complete authorship of their identities.
    /// The validator supplies authors from typed compile provenance.
    pub(crate) fn install_with_authors(
        specs: Vec<RuleObservationSpec>,
        authors: BTreeMap<String, Vec<AuthorObservation>>,
    ) -> Result<Self, ObservationFailure> {
        let mut selected_rules = BTreeSet::new();
        for spec in &specs {
            if !selected_rules.insert(spec.rule.clone()) {
                return Err(ObservationFailure::DuplicateSelector(spec.rule.clone()));
            }
            if spec.backend_rule_identity.is_empty() {
                return Err(ObservationFailure::InvalidManifest(
                    "backend rule identity must not be empty".into(),
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
        let selected_rules = specs.iter().map(|spec| spec.rule.clone()).collect();
        let mut grouped = BTreeMap::<String, Vec<RuleObservationSpec>>::new();
        let mut identity_order = Vec::new();
        for spec in specs {
            if !grouped.contains_key(&spec.backend_rule_identity) {
                identity_order.push(spec.backend_rule_identity.clone());
            }
            grouped
                .entry(spec.backend_rule_identity.clone())
                .or_default()
                .push(spec);
        }
        let rules = identity_order
            .into_iter()
            .map(|identity| {
                let selected = grouped
                    .remove(&identity)
                    .expect("grouped selected identity");
                let authors = authors.get(&identity).ok_or_else(|| {
                    ObservationFailure::InvalidManifest("missing compiled authorship".into())
                })?;
                if authors.is_empty() {
                    return Err(ObservationFailure::InvalidManifest(
                        "compiled identity has no authored rule".into(),
                    ));
                }
                let first = authors[0].spec.as_ref().map(observation_signature);
                let unanimous = authors
                    .iter()
                    .all(|author| author.spec.as_ref().map(observation_signature) == first);
                let attribution = if unanimous && first.is_some() {
                    InstalledAttribution::Certain(selected[0].clone())
                } else {
                    InstalledAttribution::Unknown {
                        selected,
                        reason: AttributionUnknownReason::DifferentObservationSpecs {
                            authors: authors.iter().map(|author| author.rule.clone()).collect(),
                        },
                    }
                };
                Ok(InstalledRule {
                    identity,
                    attribution,
                    author_count: authors.len(),
                })
            })
            .collect::<Result<Vec<_>, ObservationFailure>>()?;
        let by_identity = rules
            .iter()
            .enumerate()
            .map(|(ordinal, rule)| (rule.identity.clone(), ordinal))
            .collect();
        Ok(Self {
            rules,
            by_identity,
            selected_rules,
        })
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
        self.selected_rules.iter()
    }
}

#[derive(Clone, Debug, PartialEq)]
struct InstalledRule {
    identity: String,
    attribution: InstalledAttribution,
    author_count: usize,
}

#[derive(Clone, Debug, PartialEq)]
enum InstalledAttribution {
    Certain(RuleObservationSpec),
    Unknown {
        selected: Vec<RuleObservationSpec>,
        reason: AttributionUnknownReason,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ObservationSignature {
    rule_applied: Option<String>,
    domain_events: Vec<DomainEventSpec>,
}

fn rule_applied_constructor(spec: &RuleObservationSpec) -> String {
    spec.label.as_ref().map_or_else(
        || format!("rule:{}:{}", spec.rule.module, spec.rule.index),
        |label| format!("rule:{label}"),
    )
}

fn observation_signature(spec: &RuleObservationSpec) -> ObservationSignature {
    ObservationSignature {
        rule_applied: spec
            .emit_rule_applied
            .then(|| rule_applied_constructor(spec)),
        domain_events: spec.domain_events.clone(),
    }
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
    UnknownAttribution(UnknownAttributionEvent),
}

/// An emitted transition whose authored event vocabulary cannot be attributed.
#[derive(Clone, Debug, PartialEq)]
pub struct UnknownAttributionEvent {
    pub event_ordinal: usize,
    pub transition_ordinal: usize,
    pub emission_ordinal: usize,
    pub constructor: String,
    pub transition: TransitionIdOutput,
    pub rule: SentenceRef,
    pub reason: AttributionUnknownReason,
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
                match &selected.attribution {
                    InstalledAttribution::Certain(spec) => {
                        // A merged axiom may expose any one of its authors' labels.
                        if selected.author_count == 1 && rule_label.as_ref() != spec.label.as_ref()
                        {
                            return Err(ObservationFailure::RuleLabelMismatch {
                                identity: id.rule,
                                expected: spec.label.clone(),
                                actual: rule_label,
                            });
                        }
                        let mut emission_ordinal = 0;
                        if spec.emit_rule_applied {
                            let event_ordinal = events.len();
                            events.push(NativeEvent::RuleApplied(RuleAppliedEvent {
                                event_ordinal,
                                transition_ordinal,
                                emission_ordinal,
                                transition: id.clone(),
                                class,
                                rule: spec.rule.clone(),
                                label: spec.label.clone(),
                                bindings: bindings.clone(),
                                introduced_predicates: introduced_predicates.clone(),
                                before: before.clone(),
                                after: after.clone(),
                                effects: effects.clone(),
                            }));
                            emission_ordinal += 1;
                        }
                        for domain in &spec.domain_events {
                            let payload = domain
                                .payload
                                .iter()
                                .map(|source| {
                                    payload_value(
                                        source.clone(),
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
                                constructor: domain.constructor.clone(),
                                transition: id.clone(),
                                rule: spec.rule.clone(),
                                payload,
                            }));
                            emission_ordinal += 1;
                        }
                    }
                    InstalledAttribution::Unknown { selected, reason } => {
                        let mut candidates = BTreeMap::<String, SentenceRef>::new();
                        for spec in selected {
                            if spec.emit_rule_applied {
                                candidates
                                    .entry(rule_applied_constructor(spec))
                                    .or_insert_with(|| spec.rule.clone());
                            }
                            for domain in &spec.domain_events {
                                candidates
                                    .entry(domain.constructor.clone())
                                    .or_insert_with(|| spec.rule.clone());
                            }
                        }
                        for (emission_ordinal, (constructor, rule)) in
                            candidates.into_iter().enumerate()
                        {
                            events.push(NativeEvent::UnknownAttribution(UnknownAttributionEvent {
                                event_ordinal: events.len(),
                                transition_ordinal,
                                emission_ordinal,
                                constructor,
                                transition: id.clone(),
                                rule,
                                reason: reason.clone(),
                            }));
                        }
                    }
                }
            }
            ObservationEventOutput::Evaluation {
                rule: _,
                class,
                rule_label: _,
                anchor,
                before: _,
                after: _,
                effects,
            } => {
                inventory_evaluation_class(class);
                inventory_effects(&effects);
                if anchor > identity.len() || anchor < next_branch_ordinal {
                    return Err(ObservationFailure::InvalidEvaluationAnchor(anchor));
                }
                // Evaluation covers successor normalization only. It is diagnostic
                // activity; absence cannot establish a negative pattern result.
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
        | TransitionClassOutput::Claim => {}
    }
}

fn inventory_evaluation_class(class: EvaluationClassOutput) {
    match class {
        EvaluationClassOutput::FunctionEquation
        | EvaluationClassOutput::Simplification
        | EvaluationClassOutput::Builtin => {}
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
    let missing = || ObservationFailure::MissingPayloadSource(source.clone());
    Ok(match source {
        PayloadSource::BeforeState => DomainPayload::Term(before.clone()),
        PayloadSource::AfterState => DomainPayload::Term(after.clone()),
        PayloadSource::BindingVariable(index) => {
            DomainPayload::Term(bindings.get(index).ok_or_else(&missing)?.variable.clone())
        }
        PayloadSource::BindingValue(index) => {
            DomainPayload::Term(bindings.get(index).ok_or_else(&missing)?.value.clone())
        }
        PayloadSource::BindingValueNamed(ref name) => {
            let mut matching = bindings.iter().filter(|binding| {
                matches!(codec::from_value(&binding.variable), Ok(Pattern::Variable(ref variable)) if variable.name == *name)
            });
            let binding = matching.next().ok_or_else(&missing)?;
            if matching.next().is_some() {
                return Err(missing());
            }
            DomainPayload::Term(binding.value.clone())
        }
        PayloadSource::IntroducedPredicate(index) => {
            DomainPayload::Term(predicates.get(index).ok_or_else(&missing)?.clone())
        }
        PayloadSource::Effect(index) => {
            DomainPayload::Effect(effects.get(index).ok_or_else(&missing)?.clone())
        }
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
    InvalidEvaluationAnchor(usize),
}

#[cfg(test)]
mod tests {
    use super::*;
    use k_rust::backend::ObservationEventOutput;
    use k_rust::kompile::initial_configuration::kore_sort;
    use k_rust::kore::ast::{Variable, VariableKind};

    #[test]
    fn named_binding_payload_selects_by_variable() {
        let encoded_variable = |name: &str| {
            codec::to_value(&Pattern::Variable(Variable {
                kind: VariableKind::Element,
                name: name.into(),
                sort: kore_sort("SortNat"),
            }))
            .expect("KORE variable")
        };
        let a = codec::to_value(&Pattern::Variable(Variable {
            kind: VariableKind::Element,
            name: "a".into(),
            sort: kore_sort("SortNat"),
        }))
        .expect("KORE value");
        let v = codec::to_value(&Pattern::Variable(Variable {
            kind: VariableKind::Element,
            name: "v".into(),
            sort: kore_sort("SortNat"),
        }))
        .expect("KORE value");
        let binding = |name: &str, value: Value| BindingOutput {
            variable: encoded_variable(name),
            value,
        };
        let bindings = [binding("RuleVarA", a), binding("RuleVarV", v.clone())];
        let source = PayloadSource::BindingValueNamed("RuleVarV".into());
        let read = |source: PayloadSource, bindings: &[BindingOutput]| {
            payload_value(source, &Value::Null, &Value::Null, bindings, &[], &[])
        };
        assert_eq!(read(source.clone(), &bindings), Ok(DomainPayload::Term(v)));
        let missing = PayloadSource::BindingValueNamed("RuleVarMissing".into());
        assert_eq!(
            read(missing.clone(), &bindings),
            Err(ObservationFailure::MissingPayloadSource(missing))
        );
        let duplicated = [
            bindings[0].clone(),
            bindings[1].clone(),
            bindings[1].clone(),
        ];
        assert_eq!(
            read(source.clone(), &duplicated),
            Err(ObservationFailure::MissingPayloadSource(source))
        );
    }

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
    fn equal_identity_with_different_observation_specs_is_unknown() {
        let mut second = spec("second");
        second.backend_rule_identity = "first-id".into();
        let manifest = InstalledObservationManifest::install(vec![spec("first"), second]).unwrap();
        let branch = adapt_branch(
            Some(&manifest),
            vec![transition_id("first-id", 0)],
            Value::from(1),
            1,
            Vec::new(),
            vec![transition("first-id", "first", 0)],
        )
        .unwrap();
        assert!(branch.events.iter().all(|event| matches!(
            event,
            NativeEvent::UnknownAttribution(UnknownAttributionEvent {
                reason: AttributionUnknownReason::DifferentObservationSpecs { .. },
                ..
            })
        )));
    }

    #[test]
    fn equal_identity_with_same_observation_spec_attributes_normally() {
        let mut second = spec("second");
        second.backend_rule_identity = "first-id".into();
        second.label = Some("first".into());
        let manifest = InstalledObservationManifest::install(vec![spec("first"), second]).unwrap();
        let branch = adapt_branch(
            Some(&manifest),
            vec![transition_id("first-id", 0)],
            Value::from(1),
            1,
            Vec::new(),
            vec![transition("first-id", "second", 0)],
        )
        .unwrap();
        assert!(matches!(
            branch.events.as_slice(),
            [NativeEvent::RuleApplied(_)]
        ));
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
    fn successor_evaluation_is_anchored_without_becoming_transition_evidence() {
        let branch = adapt_branch(
            Some(&installed()),
            vec![transition_id("first-id", 0)],
            Value::from(2),
            1,
            Vec::new(),
            vec![
                transition("first-id", "first", 0),
                ObservationEventOutput::Evaluation {
                    rule: "equation-id".into(),
                    class: EvaluationClassOutput::FunctionEquation,
                    rule_label: Some("equation".into()),
                    anchor: 1,
                    before: Value::from(1),
                    after: Value::from(2),
                    effects: Vec::new(),
                },
            ],
        )
        .expect("evaluation at committed successor");
        assert_eq!(branch.events.len(), 1);
        assert!(matches!(branch.events[0], NativeEvent::RuleApplied(_)));
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
            NativeEvent::UnknownAttribution(event) => (
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
