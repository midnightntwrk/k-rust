//! Stable transition identities and opt-in structured observation contracts.

use std::{collections::BTreeMap, collections::BTreeSet, fmt, sync::Arc};

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

/// The kind of committed transition a transition observation records.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TransitionClass {
    Rewrite,
    Remainder,
    Claim,
}

/// The kind of rule applied while normalizing a branch state.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EvaluationClass {
    FunctionEquation,
    Simplification,
    Builtin,
}

/// Structured evidence for one committed transition of a branch.
///
/// Every transition observation names, by `id`, an element of the branch it is reported on, in
/// branch order; under a rule filter only the admitted elements are reported.
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

/// One equation, simplification, or builtin application performed while normalizing a state of
/// a branch.
///
/// Normalization rewrites a state to an equal state; it is not a transition, and the branch
/// records no identity for it. `anchor` places it on the branch: it is the number of committed
/// transitions (branch entries, filtered or not) that precede it, so the normalized state is the
/// one reached by `branch[..anchor]` (the initial state when `anchor` is 0), or that state
/// restricted by the negated conditions of higher-priority rules when the next transition is a
/// lower-priority rewrite. Anchors are non-decreasing along a branch's observations.
///
/// Evaluations are recorded for the normalization passes of retained branch states: the term
/// normalization of the initial state and of every rewrite successor and remainder, the
/// normalization of a higher-priority remainder before a lower-priority rewrite, and the pattern
/// normalization of a state leaving the engine as a leaf or search result. A cut-point rule is
/// proposed, not committed: its leaf stays at the state before it, and neither the rule nor its
/// successor's normalization is on that leaf's branch. Constraint simplification at the start of a
/// step reports none. Evaluations performed while deciding a rule's side conditions or building its
/// right-hand side belong to that rule's application, committed or not, and are not reported;
/// neither is the simplification that decides, at a branch stop, which candidate successors
/// survive, although a surviving candidate's own later normalization is. Evaluations of a state
/// that is later dropped (a remainder that simplifies to bottom, a leaf merged into an equal leaf,
/// leaves the breadth bound discards) are reported on no branch. Which evaluations occur, how
/// often, and in which order depends on the simplifier's strategy, so these events are diagnostics:
/// their absence is not evidence that an equation does not apply.
///
/// `before` and `after` are the endpoints of the whole normalization pass, shared by every
/// evaluation that pass performed.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EvaluationObservation {
    pub rule: String,
    pub class: EvaluationClass,
    pub rule_label: Option<String>,
    pub anchor: usize,
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
    Evaluation(EvaluationObservation),
    Uncommitted(UncommittedObservation),
}

/// One ordered write to a console descriptor on an execution branch.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DescriptorTranscriptEntry {
    /// The hook that produced this write.
    pub hook: &'static str,
    pub descriptor: i32,
    pub bytes: Arc<[u8]>,
}

/// Buffered console state owned by one execution branch.
///
/// Input is immutable and shared between forks. The cursor and transcript are values of the
/// branch, while the transcript storage is copied only when a fork first appends to it.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ExecutionIoState {
    input: Arc<[u8]>,
    cursor: usize,
    transcript: Arc<Vec<DescriptorTranscriptEntry>>,
}

impl ExecutionIoState {
    pub fn new(input: impl Into<Arc<[u8]>>) -> Self {
        Self {
            input: input.into(),
            cursor: 0,
            transcript: Arc::default(),
        }
    }

    pub fn input(&self) -> &[u8] {
        &self.input
    }

    pub const fn cursor(&self) -> usize {
        self.cursor
    }

    pub fn remaining_input(&self) -> &[u8] {
        &self.input[self.cursor..]
    }

    pub fn transcript(&self) -> &[DescriptorTranscriptEntry] {
        &self.transcript
    }

    /// Fork a tentative evaluator state from this branch.
    ///
    /// Dropping the context rolls every read and write back. `commit` returns the updated state
    /// for the caller to attach to the retained successor.
    pub(crate) fn begin_evaluation(&self) -> ExecutionEvaluationContext {
        ExecutionEvaluationContext {
            state: self.clone(),
        }
    }
}

/// The console capability available to an impure builtin candidate.
///
/// This context owns only buffered semantic state. It has no process handles and cannot read from
/// or write to the host. Candidate selection commits it by attaching `commit()`'s result to the
/// selected successor; a failed candidate is rolled back by dropping the context.
#[derive(Debug)]
pub(crate) struct ExecutionEvaluationContext {
    state: ExecutionIoState,
}

impl ExecutionEvaluationContext {
    pub(crate) fn read(&mut self, maximum: usize) -> &[u8] {
        let start = self.state.cursor;
        let end = start.saturating_add(maximum).min(self.state.input.len());
        self.state.cursor = end;
        &self.state.input[start..end]
    }

    pub(crate) fn append(
        &mut self,
        hook: &'static str,
        descriptor: i32,
        bytes: impl Into<Arc<[u8]>>,
    ) {
        Arc::make_mut(&mut self.state.transcript).push(DescriptorTranscriptEntry {
            hook,
            descriptor,
            bytes: bytes.into(),
        });
    }

    pub(crate) fn commit(self) -> ExecutionIoState {
        self.state
    }
}

/// Effects owned by the committed prefix of one execution branch.
///
/// Simplification and rule application return candidate effects as ordinary vectors. The
/// execution loop may append them here only when it retains that candidate as a successor. A
/// branch copies the journal with its semantic state, so effects from sibling, rolled-back, or
/// pruned candidates cannot enter another branch's transcript.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct EffectJournal {
    committed: Vec<BuiltinEffect>,
}

impl EffectJournal {
    pub(crate) fn commit(&mut self, effects: impl IntoIterator<Item = BuiltinEffect>) {
        self.committed.extend(effects);
    }

    pub(crate) fn into_committed(self) -> Vec<BuiltinEffect> {
        self.committed
    }
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
        let mut available = BTreeMap::<(String, Option<usize>), usize>::new();
        for priorities in definition.rewrite_theory.values() {
            for rules in priorities.values() {
                for rule in rules {
                    *available
                        .entry((
                            rule.rule.attributes.unique_id.clone(),
                            rule.rule.lhs_alternative,
                        ))
                        .or_default() += 1;
                }
            }
        }

        let mut selected = BTreeSet::new();
        for rule in rules.into_iter().map(Into::into) {
            if !selected.insert(rule.clone()) {
                return Err(ObservationFilterError::DuplicateRule(rule));
            }
            let counts = available
                .iter()
                .filter_map(|((id, _), count)| (id == &rule).then_some(*count))
                .collect::<Vec<_>>();
            if counts.is_empty() {
                return Err(ObservationFilterError::UnknownRule(rule));
            }
            if counts.iter().any(|count| *count > 1) {
                return Err(ObservationFilterError::AmbiguousRule(rule));
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
    /// Committed transitions on the chain ending at this node, this node's included.
    transitions: usize,
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
        Some(self.push(parent, Some(id), event))
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
        Some(self.push(parent, Some(id), event))
    }

    /// Record the evaluations of one normalization pass of the state at `parent`'s branch
    /// position; see [`EvaluationObservation`] for the anchor.
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
        let anchor = self.transitions(parent);
        let mut effects = effects.iter().peekable();
        for rule in applied_rules {
            let class = evaluation_class(definition, rule);
            let attributed_effects = if let Some(hook) = rule.strip_prefix("builtin:")
                && class == EvaluationClass::Builtin
                && effects.peek().is_some_and(|effect| effect.hook() == hook)
            {
                vec![effects.next().expect("peeked effect").clone()]
            } else {
                Vec::new()
            };
            if !options.observes(rule) {
                continue;
            }
            parent = Some(self.push(
                parent,
                None,
                Some(ObservationEvent::Evaluation(EvaluationObservation {
                    rule: rule.clone(),
                    class,
                    rule_label: equation_label(definition, rule),
                    anchor,
                    before: before.clone(),
                    after: after.clone(),
                    effects: attributed_effects,
                })),
            ));
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

    fn transitions(&self, head: ObservationHead) -> usize {
        head.map_or(0, |id| self.nodes[id.0].transitions)
    }

    fn push(
        &mut self,
        parent: ObservationHead,
        transition: Option<TransitionId>,
        event: Option<ObservationEvent>,
    ) -> ObservationNodeId {
        let transitions = self.transitions(parent) + usize::from(transition.is_some());
        let id = ObservationNodeId(self.nodes.len());
        self.nodes.push(ObservationNode {
            parent,
            transitions,
            transition,
            event,
        });
        id
    }
}

fn evaluation_class(definition: &BackendDefinition, rule_id: &str) -> EvaluationClass {
    if rule_id.starts_with("builtin:") {
        return EvaluationClass::Builtin;
    }
    if theory_contains_rule(&definition.function_theory, rule_id) {
        EvaluationClass::FunctionEquation
    } else {
        EvaluationClass::Simplification
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

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    use super::{
        DescriptorTranscriptEntry, EvaluationClass, ExecutionIoState, ObservationEvent,
        ObservationOptions,
    };
    use crate::{
        definition::BackendDefinition,
        rewrite::{ExecutionOptions, Pattern, execute_observed},
    };

    /// A filtered-out rewrite is still a committed transition of the branch, so the evaluation
    /// of its successor is anchored after it. The filter is built directly because the public
    /// allowlist admits rewrite identities only.
    #[test]
    fn evaluation_anchor_counts_transitions_the_filter_excludes() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortS{} [hasDomainValues{}()]
                symbol wrap{}(SortS{}) : SortS{}
                    [function{}(), total{}(), injective{}(), no-evaluators{}()]
                symbol value{}() : SortS{} [function{}(), total{}()]
                axiom{R} \implies{R}(
                    \and{R}(\top{R}(), \top{R}()),
                    \equals{SortS{}, R}(
                        value{}(),
                        \and{SortS{}}(\dv{SortS{}}("value"), \top{SortS{}}())
                    )
                ) [label{}("value")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                    value{}()
                ) [label{}("step")]
            endmodule []"#,
        )
        .unwrap();
        let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
        let initial = Pattern {
            term: definition
                .internalize_term(&parse_pattern("wrap{}(value{}())").unwrap(), &[])
                .unwrap(),
            constraints: Vec::new(),
        };
        let options = ObservationOptions {
            rules: Some(BTreeSet::from(["value".to_owned()])),
        };

        let result = execute_observed(&definition, initial, ExecutionOptions::default(), &options);

        let [leaf] = result.leaves.as_slice() else {
            panic!("expected one leaf: {:?}", result.leaves);
        };
        assert_eq!(leaf.branch.len(), 1);
        assert_eq!(leaf.branch[0].rule, "step");
        let anchors = leaf
            .observations
            .iter()
            .map(|event| match event {
                ObservationEvent::Evaluation(evaluation) => {
                    assert_eq!(evaluation.rule, "value");
                    assert_eq!(evaluation.class, EvaluationClass::FunctionEquation);
                    evaluation.anchor
                }
                other => panic!("the filter selects only the equation: {other:?}"),
            })
            .collect::<Vec<_>>();
        assert_eq!(anchors, [0, 1]);
    }

    #[test]
    fn evaluation_reads_prebuffered_input_in_order() {
        let state = ExecutionIoState::new(Vec::from(&b"abcd"[..]));
        let mut evaluation = state.begin_evaluation();

        assert_eq!(evaluation.read(2), b"ab");
        assert_eq!(evaluation.read(3), b"cd");
        assert_eq!(evaluation.read(1), b"");

        let committed = evaluation.commit();
        assert_eq!(committed.cursor(), 4);
        assert_eq!(committed.remaining_input(), b"");
    }

    #[test]
    fn dropping_a_failed_evaluation_does_not_advance_the_branch_cursor() {
        let state = ExecutionIoState::new(Vec::from(&b"retry"[..]));
        let mut failed = state.begin_evaluation();
        assert_eq!(failed.read(3), b"ret");
        drop(failed);

        assert_eq!(state.cursor(), 0);
        let mut retry = state.begin_evaluation();
        assert_eq!(retry.read(3), b"ret");
        assert_eq!(retry.commit().cursor(), 3);
    }

    #[test]
    fn forks_after_a_read_have_independent_cursors() {
        let state = ExecutionIoState::new(Vec::from(&b"abcdef"[..]));
        let mut first = state.begin_evaluation();
        assert_eq!(first.read(1), b"a");
        let fork_point = first.commit();

        let mut left = fork_point.begin_evaluation();
        let mut right = fork_point.begin_evaluation();
        assert_eq!(left.read(2), b"bc");
        assert_eq!(right.read(4), b"bcde");

        let left = left.commit();
        let right = right.commit();
        assert_eq!(fork_point.cursor(), 1);
        assert_eq!(left.cursor(), 3);
        assert_eq!(right.cursor(), 5);
        assert_eq!(left.remaining_input(), b"def");
        assert_eq!(right.remaining_input(), b"f");
    }

    #[test]
    fn forks_retain_distinct_ordered_descriptor_transcripts() {
        let state = ExecutionIoState::default();
        let mut left = state.begin_evaluation();
        let mut right = state.begin_evaluation();

        left.append("IO.write", 1, Vec::from(&b"left-out"[..]));
        left.append("IO.putc", 2, Vec::from(&b"left-err"[..]));
        right.append("IO.write", 2, Vec::from(&b"right-err"[..]));
        right.append("IO.putc", 1, Vec::from(&b"right-out"[..]));

        let left = left.commit();
        let right = right.commit();
        assert!(state.transcript().is_empty());
        assert_eq!(
            left.transcript(),
            [
                DescriptorTranscriptEntry {
                    hook: "IO.write",
                    descriptor: 1,
                    bytes: Vec::from(&b"left-out"[..]).into(),
                },
                DescriptorTranscriptEntry {
                    hook: "IO.putc",
                    descriptor: 2,
                    bytes: Vec::from(&b"left-err"[..]).into(),
                },
            ]
        );
        assert_eq!(
            right.transcript(),
            [
                DescriptorTranscriptEntry {
                    hook: "IO.write",
                    descriptor: 2,
                    bytes: Vec::from(&b"right-err"[..]).into(),
                },
                DescriptorTranscriptEntry {
                    hook: "IO.putc",
                    descriptor: 1,
                    bytes: Vec::from(&b"right-out"[..]).into(),
                },
            ]
        );
    }
}
