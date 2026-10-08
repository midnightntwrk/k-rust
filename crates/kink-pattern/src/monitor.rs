//! Incremental pattern monitor and shared-prefix tree evaluation.
//!
//! [`Monitor`] is a deterministic, branch-local automaton for one plan over one path: it is fed
//! the events of each step in order and keeps the partial occurrences of the plan's arms, an
//! `indeterminate` flag and the completed occurrences. [`Monitor::finish`] applies the witness
//! gate of [`evaluate_with`] (side condition, real prefix, `feasible`) under a path, which may be
//! the path's leaf or, for an online use, a depth cut of it.
//!
//! [`evaluate_tree`] runs the monitor over a [`PathTree`] whose nodes carry step events and whose
//! leaves are the [`PathInput`]s `evaluate_with` would receive, and returns the same
//! [`Evaluation`]. Its result equals `evaluate_with` over the leaves, under one premise (the T1
//! rule of corpus-scale README 4.6, "phase 2 under each leaf's predicate"):
//!
//! - `RelationDecider::relate` reads its path argument only through the path predicate, the
//!   equivalences and the inequalities (true of [`StructuralDecider`] and of kink-native's
//!   `BackendRelations`). Leaves that agree on those three share the monitor state of their
//!   common prefix, and `relate` is asked with the first such leaf. `feasible` and the side
//!   condition are always decided with the leaf itself.
//!
//! Inputs are validated by `evaluate_with` itself, called with the plan's arms removed (so it
//! matches nothing), which makes every validation error the reference's own. Where the monitor
//! cannot decide an input the way the reference does, it defers to the reference: a side
//! condition with a supplied side table (the table's rows are private to the reference), and
//! the existential-first collection check failing (the reference produces that error).
//!
//! A partial occurrence is keyed by (arm, next atom, chosen event indices, bindings, sorted
//! assumptions). The chosen indices are part of the key because `evaluate_with` reports one
//! witness per occurrence, so two occurrences with equal bindings and assumptions are two
//! witnesses. The `NextEvent` gap of a partial is the distance between its last chosen event
//! and the event under consideration; the partial is dropped after a `Certain` event, which
//! ends the reference's scan. At most `cap` partials are kept per monitor (one (slot, path));
//! the excess is evicted from the largest key down and sets `indeterminate`, so an overflow can
//! block `NoMatch` but never creates a witness.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use k_rust::kore::ast::Pattern;

use crate::pattern::{
    Atom, Binding, CollectionEvidence, CollectionStop, Evaluation, EvaluationContext,
    EvaluationOptions, Event, EventPresence, ExecutionStop, ExecutionTerminal, Feasibility,
    MatchMode, PathInput, PathStop, PatternArm, PatternFailure, PatternOutcome, PatternPlan,
    Relation, RelationDecider, RelationDecision, SearchPolicy, SideCondition, SideConditionTable,
    StructuralDecider, TermRelation, Witness, evaluate_with,
};

/// The default bound on partial occurrences per (slot, path): corpus-scale Q9, M5.
pub const DEFAULT_PARTIAL_CAP: usize = 4096;

/// The name of the side condition of the validation probe plan. The probe passes no side
/// table, so the condition is `Unknown` on every occurrence of the probe.
const PROBE_SIDE_CONDITION: &str = "kink-monitor-validation-probe";

/// Options of one monitor.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct MonitorOptions {
    /// At most this many partial occurrences per (slot, path); an overflow evicts the largest
    /// keys and sets `indeterminate`.
    pub cap: usize,
}

impl Default for MonitorOptions {
    fn default() -> Self {
        Self {
            cap: DEFAULT_PARTIAL_CAP,
        }
    }
}

/// A misuse of the incremental API.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum MonitorError {
    /// An event does not continue the path: its index is not the next one.
    EventIndex { expected: usize, found: usize },
    /// `finish` was asked with a path whose events are not exactly the events pushed so far.
    PathEvents { pushed: usize, path: usize },
}

impl fmt::Display for MonitorError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EventIndex { expected, found } => {
                write!(
                    formatter,
                    "event index {found} where {expected} was expected"
                )
            }
            Self::PathEvents { pushed, path } => write!(
                formatter,
                "the path has {path} events but the monitor was given {pushed}"
            ),
        }
    }
}

impl std::error::Error for MonitorError {}

/// One partial occurrence: `next_atom` atoms of arm `arm` are matched at `indices`.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Partial {
    arm: usize,
    next_atom: usize,
    indices: Vec<usize>,
    bindings: BTreeMap<String, Pattern>,
    assumptions: Vec<TermRelation>,
}

/// One complete occurrence awaiting the witness gate.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Occurrence {
    arm: usize,
    indices: Vec<usize>,
    bindings: BTreeMap<String, Pattern>,
    assumptions: Vec<TermRelation>,
}

/// The witnesses of one path and whether it had an indeterminate candidate.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MonitorVerdict {
    /// In discovery order; [`evaluate_tree`] sorts them as `evaluate_with` does.
    pub witnesses: Vec<Witness>,
    pub indeterminate: bool,
}

/// The incremental, branch-local monitor of one plan over one path.
#[derive(Clone, Debug)]
pub struct Monitor<'p> {
    plan: &'p PatternPlan,
    cap: usize,
    partials: BTreeSet<Partial>,
    completed: Vec<Occurrence>,
    events: usize,
    indeterminate: bool,
    overflowed: bool,
    peak: usize,
}

enum AtomMatch {
    Matched(BTreeMap<String, Pattern>, Vec<TermRelation>),
    Indeterminate,
    Mismatch,
}

impl<'p> Monitor<'p> {
    /// A monitor at the start of a path.
    #[must_use]
    pub const fn new(plan: &'p PatternPlan, options: MonitorOptions) -> Self {
        Self {
            plan,
            cap: options.cap,
            partials: BTreeSet::new(),
            completed: Vec::new(),
            events: 0,
            indeterminate: false,
            overflowed: false,
            peak: 0,
        }
    }

    /// A copy for one child of a branch point. States are never merged across siblings.
    #[must_use]
    pub fn branch(&self) -> Self {
        self.clone()
    }

    /// Feeds the events of one step. `relate_on` is the path under which `decider.relate`
    /// decides payload relations (the leaf, or any path with the leaf's predicate and
    /// relations; see the module documentation).
    ///
    /// # Errors
    ///
    /// [`MonitorError::EventIndex`] when an event's index is not the next one; the events
    /// before it in `events` have been consumed.
    pub fn push_step(
        &mut self,
        events: &[Event],
        relate_on: &PathInput,
        decider: &dyn RelationDecider,
    ) -> Result<(), MonitorError> {
        for event in events {
            if event.index != self.events {
                return Err(MonitorError::EventIndex {
                    expected: self.events,
                    found: event.index,
                });
            }
            self.push_event(event, relate_on, decider);
            self.events += 1;
        }
        Ok(())
    }

    fn push_event(&mut self, event: &Event, relate_on: &PathInput, decider: &dyn RelationDecider) {
        let plan = self.plan;
        let mut created = Vec::new();
        let empty = BTreeMap::new();
        for (arm_ordinal, arm) in plan.arms.iter().enumerate() {
            let Some(first) = arm.atoms.first() else {
                continue;
            };
            match match_atom(first, event, &empty, &[], relate_on, decider) {
                AtomMatch::Matched(bindings, assumptions) => self.advance(
                    Partial {
                        arm: arm_ordinal,
                        next_atom: 1,
                        indices: vec![event.index],
                        bindings,
                        assumptions,
                    },
                    &mut created,
                ),
                AtomMatch::Indeterminate => self.indeterminate = true,
                AtomMatch::Mismatch => {}
            }
        }
        let existing = std::mem::take(&mut self.partials);
        let mut kept = BTreeSet::new();
        for partial in existing {
            let arm = &plan.arms[partial.arm];
            let Some(relation) = arm.relations.get(partial.next_atom - 1).copied() else {
                continue;
            };
            let previous = *partial
                .indices
                .last()
                .expect("a partial has chosen an event");
            let gap = relation == Relation::NextEvent && event.index > previous + 1;
            match match_atom(
                &arm.atoms[partial.next_atom],
                event,
                &partial.bindings,
                &partial.assumptions,
                relate_on,
                decider,
            ) {
                AtomMatch::Matched(_, _) if gap => self.indeterminate = true,
                AtomMatch::Matched(bindings, assumptions) => {
                    let mut indices = partial.indices.clone();
                    indices.push(event.index);
                    self.advance(
                        Partial {
                            arm: partial.arm,
                            next_atom: partial.next_atom + 1,
                            indices,
                            bindings,
                            assumptions,
                        },
                        &mut created,
                    );
                }
                AtomMatch::Indeterminate => self.indeterminate = true,
                AtomMatch::Mismatch => {}
            }
            // The reference's `NextEvent` scan ends at the first Certain intermediate event.
            if !(relation == Relation::NextEvent
                && matches!(event.presence, EventPresence::Certain))
            {
                kept.insert(partial);
            }
        }
        kept.extend(created);
        while kept.len() > self.cap {
            kept.pop_last();
            self.overflowed = true;
            self.indeterminate = true;
        }
        self.peak = self.peak.max(kept.len());
        self.partials = kept;
    }

    /// Records `step` (whose `next_atom` atoms are matched) as complete or as a new partial.
    fn advance(&mut self, step: Partial, created: &mut Vec<Partial>) {
        if step.next_atom == self.plan.arms[step.arm].atoms.len() {
            self.completed.push(Occurrence {
                arm: step.arm,
                indices: step.indices,
                bindings: step.bindings,
                assumptions: step.assumptions,
            });
        } else {
            created.push(step);
        }
    }

    /// The witnesses of the occurrences completed so far, under `path`: the witness gate of
    /// `evaluate_with` with no side table (a side condition is `Unknown`), then the real-prefix
    /// test of `path.stop`, then `decider.feasible(path, assumptions)` for non-empty
    /// assumptions. `path` is the leaf, or the depth-k cut of the path for the reference
    /// semantics R(k) (corpus-scale README 4.6). Does not consume the monitor.
    ///
    /// # Errors
    ///
    /// [`MonitorError::PathEvents`] when `path` does not have exactly the pushed events.
    pub fn finish(
        &self,
        path: &PathInput,
        decider: &dyn RelationDecider,
    ) -> Result<MonitorVerdict, MonitorError> {
        if path.events.len() != self.events {
            return Err(MonitorError::PathEvents {
                pushed: self.events,
                path: path.events.len(),
            });
        }
        let mut indeterminate = self.indeterminate;
        let mut witnesses = Vec::new();
        for occurrence in &self.completed {
            if self.plan.side_condition.is_some() {
                indeterminate = true;
                continue;
            }
            if let Some(witness) = gate(self.plan, occurrence, path, decider, &mut indeterminate) {
                witnesses.push(witness);
            }
        }
        Ok(MonitorVerdict {
            witnesses,
            indeterminate,
        })
    }

    /// Whether a candidate was indeterminate or the cap overflowed so far.
    #[must_use]
    pub const fn indeterminate(&self) -> bool {
        self.indeterminate
    }

    /// Whether the cap evicted a partial occurrence.
    #[must_use]
    pub const fn overflowed(&self) -> bool {
        self.overflowed
    }

    /// The number of live partial occurrences.
    #[must_use]
    pub fn partials(&self) -> usize {
        self.partials.len()
    }

    /// The largest number of live partial occurrences after any event.
    #[must_use]
    pub const fn peak_partials(&self) -> usize {
        self.peak
    }

    /// The number of events pushed.
    #[must_use]
    pub const fn events(&self) -> usize {
        self.events
    }
}

/// The real-prefix and feasibility part of the witness gate, for a plan without a side
/// condition.
fn gate(
    plan: &PatternPlan,
    occurrence: &Occurrence,
    path: &PathInput,
    decider: &dyn RelationDecider,
    indeterminate: &mut bool,
) -> Option<Witness> {
    if !path.stop.has_real_prefix() {
        *indeterminate = true;
        return None;
    }
    if !occurrence.assumptions.is_empty() {
        match decider.feasible(path, &occurrence.assumptions) {
            Feasibility::Sat => {}
            Feasibility::Unsat => return None,
            Feasibility::Unknown => {
                *indeterminate = true;
                return None;
            }
        }
    }
    let bindings = plan
        .variables
        .iter()
        .map(|(name, _)| Binding {
            name: name.clone(),
            term: occurrence
                .bindings
                .get(name)
                .expect("validated arm binds every variable")
                .clone(),
        })
        .collect();
    Some(Witness {
        path_ordinal: path.path_ordinal,
        path_key: path.path_key.clone(),
        arm_ordinal: occurrence.arm,
        event_indices: occurrence.indices.clone(),
        events: occurrence
            .indices
            .iter()
            .map(|index| path.events[*index].clone())
            .collect(),
        bindings,
        assumptions: occurrence.assumptions.clone(),
        path_predicate: path.path_predicate.clone(),
        stop_reason: path.stop,
        execution_stop_reason: path.execution_stop,
    })
}

/// `evaluate_with`'s atom match, rule for rule.
fn match_atom(
    atom: &Atom,
    event: &Event,
    bindings: &BTreeMap<String, Pattern>,
    assumptions: &[TermRelation],
    path: &PathInput,
    decider: &dyn RelationDecider,
) -> AtomMatch {
    if atom.constructor != event.constructor {
        return AtomMatch::Mismatch;
    }
    if matches!(event.presence, EventPresence::Undecided) {
        return AtomMatch::Indeterminate;
    }
    let mut resolved = bindings.clone();
    let mut assumed = assumptions.to_vec();
    if let EventPresence::Conditional(relations) = &event.presence {
        assumed.extend(relations.iter().cloned());
        assumed.sort();
        assumed.dedup();
    }
    for clause in &atom.payload {
        let Some(term) = event.payload.get(clause.position) else {
            return AtomMatch::Mismatch;
        };
        match clause.mode {
            MatchMode::Bind
                if resolved
                    .insert(clause.variable.clone(), term.clone())
                    .is_none() => {}
            MatchMode::Bind => return AtomMatch::Mismatch,
            MatchMode::Use => {
                let Some(bound) = resolved.get(&clause.variable) else {
                    return AtomMatch::Mismatch;
                };
                match decider.relate(path, &assumed, bound, term) {
                    RelationDecision::Equal => {}
                    RelationDecision::EqualIf(relations) => {
                        assumed.extend(relations);
                        assumed.sort();
                        assumed.dedup();
                    }
                    RelationDecision::Unequal => return AtomMatch::Mismatch,
                    RelationDecision::Indeterminate => return AtomMatch::Indeterminate,
                }
            }
        }
    }
    AtomMatch::Matched(resolved, assumed)
}

/// A node of a [`PathTree`].
pub type NodeId = usize;

/// A misuse of the tree builder.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TreeError {
    UnknownNode(NodeId),
    /// A leaf's events are not the concatenation of the step events from the root to its node.
    LeafEvents {
        node: NodeId,
    },
}

impl fmt::Display for TreeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnknownNode(node) => write!(formatter, "no tree node {node}"),
            Self::LeafEvents { node } => write!(
                formatter,
                "a leaf at node {node} has events other than the node's step events"
            ),
        }
    }
}

impl std::error::Error for TreeError {}

#[derive(Clone, Debug, Eq, PartialEq)]
struct TreeNode {
    parent: Option<NodeId>,
    events: Vec<Event>,
    children: Vec<NodeId>,
    leaves: Vec<usize>,
}

/// A path tree: each node carries the events of one step (the root carries none), and each
/// leaf is the [`PathInput`] of the path from the root to its node. A node without a leaf in
/// its subtree is a discarded branch and is never evaluated.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PathTree {
    nodes: Vec<TreeNode>,
    paths: Vec<PathInput>,
    leaf_nodes: Vec<NodeId>,
}

impl Default for PathTree {
    fn default() -> Self {
        Self::new()
    }
}

impl PathTree {
    /// The root, which carries no events.
    pub const ROOT: NodeId = 0;

    /// A tree with only the root.
    #[must_use]
    pub fn new() -> Self {
        Self {
            nodes: vec![TreeNode {
                parent: None,
                events: Vec::new(),
                children: Vec::new(),
                leaves: Vec::new(),
            }],
            paths: Vec::new(),
            leaf_nodes: Vec::new(),
        }
    }

    /// The tree of `paths`, in their order: a path's events are split into steps (maximal runs
    /// of equal `step`), and paths share a node exactly while their step events are equal.
    #[must_use]
    pub fn from_paths(paths: Vec<PathInput>) -> Self {
        let mut tree = Self::new();
        for path in paths {
            let mut node = Self::ROOT;
            let mut start = 0;
            while start < path.events.len() {
                let step = path.events[start].step;
                let end = path.events[start..]
                    .iter()
                    .position(|event| event.step != step)
                    .map_or(path.events.len(), |offset| start + offset);
                let events = &path.events[start..end];
                node = match tree.nodes[node]
                    .children
                    .iter()
                    .copied()
                    .find(|child| tree.nodes[*child].events == events)
                {
                    Some(child) => child,
                    None => tree.attach(node, events.to_vec()),
                };
                start = end;
            }
            tree.nodes[node].leaves.push(tree.paths.len());
            tree.paths.push(path);
            tree.leaf_nodes.push(node);
        }
        tree
    }

    fn attach(&mut self, parent: NodeId, events: Vec<Event>) -> NodeId {
        let id = self.nodes.len();
        self.nodes.push(TreeNode {
            parent: Some(parent),
            events,
            children: Vec::new(),
            leaves: Vec::new(),
        });
        self.nodes[parent].children.push(id);
        id
    }

    /// Adds a child of `parent` carrying the events of one step.
    ///
    /// # Errors
    ///
    /// [`TreeError::UnknownNode`] when `parent` is not a node of this tree.
    pub fn add_child(&mut self, parent: NodeId, events: Vec<Event>) -> Result<NodeId, TreeError> {
        if parent >= self.nodes.len() {
            return Err(TreeError::UnknownNode(parent));
        }
        Ok(self.attach(parent, events))
    }

    /// Adds a leaf at `node`. Leaves are evaluated, and their ordinals checked, in the order
    /// they are added, like the paths given to `evaluate_with`.
    ///
    /// # Errors
    ///
    /// [`TreeError::UnknownNode`] for a node outside the tree, and [`TreeError::LeafEvents`]
    /// when `path.events` is not the concatenation of the events from the root to `node`.
    pub fn add_leaf(&mut self, node: NodeId, path: PathInput) -> Result<(), TreeError> {
        if node >= self.nodes.len() {
            return Err(TreeError::UnknownNode(node));
        }
        if self.events_to(node) != path.events {
            return Err(TreeError::LeafEvents { node });
        }
        self.nodes[node].leaves.push(self.paths.len());
        self.paths.push(path);
        self.leaf_nodes.push(node);
        Ok(())
    }

    fn events_to(&self, node: NodeId) -> Vec<Event> {
        let mut chain = Vec::new();
        let mut current = Some(node);
        while let Some(id) = current {
            chain.push(id);
            current = self.nodes[id].parent;
        }
        chain
            .iter()
            .rev()
            .flat_map(|id| self.nodes[*id].events.iter().cloned())
            .collect()
    }

    /// The leaves in insertion order.
    #[must_use]
    pub fn paths(&self) -> &[PathInput] {
        &self.paths
    }

    /// The node of leaf `leaf` (an index into [`Self::paths`]).
    #[must_use]
    pub fn leaf_node(&self, leaf: usize) -> Option<NodeId> {
        self.leaf_nodes.get(leaf).copied()
    }

    /// The parent of `node`; `None` for the root and for a node outside the tree.
    #[must_use]
    pub fn parent(&self, node: NodeId) -> Option<NodeId> {
        self.nodes.get(node).and_then(|node| node.parent)
    }

    /// The step events `node` carries.
    #[must_use]
    pub fn events(&self, node: NodeId) -> Option<&[Event]> {
        self.nodes.get(node).map(|node| node.events.as_slice())
    }

    /// The number of nodes, the root included.
    #[must_use]
    pub fn nodes(&self) -> usize {
        self.nodes.len()
    }
}

/// Options of [`evaluate_tree`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TreeOptions {
    pub evaluation: EvaluationOptions,
    pub monitor: MonitorOptions,
}

/// Counters of one tree evaluation (diagnostic only; nothing reads them for a verdict).
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct TreeStats {
    /// Leaf groups that share prefix states (equal predicate and relations).
    pub groups: usize,
    /// Node visits, summed over groups.
    pub node_visits: usize,
    /// Events pushed, summed over groups.
    pub events_pushed: usize,
    /// The largest number of live partials of any monitor.
    pub peak_partials: usize,
    /// Whether any monitor's cap evicted a partial.
    pub overflowed: bool,
    /// Whether the result is `evaluate_with`'s own (a supplied side table, or the
    /// existential-first collection check failing).
    pub deferred: bool,
}

/// [`evaluate_with`] over the leaves of `tree`, computed by the monitor over shared prefixes.
/// See the module documentation for the premise on `relate` and the cases that defer to the
/// reference.
///
/// # Errors
///
/// The [`PatternFailure`] `evaluate_with` returns for the same leaves.
pub fn evaluate_tree(
    context: &EvaluationContext,
    plan: &PatternPlan,
    tree: &PathTree,
    collection: &CollectionEvidence,
    side_table: Option<&SideConditionTable>,
    options: TreeOptions,
    decider: &dyn RelationDecider,
) -> Result<Evaluation, PatternFailure> {
    evaluate_tree_with_stats(
        context, plan, tree, collection, side_table, options, decider,
    )
    .map(|(evaluation, _)| evaluation)
}

/// [`evaluate_tree`] with its counters.
///
/// # Errors
///
/// As [`evaluate_tree`].
pub fn evaluate_tree_with_stats(
    context: &EvaluationContext,
    plan: &PatternPlan,
    tree: &PathTree,
    collection: &CollectionEvidence,
    side_table: Option<&SideConditionTable>,
    options: TreeOptions,
    decider: &dyn RelationDecider,
) -> Result<(Evaluation, TreeStats), PatternFailure> {
    let TreeOptions {
        evaluation: evaluation_options,
        monitor: monitor_options,
    } = options;
    let paths = tree.paths();
    let reference = || {
        evaluate_with(
            context,
            plan,
            paths,
            collection,
            side_table,
            evaluation_options,
            decider,
        )
    };
    let deferred = TreeStats {
        deferred: true,
        ..TreeStats::default()
    };
    // Validation is the reference's own: `evaluate_with` with a probe plan that matches
    // nothing it could report. Under existential-first, the probe has one single-atom arm per
    // constructor on a match-found path, whose occurrences are all indeterminate (its side
    // condition has no table), so the probe's collection check fails only where the real one
    // must: on a match-found path without events.
    let probe = validation_probe(plan, paths, evaluation_options.search_policy);
    let checked = evaluate_with(
        context,
        &probe,
        paths,
        collection,
        None,
        evaluation_options,
        &StructuralDecider,
    )?;
    if evaluation_options.input_error {
        return Ok((checked, TreeStats::default()));
    }
    // A side table's rows are private to the reference.
    if plan.side_condition.is_some() && side_table.is_some() {
        return reference().map(|evaluation| (evaluation, deferred));
    }

    let mut stats = TreeStats::default();
    let mut verdicts: Vec<Option<MonitorVerdict>> = vec![None; paths.len()];
    for group in scope_groups(paths) {
        stats.groups += 1;
        evaluate_group(
            plan,
            tree,
            &group,
            monitor_options,
            decider,
            &mut verdicts,
            &mut stats,
        );
    }

    let mut pending = Vec::new();
    let mut indeterminate = false;
    let mut match_stop_indeterminate = false;
    for (path, verdict) in paths.iter().zip(verdicts) {
        let verdict = verdict.expect("every leaf belongs to one group");
        let order = match &path.path_key {
            Some(key) => PathOrder::Key(key),
            None => PathOrder::Shape(TraceShape::of(path)),
        };
        pending.extend(
            verdict
                .witnesses
                .into_iter()
                .map(|witness| (order.clone(), witness)),
        );
        indeterminate |= verdict.indeterminate;
        match_stop_indeterminate |= verdict.indeterminate && path.stop == PathStop::MatchFound;
    }
    pending.sort_by(|(left_order, left), (right_order, right)| {
        left_order
            .cmp(right_order)
            .then_with(|| left.event_indices.cmp(&right.event_indices))
            .then_with(|| left.bindings.cmp(&right.bindings))
            .then_with(|| left.assumptions.cmp(&right.assumptions))
            .then_with(|| left.arm_ordinal.cmp(&right.arm_ordinal))
    });
    let witnesses = pending
        .into_iter()
        .map(|(_, witness)| witness)
        .collect::<Vec<_>>();
    if evaluation_options.search_policy == SearchPolicy::ExistentialFirst {
        let stopped = paths.iter().any(|path| path.stop == PathStop::MatchFound);
        if witnesses
            .iter()
            .any(|witness| witness.stop_reason != PathStop::MatchFound)
            || (stopped && witnesses.is_empty() && !match_stop_indeterminate)
        {
            // The reference fails here too, with its own error.
            return reference().map(|evaluation| (evaluation, deferred));
        }
    }
    let complete_coverage = collection.stop == CollectionStop::SearchExhausted
        && collection.pending_work == 0
        && paths.iter().all(|path| path.complete)
        && !indeterminate;
    let outcome = if !witnesses.is_empty() {
        PatternOutcome::Match
    } else if indeterminate || !complete_coverage {
        PatternOutcome::Unknown
    } else {
        PatternOutcome::NoMatch
    };
    let failure = if outcome == PatternOutcome::Unknown {
        paths
            .iter()
            .filter(|path| !path.complete && path.stop != PathStop::MatchFound)
            .map(|path| path.stop)
            .min()
            .or_else(|| collection_failure(collection.stop))
            .or(Some(PathStop::SolverUnknown))
    } else {
        None
    };
    Ok((
        Evaluation {
            outcome,
            complete_coverage,
            primary_witness: (evaluation_options.stable_path_keys && !witnesses.is_empty())
                .then_some(0),
            witnesses,
            failure,
            search_policy: evaluation_options.search_policy,
            bounds: context.bounds.clone(),
        },
        stats,
    ))
}

/// The plan `evaluate_with` validates the inputs with: the plan's vocabulary (which only a
/// clone reaches), no variables, a side condition that is `Unknown` without a table, and arms
/// that can only produce indeterminate candidates.
fn validation_probe(plan: &PatternPlan, paths: &[PathInput], policy: SearchPolicy) -> PatternPlan {
    let mut probe = plan.clone();
    probe.variables.clear();
    probe.side_condition = Some(SideCondition {
        name: PROBE_SIDE_CONDITION.to_owned(),
        input_variables: Vec::new(),
    });
    probe.arms = if policy == SearchPolicy::ExistentialFirst {
        paths
            .iter()
            .filter(|path| path.stop == PathStop::MatchFound)
            .flat_map(|path| &path.events)
            .map(|event| event.constructor.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .map(|constructor| PatternArm {
                atoms: vec![Atom {
                    constructor,
                    payload: Vec::new(),
                }],
                relations: Vec::new(),
            })
            .collect()
    } else {
        Vec::new()
    };
    probe
}

/// The leaves grouped by what `relate` may read: equal path predicate, equivalences and
/// inequalities. Each group lists leaf indices in insertion order.
fn scope_groups(paths: &[PathInput]) -> Vec<Vec<usize>> {
    type Scope<'a> = (&'a Pattern, &'a [TermRelation], &'a [TermRelation]);
    let mut groups: BTreeMap<Scope<'_>, Vec<usize>> = BTreeMap::new();
    for (index, path) in paths.iter().enumerate() {
        groups
            .entry((
                &path.path_predicate,
                path.equivalences.as_slice(),
                path.inequalities.as_slice(),
            ))
            .or_default()
            .push(index);
    }
    let mut groups = groups.into_values().collect::<Vec<_>>();
    groups.sort();
    groups
}

/// Runs the monitor over the part of the tree that leads to the leaves of one group, copying
/// the state at every branch point, and records each leaf's verdict.
fn evaluate_group(
    plan: &PatternPlan,
    tree: &PathTree,
    group: &[usize],
    options: MonitorOptions,
    decider: &dyn RelationDecider,
    verdicts: &mut [Option<MonitorVerdict>],
    stats: &mut TreeStats,
) {
    let representative = &tree.paths[group[0]];
    let mut needed = vec![false; tree.nodes.len()];
    let mut in_group = vec![false; tree.paths.len()];
    for leaf in group {
        in_group[*leaf] = true;
        let mut current = Some(tree.leaf_nodes[*leaf]);
        while let Some(node) = current {
            if needed[node] {
                break;
            }
            needed[node] = true;
            current = tree.nodes[node].parent;
        }
    }
    let mut stack = vec![(PathTree::ROOT, Monitor::new(plan, options))];
    while let Some((node, mut monitor)) = stack.pop() {
        stats.node_visits += 1;
        stats.events_pushed += tree.nodes[node].events.len();
        monitor
            .push_step(&tree.nodes[node].events, representative, decider)
            .expect("leaf events are validated and equal their node chain");
        stats.peak_partials = stats.peak_partials.max(monitor.peak_partials());
        stats.overflowed |= monitor.overflowed();
        for leaf in &tree.nodes[node].leaves {
            if in_group[*leaf] {
                verdicts[*leaf] = Some(
                    monitor
                        .finish(&tree.paths[*leaf], decider)
                        .expect("a leaf has exactly its node chain's events"),
                );
            }
        }
        let children = tree.nodes[node]
            .children
            .iter()
            .copied()
            .filter(|child| needed[*child])
            .collect::<Vec<_>>();
        if let Some((last, rest)) = children.split_last() {
            for child in rest.iter().rev() {
                stack.push((*child, monitor.branch()));
            }
            stack.push((*last, monitor));
        }
    }
}

/// `evaluate_with`'s trace shape: everything a path carries except its ordinal and key.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct TraceShape<'a> {
    complete: bool,
    stop: PathStop,
    execution_stop: ExecutionStop,
    execution_terminal: Option<&'a ExecutionTerminal>,
    events: &'a [Event],
    path_predicate: &'a Pattern,
    equivalences: &'a [TermRelation],
    inequalities: &'a [TermRelation],
}

impl<'a> TraceShape<'a> {
    fn of(path: &'a PathInput) -> Self {
        Self {
            complete: path.complete,
            stop: path.stop,
            execution_stop: path.execution_stop,
            execution_terminal: path.execution_terminal.as_ref(),
            events: &path.events,
            path_predicate: &path.path_predicate,
            equivalences: &path.equivalences,
            inequalities: &path.inequalities,
        }
    }
}

/// `evaluate_with`'s witness order across paths.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum PathOrder<'a> {
    Key(&'a str),
    Shape(TraceShape<'a>),
}

/// `evaluate_with`'s cause of `Unknown` for an incomplete collection stop.
const fn collection_failure(stop: CollectionStop) -> Option<PathStop> {
    match stop {
        CollectionStop::SearchExhausted | CollectionStop::MatchFound => None,
        CollectionStop::DepthLimit => Some(PathStop::DepthLimit),
        CollectionStop::TimeLimit => Some(PathStop::TimeLimit),
        CollectionStop::BranchLimit => Some(PathStop::BranchLimit),
        CollectionStop::ResultLimit => Some(PathStop::ResultLimit),
        CollectionStop::ResourceLimit => Some(PathStop::ResourceLimit),
        CollectionStop::SolverUnknown => Some(PathStop::SolverUnknown),
        CollectionStop::BackendLimit | CollectionStop::ExhaustionUnrecorded => {
            Some(PathStop::BackendLimit)
        }
        CollectionStop::Error => Some(PathStop::Error),
    }
}
