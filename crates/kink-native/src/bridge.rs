//! Maps adapted executions to kink-pattern paths and collection evidence.
//!
//! A PathSet run records exhaustion only when every leaf completes without a diagnostic.
//! A bounded frontier, failure halt, cancellation, or diagnostic keeps the result open.
//! Diagnostics affect their own path; a clean sibling remains usable evidence.
//!
//! A path's events are evidence for `Match` only when its prefix is real
//! (`PathStop::has_real_prefix`). A symbolic or constrained state may be infeasible. The leaf
//! predicate carries every condition the path's steps relied on, including the definedness of
//! the partial terms in their conditions, right-hand sides and simplified states, so an instance
//! of a feasible leaf state follows the path. A bounded
//! leaf keeps its limit stop when its state is one ground term without a path condition, or when
//! the adapter showed it feasible ([`LeafFeasibility::Syntactic`], or
//! [`LeafFeasibility::Solver`] with the Z3 profile); otherwise it is `SolverUnknown`.
//!
//! A stuck leaf is complete for a ground term without a path condition. Otherwise it is complete
//! when its state is feasible: its `Stuck` halt says that no instance of its state has a successor.
//!
//! A `Trivial` leaf is an undefined step: under its predicate, a rule applies to every instance of
//! its pre-step state and no instance has a defined successor, because the rule's result
//! (`ensures`, right-hand-side definedness) is `\bottom` there. It is complete on the same terms
//! as a stuck leaf, with stop [`PathStop::UndefinedStep`] and its pre-step term as the terminal
//! term, whose kind is [`ExecutionTerminalKind::UndefinedStep`] and is never asked of `classify`.
//! Its prefix is real: every earlier step is defined on each instance, and a ground run of an
//! instance performs those steps and emits their events, as `stop(1)` in `symbottom.k` does.
//! The undefined step itself commits no transition, so it adds no event; k-rust names its rule on
//! the leaf instead ([`crate::execution::AdaptedLeaf::undefined_rule`]), and the report states it
//! as the path's `undefined_rule`. That reading holds for
//! ground and symbolic leaves alike. It needs strategy `all`, which the adapter always requests:
//! under `any` a step follows one collection candidate per rule, so another candidate may give an
//! instance of the leaf a defined successor (k-rust KK-73 made `any` relative to the whole
//! priority, which leaves only that difference).
//! A `Trivial` leaf's key is its committed transitions followed by `undefined@N`, where `N`
//! counts the earlier `Trivial` leaves after the same transitions, since one step can leave
//! several undefined sub-cases.
//!
//! An `Indeterminate` leaf whose step needed an SMT solver that the build lacks
//! (`SearchFailureOutput::solver_unavailable` of its cause) is `SolverUnknown`; any other
//! indeterminate leaf is `BackendLimit`. Either way the path is incomplete.
//!
//! A leaf proved to have no instance is discarded: no path, no stop, counted by the report. That
//! is a `Vacuous` leaf, or a stuck, trivial or bounded leaf whose predicate the solver refuted
//! ([`LeafFeasibility::Unsat`]). An undecided `Trivial` leaf is `SolverUnknown`, like an
//! undecided stuck leaf. A diagnosed leaf is never discarded.

use k_rust::backend::{EffectOutput, SearchFailureOutput};
use k_rust::kore::{
    ast::{Pattern, Sort},
    codec,
};
use kink_pattern::{
    CollectionEvidence, CollectionStop, EmptySearchDecision, Event, EventAttribution, EventOrigin,
    ExecutionStop, ExecutionTerminal, ExecutionTerminalKind, PathInput, PathStop, SymbolSorts,
};

use crate::execution::{AdaptedExecution, HaltClass};
use crate::feasibility::LeafFeasibility;
use crate::observation::{AdaptedBranch, DomainPayload, NativeEvent};

/// What the bridge needs besides the adapted response.
pub struct BridgeContext<'a> {
    pub test_id: &'a str,
    /// The declaration-owned classifier of a terminal term. The term is ground for a ground
    /// initial state. A complete stuck leaf of a symbolic run may be constrained or symbolic,
    /// and a variable stands for any value of its sort that the path predicate admits; the
    /// classifier must then answer alike for every instance, so it may only read the parts of
    /// the term that no variable can change. It is asked only about stuck terms and must not
    /// answer `UndefinedStep` ([`BridgeFailure::ClassifiedUndefinedStep`]).
    pub classify: &'a dyn Fn(&Pattern) -> ExecutionTerminalKind,
    /// Symbol sorts of the compiled definition, to find the sort of a bare leaf state.
    pub sorts: &'a SymbolSorts,
}

/// Paths in response order and the evidence of how their collection stopped.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BridgedPaths {
    pub paths: Vec<PathInput>,
    pub collection: CollectionEvidence,
}

/// Why a response cannot be read as paths. Nothing is published.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BridgeFailure {
    NoLeaves,
    ContractViolation(HaltClass),
    /// A domain event carries an effect payload, which is not a KORE term.
    UnsupportedPayload,
    UndecodablePayload(String),
    UndecodableState(String),
    UndecidedStateSort,
    /// Two different branches have one identity, so they would share a path key.
    DuplicatePathIdentity(String),
    /// `classify` answered [`ExecutionTerminalKind::UndefinedStep`] for a stuck term. Only a
    /// `Trivial` halt shows an undefined step.
    ClassifiedUndefinedStep,
}

/// How one execution leaf becomes a path.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum LeafPath {
    /// A terminal term that every instance of the path reaches and that is stuck for each.
    Complete(ExecutionTerminal),
    Incomplete(PathStop),
}

/// Why a leaf proved to have no instance adds no path.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum DiscardReason {
    /// k-rust proved the leaf's path condition `\bottom` (`HaltClass::Vacuous`).
    Vacuous,
    /// The solver refuted the leaf's predicate ([`LeafFeasibility::Unsat`]).
    Unsat,
}

impl DiscardReason {
    /// The report name: `"vacuous"` or `"unsat"`.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Vacuous => "vacuous",
            Self::Unsat => "unsat",
        }
    }
}

/// Whether `leaf` is discarded, and why (see the module documentation). A diagnosed leaf is
/// never discarded.
#[must_use]
pub fn discarded(leaf: &crate::execution::AdaptedLeaf) -> Option<DiscardReason> {
    let reason = match (leaf.halt, leaf.feasibility) {
        (HaltClass::Vacuous, _) => DiscardReason::Vacuous,
        (
            HaltClass::Stuck | HaltClass::Trivial | HaltClass::DepthBound | HaltClass::BreadthBound,
            LeafFeasibility::Unsat,
        ) => DiscardReason::Unsat,
        _ => return None,
    };
    (!diagnosed(leaf)).then_some(reason)
}

fn diagnosed(leaf: &crate::execution::AdaptedLeaf) -> bool {
    !leaf.diagnostics.is_empty()
        || leaf
            .candidate_diagnostics
            .iter()
            .any(|diagnostics| !diagnostics.is_empty())
        || !leaf.remainder_diagnostics.is_empty()
}

/// The stop of a leaf with halt class `halt`, before its state is read, or the contract
/// violation it is. `None` is a stuck or trivial leaf: it is complete when its state is a ground
/// term, or when the adapter's evidence completes it (see the module documentation), and
/// `SolverUnknown` otherwise, because a symbolic or constrained leaf may be infeasible.
/// An `Indeterminate` leaf is `BackendLimit` here; [`indeterminate_stop`]
/// refines it by its cause. A requested depth or breadth bound keeps its limit stop only
/// for a decided or feasible state (see `decided_stop`). A vacuous leaf that is not discarded
/// is `SolverUnknown`.
/// The adapter rejects unrequested bound halts. Exhaustive over `HaltClass`.
pub const fn halt_stop(halt: HaltClass) -> Result<Option<PathStop>, BridgeFailure> {
    Ok(Some(match halt {
        HaltClass::Stuck | HaltClass::Trivial => return Ok(None),
        HaltClass::Vacuous => PathStop::SolverUnknown,
        HaltClass::Indeterminate | HaltClass::UnsupportedHook | HaltClass::SimplificationError => {
            PathStop::BackendLimit
        }
        HaltClass::DepthBound => PathStop::DepthLimit,
        HaltClass::BreadthBound => PathStop::BranchLimit,
        // Until upstream tells cancellation from timeout.
        HaltClass::Cancelled => PathStop::Error,
        HaltClass::Branch | HaltClass::CutPoint | HaltClass::TerminalRule | HaltClass::Timeout => {
            return Err(BridgeFailure::ContractViolation(halt));
        }
    }))
}

/// The stop of an `Indeterminate` leaf with `cause`: `SolverUnknown` when the stopped step needed
/// an SMT solver that the build lacks, and `BackendLimit` for any other cause or none.
#[must_use]
pub fn indeterminate_stop(cause: Option<&SearchFailureOutput>) -> PathStop {
    if cause.is_some_and(SearchFailureOutput::solver_unavailable) {
        PathStop::SolverUnknown
    } else {
        PathStop::BackendLimit
    }
}

/// `stop`, or `SolverUnknown` when `stop` vouches for a real prefix but the state is neither
/// decided nor shown feasible: a symbolic or constrained state may be infeasible without a
/// solver.
pub(crate) const fn decided_stop(stop: PathStop, feasible: bool) -> PathStop {
    if stop.has_real_prefix() && !feasible {
        PathStop::SolverUnknown
    } else {
        stop
    }
}

/// The path of a leaf, or the contract violation it is (see [`halt_stop`]). `decided` is the
/// leaf's state when it is decided (see `SplitState::decided_term`); for a stuck or trivial leaf
/// that is its terminal term. `feasible` says the adapter showed the state feasible; it keeps a
/// limit stop real. `complete_term` is the term of a stuck or trivial leaf that is not decided
/// but complete: its state is feasible (see the module documentation). A stuck terminal is
/// classified by `classify`; a trivial one is an undefined step.
pub(crate) fn leaf_path(
    halt: HaltClass,
    decided: Option<Pattern>,
    feasible: bool,
    complete_term: Option<Pattern>,
    classify: &dyn Fn(&Pattern) -> ExecutionTerminalKind,
) -> Result<LeafPath, BridgeFailure> {
    Ok(match (halt_stop(halt)?, decided.or(complete_term)) {
        (Some(stop), decided) => {
            LeafPath::Incomplete(decided_stop(stop, decided.is_some() || feasible))
        }
        (None, Some(term)) => LeafPath::Complete(ExecutionTerminal {
            kind: if halt == HaltClass::Trivial {
                ExecutionTerminalKind::UndefinedStep
            } else {
                match classify(&term) {
                    ExecutionTerminalKind::UndefinedStep => {
                        return Err(BridgeFailure::ClassifiedUndefinedStep);
                    }
                    kind => kind,
                }
            },
            state: term,
        }),
        (None, None) => LeafPath::Incomplete(PathStop::SolverUnknown),
    })
}

/// A decoded leaf state split at its sort into term and predicate conjuncts.
struct SplitState {
    sort: Sort,
    terms: Vec<Pattern>,
    predicates: Vec<Pattern>,
}

fn split_state(
    value: &serde_json::Value,
    sorts: &SymbolSorts,
) -> Result<SplitState, BridgeFailure> {
    let state = codec::from_value(value)
        .map_err(|error| BridgeFailure::UndecodableState(error.to_string()))?;
    let sort = sorts
        .sort_of(&state)
        .ok_or(BridgeFailure::UndecidedStateSort)?;
    let (terms, predicates) = partition_conjuncts(state.into_conjuncts_at(&sort));
    Ok(SplitState {
        sort,
        terms,
        predicates,
    })
}

/// Separates term conjuncts from path predicates using the bridge's state classification.
pub(crate) fn partition_conjuncts(conjuncts: Vec<Pattern>) -> (Vec<Pattern>, Vec<Pattern>) {
    conjuncts.into_iter().partition(|conjunct| {
        matches!(
            conjunct,
            Pattern::Application { .. }
                | Pattern::AssociativeApplication { .. }
                | Pattern::DomainValue { .. }
                | Pattern::String(_)
                | Pattern::Variable(_)
        )
    })
}

impl SplitState {
    /// The decided state: exactly one term conjunct, no predicate, and no free variable.
    /// Anything else is neither complete terminal evidence nor a real prefix.
    fn decided_term(&self) -> Option<Pattern> {
        match (self.terms.as_slice(), self.predicates.is_empty()) {
            ([term], true) if term.free_variables().is_empty() => Some(term.clone()),
            _ => None,
        }
    }

    fn path_predicate(&self) -> Pattern {
        match self.predicates.as_slice() {
            [] => Pattern::Top {
                sort: self.sort.clone(),
            },
            [predicate] => predicate.clone(),
            predicates => Pattern::And {
                sort: self.sort.clone(),
                arguments: predicates.to_vec(),
            },
        }
    }
}

/// `rule@target` of each transition joined by `/`, or `root` for the initial state.
fn branch_key(branch: &AdaptedBranch) -> String {
    if branch.identity.is_empty() {
        "root".to_owned()
    } else {
        branch
            .identity
            .iter()
            .map(|id| format!("{}@{}", id.rule, id.target))
            .collect::<Vec<_>>()
            .join("/")
    }
}

/// The path key of each leaf, in leaf order: its branch key, and for a `Trivial` leaf also
/// `undefined@N`, where `N` counts the earlier `Trivial` leaves with the same branch key. A
/// trivial leaf commits no transition, so it shares its branch with its step's other undefined
/// sub-cases.
#[must_use]
pub fn leaf_keys(leaves: &[crate::execution::AdaptedLeaf]) -> Vec<String> {
    let mut seen = std::collections::BTreeMap::<String, usize>::new();
    leaves
        .iter()
        .map(|leaf| {
            let key = branch_key(&leaf.branch);
            if leaf.halt != HaltClass::Trivial {
                return key;
            }
            let ordinal = seen.entry(key.clone()).or_default();
            let undefined = format!("undefined@{ordinal}");
            *ordinal += 1;
            if leaf.branch.identity.is_empty() {
                undefined
            } else {
                format!("{key}/{undefined}")
            }
        })
        .collect()
}

fn events(branch: &AdaptedBranch) -> Result<Vec<Event>, BridgeFailure> {
    branch
        .events
        .iter()
        .map(|event| {
            let (
                index,
                transition_ordinal,
                emission_ordinal,
                constructor,
                transition,
                rule,
                payload,
                attribution,
            ) = match event {
                NativeEvent::RuleApplied(event) => (
                    event.event_ordinal,
                    event.transition_ordinal,
                    event.emission_ordinal,
                    event.label.as_ref().map_or_else(
                        || format!("rule:{}:{}", event.rule.module, event.rule.index),
                        |label| format!("rule:{label}"),
                    ),
                    &event.transition,
                    &event.rule,
                    Vec::new(),
                    EventAttribution::Certain,
                ),
                NativeEvent::Domain(event) => (
                    event.event_ordinal,
                    event.transition_ordinal,
                    event.emission_ordinal,
                    event.constructor.clone(),
                    &event.transition,
                    &event.rule,
                    event
                        .payload
                        .iter()
                        .map(|payload| match payload {
                            DomainPayload::Term(value) => {
                                codec::from_value(value).map_err(|error| {
                                    BridgeFailure::UndecodablePayload(error.to_string())
                                })
                            }
                            DomainPayload::Effect(EffectOutput::UserLog { .. }) => {
                                Err(BridgeFailure::UnsupportedPayload)
                            }
                        })
                        .collect::<Result<Vec<_>, _>>()?,
                    EventAttribution::Certain,
                ),
                NativeEvent::UnknownAttribution(event) => (
                    event.event_ordinal,
                    event.transition_ordinal,
                    event.emission_ordinal,
                    event.constructor.clone(),
                    &event.transition,
                    &event.rule,
                    Vec::new(),
                    EventAttribution::Unknown(event.reason.clone()),
                ),
            };
            Ok(Event {
                index,
                constructor,
                payload,
                attribution,
                origin: EventOrigin {
                    rule: (*rule).clone(),
                    transition: transition.clone(),
                },
                transition_ordinal: widen(transition_ordinal),
                emission_ordinal: widen(emission_ordinal),
            })
        })
        .collect()
}

fn widen(value: usize) -> u64 {
    u64::try_from(value).expect("an ordinal fits in u64")
}

const fn execution_stop(stop: PathStop) -> ExecutionStop {
    match stop {
        PathStop::Terminal => ExecutionStop::Terminal,
        PathStop::Stuck => ExecutionStop::Stuck,
        PathStop::UndefinedStep => ExecutionStop::UndefinedStep,
        PathStop::MatchFound => ExecutionStop::QuerySatisfied,
        PathStop::DepthLimit => ExecutionStop::DepthLimit,
        PathStop::TimeLimit => ExecutionStop::TimeLimit,
        PathStop::BranchLimit => ExecutionStop::BranchLimit,
        PathStop::ResultLimit => ExecutionStop::ResultLimit,
        PathStop::ResourceLimit => ExecutionStop::ResourceLimit,
        PathStop::SolverUnknown => ExecutionStop::SolverUnknown,
        PathStop::BackendLimit => ExecutionStop::BackendLimit,
        PathStop::Error => ExecutionStop::Error,
    }
}

const fn collection_stop(stop: PathStop) -> CollectionStop {
    match stop {
        PathStop::DepthLimit => CollectionStop::DepthLimit,
        PathStop::TimeLimit => CollectionStop::TimeLimit,
        PathStop::BranchLimit => CollectionStop::BranchLimit,
        PathStop::ResultLimit => CollectionStop::ResultLimit,
        PathStop::ResourceLimit => CollectionStop::ResourceLimit,
        PathStop::SolverUnknown => CollectionStop::SolverUnknown,
        PathStop::BackendLimit => CollectionStop::BackendLimit,
        PathStop::Error => CollectionStop::Error,
        // Complete and query-level stops never reach here.
        PathStop::Terminal | PathStop::Stuck | PathStop::UndefinedStep | PathStop::MatchFound => {
            CollectionStop::Error
        }
    }
}

/// Paths under construction, keyed by branch identity. An exact repeat of a branch with the
/// same stop is one path; two different branches with one key are a failure.
struct PathSet<'a> {
    context: &'a BridgeContext<'a>,
    entries: Vec<(String, AdaptedBranch, PathInput)>,
    /// Incomplete stops of every item, including items that add no path.
    incomplete: Vec<PathStop>,
}

impl<'a> PathSet<'a> {
    const fn new(context: &'a BridgeContext<'a>) -> Self {
        Self {
            context,
            entries: Vec::new(),
            incomplete: Vec::new(),
        }
    }

    fn push(
        &mut self,
        leaf: &crate::execution::AdaptedLeaf,
        key: String,
    ) -> Result<(), BridgeFailure> {
        let branch = &leaf.branch;
        let halt = leaf.halt;
        // Check the contract before anything is dropped.
        halt_stop(halt)?;
        if discarded(leaf).is_some() {
            return Ok(());
        }
        let split = split_state(&branch.state, self.context.sorts)?;
        // The adapter checked the internalized state. A syntactic claim needs the split to
        // agree that no path condition is left, so such a cut path always has predicate
        // `\top`; a solver claim is about the predicate conjuncts it found.
        let feasible = match leaf.feasibility {
            LeafFeasibility::Syntactic => split.predicates.is_empty(),
            LeafFeasibility::Solver => true,
            LeafFeasibility::Unsat | LeafFeasibility::Unknown => false,
        };
        let complete_term = match split.terms.as_slice() {
            [term] if feasible => Some(term.clone()),
            _ => None,
        };
        let mapped = match leaf_path(
            halt,
            split.decided_term(),
            feasible,
            complete_term,
            self.context.classify,
        )? {
            _ if diagnosed(leaf) => LeafPath::Incomplete(PathStop::BackendLimit),
            LeafPath::Incomplete(_) if halt == HaltClass::Indeterminate => {
                LeafPath::Incomplete(indeterminate_stop(leaf.cause.as_ref()))
            }
            mapped => mapped,
        };
        let (complete, stop, execution_terminal) = match mapped {
            LeafPath::Complete(terminal) => {
                let stop = match terminal.kind {
                    ExecutionTerminalKind::Normal | ExecutionTerminalKind::SemanticCrash => {
                        PathStop::Terminal
                    }
                    ExecutionTerminalKind::Stuck => PathStop::Stuck,
                    ExecutionTerminalKind::UndefinedStep => PathStop::UndefinedStep,
                };
                (true, stop, Some(terminal))
            }
            LeafPath::Incomplete(stop) => {
                self.incomplete.push(stop);
                (false, stop, None)
            }
        };
        self.insert(
            key,
            branch,
            complete,
            stop,
            execution_terminal,
            split.path_predicate(),
        )
    }

    fn insert(
        &mut self,
        key: String,
        branch: &AdaptedBranch,
        complete: bool,
        stop: PathStop,
        execution_terminal: Option<ExecutionTerminal>,
        path_predicate: Pattern,
    ) -> Result<(), BridgeFailure> {
        if let Some((_, existing, path)) = self.entries.iter().find(|(other, ..)| *other == key) {
            return if existing == branch && path.stop == stop {
                Ok(())
            } else {
                Err(BridgeFailure::DuplicatePathIdentity(key))
            };
        }
        let path = PathInput {
            test_id: self.context.test_id.to_owned(),
            path_ordinal: self.entries.len(),
            path_key: Some(key.clone()),
            complete,
            stop,
            execution_stop: execution_stop(stop),
            execution_terminal,
            events: events(branch)?,
            path_predicate,
            equivalences: Vec::new(),
            inequalities: Vec::new(),
        };
        self.entries.push((key, branch.clone(), path));
        Ok(())
    }

    /// The most constraining incomplete stop, or exhaustion when all leaves complete. When
    /// every leaf was discarded, exhaustion is an empty search: no instance has a path.
    fn finish(self) -> BridgedPaths {
        let stop = self
            .incomplete
            .iter()
            .min()
            .map_or(CollectionStop::SearchExhausted, |stop| {
                collection_stop(*stop)
            });
        let empty = self.entries.is_empty() && stop == CollectionStop::SearchExhausted;
        BridgedPaths {
            paths: self.entries.into_iter().map(|(.., path)| path).collect(),
            collection: CollectionEvidence {
                stop,
                pending_work: u64::from(stop != CollectionStop::SearchExhausted),
                empty_search_decision: empty.then_some(EmptySearchDecision),
            },
        }
    }
}

/// Reads an adapted execution as paths; see the module documentation.
pub fn paths_from_execution(
    execution: &AdaptedExecution,
    context: &BridgeContext<'_>,
) -> Result<BridgedPaths, BridgeFailure> {
    if execution.timed_out {
        return Ok(BridgedPaths {
            paths: Vec::new(),
            collection: CollectionEvidence {
                stop: CollectionStop::TimeLimit,
                pending_work: 1,
                empty_search_decision: None,
            },
        });
    }
    if execution.leaves.is_empty() {
        return Err(BridgeFailure::NoLeaves);
    }
    let mut paths = PathSet::new(context);
    for (leaf, key) in execution.leaves.iter().zip(leaf_keys(&execution.leaves)) {
        paths.push(leaf, key)?;
    }
    Ok(paths.finish())
}

#[cfg(test)]
mod tests {
    use super::*;
    use k_rust::backend::TransitionIdOutput;
    use k_rust::kore::{json as kore_json, parser::parse_pattern};
    use kink_pattern::{
        Atom, Constructor, EvaluationContext, EvaluationOptions, EventVocabulary, ExecutionBounds,
        PatternArm, PatternOutcome, PatternPlan, SearchPolicy, evaluate,
    };
    use serde_json::Value;

    use crate::execution::{AdaptedLeaf, ExecutionBudget};
    use crate::observation::DomainEvent;

    use HaltClass as H;
    use LeafFeasibility::{Syntactic as F, Unknown as U};
    use PathStop as P;

    const GROUND: &str = r"Lbla{}()";
    const CRASH: &str = r"Lblcrash{}()";
    const SYMBOLIC: &str = r"X:SortS{}";
    const CONSTRAINED: &str =
        r#"\and{SortS{}}(Lbla{}(), \equals{SortInt{}, SortS{}}(Y:SortInt{}, \dv{SortInt{}}("1")))"#;
    /// The state k-rust reports for a leaf whose path condition became false.
    const BOTTOM: &str = r"\and{SortS{}}(Lbla{}(), \bottom{SortS{}}())";
    /// The state k-rust reports for an initial state whose constraints are false.
    const BARE_BOTTOM: &str = r"\bottom{SortS{}}()";
    const SYMBOLIC_CONSTRAINED: &str = r#"\and{SortS{}}(X:SortS{}, \equals{SortInt{}, SortS{}}(Y:SortInt{}, \dv{SortInt{}}("1")))"#;

    fn kore(source: &str) -> Value {
        kore_json::to_value(&parse_pattern(source).expect("test KORE")).expect("KORE JSON")
    }

    fn sorts() -> SymbolSorts {
        let s = || Sort::Application {
            name: "SortS".to_owned(),
            arguments: Vec::new(),
        };
        SymbolSorts::new([
            ("Lbla".to_owned(), Vec::new(), s()),
            ("Lblcrash".to_owned(), Vec::new(), s()),
        ])
    }

    fn classify(term: &Pattern) -> ExecutionTerminalKind {
        if *term == parse_pattern(CRASH).expect("crash term") {
            ExecutionTerminalKind::SemanticCrash
        } else {
            ExecutionTerminalKind::Normal
        }
    }

    /// A branch of one transition that emitted one `fired` event.
    fn branch(marker: usize, state: &str) -> AdaptedBranch {
        let transition = TransitionIdOutput {
            rule: format!("rule-{marker}"),
            target: format!("target-{marker}"),
        };
        AdaptedBranch {
            identity: vec![transition.clone()],
            state: kore(state),
            depth: 1,
            trace: Vec::new(),
            events: vec![NativeEvent::Domain(DomainEvent {
                event_ordinal: 0,
                transition_ordinal: 0,
                emission_ordinal: 0,
                constructor: "fired".to_owned(),
                transition,
                rule: kink_patch::SentenceRef::new("M", 0),
                payload: Vec::new(),
            })],
            rollbacks: Vec::new(),
        }
    }

    /// Evaluates a plan whose only event never occurs: the outcome is `NoMatch` exactly
    /// when the bridged evidence is complete.
    fn absence(bridged: &BridgedPaths) -> PatternOutcome {
        occurrence(bridged, "never")
    }

    /// Evaluates a plan whose only event is the `fired` event of every [`branch`]: the
    /// outcome is `Match` exactly when a path carrying it has a real prefix.
    fn presence(bridged: &BridgedPaths) -> PatternOutcome {
        occurrence(bridged, "fired")
    }

    fn occurrence(bridged: &BridgedPaths, constructor: &str) -> PatternOutcome {
        let vocabulary = EventVocabulary::new(
            ["never", "fired"]
                .into_iter()
                .map(|name| Constructor {
                    name: name.to_owned(),
                    payload_sorts: Vec::new(),
                })
                .collect(),
        )
        .expect("vocabulary");
        let plan = PatternPlan::new(
            &vocabulary,
            Vec::new(),
            vec![PatternArm {
                atoms: vec![Atom {
                    constructor: constructor.to_owned(),
                    payload: Vec::new(),
                }],
                relations: Vec::new(),
            }],
            None,
        )
        .expect("plan");
        let context = EvaluationContext {
            test_id: "t".to_owned(),
            bounds: ExecutionBounds {
                depth: None,
                time_ms: Some(1000),
                branches: None,
                results: None,
            },
            vocabulary,
            selected_rules: [kink_patch::SentenceRef::new("M", 0)].into_iter().collect(),
            symbol_sorts: sorts(),
        };
        evaluate(
            &context,
            &plan,
            &bridged.paths,
            &bridged.collection,
            None,
            EvaluationOptions {
                stable_path_keys: true,
                search_policy: SearchPolicy::Exhaustive,
                input_error: false,
            },
        )
        .expect("bridged paths evaluate")
        .outcome
    }

    fn bridge_context<'a>(sorts: &'a SymbolSorts) -> BridgeContext<'a> {
        BridgeContext {
            test_id: "t",
            classify: &classify,
            sorts,
        }
    }

    /// One adapted leaf over [`branch`] `0`, with the adapter's evidence.
    fn leaf(halt: HaltClass, state: &str, feasibility: LeafFeasibility, depth: u64) -> AdaptedLeaf {
        let mut branch = branch(0, state);
        branch.depth = depth;
        AdaptedLeaf {
            halt,
            feasibility,
            cause: None,
            branch,
            diagnostics: Vec::new(),
            candidate_diagnostics: Vec::new(),
            remainder_diagnostics: Vec::new(),
            undefined_rule: None,
        }
    }

    /// What one leaf becomes.
    #[derive(Clone, Copy, Debug)]
    enum Expected {
        /// The adapter's contract excludes the halt.
        Violation,
        /// A complete path with this terminal kind and terminal term.
        Complete(ExecutionTerminalKind, &'static str),
        Incomplete(PathStop),
        /// No path: the leaf is proved to have no instance.
        Discarded(DiscardReason),
    }

    /// One row: halt, leaf state, adapter feasibility, depth, expected path.
    type Row = (HaltClass, &'static str, LeafFeasibility, u64, Expected);

    /// The leaf mapping in both profiles. A decided or feasible `Trivial` leaf is a complete
    /// undefined step whose prefix witnesses a match; an undecided one is `SolverUnknown`; a
    /// refuted leaf adds no path.
    #[test]
    fn execution_leaf_rows_map_to_paths() {
        use ExecutionTerminalKind::{Normal, SemanticCrash, UndefinedStep};
        use Expected::{Complete, Discarded, Incomplete, Violation};
        use LeafFeasibility::{Solver as Z, Unsat as N};
        #[rustfmt::skip]
        let rows: [Row; 46] = [
            // Halts without solver facts.
            (H::Stuck, GROUND, U, 1, Complete(Normal, GROUND)),
            (H::Stuck, CRASH, U, 1, Complete(SemanticCrash, CRASH)),
            (H::Stuck, SYMBOLIC, U, 1, Incomplete(P::SolverUnknown)),
            (H::Stuck, CONSTRAINED, U, 1, Incomplete(P::SolverUnknown)),
            // An undefined step completes like a stuck leaf; `classify` is not asked.
            (H::Trivial, GROUND, U, 1, Complete(UndefinedStep, GROUND)),
            (H::Trivial, CRASH, U, 1, Complete(UndefinedStep, CRASH)),
            (H::Trivial, SYMBOLIC, F, 1, Complete(UndefinedStep, SYMBOLIC)),
            (H::Vacuous, GROUND, U, 1, Discarded(DiscardReason::Vacuous)),
            (H::Branch, GROUND, U, 1, Violation),
            (H::CutPoint, GROUND, U, 1, Violation),
            (H::TerminalRule, GROUND, U, 1, Violation),
            (H::DepthBound, GROUND, U, 1, Incomplete(P::DepthLimit)),
            (H::DepthBound, SYMBOLIC, U, 1, Incomplete(P::SolverUnknown)),
            (H::DepthBound, SYMBOLIC, F, 1, Incomplete(P::DepthLimit)),
            (H::DepthBound, CONSTRAINED, U, 1, Incomplete(P::SolverUnknown)),
            // A syntactic claim over a state that still splits off a path condition is ignored.
            (H::DepthBound, CONSTRAINED, F, 1, Incomplete(P::SolverUnknown)),
            (H::BreadthBound, GROUND, U, 1, Incomplete(P::BranchLimit)),
            (H::BreadthBound, SYMBOLIC, U, 1, Incomplete(P::SolverUnknown)),
            (H::BreadthBound, SYMBOLIC, F, 1, Incomplete(P::BranchLimit)),
            (H::Indeterminate, GROUND, U, 1, Incomplete(P::BackendLimit)),
            (H::Indeterminate, SYMBOLIC, F, 1, Incomplete(P::BackendLimit)),
            (H::UnsupportedHook, GROUND, U, 1, Incomplete(P::BackendLimit)),
            (H::SimplificationError, GROUND, U, 1, Incomplete(P::BackendLimit)),
            (H::Timeout, GROUND, U, 1, Violation),
            (H::Timeout, CONSTRAINED, U, 1, Violation),
            (H::Cancelled, GROUND, U, 1, Incomplete(P::Error)),
            (H::Vacuous, BOTTOM, U, 1, Discarded(DiscardReason::Vacuous)),
            // A `Stuck` halt holds for every instance of its state, in both profiles. A
            // constrained or symbolic stuck leaf completes when its state was shown feasible
            // (syntactically, or by an exact solver `Sat`). The symbolic syntactic row was
            // `SolverUnknown` before k-rust
            // offered every rule to a non-rigid top (KK-54) and stated the stuck contract (KK-55).
            (H::Stuck, CONSTRAINED, Z, 1, Complete(Normal, GROUND)),
            (H::Stuck, SYMBOLIC, F, 1, Complete(Normal, SYMBOLIC)),
            (H::Stuck, SYMBOLIC_CONSTRAINED, Z, 1, Complete(Normal, SYMBOLIC)),
            // A solver-feasible cut keeps its limit and real prefix; coverage is not needed.
            (H::DepthBound, CONSTRAINED, Z, 1, Incomplete(P::DepthLimit)),
            (H::BreadthBound, SYMBOLIC_CONSTRAINED, Z, 1, Incomplete(P::BranchLimit)),
            // A refuted predicate discards a stuck, trivial or cut leaf.
            (H::Stuck, CONSTRAINED, N, 1, Discarded(DiscardReason::Unsat)),
            (H::Stuck, CONSTRAINED, N, 0, Discarded(DiscardReason::Unsat)),
            (H::DepthBound, CONSTRAINED, N, 1, Discarded(DiscardReason::Unsat)),
            (H::BreadthBound, CONSTRAINED, N, 1, Discarded(DiscardReason::Unsat)),
            // Backend-limited leaves are kept; refuted trivial leaves are discarded.
            (H::Indeterminate, CONSTRAINED, N, 1, Incomplete(P::BackendLimit)),
            (H::Trivial, CONSTRAINED, N, 0, Discarded(DiscardReason::Unsat)),
            (H::Trivial, CONSTRAINED, U, 1, Incomplete(P::SolverUnknown)),
            (H::Trivial, CONSTRAINED, Z, 1, Complete(UndefinedStep, GROUND)),
            (H::Trivial, GROUND, F, 1, Complete(UndefinedStep, GROUND)),
            // A vacuous leaf is discarded at any depth.
            (H::Vacuous, BOTTOM, U, 0, Discarded(DiscardReason::Vacuous)),
            (H::Vacuous, BARE_BOTTOM, U, 0, Discarded(DiscardReason::Vacuous)),
            (H::Vacuous, BARE_BOTTOM, U, 1, Discarded(DiscardReason::Vacuous)),
            // The contract is checked before anything is discarded.
            (H::Timeout, CONSTRAINED, N, 0, Violation),
            (H::Branch, BOTTOM, U, 0, Violation),
        ];
        let covered = rows
            .iter()
            .map(|(halt, ..)| *halt)
            .collect::<std::collections::BTreeSet<_>>();
        assert_eq!(covered.into_iter().collect::<Vec<_>>(), HaltClass::ALL);
        let sorts = sorts();
        for (halt, state, feasibility, depth, expected) in rows {
            let id = format!("{halt:?} {state} {feasibility:?} depth={depth}");
            let execution = AdaptedExecution {
                leaves: vec![leaf(halt, state, feasibility, depth)],
                effects: Vec::new(),
                timed_out: false,
            };
            assert_eq!(
                discarded(&execution.leaves[0]),
                match expected {
                    Discarded(reason) => Some(reason),
                    _ => None,
                },
                "{id}"
            );
            let bridged = paths_from_execution(&execution, &bridge_context(&sorts));
            if let Violation = expected {
                assert_eq!(bridged, Err(BridgeFailure::ContractViolation(halt)), "{id}");
                continue;
            }
            let bridged = bridged.unwrap_or_else(|failure| panic!("{id}: {failure:?}"));
            if let Discarded(_) = expected {
                assert!(bridged.paths.is_empty(), "{id}");
                assert_eq!(
                    bridged.collection,
                    CollectionEvidence {
                        stop: CollectionStop::SearchExhausted,
                        pending_work: 0,
                        empty_search_decision: Some(EmptySearchDecision),
                    },
                    "{id}"
                );
                assert_eq!(absence(&bridged), PatternOutcome::NoMatch, "{id}");
                assert_eq!(presence(&bridged), PatternOutcome::NoMatch, "{id}");
                continue;
            }
            let [path] = bridged.paths.as_slice() else {
                panic!("{id}: one path");
            };
            let key = if halt == H::Trivial {
                "rule-0@target-0/undefined@0"
            } else {
                "rule-0@target-0"
            };
            assert_eq!(path.path_key.as_deref(), Some(key), "{id}");
            assert_eq!(bridged.collection.empty_search_decision, None, "{id}");
            match expected {
                Complete(kind, term) => {
                    assert!(path.complete, "{id}");
                    let stop = if kind == UndefinedStep {
                        P::UndefinedStep
                    } else {
                        P::Terminal
                    };
                    assert_eq!(path.stop, stop, "{id}");
                    let terminal = path.execution_terminal.as_ref().expect("terminal");
                    assert_eq!(terminal.kind, kind, "{id}");
                    assert_eq!(terminal.state, parse_pattern(term).expect("term"), "{id}");
                    assert_eq!(
                        bridged.collection.stop,
                        CollectionStop::SearchExhausted,
                        "{id}"
                    );
                    assert_eq!(absence(&bridged), PatternOutcome::NoMatch, "{id}");
                    assert_eq!(presence(&bridged), PatternOutcome::Match, "{id}");
                }
                Incomplete(stop) => {
                    assert!(!path.complete, "{id}");
                    assert_eq!(path.stop, stop, "{id}");
                    assert_eq!(bridged.collection.stop, collection_stop(stop), "{id}");
                    assert_ne!(absence(&bridged), PatternOutcome::NoMatch, "{id}");
                    let real = matches!(stop, P::DepthLimit | P::BranchLimit | P::TimeLimit);
                    assert_eq!(
                        presence(&bridged),
                        if real {
                            PatternOutcome::Match
                        } else {
                            PatternOutcome::Unknown
                        },
                        "{id}"
                    );
                }
                Violation | Discarded(_) => unreachable!(),
            }
        }
        // The path predicate keeps the constrained leaf's condition.
        let split = split_state(&kore(CONSTRAINED), &sorts).expect("split");
        assert_eq!(split.decided_term(), None);
        assert!(matches!(split.path_predicate(), Pattern::Equals { .. }));
    }

    /// A diagnosed leaf is never discarded, whatever the adapter proved about it.
    #[test]
    fn diagnosed_infeasible_leaf_is_a_backend_limit() {
        use k_rust::backend::BackendDiagnosticOutput;
        let sorts = sorts();
        for (halt, feasibility, depth) in [
            (H::Vacuous, U, 0),
            (H::Stuck, LeafFeasibility::Unsat, 0),
            (H::DepthBound, LeafFeasibility::Unsat, 1),
        ] {
            let mut diagnosed = leaf(halt, CONSTRAINED, feasibility, depth);
            diagnosed
                .diagnostics
                .push(BackendDiagnosticOutput::UnsupportedHookUnevaluated {
                    hook: "TEST.hook".into(),
                    reason: "unavailable".into(),
                });
            let execution = AdaptedExecution {
                leaves: vec![diagnosed],
                effects: Vec::new(),
                timed_out: false,
            };
            assert_eq!(discarded(&execution.leaves[0]), None);
            let bridged = paths_from_execution(&execution, &bridge_context(&sorts)).unwrap();
            assert_eq!(bridged.paths.len(), 1, "{halt:?}");
            assert_eq!(bridged.paths[0].stop, P::BackendLimit, "{halt:?}");
        }
    }

    /// An indeterminate leaf is `SolverUnknown` exactly when its step needed a solver the build
    /// lacks, and `BackendLimit` otherwise; a diagnostic still makes it `BackendLimit`.
    #[test]
    fn indeterminate_leaves_map_by_their_cause() {
        use k_rust::backend::{BackendDiagnosticOutput, SmtFailureOutput};
        let sorts = sorts();
        let requires = SearchFailureOutput::Requires {
            rule: "r".to_owned(),
            predicates: Vec::new(),
        };
        let narrowing = SearchFailureOutput::Smt {
            rule: Some("r".to_owned()),
            error: SmtFailureOutput::Unavailable,
        };
        let matching = SearchFailureOutput::Match {
            rule: "r".to_owned(),
            bindings: Vec::new(),
            remainder: Vec::new(),
        };
        for (cause, diagnosed, expected) in [
            (Some(requires.clone()), false, P::SolverUnknown),
            (Some(narrowing), false, P::SolverUnknown),
            (Some(matching), false, P::BackendLimit),
            (None, false, P::BackendLimit),
            (Some(requires), true, P::BackendLimit),
        ] {
            let mut indeterminate = leaf(H::Indeterminate, SYMBOLIC, F, 1);
            indeterminate.cause = cause.clone();
            if diagnosed {
                indeterminate.diagnostics.push(
                    BackendDiagnosticOutput::UnsupportedHookUnevaluated {
                        hook: "TEST.hook".into(),
                        reason: "unavailable".into(),
                    },
                );
            }
            let execution = AdaptedExecution {
                leaves: vec![indeterminate],
                effects: Vec::new(),
                timed_out: false,
            };
            let bridged = paths_from_execution(&execution, &bridge_context(&sorts)).unwrap();
            assert_eq!(bridged.paths[0].stop, expected, "{cause:?} {diagnosed}");
            assert!(!bridged.paths[0].complete);
            assert_eq!(presence(&bridged), PatternOutcome::Unknown);
            assert_eq!(absence(&bridged), PatternOutcome::Unknown);
        }
    }

    /// A discarded leaf leaves its siblings as they are: a complete sibling alone gives clean
    /// exhaustion without an empty-search decision.
    #[test]
    fn discarded_leaf_keeps_its_siblings() {
        let sorts = sorts();
        let mut vacuous = leaf(H::Vacuous, BOTTOM, U, 2);
        vacuous.branch = branch(1, BOTTOM);
        vacuous.branch.depth = 2;
        let execution = AdaptedExecution {
            leaves: vec![leaf(H::Stuck, GROUND, U, 1), vacuous],
            effects: Vec::new(),
            timed_out: false,
        };
        let bridged = paths_from_execution(&execution, &bridge_context(&sorts)).unwrap();
        assert_eq!(bridged.paths.len(), 1);
        assert!(bridged.paths[0].complete);
        assert_eq!(
            bridged.collection,
            CollectionEvidence {
                stop: CollectionStop::SearchExhausted,
                pending_work: 0,
                empty_search_decision: None,
            }
        );
        assert_eq!(absence(&bridged), PatternOutcome::NoMatch);
        assert_eq!(presence(&bridged), PatternOutcome::Match);
    }

    #[test]
    fn halt_stop_rejects_exactly_the_classes_the_adapter_excludes() {
        let unbounded = ExecutionBudget {
            time: std::time::Duration::from_secs(1),
            max_simplification_iterations: 1,
            max_depth: None,
            max_breadth: None,
        };
        let bounded = ExecutionBudget {
            max_depth: Some(1),
            max_breadth: Some(std::num::NonZeroUsize::new(1).unwrap()),
            ..unbounded
        };
        let excluded = |budget: &ExecutionBudget| {
            HaltClass::ALL
                .into_iter()
                .filter(|halt| !halt.adapter_admits(budget))
                .collect::<std::collections::BTreeSet<_>>()
        };
        let always_excluded = [H::Branch, H::CutPoint, H::TerminalRule, H::Timeout]
            .into_iter()
            .collect::<std::collections::BTreeSet<_>>();
        assert_eq!(
            excluded(&unbounded),
            [
                H::Branch,
                H::CutPoint,
                H::TerminalRule,
                H::DepthBound,
                H::BreadthBound,
                H::Timeout,
            ]
            .into_iter()
            .collect()
        );
        assert_eq!(excluded(&bounded), always_excluded);
        assert_eq!(
            HaltClass::ALL
                .into_iter()
                .filter(|halt| halt_stop(*halt).is_err())
                .collect::<std::collections::BTreeSet<_>>(),
            always_excluded
        );
    }

    #[test]
    fn clean_sibling_survives_diagnosed_path() {
        use k_rust::backend::BackendDiagnosticOutput;
        let sorts = sorts();
        let clean = AdaptedLeaf {
            halt: H::Stuck,
            feasibility: U,
            cause: None,
            branch: branch(0, GROUND),
            diagnostics: Vec::new(),
            candidate_diagnostics: Vec::new(),
            remainder_diagnostics: Vec::new(),
            undefined_rule: None,
        };
        let diagnostic = BackendDiagnosticOutput::UnsupportedHookUnevaluated {
            hook: "TEST.hook".into(),
            reason: "unavailable".into(),
        };
        for source in 0..3 {
            let mut diagnosed = clean.clone();
            diagnosed.branch = branch(1, GROUND);
            match source {
                0 => diagnosed.diagnostics.push(diagnostic.clone()),
                1 => diagnosed
                    .candidate_diagnostics
                    .push(vec![diagnostic.clone()]),
                2 => diagnosed.remainder_diagnostics.push(diagnostic.clone()),
                _ => unreachable!(),
            }
            let execution = AdaptedExecution {
                leaves: vec![clean.clone(), diagnosed],
                effects: Vec::new(),
                timed_out: false,
            };
            let bridged = paths_from_execution(&execution, &bridge_context(&sorts)).unwrap();
            assert_eq!(bridged.collection.stop, CollectionStop::BackendLimit);
            assert!(bridged.paths[0].complete);
            assert_eq!(bridged.paths[1].stop, P::BackendLimit);
            assert_eq!(presence(&bridged), PatternOutcome::Match);
            assert_eq!(absence(&bridged), PatternOutcome::Unknown);
        }
    }

    /// A trivial leaf commits no transition, so the undefined sub-cases of one step share their
    /// branch. Each gets its own `undefined@N` key and path; the step's other leaves keep theirs.
    #[test]
    fn undefined_sub_cases_of_one_step_are_distinct_paths() {
        let sorts = sorts();
        let trivial = |state| leaf(H::Trivial, state, F, 1);
        let execution = AdaptedExecution {
            leaves: vec![
                trivial(GROUND),
                trivial(CRASH),
                leaf(H::Stuck, GROUND, U, 1),
            ],
            effects: Vec::new(),
            timed_out: false,
        };
        assert_eq!(
            leaf_keys(&execution.leaves),
            [
                "rule-0@target-0/undefined@0",
                "rule-0@target-0/undefined@1",
                "rule-0@target-0",
            ]
        );
        let bridged = paths_from_execution(&execution, &bridge_context(&sorts)).unwrap();
        assert_eq!(
            bridged
                .paths
                .iter()
                .map(|path| path.stop)
                .collect::<Vec<_>>(),
            [P::UndefinedStep, P::UndefinedStep, P::Terminal]
        );
        assert_eq!(bridged.collection.stop, CollectionStop::SearchExhausted);
        let mut root = trivial(GROUND);
        root.branch.identity.clear();
        assert_eq!(leaf_keys(&[root]), ["undefined@0"]);
    }

    /// Only a `Trivial` halt shows an undefined step; a classifier that says so of a stuck term
    /// breaks its contract.
    #[test]
    fn a_classified_undefined_step_is_rejected() {
        let sorts = sorts();
        let execution = AdaptedExecution {
            leaves: vec![leaf(H::Stuck, GROUND, U, 1)],
            effects: Vec::new(),
            timed_out: false,
        };
        let context = BridgeContext {
            test_id: "t",
            classify: &|_| ExecutionTerminalKind::UndefinedStep,
            sorts: &sorts,
        };
        assert_eq!(
            paths_from_execution(&execution, &context),
            Err(BridgeFailure::ClassifiedUndefinedStep)
        );
    }

    #[test]
    fn a_shared_identity_of_different_branches_is_rejected() {
        let sorts = sorts();
        let execution = AdaptedExecution {
            leaves: vec![
                AdaptedLeaf {
                    halt: H::Stuck,
                    feasibility: U,
                    cause: None,
                    branch: branch(0, GROUND),
                    diagnostics: Vec::new(),
                    candidate_diagnostics: Vec::new(),
                    remainder_diagnostics: Vec::new(),
                    undefined_rule: None,
                },
                AdaptedLeaf {
                    halt: H::Stuck,
                    feasibility: U,
                    cause: None,
                    branch: branch(0, CRASH),
                    diagnostics: Vec::new(),
                    candidate_diagnostics: Vec::new(),
                    remainder_diagnostics: Vec::new(),
                    undefined_rule: None,
                },
            ],
            effects: Vec::new(),
            timed_out: false,
        };
        assert_eq!(
            paths_from_execution(&execution, &bridge_context(&sorts)),
            Err(BridgeFailure::DuplicatePathIdentity(
                "rule-0@target-0".to_owned()
            ))
        );
    }
}
