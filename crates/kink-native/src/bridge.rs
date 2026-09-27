//! Maps adapted executions to kink-pattern paths and collection evidence.
//!
//! A PathSet run records exhaustion only when every leaf completes without a diagnostic.
//! A bounded frontier, failure halt, cancellation, or diagnostic keeps the result open.
//! Diagnostics affect their own path; a clean sibling remains usable evidence.
//!
//! A path's events are evidence for `Match` only when its prefix is real
//! (`PathStop::has_real_prefix`). A symbolic or constrained state may be infeasible. A bounded
//! leaf keeps its limit stop when its state is one ground term without a path condition, or when
//! the adapter showed it feasible ([`LeafFeasibility::Syntactic`], or
//! [`LeafFeasibility::Solver`] with the Z3 profile); otherwise it is `SolverUnknown`.
//!
//! A stuck leaf is complete for a ground term without a path condition. Otherwise it is complete
//! only when three things were shown: its state is feasible, its stuckness holds for every
//! instance of the state (`AdaptedLeaf::every_instance_stuck`, which needs a ground term or the
//! Z3 profile), and every path condition of the definition is an applicability condition
//! ([`DefinitionFacts::applicability_conditions`]), so that the leaves' predicates cover every
//! instance. A symbolic `Stuck` on its own is not a completeness claim; everything else is
//! `SolverUnknown`.
//!
//! A leaf proved to have no instance is discarded: no path, no stop, counted by the report. That
//! is a `Vacuous` leaf, or a stuck or bounded leaf whose predicate the solver refuted
//! ([`LeafFeasibility::Unsat`]), at depth 0 (the initial state has no instance) or under a
//! definition whose path conditions are applicability conditions (the instances that do not
//! take its last step lie in a sibling or remainder). Under an `ensures` clause, instances that
//! violate it disappear after their prefix events have happened, so such a leaf stays
//! `SolverUnknown`. A `Trivial` leaf is always `SolverUnknown`: k-rust reports the state whose
//! every successor is undefined, whose prefix may be real. A diagnosed leaf is never discarded.

use k_rust::backend::EffectOutput;
use k_rust::kore::{
    ast::{Pattern, Sort},
    codec,
};
use kink_pattern::{
    CollectionEvidence, CollectionStop, EmptySearchDecision, Event, EventAttribution, EventOrigin,
    ExecutionStop, ExecutionTerminal, ExecutionTerminalKind, PathInput, PathStop, SymbolSorts,
};

use crate::execution::{AdaptedExecution, HaltClass};
use crate::feasibility::{DefinitionFacts, LeafFeasibility};
use crate::observation::{AdaptedBranch, DomainPayload, NativeEvent};

/// What the bridge needs besides the adapted response.
pub struct BridgeContext<'a> {
    pub test_id: &'a str,
    /// The declaration-owned classifier of a terminal term. The term is ground, except in the
    /// Z3 profile, where a complete stuck leaf may be constrained or symbolic (its variables of
    /// sort `Int` or `Bool`); the classifier must then answer for every instance, that is,
    /// classify by the constructors it sees.
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
pub fn discarded(
    leaf: &crate::execution::AdaptedLeaf,
    definition: DefinitionFacts,
) -> Option<DiscardReason> {
    let reason = match (leaf.halt, leaf.feasibility) {
        (HaltClass::Vacuous, _) => DiscardReason::Vacuous,
        (
            HaltClass::Stuck | HaltClass::DepthBound | HaltClass::BreadthBound,
            LeafFeasibility::Unsat,
        ) => DiscardReason::Unsat,
        _ => return None,
    };
    let covered = leaf.branch.depth == 0 || definition.applicability_conditions;
    (covered && !diagnosed(leaf)).then_some(reason)
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
/// violation it is. `None` is a stuck leaf: it is complete when its state is a ground terminal
/// term, or when the adapter's evidence completes it (see the module documentation), and
/// `SolverUnknown` otherwise, because a symbolic or constrained stuck leaf may be infeasible or
/// stuck only for some instances. A requested depth or breadth bound keeps its limit stop only
/// for a decided or feasible state (see `decided_stop`). A vacuous leaf that is not discarded
/// is `SolverUnknown`.
/// The adapter rejects unrequested bound halts. Exhaustive over `HaltClass`.
pub const fn halt_stop(halt: HaltClass) -> Result<Option<PathStop>, BridgeFailure> {
    Ok(Some(match halt {
        HaltClass::Stuck => return Ok(None),
        HaltClass::Trivial | HaltClass::Vacuous => PathStop::SolverUnknown,
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
/// leaf's state when it is decided (see `SplitState::decided_term`); for a stuck leaf that is
/// its terminal term. `feasible` says the adapter showed the state feasible; it keeps a limit
/// stop real. `stuck_term` is the term of a stuck leaf that is not decided but complete: its
/// state is feasible, stuck for every instance, and covered (see the module documentation).
pub(crate) fn leaf_path(
    halt: HaltClass,
    decided: Option<Pattern>,
    feasible: bool,
    stuck_term: Option<Pattern>,
    classify: &dyn Fn(&Pattern) -> ExecutionTerminalKind,
) -> Result<LeafPath, BridgeFailure> {
    Ok(match (halt_stop(halt)?, decided.or(stuck_term)) {
        (Some(stop), decided) => {
            LeafPath::Incomplete(decided_stop(stop, decided.is_some() || feasible))
        }
        (None, Some(term)) => LeafPath::Complete(ExecutionTerminal {
            kind: classify(&term),
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
    let (terms, predicates) = state
        .into_conjuncts_at(&sort)
        .into_iter()
        .partition(|conjunct| {
            matches!(
                conjunct,
                Pattern::Application { .. }
                    | Pattern::AssociativeApplication { .. }
                    | Pattern::DomainValue { .. }
                    | Pattern::String(_)
                    | Pattern::Variable(_)
            )
        });
    Ok(SplitState {
        sort,
        terms,
        predicates,
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
fn path_key(branch: &AdaptedBranch) -> String {
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
        PathStop::Terminal | PathStop::Stuck | PathStop::MatchFound => CollectionStop::Error,
    }
}

/// Paths under construction, keyed by branch identity. An exact repeat of a branch with the
/// same stop is one path; two different branches with one key are a failure.
struct PathSet<'a> {
    context: &'a BridgeContext<'a>,
    entries: Vec<(String, AdaptedBranch, PathInput)>,
    /// Incomplete stops of every item, including items that add no path.
    incomplete: Vec<PathStop>,
    definition: DefinitionFacts,
}

impl<'a> PathSet<'a> {
    const fn new(context: &'a BridgeContext<'a>, definition: DefinitionFacts) -> Self {
        Self {
            context,
            entries: Vec::new(),
            incomplete: Vec::new(),
            definition,
        }
    }

    fn push(&mut self, leaf: &crate::execution::AdaptedLeaf) -> Result<(), BridgeFailure> {
        let branch = &leaf.branch;
        let halt = leaf.halt;
        // Check the contract before anything is dropped.
        halt_stop(halt)?;
        if discarded(leaf, self.definition).is_some() {
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
        let stuck_term = match split.terms.as_slice() {
            [term]
                if feasible
                    && leaf.every_instance_stuck
                    && self.definition.applicability_conditions =>
            {
                Some(term.clone())
            }
            _ => None,
        };
        let mapped = match leaf_path(
            halt,
            split.decided_term(),
            feasible,
            stuck_term,
            self.context.classify,
        )? {
            _ if diagnosed(leaf) => LeafPath::Incomplete(PathStop::BackendLimit),
            mapped => mapped,
        };
        let (complete, stop, execution_terminal) = match mapped {
            LeafPath::Complete(terminal) => {
                let stop = match terminal.kind {
                    ExecutionTerminalKind::Normal | ExecutionTerminalKind::SemanticCrash => {
                        PathStop::Terminal
                    }
                    ExecutionTerminalKind::Stuck => PathStop::Stuck,
                };
                (true, stop, Some(terminal))
            }
            LeafPath::Incomplete(stop) => {
                self.incomplete.push(stop);
                (false, stop, None)
            }
        };
        self.insert(
            branch,
            complete,
            stop,
            execution_terminal,
            split.path_predicate(),
        )
    }

    fn insert(
        &mut self,
        branch: &AdaptedBranch,
        complete: bool,
        stop: PathStop,
        execution_terminal: Option<ExecutionTerminal>,
        path_predicate: Pattern,
    ) -> Result<(), BridgeFailure> {
        let key = path_key(branch);
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
    let mut paths = PathSet::new(context, execution.definition);
    for leaf in &execution.leaves {
        paths.push(leaf)?;
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

    /// Definition facts of a test execution.
    const fn facts(applicability_conditions: bool) -> DefinitionFacts {
        DefinitionFacts {
            applicability_conditions,
            free_rule_patterns: true,
        }
    }

    /// One adapted leaf over [`branch`] `0`, with the adapter's evidence.
    fn leaf(
        halt: HaltClass,
        state: &str,
        feasibility: LeafFeasibility,
        every_instance_stuck: bool,
        depth: u64,
    ) -> AdaptedLeaf {
        let mut branch = branch(0, state);
        branch.depth = depth;
        AdaptedLeaf {
            halt,
            feasibility,
            every_instance_stuck,
            branch,
            diagnostics: Vec::new(),
            candidate_diagnostics: Vec::new(),
            remainder_diagnostics: Vec::new(),
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

    /// One row: halt, leaf state, adapter feasibility, `every_instance_stuck`, definition
    /// `applicability_conditions`, depth, expected path.
    type Row = (
        HaltClass,
        &'static str,
        LeafFeasibility,
        bool,
        bool,
        u64,
        Expected,
    );

    /// The leaf mapping of README section 3.1 in both profiles: one row per halt class; a stuck
    /// leaf also per terminal shape; a limit over undecided states with and without adapter
    /// feasibility; and the 3b cells (solver feasibility, `Unsat`, every-instance stuckness,
    /// the applicability condition, depth 0). Every leaf carries one event, which is a witness
    /// only on a real prefix (review P1): never on a vacuous, trivial or constrained leaf, nor on
    /// a symbolic leaf the adapter did not show feasible. Feasibility alone never completes a
    /// stuck leaf (Q4), and a discarded leaf adds no path.
    #[test]
    fn execution_leaf_rows_map_to_paths() {
        use ExecutionTerminalKind::{Normal, SemanticCrash};
        use Expected::{Complete, Discarded, Incomplete, Violation};
        use LeafFeasibility::{Solver as Z, Unsat as N};
        #[rustfmt::skip]
        let rows: [Row; 51] = [
            // 3a rows (no solver facts; `applicability_conditions` does not matter).
            (H::Stuck, GROUND, U, true, false, 1, Complete(Normal, GROUND)),
            (H::Stuck, CRASH, U, true, false, 1, Complete(SemanticCrash, CRASH)),
            (H::Stuck, SYMBOLIC, U, false, true, 1, Incomplete(P::SolverUnknown)),
            (H::Stuck, SYMBOLIC, F, false, true, 1, Incomplete(P::SolverUnknown)),
            (H::Stuck, CONSTRAINED, U, true, true, 1, Incomplete(P::SolverUnknown)),
            (H::Trivial, GROUND, U, false, false, 1, Incomplete(P::SolverUnknown)),
            (H::Trivial, SYMBOLIC, F, false, false, 1, Incomplete(P::SolverUnknown)),
            (H::Vacuous, GROUND, U, false, false, 1, Incomplete(P::SolverUnknown)),
            (H::Branch, GROUND, U, false, false, 1, Violation),
            (H::CutPoint, GROUND, U, false, false, 1, Violation),
            (H::TerminalRule, GROUND, U, false, false, 1, Violation),
            (H::DepthBound, GROUND, U, false, false, 1, Incomplete(P::DepthLimit)),
            (H::DepthBound, SYMBOLIC, U, false, false, 1, Incomplete(P::SolverUnknown)),
            (H::DepthBound, SYMBOLIC, F, false, false, 1, Incomplete(P::DepthLimit)),
            (H::DepthBound, CONSTRAINED, U, false, false, 1, Incomplete(P::SolverUnknown)),
            // A syntactic claim over a state that still splits off a path condition is ignored.
            (H::DepthBound, CONSTRAINED, F, false, false, 1, Incomplete(P::SolverUnknown)),
            (H::BreadthBound, GROUND, U, false, false, 1, Incomplete(P::BranchLimit)),
            (H::BreadthBound, SYMBOLIC, U, false, false, 1, Incomplete(P::SolverUnknown)),
            (H::BreadthBound, SYMBOLIC, F, false, false, 1, Incomplete(P::BranchLimit)),
            (H::Indeterminate, GROUND, U, false, false, 1, Incomplete(P::BackendLimit)),
            (H::Indeterminate, SYMBOLIC, F, false, false, 1, Incomplete(P::BackendLimit)),
            (H::UnsupportedHook, GROUND, U, false, false, 1, Incomplete(P::BackendLimit)),
            (H::SimplificationError, GROUND, U, false, false, 1, Incomplete(P::BackendLimit)),
            (H::Timeout, GROUND, U, false, false, 1, Violation),
            (H::Timeout, CONSTRAINED, U, false, false, 1, Violation),
            (H::Cancelled, GROUND, U, false, false, 1, Incomplete(P::Error)),
            (H::Vacuous, BOTTOM, U, false, false, 1, Incomplete(P::SolverUnknown)),
            // 3b: a constrained stuck leaf completes when the solver showed it feasible, every
            // instance is stuck, and the definition's path conditions cover every instance.
            (H::Stuck, CONSTRAINED, Z, true, true, 1, Complete(Normal, GROUND)),
            (H::Stuck, CONSTRAINED, Z, true, false, 1, Incomplete(P::SolverUnknown)),
            (H::Stuck, CONSTRAINED, U, true, true, 1, Incomplete(P::SolverUnknown)),
            // A symbolic stuck leaf needs the adapter's every-instance evidence (Z3 only).
            (H::Stuck, SYMBOLIC, F, true, true, 1, Complete(Normal, SYMBOLIC)),
            (H::Stuck, SYMBOLIC, F, true, false, 1, Incomplete(P::SolverUnknown)),
            (H::Stuck, SYMBOLIC_CONSTRAINED, Z, true, true, 1, Complete(Normal, SYMBOLIC)),
            (H::Stuck, SYMBOLIC_CONSTRAINED, Z, false, true, 1, Incomplete(P::SolverUnknown)),
            // A solver-feasible cut keeps its limit and real prefix; coverage is not needed.
            (H::DepthBound, CONSTRAINED, Z, false, false, 1, Incomplete(P::DepthLimit)),
            (H::BreadthBound, SYMBOLIC_CONSTRAINED, Z, false, false, 1, Incomplete(P::BranchLimit)),
            // A refuted predicate discards a stuck or cut leaf only when covered.
            (H::Stuck, CONSTRAINED, N, true, true, 1, Discarded(DiscardReason::Unsat)),
            (H::Stuck, CONSTRAINED, N, true, false, 1, Incomplete(P::SolverUnknown)),
            (H::Stuck, CONSTRAINED, N, true, false, 0, Discarded(DiscardReason::Unsat)),
            (H::DepthBound, CONSTRAINED, N, false, true, 1, Discarded(DiscardReason::Unsat)),
            (H::DepthBound, CONSTRAINED, N, false, false, 1, Incomplete(P::SolverUnknown)),
            (H::BreadthBound, CONSTRAINED, N, false, true, 1, Discarded(DiscardReason::Unsat)),
            // Backend-limited and trivial leaves are never discarded.
            (H::Indeterminate, CONSTRAINED, N, false, true, 1, Incomplete(P::BackendLimit)),
            (H::Trivial, CONSTRAINED, N, false, true, 0, Incomplete(P::SolverUnknown)),
            (H::Trivial, GROUND, F, true, true, 1, Incomplete(P::SolverUnknown)),
            // A vacuous leaf is discarded at depth 0 or when covered.
            (H::Vacuous, BOTTOM, U, false, false, 0, Discarded(DiscardReason::Vacuous)),
            (H::Vacuous, BOTTOM, U, false, true, 1, Discarded(DiscardReason::Vacuous)),
            (H::Vacuous, BARE_BOTTOM, U, false, false, 0, Discarded(DiscardReason::Vacuous)),
            (H::Vacuous, BARE_BOTTOM, U, false, false, 1, Incomplete(P::SolverUnknown)),
            // The contract is checked before anything is discarded.
            (H::Timeout, CONSTRAINED, N, false, true, 0, Violation),
            (H::Branch, BOTTOM, U, false, true, 0, Violation),
        ];
        let covered = rows
            .iter()
            .map(|(halt, ..)| *halt)
            .collect::<std::collections::BTreeSet<_>>();
        assert_eq!(covered.into_iter().collect::<Vec<_>>(), HaltClass::ALL);
        let sorts = sorts();
        for (halt, state, feasibility, stuck, applicability, depth, expected) in rows {
            let id = format!(
                "{halt:?} {state} {feasibility:?} stuck={stuck} applicability={applicability} \
                 depth={depth}"
            );
            let execution = AdaptedExecution {
                leaves: vec![leaf(halt, state, feasibility, stuck, depth)],
                effects: Vec::new(),
                timed_out: false,
                definition: facts(applicability),
            };
            assert_eq!(
                discarded(&execution.leaves[0], execution.definition),
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
            assert_eq!(path.path_key.as_deref(), Some("rule-0@target-0"), "{id}");
            assert_eq!(bridged.collection.empty_search_decision, None, "{id}");
            match expected {
                Complete(kind, term) => {
                    assert!(path.complete, "{id}");
                    assert_eq!(path.stop, P::Terminal, "{id}");
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
            let mut diagnosed = leaf(halt, CONSTRAINED, feasibility, false, depth);
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
                definition: facts(true),
            };
            assert_eq!(discarded(&execution.leaves[0], execution.definition), None);
            let bridged = paths_from_execution(&execution, &bridge_context(&sorts)).unwrap();
            assert_eq!(bridged.paths.len(), 1, "{halt:?}");
            assert_eq!(bridged.paths[0].stop, P::BackendLimit, "{halt:?}");
        }
    }

    /// A discarded leaf leaves its siblings as they are: a complete sibling alone gives clean
    /// exhaustion without an empty-search decision.
    #[test]
    fn discarded_leaf_keeps_its_siblings() {
        let sorts = sorts();
        let mut vacuous = leaf(H::Vacuous, BOTTOM, U, false, 2);
        vacuous.branch = branch(1, BOTTOM);
        vacuous.branch.depth = 2;
        let execution = AdaptedExecution {
            leaves: vec![leaf(H::Stuck, GROUND, U, true, 1), vacuous],
            effects: Vec::new(),
            timed_out: false,
            definition: facts(true),
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
            every_instance_stuck: true,
            branch: branch(0, GROUND),
            diagnostics: Vec::new(),
            candidate_diagnostics: Vec::new(),
            remainder_diagnostics: Vec::new(),
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
                definition: facts(true),
            };
            let bridged = paths_from_execution(&execution, &bridge_context(&sorts)).unwrap();
            assert_eq!(bridged.collection.stop, CollectionStop::BackendLimit);
            assert!(bridged.paths[0].complete);
            assert_eq!(bridged.paths[1].stop, P::BackendLimit);
            assert_eq!(presence(&bridged), PatternOutcome::Match);
            assert_eq!(absence(&bridged), PatternOutcome::Unknown);
        }
    }

    #[test]
    fn a_shared_identity_of_different_branches_is_rejected() {
        let sorts = sorts();
        let execution = AdaptedExecution {
            leaves: vec![
                AdaptedLeaf {
                    halt: H::Stuck,
                    feasibility: U,
                    every_instance_stuck: true,
                    branch: branch(0, GROUND),
                    diagnostics: Vec::new(),
                    candidate_diagnostics: Vec::new(),
                    remainder_diagnostics: Vec::new(),
                },
                AdaptedLeaf {
                    halt: H::Stuck,
                    feasibility: U,
                    every_instance_stuck: true,
                    branch: branch(0, CRASH),
                    diagnostics: Vec::new(),
                    candidate_diagnostics: Vec::new(),
                    remainder_diagnostics: Vec::new(),
                },
            ],
            effects: Vec::new(),
            timed_out: false,
            definition: facts(true),
        };
        assert_eq!(
            paths_from_execution(&execution, &bridge_context(&sorts)),
            Err(BridgeFailure::DuplicatePathIdentity(
                "rule-0@target-0".to_owned()
            ))
        );
    }
}
