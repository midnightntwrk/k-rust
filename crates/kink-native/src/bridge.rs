//! Maps adapted executions and path searches to kink-pattern paths and collection evidence.
//!
//! Only an execution taken on [`ExecutionRoute::SinglePath`] can be complete. An explore-all
//! execution's collection stop is at best `ExhaustionUnrecorded`, because k-rust may have
//! merged converging branches together with their events. A search is never complete: k-rust
//! has no exhaustion record (`upstream/k-rust.toml` `search-completeness`), so its frontier and
//! incomplete items become limit or indeterminate stops and its collection stop is never
//! `SearchExhausted`. Neither function can therefore yield evidence for `NoMatch` unless the
//! execution is a single complete path. Both record their [`PathRoute`], because an
//! explore-all execution's `ExhaustionUnrecorded` still holds every distinct final state and
//! a search's does not.
//!
//! A path's events are evidence for `Match` only when its prefix is real
//! (`PathStop::has_real_prefix`). Without a solver, a symbolic or constrained state may be
//! infeasible: a stuck or limit-cut leaf whose state is not one ground term without a path
//! condition is `SolverUnknown`, as are vacuous and trivial leaves. A run that collected a
//! backend diagnostic may have kept an infeasible branch or dropped a condition, so every one
//! of its paths is `BackendLimit`.

use k_rust::backend::{EffectOutput, SearchTypeArg};
use k_rust::kore::{
    ast::{Pattern, Sort},
    codec,
};
use kink_pattern::{
    CollectionEvidence, CollectionStop, Event, EventOrigin, ExecutionStop, ExecutionTerminal,
    ExecutionTerminalKind, PathInput, PathStop, SymbolSorts, TransitionKey,
};

use crate::execution::{AdaptedExecution, ExecutionRoute, HaltClass};
use crate::observation::{AdaptedBranch, DomainPayload, NativeEvent};
use crate::search::{AdaptedIncomplete, AdaptedPathSearch, IncompleteClass};

/// What the bridge needs besides the adapted response.
pub struct BridgeContext<'a> {
    pub test_id: &'a str,
    /// The declaration-owned classifier of a ground terminal term.
    pub classify: &'a dyn Fn(&Pattern) -> ExecutionTerminalKind,
    /// Symbol sorts of the compiled definition, to find the sort of a bare leaf state.
    pub sorts: &'a SymbolSorts,
}

/// How bridged paths were obtained. A consumer that needs every final state reads it
/// instead of inferring the route from the collection stop, which an explore-all execution
/// and a search share.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PathRoute {
    Execution(ExecutionRoute),
    /// A `Final` path search: never a complete set of final states.
    Search,
}

/// Paths in response order, the route that produced them, and the evidence of how their
/// collection stopped.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BridgedPaths {
    pub paths: Vec<PathInput>,
    pub route: PathRoute,
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
    /// Only a `Final` search's witnesses are final states.
    UnsupportedQueryShape(SearchTypeArg),
    /// Two different branches have one identity, so they would share a path key.
    DuplicatePathIdentity(String),
}

/// How one leaf or search state becomes a path.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum LeafPath {
    /// A ground terminal term with no path condition.
    Complete(ExecutionTerminal),
    Incomplete(PathStop),
}

/// The stop of a leaf with halt class `halt`, before its state is read, or the contract
/// violation it is. `None` is a stuck leaf: it is complete exactly when its state is a ground
/// terminal term, and `SolverUnknown` otherwise, because the no-Z3 profile does not refute
/// path conditions and a symbolic or constrained stuck leaf may be infeasible. A limit stop
/// likewise holds only for a decided state (see `decided_stop`). Exhaustive over
/// `HaltClass`.
pub const fn halt_stop(halt: HaltClass) -> Result<Option<PathStop>, BridgeFailure> {
    Ok(Some(match halt {
        HaltClass::Stuck => return Ok(None),
        HaltClass::Trivial | HaltClass::Vacuous => PathStop::SolverUnknown,
        HaltClass::DepthBound => PathStop::DepthLimit,
        HaltClass::BreadthBound => PathStop::BranchLimit,
        HaltClass::Indeterminate | HaltClass::UnsupportedHook | HaltClass::SimplificationError => {
            PathStop::BackendLimit
        }
        HaltClass::Timeout => PathStop::TimeLimit,
        // Until upstream tells cancellation from timeout.
        HaltClass::Cancelled => PathStop::Error,
        HaltClass::Branch | HaltClass::CutPoint | HaltClass::TerminalRule => {
            return Err(BridgeFailure::ContractViolation(halt));
        }
    }))
}

/// `stop`, or `SolverUnknown` when `stop` vouches for a real prefix but the state is not
/// decided: a symbolic or constrained state may be infeasible without a solver.
pub(crate) const fn decided_stop(stop: PathStop, decided: bool) -> PathStop {
    if stop.has_real_prefix() && !decided {
        PathStop::SolverUnknown
    } else {
        stop
    }
}

/// The path of a leaf, or the contract violation it is (see [`halt_stop`]). `decided` is the
/// leaf's state when it is decided (see `SplitState::decided_term`); for a stuck leaf that is
/// its terminal term.
pub(crate) fn leaf_path(
    halt: HaltClass,
    decided: Option<Pattern>,
    classify: &dyn Fn(&Pattern) -> ExecutionTerminalKind,
) -> Result<LeafPath, BridgeFailure> {
    Ok(match (halt_stop(halt)?, decided) {
        (Some(stop), decided) => LeafPath::Incomplete(decided_stop(stop, decided.is_some())),
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
                label,
                payload,
            ) = match event {
                NativeEvent::RuleApplied(event) => (
                    event.event_ordinal,
                    event.transition_ordinal,
                    event.emission_ordinal,
                    format!("rule:{}", event.rule_label),
                    &event.transition,
                    &event.rule_label,
                    Vec::new(),
                ),
                NativeEvent::Domain(event) => (
                    event.event_ordinal,
                    event.transition_ordinal,
                    event.emission_ordinal,
                    event.constructor.clone(),
                    &event.transition,
                    &event.rule_label,
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
                ),
            };
            Ok(Event {
                index,
                constructor,
                payload,
                origin: EventOrigin {
                    rule_label: label.clone(),
                    transition: TransitionKey::from(transition),
                    semantic_site: None,
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
    /// The run collected a backend diagnostic: every leaf is `BackendLimit`.
    diagnosed: bool,
    entries: Vec<(String, AdaptedBranch, PathInput)>,
    /// Incomplete stops of every item, including items that add no path.
    incomplete: Vec<PathStop>,
}

impl<'a> PathSet<'a> {
    const fn new(context: &'a BridgeContext<'a>, diagnosed: bool) -> Self {
        Self {
            context,
            diagnosed,
            entries: Vec::new(),
            incomplete: Vec::new(),
        }
    }

    fn push(&mut self, branch: &AdaptedBranch, halt: HaltClass) -> Result<(), BridgeFailure> {
        let split = split_state(&branch.state, self.context.sorts)?;
        let mapped = match leaf_path(halt, split.decided_term(), self.context.classify)? {
            _ if self.diagnosed => LeafPath::Incomplete(PathStop::BackendLimit),
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

    /// An incomplete search state; it adds `stop` whatever its halt would be.
    fn push_incomplete(
        &mut self,
        branch: &AdaptedBranch,
        stop: PathStop,
    ) -> Result<(), BridgeFailure> {
        let split = split_state(&branch.state, self.context.sorts)?;
        let stop = decided_stop(stop, split.decided_term().is_some());
        self.incomplete.push(stop);
        self.insert(branch, false, stop, None, split.path_predicate())
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

    /// The least severe incomplete stop, else the stop of `route` running out of work: only a
    /// single-path execution records exhaustion.
    fn finish(self, route: PathRoute) -> BridgedPaths {
        let otherwise = match route {
            PathRoute::Execution(ExecutionRoute::SinglePath) => CollectionStop::SearchExhausted,
            PathRoute::Execution(ExecutionRoute::ExploreAll) | PathRoute::Search => {
                CollectionStop::ExhaustionUnrecorded
            }
        };
        let stop = self
            .incomplete
            .iter()
            .min()
            .map_or(otherwise, |stop| collection_stop(*stop));
        BridgedPaths {
            paths: self.entries.into_iter().map(|(.., path)| path).collect(),
            route,
            collection: CollectionEvidence {
                stop,
                pending_work: u64::from(stop != CollectionStop::SearchExhausted),
                empty_search_decision: None,
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
            route: PathRoute::Execution(execution.route),
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
    let mut paths = PathSet::new(context, !execution.diagnostics.is_empty());
    for leaf in &execution.leaves {
        paths.push(&leaf.branch, leaf.halt)?;
    }
    Ok(paths.finish(PathRoute::Execution(execution.route)))
}

/// The stop one upstream incomplete item stands for. A result bound adds no path: it is a
/// collection-level stop. Exhaustive over `IncompleteClass`.
pub(crate) const fn incomplete_stop(class: IncompleteClass) -> PathStop {
    match class {
        IncompleteClass::ResultBound => PathStop::ResultLimit,
        IncompleteClass::DepthBound => PathStop::DepthLimit,
        IncompleteClass::BreadthBound => PathStop::BranchLimit,
        IncompleteClass::Indeterminate => PathStop::BackendLimit,
        IncompleteClass::MatchIndeterminate | IncompleteClass::SolverDeferred => {
            PathStop::SolverUnknown
        }
        IncompleteClass::Cancelled => PathStop::Error,
    }
}

/// Reads an adapted `Final` path search as paths; see the module documentation.
pub fn paths_from_search(
    search: &AdaptedPathSearch,
    context: &BridgeContext<'_>,
) -> Result<BridgedPaths, BridgeFailure> {
    let search_type = search.query().search_type();
    if search_type != SearchTypeArg::Final {
        return Err(BridgeFailure::UnsupportedQueryShape(search_type));
    }
    let mut paths = PathSet::new(context, !search.diagnostics().is_empty());
    for witness in search
        .outcome()
        .witnesses()
        .into_iter()
        .flat_map(|w| w.iter())
    {
        // A non-frontier `Final` witness is a state that cannot rewrite: a stuck leaf.
        paths.push(witness, HaltClass::Stuck)?;
    }
    for state in search.frontier() {
        paths.push_incomplete(state, PathStop::DepthLimit)?;
    }
    for item in search.incomplete() {
        let stop = incomplete_stop(item.class());
        match item {
            AdaptedIncomplete::ResultBound => paths.incomplete.push(stop),
            AdaptedIncomplete::BreadthBound { states } => {
                for state in states {
                    paths.push_incomplete(state, stop)?;
                }
            }
            AdaptedIncomplete::DepthBound { state }
            | AdaptedIncomplete::Indeterminate { state, .. }
            | AdaptedIncomplete::Cancelled { state }
            | AdaptedIncomplete::Simplification { state, .. }
            | AdaptedIncomplete::MatchIndeterminate { state, .. }
            | AdaptedIncomplete::SolverDeferred { state, .. } => {
                paths.push_incomplete(state, stop)?;
            }
        }
    }
    Ok(paths.finish(PathRoute::Search))
}

#[cfg(test)]
mod tests {
    use super::*;
    use k_rust::backend::{
        BACKEND_SCHEMA_VERSION, IncompleteSearchOutput, PathSearchResponse, PathWitnessOutput,
        ResultModalityOutput, SearchFailureOutput, SearchStateOutput, SmtFailureOutput,
        TransitionIdOutput,
    };
    use k_rust::kore::{json as kore_json, parser::parse_pattern};
    use kink_pattern::{
        Atom, Constructor, EvaluationContext, EvaluationOptions, EventVocabulary, ExecutionBounds,
        OriginMode, PatternArm, PatternOutcome, PatternPlan, SearchPolicy, evaluate,
    };
    use serde_json::Value;

    use crate::ProvenanceStatus;
    use crate::execution::AdaptedLeaf;
    use crate::observation::{DomainEvent, InstalledObservationManifest};
    use crate::search::{QueryShape, adapt_path_response};

    use HaltClass as H;
    use PathStop as P;

    const GROUND: &str = r"Lbla{}()";
    const CRASH: &str = r"Lblcrash{}()";
    const SYMBOLIC: &str = r"X:SortS{}";
    const CONSTRAINED: &str =
        r#"\and{SortS{}}(Lbla{}(), \equals{SortInt{}, SortS{}}(Y:SortInt{}, \dv{SortInt{}}("1")))"#;
    /// The state k-rust reports for a leaf whose path condition became false.
    const BOTTOM: &str = r"\and{SortS{}}(Lbla{}(), \bottom{SortS{}}())";

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
                rule_label: "M.fired".to_owned(),
                payload: Vec::new(),
                provenance: ProvenanceStatus::SidecarOnlyMissingBridge,
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
                    origin_mode: OriginMode::EmittingSentence,
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
            selected_rule_labels: ["M.fired".to_owned()].into_iter().collect(),
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

    /// The leaf mapping, one row per halt class; a stuck leaf also per terminal shape, and a
    /// limit also over an undecided state. `None` is a contract violation. Every leaf carries
    /// one event, which is a witness only on a real prefix (review P1): never on a vacuous,
    /// trivial, symbolic or constrained leaf.
    #[test]
    fn execution_leaf_rows_map_to_paths() {
        use ExecutionTerminalKind::{Normal, SemanticCrash};
        // (halt, leaf state, expected complete terminal kind or incomplete stop)
        type Expected = Option<Result<ExecutionTerminalKind, PathStop>>;
        let rows: [(HaltClass, &str, Expected); 20] = [
            (H::Stuck, GROUND, Some(Ok(Normal))),
            (H::Stuck, CRASH, Some(Ok(SemanticCrash))),
            (H::Stuck, SYMBOLIC, Some(Err(P::SolverUnknown))),
            (H::Stuck, CONSTRAINED, Some(Err(P::SolverUnknown))),
            (H::Trivial, GROUND, Some(Err(P::SolverUnknown))),
            (H::Vacuous, GROUND, Some(Err(P::SolverUnknown))),
            (H::Branch, GROUND, None),
            (H::CutPoint, GROUND, None),
            (H::TerminalRule, GROUND, None),
            (H::DepthBound, GROUND, Some(Err(P::DepthLimit))),
            (H::DepthBound, CONSTRAINED, Some(Err(P::SolverUnknown))),
            (H::BreadthBound, GROUND, Some(Err(P::BranchLimit))),
            (H::BreadthBound, SYMBOLIC, Some(Err(P::SolverUnknown))),
            (H::Indeterminate, GROUND, Some(Err(P::BackendLimit))),
            (H::UnsupportedHook, GROUND, Some(Err(P::BackendLimit))),
            (H::SimplificationError, GROUND, Some(Err(P::BackendLimit))),
            (H::Timeout, GROUND, Some(Err(P::TimeLimit))),
            (H::Timeout, CONSTRAINED, Some(Err(P::SolverUnknown))),
            (H::Cancelled, GROUND, Some(Err(P::Error))),
            (H::Vacuous, BOTTOM, Some(Err(P::SolverUnknown))),
        ];
        let covered = rows
            .iter()
            .map(|(halt, ..)| *halt)
            .collect::<std::collections::BTreeSet<_>>();
        assert_eq!(covered.into_iter().collect::<Vec<_>>(), HaltClass::ALL);
        let sorts = sorts();
        for (halt, state, expected) in rows {
            let id = format!("{halt:?} {state}");
            let execution = AdaptedExecution {
                route: ExecutionRoute::SinglePath,
                leaves: vec![AdaptedLeaf {
                    halt,
                    branch: branch(0, state),
                }],
                effects: Vec::new(),
                diagnostics: Vec::new(),
                timed_out: false,
            };
            let bridged = paths_from_execution(&execution, &bridge_context(&sorts));
            let Some(expected) = expected else {
                assert_eq!(bridged, Err(BridgeFailure::ContractViolation(halt)), "{id}");
                continue;
            };
            let bridged = bridged.unwrap_or_else(|failure| panic!("{id}: {failure:?}"));
            let [path] = bridged.paths.as_slice() else {
                panic!("{id}: one path");
            };
            assert_eq!(path.path_key.as_deref(), Some("rule-0@target-0"), "{id}");
            match expected {
                Ok(kind) => {
                    assert!(path.complete, "{id}");
                    assert_eq!(path.stop, P::Terminal, "{id}");
                    let terminal = path.execution_terminal.as_ref().expect("terminal");
                    assert_eq!(terminal.kind, kind, "{id}");
                    assert_eq!(terminal.state, parse_pattern(state).expect("state"), "{id}");
                    assert_eq!(
                        bridged.collection.stop,
                        CollectionStop::SearchExhausted,
                        "{id}"
                    );
                    assert_eq!(absence(&bridged), PatternOutcome::NoMatch, "{id}");
                    assert_eq!(presence(&bridged), PatternOutcome::Match, "{id}");
                }
                Err(stop) => {
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
            }
        }
        // The path predicate keeps the constrained leaf's condition.
        let split = split_state(&kore(CONSTRAINED), &sorts).expect("split");
        assert_eq!(split.decided_term(), None);
        assert!(matches!(split.path_predicate(), Pattern::Equals { .. }));
    }

    /// Complete evidence needs the single-path route, no diagnostic and no timeout, and a
    /// witness needs a real prefix: a diagnostic makes every path of its run `BackendLimit`,
    /// so its events are no witness even on a stuck ground leaf (review P1), and the
    /// collection says so even beside a less severe limit.
    #[test]
    fn execution_collection_rows_never_overclaim() {
        let sorts = sorts();
        let leaf = |marker, halt| AdaptedLeaf {
            halt,
            branch: branch(marker, GROUND),
        };
        let execution = |route, leaves, diagnostics, timed_out| AdaptedExecution {
            route,
            leaves,
            effects: Vec::new(),
            diagnostics,
            timed_out,
        };
        let budget = k_rust_backend::diagnostic::BackendDiagnostic::SimplificationBudgetExhausted {
            limit: 1,
            subject: k_rust_backend::simplify::BudgetSubject::Term,
        };
        // (id, execution, expected collection stop, paths, occurrence of every leaf's event)
        let rows = [
            (
                "single-path-is-complete",
                execution(
                    ExecutionRoute::SinglePath,
                    vec![leaf(0, H::Stuck)],
                    Vec::new(),
                    false,
                ),
                CollectionStop::SearchExhausted,
                1,
                PatternOutcome::Match,
            ),
            (
                "explore-all-records-no-exhaustion",
                execution(
                    ExecutionRoute::ExploreAll,
                    vec![leaf(0, H::Stuck), leaf(1, H::Stuck)],
                    Vec::new(),
                    false,
                ),
                CollectionStop::ExhaustionUnrecorded,
                2,
                PatternOutcome::Match,
            ),
            (
                "explore-all-reports-its-least-severe-limit",
                execution(
                    ExecutionRoute::ExploreAll,
                    vec![
                        leaf(0, H::Stuck),
                        leaf(1, H::Indeterminate),
                        leaf(2, H::DepthBound),
                    ],
                    Vec::new(),
                    false,
                ),
                CollectionStop::DepthLimit,
                3,
                PatternOutcome::Match,
            ),
            (
                "a-diagnostic-makes-the-single-path-incomplete",
                execution(
                    ExecutionRoute::SinglePath,
                    vec![leaf(0, H::Stuck)],
                    vec![budget.clone()],
                    false,
                ),
                CollectionStop::BackendLimit,
                1,
                PatternOutcome::Unknown,
            ),
            (
                "a-diagnostic-makes-every-explored-path-a-backend-limit",
                execution(
                    ExecutionRoute::ExploreAll,
                    vec![leaf(0, H::Stuck), leaf(1, H::DepthBound)],
                    vec![budget],
                    false,
                ),
                CollectionStop::BackendLimit,
                2,
                PatternOutcome::Unknown,
            ),
            (
                "a-timed-out-run-is-not-decoded",
                execution(
                    ExecutionRoute::SinglePath,
                    vec![leaf(0, H::Stuck)],
                    Vec::new(),
                    true,
                ),
                CollectionStop::TimeLimit,
                0,
                PatternOutcome::Unknown,
            ),
        ];
        for (id, execution, stop, paths, occurrence) in rows {
            let bridged = paths_from_execution(&execution, &bridge_context(&sorts))
                .unwrap_or_else(|failure| panic!("{id}: {failure:?}"));
            assert_eq!(bridged.collection.stop, stop, "{id}");
            assert_eq!(bridged.route, PathRoute::Execution(execution.route), "{id}");
            assert_eq!(bridged.paths.len(), paths, "{id}");
            assert_eq!(presence(&bridged), occurrence, "{id}");
            if !execution.diagnostics.is_empty() {
                for path in &bridged.paths {
                    assert!(!path.complete && path.execution_terminal.is_none(), "{id}");
                    assert_eq!(path.stop, P::BackendLimit, "{id}");
                }
            }
            assert_eq!(
                absence(&bridged) == PatternOutcome::NoMatch,
                stop == CollectionStop::SearchExhausted,
                "{id}"
            );
        }
        assert_eq!(
            paths_from_execution(
                &execution(ExecutionRoute::ExploreAll, Vec::new(), Vec::new(), false),
                &bridge_context(&sorts)
            ),
            Err(BridgeFailure::NoLeaves)
        );
        let mut effect = leaf(0, H::Stuck);
        effect.branch.events = vec![NativeEvent::Domain(DomainEvent {
            event_ordinal: 0,
            transition_ordinal: 0,
            emission_ordinal: 0,
            constructor: "logged".to_owned(),
            transition: effect.branch.identity[0].clone(),
            rule_label: "M.logged".to_owned(),
            payload: vec![DomainPayload::Effect(EffectOutput::UserLog {
                message: "hello".to_owned(),
            })],
            provenance: ProvenanceStatus::SidecarOnlyMissingBridge,
        })];
        assert_eq!(
            paths_from_execution(
                &execution(ExecutionRoute::SinglePath, vec![effect], Vec::new(), false),
                &bridge_context(&sorts)
            ),
            Err(BridgeFailure::UnsupportedPayload)
        );
    }

    fn search_state(marker: usize) -> SearchStateOutput {
        SearchStateOutput {
            state: kore(GROUND),
            depth: 1,
            trace: Vec::new(),
            branch: vec![TransitionIdOutput {
                rule: format!("rule-{marker}"),
                target: format!("target-{marker}"),
            }],
            observations: Vec::new(),
        }
    }

    fn witness(marker: usize, depth: u64) -> PathWitnessOutput {
        let state = search_state(marker);
        PathWitnessOutput {
            id: state.branch,
            state: state.state,
            depth,
            trace: Vec::new(),
            observations: Vec::new(),
        }
    }

    fn search(
        query: QueryShape,
        witnesses: Vec<PathWitnessOutput>,
        incomplete: Vec<IncompleteSearchOutput>,
    ) -> AdaptedPathSearch {
        adapt_path_response(
            &InstalledObservationManifest::install(Vec::new()).expect("empty manifest"),
            query,
            PathSearchResponse {
                schema_version: BACKEND_SCHEMA_VERSION,
                modality: ResultModalityOutput::PathSet,
                witnesses,
                effects: Vec::new(),
                incomplete,
            },
        )
        .expect("adapted search")
    }

    /// One row per incomplete class, a frontier-only row and an empty-incomplete row: a
    /// search collection is never `SearchExhausted`, so absence is never `NoMatch`.
    #[test]
    fn search_outcomes_never_reach_search_exhausted() {
        use IncompleteSearchOutput as I;
        let unbounded = QueryShape::new(SearchTypeArg::Final, None);
        let requires = || SearchFailureOutput::Requires {
            rule: "r".to_owned(),
            predicates: Vec::new(),
        };
        // (id, query, witnesses, incomplete items, expected collection stop, path count)
        type Row = (
            &'static str,
            QueryShape,
            Vec<PathWitnessOutput>,
            Vec<I>,
            CollectionStop,
            usize,
        );
        let rows: Vec<Row> = vec![
            (
                "empty-incomplete",
                unbounded,
                vec![witness(0, 1)],
                Vec::new(),
                CollectionStop::ExhaustionUnrecorded,
                1,
            ),
            (
                "frontier-only",
                QueryShape::new(SearchTypeArg::Final, Some(1)),
                vec![witness(0, 1)],
                Vec::new(),
                CollectionStop::DepthLimit,
                1,
            ),
            (
                "result-bound",
                unbounded,
                Vec::new(),
                vec![I::ResultBound],
                CollectionStop::ResultLimit,
                0,
            ),
            (
                "depth-bound",
                unbounded,
                Vec::new(),
                vec![I::DepthBound {
                    state: search_state(1),
                }],
                CollectionStop::DepthLimit,
                1,
            ),
            (
                "breadth-bound",
                unbounded,
                Vec::new(),
                vec![I::BreadthBound {
                    states: vec![search_state(1), search_state(2)],
                }],
                CollectionStop::BranchLimit,
                2,
            ),
            (
                "indeterminate",
                unbounded,
                Vec::new(),
                vec![I::Indeterminate {
                    state: search_state(1),
                    reason: requires(),
                }],
                CollectionStop::BackendLimit,
                1,
            ),
            (
                "indeterminate-cancelled",
                unbounded,
                Vec::new(),
                vec![I::Indeterminate {
                    state: search_state(1),
                    reason: SearchFailureOutput::Cancelled,
                }],
                CollectionStop::Error,
                1,
            ),
            (
                "cancelled",
                unbounded,
                Vec::new(),
                vec![I::Cancelled {
                    state: search_state(1),
                }],
                CollectionStop::Error,
                1,
            ),
            (
                "simplification",
                unbounded,
                Vec::new(),
                vec![I::Simplification {
                    state: search_state(1),
                    error: requires(),
                }],
                CollectionStop::BackendLimit,
                1,
            ),
            (
                "match-indeterminate",
                unbounded,
                Vec::new(),
                vec![I::Match {
                    state: search_state(1),
                    bindings: Vec::new(),
                    remainder: Vec::new(),
                }],
                CollectionStop::SolverUnknown,
                1,
            ),
            (
                "solver-deferred",
                unbounded,
                Vec::new(),
                vec![I::Smt {
                    state: search_state(1),
                    error: SmtFailureOutput::Unavailable,
                }],
                CollectionStop::SolverUnknown,
                1,
            ),
            (
                "constrained-frontier-is-undecided",
                QueryShape::new(SearchTypeArg::Final, Some(1)),
                vec![PathWitnessOutput {
                    state: kore(CONSTRAINED),
                    ..witness(0, 1)
                }],
                Vec::new(),
                CollectionStop::SolverUnknown,
                1,
            ),
            (
                "constrained-depth-bound-is-undecided",
                unbounded,
                Vec::new(),
                vec![I::DepthBound {
                    state: SearchStateOutput {
                        state: kore(CONSTRAINED),
                        ..search_state(1)
                    },
                }],
                CollectionStop::SolverUnknown,
                1,
            ),
            (
                "witness-beside-a-depth-bound",
                unbounded,
                vec![witness(0, 1)],
                vec![I::DepthBound {
                    state: search_state(1),
                }],
                CollectionStop::DepthLimit,
                2,
            ),
        ];
        let classes = rows
            .iter()
            .flat_map(|(_, query, witnesses, incomplete, ..)| {
                search(*query, witnesses.clone(), incomplete.clone())
                    .incomplete()
                    .iter()
                    .map(AdaptedIncomplete::class)
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        for class in [
            IncompleteClass::ResultBound,
            IncompleteClass::DepthBound,
            IncompleteClass::BreadthBound,
            IncompleteClass::Indeterminate,
            IncompleteClass::Cancelled,
            IncompleteClass::MatchIndeterminate,
            IncompleteClass::SolverDeferred,
        ] {
            assert!(classes.contains(&class), "{class:?} has a row");
        }
        let sorts = sorts();
        for (id, query, witnesses, incomplete, stop, paths) in rows {
            let bridged = paths_from_search(
                &search(query, witnesses, incomplete),
                &bridge_context(&sorts),
            )
            .unwrap_or_else(|failure| panic!("{id}: {failure:?}"));
            assert_eq!(bridged.collection.stop, stop, "{id}");
            assert_eq!(bridged.route, PathRoute::Search, "{id}");
            assert_ne!(
                bridged.collection.stop,
                CollectionStop::SearchExhausted,
                "{id}"
            );
            assert_eq!(bridged.paths.len(), paths, "{id}");
            assert_ne!(absence(&bridged), PatternOutcome::NoMatch, "{id}");
        }
        // A ground witness is still a complete final path, unless the search collected a
        // backend diagnostic (review P2.3; the live row is in tests/bridge.rs).
        let budget = k_rust_backend::diagnostic::BackendDiagnostic::SimplificationBudgetExhausted {
            limit: 1,
            subject: k_rust_backend::simplify::BudgetSubject::Term,
        };
        // (id, diagnostics, expected path stop, collection stop)
        #[rustfmt::skip]
        let diagnosed = [
            ("undiagnosed-witness", Vec::new(), P::Terminal, CollectionStop::ExhaustionUnrecorded),
            ("diagnosed-witness", vec![budget], P::BackendLimit, CollectionStop::BackendLimit),
        ];
        for (id, diagnostics, stop, collection) in diagnosed {
            let adapted =
                search(unbounded, vec![witness(0, 1)], Vec::new()).with_diagnostics(diagnostics);
            let bridged = paths_from_search(&adapted, &bridge_context(&sorts))
                .unwrap_or_else(|failure| panic!("{id}: {failure:?}"));
            let [path] = bridged.paths.as_slice() else {
                panic!("{id}: one path");
            };
            assert_eq!(path.complete, stop == P::Terminal, "{id}");
            assert_eq!(path.stop, stop, "{id}");
            assert_eq!(bridged.collection.stop, collection, "{id}");
        }
    }

    #[test]
    fn only_final_searches_are_bridged() {
        let sorts = sorts();
        for search_type in [
            SearchTypeArg::All,
            SearchTypeArg::OneStep,
            SearchTypeArg::OneOrMoreSteps,
        ] {
            assert_eq!(
                paths_from_search(
                    &search(
                        QueryShape::new(search_type, None),
                        vec![witness(0, 1)],
                        Vec::new()
                    ),
                    &bridge_context(&sorts)
                ),
                Err(BridgeFailure::UnsupportedQueryShape(search_type))
            );
        }
    }

    #[test]
    fn a_shared_identity_of_different_branches_is_rejected() {
        let sorts = sorts();
        let mut other = witness(0, 1);
        other.state = kore(CRASH);
        assert_eq!(
            paths_from_search(
                &search(
                    QueryShape::new(SearchTypeArg::Final, None),
                    vec![witness(0, 1), other],
                    Vec::new()
                ),
                &bridge_context(&sorts)
            ),
            Err(BridgeFailure::DuplicatePathIdentity(
                "rule-0@target-0".to_owned()
            ))
        );
    }
}
