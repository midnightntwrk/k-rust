//! ```toml algorithm
//! id = "backend.search.configurations"
//! name = "breadth-first search over configurations"
//! sites = ["search_graph_using", "search_graph_collecting", "materialize_search_state", "retain_state_result"]
//! variable = "n = distinct (depth, pattern, is_rewritable) keys at one depth; r = results retained"
//! counters = ["SearchStatesDeduplicated"]
//! span = "per problem"
//! consumes = [{ type = "k_rust_backend::rewrite::RewriteResult", role = "rewrite result" }]
//!
//! [[cost]]
//! mode = "one depth"
//! bound = "O(n) rewrite steps plus O(r) pattern comparisons per retained result"
//!
//! [[cost]]
//! mode = "result or pattern bound reached"
//! bound = "one extra rewrite step in state_may_expand"
//! ```
//!
//! ```toml algorithm
//! id = "backend.search.paths"
//! name = "breadth-first enumeration of simple rewrite paths"
//! sites = ["search_paths_using", "search_paths_collecting", "retain_witness"]
//! variable = "d = path depth; b = branching factor"
//! counters = []
//! no_counter = "path enumeration has no dedicated counter"
//! span = "per problem"
//! consumes = [{ type = "k_rust_backend::rewrite::RewriteResult", role = "rewrite result" }]
//!
//! [[cost]]
//! mode = "simple paths"
//! bound = "exponential in b and d, plus O(d) visited-list work per pop"
//! ```
//!
//! ```toml algorithm
//! id = "backend.search.patterns"
//! name = "pattern search over rewrite results"
//! sites = ["search_pattern_using", "search_pattern_paths_using", "match_pattern_with_variables", "match_disjunction_using"]
//! variable = "m = result patterns examined; k = matches retained"
//! counters = []
//! no_counter = "pattern search has no dedicated counter"
//! span = "per problem"
//! consumes = [{ type = "k_rust_backend::matching::MatchResult", role = "match result" }]
//!
//! [[cost]]
//! mode = "result-set search"
//! bound = "O(m) matches, each followed by one predicate simplification and at most one is_sat, plus O(k) comparisons per retained match, plus the selected rewrite-search strategy"
//! ```
//!
//! ```toml algorithm
//! id = "backend.substitution.extract_output"
//! name = "output-restricted substitution extraction"
//! sites = ["normalize_match_condition"]
//! variable = "c = constraints; t = term size"
//! counters = []
//! no_counter = "output-restricted extraction has no dedicated counter"
//! span = "per call"
//! variant_of = "backend.substitution.extract"
//!
//! [[cost]]
//! mode = "search result normalization"
//! bound = "O(c^2 x t)"
//! ```
//!
//! Breadth-first search over configurations with `(depth, pattern, is_rewritable)`
//! deduplication (Kore constructExecutionGraph; the LLVM backend's search), O(distinct
//! configurations per depth) rewrite steps, `Counter::SearchStatesDeduplicated`; breadth-first
//! enumeration of simple paths with a per-path visited list, exponential in branching plus
//! O(depth) per pop; pattern search over the result set. `normalize_match_condition` is the
//! output-restricted variant of substitution extraction, O(c^2 x t) for c constraints, no
//! counter.

use std::collections::{BTreeSet, HashSet, VecDeque};

use k_rust_kore::measure::{self, Algorithm, Counter};

use crate::{
    builtin::{BuiltinEffect, BuiltinError},
    cancellation::cancellation_requested,
    definition::BackendDefinition,
    diagnostic::{self, BackendDiagnostic, PathDiagnostics, extend_distinct},
    matching::{MatchMode, MatchResult, match_terms_in_definition},
    rewrite::{
        AppliedRule, IndeterminateReason, Pattern, RemainderBranch, RewriteResult, TraceEntry,
        TraceKind, Truth, UndecidedStep, predicates_truth, rewrite_step_with_options,
        simplify_result_pattern, substitute_predicates,
    },
    rule::Predicate,
    simplify::{
        DEFAULT_MAX_SIMPLIFICATION_ITERATIONS, SimplificationError, SimplificationOptions,
        simplify_predicates_with_solver, simplify_with_solver,
    },
    smt::{NoSolver, Satisfiability, SmtError, SmtSolver},
    substitution::{Substitution, compose, substitute},
    transition::{ObservationEvent, ObservationHead, ObservationLog, ObservationOptions},
};

pub use crate::transition::{PatternDigest, TransitionId};

/// Which nodes in the execution tree are returned by a search.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SearchType {
    /// Configurations reached in exactly one semantic rewrite step.
    One,
    /// Configurations whose `Stuck` step has no successor for any ground instance satisfying
    /// the state's constraints. A depth bound is reported as an incomplete frontier instead.
    Final,
    /// Every reachable configuration, including the initial configuration.
    Star,
    /// Every configuration reached in at least one semantic rewrite step.
    Plus,
}

/// Whether a result denotes unique states or distinct execution paths.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ResultModality {
    StateSet,
    PathSet,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SearchOptions {
    pub search_type: SearchType,
    pub max_depth: u64,
    pub max_breadth: Option<usize>,
    pub max_results: Option<usize>,
    pub max_simplification_iterations: usize,
}

impl Default for SearchOptions {
    fn default() -> Self {
        Self {
            search_type: SearchType::Final,
            max_depth: u64::MAX,
            max_breadth: None,
            max_results: None,
            max_simplification_iterations: DEFAULT_MAX_SIMPLIFICATION_ITERATIONS,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SearchState {
    pub pattern: Pattern,
    pub depth: u64,
    /// One valid path to this pattern; when paths converge, which witness survives is unspecified.
    pub trace: Vec<TraceEntry>,
    /// Stable semantic path prefix when structured observation was enabled.
    pub branch: Vec<TransitionId>,
    /// Ordered structured events retained for this search path.
    pub observations: Vec<ObservationEvent>,
    /// The backend diagnostics of the work the path in `trace` went through, in the order the
    /// path first met them, each distinct diagnostic once: the simplification of every state on
    /// the path, the rewrite-step work each successor was derived from
    /// (`AppliedRule::diagnostics`, `RemainderBranch::diagnostics`), and for a reported state its
    /// externalisation; for a state reported because its step halted (`Stuck` in a `Final`
    /// search, an indeterminate or failed step, a cancellation), that step's work. A state
    /// reported before its step runs (`Star`/`Plus` results) does not carry that step's work:
    /// when the step emits and returns `Stuck`, no entry derives from it. When converging paths
    /// are deduplicated, the recorded path's list is kept, like its trace. A non-empty list means
    /// the state may not be the normal form a larger budget would reach, or that a condition on
    /// its path was left undecided; a caller collecting with `diagnostic::collect` around the
    /// search still receives every diagnostic.
    pub diagnostics: Vec<BackendDiagnostic>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum IncompleteSearch {
    ResultBound,
    DepthBound(SearchState),
    BreadthBound(Vec<SearchState>),
    Indeterminate {
        state: SearchState,
        reason: IndeterminateReason,
    },
    Cancelled(SearchState),
    Simplification {
        state: SearchState,
        error: SimplificationError,
    },
    Match {
        state: SearchState,
        substitution: Substitution,
        remainder: Vec<(crate::term::Term, crate::term::Term)>,
    },
    Smt {
        state: SearchState,
        error: SmtError,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SearchResult {
    pub states: Vec<SearchState>,
    pub effects: Vec<BuiltinEffect>,
    pub incomplete: Vec<IncompleteSearch>,
}

impl SearchResult {
    pub const fn modality(&self) -> ResultModality {
        ResultModality::StateSet
    }
}

/// One acyclic execution path selected by a path-sensitive search.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PathWitness {
    /// Ordered semantic transition identities from the initial state to `pattern`.
    pub id: Vec<TransitionId>,
    pub pattern: Pattern,
    pub depth: u64,
    /// The path's rewrite, remainder, and arrival-local simplification trace entries.
    pub trace: Vec<TraceEntry>,
    /// Ordered structured events retained for this witness.
    pub observations: Vec<ObservationEvent>,
    /// The backend diagnostics of the work this path went through, as for
    /// [`SearchState::diagnostics`]; each witness carries its own path's list.
    pub diagnostics: Vec<BackendDiagnostic>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PathSearchResult {
    pub witnesses: Vec<PathWitness>,
    pub effects: Vec<BuiltinEffect>,
    pub incomplete: Vec<IncompleteSearch>,
}

impl PathSearchResult {
    pub const fn modality(&self) -> ResultModality {
        ResultModality::PathSet
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SearchMatch {
    pub substitution: Substitution,
    pub constraints: Vec<Predicate>,
    pub state: SearchState,
    /// The backend diagnostics of matching `state` against the target pattern (the match
    /// condition's simplification), each distinct diagnostic once, in emission order. They are
    /// facts about this match, kept apart from the diagnostics of the state's path
    /// (`state.diagnostics`).
    pub diagnostics: Vec<BackendDiagnostic>,
}

/// The condition under which a subject is an instance of a search pattern.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PatternMatch {
    pub substitution: Substitution,
    pub constraints: Vec<Predicate>,
}

/// A pattern match which could not be decided by the available simplifier and solver.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PatternMatchError {
    Indeterminate {
        substitution: Substitution,
        remainder: Vec<(crate::term::Term, crate::term::Term)>,
    },
    Simplification(SimplificationError),
    Smt(SmtError),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PatternSearchResult {
    pub matches: Vec<SearchMatch>,
    pub effects: Vec<BuiltinEffect>,
    pub incomplete: Vec<IncompleteSearch>,
}

impl PatternSearchResult {
    pub const fn modality(&self) -> ResultModality {
        ResultModality::StateSet
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PathSearchMatch {
    pub substitution: Substitution,
    pub constraints: Vec<Predicate>,
    pub witness: PathWitness,
    /// The backend diagnostics of matching the witness against the target pattern, kept apart
    /// from the witness path's own (`witness.diagnostics`), as for [`SearchMatch::diagnostics`].
    pub diagnostics: Vec<BackendDiagnostic>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PatternPathSearchResult {
    pub matches: Vec<PathSearchMatch>,
    pub effects: Vec<BuiltinEffect>,
    pub incomplete: Vec<IncompleteSearch>,
}

impl PatternPathSearchResult {
    pub const fn modality(&self) -> ResultModality {
        ResultModality::PathSet
    }
}

/// Match a constrained pattern against each alternative in a disjunction.
pub fn match_disjunction(
    definition: &BackendDefinition,
    target: &Pattern,
    subjects: &[Pattern],
) -> Result<Vec<PatternMatch>, PatternMatchError> {
    match_disjunction_using(
        definition,
        target,
        subjects,
        SimplificationOptions::default(),
        &NoSolver,
        true,
    )
}

/// Match a constrained pattern against each alternative using the supplied SMT solver.
pub fn match_disjunction_with_solver(
    definition: &BackendDefinition,
    target: &Pattern,
    subjects: &[Pattern],
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Result<Vec<PatternMatch>, PatternMatchError> {
    match_disjunction_using(definition, target, subjects, options, solver, false)
}

fn match_disjunction_using(
    definition: &BackendDefinition,
    target: &Pattern,
    subjects: &[Pattern],
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
    retain_unknown: bool,
) -> Result<Vec<PatternMatch>, PatternMatchError> {
    let _span = measure::algorithm_span(Algorithm::BackendSearchPatterns);
    let output_variables = pattern_variables(target);
    let mut matches = Vec::new();
    for subject in subjects {
        let Some(found) = match_pattern_with_variables(
            definition,
            target,
            subject,
            &output_variables,
            options,
            solver,
            retain_unknown,
        )?
        else {
            continue;
        };
        if !matches.contains(&found) {
            matches.push(found);
        }
    }
    Ok(matches)
}

pub fn search_graph(
    definition: &BackendDefinition,
    initial: Pattern,
    options: SearchOptions,
) -> SearchResult {
    search_graph_with_solver(definition, initial, options, &NoSolver)
}

pub fn search_graph_with_solver(
    definition: &BackendDefinition,
    initial: Pattern,
    options: SearchOptions,
    solver: &dyn SmtSolver,
) -> SearchResult {
    search_graph_with_solver_and_observer(definition, initial, options, solver, |_| {})
}

/// Search with branch-local structured transition observation enabled.
pub fn search_graph_observed(
    definition: &BackendDefinition,
    initial: Pattern,
    options: SearchOptions,
    observation: &ObservationOptions,
) -> SearchResult {
    search_graph_observed_with_solver(definition, initial, options, &NoSolver, observation)
}

/// Search with structured observation and the supplied SMT solver.
pub fn search_graph_observed_with_solver(
    definition: &BackendDefinition,
    initial: Pattern,
    options: SearchOptions,
    solver: &dyn SmtSolver,
    observation: &ObservationOptions,
) -> SearchResult {
    search_graph_using(
        definition,
        vec![initial],
        options,
        solver,
        Some(observation),
        |_| {},
    )
}

pub fn search_graph_with_solver_and_observer(
    definition: &BackendDefinition,
    initial: Pattern,
    options: SearchOptions,
    solver: &dyn SmtSolver,
    mut observe: impl FnMut(&BuiltinEffect),
) -> SearchResult {
    search_graph_using(
        definition,
        vec![initial],
        options,
        solver,
        None,
        &mut observe,
    )
}

pub fn search_graph_disjunction_with_solver_and_observer(
    definition: &BackendDefinition,
    initial: Vec<Pattern>,
    options: SearchOptions,
    solver: &dyn SmtSolver,
    mut observe: impl FnMut(&BuiltinEffect),
) -> SearchResult {
    search_graph_using(definition, initial, options, solver, None, &mut observe)
}

fn search_graph_using(
    definition: &BackendDefinition,
    initial: Vec<Pattern>,
    options: SearchOptions,
    solver: &dyn SmtSolver,
    observation: Option<&ObservationOptions>,
    observe: impl FnMut(&BuiltinEffect),
) -> SearchResult {
    search_graph_collecting(
        definition,
        initial,
        options,
        solver,
        observation,
        observe,
        |_| false,
    )
}

#[allow(clippy::too_many_arguments)]
fn search_graph_collecting(
    definition: &BackendDefinition,
    initial: Vec<Pattern>,
    options: SearchOptions,
    solver: &dyn SmtSolver,
    observation: Option<&ObservationOptions>,
    mut observe: impl FnMut(&BuiltinEffect),
    mut pattern_bound_reached: impl FnMut(&SearchState) -> bool,
) -> SearchResult {
    let _span = measure::algorithm_span(Algorithm::BackendSearchConfigurations);
    let mut observation_log = ObservationLog::default();
    let request_diagnostics = PathDiagnostics::new_request();
    let mut pending = initial
        .into_iter()
        .map(|pattern| SearchWorkState {
            state: SearchState {
                pattern,
                depth: 0,
                trace: Vec::new(),
                branch: Vec::new(),
                observations: Vec::new(),
                diagnostics: Vec::new(),
            },
            observation: None,
            diagnostics: request_diagnostics.empty_like(),
            kind: QueuedStateKind::Rewritable,
        })
        .collect::<VecDeque<_>>();
    let mut states = Vec::new();
    let mut effects = Vec::new();
    let mut incomplete = Vec::new();
    let mut fresh_counter = 0;
    // Kore's execution graph recombines branches that reach the same configuration at the same
    // step (Strategy.hs, constructExecutionGraph), and the LLVM backend's search drops any
    // configuration it has already visited: the search is over states, not over paths. Two
    // work states with one simplified pattern at one depth have the same successors, so the
    // second is dropped here, which bounds the work per step by the number of distinct
    // configurations rather than by the number of interleavings that reach them.
    let mut expanded: HashSet<(u64, Pattern, bool)> = HashSet::new();

    let mut validated = VecDeque::with_capacity(pending.len());
    // Invariant: `validated` holds, in queue order, the popped states without a surviving macro or alias symbol, and `incomplete` one entry per other popped state; nothing is pushed onto `pending`, so each initial state is popped once.
    while let Some(work) = pending.pop_front() {
        if let Some(symbol) = work.state.pattern.macro_or_alias_symbol() {
            incomplete.push(rewrite_incomplete(
                work.materialize(&observation_log),
                IndeterminateReason::SurvivingMacroOrAlias { symbol },
            ));
        } else {
            validated.push_back(work);
        }
    }
    pending = validated;
    if pending.is_empty() && !incomplete.is_empty() {
        return SearchResult {
            states,
            effects,
            incomplete,
        };
    }

    if options.max_breadth == Some(0) {
        incomplete.push(IncompleteSearch::BreadthBound(
            pending
                .drain(..)
                .map(|work| work.materialize(&observation_log))
                .collect(),
        ));
        return SearchResult {
            states,
            effects,
            incomplete,
        };
    }

    if options.max_results == Some(0) {
        incomplete.push(IncompleteSearch::ResultBound);
        return SearchResult {
            states,
            effects,
            incomplete,
        };
    }

    // `pending` is FIFO, so popped depths never decrease; `expanded` holds every
    // `(depth, simplified pattern)` expanded so far, so a configuration is expanded once per depth.
    // Invariant: `pending` holds unexpanded states no deeper than `max_depth`; `states` only grows.
    while let Some(work) = pending.pop_front() {
        if cancellation_requested() {
            incomplete.push(IncompleteSearch::Cancelled(
                work.materialize(&observation_log),
            ));
            break;
        }
        let SearchWorkState {
            mut state,
            observation: mut observation_head,
            mut diagnostics,
            kind,
        } = work;
        let is_rewritable = matches!(kind, QueuedStateKind::Rewritable);
        if let Some(symbol) = state.pattern.macro_or_alias_symbol() {
            incomplete.push(rewrite_incomplete(
                materialize_search_state(state, observation_head, &diagnostics, &observation_log),
                IndeterminateReason::SurvivingMacroOrAlias { symbol },
            ));
            continue;
        }
        // The state's own constraint and term simplification is on its path: every result,
        // incomplete entry and successor derived from this state carries it.
        let (simplified_constraints, emitted) = diagnostic::collect(|| {
            simplify_predicates_with_solver(
                definition,
                &state.pattern.constraints,
                &[],
                SimplificationOptions::keep_partial(options.max_simplification_iterations),
                solver,
            )
        });
        diagnostics.extend(&emitted);
        match simplified_constraints {
            Ok(constraints) => state.pattern.constraints = constraints,
            Err(error) => {
                incomplete.push(simplification_incomplete(
                    materialize_search_state(
                        state,
                        observation_head,
                        &diagnostics,
                        &observation_log,
                    ),
                    error,
                ));
                continue;
            }
        }
        let pattern_before_simplification = state.pattern.clone();
        let (simplified_term, emitted) = diagnostic::collect(|| {
            simplify_with_solver(
                definition,
                &state.pattern.term,
                &state.pattern.constraints,
                SimplificationOptions::keep_partial(options.max_simplification_iterations),
                solver,
            )
        });
        diagnostics.extend(&emitted);
        match simplified_term {
            Ok(simplified) => {
                state.pattern.term = simplified.term;
                state.pattern.constraints.extend(simplified.constraints);
                observation_head = observation_log.append_simplification(
                    observation_head,
                    definition,
                    pattern_before_simplification,
                    &state.pattern,
                    &simplified.applied_rules,
                    &simplified.effects,
                    observation,
                );
                record_effects(
                    &mut effects,
                    simplified.effects.iter().cloned(),
                    &mut observe,
                );
                state
                    .trace
                    .extend(
                        simplified
                            .applied_rules
                            .into_iter()
                            .map(|unique_id| TraceEntry {
                                depth: state.depth,
                                kind: TraceKind::Simplification,
                                label: None,
                                unique_id,
                            }),
                    );
            }
            Err(error) => {
                incomplete.push(simplification_incomplete(
                    materialize_search_state(
                        state,
                        observation_head,
                        &diagnostics,
                        &observation_log,
                    ),
                    error,
                ));
                continue;
            }
        }

        // Kore's Simplify primitive turns a false-constrained configuration into a Bottom node,
        // which has no program state and cannot be selected by a search strategy.
        if predicates_truth(&state.pattern.constraints) == Truth::False {
            continue;
        }
        // A duplicate takes its own path's diagnostics with it: the state kept for this key
        // reports the path recorded first, like its trace.
        if !expanded.insert((state.depth, state.pattern.clone(), is_rewritable)) {
            measure::bump(Counter::SearchStatesDeduplicated);
            continue;
        }
        let at_depth_bound = state.depth >= options.max_depth;
        let is_result = selects_reachable_state(options.search_type, state.depth)
            || (options.search_type == SearchType::Final && at_depth_bound);
        let retention = if is_result {
            externalise_result(
                definition,
                state.clone(),
                observation_head,
                diagnostics.clone(),
                options.max_simplification_iterations,
                solver,
                &mut effects,
                &mut observe,
                &mut incomplete,
                &mut observation_log,
                observation,
            )
            .map(|result| {
                retain_state_result(
                    &mut states,
                    result,
                    options.max_results,
                    &mut pattern_bound_reached,
                )
            })
            .unwrap_or(StateRetention::Continue)
        } else {
            StateRetention::Continue
        };
        match retention {
            StateRetention::ResultBound => {
                let truncated = !pending.is_empty()
                    || (options.search_type != SearchType::Final
                        && state_may_expand(
                            definition,
                            &state,
                            is_rewritable,
                            options,
                            &mut fresh_counter,
                            solver,
                        ));
                if truncated {
                    incomplete.push(IncompleteSearch::ResultBound);
                }
                break;
            }
            StateRetention::PatternBound
                if !pending.is_empty()
                    || (options.search_type != SearchType::Final
                        && state_may_expand(
                            definition,
                            &state,
                            is_rewritable,
                            options,
                            &mut fresh_counter,
                            solver,
                        )) =>
            {
                incomplete.push(IncompleteSearch::ResultBound);
                break;
            }
            _ => {}
        }
        if options.search_type == SearchType::One && state.depth == 1 {
            continue;
        }
        if at_depth_bound {
            incomplete.push(IncompleteSearch::DepthBound(materialize_search_state(
                state,
                observation_head,
                &diagnostics,
                &observation_log,
            )));
            continue;
        }

        let (rewrite, step_diagnostics) = step_search_state(
            definition,
            &state.pattern,
            kind,
            &mut fresh_counter,
            options,
            solver,
        );
        // See `step_observed_cancellation`.
        if step_observed_cancellation() {
            diagnostics.extend(&step_diagnostics);
            incomplete.push(IncompleteSearch::Cancelled(materialize_search_state(
                state,
                observation_head,
                &diagnostics,
                &observation_log,
            )));
            continue;
        }
        if halts(&rewrite) {
            diagnostics.extend(&step_diagnostics);
        }
        match rewrite {
            RewriteResult::Stuck(pattern) => {
                if options.search_type != SearchType::Final {
                    continue;
                }
                state.pattern = pattern;
                let retention = externalise_result(
                    definition,
                    state,
                    observation_head,
                    diagnostics,
                    options.max_simplification_iterations,
                    solver,
                    &mut effects,
                    &mut observe,
                    &mut incomplete,
                    &mut observation_log,
                    observation,
                )
                .map(|result| {
                    retain_state_result(
                        &mut states,
                        result,
                        options.max_results,
                        &mut pattern_bound_reached,
                    )
                })
                .unwrap_or(StateRetention::Continue);
                match retention {
                    StateRetention::ResultBound => {
                        if !pending.is_empty() {
                            incomplete.push(IncompleteSearch::ResultBound);
                        }
                        break;
                    }
                    StateRetention::PatternBound if !pending.is_empty() => {
                        incomplete.push(IncompleteSearch::ResultBound);
                        break;
                    }
                    _ => {}
                }
            }
            RewriteResult::Trivial(_, _) | RewriteResult::Vacuous(_) => {}
            RewriteResult::Indeterminate { pattern, reason } => {
                state.pattern = pattern;
                incomplete.push(rewrite_incomplete(
                    materialize_search_state(
                        state,
                        observation_head,
                        &diagnostics,
                        &observation_log,
                    ),
                    reason,
                ));
            }
            RewriteResult::Simplification { pattern, error } => {
                state.pattern = pattern;
                incomplete.push(simplification_incomplete(
                    materialize_search_state(
                        state,
                        observation_head,
                        &diagnostics,
                        &observation_log,
                    ),
                    error,
                ));
            }
            RewriteResult::Finished(applied) => {
                record_applied_effects(&mut effects, &applied, &mut observe);
                pending.push_back(next_search_work_state(
                    definition,
                    state.depth,
                    state.trace,
                    observation_head,
                    diagnostics,
                    applied,
                    &mut observation_log,
                    observation,
                ));
                if observed_search_breadth_exceeded(
                    &mut pending,
                    &mut incomplete,
                    options.max_breadth,
                    &observation_log,
                ) {
                    break;
                }
            }
            RewriteResult::Branch {
                branches,
                remainder,
                ..
            } => {
                for applied in branches {
                    record_applied_effects(&mut effects, &applied, &mut observe);
                    pending.push_back(next_search_work_state(
                        definition,
                        state.depth,
                        state.trace.clone(),
                        observation_head,
                        diagnostics.clone(),
                        applied,
                        &mut observation_log,
                        observation,
                    ));
                }
                if let Some(remainder) = remainder {
                    record_effects(
                        &mut effects,
                        remainder.effects.iter().cloned(),
                        &mut observe,
                    );
                    let remaining = remaining_search_work_state(
                        definition,
                        state.depth,
                        state.trace,
                        observation_head,
                        diagnostics,
                        state.pattern,
                        remainder,
                        &mut observation_log,
                        observation,
                    );
                    pending.push_back(remaining);
                }
                if observed_search_breadth_exceeded(
                    &mut pending,
                    &mut incomplete,
                    options.max_breadth,
                    &observation_log,
                ) {
                    break;
                }
            }
        }
    }

    SearchResult {
        states,
        effects,
        incomplete,
    }
}

#[derive(Clone)]
struct SearchWorkState {
    state: SearchState,
    observation: ObservationHead,
    /// The diagnostics of this state's path so far, shared with the paths it forks into;
    /// materialised into `SearchState::diagnostics` when the state is reported.
    diagnostics: PathDiagnostics,
    kind: QueuedStateKind,
}

#[derive(Clone)]
enum QueuedStateKind {
    Rewritable,
    Remaining(Option<UndecidedStep>),
}

impl SearchWorkState {
    fn materialize(self, observation_log: &ObservationLog) -> SearchState {
        materialize_search_state(
            self.state,
            self.observation,
            &self.diagnostics,
            observation_log,
        )
    }
}

fn materialize_search_state(
    mut state: SearchState,
    observation: ObservationHead,
    diagnostics: &PathDiagnostics,
    observation_log: &ObservationLog,
) -> SearchState {
    (state.branch, state.observations) = observation_log.materialize(observation);
    state.diagnostics = diagnostics.to_vec();
    state
}

/// One rewrite step of a work state, with the diagnostics it emitted: a `Finished` or `Branch`
/// step has already attributed them to its candidates (`AppliedRule::diagnostics`,
/// `RemainderBranch::diagnostics`), so the collection is for a step that ends the state's
/// exploration ([`halts`]) or is cut off by a cancellation, whose entry carries the whole step.
fn step_search_state(
    definition: &BackendDefinition,
    pattern: &Pattern,
    kind: QueuedStateKind,
    fresh_counter: &mut u64,
    options: SearchOptions,
    solver: &dyn SmtSolver,
) -> (RewriteResult, Vec<BackendDiagnostic>) {
    diagnostic::collect(|| match kind {
        QueuedStateKind::Rewritable => rewrite_step_with_options(
            definition,
            pattern,
            fresh_counter,
            SimplificationOptions::keep_partial(options.max_simplification_iterations),
            solver,
        ),
        QueuedStateKind::Remaining(None) => RewriteResult::Stuck(pattern.clone()),
        QueuedStateKind::Remaining(Some(undecided)) => undecided.into_result(pattern.clone()),
    })
}

/// Whether a step result ends the state's exploration without a successor, so that the step's
/// work belongs to the state's own path.
const fn halts(rewrite: &RewriteResult) -> bool {
    !matches!(
        rewrite,
        RewriteResult::Finished(_) | RewriteResult::Branch { .. }
    )
}

/// Externalise a search result in the simplifier's normal form
/// (`rewrite::simplify_leaf_pattern`), materializing its observations.
///
/// The work state that continues the search keeps its loop-head constraints as path knowledge;
/// only the reported copy is simplified. `None` is a result whose constraints simplify to
/// `\bottom`: an empty state is no result, as it is none at the loop head. A failed
/// simplification reports the unsimplified state in `incomplete` instead of a result.
///
/// A simplification that returns while the request is cancelled is not a result either. The
/// simplifier keeps a constraint whose validity the solver leaves unknown, and once the request
/// is cancelled every solver query answers unknown, so a constraint that refutes the state may
/// have been kept only because of the cancellation. Publishing that copy would report a state
/// that is not known to be reachable as part of a complete answer; the state's exploration is
/// reported as cancelled instead.
///
/// The externalisation's diagnostics are on the reported entry only (the result, or the
/// incomplete entry that replaces it), not on `diagnostics`' path, which the work state that
/// continues the search keeps: its successors are not derived from the reported copy.
#[allow(clippy::too_many_arguments)]
fn externalise_result(
    definition: &BackendDefinition,
    mut state: SearchState,
    mut observation: ObservationHead,
    mut diagnostics: PathDiagnostics,
    max_iterations: usize,
    solver: &dyn SmtSolver,
    effects: &mut Vec<BuiltinEffect>,
    observe: &mut impl FnMut(&BuiltinEffect),
    incomplete: &mut Vec<IncompleteSearch>,
    observation_log: &mut ObservationLog,
    observation_options: Option<&ObservationOptions>,
) -> Option<SearchState> {
    let (simplified, emitted) = diagnostic::collect(|| {
        simplify_result_pattern(
            definition,
            &state.pattern,
            max_iterations,
            solver,
            state.depth,
            &mut state.trace,
            Some(&mut observation),
            observation_log,
            observation_options,
        )
    });
    diagnostics.extend(&emitted);
    match simplified {
        Ok(simplified) if predicates_truth(&simplified.pattern.constraints) == Truth::False => {
            record_effects(effects, simplified.effects, observe);
            None
        }
        Ok(simplified) if cancellation_requested() => {
            record_effects(effects, simplified.effects, observe);
            incomplete.push(IncompleteSearch::Cancelled(materialize_search_state(
                state,
                observation,
                &diagnostics,
                observation_log,
            )));
            None
        }
        Ok(simplified) => {
            record_effects(effects, simplified.effects, observe);
            state.pattern = simplified.pattern;
            Some(materialize_search_state(
                state,
                observation,
                &diagnostics,
                observation_log,
            ))
        }
        Err(error) => {
            incomplete.push(simplification_incomplete(
                materialize_search_state(state, observation, &diagnostics, observation_log),
                error,
            ));
            None
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn next_search_work_state(
    definition: &BackendDefinition,
    depth: u64,
    trace: Vec<TraceEntry>,
    observation: ObservationHead,
    mut diagnostics: PathDiagnostics,
    applied: AppliedRule,
    observation_log: &mut ObservationLog,
    observation_options: Option<&ObservationOptions>,
) -> SearchWorkState {
    diagnostics.extend(&applied.diagnostics);
    let mut observation = observation;
    for simplification in &applied.remainder_simplifications {
        observation = observation_log.append_simplification(
            observation,
            definition,
            simplification.before.clone(),
            &simplification.after,
            &simplification.applied_rules,
            &simplification.effects,
            observation_options,
        );
    }
    let observation = observation_log.append_applied(observation, &applied, observation_options);
    SearchWorkState {
        state: next_state(depth, trace, applied),
        observation,
        diagnostics,
        kind: QueuedStateKind::Rewritable,
    }
}

#[allow(clippy::too_many_arguments)]
fn remaining_search_work_state(
    definition: &BackendDefinition,
    depth: u64,
    trace: Vec<TraceEntry>,
    observation: ObservationHead,
    mut diagnostics: PathDiagnostics,
    before: Pattern,
    remainder: RemainderBranch,
    observation_log: &mut ObservationLog,
    observation_options: Option<&ObservationOptions>,
) -> SearchWorkState {
    diagnostics.extend(&remainder.diagnostics);
    let (observation, kind) = replay_search_remainder(
        definition,
        observation,
        before,
        &remainder,
        observation_log,
        observation_options,
    );
    SearchWorkState {
        state: remaining_state(depth, trace, remainder),
        observation,
        diagnostics,
        kind,
    }
}

fn observed_search_breadth_exceeded(
    pending: &mut VecDeque<SearchWorkState>,
    incomplete: &mut Vec<IncompleteSearch>,
    max_breadth: Option<usize>,
    observation_log: &ObservationLog,
) -> bool {
    if !max_breadth.is_some_and(|bound| pending.len() > bound) {
        return false;
    }
    incomplete.push(IncompleteSearch::BreadthBound(
        pending
            .drain(..)
            .map(|work| work.materialize(observation_log))
            .collect(),
    ));
    true
}

/// Search for one witness per distinct acyclic semantic path.
///
/// Unlike [`search_graph`], this modality does not deduplicate converging result patterns.
/// `max_results` therefore counts witnesses rather than unique states.
pub fn search_paths(
    definition: &BackendDefinition,
    initial: Pattern,
    options: SearchOptions,
) -> PathSearchResult {
    search_paths_with_solver(definition, initial, options, &NoSolver)
}

/// Search for acyclic path witnesses using the supplied SMT solver.
pub fn search_paths_with_solver(
    definition: &BackendDefinition,
    initial: Pattern,
    options: SearchOptions,
    solver: &dyn SmtSolver,
) -> PathSearchResult {
    search_paths_using(definition, initial, options, solver, None)
}

/// Search for observed acyclic path witnesses.
pub fn search_paths_observed(
    definition: &BackendDefinition,
    initial: Pattern,
    options: SearchOptions,
    observation: &ObservationOptions,
) -> PathSearchResult {
    search_paths_observed_with_solver(definition, initial, options, &NoSolver, observation)
}

/// Search for observed acyclic path witnesses using the supplied SMT solver.
pub fn search_paths_observed_with_solver(
    definition: &BackendDefinition,
    initial: Pattern,
    options: SearchOptions,
    solver: &dyn SmtSolver,
    observation: &ObservationOptions,
) -> PathSearchResult {
    search_paths_using(definition, initial, options, solver, Some(observation))
}

fn search_paths_using(
    definition: &BackendDefinition,
    initial: Pattern,
    options: SearchOptions,
    solver: &dyn SmtSolver,
    observation: Option<&ObservationOptions>,
) -> PathSearchResult {
    search_paths_collecting(definition, initial, options, solver, observation, |_| false)
}

fn search_paths_collecting(
    definition: &BackendDefinition,
    initial: Pattern,
    options: SearchOptions,
    solver: &dyn SmtSolver,
    observation: Option<&ObservationOptions>,
    mut pattern_bound_reached: impl FnMut(&PathWitness) -> bool,
) -> PathSearchResult {
    let _span = measure::algorithm_span(Algorithm::BackendSearchPaths);
    let mut observation_log = ObservationLog::default();
    let mut pending = VecDeque::from([PathSearchState {
        state: SearchState {
            pattern: initial,
            depth: 0,
            trace: Vec::new(),
            branch: Vec::new(),
            observations: Vec::new(),
            diagnostics: Vec::new(),
        },
        id: Vec::new(),
        visited: Vec::new(),
        observation: None,
        diagnostics: PathDiagnostics::new_request(),
        kind: QueuedStateKind::Rewritable,
    }]);
    let mut witnesses = Vec::new();
    let mut effects = Vec::new();
    let mut incomplete = Vec::new();
    let mut fresh_counter = 0;

    let mut validated = VecDeque::with_capacity(pending.len());
    // Invariant: `validated` holds, in queue order, the popped paths without a surviving macro or alias symbol, and `incomplete` one entry per other popped path; nothing is pushed onto `pending`, so the initial path is popped once.
    while let Some(path) = pending.pop_front() {
        if let Some(symbol) = path.state.pattern.macro_or_alias_symbol() {
            incomplete.push(rewrite_incomplete(
                path.materialize_state(&observation_log),
                IndeterminateReason::SurvivingMacroOrAlias { symbol },
            ));
        } else {
            validated.push_back(path);
        }
    }
    pending = validated;
    if pending.is_empty() && !incomplete.is_empty() {
        return PathSearchResult {
            witnesses,
            effects,
            incomplete,
        };
    }

    if options.max_breadth == Some(0) {
        incomplete.push(IncompleteSearch::BreadthBound(
            pending
                .drain(..)
                .map(|path| path.materialize_state(&observation_log))
                .collect(),
        ));
        return PathSearchResult {
            witnesses,
            effects,
            incomplete,
        };
    }

    if options.max_results == Some(0) {
        incomplete.push(IncompleteSearch::ResultBound);
        return PathSearchResult {
            witnesses,
            effects,
            incomplete,
        };
    }

    // Invariant: a queued path's `visited` is exactly its own patterns, so paths stay simple.
    while let Some(mut path) = pending.pop_front() {
        if cancellation_requested() {
            incomplete.push(IncompleteSearch::Cancelled(
                path.materialize_state(&observation_log),
            ));
            break;
        }
        let is_rewritable = matches!(path.kind, QueuedStateKind::Rewritable);
        if let Some(symbol) = path.state.pattern.macro_or_alias_symbol() {
            incomplete.push(rewrite_incomplete(
                path.materialize_state(&observation_log),
                IndeterminateReason::SurvivingMacroOrAlias { symbol },
            ));
            continue;
        }
        // The path's own simplification of this state is on the path: every witness, incomplete
        // entry and extension derived from it carries it.
        let (simplified_constraints, emitted) = diagnostic::collect(|| {
            simplify_predicates_with_solver(
                definition,
                &path.state.pattern.constraints,
                &[],
                SimplificationOptions::keep_partial(options.max_simplification_iterations),
                solver,
            )
        });
        path.diagnostics.extend(&emitted);
        match simplified_constraints {
            Ok(constraints) => path.state.pattern.constraints = constraints,
            Err(error) => {
                incomplete.push(simplification_incomplete(
                    path.materialize_state(&observation_log),
                    error,
                ));
                continue;
            }
        }
        let pattern_before_simplification = path.state.pattern.clone();
        let (simplified_term, emitted) = diagnostic::collect(|| {
            simplify_with_solver(
                definition,
                &path.state.pattern.term,
                &path.state.pattern.constraints,
                SimplificationOptions::keep_partial(options.max_simplification_iterations),
                solver,
            )
        });
        path.diagnostics.extend(&emitted);
        match simplified_term {
            Ok(simplified) => {
                path.state.pattern.term = simplified.term;
                path.state
                    .pattern
                    .constraints
                    .extend(simplified.constraints);
                path.observation = observation_log.append_simplification(
                    path.observation,
                    definition,
                    pattern_before_simplification,
                    &path.state.pattern,
                    &simplified.applied_rules,
                    &simplified.effects,
                    observation,
                );
                effects.extend(simplified.effects.iter().cloned());
                path.state
                    .trace
                    .extend(
                        simplified
                            .applied_rules
                            .into_iter()
                            .map(|unique_id| TraceEntry {
                                depth: path.state.depth,
                                kind: TraceKind::Simplification,
                                label: None,
                                unique_id,
                            }),
                    );
            }
            Err(error) => {
                incomplete.push(simplification_incomplete(
                    path.materialize_state(&observation_log),
                    error,
                ));
                continue;
            }
        }

        if predicates_truth(&path.state.pattern.constraints) == Truth::False {
            continue;
        }
        if path
            .visited
            .contains(&(path.state.pattern.clone(), is_rewritable))
        {
            continue;
        }
        path.visited
            .push((path.state.pattern.clone(), is_rewritable));

        let at_depth_bound = path.state.depth >= options.max_depth;
        let is_result = selects_reachable_state(options.search_type, path.state.depth)
            || (options.search_type == SearchType::Final && at_depth_bound);
        let retention = is_result.then(|| {
            retain_witness(
                definition,
                &mut witnesses,
                &path,
                options,
                solver,
                &mut effects,
                &mut incomplete,
                &mut observation_log,
                observation,
                &mut pattern_bound_reached,
            )
        });
        match retention {
            Some(WitnessRetention::ResultBound) => {
                incomplete.push(IncompleteSearch::ResultBound);
                break;
            }
            Some(WitnessRetention::PatternBound)
                if !pending.is_empty()
                    || (options.search_type != SearchType::Final
                        && state_may_expand(
                            definition,
                            &path.state,
                            is_rewritable,
                            options,
                            &mut fresh_counter,
                            solver,
                        )) =>
            {
                incomplete.push(IncompleteSearch::ResultBound);
                break;
            }
            _ => {}
        }
        if options.search_type == SearchType::One && path.state.depth == 1 {
            continue;
        }
        if at_depth_bound {
            incomplete.push(IncompleteSearch::DepthBound(
                path.materialize_state(&observation_log),
            ));
            continue;
        }

        let (rewrite, step_diagnostics) = step_search_state(
            definition,
            &path.state.pattern,
            path.kind.clone(),
            &mut fresh_counter,
            options,
            solver,
        );
        // See `step_observed_cancellation`.
        if step_observed_cancellation() {
            path.diagnostics.extend(&step_diagnostics);
            incomplete.push(IncompleteSearch::Cancelled(
                path.materialize_state(&observation_log),
            ));
            continue;
        }
        if halts(&rewrite) {
            path.diagnostics.extend(&step_diagnostics);
        }
        match rewrite {
            RewriteResult::Stuck(pattern) => {
                path.state.pattern = pattern;
                let retention = (options.search_type == SearchType::Final).then(|| {
                    retain_witness(
                        definition,
                        &mut witnesses,
                        &path,
                        options,
                        solver,
                        &mut effects,
                        &mut incomplete,
                        &mut observation_log,
                        observation,
                        &mut pattern_bound_reached,
                    )
                });
                match retention {
                    Some(WitnessRetention::ResultBound) => {
                        incomplete.push(IncompleteSearch::ResultBound);
                        break;
                    }
                    Some(WitnessRetention::PatternBound) if !pending.is_empty() => {
                        incomplete.push(IncompleteSearch::ResultBound);
                        break;
                    }
                    _ => {}
                }
            }
            RewriteResult::Trivial(_, _) | RewriteResult::Vacuous(_) => {}
            RewriteResult::Indeterminate { pattern, reason } => {
                path.state.pattern = pattern;
                incomplete.push(rewrite_incomplete(
                    path.materialize_state(&observation_log),
                    reason,
                ));
            }
            RewriteResult::Simplification { pattern, error } => {
                path.state.pattern = pattern;
                incomplete.push(simplification_incomplete(
                    path.materialize_state(&observation_log),
                    error,
                ));
            }
            RewriteResult::Finished(applied) => {
                effects.extend(
                    applied
                        .remainder_simplifications
                        .iter()
                        .flat_map(|simplification| simplification.effects.iter().cloned()),
                );
                effects.extend(applied.effects.iter().cloned());
                pending.push_back(next_path_state(
                    definition,
                    path,
                    applied,
                    &mut observation_log,
                    observation,
                ));
                if path_search_breadth_exceeded(
                    &mut pending,
                    &mut incomplete,
                    options.max_breadth,
                    &observation_log,
                ) {
                    break;
                }
            }
            RewriteResult::Branch {
                branches,
                remainder,
                ..
            } => {
                for applied in branches {
                    effects.extend(
                        applied
                            .remainder_simplifications
                            .iter()
                            .flat_map(|simplification| simplification.effects.iter().cloned()),
                    );
                    effects.extend(applied.effects.iter().cloned());
                    pending.push_back(next_path_state(
                        definition,
                        path.clone(),
                        applied,
                        &mut observation_log,
                        observation,
                    ));
                }
                if let Some(remainder) = remainder {
                    effects.extend(remainder.effects.iter().cloned());
                    let remaining = remaining_path_state(
                        definition,
                        path,
                        remainder,
                        &mut observation_log,
                        observation,
                    );
                    pending.push_back(remaining);
                }
                if path_search_breadth_exceeded(
                    &mut pending,
                    &mut incomplete,
                    options.max_breadth,
                    &observation_log,
                ) {
                    break;
                }
            }
        }
    }

    PathSearchResult {
        witnesses,
        effects,
        incomplete,
    }
}

#[derive(Clone)]
struct PathSearchState {
    state: SearchState,
    id: Vec<TransitionId>,
    visited: Vec<(Pattern, bool)>,
    observation: ObservationHead,
    /// The diagnostics of this path so far, shared with the paths that extend it.
    diagnostics: PathDiagnostics,
    kind: QueuedStateKind,
}

impl PathSearchState {
    fn materialize_state(self, observation_log: &ObservationLog) -> SearchState {
        materialize_search_state(
            self.state,
            self.observation,
            &self.diagnostics,
            observation_log,
        )
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum WitnessRetention {
    Continue,
    ResultBound,
    PatternBound,
}

/// Retain one externalized path witness and classify any result bound reached there.
///
/// The witness is externalised in the simplifier's normal form (`externalise_result`); an
/// empty witness is not retained and a failed simplification is reported as incomplete.
#[allow(clippy::too_many_arguments)]
fn retain_witness(
    definition: &BackendDefinition,
    witnesses: &mut Vec<PathWitness>,
    path: &PathSearchState,
    options: SearchOptions,
    solver: &dyn SmtSolver,
    effects: &mut Vec<BuiltinEffect>,
    incomplete: &mut Vec<IncompleteSearch>,
    observation_log: &mut ObservationLog,
    observation_options: Option<&ObservationOptions>,
    pattern_bound_reached: &mut impl FnMut(&PathWitness) -> bool,
) -> WitnessRetention {
    if options
        .max_results
        .is_some_and(|limit| witnesses.len() >= limit)
    {
        return WitnessRetention::ResultBound;
    }
    if let Some(state) = externalise_result(
        definition,
        path.state.clone(),
        path.observation,
        path.diagnostics.clone(),
        options.max_simplification_iterations,
        solver,
        effects,
        &mut |_| {},
        incomplete,
        observation_log,
        observation_options,
    ) {
        let witness = PathWitness {
            id: path.id.clone(),
            pattern: state.pattern,
            depth: state.depth,
            trace: state.trace,
            observations: state.observations,
            diagnostics: state.diagnostics,
        };
        let pattern_bound_reached = pattern_bound_reached(&witness);
        witnesses.push(witness);
        if pattern_bound_reached {
            return WitnessRetention::PatternBound;
        }
    }
    WitnessRetention::Continue
}

fn next_path_state(
    definition: &BackendDefinition,
    mut path: PathSearchState,
    applied: AppliedRule,
    observation_log: &mut ObservationLog,
    observation_options: Option<&ObservationOptions>,
) -> PathSearchState {
    path.diagnostics.extend(&applied.diagnostics);
    path.id.push(TransitionId {
        rule: applied.unique_id.clone(),
        target: PatternDigest::of(&applied.pattern),
    });
    for simplification in &applied.remainder_simplifications {
        path.observation = observation_log.append_simplification(
            path.observation,
            definition,
            simplification.before.clone(),
            &simplification.after,
            &simplification.applied_rules,
            &simplification.effects,
            observation_options,
        );
    }
    path.observation =
        observation_log.append_applied(path.observation, &applied, observation_options);
    path.state = next_state(path.state.depth, path.state.trace, applied);
    path.kind = QueuedStateKind::Rewritable;
    path
}

fn remaining_path_state(
    definition: &BackendDefinition,
    mut path: PathSearchState,
    remainder: RemainderBranch,
    observation_log: &mut ObservationLog,
    observation_options: Option<&ObservationOptions>,
) -> PathSearchState {
    path.diagnostics.extend(&remainder.diagnostics);
    path.id.push(TransitionId {
        rule: format!("remainder:{}", remainder.rule_ids.join(",")),
        target: PatternDigest::of(&remainder.pattern),
    });
    let (observation, kind) = replay_search_remainder(
        definition,
        path.observation,
        path.state.pattern.clone(),
        &remainder,
        observation_log,
        observation_options,
    );
    path.observation = observation;
    path.state = remaining_state(path.state.depth, path.state.trace, remainder);
    path.kind = kind;
    path
}

fn path_search_breadth_exceeded(
    pending: &mut VecDeque<PathSearchState>,
    incomplete: &mut Vec<IncompleteSearch>,
    max_breadth: Option<usize>,
    observation_log: &ObservationLog,
) -> bool {
    if !max_breadth.is_some_and(|bound| pending.len() > bound) {
        return false;
    }
    incomplete.push(IncompleteSearch::BreadthBound(
        pending
            .drain(..)
            .map(|path| path.materialize_state(observation_log))
            .collect(),
    ));
    true
}

/// Search the selected execution states for instances of `target`.
pub fn search_pattern(
    definition: &BackendDefinition,
    initial: Pattern,
    target: &Pattern,
    options: SearchOptions,
) -> PatternSearchResult {
    search_pattern_with_solver(definition, initial, target, options, &NoSolver)
}

pub fn search_pattern_with_solver(
    definition: &BackendDefinition,
    initial: Pattern,
    target: &Pattern,
    options: SearchOptions,
    solver: &dyn SmtSolver,
) -> PatternSearchResult {
    search_pattern_using(definition, vec![initial], target, options, solver, None)
}

pub fn search_pattern_disjunction_with_solver(
    definition: &BackendDefinition,
    initial: Vec<Pattern>,
    target: &Pattern,
    options: SearchOptions,
    solver: &dyn SmtSolver,
) -> PatternSearchResult {
    search_pattern_using(definition, initial, target, options, solver, None)
}

/// Search selected states for a pattern with structured transition observation enabled.
pub fn search_pattern_observed(
    definition: &BackendDefinition,
    initial: Pattern,
    target: &Pattern,
    options: SearchOptions,
    observation: &ObservationOptions,
) -> PatternSearchResult {
    search_pattern_observed_with_solver(
        definition,
        initial,
        target,
        options,
        &NoSolver,
        observation,
    )
}

/// Search selected states for a pattern with observation and the supplied SMT solver.
pub fn search_pattern_observed_with_solver(
    definition: &BackendDefinition,
    initial: Pattern,
    target: &Pattern,
    options: SearchOptions,
    solver: &dyn SmtSolver,
    observation: &ObservationOptions,
) -> PatternSearchResult {
    search_pattern_using(
        definition,
        vec![initial],
        target,
        options,
        solver,
        Some(observation),
    )
}

/// `--bound` promises at most N results, selected from this engine's own BFS
/// match list. Structural ordering is applied only when the CLI externalizes those selected
/// results, so truncation remains a subset of the unbounded BFS list.
/// See docs/compatibility.md#search-results.
fn search_pattern_using(
    definition: &BackendDefinition,
    initial: Vec<Pattern>,
    target: &Pattern,
    options: SearchOptions,
    solver: &dyn SmtSolver,
    observation: Option<&ObservationOptions>,
) -> PatternSearchResult {
    let _span = measure::algorithm_span(Algorithm::BackendSearchPatterns);
    let requested_bound = options.max_results;
    if requested_bound == Some(0) {
        return PatternSearchResult {
            matches: Vec::new(),
            effects: Vec::new(),
            incomplete: vec![IncompleteSearch::ResultBound],
        };
    }
    let graph_options = SearchOptions {
        max_results: None,
        ..options
    };
    let mut matches = Vec::new();
    let mut match_incomplete = Vec::new();
    let output_variables = pattern_variables(target);
    let mut collect_match = |state: &SearchState| {
        let (found, diagnostics) = match_search_result(
            definition,
            target,
            &state.pattern,
            &output_variables,
            options,
            solver,
        );
        let found = match found {
            Ok(Some(found)) => found,
            Ok(None) => return false,
            Err(error) => {
                match_incomplete.push(pattern_match_incomplete(
                    undecided_match_state(state.clone(), &diagnostics),
                    error,
                ));
                return false;
            }
        };

        let found = SearchMatch {
            substitution: found.substitution,
            constraints: found.constraints,
            state: state.clone(),
            diagnostics,
        };
        retain_pattern_match(&mut matches, found, requested_bound)
    };
    let graph = search_graph_collecting(
        definition,
        initial,
        graph_options,
        solver,
        observation,
        |_| {},
        &mut collect_match,
    );
    let incomplete = merge_pattern_incomplete(graph.incomplete, match_incomplete);

    PatternSearchResult {
        matches,
        effects: graph.effects,
        incomplete,
    }
}

/// Search selected path witnesses for instances of `target` without collapsing equal matches.
pub fn search_pattern_paths(
    definition: &BackendDefinition,
    initial: Pattern,
    target: &Pattern,
    options: SearchOptions,
) -> PatternPathSearchResult {
    search_pattern_paths_with_solver(definition, initial, target, options, &NoSolver)
}

/// Search selected path witnesses for instances using the supplied SMT solver.
pub fn search_pattern_paths_with_solver(
    definition: &BackendDefinition,
    initial: Pattern,
    target: &Pattern,
    options: SearchOptions,
    solver: &dyn SmtSolver,
) -> PatternPathSearchResult {
    search_pattern_paths_using(definition, initial, target, options, solver, None)
}

/// Search selected path witnesses for a pattern with structured observation enabled.
pub fn search_pattern_paths_observed(
    definition: &BackendDefinition,
    initial: Pattern,
    target: &Pattern,
    options: SearchOptions,
    observation: &ObservationOptions,
) -> PatternPathSearchResult {
    search_pattern_paths_observed_with_solver(
        definition,
        initial,
        target,
        options,
        &NoSolver,
        observation,
    )
}

/// Search observed path witnesses for a pattern using the supplied SMT solver.
pub fn search_pattern_paths_observed_with_solver(
    definition: &BackendDefinition,
    initial: Pattern,
    target: &Pattern,
    options: SearchOptions,
    solver: &dyn SmtSolver,
    observation: &ObservationOptions,
) -> PatternPathSearchResult {
    search_pattern_paths_using(
        definition,
        initial,
        target,
        options,
        solver,
        Some(observation),
    )
}

fn search_pattern_paths_using(
    definition: &BackendDefinition,
    initial: Pattern,
    target: &Pattern,
    options: SearchOptions,
    solver: &dyn SmtSolver,
    observation: Option<&ObservationOptions>,
) -> PatternPathSearchResult {
    let _span = measure::algorithm_span(Algorithm::BackendSearchPatterns);
    let requested_bound = options.max_results;
    if requested_bound == Some(0) {
        return PatternPathSearchResult {
            matches: Vec::new(),
            effects: Vec::new(),
            incomplete: vec![IncompleteSearch::ResultBound],
        };
    }
    let graph_options = SearchOptions {
        max_results: None,
        ..options
    };
    let mut matches = Vec::new();
    let mut match_incomplete = Vec::new();
    let output_variables = pattern_variables(target);
    let mut collect_match = |witness: &PathWitness| {
        let (found, diagnostics) = match_search_result(
            definition,
            target,
            &witness.pattern,
            &output_variables,
            options,
            solver,
        );
        let found = match found {
            Ok(Some(found)) => found,
            Ok(None) => return false,
            Err(error) => {
                match_incomplete.push(pattern_match_incomplete(
                    undecided_match_state(witness_search_state(witness.clone()), &diagnostics),
                    error,
                ));
                return false;
            }
        };

        matches.push(PathSearchMatch {
            substitution: found.substitution,
            constraints: found.constraints,
            witness: witness.clone(),
            diagnostics,
        });
        requested_bound.is_some_and(|bound| matches.len() >= bound)
    };
    let graph = search_paths_collecting(
        definition,
        initial,
        graph_options,
        solver,
        observation,
        &mut collect_match,
    );
    let incomplete = merge_pattern_incomplete(graph.incomplete, match_incomplete);

    PatternPathSearchResult {
        matches,
        effects: graph.effects,
        incomplete,
    }
}

/// Match one search result against the target pattern, with the diagnostics the match emitted
/// (each distinct diagnostic once, in emission order). They concern the match, not the result's
/// path: a match entry records them apart from its state's or witness's list.
fn match_search_result(
    definition: &BackendDefinition,
    target: &Pattern,
    subject: &Pattern,
    output_variables: &BTreeSet<crate::term::Variable>,
    options: SearchOptions,
    solver: &dyn SmtSolver,
) -> (
    Result<Option<PatternMatch>, PatternMatchError>,
    Vec<BackendDiagnostic>,
) {
    let (found, emitted) = diagnostic::collect(|| {
        match_pattern_with_variables(
            definition,
            target,
            subject,
            output_variables,
            simplification_options(options),
            solver,
            false,
        )
    });
    let mut diagnostics = Vec::new();
    extend_distinct(&mut diagnostics, &emitted);
    (found, diagnostics)
}

/// The state an undecided match reports: its path's diagnostics followed by those of the
/// match that could not be decided. An incomplete entry has no match entry of its own, and the
/// undecided match is the work that entry reports, so its diagnostics travel with the entry.
fn undecided_match_state(mut state: SearchState, diagnostics: &[BackendDiagnostic]) -> SearchState {
    extend_distinct(&mut state.diagnostics, diagnostics);
    state
}

fn witness_search_state(witness: PathWitness) -> SearchState {
    SearchState {
        pattern: witness.pattern,
        depth: witness.depth,
        trace: witness.trace,
        branch: witness.id,
        observations: witness.observations,
        diagnostics: witness.diagnostics,
    }
}

/// Whether the request was cancelled by the time a state's rewrite step returned.
///
/// A step whose solver queries answered unknown because of the cancellation may have kept an
/// equation's or rule's outcome undecided without recording an incomplete entry (the simplifier
/// keeps an undecided constraint and an undecided equation leaves its subject unevaluated), so
/// neither its successors nor a `Stuck` verdict can be trusted as complete. Search arms no step
/// deadline, so the cancellation is its only interruption source, and the state's exploration
/// is reported as cancelled.
fn step_observed_cancellation() -> bool {
    cancellation_requested()
}

/// Classify a simplification failure that ends the exploration of `state`.
///
/// Search arms no step deadline, so request cancellation is its only interruption source. Every
/// interruption signal the simplifier can raise therefore reports the cancellation: the
/// fixed-point loops' `Cancelled` and `Interrupted`, and a native hook's `Interrupted`, which a
/// hook returns when it observes the cancellation first. Any other failure recorded once the
/// request is cancelled is reported as the cancellation too (see [`rewrite_incomplete`]).
fn simplification_incomplete(state: SearchState, error: SimplificationError) -> IncompleteSearch {
    match error {
        SimplificationError::Cancelled
        | SimplificationError::Interrupted
        | SimplificationError::Builtin(BuiltinError::Interrupted) => {
            IncompleteSearch::Cancelled(state)
        }
        _ if cancellation_requested() => IncompleteSearch::Cancelled(state),
        error => IncompleteSearch::Simplification { state, error },
    }
}

fn merge_pattern_incomplete(
    mut traversal: Vec<IncompleteSearch>,
    mut matching: Vec<IncompleteSearch>,
) -> Vec<IncompleteSearch> {
    let result_bound = matches!(traversal.last(), Some(IncompleteSearch::ResultBound))
        .then(|| traversal.pop())
        .flatten();
    traversal.append(&mut matching);
    traversal.extend(result_bound);
    traversal
}

fn retain_pattern_match(
    matches: &mut Vec<SearchMatch>,
    found: SearchMatch,
    max_results: Option<usize>,
) -> bool {
    if matches.iter().any(|existing| {
        existing.substitution == found.substitution && existing.constraints == found.constraints
    }) {
        return false;
    }
    matches.push(found);
    max_results.is_some_and(|bound| matches.len() >= bound)
}

/// Classify a rewrite step that ends the exploration of `state` without a successor.
///
/// Once the request is cancelled, every solver query answers unknown, so a condition,
/// narrowing or remainder check posed after the cancellation ends as an SMT or remainder
/// indeterminacy that the cancellation caused rather than the configuration. The state's
/// exploration ended because the request was cancelled, and search has no other interruption
/// source (it arms no step deadline), so any entry recorded while the cancellation is set is
/// reported as `Cancelled`.
fn rewrite_incomplete(state: SearchState, reason: IndeterminateReason) -> IncompleteSearch {
    if cancellation_requested() {
        IncompleteSearch::Cancelled(state)
    } else {
        IncompleteSearch::Indeterminate { state, reason }
    }
}

/// Classify a target-pattern check that could not decide whether `state` matches.
///
/// As in [`rewrite_incomplete`], a solver query posed after the request is cancelled answers
/// unknown because of the cancellation, so an undecided check recorded while the cancellation is
/// set reports the cancellation.
fn pattern_match_incomplete(state: SearchState, error: PatternMatchError) -> IncompleteSearch {
    match error {
        PatternMatchError::Simplification(error) => simplification_incomplete(state, error),
        _ if cancellation_requested() => IncompleteSearch::Cancelled(state),
        PatternMatchError::Indeterminate {
            substitution,
            remainder,
        } => IncompleteSearch::Match {
            state,
            substitution,
            remainder,
        },
        PatternMatchError::Smt(error) => IncompleteSearch::Smt { state, error },
    }
}

fn pattern_variables(pattern: &Pattern) -> BTreeSet<crate::term::Variable> {
    pattern
        .term
        .attributes()
        .variables
        .iter()
        .cloned()
        .chain(
            pattern
                .constraints
                .iter()
                .flat_map(Predicate::free_variables),
        )
        .collect()
}

fn match_pattern_with_variables(
    definition: &BackendDefinition,
    target: &Pattern,
    subject: &Pattern,
    output_variables: &BTreeSet<crate::term::Variable>,
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
    retain_unknown: bool,
) -> Result<Option<PatternMatch>, PatternMatchError> {
    let substitution = match match_terms_in_definition(
        MatchMode::Implies,
        definition,
        &target.term,
        &subject.term,
    ) {
        MatchResult::Success(substitution) => substitution,
        MatchResult::Failed(_) => return Ok(None),
        MatchResult::Indeterminate {
            substitution,
            remainder,
        } => {
            return Err(PatternMatchError::Indeterminate {
                substitution,
                remainder,
            });
        }
    };

    let mut constraints = subject.constraints.clone();
    constraints.extend(substitute_predicates(&target.constraints, &substitution));
    let (substitution, constraints) =
        normalize_match_condition(substitution, constraints, output_variables);
    let constraints =
        simplify_predicates_with_solver(definition, &constraints, &[], options, solver)
            .map_err(PatternMatchError::Simplification)?;
    match predicates_truth(&constraints) {
        Truth::False => return Ok(None),
        Truth::True => {}
        Truth::Unknown if retain_unknown => {}
        Truth::Unknown => match solver.is_sat(&constraints, &substitution) {
            Ok(Satisfiability::Unsat) => return Ok(None),
            Ok(Satisfiability::Sat) => {}
            Ok(Satisfiability::Unknown(reason)) => {
                return Err(PatternMatchError::Smt(SmtError::Unknown(reason)));
            }
            Err(error) => return Err(PatternMatchError::Smt(error)),
        },
    }

    Ok(Some(PatternMatch {
        substitution,
        constraints,
    }))
}

fn normalize_match_condition(
    output: Substitution,
    mut constraints: Vec<Predicate>,
    output_variables: &BTreeSet<crate::term::Variable>,
) -> (Substitution, Vec<Predicate>) {
    let _span = measure::algorithm_span(Algorithm::BackendSubstitutionExtractOutput);
    let mut solved = Substitution::new();
    // Invariant: each round moves one solvable equality into `solved`; exit when none remains.
    loop {
        let mut binding = None;
        for (index, constraint) in constraints.iter().enumerate() {
            let Predicate::Equals(left, right) = constraint else {
                continue;
            };
            let left = substitute(left, &solved);
            let right = substitute(right, &solved);
            if left == right {
                binding = Some((index, None));
                break;
            }
            let candidate = match (left.kind(), right.kind()) {
                (crate::term::TermKind::Variable(variable), _)
                    if !right.attributes().variables.contains(variable) =>
                {
                    Some((variable.clone(), right))
                }
                (_, crate::term::TermKind::Variable(variable))
                    if !left.attributes().variables.contains(variable) =>
                {
                    Some((variable.clone(), left))
                }
                _ => None,
            };
            if let Some(candidate) = candidate {
                binding = Some((index, Some(candidate)));
                break;
            }
        }
        let Some((index, binding)) = binding else {
            break;
        };
        constraints.remove(index);
        let Some((variable, value)) = binding else {
            continue;
        };
        let binding = Substitution::from([(variable, value)]);
        solved = compose(&binding, &solved);
        constraints = substitute_predicates(&constraints, &binding);
    }

    let mut output = compose(&solved, &output);
    output.retain(|variable, _| output_variables.contains(variable));
    let constraints = substitute_predicates(&constraints, &solved);
    (output, constraints)
}

fn simplification_options(options: SearchOptions) -> SimplificationOptions {
    SimplificationOptions {
        max_iterations: options.max_simplification_iterations,
        ..SimplificationOptions::default()
    }
}

fn selects_reachable_state(search_type: SearchType, depth: u64) -> bool {
    match search_type {
        SearchType::Star => true,
        SearchType::Plus => depth > 0,
        SearchType::One => depth == 1,
        SearchType::Final => false,
    }
}

/// Whether a state that just satisfied the result bound could still contribute unexplored
/// successors. Stopping at the bound is only a truncation when such work remains; a search
/// that is exhausted exactly at the bound is complete.
fn state_may_expand(
    definition: &BackendDefinition,
    state: &SearchState,
    is_rewritable: bool,
    options: SearchOptions,
    fresh_counter: &mut u64,
    solver: &dyn SmtSolver,
) -> bool {
    if !is_rewritable {
        return false;
    }
    if options.search_type == SearchType::One && state.depth == 1 {
        return false;
    }
    if state.depth >= options.max_depth {
        // Continuing would have reported a depth bound; the frontier is not exhausted.
        return true;
    }
    !matches!(
        rewrite_step_with_options(
            definition,
            &state.pattern,
            fresh_counter,
            simplification_options(options),
            solver,
        ),
        RewriteResult::Stuck(_) | RewriteResult::Trivial(_, _) | RewriteResult::Vacuous(_)
    )
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum StateRetention {
    Continue,
    ResultBound,
    PatternBound,
}

/// Retain one unique state result and classify any result bound reached there.
fn retain_state_result(
    states: &mut Vec<SearchState>,
    state: SearchState,
    max_results: Option<usize>,
    pattern_bound_reached: &mut impl FnMut(&SearchState) -> bool,
) -> StateRetention {
    if states.iter().any(|found| found.pattern == state.pattern) {
        return StateRetention::Continue;
    }
    let pattern_bound_reached = pattern_bound_reached(&state);
    states.push(state);
    if pattern_bound_reached {
        StateRetention::PatternBound
    } else if max_results.is_some_and(|limit| states.len() >= limit) {
        StateRetention::ResultBound
    } else {
        StateRetention::Continue
    }
}

fn record_effects(
    recorded: &mut Vec<BuiltinEffect>,
    effects: impl IntoIterator<Item = BuiltinEffect>,
    observe: &mut impl FnMut(&BuiltinEffect),
) {
    for effect in effects {
        observe(&effect);
        recorded.push(effect);
    }
}

fn record_applied_effects(
    recorded: &mut Vec<BuiltinEffect>,
    applied: &AppliedRule,
    observe: &mut impl FnMut(&BuiltinEffect),
) {
    for simplification in &applied.remainder_simplifications {
        record_effects(
            recorded,
            simplification.effects.iter().cloned(),
            &mut *observe,
        );
    }
    record_effects(recorded, applied.effects.iter().cloned(), observe);
}

fn next_state(depth: u64, mut trace: Vec<TraceEntry>, applied: AppliedRule) -> SearchState {
    for simplification in &applied.remainder_simplifications {
        trace.extend(
            simplification
                .applied_rules
                .iter()
                .cloned()
                .map(|unique_id| TraceEntry {
                    depth,
                    kind: TraceKind::Simplification,
                    label: None,
                    unique_id,
                }),
        );
    }
    trace.push(TraceEntry {
        depth: depth + 1,
        kind: TraceKind::Rewrite,
        label: applied.label,
        unique_id: applied.unique_id,
    });
    SearchState {
        pattern: applied.pattern,
        depth: depth + 1,
        trace,
        branch: Vec::new(),
        observations: Vec::new(),
        diagnostics: Vec::new(),
    }
}

fn remaining_state(
    depth: u64,
    mut trace: Vec<TraceEntry>,
    remainder: RemainderBranch,
) -> SearchState {
    trace.push(TraceEntry {
        depth,
        kind: TraceKind::Remainder,
        label: None,
        unique_id: remainder.rule_ids.join(","),
    });
    for simplification in &remainder.simplifications {
        trace.extend(
            simplification
                .applied_rules
                .iter()
                .cloned()
                .map(|unique_id| TraceEntry {
                    depth,
                    kind: TraceKind::Simplification,
                    label: None,
                    unique_id,
                }),
        );
    }
    SearchState {
        pattern: remainder.pattern,
        depth,
        trace,
        branch: Vec::new(),
        observations: Vec::new(),
        diagnostics: Vec::new(),
    }
}

fn replay_search_remainder(
    definition: &BackendDefinition,
    mut observation: ObservationHead,
    before: Pattern,
    remainder: &RemainderBranch,
    observation_log: &mut ObservationLog,
    observation_options: Option<&ObservationOptions>,
) -> (ObservationHead, QueuedStateKind) {
    let transition_pattern = remainder
        .simplifications
        .first()
        .map_or_else(|| remainder.pattern.clone(), |record| record.before.clone());
    let transition_remainder = RemainderBranch {
        pattern: transition_pattern,
        ..remainder.clone()
    };
    observation = observation_log.append_remainder(
        observation,
        before,
        &transition_remainder,
        observation_options,
    );
    for simplification in &remainder.simplifications {
        observation = observation_log.append_simplification(
            observation,
            definition,
            simplification.before.clone(),
            &simplification.after,
            &simplification.applied_rules,
            &simplification.effects,
            observation_options,
        );
    }
    (
        observation,
        QueuedStateKind::Remaining(remainder.indeterminate.clone()),
    )
}

#[cfg(test)]
mod tests {
    use std::{collections::BTreeSet, sync::Arc};

    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};
    use proptest::prelude::*;

    use super::*;
    use crate::transition::{ObservationEvent, ObservationOptions};
    use crate::{
        diagnostic::{self, BackendDiagnostic},
        simplify::BudgetSubject,
        term::{Sort, Symbol, Term, TermKind, Variable},
    };

    #[test]
    fn cancellation_is_not_reported_as_a_simplifier_failure() {
        let definition = definition();
        let token = crate::cancellation::CancellationToken::new();
        token.cancel();
        let result = token
            .scope(|| search_graph(&definition, initial(&definition), SearchOptions::default()));

        assert!(result.states.is_empty());
        let [IncompleteSearch::Cancelled(state)] = result.incomplete.as_slice() else {
            panic!("expected cancellation, found {:?}", result.incomplete);
        };
        assert_eq!(state.depth, 0);
    }

    fn definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module SEARCH
                sort SortS{} []
                symbol initial{}() : SortS{} [constructor{}()]
                symbol next1{}() : SortS{} [constructor{}()]
                symbol next2{}() : SortS{} [constructor{}()]
                symbol final1{}() : SortS{} [constructor{}()]
                symbol final2{}() : SortS{} [constructor{}()]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(initial{}(), \top{SortS{}}()),
                    next1{}()
                ) [label{}("initial-next1")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(initial{}(), \top{SortS{}}()),
                    next2{}()
                ) [label{}("initial-next2")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(next1{}(), \top{SortS{}}()),
                    final1{}()
                ) [label{}("next1-final1")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(next2{}(), \top{SortS{}}()),
                    final2{}()
                ) [label{}("next2-final2")]
            endmodule []"#,
        )
        .expect("search definition should parse");
        BackendDefinition::internalize(&syntax, "SEARCH")
            .expect("search definition should internalize")
    }

    fn converging_definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module SEARCH
                sort SortS{} []
                symbol initial{}() : SortS{} [constructor{}()]
                symbol next1{}() : SortS{} [constructor{}()]
                symbol next2{}() : SortS{} [constructor{}()]
                symbol final1{}() : SortS{} [constructor{}()]
                symbol final2{}() : SortS{} [constructor{}()]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(initial{}(), \top{SortS{}}()),
                    next1{}()
                ) [label{}("initial-next1")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(initial{}(), \top{SortS{}}()),
                    next2{}()
                ) [label{}("initial-next2")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(next1{}(), \top{SortS{}}()),
                    final1{}()
                ) [label{}("next1-final1")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(next2{}(), \top{SortS{}}()),
                    final1{}()
                ) [label{}("next2-final1")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(next2{}(), \top{SortS{}}()),
                    final2{}()
                ) [label{}("next2-final2")]
            endmodule []"#,
        )
        .expect("converging search definition should parse");
        BackendDefinition::internalize(&syntax, "SEARCH")
            .expect("converging search definition should internalize")
    }

    #[cfg(feature = "z3")]
    fn conditional_remainder_definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module SEARCH-REMAINDER
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                sort SortS{} []
                symbol initial{}(SortInt{}) : SortS{} [constructor{}()]
                symbol middle{}(SortInt{}) : SortS{} [constructor{}()]
                symbol done{}() : SortS{} [constructor{}()]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(initial{}(X:SortInt{}), \top{SortS{}}()),
                    middle{}(X:SortInt{})
                ) [label{}("initial-middle")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(
                        middle{}(X:SortInt{}),
                        \equals{SortInt{}, SortS{}}(
                            X:SortInt{},
                            \dv{SortInt{}}("0")
                        )
                    ),
                    done{}()
                ) [label{}("middle-done")]
            endmodule []"#,
        )
        .expect("conditional-remainder search definition should parse");
        BackendDefinition::internalize(&syntax, "SEARCH-REMAINDER")
            .expect("conditional-remainder search definition should internalize")
    }

    fn search_bound_definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module SEARCH-BOUND
                sort SortS{} []
                symbol a{}() : SortS{} [constructor{}()]
                symbol b{}() : SortS{} [constructor{}()]
                symbol c{}() : SortS{} [constructor{}()]
                symbol d{}() : SortS{} [constructor{}()]
                symbol e{}() : SortS{} [constructor{}()]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(a{}(), \top{SortS{}}()), b{}()
                ) [label{}("a-b")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(a{}(), \top{SortS{}}()), c{}()
                ) [label{}("a-c")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(b{}(), \top{SortS{}}()), d{}()
                ) [label{}("b-d")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(d{}(), \top{SortS{}}()), e{}()
                ) [label{}("d-e")]
            endmodule []"#,
        )
        .expect("search-bound definition should parse");
        BackendDefinition::internalize(&syntax, "SEARCH-BOUND")
            .expect("search-bound definition should internalize")
    }

    fn infinite_result_definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module INFINITE-RESULT
                sort SortNat{} []
                sort SortS{} []
                symbol zero{}() : SortNat{} [constructor{}()]
                symbol successor{}(SortNat{}) : SortNat{} [constructor{}()]
                symbol loop{}(SortNat{}) : SortS{} [constructor{}()]
                symbol done{}(SortNat{}) : SortS{} [constructor{}()]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(loop{}(N:SortNat{}), \top{SortS{}}()),
                    done{}(N:SortNat{})
                ) [label{}("emit")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(loop{}(N:SortNat{}), \top{SortS{}}()),
                    loop{}(successor{}(N:SortNat{}))
                ) [label{}("continue")]
            endmodule []"#,
        )
        .expect("infinite-result definition should parse");
        BackendDefinition::internalize(&syntax, "INFINITE-RESULT")
            .expect("infinite-result definition should internalize")
    }

    fn diamond_definition(cyclic: bool) -> BackendDefinition {
        let cycle = if cyclic {
            r#"
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(merged{}(), \top{SortS{}}()),
                    initial{}()
                ) [label{}("merged-initial")]
            "#
        } else {
            ""
        };
        let syntax = parse_definition(&format!(
            r#"[]
            module DIAMOND
                sort SortS{{}} []
                symbol initial{{}}() : SortS{{}} [constructor{{}}()]
                symbol left{{}}() : SortS{{}} [constructor{{}}()]
                symbol right{{}}() : SortS{{}} [constructor{{}}()]
                symbol merged{{}}() : SortS{{}} [constructor{{}}()]
                axiom{{}} \rewrites{{SortS{{}}}}(
                    \and{{SortS{{}}}}(initial{{}}(), \top{{SortS{{}}}}()),
                    left{{}}()
                ) [label{{}}("initial-left")]
                axiom{{}} \rewrites{{SortS{{}}}}(
                    \and{{SortS{{}}}}(initial{{}}(), \top{{SortS{{}}}}()),
                    right{{}}()
                ) [label{{}}("initial-right")]
                axiom{{}} \rewrites{{SortS{{}}}}(
                    \and{{SortS{{}}}}(left{{}}(), \top{{SortS{{}}}}()),
                    merged{{}}()
                ) [label{{}}("left-merged")]
                axiom{{}} \rewrites{{SortS{{}}}}(
                    \and{{SortS{{}}}}(right{{}}(), \top{{SortS{{}}}}()),
                    merged{{}}()
                ) [label{{}}("right-merged")]
                {cycle}
            endmodule []"#
        ))
        .expect("diamond definition should parse");
        BackendDefinition::internalize(&syntax, "DIAMOND")
            .expect("diamond definition should internalize")
    }

    /// Three threads that each advance a private counter three times, in any interleaving; every
    /// step logs one line. The state graph is the 4 x 4 x 4 lattice of counter values (64
    /// configurations, 144 edges), while the tree of interleavings has 5247 edges.
    fn interleaving_definition() -> BackendDefinition {
        let mut module = String::from(
            r#"[]
            module INTERLEAVING
                sort SortS{} []
                sort SortK{} []
                sort SortString{} [hasDomainValues{}()]
                symbol state{}(SortS{}, SortS{}, SortS{}) : SortS{} [constructor{}()]
                symbol dotk{}() : SortK{} [constructor{}()]
                hooked-symbol log{}(SortString{}) : SortK{}
                    [function{}(), total{}(), hook{}("IO.logString")]
                symbol tick{}(SortK{}, SortS{}) : SortS{} [function{}()]
                axiom{R} \implies{R}(
                    \top{R}(),
                    \equals{SortS{}, R}(
                        tick{}(dotk{}(), X:SortS{}),
                        \and{SortS{}}(X:SortS{}, \top{SortS{}}())
                    )
                ) [label{}("tick"), simplification{}()]
"#,
        );
        for thread in ["a", "b", "c"] {
            for step in 0..4 {
                module.push_str(&format!(
                    "symbol {thread}{step}{{}}() : SortS{{}} [constructor{{}}()]\n"
                ));
            }
        }
        for (thread, before, after) in [
            (
                "a",
                "state{}(a0{}(), Y:SortS{}, Z:SortS{})",
                "state{}(NEXT, Y:SortS{}, Z:SortS{})",
            ),
            (
                "b",
                "state{}(X:SortS{}, b0{}(), Z:SortS{})",
                "state{}(X:SortS{}, NEXT, Z:SortS{})",
            ),
            (
                "c",
                "state{}(X:SortS{}, Y:SortS{}, c0{}())",
                "state{}(X:SortS{}, Y:SortS{}, NEXT)",
            ),
        ] {
            for step in 0..3 {
                let from = format!("{thread}{step}{{}}()");
                let next = format!(
                    "tick{{}}(log{{}}(\\dv{{SortString{{}}}}(\"{thread}{step}\")), {thread}{}{{}}())",
                    step + 1
                );
                let left = before.replace(&format!("{thread}0{{}}()"), &from);
                let right = after.replace("NEXT", &next);
                module.push_str(&format!(
                    "axiom{{}} \\rewrites{{SortS{{}}}}(\\and{{SortS{{}}}}({left}, \\top{{SortS{{}}}}()), {right}) [label{{}}(\"{thread}{step}\")]\n"
                ));
            }
        }
        module.push_str("endmodule []");
        let syntax = parse_definition(&module).expect("interleaving definition should parse");
        BackendDefinition::internalize(&syntax, "INTERLEAVING")
            .expect("interleaving definition should internalize")
    }

    fn rewrite_simplification_failure_definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module SEARCH
                sort SortS{} []
                symbol initial{}() : SortS{} [constructor{}()]
                symbol done{}() : SortS{} [constructor{}()]
                symbol expand{}(SortS{}) : SortS{} [function{}()]
                axiom{R} \implies{R}(
                    \top{R}(),
                    \equals{SortS{}, R}(
                        expand{}(X:SortS{}),
                        \and{SortS{}}(
                            expand{}(expand{}(X:SortS{})),
                            \top{SortS{}}()
                        )
                    )
                ) [label{}("expand"), simplification{}()]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(
                        initial{}(),
                        \equals{SortS{}, SortS{}}(
                            expand{}(initial{}()),
                            initial{}()
                        )
                    ),
                    done{}()
                ) [label{}("conditional")]
            endmodule []"#,
        )
        .expect("search definition should parse");
        BackendDefinition::internalize(&syntax, "SEARCH")
            .expect("search definition should internalize")
    }

    #[test]
    fn rewrite_budget_exhaustion_is_not_classified_as_simplification_failure() {
        let definition = rewrite_simplification_failure_definition();
        let (result, diagnostics) = diagnostic::collect(|| {
            search_graph(
                &definition,
                pattern(&definition, "initial{}()"),
                SearchOptions {
                    max_simplification_iterations: 1,
                    ..SearchOptions::default()
                },
            )
        });

        assert!(result.incomplete.iter().all(|incomplete| !matches!(
            incomplete,
            IncompleteSearch::Simplification {
                error: SimplificationError::IterationLimit { .. }
                    | SimplificationError::PredicateIterationLimit { .. },
                ..
            }
        )));
        assert!(diagnostics.iter().any(|diagnostic| matches!(
            diagnostic,
            BackendDiagnostic::SimplificationBudgetExhausted {
                limit: 1,
                subject: BudgetSubject::Predicates,
            }
        )));
    }

    #[test]
    fn every_interruption_signal_is_classified_as_cancellation() {
        let definition = definition();
        let state = SearchState {
            pattern: initial(&definition),
            depth: 0,
            trace: Vec::new(),
            branch: Vec::new(),
            observations: Vec::new(),
            diagnostics: Vec::new(),
        };

        for error in [
            SimplificationError::Cancelled,
            SimplificationError::Interrupted,
            SimplificationError::Builtin(BuiltinError::Interrupted),
        ] {
            assert_eq!(
                simplification_incomplete(state.clone(), error.clone()),
                IncompleteSearch::Cancelled(state.clone()),
                "{error:?}"
            );
        }
    }

    #[test]
    fn every_entry_recorded_after_cancellation_is_classified_as_cancellation() {
        let definition = definition();
        let state = SearchState {
            pattern: initial(&definition),
            depth: 0,
            trace: Vec::new(),
            branch: Vec::new(),
            observations: Vec::new(),
            diagnostics: Vec::new(),
        };
        let unknown = || SmtError::Unknown("request cancelled".into());
        let smt = || IndeterminateReason::Smt {
            rule_id: "rule".into(),
            error: unknown(),
        };
        let remainder = || IndeterminateReason::Remainder {
            rule_ids: vec!["rule".into()],
            predicates: Vec::new(),
            satisfiability: Ok(Satisfiability::Unknown("request cancelled".into())),
        };
        let pattern_smt = || PatternMatchError::Smt(unknown());
        let pattern_match = || PatternMatchError::Indeterminate {
            substitution: Substitution::new(),
            remainder: Vec::new(),
        };

        // Without a cancellation the reasons are reported as they are.
        assert!(matches!(
            rewrite_incomplete(state.clone(), smt()),
            IncompleteSearch::Indeterminate { .. }
        ));
        assert!(matches!(
            pattern_match_incomplete(state.clone(), pattern_smt()),
            IncompleteSearch::Smt { .. }
        ));

        let token = crate::cancellation::CancellationToken::new();
        token.cancel();
        token.scope(|| {
            for reason in [smt(), remainder()] {
                assert_eq!(
                    rewrite_incomplete(state.clone(), reason.clone()),
                    IncompleteSearch::Cancelled(state.clone()),
                    "{reason:?}"
                );
            }
            for error in [pattern_smt(), pattern_match()] {
                assert_eq!(
                    pattern_match_incomplete(state.clone(), error.clone()),
                    IncompleteSearch::Cancelled(state.clone()),
                    "{error:?}"
                );
            }
            assert_eq!(
                simplification_incomplete(
                    state.clone(),
                    SimplificationError::SmtPredicate {
                        predicate: Box::new(Predicate::True),
                        error: unknown(),
                    },
                ),
                IncompleteSearch::Cancelled(state.clone())
            );
        });
    }

    fn initial(definition: &BackendDefinition) -> Pattern {
        pattern(definition, "initial{}()")
    }

    #[test]
    fn pattern_digests_pin_canonical_kore() {
        let definition = definition();

        assert_eq!(
            PatternDigest::of(&initial(&definition)).to_string(),
            "7712dc0593a7e3c45c882dedb8016f1d148662e343ffe9e3b87705f3f15c83b9"
        );
    }

    fn pattern(definition: &BackendDefinition, source: &str) -> Pattern {
        Pattern {
            term: definition
                .internalize_term(
                    &parse_pattern(source).expect("search pattern should parse"),
                    &[],
                )
                .expect("search pattern should internalize"),
            constraints: Vec::new(),
        }
    }

    fn names(result: &SearchResult) -> BTreeSet<String> {
        result
            .states
            .iter()
            .map(|state| match state.pattern.term.kind() {
                TermKind::Application { symbol, .. } => symbol.name.to_string(),
                other => panic!("expected an application, found {other:?}"),
            })
            .collect()
    }

    fn state_name(state: &SearchState) -> String {
        match state.pattern.term.kind() {
            TermKind::Application { symbol, .. } => symbol.name.to_string(),
            other => panic!("expected an application, found {other:?}"),
        }
    }

    fn search_types() -> impl Strategy<Value = SearchType> {
        prop_oneof![
            Just(SearchType::One),
            Just(SearchType::Star),
            Just(SearchType::Plus),
            Just(SearchType::Final),
        ]
    }

    fn result_variable() -> Variable {
        Variable::new("Result", Sort::simple("SortS"))
    }

    fn pattern_result_names(result: &PatternSearchResult, variable: &Variable) -> BTreeSet<String> {
        result
            .matches
            .iter()
            .map(|found| match found.substitution[variable].kind() {
                TermKind::Application { symbol, .. } => symbol.name.to_string(),
                other => panic!("expected an application, found {other:?}"),
            })
            .collect()
    }

    proptest! {
        #[test]
        fn complete_result_bounded_state_search_agrees_with_unbounded_search(
            search_type in search_types(),
            max_depth in 0_u64..=4,
            max_results in 0_usize..=7,
        ) {
            let definition = definition();
            let options = SearchOptions {
                search_type,
                max_depth,
                max_results: Some(max_results),
                ..SearchOptions::default()
            };
            let bounded = search_graph(&definition, initial(&definition), options);
            if bounded.incomplete.is_empty() {
                let unbounded = search_graph(
                    &definition,
                    initial(&definition),
                    SearchOptions { max_results: None, ..options },
                );
                prop_assert_eq!(names(&bounded), names(&unbounded));
            }
        }

        #[test]
        fn complete_result_bounded_pattern_search_agrees_with_unbounded_search(
            search_type in search_types(),
            max_depth in 0_u64..=4,
            max_results in 0_usize..=7,
        ) {
            let definition = definition();
            let result_variable = result_variable();
            let target = Pattern {
                term: Term::variable(result_variable.clone()),
                constraints: Vec::new(),
            };
            let options = SearchOptions {
                search_type,
                max_depth,
                max_results: Some(max_results),
                ..SearchOptions::default()
            };
            let bounded = search_pattern(&definition, initial(&definition), &target, options);
            if bounded.incomplete.is_empty() {
                let unbounded = search_pattern(
                    &definition,
                    initial(&definition),
                    &target,
                    SearchOptions { max_results: None, ..options },
                );
                prop_assert_eq!(
                    pattern_result_names(&bounded, &result_variable),
                    pattern_result_names(&unbounded, &result_variable),
                );
            }
        }

        #[test]
        fn bounded_search_incompleteness_never_invents_states(
            search_type in search_types(),
            max_depth in 0_u64..=4,
            max_breadth in 0_usize..=7,
            max_results in 0_usize..=7,
        ) {
            let definition = definition();
            let bounded = search_graph(
                &definition,
                initial(&definition),
                SearchOptions {
                    search_type,
                    max_depth,
                    max_breadth: Some(max_breadth),
                    max_results: Some(max_results),
                    ..SearchOptions::default()
                },
            );
            prop_assume!(!bounded.incomplete.is_empty());

            let selected = search_graph(
                &definition,
                initial(&definition),
                SearchOptions {
                    search_type,
                    max_depth,
                    ..SearchOptions::default()
                },
            );
            let closure = search_graph(
                &definition,
                initial(&definition),
                SearchOptions { search_type: SearchType::Star, ..SearchOptions::default() },
            );
            let selected_names = names(&selected);
            let closure_names = names(&closure);

            prop_assert!(names(&bounded).is_subset(&selected_names));
            for marker in &bounded.incomplete {
                match marker {
                    IncompleteSearch::DepthBound(state) => {
                        prop_assert!(closure_names.contains(&state_name(state)));
                    }
                    IncompleteSearch::BreadthBound(states) => {
                        for state in states {
                            prop_assert!(closure_names.contains(&state_name(state)));
                        }
                    }
                    IncompleteSearch::ResultBound => {}
                    other => prop_assert!(false, "unexpected marker for finite fixture: {other:?}"),
                }
            }
        }

        #[test]
        fn bounded_properties_hold_on_the_converging_fixture(
            search_type in search_types(),
            max_depth in 0_u64..=4,
            max_results in 0_usize..=7,
        ) {
            let definition = converging_definition();
            let options = SearchOptions {
                search_type,
                max_depth,
                max_results: Some(max_results),
                ..SearchOptions::default()
            };
            let bounded = search_graph(&definition, initial(&definition), options);
            if bounded.incomplete.is_empty() {
                let unbounded = search_graph(
                    &definition,
                    initial(&definition),
                    SearchOptions { max_results: None, ..options },
                );
                prop_assert_eq!(names(&bounded), names(&unbounded));
            }
        }

        #[test]
        fn complete_result_bounded_path_search_agrees_with_unbounded_search(
            cyclic in any::<bool>(),
            search_type in search_types(),
            max_depth in 0_u64..=4,
            max_results in 0_usize..=7,
        ) {
            let definition = diamond_definition(cyclic);
            let options = SearchOptions {
                search_type,
                max_depth,
                max_results: Some(max_results),
                ..SearchOptions::default()
            };
            let bounded = search_paths(&definition, initial(&definition), options);
            if bounded.incomplete.is_empty() {
                let unbounded = search_paths(
                    &definition,
                    initial(&definition),
                    SearchOptions { max_results: None, ..options },
                );
                prop_assert_eq!(
                    bounded
                        .witnesses
                        .into_iter()
                        .map(|witness| witness.id)
                        .collect::<BTreeSet<_>>(),
                    unbounded
                        .witnesses
                        .into_iter()
                        .map(|witness| witness.id)
                        .collect::<BTreeSet<_>>(),
                );
            }
        }
    }

    #[test]
    fn state_search_deduplicates_converging_paths() {
        let definition = converging_definition();
        let result = search_graph(
            &definition,
            initial(&definition),
            SearchOptions {
                search_type: SearchType::Final,
                ..SearchOptions::default()
            },
        );

        assert_eq!(
            names(&result),
            BTreeSet::from(["final1".into(), "final2".into()])
        );
        assert_eq!(
            result
                .states
                .iter()
                .filter(|state| state_name(state) == "final1")
                .count(),
            1
        );
        assert_eq!(result.modality(), ResultModality::StateSet);
    }

    #[test]
    fn builtin_effect_observer_preserves_state_search_results() {
        let definition = diamond_definition(false);
        let expected = search_graph(&definition, initial(&definition), SearchOptions::default());
        let mut observed = Vec::new();
        let actual = search_graph_with_solver_and_observer(
            &definition,
            initial(&definition),
            SearchOptions::default(),
            &NoSolver,
            |effect| observed.push(effect.clone()),
        );

        assert_eq!(actual, expected);
        assert_eq!(observed, actual.effects);
    }

    #[test]
    fn pattern_bound_stops_effects_and_the_effect_observer() {
        let definition = interleaving_definition();
        let initial = pattern(&definition, "state{}(a0{}(), b0{}(), c0{}())");
        let options = SearchOptions {
            search_type: SearchType::Star,
            ..SearchOptions::default()
        };
        let target = Pattern {
            term: Term::variable(result_variable()),
            constraints: Vec::new(),
        };
        let pattern_result = search_pattern(
            &definition,
            initial.clone(),
            &target,
            SearchOptions {
                max_results: Some(2),
                ..options
            },
        );

        let mut retained = 0;
        let mut observed = Vec::new();
        let graph_result = search_graph_collecting(
            &definition,
            vec![initial],
            options,
            &NoSolver,
            None,
            |effect| observed.push(effect.clone()),
            |_| {
                retained += 1;
                retained == 2
            },
        );

        assert_eq!(pattern_result.matches.len(), 2);
        // Expanding the initial state commits all three sibling effects. Reaching the bound on
        // the first depth-one result prevents every deeper effect.
        assert_eq!(
            pattern_result.effects,
            [
                BuiltinEffect::UserLog("a0".into()),
                BuiltinEffect::UserLog("b0".into()),
                BuiltinEffect::UserLog("c0".into()),
            ]
        );
        assert_eq!(pattern_result.incomplete, [IncompleteSearch::ResultBound]);
        assert_eq!(graph_result.states.len(), 2);
        assert_eq!(observed, graph_result.effects);
        assert_eq!(graph_result.effects, pattern_result.effects);
        assert_eq!(graph_result.incomplete, [IncompleteSearch::ResultBound]);
    }

    #[test]
    fn observed_search_retains_branch_local_transition_streams() {
        let definition = definition();
        let result = search_graph_observed(
            &definition,
            initial(&definition),
            SearchOptions::default(),
            &ObservationOptions::all(),
        );

        assert_eq!(result.states.len(), 2);
        assert_eq!(
            result
                .states
                .iter()
                .map(|state| {
                    state
                        .observations
                        .iter()
                        .filter_map(|event| match event {
                            ObservationEvent::Transition(observation) => {
                                Some(observation.id.rule.as_str())
                            }
                            ObservationEvent::Evaluation(_) => None,
                            ObservationEvent::Uncommitted(_) => {
                                panic!("search cannot retain a rolled-back transition")
                            }
                        })
                        .collect::<Vec<_>>()
                })
                .collect::<BTreeSet<_>>(),
            BTreeSet::from([
                vec!["initial-next1", "next1-final1"],
                vec!["initial-next2", "next2-final2"],
            ])
        );
        assert!(
            result
                .states
                .iter()
                .all(|state| state.branch.len() == state.depth as usize)
        );
    }

    #[test]
    fn observed_search_preserves_non_observation_outputs() {
        let definition = definition();
        let initial = initial(&definition);
        let expected = search_graph(&definition, initial.clone(), SearchOptions::default());
        let mut actual = search_graph_observed(
            &definition,
            initial,
            SearchOptions::default(),
            &ObservationOptions::all(),
        );

        assert!(
            actual
                .states
                .iter()
                .all(|state| !state.observations.is_empty())
        );
        for state in &mut actual.states {
            state.branch.clear();
            state.observations.clear();
        }
        assert_eq!(actual, expected);
    }

    #[test]
    fn path_search_returns_a_witness_per_distinct_path() {
        let definition = diamond_definition(false);
        let result = search_paths(&definition, initial(&definition), SearchOptions::default());

        assert_eq!(result.modality(), ResultModality::PathSet);
        assert_eq!(result.witnesses.len(), 2);
        assert_eq!(
            result
                .witnesses
                .iter()
                .map(|witness| witness
                    .id
                    .iter()
                    .map(|transition| transition.rule.as_str())
                    .collect::<Vec<_>>())
                .collect::<BTreeSet<_>>(),
            BTreeSet::from([
                vec!["initial-left", "left-merged"],
                vec!["initial-right", "right-merged"],
            ])
        );
    }

    #[test]
    fn observed_path_search_retains_each_witness_stream() {
        let definition = diamond_definition(false);
        let result = search_paths_observed(
            &definition,
            initial(&definition),
            SearchOptions::default(),
            &ObservationOptions::all(),
        );

        assert_eq!(result.witnesses.len(), 2);
        assert!(result.witnesses.iter().all(|witness| {
            witness
                .observations
                .iter()
                .filter_map(|event| match event {
                    ObservationEvent::Transition(observation) => Some(&observation.id),
                    ObservationEvent::Evaluation(_) => None,
                    ObservationEvent::Uncommitted(_) => {
                        panic!("path search cannot retain a rollback")
                    }
                })
                .eq(witness.id.iter())
        }));
    }

    #[test]
    fn observed_path_search_preserves_non_observation_outputs() {
        let definition = diamond_definition(false);
        let initial = initial(&definition);
        let expected = search_paths(&definition, initial.clone(), SearchOptions::default());
        let mut actual = search_paths_observed(
            &definition,
            initial,
            SearchOptions::default(),
            &ObservationOptions::all(),
        );

        assert!(
            actual
                .witnesses
                .iter()
                .all(|witness| !witness.observations.is_empty())
        );
        for witness in &mut actual.witnesses {
            witness.observations.clear();
        }
        assert_eq!(actual, expected);
    }

    #[test]
    fn observed_pattern_path_search_preserves_witness_streams() {
        let definition = diamond_definition(false);
        let target = pattern(&definition, "merged{}()");
        let result = search_pattern_paths_observed(
            &definition,
            initial(&definition),
            &target,
            SearchOptions::default(),
            &ObservationOptions::all(),
        );

        assert_eq!(result.matches.len(), 2);
        assert!(
            result
                .matches
                .iter()
                .all(|found| found.witness.observations.len() == 2)
        );
    }

    #[test]
    fn bounded_observed_pattern_searches_preserve_retained_streams() {
        fn transition_ids(observations: &[ObservationEvent]) -> Vec<&TransitionId> {
            observations
                .iter()
                .filter_map(|event| match event {
                    ObservationEvent::Transition(observation) => Some(&observation.id),
                    ObservationEvent::Evaluation(_) => None,
                    ObservationEvent::Uncommitted(_) => {
                        panic!("search cannot retain a rolled-back transition")
                    }
                })
                .collect()
        }

        let definition = diamond_definition(false);
        let target = pattern(&definition, "merged{}()");
        let options = SearchOptions {
            max_results: Some(1),
            ..SearchOptions::default()
        };
        let states = search_pattern_observed(
            &definition,
            initial(&definition),
            &target,
            options,
            &ObservationOptions::all(),
        );
        let paths = search_pattern_paths_observed(
            &definition,
            initial(&definition),
            &target,
            options,
            &ObservationOptions::all(),
        );

        assert_eq!(states.matches.len(), 1);
        assert_eq!(states.incomplete, [IncompleteSearch::ResultBound]);
        assert_eq!(states.matches[0].state.branch.len(), 2);
        assert!(
            transition_ids(&states.matches[0].state.observations)
                .into_iter()
                .eq(&states.matches[0].state.branch)
        );

        assert_eq!(paths.matches.len(), 1);
        assert_eq!(paths.incomplete, [IncompleteSearch::ResultBound]);
        assert_eq!(paths.matches[0].witness.id.len(), 2);
        assert!(
            transition_ids(&paths.matches[0].witness.observations)
                .into_iter()
                .eq(&paths.matches[0].witness.id)
        );
    }

    #[test]
    fn path_witness_identities_are_deterministic_across_replays() {
        let search = || {
            let definition = diamond_definition(false);
            search_paths(&definition, initial(&definition), SearchOptions::default())
                .witnesses
                .into_iter()
                .map(|witness| witness.id)
                .collect::<Vec<_>>()
        };

        assert_eq!(search(), search());
    }

    #[test]
    fn equal_binding_paths_keep_distinct_trace_identities() {
        let definition = diamond_definition(false);
        let result_variable = result_variable();
        let target = Pattern {
            term: Term::variable(result_variable.clone()),
            constraints: Vec::new(),
        };
        let result = search_pattern_paths(
            &definition,
            initial(&definition),
            &target,
            SearchOptions::default(),
        );

        assert_eq!(result.modality(), ResultModality::PathSet);
        assert_eq!(result.matches.len(), 2);
        assert_eq!(
            result
                .matches
                .iter()
                .map(|found| found.substitution[&result_variable].clone())
                .collect::<BTreeSet<_>>()
                .len(),
            1
        );
        assert_eq!(
            result
                .matches
                .iter()
                .map(|found| found.witness.id.clone())
                .collect::<BTreeSet<_>>()
                .len(),
            2
        );
    }

    #[test]
    fn pattern_path_bound_reports_unchecked_later_witnesses() {
        let definition = diamond_definition(false);
        let target = Pattern {
            term: Term::variable(result_variable()),
            constraints: vec![Predicate::Not(Box::new(Predicate::Equals(
                pattern(&definition, "merged{}()").term,
                Term::variable(result_variable()),
            )))],
        };
        let result = search_pattern_paths(
            &definition,
            initial(&definition),
            &target,
            SearchOptions {
                search_type: SearchType::Plus,
                max_results: Some(2),
                ..SearchOptions::default()
            },
        );

        assert_eq!(result.matches.len(), 2);
        assert_eq!(result.incomplete, [IncompleteSearch::ResultBound]);
    }

    #[test]
    fn nonmatching_path_witnesses_do_not_consume_the_bound() {
        let definition = diamond_definition(false);
        let result = search_pattern_paths(
            &definition,
            initial(&definition),
            &pattern(&definition, "right{}()"),
            SearchOptions {
                search_type: SearchType::Plus,
                max_results: Some(1),
                ..SearchOptions::default()
            },
        );

        assert_eq!(result.matches.len(), 1);
        assert_eq!(
            state_name(&witness_search_state(result.matches[0].witness.clone())),
            "right"
        );
        assert_eq!(
            result.matches[0]
                .witness
                .id
                .iter()
                .map(|transition| transition.rule.as_str())
                .collect::<Vec<_>>(),
            ["initial-right"]
        );
        assert_eq!(result.incomplete, [IncompleteSearch::ResultBound]);
    }

    #[test]
    fn cycle_control_terminates_path_search_without_duplicate_witnesses() {
        let definition = diamond_definition(true);
        let result = search_paths(
            &definition,
            initial(&definition),
            SearchOptions {
                search_type: SearchType::Star,
                ..SearchOptions::default()
            },
        );
        let ids = result
            .witnesses
            .iter()
            .map(|witness| witness.id.clone())
            .collect::<BTreeSet<_>>();

        assert_eq!(ids.len(), result.witnesses.len());
        assert_eq!(result.witnesses.len(), 5);
        assert_eq!(
            result.witnesses.iter().map(|witness| witness.depth).max(),
            Some(2)
        );
        assert!(result.incomplete.is_empty());
    }

    #[test]
    fn result_bound_truncates_witnesses_and_reports_incompleteness() {
        let definition = diamond_definition(false);
        let result = search_paths(
            &definition,
            initial(&definition),
            SearchOptions {
                max_results: Some(1),
                ..SearchOptions::default()
            },
        );

        assert_eq!(result.witnesses.len(), 1);
        assert!(result.incomplete.contains(&IncompleteSearch::ResultBound));
    }

    #[test]
    fn exact_witness_bound_on_a_cyclic_graph_is_complete() {
        let definition = diamond_definition(true);
        let result = search_paths(
            &definition,
            initial(&definition),
            SearchOptions {
                search_type: SearchType::Star,
                max_results: Some(5),
                ..SearchOptions::default()
            },
        );

        assert_eq!(result.witnesses.len(), 5);
        assert!(result.incomplete.is_empty());
    }

    #[test]
    fn pattern_path_bound_reports_unchecked_cycle_candidates() {
        let definition = diamond_definition(true);
        let target = Pattern {
            term: Term::variable(result_variable()),
            constraints: Vec::new(),
        };
        let result = search_pattern_paths(
            &definition,
            initial(&definition),
            &target,
            SearchOptions {
                search_type: SearchType::Star,
                max_results: Some(5),
                ..SearchOptions::default()
            },
        );

        assert_eq!(result.matches.len(), 5);
        // Raw path search can prove that the bound is exact by continuing until its queued
        // cycle candidates are pruned. Pattern search stops at five matches, so those unchecked
        // candidates conservatively make this result incomplete.
        assert_eq!(result.incomplete, [IncompleteSearch::ResultBound]);
    }

    #[test]
    fn a_deduplicated_state_keeps_one_valid_trace() {
        let definition = converging_definition();
        let result = search_graph(
            &definition,
            initial(&definition),
            SearchOptions {
                search_type: SearchType::Final,
                ..SearchOptions::default()
            },
        );
        let final1 = result
            .states
            .iter()
            .find(|state| state_name(state) == "final1")
            .expect("final1 should be reachable");
        let labels = final1
            .trace
            .iter()
            .filter(|entry| entry.kind == TraceKind::Rewrite)
            .map(|entry| entry.label.as_deref().expect("fixture rules have labels"))
            .collect::<Vec<_>>();

        assert!(
            labels == ["initial-next1", "next1-final1"]
                || labels == ["initial-next2", "next2-final1"],
            "unexpected witness: {labels:?}"
        );
    }

    #[test]
    fn search_traces_are_always_valid_paths() {
        for definition in [definition(), converging_definition()] {
            for search_type in [
                SearchType::One,
                SearchType::Star,
                SearchType::Plus,
                SearchType::Final,
            ] {
                let result = search_graph(
                    &definition,
                    initial(&definition),
                    SearchOptions {
                        search_type,
                        ..SearchOptions::default()
                    },
                );
                for state in result.states {
                    let mut current = "initial";
                    let mut rewrite_count = 0;
                    for entry in &state.trace {
                        if entry.kind != TraceKind::Rewrite {
                            continue;
                        }
                        let label = entry.label.as_deref().expect("fixture rules have labels");
                        current = match (current, label) {
                            ("initial", "initial-next1") => "next1",
                            ("initial", "initial-next2") => "next2",
                            ("next1", "next1-final1") => "final1",
                            ("next2", "next2-final1") => "final1",
                            ("next2", "next2-final2") => "final2",
                            edge => panic!("invalid trace edge {edge:?} in {:?}", state.trace),
                        };
                        rewrite_count += 1;
                    }
                    assert_eq!(rewrite_count, state.depth, "{:?}", state.trace);
                    assert_eq!(current, state_name(&state), "{:?}", state.trace);
                }
            }
        }
    }

    fn search(search_type: SearchType) -> SearchResult {
        let definition = definition();
        search_graph(
            &definition,
            initial(&definition),
            SearchOptions {
                search_type,
                ..SearchOptions::default()
            },
        )
    }

    #[test]
    fn one_selects_exactly_one_step() {
        let result = search(SearchType::One);
        assert_eq!(
            names(&result),
            BTreeSet::from(["next1".into(), "next2".into()])
        );
        assert!(result.incomplete.is_empty());
    }

    #[test]
    fn star_selects_the_reflexive_transitive_closure() {
        let result = search(SearchType::Star);
        assert_eq!(
            names(&result),
            BTreeSet::from([
                "initial".into(),
                "next1".into(),
                "next2".into(),
                "final1".into(),
                "final2".into(),
            ])
        );
        assert!(result.incomplete.is_empty());
    }

    #[test]
    fn plus_selects_the_strict_transitive_closure() {
        let result = search(SearchType::Plus);
        assert_eq!(
            names(&result),
            BTreeSet::from([
                "next1".into(),
                "next2".into(),
                "final1".into(),
                "final2".into(),
            ])
        );
        assert!(result.incomplete.is_empty());
    }

    #[test]
    fn final_selects_only_irreducible_configurations() {
        let result = search(SearchType::Final);
        assert_eq!(
            names(&result),
            BTreeSet::from(["final1".into(), "final2".into()])
        );
        assert!(result.incomplete.is_empty());
    }

    #[test]
    #[cfg(feature = "z3")]
    fn queued_remainders_follow_normal_search_selection() {
        let definition = conditional_remainder_definition();
        let initial = pattern(&definition, "initial{}(X:SortInt{})");
        let solver = crate::smt::Z3Solver::new(&definition).expect("Z3 should initialize");

        for search_type in [SearchType::Star, SearchType::Plus, SearchType::Final] {
            let options = SearchOptions {
                search_type,
                ..SearchOptions::default()
            };
            let graph = search_graph_with_solver(&definition, initial.clone(), options, &solver);
            assert!(graph.incomplete.is_empty(), "{search_type:?}: {graph:#?}");
            assert_eq!(
                graph
                    .states
                    .iter()
                    .filter(|state| state
                        .trace
                        .iter()
                        .any(|entry| entry.kind == TraceKind::Remainder))
                    .count(),
                1,
                "{search_type:?}: {graph:#?}"
            );

            let paths = search_paths_with_solver(&definition, initial.clone(), options, &solver);
            assert!(paths.incomplete.is_empty(), "{search_type:?}: {paths:#?}");
            assert_eq!(
                paths
                    .witnesses
                    .iter()
                    .filter(|witness| witness
                        .trace
                        .iter()
                        .any(|entry| entry.kind == TraceKind::Remainder))
                    .count(),
                1,
                "{search_type:?}: {paths:#?}"
            );
        }
    }

    #[test]
    fn result_bound_stops_the_breadth_first_search() {
        let definition = definition();
        let result = search_graph(
            &definition,
            initial(&definition),
            SearchOptions {
                search_type: SearchType::One,
                max_results: Some(1),
                ..SearchOptions::default()
            },
        );

        assert_eq!(names(&result), BTreeSet::from(["next1".into()]));
        assert_eq!(result.incomplete, [IncompleteSearch::ResultBound]);
    }

    #[test]
    fn exhausting_the_graph_exactly_at_the_result_bound_is_complete() {
        let definition = definition();
        for (search_type, bound, expected) in [
            (SearchType::One, 2, ["next1", "next2"].as_slice()),
            (SearchType::Final, 2, ["final1", "final2"].as_slice()),
            (
                SearchType::Star,
                5,
                ["initial", "next1", "next2", "final1", "final2"].as_slice(),
            ),
        ] {
            let result = search_graph(
                &definition,
                initial(&definition),
                SearchOptions {
                    search_type,
                    max_results: Some(bound),
                    ..SearchOptions::default()
                },
            );
            assert_eq!(
                names(&result),
                expected.iter().map(|name| (*name).to_owned()).collect(),
                "{search_type:?}"
            );
            assert!(result.incomplete.is_empty(), "{search_type:?}");
        }
    }

    #[test]
    fn result_bound_at_the_depth_bound_still_reports_truncation() {
        let definition = definition();
        let result = search_graph(
            &definition,
            initial(&definition),
            SearchOptions {
                search_type: SearchType::Star,
                max_depth: 1,
                max_results: Some(3),
                ..SearchOptions::default()
            },
        );

        assert_eq!(
            names(&result),
            BTreeSet::from(["initial".into(), "next1".into(), "next2".into()])
        );
        // `next1` was already reported as depth-bound before the result bound fired on `next2`.
        assert!(
            matches!(
                result.incomplete.as_slice(),
                [
                    IncompleteSearch::DepthBound(_),
                    IncompleteSearch::ResultBound
                ]
            ),
            "{:?}",
            result.incomplete
        );
    }

    #[test]
    fn zero_result_bounds_are_reported_as_incomplete() {
        let definition = definition();
        let options = SearchOptions {
            search_type: SearchType::Star,
            max_results: Some(0),
            ..SearchOptions::default()
        };
        let graph = search_graph(&definition, initial(&definition), options);
        assert!(graph.states.is_empty());
        assert_eq!(graph.incomplete, [IncompleteSearch::ResultBound]);

        let target = Pattern {
            term: Term::variable(Variable::new("Result", Sort::simple("SortS"))),
            constraints: Vec::new(),
        };
        let pattern = search_pattern(&definition, initial(&definition), &target, options);
        assert!(pattern.matches.is_empty());
        assert_eq!(pattern.incomplete, [IncompleteSearch::ResultBound]);
    }

    #[test]
    fn pattern_result_bound_reports_mid_collection_truncation() {
        let definition = definition();
        let target = Pattern {
            term: Term::variable(Variable::new("Result", Sort::simple("SortS"))),
            constraints: Vec::new(),
        };
        let result = search_pattern(
            &definition,
            initial(&definition),
            &target,
            SearchOptions {
                search_type: SearchType::Final,
                max_results: Some(1),
                ..SearchOptions::default()
            },
        );

        assert_eq!(result.matches.len(), 1);
        assert_eq!(result.incomplete, [IncompleteSearch::ResultBound]);

        let result = search_pattern(
            &definition,
            initial(&definition),
            &target,
            SearchOptions {
                search_type: SearchType::Final,
                max_results: Some(2),
                ..SearchOptions::default()
            },
        );
        assert_eq!(result.matches.len(), 2);
        assert!(result.incomplete.is_empty());
    }

    #[test]
    fn selective_pattern_bound_skips_nonmatches_and_honors_constraints() {
        let definition = definition();
        let result_variable = result_variable();
        let target = Pattern {
            term: Term::variable(result_variable.clone()),
            constraints: vec![Predicate::Not(Box::new(Predicate::Equals(
                pattern(&definition, "final1{}()").term,
                Term::variable(result_variable.clone()),
            )))],
        };
        let result = search_pattern(
            &definition,
            initial(&definition),
            &target,
            SearchOptions {
                search_type: SearchType::Final,
                max_results: Some(1),
                ..SearchOptions::default()
            },
        );

        assert_eq!(result.matches.len(), 1);
        assert_eq!(
            result.matches[0].substitution[&result_variable],
            pattern(&definition, "final2{}()").term
        );
        assert!(result.matches[0].constraints.is_empty());
        assert!(result.incomplete.is_empty());
    }

    #[test]
    fn duplicate_pattern_projections_do_not_consume_the_bound() {
        let definition = definition();
        let initial = |variable: &str| Pattern {
            term: pattern(&definition, "final1{}()").term,
            constraints: vec![Predicate::Equals(
                Term::variable(Variable::new(variable, Sort::simple("SortS"))),
                pattern(&definition, "final2{}()").term,
            )],
        };
        let alternatives = vec![initial("Hidden1"), initial("Hidden2")];
        let graph = search_graph_disjunction_with_solver_and_observer(
            &definition,
            alternatives.clone(),
            SearchOptions::default(),
            &NoSolver,
            |_| {},
        );
        assert_eq!(graph.states.len(), 2);

        let result = search_pattern_disjunction_with_solver(
            &definition,
            alternatives,
            &pattern(&definition, "final1{}()"),
            SearchOptions {
                max_results: Some(2),
                ..SearchOptions::default()
            },
            &NoSolver,
        );

        assert_eq!(result.matches.len(), 1);
        assert!(result.matches[0].substitution.is_empty());
        assert!(result.matches[0].constraints.is_empty());
        assert!(result.incomplete.is_empty());
    }

    #[test]
    fn bounded_pattern_search_stops_on_an_infinite_result_stream() {
        let definition = infinite_result_definition();
        let result_variable = Variable::new("Result", Sort::simple("SortNat"));
        let target = pattern(&definition, "done{}(Result:SortNat{})");
        let expected = [
            "zero{}()",
            "successor{}(zero{}())",
            "successor{}(successor{}(zero{}()))",
            "successor{}(successor{}(successor{}(zero{}())))",
            "successor{}(successor{}(successor{}(successor{}(zero{}()))))",
        ]
        .map(|source| pattern(&definition, source).term);
        let options = SearchOptions {
            search_type: SearchType::Final,
            max_results: Some(5),
            ..SearchOptions::default()
        };

        let states = search_pattern(
            &definition,
            pattern(&definition, "loop{}(zero{}())"),
            &target,
            options,
        );
        assert_eq!(states.matches.len(), 5);
        assert_eq!(
            states
                .matches
                .iter()
                .map(|found| found.substitution[&result_variable].clone())
                .collect::<Vec<_>>(),
            expected
        );
        assert_eq!(states.incomplete, [IncompleteSearch::ResultBound]);

        let paths = search_pattern_paths(
            &definition,
            pattern(&definition, "loop{}(zero{}())"),
            &target,
            options,
        );
        assert_eq!(paths.matches.len(), 5);
        assert_eq!(
            paths
                .matches
                .iter()
                .map(|found| found.substitution[&result_variable].clone())
                .collect::<Vec<_>>(),
            expected
        );
        assert_eq!(paths.incomplete, [IncompleteSearch::ResultBound]);
    }

    #[test]
    fn zero_pattern_path_bound_does_not_traverse() {
        let definition = infinite_result_definition();
        let result = search_pattern_paths(
            &definition,
            pattern(&definition, "loop{}(zero{}())"),
            &pattern(&definition, "done{}(Result:SortNat{})"),
            SearchOptions {
                search_type: SearchType::Final,
                max_results: Some(0),
                ..SearchOptions::default()
            },
        );

        assert!(result.matches.is_empty());
        assert!(result.effects.is_empty());
        assert_eq!(result.incomplete, [IncompleteSearch::ResultBound]);
    }

    #[test]
    fn breadth_bound_reports_the_live_search_frontier() {
        let definition = definition();
        let result = search_graph(
            &definition,
            initial(&definition),
            SearchOptions {
                max_breadth: Some(1),
                ..SearchOptions::default()
            },
        );

        assert!(result.states.is_empty());
        let [IncompleteSearch::BreadthBound(frontier)] = result.incomplete.as_slice() else {
            panic!(
                "expected a breadth-bound frontier, found {:?}",
                result.incomplete
            );
        };
        assert_eq!(
            frontier
                .iter()
                .map(|state| match state.pattern.term.kind() {
                    TermKind::Application { symbol, .. } => symbol.name.as_ref(),
                    other => panic!("expected an application, found {other:?}"),
                })
                .collect::<Vec<_>>(),
            vec!["next1", "next2"]
        );
    }

    #[test]
    fn zero_breadth_reports_the_initial_search_frontier() {
        let definition = definition();
        let result = search_graph(
            &definition,
            initial(&definition),
            SearchOptions {
                max_breadth: Some(0),
                ..SearchOptions::default()
            },
        );

        assert!(result.states.is_empty());
        let [IncompleteSearch::BreadthBound(frontier)] = result.incomplete.as_slice() else {
            panic!(
                "expected a breadth-bound frontier, found {:?}",
                result.incomplete
            );
        };
        assert_eq!(frontier.len(), 1);
        assert_eq!(frontier[0].depth, 0);
        assert!(matches!(
            frontier[0].pattern.term.kind(),
            TermKind::Application { symbol, .. } if symbol.name.as_ref() == "initial"
        ));
    }

    #[test]
    fn final_search_recognizes_a_normal_form_at_the_depth_bound() {
        let definition = definition();
        let result = search_graph(
            &definition,
            initial(&definition),
            SearchOptions {
                search_type: SearchType::Final,
                max_depth: 2,
                ..SearchOptions::default()
            },
        );

        assert_eq!(
            names(&result),
            BTreeSet::from(["final1".into(), "final2".into()])
        );
        assert_eq!(
            result
                .incomplete
                .iter()
                .filter(|entry| matches!(entry, IncompleteSearch::DepthBound(_)))
                .count(),
            2
        );
    }

    #[test]
    fn final_search_reports_rewritable_states_at_the_depth_bound() {
        let definition = definition();
        let result = search_graph(
            &definition,
            initial(&definition),
            SearchOptions {
                search_type: SearchType::Final,
                max_depth: 1,
                ..SearchOptions::default()
            },
        );

        assert_eq!(
            names(&result),
            BTreeSet::from(["next1".into(), "next2".into()])
        );
        assert_eq!(
            result
                .incomplete
                .iter()
                .filter(|entry| matches!(entry, IncompleteSearch::DepthBound(_)))
                .count(),
            2
        );
    }

    #[test]
    fn final_search_at_depth_zero_reports_the_initial_state() {
        let definition = definition();
        let result = search_graph(
            &definition,
            initial(&definition),
            SearchOptions {
                search_type: SearchType::Final,
                max_depth: 0,
                ..SearchOptions::default()
            },
        );

        assert_eq!(names(&result), BTreeSet::from(["initial".into()]));
        assert!(matches!(
            result.incomplete.as_slice(),
            [IncompleteSearch::DepthBound(state)] if state.depth == 0
        ));
    }

    #[test]
    fn final_search_merges_stuck_and_depth_bound_states() {
        let definition = search_bound_definition();
        for (max_depth, expected) in [
            (2, BTreeSet::from(["c".into(), "d".into()])),
            (3, BTreeSet::from(["c".into(), "e".into()])),
        ] {
            let result = search_graph(
                &definition,
                pattern(&definition, "a{}()"),
                SearchOptions {
                    search_type: SearchType::Final,
                    max_depth,
                    ..SearchOptions::default()
                },
            );

            assert_eq!(names(&result), expected, "depth {max_depth}");
            assert_eq!(
                result
                    .incomplete
                    .iter()
                    .filter(|entry| matches!(entry, IncompleteSearch::DepthBound(_)))
                    .count(),
                1,
                "depth {max_depth}"
            );
        }
    }

    #[test]
    fn final_search_does_not_step_at_the_depth_bound() {
        let definition = rewrite_simplification_failure_definition();
        let result = search_graph(
            &definition,
            pattern(&definition, "initial{}()"),
            SearchOptions {
                search_type: SearchType::Final,
                max_depth: 0,
                max_simplification_iterations: 1,
                ..SearchOptions::default()
            },
        );

        assert_eq!(names(&result), BTreeSet::from(["initial".into()]));
        assert!(matches!(
            result.incomplete.as_slice(),
            [IncompleteSearch::DepthBound(_)]
        ));
    }

    #[test]
    fn vacuous_states_are_never_search_results() {
        let definition = definition();
        let vacuous = Pattern {
            term: initial(&definition).term,
            constraints: vec![Predicate::False],
        };

        for search_type in [
            SearchType::One,
            SearchType::Star,
            SearchType::Plus,
            SearchType::Final,
        ] {
            let result = search_graph(
                &definition,
                vacuous.clone(),
                SearchOptions {
                    search_type,
                    max_depth: 0,
                    ..SearchOptions::default()
                },
            );
            assert!(result.states.is_empty(), "{search_type:?}");
        }
    }

    #[test]
    fn search_frontier_recombines_paths_that_reach_a_configuration_at_the_same_depth() {
        // Kore's execution graph recombines branches that converge to the same configuration
        // at the same step (Strategy.hs, constructExecutionGraph), and the LLVM backend's search
        // keeps a visited set; either way a configuration is expanded once per depth, so the
        // work per step is bounded by the number of distinct configurations, not by the
        // number of interleavings that reach them.
        let definition = interleaving_definition();
        let initial = pattern(&definition, "state{}(a0{}(), b0{}(), c0{}())");

        // Within six steps: 54 configurations, each rule application is one of the 114 edges
        // of the state graph below the cut, and the cut holds each of its ten configurations
        // once (510 interleavings reach them).
        let result = search_graph(
            &definition,
            initial.clone(),
            SearchOptions {
                search_type: SearchType::Star,
                max_depth: 6,
                ..SearchOptions::default()
            },
        );
        assert_eq!(result.states.len(), 54);
        let cut = result
            .incomplete
            .iter()
            .map(|entry| match entry {
                IncompleteSearch::DepthBound(state) => &state.pattern.term,
                other => panic!("expected a depth-bound report, found {other:?}"),
            })
            .collect::<Vec<_>>();
        assert_eq!(cut.iter().collect::<BTreeSet<_>>().len(), 10);
        assert_eq!(cut.len(), 10);
        assert_eq!(result.effects.len(), 114);

        // The complete final search: one final configuration reached by 144 rule applications,
        // the edges of the lattice, not the 5247 edges of the interleaving tree.
        let result = search_graph(
            &definition,
            initial,
            SearchOptions {
                search_type: SearchType::Final,
                ..SearchOptions::default()
            },
        );
        assert_eq!(
            result
                .states
                .iter()
                .map(|state| state.pattern.term.clone())
                .collect::<Vec<_>>(),
            vec![pattern(&definition, "state{}(a3{}(), b3{}(), c3{}())").term]
        );
        assert!(result.incomplete.is_empty(), "{:?}", result.incomplete);
        assert_eq!(result.effects.len(), 144);
    }

    #[test]
    fn final_path_search_reports_witnesses_at_the_depth_bound() {
        let definition = definition();
        let result = search_paths(
            &definition,
            initial(&definition),
            SearchOptions {
                search_type: SearchType::Final,
                max_depth: 1,
                ..SearchOptions::default()
            },
        );

        assert_eq!(
            result
                .witnesses
                .iter()
                .map(|witness| match witness.pattern.term.kind() {
                    TermKind::Application { symbol, .. } => symbol.name.to_string(),
                    other => panic!("expected an application, found {other:?}"),
                })
                .collect::<BTreeSet<_>>(),
            BTreeSet::from(["next1".into(), "next2".into()])
        );
        assert_eq!(
            result
                .incomplete
                .iter()
                .filter(|entry| matches!(entry, IncompleteSearch::DepthBound(_)))
                .count(),
            2
        );
    }

    #[test]
    fn pattern_search_returns_substitutions_for_matching_states() {
        let definition = definition();
        let result_variable = Variable::new("Result", Sort::simple("SortS"));
        let target = Pattern {
            term: Term::variable(result_variable.clone()),
            constraints: Vec::new(),
        };

        let result = search_pattern(
            &definition,
            initial(&definition),
            &target,
            SearchOptions {
                search_type: SearchType::Final,
                ..SearchOptions::default()
            },
        );

        assert_eq!(result.matches.len(), 2);
        assert_eq!(
            result
                .matches
                .iter()
                .map(|found| match found.substitution[&result_variable].kind() {
                    TermKind::Application { symbol, .. } => symbol.name.to_string(),
                    other => panic!("expected an application, found {other:?}"),
                })
                .collect::<BTreeSet<_>>(),
            BTreeSet::from(["final1".into(), "final2".into()])
        );
        assert!(result.incomplete.is_empty());
    }

    #[test]
    fn matches_each_disjunction_alternative_independently() {
        let definition = definition();
        let result_variable = Variable::new("Result", Sort::simple("SortS"));
        let target = Pattern {
            term: Term::variable(result_variable.clone()),
            constraints: Vec::new(),
        };
        let subjects = [
            pattern(&definition, "final1{}()"),
            pattern(&definition, "final2{}()"),
        ];

        let matches = match_disjunction(&definition, &target, &subjects).unwrap();

        assert_eq!(matches.len(), 2);
        assert_eq!(
            matches
                .iter()
                .map(|found| match found.substitution[&result_variable].kind() {
                    TermKind::Application { symbol, .. } => symbol.name.to_string(),
                    other => panic!("expected an application, found {other:?}"),
                })
                .collect::<BTreeSet<_>>(),
            BTreeSet::from(["final1".into(), "final2".into()])
        );
        assert!(matches.iter().all(|found| found.constraints.is_empty()));
    }

    #[test]
    fn disjunction_matching_returns_top_only_for_an_exact_alternative() {
        let definition = definition();
        let target = initial(&definition);
        let absent = [
            pattern(&definition, "final1{}()"),
            pattern(&definition, "final2{}()"),
        ];
        let present = [pattern(&definition, "final1{}()"), initial(&definition)];

        assert!(
            match_disjunction(&definition, &target, &absent)
                .unwrap()
                .is_empty()
        );
        assert_eq!(
            match_disjunction(&definition, &target, &present).unwrap(),
            vec![PatternMatch {
                substitution: Substitution::new(),
                constraints: Vec::new(),
            }]
        );
    }

    #[test]
    fn disjunction_matching_retains_predicates_without_an_smt_decision() {
        let definition = definition();
        let variable = Term::variable(Variable::new("X", Sort::simple("SortS")));
        let unresolved = Predicate::Not(Box::new(Predicate::Equals(
            variable,
            pattern(&definition, "final1{}()").term,
        )));
        let subject = Pattern {
            term: initial(&definition).term,
            constraints: vec![unresolved.clone()],
        };

        let matches = match_disjunction(&definition, &initial(&definition), &[subject]).unwrap();

        assert_eq!(
            matches,
            vec![PatternMatch {
                substitution: Substitution::new(),
                constraints: vec![unresolved],
            }]
        );
    }

    #[test]
    fn concrete_pattern_search_reports_reachability() {
        let definition = definition();
        let target = pattern(&definition, "initial{}()");

        let reachable = search_pattern(
            &definition,
            initial(&definition),
            &target,
            SearchOptions {
                search_type: SearchType::Star,
                ..SearchOptions::default()
            },
        );
        let unreachable = search_pattern(
            &definition,
            initial(&definition),
            &target,
            SearchOptions {
                search_type: SearchType::Final,
                ..SearchOptions::default()
            },
        );

        assert_eq!(reachable.matches.len(), 1);
        assert!(reachable.matches[0].substitution.is_empty());
        assert!(unreachable.matches.is_empty());
    }

    #[test]
    fn constrained_kore_search_patterns_filter_solutions() {
        let definition = definition();
        let syntax = parse_pattern(
            r#"\and{SortS{}}(
                Result:SortS{},
                \equals{SortS{}, SortS{}}(Result:SortS{}, final1{}())
            )"#,
        )
        .expect("constrained target should parse");
        let target = definition
            .internalize_pattern(&syntax, &[])
            .expect("constrained target should internalize");

        let result = search_pattern(
            &definition,
            initial(&definition),
            &target,
            SearchOptions {
                search_type: SearchType::Final,
                ..SearchOptions::default()
            },
        );

        assert_eq!(result.matches.len(), 1);
        assert!(result.matches[0].constraints.is_empty());
        assert!(result.incomplete.is_empty());
    }

    #[test]
    fn projects_solved_path_equalities_onto_search_variables() {
        let sort = Sort::simple("SortS");
        let result_variable = Variable::new("Result", sort.clone());
        let configuration_variable = Variable::new("Configuration", sort.clone());
        let left = Variable::new("Left", sort.clone());
        let right = Variable::new("Right", sort.clone());
        let value = Term::application(
            Arc::new(Symbol::constructor(
                "arrow",
                vec![sort.clone(), sort.clone()],
                sort,
            )),
            Vec::new(),
            vec![Term::variable(left), Term::variable(right)],
        );

        let (output, constraints) = normalize_match_condition(
            Substitution::from([(
                result_variable.clone(),
                Term::variable(configuration_variable.clone()),
            )]),
            vec![Predicate::Equals(
                Term::variable(configuration_variable),
                value.clone(),
            )],
            &BTreeSet::from([result_variable.clone()]),
        );

        assert_eq!(output, Substitution::from([(result_variable, value)]));
        assert!(constraints.is_empty());
    }

    /// `start() => wrap(f(partial("v")))` with `f(I) => I`: the loop head of the successor
    /// applies the equation and carries `\ceil(partial("v"))`, which `wrap` (a total context)
    /// entails. Every reported result is externalised in the simplifier's normal form, so
    /// neither the state result nor the path witness carries the conjunct. The equation fires
    /// inside the rewrite step's result simplification, and the externalisation applies
    /// nothing, so the trace has no simplification entry.
    fn discarded_operand_definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module SEARCH
                sort SortS{} [hasDomainValues{}()]
                sort SortC{} []
                symbol start{}() : SortC{} [constructor{}()]
                symbol wrap{}(SortS{}) : SortC{} [constructor{}()]
                symbol partial{}(SortS{}) : SortS{} [function{}()]
                symbol f{}(SortS{}) : SortS{} [function{}(), total{}()]
                axiom{R} \implies{R}(\top{R}(), \equals{SortS{}, R}(
                    f{}(I:SortS{}), \and{SortS{}}(I:SortS{}, \top{SortS{}}())
                )) [label{}("identity"), simplification{}()]
                axiom{} \rewrites{SortC{}}(
                    \and{SortC{}}(start{}(), \top{SortC{}}()),
                    wrap{}(f{}(partial{}(\dv{SortS{}}("v"))))
                ) [label{}("step")]
            endmodule []"#,
        )
        .expect("discarded-operand definition should parse");
        BackendDefinition::internalize(&syntax, "SEARCH")
            .expect("discarded-operand definition should internalize")
    }

    #[test]
    fn final_results_are_externalised_in_the_simplifier_normal_form() {
        let definition = discarded_operand_definition();
        let options = SearchOptions {
            search_type: SearchType::Final,
            ..SearchOptions::default()
        };
        let expected = pattern(&definition, r#"wrap{}(partial{}(\dv{SortS{}}("v")))"#);
        let simplification_ids = |trace: &[TraceEntry]| {
            trace
                .iter()
                .filter(|entry| entry.kind == TraceKind::Simplification)
                .map(|entry| entry.unique_id.clone())
                .collect::<Vec<_>>()
        };

        let graph = search_graph(&definition, pattern(&definition, "start{}()"), options);
        assert!(graph.incomplete.is_empty(), "{:?}", graph.incomplete);
        let [state] = graph.states.as_slice() else {
            panic!("expected one final state, found {:?}", graph.states);
        };
        assert_eq!(state.pattern, expected, "{state:#?}");
        assert_eq!(simplification_ids(&state.trace), Vec::<String>::new());

        let paths = search_paths(&definition, pattern(&definition, "start{}()"), options);
        assert!(paths.incomplete.is_empty(), "{:?}", paths.incomplete);
        let [witness] = paths.witnesses.as_slice() else {
            panic!("expected one witness, found {:?}", paths.witnesses);
        };
        assert_eq!(witness.pattern, expected, "{witness:#?}");
        assert_eq!(simplification_ids(&witness.trace), Vec::<String>::new());
    }
}
