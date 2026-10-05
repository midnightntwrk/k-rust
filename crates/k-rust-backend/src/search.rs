//! ```toml algorithm
//! id = "backend.search.configurations"
//! name = "breadth-first search over configurations"
//! sites = ["search_graph_using", "search_graph_collecting", "materialize_search_state"]
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
//! sites = ["search_paths_using", "search_paths_collecting"]
//! variable = "d = path depth; b = branching factor"
//! counters = []
//! no_counter = "path enumeration has no dedicated counter"
//! span = "per problem"
//! consumes = [{ type = "k_rust_backend::rewrite::RewriteResult", role = "rewrite result" }]
//!
//! [[cost]]
//! mode = "simple paths"
//! bound = "exponential in b and d, plus O(d) visited-list work per pop and O(KORE text bytes) per transition for the returned path identity; digest memory is O(printer traversal stack)"
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
//! bound = """\
//! O(m) matches, each followed by one predicate simplification and at most one is_sat, plus \
//! O(k) comparisons per retained match, plus the selected rewrite-search strategy; a match \
//! whose subject or target has a term that is not ceil_free also computes the subject's \
//! pattern_knowledge (condition_definedness of its constraints and ceil_term of its term) and \
//! condition_definedness of the instantiated target constraints, and the knowledge members not \
//! among the subject's constraints are simplified once on their own (a member simplified to \
//! bottom ends the match with no match) before they join the simplification and the is_sat \
//! query as known facts, while a ceil_free subject and target cost one stored-attribute read \
//! per term"""
//! ```
//!
//! ```toml algorithm
//! id = "backend.substitution.extract_output"
//! name = "output-restricted substitution extraction"
//! sites = ["normalize_match_condition"]
//! variable = """\
//! c = constraints; t = term size; f = the subject's knowledge facts decided with the condition"""
//! counters = []
//! no_counter = "output-restricted extraction has no dedicated counter"
//! span = "per call"
//! variant_of = "backend.substitution.extract"
//!
//! [[cost]]
//! mode = "search result normalization"
//! bound = """\
//! O(c^2 x t), plus for each solved binding whose value is not ceil_free one ceil_term walk of \
//! the value and O((c + f) x t) membership comparisons per obligation it yields, and, when f > \
//! 0, O(f x t) per solved binding to eliminate it from the facts (a binding from the subject's \
//! own constraints) or to move the facts it rewrites into the constraints (any other binding, \
//! which also reads the variable sets of the c constraints)"""
//! ```
//!
//! Breadth-first search over configurations with `(depth, pattern, is_rewritable)`
//! deduplication, the pattern compared up to the names of the variables the request did not
//! name (`RequestNames::state_key`, a canonical numbering per state), O(distinct states per
//! depth) rewrite steps, `Counter::SearchStatesDeduplicated`; breadth-first enumeration of
//! simple paths with a per-path visited list of the same keys, exponential in branching plus
//! O(depth) per pop; pattern search over the result set. A state result, and a pattern
//! search's solution (`RequestNames::solution_key`), is retained once up to the same renaming,
//! one key per result. `normalize_match_condition` is the
//! output-restricted variant of substitution extraction, O(c^2 x t) for c constraints plus the
//! definedness of each solved value that is not `ceil_free`, no counter.

#![deny(clippy::wildcard_enum_match_arm)]

use std::collections::{BTreeSet, HashSet, VecDeque};

use k_rust_kore::measure::{self, Algorithm, Counter};

use crate::{
    builtin::BuiltinEffect,
    condition::{eliminate_bindings, instantiate_constraints},
    definedness::{FactsVerdict, UndecidedFacts, knowledge_facts, pattern_knowledge},
    definition::BackendDefinition,
    diagnostic::{self, BackendDiagnostic, PathDiagnostics, extend_distinct},
    fresh::{FreshCounter, RequestNames},
    matching::{MatchMode, MatchResult, match_terms_in_definition},
    rewrite::{
        AppliedRule, IndeterminateReason, Pattern, RemainderBranch, RewriteResult, TraceEntry,
        TraceKind, Truth, UndecidedStep, predicates_truth, rewrite_step_with_options,
        simplify_result_pattern,
    },
    rule::Predicate,
    simplify::{
        DEFAULT_MAX_SIMPLIFICATION_ITERATIONS, SimplificationError, SimplificationOptions,
        simplify_predicates_with_solver, simplify_with_solver,
    },
    smt::{NoSolver, Satisfiability, SmtError, SmtSolver},
    stop::{self, Stop, StopCause, Stoppable},
    substitution::{Substitution, compose, substitute},
    transition::{ObservationEvent, ObservationHead, ObservationLog, ObservationOptions},
};

mod retention;

pub use retention::{BreadthExceeded, Exhausted, FurtherResult, Truncation, UnexploredWork};
use retention::{
    Remaining, StateRetention, WitnessRetention, breadth_exceeded, pop_or_exhausted, remaining,
    retain_pattern_match, retain_state_result, retain_witness,
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SearchOptions {
    pub search_type: SearchType,
    pub max_depth: u64,
    pub max_breadth: Option<usize>,
    pub max_results: Option<usize>,
    pub max_simplification_iterations: usize,
    /// Further names of the request: the spellings of its patterns as the caller received them
    /// (`RequestNames::of_received`), which unfolding their aliases may have dropped from the
    /// internalized patterns. The search mints no name spelled like one of them, nor like a
    /// variable of its initial patterns or target (`fresh::FreshCounter`).
    pub request_names: RequestNames,
}

impl Default for SearchOptions {
    fn default() -> Self {
        Self {
            search_type: SearchType::Final,
            max_depth: u64::MAX,
            max_breadth: None,
            max_results: None,
            max_simplification_iterations: DEFAULT_MAX_SIMPLIFICATION_ITERATIONS,
            request_names: RequestNames::default(),
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

/// A state, or a frontier, whose exploration the search did not finish.
///
/// Every entry concerns the states it lists; why the whole search stopped is the result's
/// [`SearchEnd`].
///
/// A stop of a state's simplification is not one of its failures: it arrives on the outer layer
/// of the simplifier's result, so recording it as the state's failure does not compile:
///
/// ```compile_fail,E0308
/// use k_rust_backend::{
///     definition::BackendDefinition,
///     rule::Predicate,
///     search::{IncompleteSearch, SearchState},
///     simplify::{SimplificationOptions, simplify_predicates_with_solver},
///     smt::NoSolver,
/// };
///
/// fn constraints(
///     definition: &BackendDefinition,
///     state: SearchState,
/// ) -> Result<Vec<Predicate>, IncompleteSearch> {
///     let options = SimplificationOptions::default();
///     let predicates = state.pattern.constraints.clone();
///     Ok(match simplify_predicates_with_solver(definition, &predicates, &[], options, &NoSolver) {
///         Ok(Ok(constraints)) => constraints,
///         Ok(Err(error)) => return Err(IncompleteSearch::Simplification { state, error }),
///         Err(error) => return Err(IncompleteSearch::Simplification { state, error }),
///     })
/// }
/// ```
///
/// It is the state's `Stopped` entry, with its cause:
///
/// ```
/// use k_rust_backend::{
///     definition::BackendDefinition,
///     rule::Predicate,
///     search::{IncompleteSearch, SearchState},
///     simplify::{SimplificationOptions, simplify_predicates_with_solver},
///     smt::NoSolver,
/// };
///
/// fn constraints(
///     definition: &BackendDefinition,
///     state: SearchState,
/// ) -> Result<Vec<Predicate>, IncompleteSearch> {
///     let options = SimplificationOptions::default();
///     let predicates = state.pattern.constraints.clone();
///     Ok(match simplify_predicates_with_solver(definition, &predicates, &[], options, &NoSolver) {
///         Ok(Ok(constraints)) => constraints,
///         Ok(Err(error)) => return Err(IncompleteSearch::Simplification { state, error }),
///         Err(stop) => return Err(IncompleteSearch::Stopped { state, cause: stop.into_cause() }),
///     })
/// }
/// ```
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum IncompleteSearch {
    DepthBound(SearchState),
    BreadthBound(Vec<SearchState>),
    Indeterminate {
        state: SearchState,
        reason: IndeterminateReason,
    },
    /// The state's exploration stopped before it produced its answer. A cancelled request or a
    /// failed solver prelude ends the search: the state whose exploration observed it is listed
    /// here, and the search ends with [`SearchEnd::Stopped`]. When a target-pattern match
    /// observed it, the matched state is listed here and the search ends at the next state's
    /// poll with [`SearchEnd::Stopped`] or, when no state remains, with
    /// [`SearchEnd::Exhausted`]. An exhausted stack (or a step deadline a caller armed around the
    /// search) ends this state only. A result whose exploration returned before the stop is
    /// published: no answer in it is missing.
    Stopped {
        state: SearchState,
        cause: StopCause,
    },
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

/// Why a search's exploration ended. `E` is what a result bound states about the results beyond
/// the retained ones.
///
/// The ends that claim something about the work left behind need evidence only the search can
/// mint: a completeness claim needs an [`Exhausted`] token, a result bound its evidence `E`, a
/// breadth bound a [`BreadthExceeded`] token. Outside this crate such an end can be read but
/// not built. A completeness claim does not compile:
///
/// ```compile_fail
/// use k_rust_backend::search::{Exhausted, SearchEnd, UnexploredWork};
///
/// fn exhausted(end: &SearchEnd<UnexploredWork>) -> bool {
///     *end == SearchEnd::<UnexploredWork>::Exhausted(Exhausted(()))
/// }
/// ```
///
/// while reading one does:
///
/// ```
/// use k_rust_backend::search::{SearchEnd, UnexploredWork};
///
/// fn exhausted(end: &SearchEnd<UnexploredWork>) -> bool {
///     matches!(end, SearchEnd::Exhausted(_))
/// }
/// ```
///
/// Likewise a result bound's evidence does not compile:
///
/// ```compile_fail
/// use k_rust_backend::search::{SearchEnd, UnexploredWork};
///
/// fn result_bound(end: &SearchEnd<UnexploredWork>) -> bool {
///     *end == SearchEnd::ResultBound(UnexploredWork(()))
/// }
/// ```
///
/// while reading it does:
///
/// ```
/// use k_rust_backend::search::{SearchEnd, UnexploredWork};
///
/// fn result_bound(end: &SearchEnd<UnexploredWork>) -> bool {
///     matches!(end, SearchEnd::ResultBound(_))
/// }
/// ```
#[must_use]
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SearchEnd<E> {
    /// Nothing remained: every state reached within the bounds was explored or is listed among
    /// the result's incomplete entries.
    Exhausted(Exhausted),
    /// The search stopped with its result bound reached, and `E` states what lies beyond.
    ResultBound(E),
    /// The frontier exceeded `max_breadth`; it is the result's
    /// [`IncompleteSearch::BreadthBound`] entry.
    BreadthBound(BreadthExceeded),
    /// The search stopped before exploring what remained, for the cause given; the state being
    /// explored is listed as an [`IncompleteSearch::Stopped`] entry with the same cause.
    Stopped(StopCause),
}

/// A state-set search's results.
///
/// A result states why its search ended; a literal without an [`end`](Self::end) does not
/// compile:
///
/// ```compile_fail
/// use k_rust_backend::search::SearchResult;
///
/// let result = SearchResult { states: vec![], effects: vec![], incomplete: vec![] };
/// ```
///
/// ```
/// use k_rust_backend::{search::{SearchEnd, SearchResult}, stop::StopCause};
///
/// let result = SearchResult { states: vec![], effects: vec![], incomplete: vec![], end:
/// SearchEnd::Stopped(StopCause::Cancelled) };
/// ```
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SearchResult {
    pub states: Vec<SearchState>,
    pub effects: Vec<BuiltinEffect>,
    /// The states whose exploration was not finished.
    pub incomplete: Vec<IncompleteSearch>,
    pub end: SearchEnd<UnexploredWork>,
}

impl SearchResult {
    pub const fn modality(&self) -> ResultModality {
        ResultModality::StateSet
    }

    /// Whether `states` is every result within the bounds: nothing remained and no state's
    /// exploration was left unfinished.
    pub fn is_complete(&self) -> bool {
        is_complete(&self.end, &self.incomplete)
    }
}

fn is_complete<E>(end: &SearchEnd<E>, incomplete: &[IncompleteSearch]) -> bool {
    matches!(end, SearchEnd::Exhausted(_)) && incomplete.is_empty()
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
    /// The states whose exploration was not finished.
    pub incomplete: Vec<IncompleteSearch>,
    pub end: SearchEnd<Truncation>,
}

impl PathSearchResult {
    pub const fn modality(&self) -> ResultModality {
        ResultModality::PathSet
    }

    /// Whether `witnesses` is every result within the bounds: nothing remained and no state's
    /// exploration was left unfinished.
    pub fn is_complete(&self) -> bool {
        is_complete(&self.end, &self.incomplete)
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
    /// The states whose exploration was not finished.
    pub incomplete: Vec<IncompleteSearch>,
    pub end: SearchEnd<UnexploredWork>,
}

impl PatternSearchResult {
    pub const fn modality(&self) -> ResultModality {
        ResultModality::StateSet
    }

    /// Whether `matches` is every result within the bounds: nothing remained and no state's
    /// exploration was left unfinished.
    pub fn is_complete(&self) -> bool {
        is_complete(&self.end, &self.incomplete)
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
    /// The states whose exploration was not finished.
    pub incomplete: Vec<IncompleteSearch>,
    pub end: SearchEnd<Truncation>,
}

impl PatternPathSearchResult {
    pub const fn modality(&self) -> ResultModality {
        ResultModality::PathSet
    }

    /// Whether `matches` is every result within the bounds: nothing remained and no state's
    /// exploration was left unfinished.
    pub fn is_complete(&self) -> bool {
        is_complete(&self.end, &self.incomplete)
    }
}

/// Match a constrained pattern against each alternative in a disjunction.
///
/// An alternative with no instance by its own definedness (a partial subterm of its term, or an
/// obligation of its constraints, that is false) has no match.
///
/// The result has two layers: the outer `Err` is a [`Stop`], for which no match was decided; the
/// inner result is the matches, or why one of them could not be decided.
pub fn match_disjunction(
    definition: &BackendDefinition,
    target: &Pattern,
    subjects: &[Pattern],
) -> Stoppable<Result<Vec<PatternMatch>, PatternMatchError>> {
    match_disjunction_using(
        definition,
        target,
        subjects,
        SimplificationOptions::default(),
        &NoSolver,
        true,
    )
}

/// Match a constrained pattern against each alternative using the supplied SMT solver, with the
/// two layers of [`match_disjunction`].
pub fn match_disjunction_with_solver(
    definition: &BackendDefinition,
    target: &Pattern,
    subjects: &[Pattern],
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Stoppable<Result<Vec<PatternMatch>, PatternMatchError>> {
    match_disjunction_using(definition, target, subjects, options, solver, false)
}

fn match_disjunction_using(
    definition: &BackendDefinition,
    target: &Pattern,
    subjects: &[Pattern],
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
    retain_unknown: bool,
) -> Stoppable<Result<Vec<PatternMatch>, PatternMatchError>> {
    let _span = measure::algorithm_span(Algorithm::BackendSearchPatterns);
    let output_variables = pattern_variables(target);
    let mut matches = Vec::new();
    for subject in subjects {
        let found = match match_pattern_with_variables(
            definition,
            target,
            subject,
            &output_variables,
            options,
            solver,
            retain_unknown,
        )? {
            Ok(found) => found,
            Err(error) => return Ok(Err(error)),
        };
        let Some(found) = found else {
            continue;
        };
        if !matches.contains(&found) {
            matches.push(found);
        }
    }
    Ok(Ok(matches))
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
        RequestNames::default(),
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
    request: RequestNames,
    options: SearchOptions,
    solver: &dyn SmtSolver,
    observation: Option<&ObservationOptions>,
    mut observe: impl FnMut(&BuiltinEffect),
    mut pattern_bound_reached: impl FnMut(&SearchState) -> bool,
) -> SearchResult {
    let _span = measure::algorithm_span(Algorithm::BackendSearchConfigurations);
    let mut observation_log = ObservationLog::default();
    let request_diagnostics = PathDiagnostics::new_request();
    let mut states = Vec::new();
    // The `RequestNames::state_key` of every state in `states`.
    let mut retained = HashSet::new();
    let mut effects = Vec::new();
    let mut incomplete = Vec::new();
    // One request: every name the search mints is apart from every variable of the initial
    // patterns and of the target it matches them against.
    let mut fresh_counter = {
        let mut names = RequestNames::of(&initial.iter().collect::<Vec<_>>());
        names.extend(&request);
        names.extend(&options.request_names);
        FreshCounter::for_request_names(names)
    };
    // The search is over states, not over paths. Two work states at one depth whose simplified
    // patterns are equal up to the names of the variables the request did not name (their
    // `RequestNames::state_key`s are equal) denote the same configurations and have the same
    // successors up to that renaming, so the second is dropped here, which bounds the work per
    // step by the number of distinct states rather than by the number of interleavings that
    // reach them. Comparing the patterns by name instead would keep two branches that each
    // introduced a variable apart, since the request's counter names the two variables apart.
    let mut expanded: HashSet<(u64, Pattern, bool)> = HashSet::new();

    let mut pending = VecDeque::with_capacity(initial.len());
    // Invariant: `pending` holds, in input order, the initial states without a surviving macro or
    // alias symbol, and `incomplete` one entry per other initial state.
    for pattern in initial {
        let work = SearchWorkState {
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
        };
        if let Some(symbol) = work.state.pattern.macro_or_alias_symbol() {
            incomplete.push(IncompleteSearch::Indeterminate {
                state: work.materialize(&observation_log),
                reason: IndeterminateReason::SurvivingMacroOrAlias { symbol },
            });
        } else {
            pending.push_back(work);
        }
    }

    // A zero breadth bound is exceeded by any initial state; a zero result bound stops before
    // the first state, leaving the initial states unexplored.
    if options.max_breadth == Some(0)
        && let Some(exceeded) =
            breadth_exceeded(&mut pending, &mut incomplete, options.max_breadth, |work| {
                work.materialize(&observation_log)
            })
    {
        return SearchResult {
            states,
            effects,
            incomplete,
            end: SearchEnd::BreadthBound(exceeded),
        };
    }
    if options.max_results == Some(0) {
        return SearchResult {
            states,
            effects,
            incomplete,
            end: remaining(&pending, || false).result_bound(|unexplored| unexplored),
        };
    }

    // `pending` is FIFO, so popped depths never decrease; `expanded` holds the key of every
    // `(depth, simplified pattern)` expanded so far, so a state is expanded once per depth.
    // Invariant: `pending` holds unexpanded states no deeper than `max_depth`; `states` only grows.
    let end = loop {
        let work = match pop_or_exhausted(&mut pending) {
            Ok(work) => work,
            Err(exhausted) => break SearchEnd::Exhausted(exhausted),
        };
        // Publish a stop of the state's exploration as its `Stopped` entry; the search ends when
        // the stop ends every remaining state ([`stop_ends_search`]). Never falls through.
        macro_rules! publish_stop {
            ($state:expr, $stop:expr) => {{
                let cause = Stop::into_cause($stop);
                incomplete.push(IncompleteSearch::Stopped {
                    state: $state,
                    cause: cause.clone(),
                });
                if stop_ends_search(&cause) {
                    break SearchEnd::Stopped(cause);
                }
                continue;
            }};
        }
        if let Err(stop) = stop::check() {
            publish_stop!(work.materialize(&observation_log), stop);
        }
        let SearchWorkState {
            mut state,
            observation: mut observation_head,
            mut diagnostics,
            kind,
        } = work;
        let is_rewritable = matches!(kind, QueuedStateKind::Rewritable);
        if let Some(symbol) = state.pattern.macro_or_alias_symbol() {
            incomplete.push(IncompleteSearch::Indeterminate {
                state: materialize_search_state(
                    state,
                    observation_head,
                    &diagnostics,
                    &observation_log,
                ),
                reason: IndeterminateReason::SurvivingMacroOrAlias { symbol },
            });
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
            Ok(Ok(constraints)) => state.pattern.constraints = constraints,
            Ok(Err(error)) => {
                incomplete.push(IncompleteSearch::Simplification {
                    state: materialize_search_state(
                        state,
                        observation_head,
                        &diagnostics,
                        &observation_log,
                    ),
                    error,
                });
                continue;
            }
            Err(stop) => publish_stop!(
                materialize_search_state(state, observation_head, &diagnostics, &observation_log),
                stop
            ),
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
            Ok(Ok(simplified)) => {
                let simplified = simplified.into_parts();
                state.pattern.term = simplified.term;
                state.pattern.constraints.extend(simplified.conditions);
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
            Ok(Err(error)) => {
                incomplete.push(IncompleteSearch::Simplification {
                    state: materialize_search_state(
                        state,
                        observation_head,
                        &diagnostics,
                        &observation_log,
                    ),
                    error,
                });
                continue;
            }
            Err(stop) => publish_stop!(
                materialize_search_state(state, observation_head, &diagnostics, &observation_log),
                stop
            ),
        }

        // Kore's Simplify primitive turns a false-constrained configuration into a Bottom node,
        // which has no program state and cannot be selected by a search strategy.
        if predicates_truth(&state.pattern.constraints) == Truth::False {
            continue;
        }
        // So is an initial state whose own definedness is refuted: it has no instance.
        match initial_state_is_empty(
            definition,
            &state,
            is_rewritable,
            options.max_simplification_iterations,
            solver,
            &mut diagnostics,
        ) {
            Ok(true) => continue,
            Ok(false) => {}
            Err(stop) => publish_stop!(
                materialize_search_state(state, observation_head, &diagnostics, &observation_log),
                stop
            ),
        }
        // A duplicate takes its own path's diagnostics with it: the state kept for this key
        // reports the path recorded first, like its trace.
        if !expanded.insert((
            state.depth,
            fresh_counter.request().state_key(&state.pattern),
            is_rewritable,
        )) {
            measure::bump(Counter::SearchStatesDeduplicated);
            continue;
        }
        let at_depth_bound = state.depth >= options.max_depth;
        let is_result = selects_reachable_state(options.search_type, state.depth)
            || (options.search_type == SearchType::Final && at_depth_bound);
        let retention = if is_result {
            match externalise_result(
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
            ) {
                Ok(Some(result)) => retain_state_result(
                    &mut states,
                    &mut retained,
                    fresh_counter.request(),
                    result,
                    options.max_results,
                    &mut pattern_bound_reached,
                ),
                Ok(None) => StateRetention::Continue,
                Err(cause) if stop_ends_search(&cause) => break SearchEnd::Stopped(cause),
                // The state's result is not known, but its successors can still be explored.
                Err(_) => StateRetention::Continue,
            }
        } else {
            StateRetention::Continue
        };
        // A `Final` search selects this state before its step only at the depth bound, where
        // the state has no successor within the bounds; any other selected state may still have
        // successors.
        let may_expand = |fresh_counter: &mut FreshCounter| {
            options.search_type != SearchType::Final
                && state_may_expand(
                    definition,
                    &state,
                    is_rewritable,
                    &options,
                    fresh_counter,
                    solver,
                )
        };
        match retention {
            StateRetention::ResultBound => {
                break remaining(&pending, || may_expand(&mut fresh_counter))
                    .result_bound(|unexplored| unexplored);
            }
            StateRetention::PatternBound => {
                match remaining(&pending, || may_expand(&mut fresh_counter)) {
                    Remaining::Unexplored(unexplored) => break SearchEnd::ResultBound(unexplored),
                    // The state continues through the loop body; the loop head observes the
                    // empty frontier.
                    Remaining::Exhausted(_) => {}
                }
            }
            StateRetention::Continue => {}
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
            &options,
            solver,
        );
        // A stopped step has no successor set: the state's entry carries the step's work.
        let rewrite = match rewrite {
            Ok(rewrite) => rewrite,
            Err(stop) => {
                diagnostics.extend(&step_diagnostics);
                publish_stop!(
                    materialize_search_state(
                        state,
                        observation_head,
                        &diagnostics,
                        &observation_log
                    ),
                    stop
                );
            }
        };
        if halts(&rewrite) {
            diagnostics.extend(&step_diagnostics);
        }
        match rewrite {
            RewriteResult::Stuck(pattern) => {
                if options.search_type != SearchType::Final {
                    continue;
                }
                state.pattern = pattern;
                let retention = match externalise_result(
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
                ) {
                    Ok(Some(result)) => retain_state_result(
                        &mut states,
                        &mut retained,
                        fresh_counter.request(),
                        result,
                        options.max_results,
                        &mut pattern_bound_reached,
                    ),
                    Ok(None) => StateRetention::Continue,
                    Err(cause) if stop_ends_search(&cause) => break SearchEnd::Stopped(cause),
                    Err(_) => StateRetention::Continue,
                };
                // A stuck state has no successor: only the frontier can remain.
                match retention {
                    StateRetention::ResultBound => {
                        break remaining(&pending, || false).result_bound(|unexplored| unexplored);
                    }
                    StateRetention::PatternBound => match remaining(&pending, || false) {
                        Remaining::Unexplored(unexplored) => {
                            break SearchEnd::ResultBound(unexplored);
                        }
                        Remaining::Exhausted(_) => {}
                    },
                    StateRetention::Continue => {}
                }
            }
            RewriteResult::Trivial(_, _) | RewriteResult::Vacuous(_) => {}
            RewriteResult::Indeterminate { pattern, reason } => {
                state.pattern = pattern;
                incomplete.push(IncompleteSearch::Indeterminate {
                    state: materialize_search_state(
                        state,
                        observation_head,
                        &diagnostics,
                        &observation_log,
                    ),
                    reason,
                });
            }
            RewriteResult::Simplification { pattern, error } => {
                state.pattern = pattern;
                incomplete.push(IncompleteSearch::Simplification {
                    state: materialize_search_state(
                        state,
                        observation_head,
                        &diagnostics,
                        &observation_log,
                    ),
                    error,
                });
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
                if let Some(exceeded) =
                    breadth_exceeded(&mut pending, &mut incomplete, options.max_breadth, |work| {
                        work.materialize(&observation_log)
                    })
                {
                    break SearchEnd::BreadthBound(exceeded);
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
                if let Some(exceeded) =
                    breadth_exceeded(&mut pending, &mut incomplete, options.max_breadth, |work| {
                        work.materialize(&observation_log)
                    })
                {
                    break SearchEnd::BreadthBound(exceeded);
                }
            }
        }
    };

    SearchResult {
        states,
        effects,
        incomplete,
        end,
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

/// Whether `state`, popped as `is_rewritable`, is an initial state with no instance by its own
/// definedness (I7'); the decision's diagnostics join `diagnostics`.
///
/// A pattern `t ∧ φ` denotes `⌈t⌉ ∧ t ∧ φ`. An initial state is the caller's pattern, whose
/// facts (the members of its knowledge that are not among its constraints) nothing has decided,
/// so a refuted fact means it has no instance, exactly as constraints simplified to `\bottom` do.
/// A successor needs no decision: the step that produced it decided its right-hand side's
/// definedness, and term simplification conjoins its own obligations. The initial states are
/// exactly the rewritable states at depth 0, since a successor is queued at its step's depth + 1
/// and a step's remainder, which carries its state's term, at the step's depth as `Remaining`.
fn initial_state_is_empty(
    definition: &BackendDefinition,
    state: &SearchState,
    is_rewritable: bool,
    max_simplification_iterations: usize,
    solver: &dyn SmtSolver,
    diagnostics: &mut PathDiagnostics,
) -> Stoppable<bool> {
    if state.depth != 0 || !is_rewritable {
        return Ok(false);
    }
    let (verdict, emitted) = diagnostic::collect(|| {
        UndecidedFacts::of_pattern(definition, &state.pattern).decide(
            definition,
            SimplificationOptions {
                max_iterations: max_simplification_iterations,
                ..SimplificationOptions::default()
            },
            solver,
        )
    });
    diagnostics.extend(&emitted);
    Ok(match verdict? {
        FactsVerdict::Refuted => true,
        FactsVerdict::NotRefuted(_) => false,
    })
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
/// exploration ([`halts`]) or that stopped, whose entry carries the whole step.
fn step_search_state(
    definition: &BackendDefinition,
    pattern: &Pattern,
    kind: QueuedStateKind,
    fresh_counter: &mut FreshCounter,
    options: &SearchOptions,
    solver: &dyn SmtSolver,
) -> (Stoppable<RewriteResult>, Vec<BackendDiagnostic>) {
    diagnostic::collect(|| match kind {
        QueuedStateKind::Rewritable => rewrite_step_with_options(
            definition,
            pattern,
            fresh_counter,
            SimplificationOptions::keep_partial(options.max_simplification_iterations),
            solver,
        ),
        QueuedStateKind::Remaining(None) => Ok(RewriteResult::Stuck(pattern.clone())),
        QueuedStateKind::Remaining(Some(undecided)) => Ok(undecided.into_result(pattern.clone())),
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
/// only the reported copy is simplified. `Ok(None)` is a result whose constraints simplify to
/// `\bottom`: an empty state is no result, as it is none at the loop head. A failed
/// simplification reports the unsimplified state in `incomplete` instead of a result.
///
/// A result is published only from a simplification that returned its answer. A stopped one
/// (a constraint that refutes the state may not have been decided) reports the state's
/// `Stopped` entry in `incomplete` instead, and `Err` returns its cause, so that the loop ends
/// when the stop ends the search ([`stop_ends_search`]).
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
) -> Result<Option<SearchState>, StopCause> {
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
        Ok(Ok(simplified)) if predicates_truth(&simplified.pattern.constraints) == Truth::False => {
            record_effects(effects, simplified.effects, observe);
            Ok(None)
        }
        Ok(Ok(simplified)) => {
            record_effects(effects, simplified.effects, observe);
            state.pattern = simplified.pattern;
            Ok(Some(materialize_search_state(
                state,
                observation,
                &diagnostics,
                observation_log,
            )))
        }
        Ok(Err(error)) => {
            incomplete.push(IncompleteSearch::Simplification {
                state: materialize_search_state(state, observation, &diagnostics, observation_log),
                error,
            });
            Ok(None)
        }
        Err(stop) => {
            let cause = stop.into_cause();
            incomplete.push(IncompleteSearch::Stopped {
                state: materialize_search_state(state, observation, &diagnostics, observation_log),
                cause: cause.clone(),
            });
            Err(cause)
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
    search_paths_collecting(
        definition,
        initial,
        RequestNames::default(),
        options,
        solver,
        observation,
        |_| false,
    )
}

fn search_paths_collecting(
    definition: &BackendDefinition,
    initial: Pattern,
    request: RequestNames,
    options: SearchOptions,
    solver: &dyn SmtSolver,
    observation: Option<&ObservationOptions>,
    mut pattern_bound_reached: impl FnMut(&PathWitness) -> bool,
) -> PathSearchResult {
    let _span = measure::algorithm_span(Algorithm::BackendSearchPaths);
    let mut observation_log = ObservationLog::default();
    let mut witnesses = Vec::new();
    let mut effects = Vec::new();
    let mut incomplete = Vec::new();
    // One request: every name the search mints is apart from every variable of the initial
    // pattern and of the target it matches it against.
    let mut fresh_counter = {
        let mut names = RequestNames::of(&[&initial]);
        names.extend(&request);
        names.extend(&options.request_names);
        FreshCounter::for_request_names(names)
    };

    let initial = PathSearchState {
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
    };
    let mut pending = VecDeque::with_capacity(1);
    // `pending` holds the initial path unless its state has a surviving macro or alias symbol,
    // in which case `incomplete` reports it.
    if let Some(symbol) = initial.state.pattern.macro_or_alias_symbol() {
        incomplete.push(IncompleteSearch::Indeterminate {
            state: initial.materialize_state(&observation_log),
            reason: IndeterminateReason::SurvivingMacroOrAlias { symbol },
        });
    } else {
        pending.push_back(initial);
    }

    // A zero breadth bound is exceeded by the initial path; a zero result bound stops before it,
    // leaving it unexplored.
    if options.max_breadth == Some(0)
        && let Some(exceeded) =
            breadth_exceeded(&mut pending, &mut incomplete, options.max_breadth, |path| {
                path.materialize_state(&observation_log)
            })
    {
        return PathSearchResult {
            witnesses,
            effects,
            incomplete,
            end: SearchEnd::BreadthBound(exceeded),
        };
    }
    if options.max_results == Some(0) {
        return PathSearchResult {
            witnesses,
            effects,
            incomplete,
            end: remaining(&pending, || false).result_bound(Truncation::UnexploredWork),
        };
    }

    // Invariant: a queued path's `visited` is exactly its own patterns, so paths stay simple.
    let end = loop {
        let mut path = match pop_or_exhausted(&mut pending) {
            Ok(path) => path,
            Err(exhausted) => break SearchEnd::Exhausted(exhausted),
        };
        // Publish a stop of the path's exploration as its `Stopped` entry; the search ends when
        // the stop ends every remaining path ([`stop_ends_search`]). Never falls through.
        macro_rules! publish_stop {
            ($stop:expr) => {{
                let cause = Stop::into_cause($stop);
                incomplete.push(IncompleteSearch::Stopped {
                    state: path.materialize_state(&observation_log),
                    cause: cause.clone(),
                });
                if stop_ends_search(&cause) {
                    break SearchEnd::Stopped(cause);
                }
                continue;
            }};
        }
        if let Err(stop) = stop::check() {
            publish_stop!(stop);
        }
        let is_rewritable = matches!(path.kind, QueuedStateKind::Rewritable);
        if let Some(symbol) = path.state.pattern.macro_or_alias_symbol() {
            incomplete.push(IncompleteSearch::Indeterminate {
                state: path.materialize_state(&observation_log),
                reason: IndeterminateReason::SurvivingMacroOrAlias { symbol },
            });
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
            Ok(Ok(constraints)) => path.state.pattern.constraints = constraints,
            Ok(Err(error)) => {
                incomplete.push(IncompleteSearch::Simplification {
                    state: path.materialize_state(&observation_log),
                    error,
                });
                continue;
            }
            Err(stop) => publish_stop!(stop),
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
            Ok(Ok(simplified)) => {
                let simplified = simplified.into_parts();
                path.state.pattern.term = simplified.term;
                path.state.pattern.constraints.extend(simplified.conditions);
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
            Ok(Err(error)) => {
                incomplete.push(IncompleteSearch::Simplification {
                    state: path.materialize_state(&observation_log),
                    error,
                });
                continue;
            }
            Err(stop) => publish_stop!(stop),
        }

        // A path ends at a state with no instance: one whose constraints are false, or an
        // initial state whose own definedness is refuted.
        if predicates_truth(&path.state.pattern.constraints) == Truth::False {
            continue;
        }
        match initial_state_is_empty(
            definition,
            &path.state,
            is_rewritable,
            options.max_simplification_iterations,
            solver,
            &mut path.diagnostics,
        ) {
            Ok(true) => continue,
            Ok(false) => {}
            Err(stop) => publish_stop!(stop),
        }
        // A path that reaches a state it already visited, up to the names of the variables the
        // request did not name, is a cycle: the state's continuations are those of the earlier
        // visit, renamed.
        let key = (
            fresh_counter.request().state_key(&path.state.pattern),
            is_rewritable,
        );
        if path.visited.contains(&key) {
            continue;
        }
        path.visited.push(key);

        let at_depth_bound = path.state.depth >= options.max_depth;
        let is_result = selects_reachable_state(options.search_type, path.state.depth)
            || (options.search_type == SearchType::Final && at_depth_bound);
        let retention = is_result.then(|| {
            retain_witness(
                definition,
                &mut witnesses,
                &path,
                &options,
                solver,
                &mut effects,
                &mut incomplete,
                &mut observation_log,
                observation,
                &mut pattern_bound_reached,
            )
        });
        match retention {
            Some(WitnessRetention::Further(further)) => {
                break SearchEnd::ResultBound(Truncation::FurtherResult(further));
            }
            Some(WitnessRetention::Stopped(cause)) if stop_ends_search(&cause) => {
                break SearchEnd::Stopped(cause);
            }
            // The path's witness is not known, but its extensions can still be explored.
            Some(WitnessRetention::Stopped(_)) => {}
            // The unexplored work after the collector's bound may hold no further result; see
            // `Truncation`.
            Some(WitnessRetention::PatternBound) => {
                let may_expand = || {
                    options.search_type != SearchType::Final
                        && state_may_expand(
                            definition,
                            &path.state,
                            is_rewritable,
                            &options,
                            &mut fresh_counter,
                            solver,
                        )
                };
                match remaining(&pending, may_expand) {
                    Remaining::Unexplored(unexplored) => {
                        break SearchEnd::ResultBound(Truncation::UnexploredWork(unexplored));
                    }
                    // The path continues through the loop body; the loop head observes the
                    // empty frontier.
                    Remaining::Exhausted(_) => {}
                }
            }
            Some(WitnessRetention::Continue) | None => {}
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
            &options,
            solver,
        );
        // A stopped step has no successor set: the path's entry carries the step's work.
        let rewrite = match rewrite {
            Ok(rewrite) => rewrite,
            Err(stop) => {
                path.diagnostics.extend(&step_diagnostics);
                publish_stop!(stop);
            }
        };
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
                        &options,
                        solver,
                        &mut effects,
                        &mut incomplete,
                        &mut observation_log,
                        observation,
                        &mut pattern_bound_reached,
                    )
                });
                match retention {
                    Some(WitnessRetention::Further(further)) => {
                        break SearchEnd::ResultBound(Truncation::FurtherResult(further));
                    }
                    Some(WitnessRetention::Stopped(cause)) if stop_ends_search(&cause) => {
                        break SearchEnd::Stopped(cause);
                    }
                    Some(WitnessRetention::Stopped(_)) => {}
                    // A stuck state has no successor: only the frontier can remain.
                    Some(WitnessRetention::PatternBound) => match remaining(&pending, || false) {
                        Remaining::Unexplored(unexplored) => {
                            break SearchEnd::ResultBound(Truncation::UnexploredWork(unexplored));
                        }
                        Remaining::Exhausted(_) => {}
                    },
                    Some(WitnessRetention::Continue) | None => {}
                }
            }
            RewriteResult::Trivial(_, _) | RewriteResult::Vacuous(_) => {}
            RewriteResult::Indeterminate { pattern, reason } => {
                path.state.pattern = pattern;
                incomplete.push(IncompleteSearch::Indeterminate {
                    state: path.materialize_state(&observation_log),
                    reason,
                });
            }
            RewriteResult::Simplification { pattern, error } => {
                path.state.pattern = pattern;
                incomplete.push(IncompleteSearch::Simplification {
                    state: path.materialize_state(&observation_log),
                    error,
                });
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
                if let Some(exceeded) =
                    breadth_exceeded(&mut pending, &mut incomplete, options.max_breadth, |path| {
                        path.materialize_state(&observation_log)
                    })
                {
                    break SearchEnd::BreadthBound(exceeded);
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
                if let Some(exceeded) =
                    breadth_exceeded(&mut pending, &mut incomplete, options.max_breadth, |path| {
                        path.materialize_state(&observation_log)
                    })
                {
                    break SearchEnd::BreadthBound(exceeded);
                }
            }
        }
    };

    PathSearchResult {
        witnesses,
        effects,
        incomplete,
        end,
    }
}

#[derive(Clone)]
struct PathSearchState {
    state: SearchState,
    id: Vec<TransitionId>,
    /// The `RequestNames::state_key` of every state on the path, with its rewritability.
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
    // A zero result bound stops before the first initial state, leaving every one unexplored.
    if requested_bound == Some(0) {
        return PatternSearchResult {
            matches: Vec::new(),
            effects: Vec::new(),
            incomplete: Vec::new(),
            end: remaining(initial.as_slice(), || false).result_bound(|unexplored| unexplored),
        };
    }
    let graph_options = SearchOptions {
        max_results: None,
        ..options.clone()
    };
    let mut matches = Vec::new();
    // The `RequestNames::solution_key` of every match in `matches`, over the names of the
    // request: the initial patterns' and the target's.
    let mut retained = HashSet::new();
    let request = {
        let mut names = RequestNames::of(&[target]);
        names.extend(&RequestNames::of(&initial.iter().collect::<Vec<_>>()));
        names.extend(&options.request_names);
        names
    };
    let mut match_incomplete = Vec::new();
    let output_variables = pattern_variables(target);
    let mut collect_match = |state: &SearchState| {
        let (found, diagnostics) = match_search_result(
            definition,
            target,
            &state.pattern,
            &output_variables,
            &options,
            solver,
        );
        let found = match found {
            Ok(Ok(Some(found))) => found,
            Ok(Ok(None)) => return false,
            Ok(Err(error)) => {
                match_incomplete.push(pattern_match_incomplete(
                    undecided_match_state(state.clone(), &diagnostics),
                    error,
                ));
                return false;
            }
            // The next state's poll ends the search when the stop ends every remaining state.
            Err(stop) => {
                match_incomplete.push(IncompleteSearch::Stopped {
                    state: undecided_match_state(state.clone(), &diagnostics),
                    cause: stop.into_cause(),
                });
                return false;
            }
        };

        let found = SearchMatch {
            substitution: found.substitution,
            constraints: found.constraints,
            state: state.clone(),
            diagnostics,
        };
        retain_pattern_match(
            &mut matches,
            &mut retained,
            &request,
            found,
            requested_bound,
        )
    };
    let graph = search_graph_collecting(
        definition,
        initial,
        request.clone(),
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
        end: graph.end,
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
    // A zero result bound stops before the initial state, leaving it unexplored: the frontier
    // is the one initial state, so work always remains.
    if requested_bound == Some(0) {
        return PatternPathSearchResult {
            matches: Vec::new(),
            effects: Vec::new(),
            incomplete: Vec::new(),
            end: remaining(std::slice::from_ref(&initial), || false)
                .result_bound(Truncation::UnexploredWork),
        };
    }
    let graph_options = SearchOptions {
        max_results: None,
        ..options.clone()
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
            &options,
            solver,
        );
        let found = match found {
            Ok(Ok(Some(found))) => found,
            Ok(Ok(None)) => return false,
            Ok(Err(error)) => {
                match_incomplete.push(pattern_match_incomplete(
                    undecided_match_state(witness_search_state(witness.clone()), &diagnostics),
                    error,
                ));
                return false;
            }
            // The next path's poll ends the search when the stop ends every remaining path.
            Err(stop) => {
                match_incomplete.push(IncompleteSearch::Stopped {
                    state: undecided_match_state(
                        witness_search_state(witness.clone()),
                        &diagnostics,
                    ),
                    cause: stop.into_cause(),
                });
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
        RequestNames::of(&[target]),
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
        end: graph.end,
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
    options: &SearchOptions,
    solver: &dyn SmtSolver,
) -> (
    Stoppable<Result<Option<PatternMatch>, PatternMatchError>>,
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

/// Whether a stop published as a state's `Stopped` entry ends the search. A cancelled request or
/// a failed solver prelude leaves no answer for any remaining state, so the search ends; a passed
/// step deadline (only a caller that arms one around the search can raise it) or an exhausted
/// stack ends the exploration of the state it stopped only.
#[deny(clippy::wildcard_enum_match_arm)]
fn stop_ends_search(cause: &StopCause) -> bool {
    match cause {
        StopCause::Cancelled | StopCause::SolverPrelude(_) => true,
        StopCause::Deadline(_) | StopCause::StackExhausted => false,
    }
}

/// The traversal's entries, then the entries of the matches it could not decide.
fn merge_pattern_incomplete(
    mut traversal: Vec<IncompleteSearch>,
    mut matching: Vec<IncompleteSearch>,
) -> Vec<IncompleteSearch> {
    traversal.append(&mut matching);
    traversal
}

/// The entry of a target-pattern check that could not decide whether `state` matches.
#[deny(clippy::wildcard_enum_match_arm)]
fn pattern_match_incomplete(state: SearchState, error: PatternMatchError) -> IncompleteSearch {
    match error {
        PatternMatchError::Simplification(error) => {
            IncompleteSearch::Simplification { state, error }
        }
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
) -> Stoppable<Result<Option<PatternMatch>, PatternMatchError>> {
    let substitution = match match_terms_in_definition(
        MatchMode::Implies,
        definition,
        &target.term,
        &subject.term,
    ) {
        MatchResult::Success(substitution) => substitution,
        MatchResult::Failed(_) => return Ok(Ok(None)),
        MatchResult::Indeterminate {
            substitution,
            remainder,
        } => {
            return Ok(Err(PatternMatchError::Indeterminate {
                substitution,
                remainder,
            }));
        }
    };

    // Every instance of the subject satisfies its knowledge (I7): the definedness of its term
    // and the obligations its own constraints state. The target's constraints are instantiated
    // with the definedness of their atoms stated (I1), except where that knowledge already
    // holds it, so the match condition excludes the instances on which a target atom denotes
    // `\bottom`: the solver reads a partial function as a total one and would give it a value.
    let subject_knowledge = pattern_knowledge(definition, subject);
    let mut constraints = subject.constraints.clone();
    constraints.extend(
        instantiate_constraints(&target.constraints, &substitution)
            .with_definedness(definition, &subject_knowledge),
    );
    // The knowledge the subject's constraints do not already carry is decided with the match
    // condition, not reported in it: it holds on every instance of the subject, which the
    // match's state carries. The subject's constraints themselves travel in the condition, and
    // so does a fact that an equation of the target rewrites (`normalize_match_condition`).
    let facts = knowledge_facts(subject_knowledge, &subject.constraints);
    let (substitution, constraints, facts) = normalize_match_condition(
        definition,
        substitution,
        constraints,
        subject.constraints.len(),
        facts,
        output_variables,
    );
    // A match reports that an instance exists, so the facts are decided before they are taken as
    // known (I7'): a refuted fact means the subject has no instance, and so no instance of it
    // matches. An undecided fact stays a fact about the subject, not a condition of the match.
    // Only the decided residual is assumed, which leaves the condition's meaning on the subject's
    // instances unchanged: `F' ∧ simplify(C | F')` is `F' ∧ C`.
    let facts = match facts.decide(definition, options, solver)? {
        FactsVerdict::Refuted => return Ok(Ok(None)),
        FactsVerdict::NotRefuted(facts) => facts,
    };
    let constraints = match simplify_predicates_with_solver(
        definition,
        &constraints,
        facts.as_known(),
        options,
        solver,
    )? {
        Ok(constraints) => constraints,
        Err(error) => return Ok(Err(PatternMatchError::Simplification(error))),
    };
    match predicates_truth(&constraints) {
        Truth::False => return Ok(Ok(None)),
        Truth::True => {}
        Truth::Unknown if retain_unknown => {}
        // A stop leaves the match without an answer; it is returned, never read as a match.
        Truth::Unknown => {
            match is_sat_with_facts(solver, facts.as_known(), &constraints, &substitution)? {
                Ok(Satisfiability::Unsat) => return Ok(Ok(None)),
                Ok(Satisfiability::Sat) => {}
                Ok(Satisfiability::Unknown(reason)) => {
                    return Ok(Err(PatternMatchError::Smt(SmtError::Unknown(reason))));
                }
                Err(error) => return Ok(Err(PatternMatchError::Smt(error))),
            }
        }
    }

    Ok(Ok(Some(PatternMatch {
        substitution,
        constraints,
    })))
}

/// Whether `facts ∧ constraints` is satisfiable together with `substitution`.
fn is_sat_with_facts(
    solver: &dyn SmtSolver,
    facts: &[Predicate],
    constraints: &[Predicate],
    substitution: &Substitution,
) -> Stoppable<Result<Satisfiability, SmtError>> {
    if facts.is_empty() {
        return solver.is_sat(constraints, substitution);
    }
    let mut query = facts.to_vec();
    query.extend_from_slice(constraints);
    solver.is_sat(&query, substitution)
}

/// Solve the match condition's equalities `x = t` for a variable `x`, eliminating each binding
/// from the remaining constraints with its definedness kept (I2): an element variable denotes a
/// defined element, so `∃x. (x = t ∧ ψ)` is `⌈t⌉ ∧ ψ[t/x]`.
///
/// The condition is a predicate over the instances of the state; its first `state_constraints`
/// constraints are the state's own, and `facts` are further predicates that hold on every
/// instance of the state. The returned facts are undecided: the caller decides them (I7',
/// [`UndecidedFacts::decide`]) before it takes them as known while it decides the returned
/// constraints, so a predicate stays among them only while it holds on every instance:
///
/// - An equation that holds on every instance (one of the state's own constraints, or one
///   derived from them by such equations) leaves that set unchanged when it is eliminated:
///   there `x = t`, so `F[t/x]` holds wherever `F` does, and so does `⌈t⌉`. The binding is
///   applied to the facts, and its `⌈t⌉` joins them.
/// - Any other equation (one instantiated from the target's constraints, or rewritten by one)
///   holds only on the instances the match selects. On those `F[t/x]` holds, but elsewhere it
///   can be false (`⌈10 /Int X⌉` under `X ↦ 0` is `⌈10 /Int 0⌉`, which is `⊥`), so a fact the
///   binding rewrites is no longer known: it joins the constraints as a conjunct of the match
///   condition, decided and reported like the other obligations. A fact that does not mention
///   `x` is unchanged and stays known, as does every constraint's status that `x` leaves alone.
///
/// An obligation `⌈t⌉` is omitted only where the remaining facts, or the constraints, hold it. An
/// obligation omitted because a fact holds it is a member of the returned facts, so it is decided
/// with that fact.
fn normalize_match_condition(
    definition: &BackendDefinition,
    output: Substitution,
    mut constraints: Vec<Predicate>,
    state_constraints: usize,
    mut facts: Vec<Predicate>,
    output_variables: &BTreeSet<crate::term::Variable>,
) -> (Substitution, Vec<Predicate>, UndecidedFacts) {
    let _span = measure::algorithm_span(Algorithm::BackendSubstitutionExtractOutput);
    let mut solved = Substitution::new();
    // `on_every_instance[i]`: constraint `i` holds on every instance of the state.
    let mut on_every_instance = (0..constraints.len())
        .map(|index| index < state_constraints)
        .collect::<Vec<_>>();
    // Invariant: each round moves one solvable equality into `solved`; exit when none remains.
    // No variable of `solved` occurs in `constraints` or `facts` after a round: the bound value
    // is read from the substituted constraints, and the binding is eliminated from both (a fact
    // that mentions it is either rewritten in place or moved into the constraints).
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
        let equation_on_every_instance = on_every_instance.remove(index);
        let Some((variable, value)) = binding else {
            continue;
        };
        let binding = Substitution::from([(variable.clone(), value)]);
        solved = compose(&binding, &solved);
        // No round adds a fact once none remains, so the statuses matter only while some do.
        if !facts.is_empty() {
            if equation_on_every_instance {
                facts = eliminate_bindings(definition, &facts, &binding, &[]);
            } else {
                for (holds, constraint) in on_every_instance.iter_mut().zip(&constraints) {
                    if *holds && mentions_variable(constraint, &variable) {
                        *holds = false;
                    }
                }
                let (rewritten, kept): (Vec<_>, Vec<_>) = facts
                    .into_iter()
                    .partition(|fact| mentions_variable(fact, &variable));
                facts = kept;
                on_every_instance.extend(rewritten.iter().map(|_| false));
                constraints.extend(rewritten);
            }
        }
        // `eliminate_bindings` keeps the order of `constraints` and appends the obligations,
        // which hold wherever the equation does.
        constraints = eliminate_bindings(definition, &constraints, &binding, &facts);
        on_every_instance.resize(constraints.len(), equation_on_every_instance);
    }

    let mut output = compose(&solved, &output);
    output.retain(|variable, _| output_variables.contains(variable));
    // Each binding was eliminated from the constraints and the facts with its definedness
    // stated, and the later bindings were eliminated from those obligations too: a composed
    // value is `s[t/x]` for bindings `y ↦ s` and `x ↦ t`, whose definedness `⌈s⌉[t/x] ∧ ⌈t⌉`
    // is among the constraints or the facts. No constraint mentions a solved variable, so
    // `solved` is not applied to them again.
    (output, constraints, UndecidedFacts::new(facts))
}

/// Whether a term of `predicate` has `variable` free.
fn mentions_variable(predicate: &Predicate, variable: &crate::term::Variable) -> bool {
    let mut found = false;
    predicate.visit_terms(&mut |term| found |= term.attributes().variables.contains(variable));
    found
}

fn simplification_options(options: &SearchOptions) -> SimplificationOptions {
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
    options: &SearchOptions,
    fresh_counter: &mut FreshCounter,
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
    match rewrite_step_with_options(
        definition,
        &state.pattern,
        fresh_counter,
        simplification_options(options),
        solver,
    ) {
        Ok(rewritten) => !matches!(
            rewritten,
            RewriteResult::Stuck(_) | RewriteResult::Trivial(_, _) | RewriteResult::Vacuous(_)
        ),
        Err(stop) => {
            // Kept outcome: the state may expand, so the search ends at its result bound with
            // work left (`SearchEnd::ResultBound`). That holds whatever the step would have
            // found; the step's answer could only refine it into `Exhausted`.
            stop.forgo_refinement();
            true
        }
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
#[allow(clippy::wildcard_enum_match_arm)]
mod tests {
    use std::{collections::BTreeSet, sync::Arc};

    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};
    use proptest::prelude::*;

    use super::*;
    use crate::transition::{ObservationEvent, ObservationOptions};
    use crate::{
        builtin::BuiltinError,
        diagnostic::{self, BackendDiagnostic},
        simplify::BudgetSubject,
        term::{Sort, Symbol, Term, TermKind, Variable},
    };

    #[test]
    fn cancellation_is_not_reported_as_a_simplifier_failure() {
        let definition = definition();
        let token = crate::stop::CancellationToken::new();
        token.cancel();
        let result = token
            .scope(|| search_graph(&definition, initial(&definition), SearchOptions::default()));

        // Exactly one entry names the stop, with its cause, and the search ends with it.
        assert!(result.states.is_empty());
        let [
            IncompleteSearch::Stopped {
                state,
                cause: StopCause::Cancelled,
            },
        ] = result.incomplete.as_slice()
        else {
            panic!("expected cancellation, found {:?}", result.incomplete);
        };
        assert_eq!(state.depth, 0);
        assert_eq!(result.end, SearchEnd::Stopped(StopCause::Cancelled));
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
    fn a_stop_ends_the_search_exactly_when_it_ends_every_remaining_state() {
        let deadline = StopCause::Deadline(crate::timeout::StepTimeoutMode::Manual(
            std::time::Duration::from_millis(1),
        ));
        let prelude = StopCause::SolverPrelude(crate::stop::PreludeFailure::Inconsistent);
        for (cause, ends) in [
            (StopCause::Cancelled, true),
            (prelude, true),
            (deadline, false),
            (StopCause::StackExhausted, false),
        ] {
            assert_eq!(stop_ends_search(&cause), ends, "{cause:?}");
        }
    }

    /// An undecided match is reported with its own reason, whatever the request's token says: a
    /// stop reaches the search on the outer layer of a result, so no entry is reinterpreted as
    /// stopped because the request is cancelled when it is recorded.
    #[test]
    fn an_entry_keeps_its_reason_under_a_cancelled_request() {
        let definition = definition();
        let state = SearchState {
            pattern: initial(&definition),
            depth: 0,
            trace: Vec::new(),
            branch: Vec::new(),
            observations: Vec::new(),
            diagnostics: Vec::new(),
        };
        let unknown = || SmtError::Unknown("timeout".into());
        let failure = SimplificationError::Builtin(BuiltinError::WrongArity {
            hook: "INT.add".into(),
            expected: 2,
            actual: 1,
        });
        let token = crate::stop::CancellationToken::new();
        token.cancel();
        token.scope(|| {
            assert_eq!(
                pattern_match_incomplete(state.clone(), PatternMatchError::Smt(unknown())),
                IncompleteSearch::Smt {
                    state: state.clone(),
                    error: unknown(),
                }
            );
            assert_eq!(
                pattern_match_incomplete(
                    state.clone(),
                    PatternMatchError::Indeterminate {
                        substitution: Substitution::new(),
                        remainder: Vec::new(),
                    },
                ),
                IncompleteSearch::Match {
                    state: state.clone(),
                    substitution: Substitution::new(),
                    remainder: Vec::new(),
                }
            );
            assert_eq!(
                pattern_match_incomplete(
                    state.clone(),
                    PatternMatchError::Simplification(failure.clone()),
                ),
                IncompleteSearch::Simplification {
                    state: state.clone(),
                    error: failure,
                }
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
            let bounded = search_graph(&definition, initial(&definition), options.clone());
            if bounded.is_complete() {
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
            let bounded = search_pattern(&definition, initial(&definition), &target, options.clone());
            if bounded.is_complete() {
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
            prop_assume!(!bounded.is_complete());

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
            let bounded = search_graph(&definition, initial(&definition), options.clone());
            if bounded.is_complete() {
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
            let bounded = search_paths(&definition, initial(&definition), options.clone());
            if bounded.is_complete() {
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
                ..options.clone()
            },
        );

        let mut retained = 0;
        let mut observed = Vec::new();
        let graph_result = search_graph_collecting(
            &definition,
            vec![initial],
            RequestNames::default(),
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
        assert_eq!(pattern_result.incomplete, []);
        assert!(
            matches!(pattern_result.end, SearchEnd::ResultBound(_)),
            "{:?}",
            pattern_result.end
        );
        assert_eq!(graph_result.states.len(), 2);
        assert_eq!(observed, graph_result.effects);
        assert_eq!(graph_result.effects, pattern_result.effects);
        assert_eq!(graph_result.incomplete, []);
        assert!(
            matches!(graph_result.end, SearchEnd::ResultBound(_)),
            "{:?}",
            graph_result.end
        );
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
            options.clone(),
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
        assert_eq!(states.incomplete, []);
        assert!(
            matches!(states.end, SearchEnd::ResultBound(_)),
            "{:?}",
            states.end
        );
        assert_eq!(states.matches[0].state.branch.len(), 2);
        assert!(
            transition_ids(&states.matches[0].state.observations)
                .into_iter()
                .eq(&states.matches[0].state.branch)
        );

        assert_eq!(paths.matches.len(), 1);
        assert_eq!(paths.incomplete, []);
        assert!(
            matches!(
                paths.end,
                SearchEnd::ResultBound(Truncation::UnexploredWork(_))
            ),
            "{:?}",
            paths.end
        );
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
        assert_eq!(result.incomplete, []);
        assert!(
            matches!(
                result.end,
                SearchEnd::ResultBound(Truncation::UnexploredWork(_))
            ),
            "{:?}",
            result.end
        );
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
        assert_eq!(result.incomplete, []);
        assert!(
            matches!(
                result.end,
                SearchEnd::ResultBound(Truncation::UnexploredWork(_))
            ),
            "{:?}",
            result.end
        );
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
        assert!(
            matches!(
                result.end,
                SearchEnd::ResultBound(Truncation::FurtherResult(_))
            ),
            "{:?}",
            result.end
        );
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
        assert!(result.is_complete(), "{result:?}");
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
        assert_eq!(result.incomplete, []);
        assert!(
            matches!(
                result.end,
                SearchEnd::ResultBound(Truncation::UnexploredWork(_))
            ),
            "{:?}",
            result.end
        );
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
            let graph =
                search_graph_with_solver(&definition, initial.clone(), options.clone(), &solver);
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
        assert_eq!(result.incomplete, []);
        assert!(
            matches!(result.end, SearchEnd::ResultBound(_)),
            "{:?}",
            result.end
        );
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
            assert!(result.is_complete(), "{search_type:?}: {result:?}");
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
                [IncompleteSearch::DepthBound(_)]
            ),
            "{:?}",
            result.incomplete
        );
        assert!(
            matches!(result.end, SearchEnd::ResultBound(_)),
            "{:?}",
            result.end
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
        let graph = search_graph(&definition, initial(&definition), options.clone());
        assert!(graph.states.is_empty());
        assert_eq!(graph.incomplete, []);
        assert!(
            matches!(graph.end, SearchEnd::ResultBound(_)),
            "{:?}",
            graph.end
        );

        let target = Pattern {
            term: Term::variable(Variable::new("Result", Sort::simple("SortS"))),
            constraints: Vec::new(),
        };
        let pattern = search_pattern(&definition, initial(&definition), &target, options.clone());
        assert!(pattern.matches.is_empty());
        assert_eq!(pattern.incomplete, []);
        assert!(
            matches!(pattern.end, SearchEnd::ResultBound(_)),
            "{:?}",
            pattern.end
        );
    }

    #[test]
    fn zero_bounds_on_an_empty_initial_frontier_are_complete() {
        // An initial disjunction without a branch denotes no state, so a search from it has
        // nothing to explore: a zero result bound or a zero breadth bound leaves no work behind,
        // and its empty result set is complete.
        let definition = definition();
        let target = Pattern {
            term: Term::variable(result_variable()),
            constraints: Vec::new(),
        };
        for options in [
            SearchOptions {
                max_results: Some(0),
                ..SearchOptions::default()
            },
            SearchOptions {
                max_breadth: Some(0),
                ..SearchOptions::default()
            },
        ] {
            let graph = search_graph_disjunction_with_solver_and_observer(
                &definition,
                Vec::new(),
                options.clone(),
                &NoSolver,
                |_| {},
            );
            assert!(graph.states.is_empty());
            assert!(graph.is_complete(), "{options:?}: {graph:?}");

            let pattern = search_pattern_disjunction_with_solver(
                &definition,
                Vec::new(),
                &target,
                options.clone(),
                &NoSolver,
            );
            assert!(pattern.matches.is_empty());
            assert!(pattern.is_complete(), "{options:?}: {pattern:?}");
        }
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
        assert_eq!(result.incomplete, []);
        assert!(
            matches!(result.end, SearchEnd::ResultBound(_)),
            "{:?}",
            result.end
        );

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
        assert!(result.is_complete(), "{result:?}");
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
        assert!(result.is_complete(), "{result:?}");
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
        assert!(result.is_complete(), "{result:?}");
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
            options.clone(),
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
        assert_eq!(states.incomplete, []);
        assert!(
            matches!(states.end, SearchEnd::ResultBound(_)),
            "{:?}",
            states.end
        );

        let paths = search_pattern_paths(
            &definition,
            pattern(&definition, "loop{}(zero{}())"),
            &target,
            options.clone(),
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
        assert_eq!(paths.incomplete, []);
        assert!(
            matches!(
                paths.end,
                SearchEnd::ResultBound(Truncation::UnexploredWork(_))
            ),
            "{:?}",
            paths.end
        );
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
        assert_eq!(result.incomplete, []);
        assert!(
            matches!(
                result.end,
                SearchEnd::ResultBound(Truncation::UnexploredWork(_))
            ),
            "{:?}",
            result.end
        );
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
        assert!(
            matches!(result.end, SearchEnd::BreadthBound(_)),
            "{:?}",
            result.end
        );
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
        assert!(
            matches!(result.end, SearchEnd::BreadthBound(_)),
            "{:?}",
            result.end
        );
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

        let matches = match_disjunction(&definition, &target, &subjects)
            .expect("no stop is armed")
            .unwrap();

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
                .expect("no stop is armed")
                .unwrap()
                .is_empty()
        );
        assert_eq!(
            match_disjunction(&definition, &target, &present)
                .expect("no stop is armed")
                .unwrap(),
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

        let matches = match_disjunction(&definition, &initial(&definition), &[subject])
            .expect("no stop is armed")
            .unwrap();

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

        let (output, constraints, facts) = normalize_match_condition(
            &definition(),
            Substitution::from([(
                result_variable.clone(),
                Term::variable(configuration_variable.clone()),
            )]),
            vec![Predicate::Equals(
                Term::variable(configuration_variable),
                value.clone(),
            )],
            0,
            Vec::new(),
            &BTreeSet::from([result_variable.clone()]),
        );

        assert_eq!(output, Substitution::from([(result_variable, value)]));
        assert!(constraints.is_empty());
        assert!(facts.is_empty());
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

        let graph = search_graph(
            &definition,
            pattern(&definition, "start{}()"),
            options.clone(),
        );
        assert!(graph.incomplete.is_empty(), "{:?}", graph.incomplete);
        let [state] = graph.states.as_slice() else {
            panic!("expected one final state, found {:?}", graph.states);
        };
        assert_eq!(state.pattern, expected, "{state:#?}");
        assert_eq!(simplification_ids(&state.trace), Vec::<String>::new());

        let paths = search_paths(
            &definition,
            pattern(&definition, "start{}()"),
            options.clone(),
        );
        assert!(paths.incomplete.is_empty(), "{:?}", paths.incomplete);
        let [witness] = paths.witnesses.as_slice() else {
            panic!("expected one witness, found {:?}", paths.witnesses);
        };
        assert_eq!(witness.pattern, expected, "{witness:#?}");
        assert_eq!(simplification_ids(&witness.trace), Vec::<String>::new());
    }

    /// A definition with a partial `divInt` (no `total` attribute, no ceil equation) and a
    /// partial uninterpreted `g` (no `total` attribute, no equation).
    fn partial_target_definition() -> BackendDefinition {
        partial_target_definition_with("")
    }

    /// `partial_target_definition` with `declarations` added to its module.
    fn partial_target_definition_with(declarations: &str) -> BackendDefinition {
        const SENTENCES: &str = r#"
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                sort SortState{} []
                symbol pair{}(SortInt{}, SortInt{}) : SortState{} [constructor{}()]
                hooked-symbol leInt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.le"), smt-hook{}("<=")]
                hooked-symbol addInt{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), total{}(), hook{}("INT.add"), smt-hook{}("+")]
                hooked-symbol divInt{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), hook{}("INT.tdiv"), smt-hook{}("div")]
                symbol g{}(SortInt{}) : SortInt{} [function{}()]"#;
        let syntax = parse_definition(&format!(
            "[]\nmodule MAIN{SENTENCES}\n{declarations}\nendmodule []"
        ))
        .expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    /// The target `term ∧ (value <=Int value +Int 1)` over `partial_target_definition`.
    #[cfg(feature = "z3")]
    fn target_bounded_by_successor(
        definition: &BackendDefinition,
        term: &str,
        value: &str,
    ) -> Pattern {
        let bounded =
            format!(r#"leInt{{}}({value}, addInt{{}}({value}, \dv{{SortInt{{}}}}("1")))"#);
        Pattern {
            term: pattern(definition, term).term,
            constraints: vec![Predicate::Equals(
                pattern(definition, r#"\dv{SortBool{}}("true")"#).term,
                pattern(definition, &bounded).term,
            )],
        }
    }

    /// A state whose constraints refute `⌈g(X)⌉` has no instance on which the target's
    /// instantiated constraint `g(X) <=Int g(X) +Int 1` holds: that atom denotes `⊥` wherever
    /// `g(X)` is undefined (I1), so the state does not match the target, although the solver
    /// reads `g` as a total function on which the atom is valid.
    #[cfg(feature = "z3")]
    #[test]
    fn a_target_constraint_undefined_on_the_state_does_not_match() {
        let definition = partial_target_definition();
        let solver = crate::smt::Z3Solver::new(&definition).expect("Z3 should initialize");
        let target = target_bounded_by_successor(
            &definition,
            r#"pair{}(A:SortInt{}, B:SortInt{})"#,
            r#"g{}(A:SortInt{})"#,
        );
        let subject = Pattern {
            term: pattern(&definition, r#"pair{}(X:SortInt{}, \dv{SortInt{}}("1"))"#).term,
            constraints: vec![Predicate::Not(Box::new(Predicate::Ceil(
                pattern(&definition, r#"g{}(X:SortInt{})"#).term,
            )))],
        };

        let matches = match_disjunction_with_solver(
            &definition,
            &target,
            &[subject],
            SimplificationOptions::default(),
            &solver,
        )
        .expect("no stop is armed")
        .expect("the match should be decided");

        assert!(matches.is_empty(), "{matches:#?}");
    }

    /// The state `pair(X, 10 /Int X)` is empty wherever `10 /Int X` is undefined, so
    /// `⌈10 /Int X⌉` holds on each of its instances (I7) and the target `pair(X, Y)` constrained
    /// by `Y <=Int Y +Int 1` matches it with that constraint alone.
    #[cfg(feature = "z3")]
    #[test]
    fn a_state_whose_term_defines_the_target_constraint_matches() {
        let definition = partial_target_definition();
        let solver = crate::smt::Z3Solver::new(&definition).expect("Z3 should initialize");
        let target = target_bounded_by_successor(
            &definition,
            r#"pair{}(A:SortInt{}, B:SortInt{})"#,
            r#"B:SortInt{}"#,
        );
        let subject = pattern(
            &definition,
            r#"pair{}(X:SortInt{}, divInt{}(\dv{SortInt{}}("10"), X:SortInt{}))"#,
        );

        let matches = match_disjunction_with_solver(
            &definition,
            &target,
            &[subject],
            SimplificationOptions::default(),
            &solver,
        )
        .expect("no stop is armed")
        .expect("the match should be decided");

        let [found] = matches.as_slice() else {
            panic!("expected one match, found {matches:#?}");
        };
        let quotient = pattern(
            &definition,
            r#"divInt{}(\dv{SortInt{}}("10"), X:SortInt{})"#,
        )
        .term;
        assert_eq!(
            found
                .substitution
                .get(&Variable::new("B", Sort::simple("SortInt"))),
            Some(&quotient),
            "{found:#?}"
        );
        assert!(
            !found
                .constraints
                .contains(&Predicate::Ceil(quotient.clone())),
            "the state's own definedness is known, not restated: {found:#?}"
        );
    }

    /// The state `pair(X, 10 /Int X)` against the target `pair(X, Y)` constrained by
    /// `Y <=Int Y +Int 1`: the target's variables share the state's names, and the match is the
    /// same as under fresh names, with `Y ↦ 10 /Int X` and no restated `⌈10 /Int X⌉`.
    #[cfg(feature = "z3")]
    #[test]
    fn a_state_whose_term_defines_the_target_constraint_matches_under_shared_names() {
        let definition = partial_target_definition();
        let solver = crate::smt::Z3Solver::new(&definition).expect("Z3 should initialize");
        let target = target_bounded_by_successor(
            &definition,
            r#"pair{}(X:SortInt{}, Y:SortInt{})"#,
            r#"Y:SortInt{}"#,
        );
        let subject = pattern(
            &definition,
            r#"pair{}(X:SortInt{}, divInt{}(\dv{SortInt{}}("10"), X:SortInt{}))"#,
        );

        let matches = match_disjunction_with_solver(
            &definition,
            &target,
            &[subject],
            SimplificationOptions::default(),
            &solver,
        )
        .expect("no stop is armed")
        .expect("the match should be decided");

        let [found] = matches.as_slice() else {
            panic!("expected one match, found {matches:#?}");
        };
        let quotient = pattern(
            &definition,
            r#"divInt{}(\dv{SortInt{}}("10"), X:SortInt{})"#,
        )
        .term;
        assert_eq!(
            found
                .substitution
                .get(&Variable::new("Y", Sort::simple("SortInt"))),
            Some(&quotient),
            "{found:#?}"
        );
        assert!(
            !found
                .constraints
                .contains(&Predicate::Ceil(quotient.clone())),
            "the state's own definedness is known, not restated: {found:#?}"
        );
    }

    /// The state `pair(X, Y) ∧ Z = X ∧ Y = 10 /Int Z` (its equalities not yet applied to one
    /// another) and the target `pair(A, B)`, which has no constraints.
    fn unsaturated_partial_subject(definition: &BackendDefinition) -> (Pattern, Pattern) {
        let int = Sort::simple("SortInt");
        let variable = |name: &str| Term::variable(Variable::new(name, int.clone()));
        let subject = Pattern {
            term: pattern(definition, r#"pair{}(X:SortInt{}, Y:SortInt{})"#).term,
            constraints: vec![
                Predicate::Equals(variable("Z"), variable("X")),
                Predicate::Equals(
                    variable("Y"),
                    pattern(definition, r#"divInt{}(\dv{SortInt{}}("10"), Z:SortInt{})"#).term,
                ),
            ],
        };
        let target = pattern(definition, r#"pair{}(A:SortInt{}, B:SortInt{})"#);
        (target, subject)
    }

    /// The single match of `unsaturated_partial_subject` is `A ↦ X`, `B ↦ 10 /Int X` with no
    /// constraints: `⌈10 /Int Z⌉` holds on every instance of the state (its constraint
    /// `Y = 10 /Int Z` states it), so eliminating `Z ↦ X` and `Y ↦ 10 /Int X` from the
    /// condition leaves `⌈10 /Int X⌉` known, not an obligation of the match.
    fn assert_unsaturated_partial_subject_matches(
        definition: &BackendDefinition,
        matches: &[PatternMatch],
    ) {
        let [found] = matches else {
            panic!("expected one match, found {matches:#?}");
        };
        let int = Sort::simple("SortInt");
        let expected = Substitution::from([
            (
                Variable::new("A", int.clone()),
                Term::variable(Variable::new("X", int.clone())),
            ),
            (
                Variable::new("B", int),
                pattern(definition, r#"divInt{}(\dv{SortInt{}}("10"), X:SortInt{})"#).term,
            ),
        ]);
        assert_eq!(found.substitution, expected, "{found:#?}");
        assert!(found.constraints.is_empty(), "{found:#?}");
    }

    /// Without a solver the match is decided, not left undecided: the state's knowledge follows
    /// the eliminated bindings, so no obligation over them remains for a solver to discharge.
    #[test]
    fn a_state_with_unsaturated_equalities_matches_without_a_solver() {
        let definition = partial_target_definition();
        let (target, subject) = unsaturated_partial_subject(&definition);

        let decided = match_disjunction_with_solver(
            &definition,
            &target,
            std::slice::from_ref(&subject),
            SimplificationOptions::default(),
            &NoSolver,
        )
        .expect("no stop is armed")
        .expect("the match should be decided without a solver");
        assert_unsaturated_partial_subject_matches(&definition, &decided);

        let retained = match_disjunction(&definition, &target, &[subject])
            .expect("no stop is armed")
            .expect("the match should be computed");
        assert_unsaturated_partial_subject_matches(&definition, &retained);
    }

    #[cfg(feature = "z3")]
    #[test]
    fn a_state_with_unsaturated_equalities_matches_with_a_solver() {
        let definition = partial_target_definition();
        let solver = crate::smt::Z3Solver::new(&definition).expect("Z3 should initialize");
        let (target, subject) = unsaturated_partial_subject(&definition);

        let matches = match_disjunction_with_solver(
            &definition,
            &target,
            &[subject],
            SimplificationOptions::default(),
            &solver,
        )
        .expect("no stop is armed")
        .expect("the match should be decided");
        assert_unsaturated_partial_subject_matches(&definition, &matches);
    }

    /// The state `pair(X, 10 /Int X)` and the target `pair(A, B) ∧ A = 0`, with `⌈B⌉` also
    /// among the target's constraints when `ceil_second` is set.
    fn target_fixing_the_divisor(
        definition: &BackendDefinition,
        ceil_second: bool,
    ) -> (Pattern, Pattern) {
        let int = Sort::simple("SortInt");
        let mut constraints = vec![Predicate::Equals(
            Term::variable(Variable::new("A", int.clone())),
            pattern(definition, r#"\dv{SortInt{}}("0")"#).term,
        )];
        if ceil_second {
            constraints.push(Predicate::Ceil(Term::variable(Variable::new("B", int))));
        }
        let target = Pattern {
            term: pattern(definition, r#"pair{}(A:SortInt{}, B:SortInt{})"#).term,
            constraints,
        };
        let subject = pattern(
            definition,
            r#"pair{}(X:SortInt{}, divInt{}(\dv{SortInt{}}("10"), X:SortInt{}))"#,
        );
        (target, subject)
    }

    /// `⌈10 /Int X⌉` holds on every instance of the state `pair(X, 10 /Int X)`, so no instance
    /// has `X = 0` and the state matches neither form of `target_fixing_the_divisor`. The
    /// target's equation `A = 0`, instantiated as `X = 0`, holds only on the instances the match
    /// would select; eliminating it rewrites that fact to `⌈10 /Int 0⌉`, which is a conjunct of
    /// the match condition (and `⊥`), not a fact about the state. Taking it as known would
    /// discharge the target's `⌈B⌉` (instantiated as `⌈10 /Int 0⌉`); leaving it out would drop
    /// the only conjunct that refutes the plain target.
    fn assert_the_divisor_cannot_be_zero(
        definition: &BackendDefinition,
        ceil_second: bool,
        solver: Option<&dyn SmtSolver>,
    ) {
        let (target, subject) = target_fixing_the_divisor(definition, ceil_second);
        let matches = match solver {
            Some(solver) => match_disjunction_with_solver(
                definition,
                &target,
                &[subject],
                SimplificationOptions::default(),
                solver,
            )
            .expect("no stop is armed"),
            None => match_disjunction(definition, &target, &[subject]).expect("no stop is armed"),
        }
        .expect("the match should be computed");
        assert!(matches.is_empty(), "{matches:#?}");
    }

    #[test]
    fn a_target_equation_does_not_make_a_rewritten_state_fact_known() {
        let definition = partial_target_definition();
        assert_the_divisor_cannot_be_zero(&definition, true, Some(&NoSolver));
        assert_the_divisor_cannot_be_zero(&definition, true, None);
    }

    #[cfg(feature = "z3")]
    #[test]
    fn a_target_equation_does_not_make_a_rewritten_state_fact_known_with_a_solver() {
        let definition = partial_target_definition();
        let solver = crate::smt::Z3Solver::new(&definition).expect("Z3 should initialize");
        assert_the_divisor_cannot_be_zero(&definition, true, Some(&solver));
    }

    #[test]
    fn a_target_equation_refuted_by_the_state_term_definedness_does_not_match() {
        let definition = partial_target_definition();
        assert_the_divisor_cannot_be_zero(&definition, false, Some(&NoSolver));
        assert_the_divisor_cannot_be_zero(&definition, false, None);
    }

    #[cfg(feature = "z3")]
    #[test]
    fn a_target_equation_refuted_by_the_state_term_definedness_does_not_match_with_a_solver() {
        let definition = partial_target_definition();
        let solver = crate::smt::Z3Solver::new(&definition).expect("Z3 should initialize");
        assert_the_divisor_cannot_be_zero(&definition, false, Some(&solver));
    }

    /// `partial_target_definition` with `neInt` and the simplification axiom
    /// `⌈divInt(I1, I2)⌉ = (neInt(I2, 0) = true)`: `divInt` is defined exactly where its divisor
    /// is not zero.
    fn ceil_axiom_definition() -> BackendDefinition {
        partial_target_definition_with(
            r#"hooked-symbol neInt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.ne"), smt-hook{}("distinct")]
                axiom{R} \implies{R}(\top{R}(), \equals{R, R}(
                    \ceil{SortInt{}, R}(divInt{}(I1:SortInt{}, I2:SortInt{})),
                    \and{R}(
                        \equals{SortBool{}, R}(
                            neInt{}(I2:SortInt{}, \dv{SortInt{}}("0")),
                            \dv{SortBool{}}("true")),
                        \top{R}())))
                    [label{}("ceil-div"), simplification{}()]"#,
        )
    }

    fn pair_target(definition: &BackendDefinition) -> Pattern {
        pattern(definition, r#"pair{}(A:SortInt{}, B:SortInt{})"#)
    }

    /// The subject `pair(X, X /Int 0)`, which has no instance under `ceil_axiom_definition`.
    fn zero_divisor_subject(definition: &BackendDefinition) -> Pattern {
        pattern(
            definition,
            r#"pair{}(X:SortInt{}, divInt{}(X:SortInt{}, \dv{SortInt{}}("0")))"#,
        )
    }

    /// Matches of `subject` against `target` through `match_disjunction` and through
    /// `match_disjunction_with_solver` without a solver, in that order.
    fn matches_with_and_without_retention(
        definition: &BackendDefinition,
        target: &Pattern,
        subject: &Pattern,
    ) -> [Vec<PatternMatch>; 2] {
        let retained = match_disjunction(definition, target, std::slice::from_ref(subject))
            .expect("no stop is armed")
            .expect("the match should be computed");
        let decided = match_disjunction_with_solver(
            definition,
            target,
            std::slice::from_ref(subject),
            SimplificationOptions::default(),
            &NoSolver,
        )
        .expect("no stop is armed")
        .expect("the match should be decided without a solver");
        [retained, decided]
    }

    /// `pair(X, X /Int 0)` denotes `⌈X /Int 0⌉ ∧ pair(X, X /Int 0)`, and the ceil axiom makes
    /// `⌈X /Int 0⌉` the false `0 =/=Int 0`: the subject has no instance, so none matches (I7').
    #[test]
    fn a_state_empty_by_its_term_definedness_does_not_match() {
        let definition = ceil_axiom_definition();
        let target = pair_target(&definition);
        let subject = zero_divisor_subject(&definition);
        for matches in matches_with_and_without_retention(&definition, &target, &subject) {
            assert!(matches.is_empty(), "{matches:#?}");
        }
    }

    /// `10 /Int 0` evaluates to `\bottom`, so `⌈10 /Int 0⌉` is false without any ceil axiom and
    /// `pair(X, 10 /Int 0)` has no instance to match.
    #[test]
    fn a_ground_undefined_subterm_empties_the_state() {
        let definition = partial_target_definition();
        let target = pair_target(&definition);
        let subject = pattern(
            &definition,
            r#"pair{}(X:SortInt{}, divInt{}(\dv{SortInt{}}("10"), \dv{SortInt{}}("0")))"#,
        );
        for matches in matches_with_and_without_retention(&definition, &target, &subject) {
            assert!(matches.is_empty(), "{matches:#?}");
        }
    }

    /// The subject `pair(X, X /Int 0) ∧ ⌈X /Int 0⌉`: its term's fact (the ceil axiom's instance,
    /// false) is decided before it is assumed, so it cannot hold the constraint `⌈X /Int 0⌉` that
    /// it refutes, and the subject does not match.
    #[test]
    fn a_refuted_state_fact_is_not_assumed_for_its_constraints() {
        let definition = ceil_axiom_definition();
        let target = pair_target(&definition);
        let mut subject = zero_divisor_subject(&definition);
        subject.constraints.push(Predicate::Ceil(
            pattern(&definition, r#"divInt{}(X:SortInt{}, \dv{SortInt{}}("0"))"#).term,
        ));
        let matches = match_disjunction(&definition, &target, &[subject])
            .expect("no stop is armed")
            .expect("the match should be computed");
        assert!(matches.is_empty(), "{matches:#?}");
    }

    /// `pair(X, 10 /Int X)` has the fact `X =/=Int 0`, which neither the simplifier nor an absent
    /// solver refutes: the fact restates the subject and is not a condition of the match, so the
    /// match is decided, with no constraints, as without the fact.
    #[test]
    fn an_undecided_state_fact_keeps_the_match() {
        let definition = ceil_axiom_definition();
        let target = pair_target(&definition);
        let subject = pattern(
            &definition,
            r#"pair{}(X:SortInt{}, divInt{}(\dv{SortInt{}}("10"), X:SortInt{}))"#,
        );
        let matches = match_disjunction_with_solver(
            &definition,
            &target,
            &[subject],
            SimplificationOptions::default(),
            &NoSolver,
        )
        .expect("no stop is armed")
        .expect("the match should be decided without a solver");
        let [found] = matches.as_slice() else {
            panic!("expected one match, found {matches:#?}");
        };
        let int = Sort::simple("SortInt");
        let expected = Substitution::from([
            (
                Variable::new("A", int.clone()),
                Term::variable(Variable::new("X", int.clone())),
            ),
            (
                Variable::new("B", int),
                pattern(
                    &definition,
                    r#"divInt{}(\dv{SortInt{}}("10"), X:SortInt{})"#,
                )
                .term,
            ),
        ]);
        assert_eq!(found.substitution, expected, "{found:#?}");
        assert!(found.constraints.is_empty(), "{found:#?}");
    }

    /// An initial state with no instance yields no match, so it does not take the only result
    /// slot of a bounded search, and the search goes on to the state that matches.
    #[test]
    fn an_empty_initial_state_does_not_take_a_result_bound() {
        let definition = ceil_axiom_definition();
        let target = pair_target(&definition);
        let result = search_pattern_disjunction_with_solver(
            &definition,
            vec![
                zero_divisor_subject(&definition),
                pattern(
                    &definition,
                    r#"pair{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("2"))"#,
                ),
            ],
            &target,
            SearchOptions {
                search_type: SearchType::Star,
                max_results: Some(1),
                ..SearchOptions::default()
            },
            &NoSolver,
        );
        let [found] = result.matches.as_slice() else {
            panic!("expected one match, found {:#?}", result.matches);
        };
        let int = Sort::simple("SortInt");
        let expected = Substitution::from([
            (
                Variable::new("A", int.clone()),
                pattern(&definition, r#"\dv{SortInt{}}("1")"#).term,
            ),
            (
                Variable::new("B", int),
                pattern(&definition, r#"\dv{SortInt{}}("2")"#).term,
            ),
        ]);
        assert_eq!(found.substitution, expected, "{found:#?}");
    }
}
