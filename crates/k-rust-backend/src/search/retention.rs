//! Why a search ended, and the retention of its results.
//!
//! A search ends in one of four ways ([`SearchEnd`]), and the two ends that make a claim about
//! the work left behind carry a token minted here and nowhere else: [`Exhausted`] (nothing
//! remained, so the result set is complete up to the per-state entries) exists only once the
//! frontier was observed empty, and [`BreadthExceeded`] only once an oversized frontier was
//! recorded as one [`IncompleteSearch::BreadthBound`] entry. The result bound's evidence says
//! what the bound left behind: [`UnexploredWork`] when work remained, [`FurtherResult`] when a
//! result beyond the retained ones arrived. The token fields are private to this module, so the
//! search loops can state an end other than a cancellation only through [`pop_or_exhausted`],
//! [`remaining`], [`breadth_exceeded`] and [`retain_witness`].

#![deny(clippy::wildcard_enum_match_arm)]

use std::collections::{HashMap, VecDeque};

use super::{
    IncompleteSearch, PathSearchState, PathWitness, SearchEnd, SearchMatch, SearchOptions,
    SearchState, externalise_result,
};
use crate::{
    builtin::BuiltinEffect,
    definition::BackendDefinition,
    diagnostic::BackendDiagnostic,
    fresh::{RequestNames, SolutionKey},
    rewrite::Pattern,
    smt::SmtSolver,
    stop::StopCause,
    transition::{ObservationLog, ObservationOptions},
};

/// Nothing remained: the frontier was observed empty and the state the search stopped at, if
/// any, cannot expand. The only evidence [`SearchEnd::Exhausted`] accepts; minted by
/// `pop_or_exhausted` and `remaining`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Exhausted(());

/// Work remained when the result bound was reached (a queued state, or a state the search
/// stopped at that may still rewrite), so further results may exist. Minted by `remaining`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct UnexploredWork(());

/// A state selected as a result arrived after the result bound was full and was discarded, so
/// the retained results are not all of them. Minted by `retain_witness`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct FurtherResult(());

/// The frontier exceeded `max_breadth` and was recorded, unexplored, as one
/// [`IncompleteSearch::BreadthBound`] entry. Minted by `breadth_exceeded`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BreadthExceeded(());

/// What a path search's result bound left behind: a discarded path witness, or, for a search
/// that stopped at its N-th pattern match, the unexplored work after it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Truncation {
    UnexploredWork(UnexploredWork),
    FurtherResult(FurtherResult),
}

/// The head of every search loop: the next work item, or [`Exhausted`] once the frontier is
/// empty.
pub(super) fn pop_or_exhausted<T>(frontier: &mut VecDeque<T>) -> Result<T, Exhausted> {
    frontier.pop_front().ok_or(Exhausted(()))
}

/// What remains when a search stops at a bound.
#[must_use]
pub(super) enum Remaining {
    Unexplored(UnexploredWork),
    Exhausted(Exhausted),
}

impl Remaining {
    /// The end of a search that stops here: a result bound with `evidence` when work remained,
    /// exhaustion otherwise.
    pub(super) fn result_bound<E>(
        self,
        evidence: impl FnOnce(UnexploredWork) -> E,
    ) -> SearchEnd<E> {
        match self {
            Self::Unexplored(unexplored) => SearchEnd::ResultBound(evidence(unexplored)),
            Self::Exhausted(exhausted) => SearchEnd::Exhausted(exhausted),
        }
    }
}

/// A search's queue of unexplored work, as `remaining` observes it: a loop's `VecDeque`, or the
/// initial states a search has not yet queued.
pub(super) trait Frontier {
    fn is_empty(&self) -> bool;
}

impl<T> Frontier for VecDeque<T> {
    fn is_empty(&self) -> bool {
        VecDeque::is_empty(self)
    }
}

impl<T> Frontier for [T] {
    fn is_empty(&self) -> bool {
        <[T]>::is_empty(self)
    }
}

/// Whether work remains when a search stops at a bound: `Unexplored` when `frontier` is not
/// empty or `may_expand` holds for the state the search stopped at, `Exhausted` otherwise.
/// `may_expand` runs only when the frontier is empty.
pub(super) fn remaining<F: Frontier + ?Sized>(
    frontier: &F,
    may_expand: impl FnOnce() -> bool,
) -> Remaining {
    if !frontier.is_empty() || may_expand() {
        Remaining::Unexplored(UnexploredWork(()))
    } else {
        Remaining::Exhausted(Exhausted(()))
    }
}

/// When `frontier` holds more than `max_breadth` states, drain it, unexplored, into one
/// [`IncompleteSearch::BreadthBound`] entry and return the token; `None` otherwise.
#[must_use]
pub(super) fn breadth_exceeded<T>(
    frontier: &mut VecDeque<T>,
    incomplete: &mut Vec<IncompleteSearch>,
    max_breadth: Option<usize>,
    materialize: impl FnMut(T) -> SearchState,
) -> Option<BreadthExceeded> {
    if !max_breadth.is_some_and(|bound| frontier.len() > bound) {
        return None;
    }
    incomplete.push(IncompleteSearch::BreadthBound(
        frontier.drain(..).map(materialize).collect(),
    ));
    Some(BreadthExceeded(()))
}

/// How retaining a unique state result bears on the search's bounds.
#[must_use]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum StateRetention {
    Continue,
    /// `max_results` states are retained.
    ResultBound,
    /// The caller's collector reached its own bound on this state.
    PatternBound,
}

/// ```toml algorithm-site
/// id = "backend.search.configurations"
/// role = "part"
/// sites = ["retain_state_result"]
/// ```
///
/// Retain one unique state result and classify any result bound reached there.
///
/// A result is unique unless an earlier result is its state up to the names of the variables
/// the request does not name (their `RequestNames::state_key`s are equal, `retained` holds the
/// keys of `states`): such a result denotes the same configurations, so listing it again would
/// list one state twice and take a result slot from a different one.
///
/// A result dropped as a duplicate gives its path facts (`crate::path_facts`) to the result kept
/// for its key ([`union_path_facts`]): it is dropped anyway, so this changes no result but the
/// kept one's marks. Returns, with the retention, the index in `states` of the result that
/// holds `state`'s path: its own, or the one kept for its key.
pub(super) fn retain_state_result(
    states: &mut Vec<SearchState>,
    retained: &mut HashMap<Pattern, usize>,
    request: &RequestNames,
    state: SearchState,
    max_results: Option<usize>,
    pattern_bound_reached: &mut impl FnMut(&SearchState) -> bool,
) -> (StateRetention, usize) {
    let key = request.state_key(&state.pattern);
    if let Some(&index) = retained.get(&key) {
        union_path_facts(&mut states[index].diagnostics, &state.diagnostics);
        return (StateRetention::Continue, index);
    }
    let index = states.len();
    retained.insert(key, index);
    let pattern_bound_reached = pattern_bound_reached(&state);
    states.push(state);
    let retention = if pattern_bound_reached {
        StateRetention::PatternBound
    } else if max_results.is_some_and(|limit| states.len() >= limit) {
        StateRetention::ResultBound
    } else {
        StateRetention::Continue
    };
    (retention, index)
}

/// Add the path facts among `diagnostics` (`BackendDiagnostic::is_path_fact`), those
/// of a result or a match dropped as a duplicate, to `kept`, the diagnostics of the one retained
/// for its key, so that the kept one names every value the definition leaves open that a path
/// reaching it read. The dropped one's other diagnostics stay with its path.
pub(super) fn union_path_facts(
    kept: &mut Vec<BackendDiagnostic>,
    diagnostics: &[BackendDiagnostic],
) {
    for diagnostic in diagnostics {
        if diagnostic.is_path_fact() && !kept.contains(diagnostic) {
            kept.push(diagnostic.clone());
        }
    }
}

/// How retaining a path witness bears on the search's bounds.
#[must_use]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum WitnessRetention {
    Continue,
    /// A witness arrived with `max_results` witnesses already retained and was discarded.
    Further(FurtherResult),
    /// The caller's collector reached its own bound on this witness.
    PatternBound,
    /// The witness's externalisation stopped with this cause, published as the path's `Stopped`
    /// entry; no witness was retained.
    Stopped(StopCause),
}

/// ```toml algorithm-site
/// id = "backend.search.paths"
/// role = "part"
/// sites = ["retain_witness"]
/// ```
///
/// Retain one externalized path witness and classify any result bound reached there.
///
/// The witness is externalised in the simplifier's normal form (`externalise_result`); an
/// empty witness is not retained, a failed simplification is reported as incomplete, and a
/// stopped one is reported as the path's `Stopped` entry.
#[allow(clippy::too_many_arguments)]
pub(super) fn retain_witness(
    definition: &BackendDefinition,
    witnesses: &mut Vec<PathWitness>,
    path: &PathSearchState,
    options: &SearchOptions,
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
        return WitnessRetention::Further(FurtherResult(()));
    }
    let externalised = match externalise_result(
        definition,
        super::with_trace(path.state.clone(), path.trace.clone()),
        path.observation,
        path.diagnostics.clone(),
        options.max_simplification_iterations,
        // The path search keeps every witness's trace.
        true,
        solver,
        effects,
        &mut |_| {},
        incomplete,
        observation_log,
        observation_options,
    ) {
        Ok(externalised) => externalised,
        Err(cause) => return WitnessRetention::Stopped(cause),
    };
    if let Some(state) = externalised {
        let witness = PathWitness {
            id: path.id.to_vec(),
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

/// Retain one pattern match unless a retained match is the same solution; whether
/// `max_results` matches are now retained.
///
/// Two matches are the same solution when they are equal up to the names of the variables the
/// request does not name (their `RequestNames::solution_key`s are equal, `retained` holds the
/// keys of `matches`): they denote the same instances of the target, so the second would take
/// a result slot from a different solution.
///
/// A match dropped as the same solution gives its path facts (`crate::path_facts`), those of
/// its state's path and of its own matching, to the match kept for its key
/// ([`union_path_facts`]). Returns whether `max_results` matches are retained, with the index in
/// `matches` of the match that holds `found`: its own, or the one kept for its key.
pub(super) fn retain_pattern_match(
    matches: &mut Vec<SearchMatch>,
    retained: &mut HashMap<SolutionKey, usize>,
    request: &RequestNames,
    found: SearchMatch,
    max_results: Option<usize>,
) -> (bool, usize) {
    let key = request.solution_key(&found.substitution, &found.constraints);
    if let Some(&index) = retained.get(&key) {
        let kept = &mut matches[index];
        union_path_facts(&mut kept.state.diagnostics, &found.state.diagnostics);
        union_path_facts(&mut kept.diagnostics, &found.diagnostics);
        return (false, index);
    }
    let index = matches.len();
    retained.insert(key, index);
    matches.push(found);
    (
        max_results.is_some_and(|bound| matches.len() >= bound),
        index,
    )
}
