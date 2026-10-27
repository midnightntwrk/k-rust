//! ```toml algorithm
//! id = "backend.proof.search"
//! name = "reachability-logic proof search"
//! sites = ["prove_claim", "extend_frontier", "finish_at_breadth_limit", "apply_claim", "stuck_leaf", "ProofLeaf::proven_vacuously", "ProofLeaf::with_contradicted_total"]
//! variable = "s = explored states; c = circularities; u = states still pending when the breadth limit is reached"
//! counters = ["ProofStatesExplored", "ProofImplicationChecks"]
//! span = "per problem"
//! consumes = [
//!   { type = "k_rust_backend::claim::ReachabilityClaim", role = "claim" },
//!   { type = "k_rust_backend::matching::MatchResult", role = "match result" },
//!   { type = "k_rust_backend::rewrite::RewriteResult", role = "rewrite result" },
//!   { type = "k_rust_backend::unification::UnificationResult", role = "unification result" },
//!   { type = "k_rust_backend::substitution::Substitution", role = "extracted substitution" },
//! ]
//! produces = [{ type = "k_rust_backend::proof::ProofResult", role = "proof result" }]
//!
//! [[cost]]
//! mode = "one proof"
//! bound = "O(s) x (simplification + one is_sat + implication when depth >= min_depth + O(c) claim applications + one rewrite step), plus u leaf simplifications at the breadth limit, plus one terminal-instance certification attempt at each refuted current target on a certifiable trace and for each Stuck leaf (stuck_leaf), each up to two is_sat queries and two rewrite steps, plus for a step's undefined step (decide_undefined_step, shared with executions) one normalization of each sibling candidate not yet normalized, one predicate simplification and one is_sat per undefined candidate and trivial entry, and one more simplification when several are non-empty over one term; a step with trivial entries and an applied candidate normalizes each candidate within the step"
//!
//! [[cost]]
//! mode = "facade evidence projection"
//! bound = "one scan of each retained leaf trace to select actual claim applications, one sorted set of the available trusted reachability labels, and encoding of a contradicted-total record only where the core retained one; no solver query or rerun"
//! ```
//!
//! Reachability-logic proof search: per explored state one
//! simplification, one subsumption check (`Counter::ProofImplicationChecks`), circularity
//! application at depth > 0, one rewrite step (one-path: tracking whether it may drop a
//! successor, until one may have been dropped); breadth- or depth-first by option, no state
//! deduplication; O(explored states) x (simplification + implication + |circularities| x
//! claim application + one step), `Counter::ProofStatesExplored`. A `Stuck` leaf is certified
//! as a refutation by at most two more satisfiability queries and two more rewrite steps
//! (`stuck_leaf`); the same refinement can find a terminal counterexample at a refuted
//! current target before branching on a symbolic continuation.

#![deny(clippy::wildcard_enum_match_arm)]

use std::{
    collections::{BTreeSet, VecDeque},
    error::Error,
    fmt,
    sync::Arc,
    time::Duration,
};

use k_rust_kore::{
    measure::{self, Algorithm, Counter},
    names::{BuiltinSort, WellKnownSymbol},
};

use crate::{
    claim::{ReachabilityClaim, ReachabilityMode},
    condition::{MatchSolution, eliminate_bindings, instantiate_constraints},
    definedness::{ceil_term, pattern_knowledge},
    definition::BackendDefinition,
    fresh::FreshCounter,
    implication::{
        Coverage, CoverageCondition, ImplicationCondition, ImplicationError, Instance,
        check_disjunctive_implication_with_existentials,
    },
    matching::{
        MatchMode, MatchResult, match_terms_in_definition, solve_collection_pairs_in_definition,
    },
    rewrite::{
        HaltReason, IndeterminateReason, Pattern, RecoveredMatch, RemainderBranch, RewriteResult,
        Sibling, TraceEntry, TraceKind, Truth, UndecidedStep, UndefinedDecision, UndefinedGroup,
        UndefinedPart, collection_unification_definedness, conjunctively_contains_alpha_equivalent,
        decide_undefined_step, entry_undefined_part, predicates_truth,
        quantify_introduced_variables, recover_indeterminate_match,
        rewrite_step_sequential_tracking_dropped, rewrite_step_sequential_with_options,
        rewrite_step_with_options, sibling_undefined_parts, simplify_leaf_pattern,
        substitute_predicates, successor_undefinedness,
    },
    simplify::{
        ContradictedTotal, DEFAULT_MAX_SIMPLIFICATION_ITERATIONS, SimplificationError,
        SimplificationOptions, simplify_predicates_with_solver, simplify_with_solver,
    },
    smt::{Satisfiability, SmtError, SmtSolver, Validity},
    stop::{self, StopCause, Stoppable},
    substitution::{Substitution, compose, extract_substitution_for, substitute},
    term::names::FreshMarker,
    term::{HeadRole, Term, TermKind},
    timeout::{StepTimeoutController, StepTimeoutOptions, StepTimer},
    unification::{MatchUnification, unify_from},
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ProofOptions {
    pub max_depth: u64,
    pub min_depth: u64,
    pub breadth_limit: Option<usize>,
    pub max_counterexamples: usize,
    pub max_simplification_iterations: usize,
    pub allow_vacuous: bool,
    pub search_order: ProofSearchOrder,
    pub step_timeout: Option<Duration>,
    pub moving_average_timeout: bool,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum ProofSearchOrder {
    #[default]
    BreadthFirst,
    DepthFirst,
}

impl Default for ProofOptions {
    fn default() -> Self {
        Self {
            max_depth: u64::MAX,
            min_depth: 0,
            breadth_limit: None,
            max_counterexamples: 1,
            max_simplification_iterations: DEFAULT_MAX_SIMPLIFICATION_ITERATIONS,
            allow_vacuous: false,
            search_order: ProofSearchOrder::BreadthFirst,
            step_timeout: None,
            moving_average_timeout: false,
        }
    }
}

/// A claim's verdict.
///
/// `Disproved` states that the claim is false: some leaf is a certified refutation
/// ([`ProofLeaf::certified`]). `Failed` states only what the search established: it stopped at
/// a leaf outside the destination that it did not continue (an uncertified `Stuck` leaf), or at
/// an empty leaf that the vacuity policy rejects (`Trivial`, `Vacuous`). Neither shows the claim
/// false. Precedence when leaves disagree: `Disproved`, `Failed`, `Indeterminate`, `DepthBound`,
/// `BreadthBound`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ProofStatus {
    Proven,
    Disproved,
    Failed,
    Indeterminate,
    DepthBound,
    BreadthBound,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProofIndeterminateReason {
    Implication,
    Rewrite(IndeterminateReason),
    Simplification(SimplificationError),
    Claim {
        claim_id: String,
        reason: ClaimIndeterminateReason,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ClaimIndeterminateReason {
    Simplification(SimplificationError),
    Match {
        substitution: Substitution,
        remainder: Vec<(Term, Term)>,
    },
    Smt(SmtError),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProofLeafOutcome {
    Proven(ImplicationCondition),
    Trusted,
    Stuck,
    Trivial,
    Vacuous,
    DepthBound,
    BreadthBound,
    /// The state's step stopped before it produced its answer: the step deadline passed (the
    /// proof then ends) or the thread's stack ran out (the proof goes on with the other states).
    /// A cancelled request or a failed solver prelude is never a leaf: it ends the proof without
    /// a leaf for the state being explored, and a leaf whose outcome was already decided when it
    /// arrived during its normalisation keeps that outcome; [`ProofResult::stopped`] is the one
    /// place it is named. A stop during a leaf's normalisation keeps the decided outcome whatever
    /// its cause; a stop during a `Stuck` leaf's certification is its state's step's stop.
    Stopped(StopCause),
    Indeterminate(ProofIndeterminateReason),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofLeaf {
    pub pattern: Pattern,
    pub depth: u64,
    pub trace: Vec<TraceEntry>,
    pub outcome: ProofLeafOutcome,
    /// Set only on a `Stuck` leaf that certifies a refutation of the claim: some configuration
    /// the claim's left-hand side covers reaches a configuration of this leaf on every path
    /// the search followed, never passes through the destination, and has no successor there.
    /// The conditions are listed at `stuck_leaf` in this module.
    pub certified: bool,
    /// Set when emptiness or an undefined step comes from an equation of a symbol declared
    /// `total` (or `functional`), including accepted vacuous success: the equation reduced an application to bottom and the
    /// definition contradicts the attribute there. A diagnostic only; the leaf and the verdict
    /// are the same with or without it ([`ContradictedTotal`]).
    pub contradicted_total: Option<Box<ContradictedTotal>>,
}

impl ProofLeaf {
    /// Whether this leaf was accepted as Proven(False) by the vacuity policy. An undefined
    /// step may retain its nonempty predecessor as the displayed pattern; this flag does not
    /// assert that the displayed pattern itself is empty.
    #[must_use]
    pub fn proven_vacuously(&self) -> bool {
        matches!(&self.outcome, ProofLeafOutcome::Proven(condition)
            if condition.predicates == [crate::rule::Predicate::False])
    }

    /// Retain the contradiction on an empty/undefined branch, including accepted
    /// Proven(False). The displayed pattern can be its predecessor; the record explains
    /// the branch's undefinedness and does not change the verdict.
    fn with_contradicted_total(
        mut self,
        contradicted_total: Option<Box<ContradictedTotal>>,
    ) -> Self {
        if matches!(
            self.outcome,
            ProofLeafOutcome::Vacuous | ProofLeafOutcome::Trivial
        ) || self.proven_vacuously()
        {
            self.contradicted_total = contradicted_total;
        }
        self
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofResult {
    pub status: ProofStatus,
    pub leaves: Vec<ProofLeaf>,
    pub explored_states: u64,
    pub unexplored_states: u64,
    /// Set when the exploration ended early because it stopped: a cancelled request, a failed
    /// solver prelude, or a passed step deadline (whose state is also a `Stopped` leaf). Also set
    /// when the request was cancelled or the solver's prelude failed while a leaf whose outcome
    /// was already decided (`Stuck`, `DepthBound`, `BreadthBound`, `Indeterminate`) was being
    /// normalised, even if no state remains: that leaf keeps its outcome with its pattern left
    /// unsimplified, and the poll after the refinement names the stop. The status is still the
    /// one the leaves found establish, so a `Disproved` or `Failed` verdict reached before the
    /// stop stands; `Proven` is not reachable, since states remain unexplored or a leaf that is
    /// not proven was being refined.
    pub stopped: Option<StopCause>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProofError {
    Implication(ImplicationError),
    ZeroCounterexampleLimit,
    /// The claim's constraints have no definedness-explicit form
    /// ([`ReachabilityClaim::unstated`]), so no proof decision on them would answer for the
    /// instances where one of their terms is undefined: the claim is refused, not proven.
    UnstatedDefinedness(crate::definition::UnstatedDefinedness),
}

impl fmt::Display for ProofError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Implication(error) => write!(formatter, "{error}"),
            Self::UnstatedDefinedness(reason) => {
                write!(
                    formatter,
                    "the claim's constraints cannot be read faithfully: {reason}"
                )
            }
            Self::ZeroCounterexampleLimit => formatter.write_str(
                "the counterexample limit is 0, and a proof needs a limit of at least 1",
            ),
        }
    }
}

impl Error for ProofError {}

pub fn prove_claim(
    definition: &BackendDefinition,
    claim: &ReachabilityClaim,
    circularities: &[&ReachabilityClaim],
    options: ProofOptions,
    solver: &dyn SmtSolver,
) -> Result<ProofResult, ProofError> {
    let _apart = crate::rule::ApartScope::enter();
    let _domain = crate::term::domain::DomainScope::enter(definition);
    let _hook_values = crate::deferred::HookValueScope::enter(definition);
    let _span = measure::algorithm_span(Algorithm::BackendProofSearch);
    if let Some(reason) = &claim.unstated {
        return Err(ProofError::UnstatedDefinedness(reason.clone()));
    }
    // A claim whose meaning cannot be stated is no assumption either, trusted or not.
    let circularities = circularities
        .iter()
        .copied()
        .filter(|circularity| circularity.unstated.is_none())
        .collect::<Vec<_>>();
    let circularities = circularities.as_slice();
    if options.max_counterexamples == 0 {
        return Err(ProofError::ZeroCounterexampleLimit);
    }
    if claim.attributes.trusted {
        return Ok(ProofResult {
            status: ProofStatus::Proven,
            leaves: vec![ProofLeaf {
                pattern: claim.lhs.clone(),
                depth: 0,
                trace: Vec::new(),
                outcome: ProofLeafOutcome::Trusted,
                certified: false,
                contradicted_total: None,
            }],
            explored_states: 0,
            unexplored_states: 0,
            stopped: None,
        });
    }

    let mut initial = claim.lhs.clone();
    // The claim's left-hand side states its own definedness. One that depends on an impure
    // application in an operand a conditional never evaluates is not restated; simplifying the
    // state, which reaches the same operand, is the unsupported-hook outcome.
    let initial_definedness = ceil_term(definition, &initial.term).unwrap_or_default();
    extend_unique(&mut initial.constraints, initial_definedness);
    let mut pending = VecDeque::from([ProofState::initial(initial)]);
    let mut leaves = Vec::new();
    // The claim's universals are fixed for the whole proof, including those that the path
    // has overwritten and that no longer occur in the current state; only the destination's
    // existentials may be quantified when a coverage condition is complemented.
    let claim_universals = variables_of_claim(claim)
        .difference(&claim.existentials)
        .cloned()
        .collect::<BTreeSet<_>>();
    // One request: the proved claim with every circularity and trusted lemma it may apply.
    // Every name the proof mints, rewriting or renaming a claim, is apart from all of them.
    let mut fresh_counter = FreshCounter::for_request(
        &std::iter::once(claim)
            .chain(circularities.iter().copied())
            .flat_map(|claim| std::iter::once(&claim.lhs).chain(claim.rhs.iter()))
            .collect::<Vec<_>>(),
    );
    let mut explored_states = 0;
    let timeout_controller = StepTimeoutController::new(StepTimeoutOptions {
        manual: options.step_timeout,
        moving_average: options.moving_average_timeout,
    });
    // A stop observed after a leaf's outcome was decided, while the leaf was refined; the
    // leaf keeps its outcome and every exit names the stop (`forgone_refinement_stop`).
    let mut forgone_stop = None;
    macro_rules! record_leaf {
        ($leaf:expr) => {{
            leaves.push($leaf);
            if counterexample_limit_reached(&leaves, options) {
                return Ok(finish_explored(
                    leaves,
                    explored_states,
                    pending.len() as u64,
                    forgone_stop,
                ));
            }
        }};
    }
    // Every queued state is a rewrite or claim successor at depth + 1. Complete rewrite
    // remainders and implication remainders are classified without entering the frontier.
    // Invariant: `pending` holds the unexpanded states; `leaves` only grows; pops are counted.
    'states: while let Some(mut state) = match options.search_order {
        ProofSearchOrder::BreadthFirst => pending.pop_front(),
        ProofSearchOrder::DepthFirst => pending.pop_back(),
    } {
        // No step has begun: whatever stopped, the state stays unexplored and the proof ends.
        if let Err(stop) = stop::check() {
            return Ok(finish_stopped(
                leaves,
                explored_states,
                pending.len() as u64 + 1,
                stop.into_cause(),
            ));
        }
        explored_states += 1;
        measure::bump(Counter::ProofStatesExplored);
        let mut step_timer = timeout_controller.begin_step();
        // Publish a stop of this state's step as `proof_stop` decides; never falls through.
        macro_rules! publish_stop {
            ($cause:expr) => {{
                let cause: StopCause = $cause;
                match proof_stop(&cause, &mut step_timer) {
                    ProofStop::Leaf => {
                        record_leaf!(state.leaf(ProofLeafOutcome::Stopped(cause)));
                        continue 'states;
                    }
                    ProofStop::LeafAndFinish => {
                        leaves.push(state.leaf(ProofLeafOutcome::Stopped(cause.clone())));
                        return Ok(finish_stopped(
                            leaves,
                            explored_states,
                            pending.len() as u64,
                            cause,
                        ));
                    }
                    ProofStop::Finish => {
                        return Ok(finish_stopped(
                            leaves,
                            explored_states,
                            pending.len() as u64 + 1,
                            cause,
                        ));
                    }
                }
            }};
        }
        // Poll for a stop between two phases of the state's step and publish it; no stop is
        // alive at a poll, since every phase's own stop is published before it.
        macro_rules! finish_if_interrupted {
            () => {
                if let Err(stop) = stop::check() {
                    publish_stop!(stop.into_cause());
                }
            };
        }
        // Record a leaf built by `externalise_leaf` or `stuck_leaf`, which refine an outcome that
        // is already decided, then poll for the stop that refinement may have forgone. A leaf the
        // refinement proved (an empty state under `allow_vacuous`) rests on no missing answer, nor
        // does a split part the refinement showed empty, which is no leaf.
        macro_rules! record_refined_leaf {
            ($leaf:expr) => {{
                let leaf: Option<ProofLeaf> = $leaf;
                if let Some(leaf) = leaf {
                    if !is_proven(&leaf) {
                        forgone_stop = forgone_stop.or_else(forgone_refinement_stop);
                    }
                    record_leaf!(leaf);
                }
            }};
        }
        // The leaf of `stuck_leaf` for `$stuck`, recorded; a stop of its certification ends this
        // state's step, and `$stuck` is the state it publishes.
        macro_rules! record_stuck_leaf {
            ($stuck:expr, $evidence:expr) => {{
                let stuck: ProofState = $stuck;
                match stuck_leaf(
                    definition,
                    stuck.clone(),
                    $evidence,
                    claim.mode,
                    &fresh_counter,
                    options,
                    solver,
                ) {
                    Ok(leaf) => record_refined_leaf!(leaf),
                    Err(stop) => {
                        state = stuck;
                        publish_stop!(stop.into_cause());
                    }
                }
            }};
        }
        // A state that denotes no state, found by its normalization: when a rule step produced
        // it, it is no successor of that step, and its instances are the step's undefined step
        // where no other candidate takes them (`proof_undefined_step`); otherwise, or when the
        // configuration the step was taken from has no instance, its emptiness is graded by what
        // the state is (`vacuous_outcome`): `Vacuous` for a successor.
        macro_rules! record_bottom {
            ($contradicted_total:expr) => {{
                let contradicted_total: Option<Box<ContradictedTotal>> = $contradicted_total;
                match proof_undefined_step(
                    definition,
                    &state,
                    contradicted_total.clone(),
                    options,
                    solver,
                ) {
                    Ok(ProofUndefined::Leaves(undefined)) => {
                        for (undefined, contradicted_total) in undefined {
                            if let Some(outcome) =
                                vacuous_outcome(&undefined, options, ProofLeafOutcome::Trivial)
                            {
                                record_leaf!(
                                    undefined
                                        .leaf(outcome)
                                        .with_contradicted_total(contradicted_total)
                                );
                            }
                        }
                    }
                    Ok(ProofUndefined::Covered) => {}
                    Ok(ProofUndefined::NoInstance) => {
                        if let Some(outcome) =
                            vacuous_outcome(&state, options, ProofLeafOutcome::Vacuous)
                        {
                            record_leaf!(
                                state
                                    .leaf(outcome)
                                    .with_contradicted_total(contradicted_total)
                            );
                        }
                    }
                    Err(stop) => publish_stop!(stop.into_cause()),
                }
                continue 'states;
            }};
        }
        finish_if_interrupted!();
        let simplified_constraints = match simplify_predicates_with_solver(
            definition,
            &state.pattern.constraints,
            &[],
            SimplificationOptions::keep_partial(options.max_simplification_iterations),
            solver,
        ) {
            Ok(simplified_constraints) => simplified_constraints,
            Err(stop) => publish_stop!(stop.into_cause()),
        };
        finish_if_interrupted!();
        state.pattern.constraints = match simplified_constraints {
            Ok(constraints) => constraints,
            Err(error) => {
                record_leaf!(state.leaf(ProofLeafOutcome::Indeterminate(
                    ProofIndeterminateReason::Simplification(error),
                )));
                continue;
            }
        };
        if predicates_truth(&state.pattern.constraints) == Truth::False {
            record_bottom!(None);
        }
        let simplified = match simplify_with_solver(
            definition,
            &state.pattern.term,
            &state.pattern.constraints,
            SimplificationOptions::keep_partial(options.max_simplification_iterations),
            solver,
        ) {
            Ok(simplified) => simplified,
            Err(stop) => publish_stop!(stop.into_cause()),
        };
        finish_if_interrupted!();
        let simplified = match simplified {
            Ok(simplified) => simplified.into_parts(),
            Err(error) => {
                record_leaf!(state.leaf(ProofLeafOutcome::Indeterminate(
                    ProofIndeterminateReason::Simplification(error),
                )));
                continue;
            }
        };
        let contradicted_total = simplified.contradicted_total;
        state.pattern.term = simplified.term;
        extend_unique(
            &mut state.pattern.constraints,
            simplified.conditions.into_predicates(),
        );
        state.trace.extend(
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

        let bottom = match state_is_bottom(&state, solver) {
            Ok(bottom) => bottom,
            Err(stop) => publish_stop!(stop.into_cause()),
        };
        if bottom {
            record_bottom!(contradicted_total);
        }

        let mut implication_indeterminate = false;
        let mut current_target_refuted = false;
        let mut implication_remainder = None;
        if state.depth >= options.min_depth {
            measure::bump(Counter::ProofImplicationChecks);
            let implication = match check_disjunctive_implication_with_existentials(
                definition,
                &state.pattern,
                &claim.rhs,
                &claim.existentials,
                SimplificationOptions {
                    max_iterations: options.max_simplification_iterations,
                    ..SimplificationOptions::default()
                },
                solver,
            ) {
                Ok(implication) => implication,
                // The check stopped (it ran out of this thread's stack, say): the state cannot be
                // decided here, and `proof_stop` decides whether the rest of the proof can be.
                Err(stop) => publish_stop!(stop.into_cause()),
            };
            finish_if_interrupted!();
            let implication = implication.map_err(ProofError::Implication)?;
            current_target_refuted = matches!(
                implication,
                Coverage::PartialCoverage { .. } | Coverage::ConditionRefuted { .. }
            );
            match implication {
                Coverage::Covered(bindings) => {
                    record_leaf!(state.leaf(ProofLeafOutcome::Proven(bindings.into())));
                    continue;
                }
                Coverage::Vacuous => {
                    record_bottom!(None);
                }
                // Only a coverage condition says which part of the state already lies in the
                // destination, so only its complement is the uncovered part. A refuted
                // destination condition covers none of the state: its report (bindings and
                // predicates) has no complement, and the whole state takes the arms below.
                // A coverage condition splits the state into the covered part, which needs no
                // leaf, and the uncovered part. When the uncovered part is shown empty, the
                // destination covers every configuration of the state, which is a proven leaf.
                Coverage::PartialCoverage { coverage, .. } | Coverage::Contingent(coverage) => {
                    let uncovered = match uncovered_remainder(
                        definition,
                        &state.pattern,
                        claim,
                        &claim_universals,
                        &coverage,
                        options,
                        solver,
                    ) {
                        Ok(uncovered) => uncovered,
                        Err(stop) => publish_stop!(stop.into_cause()),
                    };
                    finish_if_interrupted!();
                    let Some(remainder) = uncovered else {
                        record_leaf!(state.leaf(ProofLeafOutcome::Proven(coverage.to_condition())));
                        continue;
                    };
                    implication_remainder = Some(remainder);
                }
                Coverage::ConditionRefuted { .. } | Coverage::TermMismatch => {}
                Coverage::Undecided => implication_indeterminate = true,
            }
        }

        if state.depth < options.min_depth || implication_indeterminate {
            state.destination_undecided = true;
        }

        if let Some(remainder) = implication_remainder {
            // This is the part of the current state not covered by the destination,
            // not a new proof state. Continue the same iteration with the complement
            // attached so that rewriting gets a chance to make progress. Re-enqueuing
            // it would immediately repeat the same implication check forever.
            state = state.remaining(remainder);
        }

        // A symbolic continuation can include a terminal instance (its K tail is empty)
        // beside instances that can still move. Preserve the existing exact terminal-instance
        // refutation before branching on that continuation. A failed certification says
        // nothing about future reachability: discard its refinement and continue this state.
        if current_target_refuted && state.path_certifiable() {
            let candidate = crate::diagnostic::attempt(
                || {
                    stuck_leaf(
                        definition,
                        state.clone(),
                        StuckEvidence::StepNotRun,
                        claim.mode,
                        &fresh_counter,
                        options,
                        solver,
                    )
                },
                |result| matches!(result, Ok(Some(leaf)) if leaf.certified),
            );
            match candidate {
                Ok(Some(leaf)) if leaf.certified => {
                    record_leaf!(leaf);
                    continue;
                }
                Ok(_) => {}
                Err(stop) => publish_stop!(stop.into_cause()),
            }
        }

        if let ProofStateKind::Remaining(undecided) = state.kind.clone() {
            let outcome = match undecided {
                Some(UndecidedStep::Indeterminate(reason)) => {
                    ProofLeafOutcome::Indeterminate(ProofIndeterminateReason::Rewrite(reason))
                }
                Some(UndecidedStep::Simplification(error)) => {
                    ProofLeafOutcome::Indeterminate(ProofIndeterminateReason::Simplification(error))
                }
                None if implication_indeterminate => {
                    ProofLeafOutcome::Indeterminate(ProofIndeterminateReason::Implication)
                }
                None => {
                    record_stuck_leaf!(state, StuckEvidence::StepNotRun);
                    continue;
                }
            };
            record_refined_leaf!(externalise_leaf(
                definition, state, outcome, options, solver
            ));
            continue;
        }

        if state.depth >= options.max_depth {
            record_refined_leaf!(externalise_leaf(
                definition,
                state,
                ProofLeafOutcome::DepthBound,
                options,
                solver,
            ));
            continue;
        }

        let mut claim_indeterminate = None;
        if state.depth > 0 {
            let mut claim_transition = None;
            for candidate in circularities {
                if claim.mode == ReachabilityMode::AllPath
                    && candidate.mode == ReachabilityMode::OnePath
                {
                    continue;
                }
                let transition = match apply_claim(
                    definition,
                    candidate,
                    &state.pattern,
                    options,
                    solver,
                    &mut fresh_counter,
                ) {
                    Ok(transition) => transition,
                    Err(stop) => publish_stop!(stop.into_cause()),
                };
                finish_if_interrupted!();
                match transition {
                    ClaimApplication::NotApplicable => {}
                    ClaimApplication::Indeterminate(reason) => {
                        claim_indeterminate.get_or_insert_with(|| {
                            ProofIndeterminateReason::Claim {
                                claim_id: candidate.attributes.unique_id.clone(),
                                reason,
                            }
                        });
                    }
                    transition @ ClaimApplication::Applied { .. } => {
                        claim_transition = Some((candidate, transition));
                        break;
                    }
                }
            }
            if let Some((candidate, transition)) = claim_transition {
                match transition {
                    ClaimApplication::Applied {
                        patterns,
                        remainder,
                    } => {
                        if extend_frontier(
                            &mut pending,
                            patterns.into_iter().map(|pattern| {
                                state.clone().claimed(
                                    pattern,
                                    candidate.attributes.label.clone(),
                                    candidate.attributes.unique_id.clone(),
                                )
                            }),
                            options.breadth_limit,
                        ) {
                            return Ok(finish_at_breadth_limit(
                                definition,
                                leaves,
                                pending,
                                explored_states,
                                forgone_stop,
                                options,
                                solver,
                            ));
                        }
                        // The sub-case the claim did not cover stays at the same depth and
                        // continues through the other claims and the semantics, exactly like
                        // the remainder of a partially applicable rule.
                        if let Some(remainder) = remainder
                            && extend_frontier(
                                &mut pending,
                                std::iter::once(state.remaining(remainder)),
                                options.breadth_limit,
                            )
                        {
                            return Ok(finish_at_breadth_limit(
                                definition,
                                leaves,
                                pending,
                                explored_states,
                                forgone_stop,
                                options,
                                solver,
                            ));
                        }
                    }
                    ClaimApplication::Indeterminate(_) | ClaimApplication::NotApplicable => {
                        unreachable!()
                    }
                }
                continue;
            }
        }

        let simplification =
            SimplificationOptions::keep_partial(options.max_simplification_iterations);
        let stepped = match claim.mode {
            // Once the trace may have dropped a successor, no later step can make it certifiable
            // again, so the step no longer asks.
            ReachabilityMode::OnePath if state.alternative_discarded => {
                rewrite_step_sequential_with_options(
                    definition,
                    &state.pattern,
                    &mut fresh_counter,
                    simplification,
                    solver,
                )
                .map(|rewritten| (rewritten, true))
            }
            ReachabilityMode::OnePath => rewrite_step_sequential_tracking_dropped(
                definition,
                &state.pattern,
                &mut fresh_counter,
                simplification,
                solver,
            ),
            ReachabilityMode::AllPath => rewrite_step_with_options(
                definition,
                &state.pattern,
                &mut fresh_counter,
                simplification,
                solver,
            )
            .map(|rewritten| (rewritten, false)),
        };
        let (rewritten, dropped) = match stepped {
            Ok(stepped) => stepped,
            Err(stop) => publish_stop!(stop.into_cause()),
        };
        finish_if_interrupted!();
        if dropped
            && matches!(
                rewritten,
                RewriteResult::Finished(_) | RewriteResult::Branch { .. }
            )
        {
            state.alternative_discarded = true;
        }
        match rewritten {
            RewriteResult::Finished(applied) => {
                if extend_frontier(
                    &mut pending,
                    state.successors(vec![applied], false, 0, StepUndefinedness::default()),
                    options.breadth_limit,
                ) {
                    return Ok(finish_at_breadth_limit(
                        definition,
                        leaves,
                        pending,
                        explored_states,
                        forgone_stop,
                        options,
                        solver,
                    ));
                }
            }
            RewriteResult::Branch {
                branches,
                remainder,
                trivial,
                ..
            } => {
                // The instances the step itself left without a defined successor (its trivial
                // entries) are parts of its undefined step, with those of the candidates whose
                // successors normalize to `\bottom`: one undefined step, whose instances fail the
                // claim, as any instance with no successor does. With such entries the
                // candidates are normalized here, so that the undefined step is decided once;
                // otherwise each successor decides it if it turns out to denote no state.
                let depth = state.depth + 1;
                let offset = trivial.len();
                let mut parts = Vec::new();
                for (index, entry) in trivial.iter().enumerate() {
                    match entry_undefined_part(
                        definition,
                        options.max_simplification_iterations,
                        solver,
                        index,
                        entry,
                        depth,
                    ) {
                        Ok(Some(part)) => parts.push(part),
                        Ok(None) => {}
                        Err(stop) => publish_stop!(stop.into_cause()),
                    }
                }
                finish_if_interrupted!();
                let has_remainder = remainder.is_some();
                let successors = if parts.is_empty() {
                    state.successors(branches, has_remainder, offset, Default::default())
                } else {
                    let mut defined = Vec::with_capacity(branches.len());
                    for (candidate, applied) in branches.into_iter().enumerate() {
                        let rule = applied.observing_rule();
                        let undefined = match successor_undefinedness(
                            definition,
                            &applied.pattern,
                            &applied.before.constraints,
                            simplification,
                            solver,
                            None,
                        ) {
                            Ok(undefined) => undefined,
                            Err(stop) => publish_stop!(stop.into_cause()),
                        };
                        match undefined {
                            Some(undefined) => parts.push(UndefinedPart::candidate(
                                offset + candidate,
                                &applied.before,
                                &applied.pattern,
                                &applied.unique_id,
                                &applied.label,
                                rule,
                                undefined.halt(depth),
                                Vec::new(),
                                applied.remainder_simplifications.clone(),
                            )),
                            None => defined.push(applied),
                        }
                    }
                    let built = defined
                        .iter()
                        .map(|applied| applied.pattern.clone())
                        .collect::<Vec<_>>();
                    let others = !built.is_empty() || has_remainder;
                    let decision = decide_undefined_step(
                        definition,
                        options.max_simplification_iterations,
                        solver,
                        parts,
                        &built.iter().collect::<Vec<_>>(),
                        others,
                        &mut crate::diagnostic::PathDiagnostics::new_request(),
                    );
                    let reported = matches!(decision, Ok(UndefinedDecision::Groups(..)));
                    match decision {
                        Ok(UndefinedDecision::Groups(groups, _)) => {
                            for group in groups {
                                let (undefined, contradicted_total) = state.undefined_group(group);
                                if let Some(outcome) =
                                    vacuous_outcome(&undefined, options, ProofLeafOutcome::Trivial)
                                {
                                    record_leaf!(
                                        undefined
                                            .leaf(outcome)
                                            .with_contradicted_total(contradicted_total)
                                    );
                                }
                            }
                        }
                        Ok(UndefinedDecision::Covered) => {}
                        Ok(UndefinedDecision::NoInstance) => {
                            // Nothing is dropped: no instance is left without a defined candidate
                            // or a remainder to take it.
                            debug_assert!(
                                built.is_empty() && !has_remainder,
                                "an undefined step with no instance leaves no defined candidate and no remainder"
                            );
                            if let Some(outcome) =
                                vacuous_outcome(&state, options, ProofLeafOutcome::Vacuous)
                            {
                                record_leaf!(state.clone().leaf(outcome));
                            }
                            continue;
                        }
                        Err(stop) => publish_stop!(stop.into_cause()),
                    }
                    finish_if_interrupted!();
                    let count = defined.len();
                    state.successors(
                        defined,
                        has_remainder,
                        offset,
                        StepUndefinedness::decided(offset, count, reported),
                    )
                };
                let mut successors = successors;
                if let Some(remainder) = remainder {
                    successors.push(state.clone().rewrite_remaining(remainder));
                }
                if extend_frontier(&mut pending, successors, options.breadth_limit) {
                    return Ok(finish_at_breadth_limit(
                        definition,
                        leaves,
                        pending,
                        explored_states,
                        forgone_stop,
                        options,
                        solver,
                    ));
                }
            }
            RewriteResult::Stuck(_) => {
                let outcome = if implication_indeterminate {
                    ProofLeafOutcome::Indeterminate(ProofIndeterminateReason::Implication)
                } else if let Some(reason) = claim_indeterminate {
                    ProofLeafOutcome::Indeterminate(reason)
                } else {
                    record_stuck_leaf!(state, StuckEvidence::StepStuck);
                    continue;
                };
                record_refined_leaf!(externalise_leaf(
                    definition, state, outcome, options, solver
                ));
            }
            RewriteResult::Trivial(_, applications) => {
                let contradicted_total = applications
                    .into_iter()
                    .find_map(|application| application.contradicted_total);
                // The step's result: a successor that denotes no state.
                state.depth += 1;
                state.origin = StateOrigin::Successor;
                state.trace.push(TraceEntry {
                    depth: state.depth,
                    kind: TraceKind::Rewrite,
                    label: None,
                    unique_id: "trivial".into(),
                });
                if let Some(outcome) = vacuous_outcome(&state, options, ProofLeafOutcome::Trivial) {
                    record_leaf!(
                        state
                            .leaf(outcome)
                            .with_contradicted_total(contradicted_total)
                    );
                }
            }
            RewriteResult::Vacuous(_) => {
                if let Some(outcome) = vacuous_outcome(&state, options, ProofLeafOutcome::Vacuous) {
                    record_leaf!(state.leaf(outcome));
                }
            }
            RewriteResult::Indeterminate { reason, .. } => {
                record_refined_leaf!(externalise_leaf(
                    definition,
                    state,
                    ProofLeafOutcome::Indeterminate(ProofIndeterminateReason::Rewrite(reason)),
                    options,
                    solver,
                ));
            }
            RewriteResult::Simplification { error, .. } => {
                record_refined_leaf!(externalise_leaf(
                    definition,
                    state,
                    ProofLeafOutcome::Indeterminate(ProofIndeterminateReason::Simplification(
                        error
                    )),
                    options,
                    solver,
                ));
            }
        }
    }

    Ok(finish_explored(leaves, explored_states, 0, forgone_stop))
}

fn extend_frontier(
    pending: &mut VecDeque<ProofState>,
    states: impl IntoIterator<Item = ProofState>,
    breadth_limit: Option<usize>,
) -> bool {
    pending.extend(states);
    breadth_limit.is_some_and(|limit| pending.len() > limit)
}

/// The result of a proof whose frontier exceeded the breadth limit: every pending state is a
/// `BreadthBound` leaf. Their normalisation is a refinement, so a stop it forgoes is polled after
/// it, as the loop does for its own refined leaves.
fn finish_at_breadth_limit(
    definition: &BackendDefinition,
    mut leaves: Vec<ProofLeaf>,
    pending: VecDeque<ProofState>,
    explored_states: u64,
    forgone_stop: Option<StopCause>,
    options: ProofOptions,
    solver: &dyn SmtSolver,
) -> ProofResult {
    let unexplored_states = pending.len() as u64;
    leaves.extend(pending.into_iter().filter_map(|state| {
        externalise_leaf(
            definition,
            state,
            ProofLeafOutcome::BreadthBound,
            options,
            solver,
        )
    }));
    // `unexplored_states > 0`, so a stop named here never comes with a `Proven` status.
    let forgone_stop = forgone_stop.or_else(forgone_refinement_stop);
    finish_explored(leaves, explored_states, unexplored_states, forgone_stop)
}

/// Externalise a proof leaf in the simplifier's normal form (`rewrite::simplify_leaf_pattern`).
///
/// The leaves simplified are the states the proof could not close: `Stuck`, `DepthBound`,
/// `BreadthBound`, and `Indeterminate` for a reason other than a simplification failure. A
/// proven, trusted, trivial, vacuous, or stopped leaf is reported as it stands. A constraint
/// set that simplifies to `\bottom` is an empty state and takes the outcome the loop head gives
/// one ([`vacuous_outcome`]), which is no leaf (`None`) for a split part. When the
/// simplification fails, an `Indeterminate` leaf keeps its pattern and reason; any other leaf
/// reports the failure as a failed loop-head simplification does. A stop keeps the decided
/// outcome with the unsimplified pattern.
fn externalise_leaf(
    definition: &BackendDefinition,
    mut state: ProofState,
    outcome: ProofLeafOutcome,
    options: ProofOptions,
    solver: &dyn SmtSolver,
) -> Option<ProofLeaf> {
    let externalised = match &outcome {
        ProofLeafOutcome::Stuck | ProofLeafOutcome::DepthBound | ProofLeafOutcome::BreadthBound => {
            true
        }
        ProofLeafOutcome::Indeterminate(reason) => {
            !matches!(reason, ProofIndeterminateReason::Simplification(_))
        }
        ProofLeafOutcome::Proven(_)
        | ProofLeafOutcome::Trusted
        | ProofLeafOutcome::Trivial
        | ProofLeafOutcome::Vacuous
        | ProofLeafOutcome::Stopped(_) => false,
    };
    if !externalised {
        return Some(state.leaf(outcome));
    }
    let leaf = match simplify_leaf_pattern(
        definition,
        &state.pattern,
        options.max_simplification_iterations,
        solver,
        state.depth,
        &mut state.trace,
    ) {
        Ok(Ok(simplified)) if predicates_truth(&simplified.pattern.constraints) == Truth::False => {
            state.pattern = simplified.pattern;
            let outcome = vacuous_outcome(&state, options, ProofLeafOutcome::Vacuous)?;
            state.leaf(outcome)
        }
        Ok(Ok(simplified)) => {
            state.pattern = simplified.pattern;
            state.leaf(outcome)
        }
        Ok(Err(_)) if matches!(outcome, ProofLeafOutcome::Indeterminate(_)) => state.leaf(outcome),
        Ok(Err(error)) => state.leaf(ProofLeafOutcome::Indeterminate(
            ProofIndeterminateReason::Simplification(error),
        )),
        Err(stop) => {
            // Kept outcome: the decided one, with the unsimplified pattern, which denotes the
            // same configurations; the normalisation only refines the outcome (into `Vacuous`,
            // or `Proven` under `allow_vacuous`). A stop of the request or of the solver's
            // prelude stays raised: the proof polls it after the refinement
            // (`forgone_refinement_stop`) to name it in `ProofResult::stopped`, and a `Stuck`
            // leaf's certification observes it again at its first solver query. A passed step
            // deadline or an exhausted stack ends this state's step, whose outcome is decided.
            stop.forgo_refinement();
            state.leaf(outcome)
        }
    };
    Some(leaf)
}

/// Whether the rewrite step on a `Stuck` leaf is already known to have no successor.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum StuckEvidence {
    /// The rewrite step on this state returned `RewriteResult::Stuck`.
    StepStuck,
    /// The search stopped the state without rewriting it: a rewrite
    /// remainder on which no rule applied.
    StepNotRun,
}

/// The leaf of a state the search stops as `Stuck`, certified when it refutes the claim.
///
/// A leaf `(t, φ)` stands for the configurations `σ(t)` with `σ ⊨ φ`, where `σ` also fixes the
/// claim's universals. It refutes the claim when one such configuration is reached from the
/// left-hand side on every path the definition allows, never passes through the destination,
/// and has no successor. The leaf is certified only when all of these hold:
///
/// - (a) No successor: the rewrite step on the leaf returns `RewriteResult::Stuck`. A state the
///   search stopped without rewriting it is stepped once here, and certified only if that step
///   is stuck.
/// - (b) The trace follows every path: an all-path claim, or a one-path trace on which no step
///   may have dropped a successor (`ProofState::alternative_discarded`). Every configuration on
///   such a trace has exactly the successors the search kept, so the path to the leaf is the
///   only path from its start, and a one-path claim fails there as an all-path claim would.
///
/// (a) and (d) may instead hold of one instance of the leaf, `empty_computation_instance`: the
/// refutation needs one configuration, and an instance's configurations are the leaf's.
/// - (c) No circularity or trusted claim on the trace (`TraceKind::Claim`): a claim step
///   summarises paths without following them.
/// - (d) The leaf is non-empty outside the destination: its term contains no function
///   application or conjunction of terms, and its constraints, which carry the complement of
///   every destination coverage condition on the trace, together with the definedness of its
///   term are satisfiable by a query whose translation is exact (`smt::translation_exactness`), or
///   are true syntactically, and every free variable has an inhabited sort
///   (`implication::Instance::shown`, shared with the complete implication policy).
///   Those complements say "outside the destination" only if every state on the trace had its
///   implication check run and decided (`ProofState::destination_undecided`): a skipped or
///   undecided check leaves no complement, and the configurations that continued past it may
///   have reached the destination there.
///
/// Every other `Stuck` leaf reports `ProofStatus::Failed`.
///
/// A stop of the certification is returned: a certification decided from a missing answer
/// could certify a refutation that does not hold, so the state's step ends with the stop.
/// A split part that externalisation shows empty is no leaf (`None`, [`vacuous_outcome`]).
fn stuck_leaf(
    definition: &BackendDefinition,
    state: ProofState,
    evidence: StuckEvidence,
    mode: ReachabilityMode,
    fresh_counter: &FreshCounter,
    options: ProofOptions,
    solver: &dyn SmtSolver,
) -> Stoppable<Option<ProofLeaf>> {
    let path_certifiable = state.path_certifiable();
    let Some(mut leaf) =
        externalise_leaf(definition, state, ProofLeafOutcome::Stuck, options, solver)
    else {
        return Ok(None);
    };
    let refutes = |instance: &Pattern, evidence: StuckEvidence| -> Stoppable<bool> {
        Ok(leaf_is_nonempty(definition, instance, solver)?
            && (evidence == StuckEvidence::StepStuck
                || has_no_successor(
                    definition,
                    instance,
                    mode,
                    fresh_counter.clone(),
                    options,
                    solver,
                )?))
    };
    leaf.certified = leaf.outcome == ProofLeafOutcome::Stuck
        && path_certifiable
        && (refutes(&leaf.pattern, evidence)?
            || match empty_computation_instance(definition, &leaf.pattern) {
                Some(instance) => refutes(&instance, StuckEvidence::StepNotRun)?,
                None => false,
            });
    Ok(Some(leaf))
}

/// The instance of `pattern` that binds every variable of sort `K` to the empty computation
/// `.K`, or `None` when `pattern` has no such variable (or the definition no `.K`).
///
/// Conditions (a) and (d) of [`stuck_leaf`] ask for one configuration of the leaf, not all of
/// them. A leaf whose `<k>` cell ends in the frame variable of a claim written with `...` has
/// successors, since the frame may hold more code, yet its configurations with nothing left to
/// run may have none. The instance is a subset of the leaf and is reached along the same trace
/// from the matching instance of the left-hand side, so (a) and (d) established on it certify the
/// leaf. The choice of `.K` is a witness, not an assumption: when the instance still rewrites,
/// is empty, or is not decided exactly, the leaf is not certified by it.
fn empty_computation_instance(
    definition: &BackendDefinition,
    pattern: &Pattern,
) -> Option<Pattern> {
    let computations = pattern
        .term
        .attributes()
        .variables
        .iter()
        .cloned()
        .chain(
            pattern
                .constraints
                .iter()
                .flat_map(crate::rule::Predicate::free_variables),
        )
        .filter(|variable| variable.sort.is_builtin(BuiltinSort::K))
        .collect::<BTreeSet<_>>();
    if computations.is_empty() {
        return None;
    }
    let dotk = definition.symbols().get(WellKnownSymbol::DotK.as_str())?;
    if !dotk.sort_variables.is_empty() || !dotk.argument_sorts.is_empty() {
        return None;
    }
    let empty = Term::application(Arc::clone(dotk), Vec::new(), Vec::new());
    let substitution = computations
        .into_iter()
        .map(|variable| (variable, empty.clone()))
        .collect::<Substitution>();
    #[expect(
        clippy::disallowed_methods,
        reason = "a nullary constructor substituted for variables; a constructor application denotes an element"
    )]
    Some(Pattern {
        term: substitute(&pattern.term, &substitution),
        constraints: substitute_predicates(&pattern.constraints, &substitution),
    })
}

/// Condition (d) of [`stuck_leaf`]; a stop of the solver's query is returned.
fn leaf_is_nonempty(
    definition: &BackendDefinition,
    pattern: &Pattern,
    solver: &dyn SmtSolver,
) -> Stoppable<bool> {
    // An unevaluated function application, an equation-head application that its equations may
    // still rewrite, or a macro or alias application may denote a value that the destination
    // match would have accepted, so the leaf's configurations are known only for a term built
    // from free constructors.
    let mut constructors_only = true;
    pattern.term.visit_symbols(&mut |symbol| {
        constructors_only &= symbol.attributes.head_role() == HeadRole::FreeConstructor;
    });
    Ok(constructors_only && Instance::shown(definition, pattern, &[], solver)?.is_some())
}

/// Condition (a) of [`stuck_leaf`] for a state the search stopped without rewriting it. The
/// step runs on a copy of the fresh-name counter: its successors, if any, are discarded. A stop
/// of the step is returned.
fn has_no_successor(
    definition: &BackendDefinition,
    pattern: &Pattern,
    mode: ReachabilityMode,
    mut fresh_counter: FreshCounter,
    options: ProofOptions,
    solver: &dyn SmtSolver,
) -> Stoppable<bool> {
    let simplification = SimplificationOptions::keep_partial(options.max_simplification_iterations);
    let rewritten = match mode {
        ReachabilityMode::OnePath => rewrite_step_sequential_with_options(
            definition,
            pattern,
            &mut fresh_counter,
            simplification,
            solver,
        ),
        ReachabilityMode::AllPath => rewrite_step_with_options(
            definition,
            pattern,
            &mut fresh_counter,
            simplification,
            solver,
        ),
    }?;
    Ok(matches!(rewritten, RewriteResult::Stuck(_)))
}

fn counterexample_limit_reached(leaves: &[ProofLeaf], options: ProofOptions) -> bool {
    leaves.iter().filter(|leaf| !is_proven(leaf)).count() >= options.max_counterexamples
}

#[derive(Clone)]
struct ProofState {
    pattern: Pattern,
    depth: u64,
    /// How the state was reached, for the report: the steps, claim applications and splits on
    /// its path, and the equations its normalizations applied. It is never read for a verdict;
    /// what the state is (the claim's left-hand side, a successor, or a split part) is `origin`.
    trace: Vec<TraceEntry>,
    /// What the state's configurations are, which decides what its emptiness means
    /// ([`vacuous_outcome`]).
    origin: StateOrigin,
    kind: ProofStateKind,
    /// A one-path step on this trace may have dropped a successor of a configuration it covered:
    /// an overlapping rule of equal priority, a second collection match, or a rule whose
    /// right-hand side stands for several successors (`rewrite_step_sequential_tracking_dropped`).
    alternative_discarded: bool,
    /// Some state on this trace was not shown outside the destination: its implication check
    /// was skipped (below the minimum depth) or undecided. Part of its configurations may then
    /// have satisfied the claim there, before the path went on.
    destination_undecided: bool,
    /// The rule step that produced this state, for the undefined step it is when it turns out
    /// to denote no state ([`proof_undefined_step`]); `None` for a state no rule step produced.
    producer: Option<std::rc::Rc<ProofProducer>>,
}

/// The rule step that produced a proof state: the state it was taken from, the candidate whose
/// successor the state is, the step's other applied candidates, whether it left a remainder,
/// and what its successors have decided about its undefined step, shared among them.
struct ProofProducer {
    parent: ProofState,
    candidate: Sibling,
    siblings: Vec<Sibling>,
    has_remainder: bool,
    undefined: std::rc::Rc<std::cell::RefCell<StepUndefinedness>>,
}

/// What a step's undefined step has come to so far ([`proof_undefined_step`]).
///
/// A decision splits the step's candidates into parts, whose instances it reports where no
/// candidate counted defined takes them, and candidates counted defined, whose instances it
/// excludes. A candidate's normalization within the decision is not its proof state's: the
/// state goes on to a satisfiability check of its whole constraint and to the destination
/// check, either of which can show it denotes no state. A candidate counted defined whose state
/// then denotes no state is no successor either, and its instances were excluded from every
/// earlier decision; it takes its own decision, against the candidates still counted defined.
#[derive(Clone, Debug, Default)]
struct StepUndefinedness {
    /// The candidates still counted defined; `None` until the step's first decision.
    defined: Option<std::collections::BTreeSet<usize>>,
    /// Whether a decision of the step reported an instance.
    reported: bool,
}

impl StepUndefinedness {
    /// A step whose undefined step was decided within it, counting every one of its `count`
    /// successors (numbered from `offset`) defined; `reported` says whether it found instances.
    fn decided(offset: usize, count: usize, reported: bool) -> Self {
        Self {
            defined: Some((offset..offset + count).collect()),
            reported,
        }
    }
}

#[derive(Clone)]
enum ProofStateKind {
    Rewritable,
    Remaining(Option<UndecidedStep>),
}

/// What a proof state's configurations are, relative to the claim's left-hand side.
///
/// A state's emptiness means something different for each ([`vacuous_outcome`]), so the
/// provenance is recorded where the state is built, and never inferred from its depth or trace:
/// normalizing a state appends the equations it applied to the trace without changing the
/// configurations the state denotes, and a split appends a remainder entry without being a step.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum StateOrigin {
    /// The claim's left-hand side, before or after normalization: exactly the configurations the
    /// claim is about.
    Initial,
    /// A successor of a step: a rule step's result, a claim application's right-hand side, or a
    /// group of a step's undefined step.
    Successor,
    /// A part of a state that one of the prover's case splits set aside: the part a destination
    /// did not cover, the part a claim did not apply to, or the part no rule of a step took.
    /// Its configurations are those of the state it was split from that the other side of the
    /// split did not take.
    Split,
}

impl ProofState {
    /// The proof state of the claim's left-hand side `pattern`.
    fn initial(pattern: Pattern) -> Self {
        Self {
            pattern,
            depth: 0,
            trace: Vec::new(),
            origin: StateOrigin::Initial,
            kind: ProofStateKind::Rewritable,
            alternative_discarded: false,
            destination_undecided: false,
            producer: None,
        }
    }

    fn leaf(self, outcome: ProofLeafOutcome) -> ProofLeaf {
        ProofLeaf {
            pattern: self.pattern,
            depth: self.depth,
            trace: self.trace,
            outcome,
            certified: false,
            contradicted_total: None,
        }
    }

    /// Conditions (b), (c) and the trace part of (d) of [`stuck_leaf`], which depend only on
    /// how the search reached this state.
    fn path_certifiable(&self) -> bool {
        !self.alternative_discarded
            && !self.destination_undecided
            && !self
                .trace
                .iter()
                .any(|entry| entry.kind == TraceKind::Claim)
    }

    fn rewritten(mut self, applied: crate::rewrite::AppliedRule) -> Self {
        self.producer = None;
        self.origin = StateOrigin::Successor;
        for simplification in &applied.remainder_simplifications {
            self.trace.extend(
                simplification
                    .applied_rules
                    .iter()
                    .cloned()
                    .map(|unique_id| TraceEntry {
                        depth: self.depth,
                        kind: TraceKind::Simplification,
                        label: None,
                        unique_id,
                    }),
            );
        }
        self.depth += 1;
        self.trace.push(TraceEntry {
            depth: self.depth,
            kind: TraceKind::Rewrite,
            label: applied.label,
            unique_id: applied.unique_id,
        });
        self.pattern = applied.pattern;
        self.kind = ProofStateKind::Rewritable;
        self
    }

    fn claimed(mut self, pattern: Pattern, label: Option<String>, unique_id: String) -> Self {
        self.producer = None;
        self.origin = StateOrigin::Successor;
        self.depth += 1;
        self.trace.push(TraceEntry {
            depth: self.depth,
            kind: TraceKind::Claim,
            label,
            unique_id,
        });
        self.pattern = pattern;
        self.kind = ProofStateKind::Rewritable;
        self
    }

    /// The part `remainder` of this state that a split set aside. It is a `Split` whatever this
    /// state is: its configurations are this state's that the other side of the split did not
    /// take, so its emptiness says that side took every one of them.
    fn remaining(mut self, remainder: crate::rewrite::RemainderBranch) -> Self {
        self.producer = None;
        self.origin = StateOrigin::Split;
        self.trace.push(TraceEntry {
            depth: self.depth,
            kind: TraceKind::Remainder,
            label: None,
            unique_id: remainder.rule_ids.join(","),
        });
        for simplification in &remainder.simplifications {
            self.trace.extend(
                simplification
                    .applied_rules
                    .iter()
                    .cloned()
                    .map(|unique_id| TraceEntry {
                        depth: self.depth,
                        kind: TraceKind::Simplification,
                        label: None,
                        unique_id,
                    }),
            );
        }
        self.pattern = remainder.pattern;
        self
    }

    fn rewrite_remaining(mut self, remainder: crate::rewrite::RemainderBranch) -> Self {
        self.kind = ProofStateKind::Remaining(remainder.indeterminate.clone());
        self.remaining(remainder)
    }

    /// The successors of the step `self` took, one per applied candidate, each knowing the
    /// others for its undefined step; `offset` is the number of the step's trivial entries,
    /// which come first among its candidates, and `undefined` what the step already decided
    /// about its undefined step.
    fn successors(
        &self,
        branches: Vec<crate::rewrite::AppliedRule>,
        has_remainder: bool,
        offset: usize,
        undefined: StepUndefinedness,
    ) -> Vec<ProofState> {
        let parent = ProofState {
            producer: None,
            ..self.clone()
        };
        let candidates = branches
            .iter()
            .enumerate()
            .map(|(index, applied)| Sibling::of(offset + index, applied))
            .collect::<Vec<_>>();
        let undefined = std::rc::Rc::new(std::cell::RefCell::new(undefined));
        branches
            .into_iter()
            .zip(&candidates)
            .map(|(applied, candidate)| {
                let siblings = candidates
                    .iter()
                    .filter(|sibling| sibling.index != candidate.index)
                    .cloned()
                    .collect();
                let mut successor = parent.clone().rewritten(applied);
                successor.producer = Some(std::rc::Rc::new(ProofProducer {
                    parent: parent.clone(),
                    candidate: candidate.clone(),
                    siblings,
                    has_remainder,
                    undefined: undefined.clone(),
                }));
                successor
            })
            .collect()
    }

    /// The proof state of one group of a step's undefined step taken from `self`: the
    /// configuration under the group's conditions, one rewrite step below, on the path through
    /// the remainder simplifications its first part went through, naming that part's rule.
    fn undefined_group(
        &self,
        group: UndefinedGroup,
    ) -> (ProofState, Option<Box<ContradictedTotal>>) {
        let mut undefined = ProofState {
            producer: None,
            origin: StateOrigin::Successor,
            ..self.clone()
        };
        for simplification in &group.remainder_simplifications {
            undefined.trace.extend(
                simplification
                    .applied_rules
                    .iter()
                    .cloned()
                    .map(|unique_id| TraceEntry {
                        depth: self.depth,
                        kind: TraceKind::Simplification,
                        label: None,
                        unique_id,
                    }),
            );
        }
        let (rule_id, label, contradicted_total) = match group.halt {
            HaltReason::Trivial {
                rule_id,
                label,
                contradicted_total,
                ..
            } => (rule_id, label, contradicted_total),
            HaltReason::Stopped(_)
            | HaltReason::Stuck
            | HaltReason::Vacuous { .. }
            | HaltReason::Branch { .. }
            | HaltReason::CutPointRule { .. }
            | HaltReason::TerminalRule { .. }
            | HaltReason::DepthBound
            | HaltReason::BreadthBound
            | HaltReason::WorkBound
            | HaltReason::Indeterminate(_)
            | HaltReason::Simplification(_) => (None, None, None),
        };
        undefined.pattern = group.pattern;
        undefined.depth += 1;
        undefined.trace.push(TraceEntry {
            depth: undefined.depth,
            kind: TraceKind::Rewrite,
            label,
            unique_id: rule_id.unwrap_or_else(|| "trivial".into()),
        });
        (undefined, contradicted_total)
    }
}

enum ClaimApplication {
    NotApplicable,
    /// The claim's right-hand sides on the covered sub-case, plus the uncovered sub-case when
    /// the claim matched only under a condition on the subject.
    Applied {
        patterns: Vec<Pattern>,
        remainder: Option<RemainderBranch>,
    },
    Indeterminate(ClaimIndeterminateReason),
}

fn apply_claim(
    definition: &BackendDefinition,
    claim: &ReachabilityClaim,
    subject: &Pattern,
    options: ProofOptions,
    solver: &dyn SmtSolver,
    fresh_counter: &mut FreshCounter,
) -> Stoppable<ClaimApplication> {
    let claim = freshen_claim(claim, subject, fresh_counter);
    let claim_variables = variables_of_claim(&claim);
    let matched = match_terms_in_definition(
        MatchMode::Rewrite,
        definition,
        &claim.lhs.term,
        &subject.term,
    );
    // A match the matcher could not decide leaves the claim's applicability open: some instance
    // of the claim may apply, so it is not read as not applicable.
    let undecided = || -> Stoppable<ClaimApplication> {
        Ok(ClaimApplication::Indeterminate(
            ClaimIndeterminateReason::Match {
                substitution: Substitution::new(),
                remainder: vec![(claim.lhs.term.clone(), subject.term.clone())],
            },
        ))
    };
    let matched = match matched {
        MatchResult::Success(substitution) => MatchSolution::new(substitution),
        MatchResult::Failed(_) => return Ok(ClaimApplication::NotApplicable),
        MatchResult::Undecided(_) => return undecided(),
        MatchResult::Indeterminate {
            substitution,
            remainder,
        } => {
            let recovered = match recover_indeterminate_match(
                definition,
                substitution,
                remainder,
                &subject.constraints,
                SimplificationOptions {
                    max_iterations: options.max_simplification_iterations,
                    ..SimplificationOptions::default()
                },
                solver,
            )? {
                Ok(recovered) => recovered,
                Err(error) => {
                    return Ok(ClaimApplication::Indeterminate(
                        ClaimIndeterminateReason::Simplification(error),
                    ));
                }
            };
            match recovered {
                RecoveredMatch::Failed(_) => return Ok(ClaimApplication::NotApplicable),
                RecoveredMatch::Undecided(_) => return undecided(),
                RecoveredMatch::Matched {
                    solution,
                    remainder,
                } if remainder.is_empty() => solution,
                RecoveredMatch::Matched {
                    solution,
                    remainder,
                } => {
                    // A symbolic subject can still be covered by the claim on the sub-case
                    // where the unresolved pairs unify. Those equalities become the match
                    // condition; their complement is the remainder the claim leaves behind.
                    match unify_from(definition, solution, remainder) {
                        MatchUnification::Unified(matched) => matched,
                        MatchUnification::Bottom(_) => return Ok(ClaimApplication::NotApplicable),
                        MatchUnification::Unsupported {
                            solution,
                            remainder,
                        } => {
                            // Collection pairs are beyond the syntactic unifier; solve them as
                            // rule application does (rewrite.rs recover_general_unification),
                            // accepting a unique solution.
                            let solutions = solve_collection_pairs_in_definition(
                                MatchMode::Rewrite,
                                definition,
                                solution.substitution().clone(),
                                &remainder,
                                None,
                            );
                            match solutions.as_deref() {
                                Some([]) => return Ok(ClaimApplication::NotApplicable),
                                Some([collection]) => {
                                    let mut matched = MatchSolution::from_parts(
                                        collection.matched.substitution().clone(),
                                        solution.into_parts().1,
                                    );
                                    matched
                                        .conjoin(collection.matched.conditions().iter().cloned());
                                    match collection_unification_definedness(
                                        definition,
                                        &remainder,
                                        matched.substitution(),
                                    ) {
                                        Ok(definedness) => matched.conjoin(definedness),
                                        Err(outcome) => {
                                            return Ok(ClaimApplication::Indeterminate(
                                                ClaimIndeterminateReason::Simplification(
                                                    outcome.into(),
                                                ),
                                            ));
                                        }
                                    }
                                    matched
                                }
                                _ => {
                                    return Ok(ClaimApplication::Indeterminate(
                                        ClaimIndeterminateReason::Match {
                                            substitution: solution.substitution().clone(),
                                            remainder,
                                        },
                                    ));
                                }
                            }
                        }
                    }
                }
            }
        }
    };
    let (mut substitution, match_conditions) =
        match bind_subject_variables(definition, &claim, matched) {
            Ok(matched) => matched.into_parts(),
            Err(outcome) => {
                return Ok(ClaimApplication::Indeterminate(
                    ClaimIndeterminateReason::Simplification(outcome.into()),
                ));
            }
        };
    let simplification = SimplificationOptions {
        max_iterations: options.max_simplification_iterations,
        ..SimplificationOptions::default()
    };
    // Every instance of the subject satisfies its constraints with their definedness stated and
    // the definedness of its term (I7): the claim's condition is stated and decided under these
    // facts, so a `⌈t⌉` the subject already implies is neither restated nor left open.
    let subject_knowledge = pattern_knowledge(definition, subject);
    let mut match_conditions = match simplify_predicates_with_solver(
        definition,
        &match_conditions,
        &subject_knowledge,
        simplification,
        solver,
    )? {
        Ok(conditions) => conditions,
        Err(error) => {
            return Ok(ClaimApplication::Indeterminate(
                ClaimIndeterminateReason::Simplification(error),
            ));
        }
    };
    if predicates_truth(&match_conditions) == Truth::False {
        return Ok(ClaimApplication::NotApplicable);
    }

    // The instantiated `requires` is `⊥` wherever one of its atoms is over an undefined term, so
    // the claim does not apply there (I1): state that definedness before the condition is
    // simplified or decided, since a solver reads a partial function as a total operation.
    let mut match_knowledge = subject_knowledge.to_vec();
    extend_unique(&mut match_knowledge, match_conditions.clone());
    let requires = match instantiate_constraints(&claim.lhs.constraints, &substitution)
        .with_definedness(definition, &match_knowledge)
    {
        Ok(requires) => requires,
        Err(outcome) => {
            return Ok(ClaimApplication::Indeterminate(
                ClaimIndeterminateReason::Simplification(outcome.into()),
            ));
        }
    };
    let requires = match simplify_predicates_with_solver(
        definition,
        &requires,
        &match_knowledge,
        simplification,
        solver,
    )? {
        Ok(requires) => requires,
        Err(error) => {
            return Ok(ClaimApplication::Indeterminate(
                ClaimIndeterminateReason::Simplification(error),
            ));
        }
    };
    if predicates_truth(&requires) == Truth::False {
        return Ok(ClaimApplication::NotApplicable);
    }

    let unbound = claim_variables
        .into_iter()
        .filter(|variable| !substitution.contains_key(variable))
        .collect::<BTreeSet<_>>();
    let (defined, requires) =
        extract_substitution_for(&requires, &unbound, definition.sort_graph());
    substitution = compose(&defined, &substitution);
    // A claim variable bound by an equation of the requires denotes a defined element, so its
    // value's definedness stays among the conditions the claim applies under (I2).
    match_conditions =
        match eliminate_bindings(definition, &match_conditions, &defined, &subject_knowledge) {
            Ok(conditions) => conditions,
            Err(outcome) => {
                return Ok(ClaimApplication::Indeterminate(
                    ClaimIndeterminateReason::Simplification(outcome.into()),
                ));
            }
        };
    match_conditions = match simplify_predicates_with_solver(
        definition,
        &match_conditions,
        &subject_knowledge,
        simplification,
        solver,
    )? {
        Ok(conditions) => conditions,
        Err(error) => {
            return Ok(ClaimApplication::Indeterminate(
                ClaimIndeterminateReason::Simplification(error),
            ));
        }
    };
    if predicates_truth(&match_conditions) == Truth::False {
        return Ok(ClaimApplication::NotApplicable);
    }
    let mut match_knowledge = subject_knowledge.to_vec();
    extend_unique(&mut match_knowledge, match_conditions.clone());
    let requires = match eliminate_bindings(definition, &requires, &defined, &match_knowledge) {
        Ok(requires) => requires,
        Err(outcome) => {
            return Ok(ClaimApplication::Indeterminate(
                ClaimIndeterminateReason::Simplification(outcome.into()),
            ));
        }
    };
    let requires = match simplify_predicates_with_solver(
        definition,
        &requires,
        &match_knowledge,
        simplification,
        solver,
    )? {
        Ok(requires) => requires,
        Err(error) => {
            return Ok(ClaimApplication::Indeterminate(
                ClaimIndeterminateReason::Simplification(error),
            ));
        }
    };
    if predicates_truth(&requires) == Truth::False {
        return Ok(ClaimApplication::NotApplicable);
    }

    // Conditions the path already satisfies do not narrow it. Every other match or requires
    // predicate describes the covered sub-case; their joint complement is the claim remainder.
    let mut conditions = match_conditions;
    extend_unique(&mut conditions, requires);
    conditions.retain(|condition| {
        predicates_truth(std::slice::from_ref(condition)) == Truth::Unknown
            && !subject.constraints.contains(condition)
            && !subject_knowledge.contains(condition)
    });
    if !conditions.is_empty() {
        // A stop leaves the claim's coverage without an answer, so the application has none.
        match solver.check_predicates(&subject_knowledge, &Substitution::new(), &conditions)? {
            Ok(validity) => match validity {
                Validity::Valid => conditions.clear(),
                Validity::Refuted | Validity::InconsistentGroundTruth => {
                    return Ok(ClaimApplication::NotApplicable);
                }
                // The claim covers the part where its conditions hold; the complement below is
                // the remainder. The split is sound for any answer.
                Validity::Contingent => {}
                Validity::Unknown(reason) => {
                    return Ok(ClaimApplication::Indeterminate(
                        ClaimIndeterminateReason::Smt(SmtError::Unknown(reason)),
                    ));
                }
            },
            // Without a solver the conditions stay undecided and the same split applies.
            Err(SmtError::Unavailable) => {}
            Err(error) => {
                return Ok(ClaimApplication::Indeterminate(
                    ClaimIndeterminateReason::Smt(error),
                ));
            }
        }
    }

    let complement = if conditions.is_empty() {
        None
    } else {
        let condition = quantify_introduced_variables(subject, conditions.clone());
        let negated =
            crate::simplify::normalize_predicate(crate::rule::Predicate::Not(Arc::new(condition)));
        if conjunctively_contains_alpha_equivalent(&subject.constraints, &negated) {
            // This subject is the remainder of an earlier application of the same claim.
            return Ok(ClaimApplication::NotApplicable);
        }
        Some(negated)
    };
    // The remainder denotes the subject's states the claim does not apply to: the subject under
    // the negated application condition. When that condition is unsatisfiable under the
    // subject's knowledge, the remainder denotes no state: the claim covers the whole subject,
    // and the remainder is dropped instead of becoming a bottom successor for the vacuity check
    // to reject.
    let complement = match complement {
        Some(negated) => {
            let unsatisfiable = remainder_is_unsatisfiable(
                definition,
                &subject_knowledge,
                &negated,
                simplification,
                solver,
            )?;
            (!unsatisfiable).then_some(negated)
        }
        None => None,
    };
    let mut covered_knowledge = subject.constraints.clone();
    extend_unique(&mut covered_knowledge, conditions);

    let remainder = complement.map(|complement| {
        let mut constraints = subject.constraints.clone();
        extend_unique(&mut constraints, vec![complement]);
        RemainderBranch {
            pattern: Pattern {
                term: subject.term.clone(),
                constraints,
            },
            rule_ids: vec![format!("claim:{}", claim.attributes.unique_id)],
            effects: Vec::new(),
            simplifications: Vec::new(),
            indeterminate: None,
            diagnostics: Vec::new(),
            observations: Vec::new(),
        }
    });
    let mut patterns = Vec::with_capacity(claim.rhs.len());
    for rhs in &claim.rhs {
        let mut constraints = covered_knowledge.clone();
        // An equivalence (I1): the successor states the definedness its constraints imply, so
        // later decisions on it do not read a partial term as total.
        let rhs_constraints = match instantiate_constraints(&rhs.constraints, &substitution)
            .with_definedness(definition, &constraints)
        {
            Ok(rhs_constraints) => rhs_constraints,
            Err(outcome) => {
                return Ok(ClaimApplication::Indeterminate(
                    ClaimIndeterminateReason::Simplification(outcome.into()),
                ));
            }
        };
        extend_unique(&mut constraints, rhs_constraints);
        patterns.push(Pattern {
            term: substitute(&rhs.term, &substitution),
            constraints,
        });
    }
    Ok(ClaimApplication::Applied {
        patterns,
        remainder,
    })
}

/// Whether a split part, the subject under `negated` (the negated, quantified condition of the
/// other side of the split: a claim's match condition, or a destination's coverage condition),
/// is shown empty. It is when that condition simplifies to false or the solver refutes it
/// together with `subject_knowledge`, the subject's `pattern_knowledge`; an undecided or
/// unavailable solver, or a failed simplification, keeps it. A stop (a cancelled request, a
/// passed step deadline, a failed solver prelude or an exhausted stack) is returned instead:
/// keeping the remainder would turn a missing answer into a state the split does not cover.
fn remainder_is_unsatisfiable(
    definition: &BackendDefinition,
    subject_knowledge: &[crate::rule::Predicate],
    negated: &crate::rule::Predicate,
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Stoppable<bool> {
    // The stop is returned before the fallback sees the result, which it matches on the
    // failure layer only.
    let simplified = match simplify_predicates_with_solver(
        definition,
        std::slice::from_ref(negated),
        subject_knowledge,
        options,
        solver,
    )? {
        Ok(simplified) => simplified,
        Err(_) => return Ok(false),
    };
    if predicates_truth(&simplified) == Truth::False {
        return Ok(true);
    }
    let mut constraints = subject_knowledge.to_vec();
    extend_unique(&mut constraints, simplified);
    Ok(matches!(
        solver.is_sat(&constraints, &Substitution::new())?,
        Ok(Satisfiability::Unsat)
    ))
}

/// Unification may bind variables of the subject rather than of the claim. Such bindings are
/// conditions on the subject, not part of the claim's instantiation: keep them as equalities
/// (with the definedness of the bound value) and drop them from the substitution, as rule
/// application does for configuration variables.
/// The conditions leave under the remaining substitution of claim variables ([`MatchSolution`]):
/// they were gathered while the unifier and the collection solver still bound claim variables,
/// and the claim's right-hand side and requires are instantiated by that substitution, which
/// uses its bindings up.
fn bind_subject_variables(
    definition: &BackendDefinition,
    claim: &ReachabilityClaim,
    matched: MatchSolution,
) -> Result<MatchSolution, crate::deferred::DeferredOutcome> {
    let (mut substitution, mut conditions) = matched.into_parts();
    let claim_variables = variables_of_claim(claim);
    let bound = substitution
        .iter()
        .filter(|(variable, _)| !claim_variables.contains(*variable))
        .map(|(variable, value)| (variable.clone(), value.clone()))
        .collect::<Vec<_>>();
    for (variable, value) in bound {
        substitution.remove(&variable);
        extend_unique(
            &mut conditions,
            vec![crate::rule::Predicate::Equals(
                Term::variable(variable),
                value.clone(),
            )],
        );
        if !matches!(value.kind(), TermKind::Variable(_)) {
            extend_unique(&mut conditions, ceil_term(definition, &value)?);
        }
    }
    Ok(MatchSolution::from_parts(substitution, conditions))
}

fn variables_of_claim(claim: &ReachabilityClaim) -> BTreeSet<crate::term::Variable> {
    claim
        .lhs
        .term
        .attributes()
        .variables
        .iter()
        .cloned()
        .chain(
            claim
                .lhs
                .constraints
                .iter()
                .flat_map(crate::rule::Predicate::free_variables),
        )
        .chain(claim.rhs.iter().flat_map(|rhs| {
            rhs.term.attributes().variables.iter().cloned().chain(
                rhs.constraints
                    .iter()
                    .flat_map(crate::rule::Predicate::free_variables),
            )
        }))
        .chain(claim.existentials.iter().cloned())
        .collect()
}

/// ```toml algorithm-site
/// id = "backend.fresh.variables"
/// role = "part"
/// sites = ["freshen_claim"]
/// ```
fn freshen_claim(
    claim: &ReachabilityClaim,
    subject: &Pattern,
    fresh_counter: &mut FreshCounter,
) -> ReachabilityClaim {
    let mut names = subject
        .term
        .attributes()
        .variables
        .iter()
        .map(|variable| variable.name.clone())
        .collect::<BTreeSet<_>>();
    for predicate in &subject.constraints {
        names.extend(
            predicate
                .free_variables()
                .into_iter()
                .map(|variable| variable.name),
        );
    }
    let variables = variables_of_claim(claim);
    let mut renaming = Substitution::new();
    for variable in variables {
        let name = fresh_counter.mint(&variable.name, FreshMarker::Claim, &mut names);
        renaming.insert(variable.clone(), Term::variable(variable.with_name(name)));
    }
    #[expect(
        clippy::disallowed_methods,
        reason = "a renaming to fresh variables; a variable denotes an element"
    )]
    let rename_pattern = |pattern: &Pattern| Pattern {
        term: substitute(&pattern.term, &renaming),
        constraints: substitute_predicates(&pattern.constraints, &renaming),
    };
    ReachabilityClaim {
        lhs: rename_pattern(&claim.lhs),
        rhs: claim.rhs.iter().map(rename_pattern).collect(),
        existentials: claim
            .existentials
            .iter()
            .map(|variable| {
                let renamed = renaming
                    .get(variable)
                    .expect("every claim variable is refreshed");
                let crate::term::TermKind::Variable(variable) = renamed.kind() else {
                    unreachable!("claim variables are renamed to variables")
                };
                variable.clone()
            })
            .collect(),
        mode: claim.mode,
        attributes: claim.attributes.clone(),
        unstated: claim.unstated.clone(),
    }
}

fn finish(leaves: Vec<ProofLeaf>, explored_states: u64, unexplored_states: u64) -> ProofResult {
    let any_certified = leaves
        .iter()
        .any(|leaf| leaf.certified && leaf.outcome == ProofLeafOutcome::Stuck);
    let any_failed = leaves.iter().any(|leaf| {
        matches!(
            leaf.outcome,
            ProofLeafOutcome::Stuck | ProofLeafOutcome::Trivial | ProofLeafOutcome::Vacuous
        )
    });
    let any_indeterminate = leaves.iter().any(|leaf| {
        matches!(
            leaf.outcome,
            ProofLeafOutcome::Stopped(_) | ProofLeafOutcome::Indeterminate(_)
        )
    });
    let any_depth_bound = leaves
        .iter()
        .any(|leaf| matches!(leaf.outcome, ProofLeafOutcome::DepthBound));
    let any_breadth_bound = leaves
        .iter()
        .any(|leaf| matches!(leaf.outcome, ProofLeafOutcome::BreadthBound));
    let status = if any_certified {
        ProofStatus::Disproved
    } else if any_failed {
        ProofStatus::Failed
    } else if any_indeterminate {
        ProofStatus::Indeterminate
    } else if any_depth_bound {
        ProofStatus::DepthBound
    } else if any_breadth_bound {
        ProofStatus::BreadthBound
    } else if unexplored_states > 0 {
        ProofStatus::Indeterminate
    } else if leaves.iter().all(is_proven) {
        ProofStatus::Proven
    } else {
        ProofStatus::Indeterminate
    };
    ProofResult {
        status,
        leaves,
        explored_states,
        unexplored_states,
        stopped: None,
    }
}

/// [`finish`] for an exploration that ended early because it stopped with `cause`.
fn finish_stopped(
    leaves: Vec<ProofLeaf>,
    explored_states: u64,
    unexplored_states: u64,
    cause: StopCause,
) -> ProofResult {
    ProofResult {
        stopped: Some(cause),
        ..finish(leaves, explored_states, unexplored_states)
    }
}

/// [`finish`] for an exploration that ended without a stop of its own: every state was explored
/// or a bound was reached. `forgone_stop` is a stop observed while a decided leaf was refined.
fn finish_explored(
    leaves: Vec<ProofLeaf>,
    explored_states: u64,
    unexplored_states: u64,
    forgone_stop: Option<StopCause>,
) -> ProofResult {
    match forgone_stop {
        Some(cause) => finish_stopped(leaves, explored_states, unexplored_states, cause),
        None => finish(leaves, explored_states, unexplored_states),
    }
}

/// Poll, after a decided leaf was refined (normalised by [`externalise_leaf`], certified by
/// [`stuck_leaf`]), for a stop that refinement may have forgone. The normalisation keeps the
/// leaf's outcome when it stops. A cancelled request or a failed solver prelude keeps its signal
/// raised, so this poll mints its stop again, and the proof names it in [`ProofResult::stopped`]
/// at whichever exit comes next; a stop arriving after the refinement is also observed, which
/// only names a stop the result may not depend on. A passed step deadline ends only the step of
/// the state just recorded, whose outcome is decided, so it is dismissed.
#[deny(clippy::wildcard_enum_match_arm)]
fn forgone_refinement_stop() -> Option<StopCause> {
    let stop = stop::check().err()?;
    match stop.cause() {
        StopCause::Cancelled | StopCause::SolverPrelude(_) => Some(stop.into_cause()),
        StopCause::Deadline(_) | StopCause::StackExhausted(_) => {
            stop.forgo_refinement();
            None
        }
    }
}

/// What the proof does with a state whose step stopped.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ProofStop {
    /// The state is a `Stopped` leaf, and the proof goes on with the other states.
    Leaf,
    /// The state is a `Stopped` leaf, and the proof ends.
    LeafAndFinish,
    /// The proof ends, and the state stays unexplored.
    Finish,
}

/// Publish a stop of the state's step. The step produced no answer, so its duration measures no
/// step and is not recorded. A passed step deadline ends the proof after recording the state,
/// whose step ran out of its time; an exhausted stack stops the state being stepped only, and the
/// rest of the proof can still be decided; a cancelled request or a failed solver prelude ends
/// every remaining state, so the proof ends with the state unexplored.
#[deny(clippy::wildcard_enum_match_arm)]
fn proof_stop(cause: &StopCause, step_timer: &mut StepTimer<'_>) -> ProofStop {
    step_timer.discard_measurement();
    match cause {
        StopCause::Deadline(_) => ProofStop::LeafAndFinish,
        StopCause::StackExhausted(_) => ProofStop::Leaf,
        StopCause::Cancelled | StopCause::SolverPrelude(_) => ProofStop::Finish,
    }
}

fn is_proven(leaf: &ProofLeaf) -> bool {
    matches!(
        leaf.outcome,
        ProofLeafOutcome::Proven(_) | ProofLeafOutcome::Trusted
    )
}

/// What a proof state that denotes no state comes to ([`proof_undefined_step`]).
enum ProofUndefined {
    /// The undefined step of the step that produced it: its `Trivial` states.
    Leaves(Vec<(ProofState, Option<Box<ContradictedTotal>>)>),
    /// No instance is left undefined: another candidate or the remainder takes every instance,
    /// or an earlier decision of the step already reported its instances.
    Covered,
    /// The configuration the step was taken from has no instance, or no rule step produced the
    /// state: it is `Vacuous`.
    NoInstance,
}

/// `state`, which its normalization showed to denote no state: when a rule step produced it, it
/// is no successor of that step, an all-path claim has no path through it, and its instances
/// are the step's undefined step where no other candidate takes them, decided as an execution
/// decides it ([`decide_undefined_step`]).
///
/// The first successor of a step to find this decides for the step, after normalizing the
/// step's other candidates: those shown undefined are parts with it, the others are counted
/// defined ([`StepUndefinedness`]). A later successor that was a part is covered: its instances
/// are in that decision. A later successor that was counted defined had its instances excluded
/// from every decision so far, so it takes its own decision, excluded by the candidates still
/// counted defined; the instances it reports are disjoint from every earlier decision's, and an
/// instance on which every candidate that applies denotes no state is reported by the decision
/// of the last of them to be found so.
fn proof_undefined_step(
    definition: &BackendDefinition,
    state: &ProofState,
    contradicted_total: Option<Box<ContradictedTotal>>,
    options: ProofOptions,
    solver: &dyn SmtSolver,
) -> Stoppable<ProofUndefined> {
    let Some(producer) = &state.producer else {
        return Ok(ProofUndefined::NoInstance);
    };
    let candidate = &producer.candidate;
    let earlier = producer.undefined.borrow().clone();
    if let Some(defined) = &earlier.defined
        && !defined.contains(&candidate.index)
    {
        return Ok(ProofUndefined::Covered);
    }
    let depth = producer.parent.depth + 1;
    let halt = HaltReason::Trivial {
        depth,
        rule_id: None,
        label: None,
        obligation: crate::rule::Predicate::False,
        contradicted_total,
    };
    let mut parts = vec![candidate.part(halt)];
    let mut diagnostics = crate::diagnostic::PathDiagnostics::new_request();
    let defined = match &earlier.defined {
        Some(defined) => producer
            .siblings
            .iter()
            .filter(|sibling| defined.contains(&sibling.index))
            .collect::<Vec<_>>(),
        None => {
            let mut defined = Vec::with_capacity(producer.siblings.len());
            sibling_undefined_parts(
                definition,
                options.max_simplification_iterations,
                solver,
                None,
                &producer.siblings,
                depth,
                &mut parts,
                &mut defined,
                &mut diagnostics,
            )?;
            defined
        }
    };
    // An earlier decision's instances are accounted for, so this one finding none is no sign
    // that the configuration has no instance.
    let others = producer.has_remainder || !defined.is_empty() || earlier.reported;
    let decision = decide_undefined_step(
        definition,
        options.max_simplification_iterations,
        solver,
        parts,
        &defined
            .iter()
            .map(|sibling| sibling.built())
            .collect::<Vec<_>>(),
        others,
        &mut diagnostics,
    )?;
    *producer.undefined.borrow_mut() = StepUndefinedness {
        defined: Some(defined.iter().map(|sibling| sibling.index).collect()),
        reported: earlier.reported || matches!(decision, UndefinedDecision::Groups(..)),
    };
    Ok(match decision {
        UndefinedDecision::Groups(groups, _) => ProofUndefined::Leaves(
            groups
                .into_iter()
                .map(|group| producer.parent.undefined_group(group))
                .collect(),
        ),
        UndefinedDecision::Covered => ProofUndefined::Covered,
        UndefinedDecision::NoInstance => ProofUndefined::NoInstance,
    })
}

/// Whether the state's constraints are shown unsatisfiable. A stop of the solver's query is
/// returned, never read as "not bottom", which would keep the state from a missing answer.
fn state_is_bottom(state: &ProofState, solver: &dyn SmtSolver) -> Stoppable<bool> {
    Ok(predicates_truth(&state.pattern.constraints) == Truth::False
        || matches!(
            solver.is_sat(&state.pattern.constraints, &Substitution::new())?,
            Ok(Satisfiability::Unsat)
        ))
}

/// The leaf of a state shown to denote no configuration, decided by what the state is
/// (`ProofState::origin`) and never by its depth or trace; `None` when the state is no leaf.
///
/// - The claim's left-hand side (`Initial`, before or after its normalization, which applies
///   equalities and states definedness the left-hand side already implies): the claim is about no
///   configuration, so it holds vacuously and the leaf is proven.
/// - A successor (`Successor`): it has no instance because the path's own conditions contradict
///   each other or its step is undefined; that is reported as `cause` rather than counted as a
///   proof, unless the caller allows vacuous proofs.
/// - A split part (`Split`): the parts of a split partition the state split, so an empty part
///   means the other side took every configuration. No path ends here and there is nothing for
///   the vacuity policy to reject, whatever `allow_vacuous` says: the part is no leaf.
#[deny(clippy::wildcard_enum_match_arm)]
fn vacuous_outcome(
    state: &ProofState,
    options: ProofOptions,
    cause: ProofLeafOutcome,
) -> Option<ProofLeafOutcome> {
    let proven = || {
        ProofLeafOutcome::Proven(ImplicationCondition {
            predicates: vec![crate::rule::Predicate::False],
            substitution: Substitution::new(),
            witnesses: Substitution::new(),
        })
    };
    match state.origin {
        StateOrigin::Initial => Some(proven()),
        StateOrigin::Successor if options.allow_vacuous => Some(proven()),
        StateOrigin::Successor => Some(cause),
        StateOrigin::Split => None,
    }
}

fn extend_unique(left: &mut Vec<crate::rule::Predicate>, right: Vec<crate::rule::Predicate>) {
    for predicate in right {
        if !left.contains(&predicate) {
            left.push(predicate);
        }
    }
}

/// The part of `pattern` a destination does not cover: `pattern` under the complement of the
/// coverage condition (`complement_implication_condition`), recorded as a remainder of the
/// destination's check. `None` when that part is shown empty ([`remainder_is_unsatisfiable`]
/// under the pattern's knowledge): the destination then covers every configuration of
/// `pattern`. The check comes before the part is stepped, since an empty part that is stepped
/// would yield successors that denote no state, which the vacuity policy rejects as paths whose
/// own conditions contradict each other. A stop of the check is returned.
fn uncovered_remainder(
    definition: &BackendDefinition,
    pattern: &Pattern,
    claim: &ReachabilityClaim,
    universals: &BTreeSet<crate::term::Variable>,
    coverage: &CoverageCondition,
    options: ProofOptions,
    solver: &dyn SmtSolver,
) -> Stoppable<Option<RemainderBranch>> {
    let complement = complement_implication_condition(pattern, universals, coverage);
    let knowledge = pattern_knowledge(definition, pattern);
    if remainder_is_unsatisfiable(
        definition,
        &knowledge,
        &complement,
        SimplificationOptions {
            max_iterations: options.max_simplification_iterations,
            ..SimplificationOptions::default()
        },
        solver,
    )? {
        return Ok(None);
    }
    let mut constraints = pattern.constraints.clone();
    extend_unique(&mut constraints, vec![complement]);
    Ok(Some(RemainderBranch {
        pattern: Pattern {
            term: pattern.term.clone(),
            constraints,
        },
        rule_ids: vec![format!("destination:{}", claim.attributes.unique_id)],
        effects: Vec::new(),
        simplifications: Vec::new(),
        indeterminate: None,
        diagnostics: Vec::new(),
        observations: Vec::new(),
    }))
}

/// The part of `pattern` that `coverage` does not cover: `¬∃E. covered`, where `covered` is the
/// predicate that holds exactly on the covered part ([`CoverageCondition::covered`]) and `E` are
/// its variables that are neither in the state nor among the claim's `universals`.
/// A universal stays free even when the current state no longer mentions it: it names the
/// same value in every state of the proof, so quantifying it would turn "the initial value
/// differs" into `⊥` and drop the uncovered part.
fn complement_implication_condition(
    pattern: &Pattern,
    universals: &BTreeSet<crate::term::Variable>,
    coverage: &CoverageCondition,
) -> crate::rule::Predicate {
    let mut covered = coverage.covered();
    let in_scope = pattern
        .term
        .attributes()
        .variables
        .iter()
        .cloned()
        .chain(
            pattern
                .constraints
                .iter()
                .flat_map(crate::rule::Predicate::free_variables),
        )
        .chain(universals.iter().cloned())
        .collect::<BTreeSet<_>>();
    // Outermost first in order of first occurrence, so the binders' order depends on where the
    // variables occur, not on their names.
    let introduced = crate::rewrite::free_variables_by_first_occurrence(&covered)
        .into_iter()
        .filter(|variable| !in_scope.contains(variable))
        .collect::<Vec<_>>();
    for variable in introduced.into_iter().rev() {
        covered = crate::rule::Predicate::Exists(variable, Arc::new(covered));
    }
    crate::simplify::normalize_predicate(crate::rule::Predicate::Not(Arc::new(covered)))
}

#[cfg(test)]
#[allow(clippy::wildcard_enum_match_arm)]
mod tests {
    use std::{thread, time::Duration};

    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    use super::*;
    use crate::{
        diagnostic::{self, BackendDiagnostic},
        simplify::BudgetSubject,
        smt::{NoSolver, Satisfiability},
        timeout::StepTimeoutMode,
    };

    struct SlowSolver;

    impl SmtSolver for SlowSolver {
        fn is_sat(
            &self,
            _predicates: &[crate::rule::Predicate],
            _substitution: &Substitution,
        ) -> Stoppable<Result<Satisfiability, SmtError>> {
            thread::sleep(Duration::from_millis(5));
            Ok(Ok(Satisfiability::Sat))
        }

        fn check_predicates(
            &self,
            _known: &[crate::rule::Predicate],
            _substitution: &Substitution,
            _checked: &[crate::rule::Predicate],
        ) -> Stoppable<Result<Validity, SmtError>> {
            thread::sleep(Duration::from_millis(5));
            Ok(Ok(Validity::Contingent))
        }
    }

    #[derive(Clone, Debug)]
    struct FixedSolver {
        satisfiability: Result<Satisfiability, SmtError>,
        validity: Result<Validity, SmtError>,
    }

    impl SmtSolver for FixedSolver {
        fn is_sat(
            &self,
            _predicates: &[crate::rule::Predicate],
            _substitution: &Substitution,
        ) -> Stoppable<Result<Satisfiability, SmtError>> {
            Ok(self.satisfiability.clone())
        }

        fn check_predicates(
            &self,
            _known: &[crate::rule::Predicate],
            _substitution: &Substitution,
            _checked: &[crate::rule::Predicate],
        ) -> Stoppable<Result<Validity, SmtError>> {
            Ok(self.validity.clone())
        }
    }

    struct NonemptyUnsatSolver;

    impl SmtSolver for NonemptyUnsatSolver {
        fn is_sat(
            &self,
            predicates: &[crate::rule::Predicate],
            _substitution: &Substitution,
        ) -> Stoppable<Result<Satisfiability, SmtError>> {
            Ok(Ok(if predicates.is_empty() {
                Satisfiability::Sat
            } else {
                Satisfiability::Unsat
            }))
        }

        fn check_predicates(
            &self,
            _known: &[crate::rule::Predicate],
            _substitution: &Substitution,
            _checked: &[crate::rule::Predicate],
        ) -> Stoppable<Result<Validity, SmtError>> {
            Ok(Ok(Validity::Contingent))
        }
    }

    fn definition(rules: &str, claims: &str) -> BackendDefinition {
        let source = format!(
            r#"[]
            module MAIN
                sort SortS{{}} []
                symbol a{{}}() : SortS{{}} [constructor{{}}()]
                symbol b{{}}() : SortS{{}} [constructor{{}}()]
                symbol c{{}}() : SortS{{}} [constructor{{}}()]
                alias weakExistsFinally{{S}}(S) : S
                    where weakExistsFinally{{S}}(@X:S) := @X:S []
                alias weakAlwaysFinally{{S}}(S) : S
                    where weakAlwaysFinally{{S}}(@X:S) := @X:S []
                {rules}
                {claims}
            endmodule []"#
        );
        let syntax = parse_definition(&source).expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    fn claim_with_label<'a>(
        definition: &'a BackendDefinition,
        label: &str,
    ) -> &'a ReachabilityClaim {
        definition
            .reachability_claims()
            .iter()
            .find(|claim| claim.attributes.label.as_deref() == Some(label))
            .unwrap_or_else(|| panic!("claim {label:?} should be indexed"))
    }

    /// A definition with a partial `divInt` (no `total` attribute, no ceil equation), so that
    /// `10 /Int Y` is undefined at `Y = 0`.
    #[cfg(feature = "z3")]
    fn partial_claim_definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                sort SortState{} []
                symbol pair{}(SortInt{}, SortInt{}) : SortState{} [constructor{}()]
                symbol done{}() : SortState{} [constructor{}()]
                hooked-symbol leInt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.le"), smt-hook{}("<=")]
                hooked-symbol addInt{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), total{}(), hook{}("INT.add"), smt-hook{}("+")]
                hooked-symbol divInt{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), hook{}("INT.tdiv"), smt-hook{}("div")]
            endmodule []"#,
        )
        .expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    /// A one-path claim `lhs ∧ requires ⇒ rhs` over `partial_claim_definition`.
    #[cfg(feature = "z3")]
    fn partial_claim(
        definition: &BackendDefinition,
        lhs: &str,
        requires: &str,
        rhs: &str,
    ) -> ReachabilityClaim {
        let requires = crate::rule::Predicate::Equals(
            term(definition, r#"\dv{SortBool{}}("true")"#),
            term(definition, requires),
        );
        ReachabilityClaim {
            lhs: Pattern {
                term: term(definition, lhs),
                constraints: vec![requires],
            },
            rhs: vec![Pattern {
                term: term(definition, rhs),
                constraints: Vec::new(),
            }],
            existentials: BTreeSet::new(),
            mode: crate::claim::ReachabilityMode::OnePath,
            attributes: crate::claim::ClaimAttributes {
                label: Some("partial".into()),
                unique_id: "partial".into(),
                trusted: false,
                source: None,
                location: None,
                sentence: 0,
            },
            unstated: None,
        }
    }

    /// Ported from the probe `cbc07_probe_claim_requires_over_a_partial_term` (P3).
    /// At `Y = 0` the claim's instantiated `requires` `10 /Int Y <=Int 10 /Int Y +Int 1` denotes
    /// `⊥` (I1), so the claim does not apply to `pair(0, 1)`: those instances must stay in the
    /// remainder rather than leave the proof unexamined.
    #[cfg(feature = "z3")]
    #[test]
    fn a_claim_requires_over_a_partial_term_leaves_its_undefined_instances() {
        let definition = partial_claim_definition();
        let solver = crate::smt::Z3Solver::new(&definition).expect("Z3 should initialize");
        let claim = partial_claim(
            &definition,
            r#"pair{}(X:SortInt{}, \dv{SortInt{}}("1"))"#,
            r#"leInt{}(divInt{}(\dv{SortInt{}}("10"), X:SortInt{}), addInt{}(divInt{}(\dv{SortInt{}}("10"), X:SortInt{}), \dv{SortInt{}}("1")))"#,
            r#"pair{}(X:SortInt{}, \dv{SortInt{}}("2"))"#,
        );
        let subject = Pattern {
            term: term(&definition, r#"pair{}(Y:SortInt{}, \dv{SortInt{}}("1"))"#),
            constraints: Vec::new(),
        };
        let mut fresh = crate::fresh::FreshCounter::default();
        let application = apply_claim(
            &definition,
            &claim,
            &subject,
            ProofOptions::default(),
            &solver,
            &mut fresh,
        )
        .expect("no stop is armed");
        let ClaimApplication::Applied {
            patterns,
            remainder,
        } = application
        else {
            panic!("the claim should apply to the defined instances");
        };
        assert_eq!(patterns.len(), 1, "{patterns:#?}");
        let remainder = remainder.expect("the instances where 10 /Int Y is undefined remain");
        assert_eq!(remainder.pattern.term, subject.term);
        let mut constraints = remainder.pattern.constraints.clone();
        constraints.push(crate::rule::Predicate::Equals(
            term(&definition, "Y:SortInt{}"),
            term(&definition, r#"\dv{SortInt{}}("0")"#),
        ));
        assert_eq!(
            solver.is_sat(&constraints, &Substitution::new()),
            Ok(Ok(Satisfiability::Sat)),
            "the remainder must admit Y = 0: {:#?}",
            remainder.pattern.constraints
        );
    }

    /// Ported from the probe `cbc07_probe_claim_subject_term_defines` (I7).
    /// The subject `pair(Y, 10 /Int Y)` is empty where `10 /Int Y` is undefined, so `⌈10 /Int Y⌉`
    /// holds on every instance and the claim covers the whole subject.
    #[cfg(feature = "z3")]
    #[test]
    fn a_claim_on_a_subject_whose_term_defines_the_partial_term_leaves_no_remainder() {
        let definition = partial_claim_definition();
        let solver = crate::smt::Z3Solver::new(&definition).expect("Z3 should initialize");
        let claim = partial_claim(
            &definition,
            r#"pair{}(X:SortInt{}, Z:SortInt{})"#,
            r#"leInt{}(Z:SortInt{}, addInt{}(Z:SortInt{}, \dv{SortInt{}}("1")))"#,
            r#"done{}()"#,
        );
        let subject = Pattern {
            term: term(
                &definition,
                r#"pair{}(Y:SortInt{}, divInt{}(\dv{SortInt{}}("10"), Y:SortInt{}))"#,
            ),
            constraints: Vec::new(),
        };
        let mut fresh = crate::fresh::FreshCounter::default();
        let application = apply_claim(
            &definition,
            &claim,
            &subject,
            ProofOptions::default(),
            &solver,
            &mut fresh,
        )
        .expect("no stop is armed");
        let ClaimApplication::Applied {
            patterns,
            remainder,
        } = application
        else {
            panic!("the claim should apply");
        };
        assert_eq!(patterns.len(), 1, "{patterns:#?}");
        assert!(remainder.is_none(), "{remainder:#?}");
    }

    fn claim_requires_definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                sort SortState{} []
                symbol start{}(SortInt{}) : SortState{} [constructor{}()]
                symbol middle{}(SortInt{}) : SortState{} [constructor{}()]
                symbol end{}(SortInt{}) : SortState{} [constructor{}()]
                symbol f{}(SortInt{}) : SortInt{} [function{}()]
                symbol opaque{}(SortInt{}) : SortInt{}
                    [function{}(), total{}(), no-evaluators{}()]
                alias weakAlwaysFinally{S}(S) : S
                    where weakAlwaysFinally{S}(@X:S) := @X:S []
                axiom{R} \implies{R}(
                    \top{R}(),
                    \equals{SortInt{}, R}(
                        f{}(X:SortInt{}),
                        \and{SortInt{}}(X:SortInt{}, \top{SortInt{}}())
                    )
                ) [label{}("identity-f"), simplification{}()]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(start{}(X:SortInt{}), \top{SortState{}}()),
                    middle{}(X:SortInt{})
                ) [label{}("start")]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(middle{}(X:SortInt{}), \top{SortState{}}()),
                    end{}(X:SortInt{})
                ) [label{}("finish")]
                claim{} \implies{SortState{}}(
                    \and{SortState{}}(start{}(N:SortInt{}), \top{SortState{}}()),
                    weakAlwaysFinally{SortState{}}(end{}(f{}(N:SortInt{})))
                ) [label{}("goal")]
                claim{} \implies{SortState{}}(
                    \and{SortState{}}(
                        middle{}(Y:SortInt{}),
                        \equals{SortInt{}, SortState{}}(
                            Z:SortInt{},
                            f{}(Y:SortInt{})
                        )
                    ),
                    weakAlwaysFinally{SortState{}}(end{}(Z:SortInt{}))
                ) [label{}("defines-z"), trusted{}()]
                claim{} \implies{SortState{}}(
                    \and{SortState{}}(
                        middle{}(Y:SortInt{}),
                        \equals{SortInt{}, SortState{}}(
                            opaque{}(Y:SortInt{}),
                            \dv{SortInt{}}("0")
                        )
                    ),
                    weakAlwaysFinally{SortState{}}(end{}(Y:SortInt{}))
                ) [label{}("guarded"), trusted{}()]
            endmodule []"#,
        )
        .expect("claim requires definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN")
            .expect("claim requires definition should internalize")
    }

    fn term(definition: &BackendDefinition, source: &str) -> Term {
        let syntax = parse_pattern(source).expect("term should parse");
        definition
            .internalize_term(&syntax, &[])
            .expect("term should internalize")
    }

    fn prove_claim(
        definition: &BackendDefinition,
        claim: &ReachabilityClaim,
        options: ProofOptions,
        solver: &dyn SmtSolver,
    ) -> Result<ProofResult, ProofError> {
        let circularities = definition.reachability_claims().iter().collect::<Vec<_>>();
        super::prove_claim(definition, claim, &circularities, options, solver)
    }

    #[test]
    fn complements_disjunctive_destination_coverage_branchwise() {
        let definition = definition("", "");
        let x = term(&definition, "X:SortS{}");
        let first = crate::rule::Predicate::Equals(x.clone(), term(&definition, "a{}()"));
        let second = crate::rule::Predicate::Equals(x.clone(), term(&definition, "b{}()"));
        let pattern = Pattern {
            term: x,
            constraints: Vec::new(),
        };

        assert_eq!(
            complement_implication_condition(
                &pattern,
                &BTreeSet::new(),
                &CoverageCondition::of_obligations(vec![crate::rule::Predicate::Or(
                    vec![first.clone(), second.clone(),].into()
                )]),
            ),
            crate::rule::Predicate::And(
                vec![
                    crate::rule::Predicate::Not(Arc::new(first)),
                    crate::rule::Predicate::Not(Arc::new(second)),
                ]
                .into()
            ),
        );
    }

    /// A claim universal `X` that the path overwrote occurs only in the coverage condition
    /// `X = a`. The uncovered part is the states where the initial `X` differs, `¬(X = a)`;
    /// quantifying `X` would give `¬∃X. X = a`, which is `⊥` and loses that part.
    #[test]
    fn complement_keeps_a_claim_universal_absent_from_the_state_free() {
        let definition = definition("", "");
        let x = term(&definition, "X:SortS{}");
        let crate::term::TermKind::Variable(universal) = x.kind() else {
            unreachable!("X parses as a variable")
        };
        let covered = crate::rule::Predicate::Equals(x.clone(), term(&definition, "a{}()"));
        let pattern = Pattern {
            term: term(&definition, "b{}()"),
            constraints: Vec::new(),
        };
        let condition = CoverageCondition::of_obligations(vec![covered.clone()]);

        assert_eq!(
            complement_implication_condition(
                &pattern,
                &BTreeSet::from([universal.clone()]),
                &condition,
            ),
            crate::rule::Predicate::Not(Arc::new(covered.clone())),
        );
        // A destination existential is still quantified.
        assert_eq!(
            complement_implication_condition(&pattern, &BTreeSet::new(), &condition),
            crate::rule::Predicate::Not(Arc::new(crate::rule::Predicate::Exists(
                universal.clone(),
                Arc::new(covered),
            ))),
        );
    }

    /// A trivial (empty) successor is a leaf the vacuity policy rejects: the claim fails, but
    /// no configuration of the leaf refutes it. Only a certified stuck leaf disproves the claim,
    /// and it takes precedence over every other leaf; an uncertified one fails the claim ahead
    /// of an indeterminate leaf.
    #[test]
    fn finish_reserves_disproved_for_a_certified_stuck_leaf() {
        let definition = definition("", "");
        let leaf = |outcome: ProofLeafOutcome, certified: bool| ProofLeaf {
            pattern: Pattern {
                term: term(&definition, "a{}()"),
                constraints: Vec::new(),
            },
            depth: 1,
            trace: Vec::new(),
            outcome,
            certified,
            contradicted_total: None,
        };
        let status = |leaves: Vec<ProofLeaf>| finish(leaves, 1, 0).status;
        let indeterminate = || {
            leaf(
                ProofLeafOutcome::Indeterminate(ProofIndeterminateReason::Implication),
                false,
            )
        };

        assert_eq!(
            status(vec![leaf(ProofLeafOutcome::Trivial, false)]),
            ProofStatus::Failed
        );
        assert_eq!(
            status(vec![leaf(ProofLeafOutcome::Vacuous, false)]),
            ProofStatus::Failed
        );
        assert_eq!(
            status(vec![indeterminate(), leaf(ProofLeafOutcome::Stuck, false)]),
            ProofStatus::Failed
        );
        assert_eq!(
            status(vec![
                leaf(ProofLeafOutcome::Trivial, false),
                indeterminate(),
                leaf(ProofLeafOutcome::Stuck, true),
            ]),
            ProofStatus::Disproved
        );
        assert_eq!(
            status(vec![
                indeterminate(),
                leaf(ProofLeafOutcome::DepthBound, false)
            ]),
            ProofStatus::Indeterminate
        );
    }

    /// spec-rule-application def032: the trusted claim `mid(Y -Int 1) => end(Y)` unifies with
    /// `mid(X)` under the condition `X = Y + -1` whose complement, once the claim variable `Y`
    /// is quantified, is `\not(\exists Y. X = Y + -1)`: unsatisfiable over the integers. The
    /// remainder then denotes no state, so the claim covers the whole subject and the proof
    /// holds; an unsatisfiable remainder must not surface as a vacuous leaf that fails the proof.
    #[cfg(feature = "z3")]
    #[test]
    fn prunes_an_unsatisfiable_claim_remainder_instead_of_reporting_it_vacuous() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                sort SortS{} []
                hooked-symbol plusInt{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), total{}(), hook{}("INT.add"), smt-hook{}("+")]
                symbol start{}(SortInt{}) : SortS{} [constructor{}()]
                symbol mid{}(SortInt{}) : SortS{} [constructor{}()]
                symbol end{}(SortInt{}) : SortS{} [constructor{}()]
                alias weakExistsFinally{S}(S) : S
                    where weakExistsFinally{S}(@X:S) := @X:S []
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(start{}(X:SortInt{}), \top{SortS{}}()),
                    mid{}(X:SortInt{})
                ) [label{}("start")]
                claim{} \implies{SortS{}}(
                    \and{SortS{}}(start{}(X:SortInt{}), \top{SortS{}}()),
                    weakExistsFinally{SortS{}}(
                        \exists{SortS{}}(
                            Z:SortInt{},
                            \and{SortS{}}(end{}(Z:SortInt{}), \top{SortS{}}())
                        )
                    )
                ) [label{}("main")]
                claim{} \implies{SortS{}}(
                    \and{SortS{}}(
                        mid{}(plusInt{}(Y:SortInt{}, \dv{SortInt{}}("-1"))),
                        \top{SortS{}}()
                    ),
                    weakExistsFinally{SortS{}}(
                        \and{SortS{}}(end{}(Y:SortInt{}), \top{SortS{}}())
                    )
                ) [label{}("shift"), trusted{}()]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let solver = crate::smt::Z3Solver::new(&definition).expect("Z3 should initialize");

        let result = prove_claim(
            &definition,
            claim_with_label(&definition, "main"),
            ProofOptions::default(),
            &solver,
        )
        .expect("claim should execute");

        assert_eq!(result.status, ProofStatus::Proven, "{result:#?}");
        assert!(
            !result
                .leaves
                .iter()
                .any(|leaf| matches!(leaf.outcome, ProofLeafOutcome::Vacuous)),
            "{result:#?}"
        );
        assert!(
            !result.leaves.iter().any(|leaf| leaf
                .trace
                .iter()
                .any(|entry| entry.kind == TraceKind::Remainder
                    && entry.unique_id.starts_with("claim:"))),
            "the unsatisfiable remainder must be pruned, not explored: {result:#?}"
        );
        assert!(
            result
                .leaves
                .iter()
                .any(|leaf| leaf.trace.iter().any(|entry| {
                    entry.kind == TraceKind::Claim && entry.label.as_deref() == Some("shift")
                })),
            "{result:#?}"
        );
    }

    /// Reduced from regression-new set_unification (host ratchet runs 13 to 26): the trusted
    /// claim's left-hand side `SetItem(I) F'` unifies with the subject `SetItem(I) F` by binding
    /// the subject frame `F` to the claim frame `F'`. The claim's successors are the states of
    /// its right-hand side under that unifier, so the right-hand side takes the unifier's whole
    /// substitution and the successor keeps the binding of the subject's variable as a
    /// condition: the subject's variables are free in the state, and the binding is what
    /// relates the claim frame to the subject's frame. The successor is then expressed over the
    /// subject's frame, which the outer claim's destination `?_ F` covers. Dropping the binding
    /// leaves the freshened claim frame unconstrained next to the subject frame, a successor
    /// with an arbitrary frame, and refutes the outer claim.
    #[cfg(feature = "z3")]
    #[test]
    fn applies_a_subject_variable_binding_to_the_claim_successor() {
        // The claim excludes `I in F`, where the `start` step's result set is undefined.
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                hooked-sort SortSet{}
                    [hook{}("SET.Set"), unit{}(setUnit{}()), element{}(setItem{}()), concat{}(setConcat{}())]
                sort SortS{} []
                sort SortCfg{} []
                hooked-symbol setUnit{}() : SortSet{}
                    [function{}(), total{}(), hook{}("SET.unit")]
                hooked-symbol setItem{}(SortInt{}) : SortSet{}
                    [function{}(), total{}(), hook{}("SET.element")]
                hooked-symbol setConcat{}(SortSet{}, SortSet{}) : SortSet{}
                    [function{}(), hook{}("SET.concat"), assoc{}(), comm{}(), idem{}()]
                hooked-symbol setIn{}(SortInt{}, SortSet{}) : SortBool{}
                    [function{}(), total{}(), hook{}("SET.in")]
                symbol start{}(SortInt{}) : SortS{} [constructor{}()]
                symbol mid{}(SortInt{}) : SortS{} [constructor{}()]
                symbol end{}() : SortS{} [constructor{}()]
                symbol cfg{}(SortS{}, SortSet{}) : SortCfg{} [constructor{}()]
                alias weakExistsFinally{S}(S) : S
                    where weakExistsFinally{S}(@X:S) := @X:S []
                axiom{} \rewrites{SortCfg{}}(
                    \and{SortCfg{}}(cfg{}(start{}(I:SortInt{}), F:SortSet{}), \top{SortCfg{}}()),
                    cfg{}(mid{}(I:SortInt{}), setConcat{}(setItem{}(I:SortInt{}), F:SortSet{}))
                ) [label{}("start")]
                claim{} \implies{SortCfg{}}(
                    \and{SortCfg{}}(
                        cfg{}(start{}(I:SortInt{}), F:SortSet{}),
                        \equals{SortBool{}, SortCfg{}}(
                            setIn{}(I:SortInt{}, F:SortSet{}),
                            \dv{SortBool{}}("false")
                        )
                    ),
                    weakExistsFinally{SortCfg{}}(
                        \exists{SortCfg{}}(
                            G:SortSet{},
                            \and{SortCfg{}}(
                                cfg{}(end{}(), setConcat{}(G:SortSet{}, F:SortSet{})),
                                \top{SortCfg{}}()
                            )
                        )
                    )
                ) [label{}("main")]
                claim{} \implies{SortCfg{}}(
                    \and{SortCfg{}}(
                        cfg{}(mid{}(J:SortInt{}), setConcat{}(setItem{}(J:SortInt{}), H:SortSet{})),
                        \top{SortCfg{}}()
                    ),
                    weakExistsFinally{SortCfg{}}(
                        \exists{SortCfg{}}(
                            G:SortSet{},
                            \and{SortCfg{}}(
                                cfg{}(
                                    end{}(),
                                    setConcat{}(
                                        setItem{}(J:SortInt{}),
                                        setConcat{}(G:SortSet{}, H:SortSet{})
                                    )
                                ),
                                \top{SortCfg{}}()
                            )
                        )
                    )
                ) [label{}("finish"), trusted{}()]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let solver = crate::smt::Z3Solver::new(&definition).expect("Z3 should initialize");

        let result = prove_claim(
            &definition,
            &definition.reachability_claims()[0],
            ProofOptions::default(),
            &solver,
        )
        .expect("claim should execute");

        assert_eq!(result.status, ProofStatus::Proven, "{result:#?}");
        for leaf in &result.leaves {
            assert!(
                leaf.pattern
                    .term
                    .attributes()
                    .variables
                    .iter()
                    .all(|variable| !variable.name.starts_with("H!")),
                "the claim successor must be expressed over the subject frame F, not the claim frame H: {leaf:#?}"
            );
        }
    }

    #[cfg(feature = "z3")]
    #[test]
    fn proves_a_destination_covered_by_complementary_branches() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                alias weakExistsFinally{S}(S) : S
                    where weakExistsFinally{S}(@X:S) := @X:S []
                claim{} \implies{SortInt{}}(
                    \and{SortInt{}}(X:SortInt{}, \top{SortInt{}}()),
                    weakExistsFinally{SortInt{}}(
                        \or{SortInt{}}(
                            \and{SortInt{}}(
                                X:SortInt{},
                                \equals{SortInt{}, SortInt{}}(
                                    X:SortInt{},
                                    \dv{SortInt{}}("0")
                                )
                            ),
                            \and{SortInt{}}(
                                X:SortInt{},
                                \not{SortInt{}}(
                                    \equals{SortInt{}, SortInt{}}(
                                        X:SortInt{},
                                        \dv{SortInt{}}("0")
                                    )
                                )
                            )
                        )
                    )
                ) [label{}("complementary")]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let solver = crate::smt::Z3Solver::new(&definition).expect("Z3 should initialize");

        let result = prove_claim(
            &definition,
            &definition.reachability_claims()[0],
            ProofOptions::default(),
            &solver,
        )
        .expect("claim should execute");

        assert_eq!(result.status, ProofStatus::Proven);
        assert_eq!(result.explored_states, 1);
        assert!(matches!(
            result.leaves.as_slice(),
            [ProofLeaf {
                outcome: ProofLeafOutcome::Proven(_),
                ..
            }]
        ));
    }

    #[cfg(feature = "z3")]
    #[test]
    fn closes_the_remainder_after_exhaustive_constructor_case_analysis() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortS{} []
                sort SortT{} []
                symbol a{}() : SortS{} [constructor{}()]
                symbol b{}() : SortS{} [constructor{}()]
                symbol c{}() : SortS{} [constructor{}()]
                symbol total{}(SortS{}) : SortT{} [constructor{}()]
                symbol end{}() : SortT{} [constructor{}()]
                alias weakAlwaysFinally{S}(S) : S
                    where weakAlwaysFinally{S}(@X:S) := @X:S []
                axiom{} \or{SortS{}}(
                    a{}(), b{}(), c{}(), \bottom{SortS{}}()
                ) [constructor{}()]
                axiom{} \rewrites{SortT{}}(
                    \and{SortT{}}(total{}(a{}()), \top{SortT{}}()),
                    end{}()
                ) [label{}("a")]
                axiom{} \rewrites{SortT{}}(
                    \and{SortT{}}(total{}(b{}()), \top{SortT{}}()),
                    end{}()
                ) [label{}("b")]
                axiom{} \rewrites{SortT{}}(
                    \and{SortT{}}(total{}(c{}()), \top{SortT{}}()),
                    end{}()
                ) [label{}("c")]
                claim{} \implies{SortT{}}(
                    \and{SortT{}}(total{}(X:SortS{}), \top{SortT{}}()),
                    weakAlwaysFinally{SortT{}}(end{}())
                ) [label{}("total")]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let solver = crate::smt::Z3Solver::new(&definition).expect("Z3 should initialize");

        let result = prove_claim(
            &definition,
            &definition.reachability_claims()[0],
            ProofOptions::default(),
            &solver,
        )
        .expect("claim should execute");

        assert_eq!(result.status, ProofStatus::Proven, "{result:#?}");
        assert_eq!(result.explored_states, 4);
        assert_eq!(result.unexplored_states, 0);
    }

    #[test]
    fn simplifies_function_patterns_while_applying_claims() {
        let definition = definition(
            r#"
            symbol start{}(SortS{}) : SortS{} [constructor{}()]
            symbol state{}(SortS{}, SortS{}) : SortS{} [constructor{}()]
            symbol identity{}(SortS{}) : SortS{} [function{}(), total{}()]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    identity{}(X:SortS{}),
                    \and{SortS{}}(X:SortS{}, \top{SortS{}}())
                )
            ) [label{}("identity"), simplification{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(start{}(X:SortS{}), \top{SortS{}}()),
                state{}(X:SortS{}, X:SortS{})
            ) [label{}("start")]
            "#,
            r#"
            claim{} \implies{SortS{}}(
                \and{SortS{}}(start{}(a{}()), \top{SortS{}}()),
                weakAlwaysFinally{SortS{}}(c{}())
            ) [label{}("main")]
            claim{} \implies{SortS{}}(
                \and{SortS{}}(
                    state{}(identity{}(N:SortS{}), N:SortS{}),
                    \top{SortS{}}()
                ),
                weakAlwaysFinally{SortS{}}(c{}())
            ) [label{}("circularity"), trusted{}()]
            "#,
        );

        let result = prove_claim(
            &definition,
            claim_with_label(&definition, "main"),
            ProofOptions::default(),
            &NoSolver,
        )
        .expect("claim should execute");

        assert_eq!(result.status, ProofStatus::Proven, "{result:#?}");
        assert_eq!(result.explored_states, 3);
        assert_eq!(result.unexplored_states, 0);
    }

    #[test]
    fn claim_requires_defining_an_unbound_variable_is_a_substitution() {
        let definition = claim_requires_definition();
        let x = Term::variable(crate::term::Variable::new(
            "X",
            crate::term::Sort::simple("SortInt"),
        ));
        let subject = Pattern {
            term: term(&definition, "middle{}(X:SortInt{})"),
            constraints: Vec::new(),
        };
        let mut fresh = crate::fresh::FreshCounter::default();

        let ClaimApplication::Applied {
            patterns,
            remainder: None,
        } = apply_claim(
            &definition,
            claim_with_label(&definition, "defines-z"),
            &subject,
            ProofOptions::default(),
            &NoSolver,
            &mut fresh,
        )
        .expect("no stop is armed")
        else {
            panic!("the defining requires equality should instantiate the claim");
        };
        let [successor] = patterns.as_slice() else {
            panic!("expected one claim successor, found {patterns:?}");
        };
        assert_eq!(successor.term, term(&definition, "end{}(X:SortInt{})"));
        assert!(successor.constraints.is_empty());
        assert_eq!(
            successor.term.attributes().variables.to_btree_set(),
            BTreeSet::from([match x.kind() {
                TermKind::Variable(variable) => variable.clone(),
                _ => unreachable!("the test term is a variable"),
            }])
        );
    }

    #[test]
    fn claim_with_undecidable_requires_narrows() {
        let definition = claim_requires_definition();
        let subject = Pattern {
            term: term(&definition, "middle{}(X:SortInt{})"),
            constraints: Vec::new(),
        };
        let expected = crate::rule::Predicate::Equals(
            term(&definition, "opaque{}(X:SortInt{})"),
            term(&definition, r#"\dv{SortInt{}}("0")"#),
        );
        let solver = FixedSolver {
            satisfiability: Ok(Satisfiability::Sat),
            validity: Ok(Validity::Contingent),
        };

        for solver in [&solver as &dyn SmtSolver, &NoSolver as &dyn SmtSolver] {
            let mut fresh = crate::fresh::FreshCounter::default();
            let ClaimApplication::Applied {
                patterns,
                remainder: Some(remainder),
            } = apply_claim(
                &definition,
                claim_with_label(&definition, "guarded"),
                &subject,
                ProofOptions::default(),
                solver,
                &mut fresh,
            )
            .expect("no stop is armed")
            else {
                panic!("an undecidable requires should split the covered sub-case");
            };
            let [successor] = patterns.as_slice() else {
                panic!("expected one claim successor, found {patterns:?}");
            };
            assert_eq!(successor.term, term(&definition, "end{}(X:SortInt{})"));
            assert_eq!(successor.constraints, vec![expected.clone()]);
            assert_eq!(remainder.pattern.term, subject.term);
            assert_eq!(
                remainder.pattern.constraints,
                vec![crate::rule::Predicate::Not(Arc::new(expected.clone()))]
            );
        }
    }

    #[test]
    fn solver_unknown_on_claim_requires_stays_indeterminate() {
        let definition = claim_requires_definition();
        let subject = Pattern {
            term: term(&definition, "middle{}(X:SortInt{})"),
            constraints: Vec::new(),
        };
        let solver = FixedSolver {
            satisfiability: Ok(Satisfiability::Sat),
            validity: Ok(Validity::Unknown("timeout".into())),
        };
        let mut fresh = crate::fresh::FreshCounter::default();

        assert!(matches!(
            apply_claim(
                &definition,
                claim_with_label(&definition, "guarded"),
                &subject,
                ProofOptions::default(),
                &solver,
                &mut fresh,
            ).expect("no stop is armed"),
            ClaimApplication::Indeterminate(ClaimIndeterminateReason::Smt(
                SmtError::Unknown(reason)
            )) if reason == "timeout"
        ));
    }

    #[test]
    fn proves_a_claim_whose_existential_is_defined_by_an_obligation() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                sort SortState{} []
                symbol start{}() : SortState{} [constructor{}()]
                symbol done{}(SortInt{}) : SortState{} [constructor{}()]
                alias weakAlwaysFinally{S}(S) : S
                    where weakAlwaysFinally{S}(@X:S) := @X:S []
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(start{}(), \top{SortState{}}()),
                    done{}(\dv{SortInt{}}("5"))
                ) [label{}("step")]
                claim{} \implies{SortState{}}(
                    \and{SortState{}}(start{}(), \top{SortState{}}()),
                    weakAlwaysFinally{SortState{}}(
                        \exists{SortState{}}(
                            C:SortInt{},
                            \and{SortState{}}(
                                done{}(\dv{SortInt{}}("5")),
                                \equals{SortInt{}, SortState{}}(
                                    C:SortInt{},
                                    \dv{SortInt{}}("5")
                                )
                            )
                        )
                    )
                ) [label{}("existential-obligation")]
            endmodule []"#,
        )
        .expect("existential claim should parse");
        let definition = BackendDefinition::internalize(&syntax, "MAIN")
            .expect("existential claim should internalize");

        let result = prove_claim(
            &definition,
            &definition.reachability_claims()[0],
            ProofOptions::default(),
            &NoSolver,
        )
        .expect("claim should execute");

        assert_eq!(result.status, ProofStatus::Proven, "{result:#?}");
        assert_eq!(result.explored_states, 2);
        assert_eq!(result.unexplored_states, 0);
    }

    /// `done(7)` refutes `∃N. done(N) ∧ N = 8`: the match binds `N := 7` and the obligation
    /// `7 = 8` is false, so no part of the state lies in the destination. The refutation's
    /// condition holds that binding and no predicate; the whole state must stay the leaf, never
    /// the complement of that condition (which is bottom and would read as a vacuous branch).
    #[test]
    fn a_refuted_destination_condition_leaves_the_whole_state_stuck() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                sort SortState{} []
                symbol start{}() : SortState{} [constructor{}()]
                symbol done{}(SortInt{}) : SortState{} [constructor{}()]
                symbol held{}(SortInt{}) : SortState{} [constructor{}()]
                alias weakAlwaysFinally{S}(S) : S
                    where weakAlwaysFinally{S}(@X:S) := @X:S []
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(start{}(), \top{SortState{}}()),
                    done{}(\dv{SortInt{}}("7"))
                ) [label{}("step")]
                claim{} \implies{SortState{}}(
                    \and{SortState{}}(start{}(), \top{SortState{}}()),
                    weakAlwaysFinally{SortState{}}(
                        \exists{SortState{}}(
                            N:SortInt{},
                            \and{SortState{}}(
                                done{}(N:SortInt{}),
                                \equals{SortInt{}, SortState{}}(
                                    N:SortInt{},
                                    \dv{SortInt{}}("8")
                                )
                            )
                        )
                    )
                ) [label{}("after-a-step")]
                claim{} \implies{SortState{}}(
                    \and{SortState{}}(held{}(\dv{SortInt{}}("7")), \top{SortState{}}()),
                    weakAlwaysFinally{SortState{}}(
                        \exists{SortState{}}(
                            N:SortInt{},
                            \and{SortState{}}(
                                held{}(N:SortInt{}),
                                \equals{SortInt{}, SortState{}}(
                                    N:SortInt{},
                                    \dv{SortInt{}}("8")
                                )
                            )
                        )
                    )
                ) [label{}("at-the-start")]
            endmodule []"#,
        )
        .expect("refuted destination claims should parse");
        let definition = BackendDefinition::internalize(&syntax, "MAIN")
            .expect("refuted destination claims should internalize");
        let stuck_state = Pattern {
            term: term(&definition, r#"done{}(\dv{SortInt{}}("7"))"#),
            constraints: Vec::new(),
        };

        let claim = claim_with_label(&definition, "after-a-step");
        let refutation = check_disjunctive_implication_with_existentials(
            &definition,
            &stuck_state,
            &claim.rhs,
            &claim.existentials,
            SimplificationOptions::default(),
            &NoSolver,
        )
        .expect("no stop is armed")
        .expect("the destination check should run");
        let Coverage::ConditionRefuted { report, .. } = &refutation else {
            panic!("a refutation reports the match it refuted: {refutation:#?}");
        };
        let condition = report.condition();
        assert!(condition.predicates.is_empty(), "{refutation:#?}");
        assert!(
            !condition.substitution.is_empty() || !condition.witnesses.is_empty(),
            "{refutation:#?}"
        );

        // Each claim's left-hand side matches only its own states, so neither claim can serve
        // as a circularity for the other.
        let held_state = Pattern {
            term: term(&definition, r#"held{}(\dv{SortInt{}}("7"))"#),
            constraints: Vec::new(),
        };
        for (label, depth, stuck_state) in [
            ("after-a-step", 1, &stuck_state),
            ("at-the-start", 0, &held_state),
        ] {
            for allow_vacuous in [false, true] {
                let options = ProofOptions {
                    allow_vacuous,
                    ..ProofOptions::default()
                };
                let result = prove_claim(
                    &definition,
                    claim_with_label(&definition, label),
                    options,
                    &NoSolver,
                )
                .expect("claim should execute");

                assert_eq!(
                    result.status,
                    ProofStatus::Disproved,
                    "{label}: {result:#?}"
                );
                let [leaf] = result.leaves.as_slice() else {
                    panic!("{label}: expected one leaf, found {result:#?}");
                };
                assert_eq!(
                    leaf.outcome,
                    ProofLeafOutcome::Stuck,
                    "{label}: {result:#?}"
                );
                assert_eq!(leaf.depth, depth, "{label}: {result:#?}");
                assert_eq!(&leaf.pattern, stuck_state, "{label}: {result:#?}");
            }
        }
    }

    /// Refutes an obligation that is a single equation, answers every other obligation as
    /// contingent, and every satisfiability query as `Sat`. For the claim of
    /// [`a_refuted_binding_of_a_variable_state_leaves_the_whole_state_uncovered`] the only
    /// equation obligation is the destination's `0 = X` under `X >Int 0`, which is refuted: no
    /// positive integer is `0`, and the state `X >Int 0` has instances.
    struct RefutesEquationSolver;

    impl SmtSolver for RefutesEquationSolver {
        fn is_sat(
            &self,
            _predicates: &[crate::rule::Predicate],
            _substitution: &Substitution,
        ) -> Stoppable<Result<Satisfiability, SmtError>> {
            Ok(Ok(Satisfiability::Sat))
        }

        fn check_predicates(
            &self,
            _known: &[crate::rule::Predicate],
            _substitution: &Substitution,
            checked: &[crate::rule::Predicate],
        ) -> Stoppable<Result<Validity, SmtError>> {
            Ok(Ok(match checked {
                [crate::rule::Predicate::Equals(..)] => Validity::Refuted,
                _ => Validity::Contingent,
            }))
        }
    }

    fn variable_state_definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                hooked-symbol gtInt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.gt"), smt-hook{}(">")]
                alias weakAlwaysFinally{S}(S) : S
                    where weakAlwaysFinally{S}(@X:S) := @X:S []
                claim{} \implies{SortInt{}}(
                    \and{SortInt{}}(
                        X:SortInt{},
                        \equals{SortBool{}, SortInt{}}(
                            gtInt{}(X:SortInt{}, \dv{SortInt{}}("0")),
                            \dv{SortBool{}}("true")
                        )
                    ),
                    weakAlwaysFinally{SortInt{}}(\dv{SortInt{}}("0"))
                ) [label{}("positive-reaches-zero")]
            endmodule []"#,
        )
        .expect("variable state definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN")
            .expect("variable state definition should internalize")
    }

    /// `X ∧ X >Int 0 ⇒ ◇ 0` is false in a definition without rules: every instance is a
    /// positive integer, none is `0`, and none rewrites. The destination match leaves the
    /// obligation `0 = X`, which the state's constraint refutes, so no instance is covered and
    /// the uncovered part is the whole state, `X ∧ X >Int 0 ∧ ¬(0 = X)`. That equation binds the
    /// state's own variable; the uncovered part is the complement of every obligation the
    /// covered instances satisfy, the binding included. Dropping it from the complement would
    /// leave `¬⊤ = ⊥`, an empty remainder that vacuity closes although no instance reached `0`.
    fn assert_a_refuted_binding_leaves_the_whole_state_uncovered(solver: &dyn SmtSolver) {
        let definition = variable_state_definition();
        let claim = claim_with_label(&definition, "positive-reaches-zero");
        let variable = term(&definition, "X:SortInt{}");
        for allow_vacuous in [true, false] {
            let options = ProofOptions {
                allow_vacuous,
                ..ProofOptions::default()
            };
            let result =
                prove_claim(&definition, claim, options, solver).expect("claim should execute");
            let label = format!("allow_vacuous {allow_vacuous}");

            assert_ne!(result.status, ProofStatus::Proven, "{label}: {result:#?}");
            assert!(
                !result.leaves.iter().any(|leaf| matches!(
                    leaf.outcome,
                    ProofLeafOutcome::Proven(_) | ProofLeafOutcome::Vacuous
                )),
                "{label}: {result:#?}"
            );
            let [leaf] = result.leaves.as_slice() else {
                panic!("{label}: expected one leaf, found {result:#?}");
            };
            assert_eq!(
                leaf.outcome,
                ProofLeafOutcome::Stuck,
                "{label}: {result:#?}"
            );
            assert_eq!(leaf.pattern.term, variable, "{label}: {result:#?}");
            assert!(
                !leaf
                    .pattern
                    .constraints
                    .contains(&crate::rule::Predicate::False),
                "{label}: {result:#?}"
            );
        }
    }

    #[test]
    fn a_refuted_binding_of_a_variable_state_leaves_the_whole_state_uncovered() {
        assert_a_refuted_binding_leaves_the_whole_state_uncovered(&RefutesEquationSolver);
    }

    #[test]
    #[cfg(feature = "z3")]
    fn a_refuted_binding_of_a_variable_state_leaves_the_whole_state_uncovered_under_z3() {
        let definition = variable_state_definition();
        let solver = crate::smt::Z3Solver::new(&definition).expect("Z3 should initialize");
        assert_a_refuted_binding_leaves_the_whole_state_uncovered(&solver);
    }

    #[test]
    #[cfg(feature = "z3")]
    fn checks_implication_before_classifying_a_rewrite_remainder_as_stuck() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                sort SortState{} []
                symbol start{}(SortInt{}) : SortState{} [constructor{}()]
                symbol b{}() : SortState{} [constructor{}()]
                alias weakAlwaysFinally{S}(S) : S
                    where weakAlwaysFinally{S}(@X:S) := @X:S []
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        start{}(X:SortInt{}),
                        \equals{SortInt{}, SortState{}}(
                            X:SortInt{},
                            \dv{SortInt{}}("0")
                        )
                    ),
                    b{}()
                ) [label{}("guarded")]
                claim{} \implies{SortState{}}(
                    \and{SortState{}}(start{}(X:SortInt{}), \top{SortState{}}()),
                    weakAlwaysFinally{SortState{}}(
                        \or{SortState{}}(
                            b{}(),
                            \and{SortState{}}(
                                start{}(X:SortInt{}),
                                \not{SortState{}}(
                                    \equals{SortInt{}, SortState{}}(
                                        X:SortInt{},
                                        \dv{SortInt{}}("0")
                                    )
                                )
                            )
                        )
                    )
                ) [label{}("remainder-covered")]
            endmodule []"#,
        )
        .expect("remainder implication probe should parse");
        let definition = BackendDefinition::internalize(&syntax, "MAIN")
            .expect("remainder implication probe should internalize");
        let solver = crate::smt::Z3Solver::new(&definition).expect("Z3 should initialize");

        let result = prove_claim(
            &definition,
            claim_with_label(&definition, "remainder-covered"),
            ProofOptions::default(),
            &solver,
        )
        .expect("claim should execute");

        assert_eq!(result.status, ProofStatus::Proven, "{result:#?}");
        assert!(
            result
                .leaves
                .iter()
                .all(|leaf| matches!(leaf.outcome, ProofLeafOutcome::Proven(_))),
            "{result:#?}"
        );
    }

    /// A destination obligation that holds on part of the state splits it: the uncovered part
    /// continues and, having no successor, is a stuck leaf (disproved) carrying the failing
    /// condition. An unknown solver answer establishes no part, so the leaf stays indeterminate.
    #[test]
    fn a_contingent_destination_splits_the_state_and_an_unknown_one_does_not() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                sort SortState{} []
                symbol start{}(SortInt{}) : SortState{} [constructor{}()]
                symbol other{}() : SortState{} [constructor{}()]
                alias weakAlwaysFinally{S}(S) : S
                    where weakAlwaysFinally{S}(@X:S) := @X:S []
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(other{}(), \top{SortState{}}()),
                    other{}()
                ) [label{}("unrelated")]
                claim{} \implies{SortState{}}(
                    \and{SortState{}}(start{}(X:SortInt{}), \top{SortState{}}()),
                    weakAlwaysFinally{SortState{}}(
                        \and{SortState{}}(
                            start{}(X:SortInt{}),
                            \equals{SortInt{}, SortState{}}(
                                X:SortInt{},
                                \dv{SortInt{}}("0")
                            )
                        )
                    )
                ) [label{}("contingent")]
            endmodule []"#,
        )
        .expect("contingent destination probe should parse");
        let definition = BackendDefinition::internalize(&syntax, "MAIN")
            .expect("contingent destination probe should internalize");
        let claim = claim_with_label(&definition, "contingent");
        let covered = crate::rule::Predicate::Equals(
            term(&definition, "X:SortInt{}"),
            term(&definition, r#"\dv{SortInt{}}("0")"#),
        );

        let contingent = FixedSolver {
            satisfiability: Ok(Satisfiability::Sat),
            validity: Ok(Validity::Contingent),
        };
        let result = prove_claim(&definition, claim, ProofOptions::default(), &contingent)
            .expect("claim should execute");
        assert_eq!(result.status, ProofStatus::Disproved, "{result:#?}");
        let [leaf] = result.leaves.as_slice() else {
            panic!("expected one leaf, found {result:#?}");
        };
        assert_eq!(leaf.outcome, ProofLeafOutcome::Stuck, "{result:#?}");
        assert!(
            leaf.pattern
                .constraints
                .contains(&crate::rule::Predicate::Not(Arc::new(covered))),
            "{result:#?}"
        );

        let unknown = FixedSolver {
            satisfiability: Ok(Satisfiability::Sat),
            validity: Ok(Validity::Unknown("timeout".into())),
        };
        let result = prove_claim(&definition, claim, ProofOptions::default(), &unknown)
            .expect("claim should execute");
        assert_eq!(result.status, ProofStatus::Indeterminate, "{result:#?}");
        let [leaf] = result.leaves.as_slice() else {
            panic!("expected one leaf, found {result:#?}");
        };
        assert_eq!(
            leaf.outcome,
            ProofLeafOutcome::Indeterminate(ProofIndeterminateReason::Implication),
            "{result:#?}"
        );
    }

    /// A destination reached through a match remainder (`start(X)` against `start(0)`) is
    /// classified like any other obligation. A contingent one closes the covered part and hands
    /// the rest to the rewrite step, whatever the stuck check says: here the rest takes the rule
    /// to b(), and its certified terminal leaf is at depth 1.
    /// An undecided one leaves the state indeterminate instead of a stuck complement that is not
    /// shown non-empty.
    #[test]
    fn a_match_remainder_obligation_is_classified_like_any_other() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                sort SortState{} []
                symbol start{}(SortInt{}) : SortState{} [constructor{}()]
                symbol idle{}(SortInt{}) : SortState{} [constructor{}()]
                symbol b{}() : SortState{} [constructor{}()]
                alias weakAlwaysFinally{S}(S) : S
                    where weakAlwaysFinally{S}(@X:S) := @X:S []
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(start{}(X:SortInt{}), \top{SortState{}}()),
                    b{}()
                ) [label{}("step")]
                claim{} \implies{SortState{}}(
                    \and{SortState{}}(start{}(X:SortInt{}), \top{SortState{}}()),
                    weakAlwaysFinally{SortState{}}(start{}(\dv{SortInt{}}("0")))
                ) [label{}("rewritable")]
                claim{} \implies{SortState{}}(
                    \and{SortState{}}(idle{}(X:SortInt{}), \top{SortState{}}()),
                    weakAlwaysFinally{SortState{}}(idle{}(\dv{SortInt{}}("0")))
                ) [label{}("terminal")]
            endmodule []"#,
        )
        .expect("remainder destination probe should parse");
        let definition = BackendDefinition::internalize(&syntax, "MAIN")
            .expect("remainder destination probe should internalize");
        // The remainder obligation is the destination's value equal to the state's.
        let covered = crate::rule::Predicate::Equals(
            term(&definition, r#"\dv{SortInt{}}("0")"#),
            term(&definition, "X:SortInt{}"),
        );

        let contingent = FixedSolver {
            satisfiability: Ok(Satisfiability::Sat),
            validity: Ok(Validity::Contingent),
        };
        let result = prove_claim(
            &definition,
            claim_with_label(&definition, "rewritable"),
            ProofOptions {
                ..ProofOptions::default()
            },
            &contingent,
        )
        .expect("claim should execute");
        assert_eq!(result.status, ProofStatus::Disproved, "{result:#?}");
        let [leaf] = result.leaves.as_slice() else {
            panic!("expected one leaf, found {result:#?}");
        };
        assert_eq!(leaf.outcome, ProofLeafOutcome::Stuck, "{result:#?}");
        assert_eq!(leaf.depth, 1, "{result:#?}");
        assert_eq!(leaf.pattern.term, term(&definition, "b{}()"), "{result:#?}");
        assert!(
            leaf.pattern
                .constraints
                .contains(&crate::rule::Predicate::Not(Arc::new(covered.clone()))),
            "{result:#?}"
        );

        let unknown = FixedSolver {
            satisfiability: Ok(Satisfiability::Sat),
            validity: Ok(Validity::Unknown("timeout".into())),
        };
        let result = prove_claim(
            &definition,
            claim_with_label(&definition, "terminal"),
            ProofOptions::default(),
            &unknown,
        )
        .expect("claim should execute");
        assert_eq!(result.status, ProofStatus::Indeterminate, "{result:#?}");
        let [leaf] = result.leaves.as_slice() else {
            panic!("expected one leaf, found {result:#?}");
        };
        assert_eq!(
            leaf.outcome,
            ProofLeafOutcome::Indeterminate(ProofIndeterminateReason::Implication),
            "{result:#?}"
        );
    }

    /// A disjunctive destination whose consequents together cover only part of the state splits
    /// it the same way. The part where `X = 0` is already at the second consequent and closes; the
    /// rest takes the `X =/= 0` rule to `b()`. Rewriting the whole state instead would send the
    /// `X = 0` part to the stuck `c()`, although the claim holds.
    #[test]
    #[cfg(feature = "z3")]
    fn a_contingent_disjunctive_destination_closes_the_covered_part() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                sort SortState{} []
                symbol start{}(SortInt{}) : SortState{} [constructor{}()]
                symbol b{}() : SortState{} [constructor{}()]
                symbol c{}() : SortState{} [constructor{}()]
                alias weakAlwaysFinally{S}(S) : S
                    where weakAlwaysFinally{S}(@X:S) := @X:S []
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        start{}(X:SortInt{}),
                        \not{SortState{}}(
                            \equals{SortInt{}, SortState{}}(
                                X:SortInt{},
                                \dv{SortInt{}}("0")
                            )
                        )
                    ),
                    b{}()
                ) [label{}("nonzero")]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        start{}(X:SortInt{}),
                        \equals{SortInt{}, SortState{}}(
                            X:SortInt{},
                            \dv{SortInt{}}("0")
                        )
                    ),
                    c{}()
                ) [label{}("zero")]
                claim{} \implies{SortState{}}(
                    \and{SortState{}}(start{}(X:SortInt{}), \top{SortState{}}()),
                    weakAlwaysFinally{SortState{}}(
                        \or{SortState{}}(
                            b{}(),
                            \and{SortState{}}(
                                start{}(X:SortInt{}),
                                \equals{SortInt{}, SortState{}}(
                                    X:SortInt{},
                                    \dv{SortInt{}}("0")
                                )
                            )
                        )
                    )
                ) [label{}("disjunctive-contingent")]
            endmodule []"#,
        )
        .expect("disjunctive contingent destination probe should parse");
        let definition = BackendDefinition::internalize(&syntax, "MAIN")
            .expect("disjunctive contingent destination probe should internalize");
        let solver = crate::smt::Z3Solver::new(&definition).expect("Z3 should initialize");

        let result = prove_claim(
            &definition,
            claim_with_label(&definition, "disjunctive-contingent"),
            ProofOptions::default(),
            &solver,
        )
        .expect("claim should execute");

        assert_eq!(result.status, ProofStatus::Proven, "{result:#?}");
        assert!(
            result
                .leaves
                .iter()
                .all(|leaf| matches!(leaf.outcome, ProofLeafOutcome::Proven(_))),
            "{result:#?}"
        );
    }

    const NON_TERMINATING_SIMPLIFIER: &str = r#"
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
    "#;

    #[test]
    fn rewrite_budget_exhaustion_is_not_a_proof_simplification_error() {
        let rules = format!(
            r#"
            {NON_TERMINATING_SIMPLIFIER}
            axiom{{}} \rewrites{{SortS{{}}}}(
                \and{{SortS{{}}}}(
                    a{{}}(),
                    \equals{{SortS{{}}, SortS{{}}}}(
                        expand{{}}(a{{}}()),
                        a{{}}()
                    )
                ),
                b{{}}()
            ) [label{{}}("conditional")]
            "#
        );
        let claims = modal_claim(ReachabilityMode::AllPath, "a", "c", false);
        let definition = definition(&rules, &claims);

        let (result, diagnostics) = diagnostic::collect(|| {
            prove_claim(
                &definition,
                &definition.reachability_claims()[0],
                ProofOptions {
                    max_simplification_iterations: 1,
                    ..ProofOptions::default()
                },
                &NoSolver,
            )
        });
        let result = result.expect("budget exhaustion should remain a proof outcome");

        assert!(
            result.leaves.iter().all(|leaf| !matches!(
                leaf.outcome,
                ProofLeafOutcome::Indeterminate(ProofIndeterminateReason::Simplification(
                    SimplificationError::IterationLimit { .. }
                        | SimplificationError::PredicateIterationLimit { .. }
                ))
            )),
            "{result:#?}"
        );
        assert!(diagnostics.iter().any(|diagnostic| matches!(
            diagnostic,
            BackendDiagnostic::SimplificationBudgetExhausted {
                limit: 1,
                subject: BudgetSubject::Predicates,
            }
        )));
    }

    #[test]
    fn claim_requires_simplification_failure_keeps_its_identity() {
        let claims = r#"
            claim{} \implies{SortS{}}(
                \and{SortS{}}(
                    a{}(),
                    \equals{SortS{}, SortS{}}(
                        expand{}(a{}()),
                        a{}()
                    )
                ),
                weakAlwaysFinally{SortS{}}(c{}())
            ) [label{}("conditional-claim")]
        "#;
        let definition = definition(NON_TERMINATING_SIMPLIFIER, claims);
        let subject = Pattern {
            term: term(&definition, "a{}()"),
            constraints: Vec::new(),
        };
        let mut fresh = crate::fresh::FreshCounter::default();

        let result = apply_claim(
            &definition,
            &definition.reachability_claims()[0],
            &subject,
            ProofOptions {
                max_simplification_iterations: 1,
                ..ProofOptions::default()
            },
            &NoSolver,
            &mut fresh,
        )
        .expect("no stop is armed");

        assert!(matches!(
            result,
            ClaimApplication::Indeterminate(ClaimIndeterminateReason::Simplification(
                SimplificationError::IterationLimit { .. }
                    | SimplificationError::PredicateIterationLimit { .. }
            ))
        ));
    }

    /// A simplification failure while a lower priority group rewrites the remainder of a
    /// productive group is the same failure as one in the first group: the remainder's leaf
    /// reports the simplification error, not a rewrite indeterminacy.
    #[test]
    fn lower_group_simplification_failure_on_the_remainder_keeps_its_identity() {
        let rules = r#"
            hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
            hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
            sort SortIOInt{} []
            symbol opaque{}() : SortBool{} [function{}(), total{}(), no-evaluators{}()]
            symbol isIOInt{}(SortIOInt{}) : SortBool{}
                [function{}(), total{}(), no-evaluators{}()]
            hooked-symbol getc{}(SortInt{}) : SortIOInt{}
                [function{}(), total{}(), hook{}("IO.getc")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    a{}(),
                    \equals{SortBool{}, SortS{}}(opaque{}(), \dv{SortBool{}}("true"))
                ),
                c{}()
            ) [label{}("first"), priority{}("10")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    a{}(),
                    \equals{SortBool{}, SortS{}}(
                        isIOInt{}(getc{}(\dv{SortInt{}}("0"))),
                        \dv{SortBool{}}("true")
                    )
                ),
                b{}()
            ) [label{}("lower-error"), priority{}("50")]
        "#;
        let claims = modal_claim(ReachabilityMode::AllPath, "a", "c", false);
        let definition = definition(rules, &claims);
        // The first group's condition is undecided and its remainder satisfiable, so the step
        // branches to the destination and hands the remainder to the lower group, whose
        // condition needs a hook that has no console to read.
        let solver = FixedSolver {
            satisfiability: Ok(Satisfiability::Sat),
            validity: Ok(Validity::Contingent),
        };

        let result = prove_claim(
            &definition,
            &definition.reachability_claims()[0],
            ProofOptions::default(),
            &solver,
        )
        .expect("the proof should run");

        assert!(
            result.leaves.iter().any(|leaf| matches!(
                &leaf.outcome,
                ProofLeafOutcome::Indeterminate(ProofIndeterminateReason::Simplification(
                    SimplificationError::UnsupportedHook { hook, .. }
                )) if hook == "IO.getc"
            )),
            "{result:#?}"
        );
        assert!(
            result.leaves.iter().all(|leaf| !matches!(
                leaf.outcome,
                ProofLeafOutcome::Indeterminate(ProofIndeterminateReason::Rewrite(_))
            )),
            "{result:#?}"
        );
    }

    #[cfg(feature = "z3")]
    #[test]
    fn proves_map_construction_under_antecedent_definedness() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortKey{} []
                sort SortValue{} [hasDomainValues{}()]
                hooked-sort SortMap{}
                    [hook{}("MAP.Map"), unit{}(mapUnit{}()), element{}(mapItem{}()), concat{}(mapConcat{}())]
                sort SortState{} []
                hooked-symbol mapUnit{}() : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.unit")]
                hooked-symbol mapItem{}(SortKey{}, SortValue{}) : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.element")]
                hooked-symbol mapConcat{}(SortMap{}, SortMap{}) : SortMap{}
                    [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
                symbol start{}(SortKey{}, SortMap{}) : SortState{} [constructor{}()]
                symbol done{}(SortMap{}) : SortState{} [constructor{}()]
                alias weakAlwaysFinally{S}(S) : S
                    where weakAlwaysFinally{S}(@X:S) := @X:S []
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        start{}(KEY:SortKey{}, MAP:SortMap{}),
                        \top{SortState{}}()
                    ),
                    done{}(
                        mapConcat{}(
                            mapItem{}(KEY:SortKey{}, \dv{SortValue{}}("new")),
                            MAP:SortMap{}
                        )
                    )
                ) [label{}("insert")]
                claim{} \implies{SortState{}}(
                    \and{SortState{}}(
                        start{}(
                            X:SortKey{},
                            mapConcat{}(
                                mapItem{}(Y:SortKey{}, \dv{SortValue{}}("old")),
                                REST:SortMap{}
                            )
                        ),
                        \top{SortState{}}()
                    ),
                    weakAlwaysFinally{SortState{}}(
                        done{}(
                            mapConcat{}(
                                mapItem{}(X:SortKey{}, \dv{SortValue{}}("new")),
                                mapConcat{}(
                                    mapItem{}(Y:SortKey{}, \dv{SortValue{}}("old")),
                                    REST:SortMap{}
                                )
                            )
                        )
                    )
                ) [label{}("map-definedness")]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let solver = crate::smt::Z3Solver::new(&definition).expect("Z3 should initialize");

        // The step's result `X |-> "new" Y |-> "old" REST` is undefined where `X` is a key of the
        // antecedent's map: the claim fails there, and holds on every other instance.
        let result = prove_claim(
            &definition,
            &definition.reachability_claims()[0],
            ProofOptions::default(),
            &solver,
        )
        .expect("claim should execute");
        assert_eq!(result.status, ProofStatus::Failed, "{result:#?}");
        assert!(
            result.leaves.iter().all(|leaf| matches!(
                leaf.outcome,
                ProofLeafOutcome::Proven(_) | ProofLeafOutcome::Trivial
            )),
            "{result:#?}"
        );

        let result = prove_claim(
            &definition,
            &definition.reachability_claims()[0],
            ProofOptions {
                allow_vacuous: true,
                ..ProofOptions::default()
            },
            &solver,
        )
        .expect("claim should execute");

        assert_eq!(result.status, ProofStatus::Proven);
        assert_eq!(result.unexplored_states, 0);
    }

    const A_TO_B: &str = r#"
        axiom{} \rewrites{SortS{}}(
            \and{SortS{}}(a{}(), \top{SortS{}}()),
            \and{SortS{}}(b{}(), \top{SortS{}}())
        ) [label{}("a-to-b")]
    "#;

    #[test]
    fn unselected_claims_are_not_circularities() {
        let definition = definition(
            r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(a{}(), \top{SortS{}}()),
                b{}()
            ) [label{}("a-to-b")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(b{}(), \top{SortS{}}()),
                c{}()
            ) [label{}("b-to-c")]
            symbol d{}() : SortS{} [constructor{}()]
            "#,
            r#"
            claim{} \implies{SortS{}}(
                \and{SortS{}}(a{}(), \top{SortS{}}()),
                weakAlwaysFinally{SortS{}}(d{}())
            ) [label{}("ca")]
            claim{} \implies{SortS{}}(
                \and{SortS{}}(b{}(), \top{SortS{}}()),
                weakAlwaysFinally{SortS{}}(d{}())
            ) [label{}("cb")]
            "#,
        );

        let isolated = [claim_with_label(&definition, "ca")];
        let result = super::prove_claim(
            &definition,
            claim_with_label(&definition, "ca"),
            &isolated,
            ProofOptions::default(),
            &NoSolver,
        )
        .expect("claim should execute");

        assert_eq!(result.status, ProofStatus::Disproved, "{result:#?}");
        assert!(matches!(
            result.leaves.as_slice(),
            [ProofLeaf {
                pattern: Pattern { term: stuck, .. },
                outcome: ProofLeafOutcome::Stuck,
                ..
            }] if stuck == &term(&definition, "c{}()")
        ));

        let circularities = definition.reachability_claims().iter().collect::<Vec<_>>();
        let batch = super::prove_claim(
            &definition,
            claim_with_label(&definition, "ca"),
            &circularities,
            ProofOptions::default(),
            &NoSolver,
        )
        .expect("batch claim should execute");
        assert_eq!(batch.status, ProofStatus::Proven, "{batch:#?}");
        assert!(batch.leaves[0].trace.iter().any(|entry| {
            entry.kind == TraceKind::Claim && entry.label.as_deref() == Some("cb")
        }));
    }

    const A_TO_B_AND_C: &str = r#"
        axiom{} \rewrites{SortS{}}(
            \and{SortS{}}(a{}(), \top{SortS{}}()),
            \and{SortS{}}(b{}(), \top{SortS{}}())
        ) [label{}("a-to-b")]
        axiom{} \rewrites{SortS{}}(
            \and{SortS{}}(a{}(), \top{SortS{}}()),
            \and{SortS{}}(c{}(), \top{SortS{}}())
        ) [label{}("a-to-c")]
    "#;

    const START_CASE_SPLIT: &str = r#"
        symbol start{}(SortS{}) : SortS{} [constructor{}()]
        symbol good{}() : SortS{} [constructor{}()]
        symbol bad{}() : SortS{} [constructor{}()]
        axiom{} \rewrites{SortS{}}(
            \and{SortS{}}(
                start{}(X:SortS{}),
                \equals{SortS{}, SortS{}}(X:SortS{}, a{}())
            ),
            good{}()
        ) [label{}("start-to-good")]
        axiom{} \rewrites{SortS{}}(
            \and{SortS{}}(
                start{}(X:SortS{}),
                \not{SortS{}}(
                    \equals{SortS{}, SortS{}}(X:SortS{}, a{}())
                )
            ),
            bad{}()
        ) [label{}("start-to-bad")]
    "#;

    fn start_claim(mode: ReachabilityMode, destination: &str) -> String {
        let modality = match mode {
            ReachabilityMode::OnePath => "weakExistsFinally",
            ReachabilityMode::AllPath => "weakAlwaysFinally",
        };
        format!(
            r#"claim{{}} \implies{{SortS{{}}}}(
                \and{{SortS{{}}}}(start{{}}(X:SortS{{}}), \top{{SortS{{}}}}()),
                {modality}{{SortS{{}}}}(
                    \and{{SortS{{}}}}({destination}{{}}(), \top{{SortS{{}}}}())
                )
            ) [label{{}}("case-split-{destination}")]"#
        )
    }

    #[test]
    fn one_path_case_split_must_close_every_branch() {
        let claims = [
            start_claim(ReachabilityMode::OnePath, "good"),
            start_claim(ReachabilityMode::AllPath, "good"),
        ]
        .join("\n");
        let definition = definition(START_CASE_SPLIT, &claims);
        let solver = FixedSolver {
            satisfiability: Ok(Satisfiability::Sat),
            validity: Ok(Validity::Contingent),
        };

        for claim in definition.reachability_claims() {
            let result = prove_claim(
                &definition,
                claim,
                ProofOptions {
                    max_counterexamples: 2,
                    ..ProofOptions::default()
                },
                &solver,
            )
            .expect("case-split claim should execute");

            // `bad()` under `¬(X = a())` is not certified: the sort of `X` and the constructor
            // `a()` have no SMT translation, so its non-emptiness is only satisfiable modulo
            // abstraction (and the one-path trace may have dropped an alternative).
            assert_eq!(result.status, ProofStatus::Failed, "{result:#?}");
            assert!(result.leaves.iter().any(|leaf| {
                leaf.outcome == ProofLeafOutcome::Stuck
                    && leaf.pattern.term == term(&definition, "bad{}()")
            }));
        }
    }

    #[test]
    fn one_path_applies_overlapping_rules_sequentially() {
        let claims = [
            modal_claim(ReachabilityMode::OnePath, "a", "b", false),
            modal_claim(ReachabilityMode::OnePath, "a", "c", false),
        ]
        .join("\n");
        let definition = definition(A_TO_B_AND_C, &claims);

        // Overlapping equal-priority rules are applied in declaration order, each to the
        // remainder of the previous one; a-to-b consumes the concrete subject, so a-to-c is
        // never applied.
        let first = prove_claim(
            &definition,
            claim_with_label(&definition, "one-a-b"),
            ProofOptions::default(),
            &NoSolver,
        )
        .expect("first overlapping claim should execute");
        assert_eq!(first.status, ProofStatus::Proven, "{first:#?}");
        assert_eq!(first.explored_states, 2);
        assert!(matches!(
            first.leaves.as_slice(),
            [ProofLeaf { trace, .. }]
                if matches!(trace.as_slice(), [TraceEntry {
                    kind: TraceKind::Rewrite,
                    label: Some(label),
                    ..
                }] if label == "a-to-b")
        ));

        let second = prove_claim(
            &definition,
            claim_with_label(&definition, "one-a-c"),
            ProofOptions::default(),
            &NoSolver,
        )
        .expect("second overlapping claim should execute");
        // The claim is true (a-to-c reaches `c`), so the stuck `b` the sequential step reaches
        // fails the proof without disproving the claim.
        assert_eq!(second.status, ProofStatus::Failed, "{second:#?}");
        assert!(second.leaves.iter().all(|leaf| {
            leaf.trace
                .iter()
                .all(|entry| entry.label.as_deref() != Some("a-to-c"))
        }));
    }

    #[test]
    fn one_path_counterexample_limit_applies() {
        let rules = r#"
            symbol d{}() : SortS{} [constructor{}()]
            symbol e{}() : SortS{} [constructor{}()]
            symbol start{}(SortS{}) : SortS{} [constructor{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    start{}(X:SortS{}),
                    \equals{SortS{}, SortS{}}(X:SortS{}, a{}())
                ),
                b{}()
            ) [label{}("start-a")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    start{}(X:SortS{}),
                    \equals{SortS{}, SortS{}}(X:SortS{}, b{}())
                ),
                c{}()
            ) [label{}("start-b")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    start{}(X:SortS{}),
                    \and{SortS{}}(
                        \not{SortS{}}(
                            \equals{SortS{}, SortS{}}(X:SortS{}, a{}())
                        ),
                        \not{SortS{}}(
                            \equals{SortS{}, SortS{}}(X:SortS{}, b{}())
                        )
                    )
                ),
                d{}()
            ) [label{}("start-other")]
        "#;
        let claims = start_claim(ReachabilityMode::OnePath, "e");
        let definition = definition(rules, &claims);
        let solver = FixedSolver {
            satisfiability: Ok(Satisfiability::Sat),
            validity: Ok(Validity::Contingent),
        };

        let result = prove_claim(
            &definition,
            &definition.reachability_claims()[0],
            ProofOptions {
                max_counterexamples: 2,
                ..ProofOptions::default()
            },
            &solver,
        )
        .expect("counterexample-limited claim should execute");

        assert_eq!(result.status, ProofStatus::Failed, "{result:#?}");
        assert_eq!(result.leaves.len(), 2, "{result:#?}");
        assert_eq!(result.unexplored_states, 1, "{result:#?}");
    }

    const A_TO_A: &str = r#"
        axiom{} \rewrites{SortS{}}(
            \and{SortS{}}(a{}(), \top{SortS{}}()),
            \and{SortS{}}(a{}(), \top{SortS{}}())
        ) [label{}("a-loop")]
    "#;

    const A_TO_BOTTOM: &str = r#"
        axiom{} \rewrites{SortS{}}(
            \and{SortS{}}(a{}(), \top{SortS{}}()),
            \bottom{SortS{}}()
        ) [label{}("a-to-bottom")]
    "#;

    fn modal_claim(mode: ReachabilityMode, left: &str, right: &str, trusted: bool) -> String {
        let modality = match mode {
            ReachabilityMode::OnePath => "weakExistsFinally",
            ReachabilityMode::AllPath => "weakAlwaysFinally",
        };
        let mode_label = match mode {
            ReachabilityMode::OnePath => "one",
            ReachabilityMode::AllPath => "all",
        };
        let attributes = if trusted {
            format!("label{{}}(\"{mode_label}-{left}-{right}\"), trusted{{}}()")
        } else {
            format!("label{{}}(\"{mode_label}-{left}-{right}\")")
        };
        format!(
            r#"claim{{}} \implies{{SortS{{}}}}(
                \and{{SortS{{}}}}(\top{{SortS{{}}}}(), {left}{{}}()),
                {modality}{{SortS{{}}}}(
                    \and{{SortS{{}}}}({right}{{}}(), \top{{SortS{{}}}}())
                )
            ) [{attributes}]"#
        )
    }

    #[test]
    fn bottom_rewrites_are_vacuous_unless_allowed() {
        for mode in [ReachabilityMode::OnePath, ReachabilityMode::AllPath] {
            let claims = modal_claim(mode, "a", "b", false);
            let definition = definition(A_TO_BOTTOM, &claims);
            let claim = &definition.reachability_claims()[0];

            let rejected =
                prove_claim(&definition, claim, ProofOptions::default(), &NoSolver).unwrap();
            assert_eq!(rejected.status, ProofStatus::Failed, "{rejected:#?}");
            assert!(matches!(
                rejected.leaves.as_slice(),
                [ProofLeaf {
                    depth: 1,
                    trace,
                    outcome: ProofLeafOutcome::Trivial,
                    ..
                }] if matches!(trace.as_slice(), [TraceEntry {
                    depth: 1,
                    kind: TraceKind::Rewrite,
                    label: None,
                    unique_id,
                }] if unique_id == "trivial")
            ));

            let allowed = prove_claim(
                &definition,
                claim,
                ProofOptions {
                    allow_vacuous: true,
                    ..ProofOptions::default()
                },
                &NoSolver,
            )
            .unwrap();
            assert_eq!(allowed.status, ProofStatus::Proven, "{allowed:#?}");
            assert!(matches!(
                allowed.leaves.as_slice(),
                [ProofLeaf {
                    depth: 1,
                    outcome: ProofLeafOutcome::Proven(ImplicationCondition {
                        predicates,
                        ..
                    }),
                    ..
                }] if predicates == &[crate::rule::Predicate::False]
            ));
        }
    }

    /// `a-to-bottom` has no result for `a`, but its sibling of the same priority takes `a` to
    /// `c`: every instance of `a` has a defined successor, so no instance ends in an undefined
    /// step, and the all-path claim holds without accepting vacuous branches.
    #[test]
    fn a_bottom_result_that_a_sibling_covers_is_not_a_leaf() {
        let rules = r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(a{}(), \top{SortS{}}()),
                \and{SortS{}}(b{}(), \bottom{SortS{}}())
            ) [label{}("a-to-bottom")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(a{}(), \top{SortS{}}()),
                c{}()
            ) [label{}("a-to-c")]
        "#;
        // The one-path step tries `a-to-bottom` first; its instances, which it leaves without a
        // result, are offered to `a-to-c`, which gives them one.
        for mode in [ReachabilityMode::AllPath, ReachabilityMode::OnePath] {
            let claims = modal_claim(mode, "a", "c", false);
            let definition = definition(rules, &claims);
            let claim = &definition.reachability_claims()[0];

            let proven = prove_claim(
                &definition,
                claim,
                ProofOptions {
                    max_counterexamples: 2,
                    ..ProofOptions::default()
                },
                &NoSolver,
            )
            .unwrap();
            assert_eq!(proven.status, ProofStatus::Proven, "{mode:?}: {proven:#?}");
            assert!(
                !proven
                    .leaves
                    .iter()
                    .any(|leaf| matches!(leaf.outcome, ProofLeafOutcome::Trivial)),
                "{mode:?}: {proven:#?}"
            );
        }
    }

    /// A bottom result is offered only to the rules of its own priority: a lower-priority rule
    /// is blocked where the bottom rule applies, so the one-path claim fails as the all-path
    /// claim does.
    #[test]
    fn a_bottom_result_is_not_offered_to_a_lower_priority() {
        let rules = r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(a{}(), \top{SortS{}}()),
                \and{SortS{}}(b{}(), \bottom{SortS{}}())
            ) [label{}("a-to-bottom")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(a{}(), \top{SortS{}}()),
                c{}()
            ) [label{}("a-to-c"), priority{}("60")]
        "#;
        for mode in [ReachabilityMode::AllPath, ReachabilityMode::OnePath] {
            let claims = modal_claim(mode, "a", "c", false);
            let definition = definition(rules, &claims);
            let claim = &definition.reachability_claims()[0];
            let failed =
                prove_claim(&definition, claim, ProofOptions::default(), &NoSolver).unwrap();
            assert_eq!(failed.status, ProofStatus::Failed, "{mode:?}: {failed:#?}");
            assert!(
                matches!(
                    failed.leaves.as_slice(),
                    [ProofLeaf {
                        outcome: ProofLeafOutcome::Trivial,
                        ..
                    }]
                ),
                "{mode:?}: {failed:#?}"
            );
        }
    }

    #[test]
    fn smt_unsat_state_after_a_step_is_vacuous() {
        let rules = r#"
            symbol opaque{}() : SortS{} [function{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    a{}(),
                    \equals{SortS{}, SortS{}}(opaque{}(), a{}())
                ),
                b{}()
            ) [label{}("a-to-b-under-opaque-condition")]
        "#;
        let claims = modal_claim(ReachabilityMode::AllPath, "a", "c", false);
        let definition = definition(rules, &claims);
        let claim = &definition.reachability_claims()[0];

        let rejected = prove_claim(
            &definition,
            claim,
            ProofOptions::default(),
            &NonemptyUnsatSolver,
        )
        .unwrap();
        assert_eq!(rejected.status, ProofStatus::Failed, "{rejected:#?}");
        assert!(matches!(
            rejected.leaves.as_slice(),
            [ProofLeaf {
                depth: 1,
                outcome: ProofLeafOutcome::Vacuous,
                ..
            }]
        ));

        let allowed = prove_claim(
            &definition,
            claim,
            ProofOptions {
                allow_vacuous: true,
                ..ProofOptions::default()
            },
            &NonemptyUnsatSolver,
        )
        .unwrap();
        assert_eq!(allowed.status, ProofStatus::Proven, "{allowed:#?}");
        assert!(matches!(
            allowed.leaves.as_slice(),
            [ProofLeaf {
                depth: 1,
                outcome: ProofLeafOutcome::Proven(ImplicationCondition {
                    predicates,
                    ..
                }),
                ..
            }] if predicates == &[crate::rule::Predicate::False]
        ));
    }

    #[test]
    fn inconsistent_antecedent_is_accepted_at_depth_zero_including_smt_unsat() {
        let claims = r#"
            claim{} \implies{SortS{}}(
                \and{SortS{}}(\bottom{SortS{}}(), a{}()),
                weakAlwaysFinally{SortS{}}(
                    \and{SortS{}}(b{}(), \top{SortS{}}())
                )
            ) [label{}("false-antecedent")]
        "#;
        let syntactic_definition = definition("", claims);
        let claim = &syntactic_definition.reachability_claims()[0];

        let result = prove_claim(
            &syntactic_definition,
            claim,
            ProofOptions::default(),
            &NoSolver,
        )
        .unwrap();

        assert_eq!(result.status, ProofStatus::Proven);
        assert!(matches!(
            result.leaves.as_slice(),
            [ProofLeaf {
                outcome: ProofLeafOutcome::Proven(ImplicationCondition { predicates, .. }),
                ..
            }] if predicates == &[crate::rule::Predicate::False]
        ));

        let claims = r#"
            claim{} \implies{SortS{}}(
                \and{SortS{}}(
                    a{}(),
                    \equals{SortS{}, SortS{}}(opaque{}(), a{}())
                ),
                weakAlwaysFinally{SortS{}}(b{}())
            ) [label{}("smt-unsat-antecedent")]
        "#;
        let definition = definition("symbol opaque{}() : SortS{} [function{}()]", claims);
        let result = prove_claim(
            &definition,
            claim_with_label(&definition, "smt-unsat-antecedent"),
            ProofOptions::default(),
            &NonemptyUnsatSolver,
        )
        .unwrap();

        assert_eq!(result.status, ProofStatus::Proven, "{result:#?}");
        assert!(matches!(
            result.leaves.as_slice(),
            [ProofLeaf {
                depth: 0,
                outcome: ProofLeafOutcome::Proven(ImplicationCondition {
                    predicates,
                    ..
                }),
                ..
            }] if predicates == &[crate::rule::Predicate::False]
        ));
    }

    /// The proven `\bottom` leaf of an empty claim left-hand side.
    fn is_vacuous_proof(outcome: &ProofLeafOutcome) -> bool {
        matches!(
            outcome,
            ProofLeafOutcome::Proven(ImplicationCondition { predicates, .. })
                if predicates == &[crate::rule::Predicate::False]
        )
    }

    /// A state of the given origin, depth and trace over `a{}()`, with the constraint `\bottom`.
    fn empty_state(
        definition: &BackendDefinition,
        origin: StateOrigin,
        depth: u64,
        trace: Vec<TraceEntry>,
    ) -> ProofState {
        let mut state = ProofState::initial(Pattern {
            term: term(definition, "a{}()"),
            constraints: vec![crate::rule::Predicate::False],
        });
        state.origin = origin;
        state.depth = depth;
        state.trace = trace;
        state
    }

    /// An empty state's verdict is a function of what the state is, never of its depth or of the
    /// equations and splits its trace reports (CS-10-1). The claim's left-hand side is proven
    /// whatever its normalization recorded; a successor is rejected unless vacuous results are
    /// allowed; a split part is no leaf, so a split at depth 0 with an empty trace is never taken
    /// for the left-hand side and proven.
    #[test]
    fn vacuous_outcome_is_decided_by_the_state_origin_not_its_trace() {
        let definition = definition("", "");
        let simplification = TraceEntry {
            depth: 0,
            kind: TraceKind::Simplification,
            label: None,
            unique_id: "some-equation".into(),
        };
        for allow_vacuous in [false, true] {
            let options = ProofOptions {
                allow_vacuous,
                ..ProofOptions::default()
            };
            for depth in [0, 1] {
                for trace in [Vec::new(), vec![simplification.clone()]] {
                    let label = format!("allow_vacuous {allow_vacuous}, depth {depth}, {trace:?}");
                    let outcome = |origin| {
                        vacuous_outcome(
                            &empty_state(&definition, origin, depth, trace.clone()),
                            options,
                            ProofLeafOutcome::Vacuous,
                        )
                    };
                    assert!(
                        outcome(StateOrigin::Initial)
                            .is_some_and(|outcome| is_vacuous_proof(&outcome)),
                        "{label}"
                    );
                    let successor = outcome(StateOrigin::Successor).expect("a successor is a leaf");
                    if allow_vacuous {
                        assert!(is_vacuous_proof(&successor), "{label}: {successor:?}");
                    } else {
                        assert_eq!(successor, ProofLeafOutcome::Vacuous, "{label}");
                    }
                    assert_eq!(outcome(StateOrigin::Split), None, "{label}");
                }
            }
        }
    }

    /// Externalising a leaf normalizes it for display, which may apply equations and show the
    /// leaf empty; the empty leaf takes the outcome its origin gives, however the trace grew. A
    /// depth-bound left-hand side (`--depth 0`) shown empty there is proven, not `Vacuous`.
    #[test]
    fn an_externalised_empty_leaf_takes_the_outcome_of_its_origin() {
        let definition = definition(
            r#"
            symbol f{}() : SortS{} [function{}(), total{}()]
            axiom{R} \implies{R}(\top{R}(), \equals{SortS{}, R}(
                f{}(), \and{SortS{}}(a{}(), \top{SortS{}}())
            )) [label{}("f-is-a"), simplification{}()]
            "#,
            "",
        );
        let normalized = TraceEntry {
            depth: 0,
            kind: TraceKind::Simplification,
            label: None,
            unique_id: "f-is-a".into(),
        };
        for allow_vacuous in [false, true] {
            let options = ProofOptions {
                allow_vacuous,
                ..ProofOptions::default()
            };
            let externalise = |origin| {
                let mut state = empty_state(&definition, origin, 0, vec![normalized.clone()]);
                state.pattern.term = term(&definition, "f{}()");
                externalise_leaf(
                    &definition,
                    state,
                    ProofLeafOutcome::DepthBound,
                    options,
                    &NoSolver,
                )
            };
            let initial = externalise(StateOrigin::Initial).expect("the left-hand side is a leaf");
            assert!(is_vacuous_proof(&initial.outcome), "{initial:#?}");
            assert_eq!(initial.depth, 0);
            let successor = externalise(StateOrigin::Successor).expect("a successor is a leaf");
            if allow_vacuous {
                assert!(is_vacuous_proof(&successor.outcome), "{successor:#?}");
            } else {
                assert_eq!(
                    successor.outcome,
                    ProofLeafOutcome::Vacuous,
                    "{successor:#?}"
                );
            }
            assert!(externalise(StateOrigin::Split).is_none());
        }
    }

    /// `f() ∧ opaque() = a()` denotes no configuration when the solver refutes its constraint, so
    /// the claim holds vacuously, as `a() ∧ opaque() = a()` does in
    /// `inconsistent_antecedent_is_accepted_at_depth_zero_including_smt_unsat`. Normalizing the
    /// left-hand side applies `f() = a()` before the solver is asked, which records the equation
    /// in the trace; an equality changes no configuration the state denotes, so the verdict is
    /// the same (CS-10-1).
    #[test]
    fn an_initial_state_normalized_by_an_equation_and_refuted_by_smt_is_proven() {
        let claims = r#"
            claim{} \implies{SortS{}}(
                \and{SortS{}}(
                    f{}(),
                    \equals{SortS{}, SortS{}}(opaque{}(), a{}())
                ),
                weakAlwaysFinally{SortS{}}(b{}())
            ) [label{}("normalized-smt-unsat-antecedent")]
        "#;
        let definition = definition(
            r#"
            symbol opaque{}() : SortS{} [function{}()]
            symbol f{}() : SortS{} [function{}(), total{}()]
            axiom{R} \implies{R}(\top{R}(), \equals{SortS{}, R}(
                f{}(), \and{SortS{}}(a{}(), \top{SortS{}}())
            )) [label{}("f-is-a"), simplification{}()]
            "#,
            claims,
        );
        let claim = claim_with_label(&definition, "normalized-smt-unsat-antecedent");
        for allow_vacuous in [false, true] {
            let result = prove_claim(
                &definition,
                claim,
                ProofOptions {
                    allow_vacuous,
                    ..ProofOptions::default()
                },
                &NonemptyUnsatSolver,
            )
            .unwrap();
            assert_eq!(result.status, ProofStatus::Proven, "{result:#?}");
            let [leaf] = result.leaves.as_slice() else {
                panic!("expected one leaf, found {result:#?}");
            };
            assert_eq!(leaf.depth, 0, "{result:#?}");
            assert!(is_vacuous_proof(&leaf.outcome), "{result:#?}");
            // The case the test is about: the left-hand side's normalization applied an equation.
            assert!(
                leaf.trace
                    .iter()
                    .any(|entry| entry.kind == TraceKind::Simplification),
                "{result:#?}"
            );
        }
    }

    /// Refutes every query that holds a negation, anywhere in a conjunction, and finds every
    /// condition contingent: the complement of a destination's or a rule's condition is empty,
    /// while the condition itself is not decided.
    struct ComplementUnsatSolver;

    fn holds_a_negation(predicate: &crate::rule::Predicate) -> bool {
        match predicate {
            crate::rule::Predicate::Not(_) => true,
            crate::rule::Predicate::And(conjuncts) => conjuncts.iter().any(holds_a_negation),
            _ => false,
        }
    }

    impl SmtSolver for ComplementUnsatSolver {
        fn is_sat(
            &self,
            predicates: &[crate::rule::Predicate],
            _substitution: &Substitution,
        ) -> Stoppable<Result<Satisfiability, SmtError>> {
            Ok(Ok(if predicates.iter().any(holds_a_negation) {
                Satisfiability::Unsat
            } else {
                Satisfiability::Sat
            }))
        }

        fn check_predicates(
            &self,
            _known: &[crate::rule::Predicate],
            _substitution: &Substitution,
            _checked: &[crate::rule::Predicate],
        ) -> Stoppable<Result<Validity, SmtError>> {
            Ok(Ok(Validity::Contingent))
        }
    }

    /// `a()` reaches `a() ∧ opaque() = a()` where the destination's condition holds, and the
    /// solver shows its complement empty: the destination covers every configuration of `a()`.
    /// The part it does not cover is empty and is no state to step or to leave stuck; the claim
    /// is proven by the covered state (CS-10-1).
    #[test]
    fn an_empty_uncovered_destination_part_leaves_the_state_proven() {
        let claims = r#"
            claim{} \implies{SortS{}}(
                \and{SortS{}}(a{}(), \top{SortS{}}()),
                weakAlwaysFinally{SortS{}}(
                    \and{SortS{}}(a{}(), \equals{SortS{}, SortS{}}(opaque{}(), a{}()))
                )
            ) [label{}("contingent-destination")]
        "#;
        let definition = definition(
            "symbol opaque{}() : SortS{} [function{}(), total{}()]",
            claims,
        );
        let claim = claim_with_label(&definition, "contingent-destination");
        for allow_vacuous in [false, true] {
            let result = prove_claim(
                &definition,
                claim,
                ProofOptions {
                    allow_vacuous,
                    ..ProofOptions::default()
                },
                &ComplementUnsatSolver,
            )
            .unwrap();
            let label = format!("allow_vacuous {allow_vacuous}");
            assert_eq!(result.status, ProofStatus::Proven, "{label}: {result:#?}");
            assert!(
                result
                    .leaves
                    .iter()
                    .all(|leaf| matches!(leaf.outcome, ProofLeafOutcome::Proven(_))
                        && !is_vacuous_proof(&leaf.outcome)),
                "{label}: {result:#?}"
            );
        }
    }

    /// Answers the first query that holds a negation `Sat`, and refutes every later one; every
    /// condition is contingent. It stands for a solver whose first answer about a split part
    /// came from a translation too weak to refute it, while a later normalization shows it
    /// empty.
    #[derive(Default)]
    struct LateComplementUnsatSolver {
        negations: std::sync::atomic::AtomicUsize,
    }

    impl SmtSolver for LateComplementUnsatSolver {
        fn is_sat(
            &self,
            predicates: &[crate::rule::Predicate],
            _substitution: &Substitution,
        ) -> Stoppable<Result<Satisfiability, SmtError>> {
            if !predicates.iter().any(holds_a_negation) {
                return Ok(Ok(Satisfiability::Sat));
            }
            let earlier = self
                .negations
                .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            Ok(Ok(if earlier == 0 {
                Satisfiability::Sat
            } else {
                Satisfiability::Unsat
            }))
        }

        fn check_predicates(
            &self,
            _known: &[crate::rule::Predicate],
            _substitution: &Substitution,
            _checked: &[crate::rule::Predicate],
        ) -> Stoppable<Result<Validity, SmtError>> {
            Ok(Ok(Validity::Contingent))
        }
    }

    /// The rule takes `a()` to `b()` where `opaque() = a()`; the step keeps the part where the
    /// condition fails, `a() ∧ ¬(opaque() = a())`, on a `Sat` answer, and that part is shown
    /// empty only at the next state's normalization. Then the rule took every configuration of
    /// `a()`: the empty part is no path whose conditions contradict each other, so it is no
    /// `Vacuous` leaf, and the claim is proven by the rule's successor (CS-10-1).
    #[test]
    fn a_rewrite_remainder_shown_empty_later_is_no_vacuous_leaf() {
        let rules = r#"
            symbol opaque{}() : SortS{} [function{}(), total{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    a{}(),
                    \equals{SortS{}, SortS{}}(opaque{}(), a{}())
                ),
                b{}()
            ) [label{}("a-to-b-under-opaque-condition")]
        "#;
        let claims = modal_claim(ReachabilityMode::AllPath, "a", "b", false);
        let definition = definition(rules, &claims);
        let claim = &definition.reachability_claims()[0];
        for allow_vacuous in [false, true] {
            let result = prove_claim(
                &definition,
                claim,
                ProofOptions {
                    allow_vacuous,
                    ..ProofOptions::default()
                },
                &LateComplementUnsatSolver::default(),
            )
            .unwrap();
            assert_eq!(result.status, ProofStatus::Proven, "{result:#?}");
            assert!(
                !result
                    .leaves
                    .iter()
                    .any(|leaf| is_vacuous_proof(&leaf.outcome)
                        || leaf.outcome == ProofLeafOutcome::Vacuous),
                "{result:#?}"
            );
        }
    }

    #[test]
    fn proves_direct_and_rewritten_reachability() {
        let claims = [
            modal_claim(ReachabilityMode::OnePath, "a", "a", false),
            modal_claim(ReachabilityMode::OnePath, "a", "b", false),
        ]
        .join("\n");
        let definition = definition(A_TO_B, &claims);

        let direct = prove_claim(
            &definition,
            claim_with_label(&definition, "one-a-a"),
            ProofOptions::default(),
            &NoSolver,
        )
        .unwrap();
        let rewritten = prove_claim(
            &definition,
            claim_with_label(&definition, "one-a-b"),
            ProofOptions::default(),
            &NoSolver,
        )
        .unwrap();

        assert_eq!(direct.status, ProofStatus::Proven);
        assert_eq!(direct.leaves[0].depth, 0);
        assert_eq!(rewritten.status, ProofStatus::Proven);
        assert_eq!(rewritten.leaves[0].depth, 1);
    }

    fn optional_indeterminate_claims(
        extra_rules: &str,
        include_applicable_claim: bool,
    ) -> BackendDefinition {
        let rules = format!(
            r#"
            symbol opaque{{}}() : SortS{{}} [function{{}}()]
            axiom{{}} \rewrites{{SortS{{}}}}(
                \and{{SortS{{}}}}(a{{}}(), \top{{SortS{{}}}}()),
                b{{}}()
            ) [label{{}}("a-to-b")]
            {extra_rules}
            "#
        );
        let applicable = if include_applicable_claim {
            r#"
            claim{} \implies{SortS{}}(
                \and{SortS{}}(
                    b{}(),
                    \and{SortS{}}(\top{SortS{}}(), \top{SortS{}}())
                ),
                weakAlwaysFinally{SortS{}}(c{}())
            ) [label{}("applicable-third"), trusted{}()]
            "#
        } else {
            ""
        };
        let claims = format!(
            r#"
            claim{{}} \implies{{SortS{{}}}}(
                \and{{SortS{{}}}}(a{{}}(), \top{{SortS{{}}}}()),
                weakAlwaysFinally{{SortS{{}}}}(c{{}}())
            ) [label{{}}("main")]
            claim{{}} \implies{{SortS{{}}}}(
                \and{{SortS{{}}}}(
                    b{{}}(),
                    \equals{{SortS{{}}, SortS{{}}}}(opaque{{}}(), a{{}}())
                ),
                weakAlwaysFinally{{SortS{{}}}}(c{{}}())
            ) [label{{}}("indeterminate-second"), trusted{{}}()]
            {applicable}
            "#
        );
        definition(&rules, &claims)
    }

    #[test]
    fn later_applicable_claim_wins_over_an_indeterminate_candidate() {
        let definition = optional_indeterminate_claims("", true);

        let result = prove_claim(
            &definition,
            claim_with_label(&definition, "main"),
            ProofOptions::default(),
            &NoSolver,
        )
        .unwrap();

        assert_eq!(result.status, ProofStatus::Proven, "{result:#?}");
        assert!(result.leaves.iter().any(|leaf| {
            leaf.trace.iter().any(|entry| {
                entry.kind == TraceKind::Claim
                    && entry.label.as_deref() == Some("indeterminate-second")
            })
        }));
        assert!(result.leaves.iter().any(|leaf| {
            leaf.trace.iter().any(|entry| {
                entry.kind == TraceKind::Claim && entry.label.as_deref() == Some("applicable-third")
            })
        }));
    }

    #[test]
    fn ordinary_rewriting_continues_past_an_indeterminate_claim() {
        let definition = optional_indeterminate_claims(
            r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(b{}(), \top{SortS{}}()),
                c{}()
            ) [label{}("b-to-c")]
            "#,
            false,
        );

        let result = prove_claim(
            &definition,
            claim_with_label(&definition, "main"),
            ProofOptions::default(),
            &NoSolver,
        )
        .unwrap();

        assert_eq!(result.status, ProofStatus::Proven, "{result:#?}");
        assert!(result.leaves.iter().any(|leaf| {
            leaf.trace
                .iter()
                .any(|entry| entry.label.as_deref() == Some("b-to-c"))
        }));
    }

    #[test]
    fn undecidable_claim_requires_splits_covered_and_stuck_remainder() {
        let definition = optional_indeterminate_claims("", false);

        let result = prove_claim(
            &definition,
            claim_with_label(&definition, "main"),
            ProofOptions::default(),
            &NoSolver,
        )
        .unwrap();

        let requires = crate::rule::Predicate::Equals(
            term(&definition, "opaque{}()"),
            term(&definition, "a{}()"),
        );
        // `opaque()` is partial, and the equality with the defined `a()` is `⊥` where it is
        // undefined, so the instantiated requires is stated as `⌈opaque()⌉ ∧ opaque() = a()`
        // (I1): the equality already implies `⌈opaque()⌉`, so this is the same condition.
        let definedness = crate::rule::Predicate::Ceil(term(&definition, "opaque{}()"));
        let condition =
            crate::rule::Predicate::And(vec![definedness.clone(), requires.clone()].into());
        // The stuck `b()` carries `¬(⌈opaque()⌉ ∧ opaque() = a())`, whose satisfiability rests on
        // the abstracted `opaque()`: the leaf fails the claim without certifying a refutation.
        assert_eq!(result.status, ProofStatus::Failed, "{result:#?}");
        assert!(
            result.leaves.iter().any(|leaf| {
                leaf.pattern.term == term(&definition, "c{}()")
                    && leaf.pattern.constraints.contains(&requires)
                    && leaf.pattern.constraints.contains(&definedness)
                    && matches!(leaf.outcome, ProofLeafOutcome::Proven(_))
                    && leaf.trace.iter().any(|entry| {
                        entry.kind == TraceKind::Claim
                            && entry.label.as_deref() == Some("indeterminate-second")
                    })
            }),
            "{result:#?}"
        );
        assert!(result.leaves.iter().any(|leaf| {
            leaf.pattern.term == term(&definition, "b{}()")
                && leaf
                    .pattern
                    .constraints
                    .contains(&crate::rule::Predicate::Not(Arc::new(condition.clone())))
                && matches!(leaf.outcome, ProofLeafOutcome::Stuck)
                && leaf
                    .trace
                    .iter()
                    .any(|entry| entry.kind == TraceKind::Remainder)
        }));
        assert_eq!(result.explored_states, 4);
        assert_eq!(result.unexplored_states, 0);
    }

    #[test]
    fn reports_stuck_and_depth_bounded_claims_separately() {
        let claims = modal_claim(ReachabilityMode::AllPath, "a", "b", false);
        let stuck_definition = definition("", &claims);
        let bounded_definition = definition(A_TO_B, &claims);

        let stuck = prove_claim(
            &stuck_definition,
            &stuck_definition.reachability_claims()[0],
            ProofOptions::default(),
            &NoSolver,
        )
        .unwrap();
        let bounded = prove_claim(
            &bounded_definition,
            &bounded_definition.reachability_claims()[0],
            ProofOptions {
                max_depth: 0,
                ..ProofOptions::default()
            },
            &NoSolver,
        )
        .unwrap();

        assert_eq!(stuck.status, ProofStatus::Disproved);
        assert_eq!(bounded.status, ProofStatus::DepthBound);
    }

    /// Cancels the request at its first query and polls for a stop before answering, as a
    /// solver polls before each attempt, so under the cancelled request that query and every
    /// later one return the cancellation's stop.
    struct CancellingSolver(crate::stop::CancellationToken);

    impl SmtSolver for CancellingSolver {
        fn is_sat(
            &self,
            _predicates: &[crate::rule::Predicate],
            _substitution: &Substitution,
        ) -> Stoppable<Result<Satisfiability, SmtError>> {
            self.0.cancel();
            crate::stop::check()?;
            Ok(Ok(Satisfiability::Sat))
        }

        fn check_predicates(
            &self,
            _known: &[crate::rule::Predicate],
            _substitution: &Substitution,
            _checked: &[crate::rule::Predicate],
        ) -> Stoppable<Result<Validity, SmtError>> {
            self.0.cancel();
            crate::stop::check()?;
            Ok(Ok(Validity::Contingent))
        }
    }

    #[test]
    fn a_cancelled_request_ends_the_proof_and_names_the_stop_once() {
        let claims = modal_claim(ReachabilityMode::OnePath, "a", "a", false);
        let definition = definition("", &claims);
        let claim = claim_with_label(&definition, "one-a-a");

        // Cancelled before the proof starts: the loop head observes it.
        let token = crate::stop::CancellationToken::new();
        token.cancel();
        let before = token
            .scope(|| prove_claim(&definition, claim, ProofOptions::default(), &NoSolver))
            .unwrap();
        // Cancelled by the solver during the state's step: the poll after the phase observes it.
        let token = crate::stop::CancellationToken::new();
        let during = token
            .scope(|| {
                prove_claim(
                    &definition,
                    claim,
                    ProofOptions::default(),
                    &CancellingSolver(token.clone()),
                )
            })
            .unwrap();

        for (result, explored) in [(&before, 0), (&during, 1)] {
            // The stop is named once, with its cause, by the result: the state being explored
            // stays unexplored and is no leaf, so no verdict is taken from its missing answer.
            assert_eq!(result.stopped, Some(StopCause::Cancelled), "{result:#?}");
            assert!(result.leaves.is_empty(), "{result:#?}");
            assert_eq!(result.explored_states, explored, "{result:#?}");
            assert_eq!(result.unexplored_states, 1, "{result:#?}");
            assert_eq!(result.status, ProofStatus::Indeterminate, "{result:#?}");
        }
    }

    /// Answers every query as satisfiable or contingent until its `at`-th query, where it cancels
    /// the request; it polls for a stop before answering, as a solver polls before each attempt,
    /// so under the cancelled request that query and every later one return the cancellation's
    /// stop. Counts the queries it was asked.
    struct CancelAtQuery {
        token: crate::stop::CancellationToken,
        at: usize,
        queries: std::sync::atomic::AtomicUsize,
    }

    impl CancelAtQuery {
        fn new(token: crate::stop::CancellationToken, at: usize) -> Self {
            Self {
                token,
                at,
                queries: std::sync::atomic::AtomicUsize::new(0),
            }
        }

        /// Counts this query, cancelling the request from the `at`-th on, and polls for a stop.
        fn poll(&self) -> Stoppable<()> {
            let query = self
                .queries
                .fetch_add(1, std::sync::atomic::Ordering::SeqCst)
                + 1;
            if query >= self.at {
                self.token.cancel();
            }
            crate::stop::check()
        }
    }

    impl SmtSolver for CancelAtQuery {
        fn is_sat(
            &self,
            _predicates: &[crate::rule::Predicate],
            _substitution: &Substitution,
        ) -> Stoppable<Result<Satisfiability, SmtError>> {
            self.poll()?;
            Ok(Ok(Satisfiability::Sat))
        }

        fn check_predicates(
            &self,
            _known: &[crate::rule::Predicate],
            _substitution: &Substitution,
            _checked: &[crate::rule::Predicate],
        ) -> Stoppable<Result<Validity, SmtError>> {
            self.poll()?;
            Ok(Ok(Validity::Contingent))
        }
    }

    /// `state(f(X), f(Y))`, where `f(Z) = Z` only under `Z >Int 0`: simplifying the state asks
    /// the solver about that condition for each argument in turn, and the simplifier polls the
    /// cancellation between them. So every normalisation of a leaf's pattern queries the solver
    /// and then polls, and a cancellation raised by its first query ends it.
    fn refined_leaf_definition(rules: &str, destination: &str) -> BackendDefinition {
        let source = format!(
            r#"[]
            module MAIN
                hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
                hooked-sort SortBool{{}} [hook{{}}("BOOL.Bool"), hasDomainValues{{}}()]
                sort SortState{{}} []
                symbol state{{}}(SortInt{{}}, SortInt{{}}) : SortState{{}} [constructor{{}}()]
                symbol done{{}}() : SortState{{}} [constructor{{}}()]
                symbol f{{}}(SortInt{{}}) : SortInt{{}} [function{{}}()]
                hooked-symbol gtInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
                    [function{{}}(), total{{}}(), hook{{}}("INT.gt"), smt-hook{{}}(">")]
                alias {destination}{{S}}(S) : S
                    where {destination}{{S}}(@X:S) := @X:S []
                axiom{{R}} \implies{{R}}(
                    \and{{R}}(
                        \equals{{SortBool{{}}, R}}(
                            gtInt{{}}(X0:SortInt{{}}, \dv{{SortInt{{}}}}("0")),
                            \dv{{SortBool{{}}}}("true")
                        ),
                        \and{{R}}(\in{{SortInt{{}}, R}}(X0:SortInt{{}}, Z:SortInt{{}}), \top{{R}}())
                    ),
                    \equals{{SortInt{{}}, R}}(
                        f{{}}(X0:SortInt{{}}),
                        \and{{SortInt{{}}}}(Z:SortInt{{}}, \top{{SortInt{{}}}}())
                    )
                ) [label{{}}("f-positive")]
                {rules}
                claim{{}} \implies{{SortState{{}}}}(
                    \and{{SortState{{}}}}(
                        \top{{SortState{{}}}}(),
                        state{{}}(f{{}}(X:SortInt{{}}), f{{}}(Y:SortInt{{}}))
                    ),
                    {destination}{{SortState{{}}}}(
                        \and{{SortState{{}}}}(done{{}}(), \top{{SortState{{}}}}())
                    )
                ) [label{{}}("refined")]
            endmodule []"#
        );
        let syntax = parse_definition(&source).expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    #[test]
    fn a_cancellation_during_a_decided_leafs_refinement_is_named_once_by_the_result() {
        const TWO_SUCCESSORS: &str = r#"
            axiom{} \rewrites{SortState{}}(
                \and{SortState{}}(state{}(X:SortInt{}, Y:SortInt{}), \top{SortState{}}()),
                \and{SortState{}}(state{}(Y:SortInt{}, X:SortInt{}), \top{SortState{}}())
            ) [label{}("swap")]
            axiom{} \rewrites{SortState{}}(
                \and{SortState{}}(state{}(X:SortInt{}, Y:SortInt{}), \top{SortState{}}()),
                \and{SortState{}}(state{}(X:SortInt{}, X:SortInt{}), \top{SortState{}}())
            ) [label{}("copy")]
        "#;
        // Each proof ends with an empty frontier after its last leaf was refined: a `DepthBound`
        // leaf (the exit after the loop), a `Stuck` leaf normalised and then certified, and the
        // `BreadthBound` leaves of the two successors that exceed the breadth limit.
        let no_rules = refined_leaf_definition("", "weakExistsFinally");
        let breadth_bound = refined_leaf_definition(TWO_SUCCESSORS, "weakAlwaysFinally");
        let cases = [
            (
                "depth bound",
                &no_rules,
                ProofOptions {
                    max_depth: 0,
                    ..ProofOptions::default()
                },
                ProofLeafOutcome::DepthBound,
            ),
            (
                "stuck",
                &no_rules,
                ProofOptions::default(),
                ProofLeafOutcome::Stuck,
            ),
            (
                "breadth bound",
                &breadth_bound,
                ProofOptions {
                    breadth_limit: Some(1),
                    ..ProofOptions::default()
                },
                ProofLeafOutcome::BreadthBound,
            ),
        ];
        for (name, definition, options, decided) in cases {
            let claim = claim_with_label(definition, "refined");
            let uncancelled = CancelAtQuery::new(crate::stop::CancellationToken::new(), usize::MAX);
            let complete = prove_claim(definition, claim, options, &uncancelled).unwrap();
            assert_eq!(complete.stopped, None, "{name}: {complete:#?}");
            assert!(
                !complete.leaves.is_empty()
                    && complete.leaves.iter().all(|leaf| leaf.outcome == decided),
                "{name}: {complete:#?}"
            );
            let queries = uncancelled
                .queries
                .load(std::sync::atomic::Ordering::SeqCst);
            // Cancel at every query the proof makes, so that some cancellation arrives while a
            // leaf whose outcome is decided is being refined.
            let mut cancelled_after_a_decision = 0;
            for at in 1..=queries {
                let token = crate::stop::CancellationToken::new();
                let solver = CancelAtQuery::new(token.clone(), at);
                let result = token
                    .scope(|| prove_claim(definition, claim, options, &solver))
                    .unwrap();
                // The stop is named once, by the result, whether states remain or not; a leaf
                // keeps the outcome decided before the cancellation arrived.
                assert_eq!(
                    result.stopped,
                    Some(StopCause::Cancelled),
                    "{name}, cancelled at query {at}: {result:#?}"
                );
                assert!(
                    result.leaves.iter().all(|leaf| leaf.outcome == decided),
                    "{name}, cancelled at query {at}: {result:#?}"
                );
                assert_ne!(result.status, ProofStatus::Proven, "{name}: {result:#?}");
                if !result.leaves.is_empty() {
                    cancelled_after_a_decision += 1;
                }
            }
            assert!(cancelled_after_a_decision > 0, "{name}: {queries} queries");
        }
    }

    /// `pair(Int, Int)` with `f(Z) = Z` only under `Z >Int 0`, so that simplifying `f(X)` asks the
    /// solver about `X >Int 0` and then polls for a stop.
    fn conditional_identity_definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                sort SortState{} []
                symbol pair{}(SortInt{}, SortInt{}) : SortState{} [constructor{}()]
                symbol f{}(SortInt{}) : SortInt{} [function{}()]
                hooked-symbol gtInt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.gt"), smt-hook{}(">")]
                axiom{R} \implies{R}(
                    \and{R}(
                        \equals{SortBool{}, R}(
                            gtInt{}(X0:SortInt{}, \dv{SortInt{}}("0")),
                            \dv{SortBool{}}("true")
                        ),
                        \and{R}(\in{SortInt{}, R}(X0:SortInt{}, Z:SortInt{}), \top{R}())
                    ),
                    \equals{SortInt{}, R}(
                        f{}(X0:SortInt{}),
                        \and{SortInt{}}(Z:SortInt{}, \top{SortInt{}}())
                    )
                ) [label{}("f-positive")]
            endmodule []"#,
        )
        .expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    /// The remainder of a claim application is kept or pruned from an answer about it; a stop
    /// before that answer is returned with its cause, never taken for "satisfiable".
    #[test]
    fn a_stop_during_the_remainder_check_is_returned_instead_of_keeping_the_remainder() {
        let definition = conditional_identity_definition();
        let x = term(&definition, "X:SortInt{}");
        let negated = crate::rule::Predicate::Not(Arc::new(crate::rule::Predicate::Equals(
            term(&definition, "f{}(X:SortInt{})"),
            x,
        )));
        let options = SimplificationOptions::default();
        let check = || {
            remainder_is_unsatisfiable(&definition, &[], &negated, options, &NoSolver)
                .map_err(crate::stop::Stop::into_cause)
        };

        assert_eq!(check(), Ok(false));
        let token = crate::stop::CancellationToken::new();
        token.cancel();
        assert_eq!(token.scope(check), Err(StopCause::Cancelled));
    }

    /// `state(X)` with two rules of one priority: `positive` rewrites it to `done` where
    /// `X >Int 0`, and `undefined` rewrites it to `\bottom`. The step is a `Branch` with `done` as
    /// its successor and one trivial entry, whose instances `not (X >Int 0)` have an undefined
    /// step; `undefined_step_state` asks the solver whether that set is empty.
    fn undefined_step_definition() -> BackendDefinition {
        let source = r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                sort SortState{} []
                symbol state{}(SortInt{}) : SortState{} [constructor{}()]
                symbol done{}() : SortState{} [constructor{}()]
                hooked-symbol gtInt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.gt"), smt-hook{}(">")]
                alias weakAlwaysFinally{S}(S) : S
                    where weakAlwaysFinally{S}(@X:S) := @X:S []
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        state{}(X:SortInt{}),
                        \equals{SortBool{}, SortState{}}(
                            gtInt{}(X:SortInt{}, \dv{SortInt{}}("0")),
                            \dv{SortBool{}}("true")
                        )
                    ),
                    done{}()
                ) [label{}("positive")]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(state{}(X:SortInt{}), \top{SortState{}}()),
                    \bottom{SortState{}}()
                ) [label{}("undefined")]
                claim{} \implies{SortState{}}(
                    \and{SortState{}}(\top{SortState{}}(), state{}(X:SortInt{})),
                    weakAlwaysFinally{SortState{}}(
                        \and{SortState{}}(done{}(), \top{SortState{}}())
                    )
                ) [label{}("undefined-step")]
            endmodule []"#;
        let syntax = parse_definition(source).expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    /// Answers every query as satisfiable or contingent, except its first satisfiability query
    /// about a predicate that mentions `gtInt`, which stops: with `request`, it cancels that
    /// token, the request's, and polls for a stop, as a solver polls before each attempt;
    /// without, it returns a stop of its own that no later poll observes. Counts those queries.
    struct StopsAtBottomCheck {
        request: Option<crate::stop::CancellationToken>,
        stops: bool,
        bottom_checks: std::sync::atomic::AtomicUsize,
    }

    impl SmtSolver for StopsAtBottomCheck {
        fn is_sat(
            &self,
            predicates: &[crate::rule::Predicate],
            _substitution: &Substitution,
        ) -> Stoppable<Result<Satisfiability, SmtError>> {
            if format!("{predicates:?}").contains("gtInt")
                && self
                    .bottom_checks
                    .fetch_add(1, std::sync::atomic::Ordering::SeqCst)
                    == 0
                && self.stops
            {
                match &self.request {
                    Some(request) => request.cancel(),
                    None => {
                        let own = crate::stop::CancellationToken::new();
                        own.cancel();
                        own.scope(crate::stop::check)?;
                    }
                }
            }
            crate::stop::check()?;
            Ok(Ok(Satisfiability::Sat))
        }

        fn check_predicates(
            &self,
            _known: &[crate::rule::Predicate],
            _substitution: &Substitution,
            _checked: &[crate::rule::Predicate],
        ) -> Stoppable<Result<Validity, SmtError>> {
            crate::stop::check()?;
            Ok(Ok(Validity::Contingent))
        }
    }

    /// A stop of `undefined_step_state`'s bottom check (the site that read a cancelled query as
    /// "not bottom") leaves no `Trivial` leaf. The loop no longer re-reads the request's flag
    /// after the phase, so the check itself returns the stop: whether the request's token was
    /// cancelled before the check answered, or the check's query stopped for a cause no later
    /// poll observes.
    #[test]
    fn a_stop_before_the_undefined_step_bottom_check_leaves_no_trivial_leaf() {
        let definition = undefined_step_definition();
        let claim = claim_with_label(&definition, "undefined-step");
        let solver = |request, stops| StopsAtBottomCheck {
            request,
            stops,
            bottom_checks: std::sync::atomic::AtomicUsize::new(0),
        };

        // Control: the undefined instances are not shown empty, so they are a `Trivial` leaf;
        // their bottom check is the proof's only satisfiability query about `gtInt`.
        let unstopped = solver(None, false);
        let control = prove_claim(&definition, claim, ProofOptions::default(), &unstopped).unwrap();
        assert_eq!(control.stopped, None, "{control:#?}");
        assert!(
            control
                .leaves
                .iter()
                .any(|leaf| leaf.outcome == ProofLeafOutcome::Trivial),
            "{control:#?}"
        );
        assert_eq!(
            unstopped
                .bottom_checks
                .load(std::sync::atomic::Ordering::SeqCst),
            1
        );

        for request in [Some(crate::stop::CancellationToken::new()), None] {
            let token = request.clone().unwrap_or_default();
            let stopping = solver(request, true);
            let result = token
                .scope(|| prove_claim(&definition, claim, ProofOptions::default(), &stopping))
                .unwrap();
            assert_eq!(result.stopped, Some(StopCause::Cancelled), "{result:#?}");
            assert!(
                !result
                    .leaves
                    .iter()
                    .any(|leaf| leaf.outcome == ProofLeafOutcome::Trivial),
                "{result:#?}"
            );
            assert_eq!(result.status, ProofStatus::Indeterminate, "{result:#?}");
        }
    }

    /// Cancels the request at a query that mentions `gtInt` and polls for a stop before answering,
    /// as a solver polls before each attempt, so under the cancelled request that query and every
    /// later one return the cancellation's stop; answers every other query as satisfiable or
    /// contingent. Counts the `gtInt` queries.
    struct CancelOnCondition {
        token: crate::stop::CancellationToken,
        cancels: bool,
        condition_queries: std::sync::atomic::AtomicUsize,
    }

    impl CancelOnCondition {
        fn poll(&self, predicates: &[&[crate::rule::Predicate]]) -> Stoppable<()> {
            if format!("{predicates:?}").contains("gtInt") {
                self.condition_queries
                    .fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                if self.cancels {
                    self.token.cancel();
                }
            }
            crate::stop::check()
        }
    }

    impl SmtSolver for CancelOnCondition {
        fn is_sat(
            &self,
            predicates: &[crate::rule::Predicate],
            _substitution: &Substitution,
        ) -> Stoppable<Result<Satisfiability, SmtError>> {
            self.poll(&[predicates])?;
            Ok(Ok(Satisfiability::Sat))
        }

        fn check_predicates(
            &self,
            known: &[crate::rule::Predicate],
            _substitution: &Substitution,
            checked: &[crate::rule::Predicate],
        ) -> Stoppable<Result<Validity, SmtError>> {
            self.poll(&[known, checked])?;
            Ok(Ok(Validity::Contingent))
        }
    }

    /// A cancellation that arrives inside the implication check reaches the check's result as a
    /// stop; the proof publishes it as `stopped`, as it does every cancellation, and does not
    /// fail with a `ProofError`. Only the destination's obligation `f(X) = X` mentions `gtInt`,
    /// so the solver cancels while the implication check simplifies that obligation.
    /// A claim whose constraints have no definedness-explicit form is refused, not proven, and
    /// keeps its refusal when it is renamed apart for an application as a circularity.
    #[test]
    fn a_refused_claim_is_not_proven_and_its_renaming_keeps_the_refusal() {
        let definition = conditional_identity_definition();
        let state = term(&definition, "pair{}(X:SortInt{}, Y:SortInt{})");
        let claim = ReachabilityClaim {
            lhs: Pattern {
                term: state.clone(),
                constraints: Vec::new(),
            },
            rhs: vec![Pattern {
                term: state.clone(),
                constraints: Vec::new(),
            }],
            existentials: BTreeSet::new(),
            mode: ReachabilityMode::AllPath,
            attributes: crate::claim::ClaimAttributes {
                label: Some("refused".into()),
                unique_id: "refused".into(),
                trusted: false,
                source: None,
                location: None,
                sentence: 0,
            },
            unstated: Some(crate::definition::UnstatedDefinedness::TermConjunction),
        };
        let refused = super::prove_claim(
            &definition,
            &claim,
            &[],
            ProofOptions::default(),
            &crate::smt::NoSolver,
        );
        assert!(
            matches!(
                refused,
                Err(ProofError::UnstatedDefinedness(
                    crate::definition::UnstatedDefinedness::TermConjunction
                ))
            ),
            "{refused:?}"
        );
        let subject = Pattern {
            term: state,
            constraints: Vec::new(),
        };
        let renamed = freshen_claim(&claim, &subject, &mut crate::fresh::FreshCounter::default());
        assert_eq!(renamed.unstated, claim.unstated);
    }

    #[test]
    fn a_cancellation_during_the_implication_check_is_published_as_the_proofs_stop() {
        let definition = conditional_identity_definition();
        let state = term(&definition, "pair{}(X:SortInt{}, Y:SortInt{})");
        let claim = ReachabilityClaim {
            lhs: Pattern {
                term: state.clone(),
                constraints: Vec::new(),
            },
            rhs: vec![Pattern {
                term: state,
                constraints: vec![crate::rule::Predicate::Equals(
                    term(&definition, "f{}(X:SortInt{})"),
                    term(&definition, "X:SortInt{}"),
                )],
            }],
            existentials: BTreeSet::new(),
            mode: ReachabilityMode::OnePath,
            attributes: crate::claim::ClaimAttributes {
                label: Some("conditional-identity".into()),
                unique_id: "conditional-identity".into(),
                trusted: false,
                source: None,
                location: None,
                sentence: 0,
            },
            unstated: None,
        };
        let prove = |cancels| {
            let token = crate::stop::CancellationToken::new();
            let solver = CancelOnCondition {
                token: token.clone(),
                cancels,
                condition_queries: std::sync::atomic::AtomicUsize::new(0),
            };
            let result = token.scope(|| {
                super::prove_claim(&definition, &claim, &[], ProofOptions::default(), &solver)
            });
            let queries = solver
                .condition_queries
                .load(std::sync::atomic::Ordering::SeqCst);
            (result, queries, token.is_cancelled())
        };

        let (uncancelled, queries, _) = prove(false);
        let uncancelled = uncancelled.expect("the uncancelled proof ends");
        assert_eq!(uncancelled.stopped, None, "{uncancelled:#?}");
        assert!(queries > 0, "the implication check asks about `gtInt`");

        let (cancelled, _, was_cancelled) = prove(true);
        assert!(was_cancelled);
        let cancelled = cancelled.expect("a cancellation is the proof's stop, not its error");
        assert_eq!(
            cancelled.stopped,
            Some(StopCause::Cancelled),
            "{cancelled:#?}"
        );
        assert!(cancelled.leaves.is_empty(), "{cancelled:#?}");
        assert_eq!(
            cancelled.status,
            ProofStatus::Indeterminate,
            "{cancelled:#?}"
        );
    }

    #[test]
    fn discards_a_proof_step_that_exceeds_its_manual_timeout() {
        let claims = modal_claim(ReachabilityMode::OnePath, "a", "a", false);
        let definition = definition("", &claims);

        let result = prove_claim(
            &definition,
            claim_with_label(&definition, "one-a-a"),
            ProofOptions {
                step_timeout: Some(Duration::from_millis(1)),
                ..ProofOptions::default()
            },
            &SlowSolver,
        )
        .unwrap();

        assert_eq!(result.status, ProofStatus::Indeterminate);
        assert!(matches!(
            result.leaves.as_slice(),
            [ProofLeaf {
                outcome: ProofLeafOutcome::Stopped(StopCause::Deadline(StepTimeoutMode::Manual(timeout))),
                ..
            }] if *timeout == Duration::from_millis(1)
        ));
        assert_eq!(
            result.stopped,
            Some(StopCause::Deadline(StepTimeoutMode::Manual(
                Duration::from_millis(1)
            )))
        );
    }

    #[test]
    fn interrupts_native_hook_evaluation_at_the_step_deadline() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                sort SortState{} []
                hooked-symbol pow{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), total{}(), hook{}("INT.pow")]
                symbol state{}(SortInt{}) : SortState{} [constructor{}()]
                symbol done{}() : SortState{} [constructor{}()]
                alias weakExistsFinally{S}(S) : S
                    where weakExistsFinally{S}(@X:S) := @X:S []
                claim{} \implies{SortState{}}(
                    \and{SortState{}}(
                        \top{SortState{}}(),
                        state{}(
                            pow{}(
                                \dv{SortInt{}}("2"),
                                \dv{SortInt{}}("10")
                            )
                        )
                    ),
                    weakExistsFinally{SortState{}}(
                        \and{SortState{}}(done{}(), \top{SortState{}}())
                    )
                ) [label{}("native-hook-timeout")]
            endmodule []"#,
        )
        .expect("native hook claim should parse");
        let definition = BackendDefinition::internalize(&syntax, "MAIN")
            .expect("native hook claim should internalize");

        let result = prove_claim(
            &definition,
            &definition.reachability_claims()[0],
            ProofOptions {
                step_timeout: Some(Duration::ZERO),
                ..ProofOptions::default()
            },
            &NoSolver,
        )
        .expect("timeout should be a proof outcome");

        assert_eq!(result.status, ProofStatus::Indeterminate);
        assert!(matches!(
            result.leaves.as_slice(),
            [ProofLeaf {
                outcome: ProofLeafOutcome::Stopped(StopCause::Deadline(StepTimeoutMode::Manual(timeout))),
                ..
            }] if timeout.is_zero()
        ));
        assert_eq!(
            result.stopped,
            Some(StopCause::Deadline(StepTimeoutMode::Manual(Duration::ZERO)))
        );
    }

    #[test]
    fn interrupts_an_equation_loop_at_the_step_deadline() {
        // `spin(a) = spin(b)` and `spin(b) = spin(a)` never reach a value and call no hook; with
        // no iteration bound only the step deadline ends the loop-head simplification.
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                sort SortT{} []
                sort SortState{} []
                symbol a{}() : SortT{} [constructor{}(), total{}()]
                symbol b{}() : SortT{} [constructor{}(), total{}()]
                symbol spin{}(SortT{}) : SortInt{} [function{}()]
                symbol state{}(SortInt{}) : SortState{} [constructor{}()]
                symbol done{}() : SortState{} [constructor{}()]
                alias weakExistsFinally{S}(S) : S
                    where weakExistsFinally{S}(@X:S) := @X:S []
                axiom{R} \implies{R}(
                    \and{R}(\top{R}(), \and{R}(\in{SortT{}, R}(X0:SortT{}, a{}()), \top{R}())),
                    \equals{SortInt{}, R}(spin{}(X0:SortT{}), \and{SortInt{}}(spin{}(b{}()), \top{SortInt{}}()))
                ) [label{}("spin-a")]
                axiom{R} \implies{R}(
                    \and{R}(\top{R}(), \and{R}(\in{SortT{}, R}(X0:SortT{}, b{}()), \top{R}())),
                    \equals{SortInt{}, R}(spin{}(X0:SortT{}), \and{SortInt{}}(spin{}(a{}()), \top{SortInt{}}()))
                ) [label{}("spin-b")]
                claim{} \implies{SortState{}}(
                    \and{SortState{}}(\top{SortState{}}(), state{}(spin{}(a{}()))),
                    weakExistsFinally{SortState{}}(
                        \and{SortState{}}(done{}(), \top{SortState{}}())
                    )
                ) [label{}("equation-loop-timeout")]
            endmodule []"#,
        )
        .expect("equation loop claim should parse");
        let definition = BackendDefinition::internalize(&syntax, "MAIN")
            .expect("equation loop claim should internalize");
        let step_timeout = Duration::from_millis(50);
        let (sender, receiver) = std::sync::mpsc::channel();
        thread::spawn(move || {
            let result = prove_claim(
                &definition,
                &definition.reachability_claims()[0],
                ProofOptions {
                    max_simplification_iterations: usize::MAX,
                    step_timeout: Some(step_timeout),
                    ..ProofOptions::default()
                },
                &NoSolver,
            );
            let _ = sender.send(result);
        });

        let result = receiver
            .recv_timeout(Duration::from_secs(120))
            .expect("the step deadline should end the equation loop")
            .expect("timeout should be a proof outcome");

        assert_eq!(result.status, ProofStatus::Indeterminate);
        assert!(matches!(
            result.leaves.as_slice(),
            [ProofLeaf {
                outcome: ProofLeafOutcome::Stopped(StopCause::Deadline(StepTimeoutMode::Manual(timeout))),
                ..
            }] if *timeout == step_timeout
        ));
        assert_eq!(
            result.stopped,
            Some(StopCause::Deadline(StepTimeoutMode::Manual(step_timeout)))
        );
    }

    #[test]
    fn accepts_trusted_claims_without_exploration() {
        let claims = modal_claim(ReachabilityMode::AllPath, "a", "b", true);
        let definition = definition("", &claims);

        let result = prove_claim(
            &definition,
            &definition.reachability_claims()[0],
            ProofOptions::default(),
            &NoSolver,
        )
        .unwrap();

        assert_eq!(result.status, ProofStatus::Proven);
        assert_eq!(result.explored_states, 0);
        assert!(matches!(
            result.leaves[0].outcome,
            ProofLeafOutcome::Trusted
        ));
    }

    #[test]
    fn distinguishes_existential_and_universal_rewrite_paths() {
        // a-to-b is declared first, so the one-path proof follows it; the all-path proof
        // explores the a-to-c path as well and finds it stuck at c.
        let claims = [
            modal_claim(ReachabilityMode::OnePath, "a", "b", false),
            modal_claim(ReachabilityMode::AllPath, "a", "b", false),
        ]
        .join("\n");
        let definition = definition(A_TO_B_AND_C, &claims);

        let one_path = prove_claim(
            &definition,
            claim_with_label(&definition, "one-a-b"),
            ProofOptions::default(),
            &NoSolver,
        )
        .unwrap();
        let all_path = prove_claim(
            &definition,
            claim_with_label(&definition, "all-a-b"),
            ProofOptions {
                max_counterexamples: 2,
                ..ProofOptions::default()
            },
            &NoSolver,
        )
        .unwrap();

        assert_eq!(one_path.status, ProofStatus::Proven);
        assert_eq!(one_path.explored_states, 2);
        assert!(one_path.leaves.iter().all(|leaf| {
            leaf.trace
                .iter()
                .all(|entry| entry.label.as_deref() != Some("a-to-c"))
        }));
        assert_eq!(all_path.status, ProofStatus::Disproved);
        assert_eq!(all_path.leaves.len(), 2);
        assert_eq!(all_path.unexplored_states, 0);
    }

    #[test]
    fn circularities_use_only_claims_at_least_as_strong_as_the_goal() {
        for (goal_mode, lemma_mode, expected) in [
            (
                ReachabilityMode::OnePath,
                ReachabilityMode::AllPath,
                ProofStatus::Proven,
            ),
            (
                ReachabilityMode::AllPath,
                ReachabilityMode::OnePath,
                ProofStatus::Disproved,
            ),
        ] {
            let claims = [
                modal_claim(goal_mode, "a", "c", false),
                modal_claim(lemma_mode, "b", "c", true),
            ]
            .join("\n");
            let definition = definition(A_TO_B, &claims);
            let goal = &definition.reachability_claims()[0];
            let result = prove_claim(&definition, goal, ProofOptions::default(), &NoSolver)
                .expect("claim should execute");
            let lemma_label = format!(
                "{}-b-c",
                if lemma_mode == ReachabilityMode::AllPath {
                    "all"
                } else {
                    "one"
                }
            );
            assert_eq!(
                result.status, expected,
                "{goal_mode:?} with {lemma_mode:?}: {result:#?}"
            );
            assert_eq!(
                result
                    .leaves
                    .iter()
                    .any(|leaf| leaf.trace.iter().any(|entry| {
                        entry.kind == TraceKind::Claim
                            && entry.label.as_deref() == Some(lemma_label.as_str())
                    })),
                expected == ProofStatus::Proven,
            );
        }
    }

    #[test]
    fn limits_live_breadth_and_collected_counterexamples() {
        let claims = modal_claim(ReachabilityMode::AllPath, "a", "c", false);
        let definition = definition(A_TO_B_AND_C, &claims);
        let claim = &definition.reachability_claims()[0];

        let breadth_limited = prove_claim(
            &definition,
            claim,
            ProofOptions {
                breadth_limit: Some(1),
                ..ProofOptions::default()
            },
            &NoSolver,
        )
        .unwrap();
        assert_eq!(breadth_limited.status, ProofStatus::BreadthBound);
        assert_eq!(breadth_limited.explored_states, 1);
        assert_eq!(breadth_limited.unexplored_states, 2);
        assert_eq!(breadth_limited.leaves.len(), 2);
        assert!(
            breadth_limited
                .leaves
                .iter()
                .all(|leaf| matches!(leaf.outcome, ProofLeafOutcome::BreadthBound))
        );
        assert_eq!(
            breadth_limited
                .leaves
                .iter()
                .map(|leaf| leaf.pattern.term.clone())
                .collect::<BTreeSet<_>>(),
            [term(&definition, "b{}()"), term(&definition, "c{}()")]
                .into_iter()
                .collect()
        );

        // The default limit of one counterexample stops the proof at the stuck b leaf, which the
        // declaration order reaches first; the c path stays unexplored.
        let limited = prove_claim(&definition, claim, ProofOptions::default(), &NoSolver).unwrap();
        assert_eq!(limited.status, ProofStatus::Disproved);
        assert_eq!(limited.leaves.len(), 1);
        assert_eq!(limited.unexplored_states, 1);
    }

    #[test]
    fn rejects_a_zero_counterexample_limit() {
        let claims = modal_claim(ReachabilityMode::AllPath, "a", "b", false);
        let definition = definition("", &claims);
        assert_eq!(
            prove_claim(
                &definition,
                &definition.reachability_claims()[0],
                ProofOptions {
                    max_counterexamples: 0,
                    ..ProofOptions::default()
                },
                &NoSolver,
            ),
            Err(ProofError::ZeroCounterexampleLimit)
        );
        assert_eq!(
            ProofError::ZeroCounterexampleLimit.to_string(),
            "the counterexample limit is 0, and a proof needs a limit of at least 1"
        );
    }

    #[test]
    fn supports_breadth_first_and_depth_first_proof_search() {
        let rules = r#"
            symbol d{}() : SortS{} [constructor{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(a{}(), \top{SortS{}}()), b{}()
            ) [label{}("a-to-b")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(a{}(), \top{SortS{}}()), d{}()
            ) [label{}("a-to-d")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(b{}(), \top{SortS{}}()), c{}()
            ) [label{}("b-to-c")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(d{}(), \top{SortS{}}()), c{}()
            ) [label{}("d-to-c")]
        "#;
        let claims = modal_claim(ReachabilityMode::AllPath, "a", "c", false);
        let definition = definition(rules, &claims);
        let claim = &definition.reachability_claims()[0];

        let breadth_first = prove_claim(
            &definition,
            claim,
            ProofOptions {
                search_order: ProofSearchOrder::BreadthFirst,
                ..ProofOptions::default()
            },
            &NoSolver,
        )
        .unwrap();
        let depth_first = prove_claim(
            &definition,
            claim,
            ProofOptions {
                search_order: ProofSearchOrder::DepthFirst,
                ..ProofOptions::default()
            },
            &NoSolver,
        )
        .unwrap();

        assert_eq!(breadth_first.status, ProofStatus::Proven);
        assert_eq!(depth_first.status, ProofStatus::Proven);
        assert_eq!(breadth_first.explored_states, 5);
        assert_eq!(depth_first.explored_states, 5);
        assert_ne!(breadth_first.leaves[0].trace, depth_first.leaves[0].trace);
    }

    #[test]
    fn a_refuted_current_target_continues_to_a_semantic_terminal() {
        let claims = r#"claim{} \implies{SortS{}}(
            \and{SortS{}}(\top{SortS{}}(), a{}()),
            weakExistsFinally{SortS{}}(
                \and{SortS{}}(a{}(), \bottom{SortS{}}())
            )
        ) [label{}("one-a-a")]"#;
        let definition = definition(A_TO_B, claims);

        let result = prove_claim(
            &definition,
            claim_with_label(&definition, "one-a-a"),
            ProofOptions::default(),
            &NoSolver,
        )
        .unwrap();

        // `a` has the one successor `b`, which has none and is outside the empty destination:
        // the only path from `a` never reaches it, so the one-path claim is refuted.
        assert_eq!(result.status, ProofStatus::Disproved);
        assert_eq!(result.explored_states, 2);
        assert_eq!(result.leaves[0].depth, 1);
        assert!(result.leaves[0].certified);
    }

    #[test]
    fn applies_guarded_claim_circularities_only_after_a_semantic_step() {
        let claims = modal_claim(ReachabilityMode::OnePath, "a", "b", false);
        let definition = definition(A_TO_A, &claims);

        let result = prove_claim(
            &definition,
            &definition.reachability_claims()[0],
            ProofOptions {
                max_depth: 3,
                ..ProofOptions::default()
            },
            &NoSolver,
        )
        .unwrap();

        assert_eq!(result.status, ProofStatus::Proven);
        assert_eq!(result.leaves[0].depth, 2);
        assert_eq!(
            result.leaves[0]
                .trace
                .iter()
                .map(|entry| entry.kind)
                .collect::<Vec<_>>(),
            vec![TraceKind::Rewrite, TraceKind::Claim]
        );
    }

    #[test]
    #[cfg(feature = "z3")]
    fn applies_a_partially_matching_claim_and_closes_its_remainder_by_rules() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortV{} []
                sort SortS{} []
                symbol va{}() : SortV{} [constructor{}()]
                symbol vb{}() : SortV{} [constructor{}()]
                symbol vc{}() : SortV{} [constructor{}()]
                axiom{} \or{SortV{}}(
                    va{}(), vb{}(), vc{}(), \bottom{SortV{}}()
                ) [constructor{}()]
                symbol init{}(SortV{}) : SortS{} [constructor{}()]
                symbol start{}(SortV{}) : SortS{} [constructor{}()]
                symbol done{}() : SortS{} [constructor{}()]
                alias weakAlwaysFinally{S}(S) : S
                    where weakAlwaysFinally{S}(@X:S) := @X:S []
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(init{}(X:SortV{}), \top{SortS{}}()),
                    start{}(X:SortV{})
                ) [label{}("init")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(start{}(vb{}()), \top{SortS{}}()),
                    done{}()
                ) [label{}("b")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(start{}(vc{}()), \top{SortS{}}()),
                    done{}()
                ) [label{}("c")]
                claim{} \implies{SortS{}}(
                    \and{SortS{}}(init{}(X:SortV{}), \top{SortS{}}()),
                    weakAlwaysFinally{SortS{}}(done{}())
                ) [label{}("main")]
                claim{} \implies{SortS{}}(
                    \and{SortS{}}(start{}(va{}()), \top{SortS{}}()),
                    weakAlwaysFinally{SortS{}}(done{}())
                ) [label{}("a-case"), trusted{}()]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let solver = crate::smt::Z3Solver::new(&definition).expect("Z3 should initialize");

        let result = prove_claim(
            &definition,
            claim_with_label(&definition, "main"),
            ProofOptions::default(),
            &solver,
        )
        .expect("claim should execute");

        assert_eq!(result.status, ProofStatus::Proven, "{result:#?}");
        let claimed = result
            .leaves
            .iter()
            .find(|leaf| {
                leaf.trace.iter().any(|entry| {
                    entry.kind == TraceKind::Claim && entry.label.as_deref() == Some("a-case")
                })
            })
            .expect("the trusted claim covers the `va` sub-case");
        assert!(claimed.pattern.constraints.iter().any(|predicate| {
            matches!(predicate, crate::rule::Predicate::Equals(left, _)
                if matches!(left.kind(), TermKind::Variable(_)))
        }));
        assert!(result.leaves.iter().any(|leaf| {
            leaf.trace.iter().any(|entry| {
                entry.kind == TraceKind::Remainder && entry.unique_id.starts_with("claim:")
            })
        }));
        assert_eq!(result.unexplored_states, 0);
    }

    #[cfg(feature = "z3")]
    fn overlapping_claim_remainder_definition(
        mode: ReachabilityMode,
        reverse_claims: bool,
        include_summary_rules: bool,
        include_d_rule: bool,
        include_initial_step: bool,
    ) -> BackendDefinition {
        let modality = match mode {
            ReachabilityMode::OnePath => "weakExistsFinally",
            ReachabilityMode::AllPath => "weakAlwaysFinally",
        };
        let initial = if include_initial_step {
            "init{}(X:SortInt{})"
        } else {
            "start{}(X:SortInt{})"
        };
        let init_rule = include_initial_step.then_some(
            r#"
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(init{}(X:SortInt{}), \top{SortS{}}()),
                    start{}(X:SortInt{})
                ) [label{}("init")]
            "#,
        );
        let d_rule = include_d_rule.then_some(
            r#"
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(
                        start{}(\dv{SortInt{}}("3")),
                        \top{SortS{}}()
                    ),
                    done{}()
                ) [label{}("d-case")]
            "#,
        );
        let ab_rule = r#"
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(
                        start{}(X:SortInt{}),
                        \or{SortS{}}(
                            \equals{SortInt{}, SortS{}}(
                                X:SortInt{}, \dv{SortInt{}}("0")
                            ),
                            \equals{SortInt{}, SortS{}}(
                                X:SortInt{}, \dv{SortInt{}}("1")
                            ),
                            \bottom{SortS{}}()
                        )
                    ),
                    done{}()
                ) [label{}("ab-semantics")]
            "#;
        let bc_rule = r#"
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(
                        start{}(X:SortInt{}),
                        \or{SortS{}}(
                            \equals{SortInt{}, SortS{}}(
                                X:SortInt{}, \dv{SortInt{}}("1")
                            ),
                            \equals{SortInt{}, SortS{}}(
                                X:SortInt{}, \dv{SortInt{}}("2")
                            ),
                            \bottom{SortS{}}()
                        )
                    ),
                    done{}()
                ) [label{}("bc-semantics")]
            "#;
        let summary_rules = include_summary_rules.then(|| {
            if reverse_claims {
                format!("{bc_rule}\n{ab_rule}")
            } else {
                format!("{ab_rule}\n{bc_rule}")
            }
        });
        let ab = format!(
            r#"
                claim{{}} \implies{{SortS{{}}}}(
                    \and{{SortS{{}}}}(
                        start{{}}(X:SortInt{{}}),
                        \or{{SortS{{}}}}(
                            \equals{{SortInt{{}}, SortS{{}}}}(
                                X:SortInt{{}}, \dv{{SortInt{{}}}}("0")
                            ),
                            \equals{{SortInt{{}}, SortS{{}}}}(
                                X:SortInt{{}}, \dv{{SortInt{{}}}}("1")
                            ),
                            \bottom{{SortS{{}}}}()
                        )
                    ),
                    {modality}{{SortS{{}}}}(done{{}}())
                ) [label{{}}("ab"), trusted{{}}()]
            "#,
        );
        let bc = format!(
            r#"
                claim{{}} \implies{{SortS{{}}}}(
                    \and{{SortS{{}}}}(
                        start{{}}(X:SortInt{{}}),
                        \or{{SortS{{}}}}(
                            \equals{{SortInt{{}}, SortS{{}}}}(
                                X:SortInt{{}}, \dv{{SortInt{{}}}}("1")
                            ),
                            \equals{{SortInt{{}}, SortS{{}}}}(
                                X:SortInt{{}}, \dv{{SortInt{{}}}}("2")
                            ),
                            \bottom{{SortS{{}}}}()
                        )
                    ),
                    {modality}{{SortS{{}}}}(done{{}}())
                ) [label{{}}("bc"), trusted{{}}()]
            "#,
        );
        let summaries = if reverse_claims {
            format!("{bc}\n{ab}")
        } else {
            format!("{ab}\n{bc}")
        };
        let source = format!(
            r#"[]
            module MAIN
                hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
                sort SortS{{}} []
                symbol init{{}}(SortInt{{}}) : SortS{{}} [constructor{{}}()]
                symbol start{{}}(SortInt{{}}) : SortS{{}} [constructor{{}}()]
                symbol done{{}}() : SortS{{}} [constructor{{}}()]
                alias weakExistsFinally{{S}}(S) : S
                    where weakExistsFinally{{S}}(@X:S) := @X:S []
                alias weakAlwaysFinally{{S}}(S) : S
                    where weakAlwaysFinally{{S}}(@X:S) := @X:S []
                {init_rule}
                {summary_rules}
                {d_rule}
                claim{{}} \implies{{SortS{{}}}}(
                    \and{{SortS{{}}}}(
                        {initial},
                        \or{{SortS{{}}}}(
                            \equals{{SortInt{{}}, SortS{{}}}}(
                                X:SortInt{{}}, \dv{{SortInt{{}}}}("0")
                            ),
                            \equals{{SortInt{{}}, SortS{{}}}}(
                                X:SortInt{{}}, \dv{{SortInt{{}}}}("1")
                            ),
                            \equals{{SortInt{{}}, SortS{{}}}}(
                                X:SortInt{{}}, \dv{{SortInt{{}}}}("2")
                            ),
                            \equals{{SortInt{{}}, SortS{{}}}}(
                                X:SortInt{{}}, \dv{{SortInt{{}}}}("3")
                            ),
                            \bottom{{SortS{{}}}}()
                        )
                    ),
                    {modality}{{SortS{{}}}}(done{{}}())
                ) [label{{}}("main")]
                {summaries}
            endmodule []"#,
            init_rule = init_rule.unwrap_or_default(),
            summary_rules = summary_rules.as_deref().unwrap_or_default(),
            d_rule = d_rule.unwrap_or_default(),
        );
        let syntax = parse_definition(&source).expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    #[test]
    #[cfg(feature = "z3")]
    fn overlapping_claim_remainders_preserve_coverage_in_both_modes_and_orders() {
        for mode in [ReachabilityMode::OnePath, ReachabilityMode::AllPath] {
            for reverse_claims in [false, true] {
                let definition =
                    overlapping_claim_remainder_definition(mode, reverse_claims, true, true, true);
                let solver = crate::smt::Z3Solver::new(&definition).expect("Z3 should initialize");
                let result = prove_claim(
                    &definition,
                    claim_with_label(&definition, "main"),
                    ProofOptions::default(),
                    &solver,
                )
                .expect("claim should execute");

                assert_eq!(result.status, ProofStatus::Proven, "{result:#?}");
                // Claims are tried in declaration order; the first covers its guarded sub-case
                // and its complement reaches the second.
                let (first, second) = if reverse_claims {
                    ("bc", "ab")
                } else {
                    ("ab", "bc")
                };
                assert!(
                    result.leaves.iter().all(|leaf| {
                        matches!(
                            leaf.trace.first(),
                            Some(TraceEntry {
                                kind: TraceKind::Rewrite,
                                label: Some(label),
                                ..
                            }) if label == "init"
                        )
                    }),
                    "every proof branch must start with semantic progress: {result:#?}"
                );
                assert!(
                    result
                        .leaves
                        .iter()
                        .any(|leaf| leaf.trace.iter().any(|entry| {
                            entry.kind == TraceKind::Claim && entry.label.as_deref() == Some(first)
                        })),
                    "the first summary must cover its guarded sub-case: {result:#?}"
                );
                assert!(
                    result.leaves.iter().any(|leaf| {
                        matches!(
                            leaf.trace.as_slice(),
                            [
                                TraceEntry { kind: TraceKind::Rewrite, label: Some(init), .. },
                                TraceEntry { kind: TraceKind::Remainder, .. },
                                TraceEntry { kind: TraceKind::Claim, label: Some(claim), .. },
                            ] if init == "init" && claim == second
                        )
                    }),
                    "the first complement must reach the second summary: {result:#?}"
                );
                assert!(
                    result.leaves.iter().any(|leaf| {
                        matches!(
                            leaf.trace.as_slice(),
                            [
                                TraceEntry { kind: TraceKind::Rewrite, label: Some(init), .. },
                                TraceEntry { kind: TraceKind::Remainder, .. },
                                TraceEntry { kind: TraceKind::Remainder, .. },
                                TraceEntry { kind: TraceKind::Rewrite, label: Some(finish), .. },
                            ] if init == "init" && finish == "d-case"
                        )
                    }),
                    "the complement of both summaries must reach the d rule: {result:#?}"
                );
                assert!(
                    result.leaves.iter().all(|leaf| {
                        !leaf.trace.iter().any(|entry| {
                            entry.label.as_deref() == Some("ab-semantics")
                                || entry.label.as_deref() == Some("bc-semantics")
                        })
                    }),
                    "the main witness must exercise claims before summary rules: {result:#?}"
                );
            }
        }
    }

    #[test]
    #[cfg(feature = "z3")]
    fn overlapping_claim_summaries_are_independently_semantically_valid() {
        for mode in [ReachabilityMode::OnePath, ReachabilityMode::AllPath] {
            for reverse_claims in [false, true] {
                let definition =
                    overlapping_claim_remainder_definition(mode, reverse_claims, true, true, true);
                let solver = crate::smt::Z3Solver::new(&definition).expect("Z3 should initialize");
                let mut claim = claim_with_label(&definition, "ab").clone();
                claim.attributes.trusted = false;
                let result =
                    super::prove_claim(&definition, &claim, &[], ProofOptions::default(), &solver)
                        .expect("claim should execute without circularities");

                assert_eq!(result.status, ProofStatus::Proven, "{result:#?}");
                assert!(
                    result.leaves.iter().all(|leaf| {
                        leaf.trace
                            .iter()
                            .all(|entry| entry.kind != TraceKind::Claim)
                            && leaf
                                .trace
                                .iter()
                                .any(|entry| entry.kind == TraceKind::Rewrite)
                    }),
                    "each summary must be proved from semantics alone: {result:#?}"
                );
            }
        }
    }

    #[test]
    #[cfg(feature = "z3")]
    fn overlapping_claim_remainders_require_complement_coverage_and_semantic_progress() {
        for mode in [ReachabilityMode::OnePath, ReachabilityMode::AllPath] {
            let without_d = overlapping_claim_remainder_definition(mode, false, true, false, true);
            let solver = crate::smt::Z3Solver::new(&without_d).expect("Z3 should initialize");
            let result = prove_claim(
                &without_d,
                claim_with_label(&without_d, "main"),
                ProofOptions::default(),
                &solver,
            )
            .expect("claim should execute");

            // Over the integers the uncovered `X` outside {0, 1, 2} is a certified refutation in
            // both modes: `init(3)` has the one successor `start(3)`, which has none, so no path
            // reaches `done`. The one-path trace follows a step on which one rule applies.
            let expected = ProofStatus::Disproved;
            assert_eq!(result.status, expected, "{result:#?}");
            assert!(
                result.leaves.iter().any(|leaf| {
                    matches!(leaf.outcome, ProofLeafOutcome::Stuck)
                        && leaf
                            .trace
                            .iter()
                            .filter(|entry| entry.kind == TraceKind::Remainder)
                            .count()
                            == 2
                }),
                "the uncovered d complement must remain visible: {result:#?}"
            );

            let without_progress =
                overlapping_claim_remainder_definition(mode, false, false, true, false);
            let solver =
                crate::smt::Z3Solver::new(&without_progress).expect("Z3 should initialize");
            let result = prove_claim(
                &without_progress,
                claim_with_label(&without_progress, "main"),
                ProofOptions::default(),
                &solver,
            )
            .expect("claim should execute");

            assert_eq!(result.status, expected, "{result:#?}");
            assert!(
                result.leaves.iter().all(|leaf| {
                    leaf.trace
                        .iter()
                        .all(|entry| entry.kind != TraceKind::Claim)
                }),
                "claims must remain unavailable before a semantic step: {result:#?}"
            );
        }
    }

    /// A refuted remainder obligation covers none of that input region. Its complement
    /// continues to rewriting under the ordinary proof policy.
    #[test]
    fn partial_destination_remainders_continue_to_semantic_steps() {
        let definition = definition(
            r#"
            symbol start{}(SortS{}) : SortS{} [constructor{}()]
            symbol done{}(SortS{}) : SortS{} [constructor{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(start{}(X:SortS{}), \top{SortS{}}()),
                done{}(X:SortS{})
            ) [label{}("step")]
            "#,
            r#"
            claim{} \implies{SortS{}}(
                \and{SortS{}}(start{}(X:SortS{}), \top{SortS{}}()),
                weakAlwaysFinally{SortS{}}(done{}(a{}()))
            ) [label{}("partial-destination")]
            "#,
        );

        /// Refutes the destination obligation `a() = X` and decides nothing else, so the
        /// complement `¬(a() = X)` that the uncovered part carries stays undecided.
        struct RefutesTheObligation;
        impl SmtSolver for RefutesTheObligation {
            fn is_sat(
                &self,
                _predicates: &[crate::rule::Predicate],
                _substitution: &Substitution,
            ) -> Stoppable<Result<Satisfiability, SmtError>> {
                Ok(Ok(Satisfiability::Sat))
            }

            fn check_predicates(
                &self,
                _known: &[crate::rule::Predicate],
                _substitution: &Substitution,
                checked: &[crate::rule::Predicate],
            ) -> Stoppable<Result<Validity, SmtError>> {
                Ok(Ok(match checked {
                    [crate::rule::Predicate::Equals(..)] => Validity::Refuted,
                    _ => Validity::Unknown("undecided".into()),
                }))
            }
        }
        let refuted = RefutesTheObligation;
        let result = prove_claim(
            &definition,
            &definition.reachability_claims()[0],
            ProofOptions::default(),
            &refuted,
        )
        .expect("claim should execute");

        // The terminal leaf is not a certified refutation: X has an untranslated sort.
        assert_eq!(result.status, ProofStatus::Failed);
        assert!(result.leaves.iter().any(|leaf| {
            leaf.trace
                .iter()
                .any(|entry| entry.kind == TraceKind::Remainder)
                && leaf.pattern.constraints.iter().any(|predicate| {
                    matches!(
                        predicate,
                        crate::rule::Predicate::Not(inner)
                            if matches!(inner.as_ref(), crate::rule::Predicate::Equals(..))
                    )
                })
        }));
    }

    /// `a() => wrap(f(partial(b())))` with `f(I) => I` and the claim `a() => c()`: the
    /// successor's loop head applies the equation and carries `\ceil(partial(b()))`, which the
    /// constructor `wrap` entails. The stuck leaf is externalised in the simplifier's normal
    /// form without the conjunct. The equation fires inside the rewrite step's result
    /// simplification, and the externalisation applies nothing, so the trace has no
    /// simplification entry.
    #[test]
    fn a_stuck_leaf_is_externalised_in_the_simplifier_normal_form() {
        let definition = definition(
            r#"
            symbol wrap{}(SortS{}) : SortS{} [constructor{}()]
            symbol partial{}(SortS{}) : SortS{} [function{}()]
            symbol f{}(SortS{}) : SortS{} [function{}(), total{}()]
            axiom{R} \implies{R}(\top{R}(), \equals{SortS{}, R}(
                f{}(I:SortS{}), \and{SortS{}}(I:SortS{}, \top{SortS{}}())
            )) [label{}("identity"), simplification{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(a{}(), \top{SortS{}}()),
                wrap{}(f{}(partial{}(b{}())))
            ) [label{}("step")]
            "#,
            &modal_claim(ReachabilityMode::AllPath, "a", "c", false),
        );
        let claim = &definition.reachability_claims()[0];

        let result = prove_claim(
            &definition,
            claim,
            ProofOptions {
                max_counterexamples: 2,
                ..ProofOptions::default()
            },
            &NoSolver,
        )
        .expect("the claim should execute");

        // `partial(b())` is an unevaluated function application: the leaf may be empty. The
        // step carries its definedness, so the instances where it is undefined are a `Trivial`
        // leaf of their own.
        assert_eq!(result.status, ProofStatus::Failed, "{result:#?}");
        let [undefined, leaf] = result.leaves.as_slice() else {
            panic!("expected two leaves, found {:?}", result.leaves);
        };
        assert_eq!(undefined.outcome, ProofLeafOutcome::Trivial);
        assert_eq!(leaf.outcome, ProofLeafOutcome::Stuck);
        assert_eq!(
            leaf.pattern.term,
            term(&definition, "wrap{}(partial{}(b{}()))")
        );
        assert_eq!(leaf.pattern.constraints, Vec::new(), "{leaf:#?}");
        let simplification_ids = leaf
            .trace
            .iter()
            .filter(|entry| entry.kind == TraceKind::Simplification)
            .map(|entry| entry.unique_id.as_str())
            .collect::<Vec<_>>();
        assert_eq!(simplification_ids, Vec::<&str>::new());
    }

    /// Two constants of `SortK`, rules `start(X) => mid(X)`, `mid(a) => end`, `mid(b) => fin`,
    /// the false claim `main: start(X) => end`, and the true trusted lemma
    /// `mid(Y) /\ Y = a => end` whose `Y = a` is spelled with a binder named `binder`:
    /// `\not(\exists binder. binder = a /\ \not(binder = Y))`.
    fn claim_capture_definition(binder: &str) -> BackendDefinition {
        let source = format!(
            r#"[]
            module MAIN
                sort SortK{{}} []
                sort SortS{{}} []
                symbol a{{}}() : SortK{{}} [constructor{{}}(), functional{{}}()]
                symbol b{{}}() : SortK{{}} [constructor{{}}(), functional{{}}()]
                axiom{{}} \or{{SortK{{}}}}(a{{}}(), b{{}}()) [constructor{{}}()]
                symbol start{{}}(SortK{{}}) : SortS{{}} [constructor{{}}(), functional{{}}()]
                symbol mid{{}}(SortK{{}}) : SortS{{}} [constructor{{}}(), functional{{}}()]
                symbol end{{}}() : SortS{{}} [constructor{{}}(), functional{{}}()]
                symbol fin{{}}() : SortS{{}} [constructor{{}}(), functional{{}}()]
                alias weakAlwaysFinally{{S}}(S) : S
                    where weakAlwaysFinally{{S}}(@X:S) := @X:S []
                axiom{{}} \rewrites{{SortS{{}}}}(
                    \and{{SortS{{}}}}(start{{}}(X:SortK{{}}), \top{{SortS{{}}}}()),
                    \and{{SortS{{}}}}(mid{{}}(X:SortK{{}}), \top{{SortS{{}}}}())) [label{{}}("r-start")]
                axiom{{}} \rewrites{{SortS{{}}}}(
                    \and{{SortS{{}}}}(mid{{}}(a{{}}()), \top{{SortS{{}}}}()),
                    \and{{SortS{{}}}}(end{{}}(), \top{{SortS{{}}}}())) [label{{}}("r-a")]
                axiom{{}} \rewrites{{SortS{{}}}}(
                    \and{{SortS{{}}}}(mid{{}}(b{{}}()), \top{{SortS{{}}}}()),
                    \and{{SortS{{}}}}(fin{{}}(), \top{{SortS{{}}}}())) [label{{}}("r-b")]
                claim{{}} \implies{{SortS{{}}}}(
                    \and{{SortS{{}}}}(start{{}}(X:SortK{{}}), \top{{SortS{{}}}}()),
                    weakAlwaysFinally{{SortS{{}}}}(end{{}}())) [label{{}}("main")]
                claim{{}} \implies{{SortS{{}}}}(
                    \and{{SortS{{}}}}(mid{{}}(Y:SortK{{}}),
                        \not{{SortS{{}}}}(\exists{{SortS{{}}}}({binder}:SortK{{}},
                            \and{{SortS{{}}}}(
                                \equals{{SortK{{}}, SortS{{}}}}({binder}:SortK{{}}, a{{}}()),
                                \not{{SortS{{}}}}(
                                    \equals{{SortK{{}}, SortS{{}}}}({binder}:SortK{{}}, Y:SortK{{}})))))),
                    weakAlwaysFinally{{SortS{{}}}}(end{{}}())) [label{{}}("lemma"), trusted{{}}()]
            endmodule []"#
        );
        let syntax = parse_definition(&source).expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    /// The lemma's binder spelled `X`, the name of the subject's variable in `mid(X)`.
    /// Matching binds the lemma's `Y` to `X`, and the substitution into
    /// `\not(\exists X. X = a /\ \not(X = Y))` must rename the binder, or it captures the
    /// subject's `X`, the requires becomes `\top`, and the false claim is proven. Every
    /// spelling answers as the `W` control.
    #[test]
    fn a_claim_binder_named_like_a_subject_variable_captures_nothing() {
        fn status(binder: &str, solver: Option<&str>) -> ProofStatus {
            let definition = claim_capture_definition(binder);
            let lemma = claim_with_label(&definition, "lemma");
            let prove = |solver: &dyn SmtSolver| {
                super::prove_claim(
                    &definition,
                    claim_with_label(&definition, "main"),
                    &[lemma],
                    ProofOptions::default(),
                    solver,
                )
                .expect("the claim should execute")
                .status
            };
            match solver {
                None => prove(&NoSolver),
                #[cfg(feature = "z3")]
                Some(_) => {
                    prove(&crate::smt::Z3Solver::new(&definition).expect("Z3 should initialize"))
                }
                #[cfg(not(feature = "z3"))]
                Some(_) => unreachable!("Z3 runs only with the z3 feature"),
            }
        }
        let control = status("W", None);
        assert_ne!(control, ProofStatus::Proven);
        assert_eq!(status("X", None), control);
        #[cfg(feature = "z3")]
        for binder in ["W", "X"] {
            assert_eq!(
                status(binder, Some("z3")),
                ProofStatus::Failed,
                "binder {binder}"
            );
        }
    }
}
