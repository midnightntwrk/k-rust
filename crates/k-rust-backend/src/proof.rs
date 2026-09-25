//! ```toml algorithm
//! id = "backend.proof.search"
//! name = "reachability-logic proof search"
//! sites = ["prove_claim", "extend_frontier", "finish_at_breadth_limit", "apply_claim"]
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
//! bound = "O(s) x (simplification + one is_sat + implication when depth >= min_depth + O(c) claim applications + one rewrite step), plus u leaf simplifications at the breadth limit"
//! ```
//!
//! Reachability-logic proof search (Kore proveClaim; pyk APR): per explored state one
//! simplification, one subsumption check (`Counter::ProofImplicationChecks`), circularity
//! application at depth > 0, one rewrite step; breadth- or depth-first by option, no state
//! deduplication; O(explored states) x (simplification + implication + |circularities| x
//! claim application + one step), `Counter::ProofStatesExplored`.

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
    definedness::ceil_term,
    definition::BackendDefinition,
    fresh::fresh_name,
    implication::{
        ImplicationCondition, ImplicationError, ImplicationFailure, ImplicationStatus,
        check_disjunctive_implication_with_existentials,
    },
    matching::{
        MatchMode, MatchResult, match_terms_in_definition, solve_collection_pairs_in_definition,
    },
    rewrite::{
        IndeterminateReason, Pattern, RemainderBranch, RewriteResult, TraceEntry, TraceKind, Truth,
        UndecidedStep, collection_unification_definedness, conjunctively_contains_alpha_equivalent,
        predicates_truth, quantify_introduced_variables, recover_indeterminate_match,
        rewrite_step_sequential_tracking_dropped, rewrite_step_sequential_with_options,
        rewrite_step_with_options, simplify_leaf_pattern, substitute_predicates,
    },
    simplify::{
        DEFAULT_MAX_SIMPLIFICATION_ITERATIONS, SimplificationError, SimplificationOptions,
        simplify_predicates_with_solver, simplify_with_solver,
    },
    smt::{Satisfiability, SmtError, SmtSolver, Validity},
    substitution::{Substitution, compose, extract_substitution_for, substitute},
    term::names::FreshMarker,
    term::{SymbolType, Term, TermKind},
    timeout::{StepTimeoutController, StepTimeoutMode, StepTimeoutOptions},
    unification::{UnificationResult, unify_term_pairs},
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
    pub stuck_check: bool,
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
            stuck_check: true,
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
    TimedOut(StepTimeoutMode),
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
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofResult {
    pub status: ProofStatus,
    pub leaves: Vec<ProofLeaf>,
    pub explored_states: u64,
    pub unexplored_states: u64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProofError {
    Implication(ImplicationError),
    ZeroCounterexampleLimit,
}

impl fmt::Display for ProofError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
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
    let _span = measure::algorithm_span(Algorithm::BackendProofSearch);
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
            }],
            explored_states: 0,
            unexplored_states: 0,
        });
    }

    let mut initial = claim.lhs.clone();
    let initial_definedness = ceil_term(definition, &initial.term);
    extend_unique(&mut initial.constraints, initial_definedness);
    let mut pending = VecDeque::from([ProofState {
        pattern: initial,
        depth: 0,
        trace: Vec::new(),
        kind: ProofStateKind::Rewritable,
        alternative_discarded: false,
        destination_undecided: false,
    }]);
    let mut leaves = Vec::new();
    // The claim's universals are fixed for the whole proof, including those that the path
    // has overwritten and that no longer occur in the current state; only the destination's
    // existentials may be quantified when a coverage condition is complemented.
    let claim_universals = variables_of_claim(claim)
        .difference(&claim.existentials)
        .cloned()
        .collect::<BTreeSet<_>>();
    let mut fresh_counter = 0;
    let mut explored_states = 0;
    let timeout_controller = StepTimeoutController::new(StepTimeoutOptions {
        manual: options.step_timeout,
        moving_average: options.moving_average_timeout,
    });
    macro_rules! record_leaf {
        ($leaf:expr) => {{
            leaves.push($leaf);
            if counterexample_limit_reached(&leaves, options) {
                return Ok(finish(leaves, explored_states, pending.len() as u64));
            }
        }};
    }
    // Every queued state is a rewrite or claim successor at depth + 1. Complete rewrite
    // remainders and implication remainders are classified without entering the frontier.
    // Invariant: `pending` holds the unexpanded states; `leaves` only grows; pops are counted.
    while let Some(mut state) = match options.search_order {
        ProofSearchOrder::BreadthFirst => pending.pop_front(),
        ProofSearchOrder::DepthFirst => pending.pop_back(),
    } {
        explored_states += 1;
        measure::bump(Counter::ProofStatesExplored);
        let mut step_timer = timeout_controller.begin_step();
        macro_rules! finish_if_timed_out {
            () => {
                if let Some(mode) = step_timer.timed_out() {
                    step_timer.discard_measurement();
                    leaves.push(state.leaf(ProofLeafOutcome::TimedOut(mode)));
                    return Ok(finish(leaves, explored_states, pending.len() as u64));
                }
            };
        }
        let simplified_constraints = simplify_predicates_with_solver(
            definition,
            &state.pattern.constraints,
            &[],
            SimplificationOptions::keep_partial(options.max_simplification_iterations),
            solver,
        );
        finish_if_timed_out!();
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
            let outcome = vacuous_outcome(&state, options, ProofLeafOutcome::Vacuous);
            record_leaf!(state.leaf(outcome));
            continue;
        }
        let simplified = simplify_with_solver(
            definition,
            &state.pattern.term,
            &state.pattern.constraints,
            SimplificationOptions::keep_partial(options.max_simplification_iterations),
            solver,
        );
        finish_if_timed_out!();
        let simplified = match simplified {
            Ok(simplified) => simplified,
            Err(error) => {
                record_leaf!(state.leaf(ProofLeafOutcome::Indeterminate(
                    ProofIndeterminateReason::Simplification(error),
                )));
                continue;
            }
        };
        state.pattern.term = simplified.term;
        extend_unique(&mut state.pattern.constraints, simplified.constraints);
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

        if state_is_bottom(&state, solver) {
            let outcome = vacuous_outcome(&state, options, ProofLeafOutcome::Vacuous);
            record_leaf!(state.leaf(outcome));
            continue;
        }

        let mut implication_indeterminate = false;
        let mut implication_remainder = None;
        if state.depth >= options.min_depth {
            measure::bump(Counter::ProofImplicationChecks);
            let implication = check_disjunctive_implication_with_existentials(
                definition,
                &state.pattern,
                &claim.rhs,
                &claim.existentials,
                SimplificationOptions {
                    max_iterations: options.max_simplification_iterations,
                    ..SimplificationOptions::default()
                },
                solver,
            );
            finish_if_timed_out!();
            let implication = match implication {
                // The check ran out of this thread's stack: the state cannot be decided here,
                // and the rest of the proof can still be.
                Err(ImplicationError::Simplification(
                    error @ SimplificationError::StackExhausted,
                )) => {
                    record_leaf!(state.leaf(ProofLeafOutcome::Indeterminate(
                        ProofIndeterminateReason::Simplification(error),
                    )));
                    continue;
                }
                implication => implication.map_err(ProofError::Implication)?,
            };
            match implication.status {
                ImplicationStatus::Valid => {
                    let outcome = if implication.vacuous {
                        vacuous_outcome(&state, options, ProofLeafOutcome::Vacuous)
                    } else {
                        let condition = implication
                            .condition
                            .expect("a valid implication always has a condition");
                        ProofLeafOutcome::Proven(condition)
                    };
                    record_leaf!(state.leaf(outcome));
                    continue;
                }
                // Only a coverage condition says which part of the state already lies
                // in the destination, so only its complement is the uncovered part. Both a
                // partial coverage and a contingent obligation carry one. A refuted
                // obligation (`ConsequentCondition`) covers none of the state; its
                // condition is the matcher's report (bindings and predicates), whose
                // complement can be bottom. The whole state is then the part outside the
                // destination and takes the arms below.
                ImplicationStatus::Invalid
                    if matches!(
                        implication.failure,
                        Some(
                            ImplicationFailure::PartialCoverage
                                | ImplicationFailure::ContingentCondition
                        )
                    ) =>
                {
                    let condition = implication
                        .condition
                        .expect("a partial implication carries its coverage condition");
                    let mut constraints = state.pattern.constraints.clone();
                    extend_unique(
                        &mut constraints,
                        vec![complement_implication_condition(
                            &state.pattern,
                            &claim_universals,
                            condition,
                        )],
                    );
                    let remainder = crate::rewrite::RemainderBranch {
                        pattern: Pattern {
                            term: state.pattern.term.clone(),
                            constraints,
                        },
                        rule_ids: vec![format!("destination:{}", claim.attributes.unique_id)],
                        effects: Vec::new(),
                        simplifications: Vec::new(),
                        indeterminate: None,
                    };
                    // A contingent destination covers part of the state; the part it does not
                    // cover may still rewrite into the destination, so it continues whatever
                    // the stuck check says. The stuck check stops only a part whose destination
                    // condition was refuted.
                    if options.stuck_check
                        && implication.failure != Some(ImplicationFailure::ContingentCondition)
                    {
                        record_leaf!(stuck_leaf(
                            definition,
                            state.remaining(remainder),
                            StuckEvidence::StepNotRun,
                            claim.mode,
                            fresh_counter,
                            options,
                            solver,
                        ));
                        continue;
                    }
                    implication_remainder = Some(remainder);
                }
                ImplicationStatus::Invalid
                    if options.stuck_check
                        && implication.failure == Some(ImplicationFailure::ConsequentCondition) =>
                {
                    record_leaf!(stuck_leaf(
                        definition,
                        state,
                        StuckEvidence::StepNotRun,
                        claim.mode,
                        fresh_counter,
                        options,
                        solver,
                    ));
                    continue;
                }
                ImplicationStatus::Invalid => {}
                ImplicationStatus::Indeterminate => implication_indeterminate = true,
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
                    record_leaf!(stuck_leaf(
                        definition,
                        state,
                        StuckEvidence::StepNotRun,
                        claim.mode,
                        fresh_counter,
                        options,
                        solver,
                    ));
                    continue;
                }
            };
            record_leaf!(externalise_leaf(
                definition, state, outcome, options, solver
            ));
            continue;
        }

        if state.depth >= options.max_depth {
            record_leaf!(externalise_leaf(
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
                if candidate.mode != claim.mode {
                    continue;
                }
                let transition = apply_claim(
                    definition,
                    candidate,
                    &state.pattern,
                    options,
                    solver,
                    &mut fresh_counter,
                );
                finish_if_timed_out!();
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
        let (rewritten, dropped) = match claim.mode {
            // Once the trace may have dropped a successor, no later step can make it certifiable
            // again, so the step no longer asks.
            ReachabilityMode::OnePath if state.alternative_discarded => (
                rewrite_step_sequential_with_options(
                    definition,
                    &state.pattern,
                    &mut fresh_counter,
                    simplification,
                    solver,
                ),
                true,
            ),
            ReachabilityMode::OnePath => rewrite_step_sequential_tracking_dropped(
                definition,
                &state.pattern,
                &mut fresh_counter,
                simplification,
                solver,
            ),
            ReachabilityMode::AllPath => (
                rewrite_step_with_options(
                    definition,
                    &state.pattern,
                    &mut fresh_counter,
                    simplification,
                    solver,
                ),
                false,
            ),
        };
        finish_if_timed_out!();
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
                    std::iter::once(state.rewritten(applied)),
                    options.breadth_limit,
                ) {
                    return Ok(finish_at_breadth_limit(
                        definition,
                        leaves,
                        pending,
                        explored_states,
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
                let mut successors = branches
                    .into_iter()
                    .map(|applied| state.clone().rewritten(applied))
                    .collect::<Vec<_>>();
                if let Some(remainder) = remainder {
                    successors.push(state.clone().rewrite_remaining(remainder));
                }
                if extend_frontier(&mut pending, successors, options.breadth_limit) {
                    return Ok(finish_at_breadth_limit(
                        definition,
                        leaves,
                        pending,
                        explored_states,
                        options,
                        solver,
                    ));
                }
                for trivial in trivial {
                    let mut trivial_state = state.clone();
                    trivial_state.depth += 1;
                    trivial_state.trace.push(TraceEntry {
                        depth: trivial_state.depth,
                        kind: TraceKind::Rewrite,
                        label: trivial.label,
                        unique_id: trivial.rule_id,
                    });
                    extend_unique(
                        &mut trivial_state.pattern.constraints,
                        vec![trivial.applicability],
                    );
                    let outcome =
                        vacuous_outcome(&trivial_state, options, ProofLeafOutcome::Trivial);
                    record_leaf!(trivial_state.leaf(outcome));
                }
            }
            RewriteResult::Stuck(_) => {
                let outcome = if implication_indeterminate {
                    ProofLeafOutcome::Indeterminate(ProofIndeterminateReason::Implication)
                } else if let Some(reason) = claim_indeterminate {
                    ProofLeafOutcome::Indeterminate(reason)
                } else {
                    record_leaf!(stuck_leaf(
                        definition,
                        state,
                        StuckEvidence::StepStuck,
                        claim.mode,
                        fresh_counter,
                        options,
                        solver,
                    ));
                    continue;
                };
                record_leaf!(externalise_leaf(
                    definition, state, outcome, options, solver
                ));
            }
            RewriteResult::Trivial(_, _) => {
                state.depth += 1;
                state.trace.push(TraceEntry {
                    depth: state.depth,
                    kind: TraceKind::Rewrite,
                    label: None,
                    unique_id: "trivial".into(),
                });
                let outcome = vacuous_outcome(&state, options, ProofLeafOutcome::Trivial);
                record_leaf!(state.leaf(outcome));
            }
            RewriteResult::Vacuous(_) => {
                let outcome = vacuous_outcome(&state, options, ProofLeafOutcome::Vacuous);
                record_leaf!(state.leaf(outcome));
            }
            RewriteResult::Indeterminate { reason, .. } => {
                record_leaf!(externalise_leaf(
                    definition,
                    state,
                    ProofLeafOutcome::Indeterminate(ProofIndeterminateReason::Rewrite(reason)),
                    options,
                    solver,
                ));
            }
            RewriteResult::Simplification { error, .. } => {
                record_leaf!(externalise_leaf(
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

    Ok(finish(leaves, explored_states, 0))
}

fn extend_frontier(
    pending: &mut VecDeque<ProofState>,
    states: impl IntoIterator<Item = ProofState>,
    breadth_limit: Option<usize>,
) -> bool {
    pending.extend(states);
    breadth_limit.is_some_and(|limit| pending.len() > limit)
}

fn finish_at_breadth_limit(
    definition: &BackendDefinition,
    mut leaves: Vec<ProofLeaf>,
    pending: VecDeque<ProofState>,
    explored_states: u64,
    options: ProofOptions,
    solver: &dyn SmtSolver,
) -> ProofResult {
    let unexplored_states = pending.len() as u64;
    leaves.extend(pending.into_iter().map(|state| {
        externalise_leaf(
            definition,
            state,
            ProofLeafOutcome::BreadthBound,
            options,
            solver,
        )
    }));
    finish(leaves, explored_states, unexplored_states)
}

/// Externalise a proof leaf in the simplifier's normal form (`rewrite::simplify_leaf_pattern`).
///
/// The leaves simplified are the states the proof could not close: `Stuck`, `DepthBound`,
/// `BreadthBound`, and `Indeterminate` for a reason other than a simplification failure. A
/// proven, trusted, trivial, vacuous, or timed-out leaf is reported as it stands. A constraint
/// set that simplifies to `\bottom` is an empty state and takes the outcome the loop head gives
/// one. When the simplification fails, an `Indeterminate` leaf keeps its pattern and reason;
/// any other leaf reports the failure, as a failed loop-head simplification does. The outcome is
/// decided before externalisation, which only normalises the pattern, so a step deadline that
/// passes during it leaves the leaf as it stands with its unsimplified pattern.
fn externalise_leaf(
    definition: &BackendDefinition,
    mut state: ProofState,
    outcome: ProofLeafOutcome,
    options: ProofOptions,
    solver: &dyn SmtSolver,
) -> ProofLeaf {
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
        | ProofLeafOutcome::TimedOut(_) => false,
    };
    if !externalised {
        return state.leaf(outcome);
    }
    match simplify_leaf_pattern(
        definition,
        &state.pattern,
        options.max_simplification_iterations,
        solver,
        state.depth,
        &mut state.trace,
    ) {
        Ok(simplified) if predicates_truth(&simplified.pattern.constraints) == Truth::False => {
            state.pattern = simplified.pattern;
            let outcome = vacuous_outcome(&state, options, ProofLeafOutcome::Vacuous);
            state.leaf(outcome)
        }
        Ok(simplified) => {
            state.pattern = simplified.pattern;
            state.leaf(outcome)
        }
        Err(SimplificationError::Interrupted) => state.leaf(outcome),
        Err(_) if matches!(outcome, ProofLeafOutcome::Indeterminate(_)) => state.leaf(outcome),
        Err(error) => state.leaf(ProofLeafOutcome::Indeterminate(
            ProofIndeterminateReason::Simplification(error),
        )),
    }
}

/// Whether the rewrite step on a `Stuck` leaf is already known to have no successor.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum StuckEvidence {
    /// The rewrite step on this state returned `RewriteResult::Stuck`.
    StepStuck,
    /// The search stopped the state without rewriting it: a stuck-check stop, or a rewrite
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
///   application, and its constraints, which carry the complement of every destination coverage
///   condition on the trace, together with the definedness of its term are satisfiable by a
///   query that approximates nothing (`smt::translates_exactly`), or are true syntactically.
///   Those complements say "outside the destination" only if every state on the trace had its
///   implication check run and decided (`ProofState::destination_undecided`): a skipped or
///   undecided check leaves no complement, and the configurations that continued past it may
///   have reached the destination there.
///
/// Every other `Stuck` leaf reports `ProofStatus::Failed`.
fn stuck_leaf(
    definition: &BackendDefinition,
    state: ProofState,
    evidence: StuckEvidence,
    mode: ReachabilityMode,
    fresh_counter: u64,
    options: ProofOptions,
    solver: &dyn SmtSolver,
) -> ProofLeaf {
    let path_certifiable = state.path_certifiable();
    let mut leaf = externalise_leaf(definition, state, ProofLeafOutcome::Stuck, options, solver);
    let refutes = |instance: &Pattern, evidence: StuckEvidence| {
        leaf_is_nonempty(definition, instance, solver)
            && (evidence == StuckEvidence::StepStuck
                || has_no_successor(definition, instance, mode, fresh_counter, options, solver))
    };
    leaf.certified = leaf.outcome == ProofLeafOutcome::Stuck
        && path_certifiable
        && (refutes(&leaf.pattern, evidence)
            || empty_computation_instance(definition, &leaf.pattern)
                .is_some_and(|instance| refutes(&instance, StuckEvidence::StepNotRun)));
    leaf
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
    let dotk = definition.symbols.get(WellKnownSymbol::DotK.as_str())?;
    if !dotk.sort_variables.is_empty() || !dotk.argument_sorts.is_empty() {
        return None;
    }
    let empty = Term::application(Arc::clone(dotk), Vec::new(), Vec::new());
    let substitution = computations
        .into_iter()
        .map(|variable| (variable, empty.clone()))
        .collect::<Substitution>();
    Some(Pattern {
        term: substitute(&pattern.term, &substitution),
        constraints: substitute_predicates(&pattern.constraints, &substitution),
    })
}

/// Condition (d) of [`stuck_leaf`].
fn leaf_is_nonempty(
    definition: &BackendDefinition,
    pattern: &Pattern,
    solver: &dyn SmtSolver,
) -> bool {
    // An unevaluated function application may denote no value, or a value that the destination
    // match would have accepted; a conjunction of terms may denote no value.
    let mut constructors_only = !matches!(pattern.term.kind(), TermKind::And(..));
    pattern.term.visit_symbols(&mut |symbol| {
        constructors_only &= symbol.attributes.symbol_type == SymbolType::Constructor;
    });
    if !constructors_only {
        return false;
    }
    let mut query = pattern.constraints.clone();
    extend_unique(&mut query, ceil_term(definition, &pattern.term));
    predicates_truth(&query) == Truth::True
        || (crate::smt::translates_exactly(&query)
            && matches!(
                solver.is_sat(&query, &Substitution::new()),
                Ok(Satisfiability::Sat)
            ))
}

/// Condition (a) of [`stuck_leaf`] for a state the search stopped without rewriting it. The
/// step runs on a copy of the fresh-name counter: its successors, if any, are discarded.
fn has_no_successor(
    definition: &BackendDefinition,
    pattern: &Pattern,
    mode: ReachabilityMode,
    mut fresh_counter: u64,
    options: ProofOptions,
    solver: &dyn SmtSolver,
) -> bool {
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
    };
    matches!(rewritten, RewriteResult::Stuck(_))
}

fn counterexample_limit_reached(leaves: &[ProofLeaf], options: ProofOptions) -> bool {
    leaves.iter().filter(|leaf| !is_proven(leaf)).count() >= options.max_counterexamples
}

#[derive(Clone)]
struct ProofState {
    pattern: Pattern,
    depth: u64,
    trace: Vec<TraceEntry>,
    kind: ProofStateKind,
    /// A one-path step on this trace may have dropped a successor of a configuration it covered:
    /// an overlapping rule of equal priority, a second collection match, or a rule whose
    /// right-hand side stands for several successors (`rewrite_step_sequential_tracking_dropped`).
    alternative_discarded: bool,
    /// Some state on this trace was not shown outside the destination: its implication check
    /// was skipped (below the minimum depth) or undecided. Part of its configurations may then
    /// have satisfied the claim there, before the path went on.
    destination_undecided: bool,
}

#[derive(Clone)]
enum ProofStateKind {
    Rewritable,
    Remaining(Option<UndecidedStep>),
}

impl ProofState {
    fn leaf(self, outcome: ProofLeafOutcome) -> ProofLeaf {
        ProofLeaf {
            pattern: self.pattern,
            depth: self.depth,
            trace: self.trace,
            outcome,
            certified: false,
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

    fn remaining(mut self, remainder: crate::rewrite::RemainderBranch) -> Self {
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
    fresh_counter: &mut u64,
) -> ClaimApplication {
    let claim = freshen_claim(claim, subject, fresh_counter);
    let claim_variables = variables_of_claim(&claim);
    let matched = match_terms_in_definition(
        MatchMode::Rewrite,
        definition,
        &claim.lhs.term,
        &subject.term,
    );
    let (substitution, match_conditions) = match matched {
        MatchResult::Success(substitution) => (substitution, Vec::new()),
        MatchResult::Failed(_) => return ClaimApplication::NotApplicable,
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
            ) {
                Ok(recovered) => recovered,
                Err(error) => {
                    return ClaimApplication::Indeterminate(
                        ClaimIndeterminateReason::Simplification(error),
                    );
                }
            };
            match recovered.result {
                MatchResult::Success(substitution) => (substitution, recovered.conditions),
                MatchResult::Failed(_) => return ClaimApplication::NotApplicable,
                MatchResult::Indeterminate {
                    substitution,
                    remainder,
                } => {
                    // A symbolic subject can still be covered by the claim on the sub-case
                    // where the unresolved pairs unify. Those equalities become the match
                    // condition; their complement is the remainder the claim leaves behind.
                    match unify_term_pairs(definition, substitution, remainder.iter().cloned()) {
                        UnificationResult::Unified(unified) => {
                            let mut conditions = recovered.conditions;
                            extend_unique(&mut conditions, unified.constraints);
                            (unified.substitution, conditions)
                        }
                        UnificationResult::Bottom(_) => return ClaimApplication::NotApplicable,
                        UnificationResult::Unsupported {
                            substitution,
                            constraints,
                            remainder,
                        } => {
                            // Collection pairs are beyond the syntactic unifier; solve them as
                            // rule application does (rewrite.rs recover_general_unification),
                            // accepting a unique solution.
                            let solutions = solve_collection_pairs_in_definition(
                                MatchMode::Rewrite,
                                definition,
                                substitution.clone(),
                                &remainder,
                                None,
                            );
                            match solutions.as_deref() {
                                Some([]) => return ClaimApplication::NotApplicable,
                                Some([solution]) => {
                                    let mut conditions = recovered.conditions;
                                    extend_unique(&mut conditions, constraints);
                                    extend_unique(&mut conditions, solution.constraints.clone());
                                    extend_unique(
                                        &mut conditions,
                                        collection_unification_definedness(
                                            definition,
                                            &remainder,
                                            &solution.substitution,
                                        ),
                                    );
                                    (solution.substitution.clone(), conditions)
                                }
                                _ => {
                                    return ClaimApplication::Indeterminate(
                                        ClaimIndeterminateReason::Match {
                                            substitution,
                                            remainder,
                                        },
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
    };
    let (mut substitution, match_conditions) =
        bind_subject_variables(definition, &claim, substitution, match_conditions);
    let simplification = SimplificationOptions {
        max_iterations: options.max_simplification_iterations,
        ..SimplificationOptions::default()
    };
    let mut match_conditions = match simplify_predicates_with_solver(
        definition,
        &match_conditions,
        &subject.constraints,
        simplification,
        solver,
    ) {
        Ok(conditions) => conditions,
        Err(error) => {
            return ClaimApplication::Indeterminate(ClaimIndeterminateReason::Simplification(
                error,
            ));
        }
    };
    if predicates_truth(&match_conditions) == Truth::False {
        return ClaimApplication::NotApplicable;
    }

    let requires = substitute_predicates(&claim.lhs.constraints, &substitution);
    let mut match_knowledge = subject.constraints.clone();
    extend_unique(&mut match_knowledge, match_conditions.clone());
    let requires = match simplify_predicates_with_solver(
        definition,
        &requires,
        &match_knowledge,
        simplification,
        solver,
    ) {
        Ok(requires) => requires,
        Err(error) => {
            return ClaimApplication::Indeterminate(ClaimIndeterminateReason::Simplification(
                error,
            ));
        }
    };
    if predicates_truth(&requires) == Truth::False {
        return ClaimApplication::NotApplicable;
    }

    let unbound = claim_variables
        .into_iter()
        .filter(|variable| !substitution.contains_key(variable))
        .collect::<BTreeSet<_>>();
    let (defined, requires) = extract_substitution_for(&requires, &unbound, &definition.sort_graph);
    substitution = compose(&defined, &substitution);
    match_conditions = substitute_predicates(&match_conditions, &defined);
    match_conditions = match simplify_predicates_with_solver(
        definition,
        &match_conditions,
        &subject.constraints,
        simplification,
        solver,
    ) {
        Ok(conditions) => conditions,
        Err(error) => {
            return ClaimApplication::Indeterminate(ClaimIndeterminateReason::Simplification(
                error,
            ));
        }
    };
    if predicates_truth(&match_conditions) == Truth::False {
        return ClaimApplication::NotApplicable;
    }
    let mut match_knowledge = subject.constraints.clone();
    extend_unique(&mut match_knowledge, match_conditions.clone());
    let requires = substitute_predicates(&requires, &defined);
    let requires = match simplify_predicates_with_solver(
        definition,
        &requires,
        &match_knowledge,
        simplification,
        solver,
    ) {
        Ok(requires) => requires,
        Err(error) => {
            return ClaimApplication::Indeterminate(ClaimIndeterminateReason::Simplification(
                error,
            ));
        }
    };
    if predicates_truth(&requires) == Truth::False {
        return ClaimApplication::NotApplicable;
    }

    // Conditions the path already satisfies do not narrow it. Every other match or requires
    // predicate describes the covered sub-case; their joint complement is the claim remainder.
    let mut conditions = match_conditions;
    extend_unique(&mut conditions, requires);
    conditions.retain(|condition| {
        predicates_truth(std::slice::from_ref(condition)) == Truth::Unknown
            && !subject.constraints.contains(condition)
    });
    if !conditions.is_empty() {
        match solver.check_predicates(&subject.constraints, &Substitution::new(), &conditions) {
            Ok(Validity::Valid) => conditions.clear(),
            Ok(Validity::Invalid | Validity::InconsistentGroundTruth) => {
                return ClaimApplication::NotApplicable;
            }
            Ok(Validity::Indeterminate) | Err(SmtError::Unavailable) => {}
            Ok(Validity::Unknown(reason)) => {
                return ClaimApplication::Indeterminate(ClaimIndeterminateReason::Smt(
                    SmtError::Unknown(reason),
                ));
            }
            Err(error) => {
                return ClaimApplication::Indeterminate(ClaimIndeterminateReason::Smt(error));
            }
        }
    }

    let complement = if conditions.is_empty() {
        None
    } else {
        let condition = quantify_introduced_variables(subject, conditions.clone());
        let negated =
            crate::simplify::normalize_predicate(crate::rule::Predicate::Not(Box::new(condition)));
        if conjunctively_contains_alpha_equivalent(&subject.constraints, &negated) {
            // This subject is the remainder of an earlier application of the same claim.
            return ClaimApplication::NotApplicable;
        }
        Some(negated)
    };
    // Kore evaluates the remainder predicate and prunes an unsatisfiable remainder before it
    // becomes a state (RewriteStep.hs:308-322): the claim then covers the whole subject, and no
    // bottom successor is left for the vacuity check to reject.
    let complement = match complement {
        Some(negated) => {
            match remainder_is_unsatisfiable(definition, subject, &negated, simplification, solver)
            {
                Ok(true) => None,
                Ok(false) => Some(negated),
                Err(error) => {
                    return ClaimApplication::Indeterminate(
                        ClaimIndeterminateReason::Simplification(error),
                    );
                }
            }
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
        }
    });
    ClaimApplication::Applied {
        patterns: claim
            .rhs
            .iter()
            .map(|rhs| {
                let mut constraints = covered_knowledge.clone();
                extend_unique(
                    &mut constraints,
                    substitute_predicates(&rhs.constraints, &substitution),
                );
                Pattern {
                    term: substitute(&rhs.term, &substitution),
                    constraints,
                }
            })
            .collect(),
        remainder,
    }
}

/// The remainder of a claim application is the subject under the negated, quantified match
/// condition. It is unsatisfiable when that condition simplifies to false or the solver refutes
/// it together with the subject's constraints; an undecided or unavailable solver, or a failed
/// simplification, keeps it. An exhausted stack is returned instead: keeping the remainder would
/// turn the lack of stack into a state the claim does not cover.
fn remainder_is_unsatisfiable(
    definition: &BackendDefinition,
    subject: &Pattern,
    negated: &crate::rule::Predicate,
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Result<bool, SimplificationError> {
    let simplified = match simplify_predicates_with_solver(
        definition,
        std::slice::from_ref(negated),
        &subject.constraints,
        options,
        solver,
    ) {
        Ok(simplified) => simplified,
        Err(error @ SimplificationError::StackExhausted) => return Err(error),
        Err(_) => return Ok(false),
    };
    if predicates_truth(&simplified) == Truth::False {
        return Ok(true);
    }
    let mut constraints = subject.constraints.clone();
    extend_unique(&mut constraints, simplified);
    Ok(matches!(
        solver.is_sat(&constraints, &Substitution::new()),
        Ok(Satisfiability::Unsat)
    ))
}

/// Unification may bind variables of the subject rather than of the claim. Such bindings are
/// conditions on the subject, not part of the claim's instantiation: keep them as equalities
/// (with the definedness of the bound value) and drop them from the substitution, as rule
/// application does for configuration variables.
fn bind_subject_variables(
    definition: &BackendDefinition,
    claim: &ReachabilityClaim,
    mut substitution: Substitution,
    mut conditions: Vec<crate::rule::Predicate>,
) -> (Substitution, Vec<crate::rule::Predicate>) {
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
            extend_unique(&mut conditions, ceil_term(definition, &value));
        }
    }
    (substitution, conditions)
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
    fresh_counter: &mut u64,
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
        let name = fresh_name(
            &variable.name,
            FreshMarker::Claim,
            fresh_counter,
            &mut names,
        );
        renaming.insert(variable.clone(), Term::variable(variable.with_name(name)));
    }
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
            ProofLeafOutcome::TimedOut(_) | ProofLeafOutcome::Indeterminate(_)
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
    }
}

fn is_proven(leaf: &ProofLeaf) -> bool {
    matches!(
        leaf.outcome,
        ProofLeafOutcome::Proven(_) | ProofLeafOutcome::Trusted
    )
}

fn state_is_bottom(state: &ProofState, solver: &dyn SmtSolver) -> bool {
    predicates_truth(&state.pattern.constraints) == Truth::False
        || matches!(
            solver.is_sat(&state.pattern.constraints, &Substitution::new()),
            Ok(Satisfiability::Unsat)
        )
}

/// Kore accepts a bottom initial claim, but rejects bottom successors unless vacuity is allowed.
fn vacuous_outcome(
    state: &ProofState,
    options: ProofOptions,
    cause: ProofLeafOutcome,
) -> ProofLeafOutcome {
    if (state.depth == 0 && state.trace.is_empty()) || options.allow_vacuous {
        ProofLeafOutcome::Proven(ImplicationCondition {
            predicates: vec![crate::rule::Predicate::False],
            substitution: Substitution::new(),
            witnesses: Substitution::new(),
        })
    } else {
        cause
    }
}

fn extend_unique(left: &mut Vec<crate::rule::Predicate>, right: Vec<crate::rule::Predicate>) {
    for predicate in right {
        if !left.contains(&predicate) {
            left.push(predicate);
        }
    }
}

/// The part of `pattern` that `condition` does not cover: `¬∃E. condition`, where `E` are the
/// condition's variables that are neither in the state nor among the claim's `universals`.
/// A universal stays free even when the current state no longer mentions it: it names the
/// same value in every state of the proof, so quantifying it would turn "the initial value
/// differs" into `⊥` and drop the uncovered part.
fn complement_implication_condition(
    pattern: &Pattern,
    universals: &BTreeSet<crate::term::Variable>,
    condition: ImplicationCondition,
) -> crate::rule::Predicate {
    let mut covered = conjoin_predicates(condition.predicates);
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
    let introduced = covered
        .free_variables()
        .difference(&in_scope)
        .cloned()
        .collect::<Vec<_>>();
    for variable in introduced.into_iter().rev() {
        covered = crate::rule::Predicate::Exists(variable, Box::new(covered));
    }
    crate::simplify::normalize_predicate(crate::rule::Predicate::Not(Box::new(covered)))
}

fn conjoin_predicates(mut predicates: Vec<crate::rule::Predicate>) -> crate::rule::Predicate {
    match predicates.len() {
        0 => crate::rule::Predicate::True,
        1 => predicates.pop().expect("one predicate is present"),
        _ => crate::rule::Predicate::And(predicates),
    }
}

#[cfg(test)]
mod tests {
    use std::{thread, time::Duration};

    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    use super::*;
    use crate::{
        diagnostic::{self, BackendDiagnostic},
        simplify::BudgetSubject,
        smt::{NoSolver, Satisfiability},
    };

    struct SlowSolver;

    impl SmtSolver for SlowSolver {
        fn is_sat(
            &self,
            _predicates: &[crate::rule::Predicate],
            _substitution: &Substitution,
        ) -> Result<Satisfiability, SmtError> {
            thread::sleep(Duration::from_millis(5));
            Ok(Satisfiability::Sat)
        }

        fn check_predicates(
            &self,
            _known: &[crate::rule::Predicate],
            _substitution: &Substitution,
            _checked: &[crate::rule::Predicate],
        ) -> Result<Validity, SmtError> {
            thread::sleep(Duration::from_millis(5));
            Ok(Validity::Indeterminate)
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
        ) -> Result<Satisfiability, SmtError> {
            self.satisfiability.clone()
        }

        fn check_predicates(
            &self,
            _known: &[crate::rule::Predicate],
            _substitution: &Substitution,
            _checked: &[crate::rule::Predicate],
        ) -> Result<Validity, SmtError> {
            self.validity.clone()
        }
    }

    struct NonemptyUnsatSolver;

    impl SmtSolver for NonemptyUnsatSolver {
        fn is_sat(
            &self,
            predicates: &[crate::rule::Predicate],
            _substitution: &Substitution,
        ) -> Result<Satisfiability, SmtError> {
            Ok(if predicates.is_empty() {
                Satisfiability::Sat
            } else {
                Satisfiability::Unsat
            })
        }

        fn check_predicates(
            &self,
            _known: &[crate::rule::Predicate],
            _substitution: &Substitution,
            _checked: &[crate::rule::Predicate],
        ) -> Result<Validity, SmtError> {
            Ok(Validity::Indeterminate)
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
            .reachability_claims
            .iter()
            .find(|claim| claim.attributes.label.as_deref() == Some(label))
            .unwrap_or_else(|| panic!("claim {label:?} should be indexed"))
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
        let circularities = definition.reachability_claims.iter().collect::<Vec<_>>();
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
                ImplicationCondition {
                    predicates: vec![crate::rule::Predicate::Or(vec![
                        first.clone(),
                        second.clone(),
                    ])],
                    substitution: Substitution::new(),
                    witnesses: Substitution::new(),
                },
            ),
            crate::rule::Predicate::And(vec![
                crate::rule::Predicate::Not(Box::new(first)),
                crate::rule::Predicate::Not(Box::new(second)),
            ]),
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
        let condition = ImplicationCondition {
            predicates: vec![covered.clone()],
            substitution: Substitution::new(),
            witnesses: Substitution::new(),
        };

        assert_eq!(
            complement_implication_condition(
                &pattern,
                &BTreeSet::from([universal.clone()]),
                condition.clone(),
            ),
            crate::rule::Predicate::Not(Box::new(covered.clone())),
        );
        // A destination existential is still quantified.
        assert_eq!(
            complement_implication_condition(&pattern, &BTreeSet::new(), condition),
            crate::rule::Predicate::Not(Box::new(crate::rule::Predicate::Exists(
                universal.clone(),
                Box::new(covered),
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
    /// is quantified, is `\not(\exists Y. X = Y + -1)`: unsatisfiable over the integers. Kore
    /// evaluates the remainder predicate and prunes an UNSAT remainder before it becomes a
    /// state (RewriteStep.hs:308-322), so the reference proves the claim; an unsatisfiable
    /// remainder must not surface as a vacuous leaf that fails the proof.
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
    /// the subject frame `F` to the claim frame `F'`. Kore applies the unifier's whole
    /// substitution to the claim's right-hand side and keeps the configuration-variable binding
    /// in the result's condition (RewriteStep.hs:105-190 finalizeAppliedRule, :271
    /// resetResultPattern), so the successor is expressed over the subject's frame and the outer
    /// claim's destination `?_ F` covers it. Dropping the binding leaves the freshened claim
    /// frame free next to the subject frame and refutes the outer claim.
    #[cfg(feature = "z3")]
    #[test]
    fn applies_a_subject_variable_binding_to_the_claim_successor() {
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
                    \and{SortCfg{}}(cfg{}(start{}(I:SortInt{}), F:SortSet{}), \top{SortCfg{}}()),
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
            &definition.reachability_claims[0],
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
            &definition.reachability_claims[0],
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
            &definition.reachability_claims[0],
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
        let mut fresh = 0;

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
        else {
            panic!("the defining requires equality should instantiate the claim");
        };
        let [successor] = patterns.as_slice() else {
            panic!("expected one claim successor, found {patterns:?}");
        };
        assert_eq!(successor.term, term(&definition, "end{}(X:SortInt{})"));
        assert!(successor.constraints.is_empty());
        assert_eq!(
            successor.term.attributes().variables,
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
            validity: Ok(Validity::Indeterminate),
        };

        for solver in [&solver as &dyn SmtSolver, &NoSolver as &dyn SmtSolver] {
            let mut fresh = 0;
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
                vec![crate::rule::Predicate::Not(Box::new(expected.clone()))]
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
        let mut fresh = 0;

        assert!(matches!(
            apply_claim(
                &definition,
                claim_with_label(&definition, "guarded"),
                &subject,
                ProofOptions::default(),
                &solver,
                &mut fresh,
            ),
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
            &definition.reachability_claims[0],
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
        .expect("the destination check should run");
        assert_eq!(
            refutation.status,
            ImplicationStatus::Invalid,
            "{refutation:#?}"
        );
        assert_eq!(
            refutation.failure,
            Some(ImplicationFailure::ConsequentCondition),
            "{refutation:#?}"
        );
        let condition = refutation
            .condition
            .as_ref()
            .expect("a refutation reports the match it refuted");
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
                for stuck_check in [true, false] {
                    let options = ProofOptions {
                        allow_vacuous,
                        stuck_check,
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
            validity: Ok(Validity::Indeterminate),
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
                .contains(&crate::rule::Predicate::Not(Box::new(covered))),
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
    /// to `b()` and the stuck leaf (disproved) is at depth 1, not the stuck-check stop at depth 0.
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
            validity: Ok(Validity::Indeterminate),
        };
        for stuck_check in [true, false] {
            let result = prove_claim(
                &definition,
                claim_with_label(&definition, "rewritable"),
                ProofOptions {
                    stuck_check,
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
                    .contains(&crate::rule::Predicate::Not(Box::new(covered.clone()))),
                "{result:#?}"
            );
        }

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
                &definition.reachability_claims[0],
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
        let mut fresh = 0;

        let result = apply_claim(
            &definition,
            &definition.reachability_claims[0],
            &subject,
            ProofOptions {
                max_simplification_iterations: 1,
                ..ProofOptions::default()
            },
            &NoSolver,
            &mut fresh,
        );

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
            validity: Ok(Validity::Indeterminate),
        };

        let result = prove_claim(
            &definition,
            &definition.reachability_claims[0],
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

        let result = prove_claim(
            &definition,
            &definition.reachability_claims[0],
            ProofOptions::default(),
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

        let circularities = definition.reachability_claims.iter().collect::<Vec<_>>();
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
            validity: Ok(Validity::Indeterminate),
        };

        for claim in &definition.reachability_claims {
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
            validity: Ok(Validity::Indeterminate),
        };

        let result = prove_claim(
            &definition,
            &definition.reachability_claims[0],
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
            let claim = &definition.reachability_claims[0];

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

    #[test]
    fn trivial_sub_cases_of_a_mixed_group_fail_the_claim() {
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
        let claims = modal_claim(ReachabilityMode::AllPath, "a", "c", false);
        let definition = definition(rules, &claims);
        let claim = &definition.reachability_claims[0];

        let rejected = prove_claim(
            &definition,
            claim,
            ProofOptions {
                max_counterexamples: 2,
                ..ProofOptions::default()
            },
            &NoSolver,
        )
        .unwrap();
        assert_eq!(rejected.status, ProofStatus::Failed, "{rejected:#?}");
        assert!(
            rejected.leaves.iter().any(|leaf| {
                leaf.depth == 1 && matches!(leaf.outcome, ProofLeafOutcome::Trivial)
            })
        );

        let allowed = prove_claim(
            &definition,
            claim,
            ProofOptions {
                allow_vacuous: true,
                max_counterexamples: 2,
                ..ProofOptions::default()
            },
            &NoSolver,
        )
        .unwrap();
        assert_eq!(allowed.status, ProofStatus::Proven, "{allowed:#?}");
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
        let claim = &definition.reachability_claims[0];

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
        let claim = &syntactic_definition.reachability_claims[0];

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
        // The stuck `b()` carries `¬(opaque() = a())`, whose satisfiability rests on the
        // abstracted `opaque()`: the leaf fails the claim without certifying a refutation.
        assert_eq!(result.status, ProofStatus::Failed, "{result:#?}");
        assert!(result.leaves.iter().any(|leaf| {
            leaf.pattern.term == term(&definition, "c{}()")
                && leaf.pattern.constraints.contains(&requires)
                && matches!(leaf.outcome, ProofLeafOutcome::Proven(_))
                && leaf.trace.iter().any(|entry| {
                    entry.kind == TraceKind::Claim
                        && entry.label.as_deref() == Some("indeterminate-second")
                })
        }));
        assert!(result.leaves.iter().any(|leaf| {
            leaf.pattern.term == term(&definition, "b{}()")
                && leaf
                    .pattern
                    .constraints
                    .contains(&crate::rule::Predicate::Not(Box::new(requires.clone())))
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
            &stuck_definition.reachability_claims[0],
            ProofOptions::default(),
            &NoSolver,
        )
        .unwrap();
        let bounded = prove_claim(
            &bounded_definition,
            &bounded_definition.reachability_claims[0],
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
                outcome: ProofLeafOutcome::TimedOut(StepTimeoutMode::Manual(timeout)),
                ..
            }] if *timeout == Duration::from_millis(1)
        ));
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
            &definition.reachability_claims[0],
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
                outcome: ProofLeafOutcome::TimedOut(StepTimeoutMode::Manual(timeout)),
                ..
            }] if timeout.is_zero()
        ));
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
                &definition.reachability_claims[0],
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
                outcome: ProofLeafOutcome::TimedOut(StepTimeoutMode::Manual(timeout)),
                ..
            }] if *timeout == step_timeout
        ));
    }

    #[test]
    fn accepts_trusted_claims_without_exploration() {
        let claims = modal_claim(ReachabilityMode::AllPath, "a", "b", true);
        let definition = definition("", &claims);

        let result = prove_claim(
            &definition,
            &definition.reachability_claims[0],
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
    fn limits_live_breadth_and_collected_counterexamples() {
        let claims = modal_claim(ReachabilityMode::AllPath, "a", "c", false);
        let definition = definition(A_TO_B_AND_C, &claims);
        let claim = &definition.reachability_claims[0];

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
                &definition.reachability_claims[0],
                ProofOptions {
                    max_counterexamples: 0,
                    ..ProofOptions::default()
                },
                &NoSolver,
            ),
            Err(ProofError::ZeroCounterexampleLimit)
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
        let claim = &definition.reachability_claims[0];

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
    fn condition_stuck_check_can_be_disabled() {
        let claims = modal_claim(ReachabilityMode::OnePath, "a", "a", false);
        let mut definition = definition(A_TO_B, &claims);
        definition
            .reachability_claims
            .iter_mut()
            .find(|claim| claim.attributes.label.as_deref() == Some("one-a-a"))
            .expect("the target claim should be indexed")
            .rhs[0]
            .constraints
            .push(crate::rule::Predicate::False);

        let checked = prove_claim(
            &definition,
            claim_with_label(&definition, "one-a-a"),
            ProofOptions::default(),
            &NoSolver,
        )
        .unwrap();
        let unchecked = prove_claim(
            &definition,
            claim_with_label(&definition, "one-a-a"),
            ProofOptions {
                stuck_check: false,
                ..ProofOptions::default()
            },
            &NoSolver,
        )
        .unwrap();

        // The stuck check stops `a`, which still rewrites to `b`: not a refutation.
        assert_eq!(checked.status, ProofStatus::Failed);
        assert_eq!(checked.explored_states, 1);
        assert_eq!(checked.leaves[0].depth, 0);
        // `a` has the one successor `b`, which has none and is outside the empty destination:
        // the only path from `a` never reaches it, so the one-path claim is refuted.
        assert_eq!(unchecked.status, ProofStatus::Disproved);
        assert_eq!(unchecked.explored_states, 2);
        assert_eq!(unchecked.leaves[0].depth, 1);
        assert!(unchecked.leaves[0].certified);
    }

    #[test]
    fn applies_guarded_claim_circularities_only_after_a_semantic_step() {
        let claims = modal_claim(ReachabilityMode::OnePath, "a", "b", false);
        let definition = definition(A_TO_A, &claims);

        let result = prove_claim(
            &definition,
            &definition.reachability_claims[0],
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

    /// A remainder obligation that the solver refutes is partial coverage: the stuck check
    /// stops the uncovered part, and without it the part continues to rewriting.
    #[test]
    fn partial_destination_remainders_respect_the_stuck_check() {
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
            ) -> Result<Satisfiability, SmtError> {
                Ok(Satisfiability::Sat)
            }

            fn check_predicates(
                &self,
                _known: &[crate::rule::Predicate],
                _substitution: &Substitution,
                checked: &[crate::rule::Predicate],
            ) -> Result<Validity, SmtError> {
                Ok(match checked {
                    [crate::rule::Predicate::Equals(..)] => Validity::Invalid,
                    _ => Validity::Unknown("undecided".into()),
                })
            }
        }
        let refuted = RefutesTheObligation;
        let checked = prove_claim(
            &definition,
            &definition.reachability_claims[0],
            ProofOptions::default(),
            &refuted,
        )
        .expect("claim should execute");
        let unchecked = prove_claim(
            &definition,
            &definition.reachability_claims[0],
            ProofOptions {
                stuck_check: false,
                ..ProofOptions::default()
            },
            &refuted,
        )
        .expect("claim should execute without the stuck heuristic");

        // Neither leaf certifies a refutation: `X` has a sort without an SMT translation, and
        // the stuck check stops a state that still rewrites.
        assert_eq!(checked.status, ProofStatus::Failed);
        assert_eq!(checked.leaves[0].depth, 1);
        assert!(
            matches!(checked.leaves[0].outcome, ProofLeafOutcome::Stuck),
            "{checked:#?}"
        );
        assert_eq!(unchecked.status, ProofStatus::Failed);
        assert!(unchecked.leaves.iter().any(|leaf| {
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
        let claim = &definition.reachability_claims[0];

        let result = prove_claim(&definition, claim, ProofOptions::default(), &NoSolver)
            .expect("the claim should execute");

        // `partial(b())` is an unevaluated function application: the leaf may be empty.
        assert_eq!(result.status, ProofStatus::Failed, "{result:#?}");
        let [leaf] = result.leaves.as_slice() else {
            panic!("expected one leaf, found {:?}", result.leaves);
        };
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
}
