//! Breadth-first reachability proof execution.

use std::{
    collections::{BTreeSet, VecDeque},
    error::Error,
    fmt,
    time::Duration,
};

use crate::{
    claim::{ReachabilityClaim, ReachabilityMode},
    definedness::ceil_term,
    definition::BackendDefinition,
    implication::{
        ImplicationCondition, ImplicationError, ImplicationFailure, ImplicationStatus,
        check_disjunctive_implication_with_existentials,
    },
    matching::{
        MatchMode, MatchResult, match_terms_in_definition, solve_collection_pairs_in_definition,
    },
    rewrite::{
        IndeterminateReason, Pattern, RemainderBranch, RewriteResult, TraceEntry, TraceKind, Truth,
        collection_unification_definedness, conjunctively_contains_alpha_equivalent,
        predicates_truth, quantify_introduced_variables, recover_indeterminate_match,
        rewrite_step_sequential_with_options, rewrite_step_with_options, substitute_predicates,
    },
    simplify::{
        DEFAULT_MAX_SIMPLIFICATION_ITERATIONS, SimplificationError, SimplificationOptions,
        simplify_predicates_with_solver, simplify_with_solver,
    },
    smt::{Satisfiability, SmtError, SmtSolver, Validity},
    substitution::{Substitution, compose, extract_substitution_for, substitute},
    term::{Term, TermKind},
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ProofStatus {
    Proven,
    Disproved,
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
    }]);
    let mut leaves = Vec::new();
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
    while let Some(mut state) = match options.search_order {
        ProofSearchOrder::BreadthFirst => pending.pop_front(),
        ProofSearchOrder::DepthFirst => pending.pop_back(),
    } {
        explored_states += 1;
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
            let implication = implication.map_err(ProofError::Implication)?;
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
                ImplicationStatus::Invalid if implication.condition.is_some() => {
                    let condition = implication
                        .condition
                        .expect("a partial implication carries its coverage condition");
                    let mut constraints = state.pattern.constraints.clone();
                    extend_unique(
                        &mut constraints,
                        vec![complement_implication_condition(&state.pattern, condition)],
                    );
                    let remainder = crate::rewrite::RemainderBranch {
                        pattern: Pattern {
                            term: state.pattern.term.clone(),
                            constraints,
                        },
                        rule_ids: vec![format!("destination:{}", claim.attributes.unique_id)],
                    };
                    if options.stuck_check {
                        record_leaf!(state.remaining(remainder).leaf(ProofLeafOutcome::Stuck));
                        continue;
                    }
                    implication_remainder = Some(remainder);
                }
                ImplicationStatus::Invalid
                    if options.stuck_check
                        && implication.failure == Some(ImplicationFailure::ConsequentCondition) =>
                {
                    record_leaf!(state.leaf(ProofLeafOutcome::Stuck));
                    continue;
                }
                ImplicationStatus::Invalid => {}
                ImplicationStatus::Indeterminate => implication_indeterminate = true,
            }
        }

        if let Some(remainder) = implication_remainder {
            // This is the part of the current state not covered by the destination,
            // not a new proof state. Continue the same iteration with the complement
            // attached so that rewriting gets a chance to make progress. Re-enqueuing
            // it would immediately repeat the same implication check forever.
            state = state.remaining(remainder);
        }

        if state.depth >= options.max_depth {
            record_leaf!(state.leaf(ProofLeafOutcome::DepthBound));
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
                            return Ok(finish_at_breadth_limit(leaves, pending, explored_states));
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
                            return Ok(finish_at_breadth_limit(leaves, pending, explored_states));
                        }
                    }
                    ClaimApplication::Indeterminate(_) | ClaimApplication::NotApplicable => {
                        unreachable!()
                    }
                }
                continue;
            }
        }

        let rewritten = match claim.mode {
            ReachabilityMode::OnePath => rewrite_step_sequential_with_options(
                definition,
                &state.pattern,
                &mut fresh_counter,
                SimplificationOptions::keep_partial(options.max_simplification_iterations),
                solver,
            ),
            ReachabilityMode::AllPath => rewrite_step_with_options(
                definition,
                &state.pattern,
                &mut fresh_counter,
                SimplificationOptions::keep_partial(options.max_simplification_iterations),
                solver,
            ),
        };
        finish_if_timed_out!();
        match rewritten {
            RewriteResult::Finished(applied) => {
                if extend_frontier(
                    &mut pending,
                    std::iter::once(state.rewritten(applied)),
                    options.breadth_limit,
                ) {
                    return Ok(finish_at_breadth_limit(leaves, pending, explored_states));
                }
            }
            RewriteResult::Branch {
                branches,
                remainder,
                trivial,
                ..
            } => {
                if extend_frontier(
                    &mut pending,
                    branches
                        .into_iter()
                        .map(|applied| state.clone().rewritten(applied)),
                    options.breadth_limit,
                ) {
                    return Ok(finish_at_breadth_limit(leaves, pending, explored_states));
                }
                if let Some(remainder) = remainder
                    && extend_frontier(
                        &mut pending,
                        std::iter::once(state.clone().remaining(remainder)),
                        options.breadth_limit,
                    )
                {
                    return Ok(finish_at_breadth_limit(leaves, pending, explored_states));
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
                    ProofLeafOutcome::Stuck
                };
                record_leaf!(state.leaf(outcome));
            }
            RewriteResult::Trivial(_) => {
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
                let reason = match reason {
                    IndeterminateReason::Simplification { error, .. } => {
                        ProofIndeterminateReason::Simplification(error)
                    }
                    reason => ProofIndeterminateReason::Rewrite(reason),
                };
                record_leaf!(state.leaf(ProofLeafOutcome::Indeterminate(reason,)));
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
    mut leaves: Vec<ProofLeaf>,
    pending: VecDeque<ProofState>,
    explored_states: u64,
) -> ProofResult {
    let unexplored_states = pending.len() as u64;
    leaves.extend(
        pending
            .into_iter()
            .map(|state| state.leaf(ProofLeafOutcome::BreadthBound)),
    );
    finish(leaves, explored_states, unexplored_states)
}

fn counterexample_limit_reached(leaves: &[ProofLeaf], options: ProofOptions) -> bool {
    leaves.iter().filter(|leaf| !is_proven(leaf)).count() >= options.max_counterexamples
}

#[derive(Clone)]
struct ProofState {
    pattern: Pattern,
    depth: u64,
    trace: Vec<TraceEntry>,
}

impl ProofState {
    fn leaf(self, outcome: ProofLeafOutcome) -> ProofLeaf {
        ProofLeaf {
            pattern: self.pattern,
            depth: self.depth,
            trace: self.trace,
            outcome,
        }
    }

    fn rewritten(mut self, applied: crate::rewrite::AppliedRule) -> Self {
        self.depth += 1;
        self.trace.push(TraceEntry {
            depth: self.depth,
            kind: TraceKind::Rewrite,
            label: applied.label,
            unique_id: applied.unique_id,
        });
        self.pattern = applied.pattern;
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
        self
    }

    fn remaining(mut self, remainder: crate::rewrite::RemainderBranch) -> Self {
        self.trace.push(TraceEntry {
            depth: self.depth,
            kind: TraceKind::Remainder,
            label: None,
            unique_id: remainder.rule_ids.join(","),
        });
        self.pattern = remainder.pattern;
        self
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
    let complement = complement.filter(|negated| {
        !remainder_is_unsatisfiable(definition, subject, negated, simplification, solver)
    });
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
/// it together with the subject's constraints; an undecided or unavailable solver keeps it.
fn remainder_is_unsatisfiable(
    definition: &BackendDefinition,
    subject: &Pattern,
    negated: &crate::rule::Predicate,
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> bool {
    let simplified = match simplify_predicates_with_solver(
        definition,
        std::slice::from_ref(negated),
        &subject.constraints,
        options,
        solver,
    ) {
        Ok(simplified) => simplified,
        Err(_) => return false,
    };
    if predicates_truth(&simplified) == Truth::False {
        return true;
    }
    let mut constraints = subject.constraints.clone();
    extend_unique(&mut constraints, simplified);
    matches!(
        solver.is_sat(&constraints, &Substitution::new()),
        Ok(Satisfiability::Unsat)
    )
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
        let name = loop {
            let name = format!("{}!claim{}", variable.name, *fresh_counter);
            *fresh_counter += 1;
            if names.insert(name.as_str().into()) {
                break name;
            }
        };
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
    let any_disproved = leaves.iter().any(|leaf| {
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
    let status = if any_disproved {
        ProofStatus::Disproved
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

fn complement_implication_condition(
    pattern: &Pattern,
    condition: ImplicationCondition,
) -> crate::rule::Predicate {
    let mut covered = conjoin_predicates(condition.predicates);
    let state_variables = pattern
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
        .collect::<BTreeSet<_>>();
    let introduced = covered
        .free_variables()
        .difference(&state_variables)
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

    #[test]
    fn trivial_successors_refute_both_modes() {
        let definition = definition("", "");
        let leaf = ProofLeaf {
            pattern: Pattern {
                term: term(&definition, "a{}()"),
                constraints: Vec::new(),
            },
            depth: 1,
            trace: Vec::new(),
            outcome: ProofLeafOutcome::Trivial,
        };

        assert_eq!(
            finish(vec![leaf.clone()], 1, 0).status,
            ProofStatus::Disproved
        );
        assert_eq!(finish(vec![leaf], 1, 0).status, ProofStatus::Disproved);
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
            &definition.reachability_claims[0],
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
            &definition.reachability_claims[0],
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
            &definition.reachability_claims[1],
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
                &definition.reachability_claims[2],
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
                &definition.reachability_claims[2],
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

        let isolated = [&definition.reachability_claims[0]];
        let result = super::prove_claim(
            &definition,
            &definition.reachability_claims[0],
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
            &definition.reachability_claims[0],
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

            assert_eq!(result.status, ProofStatus::Disproved, "{result:#?}");
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

        let first = prove_claim(
            &definition,
            &definition.reachability_claims[0],
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
            &definition.reachability_claims[1],
            ProofOptions::default(),
            &NoSolver,
        )
        .expect("second overlapping claim should execute");
        assert_eq!(second.status, ProofStatus::Disproved, "{second:#?}");
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

        assert_eq!(result.status, ProofStatus::Disproved, "{result:#?}");
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
        let trusted = if trusted {
            "trusted{}()"
        } else {
            "label{}(\"claim\")"
        };
        format!(
            r#"claim{{}} \implies{{SortS{{}}}}(
                \and{{SortS{{}}}}(\top{{SortS{{}}}}(), {left}{{}}()),
                {modality}{{SortS{{}}}}(
                    \and{{SortS{{}}}}({right}{{}}(), \top{{SortS{{}}}}())
                )
            ) [{trusted}]"#
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
            assert_eq!(rejected.status, ProofStatus::Disproved, "{rejected:#?}");
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
    fn trivial_sub_cases_of_a_mixed_group_refute_the_claim() {
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
        assert_eq!(rejected.status, ProofStatus::Disproved, "{rejected:#?}");
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
        assert_eq!(rejected.status, ProofStatus::Disproved, "{rejected:#?}");
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
            &definition.reachability_claims[0],
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
            &definition.reachability_claims[0],
            ProofOptions::default(),
            &NoSolver,
        )
        .unwrap();
        let rewritten = prove_claim(
            &definition,
            &definition.reachability_claims[1],
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
                \and{SortS{}}(b{}(), \top{SortS{}}()),
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
            &definition.reachability_claims[0],
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
            &definition.reachability_claims[0],
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
            &definition.reachability_claims[0],
            ProofOptions::default(),
            &NoSolver,
        )
        .unwrap();

        let requires = crate::rule::Predicate::Equals(
            term(&definition, "opaque{}()"),
            term(&definition, "a{}()"),
        );
        assert_eq!(result.status, ProofStatus::Disproved, "{result:#?}");
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
            &definition.reachability_claims[0],
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
        let claims = [
            modal_claim(ReachabilityMode::OnePath, "a", "b", false),
            modal_claim(ReachabilityMode::AllPath, "a", "b", false),
        ]
        .join("\n");
        let definition = definition(A_TO_B_AND_C, &claims);

        let one_path = prove_claim(
            &definition,
            &definition.reachability_claims[0],
            ProofOptions::default(),
            &NoSolver,
        )
        .unwrap();
        let all_path = prove_claim(
            &definition,
            &definition.reachability_claims[1],
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
        definition.reachability_claims[0].rhs[0]
            .constraints
            .push(crate::rule::Predicate::False);

        let checked = prove_claim(
            &definition,
            &definition.reachability_claims[0],
            ProofOptions::default(),
            &NoSolver,
        )
        .unwrap();
        let unchecked = prove_claim(
            &definition,
            &definition.reachability_claims[0],
            ProofOptions {
                stuck_check: false,
                ..ProofOptions::default()
            },
            &NoSolver,
        )
        .unwrap();

        assert_eq!(checked.status, ProofStatus::Disproved);
        assert_eq!(checked.explored_states, 1);
        assert_eq!(checked.leaves[0].depth, 0);
        assert_eq!(unchecked.status, ProofStatus::Disproved);
        assert_eq!(unchecked.explored_states, 2);
        assert_eq!(unchecked.leaves[0].depth, 1);
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
            &definition.reachability_claims[0],
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

        let checked = prove_claim(
            &definition,
            &definition.reachability_claims[0],
            ProofOptions::default(),
            &NoSolver,
        )
        .expect("claim should execute");
        let unchecked = prove_claim(
            &definition,
            &definition.reachability_claims[0],
            ProofOptions {
                stuck_check: false,
                ..ProofOptions::default()
            },
            &NoSolver,
        )
        .expect("claim should execute without the stuck heuristic");

        assert_eq!(checked.status, ProofStatus::Disproved);
        assert_eq!(checked.leaves[0].depth, 1);
        assert!(matches!(checked.leaves[0].outcome, ProofLeafOutcome::Stuck));
        assert_eq!(unchecked.status, ProofStatus::Disproved);
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
}
