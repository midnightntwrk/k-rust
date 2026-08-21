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
    matching::{MatchMode, MatchResult, match_terms_in_definition},
    rewrite::{
        IndeterminateReason, Pattern, RewriteResult, TraceEntry, TraceKind, Truth,
        predicates_truth, recover_indeterminate_match, rewrite_step_with_solver,
        substitute_predicates,
    },
    simplify::{
        SimplificationError, SimplificationOptions, simplify_predicates_with_solver,
        simplify_with_solver,
    },
    smt::{SmtError, SmtSolver, Validity},
    substitution::{Substitution, substitute},
    term::Term,
    timeout::{StepTimeoutController, StepTimeoutMode, StepTimeoutOptions},
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
            max_simplification_iterations: 100,
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
    Match {
        substitution: Substitution,
        remainder: Vec<(Term, Term)>,
    },
    Requires(Vec<crate::rule::Predicate>),
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
            if counterexample_limit_reached(claim.mode, &leaves, options) {
                return Ok(finish(
                    claim.mode,
                    leaves,
                    explored_states,
                    pending.len() as u64,
                ));
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
                    return Ok(finish(
                        claim.mode,
                        leaves,
                        explored_states,
                        pending.len() as u64,
                    ));
                }
            };
        }
        let simplified_constraints = simplify_predicates_with_solver(
            definition,
            &state.pattern.constraints,
            &[],
            SimplificationOptions {
                max_iterations: options.max_simplification_iterations,
            },
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
        // An inconsistent claim antecedent is a valid implication. This is distinct from an
        // execution branch becoming bottom after a rewrite, which remains governed by
        // `allow_vacuous` below (matching the reference prover's custom-simplification tests).
        if state.depth == 0
            && state.trace.is_empty()
            && predicates_truth(&state.pattern.constraints) == Truth::False
        {
            let outcome = ProofLeafOutcome::Proven(ImplicationCondition {
                predicates: vec![crate::rule::Predicate::False],
                substitution: Default::default(),
            });
            record_leaf!(state.leaf(outcome));
            if claim.mode == ReachabilityMode::OnePath {
                return Ok(finish(claim.mode, leaves, explored_states, 0));
            }
            continue;
        }
        let simplified = simplify_with_solver(
            definition,
            &state.pattern.term,
            &state.pattern.constraints,
            SimplificationOptions {
                max_iterations: options.max_simplification_iterations,
            },
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

        if predicates_truth(&state.pattern.constraints) == Truth::False {
            let outcome = if options.allow_vacuous {
                ProofLeafOutcome::Proven(ImplicationCondition {
                    predicates: vec![crate::rule::Predicate::False],
                    substitution: Default::default(),
                })
            } else {
                ProofLeafOutcome::Vacuous
            };
            let proven = matches!(outcome, ProofLeafOutcome::Proven(_));
            record_leaf!(state.leaf(outcome));
            if proven && claim.mode == ReachabilityMode::OnePath {
                return Ok(finish(claim.mode, leaves, explored_states, 0));
            }
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
                },
                solver,
            );
            finish_if_timed_out!();
            let implication = implication.map_err(ProofError::Implication)?;
            match implication.status {
                ImplicationStatus::Valid => {
                    let condition = implication
                        .condition
                        .expect("a valid implication always has a condition");
                    record_leaf!(state.leaf(ProofLeafOutcome::Proven(condition)));
                    if claim.mode == ReachabilityMode::OnePath {
                        return Ok(finish(claim.mode, leaves, explored_states, 0));
                    }
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
            if extend_frontier(
                &mut pending,
                std::iter::once(state.remaining(remainder)),
                options.breadth_limit,
            ) {
                return Ok(finish_at_breadth_limit(
                    claim.mode,
                    leaves,
                    pending,
                    explored_states,
                ));
            }
            continue;
        }

        if state.depth >= options.max_depth {
            record_leaf!(state.leaf(ProofLeafOutcome::DepthBound));
            continue;
        }

        if state.depth > 0 {
            let mut claim_transition = None;
            for candidate in &definition.reachability_claims {
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
                    transition => {
                        claim_transition = Some((candidate, transition));
                        break;
                    }
                }
            }
            if let Some((candidate, transition)) = claim_transition {
                match transition {
                    ClaimApplication::Applied(patterns) => {
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
                                claim.mode,
                                leaves,
                                pending,
                                explored_states,
                            ));
                        }
                    }
                    ClaimApplication::Indeterminate(reason) => {
                        record_leaf!(state.leaf(ProofLeafOutcome::Indeterminate(
                            ProofIndeterminateReason::Claim {
                                claim_id: candidate.attributes.unique_id.clone(),
                                reason,
                            },
                        )));
                    }
                    ClaimApplication::NotApplicable => unreachable!(),
                }
                continue;
            }
        }

        let rewritten =
            rewrite_step_with_solver(definition, &state.pattern, &mut fresh_counter, solver);
        finish_if_timed_out!();
        match rewritten {
            RewriteResult::Finished(applied) => {
                if extend_frontier(
                    &mut pending,
                    std::iter::once(state.rewritten(applied)),
                    options.breadth_limit,
                ) {
                    return Ok(finish_at_breadth_limit(
                        claim.mode,
                        leaves,
                        pending,
                        explored_states,
                    ));
                }
            }
            RewriteResult::Branch {
                branches,
                remainder,
                ..
            } => {
                if extend_frontier(
                    &mut pending,
                    branches
                        .into_iter()
                        .map(|applied| state.clone().rewritten(applied)),
                    options.breadth_limit,
                ) {
                    return Ok(finish_at_breadth_limit(
                        claim.mode,
                        leaves,
                        pending,
                        explored_states,
                    ));
                }
                if let Some(remainder) = remainder {
                    if extend_frontier(
                        &mut pending,
                        std::iter::once(state.remaining(remainder)),
                        options.breadth_limit,
                    ) {
                        return Ok(finish_at_breadth_limit(
                            claim.mode,
                            leaves,
                            pending,
                            explored_states,
                        ));
                    }
                }
            }
            RewriteResult::Stuck(_) => {
                let outcome = if implication_indeterminate {
                    ProofLeafOutcome::Indeterminate(ProofIndeterminateReason::Implication)
                } else {
                    ProofLeafOutcome::Stuck
                };
                record_leaf!(state.leaf(outcome));
            }
            RewriteResult::Trivial(_) => record_leaf!(state.leaf(ProofLeafOutcome::Trivial)),
            RewriteResult::Vacuous(_) => {
                let outcome = if options.allow_vacuous {
                    ProofLeafOutcome::Proven(ImplicationCondition {
                        predicates: vec![crate::rule::Predicate::False],
                        substitution: Default::default(),
                    })
                } else {
                    ProofLeafOutcome::Vacuous
                };
                let proven = matches!(outcome, ProofLeafOutcome::Proven(_));
                record_leaf!(state.leaf(outcome));
                if proven && claim.mode == ReachabilityMode::OnePath {
                    return Ok(finish(claim.mode, leaves, explored_states, 0));
                }
            }
            RewriteResult::Indeterminate { reason, .. } => {
                record_leaf!(state.leaf(ProofLeafOutcome::Indeterminate(
                    ProofIndeterminateReason::Rewrite(reason),
                )));
            }
        }
    }

    Ok(finish(claim.mode, leaves, explored_states, 0))
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
    mode: ReachabilityMode,
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
    finish(mode, leaves, explored_states, unexplored_states)
}

fn counterexample_limit_reached(
    mode: ReachabilityMode,
    leaves: &[ProofLeaf],
    options: ProofOptions,
) -> bool {
    mode == ReachabilityMode::AllPath
        && leaves.iter().filter(|leaf| !closes_all_path(leaf)).count()
            >= options.max_counterexamples
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
    Applied(Vec<Pattern>),
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
            let recovered = recover_indeterminate_match(
                definition,
                substitution,
                remainder,
                &subject.constraints,
                SimplificationOptions {
                    max_iterations: options.max_simplification_iterations,
                },
                solver,
            );
            match recovered.result {
                MatchResult::Success(substitution) => (substitution, recovered.conditions),
                MatchResult::Failed(_) => return ClaimApplication::NotApplicable,
                MatchResult::Indeterminate {
                    substitution,
                    remainder,
                } => {
                    return ClaimApplication::Indeterminate(ClaimIndeterminateReason::Match {
                        substitution,
                        remainder,
                    });
                }
            }
        }
    };
    let mut requires = match_conditions;
    extend_unique(
        &mut requires,
        substitute_predicates(&claim.lhs.constraints, &substitution),
    );
    let requires = match simplify_predicates_with_solver(
        definition,
        &requires,
        &subject.constraints,
        SimplificationOptions {
            max_iterations: options.max_simplification_iterations,
        },
        solver,
    ) {
        Ok(requires) => requires,
        Err(_) => {
            return ClaimApplication::Indeterminate(ClaimIndeterminateReason::Requires(requires));
        }
    };
    match predicates_truth(&requires) {
        Truth::True => {}
        Truth::False => return ClaimApplication::NotApplicable,
        Truth::Unknown => {
            match solver.check_predicates(&subject.constraints, &Substitution::new(), &requires) {
                Ok(Validity::Valid) => {}
                Ok(Validity::Invalid | Validity::InconsistentGroundTruth) => {
                    return ClaimApplication::NotApplicable;
                }
                Ok(Validity::Indeterminate | Validity::Unknown(_)) => {
                    return ClaimApplication::Indeterminate(ClaimIndeterminateReason::Requires(
                        requires,
                    ));
                }
                Err(error) => {
                    return ClaimApplication::Indeterminate(ClaimIndeterminateReason::Smt(error));
                }
            }
        }
    }

    ClaimApplication::Applied(
        claim
            .rhs
            .iter()
            .map(|rhs| {
                let mut constraints = subject.constraints.clone();
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
    )
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
    let variables = claim
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
        .collect::<BTreeSet<_>>();
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

fn finish(
    mode: ReachabilityMode,
    leaves: Vec<ProofLeaf>,
    explored_states: u64,
    unexplored_states: u64,
) -> ProofResult {
    let any_proven = leaves.iter().any(is_proven);
    let any_disproved = leaves.iter().any(|leaf| {
        matches!(
            leaf.outcome,
            ProofLeafOutcome::Stuck | ProofLeafOutcome::Vacuous
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
    let status = match mode {
        ReachabilityMode::OnePath if any_proven => ProofStatus::Proven,
        ReachabilityMode::AllPath if any_disproved => ProofStatus::Disproved,
        _ if any_indeterminate => ProofStatus::Indeterminate,
        _ if any_depth_bound => ProofStatus::DepthBound,
        _ if any_breadth_bound => ProofStatus::BreadthBound,
        _ if unexplored_states > 0 => ProofStatus::Indeterminate,
        ReachabilityMode::AllPath if leaves.iter().all(closes_all_path) => ProofStatus::Proven,
        ReachabilityMode::OnePath => ProofStatus::Disproved,
        ReachabilityMode::AllPath => ProofStatus::Indeterminate,
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

fn closes_all_path(leaf: &ProofLeaf) -> bool {
    is_proven(leaf) || matches!(leaf.outcome, ProofLeafOutcome::Trivial)
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
    use crate::smt::{NoSolver, Satisfiability};

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

    fn definition(rules: &str, claims: &str) -> BackendDefinition {
        let source = format!(
            r#"[]
            module MAIN
                sort SortS{{}} []
                symbol a{{}}() : SortS{{}} [constructor{{}}()]
                symbol b{{}}() : SortS{{}} [constructor{{}}()]
                symbol c{{}}() : SortS{{}} [constructor{{}}()]
                {rules}
                {claims}
            endmodule []"#
        );
        let syntax = parse_definition(&source).expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    fn term(definition: &BackendDefinition, source: &str) -> Term {
        let syntax = parse_pattern(source).expect("term should parse");
        definition
            .internalize_term(&syntax, &[])
            .expect("term should internalize")
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
                },
            ),
            crate::rule::Predicate::And(vec![
                crate::rule::Predicate::Not(Box::new(first)),
                crate::rule::Predicate::Not(Box::new(second)),
            ]),
        );
    }

    #[test]
    fn trivial_successors_close_only_all_path_branches() {
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
            finish(ReachabilityMode::AllPath, vec![leaf.clone()], 1, 0).status,
            ProofStatus::Proven
        );
        assert_eq!(
            finish(ReachabilityMode::OnePath, vec![leaf], 1, 0).status,
            ProofStatus::Disproved
        );
    }

    #[cfg(feature = "z3")]
    #[test]
    fn proves_a_destination_covered_by_complementary_branches() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
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
                symbol mapUnit{}() : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.unit")]
                symbol mapItem{}(SortKey{}, SortValue{}) : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.element")]
                symbol mapConcat{}(SortMap{}, SortMap{}) : SortMap{}
                    [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
                symbol start{}(SortKey{}, SortMap{}) : SortState{} [constructor{}()]
                symbol done{}(SortMap{}) : SortState{} [constructor{}()]
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
    fn closes_explicit_bottom_rewrites_as_trivial() {
        let claims = modal_claim(ReachabilityMode::AllPath, "a", "b", false);
        let definition = definition(A_TO_BOTTOM, &claims);
        let claim = &definition.reachability_claims[0];

        let result = prove_claim(&definition, claim, ProofOptions::default(), &NoSolver).unwrap();

        assert_eq!(result.status, ProofStatus::Proven);
        assert!(matches!(
            result.leaves.as_slice(),
            [ProofLeaf {
                outcome: ProofLeafOutcome::Trivial,
                ..
            }]
        ));
    }

    #[test]
    fn proves_claims_with_inconsistent_initial_constraints() {
        let claims = r#"
            claim{} \implies{SortS{}}(
                \and{SortS{}}(\bottom{SortS{}}(), a{}()),
                weakAlwaysFinally{SortS{}}(
                    \and{SortS{}}(b{}(), \top{SortS{}}())
                )
            ) [label{}("false-antecedent")]
        "#;
        let definition = definition("", claims);
        let claim = &definition.reachability_claims[0];

        let result = prove_claim(&definition, claim, ProofOptions::default(), &NoSolver).unwrap();

        assert_eq!(result.status, ProofStatus::Proven);
        assert!(matches!(
            result.leaves.as_slice(),
            [ProofLeaf {
                outcome: ProofLeafOutcome::Proven(ImplicationCondition { predicates, .. }),
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
                symbol pow{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), total{}(), hook{}("INT.pow")]
                symbol state{}(SortInt{}) : SortState{} [constructor{}()]
                symbol done{}() : SortState{} [constructor{}()]
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
        let claims = modal_claim(ReachabilityMode::OnePath, "a", "c", false);
        let definition = definition(A_TO_B_AND_C, &claims);
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
        assert_eq!(breadth_first.explored_states, 3);
        assert_eq!(depth_first.explored_states, 2);
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
