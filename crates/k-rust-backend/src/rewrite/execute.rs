//! Depth-first exploration of the rewrite tree (stack discipline) with a per-state pipeline and
//! Kore's got-stuck-over-depth-bound leaf selection and equal-leaf merge (Booster performRewrite;
//! Kore GraphTraversal.checkLeftUnproven): O(states) steps, states <= branching^depth bounded by
//! `max_depth` and `max_breadth`, each state one term simplification, one predicate pass, and one
//! rewrite step; `Counter::RewriteSteps` (row B11). Not breadth-first: `enqueue_execution_states`
//! pushes successors to the front, so children are visited before siblings.

use std::collections::{BTreeSet, VecDeque};

use k_rust_kore::measure::{self, Counter};

use crate::{
    builtin::BuiltinEffect,
    cancellation::cancellation_requested,
    definition::BackendDefinition,
    rule::Predicate,
    simplify::{
        PatternSimplification, SimplificationError, SimplificationOptions,
        simplify_in_execution_with_solver, simplify_pattern_details_with_solver,
        simplify_predicates_with_solver, simplify_with_solver,
    },
    smt::SmtSolver,
    timeout::{StepTimeoutController, StepTimeoutOptions},
    transition::{
        EffectJournal, ExecutionIoState, ObservationHead, ObservationLog, ObservationOptions,
        PatternDigest, TransitionId, UncommittedObservation, UncommittedReason,
    },
};

use super::{
    AppliedRule, ExecutionBranchMode, ExecutionLeaf, ExecutionMode, ExecutionOptions,
    ExecutionResult, HaltReason, IndeterminateReason, InitialSimplificationStatus, Pattern,
    RemainderBranch, RewriteResult, TraceEntry, TraceKind, TrivialApplication, Truth,
    applied_trivial_halt, normalize_pattern_substitution, predicates_truth,
    retain_substitution_predicates, rewrite_step_with_mode, rewrite_step_with_optional_execution,
    trivial_halt, vacuous_halt,
};

pub(super) fn execute_using(
    definition: &BackendDefinition,
    initial: Vec<Pattern>,
    options: ExecutionOptions,
    solver: &dyn SmtSolver,
    initial_io: Option<ExecutionIoState>,
    observation: Option<&ObservationOptions>,
    mut observe: impl FnMut(&BuiltinEffect),
) -> (ExecutionResult, InitialSimplificationStatus) {
    let mut fresh_counter = 0;
    let mut observation_log = ObservationLog::default();
    let initial_input_count = initial.len();
    let has_execution_io = initial_io.is_some();
    let initial_io = initial_io.unwrap_or_default();
    let mut pending = initial
        .into_iter()
        .map(|pattern| {
            let io_enabled = has_execution_io && pattern_supports_execution_io(&pattern);
            ExecutionState {
                pattern,
                depth: 0,
                trace: Vec::new(),
                observation: None,
                effects: EffectJournal::default(),
                io: initial_io.clone(),
                io_enabled,
                is_initial_input: true,
            }
        })
        .collect::<VecDeque<_>>();
    let mut leaves = SelectedExecutionLeaves::default();
    let mut discarded = Vec::new();
    let mut completed_initial_simplifications = 0;
    let mut bottom_initial_simplifications = 0;
    let timeout_controller = StepTimeoutController::new(StepTimeoutOptions {
        manual: options.step_timeout,
        moving_average: options.moving_average_timeout,
    });
    let mut validated = VecDeque::with_capacity(pending.len());
    while let Some(state) = pending.pop_front() {
        if let Some(symbol) = state.pattern.macro_or_alias_symbol() {
            leaves.push(state.leaf(
                HaltReason::Indeterminate(IndeterminateReason::SurvivingMacroOrAlias { symbol }),
                &observation_log,
            ));
        } else {
            validated.push_back(state);
        }
    }
    pending = validated;
    if options.max_breadth == Some(0) {
        let mut bounded = leaves.into_inner();
        bounded.extend(
            pending
                .drain(..)
                .map(|state| execution_state_at_breadth_bound(state, &observation_log)),
        );
        return (
            ExecutionResult {
                leaves: merge_equal_final_leaves(bounded),
                effects: Vec::new(),
                discarded,
            },
            InitialSimplificationStatus {
                simplified_to_bottom: false,
            },
        );
    }
    // `pending` is a stack: `enqueue_execution_states` pushes successors to the front, so a state's
    // children are expanded before its siblings (depth-first). Each push either raises the depth,
    // which `max_depth` bounds, or consumes a remainder, so the loop terminates.
    // Invariant: `pending` holds unexpanded states of depth <= `max_depth`; `leaves` only grows.
    while let Some(mut state) = pending.pop_front() {
        measure::bump(Counter::RewriteSteps);
        let mut step_timer = timeout_controller.begin_step();
        macro_rules! finish_if_interrupted {
            () => {
                if cancellation_requested() {
                    step_timer.discard_measurement();
                    leaves.push(state.leaf(HaltReason::Cancelled, &observation_log));
                    continue;
                }
                if let Some(mode) = step_timer.timed_out() {
                    step_timer.discard_measurement();
                    leaves.push(state.leaf(HaltReason::Timeout(mode), &observation_log));
                    continue;
                }
            };
        }
        finish_if_interrupted!();
        if let Some(symbol) = state.pattern.macro_or_alias_symbol() {
            leaves.push(state.leaf(
                HaltReason::Indeterminate(IndeterminateReason::SurvivingMacroOrAlias { symbol }),
                &observation_log,
            ));
            continue;
        }
        let retained_substitution =
            normalize_pattern_substitution(&mut state.pattern, &definition.sort_graph);
        let pattern_before_constraint_simplification = state.pattern.clone();
        let mut deferred_initial_vacuity = None;
        let simplified_constraints = simplify_predicates_with_solver(
            definition,
            &state.pattern.constraints,
            &[],
            SimplificationOptions::keep_partial(options.max_simplification_iterations),
            solver,
        );
        finish_if_interrupted!();
        match simplified_constraints {
            Ok(mut constraints) => {
                retain_substitution_predicates(
                    &mut constraints,
                    &retained_substitution,
                    &definition.sort_graph,
                );
                state.pattern.constraints = constraints;
                normalize_pattern_substitution(&mut state.pattern, &definition.sort_graph);
            }
            Err(error) => {
                leaves.push(state.leaf(HaltReason::Simplification(error), &observation_log));
                continue;
            }
        }
        if predicates_truth(&state.pattern.constraints) == Truth::False {
            if state.depth == 0 && !retained_substitution.is_empty() {
                // Booster applies an input substitution before rewriting, but a contradiction
                // exposed only by that substitution does not prevent the first rewrite attempt.
                // If no rule applies, the simplified state below is still returned as vacuous.
                deferred_initial_vacuity = Some(state.pattern.clone());
                state.pattern = pattern_before_constraint_simplification;
            } else {
                if state.is_initial_input {
                    completed_initial_simplifications += 1;
                    bottom_initial_simplifications += 1;
                }
                let applied = state
                    .trace
                    .iter()
                    .rev()
                    .find(|entry| entry.kind == TraceKind::Rewrite);
                let refuted_ceil = pattern_before_constraint_simplification
                    .constraints
                    .iter()
                    .find(|predicate| matches!(predicate, Predicate::Ceil(_)));
                let halt_reason = match (applied, refuted_ceil) {
                    (Some(applied), Some(obligation)) => HaltReason::Trivial {
                        depth: state.depth,
                        rule_id: Some(applied.unique_id.clone()),
                        label: applied.label.clone(),
                        obligation: obligation.clone(),
                    },
                    _ => vacuous_halt(state.depth, &state.pattern, &state.trace),
                };
                leaves.push(state.leaf(halt_reason, &observation_log));
                continue;
            }
        }
        let pattern_before_term_simplification = state.pattern.clone();
        state.io_enabled &= pattern_supports_execution_io(&state.pattern);
        let mut io_evaluation = state.io_enabled.then(|| state.io.begin_evaluation());
        let simplified = match io_evaluation.as_mut() {
            Some(execution) => simplify_in_execution_with_solver(
                definition,
                &state.pattern.term,
                &state.pattern.constraints,
                SimplificationOptions::keep_partial(options.max_simplification_iterations),
                solver,
                execution,
            ),
            None => simplify_with_solver(
                definition,
                &state.pattern.term,
                &state.pattern.constraints,
                SimplificationOptions::keep_partial(options.max_simplification_iterations),
                solver,
            ),
        };
        finish_if_interrupted!();
        let undefined_term = match simplified {
            Ok(simplified) => {
                let undefined_term = simplified.undefined_term.clone();
                state.pattern.term = simplified.term;
                state.pattern.constraints.extend(simplified.constraints);
                normalize_pattern_substitution(&mut state.pattern, &definition.sort_graph);
                state.observation = observation_log.append_simplification(
                    state.observation,
                    definition,
                    pattern_before_term_simplification,
                    &state.pattern,
                    &simplified.applied_rules,
                    &simplified.effects,
                    observation,
                );
                state.effects.commit(simplified.effects);
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
                undefined_term
            }
            Err(error) => {
                leaves.push(state.leaf(HaltReason::Simplification(error), &observation_log));
                continue;
            }
        };
        if state.is_initial_input {
            completed_initial_simplifications += 1;
            if deferred_initial_vacuity.is_none()
                && predicates_truth(&state.pattern.constraints) == Truth::False
            {
                bottom_initial_simplifications += 1;
                let halt_reason = vacuous_halt(state.depth, &state.pattern, &state.trace);
                leaves.push(state.leaf(halt_reason, &observation_log));
                continue;
            }
        }
        if predicates_truth(&state.pattern.constraints) == Truth::False {
            if let Some(term) = undefined_term {
                let applied = state
                    .trace
                    .iter()
                    .rev()
                    .find(|entry| entry.kind == TraceKind::Rewrite);
                let halt_reason = HaltReason::Trivial {
                    depth: state.depth,
                    rule_id: applied.map(|entry| entry.unique_id.clone()),
                    label: applied.and_then(|entry| entry.label.clone()),
                    obligation: Predicate::Ceil(term),
                };
                leaves.push(state.leaf(halt_reason, &observation_log));
                continue;
            }
        }
        if let Some(execution) = io_evaluation {
            state.io = execution.commit();
        }
        state.io_enabled &= pattern_supports_execution_io(&state.pattern);
        if state.depth >= options.max_depth {
            let pattern = state.pattern.clone();
            leaves.push(externalise_leaf(
                definition,
                state,
                pattern,
                HaltReason::DepthBound,
                options.max_simplification_iterations,
                solver,
                &mut observation_log,
                observation,
            ));
            continue;
        }
        let rewritten = rewrite_step_with_optional_execution(
            definition,
            &state.pattern,
            &mut fresh_counter,
            SimplificationOptions::keep_partial(options.max_simplification_iterations),
            solver,
            options.mode,
            options.assume_initial_defined,
            state.io_enabled.then_some(&state.io),
        );
        finish_if_interrupted!();
        match rewritten {
            RewriteResult::Stuck(pattern) => match deferred_initial_vacuity {
                Some(pattern) => {
                    let halt_reason = vacuous_halt(state.depth, &pattern, &state.trace);
                    leaves.push(state.leaf_with_pattern(pattern, halt_reason, &observation_log));
                }
                None => leaves.push(externalise_leaf(
                    definition,
                    state,
                    pattern,
                    HaltReason::Stuck,
                    options.max_simplification_iterations,
                    solver,
                    &mut observation_log,
                    observation,
                )),
            },
            RewriteResult::Trivial(pattern, applications) => {
                record_trivial_candidates(&mut discarded, &applications, &pattern, observation);
                let halt_reason = applications
                    .first()
                    .map(|application| applied_trivial_halt(state.depth + 1, application))
                    .unwrap_or_else(|| trivial_halt(state.depth + 1, &pattern));
                leaves.push(state.leaf_with_pattern(pattern, halt_reason, &observation_log))
            }
            RewriteResult::Vacuous(pattern) => {
                let halt_reason = vacuous_halt(state.depth, &pattern, &state.trace);
                leaves.push(state.leaf_with_pattern(pattern, halt_reason, &observation_log))
            }
            RewriteResult::Indeterminate { pattern, reason } => match reason {
                // The simplifier already failed on this state; the leaf reports that failure
                // and is not simplified again.
                IndeterminateReason::Simplification { error, .. } => {
                    leaves.push(state.leaf_with_pattern(
                        pattern,
                        HaltReason::Simplification(error),
                        &observation_log,
                    ));
                }
                reason => leaves.push(externalise_leaf(
                    definition,
                    state,
                    pattern,
                    HaltReason::Indeterminate(reason),
                    options.max_simplification_iterations,
                    solver,
                    &mut observation_log,
                    observation,
                )),
            },
            RewriteResult::Finished(applied) => {
                if let Some(rule) = selected_stop_rule(&applied, &options.cut_point_rules) {
                    let mut applied = applied;
                    state.effects.commit(applied.effects.iter().cloned());
                    state.observation =
                        observation_log.append_applied(state.observation, &applied, observation);
                    applied.pattern = match simplify_result_pattern(
                        definition,
                        &applied.pattern,
                        options.max_simplification_iterations,
                        solver,
                        state.depth,
                        &mut state.trace,
                        Some(&mut state.observation),
                        &mut observation_log,
                        observation,
                    ) {
                        Ok(simplified) => {
                            state.effects.commit(simplified.effects);
                            simplified.pattern
                        }
                        Err(error) => {
                            leaves.push(state.leaf_with_pattern(
                                applied.pattern,
                                HaltReason::Simplification(error),
                                &observation_log,
                            ));
                            continue;
                        }
                    };
                    finish_if_interrupted!();
                    if predicates_truth(&applied.pattern.constraints) == Truth::False {
                        let halt_reason = trivial_halt(state.depth + 1, &applied.pattern);
                        leaves.push(state.leaf_with_pattern(
                            applied.pattern,
                            halt_reason,
                            &observation_log,
                        ));
                        continue;
                    }
                    leaves.push(state.leaf(
                        HaltReason::CutPointRule {
                            rule,
                            next_states: vec![applied],
                        },
                        &observation_log,
                    ));
                    continue;
                }
                let terminal_rule = selected_stop_rule(&applied, &options.terminal_rules);
                let mut next = next_state(state, applied, &mut observation_log, observation);
                if let Some(rule) = terminal_rule {
                    next.pattern = match simplify_result_pattern(
                        definition,
                        &next.pattern,
                        options.max_simplification_iterations,
                        solver,
                        next.depth,
                        &mut next.trace,
                        Some(&mut next.observation),
                        &mut observation_log,
                        observation,
                    ) {
                        Ok(simplified) => {
                            next.effects.commit(simplified.effects);
                            simplified.pattern
                        }
                        Err(error) => {
                            leaves.push(
                                next.leaf(HaltReason::Simplification(error), &observation_log),
                            );
                            continue;
                        }
                    };
                    if cancellation_requested() {
                        step_timer.discard_measurement();
                        leaves.push(next.leaf(HaltReason::Cancelled, &observation_log));
                        continue;
                    }
                    if let Some(mode) = step_timer.timed_out() {
                        step_timer.discard_measurement();
                        leaves.push(next.leaf(HaltReason::Timeout(mode), &observation_log));
                        continue;
                    }
                    let trivial = predicates_truth(&next.pattern.constraints) == Truth::False;
                    let halt_reason = if trivial {
                        trivial_halt(next.depth, &next.pattern)
                    } else {
                        HaltReason::TerminalRule { rule }
                    };
                    leaves.push(next.leaf(halt_reason, &observation_log));
                    continue;
                }
                enqueue_execution_states(&mut pending, vec![next]);
                if execution_breadth_exceeded(
                    &mut pending,
                    &mut leaves,
                    options.max_breadth,
                    &observation_log,
                ) {
                    break;
                }
            }
            RewriteResult::Branch {
                original,
                mut branches,
                mut remainder,
                trivial,
            } => {
                record_trivial_candidates(&mut discarded, &trivial, &original, observation);
                if options.branch_mode == ExecutionBranchMode::StopAtBranch {
                    if let Err(error) = expand_stopped_branch_remainder(
                        definition,
                        &mut branches,
                        &mut remainder,
                        &mut fresh_counter,
                        SimplificationOptions::keep_partial(options.max_simplification_iterations),
                        solver,
                        (options.mode, options.assume_initial_defined),
                    ) {
                        leaves
                            .push(state.leaf(HaltReason::Simplification(error), &observation_log));
                        continue;
                    }
                    let mut original = original;
                    original = match simplify_result_pattern(
                        definition,
                        &original,
                        options.max_simplification_iterations,
                        solver,
                        state.depth,
                        &mut state.trace,
                        Some(&mut state.observation),
                        &mut observation_log,
                        observation,
                    ) {
                        Ok(simplified) => {
                            state.effects.commit(simplified.effects);
                            simplified.pattern
                        }
                        Err(error) => {
                            leaves.push(state.leaf_with_pattern(
                                original,
                                HaltReason::Simplification(error),
                                &observation_log,
                            ));
                            continue;
                        }
                    };
                    if predicates_truth(&original.constraints) == Truth::False {
                        let halt_reason = trivial_halt(state.depth, &original);
                        leaves.push(state.leaf_with_pattern(
                            original,
                            halt_reason,
                            &observation_log,
                        ));
                        continue;
                    }
                    // A branch point is reported as a single leaf for the parent state. When
                    // any successor fails to simplify, the failure is likewise recorded at the
                    // parent: a leaf for one successor would silently discard its siblings and
                    // the remainder, which are all still reachable from the parent.
                    let mut simplified_branches = Vec::with_capacity(branches.len());
                    let mut failed_branch = None;
                    for mut applied in branches {
                        let attempted_id = TransitionId {
                            rule: applied.unique_id.clone(),
                            target: PatternDigest::of(&applied.pattern),
                        };
                        match simplify_result_pattern(
                            definition,
                            &applied.pattern,
                            options.max_simplification_iterations,
                            solver,
                            state.depth + 1,
                            &mut state.trace,
                            None,
                            &mut observation_log,
                            observation,
                        ) {
                            Ok(simplified) => {
                                applied.pattern = simplified.pattern;
                                applied.effects.extend(simplified.effects);
                                if predicates_truth(&applied.pattern.constraints) != Truth::False {
                                    simplified_branches.push(applied);
                                } else if observation
                                    .is_some_and(|options| options.observes(&applied.unique_id))
                                {
                                    discarded.push(UncommittedObservation {
                                        id: attempted_id,
                                        rule_label: applied.label,
                                        effects: applied.effects,
                                        reason: UncommittedReason::RolledBack,
                                    });
                                }
                            }
                            Err(error) => {
                                failed_branch = Some(error);
                                break;
                            }
                        }
                    }
                    if let Some(error) = failed_branch {
                        leaves.push(state.leaf_with_pattern(
                            original,
                            HaltReason::Simplification(error),
                            &observation_log,
                        ));
                        continue;
                    }
                    branches = simplified_branches;
                    if let Some(candidate) = &mut remainder {
                        candidate.pattern = match simplify_result_pattern(
                            definition,
                            &candidate.pattern,
                            options.max_simplification_iterations,
                            solver,
                            state.depth,
                            &mut state.trace,
                            None,
                            &mut observation_log,
                            observation,
                        ) {
                            Ok(simplified) => {
                                candidate.effects.extend(simplified.effects);
                                simplified.pattern
                            }
                            Err(error) => {
                                leaves.push(state.leaf_with_pattern(
                                    original,
                                    HaltReason::Simplification(error),
                                    &observation_log,
                                ));
                                continue;
                            }
                        };
                        if predicates_truth(&candidate.pattern.constraints) == Truth::False {
                            remainder = None;
                        }
                    }
                    finish_if_interrupted!();
                    match (branches.len(), remainder.is_some()) {
                        (0, false) => {
                            leaves.push(state.leaf_with_pattern(
                                original,
                                HaltReason::Stuck,
                                &observation_log,
                            ));
                        }
                        (1, false) => {
                            let applied = branches.pop().expect("one branch remains");
                            enqueue_execution_states(
                                &mut pending,
                                vec![next_state(
                                    state,
                                    applied,
                                    &mut observation_log,
                                    observation,
                                )],
                            );
                        }
                        (0, true) => {
                            let remainder = remainder.take().expect("one remainder remains");
                            let before = state.pattern.clone();
                            enqueue_execution_states(
                                &mut pending,
                                vec![remaining_state(
                                    state,
                                    before,
                                    remainder,
                                    &mut observation_log,
                                    observation,
                                )],
                            );
                        }
                        _ => {
                            leaves.push(state.leaf_with_pattern(
                                original,
                                HaltReason::Branch {
                                    branches,
                                    remainder,
                                },
                                &observation_log,
                            ));
                        }
                    }
                    continue;
                }
                let mut next =
                    Vec::with_capacity(branches.len() + usize::from(remainder.is_some()));
                for applied in branches {
                    next.push(next_state(
                        state.clone(),
                        applied,
                        &mut observation_log,
                        observation,
                    ));
                }
                if let Some(remainder) = remainder {
                    let before = state.pattern.clone();
                    next.push(remaining_state(
                        state,
                        before,
                        remainder,
                        &mut observation_log,
                        observation,
                    ));
                }
                enqueue_execution_states(&mut pending, next);
                if execution_breadth_exceeded(
                    &mut pending,
                    &mut leaves,
                    options.max_breadth,
                    &observation_log,
                ) {
                    break;
                }
            }
        }
    }
    let leaves = merge_equal_final_leaves(select_got_stuck_over_depth_bound(leaves.into_inner()));
    // The legacy observer is a single-stream interface. It receives a transcript only when final
    // selection retained one leaf; callers consume multi-leaf transcripts from each leaf.
    let effects = match leaves.as_slice() {
        [leaf] => leaf.effects.clone(),
        _ => Vec::new(),
    };
    for effect in &effects {
        observe(effect);
    }
    (
        ExecutionResult {
            leaves,
            effects,
            discarded,
        },
        InitialSimplificationStatus {
            simplified_to_bottom: initial_input_count != 0
                && completed_initial_simplifications == initial_input_count
                && bottom_initial_simplifications == initial_input_count,
        },
    )
}

fn pattern_supports_execution_io(pattern: &Pattern) -> bool {
    pattern.constraints.is_empty() && pattern.term.attributes().variables.is_empty()
}

/// Kore's `GraphTraversal.checkLeftUnproven` reports stuck and vacuous results in
/// preference to states that merely reached the depth bound. Apply that selection before
/// deduplication so an equal depth-bounded leaf cannot hide a later stuck leaf.
fn select_got_stuck_over_depth_bound(mut leaves: Vec<ExecutionLeaf>) -> Vec<ExecutionLeaf> {
    let got_stuck = leaves.iter().any(|leaf| {
        matches!(
            leaf.halt_reason,
            HaltReason::Stuck | HaltReason::Trivial { .. } | HaltReason::Vacuous { .. }
        )
    });
    if got_stuck {
        leaves.retain(|leaf| leaf.halt_reason != HaltReason::DepthBound);
    }
    leaves
}

#[derive(Default)]
struct SelectedExecutionLeaves {
    retained: Vec<ExecutionLeaf>,
    got_stuck: bool,
}

impl SelectedExecutionLeaves {
    fn push(&mut self, leaf: ExecutionLeaf) {
        let got_stuck = matches!(
            leaf.halt_reason,
            HaltReason::Stuck | HaltReason::Trivial { .. } | HaltReason::Vacuous { .. }
        );
        if got_stuck && !self.got_stuck {
            self.retained
                .retain(|retained| retained.halt_reason != HaltReason::DepthBound);
            self.got_stuck = true;
        }
        if self.got_stuck && leaf.halt_reason == HaltReason::DepthBound {
            return;
        }
        self.retained.push(leaf);
    }

    fn replace_unselected(&mut self, leaves: impl IntoIterator<Item = ExecutionLeaf>) {
        self.retained.clear();
        self.retained.extend(leaves);
        self.got_stuck = false;
    }

    #[cfg(test)]
    fn retained(&self) -> &[ExecutionLeaf] {
        &self.retained
    }

    fn into_inner(self) -> Vec<ExecutionLeaf> {
        self.retained
    }
}

/// Kore's `MultiOr.make` over final configurations (Exec.hs:340-342), extended with branch-local
/// observable state: leaves collapse only when their structural term, constraint set, committed
/// effects, and console state agree. Bottom leaves carry no configuration, so whole-state trivial
/// and vacuous outcomes remain distinct.
fn merge_equal_final_leaves(leaves: Vec<ExecutionLeaf>) -> Vec<ExecutionLeaf> {
    let mut seen = Vec::new();
    leaves
        .into_iter()
        .filter(|leaf| {
            if matches!(
                leaf.halt_reason,
                HaltReason::Trivial { .. } | HaltReason::Vacuous { .. }
            ) {
                return true;
            }
            let key = (
                leaf.pattern.term.clone(),
                leaf.pattern
                    .constraints
                    .iter()
                    .cloned()
                    .collect::<BTreeSet<_>>(),
                leaf.effects.clone(),
                leaf.io.clone(),
            );
            if seen.contains(&key) {
                false
            } else {
                seen.push(key);
                true
            }
        })
        .collect()
}

fn expand_stopped_branch_remainder(
    definition: &BackendDefinition,
    branches: &mut Vec<AppliedRule>,
    remainder: &mut Option<RemainderBranch>,
    fresh_counter: &mut u64,
    simplification_options: SimplificationOptions,
    solver: &dyn SmtSolver,
    execution: (ExecutionMode, bool),
) -> Result<(), SimplificationError> {
    let (mode, assume_initial_defined) = execution;
    // Each iteration applies one more rule to the remainder (a strictly smaller applicability
    // space) or ends it as stuck, indeterminate, trivial, or vacuous.
    // Invariant: `remainder` is the part of the parent pattern that `branches` does not yet cover.
    while let Some(current) = remainder.take() {
        match rewrite_step_with_mode(
            definition,
            &current.pattern,
            fresh_counter,
            simplification_options,
            solver,
            mode,
            assume_initial_defined,
        ) {
            RewriteResult::Finished(applied) => branches.insert(0, applied),
            RewriteResult::Branch {
                branches: mut lower_branches,
                remainder: lower_remainder,
                ..
            } => {
                lower_branches.append(branches);
                *branches = lower_branches;
                *remainder = lower_remainder;
            }
            RewriteResult::Indeterminate {
                reason: IndeterminateReason::Simplification { error, .. },
                ..
            } => return Err(error),
            RewriteResult::Stuck(_) | RewriteResult::Indeterminate { .. } => {
                *remainder = Some(current);
                break;
            }
            RewriteResult::Trivial(_, _) | RewriteResult::Vacuous(_) => break,
        }
    }
    Ok(())
}

fn selected_stop_rule(applied: &AppliedRule, selected: &BTreeSet<String>) -> Option<String> {
    applied
        .label
        .as_ref()
        .filter(|label| selected.contains(*label))
        .cloned()
        .or_else(|| {
            selected
                .contains(&applied.unique_id)
                .then(|| applied.unique_id.clone())
        })
}

fn record_trivial_candidates(
    discarded: &mut Vec<UncommittedObservation>,
    applications: &[TrivialApplication],
    target: &Pattern,
    observation: Option<&ObservationOptions>,
) {
    let Some(options) = observation else {
        return;
    };
    for application in applications {
        if !options.observes(&application.rule_id) {
            continue;
        }
        discarded.push(UncommittedObservation {
            id: TransitionId {
                rule: application.rule_id.clone(),
                target: PatternDigest::of(target),
            },
            rule_label: application.label.clone(),
            effects: application.effects.clone(),
            reason: UncommittedReason::RolledBack,
        });
    }
}

fn enqueue_execution_states(pending: &mut VecDeque<ExecutionState>, next: Vec<ExecutionState>) {
    for state in next.into_iter().rev() {
        pending.push_front(state);
    }
}

fn execution_breadth_exceeded(
    pending: &mut VecDeque<ExecutionState>,
    leaves: &mut SelectedExecutionLeaves,
    max_breadth: Option<usize>,
    observation_log: &ObservationLog,
) -> bool {
    if !max_breadth.is_some_and(|bound| pending.len() > bound) {
        return false;
    }
    leaves.replace_unselected(
        pending
            .drain(..)
            .map(|state| execution_state_at_breadth_bound(state, observation_log)),
    );
    true
}

fn execution_state_at_breadth_bound(
    state: ExecutionState,
    observation_log: &ObservationLog,
) -> ExecutionLeaf {
    state.leaf(HaltReason::BreadthBound, observation_log)
}

/// Simplify a pattern that leaves the rewriter, the search, or the prover into the one normal
/// form of `simplify_pattern_details_with_solver`, recording the equations it applied as
/// simplification trace entries at `depth`.
///
/// Every externalised pattern passes through this function, so a caller sees one normal form
/// whichever path produced the pattern. The loop head merges the definedness obligations the
/// term simplifier carries into the state's constraints and keeps them there: a state's
/// constraints are also the path knowledge that discharges a later match obligation
/// syntactically. Running the pattern-level passes here, on the way out only, is sound and
/// loses nothing: `C[t] /\ \ceil(t) = C[t]` when `C` is a total context (application is
/// strict), and a conjunct the other conjuncts and the definition's lemmas make valid is
/// redundant in a conjunction. On a state the loop head has already simplified the result is
/// the same pattern or a smaller constraint set, never a different term.
pub(crate) fn simplify_leaf_pattern(
    definition: &BackendDefinition,
    pattern: &Pattern,
    max_iterations: usize,
    solver: &dyn SmtSolver,
    depth: u64,
    trace: &mut Vec<TraceEntry>,
) -> Result<PatternSimplification, SimplificationError> {
    let simplified = simplify_pattern_details_with_solver(
        definition,
        pattern,
        SimplificationOptions::keep_partial(max_iterations),
        solver,
    )?;
    trace.extend(
        simplified
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
    Ok(simplified)
}

/// `simplify_leaf_pattern` plus the observation and effect bookkeeping of an execution.
pub(crate) struct ResultPatternSimplification {
    pub(crate) pattern: Pattern,
    pub(crate) effects: Vec<BuiltinEffect>,
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn simplify_result_pattern(
    definition: &BackendDefinition,
    pattern: &Pattern,
    max_iterations: usize,
    solver: &dyn SmtSolver,
    depth: u64,
    trace: &mut Vec<TraceEntry>,
    observation: Option<&mut ObservationHead>,
    observation_log: &mut ObservationLog,
    observation_options: Option<&ObservationOptions>,
) -> Result<ResultPatternSimplification, SimplificationError> {
    let before = pattern.clone();
    let PatternSimplification {
        pattern,
        applied_rules,
        effects: simplified_effects,
    } = simplify_leaf_pattern(definition, pattern, max_iterations, solver, depth, trace)?;
    if let Some(observation) = observation {
        *observation = observation_log.append_simplification(
            *observation,
            definition,
            before,
            &pattern,
            &applied_rules,
            &simplified_effects,
            observation_options,
        );
    }
    Ok(ResultPatternSimplification {
        pattern,
        effects: simplified_effects,
    })
}

/// Externalise a `Stuck`, `DepthBound`, or `Indeterminate` leaf in the simplifier's normal
/// form (`simplify_leaf_pattern`).
///
/// A constraint set that simplifies to `\bottom` makes the leaf `Trivial`, as it does for a
/// cut-point payload. When the simplification fails, an `Indeterminate` leaf keeps its pattern
/// and its reason, which already names why the state could not progress; any other leaf
/// reports the failure, as the cut-point and terminal payloads do.
#[allow(clippy::too_many_arguments)]
fn externalise_leaf(
    definition: &BackendDefinition,
    mut state: ExecutionState,
    pattern: Pattern,
    halt_reason: HaltReason,
    max_iterations: usize,
    solver: &dyn SmtSolver,
    observation_log: &mut ObservationLog,
    observation_options: Option<&ObservationOptions>,
) -> ExecutionLeaf {
    match simplify_result_pattern(
        definition,
        &pattern,
        max_iterations,
        solver,
        state.depth,
        &mut state.trace,
        Some(&mut state.observation),
        observation_log,
        observation_options,
    ) {
        Ok(simplified) if predicates_truth(&simplified.pattern.constraints) == Truth::False => {
            state.effects.commit(simplified.effects);
            let halt_reason = trivial_halt(state.depth, &simplified.pattern);
            state.leaf_with_pattern(simplified.pattern, halt_reason, observation_log)
        }
        Ok(simplified) => {
            state.effects.commit(simplified.effects);
            state.leaf_with_pattern(simplified.pattern, halt_reason, observation_log)
        }
        Err(_) if matches!(halt_reason, HaltReason::Indeterminate(_)) => {
            state.leaf_with_pattern(pattern, halt_reason, observation_log)
        }
        Err(error) => {
            state.leaf_with_pattern(pattern, HaltReason::Simplification(error), observation_log)
        }
    }
}

fn next_state(
    mut state: ExecutionState,
    applied: AppliedRule,
    observation_log: &mut ObservationLog,
    observation_options: Option<&ObservationOptions>,
) -> ExecutionState {
    state.observation =
        observation_log.append_applied(state.observation, &applied, observation_options);
    state.effects.commit(applied.effects.iter().cloned());
    if let Some(io) = applied.io {
        state.io = io;
    }
    state.trace.push(TraceEntry {
        depth: state.depth + 1,
        kind: TraceKind::Rewrite,
        label: applied.label,
        unique_id: applied.unique_id,
    });
    state.pattern = applied.pattern;
    state.depth += 1;
    state.is_initial_input = false;
    state
}

fn remaining_state(
    mut state: ExecutionState,
    before: Pattern,
    remainder: RemainderBranch,
    observation_log: &mut ObservationLog,
    observation_options: Option<&ObservationOptions>,
) -> ExecutionState {
    state.observation = observation_log.append_remainder(
        state.observation,
        before,
        &remainder,
        observation_options,
    );
    state.trace.push(TraceEntry {
        depth: state.depth,
        kind: TraceKind::Remainder,
        label: None,
        unique_id: remainder.rule_ids.join(","),
    });
    state.effects.commit(remainder.effects);
    state.pattern = remainder.pattern;
    state.is_initial_input = false;
    state
}

#[derive(Clone)]
struct ExecutionState {
    pattern: Pattern,
    depth: u64,
    trace: Vec<TraceEntry>,
    observation: ObservationHead,
    effects: EffectJournal,
    io: ExecutionIoState,
    /// Whether the console capability remains available on this concrete execution prefix.
    io_enabled: bool,
    is_initial_input: bool,
}

impl ExecutionState {
    fn leaf(self, halt_reason: HaltReason, observation_log: &ObservationLog) -> ExecutionLeaf {
        let (branch, observations) = observation_log.materialize(self.observation);
        ExecutionLeaf {
            pattern: self.pattern,
            depth: self.depth,
            trace: self.trace,
            branch,
            observations,
            effects: self.effects.into_committed(),
            io: self.io,
            halt_reason,
        }
    }

    fn leaf_with_pattern(
        self,
        pattern: Pattern,
        halt_reason: HaltReason,
        observation_log: &ObservationLog,
    ) -> ExecutionLeaf {
        ExecutionState { pattern, ..self }.leaf(halt_reason, observation_log)
    }
}

#[cfg(test)]
mod tests {
    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    use super::*;

    fn definition(axioms: &str) -> BackendDefinition {
        let source = format!(
            r#"[]
            module MAIN
                sort SortS{{}} [hasDomainValues{{}}()]
                symbol wrap{{}}(SortS{{}}) : SortS{{}}
                    [function{{}}(), total{{}}(), injective{{}}(), no-evaluators{{}}()]
                symbol injectiveFunction{{}}(SortS{{}}) : SortS{{}}
                    [function{{}}(), total{{}}(), injective{{}}()]
                {axioms}
            endmodule []"#
        );
        let syntax = parse_definition(&source).expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    fn subject(definition: &BackendDefinition, value: &str) -> Pattern {
        let syntax = parse_pattern(&format!(r#"wrap{{}}(\dv{{SortS{{}}}}("{value}"))"#))
            .expect("subject should parse");
        Pattern {
            term: definition
                .internalize_term(&syntax, &[])
                .expect("subject should internalize"),
            constraints: Vec::new(),
        }
    }

    #[test]
    fn got_stuck_selection_releases_and_suppresses_depth_bound_leaves_online() {
        let definition = definition("");
        let leaf = |name, halt_reason| ExecutionLeaf {
            pattern: subject(&definition, name),
            depth: 1,
            trace: Vec::new(),
            branch: Vec::new(),
            observations: Vec::new(),
            effects: Vec::new(),
            io: ExecutionIoState::default(),
            halt_reason,
        };
        let mut selected = SelectedExecutionLeaves::default();

        selected.push(leaf("depth-before", HaltReason::DepthBound));
        assert_eq!(selected.retained().len(), 1);

        selected.push(leaf("stuck", HaltReason::Stuck));
        assert_eq!(selected.retained().len(), 1);
        assert_eq!(selected.retained()[0].halt_reason, HaltReason::Stuck);

        selected.push(leaf("depth-after", HaltReason::DepthBound));
        selected.push(leaf("cancelled", HaltReason::Cancelled));
        assert_eq!(selected.retained().len(), 2);
        assert_eq!(selected.retained()[0].halt_reason, HaltReason::Stuck);
        assert_eq!(selected.retained()[1].halt_reason, HaltReason::Cancelled);
    }

    #[test]
    fn final_leaves_with_distinct_console_states_do_not_merge() {
        let definition = definition("");
        let cursor_zero = ExecutionIoState::new(Vec::from(&b"input"[..]));
        let mut cursor_evaluation = cursor_zero.begin_evaluation();
        assert_eq!(cursor_evaluation.read(1), b"i");
        let cursor_one = cursor_evaluation.commit();
        let mut left_evaluation = ExecutionIoState::default().begin_evaluation();
        left_evaluation.append("IO.write", 1, Vec::from(&b"left"[..]));
        let left_io = left_evaluation.commit();
        let mut right_evaluation = ExecutionIoState::default().begin_evaluation();
        right_evaluation.append("IO.write", 1, Vec::from(&b"right"[..]));
        let right_io = right_evaluation.commit();
        let leaf = |io| ExecutionLeaf {
            pattern: subject(&definition, "same"),
            depth: 1,
            trace: Vec::new(),
            branch: Vec::new(),
            observations: Vec::new(),
            effects: Vec::new(),
            io,
            halt_reason: HaltReason::Stuck,
        };

        let cursor_leaves = merge_equal_final_leaves(vec![leaf(cursor_zero), leaf(cursor_one)]);
        assert_eq!(cursor_leaves.len(), 2);

        let transcript_leaves = merge_equal_final_leaves(vec![leaf(left_io), leaf(right_io)]);

        assert_eq!(transcript_leaves.len(), 2);
        assert_eq!(
            transcript_leaves[0].io.transcript()[0].bytes.as_ref(),
            b"left"
        );
        assert_eq!(
            transcript_leaves[1].io.transcript()[0].bytes.as_ref(),
            b"right"
        );
    }
}
