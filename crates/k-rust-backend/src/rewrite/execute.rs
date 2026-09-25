//! ```toml algorithm
//! id = "backend.rewrite.execute"
//! name = "depth-first exploration of a rewrite tree"
//! sites = ["execute_using", "Execution::run", "Execution::expand", "merge_equal_final_leaves", "enqueue_execution_states"]
//! variable = "d = maximum depth; b = maximum breadth; L = final leaves"
//! counters = ["RewriteSteps"]
//! span = "per problem"
//! invariant = "pending holds unexpanded states of depth <= max_depth; leaves only grows"
//! consumes = [
//!   { type = "k_rust_backend::definition::BackendDefinition", role = "internalized theory" },
//!   { type = "k_rust_backend::rewrite::Pattern", role = "internalized pattern" },
//!   { type = "k_rust_backend::rewrite::RewriteResult", role = "rewrite result" },
//! ]
//! produces = [{ type = "k_rust_backend::rewrite::ExecutionResult", role = "execution result" }]
//!
//! [[cost]]
//! mode = "bounded execution"
//! bound = "O(states), with states at most b^d when both bounds are set and unbounded under the defaults (max_depth = u64::MAX, max_breadth = None); each state performs one term simplification, predicate pass, and rewrite step, and a state stopped at max_depth is simplified once more"
//!
//! [[cost]]
//! mode = "final leaf merge (merge_equal_final_leaves)"
//! bound = "O(L^2) structural key comparisons"
//! ```
//!
//! Depth-first exploration of the rewrite tree (stack discipline) with a per-state pipeline and
//! an equal-leaf merge; a depth-bounded leaf is a result whatever the other leaves' halt reasons,
//! so the result covers every path up to the bound: O(states) steps, states <= branching^depth bounded by
//! `max_depth` and `max_breadth`, each state one term simplification, one predicate pass, and one
//! rewrite step; `Counter::RewriteSteps`. Not breadth-first: `enqueue_execution_states`
//! pushes successors to the front, so children are visited before siblings.

// The phase methods return `Phase<T>` (below), whose `Err` is the finished `ExecutionLeaf`
// itself: one leaf per state, moved once into `leaves`.
#![allow(clippy::result_large_err)]

use std::collections::{BTreeSet, VecDeque};

use k_rust_kore::measure::{self, Algorithm, Counter};

use crate::{
    builtin::BuiltinEffect,
    cancellation::cancellation_requested,
    definition::BackendDefinition,
    diagnostic::{self, BackendDiagnostic, PathDiagnostics, extend_distinct},
    rule::Predicate,
    simplify::{
        PatternSimplification, SimplificationError, SimplificationOptions,
        simplify_in_execution_with_solver, simplify_pattern_details_with_solver,
        simplify_predicates_with_solver, simplify_with_solver,
    },
    smt::SmtSolver,
    timeout::{StepTimeoutController, StepTimeoutOptions, StepTimer},
    transition::{
        EffectJournal, ExecutionIoState, ObservationHead, ObservationLog, ObservationOptions,
        PatternDigest, TransitionId, UncommittedObservation, UncommittedReason,
    },
};

use super::{
    AppliedRule, ExecutionBranchMode, ExecutionLeaf, ExecutionOptions, ExecutionResult, HaltReason,
    IndeterminateReason, InitialSimplificationStatus, Pattern, RemainderBranch, RewriteResult,
    TraceEntry, TraceKind, TrivialApplication, Truth, UndecidedStep, applied_trivial_halt,
    normalize_pattern_substitution, predicates_truth, retain_substitution_predicates,
    rewrite_step_with_optional_execution, trivial_halt, vacuous_halt,
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
    let _span = measure::algorithm_span(Algorithm::BackendRewriteExecute);
    let timeout_controller = StepTimeoutController::new(StepTimeoutOptions {
        manual: options.step_timeout,
        moving_average: options.moving_average_timeout,
    });
    let mut execution = Execution::seed(
        definition,
        initial,
        options,
        solver,
        initial_io,
        observation,
        &mut observe,
    );
    if execution.options.max_breadth == Some(0) {
        return execution.collect_at_breadth_zero();
    }
    execution.run(&timeout_controller);
    execution.collect()
}

/// A phase either hands the state on or ends it as a leaf.
type Phase<T> = Result<T, ExecutionLeaf>;

/// What enqueueing the successors of one state did to the worklist.
enum Expansion {
    /// Successors (or none) were enqueued; the loop goes on.
    Queued,
    /// The breadth bound drained `pending` into leaves; the loop ends.
    BreadthBound,
}

/// One `execute_using` call: the seed (E0) threaded through the per-state pipeline (E1 to E7)
/// and collected at the end (E8). Every exit of the pipeline is a leaf pushed by `run`.
struct Execution<'a> {
    definition: &'a BackendDefinition,
    options: ExecutionOptions,
    solver: &'a dyn SmtSolver,
    observation: Option<&'a ObservationOptions>,
    observe: &'a mut dyn FnMut(&BuiltinEffect),
    fresh_counter: u64,
    observation_log: ObservationLog,
    initial_input_count: usize,
    pending: VecDeque<ExecutionState>,
    leaves: Vec<ExecutionLeaf>,
    discarded: Vec<UncommittedObservation>,
    completed_initial_simplifications: usize,
    bottom_initial_simplifications: usize,
}

impl<'a> Execution<'a> {
    /// E0: `pending` holds the initial patterns at depth 0 in input order, each marked as an
    /// initial input.
    fn seed(
        definition: &'a BackendDefinition,
        initial: Vec<Pattern>,
        options: ExecutionOptions,
        solver: &'a dyn SmtSolver,
        initial_io: Option<ExecutionIoState>,
        observation: Option<&'a ObservationOptions>,
        observe: &'a mut dyn FnMut(&BuiltinEffect),
    ) -> Self {
        let initial_input_count = initial.len();
        let has_execution_io = initial_io.is_some();
        let initial_io = initial_io.unwrap_or_default();
        let diagnostics = PathDiagnostics::new_request();
        let mut pending = initial
            .into_iter()
            .map(|pattern| {
                let io_enabled = has_execution_io && pattern_supports_execution_io(&pattern);
                ExecutionState {
                    pattern,
                    depth: 0,
                    trace: Vec::new(),
                    kind: ExecutionStateKind::Rewritable,
                    observation: None,
                    effects: EffectJournal::default(),
                    io: initial_io.clone(),
                    io_enabled,
                    is_initial_input: true,
                    diagnostics: diagnostics.empty_like(),
                }
            })
            .collect::<VecDeque<_>>();
        let mut leaves = Vec::new();
        let mut validated = VecDeque::with_capacity(pending.len());
        // Invariant: `validated` holds, in queue order, the popped states without a surviving macro or alias symbol, and `leaves` one leaf per other popped state; nothing is pushed onto `pending`, so each initial state is popped once.
        while let Some(state) = pending.pop_front() {
            if let Some(symbol) = state.pattern.macro_or_alias_symbol() {
                leaves.push(state.leaf(
                    HaltReason::Indeterminate(IndeterminateReason::SurvivingMacroOrAlias {
                        symbol,
                    }),
                    &ObservationLog::default(),
                ));
            } else {
                validated.push_back(state);
            }
        }
        Self {
            definition,
            options,
            solver,
            observation,
            observe,
            fresh_counter: 0,
            observation_log: ObservationLog::default(),
            initial_input_count,
            pending: validated,
            leaves,
            discarded: Vec::new(),
            completed_initial_simplifications: 0,
            bottom_initial_simplifications: 0,
        }
    }

    /// `max_breadth = Some(0)`: every initial pattern is a `BreadthBound` leaf.
    fn collect_at_breadth_zero(mut self) -> (ExecutionResult, InitialSimplificationStatus) {
        let mut leaves = self.leaves;
        leaves.extend(
            self.pending
                .drain(..)
                .map(|state| execution_state_at_breadth_bound(state, &self.observation_log)),
        );
        let leaves = merge_equal_final_leaves(leaves);
        (
            ExecutionResult {
                leaves,
                effects: Vec::new(),
                discarded: self.discarded,
            },
            InitialSimplificationStatus {
                simplified_to_bottom: false,
            },
        )
    }

    /// E1: pop each unexpanded state, count the step, time it, expand it, and enqueue its
    /// successors or record its leaf.
    ///
    /// Diagnostics. Every backend diagnostic is emitted by a unit of work of one expansion; each
    /// unit is collected separately and attached to exactly the paths derived from its result
    /// (`ExecutionLeaf::diagnostics`), in emission order:
    /// - the state's own constraint and term simplification (E2, E3): the state's path, so every
    ///   successor and its leaf;
    /// - in the rewrite step (`step.rs`, `apply.rs`), per candidate (`AppliedRule::diagnostics`,
    ///   `RemainderBranch::diagnostics`): a right-hand-side alternative's construction to its
    ///   candidate; one application group's matching, recovery and condition work (a match split
    ///   yields one group per sub-case) to the group's candidates and to the remainder, whose
    ///   constraint negates the group's applicability; the remainder's own simplification and the
    ///   lower-priority work on it to the remainder and the candidates derived from it;
    /// - a step that halts the state: its leaf; the simplification of a leaf or candidate pattern:
    ///   that leaf or candidate.
    ///
    /// Work no reported successor is derived from is on no path: a rule attempt that does not
    /// apply, an alternative refuted to bottom, a group the sequential step does not follow. A
    /// leaf cut off by a cancellation or timeout after the step carries all the work of the step
    /// and of its candidates done before it. Every collection forwards to any collector the
    /// caller holds around the execution, which therefore sees every diagnostic.
    fn run(&mut self, timeout_controller: &StepTimeoutController) {
        // `pending` is a stack: `enqueue_execution_states` pushes successors to the front, so a
        // state's children are expanded before its siblings (depth-first). Each push either
        // raises the depth, which `max_depth` bounds, or consumes a remainder, so the loop
        // terminates.
        // Invariant: `pending` holds unexpanded states of depth <= `max_depth`; `leaves` only grows.
        while let Some(state) = self.pending.pop_front() {
            measure::bump(Counter::RewriteSteps);
            let mut step_timer = timeout_controller.begin_step();
            match self.expand(state, &mut step_timer) {
                Ok(successors) => {
                    enqueue_execution_states(&mut self.pending, successors);
                    if let Expansion::BreadthBound = self.breadth_checked() {
                        break;
                    }
                }
                Err(leaf) => self.leaves.push(leaf),
            }
        }
    }

    /// The per-state pipeline E2 to E7; the interruption checks sit where the loop body had
    /// them (before constraint simplification, after it, after term simplification, after the
    /// rewrite step, and inside E6 and E7). Returns the successors `run` enqueues.
    fn expand(
        &mut self,
        state: ExecutionState,
        step_timer: &mut StepTimer<'_>,
    ) -> Phase<Vec<ExecutionState>> {
        let state = self.check_interrupted(state, step_timer)?;
        if let Some(symbol) = state.pattern.macro_or_alias_symbol() {
            return Err(state.leaf(
                HaltReason::Indeterminate(IndeterminateReason::SurvivingMacroOrAlias { symbol }),
                &self.observation_log,
            ));
        }
        let (state, deferred_initial_vacuity) = self.normalise_constraints(state, step_timer)?;
        let state = self.simplify_term(state, step_timer, deferred_initial_vacuity.is_some())?;
        // A `Finished` or `Branch` step attributes its diagnostics to its candidates; any other
        // result halts the state, whose leaf takes the step's whole collection.
        let (rewritten, step_diagnostics) = diagnostic::collect(|| match &state.kind {
            ExecutionStateKind::Rewritable => self.step(&state),
            ExecutionStateKind::Remaining(None) => RewriteResult::Stuck(state.pattern.clone()),
            ExecutionStateKind::Remaining(Some(undecided)) => {
                undecided.clone().into_result(state.pattern.clone())
            }
        });
        let mut state = match self.check_interrupted(state, step_timer) {
            Ok(state) => state,
            Err(leaf) => return Err(interrupted_with(leaf, &[&step_diagnostics])),
        };
        match rewritten {
            RewriteResult::Stuck(_)
            | RewriteResult::Trivial(_, _)
            | RewriteResult::Vacuous(_)
            | RewriteResult::Indeterminate { .. }
            | RewriteResult::Simplification { .. } => {
                state.diagnostics.extend(&step_diagnostics);
                Err(self.halt_leaf(state, rewritten, deferred_initial_vacuity))
            }
            RewriteResult::Finished(applied) => {
                let (expanded, diagnostics) =
                    diagnostic::collect(|| self.finished(state, applied, step_timer));
                expanded.map_err(|leaf| interrupted_with(leaf, &[&step_diagnostics, &diagnostics]))
            }
            RewriteResult::Branch {
                original,
                branches,
                remainder,
                trivial,
            } => {
                let (expanded, diagnostics) = diagnostic::collect(|| {
                    self.branch(state, original, branches, remainder, trivial, step_timer)
                });
                expanded.map_err(|leaf| interrupted_with(leaf, &[&step_diagnostics, &diagnostics]))
            }
        }
    }

    /// A cancellation or a step timeout turns the state into a leaf and discards the step's
    /// duration measurement.
    fn check_interrupted(
        &mut self,
        state: ExecutionState,
        step_timer: &mut StepTimer<'_>,
    ) -> Phase<ExecutionState> {
        if cancellation_requested() {
            step_timer.discard_measurement();
            return Err(state.leaf(HaltReason::Cancelled, &self.observation_log));
        }
        if let Some(mode) = step_timer.timed_out() {
            step_timer.discard_measurement();
            return Err(state.leaf(HaltReason::Timeout(mode), &self.observation_log));
        }
        Ok(state)
    }

    /// E2: the substitution is normalised, the constraints simplified with `keep_partial`, and
    /// the retained substitution predicates re-added. A `False` at depth 0 with a non-empty
    /// retained substitution is deferred (Booster applies the input substitution before the
    /// first step); any other `False` is a `Vacuous` leaf. Returns the deferred pattern.
    fn normalise_constraints(
        &mut self,
        mut state: ExecutionState,
        step_timer: &mut StepTimer<'_>,
    ) -> Phase<(ExecutionState, Option<Pattern>)> {
        let retained_substitution =
            normalize_pattern_substitution(&mut state.pattern, &self.definition.sort_graph);
        let pattern_before_constraint_simplification = state.pattern.clone();
        let mut deferred_initial_vacuity = None;
        let (simplified_constraints, diagnostics) = diagnostic::collect(|| {
            simplify_predicates_with_solver(
                self.definition,
                &state.pattern.constraints,
                &[],
                SimplificationOptions::keep_partial(self.options.max_simplification_iterations),
                self.solver,
            )
        });
        state.diagnostics.extend(&diagnostics);
        let mut state = self.check_interrupted(state, step_timer)?;
        match simplified_constraints {
            Ok(mut constraints) => {
                retain_substitution_predicates(
                    &mut constraints,
                    &retained_substitution,
                    &self.definition.sort_graph,
                );
                state.pattern.constraints = constraints;
                normalize_pattern_substitution(&mut state.pattern, &self.definition.sort_graph);
            }
            Err(error) => {
                return Err(state.leaf(HaltReason::Simplification(error), &self.observation_log));
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
                    self.completed_initial_simplifications += 1;
                    self.bottom_initial_simplifications += 1;
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
                return Err(state.leaf(halt_reason, &self.observation_log));
            }
        }
        Ok((state, deferred_initial_vacuity))
    }

    /// E3: the term is simplified under its constraints, the simplification is observed and
    /// traced, initial-input bookkeeping is done (a `False` after term simplification is
    /// `Vacuous`), and the depth bound is checked (`DepthBound` leaf).
    fn simplify_term(
        &mut self,
        mut state: ExecutionState,
        step_timer: &mut StepTimer<'_>,
        vacuity_deferred: bool,
    ) -> Phase<ExecutionState> {
        let pattern_before_term_simplification = state.pattern.clone();
        state.io_enabled &= pattern_supports_execution_io(&state.pattern);
        let mut io_evaluation = state.io_enabled.then(|| state.io.begin_evaluation());
        let (simplified, diagnostics) = diagnostic::collect(|| match io_evaluation.as_mut() {
            Some(execution) => simplify_in_execution_with_solver(
                self.definition,
                &state.pattern.term,
                &state.pattern.constraints,
                SimplificationOptions::keep_partial(self.options.max_simplification_iterations),
                self.solver,
                execution,
            ),
            None => simplify_with_solver(
                self.definition,
                &state.pattern.term,
                &state.pattern.constraints,
                SimplificationOptions::keep_partial(self.options.max_simplification_iterations),
                self.solver,
            ),
        });
        state.diagnostics.extend(&diagnostics);
        let mut state = self.check_interrupted(state, step_timer)?;
        let undefined_term = match simplified {
            Ok(simplified) => {
                let undefined_term = simplified.undefined_term.clone();
                state.pattern.term = simplified.term;
                state.pattern.constraints.extend(simplified.constraints);
                normalize_pattern_substitution(&mut state.pattern, &self.definition.sort_graph);
                state.observation = self.observation_log.append_simplification(
                    state.observation,
                    self.definition,
                    pattern_before_term_simplification,
                    &state.pattern,
                    &simplified.applied_rules,
                    &simplified.effects,
                    self.observation,
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
                return Err(state.leaf(HaltReason::Simplification(error), &self.observation_log));
            }
        };
        if state.is_initial_input {
            self.completed_initial_simplifications += 1;
            if !vacuity_deferred && predicates_truth(&state.pattern.constraints) == Truth::False {
                self.bottom_initial_simplifications += 1;
                let halt_reason = vacuous_halt(state.depth, &state.pattern, &state.trace);
                return Err(state.leaf(halt_reason, &self.observation_log));
            }
        }
        if predicates_truth(&state.pattern.constraints) == Truth::False
            && let Some(term) = undefined_term
        {
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
            return Err(state.leaf(halt_reason, &self.observation_log));
        }
        if let Some(execution) = io_evaluation {
            state.io = execution.commit();
        }
        state.io_enabled &= pattern_supports_execution_io(&state.pattern);
        if state.depth >= self.options.max_depth {
            let pattern = state.pattern.clone();
            return Err(externalise_leaf(
                self.definition,
                state,
                pattern,
                HaltReason::DepthBound,
                self.options.max_simplification_iterations,
                self.solver,
                &mut self.observation_log,
                self.observation,
            ));
        }
        Ok(state)
    }

    /// E4: one priority-grouped rewrite step (backend.rewrite.step) under the option's mode.
    fn step(&mut self, state: &ExecutionState) -> RewriteResult {
        rewrite_step_with_optional_execution(
            self.definition,
            &state.pattern,
            &mut self.fresh_counter,
            SimplificationOptions::keep_partial(self.options.max_simplification_iterations),
            self.solver,
            self.options.mode,
            self.options.assume_initial_defined,
            state.io_enabled.then_some(&state.io),
        )
    }

    /// E5: `Stuck` (or `Vacuous` when the initial vacuity was deferred), `Trivial`, `Vacuous`,
    /// and `Indeterminate` results become leaves with the matching `HaltReason`.
    fn halt_leaf(
        &mut self,
        state: ExecutionState,
        rewritten: RewriteResult,
        deferred_initial_vacuity: Option<Pattern>,
    ) -> ExecutionLeaf {
        match rewritten {
            RewriteResult::Stuck(pattern) => match deferred_initial_vacuity {
                Some(pattern) => {
                    let halt_reason = vacuous_halt(state.depth, &pattern, &state.trace);
                    state.leaf_with_pattern(pattern, halt_reason, &self.observation_log)
                }
                None => externalise_leaf(
                    self.definition,
                    state,
                    pattern,
                    HaltReason::Stuck,
                    self.options.max_simplification_iterations,
                    self.solver,
                    &mut self.observation_log,
                    self.observation,
                ),
            },
            RewriteResult::Trivial(pattern, applications) => {
                record_trivial_candidates(
                    &mut self.discarded,
                    &applications,
                    &pattern,
                    self.observation,
                );
                let halt_reason = applications
                    .first()
                    .map(|application| applied_trivial_halt(state.depth + 1, application))
                    .unwrap_or_else(|| trivial_halt(state.depth + 1, &pattern));
                state.leaf_with_pattern(pattern, halt_reason, &self.observation_log)
            }
            RewriteResult::Vacuous(pattern) => {
                let halt_reason = vacuous_halt(state.depth, &pattern, &state.trace);
                state.leaf_with_pattern(pattern, halt_reason, &self.observation_log)
            }
            RewriteResult::Simplification { pattern, error } => state.leaf_with_pattern(
                pattern,
                HaltReason::Simplification(error),
                &self.observation_log,
            ),
            RewriteResult::Indeterminate { pattern, reason } => externalise_leaf(
                self.definition,
                state,
                pattern,
                HaltReason::Indeterminate(reason),
                self.options.max_simplification_iterations,
                self.solver,
                &mut self.observation_log,
                self.observation,
            ),
            RewriteResult::Finished(_) | RewriteResult::Branch { .. } => {
                unreachable!("finished and branching results are expanded, not halted")
            }
        }
    }

    /// E6: one rule applied. A cut-point rule ends the state as a `CutPointRule` leaf with the
    /// simplified successor; a terminal rule ends the successor as a `TerminalRule` (or
    /// `Trivial`) leaf; otherwise the successor is returned.
    fn finished(
        &mut self,
        mut state: ExecutionState,
        applied: AppliedRule,
        step_timer: &mut StepTimer<'_>,
    ) -> Phase<Vec<ExecutionState>> {
        if let Some(rule) = selected_stop_rule(&applied, &self.options.cut_point_rules) {
            let mut applied = applied;
            for simplification in &applied.remainder_simplifications {
                state.observation = self.observation_log.append_simplification(
                    state.observation,
                    self.definition,
                    simplification.before.clone(),
                    &simplification.after,
                    &simplification.applied_rules,
                    &simplification.effects,
                    self.observation,
                );
                state.effects.commit(simplification.effects.iter().cloned());
                state.trace.extend(
                    simplification
                        .applied_rules
                        .iter()
                        .cloned()
                        .map(|unique_id| TraceEntry {
                            depth: state.depth,
                            kind: TraceKind::Simplification,
                            label: None,
                            unique_id,
                        }),
                );
            }
            state.effects.commit(applied.effects.iter().cloned());
            state.observation =
                self.observation_log
                    .append_applied(state.observation, &applied, self.observation);
            let (simplified, diagnostics) = diagnostic::collect(|| {
                simplify_result_pattern(
                    self.definition,
                    &applied.pattern,
                    self.options.max_simplification_iterations,
                    self.solver,
                    state.depth,
                    &mut state.trace,
                    Some(&mut state.observation),
                    &mut self.observation_log,
                    self.observation,
                )
            });
            extend_distinct(&mut applied.diagnostics, &diagnostics);
            applied.pattern = match simplified {
                Ok(simplified) => {
                    state.effects.commit(simplified.effects);
                    simplified.pattern
                }
                Err(error) => {
                    let mut state = self.check_interrupted(state, step_timer)?;
                    // The leaf reports the successor's pattern, so the successor's diagnostics.
                    state.diagnostics.extend(&applied.diagnostics);
                    return Err(state.leaf_with_pattern(
                        applied.pattern,
                        HaltReason::Simplification(error),
                        &self.observation_log,
                    ));
                }
            };
            let mut state = self.check_interrupted(state, step_timer)?;
            if predicates_truth(&applied.pattern.constraints) == Truth::False {
                state.diagnostics.extend(&applied.diagnostics);
                let halt_reason = trivial_halt(state.depth + 1, &applied.pattern);
                return Err(state.leaf_with_pattern(
                    applied.pattern,
                    halt_reason,
                    &self.observation_log,
                ));
            }
            return Err(state.leaf(
                HaltReason::CutPointRule {
                    rule,
                    next_states: vec![applied],
                },
                &self.observation_log,
            ));
        }
        let terminal_rule = selected_stop_rule(&applied, &self.options.terminal_rules);
        let mut next = next_state(
            self.definition,
            state,
            applied,
            &mut self.observation_log,
            self.observation,
        );
        if let Some(rule) = terminal_rule {
            let (simplified, diagnostics) = diagnostic::collect(|| {
                simplify_result_pattern(
                    self.definition,
                    &next.pattern,
                    self.options.max_simplification_iterations,
                    self.solver,
                    next.depth,
                    &mut next.trace,
                    Some(&mut next.observation),
                    &mut self.observation_log,
                    self.observation,
                )
            });
            next.diagnostics.extend(&diagnostics);
            next.pattern = match simplified {
                Ok(simplified) => {
                    next.effects.commit(simplified.effects);
                    simplified.pattern
                }
                Err(error) => {
                    let next = self.check_interrupted(next, step_timer)?;
                    return Err(next.leaf(HaltReason::Simplification(error), &self.observation_log));
                }
            };
            let next = self.check_interrupted(next, step_timer)?;
            let trivial = predicates_truth(&next.pattern.constraints) == Truth::False;
            let halt_reason = if trivial {
                trivial_halt(next.depth, &next.pattern)
            } else {
                HaltReason::TerminalRule { rule }
            };
            return Err(next.leaf(halt_reason, &self.observation_log));
        }
        Ok(vec![next])
    }

    /// E7: several rules applied, or one with a complete remainder. Under `StopAtBranch`, the
    /// original and every child are simplified and reported together. Under `ExploreAll`, applied
    /// branches and the remainder become the returned successors.
    fn branch(
        &mut self,
        mut state: ExecutionState,
        original: Pattern,
        mut branches: Vec<AppliedRule>,
        mut remainder: Option<RemainderBranch>,
        trivial: Vec<TrivialApplication>,
        step_timer: &mut StepTimer<'_>,
    ) -> Phase<Vec<ExecutionState>> {
        record_trivial_candidates(&mut self.discarded, &trivial, &original, self.observation);
        if self.options.branch_mode == ExecutionBranchMode::StopAtBranch {
            // The branch leaf is the parent state: its diagnostics are the parent path's and its
            // pattern's simplification; each candidate it reports carries its own.
            let (simplified_original, diagnostics) = diagnostic::collect(|| {
                simplify_result_pattern(
                    self.definition,
                    &original,
                    self.options.max_simplification_iterations,
                    self.solver,
                    state.depth,
                    &mut state.trace,
                    Some(&mut state.observation),
                    &mut self.observation_log,
                    self.observation,
                )
            });
            state.diagnostics.extend(&diagnostics);
            let original = match simplified_original {
                Ok(simplified) => {
                    state.effects.commit(simplified.effects);
                    simplified.pattern
                }
                Err(error) => {
                    let state = self.check_interrupted(state, step_timer)?;
                    return Err(state.leaf_with_pattern(
                        original,
                        HaltReason::Simplification(error),
                        &self.observation_log,
                    ));
                }
            };
            if predicates_truth(&original.constraints) == Truth::False {
                let halt_reason = trivial_halt(state.depth, &original);
                return Err(state.leaf_with_pattern(original, halt_reason, &self.observation_log));
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
                let (simplified, diagnostics) = diagnostic::collect(|| {
                    simplify_result_pattern(
                        self.definition,
                        &applied.pattern,
                        self.options.max_simplification_iterations,
                        self.solver,
                        state.depth + 1,
                        &mut state.trace,
                        None,
                        &mut self.observation_log,
                        self.observation,
                    )
                });
                extend_distinct(&mut applied.diagnostics, &diagnostics);
                match simplified {
                    Ok(simplified) => {
                        applied.pattern = simplified.pattern;
                        applied.effects.extend(simplified.effects);
                        if predicates_truth(&applied.pattern.constraints) != Truth::False {
                            simplified_branches.push(applied);
                        } else if self
                            .observation
                            .is_some_and(|options| options.observes(&applied.unique_id))
                        {
                            self.discarded.push(UncommittedObservation {
                                id: attempted_id,
                                rule_label: applied.label,
                                effects: applied.effects,
                                reason: UncommittedReason::RolledBack,
                            });
                        }
                    }
                    Err(error) => {
                        // The failure is reported on the parent's leaf, with the diagnostics of
                        // the work on the candidate that failed.
                        state.diagnostics.extend(&applied.diagnostics);
                        failed_branch = Some(error);
                        break;
                    }
                }
            }
            if let Some(error) = failed_branch {
                let state = self.check_interrupted(state, step_timer)?;
                return Err(state.leaf_with_pattern(
                    original,
                    HaltReason::Simplification(error),
                    &self.observation_log,
                ));
            }
            branches = simplified_branches;
            if let Some(candidate) = &mut remainder {
                let (simplified, diagnostics) = diagnostic::collect(|| {
                    simplify_result_pattern(
                        self.definition,
                        &candidate.pattern,
                        self.options.max_simplification_iterations,
                        self.solver,
                        state.depth,
                        &mut state.trace,
                        None,
                        &mut self.observation_log,
                        self.observation,
                    )
                });
                extend_distinct(&mut candidate.diagnostics, &diagnostics);
                candidate.pattern = match simplified {
                    Ok(simplified) => {
                        candidate.effects.extend(simplified.effects);
                        simplified.pattern
                    }
                    Err(error) => {
                        state.diagnostics.extend(&candidate.diagnostics);
                        let state = self.check_interrupted(state, step_timer)?;
                        return Err(state.leaf_with_pattern(
                            original,
                            HaltReason::Simplification(error),
                            &self.observation_log,
                        ));
                    }
                };
                if predicates_truth(&candidate.pattern.constraints) == Truth::False {
                    remainder = None;
                }
            }
            let state = self.check_interrupted(state, step_timer)?;
            match (branches.len(), remainder.is_some()) {
                (0, false) => {
                    return Err(state.leaf_with_pattern(
                        original,
                        HaltReason::Stuck,
                        &self.observation_log,
                    ));
                }
                (1, false) => {
                    let applied = branches.pop().expect("one branch remains");
                    return Ok(vec![next_state(
                        self.definition,
                        state,
                        applied,
                        &mut self.observation_log,
                        self.observation,
                    )]);
                }
                (0, true) => {
                    let remainder = remainder.take().expect("one remainder remains");
                    let before = state.pattern.clone();
                    return Ok(vec![remaining_state(
                        self.definition,
                        state,
                        before,
                        remainder,
                        &mut self.observation_log,
                        self.observation,
                    )]);
                }
                _ => {
                    return Err(state.leaf_with_pattern(
                        original,
                        HaltReason::Branch {
                            branches,
                            remainder,
                        },
                        &self.observation_log,
                    ));
                }
            }
        }
        let mut next = Vec::with_capacity(branches.len() + usize::from(remainder.is_some()));
        for applied in branches {
            next.push(next_state(
                self.definition,
                state.clone(),
                applied,
                &mut self.observation_log,
                self.observation,
            ));
        }
        if let Some(remainder) = remainder {
            let before = state.pattern.clone();
            let remaining = remaining_state(
                self.definition,
                state,
                before,
                remainder,
                &mut self.observation_log,
                self.observation,
            );
            next.push(remaining);
        }
        Ok(next)
    }

    /// After a push: `BreadthBound` when `pending` exceeds `max_breadth` (the bound drains it
    /// into leaves), else `Queued`.
    fn breadth_checked(&mut self) -> Expansion {
        if execution_breadth_exceeded(
            &mut self.pending,
            &mut self.leaves,
            self.options.max_breadth,
            &self.observation_log,
        ) {
            Expansion::BreadthBound
        } else {
            Expansion::Queued
        }
    }

    /// E8: leaves pass `merge_equal_final_leaves`. A `DepthBound` leaf is kept whatever halt
    /// reason other leaves carry: a depth-bounded result covers every path up to the bound, so a
    /// configuration reached at the bound is a result independently of other branches.
    /// `simplified_to_bottom` holds iff every initial input completed E2 and E3 and ended
    /// `Vacuous`.
    fn collect(self) -> (ExecutionResult, InitialSimplificationStatus) {
        let leaves = merge_equal_final_leaves(self.leaves);
        // The legacy observer is a single-stream interface. It receives a transcript only when
        // final selection retained one leaf; callers consume multi-leaf transcripts from each leaf.
        let effects = match leaves.as_slice() {
            [leaf] => leaf.effects.clone(),
            _ => Vec::new(),
        };
        for effect in &effects {
            (self.observe)(effect);
        }
        (
            ExecutionResult {
                leaves,
                effects,
                discarded: self.discarded,
            },
            InitialSimplificationStatus {
                simplified_to_bottom: self.initial_input_count != 0
                    && self.completed_initial_simplifications == self.initial_input_count
                    && self.bottom_initial_simplifications == self.initial_input_count,
            },
        )
    }
}

/// A leaf that a cancellation or timeout cut off after the step: it carries the work its state's
/// expansion did before the interruption (`lists`, in emission order), which was on that path
/// although the candidates it was building are not reported. Any other leaf is returned as is,
/// its diagnostics already attributed.
fn interrupted_with(mut leaf: ExecutionLeaf, lists: &[&[BackendDiagnostic]]) -> ExecutionLeaf {
    if matches!(
        leaf.halt_reason,
        HaltReason::Cancelled | HaltReason::Timeout(_)
    ) {
        for diagnostics in lists {
            extend_distinct(&mut leaf.diagnostics, diagnostics);
        }
    }
    leaf
}

fn pattern_supports_execution_io(pattern: &Pattern) -> bool {
    pattern.constraints.is_empty() && pattern.term.attributes().variables.is_empty()
}

/// Kore's `MultiOr.make` over final configurations (Exec.hs:340-342), extended with branch-local
/// observable state: leaves collapse only when their structural term, constraint set, committed
/// effects, and console state agree. Bottom leaves carry no configuration, so whole-state trivial
/// and vacuous outcomes remain distinct. The retained leaf keeps its own trace, branch, and
/// diagnostics: they describe the one path the leaf reports, and the merged paths ended in the
/// same configuration, so whether that configuration is normalized is the same for each.
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
    leaves: &mut Vec<ExecutionLeaf>,
    max_breadth: Option<usize>,
    observation_log: &ObservationLog,
) -> bool {
    if !max_breadth.is_some_and(|bound| pending.len() > bound) {
        return false;
    }
    leaves.clear();
    leaves.extend(
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
/// reports the failure, as the cut-point and terminal payloads do. The halt reason is decided
/// before externalisation, which only normalises the pattern, so a step deadline that passes
/// during it leaves the leaf as it stands with its unsimplified pattern.
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
    let (simplified, diagnostics) = diagnostic::collect(|| {
        simplify_result_pattern(
            definition,
            &pattern,
            max_iterations,
            solver,
            state.depth,
            &mut state.trace,
            Some(&mut state.observation),
            observation_log,
            observation_options,
        )
    });
    state.diagnostics.extend(&diagnostics);
    match simplified {
        Ok(simplified) if predicates_truth(&simplified.pattern.constraints) == Truth::False => {
            state.effects.commit(simplified.effects);
            let halt_reason = trivial_halt(state.depth, &simplified.pattern);
            state.leaf_with_pattern(simplified.pattern, halt_reason, observation_log)
        }
        Ok(simplified) => {
            state.effects.commit(simplified.effects);
            state.leaf_with_pattern(simplified.pattern, halt_reason, observation_log)
        }
        Err(SimplificationError::Interrupted) => {
            state.leaf_with_pattern(pattern, halt_reason, observation_log)
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
    definition: &BackendDefinition,
    mut state: ExecutionState,
    applied: AppliedRule,
    observation_log: &mut ObservationLog,
    observation_options: Option<&ObservationOptions>,
) -> ExecutionState {
    state.diagnostics.extend(&applied.diagnostics);
    for simplification in &applied.remainder_simplifications {
        state.observation = observation_log.append_simplification(
            state.observation,
            definition,
            simplification.before.clone(),
            &simplification.after,
            &simplification.applied_rules,
            &simplification.effects,
            observation_options,
        );
        state.trace.extend(
            simplification
                .applied_rules
                .iter()
                .cloned()
                .map(|unique_id| TraceEntry {
                    depth: state.depth,
                    kind: TraceKind::Simplification,
                    label: None,
                    unique_id,
                }),
        );
        state.effects.commit(simplification.effects.iter().cloned());
    }
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
    definition: &BackendDefinition,
    mut state: ExecutionState,
    before: Pattern,
    remainder: RemainderBranch,
    observation_log: &mut ObservationLog,
    observation_options: Option<&ObservationOptions>,
) -> ExecutionState {
    state.diagnostics.extend(&remainder.diagnostics);
    let transition_pattern = remainder
        .simplifications
        .first()
        .map_or_else(|| remainder.pattern.clone(), |record| record.before.clone());
    let transition_remainder = RemainderBranch {
        pattern: transition_pattern,
        ..remainder.clone()
    };
    state.observation = observation_log.append_remainder(
        state.observation,
        before,
        &transition_remainder,
        observation_options,
    );
    state.trace.push(TraceEntry {
        depth: state.depth,
        kind: TraceKind::Remainder,
        label: None,
        unique_id: remainder.rule_ids.join(","),
    });
    for simplification in &remainder.simplifications {
        state.observation = observation_log.append_simplification(
            state.observation,
            definition,
            simplification.before.clone(),
            &simplification.after,
            &simplification.applied_rules,
            &simplification.effects,
            observation_options,
        );
        state.trace.extend(
            simplification
                .applied_rules
                .iter()
                .cloned()
                .map(|unique_id| TraceEntry {
                    depth: state.depth,
                    kind: TraceKind::Simplification,
                    label: None,
                    unique_id,
                }),
        );
    }
    state.effects.commit(remainder.effects);
    state.pattern = remainder.pattern;
    state.kind = ExecutionStateKind::Remaining(remainder.indeterminate);
    state.is_initial_input = false;
    state
}

#[derive(Clone)]
enum ExecutionStateKind {
    Rewritable,
    Remaining(Option<UndecidedStep>),
}

#[derive(Clone)]
struct ExecutionState {
    pattern: Pattern,
    depth: u64,
    trace: Vec<TraceEntry>,
    kind: ExecutionStateKind,
    observation: ObservationHead,
    effects: EffectJournal,
    io: ExecutionIoState,
    /// Whether the console capability remains available on this concrete execution prefix.
    io_enabled: bool,
    is_initial_input: bool,
    /// The backend diagnostics of the work this path went through so far, shared with the
    /// paths it forked from.
    diagnostics: PathDiagnostics,
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
            diagnostics: self.diagnostics.to_vec(),
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
    fn depth_bound_leaves_are_kept_around_a_stuck_leaf() {
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
            diagnostics: Vec::new(),
        };

        let leaves = merge_equal_final_leaves(vec![
            leaf("depth-before", HaltReason::DepthBound),
            leaf("stuck", HaltReason::Stuck),
            leaf("depth-after", HaltReason::DepthBound),
        ]);

        let halt_reasons = leaves
            .iter()
            .map(|leaf| leaf.halt_reason.clone())
            .collect::<Vec<_>>();
        assert_eq!(
            halt_reasons,
            [
                HaltReason::DepthBound,
                HaltReason::Stuck,
                HaltReason::DepthBound
            ]
        );
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
            diagnostics: Vec::new(),
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
