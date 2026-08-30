//! Priority-aware rewrite steps over internalized backend theories.

use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    hash::{Hash, Hasher},
    sync::Arc,
    time::Duration,
};

use rustc_hash::{FxHashMap, FxHasher};

use crate::{
    builtin::BuiltinEffect,
    cancellation::cancellation_requested,
    definedness::ceil_term,
    definition::{BackendDefinition, ConstructorHead, constructor_head},
    matching::{
        FailReason, MatchMode, MatchResult, match_terms_in_definition,
        unify_collection_remainders_all_in_definition,
    },
    rule::{Concreteness, ConstraintKind, Predicate, RewriteRule, RuleRhs, TermIndex, term_index},
    simplify::{
        DEFAULT_MAX_SIMPLIFICATION_ITERATIONS, PatternSimplification, SimplificationError,
        SimplificationOptions, simplify_pattern_details_with_solver,
        simplify_predicates_with_solver, simplify_with_solver,
    },
    smt::{NoSolver, Satisfiability, SmtError, SmtSolver, Validity},
    substitution::{Substitution, compose, extract_substitution, substitute, substitution_binding},
    term::{Sort, Symbol, SymbolType, Term, TermKind, Variable},
    timeout::{StepTimeoutController, StepTimeoutMode, StepTimeoutOptions},
    transition::{
        ObservationEvent, ObservationOptions, PatternDigest, TransitionClass, TransitionId,
        TransitionObservation,
    },
    unification::{UnificationFailure, UnificationResult, unify_term_pairs},
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Pattern {
    pub term: Term,
    pub constraints: Vec<Predicate>,
}

/// Apply the acyclic substitution encoded by a pattern's equality constraints while retaining
/// canonical equality predicates for later RPC projection.
pub fn normalize_pattern_substitution(pattern: &mut Pattern) -> Substitution {
    let (substitution, remaining) = extract_substitution(&pattern.constraints);
    if substitution.is_empty() {
        return substitution;
    }
    pattern.term = substitute(&pattern.term, &substitution);
    let mut constraints = substitution_predicates(&substitution);
    for predicate in substitute_predicates(&remaining, &substitution) {
        if !constraints.contains(&predicate) {
            constraints.push(predicate);
        }
    }
    pattern.constraints = constraints;
    substitution
}

fn substitution_predicates(substitution: &Substitution) -> Vec<Predicate> {
    substitution
        .iter()
        .map(|(variable, value)| Predicate::Equals(Term::variable(variable.clone()), value.clone()))
        .collect()
}

pub(crate) fn retain_substitution_predicates(
    constraints: &mut Vec<Predicate>,
    substitution: &Substitution,
) {
    for (variable, value) in substitution {
        let represented = constraints.iter().any(|predicate| {
            substitution_binding(predicate).is_some_and(|(represented, _)| represented == *variable)
        });
        if !represented {
            constraints.insert(
                0,
                Predicate::Equals(Term::variable(variable.clone()), value.clone()),
            );
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AppliedRule {
    /// The constrained pattern against which this application was constructed.
    pub before: Pattern,
    pub pattern: Pattern,
    pub label: Option<String>,
    pub unique_id: String,
    pub substitution: Substitution,
    /// Rule-variable bindings suitable for execution diagnostics. Variables introduced solely as
    /// term aliases (`P #as X`) are implementation details and are omitted from this view.
    pub rule_substitution: Substitution,
    /// Conditions introduced by this rule application, before they are merged with the incoming
    /// path constraints. RPC diagnostics use this provenance to report `rule-predicate` exactly.
    pub rule_predicates: Vec<Predicate>,
    pub effects: Vec<BuiltinEffect>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RemainderBranch {
    pub pattern: Pattern,
    pub rule_ids: Vec<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RewriteResult {
    Stuck(Pattern),
    Trivial(Pattern),
    Vacuous(Pattern),
    Finished(AppliedRule),
    Branch {
        original: Pattern,
        branches: Vec<AppliedRule>,
        remainder: Option<RemainderBranch>,
    },
    Indeterminate {
        pattern: Pattern,
        reason: IndeterminateReason,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum IndeterminateReason {
    Simplification {
        rule_id: Option<String>,
        error: SimplificationError,
    },
    Match {
        rule_id: String,
        substitution: Substitution,
        remainder: Vec<(Term, Term)>,
    },
    Requires {
        rule_id: String,
        predicates: Vec<Predicate>,
    },
    Concreteness {
        rule_id: String,
        variable: Variable,
    },
    Smt {
        rule_id: String,
        error: SmtError,
    },
    Remainder {
        rule_ids: Vec<String>,
        predicates: Vec<Predicate>,
        satisfiability: Result<Satisfiability, SmtError>,
    },
}

impl IndeterminateReason {
    fn simplification(rule_id: Option<&str>, error: SimplificationError) -> Self {
        Self::Simplification {
            rule_id: rule_id.map(str::to_owned),
            error,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExecutionOptions {
    pub max_depth: u64,
    pub max_breadth: Option<usize>,
    pub max_simplification_iterations: usize,
    pub mode: ExecutionMode,
    pub branch_mode: ExecutionBranchMode,
    pub cut_point_rules: BTreeSet<String>,
    pub terminal_rules: BTreeSet<String>,
    pub step_timeout: Option<Duration>,
    pub moving_average_timeout: bool,
    /// Treat the current configuration and its partial subterms as defined while matching rules.
    pub assume_initial_defined: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ExecutionMode {
    All,
    Any,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ExecutionBranchMode {
    StopAtBranch,
    ExploreAll,
}

impl Default for ExecutionOptions {
    fn default() -> Self {
        Self {
            max_depth: u64::MAX,
            max_breadth: None,
            max_simplification_iterations: DEFAULT_MAX_SIMPLIFICATION_ITERATIONS,
            mode: ExecutionMode::All,
            branch_mode: ExecutionBranchMode::ExploreAll,
            cut_point_rules: BTreeSet::new(),
            terminal_rules: BTreeSet::new(),
            step_timeout: None,
            moving_average_timeout: false,
            assume_initial_defined: false,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TraceEntry {
    pub depth: u64,
    pub kind: TraceKind,
    pub label: Option<String>,
    pub unique_id: String,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TraceKind {
    Simplification,
    Rewrite,
    Claim,
    Remainder,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum HaltReason {
    Cancelled,
    Stuck,
    Trivial,
    Vacuous,
    Branch {
        branches: Vec<AppliedRule>,
        remainder: Option<RemainderBranch>,
    },
    CutPointRule {
        rule: String,
        next_states: Vec<AppliedRule>,
    },
    TerminalRule {
        rule: String,
    },
    DepthBound,
    BreadthBound,
    Indeterminate(IndeterminateReason),
    Simplification(SimplificationError),
    Timeout(StepTimeoutMode),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExecutionLeaf {
    pub pattern: Pattern,
    pub depth: u64,
    pub trace: Vec<TraceEntry>,
    /// Stable semantic path prefix for this leaf when observation was enabled.
    pub branch: Vec<TransitionId>,
    /// Ordered structured events retained for this branch.
    pub observations: Vec<ObservationEvent>,
    pub halt_reason: HaltReason,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExecutionResult {
    pub leaves: Vec<ExecutionLeaf>,
    pub effects: Vec<BuiltinEffect>,
}

pub fn execute(
    definition: &BackendDefinition,
    initial: Pattern,
    options: ExecutionOptions,
) -> ExecutionResult {
    execute_with_solver(definition, initial, options, &NoSolver)
}

pub fn execute_with_solver(
    definition: &BackendDefinition,
    initial: Pattern,
    options: ExecutionOptions,
    solver: &dyn SmtSolver,
) -> ExecutionResult {
    execute_with_solver_and_observer(definition, initial, options, solver, |_| {})
}

/// Execute with branch-local structured transition observation enabled.
pub fn execute_observed(
    definition: &BackendDefinition,
    initial: Pattern,
    options: ExecutionOptions,
    observation: &ObservationOptions,
) -> ExecutionResult {
    execute_observed_with_solver(definition, initial, options, &NoSolver, observation)
}

/// Execute with structured observation and the supplied SMT solver.
pub fn execute_observed_with_solver(
    definition: &BackendDefinition,
    initial: Pattern,
    options: ExecutionOptions,
    solver: &dyn SmtSolver,
    observation: &ObservationOptions,
) -> ExecutionResult {
    execute_using(
        definition,
        initial,
        options,
        solver,
        Some(observation),
        |_| {},
    )
}

pub fn execute_with_solver_and_observer(
    definition: &BackendDefinition,
    initial: Pattern,
    options: ExecutionOptions,
    solver: &dyn SmtSolver,
    observe: impl FnMut(&BuiltinEffect),
) -> ExecutionResult {
    execute_using(definition, initial, options, solver, None, observe)
}

fn execute_using(
    definition: &BackendDefinition,
    initial: Pattern,
    options: ExecutionOptions,
    solver: &dyn SmtSolver,
    observation: Option<&ObservationOptions>,
    mut observe: impl FnMut(&BuiltinEffect),
) -> ExecutionResult {
    let mut fresh_counter = 0;
    let mut observation_log = ObservationLog::default();
    let mut pending = VecDeque::from([ExecutionState {
        pattern: initial,
        depth: 0,
        trace: Vec::new(),
        observation: None,
    }]);
    let mut leaves = Vec::new();
    let mut effects = Vec::new();
    let timeout_controller = StepTimeoutController::new(StepTimeoutOptions {
        manual: options.step_timeout,
        moving_average: options.moving_average_timeout,
    });
    if options.max_breadth == Some(0) {
        return ExecutionResult {
            leaves: pending
                .drain(..)
                .map(|state| execution_state_at_breadth_bound(state, &observation_log))
                .collect(),
            effects,
        };
    }
    while let Some(mut state) = pending.pop_front() {
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
        let retained_substitution = normalize_pattern_substitution(&mut state.pattern);
        let pattern_before_constraint_simplification = state.pattern.clone();
        let mut deferred_initial_vacuity = None;
        let simplified_constraints = simplify_predicates_with_solver(
            definition,
            &state.pattern.constraints,
            &[],
            SimplificationOptions {
                max_iterations: options.max_simplification_iterations,
            },
            solver,
        );
        finish_if_interrupted!();
        match simplified_constraints {
            Ok(mut constraints) => {
                retain_substitution_predicates(&mut constraints, &retained_substitution);
                state.pattern.constraints = constraints;
                normalize_pattern_substitution(&mut state.pattern);
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
                leaves.push(state.leaf(HaltReason::Vacuous, &observation_log));
                continue;
            }
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
        finish_if_interrupted!();
        match simplified {
            Ok(simplified) => {
                state.pattern.term = simplified.term;
                state.pattern.constraints.extend(simplified.constraints);
                normalize_pattern_substitution(&mut state.pattern);
                record_effects(&mut effects, simplified.effects, &mut observe);
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
                leaves.push(state.leaf(HaltReason::Simplification(error), &observation_log));
                continue;
            }
        }
        if state.depth >= options.max_depth {
            leaves.push(state.leaf(HaltReason::DepthBound, &observation_log));
            continue;
        }
        let rewritten = rewrite_step_with_mode(
            definition,
            &state.pattern,
            &mut fresh_counter,
            SimplificationOptions {
                max_iterations: options.max_simplification_iterations,
            },
            solver,
            options.mode,
            options.assume_initial_defined,
        );
        finish_if_interrupted!();
        match rewritten {
            RewriteResult::Stuck(pattern) => {
                let (pattern, halt_reason) = deferred_initial_vacuity
                    .map_or((pattern, HaltReason::Stuck), |pattern| {
                        (pattern, HaltReason::Vacuous)
                    });
                leaves.push(state.leaf_with_pattern(pattern, halt_reason, &observation_log));
            }
            RewriteResult::Trivial(pattern) => {
                leaves.push(state.leaf_with_pattern(pattern, HaltReason::Trivial, &observation_log))
            }
            RewriteResult::Vacuous(pattern) => {
                leaves.push(state.leaf_with_pattern(pattern, HaltReason::Vacuous, &observation_log))
            }
            RewriteResult::Indeterminate { pattern, reason } => {
                let halt_reason = match reason {
                    IndeterminateReason::Simplification { error, .. } => {
                        HaltReason::Simplification(error)
                    }
                    reason => HaltReason::Indeterminate(reason),
                };
                leaves.push(state.leaf_with_pattern(pattern, halt_reason, &observation_log));
            }
            RewriteResult::Finished(applied) => {
                record_effects(&mut effects, applied.effects.iter().cloned(), &mut observe);
                if let Some(rule) = selected_stop_rule(&applied, &options.cut_point_rules) {
                    let mut applied = applied;
                    applied.pattern = match simplify_result_pattern(
                        definition,
                        &applied.pattern,
                        options.max_simplification_iterations,
                        solver,
                        state.depth,
                        &mut state.trace,
                        &mut effects,
                        &mut observe,
                    ) {
                        Ok(pattern) => pattern,
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
                        leaves.push(state.leaf_with_pattern(
                            applied.pattern,
                            HaltReason::Trivial,
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
                let mut next = next_state(
                    state.depth,
                    state.trace,
                    state.observation,
                    applied,
                    &mut observation_log,
                    observation,
                );
                if let Some(rule) = terminal_rule {
                    next.pattern = match simplify_result_pattern(
                        definition,
                        &next.pattern,
                        options.max_simplification_iterations,
                        solver,
                        next.depth,
                        &mut next.trace,
                        &mut effects,
                        &mut observe,
                    ) {
                        Ok(pattern) => pattern,
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
                    leaves.push(next.leaf(
                        if trivial {
                            HaltReason::Trivial
                        } else {
                            HaltReason::TerminalRule { rule }
                        },
                        &observation_log,
                    ));
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
            } => {
                if options.branch_mode == ExecutionBranchMode::StopAtBranch {
                    if let Err(error) = expand_stopped_branch_remainder(
                        definition,
                        &mut branches,
                        &mut remainder,
                        &mut fresh_counter,
                        SimplificationOptions {
                            max_iterations: options.max_simplification_iterations,
                        },
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
                        &mut effects,
                        &mut observe,
                    ) {
                        Ok(pattern) => pattern,
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
                        leaves.push(state.leaf_with_pattern(
                            original,
                            HaltReason::Trivial,
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
                        match simplify_result_pattern(
                            definition,
                            &applied.pattern,
                            options.max_simplification_iterations,
                            solver,
                            state.depth + 1,
                            &mut state.trace,
                            &mut effects,
                            &mut observe,
                        ) {
                            Ok(pattern) => {
                                applied.pattern = pattern;
                                if predicates_truth(&applied.pattern.constraints) != Truth::False {
                                    simplified_branches.push(applied);
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
                            &mut effects,
                            &mut observe,
                        ) {
                            Ok(pattern) => pattern,
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
                            record_effects(
                                &mut effects,
                                applied.effects.iter().cloned(),
                                &mut observe,
                            );
                            enqueue_execution_states(
                                &mut pending,
                                vec![next_state(
                                    state.depth,
                                    state.trace,
                                    state.observation,
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
                                    state.depth,
                                    state.trace,
                                    state.observation,
                                    before,
                                    remainder,
                                    &mut observation_log,
                                    observation,
                                )],
                            );
                        }
                        _ => {
                            for applied in &branches {
                                record_effects(
                                    &mut effects,
                                    applied.effects.iter().cloned(),
                                    &mut observe,
                                );
                            }
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
                    record_effects(&mut effects, applied.effects.iter().cloned(), &mut observe);
                    next.push(next_state(
                        state.depth,
                        state.trace.clone(),
                        state.observation,
                        applied,
                        &mut observation_log,
                        observation,
                    ));
                }
                if let Some(remainder) = remainder {
                    let before = state.pattern;
                    next.push(remaining_state(
                        state.depth,
                        state.trace,
                        state.observation,
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
    ExecutionResult { leaves, effects }
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
            RewriteResult::Trivial(_) | RewriteResult::Vacuous(_) => break,
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

#[allow(clippy::too_many_arguments)]
fn simplify_result_pattern(
    definition: &BackendDefinition,
    pattern: &Pattern,
    max_iterations: usize,
    solver: &dyn SmtSolver,
    depth: u64,
    trace: &mut Vec<TraceEntry>,
    effects: &mut Vec<BuiltinEffect>,
    observe: &mut impl FnMut(&BuiltinEffect),
) -> Result<Pattern, SimplificationError> {
    let PatternSimplification {
        pattern,
        applied_rules,
        effects: simplified_effects,
    } = simplify_pattern_details_with_solver(
        definition,
        pattern,
        SimplificationOptions { max_iterations },
        solver,
    )?;
    trace.extend(applied_rules.into_iter().map(|unique_id| TraceEntry {
        depth,
        kind: TraceKind::Simplification,
        label: None,
        unique_id,
    }));
    record_effects(effects, simplified_effects, observe);
    Ok(pattern)
}

fn next_state(
    depth: u64,
    mut trace: Vec<TraceEntry>,
    observation: ObservationHead,
    applied: AppliedRule,
    observation_log: &mut ObservationLog,
    observation_options: Option<&ObservationOptions>,
) -> ExecutionState {
    let observation = observation_log.append_applied(observation, &applied, observation_options);
    trace.push(TraceEntry {
        depth: depth + 1,
        kind: TraceKind::Rewrite,
        label: applied.label,
        unique_id: applied.unique_id,
    });
    ExecutionState {
        pattern: applied.pattern,
        depth: depth + 1,
        trace,
        observation,
    }
}

fn remaining_state(
    depth: u64,
    mut trace: Vec<TraceEntry>,
    observation: ObservationHead,
    before: Pattern,
    remainder: RemainderBranch,
    observation_log: &mut ObservationLog,
    observation_options: Option<&ObservationOptions>,
) -> ExecutionState {
    let observation =
        observation_log.append_remainder(observation, before, &remainder, observation_options);
    trace.push(TraceEntry {
        depth,
        kind: TraceKind::Remainder,
        label: None,
        unique_id: remainder.rule_ids.join(","),
    });
    ExecutionState {
        pattern: remainder.pattern,
        depth,
        trace,
        observation,
    }
}

struct ExecutionState {
    pattern: Pattern,
    depth: u64,
    trace: Vec<TraceEntry>,
    observation: ObservationHead,
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

#[derive(Clone, Copy)]
struct ObservationNodeId(usize);

type ObservationHead = Option<ObservationNodeId>;

struct ObservationNode {
    parent: ObservationHead,
    transition: TransitionId,
    event: Option<ObservationEvent>,
}

#[derive(Default)]
struct ObservationLog {
    nodes: Vec<ObservationNode>,
}

impl ObservationLog {
    fn append_applied(
        &mut self,
        parent: ObservationHead,
        applied: &AppliedRule,
        options: Option<&ObservationOptions>,
    ) -> ObservationHead {
        let options = options?;
        let id = TransitionId {
            rule: applied.unique_id.clone(),
            target: PatternDigest::of(&applied.pattern),
        };
        let event = options.observes(&applied.unique_id).then(|| {
            ObservationEvent::Transition(TransitionObservation {
                id: id.clone(),
                class: TransitionClass::Rewrite,
                rule_label: applied.label.clone(),
                bindings: applied.rule_substitution.clone(),
                introduced_predicates: applied.rule_predicates.clone(),
                before: applied.before.clone(),
                after: applied.pattern.clone(),
                effects: applied.effects.clone(),
            })
        });
        Some(self.push(ObservationNode {
            parent,
            transition: id,
            event,
        }))
    }

    fn append_remainder(
        &mut self,
        parent: ObservationHead,
        before: Pattern,
        remainder: &RemainderBranch,
        options: Option<&ObservationOptions>,
    ) -> ObservationHead {
        let options = options?;
        let id = TransitionId {
            rule: format!("remainder:{}", remainder.rule_ids.join(",")),
            target: PatternDigest::of(&remainder.pattern),
        };
        let event = options.rules_are_unfiltered().then(|| {
            ObservationEvent::Transition(TransitionObservation {
                id: id.clone(),
                class: TransitionClass::Remainder,
                rule_label: None,
                bindings: Substitution::new(),
                introduced_predicates: Vec::new(),
                before,
                after: remainder.pattern.clone(),
                effects: Vec::new(),
            })
        });
        Some(self.push(ObservationNode {
            parent,
            transition: id,
            event,
        }))
    }

    fn push(&mut self, node: ObservationNode) -> ObservationNodeId {
        let id = ObservationNodeId(self.nodes.len());
        self.nodes.push(node);
        id
    }

    fn materialize(&self, mut head: ObservationHead) -> (Vec<TransitionId>, Vec<ObservationEvent>) {
        let mut branch = Vec::new();
        let mut events = Vec::new();
        while let Some(id) = head {
            let node = &self.nodes[id.0];
            branch.push(node.transition.clone());
            if let Some(event) = &node.event {
                events.push(event.clone());
            }
            head = node.parent;
        }
        branch.reverse();
        events.reverse();
        (branch, events)
    }
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) enum Truth {
    True,
    False,
    #[default]
    Unknown,
}

pub fn rewrite_step(
    definition: &BackendDefinition,
    pattern: &Pattern,
    fresh_counter: &mut u64,
) -> RewriteResult {
    rewrite_step_with_solver(definition, pattern, fresh_counter, &NoSolver)
}

pub fn rewrite_step_with_solver(
    definition: &BackendDefinition,
    pattern: &Pattern,
    fresh_counter: &mut u64,
    solver: &dyn SmtSolver,
) -> RewriteResult {
    rewrite_step_with_options(
        definition,
        pattern,
        fresh_counter,
        SimplificationOptions::default(),
        solver,
    )
}

pub(crate) fn rewrite_step_with_options(
    definition: &BackendDefinition,
    pattern: &Pattern,
    fresh_counter: &mut u64,
    simplification_options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> RewriteResult {
    rewrite_step_with_mode(
        definition,
        pattern,
        fresh_counter,
        simplification_options,
        solver,
        ExecutionMode::All,
        false,
    )
}

fn rewrite_step_with_mode(
    definition: &BackendDefinition,
    pattern: &Pattern,
    fresh_counter: &mut u64,
    simplification_options: SimplificationOptions,
    solver: &dyn SmtSolver,
    mode: ExecutionMode,
    assume_initial_defined: bool,
) -> RewriteResult {
    if predicates_truth(&pattern.constraints) == Truth::False {
        return RewriteResult::Vacuous(pattern.clone());
    }
    match mode {
        ExecutionMode::All => rewrite_step_all(
            definition,
            pattern,
            fresh_counter,
            simplification_options,
            solver,
            assume_initial_defined,
        ),
        ExecutionMode::Any => rewrite_step_any(
            definition,
            pattern,
            fresh_counter,
            simplification_options,
            solver,
        ),
    }
}

fn rewrite_step_all(
    definition: &BackendDefinition,
    pattern: &Pattern,
    fresh_counter: &mut u64,
    simplification_options: SimplificationOptions,
    solver: &dyn SmtSolver,
    assume_initial_defined: bool,
) -> RewriteResult {
    let index = term_index(&pattern.term);
    let priority_groups = applicable_groups(definition, &index);
    if priority_groups.is_empty() {
        return RewriteResult::Stuck(pattern.clone());
    }
    let mut saw_trivial = false;
    for rules in priority_groups.values() {
        let mut applied = Vec::new();
        for rule in rules {
            match apply_rule(
                definition,
                rule,
                pattern,
                fresh_counter,
                simplification_options,
                solver,
                assume_initial_defined,
            ) {
                RuleAttempt::NotApplicable => {}
                RuleAttempt::Trivial => saw_trivial = true,
                RuleAttempt::Applied(results) => applied.extend(results),
                RuleAttempt::Indeterminate(reason) => {
                    return RewriteResult::Indeterminate {
                        pattern: pattern.clone(),
                        reason,
                    };
                }
            }
        }
        let raw_remainder = applied
            .iter()
            .map(|application| application.remainder.clone())
            .collect::<Vec<_>>();
        let remainder = match simplify_predicates_with_solver(
            definition,
            &raw_remainder,
            &pattern.constraints,
            simplification_options,
            solver,
        ) {
            Ok(remainder) => remainder,
            Err(error) => {
                return RewriteResult::Indeterminate {
                    pattern: pattern.clone(),
                    reason: IndeterminateReason::simplification(None, error),
                };
            }
        };
        let remainder_result = if applied.is_empty() || predicates_truth(&remainder) == Truth::False
        {
            Ok(Satisfiability::Unsat)
        } else {
            let mut predicates = pattern.constraints.clone();
            predicates.extend(remainder.iter().cloned());
            if violates_finite_constructor_domain(definition, &predicates) {
                Ok(Satisfiability::Unsat)
            } else {
                solver.is_sat(&predicates, &Substitution::new())
            }
        };
        if !matches!(
            remainder_result,
            Ok(Satisfiability::Unsat | Satisfiability::Sat)
        ) && !applied.is_empty()
        {
            return RewriteResult::Indeterminate {
                pattern: pattern.clone(),
                reason: IndeterminateReason::Remainder {
                    rule_ids: applied
                        .iter()
                        .map(|application| application.applied.unique_id.clone())
                        .collect(),
                    predicates: remainder,
                    satisfiability: remainder_result,
                },
            };
        }
        let remainder = if matches!(remainder_result, Ok(Satisfiability::Sat)) {
            let rule_ids = applied
                .iter()
                .map(|application| application.applied.unique_id.clone())
                .collect();
            let mut remainder_pattern = pattern.clone();
            extend_unique(
                &mut remainder_pattern.constraints,
                remainder.iter().cloned(),
            );
            Some(RemainderBranch {
                pattern: remainder_pattern,
                rule_ids,
            })
        } else {
            None
        };
        match applied.len() {
            0 => {}
            1 if remainder.is_none() => {
                return RewriteResult::Finished(applied.pop().unwrap().applied);
            }
            _ => {
                return RewriteResult::Branch {
                    original: pattern.clone(),
                    branches: applied
                        .into_iter()
                        .map(|application| application.applied)
                        .collect(),
                    remainder,
                };
            }
        }
    }
    if saw_trivial {
        RewriteResult::Trivial(pattern.clone())
    } else {
        RewriteResult::Stuck(pattern.clone())
    }
}

fn rewrite_step_any(
    definition: &BackendDefinition,
    pattern: &Pattern,
    fresh_counter: &mut u64,
    simplification_options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> RewriteResult {
    let index = term_index(&pattern.term);
    let priority_groups = applicable_groups(definition, &index);
    if priority_groups.is_empty() {
        return RewriteResult::Stuck(pattern.clone());
    }

    let mut remaining = pattern.clone();
    let mut remainder_conditions = Vec::new();
    let mut applied = Vec::new();
    let mut saw_trivial = false;
    for rule in priority_groups.values().flatten() {
        if predicates_truth(&remaining.constraints) == Truth::False {
            break;
        }
        match apply_rule(
            definition,
            rule,
            &remaining,
            fresh_counter,
            simplification_options,
            solver,
            false,
        ) {
            RuleAttempt::NotApplicable => {}
            RuleAttempt::Trivial => saw_trivial = true,
            RuleAttempt::Applied(results) => {
                for application in results {
                    extend_unique(
                        &mut remainder_conditions,
                        std::iter::once(application.remainder.clone()),
                    );
                    extend_unique(
                        &mut remaining.constraints,
                        std::iter::once(application.remainder),
                    );
                    applied.push(application.applied);
                }
                match simplify_predicates_with_solver(
                    definition,
                    &remaining.constraints,
                    &pattern.constraints,
                    simplification_options,
                    solver,
                ) {
                    Ok(constraints) => remaining.constraints = constraints,
                    Err(error) => {
                        return RewriteResult::Indeterminate {
                            pattern: remaining,
                            reason: IndeterminateReason::simplification(
                                Some(&rule.attributes.unique_id),
                                error,
                            ),
                        };
                    }
                }
            }
            RuleAttempt::Indeterminate(reason) => {
                return RewriteResult::Indeterminate {
                    pattern: remaining,
                    reason,
                };
            }
        }
    }

    if applied.is_empty() {
        return if saw_trivial {
            RewriteResult::Trivial(pattern.clone())
        } else {
            RewriteResult::Stuck(pattern.clone())
        };
    }

    let remainder_result = if predicates_truth(&remaining.constraints) == Truth::False
        || violates_finite_constructor_domain(definition, &remaining.constraints)
    {
        Ok(Satisfiability::Unsat)
    } else {
        solver.is_sat(&remaining.constraints, &Substitution::new())
    };
    if !matches!(
        remainder_result,
        Ok(Satisfiability::Unsat | Satisfiability::Sat)
    ) {
        return RewriteResult::Indeterminate {
            pattern: pattern.clone(),
            reason: IndeterminateReason::Remainder {
                rule_ids: applied
                    .iter()
                    .map(|application| application.unique_id.clone())
                    .collect(),
                predicates: remainder_conditions,
                satisfiability: remainder_result,
            },
        };
    }
    let remainder = matches!(remainder_result, Ok(Satisfiability::Sat)).then(|| RemainderBranch {
        pattern: remaining,
        rule_ids: applied
            .iter()
            .map(|application| application.unique_id.clone())
            .collect(),
    });
    if applied.len() == 1 && remainder.is_none() {
        RewriteResult::Finished(applied.pop().unwrap())
    } else {
        RewriteResult::Branch {
            original: pattern.clone(),
            branches: applied,
            remainder,
        }
    }
}

fn applicable_groups(
    definition: &BackendDefinition,
    index: &TermIndex,
) -> std::collections::BTreeMap<u8, Vec<std::sync::Arc<RewriteRule>>> {
    let mut groups = std::collections::BTreeMap::new();
    let covered = if index == &TermIndex::Variable {
        vec![index]
    } else {
        vec![index, &TermIndex::Variable]
    };
    for covered in covered {
        if let Some(found) = definition.rewrite_theory.get(covered) {
            for (priority, rules) in found {
                groups
                    .entry(*priority)
                    .or_insert_with(Vec::new)
                    .extend(rules.iter().cloned());
            }
        }
    }
    groups
}

enum RuleAttempt {
    NotApplicable,
    Trivial,
    Applied(Vec<RuleApplication>),
    Indeterminate(IndeterminateReason),
}

pub(crate) struct RecoveredMatch {
    pub(crate) result: MatchResult,
    pub(crate) conditions: Vec<Predicate>,
}

/// Conservatively recover matches that Booster delegates to Kore.
///
/// Both sides of each remainder are simplified after applying the partial substitution, and any
/// conditions produced by simplification are retained. For a function pattern with one unbound
/// result-sorted variable, the concrete subject is also tried as a witness; the match is accepted
/// only when evaluating that witness reproduces the subject exactly. A failed witness remains
/// indeterminate because it does not prove that no other witness exists.
pub(crate) fn recover_indeterminate_match(
    definition: &BackendDefinition,
    mut substitution: Substitution,
    remainder: Vec<(Term, Term)>,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Result<RecoveredMatch, SimplificationError> {
    let mut unresolved = Vec::new();
    let mut conditions = Vec::new();
    for (pattern, subject) in remainder {
        let pattern = substitute(&pattern, &substitution);
        let subject = substitute(&subject, &substitution);
        let mut knowledge = known_predicates.to_vec();
        extend_unique(&mut knowledge, conditions.iter().cloned());
        let simplified_pattern =
            simplify_with_solver(definition, &pattern, &knowledge, options, solver)?;
        extend_unique(&mut conditions, simplified_pattern.constraints);
        let simplified_pattern = simplified_pattern.term;
        let mut knowledge = known_predicates.to_vec();
        extend_unique(&mut knowledge, conditions.iter().cloned());
        let simplified_subject =
            simplify_with_solver(definition, &subject, &knowledge, options, solver)?;
        extend_unique(&mut conditions, simplified_subject.constraints);
        let simplified_subject = simplified_subject.term;

        if !simplified_pattern
            .attributes()
            .variables
            .is_disjoint(&simplified_subject.attributes().variables)
        {
            match unify_term_pairs(
                definition,
                substitution.clone(),
                [(simplified_pattern.clone(), simplified_subject.clone())],
            ) {
                UnificationResult::Unified(unified) => {
                    substitution = unified.substitution;
                    extend_unique(&mut conditions, unified.constraints);
                    continue;
                }
                UnificationResult::Bottom(failure) => {
                    let reason = match failure {
                        UnificationFailure::VariableRecursion(variable, term) => {
                            FailReason::VariableRecursion(variable, term)
                        }
                        UnificationFailure::DifferentSorts(left, right) => {
                            FailReason::DifferentSorts(left, right)
                        }
                        UnificationFailure::DifferentValues(left, right) => {
                            FailReason::DifferentValues(left, right)
                        }
                        UnificationFailure::DifferentSymbols(left, right) => {
                            FailReason::DifferentSymbols(left, right)
                        }
                    };
                    return Ok(RecoveredMatch {
                        result: MatchResult::Failed(reason),
                        conditions,
                    });
                }
                UnificationResult::Unsupported { .. } => {}
            }
        }

        let pair_remainder = match match_terms_in_definition(
            MatchMode::Rewrite,
            definition,
            &simplified_pattern,
            &simplified_subject,
        ) {
            MatchResult::Success(found) => {
                substitution = compose(&found, &substitution);
                continue;
            }
            MatchResult::Failed(reason) => {
                return Ok(RecoveredMatch {
                    result: MatchResult::Failed(reason),
                    conditions,
                });
            }
            MatchResult::Indeterminate {
                substitution: found,
                remainder,
            } => {
                substitution = compose(&found, &substitution);
                remainder
            }
        };

        let TermKind::Application { symbol, .. } = simplified_pattern.kind() else {
            unresolved.extend(pair_remainder);
            continue;
        };
        if !matches!(symbol.attributes.symbol_type, SymbolType::Function(_))
            || !simplified_subject.attributes().constructor_like
        {
            unresolved.extend(pair_remainder);
            continue;
        }
        let candidates = simplified_pattern
            .attributes()
            .variables
            .iter()
            .filter(|variable| {
                !substitution.contains_key(*variable) && variable.sort == simplified_subject.sort()
            })
            .cloned()
            .collect::<Vec<_>>();
        let [candidate] = candidates.as_slice() else {
            unresolved.extend(pair_remainder);
            continue;
        };
        let witness = Substitution::from([(candidate.clone(), simplified_subject.clone())]);
        let candidate_substitution = compose(&witness, &substitution);
        let candidate_pattern = substitute(&pattern, &candidate_substitution);
        let mut witness_knowledge = known_predicates.to_vec();
        extend_unique(&mut witness_knowledge, conditions.iter().cloned());
        let candidate_pattern = simplify_with_solver(
            definition,
            &candidate_pattern,
            &witness_knowledge,
            options,
            solver,
        )?;
        extend_unique(&mut conditions, candidate_pattern.constraints);
        match match_terms_in_definition(
            MatchMode::Rewrite,
            definition,
            &candidate_pattern.term,
            &simplified_subject,
        ) {
            MatchResult::Success(found) => {
                substitution = compose(&found, &candidate_substitution);
                continue;
            }
            MatchResult::Failed(_) | MatchResult::Indeterminate { .. } => {}
        }
        unresolved.extend(pair_remainder);
    }

    let conditions = substitute_predicates(&conditions, &substitution);
    let result = if unresolved.is_empty() {
        MatchResult::Success(substitution)
    } else {
        MatchResult::Indeterminate {
            substitution,
            remainder: unresolved,
        }
    };
    Ok(RecoveredMatch { result, conditions })
}

enum GeneralUnificationRecovery {
    Unified(Vec<(Substitution, Vec<Predicate>)>),
    Bottom,
    Unsupported,
}

fn recover_general_unification(
    definition: &BackendDefinition,
    rule: &RewriteRule,
    pattern: &Pattern,
    substitution: Substitution,
    remainder: &[(Term, Term)],
    fresh_counter: &mut u64,
) -> GeneralUnificationRecovery {
    match unify_term_pairs(definition, substitution, remainder.iter().cloned()) {
        UnificationResult::Bottom(_) => GeneralUnificationRecovery::Bottom,
        UnificationResult::Unsupported {
            substitution,
            constraints,
            remainder,
        } => {
            let Some(solutions) = unify_collection_remainders_all_in_definition(
                MatchMode::Rewrite,
                definition,
                substitution,
                &remainder,
            ) else {
                return GeneralUnificationRecovery::Unsupported;
            };
            if solutions.is_empty() {
                return GeneralUnificationRecovery::Bottom;
            }
            GeneralUnificationRecovery::Unified(finalize_general_unification(
                definition,
                rule,
                pattern,
                solutions,
                &constraints,
                &remainder,
                fresh_counter,
            ))
        }
        UnificationResult::Unified(unified) => {
            GeneralUnificationRecovery::Unified(finalize_general_unification(
                definition,
                rule,
                pattern,
                vec![unified.substitution],
                &unified.constraints,
                &[],
                fresh_counter,
            ))
        }
    }
}

fn finalize_general_unification(
    definition: &BackendDefinition,
    rule: &RewriteRule,
    pattern: &Pattern,
    solutions: Vec<Substitution>,
    constraints: &[Predicate],
    collection_pairs: &[(Term, Term)],
    fresh_counter: &mut u64,
) -> Vec<(Substitution, Vec<Predicate>)> {
    solutions
        .into_iter()
        .map(|substitution| {
            let (substitution, _) =
                freshen_unbound_rule_variables(rule, pattern, substitution, fresh_counter);
            let mut constraints = substitute_predicates(constraints, &substitution);
            extend_unique(
                &mut constraints,
                collection_unification_definedness(definition, collection_pairs, &substitution),
            );
            (substitution, constraints)
        })
        .collect()
}

fn collection_unification_definedness(
    definition: &BackendDefinition,
    pairs: &[(Term, Term)],
    substitution: &Substitution,
) -> Vec<Predicate> {
    let mut conditions = Vec::new();
    for (left, right) in pairs {
        extend_unique(
            &mut conditions,
            ceil_term(definition, &substitute(left, substitution)),
        );
        extend_unique(
            &mut conditions,
            ceil_term(definition, &substitute(right, substitution)),
        );
    }
    conditions
}

/// Recover first-order narrowing when a functional pattern is matched by a symbolic
/// configuration variable.
///
/// Rule variables left unbound by ordinary matching become fresh variables in the successor. The
/// resulting equality is retained on the applied branch and negated on its complementary branch.
/// Function-like fragments additionally retain the definedness conditions produced by their
/// `ceil` theory.
fn recover_functional_symbolic_match(
    definition: &BackendDefinition,
    rule: &RewriteRule,
    pattern: &Pattern,
    substitution: Substitution,
    remainder: &[(Term, Term)],
    fresh_counter: &mut u64,
) -> Option<(Substitution, Vec<Predicate>)> {
    for (rule_term, configuration_term) in remainder {
        let rule_term = substitute(rule_term, &substitution);
        let configuration_term = substitute(configuration_term, &substitution);
        let TermKind::Variable(configuration_variable) = configuration_term.kind() else {
            return None;
        };
        if !is_functional_pattern(&rule_term)
            || rule_term
                .attributes()
                .variables
                .contains(configuration_variable)
            || !definition
                .sort_graph
                .check_subsort(&rule_term.sort(), &configuration_variable.sort)
                .ok()?
        {
            return None;
        }
    }

    let (substitution, fresh_variables) =
        freshen_unbound_rule_variables(rule, pattern, substitution, fresh_counter);

    let mut conditions = Vec::new();
    for (rule_term, configuration_term) in remainder {
        let rule_term = substitute(rule_term, &substitution);
        let configuration_term = substitute(configuration_term, &substitution);
        if rule_term == configuration_term {
            continue;
        }
        let TermKind::Variable(configuration_variable) = configuration_term.kind() else {
            return None;
        };
        debug_assert!(is_functional_pattern(&rule_term));
        debug_assert!(
            definition
                .sort_graph
                .check_subsort(&rule_term.sort(), &configuration_variable.sort)
                .unwrap_or(false)
        );
        let definedness = if contains_function_pattern(&rule_term) {
            ceil_term(definition, &rule_term)
        } else {
            Vec::new()
        };
        conditions.push(Predicate::Equals(configuration_term, rule_term));
        for predicate in definedness {
            if matches!(
                &predicate,
                Predicate::Ceil(term)
                    if matches!(term.kind(), TermKind::Variable(variable) if fresh_variables.contains(variable))
            ) || conditions.contains(&predicate)
            {
                continue;
            }
            conditions.push(predicate);
        }
    }
    (!conditions.is_empty()).then_some((substitution, conditions))
}

fn freshen_unbound_rule_variables(
    rule: &RewriteRule,
    pattern: &Pattern,
    mut substitution: Substitution,
    fresh_counter: &mut u64,
) -> (Substitution, BTreeSet<Variable>) {
    let mut names_to_avoid = pattern_variable_names(pattern)
        .into_iter()
        .chain(
            substitution
                .values()
                .flat_map(|term| term.attributes().variables.iter())
                .map(|variable| variable.name.clone()),
        )
        .collect::<BTreeSet<_>>();
    let unbound = rule
        .lhs
        .attributes()
        .variables
        .iter()
        .filter(|variable| !substitution.contains_key(*variable))
        .cloned()
        .collect::<Vec<_>>();
    let mut fresh_variables = BTreeSet::new();
    for variable in unbound {
        let base_name = variable
            .name
            .strip_prefix("Rule#")
            .or_else(|| variable.name.strip_prefix("Eq#"))
            .unwrap_or(variable.name.as_ref());
        let existential = variable.with_name(format!("Ex#{base_name}"));
        let fresh = fresh_variable(&existential, &mut names_to_avoid, fresh_counter);
        let TermKind::Variable(fresh_variable) = fresh.kind() else {
            unreachable!("fresh terms are variables")
        };
        fresh_variables.insert(fresh_variable.clone());
        substitution = compose(&Substitution::from([(variable, fresh)]), &substitution);
    }
    (substitution, fresh_variables)
}

/// Preserve unresolved functional unification as equality conditions after simplification reaches
/// a fixed point. AC collection equations are deliberately excluded because they require their
/// own multi-solution theory rather than one opaque equality.
fn recover_function_equality_match(
    rule: &RewriteRule,
    pattern: &Pattern,
    substitution: Substitution,
    remainder: &[(Term, Term)],
    fresh_counter: &mut u64,
) -> Option<(Substitution, Vec<Predicate>)> {
    if remainder.is_empty()
        || remainder.iter().any(|(left, right)| {
            left.sort() != right.sort()
                || is_collection_term(left)
                || is_collection_term(right)
                || (!contains_function_pattern(left) && !contains_function_pattern(right))
        })
    {
        return None;
    }
    let (substitution, _) =
        freshen_unbound_rule_variables(rule, pattern, substitution, fresh_counter);
    let conditions = remainder
        .iter()
        .filter_map(|(left, right)| {
            let left = substitute(left, &substitution);
            let right = substitute(right, &substitution);
            (left != right).then_some(Predicate::Equals(left, right))
        })
        .collect::<Vec<_>>();
    (!conditions.is_empty()).then_some((substitution, conditions))
}

fn is_collection_term(term: &Term) -> bool {
    matches!(
        term.kind(),
        TermKind::Map { .. } | TermKind::List { .. } | TermKind::Set { .. }
    )
}

fn is_functional_pattern(term: &Term) -> bool {
    match term.kind() {
        TermKind::Application {
            symbol, arguments, ..
        } => {
            matches!(
                symbol.attributes.symbol_type,
                SymbolType::Constructor | SymbolType::Function(_)
            ) && arguments.iter().all(is_functional_pattern)
        }
        TermKind::Map { entries, rest, .. } => {
            entries
                .iter()
                .all(|(key, value)| is_functional_pattern(key) && is_functional_pattern(value))
                && rest.as_ref().is_none_or(is_functional_pattern)
        }
        TermKind::List { heads, rest, .. } => {
            heads.iter().all(is_functional_pattern)
                && rest.as_ref().is_none_or(|(middle, tails)| {
                    is_functional_pattern(middle) && tails.iter().all(is_functional_pattern)
                })
        }
        TermKind::Set { elements, rest, .. } => {
            elements.iter().all(is_functional_pattern)
                && rest.as_ref().is_none_or(is_functional_pattern)
        }
        TermKind::DomainValue { .. } | TermKind::Variable(_) => true,
        TermKind::Injection { term, .. } => is_functional_pattern(term),
        TermKind::And(..) => false,
    }
}

fn contains_function_pattern(term: &Term) -> bool {
    match term.kind() {
        TermKind::Application {
            symbol, arguments, ..
        } => {
            matches!(symbol.attributes.symbol_type, SymbolType::Function(_))
                || arguments.iter().any(contains_function_pattern)
        }
        TermKind::Injection { term, .. } => contains_function_pattern(term),
        TermKind::And(left, right) => {
            contains_function_pattern(left) || contains_function_pattern(right)
        }
        TermKind::Map { .. } | TermKind::List { .. } | TermKind::Set { .. } => true,
        TermKind::DomainValue { .. } | TermKind::Variable(_) => false,
    }
}

struct RuleApplication {
    applied: AppliedRule,
    remainder: Predicate,
}

struct PartialRuleMatch {
    substitution: Substitution,
    conditions: Vec<Predicate>,
    remainder: Vec<(Term, Term)>,
}

#[derive(Clone, Copy)]
enum SplitSide {
    Pattern,
    Subject,
}

struct IteSplit {
    side: SplitSide,
    condition: Term,
    then_pair: (Term, Term),
    else_pair: (Term, Term),
}

struct EqualitySplit {
    side: SplitSide,
    value: bool,
    left: Term,
    right: Term,
}

struct BooleanSplit {
    side: SplitSide,
    expected: bool,
    operands: Vec<Term>,
}

struct MapNotInKeysSplit {
    side: SplitSide,
    symbol: Arc<Symbol>,
    sort_arguments: Vec<Sort>,
    key: Term,
    map: Term,
}

fn apply_rule(
    definition: &BackendDefinition,
    rule: &RewriteRule,
    pattern: &Pattern,
    fresh_counter: &mut u64,
    simplification_options: SimplificationOptions,
    solver: &dyn SmtSolver,
    assume_initial_defined: bool,
) -> RuleAttempt {
    apply_rule_with_match(
        definition,
        rule,
        pattern,
        fresh_counter,
        simplification_options,
        solver,
        assume_initial_defined,
        None,
    )
}

#[allow(clippy::too_many_arguments)]
fn apply_rule_with_match(
    definition: &BackendDefinition,
    rule: &RewriteRule,
    pattern: &Pattern,
    fresh_counter: &mut u64,
    simplification_options: SimplificationOptions,
    solver: &dyn SmtSolver,
    assume_initial_defined: bool,
    matched: Option<PartialRuleMatch>,
) -> RuleAttempt {
    let (matching, mut inherited_conditions) = if let Some(matched) = matched {
        let matching = if matched.remainder.is_empty() {
            MatchResult::Success(matched.substitution)
        } else {
            MatchResult::Indeterminate {
                substitution: matched.substitution,
                remainder: matched.remainder,
            }
        };
        (matching, matched.conditions)
    } else {
        (
            match_terms_in_definition(MatchMode::Rewrite, definition, &rule.lhs, &pattern.term),
            Vec::new(),
        )
    };
    let mut path_knowledge = pattern.constraints.clone();
    if assume_initial_defined {
        extend_unique(&mut path_knowledge, ceil_term(definition, &pattern.term));
    }
    let mut inherited_knowledge = path_knowledge.clone();
    extend_unique(
        &mut inherited_knowledge,
        inherited_conditions.iter().cloned(),
    );
    let (mut substitution, mut match_conditions) = match matching {
        MatchResult::Failed(_) => return RuleAttempt::NotApplicable,
        MatchResult::Indeterminate {
            substitution,
            remainder,
        } => {
            let recovered = match recover_indeterminate_match(
                definition,
                substitution,
                remainder,
                &inherited_knowledge,
                simplification_options,
                solver,
            ) {
                Ok(recovered) => recovered,
                Err(error) => {
                    return RuleAttempt::Indeterminate(IndeterminateReason::simplification(
                        Some(&rule.attributes.unique_id),
                        error,
                    ));
                }
            };
            extend_unique(
                &mut inherited_conditions,
                recovered.conditions.iter().cloned(),
            );
            extend_unique(&mut inherited_knowledge, recovered.conditions);
            match recovered.result {
                MatchResult::Failed(_) => return RuleAttempt::NotApplicable,
                MatchResult::Success(substitution) => (substitution, Vec::new()),
                MatchResult::Indeterminate {
                    substitution,
                    remainder,
                } => {
                    if let Some(matches) =
                        recover_boolean_matches(definition, substitution.clone(), &remainder)
                    {
                        return combine_rule_attempts(matches.into_iter().map(|mut matched| {
                            let mut conditions = inherited_conditions.clone();
                            conditions.append(&mut matched.conditions);
                            matched.conditions = conditions;
                            apply_rule_with_match(
                                definition,
                                rule,
                                pattern,
                                fresh_counter,
                                simplification_options,
                                solver,
                                assume_initial_defined,
                                Some(matched),
                            )
                        }));
                    }
                    if let Some(matches) = recover_symbolic_map_key_matches(
                        definition,
                        substitution.clone(),
                        &remainder,
                    ) {
                        return combine_rule_attempts(matches.into_iter().map(|mut matched| {
                            let mut conditions = inherited_conditions.clone();
                            conditions.append(&mut matched.conditions);
                            matched.conditions = conditions;
                            apply_rule_with_match(
                                definition,
                                rule,
                                pattern,
                                fresh_counter,
                                simplification_options,
                                solver,
                                assume_initial_defined,
                                Some(matched),
                            )
                        }));
                    }
                    if let Some(matches) = recover_map_not_in_keys_matches(
                        definition,
                        rule,
                        pattern,
                        substitution.clone(),
                        &remainder,
                        fresh_counter,
                    ) {
                        return combine_rule_attempts(matches.into_iter().map(|mut matched| {
                            let mut conditions = inherited_conditions.clone();
                            conditions.append(&mut matched.conditions);
                            matched.conditions = conditions;
                            apply_rule_with_match(
                                definition,
                                rule,
                                pattern,
                                fresh_counter,
                                simplification_options,
                                solver,
                                assume_initial_defined,
                                Some(matched),
                            )
                        }));
                    }
                    if let Some(matches) = recover_equality_matches(
                        definition,
                        rule,
                        pattern,
                        substitution.clone(),
                        &remainder,
                        fresh_counter,
                    ) {
                        return combine_rule_attempts(matches.into_iter().map(|mut matched| {
                            let mut conditions = inherited_conditions.clone();
                            conditions.append(&mut matched.conditions);
                            matched.conditions = conditions;
                            apply_rule_with_match(
                                definition,
                                rule,
                                pattern,
                                fresh_counter,
                                simplification_options,
                                solver,
                                assume_initial_defined,
                                Some(matched),
                            )
                        }));
                    }
                    if let Some(matches) =
                        recover_ite_matches(definition, substitution.clone(), &remainder)
                    {
                        return combine_rule_attempts(matches.into_iter().map(|mut matched| {
                            let mut conditions = inherited_conditions.clone();
                            conditions.append(&mut matched.conditions);
                            matched.conditions = conditions;
                            apply_rule_with_match(
                                definition,
                                rule,
                                pattern,
                                fresh_counter,
                                simplification_options,
                                solver,
                                assume_initial_defined,
                                Some(matched),
                            )
                        }));
                    }
                    if let Some(matches) = unify_collection_remainders_all_in_definition(
                        MatchMode::Rewrite,
                        definition,
                        substitution.clone(),
                        &remainder,
                    ) {
                        if matches.is_empty() {
                            return RuleAttempt::NotApplicable;
                        }
                        return combine_rule_attempts(matches.into_iter().map(|substitution| {
                            let (substitution, _) = freshen_unbound_rule_variables(
                                rule,
                                pattern,
                                substitution,
                                fresh_counter,
                            );
                            let mut conditions = inherited_conditions.clone();
                            extend_unique(
                                &mut conditions,
                                collection_unification_definedness(
                                    definition,
                                    &remainder,
                                    &substitution,
                                ),
                            );
                            apply_rule_with_match(
                                definition,
                                rule,
                                pattern,
                                fresh_counter,
                                simplification_options,
                                solver,
                                assume_initial_defined,
                                Some(PartialRuleMatch {
                                    substitution,
                                    conditions,
                                    remainder: Vec::new(),
                                }),
                            )
                        }));
                    }
                    if let Some(recovered) = recover_overload_symbolic_match(
                        definition,
                        pattern,
                        substitution.clone(),
                        &remainder,
                        fresh_counter,
                    ) {
                        recovered
                    } else if remainder.iter().any(|(left, right)| {
                        !left.attributes().can_be_evaluated || !right.attributes().can_be_evaluated
                    }) {
                        // A `no-evaluators` function cannot become rigid after another
                        // simplification pass. Turning this remainder into an equality
                        // constraint would falsely make the rule applicable and can rewrite
                        // the same state forever. Booster reports the match as indeterminate.
                        return RuleAttempt::Indeterminate(IndeterminateReason::Match {
                            rule_id: rule.attributes.unique_id.clone(),
                            substitution,
                            remainder,
                        });
                    } else {
                        match recover_general_unification(
                            definition,
                            rule,
                            pattern,
                            substitution.clone(),
                            &remainder,
                            fresh_counter,
                        ) {
                            GeneralUnificationRecovery::Unified(mut solutions) => {
                                if solutions.len() == 1 {
                                    solutions.pop().expect("one unification solution")
                                } else {
                                    return combine_rule_attempts(solutions.into_iter().map(
                                        |(substitution, mut constraints)| {
                                            let mut conditions = inherited_conditions.clone();
                                            conditions.append(&mut constraints);
                                            apply_rule_with_match(
                                                definition,
                                                rule,
                                                pattern,
                                                fresh_counter,
                                                simplification_options,
                                                solver,
                                                assume_initial_defined,
                                                Some(PartialRuleMatch {
                                                    substitution,
                                                    conditions,
                                                    remainder: Vec::new(),
                                                }),
                                            )
                                        },
                                    ));
                                }
                            }
                            GeneralUnificationRecovery::Bottom => {
                                return RuleAttempt::NotApplicable;
                            }
                            GeneralUnificationRecovery::Unsupported => {
                                if let Some(recovered) = recover_functional_symbolic_match(
                                    definition,
                                    rule,
                                    pattern,
                                    substitution.clone(),
                                    &remainder,
                                    fresh_counter,
                                ) {
                                    recovered
                                } else if let Some(recovered) = recover_function_equality_match(
                                    rule,
                                    pattern,
                                    substitution.clone(),
                                    &remainder,
                                    fresh_counter,
                                ) {
                                    recovered
                                } else {
                                    let requires =
                                        substitute_predicates(&rule.requires, &substitution);
                                    let requires = match simplify_predicates_with_solver(
                                        definition,
                                        &requires,
                                        &inherited_knowledge,
                                        simplification_options,
                                        solver,
                                    ) {
                                        Ok(requires) => requires,
                                        Err(error) => {
                                            return RuleAttempt::Indeterminate(
                                                IndeterminateReason::simplification(
                                                    Some(&rule.attributes.unique_id),
                                                    error,
                                                ),
                                            );
                                        }
                                    };
                                    if predicates_truth(&requires) == Truth::False {
                                        return RuleAttempt::NotApplicable;
                                    }
                                    let unclear = requires
                                        .into_iter()
                                        .filter(|predicate| {
                                            predicates_truth(std::slice::from_ref(predicate))
                                                == Truth::Unknown
                                                && !inherited_knowledge.contains(predicate)
                                        })
                                        .collect::<Vec<_>>();
                                    if !unclear.is_empty()
                                        && matches!(
                                            solver.check_predicates(
                                                &inherited_knowledge,
                                                &Substitution::new(),
                                                &unclear,
                                            ),
                                            Ok(Validity::Invalid)
                                        )
                                    {
                                        return RuleAttempt::NotApplicable;
                                    }
                                    return RuleAttempt::Indeterminate(
                                        IndeterminateReason::Match {
                                            rule_id: rule.attributes.unique_id.clone(),
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
        MatchResult::Success(substitution) => (substitution, Vec::new()),
    };
    let configuration_bindings = substitution
        .iter()
        .filter(|(variable, _)| !rule.lhs.attributes().variables.contains(*variable))
        .map(|(variable, value)| {
            (
                variable.clone(),
                value.clone(),
                Predicate::Equals(Term::variable(variable.clone()), value.clone()),
            )
        })
        .collect::<Vec<_>>();
    for (variable, value, condition) in configuration_bindings {
        substitution.remove(&variable);
        if !match_conditions.contains(&condition) {
            match_conditions.push(condition);
        }
        extend_unique(&mut match_conditions, ceil_term(definition, &value));
    }
    inherited_conditions.append(&mut match_conditions);
    let inherited_conditions = match simplify_predicates_with_solver(
        definition,
        &inherited_conditions,
        &path_knowledge,
        simplification_options,
        solver,
    ) {
        Ok(conditions) => conditions,
        Err(error) => {
            return RuleAttempt::Indeterminate(IndeterminateReason::simplification(
                Some(&rule.attributes.unique_id),
                error,
            ));
        }
    };
    if predicates_truth(&inherited_conditions) == Truth::False {
        return RuleAttempt::NotApplicable;
    }
    let mut match_conditions = inherited_conditions
        .into_iter()
        .filter(|condition| predicates_truth(std::slice::from_ref(condition)) == Truth::Unknown)
        .collect::<Vec<_>>();

    let mut definedness_conditions = Vec::new();
    for value in substitution
        .values()
        .filter(|value| !matches!(value.kind(), TermKind::Variable(_)))
    {
        extend_unique(&mut definedness_conditions, ceil_term(definition, value));
    }
    let mut definedness_knowledge = path_knowledge.clone();
    extend_unique(&mut definedness_knowledge, match_conditions.iter().cloned());
    let definedness_conditions = match simplify_predicates_with_solver(
        definition,
        &definedness_conditions,
        &definedness_knowledge,
        simplification_options,
        solver,
    ) {
        Ok(conditions) => conditions,
        Err(error) => {
            return RuleAttempt::Indeterminate(IndeterminateReason::simplification(
                Some(&rule.attributes.unique_id),
                error,
            ));
        }
    };
    if predicates_truth(&definedness_conditions) == Truth::False {
        return RuleAttempt::Trivial;
    }
    extend_unique(
        &mut match_conditions,
        definedness_conditions.into_iter().filter(|condition| {
            predicates_truth(std::slice::from_ref(condition)) == Truth::Unknown
        }),
    );

    if !match_conditions.is_empty() {
        let mut narrowed = pattern.constraints.clone();
        extend_unique(&mut narrowed, match_conditions.iter().cloned());
        match solver.is_sat(&narrowed, &Substitution::new()) {
            Ok(Satisfiability::Sat) => {}
            Ok(Satisfiability::Unsat) => return RuleAttempt::NotApplicable,
            Ok(Satisfiability::Unknown(reason)) => {
                return RuleAttempt::Indeterminate(IndeterminateReason::Smt {
                    rule_id: rule.attributes.unique_id.clone(),
                    error: SmtError::Unknown(reason),
                });
            }
            Err(error) => {
                return RuleAttempt::Indeterminate(IndeterminateReason::Smt {
                    rule_id: rule.attributes.unique_id.clone(),
                    error,
                });
            }
        }
    }

    if let Some(variable) = check_concreteness(rule, &substitution) {
        return RuleAttempt::Indeterminate(IndeterminateReason::Concreteness {
            rule_id: rule.attributes.unique_id.clone(),
            variable,
        });
    }
    let requires = substitute_predicates(&rule.requires, &substitution);
    let mut match_knowledge = path_knowledge;
    extend_unique(&mut match_knowledge, match_conditions.iter().cloned());
    let requires = match simplify_predicates_with_solver(
        definition,
        &requires,
        &match_knowledge,
        simplification_options,
        solver,
    ) {
        Ok(requires) => requires,
        Err(error) => {
            return RuleAttempt::Indeterminate(IndeterminateReason::simplification(
                Some(&rule.attributes.unique_id),
                error,
            ));
        }
    };
    if predicates_truth(&requires) == Truth::False {
        return RuleAttempt::NotApplicable;
    }
    let mut unclear_requires = requires
        .into_iter()
        .filter(|predicate| {
            predicates_truth(std::slice::from_ref(predicate)) == Truth::Unknown
                && !pattern.constraints.contains(predicate)
        })
        .collect::<Vec<_>>();
    if !unclear_requires.is_empty() {
        match solver.check_predicates(&match_knowledge, &Substitution::new(), &unclear_requires) {
            Ok(Validity::Valid) => unclear_requires.clear(),
            Ok(Validity::Invalid) => return RuleAttempt::NotApplicable,
            Ok(Validity::Indeterminate) => {}
            Err(SmtError::Unavailable) => {
                return RuleAttempt::Indeterminate(IndeterminateReason::Requires {
                    rule_id: rule.attributes.unique_id.clone(),
                    predicates: unclear_requires,
                });
            }
            Ok(Validity::InconsistentGroundTruth) => {
                return RuleAttempt::Indeterminate(IndeterminateReason::Smt {
                    rule_id: rule.attributes.unique_id.clone(),
                    error: SmtError::InconsistentGroundTruth,
                });
            }
            Ok(Validity::Unknown(reason)) => {
                return RuleAttempt::Indeterminate(IndeterminateReason::Smt {
                    rule_id: rule.attributes.unique_id.clone(),
                    error: SmtError::Unknown(reason),
                });
            }
            Err(error) => {
                return RuleAttempt::Indeterminate(IndeterminateReason::Smt {
                    rule_id: rule.attributes.unique_id.clone(),
                    error,
                });
            }
        }
    }

    let mut applicability = match_conditions.clone();
    applicability.extend(unclear_requires.iter().cloned());
    let applicability = quantify_introduced_variables(pattern, applicability);
    if applicability != Predicate::True
        && conjunctively_contains_alpha_equivalent(
            &pattern.constraints,
            &Predicate::Not(Box::new(applicability.clone())),
        )
    {
        return RuleAttempt::NotApplicable;
    }

    let rhs = match &rule.rhs {
        RuleRhs::Term(rhs) => rhs,
        RuleRhs::Bottom => return RuleAttempt::Trivial,
        RuleRhs::Predicates(_) => return RuleAttempt::NotApplicable,
    };
    let existential_substitution = freshen_existentials(rule, pattern);
    let rhs = substitute(&substitute(rhs, &substitution), &existential_substitution);
    let mut condition_knowledge = match_knowledge;
    extend_unique(&mut condition_knowledge, unclear_requires.iter().cloned());
    let (rhs, mut rhs_constraints, effects) =
        if rule.computed_attributes.undefined_symbols.is_empty() {
            (rhs, Vec::new(), Vec::new())
        } else {
            match simplify_with_solver(
                definition,
                &rhs,
                &condition_knowledge,
                simplification_options,
                solver,
            ) {
                Ok(simplified) => (simplified.term, simplified.constraints, simplified.effects),
                Err(error) => {
                    return RuleAttempt::Indeterminate(IndeterminateReason::simplification(
                        Some(&rule.attributes.unique_id),
                        error,
                    ));
                }
            }
        };
    extend_unique(&mut condition_knowledge, rhs_constraints.iter().cloned());
    if !rule.computed_attributes.undefined_symbols.is_empty() {
        let obligations = ceil_term(definition, &rhs);
        let obligations = match simplify_predicates_with_solver(
            definition,
            &obligations,
            &condition_knowledge,
            simplification_options,
            solver,
        ) {
            Ok(obligations) => obligations,
            Err(error) => {
                return RuleAttempt::Indeterminate(IndeterminateReason::simplification(
                    Some(&rule.attributes.unique_id),
                    error,
                ));
            }
        };
        match predicates_truth(&obligations) {
            Truth::True => {}
            Truth::False => return RuleAttempt::Trivial,
            Truth::Unknown => match solver.check_predicates(
                &condition_knowledge,
                &Substitution::new(),
                &obligations,
            ) {
                Ok(Validity::Valid) => {}
                Ok(Validity::Invalid | Validity::InconsistentGroundTruth) => {
                    return RuleAttempt::Trivial;
                }
                Ok(Validity::Indeterminate | Validity::Unknown(_)) | Err(_) => {
                    extend_unique(&mut rhs_constraints, obligations);
                }
            },
        }
    }
    let ensures = substitute_predicates(
        &substitute_predicates(&rule.ensures, &substitution),
        &existential_substitution,
    );
    let mut ensures = match simplify_predicates_with_solver(
        definition,
        &ensures,
        &condition_knowledge,
        simplification_options,
        solver,
    ) {
        Ok(ensures) => ensures,
        Err(error) => {
            return RuleAttempt::Indeterminate(IndeterminateReason::simplification(
                Some(&rule.attributes.unique_id),
                error,
            ));
        }
    };
    match predicates_truth(&ensures) {
        Truth::False => return RuleAttempt::Trivial,
        Truth::True => {}
        Truth::Unknown => {
            match solver.check_predicates(&condition_knowledge, &Substitution::new(), &ensures) {
                Ok(Validity::Invalid | Validity::InconsistentGroundTruth) => {
                    return RuleAttempt::Trivial;
                }
                Ok(Validity::Valid) => ensures.clear(),
                Ok(Validity::Indeterminate) | Err(SmtError::Unavailable) => {}
                Ok(Validity::Unknown(reason)) => {
                    return RuleAttempt::Indeterminate(IndeterminateReason::Smt {
                        rule_id: rule.attributes.unique_id.clone(),
                        error: SmtError::Unknown(reason),
                    });
                }
                Err(error) => {
                    return RuleAttempt::Indeterminate(IndeterminateReason::Smt {
                        rule_id: rule.attributes.unique_id.clone(),
                        error,
                    });
                }
            }
        }
    }
    let alias_variables = term_alias_variables(&rule.lhs);
    let rule_substitution = substitution
        .iter()
        .filter(|(variable, _)| !alias_variables.contains(*variable))
        .map(|(variable, value)| (variable.clone(), value.clone()))
        .collect();
    let mut rule_predicates = Vec::new();
    extend_unique(&mut rule_predicates, match_conditions.iter().cloned());
    extend_unique(&mut rule_predicates, unclear_requires.iter().cloned());
    extend_unique(&mut rule_predicates, rhs_constraints);
    extend_unique(&mut rule_predicates, ensures);
    let mut constraints = pattern.constraints.clone();
    extend_unique(&mut constraints, rule_predicates.iter().cloned());
    let remainder = if applicability == Predicate::True {
        Predicate::False
    } else {
        Predicate::Not(Box::new(applicability))
    };
    RuleAttempt::Applied(vec![RuleApplication {
        applied: AppliedRule {
            before: pattern.clone(),
            pattern: Pattern {
                term: rhs,
                constraints,
            },
            label: rule.attributes.label.clone(),
            unique_id: rule.attributes.unique_id.clone(),
            substitution,
            rule_substitution,
            rule_predicates,
            effects,
        },
        remainder,
    }])
}

fn term_alias_variables(term: &Term) -> BTreeSet<Variable> {
    fn collect(term: &Term, output: &mut BTreeSet<Variable>) {
        match term.kind() {
            TermKind::And(left, right) => {
                if let TermKind::Variable(variable) = left.kind() {
                    output.insert(variable.clone());
                }
                if let TermKind::Variable(variable) = right.kind() {
                    output.insert(variable.clone());
                }
                collect(left, output);
                collect(right, output);
            }
            TermKind::Application { arguments, .. } => {
                for argument in arguments {
                    collect(argument, output);
                }
            }
            TermKind::Injection { term, .. } => collect(term, output),
            TermKind::Map { entries, rest, .. } => {
                for (key, value) in entries {
                    collect(key, output);
                    collect(value, output);
                }
                if let Some(rest) = rest {
                    collect(rest, output);
                }
            }
            TermKind::List { heads, rest, .. } => {
                for head in heads {
                    collect(head, output);
                }
                if let Some((middle, tails)) = rest {
                    collect(middle, output);
                    for tail in tails {
                        collect(tail, output);
                    }
                }
            }
            TermKind::Set { elements, rest, .. } => {
                for element in elements {
                    collect(element, output);
                }
                if let Some(rest) = rest {
                    collect(rest, output);
                }
            }
            TermKind::DomainValue { .. } | TermKind::Variable(_) => {}
        }
    }

    let mut variables = BTreeSet::new();
    collect(term, &mut variables);
    variables
}

/// Narrow a concrete rule-map key against symbolic keys in a closed configuration map.
///
/// Booster leaves this shape for Kore's unifier. Each possible key selection becomes an applied
/// branch guarded by equality; ordinary rule remainder construction preserves the complementary
/// disequalities on the original configuration.
fn recover_symbolic_map_key_matches(
    definition: &BackendDefinition,
    substitution: Substitution,
    remainder: &[(Term, Term)],
) -> Option<Vec<PartialRuleMatch>> {
    let protected_variables = substitution
        .values()
        .flat_map(|term| term.attributes().variables.iter().cloned())
        .collect::<BTreeSet<_>>();
    let (pair_index, map_definition, pattern_entries, pattern_rest, subject_entries) = remainder
        .iter()
        .enumerate()
        .find_map(|(index, (pattern, subject))| {
            let pattern = substitute(pattern, &substitution);
            let subject = substitute(subject, &substitution);
            let (
                TermKind::Map {
                    definition: pattern_definition,
                    entries: pattern_entries,
                    rest: Some(pattern_rest),
                },
                TermKind::Map {
                    definition: subject_definition,
                    entries: subject_entries,
                    rest: None,
                },
            ) = (pattern.kind(), subject.kind())
            else {
                return None;
            };
            if pattern_definition != subject_definition
                || pattern_entries.is_empty()
                || !pattern_entries.iter().all(|(key, _)| {
                    key.attributes().constructor_like
                        || (!key.attributes().variables.is_empty()
                            && key
                                .attributes()
                                .variables
                                .iter()
                                .all(|variable| protected_variables.contains(variable)))
                })
                || !matches!(pattern_rest.kind(), TermKind::Variable(variable)
                    if !protected_variables.contains(variable))
                || pattern_entries.len()
                    > subject_entries
                        .iter()
                        .filter(|(key, _)| matches!(key.kind(), TermKind::Variable(_)))
                        .count()
            {
                return None;
            }
            Some((
                index,
                pattern_definition.clone(),
                pattern_entries.clone(),
                pattern_rest.clone(),
                subject_entries.clone(),
            ))
        })?;
    let branch_remainder = remainder
        .iter()
        .enumerate()
        .filter(|(index, _)| *index != pair_index)
        .map(|(_, pair)| pair.clone())
        .collect::<Vec<_>>();
    let mut matches = Vec::new();
    search_symbolic_map_key_matches(
        definition,
        &map_definition,
        &pattern_entries,
        &pattern_rest,
        0,
        subject_entries,
        substitution,
        Vec::new(),
        branch_remainder,
        &mut matches,
    );
    Some(matches)
}

#[allow(clippy::too_many_arguments)]
fn search_symbolic_map_key_matches(
    definition: &BackendDefinition,
    map_definition: &Arc<crate::term::MapDefinition>,
    pattern_entries: &[(Term, Term)],
    pattern_rest: &Term,
    index: usize,
    remaining_subject: Vec<(Term, Term)>,
    substitution: Substitution,
    conditions: Vec<Predicate>,
    unresolved: Vec<(Term, Term)>,
    matches: &mut Vec<PartialRuleMatch>,
) {
    if index == pattern_entries.len() {
        let rest = substitute(pattern_rest, &substitution);
        let subject_rest = Term::map(map_definition.clone(), remaining_subject, None);
        let (substitution, unresolved) =
            match match_terms_in_definition(MatchMode::Rewrite, definition, &rest, &subject_rest) {
                MatchResult::Failed(_) => return,
                MatchResult::Success(found) => (compose(&found, &substitution), unresolved),
                MatchResult::Indeterminate {
                    substitution: found,
                    remainder,
                } => {
                    let mut unresolved = unresolved;
                    unresolved.extend(remainder);
                    (compose(&found, &substitution), unresolved)
                }
            };
        matches.push(PartialRuleMatch {
            substitution,
            conditions,
            remainder: unresolved,
        });
        return;
    }

    let (pattern_key, pattern_value) = &pattern_entries[index];
    let pattern_key = substitute(pattern_key, &substitution);
    for subject_index in 0..remaining_subject.len() {
        let (subject_key, subject_value) = &remaining_subject[subject_index];
        if !matches!(subject_key.kind(), TermKind::Variable(_)) {
            continue;
        }
        let condition = Predicate::Equals(subject_key.clone(), pattern_key.clone());
        if predicates_truth(std::slice::from_ref(&condition)) == Truth::False {
            continue;
        }
        let pattern_value = substitute(pattern_value, &substitution);
        let (next_substitution, next_unresolved) = match match_terms_in_definition(
            MatchMode::Rewrite,
            definition,
            &pattern_value,
            subject_value,
        ) {
            MatchResult::Failed(_) => continue,
            MatchResult::Success(found) => (compose(&found, &substitution), unresolved.clone()),
            MatchResult::Indeterminate {
                substitution: found,
                remainder,
            } => {
                let mut next_unresolved = unresolved.clone();
                next_unresolved.extend(remainder);
                (compose(&found, &substitution), next_unresolved)
            }
        };
        let mut next_conditions = conditions.clone();
        if predicates_truth(std::slice::from_ref(&condition)) == Truth::Unknown
            && !next_conditions.contains(&condition)
        {
            next_conditions.push(condition);
        }
        let mut next_subject = remaining_subject.clone();
        next_subject.remove(subject_index);
        search_symbolic_map_key_matches(
            definition,
            map_definition,
            pattern_entries,
            pattern_rest,
            index + 1,
            next_subject,
            next_substitution,
            next_conditions,
            next_unresolved,
            matches,
        );
    }
}

/// Decompose the Boolean unification cases used by the pinned backend: conjunction with `true`,
/// disjunction with `false`, and negation with either Boolean value.
fn recover_boolean_matches(
    definition: &BackendDefinition,
    mut substitution: Substitution,
    remainder: &[(Term, Term)],
) -> Option<Vec<PartialRuleMatch>> {
    let (index, split) = remainder
        .iter()
        .enumerate()
        .find_map(|(index, (left, right))| {
            let left = substitute(left, &substitution);
            let right = substitute(right, &substitution);
            split_boolean_pair(&left, &right).map(|split| (index, split))
        })?;
    let mut branch_remainder = remainder
        .iter()
        .enumerate()
        .filter(|(candidate, _)| *candidate != index)
        .map(|(_, pair)| pair.clone())
        .collect::<Vec<_>>();
    let expected = Term::domain_value(
        Sort::simple("SortBool"),
        if split.expected { "true" } else { "false" },
    );

    if matches!(split.side, SplitSide::Pattern) {
        for operand in split.operands {
            let operand = substitute(&operand, &substitution);
            match match_terms_in_definition(MatchMode::Implies, definition, &operand, &expected) {
                MatchResult::Failed(_) => return Some(Vec::new()),
                MatchResult::Success(found) => {
                    substitution = compose(&found, &substitution);
                }
                MatchResult::Indeterminate {
                    substitution: found,
                    remainder,
                } => {
                    substitution = compose(&found, &substitution);
                    branch_remainder.extend(remainder);
                }
            }
        }
        return Some(vec![PartialRuleMatch {
            substitution,
            conditions: Vec::new(),
            remainder: branch_remainder,
        }]);
    }

    let mut conditions = Vec::new();
    for operand in split.operands {
        let condition = Predicate::Equals(operand, expected.clone());
        match predicates_truth(std::slice::from_ref(&condition)) {
            Truth::False => return Some(Vec::new()),
            Truth::True => {}
            Truth::Unknown => conditions.push(condition),
        }
    }
    Some(vec![PartialRuleMatch {
        substitution,
        conditions,
        remainder: branch_remainder,
    }])
}

fn split_boolean_pair(left: &Term, right: &Term) -> Option<BooleanSplit> {
    if let Some(value) = bool_domain_value(right)
        && let Some((expected, operands)) = boolean_operands(left, value)
    {
        return Some(BooleanSplit {
            side: SplitSide::Pattern,
            expected,
            operands,
        });
    }
    let value = bool_domain_value(left)?;
    let (expected, operands) = boolean_operands(right, value)?;
    Some(BooleanSplit {
        side: SplitSide::Subject,
        expected,
        operands,
    })
}

fn boolean_operands(term: &Term, value: bool) -> Option<(bool, Vec<Term>)> {
    let TermKind::Application {
        symbol, arguments, ..
    } = term.kind()
    else {
        return None;
    };
    match (
        symbol.attributes.hook.as_deref(),
        value,
        arguments.as_slice(),
    ) {
        (Some("BOOL.and"), true, [left, right]) => Some((true, vec![left.clone(), right.clone()])),
        (Some("BOOL.or"), false, [left, right]) => Some((false, vec![left.clone(), right.clone()])),
        (Some("BOOL.not"), value, [operand]) => Some((!value, vec![operand.clone()])),
        _ => None,
    }
}

/// Decompose `MAP.in_keys(key, map) = false` over the known entries of a normalized map.
fn recover_map_not_in_keys_matches(
    definition: &BackendDefinition,
    rule: &RewriteRule,
    pattern: &Pattern,
    substitution: Substitution,
    remainder: &[(Term, Term)],
    fresh_counter: &mut u64,
) -> Option<Vec<PartialRuleMatch>> {
    let (index, split) = remainder
        .iter()
        .enumerate()
        .find_map(|(index, (left, right))| {
            let left = substitute(left, &substitution);
            let right = substitute(right, &substitution);
            split_map_not_in_keys_pair(&left, &right).map(|split| (index, split))
        })?;
    let substitution = if matches!(split.side, SplitSide::Pattern) {
        freshen_unbound_rule_variables(rule, pattern, substitution, fresh_counter).0
    } else {
        substitution
    };
    let key = substitute(&split.key, &substitution);
    let map = substitute(&split.map, &substitution);
    let TermKind::Map { entries, rest, .. } = map.kind() else {
        return None;
    };
    if entries.is_empty() && rest.is_some() {
        return None;
    }

    let untouched = remainder
        .iter()
        .enumerate()
        .filter(|(candidate, _)| *candidate != index)
        .map(|(_, pair)| pair.clone())
        .collect::<Vec<_>>();
    if entries.is_empty() {
        return Some(vec![PartialRuleMatch {
            substitution,
            conditions: Vec::new(),
            remainder: untouched,
        }]);
    }

    let mut conditions = ceil_term(definition, &key);
    extend_unique(&mut conditions, ceil_term(definition, &map));
    for (map_key, _) in entries {
        extend_unique(
            &mut conditions,
            [Predicate::Not(Box::new(Predicate::Equals(
                key.clone(),
                map_key.clone(),
            )))],
        );
    }
    if let Some(rest) = rest {
        let membership =
            Term::application(split.symbol, split.sort_arguments, vec![key, rest.clone()]);
        extend_unique(
            &mut conditions,
            [Predicate::Equals(
                membership,
                Term::domain_value(Sort::simple("SortBool"), "false"),
            )],
        );
    }
    conditions.retain(|condition| {
        !matches!(
            predicates_truth(std::slice::from_ref(condition)),
            Truth::True
        )
    });
    if matches!(predicates_truth(&conditions), Truth::False) {
        return Some(Vec::new());
    }
    Some(vec![PartialRuleMatch {
        substitution,
        conditions,
        remainder: untouched,
    }])
}

fn split_map_not_in_keys_pair(left: &Term, right: &Term) -> Option<MapNotInKeysSplit> {
    if bool_domain_value(right) == Some(false)
        && let Some((symbol, sort_arguments, key, map)) = map_in_keys_arguments(left)
    {
        return Some(MapNotInKeysSplit {
            side: SplitSide::Pattern,
            symbol,
            sort_arguments,
            key,
            map,
        });
    }
    if bool_domain_value(left) != Some(false) {
        return None;
    }
    let (symbol, sort_arguments, key, map) = map_in_keys_arguments(right)?;
    Some(MapNotInKeysSplit {
        side: SplitSide::Subject,
        symbol,
        sort_arguments,
        key,
        map,
    })
}

fn map_in_keys_arguments(term: &Term) -> Option<(Arc<Symbol>, Vec<Sort>, Term, Term)> {
    let TermKind::Application {
        symbol,
        sort_arguments,
        arguments,
    } = term.kind()
    else {
        return None;
    };
    if symbol.attributes.hook.as_deref() != Some("MAP.in_keys") {
        return None;
    }
    let [key, map] = arguments.as_slice() else {
        return None;
    };
    Some((
        symbol.clone(),
        sort_arguments.clone(),
        key.clone(),
        map.clone(),
    ))
}

/// Normalize unification of a hooked equality application with a Boolean domain value.
///
/// The true case delegates to ordinary unification of the operands so useful substitutions are
/// retained. The false case is the complement of operand equality and therefore remains a path
/// condition. This is the same normalization used by the pinned backend's `unifyEq` hook.
fn recover_equality_matches(
    definition: &BackendDefinition,
    rule: &RewriteRule,
    pattern: &Pattern,
    substitution: Substitution,
    remainder: &[(Term, Term)],
    fresh_counter: &mut u64,
) -> Option<Vec<PartialRuleMatch>> {
    let (index, split) = remainder
        .iter()
        .enumerate()
        .find_map(|(index, (left, right))| {
            let left = substitute(left, &substitution);
            let right = substitute(right, &substitution);
            split_equality_pair(&left, &right).map(|split| (index, split))
        })?;
    let mut untouched = remainder
        .iter()
        .enumerate()
        .filter(|(candidate, _)| *candidate != index)
        .map(|(_, pair)| pair.clone())
        .collect::<Vec<_>>();

    if split.value && matches!(split.side, SplitSide::Pattern) {
        return Some(
            match match_terms_in_definition(
                MatchMode::Implies,
                definition,
                &split.left,
                &split.right,
            ) {
                MatchResult::Failed(_) => Vec::new(),
                MatchResult::Success(found) => vec![PartialRuleMatch {
                    substitution: compose(&found, &substitution),
                    conditions: Vec::new(),
                    remainder: untouched,
                }],
                MatchResult::Indeterminate {
                    substitution: found,
                    remainder,
                } => {
                    untouched.extend(remainder);
                    vec![PartialRuleMatch {
                        substitution: compose(&found, &substitution),
                        conditions: Vec::new(),
                        remainder: untouched,
                    }]
                }
            },
        );
    }

    let substitution = if matches!(split.side, SplitSide::Pattern) {
        freshen_unbound_rule_variables(rule, pattern, substitution, fresh_counter).0
    } else {
        substitution
    };
    let left = substitute(&split.left, &substitution);
    let right = substitute(&split.right, &substitution);
    let equality = Predicate::Equals(left, right);
    let condition = if split.value {
        equality
    } else {
        Predicate::Not(Box::new(equality))
    };
    let conditions = match predicates_truth(std::slice::from_ref(&condition)) {
        Truth::False => return Some(Vec::new()),
        Truth::True => Vec::new(),
        Truth::Unknown => vec![condition],
    };
    Some(vec![PartialRuleMatch {
        substitution,
        conditions,
        remainder: untouched,
    }])
}

fn split_equality_pair(left: &Term, right: &Term) -> Option<EqualitySplit> {
    if let Some((operand1, operand2)) = equality_arguments(left)
        && let Some(value) = bool_domain_value(right)
    {
        return Some(EqualitySplit {
            side: SplitSide::Pattern,
            value,
            left: operand1,
            right: operand2,
        });
    }
    let (operand1, operand2) = equality_arguments(right)?;
    Some(EqualitySplit {
        side: SplitSide::Subject,
        value: bool_domain_value(left)?,
        left: operand1,
        right: operand2,
    })
}

fn equality_arguments(term: &Term) -> Option<(Term, Term)> {
    let TermKind::Application {
        symbol, arguments, ..
    } = term.kind()
    else {
        return None;
    };
    if !matches!(
        symbol.attributes.hook.as_deref(),
        Some("INT.eq" | "STRING.eq" | "KEQUAL.eq")
    ) || !is_functional_pattern(term)
    {
        return None;
    }
    let [left, right] = arguments.as_slice() else {
        return None;
    };
    Some((left.clone(), right.clone()))
}

fn bool_domain_value(term: &Term) -> Option<bool> {
    let TermKind::DomainValue { sort, value } = term.kind() else {
        return None;
    };
    if sort != &Sort::simple("SortBool") {
        return None;
    }
    match value.as_ref() {
        "true" => Some(true),
        "false" => Some(false),
        _ => None,
    }
}

/// Split symbolic `KEQUAL.ite` applications at the unification boundary.
///
/// Concrete conditions are handled by the builtin evaluator. When the condition remains
/// symbolic, each ITE branch is matched independently and guarded by the Boolean value which
/// selects it. This mirrors the pinned backend's `unifyIfThenElse` behavior without teaching the
/// syntax-directed matcher about branching.
fn recover_ite_matches(
    definition: &BackendDefinition,
    substitution: Substitution,
    remainder: &[(Term, Term)],
) -> Option<Vec<PartialRuleMatch>> {
    let (index, side, condition, then_pair, else_pair) =
        remainder
            .iter()
            .enumerate()
            .find_map(|(index, (pattern, subject))| {
                let pattern = substitute(pattern, &substitution);
                let subject = substitute(subject, &substitution);
                split_ite_pair(&pattern, &subject).map(
                    |IteSplit {
                         side,
                         condition,
                         then_pair,
                         else_pair,
                     }| { (index, side, condition, then_pair, else_pair) },
                )
            })?;
    let untouched = remainder
        .iter()
        .enumerate()
        .filter(|(candidate, _)| *candidate != index)
        .map(|(_, pair)| pair.clone())
        .collect::<Vec<_>>();

    let mut recovered = Vec::new();
    for (value, (pattern, subject)) in [(true, then_pair), (false, else_pair)] {
        let matched = match_terms_in_definition(MatchMode::Rewrite, definition, &pattern, &subject);
        let (found, mut branch_remainder) = match matched {
            MatchResult::Failed(_) => continue,
            MatchResult::Success(found) => (found, Vec::new()),
            MatchResult::Indeterminate {
                substitution,
                remainder,
            } => (substitution, remainder),
        };
        let mut substitution = compose(&found, &substitution);
        branch_remainder.extend(untouched.iter().cloned());
        let value = Term::domain_value(
            Sort::simple("SortBool"),
            if value { "true" } else { "false" },
        );
        let mut condition = substitute(&condition, &substitution);
        let mut conditions = Vec::new();
        if matches!(side, SplitSide::Pattern) {
            match match_terms_in_definition(MatchMode::Rewrite, definition, &condition, &value) {
                MatchResult::Failed(_) => continue,
                MatchResult::Success(found) => {
                    substitution = compose(&found, &substitution);
                }
                MatchResult::Indeterminate {
                    substitution: found,
                    remainder,
                } => {
                    substitution = compose(&found, &substitution);
                    branch_remainder.extend(remainder);
                    condition = substitute(&condition, &substitution);
                    conditions.push(Predicate::Equals(condition, value));
                }
            }
        } else {
            conditions.push(Predicate::Equals(condition, value));
        }
        recovered.push(PartialRuleMatch {
            substitution,
            conditions,
            remainder: branch_remainder,
        });
    }
    Some(recovered)
}

fn split_ite_pair(pattern: &Term, subject: &Term) -> Option<IteSplit> {
    if let Some((condition, then_branch, else_branch)) = ite_arguments(pattern) {
        return Some(IteSplit {
            side: SplitSide::Pattern,
            condition,
            then_pair: (then_branch, subject.clone()),
            else_pair: (else_branch, subject.clone()),
        });
    }
    let (condition, then_branch, else_branch) = ite_arguments(subject)?;
    Some(IteSplit {
        side: SplitSide::Subject,
        condition,
        then_pair: (pattern.clone(), then_branch),
        else_pair: (pattern.clone(), else_branch),
    })
}

fn ite_arguments(term: &Term) -> Option<(Term, Term, Term)> {
    let TermKind::Application {
        symbol, arguments, ..
    } = term.kind()
    else {
        return None;
    };
    if symbol.attributes.hook.as_deref() != Some("KEQUAL.ite") {
        return None;
    }
    let [condition, then_branch, else_branch] = arguments.as_slice() else {
        return None;
    };
    Some((condition.clone(), then_branch.clone(), else_branch.clone()))
}

fn recover_overload_symbolic_match(
    definition: &BackendDefinition,
    state: &Pattern,
    substitution: Substitution,
    remainder: &[(Term, Term)],
    fresh_counter: &mut u64,
) -> Option<(Substitution, Vec<Predicate>)> {
    let [(rule_term, configuration_term)] = remainder else {
        return None;
    };
    let rule_term = substitute(rule_term, &substitution);
    let configuration_term = substitute(configuration_term, &substitution);
    let rule_application = match rule_term.kind() {
        TermKind::Application { .. } => &rule_term,
        TermKind::Injection { term, .. } => term,
        _ => return None,
    };
    let TermKind::Application {
        symbol: rule_symbol,
        ..
    } = rule_application.kind()
    else {
        return None;
    };
    let TermKind::Injection {
        target,
        term: configuration_inner,
        ..
    } = configuration_term.kind()
    else {
        return None;
    };
    let TermKind::Variable(configuration_variable) = configuration_inner.kind() else {
        return None;
    };

    let mut candidates = definition
        .overloads
        .overloaded_by(&rule_symbol.name)
        .into_iter()
        .filter_map(|name| definition.symbols.get(&name).cloned())
        .filter(|symbol| {
            symbol.sort_variables.is_empty()
                && symbol.attributes.symbol_type == SymbolType::Constructor
                && definition
                    .sort_graph
                    .check_subsort(&symbol.result_sort, &configuration_variable.sort)
                    .unwrap_or(false)
        })
        .collect::<Vec<_>>();
    let exact = candidates
        .iter()
        .filter(|symbol| symbol.result_sort == configuration_variable.sort)
        .cloned()
        .collect::<Vec<_>>();
    if !exact.is_empty() {
        candidates = exact;
    }
    let [candidate] = candidates.as_slice() else {
        return None;
    };

    let mut names_to_avoid = pattern_variable_names(state)
        .into_iter()
        .chain(
            substitution
                .values()
                .flat_map(|term| term.attributes().variables.iter())
                .map(|variable| variable.name.clone()),
        )
        .collect::<BTreeSet<_>>();
    let arguments = candidate
        .argument_sorts
        .iter()
        .enumerate()
        .map(|(index, sort)| {
            fresh_variable(
                &Variable::new(format!("Ex#Overload{index}"), sort.clone()),
                &mut names_to_avoid,
                fresh_counter,
            )
        })
        .collect::<Vec<_>>();
    let candidate_term = Term::application(candidate.clone(), Vec::new(), arguments);
    let configuration_value = if candidate.result_sort == configuration_variable.sort {
        candidate_term.clone()
    } else {
        Term::injection(
            candidate.result_sort.clone(),
            configuration_variable.sort.clone(),
            candidate_term.clone(),
        )
    };
    let lifted = if candidate.result_sort == *target {
        candidate_term
    } else {
        Term::injection(
            candidate.result_sort.clone(),
            target.clone(),
            candidate_term,
        )
    };
    let found = match match_terms_in_definition(MatchMode::Rewrite, definition, &rule_term, &lifted)
    {
        MatchResult::Success(found) => found,
        MatchResult::Failed(_) | MatchResult::Indeterminate { .. } => return None,
    };
    Some((
        compose(&found, &substitution),
        vec![Predicate::Equals(
            Term::variable(configuration_variable.clone()),
            configuration_value,
        )],
    ))
}

fn combine_rule_attempts(attempts: impl IntoIterator<Item = RuleAttempt>) -> RuleAttempt {
    let mut applications = Vec::new();
    let mut trivial = false;
    for attempt in attempts {
        match attempt {
            RuleAttempt::NotApplicable => {}
            RuleAttempt::Trivial => trivial = true,
            RuleAttempt::Applied(mut found) => applications.append(&mut found),
            RuleAttempt::Indeterminate(reason) => return RuleAttempt::Indeterminate(reason),
        }
    }
    if applications.is_empty() {
        if trivial {
            RuleAttempt::Trivial
        } else {
            RuleAttempt::NotApplicable
        }
    } else {
        RuleAttempt::Applied(applications)
    }
}

fn conjoin(mut predicates: Vec<Predicate>) -> Predicate {
    match predicates.len() {
        0 => Predicate::True,
        1 => predicates.pop().unwrap(),
        _ => Predicate::And(predicates),
    }
}

pub(crate) fn quantify_introduced_variables(
    pattern: &Pattern,
    predicates: Vec<Predicate>,
) -> Predicate {
    let mut condition = conjoin(predicates);
    let state_variables = pattern_free_variables(pattern);
    let introduced = condition
        .free_variables()
        .difference(&state_variables)
        .cloned()
        .collect::<Vec<_>>();
    for variable in introduced.into_iter().rev() {
        condition = Predicate::Exists(variable, Box::new(condition));
    }
    condition
}

pub(crate) fn conjunctively_contains_alpha_equivalent(
    predicates: &[Predicate],
    target: &Predicate,
) -> bool {
    predicates.iter().any(|predicate| {
        alpha_equivalent(predicate, target)
            || matches!(predicate, Predicate::And(inner) if conjunctively_contains_alpha_equivalent(inner, target))
    })
}

fn alpha_equivalent(left: &Predicate, right: &Predicate) -> bool {
    let mut left_index = 0;
    let mut right_index = 0;
    alpha_normalize(left, &mut left_index) == alpha_normalize(right, &mut right_index)
}

fn alpha_normalize(predicate: &Predicate, next: &mut usize) -> Predicate {
    match predicate {
        Predicate::Exists(variable, inner) | Predicate::Forall(variable, inner) => {
            // NUL cannot occur in parsed KORE identifiers, so these canonical names cannot capture
            // a free source variable.
            let normalized = variable.with_name(format!("\0bound{next}"));
            *next += 1;
            let substitution = [(variable.clone(), Term::variable(normalized.clone()))]
                .into_iter()
                .collect();
            let inner = substitute_predicate(inner, &substitution);
            let inner = Box::new(alpha_normalize(&inner, next));
            if matches!(predicate, Predicate::Exists(..)) {
                Predicate::Exists(normalized, inner)
            } else {
                Predicate::Forall(normalized, inner)
            }
        }
        Predicate::Not(inner) => Predicate::Not(Box::new(alpha_normalize(inner, next))),
        Predicate::And(predicates) => Predicate::And(
            predicates
                .iter()
                .map(|predicate| alpha_normalize(predicate, next))
                .collect(),
        ),
        Predicate::Or(predicates) => Predicate::Or(
            predicates
                .iter()
                .map(|predicate| alpha_normalize(predicate, next))
                .collect(),
        ),
        Predicate::Implies(left, right) => Predicate::Implies(
            Box::new(alpha_normalize(left, next)),
            Box::new(alpha_normalize(right, next)),
        ),
        Predicate::Iff(left, right) => Predicate::Iff(
            Box::new(alpha_normalize(left, next)),
            Box::new(alpha_normalize(right, next)),
        ),
        predicate => predicate.clone(),
    }
}

fn extend_unique(predicates: &mut Vec<Predicate>, added: impl IntoIterator<Item = Predicate>) {
    let hash = |predicate: &Predicate| {
        let mut hasher = FxHasher::default();
        predicate.hash(&mut hasher);
        hasher.finish()
    };
    let mut positions = FxHashMap::<u64, Vec<usize>>::default();
    for (position, predicate) in predicates.iter().enumerate() {
        positions.entry(hash(predicate)).or_default().push(position);
    }
    for predicate in added {
        let predicate_hash = hash(&predicate);
        let duplicate = positions.get(&predicate_hash).is_some_and(|candidates| {
            candidates
                .iter()
                .any(|&index| predicates[index] == predicate)
        });
        if !duplicate {
            let position = predicates.len();
            predicates.push(predicate);
            positions.entry(predicate_hash).or_default().push(position);
        }
    }
}

pub(crate) fn check_concreteness(
    rule: &RewriteRule,
    substitution: &Substitution,
) -> Option<Variable> {
    let constrained = match &rule.attributes.concreteness {
        Concreteness::Unconstrained => return None,
        Concreteness::All(kind) => rule
            .lhs
            .attributes()
            .variables
            .iter()
            .cloned()
            .map(|variable| (variable, *kind))
            .collect::<Vec<_>>(),
        Concreteness::Some(constrained) => constrained
            .iter()
            .filter_map(|((name, sort), kind)| {
                rule.lhs
                    .attributes()
                    .variables
                    .iter()
                    .find(|variable| {
                        variable
                            .name
                            .as_ref()
                            .strip_prefix("Rule#")
                            .or_else(|| variable.name.as_ref().strip_prefix("Eq#"))
                            == Some(name.as_ref())
                            && sort_name(&variable.sort) == Some(sort.as_ref())
                    })
                    .cloned()
                    .map(|variable| (variable, *kind))
            })
            .collect(),
    };
    constrained.into_iter().find_map(|(variable, kind)| {
        let Some(term) = substitution.get(&variable) else {
            return Some(variable);
        };
        let concrete = term.attributes().constructor_like;
        let satisfied = match kind {
            ConstraintKind::Concrete => concrete,
            ConstraintKind::Symbolic => !concrete,
        };
        (!satisfied).then_some(variable)
    })
}

fn sort_name(sort: &Sort) -> Option<&str> {
    match sort {
        Sort::Application { name, .. } => Some(name.as_ref()),
        Sort::Variable(_) => None,
    }
}

fn freshen_existentials(rule: &RewriteRule, pattern: &Pattern) -> Substitution {
    let mut names_to_avoid = pattern_variable_names(pattern);
    rule.existentials
        .iter()
        .cloned()
        .map(|variable| {
            let fresh = freshen_existential(&variable, &mut names_to_avoid);
            (variable, fresh)
        })
        .collect()
}

/// Give an existential introduced by a rewrite the same externally meaningful name Booster does.
///
/// `Ex#` is provenance used only while a rule is internalized. At application time Booster strips
/// that marker, keeps the original name when it is available, and increments a trailing decimal
/// counter only while the name collides with a variable in the current pattern. In particular,
/// names may be reused after an earlier variable disappears from the state.
fn freshen_existential(
    variable: &Variable,
    names_to_avoid: &mut BTreeSet<crate::term::Name>,
) -> Term {
    let mut name = variable
        .name
        .strip_prefix("Ex#")
        .or_else(|| variable.name.strip_prefix("Rule#"))
        .unwrap_or(variable.name.as_ref())
        .to_owned();
    while !names_to_avoid.insert(name.as_str().into()) {
        name = increment_name_counter(&name);
    }
    Term::variable(variable.with_name(name))
}

fn increment_name_counter(name: &str) -> String {
    let digits = name.bytes().rev().take_while(u8::is_ascii_digit).count();
    if digits == 0 {
        return format!("{name}0");
    }
    let prefix = &name[..name.len() - digits];
    let counter = &name[name.len() - digits..];
    match counter
        .parse::<u64>()
        .ok()
        .and_then(|value| value.checked_add(1))
    {
        Some(counter) => format!("{prefix}{counter}"),
        None => format!("{name}0"),
    }
}

fn fresh_variable(
    variable: &Variable,
    names_to_avoid: &mut BTreeSet<crate::term::Name>,
    fresh_counter: &mut u64,
) -> Term {
    let name = loop {
        let name = format!("{}!{}", variable.name, *fresh_counter);
        *fresh_counter += 1;
        if names_to_avoid.insert(name.as_str().into()) {
            break name;
        }
    };
    Term::variable(variable.with_name(name))
}

fn pattern_variable_names(pattern: &Pattern) -> BTreeSet<crate::term::Name> {
    pattern_free_variables(pattern)
        .into_iter()
        .map(|variable| variable.name)
        .collect()
}

fn pattern_free_variables(pattern: &Pattern) -> BTreeSet<Variable> {
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

/// Apply a saturated substitution throughout a predicate collection.
pub fn substitute_predicates(
    predicates: &[Predicate],
    substitution: &Substitution,
) -> Vec<Predicate> {
    predicates
        .iter()
        .map(|predicate| substitute_predicate(predicate, substitution))
        .collect()
}

fn substitute_predicate(predicate: &Predicate, substitution: &Substitution) -> Predicate {
    match predicate {
        Predicate::True => Predicate::True,
        Predicate::False => Predicate::False,
        Predicate::Term(term) => Predicate::Term(substitute(term, substitution)),
        Predicate::Equals(left, right) => Predicate::Equals(
            substitute(left, substitution),
            substitute(right, substitution),
        ),
        Predicate::Ceil(term) => Predicate::Ceil(substitute(term, substitution)),
        Predicate::Floor(term) => Predicate::Floor(substitute(term, substitution)),
        Predicate::In(left, right) => Predicate::In(
            substitute(left, substitution),
            substitute(right, substitution),
        ),
        Predicate::Not(inner) => {
            Predicate::Not(Box::new(substitute_predicate(inner, substitution)))
        }
        Predicate::And(inner) => Predicate::And(substitute_predicates(inner, substitution)),
        Predicate::Or(inner) => Predicate::Or(substitute_predicates(inner, substitution)),
        Predicate::Implies(left, right) => Predicate::Implies(
            Box::new(substitute_predicate(left, substitution)),
            Box::new(substitute_predicate(right, substitution)),
        ),
        Predicate::Iff(left, right) => Predicate::Iff(
            Box::new(substitute_predicate(left, substitution)),
            Box::new(substitute_predicate(right, substitution)),
        ),
        Predicate::Exists(variable, inner) => Predicate::Exists(
            variable.clone(),
            Box::new(substitute_predicate(
                inner,
                &without_variable(substitution, variable),
            )),
        ),
        Predicate::Forall(variable, inner) => Predicate::Forall(
            variable.clone(),
            Box::new(substitute_predicate(
                inner,
                &without_variable(substitution, variable),
            )),
        ),
    }
}

fn without_variable(substitution: &Substitution, variable: &Variable) -> Substitution {
    let mut substitution = substitution.clone();
    substitution.remove(variable);
    substitution
}

pub(crate) fn predicates_truth(predicates: &[Predicate]) -> Truth {
    predicates.iter().fold(Truth::True, |result, predicate| {
        and_truth(result, predicate_truth(predicate))
    })
}

/// Detect a constructor exclusion that contradicts an internalized finite no-junk axiom.
pub(crate) fn violates_finite_constructor_domain(
    definition: &BackendDefinition,
    predicates: &[Predicate],
) -> bool {
    let mut exclusions = BTreeMap::<Term, BTreeSet<ConstructorHead>>::new();
    for predicate in predicates {
        collect_constructor_exclusions(definition, predicate, &mut exclusions);
    }
    exclusions.into_iter().any(|(subject, excluded)| {
        definition
            .finite_constructor_heads(&subject.sort())
            .is_some_and(|constructors| constructors.is_subset(&excluded))
    })
}

fn collect_constructor_exclusions(
    definition: &BackendDefinition,
    predicate: &Predicate,
    exclusions: &mut BTreeMap<Term, BTreeSet<ConstructorHead>>,
) {
    if let Predicate::And(predicates) = predicate {
        for predicate in predicates {
            collect_constructor_exclusions(definition, predicate, exclusions);
        }
        return;
    }
    let Predicate::Not(inner) = predicate else {
        return;
    };
    let mut inner = inner.as_ref();
    let mut binders = BTreeSet::new();
    while let Predicate::Exists(variable, body) = inner {
        binders.insert(variable.clone());
        inner = body;
    }
    let Predicate::Equals(left, right) = inner else {
        return;
    };
    let pair = [(left, right), (right, left)]
        .into_iter()
        .find_map(|(subject, constructor)| {
            let head = constructor_head(constructor)?;
            definition
                .finite_constructor_heads(&subject.sort())
                .is_some_and(|constructors| constructors.contains(&head))
                .then_some((subject, constructor, head))
        });
    let Some((subject, constructor, head)) = pair else {
        return;
    };
    if !is_functional_pattern(subject)
        || !subject.attributes().variables.is_disjoint(&binders)
        || !constructor.attributes().variables.is_subset(&binders)
    {
        return;
    }
    exclusions.entry(subject.clone()).or_default().insert(head);
}

fn predicate_truth(predicate: &Predicate) -> Truth {
    match predicate {
        Predicate::True => Truth::True,
        Predicate::False => Truth::False,
        Predicate::Term(term) => bool_term_truth(term),
        Predicate::Equals(left, right) if left == right => Truth::True,
        Predicate::Equals(left, right)
            if left.attributes().constructor_like && right.attributes().constructor_like =>
        {
            Truth::False
        }
        Predicate::Not(inner) => match predicate_truth(inner) {
            Truth::True => Truth::False,
            Truth::False => Truth::True,
            Truth::Unknown => Truth::Unknown,
        },
        Predicate::And(inner) => predicates_truth(inner),
        Predicate::Or(inner) => inner.iter().fold(Truth::False, |result, predicate| {
            or_truth(result, predicate_truth(predicate))
        }),
        Predicate::Implies(left, right) => or_truth(
            match predicate_truth(left) {
                Truth::True => Truth::False,
                Truth::False => Truth::True,
                Truth::Unknown => Truth::Unknown,
            },
            predicate_truth(right),
        ),
        Predicate::Iff(left, right) => match (predicate_truth(left), predicate_truth(right)) {
            (Truth::True, Truth::True) | (Truth::False, Truth::False) => Truth::True,
            (Truth::True, Truth::False) | (Truth::False, Truth::True) => Truth::False,
            _ => Truth::Unknown,
        },
        Predicate::Ceil(term) if term.attributes().constructor_like => Truth::True,
        Predicate::Equals(..)
        | Predicate::Ceil(_)
        | Predicate::Floor(_)
        | Predicate::In(..)
        | Predicate::Exists(..)
        | Predicate::Forall(..) => Truth::Unknown,
    }
}

fn bool_term_truth(term: &Term) -> Truth {
    match term.kind() {
        TermKind::DomainValue { sort, value }
            if sort == &Sort::simple("SortBool") && value.as_ref() == "true" =>
        {
            Truth::True
        }
        TermKind::DomainValue { sort, value }
            if sort == &Sort::simple("SortBool") && value.as_ref() == "false" =>
        {
            Truth::False
        }
        _ => Truth::Unknown,
    }
}

fn and_truth(left: Truth, right: Truth) -> Truth {
    match (left, right) {
        (Truth::False, _) | (_, Truth::False) => Truth::False,
        (Truth::True, Truth::True) => Truth::True,
        _ => Truth::Unknown,
    }
}

fn or_truth(left: Truth, right: Truth) -> Truth {
    match (left, right) {
        (Truth::True, _) | (_, Truth::True) => Truth::True,
        (Truth::False, Truth::False) => Truth::False,
        _ => Truth::Unknown,
    }
}

#[cfg(test)]
mod tests {
    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    use super::*;
    use crate::cancellation::CancellationToken;
    use crate::transition::{
        ObservationEvent, ObservationFilterError, ObservationOptions, PatternDigest,
        TransitionClass,
    };

    #[test]
    fn large_unique_extensions_preserve_first_occurrence_order() {
        let sort = Sort::simple("SortS");
        let mut predicates = (0..20)
            .map(|index| {
                Predicate::Equals(
                    Term::variable(Variable::new(format!("X{index}"), sort.clone())),
                    Term::domain_value(sort.clone(), index.to_string()),
                )
            })
            .collect::<Vec<_>>();
        let original = predicates.clone();

        extend_unique(
            &mut predicates,
            [original[19].clone(), Predicate::True, original[0].clone()],
        );

        assert_eq!(&predicates[..20], original);
        assert_eq!(predicates[20], Predicate::True);
    }

    #[test]
    fn rule_diagnostics_omit_term_alias_binders() {
        let sort = Sort::simple("SortS");
        let alias = Variable::new("Rule#Alias", sort.clone());
        let ordinary = Variable::new("Rule#Ordinary", sort.clone());
        let lhs = Term::application(
            std::sync::Arc::new(Symbol::constructor(
                "pair",
                vec![sort.clone(), sort.clone()],
                sort.clone(),
            )),
            Vec::new(),
            vec![
                Term::and(
                    Term::domain_value(sort.clone(), "value"),
                    Term::variable(alias.clone()),
                ),
                Term::variable(ordinary.clone()),
            ],
        );

        assert_eq!(term_alias_variables(&lhs), BTreeSet::from([alias]));
        assert!(!term_alias_variables(&lhs).contains(&ordinary));
    }

    fn existential_equality(bound: &str, free: &str) -> Predicate {
        let sort = Sort::simple("SortS");
        let bound = Variable::new(bound, sort.clone());
        Predicate::Exists(
            bound.clone(),
            Box::new(Predicate::Equals(
                Term::variable(bound),
                Term::variable(Variable::new(free, sort)),
            )),
        )
    }

    #[test]
    fn recognizes_alpha_equivalent_applicability_exclusions() {
        let excluded = Predicate::Not(Box::new(existential_equality("Fresh!0", "State")));
        let retried = Predicate::Not(Box::new(existential_equality("Fresh!1", "State")));
        let different_free_variable =
            Predicate::Not(Box::new(existential_equality("Fresh!1", "Other")));

        assert!(conjunctively_contains_alpha_equivalent(
            &[Predicate::And(vec![Predicate::True, excluded])],
            &retried,
        ));
        assert!(!conjunctively_contains_alpha_equivalent(
            &[different_free_variable],
            &retried,
        ));
    }

    fn definition(axioms: &str) -> BackendDefinition {
        let source = format!(
            r#"[]
            module MAIN
                sort SortS{{}} [hasDomainValues{{}}()]
                symbol wrap{{}}(SortS{{}}) : SortS{{}} [constructor{{}}()]
                symbol injectiveFunction{{}}(SortS{{}}) : SortS{{}}
                    [function{{}}(), total{{}}(), injective{{}}()]
                {axioms}
            endmodule []"#
        );
        let syntax = parse_definition(&source).expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    #[test]
    fn rejects_exclusions_covering_a_finite_constructor_sort() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortS{} []
                symbol a{}() : SortS{} [constructor{}()]
                symbol b{}() : SortS{} [constructor{}()]
                symbol c{}() : SortS{} [constructor{}()]
                axiom{} \or{SortS{}}(
                    a{}(),
                    \or{SortS{}}(b{}(), c{}(), \bottom{SortS{}}())
                ) [constructor{}()]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let variable = Term::variable(Variable::new("X", Sort::simple("SortS")));
        let excluded = ["a", "b", "c"]
            .into_iter()
            .map(|name| {
                let constructor = definition
                    .internalize_term(&parse_pattern(&format!("{name}{{}}()")).unwrap(), &[])
                    .unwrap();
                Predicate::Not(Box::new(Predicate::Equals(variable.clone(), constructor)))
            })
            .collect::<Vec<_>>();

        assert!(!violates_finite_constructor_domain(
            &definition,
            &excluded[..2]
        ));
        assert!(violates_finite_constructor_domain(&definition, &excluded));
    }

    #[test]
    fn rejects_exclusions_covering_parameterized_constructor_families() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortElement{} []
                sort SortList{} []
                symbol nil{}() : SortList{} [constructor{}()]
                symbol cons{}(SortElement{}, SortList{}) : SortList{} [constructor{}()]
                symbol unknown{}() : SortList{} [function{}(), total{}()]
                axiom{} \or{SortList{}}(
                    nil{}(),
                    \exists{SortList{}}(
                        E:SortElement{},
                        \exists{SortList{}}(
                            T:SortList{},
                            cons{}(E:SortElement{}, T:SortList{})
                        )
                    ),
                    \bottom{SortList{}}()
                ) [constructor{}()]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let list = Term::variable(Variable::new("L", Sort::simple("SortList")));
        let nil = internal_term(&definition, "nil{}()");
        let element = Variable::new("E0", Sort::simple("SortElement"));
        let tail = Variable::new("T1", Sort::simple("SortList"));
        let cons = internal_term(&definition, "cons{}(E0:SortElement{}, T1:SortList{})");
        let excludes_nil = Predicate::Not(Box::new(Predicate::Equals(list.clone(), nil)));
        let excludes_every_cons = Predicate::Not(Box::new(Predicate::Exists(
            element,
            Box::new(Predicate::Exists(
                tail,
                Box::new(Predicate::Equals(list.clone(), cons.clone())),
            )),
        )));
        let excludes_one_cons = Predicate::Not(Box::new(Predicate::Equals(list, cons)));

        assert!(!violates_finite_constructor_domain(
            &definition,
            &[excludes_nil.clone(), excludes_one_cons],
        ));
        assert!(violates_finite_constructor_domain(
            &definition,
            &[excludes_nil, excludes_every_cons],
        ));

        let unknown = internal_term(&definition, "unknown{}()");
        let nil = internal_term(&definition, "nil{}()");
        let element = Variable::new("E2", Sort::simple("SortElement"));
        let tail = Variable::new("T3", Sort::simple("SortList"));
        let cons = internal_term(&definition, "cons{}(E2:SortElement{}, T3:SortList{})");
        assert!(violates_finite_constructor_domain(
            &definition,
            &[
                Predicate::Not(Box::new(Predicate::Equals(unknown.clone(), nil))),
                Predicate::Not(Box::new(Predicate::Exists(
                    element,
                    Box::new(Predicate::Exists(
                        tail,
                        Box::new(Predicate::Equals(unknown, cons)),
                    )),
                ))),
            ],
        ));
    }

    fn set_selection_definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortElement{} [hasDomainValues{}()]
                hooked-sort SortSet{}
                    [hook{}("SET.Set"), unit{}(setUnit{}()), element{}(setItem{}()), concat{}(setConcat{}())]
                sort SortState{} []
                symbol setUnit{}() : SortSet{}
                    [function{}(), total{}(), hook{}("SET.unit")]
                symbol setItem{}(SortElement{}) : SortSet{}
                    [function{}(), total{}(), hook{}("SET.element")]
                symbol setConcat{}(SortSet{}, SortSet{}) : SortSet{}
                    [function{}(), hook{}("SET.concat"), assoc{}(), comm{}(), idem{}()]
                symbol state{}(SortSet{}) : SortState{} [constructor{}()]
                symbol picked{}(SortElement{}, SortSet{}) : SortState{} [constructor{}()]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        state{}(setConcat{}(setItem{}(ELEMENT:SortElement{}), REST:SortSet{})),
                        \top{SortState{}}()
                    ),
                    picked{}(ELEMENT:SortElement{}, REST:SortSet{})
                ) [label{}("select")]
            endmodule []"#,
        )
        .expect("set definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("set definition should internalize")
    }

    fn opaque_set_narrowing_definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortElement{} [hasDomainValues{}()]
                hooked-sort SortSet{}
                    [hook{}("SET.Set"), unit{}(setUnit{}()), element{}(setItem{}()), concat{}(setConcat{}())]
                sort SortState{} []
                symbol setUnit{}() : SortSet{}
                    [function{}(), total{}(), hook{}("SET.unit")]
                symbol setItem{}(SortElement{}) : SortSet{}
                    [function{}(), total{}(), hook{}("SET.element")]
                symbol setConcat{}(SortSet{}, SortSet{}) : SortSet{}
                    [function{}(), hook{}("SET.concat"), assoc{}(), comm{}(), idem{}()]
                symbol opaqueA{}() : SortSet{} [function{}(), total{}()]
                symbol opaqueB{}() : SortSet{} [function{}(), total{}()]
                symbol state{}(SortSet{}) : SortState{} [constructor{}()]
                symbol selected{}(SortElement{}) : SortState{} [constructor{}()]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        state{}(
                            setConcat{}(
                                setItem{}(RULE:SortElement{}),
                                setConcat{}(
                                    opaqueA{}(),
                                    setConcat{}(opaqueB{}(), opaqueB{}())
                                )
                            )
                        ),
                        \top{SortState{}}()
                    ),
                    selected{}(RULE:SortElement{})
                ) [label{}("opaque-set")]
            endmodule []"#,
        )
        .expect("opaque Set definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN")
            .expect("opaque Set definition should internalize")
    }

    fn map_selection_definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortKey{} [hasDomainValues{}()]
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
                symbol mapState{}(SortMap{}) : SortState{} [constructor{}()]
                symbol mapPicked{}(SortKey{}, SortValue{}, SortMap{}) : SortState{} [constructor{}()]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        mapState{}(
                            mapConcat{}(
                                mapItem{}(KEY:SortKey{}, VALUE:SortValue{}),
                                REST:SortMap{}
                            )
                        ),
                        \top{SortState{}}()
                    ),
                    mapPicked{}(KEY:SortKey{}, VALUE:SortValue{}, REST:SortMap{})
                ) [label{}("map-select")]
            endmodule []"#,
        )
        .expect("map definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("map definition should internalize")
    }

    fn closed_map_narrowing_definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortKey{} [hasDomainValues{}()]
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
                symbol mapState{}(SortMap{}) : SortState{} [constructor{}()]
                symbol mixedState{}(SortValue{}, SortMap{}) : SortState{} [constructor{}()]
                symbol select{}(SortValue{}) : SortValue{} [function{}(), total{}()]
                symbol done{}() : SortState{} [constructor{}()]
                symbol selected{}(SortValue{}) : SortState{} [constructor{}()]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        mapState{}(
                            mapConcat{}(
                                mapItem{}(
                                    \dv{SortKey{}}("first"),
                                    \dv{SortValue{}}("first-value")
                                ),
                                mapItem{}(
                                    \dv{SortKey{}}("second"),
                                    \dv{SortValue{}}("second-value")
                                )
                            )
                        ),
                        \top{SortState{}}()
                    ),
                    done{}()
                ) [label{}("closed-map")]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        mixedState{}(
                            select{}(RULE:SortValue{}),
                            mapConcat{}(
                                mapItem{}(
                                    \dv{SortKey{}}("first"),
                                    \dv{SortValue{}}("first-value")
                                ),
                                mapItem{}(
                                    \dv{SortKey{}}("second"),
                                    \dv{SortValue{}}("second-value")
                                )
                            )
                        ),
                        \top{SortState{}}()
                    ),
                    selected{}(RULE:SortValue{})
                ) [label{}("mixed-unification")]
            endmodule []"#,
        )
        .expect("closed map definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN")
            .expect("closed map definition should internalize")
    }

    fn symbolic_map_key_definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortKey{} [hasDomainValues{}()]
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
                symbol mapState{}(SortMap{}) : SortState{} [constructor{}()]
                symbol mapPicked{}(SortValue{}, SortMap{}) : SortState{} [constructor{}()]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        mapState{}(
                            mapConcat{}(
                                mapItem{}(\dv{SortKey{}}("wanted"), VALUE:SortValue{}),
                                REST:SortMap{}
                            )
                        ),
                        \top{SortState{}}()
                    ),
                    mapPicked{}(VALUE:SortValue{}, REST:SortMap{})
                ) [label{}("select-wanted")]
            endmodule []"#,
        )
        .expect("symbolic map-key definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN")
            .expect("symbolic map-key definition should internalize")
    }

    fn shared_symbolic_map_key_definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortKey{} []
                sort SortValue{} []
                hooked-sort SortMap{}
                    [hook{}("MAP.Map"), unit{}(mapUnit{}()), element{}(mapItem{}()), concat{}(mapConcat{}())]
                sort SortState{} []
                symbol mapUnit{}() : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.unit")]
                symbol mapItem{}(SortKey{}, SortValue{}) : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.element")]
                symbol mapConcat{}(SortMap{}, SortMap{}) : SortMap{}
                    [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
                symbol request{}(SortMap{}, SortKey{}) : SortState{} [constructor{}()]
                symbol exact{}() : SortState{} [constructor{}()]
                symbol different{}() : SortState{} [constructor{}()]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        request{}(
                            mapConcat{}(
                                mapItem{}(KEY:SortKey{}, VALUE:SortValue{}),
                                REST:SortMap{}
                            ),
                            KEY:SortKey{}
                        ),
                        \top{SortState{}}()
                    ),
                    exact{}()
                ) [label{}("exact")]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        request{}(
                            mapConcat{}(
                                mapItem{}(ENTRY:SortKey{}, VALUE:SortValue{}),
                                REST:SortMap{}
                            ),
                            REQUESTED:SortKey{}
                        ),
                        \not{SortState{}}(
                            \equals{SortKey{}, SortState{}}(
                                ENTRY:SortKey{},
                                REQUESTED:SortKey{}
                            )
                        )
                    ),
                    different{}()
                ) [label{}("different")]
            endmodule []"#,
        )
        .expect("shared symbolic map-key definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN")
            .expect("shared symbolic map-key definition should internalize")
    }

    #[cfg(feature = "z3")]
    fn map_not_in_keys_rewrite_definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                sort SortKey{} []
                sort SortValue{} []
                hooked-sort SortMap{}
                    [hook{}("MAP.Map"), unit{}(mapUnit{}()), element{}(mapItem{}()), concat{}(mapConcat{}())]
                sort SortState{} []
                symbol mapUnit{}() : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.unit")]
                symbol mapItem{}(SortKey{}, SortValue{}) : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.element")]
                symbol mapConcat{}(SortMap{}, SortMap{}) : SortMap{}
                    [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
                symbol inKeys{}(SortKey{}, SortMap{}) : SortBool{}
                    [function{}(), total{}(), hook{}("MAP.in_keys")]
                symbol state{}(SortBool{}) : SortState{} [constructor{}()]
                symbol done{}() : SortState{} [constructor{}()]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        state{}(
                            inKeys{}(
                                KEY:SortKey{},
                                mapConcat{}(
                                    mapItem{}(ENTRY:SortKey{}, VALUE:SortValue{}),
                                    REST:SortMap{}
                                )
                            )
                        ),
                        \top{SortState{}}()
                    ),
                    done{}()
                ) [label{}("not-in-keys")]
            endmodule []"#,
        )
        .expect("map not-in-keys definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN")
            .expect("map not-in-keys definition should internalize")
    }

    fn overload_rewrite_definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortSub{} [hasDomainValues{}()]
                sort SortTop{} []
                sort SortState{} []
                symbol inj{From, To}(From) : To [sortInjection{}(), injective{}()]
                symbol lower{}(SortSub{}) : SortSub{} [constructor{}()]
                symbol upper{}(SortTop{}) : SortTop{} [constructor{}()]
                symbol overloadState{}(SortTop{}) : SortState{} [constructor{}()]
                symbol overloadResult{}(SortTop{}) : SortState{} [constructor{}()]
                axiom{R} \equals{SortTop{}, R}(
                    upper{}(X:SortTop{}),
                    inj{SortSub{}, SortTop{}}(lower{}(Y:SortSub{}))
                ) [symbol-overload{}(upper{}(), lower{}())]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        overloadState{}(upper{}(X:SortTop{})),
                        \top{SortState{}}()
                    ),
                    overloadResult{}(X:SortTop{})
                ) [label{}("overload-match")]
            endmodule []"#,
        )
        .expect("overload rewrite definition should parse");
        let mut definition = BackendDefinition::internalize(&syntax, "MAIN")
            .expect("overload rewrite definition should internalize");
        definition
            .sort_graph
            .insert("SortTop", [crate::term::Name::from("SortSub")]);
        definition
    }

    #[cfg(feature = "z3")]
    fn ite_rewrite_definition(lhs: &str) -> BackendDefinition {
        let source = r#"[]
            module MAIN
                sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                sort SortValue{} []
                sort SortState{} []
                symbol ite{}(SortBool{}, SortValue{}, SortValue{}) : SortValue{}
                    [function{}(), total{}(), hook{}("KEQUAL.ite")]
                symbol chosen{}() : SortValue{} [constructor{}()]
                symbol rejected{}() : SortValue{} [constructor{}()]
                symbol state{}(SortValue{}) : SortState{} [constructor{}()]
                symbol done{}() : SortState{} [constructor{}()]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        $LHS,
                        \top{SortState{}}()
                    ),
                    done{}()
                ) [label{}("choose")]
            endmodule []"#
            .replace("$LHS", lhs);
        let syntax = parse_definition(&source).expect("ITE definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("ITE definition should internalize")
    }

    fn unresolved_function_rewrite_definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortS{} [hasDomainValues{}()]
                sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                symbol wrap{}(SortBool{}) : SortS{} [constructor{}()]
                symbol not{}(SortBool{}) : SortBool{}
                    [function{}(), total{}()]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(
                        wrap{}(not{}(X:SortBool{})),
                        \top{SortS{}}()
                    ),
                    \dv{SortS{}}("done")
                ) [label{}("negated")]
            endmodule []"#,
        )
        .expect("function rewrite definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN")
            .expect("function rewrite definition should internalize")
    }

    fn non_evaluable_function_rewrite_definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortS{} [hasDomainValues{}()]
                symbol wrap{}(SortS{}) : SortS{} [constructor{}()]
                symbol foo{}(SortS{}) : SortS{} [constructor{}()]
                symbol f{}(SortS{}) : SortS{}
                    [function{}(), total{}(), no-evaluators{}()]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(
                        wrap{}(foo{}(X:SortS{})),
                        \top{SortS{}}()
                    ),
                    wrap{}(f{}(X:SortS{}))
                ) [label{}("to-non-evaluable")]
            endmodule []"#,
        )
        .expect("non-evaluable function definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN")
            .expect("non-evaluable function definition should internalize")
    }

    #[test]
    fn aborts_after_rewriting_to_a_concrete_function_without_evaluators() {
        let definition = non_evaluable_function_rewrite_definition();
        let initial = Pattern {
            term: internal_term(&definition, r#"wrap{}(foo{}(\dv{SortS{}}("12")))"#),
            constraints: Vec::new(),
        };

        let execution = execute(
            &definition,
            initial,
            ExecutionOptions {
                max_depth: 2,
                ..ExecutionOptions::default()
            },
        );

        assert!(matches!(
            execution.leaves.as_slice(),
            [ExecutionLeaf {
                pattern: Pattern { term, constraints },
                depth: 1,
                halt_reason: HaltReason::Indeterminate(IndeterminateReason::Match {
                    rule_id,
                    ..
                }),
                ..
            }] if term == &internal_term(
                &definition,
                r#"wrap{}(f{}(\dv{SortS{}}("12")))"#,
            ) && constraints.is_empty() && rule_id == "to-non-evaluable"
        ));
    }

    fn kequal_rewrite_definition(lhs: &str) -> BackendDefinition {
        let source = r#"[]
            module MAIN
                sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                sort SortValue{} []
                sort SortState{} []
                symbol equal{}(SortValue{}, SortValue{}) : SortBool{}
                    [function{}(), total{}(), hook{}("KEQUAL.eq")]
                symbol chosen{}() : SortValue{} [constructor{}()]
                symbol rejected{}() : SortValue{} [constructor{}()]
                symbol state{}(SortBool{}) : SortState{} [constructor{}()]
                symbol done{}() : SortState{} [constructor{}()]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        $LHS,
                        \top{SortState{}}()
                    ),
                    done{}()
                ) [label{}("equality")]
            endmodule []"#
            .replace("$LHS", lhs);
        let syntax = parse_definition(&source).expect("K equality definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN")
            .expect("K equality definition should internalize")
    }

    fn scalar_equality_rewrite_definition(
        equality_hook: &str,
        operand_sort: &str,
        sort_hook: &str,
    ) -> BackendDefinition {
        let source = r#"[]
            module MAIN
                sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                sort $SORT{} [hook{}("$SORT_HOOK"), hasDomainValues{}()]
                sort SortState{} []
                symbol equal{}($SORT{}, $SORT{}) : SortBool{}
                    [function{}(), total{}(), hook{}("$EQUALITY_HOOK")]
                symbol value{}() : $SORT{} [constructor{}()]
                symbol state{}(SortBool{}) : SortState{} [constructor{}()]
                symbol done{}() : SortState{} [constructor{}()]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        state{}(equal{}(VALUE:$SORT{}, value{}())),
                        \top{SortState{}}()
                    ),
                    done{}()
                ) [label{}("scalar-equality")]
            endmodule []"#
            .replace("$EQUALITY_HOOK", equality_hook)
            .replace("$SORT_HOOK", sort_hook)
            .replace("$SORT", operand_sort);
        let syntax = parse_definition(&source).expect("scalar equality definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN")
            .expect("scalar equality definition should internalize")
    }

    fn boolean_rewrite_definition(lhs: &str) -> BackendDefinition {
        let source = r#"[]
            module MAIN
                sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                sort SortState{} []
                symbol and{}(SortBool{}, SortBool{}) : SortBool{}
                    [function{}(), total{}(), hook{}("BOOL.and")]
                symbol or{}(SortBool{}, SortBool{}) : SortBool{}
                    [function{}(), total{}(), hook{}("BOOL.or")]
                symbol not{}(SortBool{}) : SortBool{}
                    [function{}(), total{}(), hook{}("BOOL.not")]
                symbol state{}(SortBool{}) : SortState{} [constructor{}()]
                symbol done{}() : SortState{} [constructor{}()]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        $LHS,
                        \top{SortState{}}()
                    ),
                    done{}()
                ) [label{}("boolean")]
            endmodule []"#
            .replace("$LHS", lhs);
        let syntax = parse_definition(&source).expect("Boolean definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN")
            .expect("Boolean definition should internalize")
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

    fn internal_term(definition: &BackendDefinition, source: &str) -> Term {
        let syntax = parse_pattern(source).expect("term should parse");
        definition
            .internalize_term(&syntax, &[])
            .expect("term should internalize")
    }

    #[test]
    fn treats_an_undefined_matched_subterm_as_trivial() {
        let definition = definition(
            r#"
            symbol partial{}() : SortS{} [function{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                wrap{}(\dv{SortS{}}("done"))
            ) [label{}("unwrap")]
            "#,
        );
        let partial = internal_term(&definition, "partial{}()");
        let subject = Pattern {
            term: internal_term(&definition, "wrap{}(partial{}())"),
            constraints: vec![Predicate::Not(Box::new(Predicate::Ceil(partial)))],
        };
        let mut fresh = 0;

        let result = rewrite_step(&definition, &subject, &mut fresh);

        assert_eq!(result, RewriteResult::Trivial(subject));
    }

    #[test]
    fn rejects_a_symbolic_occurs_check_during_rewriting() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortS{} []
                symbol pair{}(SortS{}, SortS{}) : SortS{} [constructor{}()]
                symbol nested{}(SortS{}) : SortS{} [constructor{}()]
                symbol done{}() : SortS{} [constructor{}()]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(
                        pair{}(X:SortS{}, nested{}(X:SortS{})),
                        \top{SortS{}}()
                    ),
                    done{}()
                ) [label{}("cyclic")]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let subject = Pattern {
            term: internal_term(&definition, "pair{}(Y:SortS{}, Y:SortS{})"),
            constraints: Vec::new(),
        };
        let mut fresh = 0;

        assert_eq!(
            rewrite_step(&definition, &subject, &mut fresh),
            RewriteResult::Stuck(subject)
        );
    }

    #[test]
    fn internalizes_a_nested_bottom_rewrite_rhs_as_trivial() {
        let definition = definition(
            r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(\dv{SortS{}}("start")),
                    \top{SortS{}}()
                ),
                wrap{}(\bottom{SortS{}}())
            ) [label{}("bottom")]
            "#,
        );
        let subject = Pattern {
            term: internal_term(&definition, r#"wrap{}(\dv{SortS{}}("start"))"#),
            constraints: Vec::new(),
        };
        let mut fresh = 0;

        let result = rewrite_step(&definition, &subject, &mut fresh);

        assert_eq!(result, RewriteResult::Trivial(subject.clone()));
        let execution = execute(&definition, subject, ExecutionOptions::default());
        assert!(matches!(
            execution.leaves.as_slice(),
            [ExecutionLeaf {
                depth: 0,
                halt_reason: HaltReason::Trivial,
                ..
            }]
        ));
    }

    #[test]
    fn reports_vacuous_execution_paths() {
        let definition = definition("");
        let subject = Pattern {
            term: internal_term(&definition, r#"wrap{}(\dv{SortS{}}("start"))"#),
            constraints: vec![Predicate::False],
        };
        let mut fresh = 0;

        assert_eq!(
            rewrite_step(&definition, &subject, &mut fresh),
            RewriteResult::Vacuous(subject.clone())
        );
        let execution = execute(&definition, subject, ExecutionOptions::default());
        assert!(matches!(
            execution.leaves.as_slice(),
            [ExecutionLeaf {
                depth: 0,
                halt_reason: HaltReason::Vacuous,
                ..
            }]
        ));
    }

    #[test]
    fn input_substitution_contradictions_are_checked_after_the_first_rewrite_attempt() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                sort SortState{} []
                symbol b{}() : SortState{} [constructor{}()]
                symbol d{}() : SortState{} [constructor{}()]
                hooked-symbol intEq{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.eq")]
                hooked-symbol intNe{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.ne")]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(b{}(), \top{SortState{}}()),
                    d{}()
                ) [label{}("step")]
            endmodule []"#,
        )
        .unwrap();
        let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
        let pattern = |state: &str| {
            let syntax = parse_pattern(&format!(
                r#"\and{{SortState{{}}}}(
                    {state}{{}}(),
                    \and{{SortState{{}}}}(
                        \equals{{SortBool{{}}, SortState{{}}}}(
                            intEq{{}}(N:SortInt{{}}, \dv{{SortInt{{}}}}("0")),
                            \dv{{SortBool{{}}}}("true")
                        ),
                        \equals{{SortBool{{}}, SortState{{}}}}(
                            intNe{{}}(N:SortInt{{}}, \dv{{SortInt{{}}}}("0")),
                            \dv{{SortBool{{}}}}("true")
                        )
                    )
                )"#
            ))
            .unwrap();
            definition.internalize_pattern(&syntax, &[]).unwrap()
        };

        let rewritten = execute(&definition, pattern("b"), ExecutionOptions::default());
        let stuck = execute(&definition, pattern("d"), ExecutionOptions::default());

        assert!(matches!(
            rewritten.leaves.as_slice(),
            [ExecutionLeaf {
                pattern: Pattern { term, constraints },
                depth: 1,
                halt_reason: HaltReason::Vacuous,
                ..
            }] if term == &internal_term(&definition, "d{}()")
                && constraints.iter().any(|predicate| matches!(predicate, Predicate::False))
        ));
        assert!(matches!(
            stuck.leaves.as_slice(),
            [ExecutionLeaf {
                depth: 0,
                halt_reason: HaltReason::Vacuous,
                ..
            }]
        ));
    }

    #[cfg(feature = "z3")]
    fn symbolic_remainder_definition(rules: &str) -> BackendDefinition {
        let source = r#"[]
            module MAIN
                sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                symbol wrap{}(SortInt{}) : SortInt{} [constructor{}()]
                symbol pair{}(SortInt{}, SortInt{}) : SortInt{} [constructor{}()]
                symbol partial{}(SortInt{}) : SortInt{} [function{}()]
                symbol lt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), smt-hook{}("<")]
                $RULES
            endmodule []"#
            .replace("$RULES", rules);
        let syntax = parse_definition(&source).expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    #[cfg(feature = "z3")]
    fn symbolic_subject(definition: &BackendDefinition) -> Pattern {
        Pattern {
            term: definition
                .internalize_term(&parse_pattern("wrap{}(X:SortInt{})").unwrap(), &[])
                .unwrap(),
            constraints: Vec::new(),
        }
    }

    fn rewritten_value(result: RewriteResult) -> String {
        let RewriteResult::Finished(applied) = result else {
            panic!("expected finished rewrite, found {result:?}");
        };
        let TermKind::DomainValue { value, .. } = applied.pattern.term.kind() else {
            panic!("expected domain value, found {:?}", applied.pattern.term);
        };
        value.to_string()
    }

    #[test]
    fn tries_priority_groups_in_ascending_numeric_order() {
        let definition = definition(
            r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(\dv{SortS{}}("zero")), \top{SortS{}}()),
                \dv{SortS{}}("high")
            ) [label{}("high"), priority{}("10")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                \dv{SortS{}}("low")
            ) [label{}("low"), priority{}("50")]
            "#,
        );
        let mut fresh = 0;

        assert_eq!(
            rewritten_value(rewrite_step(
                &definition,
                &subject(&definition, "zero"),
                &mut fresh,
            )),
            "high"
        );
        assert_eq!(
            rewritten_value(rewrite_step(
                &definition,
                &subject(&definition, "one"),
                &mut fresh,
            )),
            "low"
        );
    }

    #[test]
    fn applies_rules_with_top_level_alias_binders() {
        let definition = definition(
            r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    \and{SortS{}}(wrap{}(X:SortS{}), Whole:SortS{}),
                    \top{SortS{}}()
                ),
                \dv{SortS{}}("done")
            ) [label{}("aliased")]
            "#,
        );
        let mut fresh = 0;

        assert_eq!(
            rewritten_value(rewrite_step(
                &definition,
                &subject(&definition, "value"),
                &mut fresh,
            )),
            "done"
        );
    }

    #[test]
    fn retries_function_pattern_remainders_after_simplification() {
        let definition = definition(
            r#"
            symbol identity{}(SortS{}) : SortS{} [function{}(), total{}()]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    identity{}(X:SortS{}),
                    \and{SortS{}}(X:SortS{}, \top{SortS{}}())
                )
            ) [label{}("identity"), simplification{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(identity{}(X:SortS{})),
                    \top{SortS{}}()
                ),
                \dv{SortS{}}("done")
            ) [label{}("function-pattern")]
            "#,
        );
        let mut fresh = 0;

        assert_eq!(
            rewritten_value(rewrite_step(
                &definition,
                &subject(&definition, "value"),
                &mut fresh,
            )),
            "done"
        );
    }

    #[test]
    fn simplifies_configuration_functions_after_partial_matching() {
        let definition = definition(
            r#"
            symbol pair{}(SortS{}, SortS{}) : SortS{} [constructor{}()]
            symbol identity{}(SortS{}) : SortS{} [function{}(), total{}()]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    identity{}(X:SortS{}),
                    \and{SortS{}}(X:SortS{}, \top{SortS{}}())
                )
            ) [label{}("identity"), simplification{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    pair{}(X:SortS{}, X:SortS{}),
                    \top{SortS{}}()
                ),
                \dv{SortS{}}("done")
            ) [label{}("repeated-variable")]
            "#,
        );
        let value = r#"\dv{SortS{}}("value")"#;
        let pattern = Pattern {
            term: internal_term(
                &definition,
                &format!("pair{{}}({value}, identity{{}}({value}))"),
            ),
            constraints: Vec::new(),
        };
        let mut fresh = 0;

        assert_eq!(
            rewritten_value(rewrite_step(&definition, &pattern, &mut fresh)),
            "done"
        );
    }

    #[cfg(feature = "z3")]
    #[test]
    fn narrows_configuration_variables_from_repeated_rule_variables() {
        let definition = definition(
            r#"
            symbol pair{}(SortS{}, SortS{}) : SortS{} [constructor{}()]
            symbol arrow{}(SortS{}, SortS{}) : SortS{} [constructor{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    pair{}(T:SortS{}, T:SortS{}),
                    \top{SortS{}}()
                ),
                \dv{SortS{}}("done")
            ) [label{}("repeated-variable")]
            "#,
        );
        let configuration = Pattern {
            term: internal_term(
                &definition,
                "pair{}(X:SortS{}, arrow{}(Y:SortS{}, Z:SortS{}))",
            ),
            constraints: Vec::new(),
        };
        let expected_variable = internal_term(&definition, "X:SortS{}");
        let expected_value = internal_term(&definition, "arrow{}(Y:SortS{}, Z:SortS{})");
        let solver = crate::smt::Z3Solver::new(&definition).unwrap();
        let mut fresh = 0;

        let RewriteResult::Branch { branches, .. } =
            rewrite_step_with_solver(&definition, &configuration, &mut fresh, &solver)
        else {
            panic!("repeated-variable unification should narrow the configuration");
        };
        let [applied] = branches.as_slice() else {
            panic!("expected one narrowed application, found {branches:?}");
        };
        assert!(matches!(
            applied.pattern.term.kind(),
            TermKind::DomainValue { value, .. } if value.as_ref() == "done"
        ));
        assert!(
            applied
                .pattern
                .constraints
                .contains(&Predicate::Equals(expected_variable, expected_value,))
        );
    }

    #[cfg(feature = "z3")]
    #[test]
    fn retains_conditions_from_configuration_function_simplification() {
        let definition = definition(
            r#"
            sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
            symbol pair{}(SortS{}, SortS{}) : SortS{} [constructor{}()]
            symbol constrained{}(SortS{}) : SortS{} [function{}(), total{}()]
            symbol predicate{}(SortS{}) : SortBool{} [function{}(), total{}()]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    constrained{}(X:SortS{}),
                    \and{SortS{}}(
                        X:SortS{},
                        \equals{SortBool{}, SortS{}}(
                            predicate{}(X:SortS{}),
                            \dv{SortBool{}}("true")
                        )
                    )
                )
            ) [label{}("constrained"), simplification{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    pair{}(X:SortS{}, X:SortS{}),
                    \top{SortS{}}()
                ),
                \dv{SortS{}}("done")
            ) [label{}("repeated-variable")]
            "#,
        );
        let value = r#"\dv{SortS{}}("value")"#;
        let pattern = Pattern {
            term: internal_term(
                &definition,
                &format!("pair{{}}({value}, constrained{{}}({value}))"),
            ),
            constraints: Vec::new(),
        };
        let solver = crate::smt::Z3Solver::new(&definition).unwrap();
        let mut fresh = 0;

        let RewriteResult::Branch {
            branches,
            remainder: Some(_),
            ..
        } = rewrite_step_with_solver(&definition, &pattern, &mut fresh, &solver)
        else {
            panic!("a constrained simplification should retain applied and remainder branches");
        };
        let [branch] = branches.as_slice() else {
            panic!("expected one constrained rewrite branch, found {branches:?}");
        };
        assert_eq!(
            branch.pattern.term,
            internal_term(&definition, r#"\dv{SortS{}}("done")"#)
        );
        assert!(matches!(
            branch.pattern.constraints.as_slice(),
            [Predicate::Equals(..)]
        ));
    }

    #[test]
    fn unresolved_function_equality_requires_an_smt_solver() {
        let definition = unresolved_function_rewrite_definition();
        let term = definition
            .internalize_term(
                &parse_pattern(r#"wrap{}(\dv{SortBool{}}("true"))"#).unwrap(),
                &[],
            )
            .unwrap();
        let mut fresh = 0;

        assert!(matches!(
            rewrite_step(
                &definition,
                &Pattern {
                    term,
                    constraints: Vec::new(),
                },
                &mut fresh,
            ),
            RewriteResult::Indeterminate {
                reason: IndeterminateReason::Smt {
                    error: SmtError::Unavailable,
                    ..
                },
                ..
            }
        ));
    }

    #[cfg(feature = "z3")]
    #[test]
    fn retains_unresolved_function_equality_as_a_branch_condition() {
        let definition = unresolved_function_rewrite_definition();
        let term = internal_term(&definition, r#"wrap{}(\dv{SortBool{}}("true"))"#);
        let solver = crate::smt::Z3Solver::new(&definition).unwrap();
        let mut fresh = 0;

        let RewriteResult::Branch {
            branches,
            remainder: Some(remainder),
            ..
        } = rewrite_step_with_solver(
            &definition,
            &Pattern {
                term,
                constraints: Vec::new(),
            },
            &mut fresh,
            &solver,
        )
        else {
            panic!("functional equality should produce applied and complementary branches");
        };
        let [branch] = branches.as_slice() else {
            panic!("expected one conditional function match, found {branches:?}");
        };
        let [equality @ Predicate::Equals(left, right)] = branch.pattern.constraints.as_slice()
        else {
            panic!("expected one functional equality condition");
        };
        assert!(matches!(
            left.kind(),
            TermKind::Application { symbol, .. } if symbol.name.as_ref() == "not"
        ));
        assert_eq!(right, &Term::domain_value(Sort::simple("SortBool"), "true"));
        let fresh_variables = equality.free_variables();
        let mut fresh_variables = fresh_variables.iter();
        let fresh_variable = fresh_variables
            .next()
            .expect("the unbound rule argument should be freshened");
        assert!(fresh_variables.next().is_none());
        assert!(fresh_variable.name.starts_with("Ex#X"));
        assert!(matches!(
            remainder.pattern.constraints.as_slice(),
            [Predicate::Not(inner)]
                if matches!(inner.as_ref(), Predicate::Exists(variable, condition)
                    if variable == fresh_variable && condition.as_ref() == equality)
        ));
    }

    #[cfg(feature = "z3")]
    #[test]
    fn requires_definedness_unless_the_configuration_is_assumed_defined() {
        let definition = definition(
            r#"
            symbol partial{}(SortS{}) : SortS{} [function{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(X:SortS{}),
                    \top{SortS{}}()
                ),
                \dv{SortS{}}("done")
            ) [label{}("variable-match")]
            "#,
        );
        let function = internal_term(&definition, r#"partial{}(\dv{SortS{}}("value"))"#);
        let subject = Pattern {
            term: internal_term(&definition, r#"wrap{}(partial{}(\dv{SortS{}}("value")))"#),
            constraints: Vec::new(),
        };
        let solver = crate::smt::Z3Solver::new(&definition).unwrap();
        let mut fresh = 0;

        let RewriteResult::Branch {
            branches,
            remainder: Some(remainder),
            ..
        } = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver)
        else {
            panic!("partial-function binding should retain applied and undefined branches");
        };
        let [branch] = branches.as_slice() else {
            panic!("expected one conditionally defined match, found {branches:?}");
        };
        assert_eq!(
            branch.pattern.term,
            internal_term(&definition, r#"\dv{SortS{}}("done")"#)
        );
        assert_eq!(
            branch.pattern.constraints,
            [Predicate::Ceil(function.clone())]
        );
        assert_eq!(
            remainder.pattern.constraints,
            [Predicate::Not(Box::new(Predicate::Ceil(function.clone())))]
        );
        assert_eq!(
            branch.substitution.values().collect::<Vec<_>>(),
            [&function]
        );

        let mut fresh = 0;
        let RewriteResult::Finished(assumed_defined) = rewrite_step_with_mode(
            &definition,
            &subject,
            &mut fresh,
            SimplificationOptions::default(),
            &solver,
            ExecutionMode::All,
            true,
        ) else {
            panic!("the defined configuration should rewrite without a side branch");
        };
        assert_eq!(
            assumed_defined.pattern.term,
            internal_term(&definition, r#"\dv{SortS{}}("done")"#)
        );
        assert!(assumed_defined.pattern.constraints.is_empty());
    }

    #[test]
    fn simplifies_rule_conditions_with_backend_equations_before_rewriting() {
        let definition = definition(
            r#"
            sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
            symbol isZero{}(SortS{}) : SortBool{} [function{}(), total{}()]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortBool{}, R}(
                    isZero{}(\dv{SortS{}}("zero")),
                    \and{SortBool{}}(
                        \dv{SortBool{}}("true"),
                        \top{SortBool{}}()
                    )
                )
            ) [label{}("zero-is-zero"), simplification{}()]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortBool{}, R}(
                    isZero{}(\dv{SortS{}}("one")),
                    \and{SortBool{}}(
                        \dv{SortBool{}}("false"),
                        \top{SortBool{}}()
                    )
                )
            ) [label{}("one-is-not-zero"), simplification{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(X:SortS{}),
                    \equals{SortBool{}, SortS{}}(
                        isZero{}(X:SortS{}),
                        \dv{SortBool{}}("true")
                    )
                ),
                \dv{SortS{}}("high")
            ) [label{}("conditional"), priority{}("10")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                \dv{SortS{}}("fallback")
            ) [label{}("fallback"), priority{}("50")]
            "#,
        );
        let mut fresh = 0;

        assert_eq!(
            rewritten_value(rewrite_step(
                &definition,
                &subject(&definition, "zero"),
                &mut fresh,
            )),
            "high"
        );
        assert_eq!(
            rewritten_value(rewrite_step(
                &definition,
                &subject(&definition, "one"),
                &mut fresh,
            )),
            "fallback"
        );
    }

    #[test]
    fn aborts_before_lower_priorities_when_requires_are_unknown() {
        let definition = definition(
            r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(X:SortS{}),
                    \equals{SortS{}, SortS{}}(X:SortS{}, \dv{SortS{}}("zero"))
                ),
                \dv{SortS{}}("conditional")
            ) [label{}("conditional"), priority{}("10")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                \dv{SortS{}}("fallback")
            ) [label{}("fallback"), priority{}("50")]
            "#,
        );
        let syntax = parse_pattern("wrap{}(Y:SortS{})").unwrap();
        let pattern = Pattern {
            term: definition.internalize_term(&syntax, &[]).unwrap(),
            constraints: Vec::new(),
        };
        let mut fresh = 0;

        assert!(matches!(
            rewrite_step(&definition, &pattern, &mut fresh),
            RewriteResult::Indeterminate {
                reason: IndeterminateReason::Requires { rule_id, .. },
                ..
            } if rule_id == "conditional"
        ));
    }

    #[test]
    fn false_requires_prune_a_rule_even_when_matching_is_indeterminate() {
        let definition = definition(
            r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(X:SortS{}),
                    \bottom{SortS{}}()
                ),
                \dv{SortS{}}("unreachable")
            ) [label{}("false-requires")]
            "#,
        );
        let rule = definition
            .rewrite_theory
            .values()
            .flat_map(|groups| groups.values())
            .flatten()
            .next()
            .expect("rewrite rule should be indexed");
        let pattern = Pattern {
            term: rule.lhs.clone(),
            constraints: Vec::new(),
        };
        let mut fresh = 0;

        assert!(matches!(
            rewrite_step(&definition, &pattern, &mut fresh),
            RewriteResult::Stuck(_)
        ));
    }

    #[cfg(feature = "z3")]
    #[test]
    fn z3_proves_or_refutes_symbolic_requires_before_priority_fallback() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                symbol wrap{}(SortInt{}) : SortInt{} [constructor{}()]
                symbol lt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), smt-hook{}("<")]
                axiom{} \rewrites{SortInt{}}(
                    \and{SortInt{}}(
                        wrap{}(X:SortInt{}),
                        \equals{SortBool{}, SortInt{}}(
                            lt{}(X:SortInt{}, \dv{SortInt{}}("10")),
                            \dv{SortBool{}}("true")
                        )
                    ),
                    \dv{SortInt{}}("high")
                ) [label{}("high"), priority{}("10")]
                axiom{} \rewrites{SortInt{}}(
                    \and{SortInt{}}(wrap{}(X:SortInt{}), \top{SortInt{}}()),
                    \dv{SortInt{}}("fallback")
                ) [label{}("fallback"), priority{}("50")]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let solver = crate::smt::Z3Solver::new(&definition).unwrap();
        let variable = Variable::new("Y", Sort::simple("SortInt"));
        let subject = definition
            .internalize_term(&parse_pattern("wrap{}(Y:SortInt{})").unwrap(), &[])
            .unwrap();
        let integer = |value: &str| Term::domain_value(Sort::simple("SortInt"), value);
        let run = |value: &str| {
            let pattern = Pattern {
                term: subject.clone(),
                constraints: vec![Predicate::Equals(
                    Term::variable(variable.clone()),
                    integer(value),
                )],
            };
            let mut fresh = 0;
            rewritten_value(rewrite_step_with_solver(
                &definition,
                &pattern,
                &mut fresh,
                &solver,
            ))
        };

        assert_eq!(run("5"), "high");
        assert_eq!(run("15"), "fallback");
    }

    #[cfg(feature = "z3")]
    #[test]
    fn preserves_a_satisfiable_remainder_from_one_symbolic_rule() {
        let definition = symbolic_remainder_definition(
            r#"
            axiom{} \rewrites{SortInt{}}(
                \and{SortInt{}}(
                    wrap{}(X:SortInt{}),
                    \equals{SortBool{}, SortInt{}}(
                        lt{}(X:SortInt{}, \dv{SortInt{}}("0")),
                        \dv{SortBool{}}("true")
                    )
                ),
                \dv{SortInt{}}("negative")
            ) [label{}("negative")]
            "#,
        );
        let solver = crate::smt::Z3Solver::new(&definition).unwrap();
        let mut fresh = 0;

        let RewriteResult::Branch {
            branches,
            remainder: Some(remainder),
            ..
        } = rewrite_step_with_solver(
            &definition,
            &symbolic_subject(&definition),
            &mut fresh,
            &solver,
        )
        else {
            panic!("a partial symbolic rule should retain its remainder branch");
        };
        assert_eq!(branches.len(), 1);
        assert_eq!(remainder.rule_ids, ["negative"]);
        assert_eq!(remainder.pattern.term, symbolic_subject(&definition).term);
        assert!(matches!(
            remainder.pattern.constraints.as_slice(),
            [Predicate::Not(_)]
        ));
    }

    #[cfg(feature = "z3")]
    #[test]
    fn stopping_at_a_symbolic_branch_preserves_its_remainder() {
        let definition = symbolic_remainder_definition(
            r#"
            axiom{} \rewrites{SortInt{}}(
                \and{SortInt{}}(
                    wrap{}(X:SortInt{}),
                    \equals{SortBool{}, SortInt{}}(
                        lt{}(X:SortInt{}, \dv{SortInt{}}("0")),
                        \dv{SortBool{}}("true")
                    )
                ),
                \dv{SortInt{}}("negative")
            ) [label{}("negative")]
            "#,
        );
        let solver = crate::smt::Z3Solver::new(&definition).unwrap();

        let result = execute_with_solver(
            &definition,
            symbolic_subject(&definition),
            ExecutionOptions {
                branch_mode: ExecutionBranchMode::StopAtBranch,
                ..ExecutionOptions::default()
            },
            &solver,
        );

        let [
            ExecutionLeaf {
                halt_reason:
                    HaltReason::Branch {
                        branches,
                        remainder: Some(remainder),
                    },
                ..
            },
        ] = result.leaves.as_slice()
        else {
            panic!("expected an applied branch and its symbolic remainder");
        };
        assert_eq!(branches.len(), 1);
        assert_eq!(remainder.rule_ids, ["negative"]);
        assert!(matches!(
            remainder.pattern.constraints.as_slice(),
            [Predicate::Not(_)]
        ));
    }

    #[cfg(feature = "z3")]
    #[test]
    fn stopping_at_a_branch_expands_remainders_through_lower_priorities() {
        let definition = symbolic_remainder_definition(
            r#"
            axiom{} \rewrites{SortInt{}}(
                \and{SortInt{}}(
                    wrap{}(X:SortInt{}),
                    \equals{SortBool{}, SortInt{}}(
                        lt{}(X:SortInt{}, \dv{SortInt{}}("0")),
                        \dv{SortBool{}}("true")
                    )
                ),
                \dv{SortInt{}}("negative")
            ) [label{}("negative"), priority{}("10")]
            axiom{} \rewrites{SortInt{}}(
                \and{SortInt{}}(
                    wrap{}(X:SortInt{}),
                    \equals{SortBool{}, SortInt{}}(
                        lt{}(\dv{SortInt{}}("0"), X:SortInt{}),
                        \dv{SortBool{}}("true")
                    )
                ),
                \dv{SortInt{}}("positive")
            ) [label{}("positive"), priority{}("10")]
            axiom{} \rewrites{SortInt{}}(
                \and{SortInt{}}(wrap{}(X:SortInt{}), \top{SortInt{}}()),
                \dv{SortInt{}}("zero-a")
            ) [label{}("zero-a"), priority{}("50")]
            axiom{} \rewrites{SortInt{}}(
                \and{SortInt{}}(wrap{}(X:SortInt{}), \top{SortInt{}}()),
                \dv{SortInt{}}("zero-b")
            ) [label{}("zero-b"), priority{}("50")]
            "#,
        );
        let solver = crate::smt::Z3Solver::new(&definition).unwrap();

        let result = execute_with_solver(
            &definition,
            symbolic_subject(&definition),
            ExecutionOptions {
                branch_mode: ExecutionBranchMode::StopAtBranch,
                ..ExecutionOptions::default()
            },
            &solver,
        );

        let [
            ExecutionLeaf {
                halt_reason:
                    HaltReason::Branch {
                        branches,
                        remainder: None,
                    },
                ..
            },
        ] = result.leaves.as_slice()
        else {
            panic!("expected every priority branch and no uncovered remainder");
        };
        let mut labels = branches
            .iter()
            .map(|branch| branch.label.as_deref().unwrap())
            .collect::<Vec<_>>();
        labels.sort_unstable();
        assert_eq!(labels, ["negative", "positive", "zero-a", "zero-b"]);
    }

    #[cfg(feature = "z3")]
    #[test]
    fn carries_a_symbolic_remainder_to_lower_priority_rules() {
        let definition = symbolic_remainder_definition(
            r#"
            axiom{} \rewrites{SortInt{}}(
                \and{SortInt{}}(
                    wrap{}(X:SortInt{}),
                    \equals{SortBool{}, SortInt{}}(
                        lt{}(X:SortInt{}, \dv{SortInt{}}("0")),
                        \dv{SortBool{}}("true")
                    )
                ),
                \dv{SortInt{}}("negative")
            ) [label{}("negative"), priority{}("10")]
            axiom{} \rewrites{SortInt{}}(
                \and{SortInt{}}(wrap{}(X:SortInt{}), \top{SortInt{}}()),
                \dv{SortInt{}}("fallback")
            ) [label{}("fallback"), priority{}("50")]
            "#,
        );
        let solver = crate::smt::Z3Solver::new(&definition).unwrap();

        let result = execute_with_solver(
            &definition,
            symbolic_subject(&definition),
            ExecutionOptions {
                max_depth: 1,
                ..ExecutionOptions::default()
            },
            &solver,
        );

        let mut values = result
            .leaves
            .iter()
            .map(|leaf| {
                let TermKind::DomainValue { value, .. } = leaf.pattern.term.kind() else {
                    panic!(
                        "expected rewritten domain value, found {:?}",
                        leaf.pattern.term
                    );
                };
                value.to_string()
            })
            .collect::<Vec<_>>();
        values.sort();
        assert_eq!(values, ["fallback", "negative"]);
        assert!(result.leaves.iter().any(|leaf| {
            leaf.trace
                .iter()
                .any(|entry| entry.kind == TraceKind::Remainder)
        }));
    }

    #[cfg(feature = "z3")]
    #[test]
    fn narrows_a_ground_rule_fragment_over_a_symbolic_configuration() {
        let definition = symbolic_remainder_definition(
            r#"
            axiom{} \rewrites{SortInt{}}(
                \and{SortInt{}}(
                    wrap{}(\dv{SortInt{}}("0")),
                    \top{SortInt{}}()
                ),
                \dv{SortInt{}}("zero")
            ) [label{}("zero")]
            "#,
        );
        let solver = crate::smt::Z3Solver::new(&definition).unwrap();
        let subject = symbolic_subject(&definition);
        let mut fresh = 0;

        let RewriteResult::Branch {
            branches,
            remainder: Some(remainder),
            ..
        } = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver)
        else {
            panic!("ground narrowing should produce an applied and a remaining branch");
        };

        assert_eq!(branches.len(), 1);
        assert!(matches!(
            branches[0].pattern.constraints.as_slice(),
            [Predicate::Equals(left, right)]
                if matches!(left.kind(), TermKind::Variable(_))
                    && matches!(right.kind(), TermKind::DomainValue { value, .. } if value.as_ref() == "0")
        ));
        assert!(matches!(
            remainder.pattern.constraints.as_slice(),
            [Predicate::Not(inner)]
                if matches!(inner.as_ref(), Predicate::Equals(_, _))
        ));
    }

    #[cfg(feature = "z3")]
    #[test]
    fn narrows_a_constructor_pattern_with_fresh_rule_variables() {
        let definition = symbolic_remainder_definition(
            r#"
            axiom{} \rewrites{SortInt{}}(
                \and{SortInt{}}(
                    wrap{}(
                        pair{}(
                            X:SortInt{},
                            \dv{SortInt{}}("0")
                        )
                    ),
                    \top{SortInt{}}()
                ),
                X:SortInt{}
            ) [label{}("destructure")]
            "#,
        );
        let solver = crate::smt::Z3Solver::new(&definition).unwrap();
        let subject = symbolic_subject(&definition);
        let mut fresh = 0;

        let RewriteResult::Branch {
            branches,
            remainder: Some(remainder),
            ..
        } = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver)
        else {
            panic!("constructor narrowing should produce applied and complementary branches");
        };

        let [branch] = branches.as_slice() else {
            panic!("expected one applied branch, found {branches:?}");
        };
        let TermKind::Variable(result_variable) = branch.pattern.term.kind() else {
            panic!(
                "expected the fresh component variable, found {:?}",
                branch.pattern.term
            );
        };
        let [Predicate::Equals(configuration, constructor)] = branch.pattern.constraints.as_slice()
        else {
            panic!(
                "expected one narrowing equality, found {:?}",
                branch.pattern.constraints
            );
        };
        assert!(
            matches!(configuration.kind(), TermKind::Variable(variable) if variable.name.as_ref() == "X")
        );
        let TermKind::Application {
            symbol, arguments, ..
        } = constructor.kind()
        else {
            panic!("expected constructor pattern, found {constructor:?}");
        };
        assert_eq!(symbol.name.as_ref(), "pair");
        assert!(
            matches!(arguments[0].kind(), TermKind::Variable(variable) if variable == result_variable)
        );
        assert!(
            matches!(arguments[1].kind(), TermKind::DomainValue { value, .. } if value.as_ref() == "0")
        );
        assert_ne!(result_variable.name.as_ref(), "Rule#X");
        let first_name = result_variable.name.clone();
        assert_eq!(fresh, 1);
        let [Predicate::Not(remainder_condition)] = remainder.pattern.constraints.as_slice() else {
            panic!(
                "expected a negated remainder, found {:?}",
                remainder.pattern.constraints
            );
        };
        let Predicate::Exists(remainder_variable, remainder_condition) =
            remainder_condition.as_ref()
        else {
            panic!("fresh narrowing variables must be existential in the remainder");
        };
        assert_eq!(remainder_variable, result_variable);
        assert_eq!(
            remainder_condition.as_ref(),
            &Predicate::Equals(configuration.clone(), constructor.clone())
        );

        let RewriteResult::Branch {
            branches: second, ..
        } = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver)
        else {
            panic!("repeated constructor narrowing should still apply");
        };
        assert!(matches!(
            second[0].pattern.term.kind(),
            TermKind::Variable(variable) if variable.name != first_name
        ));
        assert_eq!(fresh, 2);
    }

    #[cfg(feature = "z3")]
    #[test]
    fn narrows_a_function_pattern_with_a_definedness_condition() {
        let definition = symbolic_remainder_definition(
            r#"
            axiom{} \rewrites{SortInt{}}(
                \and{SortInt{}}(
                    wrap{}(partial{}(X:SortInt{})),
                    \top{SortInt{}}()
                ),
                X:SortInt{}
            ) [label{}("partial-destructure")]
            "#,
        );
        let solver = crate::smt::Z3Solver::new(&definition).unwrap();
        let subject = symbolic_subject(&definition);
        let mut fresh = 0;

        let RewriteResult::Branch {
            branches,
            remainder: Some(remainder),
            ..
        } = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver)
        else {
            panic!("functional narrowing should produce applied and complementary branches");
        };

        let [branch] = branches.as_slice() else {
            panic!("expected one applied branch, found {branches:?}");
        };
        let TermKind::Variable(result_variable) = branch.pattern.term.kind() else {
            panic!(
                "expected a fresh function argument, found {:?}",
                branch.pattern.term
            );
        };
        assert!(result_variable.name.starts_with("Ex#"));
        let [
            Predicate::Equals(configuration, function),
            Predicate::Ceil(defined),
        ] = branch.pattern.constraints.as_slice()
        else {
            panic!(
                "expected equality and definedness, found {:?}",
                branch.pattern.constraints
            );
        };
        assert_eq!(function, defined);
        assert!(
            matches!(configuration.kind(), TermKind::Variable(variable) if variable.name.as_ref() == "X")
        );
        assert!(matches!(
            function.kind(),
            TermKind::Application { symbol, arguments, .. }
                if symbol.name.as_ref() == "partial"
                    && matches!(arguments[0].kind(), TermKind::Variable(variable) if variable == result_variable)
        ));

        let [Predicate::Not(remainder_condition)] = remainder.pattern.constraints.as_slice() else {
            panic!("expected a negated complementary condition");
        };
        assert!(matches!(
            remainder_condition.as_ref(),
            Predicate::Exists(variable, body)
                if variable == result_variable
                    && matches!(body.as_ref(), Predicate::And(predicates) if predicates == branch.pattern.constraints.as_slice())
        ));
    }

    #[cfg(feature = "z3")]
    #[test]
    fn branches_only_after_complementary_rules_make_the_remainder_unsatisfiable() {
        let definition = symbolic_remainder_definition(
            r#"
            axiom{} \rewrites{SortInt{}}(
                \and{SortInt{}}(
                    wrap{}(X:SortInt{}),
                    \equals{SortBool{}, SortInt{}}(
                        lt{}(X:SortInt{}, \dv{SortInt{}}("0")),
                        \dv{SortBool{}}("true")
                    )
                ),
                \dv{SortInt{}}("negative")
            ) [label{}("negative")]
            axiom{} \rewrites{SortInt{}}(
                \and{SortInt{}}(
                    wrap{}(X:SortInt{}),
                    \equals{SortBool{}, SortInt{}}(
                        lt{}(X:SortInt{}, \dv{SortInt{}}("0")),
                        \dv{SortBool{}}("false")
                    )
                ),
                \dv{SortInt{}}("nonnegative")
            ) [label{}("nonnegative")]
            "#,
        );
        let solver = crate::smt::Z3Solver::new(&definition).unwrap();
        let mut fresh = 0;

        let RewriteResult::Branch { branches, .. } = rewrite_step_with_solver(
            &definition,
            &symbolic_subject(&definition),
            &mut fresh,
            &solver,
        ) else {
            panic!("complementary rules should form a complete branch");
        };
        assert_eq!(
            branches
                .iter()
                .map(|branch| branch.label.as_deref().unwrap())
                .collect::<Vec<_>>(),
            ["negative", "nonnegative"]
        );
        assert!(
            branches
                .iter()
                .all(|branch| branch.pattern.constraints.len() == 1)
        );
    }

    #[test]
    fn branches_when_multiple_rules_in_one_priority_apply() {
        let definition = definition(
            r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                \dv{SortS{}}("left")
            ) [label{}("left")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                \dv{SortS{}}("right")
            ) [label{}("right")]
            "#,
        );
        let mut fresh = 0;

        let RewriteResult::Branch { branches, .. } =
            rewrite_step(&definition, &subject(&definition, "value"), &mut fresh)
        else {
            panic!("both rules should branch");
        };
        assert_eq!(
            branches
                .iter()
                .map(|branch| branch.label.as_deref().unwrap())
                .collect::<Vec<_>>(),
            vec!["left", "right"]
        );
    }

    #[test]
    fn freshens_existentials_against_the_current_pattern() {
        let definition = definition(
            r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                \exists{SortS{}}(Y:SortS{}, wrap{}(Y:SortS{}))
            ) [label{}("fresh")]
            "#,
        );
        let pattern = subject(&definition, "value");
        let mut fresh = 0;
        let first = rewrite_step(&definition, &pattern, &mut fresh);
        let first_name = match &first {
            RewriteResult::Finished(applied) => applied
                .pattern
                .term
                .attributes()
                .variables
                .iter()
                .next()
                .unwrap()
                .name
                .clone(),
            _ => panic!("rule should apply"),
        };
        assert_eq!(first_name.as_ref(), "Y");

        let RewriteResult::Finished(first) = first else {
            unreachable!();
        };
        let second = rewrite_step(&definition, &first.pattern, &mut fresh);
        let second_name = match second {
            RewriteResult::Finished(applied) => {
                let variables = &applied.pattern.term.attributes().variables;
                assert_eq!(variables.len(), 1);
                variables.iter().next().unwrap().name.clone()
            }
            _ => panic!("rule should apply again"),
        };
        assert_eq!(second_name.as_ref(), "Y0");

        let repeated = rewrite_step(&definition, &pattern, &mut fresh);
        let repeated_name = match repeated {
            RewriteResult::Finished(applied) => {
                let variables = &applied.pattern.term.attributes().variables;
                assert_eq!(variables.len(), 1);
                variables.iter().next().unwrap().name.clone()
            }
            _ => panic!("rule should apply to the original pattern again"),
        };
        assert_eq!(repeated_name, first_name);
    }

    #[test]
    fn executes_to_a_stuck_normal_form_and_records_the_trace() {
        let definition = definition(
            r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(\dv{SortS{}}("zero")), \top{SortS{}}()),
                wrap{}(\dv{SortS{}}("one"))
            ) [label{}("first")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(\dv{SortS{}}("one")), \top{SortS{}}()),
                \dv{SortS{}}("done")
            ) [label{}("second")]
            "#,
        );

        let result = execute(
            &definition,
            subject(&definition, "zero"),
            ExecutionOptions::default(),
        );
        assert_eq!(result.leaves.len(), 1);
        let leaf = &result.leaves[0];
        assert_eq!(leaf.depth, 2);
        assert_eq!(leaf.halt_reason, HaltReason::Stuck);
        assert_eq!(
            leaf.trace
                .iter()
                .map(|entry| (entry.depth, entry.label.as_deref().unwrap()))
                .collect::<Vec<_>>(),
            vec![(1, "first"), (2, "second")]
        );
        assert!(matches!(
            leaf.pattern.term.kind(),
            TermKind::DomainValue { value, .. } if value.as_ref() == "done"
        ));
    }

    fn assert_iteration_limit(reason: &HaltReason) {
        assert!(matches!(
            reason,
            HaltReason::Simplification(
                SimplificationError::IterationLimit { .. }
                    | SimplificationError::PredicateIterationLimit { .. }
            )
        ));
    }

    fn long_requires_chain() -> String {
        let mut theory = String::new();
        for index in 0..=128 {
            theory.push_str(&format!(
                "symbol chain{index}{{}}() : SortS{{}} [function{{}}()]\n"
            ));
        }
        for index in 0..128 {
            let next = index + 1;
            theory.push_str(&format!(
                r#"
                axiom{{R}} \implies{{R}}(
                    \top{{R}}(),
                    \equals{{SortS{{}}, R}}(
                        chain{index}{{}}(),
                        \and{{SortS{{}}}}(chain{next}{{}}(), \top{{SortS{{}}}}())
                    )
                ) [label{{}}("chain-{index}"), simplification{{}}()]
                "#
            ));
        }
        theory.push_str(
            r#"
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    chain128{}(),
                    \and{SortS{}}(\dv{SortS{}}("done"), \top{SortS{}}())
                )
            ) [label{}("chain-done"), simplification{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(X:SortS{}),
                    \equals{SortS{}, SortS{}}(
                        chain0{}(),
                        \dv{SortS{}}("done")
                    )
                ),
                \dv{SortS{}}("rewritten")
            ) [label{}("conditional")]
            "#,
        );
        theory
    }

    #[test]
    fn execution_reports_default_budget_exhaustion_as_a_simplification_leaf() {
        let definition = definition(&long_requires_chain());
        let result = execute(
            &definition,
            subject(&definition, "value"),
            ExecutionOptions::default(),
        );

        let [leaf] = result.leaves.as_slice() else {
            panic!(
                "expected one exhausted execution leaf, found {:?}",
                result.leaves
            );
        };
        assert_iteration_limit(&leaf.halt_reason);
    }

    #[test]
    fn rule_requires_simplification_failure_halts_execution() {
        let definition = definition(
            r#"
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
                    wrap{}(X:SortS{}),
                    \equals{SortS{}, SortS{}}(
                        expand{}(X:SortS{}),
                        X:SortS{}
                    )
                ),
                \dv{SortS{}}("done")
            ) [label{}("conditional")]
            "#,
        );

        let result = execute(
            &definition,
            subject(&definition, "value"),
            ExecutionOptions {
                max_simplification_iterations: 1,
                ..ExecutionOptions::default()
            },
        );

        let [leaf] = result.leaves.as_slice() else {
            panic!(
                "expected one failed rule attempt, found {:?}",
                result.leaves
            );
        };
        assert_iteration_limit(&leaf.halt_reason);
    }

    #[test]
    fn terminal_rule_result_simplification_failure_halts_execution() {
        let definition = definition(
            r#"
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
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                expand{}(X:SortS{})
            ) [label{}("stop")]
            "#,
        );

        let result = execute(
            &definition,
            subject(&definition, "value"),
            ExecutionOptions {
                max_simplification_iterations: 1,
                terminal_rules: BTreeSet::from(["stop".into()]),
                ..ExecutionOptions::default()
            },
        );

        let [leaf] = result.leaves.as_slice() else {
            panic!(
                "expected one failed terminal result, found {:?}",
                result.leaves
            );
        };
        assert_iteration_limit(&leaf.halt_reason);
    }

    #[test]
    fn stopped_branch_simplification_failure_is_recorded_at_the_branch_point() {
        let definition = definition(
            r#"
            symbol expand{}(SortS{}) : SortS{} [function{}(), total{}()]
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
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                \dv{SortS{}}("left")
            ) [label{}("left")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                expand{}(X:SortS{})
            ) [label{}("middle")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                \dv{SortS{}}("right")
            ) [label{}("right")]
            "#,
        );
        let initial = subject(&definition, "value");

        let result = execute(
            &definition,
            initial.clone(),
            ExecutionOptions {
                branch_mode: ExecutionBranchMode::StopAtBranch,
                max_simplification_iterations: 1,
                ..ExecutionOptions::default()
            },
        );

        // The failure belongs to the branch point itself: a leaf for the failing successor
        // alone would lose the `left` and `right` successors that remain reachable.
        let [leaf] = result.leaves.as_slice() else {
            panic!("expected one branch-point leaf, found {:?}", result.leaves);
        };
        assert_eq!(leaf.depth, 0);
        assert_eq!(leaf.pattern, initial);
        assert_iteration_limit(&leaf.halt_reason);
    }

    #[test]
    fn execution_preserves_user_log_effects() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortString{} [hasDomainValues{}()]
                sort SortK{} []
                symbol dotk{}() : SortK{} [constructor{}()]
                symbol log{}(SortString{}) : SortK{}
                    [function{}(), total{}(), hook{}("IO.logString")]
            endmodule []"#,
        )
        .unwrap();
        let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
        let initial = definition
            .internalize_term(
                &parse_pattern(r#"log{}(\dv{SortString{}}("one line"))"#).unwrap(),
                &[],
            )
            .unwrap();

        let result = execute(
            &definition,
            Pattern {
                term: initial,
                constraints: Vec::new(),
            },
            ExecutionOptions::default(),
        );

        assert_eq!(result.effects, [BuiltinEffect::UserLog("one line".into())]);
        assert!(matches!(
            result.leaves[0].pattern.term.kind(),
            TermKind::Application { symbol, .. } if symbol.name.as_ref() == "dotk"
        ));
    }

    #[test]
    fn builtin_effect_observer_is_observational() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortString{} [hasDomainValues{}()]
                sort SortK{} []
                symbol dotk{}() : SortK{} [constructor{}()]
                symbol log{}(SortString{}) : SortK{}
                    [function{}(), total{}(), hook{}("IO.logString")]
            endmodule []"#,
        )
        .unwrap();
        let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
        let initial = Pattern {
            term: definition
                .internalize_term(
                    &parse_pattern(r#"log{}(\dv{SortString{}}("one line"))"#).unwrap(),
                    &[],
                )
                .unwrap(),
            constraints: Vec::new(),
        };
        let expected = execute(&definition, initial.clone(), ExecutionOptions::default());
        let mut observed = Vec::new();
        let actual = execute_with_solver_and_observer(
            &definition,
            initial,
            ExecutionOptions::default(),
            &NoSolver,
            |effect| observed.push(effect.clone()),
        );

        assert_eq!(actual, expected);
        assert_eq!(observed, actual.effects);
    }

    #[test]
    fn execution_interrupts_native_hooks_at_the_step_deadline() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                sort SortState{} []
                symbol pow{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), total{}(), hook{}("INT.pow")]
                symbol state{}(SortInt{}) : SortState{} [constructor{}()]
            endmodule []"#,
        )
        .unwrap();
        let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
        let initial = definition
            .internalize_pattern(
                &parse_pattern(r#"state{}(pow{}(\dv{SortInt{}}("2"), \dv{SortInt{}}("10")))"#)
                    .unwrap(),
                &[],
            )
            .unwrap();

        let result = execute(
            &definition,
            initial,
            ExecutionOptions {
                step_timeout: Some(Duration::ZERO),
                ..ExecutionOptions::default()
            },
        );

        assert!(matches!(
            result.leaves.as_slice(),
            [ExecutionLeaf {
                halt_reason: HaltReason::Timeout(StepTimeoutMode::Manual(timeout)),
                ..
            }] if timeout.is_zero()
        ));
    }

    #[test]
    fn execution_stops_before_work_when_the_request_is_cancelled() {
        let definition = definition("");
        let initial = subject(&definition, "zero");
        let token = CancellationToken::new();
        token.cancel();

        let result =
            token.scope(|| execute(&definition, initial.clone(), ExecutionOptions::default()));

        assert_eq!(
            result.leaves,
            [ExecutionLeaf {
                pattern: initial,
                depth: 0,
                trace: Vec::new(),
                branch: Vec::new(),
                observations: Vec::new(),
                halt_reason: HaltReason::Cancelled,
            }]
        );
    }

    #[test]
    fn stops_exactly_at_the_requested_depth_bound() {
        let definition = definition(
            r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                wrap{}(X:SortS{})
            ) [label{}("loop")]
            "#,
        );

        let result = execute(
            &definition,
            subject(&definition, "value"),
            ExecutionOptions {
                max_depth: 3,
                ..ExecutionOptions::default()
            },
        );
        assert_eq!(result.leaves.len(), 1);
        assert_eq!(result.leaves[0].depth, 3);
        assert_eq!(result.leaves[0].trace.len(), 3);
        assert_eq!(result.leaves[0].halt_reason, HaltReason::DepthBound);
    }

    fn stop_rule_definition() -> BackendDefinition {
        definition(
            r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(\dv{SortS{}}("start")),
                    \top{SortS{}}()
                ),
                wrap{}(\dv{SortS{}}("middle"))
            ) [label{}("first")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(\dv{SortS{}}("middle")),
                    \top{SortS{}}()
                ),
                \dv{SortS{}}("done")
            ) [label{}("stop")]
            "#,
        )
    }

    #[test]
    fn stops_before_applying_a_cut_point_rule() {
        let definition = stop_rule_definition();
        let result = execute(
            &definition,
            subject(&definition, "start"),
            ExecutionOptions {
                cut_point_rules: BTreeSet::from(["stop".into()]),
                ..ExecutionOptions::default()
            },
        );

        let [leaf] = result.leaves.as_slice() else {
            panic!("expected one cut-point leaf, found {:?}", result.leaves);
        };
        assert_eq!(leaf.depth, 1);
        assert_eq!(leaf.pattern, subject(&definition, "middle"));
        assert_eq!(leaf.trace.len(), 1);
        let HaltReason::CutPointRule { rule, next_states } = &leaf.halt_reason else {
            panic!("expected a cut-point halt, found {:?}", leaf.halt_reason);
        };
        assert_eq!(rule, "stop");
        assert_eq!(next_states.len(), 1);
        assert_eq!(
            next_states[0].pattern.term,
            internal_term(&definition, r#"\dv{SortS{}}("done")"#)
        );
    }

    #[test]
    fn stops_after_applying_a_terminal_rule() {
        let definition = stop_rule_definition();
        let result = execute(
            &definition,
            subject(&definition, "start"),
            ExecutionOptions {
                terminal_rules: BTreeSet::from(["stop".into()]),
                ..ExecutionOptions::default()
            },
        );

        let [leaf] = result.leaves.as_slice() else {
            panic!("expected one terminal leaf, found {:?}", result.leaves);
        };
        assert_eq!(leaf.depth, 2);
        assert_eq!(
            leaf.pattern.term,
            internal_term(&definition, r#"\dv{SortS{}}("done")"#)
        );
        assert_eq!(leaf.trace.len(), 2);
        assert_eq!(
            leaf.halt_reason,
            HaltReason::TerminalRule {
                rule: "stop".into()
            }
        );
    }

    fn unconditional_branch_definition() -> BackendDefinition {
        definition(
            r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                \dv{SortS{}}("left")
            ) [label{}("left")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                \dv{SortS{}}("right")
            ) [label{}("right")]
            "#,
        )
    }

    #[test]
    fn observation_filter_installation_is_atomic() {
        let definition = unconditional_branch_definition();

        assert_eq!(
            ObservationOptions::with_rules(&definition, ["left", "missing"]),
            Err(ObservationFilterError::UnknownRule("missing".into()))
        );
        assert!(ObservationOptions::with_rules(&definition, ["left", "right"]).is_ok());
    }

    #[test]
    fn single_rewrite_emits_one_committed_observation() {
        let definition = definition(
            r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                \dv{SortS{}}("done")
            ) [label{}("step")]
            "#,
        );
        let before = subject(&definition, "value");
        let result = execute_observed(
            &definition,
            before.clone(),
            ExecutionOptions::default(),
            &ObservationOptions::all(),
        );

        let [leaf] = result.leaves.as_slice() else {
            panic!("expected one execution leaf");
        };
        let [ObservationEvent::Transition(observation)] = leaf.observations.as_slice() else {
            panic!(
                "expected one committed observation: {:?}",
                leaf.observations
            );
        };
        assert_eq!(observation.class, TransitionClass::Rewrite);
        assert_eq!(observation.id.rule, "step");
        assert_eq!(observation.id.target, PatternDigest::of(&observation.after));
        assert_eq!(observation.rule_label.as_deref(), Some("step"));
        assert_eq!(observation.bindings.len(), 1);
        assert!(observation.introduced_predicates.is_empty());
        assert_eq!(observation.before, before);
        assert_eq!(observation.after, leaf.pattern);
        assert!(observation.effects.is_empty());
    }

    #[test]
    fn stops_at_a_rewrite_branch_when_requested() {
        let definition = unconditional_branch_definition();
        let initial = subject(&definition, "value");

        let result = execute(
            &definition,
            initial.clone(),
            ExecutionOptions {
                branch_mode: ExecutionBranchMode::StopAtBranch,
                ..ExecutionOptions::default()
            },
        );

        assert_eq!(result.leaves.len(), 1);
        assert_eq!(result.leaves[0].pattern, initial);
        assert_eq!(result.leaves[0].depth, 0);
        let HaltReason::Branch {
            branches,
            remainder,
        } = &result.leaves[0].halt_reason
        else {
            panic!("expected an unconditional branch point");
        };
        assert_eq!(branches.len(), 2);
        assert!(remainder.is_none());
    }

    #[test]
    fn stopped_branch_retains_effects_from_every_reported_successor() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortString{} [hasDomainValues{}()]
                sort SortK{} []
                symbol initial{}() : SortK{} [constructor{}()]
                symbol dotk{}() : SortK{} [constructor{}()]
                symbol log{}(SortString{}) : SortK{}
                    [function{}(), hook{}("IO.logString")]
                axiom{} \rewrites{SortK{}}(
                    \and{SortK{}}(initial{}(), \top{SortK{}}()),
                    log{}(\dv{SortString{}}("left"))
                ) [label{}("left")]
                axiom{} \rewrites{SortK{}}(
                    \and{SortK{}}(initial{}(), \top{SortK{}}()),
                    log{}(\dv{SortString{}}("right"))
                ) [label{}("right")]
            endmodule []"#,
        )
        .unwrap();
        let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
        let initial = definition
            .internalize_pattern(&parse_pattern("initial{}()").unwrap(), &[])
            .unwrap();

        let mut observed = Vec::new();
        let result = execute_with_solver_and_observer(
            &definition,
            initial,
            ExecutionOptions {
                branch_mode: ExecutionBranchMode::StopAtBranch,
                ..ExecutionOptions::default()
            },
            &NoSolver,
            |effect| observed.push(effect.clone()),
        );

        assert!(matches!(
            result.leaves[0].halt_reason,
            HaltReason::Branch { .. }
        ));
        assert_eq!(
            result.effects,
            [
                BuiltinEffect::UserLog("left".into()),
                BuiltinEffect::UserLog("right".into()),
            ]
        );
        assert_eq!(observed, result.effects);
    }

    #[test]
    fn normalizes_branch_payloads_before_reporting_branching() {
        let definition = definition(
            r#"
            symbol identity{}(SortS{}) : SortS{} [function{}(), total{}()]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    identity{}(X:SortS{}),
                    \and{SortS{}}(X:SortS{}, \top{SortS{}}())
                )
            ) [label{}("identity"), simplification{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                identity{}(\dv{SortS{}}("left"))
            ) [label{}("left")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                identity{}(\dv{SortS{}}("right"))
            ) [label{}("right")]
            "#,
        );

        let result = execute(
            &definition,
            subject(&definition, "value"),
            ExecutionOptions {
                branch_mode: ExecutionBranchMode::StopAtBranch,
                ..ExecutionOptions::default()
            },
        );

        let HaltReason::Branch { branches, .. } = &result.leaves[0].halt_reason else {
            panic!("expected a normalized branch point");
        };
        assert_eq!(
            branches
                .iter()
                .map(|branch| match branch.pattern.term.kind() {
                    TermKind::DomainValue { value, .. } => value.as_ref(),
                    other => panic!("branch payload was not normalized: {other:?}"),
                })
                .collect::<Vec<_>>(),
            vec!["left", "right"]
        );
    }

    #[test]
    fn continues_after_result_simplification_prunes_to_one_branch() {
        let definition = definition(
            r#"
            symbol dead{}(SortS{}) : SortS{} [function{}(), total{}()]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    dead{}(X:SortS{}),
                    \and{SortS{}}(
                        \dv{SortS{}}("dead"),
                        \bottom{SortS{}}()
                    )
                )
            ) [label{}("dead"), simplification{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                dead{}(\dv{SortS{}}("left"))
            ) [label{}("left")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                \dv{SortS{}}("right")
            ) [label{}("right")]
            "#,
        );

        let result = execute(
            &definition,
            subject(&definition, "value"),
            ExecutionOptions {
                branch_mode: ExecutionBranchMode::StopAtBranch,
                ..ExecutionOptions::default()
            },
        );

        let [leaf] = result.leaves.as_slice() else {
            panic!("expected the one viable branch to continue");
        };
        assert_eq!(leaf.depth, 1);
        assert_eq!(leaf.halt_reason, HaltReason::Stuck);
        assert_eq!(
            leaf.pattern.term,
            internal_term(&definition, r#"\dv{SortS{}}("right")"#)
        );
    }

    #[test]
    fn explores_each_rewrite_branch_by_default() {
        let definition = unconditional_branch_definition();

        let result = execute(
            &definition,
            subject(&definition, "value"),
            ExecutionOptions::default(),
        );
        assert_eq!(result.leaves.len(), 2);
        assert!(
            result
                .leaves
                .iter()
                .all(|leaf| leaf.depth == 1 && leaf.halt_reason == HaltReason::Stuck)
        );
        assert_eq!(
            result
                .leaves
                .iter()
                .map(|leaf| leaf.trace[0].label.as_deref().unwrap())
                .collect::<Vec<_>>(),
            vec!["left", "right"]
        );
    }

    #[test]
    fn breadth_bound_returns_the_live_execution_frontier() {
        let definition = unconditional_branch_definition();

        let result = execute(
            &definition,
            subject(&definition, "value"),
            ExecutionOptions {
                max_breadth: Some(1),
                ..ExecutionOptions::default()
            },
        );

        assert_eq!(result.leaves.len(), 2);
        assert!(
            result
                .leaves
                .iter()
                .all(|leaf| leaf.depth == 1 && leaf.halt_reason == HaltReason::BreadthBound)
        );
        assert_eq!(
            result
                .leaves
                .iter()
                .map(|leaf| match leaf.pattern.term.kind() {
                    TermKind::DomainValue { value, .. } => value.as_ref(),
                    other => panic!("expected a domain value, found {other:?}"),
                })
                .collect::<Vec<_>>(),
            vec!["left", "right"]
        );
    }

    #[test]
    fn zero_breadth_returns_the_initial_configuration() {
        let definition = unconditional_branch_definition();
        let initial = subject(&definition, "value");

        let result = execute(
            &definition,
            initial.clone(),
            ExecutionOptions {
                max_breadth: Some(0),
                ..ExecutionOptions::default()
            },
        );

        assert_eq!(result.leaves.len(), 1);
        assert_eq!(result.leaves[0].pattern, initial);
        assert_eq!(result.leaves[0].halt_reason, HaltReason::BreadthBound);
    }

    #[test]
    fn any_mode_uses_the_first_applicable_rule() {
        let definition = unconditional_branch_definition();

        let result = execute(
            &definition,
            subject(&definition, "value"),
            ExecutionOptions {
                mode: ExecutionMode::Any,
                ..ExecutionOptions::default()
            },
        );

        assert_eq!(result.leaves.len(), 1);
        assert_eq!(result.leaves[0].depth, 1);
        assert!(matches!(
            result.leaves[0].pattern.term.kind(),
            TermKind::DomainValue { value, .. } if value.as_ref() == "left"
        ));
        assert_eq!(result.leaves[0].trace[0].label.as_deref(), Some("left"));
    }

    #[cfg(feature = "z3")]
    #[test]
    fn any_mode_passes_only_the_first_rules_remainder_to_later_rules() {
        let definition = definition(
            r#"
            symbol fallback{}(SortS{}) : SortS{} [constructor{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(\dv{SortS{}}("a")),
                    \top{SortS{}}()
                ),
                \dv{SortS{}}("first")
            ) [label{}("specific")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                fallback{}(X:SortS{})
            ) [label{}("fallback")]
            "#,
        );
        let solver = crate::smt::Z3Solver::new(&definition).unwrap();
        let result = execute_with_solver(
            &definition,
            Pattern {
                term: internal_term(&definition, "wrap{}(Y:SortS{})"),
                constraints: Vec::new(),
            },
            ExecutionOptions {
                mode: ExecutionMode::Any,
                ..ExecutionOptions::default()
            },
            &solver,
        );

        assert_eq!(result.leaves.len(), 2);
        let specific = result
            .leaves
            .iter()
            .find(|leaf| {
                matches!(
                    leaf.pattern.term.kind(),
                    TermKind::DomainValue { value, .. } if value.as_ref() == "first"
                )
            })
            .expect("the first rule should own its matching branch");
        let fallback = result
            .leaves
            .iter()
            .find(|leaf| {
                matches!(
                    leaf.pattern.term.kind(),
                    TermKind::Application { symbol, .. } if symbol.name.as_ref() == "fallback"
                )
            })
            .expect("the later rule should receive the first rule's remainder");
        assert!(!specific.pattern.constraints.is_empty());
        assert!(
            fallback
                .pattern
                .constraints
                .iter()
                .any(|predicate| matches!(predicate, Predicate::Not(_)))
        );
    }

    #[test]
    fn rewrites_through_matching_injective_function_heads() {
        let definition = definition(
            r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(injectiveFunction{}(X:SortS{})),
                    \top{SortS{}}()
                ),
                wrap{}(X:SortS{})
            ) [label{}("injective-match")]
            "#,
        );
        let value = r#"\dv{SortS{}}("value")"#;
        let subject = Pattern {
            term: internal_term(
                &definition,
                &format!("wrap{{}}(injectiveFunction{{}}({value}))"),
            ),
            constraints: Vec::new(),
        };
        let mut fresh = 0;

        let RewriteResult::Finished(applied) = rewrite_step(&definition, &subject, &mut fresh)
        else {
            panic!("injective heads should decompose during rewrite matching");
        };

        assert_eq!(
            applied.pattern.term,
            internal_term(&definition, &format!("wrap{{}}({value})"))
        );
        assert!(applied.pattern.constraints.is_empty());
    }

    #[test]
    fn rewrites_through_a_direct_symbol_overload() {
        let definition = overload_rewrite_definition();
        let value = r#"\dv{SortSub{}}("value")"#;
        let subject = Pattern {
            term: internal_term(
                &definition,
                &format!("overloadState{{}}(inj{{SortSub{{}}, SortTop{{}}}}(lower{{}}({value})))"),
            ),
            constraints: Vec::new(),
        };
        let mut fresh = 0;

        let RewriteResult::Finished(applied) = rewrite_step(&definition, &subject, &mut fresh)
        else {
            panic!("directly overloaded constructors should match during rewriting");
        };

        assert_eq!(
            applied.pattern.term,
            internal_term(
                &definition,
                &format!("overloadResult{{}}(inj{{SortSub{{}}, SortTop{{}}}}({value}))"),
            )
        );
        assert!(applied.pattern.constraints.is_empty());
    }

    #[cfg(feature = "z3")]
    #[test]
    fn narrows_an_injected_variable_to_a_lesser_overload() {
        let definition = overload_rewrite_definition();
        let subject = Pattern {
            term: internal_term(
                &definition,
                "overloadState{}(inj{SortSub{}, SortTop{}}(CONFIG:SortSub{}))",
            ),
            constraints: Vec::new(),
        };
        let solver = crate::smt::Z3Solver::new(&definition).unwrap();
        let mut fresh = 0;

        let RewriteResult::Branch {
            branches,
            remainder: Some(remainder),
            ..
        } = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver)
        else {
            panic!("overload narrowing should retain applied and complementary branches");
        };
        let [branch] = branches.as_slice() else {
            panic!("expected one overload narrowing branch, found {branches:?}");
        };
        let TermKind::Application { arguments, .. } = branch.pattern.term.kind() else {
            panic!("expected the overload result constructor");
        };
        let TermKind::Injection { term: result, .. } = arguments[0].kind() else {
            panic!("the narrowed argument should remain injected to SortTop");
        };
        let TermKind::Variable(fresh_variable) = result.kind() else {
            panic!("the lesser overload argument should be fresh");
        };
        assert!(fresh_variable.name.starts_with("Ex#Overload0"));
        let [Predicate::Equals(configuration, value)] = branch.pattern.constraints.as_slice()
        else {
            panic!("expected the overload narrowing equality");
        };
        assert!(matches!(
            configuration.kind(),
            TermKind::Variable(variable) if variable.name.as_ref() == "CONFIG"
        ));
        assert!(matches!(
            value.kind(),
            TermKind::Application { symbol, arguments, .. }
                if symbol.name.as_ref() == "lower"
                    && matches!(arguments[0].kind(), TermKind::Variable(variable) if variable == fresh_variable)
        ));
        let [Predicate::Not(remainder_condition)] = remainder.pattern.constraints.as_slice() else {
            panic!("expected a negated complementary condition");
        };
        assert!(matches!(
            remainder_condition.as_ref(),
            Predicate::Exists(variable, equality)
                if variable == fresh_variable
                    && equality.as_ref() == &branch.pattern.constraints[0]
        ));
    }

    #[test]
    fn unifies_kequal_operands_when_matching_true() {
        let definition =
            kequal_rewrite_definition("state{}(equal{}(VALUE:SortValue{}, chosen{}()))");
        let subject = Pattern {
            term: internal_term(&definition, r#"state{}(\dv{SortBool{}}("true"))"#),
            constraints: Vec::new(),
        };
        let mut fresh = 0;

        let RewriteResult::Finished(applied) = rewrite_step(&definition, &subject, &mut fresh)
        else {
            panic!("true K equality should unify its operands");
        };
        assert_eq!(applied.pattern.term, internal_term(&definition, "done{}()"));
        assert!(applied.pattern.constraints.is_empty());
        assert!(applied.substitution.iter().any(|(variable, value)| {
            variable.name.ends_with("VALUE") && value == &internal_term(&definition, "chosen{}()")
        }));
    }

    #[test]
    fn unifies_integer_equality_operands_when_matching_true() {
        let definition = scalar_equality_rewrite_definition("INT.eq", "SortInt", "INT.Int");
        let subject = Pattern {
            term: internal_term(&definition, r#"state{}(\dv{SortBool{}}("true"))"#),
            constraints: Vec::new(),
        };
        let mut fresh = 0;

        let RewriteResult::Finished(applied) = rewrite_step(&definition, &subject, &mut fresh)
        else {
            panic!("true integer equality should unify its operands");
        };
        assert!(applied.substitution.iter().any(|(variable, value)| {
            variable.name.ends_with("VALUE") && value == &internal_term(&definition, "value{}()")
        }));
    }

    #[test]
    fn unifies_string_equality_operands_when_matching_true() {
        let definition =
            scalar_equality_rewrite_definition("STRING.eq", "SortString", "STRING.String");
        let subject = Pattern {
            term: internal_term(&definition, r#"state{}(\dv{SortBool{}}("true"))"#),
            constraints: Vec::new(),
        };
        let mut fresh = 0;

        let RewriteResult::Finished(applied) = rewrite_step(&definition, &subject, &mut fresh)
        else {
            panic!("true string equality should unify its operands");
        };
        assert!(applied.substitution.iter().any(|(variable, value)| {
            variable.name.ends_with("VALUE") && value == &internal_term(&definition, "value{}()")
        }));
    }

    #[test]
    fn unifies_both_conjunction_operands_when_matching_true() {
        let definition =
            boolean_rewrite_definition("state{}(and{}(LEFT:SortBool{}, RIGHT:SortBool{}))");
        let subject = Pattern {
            term: internal_term(&definition, r#"state{}(\dv{SortBool{}}("true"))"#),
            constraints: Vec::new(),
        };
        let mut fresh = 0;

        let RewriteResult::Finished(applied) = rewrite_step(&definition, &subject, &mut fresh)
        else {
            panic!("true conjunction should bind both operands to true");
        };
        assert_eq!(applied.substitution.len(), 2);
        assert!(applied.substitution.iter().all(|(variable, value)| {
            (variable.name.ends_with("LEFT") || variable.name.ends_with("RIGHT"))
                && value == &Term::domain_value(Sort::simple("SortBool"), "true")
        }));
    }

    #[test]
    fn unifies_both_disjunction_operands_when_matching_false() {
        let definition =
            boolean_rewrite_definition("state{}(or{}(LEFT:SortBool{}, RIGHT:SortBool{}))");
        let subject = Pattern {
            term: internal_term(&definition, r#"state{}(\dv{SortBool{}}("false"))"#),
            constraints: Vec::new(),
        };
        let mut fresh = 0;

        let RewriteResult::Finished(applied) = rewrite_step(&definition, &subject, &mut fresh)
        else {
            panic!("false disjunction should bind both operands to false");
        };
        assert_eq!(applied.substitution.len(), 2);
        assert!(applied.substitution.iter().all(|(variable, value)| {
            (variable.name.ends_with("LEFT") || variable.name.ends_with("RIGHT"))
                && value == &Term::domain_value(Sort::simple("SortBool"), "false")
        }));
    }

    #[test]
    fn unifies_negation_operand_with_the_opposite_boolean() {
        let definition = boolean_rewrite_definition("state{}(not{}(VALUE:SortBool{}))");
        let subject = Pattern {
            term: internal_term(&definition, r#"state{}(\dv{SortBool{}}("true"))"#),
            constraints: Vec::new(),
        };
        let mut fresh = 0;

        let RewriteResult::Finished(applied) = rewrite_step(&definition, &subject, &mut fresh)
        else {
            panic!("negation should bind its operand to the opposite Boolean");
        };
        assert!(applied.substitution.iter().any(|(variable, value)| {
            variable.name.ends_with("VALUE")
                && value == &Term::domain_value(Sort::simple("SortBool"), "false")
        }));
    }

    #[cfg(feature = "z3")]
    #[test]
    fn constrains_configuration_conjunction_operands_when_matching_true() {
        let definition = boolean_rewrite_definition(r#"state{}(\dv{SortBool{}}("true"))"#);
        let subject = Pattern {
            term: internal_term(
                &definition,
                "state{}(and{}(LEFT:SortBool{}, RIGHT:SortBool{}))",
            ),
            constraints: Vec::new(),
        };
        let solver = crate::smt::Z3Solver::new(&definition).unwrap();
        let mut fresh = 0;

        let RewriteResult::Branch {
            branches,
            remainder: Some(remainder),
            ..
        } = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver)
        else {
            panic!("configuration conjunction should retain its complementary state");
        };
        let [branch] = branches.as_slice() else {
            panic!("expected one conjunction branch, found {branches:?}");
        };
        let expected = ["LEFT", "RIGHT"]
            .map(|name| {
                Predicate::Equals(
                    internal_term(&definition, &format!("{name}:SortBool{{}}")),
                    Term::domain_value(Sort::simple("SortBool"), "true"),
                )
            })
            .to_vec();
        assert_eq!(branch.pattern.constraints, expected);
        assert_eq!(
            remainder.pattern.constraints,
            [Predicate::Not(Box::new(Predicate::And(expected)))]
        );
    }

    #[cfg(feature = "z3")]
    #[test]
    fn negates_kequal_operand_unification_when_matching_false() {
        let definition =
            kequal_rewrite_definition("state{}(equal{}(VALUE:SortValue{}, chosen{}()))");
        let subject = Pattern {
            term: internal_term(&definition, r#"state{}(\dv{SortBool{}}("false"))"#),
            constraints: Vec::new(),
        };
        let solver = crate::smt::Z3Solver::new(&definition).unwrap();
        let mut fresh = 0;

        let RewriteResult::Branch {
            branches,
            remainder: Some(remainder),
            ..
        } = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver)
        else {
            panic!("false K equality should retain disequality and complementary branches");
        };
        let [branch] = branches.as_slice() else {
            panic!("expected one disequality branch, found {branches:?}");
        };
        let [disequality @ Predicate::Not(inner)] = branch.pattern.constraints.as_slice() else {
            panic!("expected the negated operand equality");
        };
        let Predicate::Equals(left, right) = inner.as_ref() else {
            panic!("expected an equality beneath the negation");
        };
        let TermKind::Variable(fresh_variable) = left.kind() else {
            panic!("the unbound equality operand should be freshened");
        };
        assert!(fresh_variable.name.starts_with("Ex#VALUE"));
        assert_eq!(right, &internal_term(&definition, "chosen{}()"));
        assert!(matches!(
            remainder.pattern.constraints.as_slice(),
            [Predicate::Not(complement)]
                if matches!(complement.as_ref(), Predicate::Exists(variable, condition)
                    if variable == fresh_variable && condition.as_ref() == disequality)
        ));
    }

    #[cfg(feature = "z3")]
    #[test]
    fn constrains_configuration_kequal_operands_when_matching_true() {
        let definition = kequal_rewrite_definition(r#"state{}(\dv{SortBool{}}("true"))"#);
        let subject = Pattern {
            term: internal_term(
                &definition,
                "state{}(equal{}(CONFIG:SortValue{}, chosen{}()))",
            ),
            constraints: Vec::new(),
        };
        let solver = crate::smt::Z3Solver::new(&definition).unwrap();
        let mut fresh = 0;

        let RewriteResult::Branch {
            branches,
            remainder: Some(remainder),
            ..
        } = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver)
        else {
            panic!("configuration equality should retain applied and complementary branches");
        };
        let [branch] = branches.as_slice() else {
            panic!("expected one configuration equality branch, found {branches:?}");
        };
        let condition = Predicate::Equals(
            internal_term(&definition, "CONFIG:SortValue{}"),
            internal_term(&definition, "chosen{}()"),
        );
        assert_eq!(
            branch.pattern.constraints.as_slice(),
            std::slice::from_ref(&condition)
        );
        assert_eq!(
            remainder.pattern.constraints,
            [Predicate::Not(Box::new(condition))]
        );
    }

    #[cfg(feature = "z3")]
    #[test]
    fn splits_symbolic_if_then_else_during_rewrite_matching() {
        let definition = ite_rewrite_definition("state{}(chosen{}())");
        let subject = Pattern {
            term: internal_term(
                &definition,
                "state{}(ite{}(CONDITION:SortBool{}, chosen{}(), rejected{}()))",
            ),
            constraints: Vec::new(),
        };
        let solver = crate::smt::Z3Solver::new(&definition).unwrap();
        let mut fresh = 0;

        let RewriteResult::Branch {
            branches,
            remainder: Some(remainder),
            ..
        } = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver)
        else {
            panic!("one viable ITE branch should retain its complementary state");
        };
        let [branch] = branches.as_slice() else {
            panic!("only the selected constructor should match, found {branches:?}");
        };
        assert_eq!(branch.pattern.term, internal_term(&definition, "done{}()"));
        let condition = internal_term(&definition, "CONDITION:SortBool{}");
        let selected = Predicate::Equals(
            condition,
            Term::domain_value(Sort::simple("SortBool"), "true"),
        );
        assert_eq!(
            branch.pattern.constraints.as_slice(),
            std::slice::from_ref(&selected)
        );
        assert_eq!(
            remainder.pattern.constraints,
            [Predicate::Not(Box::new(selected))]
        );
    }

    #[cfg(feature = "z3")]
    #[test]
    fn splits_symbolic_if_then_else_on_the_rule_side() {
        let definition = ite_rewrite_definition(
            "state{}(ite{}(CONDITION:SortBool{}, chosen{}(), rejected{}()))",
        );
        let subject = Pattern {
            term: internal_term(&definition, "state{}(chosen{}())"),
            constraints: Vec::new(),
        };
        let solver = crate::smt::Z3Solver::new(&definition).unwrap();
        let mut fresh = 0;

        let RewriteResult::Finished(applied) =
            rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver)
        else {
            panic!("the viable rule-side ITE branch should match exhaustively");
        };
        assert_eq!(applied.pattern.term, internal_term(&definition, "done{}()"));
        assert!(applied.pattern.constraints.is_empty());
        assert!(applied.substitution.iter().any(|(variable, value)| {
            variable.name.ends_with("CONDITION")
                && value == &Term::domain_value(Sort::simple("SortBool"), "true")
        }));
    }

    #[cfg(feature = "z3")]
    #[test]
    fn recursively_splits_nested_symbolic_if_then_else() {
        let definition = ite_rewrite_definition("state{}(chosen{}())");
        let subject = Pattern {
            term: internal_term(
                &definition,
                "state{}(ite{}(OUTER:SortBool{}, ite{}(INNER:SortBool{}, chosen{}(), rejected{}()), rejected{}()))",
            ),
            constraints: Vec::new(),
        };
        let solver = crate::smt::Z3Solver::new(&definition).unwrap();
        let mut fresh = 0;

        let RewriteResult::Branch {
            branches,
            remainder: Some(remainder),
            ..
        } = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver)
        else {
            panic!("the nested viable path should retain its complementary state");
        };
        let [branch] = branches.as_slice() else {
            panic!("only one nested ITE path should match, found {branches:?}");
        };
        let expected = ["OUTER", "INNER"]
            .map(|name| {
                Predicate::Equals(
                    internal_term(&definition, &format!("{name}:SortBool{{}}")),
                    Term::domain_value(Sort::simple("SortBool"), "true"),
                )
            })
            .to_vec();
        assert_eq!(branch.pattern.constraints, expected);
        assert_eq!(
            remainder.pattern.constraints,
            [Predicate::Not(Box::new(Predicate::And(expected)))]
        );
    }

    #[test]
    fn branches_for_every_concrete_set_element_selection() {
        let definition = set_selection_definition();
        let first = r#"\dv{SortElement{}}("first")"#;
        let second = r#"\dv{SortElement{}}("second")"#;
        let subject = Pattern {
            term: internal_term(
                &definition,
                &format!("state{{}}(setConcat{{}}(setItem{{}}({first}), setItem{{}}({second})))"),
            ),
            constraints: Vec::new(),
        };
        let mut fresh = 0;

        let RewriteResult::Branch {
            branches,
            remainder: None,
            ..
        } = rewrite_step(&definition, &subject, &mut fresh)
        else {
            panic!("set selection should produce one exhaustive branch per element");
        };
        let mut actual = branches
            .iter()
            .map(|branch| branch.pattern.term.clone())
            .collect::<Vec<_>>();
        actual.sort();
        let mut expected = vec![
            internal_term(
                &definition,
                &format!("picked{{}}({first}, setItem{{}}({second}))"),
            ),
            internal_term(
                &definition,
                &format!("picked{{}}({second}, setItem{{}}({first}))"),
            ),
        ];
        expected.sort();

        assert_eq!(actual, expected);
        assert!(
            branches
                .iter()
                .all(|branch| branch.pattern.constraints.is_empty())
        );
    }

    #[cfg(feature = "z3")]
    #[test]
    fn branches_for_set_elements_while_preserving_an_open_subject_frame() {
        let definition = set_selection_definition();
        let first = r#"\dv{SortElement{}}("first")"#;
        let second = r#"\dv{SortElement{}}("second")"#;
        let subject = Pattern {
            term: internal_term(
                &definition,
                &format!(
                    "state{{}}(setConcat{{}}(setConcat{{}}(setItem{{}}({first}), setItem{{}}({second})), SUBJECTREST:SortSet{{}}))"
                ),
            ),
            constraints: Vec::new(),
        };
        let mut fresh = 0;
        let solver = crate::smt::Z3Solver::new(&definition).unwrap();

        let result = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver);
        let RewriteResult::Branch {
            branches,
            remainder,
            ..
        } = result.clone()
        else {
            panic!(
                "set selection should preserve the opaque subject frame in every branch: {result:#?}"
            );
        };
        let mut actual = branches
            .iter()
            .map(|branch| branch.pattern.term.clone())
            .collect::<Vec<_>>();
        actual.sort();
        let mut expected = vec![
            internal_term(
                &definition,
                &format!(
                    "picked{{}}({first}, setConcat{{}}(setItem{{}}({second}), SUBJECTREST:SortSet{{}}))"
                ),
            ),
            internal_term(
                &definition,
                &format!(
                    "picked{{}}({second}, setConcat{{}}(setItem{{}}({first}), SUBJECTREST:SortSet{{}}))"
                ),
            ),
        ];
        expected.sort();

        assert_eq!(actual, expected);
        assert!(
            branches
                .iter()
                .all(|branch| !branch.pattern.constraints.is_empty())
        );
        assert!(remainder.is_some());
    }

    #[cfg(feature = "z3")]
    #[test]
    fn rewrites_after_cancelling_common_opaque_set_chunks() {
        let definition = opaque_set_narrowing_definition();
        let subject = Pattern {
            term: internal_term(
                &definition,
                "state{}(setConcat{}(setItem{}(CONFIG:SortElement{}), setConcat{}(opaqueA{}(), setConcat{}(opaqueB{}(), setConcat{}(REST:SortSet{}, opaqueA{}())))))",
            ),
            constraints: Vec::new(),
        };
        let solver = crate::smt::Z3Solver::new(&definition).unwrap();
        let mut fresh = 0;

        let RewriteResult::Branch {
            branches,
            remainder: Some(_),
            ..
        } = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver)
        else {
            panic!("common opaque chunks should cancel before Set frame narrowing");
        };
        let [branch] = branches.as_slice() else {
            panic!("the residual Set frame has one solution: {branches:?}");
        };
        let TermKind::Application {
            symbol, arguments, ..
        } = branch.pattern.term.kind()
        else {
            panic!("rewrite result should be selected(RULE)");
        };
        assert_eq!(symbol.name.as_ref(), "selected");
        let [fresh_rule] = arguments.as_slice() else {
            panic!("selected should retain one fresh rule variable");
        };
        assert!(matches!(fresh_rule.kind(), TermKind::Variable(variable)
            if variable.name.starts_with("Ex#RULE")));
        assert!(branch.pattern.constraints.contains(&Predicate::Equals(
            internal_term(&definition, "CONFIG:SortElement{}"),
            fresh_rule.clone(),
        )));
        assert!(
            branch.pattern.constraints.contains(&Predicate::Equals(
                internal_term(&definition, "REST:SortSet{}"),
                internal_term(&definition, "setUnit{}()"),
            )),
            "missing residual frame binding: {:#?}",
            branch.pattern.constraints
        );
        assert!(
            branch
                .pattern
                .constraints
                .contains(&Predicate::Ceil(internal_term(
                    &definition,
                    "setConcat{}(opaqueA{}(), setConcat{}(opaqueB{}(), opaqueB{}()))",
                ),))
        );
    }

    #[test]
    fn branches_for_every_concrete_map_key_selection() {
        let definition = map_selection_definition();
        let first_key = r#"\dv{SortKey{}}("first")"#;
        let first_value = r#"\dv{SortValue{}}("first-value")"#;
        let second_key = r#"\dv{SortKey{}}("second")"#;
        let second_value = r#"\dv{SortValue{}}("second-value")"#;
        let subject = Pattern {
            term: internal_term(
                &definition,
                &format!(
                    "mapState{{}}(mapConcat{{}}(mapItem{{}}({first_key}, {first_value}), mapItem{{}}({second_key}, {second_value})))"
                ),
            ),
            constraints: Vec::new(),
        };
        let mut fresh = 0;

        let RewriteResult::Branch {
            branches,
            remainder: None,
            ..
        } = rewrite_step(&definition, &subject, &mut fresh)
        else {
            panic!("map selection should produce one exhaustive branch per key");
        };
        let mut actual = branches
            .iter()
            .map(|branch| branch.pattern.term.clone())
            .collect::<Vec<_>>();
        actual.sort();
        let mut expected = vec![
            internal_term(
                &definition,
                &format!(
                    "mapPicked{{}}({first_key}, {first_value}, mapItem{{}}({second_key}, {second_value}))"
                ),
            ),
            internal_term(
                &definition,
                &format!(
                    "mapPicked{{}}({second_key}, {second_value}, mapItem{{}}({first_key}, {first_value}))"
                ),
            ),
        ];
        expected.sort();

        assert_eq!(actual, expected);
        assert!(
            branches
                .iter()
                .all(|branch| branch.pattern.constraints.is_empty())
        );
    }

    #[cfg(feature = "z3")]
    #[test]
    fn narrows_an_open_configuration_map_against_a_closed_rule_map() {
        let definition = closed_map_narrowing_definition();
        let subject = Pattern {
            term: internal_term(
                &definition,
                "mapState{}(mapConcat{}(mapItem{}(KEY:SortKey{}, VALUE:SortValue{}), REST:SortMap{}))",
            ),
            constraints: Vec::new(),
        };
        let solver = crate::smt::Z3Solver::new(&definition).unwrap();
        let mut fresh = 0;

        let RewriteResult::Branch {
            branches,
            remainder: Some(_),
            ..
        } = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver)
        else {
            panic!("symmetric Map unification should narrow both entry choices");
        };
        assert_eq!(branches.len(), 2);
        assert!(
            branches
                .iter()
                .all(|branch| branch.pattern.term == internal_term(&definition, "done{}()"))
        );

        for (key, value, remainder_key, remainder_value) in [
            ("first", "first-value", "second", "second-value"),
            ("second", "second-value", "first", "first-value"),
        ] {
            let key_binding = Predicate::Equals(
                internal_term(&definition, "KEY:SortKey{}"),
                internal_term(&definition, &format!(r#"\dv{{SortKey{{}}}}("{key}")"#)),
            );
            let value_binding = Predicate::Equals(
                internal_term(&definition, "VALUE:SortValue{}"),
                internal_term(&definition, &format!(r#"\dv{{SortValue{{}}}}("{value}")"#)),
            );
            let rest_binding = Predicate::Equals(
                internal_term(&definition, "REST:SortMap{}"),
                internal_term(
                    &definition,
                    &format!(
                        r#"mapItem{{}}(\dv{{SortKey{{}}}}("{remainder_key}"), \dv{{SortValue{{}}}}("{remainder_value}"))"#
                    ),
                ),
            );
            assert!(branches.iter().any(|branch| {
                branch.pattern.constraints.contains(&key_binding)
                    && branch.pattern.constraints.contains(&value_binding)
                    && branch.pattern.constraints.contains(&rest_binding)
            }));
        }
    }

    #[cfg(feature = "z3")]
    #[test]
    fn composes_function_and_collection_unification_before_rewriting() {
        let definition = closed_map_narrowing_definition();
        let subject = Pattern {
            term: internal_term(
                &definition,
                "mixedState{}(CONFIG:SortValue{}, mapConcat{}(mapItem{}(KEY:SortKey{}, VALUE:SortValue{}), REST:SortMap{}))",
            ),
            constraints: Vec::new(),
        };
        let solver = crate::smt::Z3Solver::new(&definition).unwrap();
        let mut fresh = 0;

        let RewriteResult::Branch {
            branches,
            remainder: Some(_),
            ..
        } = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver)
        else {
            panic!("mixed first-order and collection equations should produce rewrite branches");
        };
        assert_eq!(branches.len(), 2);

        let mut selected_keys = Vec::new();
        for branch in &branches {
            let TermKind::Application {
                symbol, arguments, ..
            } = branch.pattern.term.kind()
            else {
                panic!("rewrite result should be selected(RULE)");
            };
            assert_eq!(symbol.name.as_ref(), "selected");
            let [fresh_rule] = arguments.as_slice() else {
                panic!("selected should retain exactly one fresh rule variable");
            };
            assert!(matches!(fresh_rule.kind(), TermKind::Variable(variable)
                if variable.name.starts_with("Ex#RULE")));
            let configuration_binding = Predicate::Equals(
                internal_term(&definition, "CONFIG:SortValue{}"),
                Term::application(
                    definition.symbols["select"].clone(),
                    Vec::new(),
                    vec![fresh_rule.clone()],
                ),
            );
            assert!(branch.pattern.constraints.contains(&configuration_binding));

            let key_binding = branch.pattern.constraints.iter().find_map(|predicate| {
                let Predicate::Equals(left, right) = predicate else {
                    return None;
                };
                (left == &internal_term(&definition, "KEY:SortKey{}")).then_some(right.clone())
            });
            selected_keys.push(key_binding.expect("each branch should constrain the Map key"));
        }
        selected_keys.sort();
        assert_eq!(
            selected_keys,
            [
                internal_term(&definition, r#"\dv{SortKey{}}("first")"#),
                internal_term(&definition, r#"\dv{SortKey{}}("second")"#),
            ]
        );
    }

    #[cfg(feature = "z3")]
    #[test]
    fn narrows_concrete_rule_map_keys_against_symbolic_configuration_keys() {
        let definition = symbolic_map_key_definition();
        let wanted = r#"\dv{SortKey{}}("wanted")"#;
        let selected_value = r#"\dv{SortValue{}}("selected")"#;
        let other_key = r#"\dv{SortKey{}}("other")"#;
        let other_value = r#"\dv{SortValue{}}("other-value")"#;
        let subject = Pattern {
            term: internal_term(
                &definition,
                &format!(
                    "mapState{{}}(mapConcat{{}}(mapItem{{}}(KEY:SortKey{{}}, {selected_value}), mapItem{{}}({other_key}, {other_value})))"
                ),
            ),
            constraints: Vec::new(),
        };
        let solver = crate::smt::Z3Solver::new(&definition).unwrap();
        let mut fresh = 0;

        let RewriteResult::Branch {
            branches,
            remainder: Some(remainder),
            ..
        } = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver)
        else {
            panic!("symbolic key selection should retain its complementary branch");
        };
        let [branch] = branches.as_slice() else {
            panic!("expected one symbolic key selection, found {branches:?}");
        };
        assert_eq!(
            branch.pattern.term,
            internal_term(
                &definition,
                &format!(
                    "mapPicked{{}}({selected_value}, mapItem{{}}({other_key}, {other_value}))"
                )
            )
        );
        let selected = Predicate::Equals(
            internal_term(&definition, "KEY:SortKey{}"),
            internal_term(&definition, wanted),
        );
        assert_eq!(
            branch.pattern.constraints.as_slice(),
            std::slice::from_ref(&selected)
        );
        assert_eq!(
            remainder.pattern.constraints,
            [Predicate::Not(Box::new(selected))]
        );
    }

    #[cfg(feature = "z3")]
    #[test]
    fn does_not_rebind_configuration_variables_during_map_matching() {
        let definition = shared_symbolic_map_key_definition();
        let entry = internal_term(&definition, "ENTRY:SortKey{}");
        let requested = internal_term(&definition, "REQUESTED:SortKey{}");
        let subject = Pattern {
            term: internal_term(
                &definition,
                "request{}(mapConcat{}(mapItem{}(ENTRY:SortKey{}, VALUE:SortValue{}), MAP:SortMap{}), REQUESTED:SortKey{})",
            ),
            constraints: vec![Predicate::Not(Box::new(Predicate::Equals(
                entry, requested,
            )))],
        };
        let solver = crate::smt::Z3Solver::new(&definition).unwrap();
        let mut fresh = 0;

        let result = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver);
        let RewriteResult::Finished(applied) = result else {
            panic!("the disequality rule should be uniquely applicable: {result:?}");
        };

        assert_eq!(
            applied.pattern.term,
            internal_term(&definition, "different{}()")
        );
        assert!(
            applied
                .substitution
                .keys()
                .all(|variable| variable.name.starts_with("Rule#"))
        );
    }

    #[cfg(feature = "z3")]
    #[test]
    fn branches_for_map_keys_while_preserving_an_open_subject_frame() {
        let definition = map_selection_definition();
        let first_key = r#"\dv{SortKey{}}("first")"#;
        let first_value = r#"\dv{SortValue{}}("first-value")"#;
        let second_key = r#"\dv{SortKey{}}("second")"#;
        let second_value = r#"\dv{SortValue{}}("second-value")"#;
        let subject = Pattern {
            term: internal_term(
                &definition,
                &format!(
                    "mapState{{}}(mapConcat{{}}(mapConcat{{}}(mapItem{{}}({first_key}, {first_value}), mapItem{{}}({second_key}, {second_value})), SUBJECTREST:SortMap{{}}))"
                ),
            ),
            constraints: Vec::new(),
        };
        let mut fresh = 0;
        let solver = crate::smt::Z3Solver::new(&definition).unwrap();

        let result = rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver);
        let RewriteResult::Branch {
            branches,
            remainder,
            ..
        } = result.clone()
        else {
            panic!(
                "map selection should preserve the opaque subject frame in every branch: {result:#?}"
            );
        };
        let mut actual = branches
            .iter()
            .map(|branch| branch.pattern.term.clone())
            .collect::<Vec<_>>();
        actual.sort();
        let mut expected = vec![
            internal_term(
                &definition,
                &format!(
                    "mapPicked{{}}({first_key}, {first_value}, mapConcat{{}}(mapItem{{}}({second_key}, {second_value}), SUBJECTREST:SortMap{{}}))"
                ),
            ),
            internal_term(
                &definition,
                &format!(
                    "mapPicked{{}}({second_key}, {second_value}, mapConcat{{}}(mapItem{{}}({first_key}, {first_value}), SUBJECTREST:SortMap{{}}))"
                ),
            ),
        ];
        expected.sort();

        assert_eq!(actual, expected);
        assert!(
            branches
                .iter()
                .all(|branch| !branch.pattern.constraints.is_empty())
        );
        assert!(remainder.is_some());
    }

    #[cfg(feature = "z3")]
    #[test]
    fn decomposes_false_map_membership_over_known_entries_and_a_remainder() {
        let definition = map_not_in_keys_rewrite_definition();
        let subject = Pattern {
            term: internal_term(&definition, r#"state{}(\dv{SortBool{}}("false"))"#),
            constraints: Vec::new(),
        };
        let solver = crate::smt::Z3Solver::new(&definition).unwrap();
        let mut fresh = 0;

        let RewriteResult::Branch { branches, .. } =
            rewrite_step_with_solver(&definition, &subject, &mut fresh, &solver)
        else {
            panic!("false map membership should produce a constrained rewrite branch");
        };
        let [branch] = branches.as_slice() else {
            panic!("expected one map membership branch, found {branches:?}");
        };
        assert!(branch.pattern.constraints.iter().any(|condition| {
            matches!(condition, Predicate::Not(inner) if matches!(inner.as_ref(), Predicate::Equals(..)))
        }));
        let membership_conditions = branch
            .pattern
            .constraints
            .iter()
            .filter(|condition| {
                let term = match condition {
                    Predicate::Equals(left, _) => Some(left),
                    Predicate::Not(inner) => match inner.as_ref() {
                        Predicate::Term(term) => Some(term),
                        _ => None,
                    },
                    _ => None,
                };
                term.is_some_and(|term| {
                    matches!(term.kind(), TermKind::Application { symbol, .. }
                        if symbol.attributes.hook.as_deref() == Some("MAP.in_keys"))
                })
            })
            .count();
        assert_eq!(membership_conditions, 2);
    }
}
