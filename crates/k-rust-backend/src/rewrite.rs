//! Priority-aware rewrite steps over internalized backend theories.

use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    hash::{Hash, Hasher},
    sync::Arc,
    time::Duration,
};

use k_rust_kore::measure::{self, Counter};
use rustc_hash::{FxHashMap, FxHasher};

use crate::{
    builtin::BuiltinEffect,
    cancellation::cancellation_requested,
    definedness::ceil_term,
    definition::{BackendDefinition, ConstructorHead, constructor_head},
    ite::{IteSplit, SplitSide, split_ite_pair},
    matching::{
        CollectionSolution, FailReason, MatchMode, MatchResult, Narrowing, SortGraph,
        match_terms_in_definition, solve_collection_pairs_in_definition,
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
        ObservationEvent, ObservationHead, ObservationLog, ObservationOptions, PatternDigest,
        TransitionId, UncommittedObservation, UncommittedReason,
    },
    unification::{UnificationFailure, UnificationResult, unify_term_pairs},
};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Pattern {
    pub term: Term,
    pub constraints: Vec<Predicate>,
}

/// Apply the acyclic substitution encoded by a pattern's equality constraints while retaining
/// canonical equality predicates for later RPC projection.
pub fn normalize_pattern_substitution(pattern: &mut Pattern, sorts: &SortGraph) -> Substitution {
    let (substitution, remaining) = extract_substitution(&pattern.constraints, sorts);
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
    sorts: &SortGraph,
) {
    for (variable, value) in substitution {
        let represented = constraints.iter().any(|predicate| {
            substitution_binding(predicate, sorts)
                .is_some_and(|(represented, _)| represented == *variable)
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

/// A rule that unified but whose rewritten result is bottom. Kore retains its unifier in the
/// priority-group remainder even though execution and search have no successor to enqueue.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TrivialApplication {
    pub rule_id: String,
    pub label: Option<String>,
    /// The sub-case that rewrites to bottom: the incoming constraints and this predicate.
    pub applicability: Predicate,
    /// The complementary sub-case retained in the priority-group remainder.
    pub remainder: Predicate,
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
        /// Bottom-result sub-cases, ignored by execution/search and consumed by proof vacuity.
        trivial: Vec<TrivialApplication>,
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
    /// Concrete execution must instantiate every free variable on the rule's left-hand side.
    Instantiation {
        rule_id: String,
        missing_variables: BTreeSet<Variable>,
    },
    Requires {
        rule_id: String,
        predicates: Vec<Predicate>,
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
    /// Attempted transitions discarded before they could belong to a surviving branch.
    pub discarded: Vec<UncommittedObservation>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct InitialSimplificationStatus {
    simplified_to_bottom: bool,
}

impl InitialSimplificationStatus {
    /// Whether every nonempty input disjunct completed initial simplification as false.
    pub fn simplified_to_bottom(self) -> bool {
        self.simplified_to_bottom
    }
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
        vec![initial],
        options,
        solver,
        Some(observation),
        |_| {},
    )
    .0
}

pub fn execute_with_solver_and_observer(
    definition: &BackendDefinition,
    initial: Pattern,
    options: ExecutionOptions,
    solver: &dyn SmtSolver,
    observe: impl FnMut(&BuiltinEffect),
) -> ExecutionResult {
    execute_using(definition, vec![initial], options, solver, None, observe).0
}

pub fn execute_disjunction_with_solver_and_observer(
    definition: &BackendDefinition,
    initial: Vec<Pattern>,
    options: ExecutionOptions,
    solver: &dyn SmtSolver,
    observe: impl FnMut(&BuiltinEffect),
) -> ExecutionResult {
    execute_using(definition, initial, options, solver, None, observe).0
}

/// Execute a disjunction and report the outcome of its initial simplification phase.
pub fn execute_disjunction_with_solver_and_observer_with_initial_status(
    definition: &BackendDefinition,
    initial: Vec<Pattern>,
    options: ExecutionOptions,
    solver: &dyn SmtSolver,
    observe: impl FnMut(&BuiltinEffect),
) -> (ExecutionResult, InitialSimplificationStatus) {
    execute_using(definition, initial, options, solver, None, observe)
}

fn execute_using(
    definition: &BackendDefinition,
    initial: Vec<Pattern>,
    options: ExecutionOptions,
    solver: &dyn SmtSolver,
    observation: Option<&ObservationOptions>,
    mut observe: impl FnMut(&BuiltinEffect),
) -> (ExecutionResult, InitialSimplificationStatus) {
    let mut fresh_counter = 0;
    let mut observation_log = ObservationLog::default();
    let initial_input_count = initial.len();
    let mut pending = initial
        .into_iter()
        .map(|pattern| ExecutionState {
            pattern,
            depth: 0,
            trace: Vec::new(),
            observation: None,
            is_initial_input: true,
        })
        .collect::<VecDeque<_>>();
    let mut leaves = SelectedExecutionLeaves::default();
    let mut effects = Vec::new();
    let mut discarded = Vec::new();
    let mut completed_initial_simplifications = 0;
    let mut bottom_initial_simplifications = 0;
    let timeout_controller = StepTimeoutController::new(StepTimeoutOptions {
        manual: options.step_timeout,
        moving_average: options.moving_average_timeout,
    });
    if options.max_breadth == Some(0) {
        return (
            ExecutionResult {
                leaves: merge_equal_final_leaves(
                    pending
                        .drain(..)
                        .map(|state| execution_state_at_breadth_bound(state, &observation_log))
                        .collect(),
                ),
                effects,
                discarded,
            },
            InitialSimplificationStatus {
                simplified_to_bottom: false,
            },
        );
    }
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
                leaves.push(state.leaf(HaltReason::Vacuous, &observation_log));
                continue;
            }
        }
        let pattern_before_term_simplification = state.pattern.clone();
        let simplified = simplify_with_solver(
            definition,
            &state.pattern.term,
            &state.pattern.constraints,
            SimplificationOptions::keep_partial(options.max_simplification_iterations),
            solver,
        );
        finish_if_interrupted!();
        match simplified {
            Ok(simplified) => {
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
        if state.is_initial_input {
            completed_initial_simplifications += 1;
            if deferred_initial_vacuity.is_none()
                && predicates_truth(&state.pattern.constraints) == Truth::False
            {
                bottom_initial_simplifications += 1;
                leaves.push(state.leaf(HaltReason::Vacuous, &observation_log));
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
            SimplificationOptions::keep_partial(options.max_simplification_iterations),
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
                    state.observation =
                        observation_log.append_applied(state.observation, &applied, observation);
                    applied.pattern = match simplify_result_pattern(
                        definition,
                        &applied.pattern,
                        options.max_simplification_iterations,
                        solver,
                        state.depth,
                        &mut state.trace,
                        &mut effects,
                        &mut observe,
                        Some(&mut state.observation),
                        &mut observation_log,
                        observation,
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
                        Some(&mut next.observation),
                        &mut observation_log,
                        observation,
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
                ..
            } => {
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
                        &mut effects,
                        &mut observe,
                        Some(&mut state.observation),
                        &mut observation_log,
                        observation,
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
                            &mut effects,
                            &mut observe,
                            None,
                            &mut observation_log,
                            observation,
                        ) {
                            Ok(pattern) => {
                                applied.pattern = pattern;
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
                            &mut effects,
                            &mut observe,
                            None,
                            &mut observation_log,
                            observation,
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
    (
        ExecutionResult {
            leaves: merge_equal_final_leaves(select_got_stuck_over_depth_bound(
                leaves.into_inner(),
            )),
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

/// Kore's `GraphTraversal.checkLeftUnproven` reports stuck and vacuous results in
/// preference to states that merely reached the depth bound. Apply that selection before
/// deduplication so an equal depth-bounded leaf cannot hide a later stuck leaf.
fn select_got_stuck_over_depth_bound(mut leaves: Vec<ExecutionLeaf>) -> Vec<ExecutionLeaf> {
    let got_stuck = leaves.iter().any(|leaf| {
        matches!(
            leaf.halt_reason,
            HaltReason::Stuck | HaltReason::Trivial | HaltReason::Vacuous
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
            HaltReason::Stuck | HaltReason::Trivial | HaltReason::Vacuous
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

/// Kore's `MultiOr.make` over final configurations (Exec.hs:340-342): leaves that carry the
/// same structural term and constraint set collapse into the first one found. Bottom leaves carry
/// no configuration, so whole-state trivial and vacuous outcomes remain distinct.
fn merge_equal_final_leaves(leaves: Vec<ExecutionLeaf>) -> Vec<ExecutionLeaf> {
    let mut seen = Vec::new();
    leaves
        .into_iter()
        .filter(|leaf| {
            if matches!(leaf.halt_reason, HaltReason::Trivial | HaltReason::Vacuous) {
                return true;
            }
            let key = (
                leaf.pattern.term.clone(),
                leaf.pattern
                    .constraints
                    .iter()
                    .cloned()
                    .collect::<BTreeSet<_>>(),
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
    observation: Option<&mut ObservationHead>,
    observation_log: &mut ObservationLog,
    observation_options: Option<&ObservationOptions>,
) -> Result<Pattern, SimplificationError> {
    let before = pattern.clone();
    let PatternSimplification {
        pattern,
        applied_rules,
        effects: simplified_effects,
    } = simplify_pattern_details_with_solver(
        definition,
        pattern,
        SimplificationOptions::keep_partial(max_iterations),
        solver,
    )?;
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
        is_initial_input: false,
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
        is_initial_input: false,
    }
}

struct ExecutionState {
    pattern: Pattern,
    depth: u64,
    trace: Vec<TraceEntry>,
    observation: ObservationHead,
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

/// Apply rewrite rules sequentially, feeding each rule only the remainder left by earlier rules.
///
/// This is Kore's `applyRewriteRulesSequence`, used for one-path reachability proofs.
pub fn rewrite_step_sequential_with_solver(
    definition: &BackendDefinition,
    pattern: &Pattern,
    fresh_counter: &mut u64,
    solver: &dyn SmtSolver,
) -> RewriteResult {
    rewrite_step_with_mode(
        definition,
        pattern,
        fresh_counter,
        SimplificationOptions::default(),
        solver,
        ExecutionMode::Any,
        false,
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

pub(crate) fn rewrite_step_sequential_with_options(
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
        ExecutionMode::Any,
        false,
    )
}

pub(crate) fn rewrite_step_with_mode(
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
    for rules in priority_groups.values() {
        let mut applied = Vec::new();
        let mut trivial = Vec::new();
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
                RuleAttempt::Unified {
                    applied: found,
                    trivial: found_trivial,
                } => {
                    measure::bump(Counter::RewriteRulesApplied);
                    applied.extend(found);
                    trivial.extend(found_trivial);
                }
                RuleAttempt::Indeterminate(reason) => {
                    return RewriteResult::Indeterminate {
                        pattern: pattern.clone(),
                        reason,
                    };
                }
            }
        }
        if applied.is_empty() && trivial.is_empty() {
            continue;
        }
        let rule_ids = applied
            .iter()
            .map(|application| application.applied.unique_id.clone())
            .chain(
                trivial
                    .iter()
                    .map(|application| application.rule_id.clone()),
            )
            .collect::<Vec<_>>();
        let raw_remainder = applied
            .iter()
            .map(|application| application.remainder.clone())
            .chain(
                trivial
                    .iter()
                    .map(|application| application.remainder.clone()),
            )
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
        let remainder_result = if predicates_truth(&remainder) == Truth::False {
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
        ) {
            return RewriteResult::Indeterminate {
                pattern: pattern.clone(),
                reason: IndeterminateReason::Remainder {
                    rule_ids,
                    predicates: remainder,
                    satisfiability: remainder_result,
                },
            };
        }
        let remainder = if matches!(remainder_result, Ok(Satisfiability::Sat)) {
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
        return match (applied.len(), trivial.is_empty(), remainder) {
            (0, false, None) => RewriteResult::Trivial(pattern.clone()),
            (1, true, None) => RewriteResult::Finished(applied.pop().unwrap().applied),
            (_, _, remainder) => RewriteResult::Branch {
                original: pattern.clone(),
                branches: applied
                    .into_iter()
                    .map(|application| application.applied)
                    .collect(),
                remainder,
                trivial,
            },
        };
    }
    RewriteResult::Stuck(pattern.clone())
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
    let mut trivial = Vec::new();
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
            RuleAttempt::Unified {
                applied: results,
                trivial: found_trivial,
            } => {
                measure::bump(Counter::RewriteRulesApplied);
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
                for application in found_trivial {
                    extend_unique(
                        &mut remainder_conditions,
                        std::iter::once(application.remainder.clone()),
                    );
                    extend_unique(
                        &mut remaining.constraints,
                        std::iter::once(application.remainder.clone()),
                    );
                    trivial.push(application);
                }
                match simplify_predicates_with_solver(
                    definition,
                    &remaining.constraints,
                    &pattern.constraints,
                    simplification_options,
                    solver,
                ) {
                    Ok(constraints) => {
                        remaining.constraints = pattern.constraints.clone();
                        extend_unique(&mut remaining.constraints, constraints);
                    }
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

    if applied.is_empty() && trivial.is_empty() {
        return RewriteResult::Stuck(pattern.clone());
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
                    .chain(
                        trivial
                            .iter()
                            .map(|application| application.rule_id.clone()),
                    )
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
            .chain(
                trivial
                    .iter()
                    .map(|application| application.rule_id.clone()),
            )
            .collect(),
    });
    match (applied.len(), trivial.is_empty(), remainder) {
        (0, false, None) => RewriteResult::Trivial(pattern.clone()),
        (1, true, None) => RewriteResult::Finished(applied.pop().unwrap()),
        (_, _, remainder) => RewriteResult::Branch {
            original: pattern.clone(),
            branches: applied,
            remainder,
            trivial,
        },
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
    /// The rule unified in at least one sub-case, including results that simplify to bottom.
    Unified {
        applied: Vec<RuleApplication>,
        trivial: Vec<TrivialApplication>,
    },
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
    measure::bump(Counter::RewriteIndeterminateRecoveries);
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

fn solve_collection_remainders_with_narrowing(
    definition: &BackendDefinition,
    pattern: &Pattern,
    substitution: Substitution,
    remainder: &[(Term, Term)],
    fresh_counter: &mut u64,
) -> Option<Vec<CollectionSolution>> {
    let mut names_to_avoid = pattern_variable_names(pattern);
    let mut fresh_frame = |sort: &Sort| {
        let seed = Variable::new("Ex#Frame", sort.clone());
        let fresh = fresh_variable(&seed, &mut names_to_avoid, fresh_counter);
        let TermKind::Variable(variable) = fresh.kind() else {
            unreachable!("fresh terms are variables")
        };
        variable.clone()
    };
    let mut narrowing = Narrowing {
        fresh_frame: &mut fresh_frame,
    };
    solve_collection_pairs_in_definition(
        MatchMode::Rewrite,
        definition,
        substitution,
        remainder,
        Some(&mut narrowing),
    )
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
            let Some(solutions) = solve_collection_remainders_with_narrowing(
                definition,
                pattern,
                substitution,
                &remainder,
                fresh_counter,
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
                vec![CollectionSolution {
                    substitution: unified.substitution,
                    constraints: Vec::new(),
                    fresh: BTreeSet::new(),
                }],
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
    solutions: Vec<CollectionSolution>,
    constraints: &[Predicate],
    collection_pairs: &[(Term, Term)],
    fresh_counter: &mut u64,
) -> Vec<(Substitution, Vec<Predicate>)> {
    solutions
        .into_iter()
        .map(|solution| {
            let (substitution, _) =
                freshen_unbound_rule_variables(rule, pattern, solution.substitution, fresh_counter);
            let mut all_constraints = constraints.to_vec();
            extend_unique(&mut all_constraints, solution.constraints);
            let mut constraints = substitute_predicates(&all_constraints, &substitution);
            extend_unique(
                &mut constraints,
                collection_unification_definedness(definition, collection_pairs, &substitution),
            );
            (substitution, constraints)
        })
        .collect()
}

pub(crate) fn collection_unification_definedness(
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
    // Kore's checkSubstitutionCoverage permits narrowing only when the whole initial term is
    // not constructor-like. Keep concrete rule variables available for requires to bind, then
    // check coverage before constructing the successor in apply_rule_with_match.
    if pattern.term.attributes().constructor_like {
        return (substitution, BTreeSet::new());
    }
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

fn remainder_of(applicability: &Predicate) -> Predicate {
    if *applicability == Predicate::True {
        Predicate::False
    } else {
        Predicate::Not(Box::new(applicability.clone()))
    }
}

fn trivial_application(rule: &RewriteRule, applicability: &Predicate) -> TrivialApplication {
    TrivialApplication {
        rule_id: rule.attributes.unique_id.clone(),
        label: rule.attributes.label.clone(),
        applicability: applicability.clone(),
        remainder: remainder_of(applicability),
    }
}

struct PartialRuleMatch {
    substitution: Substitution,
    conditions: Vec<Predicate>,
    remainder: Vec<(Term, Term)>,
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
    measure::bump(Counter::RewriteRuleAttempts);
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
        MatchResult::Failed(_) => {
            measure::bump(Counter::RewriteMatchFailures);
            return RuleAttempt::NotApplicable;
        }
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
                MatchResult::Failed(_) => {
                    measure::bump(Counter::RewriteMatchFailures);
                    return RuleAttempt::NotApplicable;
                }
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
                    if let Some(matches) = solve_collection_remainders_with_narrowing(
                        definition,
                        pattern,
                        substitution.clone(),
                        &remainder,
                        fresh_counter,
                    ) {
                        if matches.is_empty() {
                            return RuleAttempt::NotApplicable;
                        }
                        return combine_rule_attempts(matches.into_iter().map(|solution| {
                            let (substitution, _) = freshen_unbound_rule_variables(
                                rule,
                                pattern,
                                solution.substitution,
                                fresh_counter,
                            );
                            let mut conditions = inherited_conditions.clone();
                            extend_unique(
                                &mut conditions,
                                substitute_predicates(&solution.constraints, &substitution),
                            );
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
        let applicability = quantify_introduced_variables(pattern, match_conditions);
        return RuleAttempt::Unified {
            applied: Vec::new(),
            trivial: vec![trivial_application(rule, &applicability)],
        };
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
    if pattern.term.attributes().constructor_like {
        // Conditions can finish an otherwise incomplete match (for example, requires E = value).
        // Re-enter application with those bindings so the remaining functional equalities and
        // requires are simplified under the covering substitution before coverage is checked.
        let mut conditions = match_conditions.clone();
        extend_unique(&mut conditions, requires.iter().cloned());
        let (bindings, _) = extract_substitution(&conditions, &definition.sort_graph);
        let bindings = bindings
            .into_iter()
            .filter(|(variable, _)| {
                rule.lhs.attributes().variables.contains(variable)
                    && !substitution.contains_key(variable)
            })
            .collect::<Substitution>();
        if !bindings.is_empty() {
            return apply_rule_with_match(
                definition,
                rule,
                pattern,
                fresh_counter,
                simplification_options,
                solver,
                assume_initial_defined,
                Some(PartialRuleMatch {
                    substitution: compose(&bindings, &substitution),
                    conditions: substitute_predicates(&conditions, &bindings),
                    remainder: Vec::new(),
                }),
            );
        }
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

    if pattern.term.attributes().constructor_like {
        let missing_variables = rule
            .lhs
            .attributes()
            .variables
            .iter()
            .filter(|variable| !substitution.contains_key(*variable))
            .cloned()
            .collect::<BTreeSet<_>>();
        if !missing_variables.is_empty() {
            return RuleAttempt::Indeterminate(IndeterminateReason::Instantiation {
                rule_id: rule.attributes.unique_id.clone(),
                missing_variables,
            });
        }
    }

    let existential_substitution = freshen_existentials(rule, pattern);
    let mut condition_knowledge = match_knowledge;
    extend_unique(&mut condition_knowledge, unclear_requires.iter().cloned());
    let alternatives = match &rule.rhs {
        RuleRhs::Term(rhs) => vec![(rhs, rule.ensures.as_slice())],
        RuleRhs::Disjunction(alternatives) => alternatives
            .iter()
            .map(|alternative| (&alternative.term, alternative.ensures.as_slice()))
            .collect(),
        RuleRhs::Top => return RuleAttempt::NotApplicable,
        RuleRhs::Bottom => {
            return RuleAttempt::Unified {
                applied: Vec::new(),
                trivial: vec![trivial_application(rule, &applicability)],
            };
        }
        RuleRhs::Predicates(_) => return RuleAttempt::NotApplicable,
    };
    let mut applications = Vec::new();
    let mut trivial = Vec::new();
    for (rhs, alternative_ensures) in alternatives {
        let mut ensures = rule.ensures.clone();
        extend_unique(&mut ensures, alternative_ensures.iter().cloned());
        match apply_rhs_alternative(
            definition,
            rule,
            pattern,
            rhs,
            &ensures,
            &substitution,
            &existential_substitution,
            &condition_knowledge,
            &match_conditions,
            &unclear_requires,
            &applicability,
            simplification_options,
            solver,
        ) {
            RhsAlternativeAttempt::Applied(application) => applications.push(application),
            RhsAlternativeAttempt::Trivial => {
                trivial.push(trivial_application(rule, &applicability));
            }
            RhsAlternativeAttempt::Indeterminate(reason) => {
                return RuleAttempt::Indeterminate(reason);
            }
        }
    }
    RuleAttempt::Unified {
        applied: applications,
        trivial,
    }
}

enum RhsAlternativeAttempt {
    Applied(RuleApplication),
    Trivial,
    Indeterminate(IndeterminateReason),
}

#[allow(clippy::too_many_arguments)]
fn apply_rhs_alternative(
    definition: &BackendDefinition,
    rule: &RewriteRule,
    pattern: &Pattern,
    rhs: &Term,
    ensures: &[Predicate],
    substitution: &Substitution,
    existential_substitution: &Substitution,
    condition_knowledge: &[Predicate],
    match_conditions: &[Predicate],
    unclear_requires: &[Predicate],
    applicability: &Predicate,
    simplification_options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> RhsAlternativeAttempt {
    let rhs = substitute(&substitute(rhs, substitution), existential_substitution);
    let mut condition_knowledge = condition_knowledge.to_vec();
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
                    return RhsAlternativeAttempt::Indeterminate(
                        IndeterminateReason::simplification(
                            Some(&rule.attributes.unique_id),
                            error,
                        ),
                    );
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
                return RhsAlternativeAttempt::Indeterminate(IndeterminateReason::simplification(
                    Some(&rule.attributes.unique_id),
                    error,
                ));
            }
        };
        match predicates_truth(&obligations) {
            Truth::True => {}
            Truth::False => return RhsAlternativeAttempt::Trivial,
            Truth::Unknown => match solver.check_predicates(
                &condition_knowledge,
                &Substitution::new(),
                &obligations,
            ) {
                Ok(Validity::Valid) => {}
                Ok(Validity::Invalid | Validity::InconsistentGroundTruth) => {
                    return RhsAlternativeAttempt::Trivial;
                }
                Ok(Validity::Indeterminate | Validity::Unknown(_)) | Err(_) => {
                    extend_unique(&mut rhs_constraints, obligations);
                }
            },
        }
    }
    let ensures = substitute_predicates(
        &substitute_predicates(ensures, substitution),
        existential_substitution,
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
            return RhsAlternativeAttempt::Indeterminate(IndeterminateReason::simplification(
                Some(&rule.attributes.unique_id),
                error,
            ));
        }
    };
    match predicates_truth(&ensures) {
        Truth::False => return RhsAlternativeAttempt::Trivial,
        Truth::True => {}
        Truth::Unknown => {
            match solver.check_predicates(&condition_knowledge, &Substitution::new(), &ensures) {
                Ok(Validity::Invalid | Validity::InconsistentGroundTruth) => {
                    return RhsAlternativeAttempt::Trivial;
                }
                Ok(Validity::Valid) => ensures.clear(),
                Ok(Validity::Indeterminate) | Err(SmtError::Unavailable) => {}
                Ok(Validity::Unknown(reason)) => {
                    return RhsAlternativeAttempt::Indeterminate(IndeterminateReason::Smt {
                        rule_id: rule.attributes.unique_id.clone(),
                        error: SmtError::Unknown(reason),
                    });
                }
                Err(error) => {
                    return RhsAlternativeAttempt::Indeterminate(IndeterminateReason::Smt {
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
    RhsAlternativeAttempt::Applied(RuleApplication {
        applied: AppliedRule {
            before: pattern.clone(),
            pattern: Pattern {
                term: rhs,
                constraints,
            },
            label: rule.attributes.label.clone(),
            unique_id: rule.attributes.unique_id.clone(),
            substitution: substitution.clone(),
            rule_substitution,
            rule_predicates,
            effects,
        },
        remainder: remainder_of(applicability),
    })
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
    let mut trivial = Vec::new();
    for attempt in attempts {
        match attempt {
            RuleAttempt::NotApplicable => {}
            RuleAttempt::Unified {
                applied: mut found,
                trivial: mut found_trivial,
            } => {
                applications.append(&mut found);
                trivial.append(&mut found_trivial);
            }
            RuleAttempt::Indeterminate(reason) => return RuleAttempt::Indeterminate(reason),
        }
    }
    if applications.is_empty() && trivial.is_empty() {
        RuleAttempt::NotApplicable
    } else {
        RuleAttempt::Unified {
            applied: applications,
            trivial,
        }
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

/// Checks the equation-only `concrete` and `symbolic` application attributes.
/// Rewrite rules never call this: Booster and Kore consult these attributes only for equations.
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
}
