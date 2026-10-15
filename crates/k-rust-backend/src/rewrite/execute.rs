//! ```toml algorithm
//! id = "backend.rewrite.execute"
//! name = "depth-first exploration of a rewrite tree"
//! sites = ["execute_using", "Execution::run", "Execution::expand", "Execution::merged", "commit_applied", "ExecutionState::leaf", "merge_equal_final_leaves", "enqueue_execution_states"]
//! variable = "d = maximum depth; b = maximum breadth; L = final leaves"
//! counters = ["RewriteSteps", "ExecutionStatesMerged"]
//! span = "per problem"
//! invariant = "pending holds unexpanded states of depth <= max_depth, their depths non-increasing from front to back; leaves only grows; work counts the states taken from pending, at most max_work. A state-set run that explores every branch records a state in its merge table only once the state's expansion completed without a stop, and keeps no depth below the back of pending. When retain_trace is false, commit_applied keeps only the latest rewrite entry needed for halt metadata, and leaf returns no trace."
//! consumes = [
//!   { type = "k_rust_backend::definition::BackendDefinition", role = "internalized theory" },
//!   { type = "k_rust_backend::rewrite::Pattern", role = "internalized pattern" },
//!   { type = "k_rust_backend::rewrite::RewriteResult", role = "rewrite result" },
//! ]
//! produces = [{ type = "k_rust_backend::rewrite::ExecutionResult", role = "execution result" }]
//!
//! [[cost]]
//! mode = "bounded execution"
//! bound = "O(min(states, max_work)), with states at most b^d when both bounds are set and unbounded under the defaults (max_depth = u64::MAX, max_breadth = None, max_work = None); one integer comparison per state for the work budget; each state performs one term simplification, predicate pass, and rewrite step (a successor whose step already normalized it under strategy any takes that normalization instead), plus one predicate simplification and one satisfiability query per undefined-step (trivial) entry of its step, and a state stopped at max_depth is simplified once more; an initial state the run does not assume defined also walks its term's definedness once and simplifies the obligations that walk finds once"
//!
//! [[cost]]
//! mode = "final leaf merge (merge_equal_final_leaves)"
//! bound = "nothing with fewer than two leaves carrying a configuration; otherwise one RequestNames::state_key (backend.fresh.variables) and one console observation (linear in the leaf's transcript) per such leaf, and O(L^2) key comparisons; each merged leaf's diagnostics are appended to the retained leaf's without repeats, in time the product of the two lists' lengths; a leaf is merged only into a retained leaf of its configuration that may absorb it (merge_class), and a run-ending leaf is kept as is"
//!
//! [[cost]]
//! mode = "state-set exploration merge (Execution::merged)"
//! bound = "one expansion per distinct (depth, RequestNames::state_key, effects, observed console, console availability) class, times the maximal diagnostic sets recorded for it (one set unless converging paths carry incomparable diagnostics); one E2/E3 simplification per arriving state; nothing computed from a state while it is alone at its depth; once a second state arrives there, one RequestNames::shape_hash per state of the depth (linear in its nodes that hold variables), and one RequestNames::state_key per state whose hash another state of the depth shares, each computed once; the effects and consoles of two arrivals are compared by fingerprint in O(1) and then back to their shared history; memory: the states recorded at depths not below the shallowest pending state, each a record of about 300 bytes (64-bit) and a copy of its constraint list, holding its term by its shared nodes, not a copy, so the sum of the recorded constraint-list lengths: quadratic in path length when the path condition grows by a conjunct per step"
//!
//! [[cost]]
//! mode = "trace storage"
//! bound = "O(1) per fork and per appended entry: a path shares its trace with the paths it forked from (rewrite::path_trace); O(entries) per leaf to materialise the trace it returns"
//!
//! [[cost]]
//! mode = "effect journal and console storage"
//! bound = "O(1) per fork: a path shares its effect journal and console transcript with the paths it forked from (transition::SharedLog); O(1) plus the effect's or write's length per committed effect or console write, which folds the running digest; O(1) per fingerprint (EffectJournal::fingerprint, ExecutionIoState::observable_fingerprint); O(entries) per leaf to materialise its effects, and once per state whose transcript is read"
//!
//! [[cost]]
//! mode = "trace storage with retain_trace false"
//! bound = "O(1) rewrite entries per active path, excluding transient simplification entries"
//!
//! [[cost]]
//! mode = "branch-stop candidate identity"
//! bound = "O(1) without observation; with observation O(KORE text bytes) per candidate to name its transition, and once more for an observed discarded candidate; each digest uses O(printer traversal stack) extra memory"
//! ```
//!
//! Depth-first exploration of the rewrite tree (stack discipline) with a per-state pipeline and
//! an equal-leaf merge; the result covers every path up to the bound: O(states) steps, states <=
//! branching^depth bounded by `max_depth` and `max_breadth`, each state one term simplification,
//! one predicate pass, and one rewrite step; `Counter::RewriteSteps`. A state-set run that explores
//! every branch also merges each state equal at its depth to a recorded one
//! (`exploration_merge`), so its states are the distinct states of each depth;
//! `Counter::ExecutionStatesMerged`. Not breadth-first: `enqueue_execution_states` pushes
//! successors to the front, so children are visited before siblings.

// The phase methods return `Phase<T>` (below), whose `Err` is the finished `ExecutionLeaf`
// itself: one leaf per state, moved once into `leaves`.
#![allow(clippy::result_large_err)]

use std::collections::{BTreeSet, VecDeque};

use k_rust_kore::measure::{self, Algorithm, Counter};

use crate::{
    builtin::BuiltinEffect,
    definedness::{FactsVerdict, UndecidedFacts},
    definition::BackendDefinition,
    diagnostic::{self, BackendDiagnostic, PathDiagnostics, extend_distinct},
    fresh::{FreshCounter, RequestNames},
    rule::Predicate,
    search::ResultModality,
    simplify::{
        ContradictedTotal, PatternSimplification, Simplification, SimplificationError,
        SimplificationOptions, simplify_in_execution_with_solver,
        simplify_pattern_details_with_solver, simplify_predicates_with_solver,
        simplify_with_solver,
    },
    smt::{Satisfiability, SmtSolver},
    stop::{self, Stop, StopCause, Stoppable},
    substitution::Substitution,
    timeout::{StepTimeoutController, StepTimeoutOptions, StepTimer},
    transition::{
        EffectJournal, ExecutionIoState, ObservationHead, ObservationLog, ObservationOptions,
        PatternDigest, TransitionId, UncommittedObservation, UncommittedReason,
    },
};

use super::work::Work;
use super::{
    AppliedRule, ExecutionBranchMode, ExecutionLeaf, ExecutionOptions, ExecutionResult, HaltReason,
    IndeterminateReason, InitialDefinedness, InitialSimplificationStatus, Pattern, RemainderBranch,
    RemainderSimplification, RewriteResult, SubjectDefinedness, TraceEntry, TraceKind,
    TrivialApplication, Truth, UndecidedStep, applied_trivial_halt,
    exploration_merge::{Arrival, ExplorationMerge},
    initial_definedness, normalize_pattern_substitution,
    path_trace::PathTrace,
    predicates_truth, retain_substitution_predicates, rewrite_step_with_optional_execution, stuck,
    trivial_halt, vacuous_halt,
};

pub(super) fn execute_using(
    definition: &BackendDefinition,
    initial: Vec<Pattern>,
    options: ExecutionOptions,
    solver: &dyn SmtSolver,
    initial_io: Option<ExecutionIoState>,
    observation: Option<&ObservationOptions>,
    observe: impl FnMut(&BuiltinEffect),
) -> (ExecutionResult, InitialSimplificationStatus) {
    // Every stack stop of the run is counted, those that end a state and those a refinement
    // dismisses alike (`ExecutionResult::stack_stops`).
    let ((mut result, status), stack_stops) = crate::stop::counting_stack_stops(|| {
        execute_counted(
            definition,
            initial,
            options,
            solver,
            initial_io,
            observation,
            observe,
        )
    });
    result.stack_stops = stack_stops;
    (result, status)
}

/// [`execute_using`] inside its count of stack stops.
fn execute_counted(
    definition: &BackendDefinition,
    initial: Vec<Pattern>,
    options: ExecutionOptions,
    solver: &dyn SmtSolver,
    initial_io: Option<ExecutionIoState>,
    observation: Option<&ObservationOptions>,
    mut observe: impl FnMut(&BuiltinEffect),
) -> (ExecutionResult, InitialSimplificationStatus) {
    let _span = measure::algorithm_span(Algorithm::BackendRewriteExecute);
    let _apart = crate::rule::ApartScope::enter();
    // Every evaluation of the run, its rule and equation conditions included, runs in the mode
    // the request asks for (`crate::evaluation`).
    let _evaluation = crate::evaluation::EvaluationScope::enter(options.evaluation);
    let _domain = crate::term::domain::DomainScope::enter(definition);
    let _hook_values = crate::deferred::HookValueScope::enter(definition);
    let timeout_controller = StepTimeoutController::new(StepTimeoutOptions {
        manual: options.step_timeout,
        moving_average: options.moving_average_timeout,
    });
    let collect_coverage = options.collect_coverage;
    let run = || {
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
    };
    if !collect_coverage {
        return run();
    }
    // The definition is selected and internalized before this call, so the collection holds
    // what the run applied and nothing a module's construction did (`crate::coverage`).
    let ((mut result, status), coverage) = crate::coverage::collect(run);
    result.coverage = Some(coverage);
    (result, status)
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
    fresh_counter: FreshCounter,
    observation_log: ObservationLog,
    initial_input_count: usize,
    pending: VecDeque<ExecutionState>,
    leaves: Vec<ExecutionLeaf>,
    discarded: Vec<UncommittedObservation>,
    completed_initial_simplifications: usize,
    bottom_initial_simplifications: usize,
    /// The cause of the stop that ended the run, once one did (`ExecutionResult::stopped`).
    stopped: Option<StopCause>,
    /// The states visited and the budget (`work::Work`).
    work: Work,
    /// The merge table of a state-set run that explores every branch; `None` otherwise.
    merge: Option<ExplorationMerge>,
    /// The state being expanded, as the merge table would record it once its expansion
    /// completes; `None` when it takes no part in merging.
    arrival: Option<Arrival>,
    /// Whether the state being expanded was merged ([`Execution::merged`]).
    merged_arrival: bool,
    /// After each expansion: the merge table's size, its shallowest recorded depth, and the
    /// depth of the back of `pending`.
    #[cfg(test)]
    merge_census: Vec<(usize, Option<u64>, Option<u64>)>,
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
        // One request: every name the execution mints is apart from every variable of the
        // initial patterns and of the caller's other patterns.
        let mut request_names = RequestNames::of(&initial.iter().collect::<Vec<_>>());
        request_names.extend(&options.request_names);
        let fresh_counter = FreshCounter::for_request_names(request_names);
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
                    trace: PathTrace::default(),
                    retain_trace: options.retain_trace,
                    kind: ExecutionStateKind::Rewritable,
                    observation: None,
                    effects: EffectJournal::default(),
                    io: initial_io.clone(),
                    io_enabled,
                    is_initial_input: true,
                    defined_where: Vec::new(),
                    diagnostics: diagnostics.empty_like(),
                    producer: None,
                }
            })
            .collect::<VecDeque<_>>();
        let mut leaves = Vec::new();
        let mut validated = VecDeque::with_capacity(pending.len());
        // Invariant: `validated` holds, in queue order, the popped states without a surviving macro or alias symbol, and `leaves` one leaf per other popped state; nothing is pushed onto `pending`, so each initial state is popped once.
        while let Some(mut state) = pending.pop_front() {
            // A `\ceil` in a given state is read as deferred atoms (`crate::deferred`): a state
            // resumed from a reported one does not evaluate the operands its run left
            // unevaluated. One over an operand whose definedness depends on an impure
            // application is the unsupported-hook outcome.
            match crate::deferred::resumed_constraints(
                definition,
                std::mem::take(&mut state.pattern.constraints),
            ) {
                Ok(constraints) => state.pattern.constraints = constraints,
                Err(outcome) => {
                    leaves.push(state.leaf(
                        HaltReason::Simplification(outcome.into()),
                        &ObservationLog::default(),
                    ));
                    continue;
                }
            }
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
        let work = Work::new(options.max_work);
        let merge = (options.result_modality == ResultModality::StateSet
            && options.branch_mode == ExecutionBranchMode::ExploreAll)
            .then(ExplorationMerge::default);
        Self {
            definition,
            options,
            solver,
            observation,
            observe,
            fresh_counter,
            observation_log: ObservationLog::default(),
            initial_input_count,
            pending: validated,
            leaves,
            discarded: Vec::new(),
            completed_initial_simplifications: 0,
            bottom_initial_simplifications: 0,
            stopped: None,
            work,
            merge,
            arrival: None,
            merged_arrival: false,
            #[cfg(test)]
            merge_census: Vec::new(),
        }
    }

    /// `max_breadth = Some(0)`: every initial pattern is a `BreadthBound` leaf.
    fn collect_at_breadth_zero(mut self) -> (ExecutionResult, InitialSimplificationStatus) {
        self.drain_at_breadth_bound();
        let modality = self.options.result_modality;
        let leaves = std::mem::take(&mut self.leaves);
        let leaves = self.selected_leaves(leaves);
        (
            ExecutionResult {
                modality,
                leaves,
                effects: Vec::new(),
                discarded: self.discarded,
                coverage: None,
                work: self.work.visited(),
                stack_stops: 0,
                stopped: self.stopped,
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
    /// leaf cut off by a stop during or after the step carries all the work of the step and of
    /// its candidates done before it. Every collection forwards to any collector the caller
    /// holds around the execution, which therefore sees every diagnostic.
    ///
    /// Stops. Every phase of a state's expansion polls for a stop (`stop::check`) or receives
    /// one from the simplifier, the step or the solver on the outer layer of their results; the
    /// state then becomes a `Stopped` leaf, and [`stop_ends_execution`] decides whether the
    /// remaining states are explored. The next state's first poll observes a stop of the request
    /// or of the solver's prelude that a refinement dismissed (`externalise_leaf`).
    fn run(&mut self, timeout_controller: &StepTimeoutController) {
        // `pending` is a stack: `enqueue_execution_states` pushes successors to the front, so a
        // state's children are expanded before its siblings (depth-first). Each push either
        // raises the depth, which `max_depth` bounds, or consumes a remainder, so the loop
        // terminates.
        // Invariant: `pending` holds unexpanded states of depth <= `max_depth`; `leaves` only grows.
        while let Some(state) = self.pending.pop_front() {
            // The work budget: a run that has visited `max_work` states ends at the next one,
            // which is reported unvisited; the other pending states are dropped (`work`).
            if !self.work.visit() {
                self.leaves
                    .push(state.leaf(HaltReason::WorkBound, &self.observation_log));
                self.pending.clear();
                break;
            }
            measure::bump(Counter::RewriteSteps);
            let mut step_timer = timeout_controller.begin_step();
            self.arrival = None;
            match self.expand(state) {
                Ok(successors) => {
                    // A merged arrival took no rewrite step: its time is not a step's time.
                    if std::mem::take(&mut self.merged_arrival) {
                        step_timer.discard_measurement();
                    }
                    self.record_arrival();
                    enqueue_execution_states(&mut self.pending, successors);
                    if let Expansion::BreadthBound = self.breadth_checked() {
                        break;
                    }
                }
                Err(leaf) => {
                    let ends_execution = match &leaf.halt_reason {
                        HaltReason::Stopped(cause) => {
                            // A stop that ends the run is its cause; one local to the state ends
                            // only the state, which is left unrecorded for merging.
                            let ends = stop_ends_execution(cause, &mut step_timer);
                            if ends {
                                self.stopped = Some(cause.clone());
                            }
                            ends
                        }
                        _ => {
                            self.record_arrival();
                            false
                        }
                    };
                    self.leaves.push(leaf);
                    if ends_execution {
                        break;
                    }
                }
            }
            self.evict_unreachable_depths();
        }
    }

    /// The merge point of a state-set run (after E3: the state is normalised, not bottom, and
    /// below the depth bound): whether `state` equals, at its depth, a state whose expansion
    /// completed ([`ExplorationMerge`]), in which case it ends with no leaf and no successor.
    /// Otherwise the state is kept as the arrival `run` records once its own expansion completes
    /// without a stop: a stop in the step or in the simplifications and queries after it leaves
    /// the state unrecorded, so an equal later state is expanded itself.
    ///
    /// Initial inputs (which carry their definedness) and remainder states (which end as leaves
    /// without a step) take no part. The state is kept for comparison only when another path
    /// exists (a state is pending, or a recorded state may still be met); its shape hash is
    /// computed only when its depth holds a recorded state, and its key only when a recorded
    /// state of its hash does.
    fn merged(&mut self, state: &ExecutionState) -> bool {
        let Some(merge) = &mut self.merge else {
            return false;
        };
        if state.is_initial_input
            || !matches!(state.kind, ExecutionStateKind::Rewritable)
            || (self.pending.is_empty() && merge.is_empty())
        {
            return false;
        }
        let mut arrival = Arrival::new(
            state.depth,
            state.pattern.clone(),
            state.effects.clone(),
            state.io.clone(),
            state.io_enabled,
            state.diagnostics.clone(),
        );
        if merge.absorbs(&mut arrival, self.fresh_counter.request()) {
            measure::bump(Counter::ExecutionStatesMerged);
            self.merged_arrival = true;
            return true;
        }
        self.arrival = Some(arrival);
        false
    }

    /// Record the expanded state, if it takes part in merging.
    fn record_arrival(&mut self) {
        if let (Some(merge), Some(arrival)) = (&mut self.merge, self.arrival.take()) {
            merge.record(arrival);
        }
    }

    /// Depth-first order keeps `pending`'s depths non-increasing from front to back (a state's
    /// successors, at its depth or one deeper, go to the front, and the state was the deepest),
    /// so no state arrives at a depth below the back of `pending` any more.
    fn evict_unreachable_depths(&mut self) {
        let Some(merge) = &mut self.merge else {
            return;
        };
        match self.pending.back() {
            Some(shallowest) => merge.evict_below(shallowest.depth),
            None => merge.clear(),
        }
        #[cfg(test)]
        {
            let (recorded, shallowest_recorded) = merge.census();
            self.merge_census.push((
                recorded,
                shallowest_recorded,
                self.pending.back().map(|state| state.depth),
            ));
        }
    }

    /// The per-state pipeline E2 to E7; the polls for a stop sit between its phases (before
    /// constraint simplification, after it, after term simplification, after the rewrite step,
    /// and inside E6 and E7), and a phase whose result is a stop ends the state at once. Returns
    /// the successors `run` enqueues.
    #[deny(clippy::wildcard_enum_match_arm)]
    fn expand(&mut self, state: ExecutionState) -> Phase<Vec<ExecutionState>> {
        let state = self.check_interrupted(state)?;
        if let Some(symbol) = state.pattern.macro_or_alias_symbol() {
            return Err(state.leaf(
                HaltReason::Indeterminate(IndeterminateReason::SurvivingMacroOrAlias { symbol }),
                &self.observation_log,
            ));
        }
        // A successor whose normalization shows its step undefined everywhere another candidate
        // of the step is defined vanishes: those instances are on the other candidates' paths.
        let Some((state, deferred_initial_vacuity)) = self.normalise_constraints(state)? else {
            return Ok(Vec::new());
        };
        let Some(state) = self.simplify_term(state, deferred_initial_vacuity.is_some())? else {
            return Ok(Vec::new());
        };
        if self.merged(&state) {
            return Ok(Vec::new());
        }
        // A `Finished` or `Branch` step attributes its diagnostics to its candidates; any other
        // result halts the state, whose leaf takes the step's whole collection.
        let (rewritten, step_diagnostics) = diagnostic::collect(|| match &state.kind {
            ExecutionStateKind::Rewritable => self.step(&state),
            ExecutionStateKind::Remaining(None) => stuck(self.definition, &state.pattern),
            ExecutionStateKind::Remaining(Some(undecided)) => {
                Ok(undecided.clone().into_result(state.pattern.clone()))
            }
        });
        // A stopped step has no successor set: the state is the leaf, with the step's work.
        let rewritten = match rewritten {
            Ok(rewritten) => rewritten,
            Err(stop) => {
                return Err(interrupted_with(
                    self.stopped_leaf(state, stop),
                    &[&step_diagnostics],
                ));
            }
        };
        let mut state = match self.check_interrupted(state) {
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
                let (expanded, diagnostics) = diagnostic::collect(|| self.finished(state, applied));
                expanded.map_err(|leaf| interrupted_with(leaf, &[&step_diagnostics, &diagnostics]))
            }
            RewriteResult::Branch {
                original,
                branches,
                remainder,
                trivial,
            } => {
                let (expanded, diagnostics) = diagnostic::collect(|| {
                    self.branch(state, original, branches, remainder, trivial)
                });
                expanded.map_err(|leaf| interrupted_with(leaf, &[&step_diagnostics, &diagnostics]))
            }
        }
    }

    /// Poll for a stop between two phases of the state's expansion: a cancelled request, a
    /// failed solver prelude, or the step's passed deadline turns the state into a `Stopped`
    /// leaf ([`Self::stopped_leaf`]).
    fn check_interrupted(&self, state: ExecutionState) -> Phase<ExecutionState> {
        match stop::check() {
            Ok(()) => Ok(state),
            Err(stop) => Err(self.stopped_leaf(state, stop)),
        }
    }

    /// The leaf of a state whose expansion stopped: the state as it stood when the stop was
    /// observed, publishing the stop's cause; `run` discards the step's duration measurement
    /// ([`stop_ends_execution`]).
    fn stopped_leaf(&self, state: ExecutionState, stop: Stop) -> ExecutionLeaf {
        state.leaf(
            HaltReason::Stopped(stop.into_cause()),
            &self.observation_log,
        )
    }

    /// E2: the substitution is normalised, the constraints simplified with `keep_partial`, and
    /// the retained substitution predicates re-added. A `False` at depth 0 with a non-empty
    /// retained substitution is deferred: the first step is attempted from the state as given,
    /// and the simplified state is reported as `Vacuous` only if no rule applies. Any other
    /// `False` is a `Vacuous` leaf. Returns the deferred pattern.
    ///
    /// Either way the state denotes no configuration; the deferral changes only which leaf
    /// reports that (a `Vacuous` leaf at depth 0, or the result of the first step taken from the
    /// unsimplified state). No semantic reason selects the deferral; it is a reporting choice.
    fn normalise_constraints(
        &mut self,
        mut state: ExecutionState,
    ) -> Phase<Option<(ExecutionState, Option<Pattern>)>> {
        let retained_substitution =
            normalize_pattern_substitution(&mut state.pattern, self.definition.sort_graph());
        let pattern_before_constraint_simplification = state.pattern.clone();
        let mut deferred_initial_vacuity = None;
        let normalization = state
            .producer
            .as_ref()
            .and_then(|producer| producer.normalization.clone());
        let (simplified_constraints, diagnostics) = match normalization {
            // The step that built this successor simplified its constraints already.
            Some(normalization) => (
                Ok(Ok(normalization.constraints.clone())),
                normalization.constraint_diagnostics.clone(),
            ),
            None => diagnostic::collect(|| {
                simplify_predicates_with_solver(
                    self.definition,
                    &state.pattern.constraints,
                    &[],
                    SimplificationOptions::keep_partial(self.options.max_simplification_iterations),
                    self.solver,
                )
            }),
        };
        state.diagnostics.extend(&diagnostics);
        let simplified_constraints = match simplified_constraints {
            Ok(simplified_constraints) => simplified_constraints,
            Err(stop) => return Err(self.stopped_leaf(state, stop)),
        };
        let mut state = self.check_interrupted(state)?;
        match simplified_constraints {
            Ok(mut constraints) => {
                retain_substitution_predicates(
                    &mut constraints,
                    &retained_substitution,
                    self.definition.sort_graph(),
                );
                state.pattern.constraints = constraints;
                normalize_pattern_substitution(&mut state.pattern, self.definition.sort_graph());
            }
            Err(error) => {
                return Err(state.leaf(HaltReason::Simplification(error), &self.observation_log));
            }
        }
        if predicates_truth(&state.pattern.constraints) == Truth::False {
            if state.depth == 0 && !retained_substitution.is_empty() {
                // A contradiction exposed only by the input substitution does not prevent the
                // first rewrite attempt (see `normalise_constraints`). If no rule applies, the
                // simplified state below is still returned as vacuous.
                deferred_initial_vacuity = Some(state.pattern.clone());
                state.pattern = pattern_before_constraint_simplification;
            } else {
                if state.is_initial_input {
                    self.completed_initial_simplifications += 1;
                    self.bottom_initial_simplifications += 1;
                }
                let applied = state.trace.last_rewrite();
                let refuted_ceil = pattern_before_constraint_simplification
                    .constraints
                    .iter()
                    .find(|predicate| {
                        matches!(predicate, Predicate::Ceil(_) | Predicate::Defined(_))
                    });
                let halt_reason = match (applied, refuted_ceil) {
                    (Some(applied), Some(obligation)) => HaltReason::Trivial {
                        depth: state.depth,
                        rule_id: Some(applied.unique_id.clone()),
                        label: applied.label.clone(),
                        obligation: obligation.clone(),
                        contradicted_total: None,
                    },
                    _ => vacuous_halt(
                        state.depth,
                        &state.pattern,
                        state.trace.last_rewrite(),
                        None,
                    ),
                };
                if matches!(halt_reason, HaltReason::Trivial { .. }) {
                    return self.undefined_step_leaf(state, halt_reason).map(|()| None);
                }
                return Err(state.leaf(halt_reason, &self.observation_log));
            }
        }
        Ok(Some((state, deferred_initial_vacuity)))
    }

    /// E3: the term is simplified under its constraints, the simplification is observed and
    /// traced, initial-input bookkeeping is done (a `False` after term simplification, or a
    /// refuted fact of the initial configuration's own definedness, is `Vacuous`), and the depth
    /// bound is checked (`DepthBound` leaf).
    fn simplify_term(
        &mut self,
        mut state: ExecutionState,
        vacuity_deferred: bool,
    ) -> Phase<Option<ExecutionState>> {
        let pattern_before_term_simplification = state.pattern.clone();
        state.io_enabled &= pattern_supports_execution_io(&state.pattern);
        // The step that built this successor simplified its term already, under the same
        // constraints and console (`normalize_successor`).
        let normalized = state
            .producer
            .as_ref()
            .and_then(|producer| producer.normalization.as_ref())
            .and_then(|normalization| normalization.term.as_ref())
            .map(|term| {
                (
                    term.simplified.clone(),
                    term.diagnostics.clone(),
                    term.io.clone(),
                )
            });
        let mut normalized_io = None;
        let mut io_evaluation =
            (normalized.is_none() && state.io_enabled).then(|| state.io.begin_evaluation());
        let (simplified, diagnostics) = match normalized {
            Some((simplified, diagnostics, io)) => {
                normalized_io = io;
                (Ok(Ok(simplified)), diagnostics)
            }
            None => diagnostic::collect(|| match io_evaluation.as_mut() {
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
            }),
        };
        state.diagnostics.extend(&diagnostics);
        let simplified = match simplified {
            Ok(simplified) => simplified,
            Err(stop) => return Err(self.stopped_leaf(state, stop)),
        };
        let mut state = self.check_interrupted(state)?;
        let (undefined_term, contradicted_total) = match simplified {
            Ok(simplified) => {
                let simplified = simplified.into_parts();
                let undefined_term = simplified.undefined_term.clone();
                let contradicted_total = simplified.contradicted_total.clone();
                state.pattern.term = simplified.term;
                state.pattern.constraints.extend(simplified.conditions);
                normalize_pattern_substitution(&mut state.pattern, self.definition.sort_graph());
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
                (undefined_term, contradicted_total)
            }
            Err(error) => {
                return Err(state.leaf(HaltReason::Simplification(error), &self.observation_log));
            }
        };
        if state.is_initial_input {
            self.completed_initial_simplifications += 1;
            if !vacuity_deferred && predicates_truth(&state.pattern.constraints) == Truth::False {
                self.bottom_initial_simplifications += 1;
                let halt_reason = vacuous_halt(
                    state.depth,
                    &state.pattern,
                    state.trace.last_rewrite(),
                    contradicted_total,
                );
                return Err(state.leaf(halt_reason, &self.observation_log));
            }
            if !vacuity_deferred {
                // The initial configuration is the caller's pattern `t ∧ φ`, which denotes
                // `⌈t⌉ ∧ t ∧ φ`, and nothing has decided its own facts (I7'). A refuted fact
                // means it has no instance, exactly as constraints simplified to `\bottom` do;
                // that holds as well when the caller asserts the facts
                // (`assume_initial_defined`), since asserting a false fact leaves nothing. A
                // successor needs no such decision: its step decided its right-hand side's
                // definedness, and term simplification conjoins its own obligations.
                let (verdict, diagnostics) = diagnostic::collect(|| {
                    UndecidedFacts::of_pattern(self.definition, &state.pattern).decide(
                        self.definition,
                        SimplificationOptions {
                            max_iterations: self.options.max_simplification_iterations,
                            ..SimplificationOptions::default()
                        },
                        self.solver,
                    )
                });
                state.diagnostics.extend(&diagnostics);
                match verdict {
                    Ok(FactsVerdict::Refuted) => {
                        self.bottom_initial_simplifications += 1;
                        // No equation of a `total` symbol emptied it: its own fact did.
                        let halt_reason = vacuous_halt(
                            state.depth,
                            &state.pattern,
                            state.trace.last_rewrite(),
                            None,
                        );
                        return Err(state.leaf(halt_reason, &self.observation_log));
                    }
                    Ok(FactsVerdict::NotRefuted(_)) => {}
                    Err(stop) => return Err(self.stopped_leaf(state, stop)),
                }
                if !self.options.assume_initial_defined {
                    state = self.restrict_to_defined_instances(state)?;
                }
            }
        }
        if predicates_truth(&state.pattern.constraints) == Truth::False
            && let Some(term) = undefined_term
        {
            let applied = state.trace.last_rewrite();
            let halt_reason = HaltReason::Trivial {
                depth: state.depth,
                rule_id: applied.map(|entry| entry.unique_id.clone()),
                label: applied.and_then(|entry| entry.label.clone()),
                obligation: Predicate::Ceil(term),
                contradicted_total,
            };
            return self.undefined_step_leaf(state, halt_reason).map(|()| None);
        }
        if let Some(execution) = io_evaluation {
            state.io = execution.commit();
        } else if let Some(io) = normalized_io {
            state.io = io;
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
        // Normalized: an undefined step of the step that produced it would have shown above.
        state.producer = None;
        Ok(Some(state))
    }

    /// The initial configuration, which the run does not assume defined, restricted to its
    /// defined instances ([`initial_definedness`]): with none it is a `Vacuous` leaf, counted as
    /// simplified to `\bottom`; otherwise its open obligations restrict what its step leaves
    /// over (`ExecutionState::defined_where`), named by an
    /// [`BackendDiagnostic::UndefinedInitialInstances`] on its path.
    fn restrict_to_defined_instances(
        &mut self,
        mut state: ExecutionState,
    ) -> Phase<ExecutionState> {
        let (definedness, diagnostics) = diagnostic::collect(|| {
            initial_definedness(
                self.definition,
                &state.pattern,
                SimplificationOptions {
                    max_iterations: self.options.max_simplification_iterations,
                    ..SimplificationOptions::default()
                },
                self.solver,
            )
        });
        state.diagnostics.extend(&diagnostics);
        match definedness {
            Ok(InitialDefinedness::Undefined) => {
                self.bottom_initial_simplifications += 1;
                let halt_reason = vacuous_halt(
                    state.depth,
                    &state.pattern,
                    state.trace.last_rewrite(),
                    None,
                );
                Err(state.leaf(halt_reason, &self.observation_log))
            }
            Ok(InitialDefinedness::Where(definedness)) => {
                if !definedness.is_empty() {
                    state
                        .diagnostics
                        .extend(&[BackendDiagnostic::UndefinedInitialInstances {
                            definedness: definedness.clone(),
                        }]);
                    state.defined_where = definedness;
                }
                Ok(state)
            }
            Ok(InitialDefinedness::Unsupported(error)) => {
                Err(state.leaf(HaltReason::Simplification(error), &self.observation_log))
            }
            Err(stop) => Err(self.stopped_leaf(state, stop)),
        }
    }

    /// E4: one priority-grouped rewrite step (backend.rewrite.step) under the option's mode.
    fn step(&mut self, state: &ExecutionState) -> Stoppable<RewriteResult> {
        rewrite_step_with_optional_execution(
            self.definition,
            &state.pattern,
            &mut self.fresh_counter,
            SimplificationOptions::keep_partial(self.options.max_simplification_iterations),
            self.solver,
            self.options.mode,
            if self.options.assume_initial_defined {
                SubjectDefinedness::Assumed
            } else {
                SubjectDefinedness::Where(&state.defined_where)
            },
            state.io_enabled.then_some(&state.io),
            // Execution reads a variable-free configuration as one state.
            true,
        )
    }

    /// E5: `Stuck` (or `Vacuous` when the initial vacuity was deferred), `Trivial`, `Vacuous`,
    /// and `Indeterminate` results become leaves with the matching `HaltReason`.
    #[deny(clippy::wildcard_enum_match_arm)]
    fn halt_leaf(
        &mut self,
        state: ExecutionState,
        rewritten: RewriteResult,
        deferred_initial_vacuity: Option<Pattern>,
    ) -> ExecutionLeaf {
        match rewritten {
            RewriteResult::Stuck(pattern) => match deferred_initial_vacuity {
                Some(pattern) => {
                    let halt_reason =
                        vacuous_halt(state.depth, &pattern, state.trace.last_rewrite(), None);
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
                let halt_reason =
                    vacuous_halt(state.depth, &pattern, state.trace.last_rewrite(), None);
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
    ) -> Phase<Vec<ExecutionState>> {
        if let Some(rule) = selected_stop_rule(&applied, &self.options.cut_point_rules) {
            let mut applied = applied;
            let producer = Producer::of(&state, &applied, Vec::new());
            commit_proposed_effects(&mut state, &applied);
            // The cut-point rule is proposed, not committed: the `CutPointRule` leaf stays at
            // this state's depth and branch position and carries the successor in
            // `next_states`, with the successor's diagnostics and with the events it would add
            // to this branch, recorded on its own head: the evaluations of the higher-priority
            // remainder it was applied to (a restriction of this state that only the successor
            // derives from), its transition, and its normalization. A leaf that reports the
            // successor's pattern instead (a failed normalization or a bottom successor) is the
            // successor's, so it takes that head.
            let mut candidate_observation = applied_observation(
                self.definition,
                state.observation,
                &applied,
                &mut self.observation_log,
                self.observation,
            );
            let (simplified, diagnostics) = diagnostic::collect(|| {
                simplify_result_pattern(
                    self.definition,
                    &applied.pattern,
                    self.options.max_simplification_iterations,
                    self.solver,
                    state.depth,
                    &mut state.trace,
                    Some(&mut candidate_observation),
                    &mut self.observation_log,
                    self.observation,
                )
            });
            extend_distinct(&mut applied.diagnostics, &diagnostics);
            applied.pattern = match simplified {
                Ok(Ok(simplified)) => {
                    state.effects.commit(simplified.effects);
                    simplified.pattern
                }
                Ok(Err(error)) => {
                    let mut state = self.check_interrupted(state)?;
                    // The leaf reports the successor's pattern, so the successor's diagnostics
                    // and observations.
                    state.diagnostics.extend(&applied.diagnostics);
                    state.observation = candidate_observation;
                    return Err(state.leaf_with_pattern(
                        applied.pattern,
                        HaltReason::Simplification(error),
                        &self.observation_log,
                    ));
                }
                // The proposed successor is not normalised: the state is the leaf.
                Err(stop) => return Err(self.stopped_leaf(state, stop)),
            };
            let mut state = self.check_interrupted(state)?;
            if predicates_truth(&applied.pattern.constraints) == Truth::False {
                // The proposed successor is empty: the step is undefined on this state, whose
                // leaf it is, as for a committed successor.
                state.diagnostics.extend(&applied.diagnostics);
                let io = applied
                    .io
                    .as_ref()
                    .or(state.io_enabled.then_some(&state.io));
                let halt_reason = match self.bottom_successor_halt(
                    &producer.successor,
                    &producer.before.constraints,
                    io,
                    state.depth + 1,
                    &applied.pattern,
                    &mut state.diagnostics,
                ) {
                    Ok(halt_reason) => halt_reason,
                    Err(stop) => return Err(self.stopped_leaf(state, stop)),
                };
                state.producer = Some(std::rc::Rc::new(producer));
                return self
                    .undefined_step_leaf(state, halt_reason)
                    .map(|()| Vec::new());
            }
            return Err(self.cut_point_leaf(state, rule, applied, candidate_observation));
        }
        let terminal_rule = selected_stop_rule(&applied, &self.options.terminal_rules);
        let producer = Producer::of(&state, &applied, Vec::new());
        let mut next = next_state(
            self.definition,
            state,
            applied,
            &mut self.observation_log,
            self.observation,
        );
        next.producer = Some(std::rc::Rc::new(producer));
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
                Ok(Ok(simplified)) => {
                    next.effects.commit(simplified.effects);
                    simplified.pattern
                }
                Ok(Err(error)) => {
                    let next = self.check_interrupted(next)?;
                    return Err(next.leaf(HaltReason::Simplification(error), &self.observation_log));
                }
                Err(stop) => return Err(self.stopped_leaf(next, stop)),
            };
            let mut next = self.check_interrupted(next)?;
            if predicates_truth(&next.pattern.constraints) == Truth::False {
                let producer = next
                    .producer
                    .clone()
                    .expect("the successor's producer is set");
                let halt_reason = match self.bottom_successor_halt(
                    &producer.successor,
                    &producer.before.constraints,
                    next.io_enabled.then_some(&next.io),
                    next.depth,
                    &next.pattern,
                    &mut next.diagnostics,
                ) {
                    Ok(halt_reason) => halt_reason,
                    Err(stop) => return Err(self.stopped_leaf(next, stop)),
                };
                return self
                    .undefined_step_leaf(next, halt_reason)
                    .map(|()| Vec::new());
            }
            return Err(next.leaf(HaltReason::TerminalRule { rule }, &self.observation_log));
        }
        Ok(vec![next])
    }

    /// The `CutPointRule` leaf for a proposed successor that is normalized, on its own
    /// observation head `candidate`, and not bottom, once its effects are committed to `state`.
    /// The leaf is this state: it keeps this state's depth, branch and diagnostics; the
    /// successor, carried in `next_states`, owns its diagnostics and the events it would add to
    /// this branch.
    fn cut_point_leaf(
        &self,
        state: ExecutionState,
        rule: String,
        mut applied: AppliedRule,
        candidate: ObservationHead,
    ) -> ExecutionLeaf {
        applied.observations = self
            .observation_log
            .events_since(candidate, state.observation);
        state.leaf(
            HaltReason::CutPointRule {
                rule,
                next_states: vec![applied],
            },
            &self.observation_log,
        )
    }

    /// E7: several rules applied, or one with a complete remainder. Under `StopAtBranch`, the
    /// original and every child are simplified and reported together. Under `ExploreAll`, applied
    /// branches and the remainder become the returned successors.
    fn branch(
        &mut self,
        mut state: ExecutionState,
        original: Pattern,
        branches: Vec<AppliedRule>,
        mut remainder: Option<RemainderBranch>,
        trivial: Vec<TrivialApplication>,
    ) -> Phase<Vec<ExecutionState>> {
        record_trivial_candidates(&mut self.discarded, &trivial, &original, self.observation);
        // The instances the step leaves without a defined successor are no candidate's and not
        // the remainder's: each trivial entry's are a leaf of their own, whatever the other
        // candidates become.
        for entry in &trivial {
            match self.undefined_leaf(&state, entry) {
                Ok(Some(leaf)) => self.leaves.push(leaf),
                Ok(None) => {}
                Err(stop) => return Err(self.stopped_leaf(state, stop)),
            }
        }
        if branches.len() == 1 && remainder.is_none() {
            // The only candidate is the unique successor of this state, whatever the branch
            // mode: the other instances are the trivial entries' leaves above, so the step is no
            // branch point, and it goes on exactly as a `Finished` step does, the stop rules
            // included. Its successor is normalised by its own expansion, where a `\bottom`
            // constraint makes it `Vacuous` (or `Trivial`) rather than leaving this state stuck.
            let applied = branches.into_iter().next().expect("one branch remains");
            return self.finished(state, applied);
        }
        if self.options.branch_mode == ExecutionBranchMode::StopAtBranch {
            // The configuration the step was taken from, on its path: the leaf of a candidate
            // whose normalization shows it undefined.
            let parent = state.clone();
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
                Ok(Ok(simplified)) => {
                    state.effects.commit(simplified.effects);
                    simplified.pattern
                }
                Ok(Err(error)) => {
                    let state = self.check_interrupted(state)?;
                    return Err(state.leaf_with_pattern(
                        original,
                        HaltReason::Simplification(error),
                        &self.observation_log,
                    ));
                }
                Err(stop) => return Err(self.stopped_leaf(state, stop)),
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
            // The candidates normalized to `\bottom` and shown undefined, each with its successor
            // as the step built it, and the successors as built of the other candidates, which
            // are defined.
            let mut undefined_candidates = Vec::new();
            let mut defined_successors = Vec::new();
            for mut applied in branches {
                let built = applied.pattern.clone();
                // Each candidate's normalization is recorded on its own observation head, after
                // its transition, as it would be on the branch the candidate extends.
                let mut observation = applied_observation(
                    self.definition,
                    state.observation,
                    &applied,
                    &mut self.observation_log,
                    self.observation,
                );
                let (simplified, diagnostics) = diagnostic::collect(|| {
                    simplify_result_pattern(
                        self.definition,
                        &applied.pattern,
                        self.options.max_simplification_iterations,
                        self.solver,
                        state.depth + 1,
                        &mut state.trace,
                        Some(&mut observation),
                        &mut self.observation_log,
                        self.observation,
                    )
                });
                extend_distinct(&mut applied.diagnostics, &diagnostics);
                match simplified {
                    Ok(Ok(simplified)) => {
                        let discarded_id = self
                            .observation
                            .filter(|options| {
                                predicates_truth(&simplified.pattern.constraints) == Truth::False
                                    && options.observes(&applied.unique_id)
                            })
                            .map(|_| TransitionId {
                                rule: applied.unique_id.clone(),
                                target: PatternDigest::of(&applied.pattern),
                            });
                        applied.pattern = simplified.pattern;
                        applied.effects.extend(simplified.effects);
                        if predicates_truth(&applied.pattern.constraints) != Truth::False {
                            defined_successors.push(built);
                            simplified_branches.push((applied, observation));
                            continue;
                        }
                        // An empty candidate is no successor; an undefined one is an undefined
                        // step of this state, reported below once every candidate is known.
                        let io = applied
                            .io
                            .as_ref()
                            .or(state.io_enabled.then_some(&state.io));
                        let (undefined, work) = diagnostic::collect(|| {
                            successor_undefinedness(
                                self.definition,
                                &built,
                                &applied.before.constraints,
                                SimplificationOptions::keep_partial(
                                    self.options.max_simplification_iterations,
                                ),
                                self.solver,
                                io,
                            )
                        });
                        extend_distinct(&mut applied.diagnostics, &work);
                        match undefined {
                            Ok(Some(undefined)) => {
                                undefined_candidates.push((applied, built, undefined));
                            }
                            Ok(None) => {
                                if let Some(id) = discarded_id {
                                    self.discarded.push(UncommittedObservation {
                                        id,
                                        rule_label: applied.label,
                                        effects: applied.effects,
                                        reason: UncommittedReason::RolledBack,
                                    });
                                }
                            }
                            Err(stop) => return Err(self.stopped_leaf(state, stop)),
                        }
                    }
                    Ok(Err(error)) => {
                        // The failure is reported on the parent's leaf, with the diagnostics of
                        // the work on the candidate that failed.
                        state.diagnostics.extend(&applied.diagnostics);
                        failed_branch = Some(error);
                        break;
                    }
                    // A candidate is not normalised: the state is the leaf.
                    Err(stop) => return Err(self.stopped_leaf(state, stop)),
                }
            }
            if let Some(error) = failed_branch {
                let state = self.check_interrupted(state)?;
                return Err(state.leaf_with_pattern(
                    original,
                    HaltReason::Simplification(error),
                    &self.observation_log,
                ));
            }
            // Each undefined candidate is an undefined step of this state where no defined
            // candidate applies, reported as when its successor is expanded: the step goes on
            // with the defined candidates only, so one of them alone is this state's unique
            // successor.
            let undefined_step = !undefined_candidates.is_empty();
            for (applied, built, undefined) in undefined_candidates {
                let mut diagnostics = parent.diagnostics.clone();
                diagnostics.extend(&applied.diagnostics);
                let producer = Producer {
                    parent: parent.clone(),
                    before: applied.before,
                    successor: built,
                    rule_id: applied.unique_id,
                    label: applied.label,
                    effects: applied.effects,
                    remainder_simplifications: applied.remainder_simplifications,
                    siblings: Vec::new(),
                    defined_siblings: defined_successors.clone(),
                    normalization: None,
                };
                match self.producer_leaf(diagnostics, &producer, undefined.halt(state.depth + 1)) {
                    Ok(Some(leaf)) => self.leaves.push(leaf),
                    Ok(None) => {}
                    Err(stop) => return Err(self.stopped_leaf(state, stop)),
                }
            }
            let mut branches = simplified_branches;
            let mut remainder_observation_head = None;
            if let Some(candidate) = &mut remainder {
                let mut observation = remainder_observation(
                    self.definition,
                    state.observation,
                    state.pattern.clone(),
                    candidate,
                    &mut self.observation_log,
                    self.observation,
                );
                let (simplified, diagnostics) = diagnostic::collect(|| {
                    simplify_result_pattern(
                        self.definition,
                        &candidate.pattern,
                        self.options.max_simplification_iterations,
                        self.solver,
                        state.depth,
                        &mut state.trace,
                        Some(&mut observation),
                        &mut self.observation_log,
                        self.observation,
                    )
                });
                remainder_observation_head = observation;
                extend_distinct(&mut candidate.diagnostics, &diagnostics);
                candidate.pattern = match simplified {
                    Ok(Ok(simplified)) => {
                        candidate.effects.extend(simplified.effects);
                        simplified.pattern
                    }
                    Ok(Err(error)) => {
                        state.diagnostics.extend(&candidate.diagnostics);
                        let state = self.check_interrupted(state)?;
                        return Err(state.leaf_with_pattern(
                            original,
                            HaltReason::Simplification(error),
                            &self.observation_log,
                        ));
                    }
                    // The remainder is not normalised: the state is the leaf.
                    Err(stop) => return Err(self.stopped_leaf(state, stop)),
                };
                if predicates_truth(&candidate.pattern.constraints) == Truth::False {
                    remainder = None;
                }
            }
            let state = self.check_interrupted(state)?;
            match (branches.len(), remainder.is_some()) {
                // Every instance of the state is on an undefined step's leaf.
                (0, false) if undefined_step => return Ok(Vec::new()),
                (0, false) => {
                    return Err(state.leaf_with_pattern(
                        original,
                        HaltReason::Stuck,
                        &self.observation_log,
                    ));
                }
                (1, false) => {
                    // The only surviving candidate is the unique successor of this state, as a
                    // `Finished` step's application is: the stop rules apply to it alike. It is
                    // already normalized, on its own head, and not bottom.
                    let (applied, observation) = branches.pop().expect("one branch remains");
                    if let Some(rule) = selected_stop_rule(&applied, &self.options.cut_point_rules)
                    {
                        let mut state = state;
                        commit_proposed_effects(&mut state, &applied);
                        return Err(self.cut_point_leaf(state, rule, applied, observation));
                    }
                    let terminal_rule = selected_stop_rule(&applied, &self.options.terminal_rules);
                    let next = commit_applied(state, applied, observation);
                    if let Some(rule) = terminal_rule {
                        return Err(
                            next.leaf(HaltReason::TerminalRule { rule }, &self.observation_log)
                        );
                    }
                    return Ok(vec![next]);
                }
                (0, true) => {
                    let remainder = remainder.take().expect("one remainder remains");
                    return Ok(vec![commit_remainder(
                        state,
                        remainder,
                        remainder_observation_head,
                    )]);
                }
                _ => {
                    // The reported candidates are not committed: each carries the events it
                    // would add to the parent's branch.
                    let branches = branches
                        .into_iter()
                        .map(|(mut applied, observation)| {
                            applied.observations = self
                                .observation_log
                                .events_since(observation, state.observation);
                            applied
                        })
                        .collect();
                    if let Some(candidate) = &mut remainder {
                        candidate.observations = self
                            .observation_log
                            .events_since(remainder_observation_head, state.observation);
                    }
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
        let successors = branches
            .iter()
            .map(|applied| applied.pattern.clone())
            .collect::<Vec<_>>();
        for (index, applied) in branches.into_iter().enumerate() {
            let siblings = successors
                .iter()
                .enumerate()
                .filter(|(other, _)| *other != index)
                .map(|(_, sibling)| sibling.clone())
                .collect();
            let producer = Producer::of(&state, &applied, siblings);
            let mut successor = next_state(
                self.definition,
                state.clone(),
                applied,
                &mut self.observation_log,
                self.observation,
            );
            successor.producer = Some(std::rc::Rc::new(producer));
            next.push(successor);
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

    /// The `Trivial` halt at `depth` of a step whose successor, `built` as the step built it from
    /// a pattern with the constraints `base`, normalized to `normalized`, whose constraints are `\bottom`: the failing obligation and
    /// the contradicted attribute when [`successor_undefinedness`] shows the successor undefined,
    /// the false constraint of `normalized` otherwise. The deciding work is `diagnostics`'.
    fn bottom_successor_halt(
        &self,
        built: &Pattern,
        base: &[Predicate],
        io: Option<&ExecutionIoState>,
        depth: u64,
        normalized: &Pattern,
        diagnostics: &mut PathDiagnostics,
    ) -> Stoppable<HaltReason> {
        let (undefined, work) = diagnostic::collect(|| {
            successor_undefinedness(
                self.definition,
                built,
                base,
                SimplificationOptions::keep_partial(self.options.max_simplification_iterations),
                self.solver,
                io,
            )
        });
        diagnostics.extend(&work);
        Ok(undefined?.map_or_else(
            || trivial_halt(depth, normalized),
            |undefined| undefined.halt(depth),
        ))
    }

    /// The `Trivial` leaf of the step that produced `state`, a successor whose normalization
    /// showed it undefined (`halt_reason`, at the successor's depth), as `Err`; `Ok` when no
    /// instance is left undefined ([`Self::producer_leaf`]). A state with no recorded producer (no
    /// step produced it) is its own leaf, as before.
    fn undefined_step_leaf(
        &mut self,
        mut state: ExecutionState,
        halt_reason: HaltReason,
    ) -> Phase<()> {
        let Some(producer) = state.producer.take() else {
            return Err(state.leaf(halt_reason, &self.observation_log));
        };
        match self.producer_leaf(state.diagnostics.clone(), &producer, halt_reason) {
            Ok(Some(leaf)) => Err(leaf),
            Ok(None) => Ok(()),
            Err(stop) => Err(self.stopped_leaf(state, stop)),
        }
    }

    /// The `Trivial` leaf of `producer`'s step, whose successor is undefined (`halt_reason`, at
    /// the successor's depth); `None` when no instance is left undefined. `diagnostics` are the
    /// path's up to the finding.
    ///
    /// The leaf is the configuration the step was taken from, at that configuration's depth and
    /// on its path extended by the higher-priority remainder simplifications the candidate went
    /// through, restricted to the condition under which this candidate applies and to the
    /// instances no other applied candidate of the step takes to a defined successor; the
    /// step's events are rolled back (`discarded`). A sibling not yet normalized counts as
    /// defined unless [`successor_undefinedness`] shows it undefined, so an instance is reported
    /// undefined only when the step is shown undefined on it. A stop is returned.
    fn producer_leaf(
        &mut self,
        mut diagnostics: PathDiagnostics,
        producer: &Producer,
        halt_reason: HaltReason,
    ) -> Stoppable<Option<ExecutionLeaf>> {
        let bound = pattern_variables(&producer.before);
        let mut constraints = producer.before.constraints.clone();
        let branch = beyond(
            &producer.successor.constraints,
            &producer.before.constraints,
        );
        extend_unique_predicates(&mut constraints, closed_over(branch, &bound));
        let parent_io = producer.parent.io_enabled.then_some(&producer.parent.io);
        let mut defined = Vec::with_capacity(producer.siblings.len());
        for sibling in &producer.siblings {
            // The sibling's simplification decides this leaf's constraint, so its work is the
            // leaf's.
            let (undefined, work) = diagnostic::collect(|| {
                successor_undefinedness(
                    self.definition,
                    sibling,
                    &producer.before.constraints,
                    SimplificationOptions::keep_partial(self.options.max_simplification_iterations),
                    self.solver,
                    parent_io,
                )
            });
            diagnostics.extend(&work);
            if undefined?.is_none() {
                defined.push(sibling);
            }
        }
        for sibling in defined.into_iter().chain(&producer.defined_siblings) {
            let applies = beyond(&sibling.constraints, &producer.before.constraints);
            constraints.push(Predicate::Not(Box::new(conjunction(closed_over(
                applies, &bound,
            )))));
        }
        let mut pattern = Pattern {
            term: producer.before.term.clone(),
            constraints,
        };
        let (simplified, work) = diagnostic::collect(|| {
            simplify_predicates_with_solver(
                self.definition,
                &pattern.constraints,
                &[],
                SimplificationOptions::keep_partial(self.options.max_simplification_iterations),
                self.solver,
            )
        });
        diagnostics.extend(&work);
        match simplified {
            Ok(Ok(simplified)) => pattern.constraints = simplified,
            // A failed simplification only loses precision.
            Ok(Err(_failure)) => {}
            Err(stop) => stop.forgo_refinement(),
        }
        let empty = predicates_truth(&pattern.constraints) == Truth::False
            || matches!(
                self.solver
                    .is_sat(&pattern.constraints, &Substitution::new())?,
                Ok(Satisfiability::Unsat)
            );
        if let Some(options) = self.observation
            && options.observes(&producer.rule_id)
        {
            self.discarded.push(UncommittedObservation {
                id: TransitionId {
                    rule: producer.rule_id.clone(),
                    target: PatternDigest::of(&producer.successor),
                },
                rule_label: producer.label.clone(),
                effects: producer.effects.clone(),
                reason: UncommittedReason::RolledBack,
            });
        }
        if empty {
            return Ok(None);
        }
        let halt_reason = match halt_reason {
            HaltReason::Trivial {
                depth,
                obligation,
                contradicted_total,
                ..
            } => HaltReason::Trivial {
                depth,
                rule_id: Some(producer.rule_id.clone()),
                label: producer.label.clone(),
                obligation,
                contradicted_total,
            },
            other => other,
        };
        let mut leaf = ExecutionState {
            diagnostics,
            ..producer.parent.clone()
        };
        for simplification in &producer.remainder_simplifications {
            leaf.observation = self.observation_log.append_simplification(
                leaf.observation,
                self.definition,
                simplification.before.clone(),
                &simplification.after,
                &simplification.applied_rules,
                &simplification.effects,
                self.observation,
            );
            leaf.effects.commit(simplification.effects.iter().cloned());
            leaf.trace.extend(
                simplification
                    .applied_rules
                    .iter()
                    .cloned()
                    .map(|unique_id| TraceEntry {
                        depth: leaf.depth,
                        kind: TraceKind::Simplification,
                        label: None,
                        unique_id,
                    }),
            );
        }
        Ok(Some(leaf.leaf_with_pattern(
            pattern,
            halt_reason,
            &self.observation_log,
        )))
    }

    /// The `Trivial` leaf of `entry`, a bottom-result sub-case of the step `state` took: the
    /// pattern `entry` was applied to, restricted to `entry.undefined`, on `state`'s path
    /// extended by the higher-priority remainder simplifications it went through. `None` when
    /// that set is shown empty ([`TrivialApplication::decided_undefined_instances`]): a leaf
    /// reports instances, and the step left none undefined there. A stop of the emptiness query
    /// is returned.
    fn undefined_leaf(
        &mut self,
        state: &ExecutionState,
        entry: &TrivialApplication,
    ) -> Stoppable<Option<ExecutionLeaf>> {
        let (pattern, diagnostics) = diagnostic::collect(|| {
            entry.decided_undefined_instances(
                self.definition,
                self.options.max_simplification_iterations,
                self.solver,
            )
        });
        let Some(pattern) = pattern? else {
            return Ok(None);
        };
        let mut leaf = state.clone();
        leaf.diagnostics.extend(&entry.diagnostics);
        leaf.diagnostics.extend(&diagnostics);
        for simplification in &entry.remainder_simplifications {
            leaf.observation = self.observation_log.append_simplification(
                leaf.observation,
                self.definition,
                simplification.before.clone(),
                &simplification.after,
                &simplification.applied_rules,
                &simplification.effects,
                self.observation,
            );
            leaf.effects.commit(simplification.effects.iter().cloned());
            leaf.trace.extend(
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
        let halt_reason = applied_trivial_halt(state.depth + 1, entry);
        Ok(Some(leaf.leaf_with_pattern(
            pattern,
            halt_reason,
            &self.observation_log,
        )))
    }

    /// After a push: `BreadthBound` when `pending` exceeds `max_breadth` (the bound appends
    /// its live frontier to leaves already reached), else `Queued`.
    fn breadth_checked(&mut self) -> Expansion {
        if self
            .options
            .max_breadth
            .is_some_and(|bound| self.pending.len() > bound)
        {
            self.drain_at_breadth_bound();
            Expansion::BreadthBound
        } else {
            Expansion::Queued
        }
    }

    /// Turn every pending state into a `BreadthBound` leaf. Under
    /// `ExecutionOptions::discard_stopped` it polls once per state, and a stop that ends the run
    /// ends the drain, recorded in `stopped` (the leaves are then discarded, [`Self::selected_leaves`]).
    fn drain_at_breadth_bound(&mut self) {
        while let Some(state) = self.pending.pop_front() {
            if self.options.discard_stopped
                && let Some(cause) = run_ending_stop()
            {
                self.stopped = Some(cause);
                self.pending.clear();
                return;
            }
            self.leaves.push(execution_state_at_breadth_bound(
                state,
                &self.observation_log,
            ));
        }
    }

    /// E8's leaf selection ([`final_leaves`]). Under `ExecutionOptions::discard_stopped`, a run
    /// a stop ended selects no leaves and does no final merge, and the merge polls once per leaf:
    /// a stop that ends the run observed there discards the leaves and is recorded in `stopped`.
    fn selected_leaves(&mut self, leaves: Vec<ExecutionLeaf>) -> Vec<ExecutionLeaf> {
        let modality = self.options.result_modality;
        if !self.options.discard_stopped {
            return final_leaves(modality, self.fresh_counter.request(), leaves);
        }
        if self.stopped.is_some() {
            return Vec::new();
        }
        let selected = match modality {
            ResultModality::StateSet => {
                merge_final_leaves(self.fresh_counter.request(), leaves, run_ending_stop)
            }
            ResultModality::PathSet => Ok(leaves),
        };
        selected.unwrap_or_else(|cause| {
            self.stopped = Some(cause);
            Vec::new()
        })
    }

    /// E8: under `StateSet` leaves pass `merge_equal_final_leaves`, which merges a leaf into an
    /// earlier leaf of its configuration only when that leaf means everything it means; under
    /// `PathSet` every leaf is kept, one per explored path.
    /// `simplified_to_bottom` holds iff every initial input completed E2 and E3 and ended
    /// `Vacuous`.
    fn collect(mut self) -> (ExecutionResult, InitialSimplificationStatus) {
        let modality = self.options.result_modality;
        let leaves = std::mem::take(&mut self.leaves);
        let leaves = self.selected_leaves(leaves);
        // The legacy observer is a single-stream interface. It receives a transcript only when
        // final selection retained one leaf; callers consume multi-leaf transcripts from each leaf.
        let effects = match leaves.as_slice() {
            [leaf] => leaf.effects.clone(),
            _ => Vec::new(),
        };
        for effect in &effects {
            // An observer is the caller's code, not part of the run: whatever it evaluates is
            // outside the execution, in `Proof` mode.
            // Nor does it report to the run's coverage.
            crate::evaluation::with_evaluation(crate::evaluation::EvaluationMode::Proof, || {
                crate::coverage::suspend(|| (self.observe)(effect));
            });
        }
        (
            ExecutionResult {
                modality,
                leaves,
                effects,
                discarded: self.discarded,
                coverage: None,
                work: self.work.visited(),
                stack_stops: 0,
                stopped: self.stopped,
            },
            InitialSimplificationStatus {
                simplified_to_bottom: self.initial_input_count != 0
                    && self.completed_initial_simplifications == self.initial_input_count
                    && self.bottom_initial_simplifications == self.initial_input_count,
            },
        )
    }
}

/// A leaf that a stop cut off during or after the step: it is the state as it stood, and it
/// carries the work its state's expansion did before the stop (`lists`, in emission order),
/// which was on that path although the candidates it was building are not reported. Any other
/// leaf is returned as is, its diagnostics already attributed.
fn interrupted_with(mut leaf: ExecutionLeaf, lists: &[&[BackendDiagnostic]]) -> ExecutionLeaf {
    if let HaltReason::Stopped(_) = &leaf.halt_reason {
        for diagnostics in lists {
            extend_distinct(&mut leaf.diagnostics, diagnostics);
        }
    }
    leaf
}

/// Publish a stopped state's step: the step produced no answer, so its duration measures no
/// step and is not recorded. Returns whether the stop ends the whole execution: a cancelled
/// request or a failed solver prelude ends every remaining state, a passed step deadline or an
/// exhausted stack only the state being stepped.
fn stop_ends_execution(cause: &StopCause, step_timer: &mut StepTimer<'_>) -> bool {
    step_timer.discard_measurement();
    ends_execution(cause)
}

/// A poll for a stop that ends the run, after the exploration: a pending cancellation or a failed
/// solver prelude. A step's passed deadline or an exhausted stack ends only its step, so it is not
/// one here.
fn run_ending_stop() -> Option<StopCause> {
    match stop::check() {
        Ok(()) => None,
        Err(stop) => {
            let cause = stop.into_cause();
            ends_execution(&cause).then_some(cause)
        }
    }
}

/// Whether a stop ends the whole execution (a cancelled request, a failed solver prelude) rather
/// than the state being stepped only (a passed step deadline, an exhausted stack).
#[deny(clippy::wildcard_enum_match_arm)]
const fn ends_execution(cause: &StopCause) -> bool {
    match cause {
        StopCause::Cancelled | StopCause::SolverPrelude(_) => true,
        StopCause::Deadline(_) | StopCause::StackExhausted(_) => false,
    }
}

fn pattern_supports_execution_io(pattern: &Pattern) -> bool {
    pattern.constraints.is_empty() && pattern.term.attributes().variables.is_empty()
}

/// The leaves a result reports under `modality`. A path-set result is the per-path leaves as
/// exploration produced them; a state-set result is their disjunction, where merging equal
/// configurations loses no state.
fn final_leaves(
    modality: ResultModality,
    request: &RequestNames,
    leaves: Vec<ExecutionLeaf>,
) -> Vec<ExecutionLeaf> {
    match modality {
        ResultModality::StateSet => merge_equal_final_leaves(request, leaves),
        ResultModality::PathSet => leaves,
    }
}

/// The leaves of a state-set result with each configuration once: the result is a disjunction,
/// and a disjunct equal to an earlier one adds no state. Two leaves are one configuration when
/// their states are equal up to the names of the variables the request does not name (their
/// `RequestNames::state_key`s, which compare the constraints as a set, are equal): such a
/// variable is quantified over its own disjunct (docs/compatibility.md#result-variables), so
/// the two disjuncts denote the same configurations. Branch-local observable state must agree
/// too: committed effects and the console, which hold no variable. The console is compared as a
/// process observes it, by the input consumed and the bytes written in order
/// ([`ExecutionIoState::observable`]), not by the hooks or calls that wrote them: paths that
/// wrote the same bytes differently end in one state. Trivial and vacuous leaves are never
/// merged: a vacuous leaf carries no configuration, and a trivial leaf's configuration is the one
/// before an undefined step, which its halt describes, so whole-state trivial and vacuous outcomes
/// remain distinct.
///
/// Merging drops a leaf, which is sound only when an equal leaf that stays stands for it
/// ([`may_absorb`]); a leaf's halt can mean more than its configuration ([`merge_class`]). The leaf
/// of a stop or of the work budget that ended the run (`MergeClass::RunEnding`) also stands for the pending states the
/// run dropped, which no other leaf carries, so it is never merged, in either direction. A leaf
/// whose halt the decided configuration determines (stuck, branching, cut point) stands for any
/// later leaf of its configuration but a terminal-rule one. A leaf that marks its configuration's
/// subtree unexplored or undecided (a bound, a stop local to the state, an undecided step, a
/// failed simplification) stands only for another such leaf, and is kept beside a later leaf that
/// says what the subtree holds. A terminal-rule leaf's halt records the rule by which its path
/// arrived, and the same configuration reached by another rule may have successors: it says the
/// configuration is final, absorbs and is absorbed by only leaves that say so too (stuck or
/// terminal), and is kept beside any other equal leaf. A later leaf merges into the first retained
/// leaf of its configuration that may absorb it, and is otherwise retained itself, so a state-set
/// result may show one configuration more than once, each with a different meaning.
///
/// A retained leaf is the first of the leaves merged into it, the witness: it keeps its own
/// pattern, depth, halt reason, trace, branch, observations, effects, and console transcript, which
/// describe the one path it reports. Its diagnostics become those of every leaf merged into it, its
/// own first and then each new one in the order the merged leaves are met. A diagnostic records
/// that the work on its path may be incomplete (a term not known normalized, a condition or
/// predicate left undecided, a rule possibly left unapplied for lack of budget), and the merged
/// paths are paths of this result: dropping a merged leaf's diagnostics would make a state-set
/// result diagnostic-free where the path-set result of the same request is not, and a run without
/// diagnostics is what the explore-all coverage guarantee presumes (docs/backend-port.md). The
/// retained leaf's diagnostics may therefore name work that is not on its own trace. A merged
/// diagnostic is appended as the path that met it stated it, naming variables as that path named
/// them: two leaves whose states differ by a renaming of the variables the request does not name
/// merge, so a merged diagnostic may name a variable that does not occur in the retained leaf's
/// state, and diagnostics equal up to such names are each listed. Names minted after a fork are
/// distinct across paths (the fresh counter is request-wide), so a merged diagnostic never names
/// one of the retained leaf's own variables.
///
/// A key only tells a leaf apart from the other leaves that may be merged, so with fewer than
/// two such leaves no key is computed: a state key renames every variable the
/// request does not name, and an execution that keeps introducing variables ends with a leaf
/// holding all of them.
fn merge_equal_final_leaves(
    request: &RequestNames,
    leaves: Vec<ExecutionLeaf>,
) -> Vec<ExecutionLeaf> {
    match merge_final_leaves(request, leaves, || None) {
        Ok(merged) => merged,
        Err(cause) => unreachable!("a merge that does not poll reports no stop: {cause:?}"),
    }
}

/// [`merge_equal_final_leaves`], calling `poll` once per leaf it considers and ending with the
/// cause `poll` returns, if it returns one.
fn merge_final_leaves(
    request: &RequestNames,
    leaves: Vec<ExecutionLeaf>,
    mut poll: impl FnMut() -> Option<StopCause>,
) -> Result<Vec<ExecutionLeaf>, StopCause> {
    #[cfg(test)]
    tests::FINAL_MERGES.with(|merges| merges.set(merges.get() + 1));
    let mergeable = |leaf: &ExecutionLeaf| merge_class(&leaf.halt_reason).mergeable();
    if leaves
        .iter()
        .filter(|leaf| mergeable(leaf))
        .nth(1)
        .is_none()
    {
        return Ok(leaves);
    }
    // Each configuration's key with the indices of its retained leaves in `merged`.
    let mut seen: Vec<(_, Vec<usize>)> = Vec::new();
    let mut merged: Vec<ExecutionLeaf> = Vec::with_capacity(leaves.len());
    for leaf in leaves {
        if let Some(cause) = poll() {
            return Err(cause);
        }
        if !mergeable(&leaf) {
            merged.push(leaf);
            continue;
        }
        let key = (
            request.state_key(&leaf.pattern),
            leaf.effects.clone(),
            leaf.io.observable(),
        );
        match seen.iter_mut().find(|(seen_key, _)| *seen_key == key) {
            Some((_, retained)) => {
                let absorbing = retained
                    .iter()
                    .copied()
                    .find(|&index| may_absorb(&merged[index].halt_reason, &leaf.halt_reason));
                match absorbing {
                    Some(index) => {
                        extend_distinct(&mut merged[index].diagnostics, &leaf.diagnostics);
                    }
                    None => {
                        retained.push(merged.len());
                        merged.push(leaf);
                    }
                }
            }
            None => {
                seen.push((key, vec![merged.len()]));
                merged.push(leaf);
            }
        }
    }
    Ok(merged)
}

/// What a leaf's halt means beyond its configuration, which decides whether an equal leaf can
/// stand for it in a state-set result ([`merge_equal_final_leaves`]).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum MergeClass {
    /// `Trivial` and `Vacuous`: the leaf carries no final configuration (a trivial leaf's is the
    /// configuration before an undefined step), so it is never merged.
    NoConfiguration,
    /// A stop, or the work budget, that ended the whole run: the leaf also stands for the
    /// pending states the run dropped.
    RunEnding,
    /// A bound, a stop local to the state, an undecided step or a failed simplification: the
    /// configuration's subtree was not explored or not decided.
    Unexplored,
    /// The halt is determined by the configuration, which was decided: stuck, branching, or
    /// stopped at a cut point.
    ByConfiguration,
    /// The halt records the rule by which the path arrived (`TerminalRule`).
    ByArrival,
}

impl MergeClass {
    /// Whether a leaf of this class takes part in merging at all.
    const fn mergeable(self) -> bool {
        matches!(
            self,
            Self::Unexplored | Self::ByConfiguration | Self::ByArrival
        )
    }
}

#[deny(clippy::wildcard_enum_match_arm)]
fn merge_class(halt: &HaltReason) -> MergeClass {
    match halt {
        HaltReason::Trivial { .. } | HaltReason::Vacuous { .. } => MergeClass::NoConfiguration,
        HaltReason::Stopped(cause) => {
            if ends_execution(cause) {
                MergeClass::RunEnding
            } else {
                MergeClass::Unexplored
            }
        }
        // The budget ended the run: the leaf also stands for the pending states it dropped.
        HaltReason::WorkBound => MergeClass::RunEnding,
        HaltReason::DepthBound
        | HaltReason::BreadthBound
        | HaltReason::Indeterminate(_)
        | HaltReason::Simplification(_) => MergeClass::Unexplored,
        HaltReason::Stuck | HaltReason::Branch { .. } | HaltReason::CutPointRule { .. } => {
            MergeClass::ByConfiguration
        }
        HaltReason::TerminalRule { .. } => MergeClass::ByArrival,
    }
}

/// Whether the retained leaf, of halt `retained`, stands for a later leaf of the same
/// configuration and halt `later` in a state-set result. Only leaves that take part in merging
/// are asked.
///
/// - A leaf whose halt the decided configuration determines (stuck, branching, cut point) says
///   everything about the configuration's subtree: it stands for any later leaf of the
///   configuration but a terminal-rule one, including one that marks the subtree unexplored or
///   undecided. Two such leaves differ only where the configuration's step came out differently
///   on two paths (a solver that answered one query differently, as when it timed out), and the
///   first then stands for both.
/// - A leaf that marks its configuration's subtree unexplored or undecided (a bound, a stop local
///   to the state, an undecided step, a failed simplification) stands only for another such leaf:
///   it does not say what the subtree holds, so it does not stand for a later stuck, branching or
///   cut-point leaf, which does.
/// - A terminal-rule leaf's halt records the rule by which its path arrived, not a property of the
///   configuration, which reached otherwise may have successors: exploring from another leaf of
///   it does not recover that it is final. A terminal-rule leaf therefore absorbs, and is absorbed
///   by, only leaves that also say the configuration is final (stuck or terminal-rule).
fn may_absorb(retained: &HaltReason, later: &HaltReason) -> bool {
    let final_in_its_own_right =
        |halt: &HaltReason| matches!(halt, HaltReason::Stuck | HaltReason::TerminalRule { .. });
    match (merge_class(retained), merge_class(later)) {
        (MergeClass::ByArrival, _) | (_, MergeClass::ByArrival) => {
            final_in_its_own_right(retained) && final_in_its_own_right(later)
        }
        (MergeClass::ByConfiguration, _) | (MergeClass::Unexplored, MergeClass::Unexplored) => true,
        (MergeClass::Unexplored, _) | (MergeClass::NoConfiguration | MergeClass::RunEnding, _) => {
            false
        }
    }
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
    trace: &mut impl Extend<TraceEntry>,
) -> Stoppable<Result<PatternSimplification, SimplificationError>> {
    let simplified = match simplify_pattern_details_with_solver(
        definition,
        pattern,
        SimplificationOptions::keep_partial(max_iterations),
        solver,
    )? {
        Ok(simplified) => simplified,
        Err(error) => return Ok(Err(error)),
    };
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
    Ok(Ok(simplified))
}

/// `simplify_leaf_pattern` plus the observation and effect bookkeeping of an execution.
pub(crate) struct ResultPatternSimplification {
    pub(crate) pattern: Pattern,
    pub(crate) effects: Vec<BuiltinEffect>,
}

/// Why a successor is undefined: the definedness obligation that fails and, when an equation of
/// a `total` symbol produced the undefined term, that contradiction.
pub(crate) struct UndefinedSuccessor {
    pub(crate) obligation: Predicate,
    pub(crate) contradicted_total: Option<Box<ContradictedTotal>>,
}

impl UndefinedSuccessor {
    /// The `Trivial` halt of the step that built the successor, at the successor's `depth`; the
    /// leaf names the step's rule ([`Execution::undefined_step_leaf`]).
    fn halt(self, depth: u64) -> HaltReason {
        HaltReason::Trivial {
            depth,
            rule_id: None,
            label: None,
            obligation: self.obligation,
            contradicted_total: self.contradicted_total,
        }
    }
}

/// Whether `successor`, a candidate's successor as a step built it from a pattern with the
/// constraints `base`, is undefined, and why ([`normalize_successor`]); its diagnostics are
/// emitted.
pub(crate) fn successor_undefinedness(
    definition: &BackendDefinition,
    successor: &Pattern,
    base: &[Predicate],
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
    io: Option<&ExecutionIoState>,
) -> Stoppable<Option<UndefinedSuccessor>> {
    let checked = normalize_successor(definition, successor, base, options, solver, io)?;
    if let Some(normalization) = &checked.normalization {
        normalization.emit_diagnostics();
    }
    Ok(checked.undefined)
}

/// The normalization of a candidate's successor, done before the successor state exists.
pub(crate) struct SuccessorCheck {
    /// Why the successor is undefined, when its normalization shows it.
    pub(crate) undefined: Option<UndefinedSuccessor>,
    /// The results of the normalization's phases, which the successor state's own
    /// normalization takes instead of repeating them; `None` when a phase failed.
    pub(crate) normalization: Option<SuccessorNormalization>,
}

/// The results of the two phases of a successor's normalization ([`normalize_successor`]), with
/// the diagnostics each emitted, for the successor state built from the same pattern
/// (`Producer::normalization`).
pub(crate) struct SuccessorNormalization {
    /// The successor as the step built it, which the results are of.
    built: Pattern,
    /// The simplified constraints, before the retained substitution predicates are re-added.
    constraints: Vec<Predicate>,
    constraint_diagnostics: Vec<BackendDiagnostic>,
    /// The term phase; `None` when the constraints are `\bottom`, which ends the state before it.
    term: Option<TermNormalization>,
}

struct TermNormalization {
    simplified: Simplification,
    diagnostics: Vec<BackendDiagnostic>,
    /// The console state the evaluation committed, when the successor admitted one.
    io: Option<ExecutionIoState>,
}

impl SuccessorNormalization {
    /// The diagnostics of both phases, in emission order.
    pub(crate) fn diagnostics(&self) -> Vec<BackendDiagnostic> {
        let term = self.term.iter().flat_map(|term| &term.diagnostics);
        self.constraint_diagnostics
            .iter()
            .chain(term)
            .cloned()
            .collect()
    }

    fn emit_diagnostics(&self) {
        for diagnostic in self.diagnostics() {
            diagnostic::emit(diagnostic);
        }
    }
}

impl std::fmt::Debug for SuccessorNormalization {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str("SuccessorNormalization { .. }")
    }
}

/// The normalization of `successor`, a candidate's successor as a step built it from a pattern
/// with the constraints `base`, and whether it shows the successor undefined.
///
/// It runs, with no effect on the run, the phases a successor state goes through before its next
/// step, with the same simplifier and options, so they decide alike and their results are the
/// state's: the substitution is normalized and the constraints simplified
/// (`Execution::normalise_constraints`), where a `\bottom` that refutes a definedness condition
/// the step added makes the successor undefined; then the term is simplified under them
/// (`Execution::simplify_term`), with the console evaluation of `io` when the successor admits
/// one, where a subterm reduced to `\bottom` with the constraints `\bottom` makes it undefined.
/// A successor that is only empty, or whose simplification fails, is not shown undefined.
/// Diagnostics are not emitted; the normalization holds them.
pub(crate) fn normalize_successor(
    definition: &BackendDefinition,
    successor: &Pattern,
    base: &[Predicate],
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
    io: Option<&ExecutionIoState>,
) -> Stoppable<SuccessorCheck> {
    let failed = SuccessorCheck {
        undefined: None,
        normalization: None,
    };
    let mut pattern = successor.clone();
    let retained_substitution =
        normalize_pattern_substitution(&mut pattern, definition.sort_graph());
    let added = beyond(&pattern.constraints, base);
    let (simplified, constraint_diagnostics) = diagnostic::collect(|| {
        simplify_predicates_with_solver(definition, &pattern.constraints, &[], options, solver)
    });
    let Ok(simplified) = simplified? else {
        return Ok(failed);
    };
    let mut normalization = SuccessorNormalization {
        built: successor.clone(),
        constraints: simplified.clone(),
        constraint_diagnostics,
        term: None,
    };
    let mut constraints = simplified;
    retain_substitution_predicates(
        &mut constraints,
        &retained_substitution,
        definition.sort_graph(),
    );
    pattern.constraints = constraints;
    normalize_pattern_substitution(&mut pattern, definition.sort_graph());
    if predicates_truth(&pattern.constraints) == Truth::False {
        return Ok(SuccessorCheck {
            undefined: added
                .into_iter()
                .find(|predicate| matches!(predicate, Predicate::Ceil(_) | Predicate::Defined(_)))
                .map(|obligation| UndefinedSuccessor {
                    obligation,
                    contradicted_total: None,
                }),
            normalization: Some(normalization),
        });
    }
    let mut evaluation = io
        .filter(|_| pattern_supports_execution_io(&pattern))
        .map(ExecutionIoState::begin_evaluation);
    let (simplified, diagnostics) = diagnostic::collect(|| match evaluation.as_mut() {
        Some(evaluation) => simplify_in_execution_with_solver(
            definition,
            &pattern.term,
            &pattern.constraints,
            options,
            solver,
            evaluation,
        ),
        None => simplify_with_solver(
            definition,
            &pattern.term,
            &pattern.constraints,
            options,
            solver,
        ),
    });
    let Ok(simplified) = simplified? else {
        return Ok(failed);
    };
    let parts = simplified.clone().into_parts();
    normalization.term = Some(TermNormalization {
        simplified,
        diagnostics,
        io: evaluation.map(|evaluation| evaluation.commit()),
    });
    let mut constraints = pattern.constraints;
    constraints.extend(parts.conditions);
    Ok(SuccessorCheck {
        undefined: match parts.undefined_term {
            Some(term) if predicates_truth(&constraints) == Truth::False => {
                Some(UndefinedSuccessor {
                    obligation: Predicate::Ceil(term),
                    contradicted_total: parts.contradicted_total,
                })
            }
            _ => None,
        },
        normalization: Some(normalization),
    })
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn simplify_result_pattern(
    definition: &BackendDefinition,
    pattern: &Pattern,
    max_iterations: usize,
    solver: &dyn SmtSolver,
    depth: u64,
    trace: &mut impl Extend<TraceEntry>,
    observation: Option<&mut ObservationHead>,
    observation_log: &mut ObservationLog,
    observation_options: Option<&ObservationOptions>,
) -> Stoppable<Result<ResultPatternSimplification, SimplificationError>> {
    let before = pattern.clone();
    let PatternSimplification {
        pattern,
        applied_rules,
        effects: simplified_effects,
    } = match simplify_leaf_pattern(definition, pattern, max_iterations, solver, depth, trace)? {
        Ok(simplified) => simplified,
        Err(error) => return Ok(Err(error)),
    };
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
    Ok(Ok(ResultPatternSimplification {
        pattern,
        effects: simplified_effects,
    }))
}

/// Externalise a `Stuck`, `DepthBound`, or `Indeterminate` leaf in the simplifier's normal
/// form (`simplify_leaf_pattern`).
///
/// A constraint set that simplifies to `\bottom` makes the leaf `Trivial`, as it does for a
/// cut-point payload. When the simplification fails, an `Indeterminate` leaf keeps its pattern
/// and its reason, which already names why the state could not progress; any other leaf
/// reports the failure, as the cut-point and terminal payloads do. The halt reason is decided
/// before externalisation, which only normalises the pattern, so a stop during it leaves the
/// leaf as it stands with its unsimplified pattern.
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
        Ok(Ok(simplified)) if predicates_truth(&simplified.pattern.constraints) == Truth::False => {
            state.effects.commit(simplified.effects);
            let halt_reason = trivial_halt(state.depth, &simplified.pattern);
            state.leaf_with_pattern(simplified.pattern, halt_reason, observation_log)
        }
        Ok(Ok(simplified)) => {
            state.effects.commit(simplified.effects);
            state.leaf_with_pattern(simplified.pattern, halt_reason, observation_log)
        }
        Ok(Err(_)) if matches!(halt_reason, HaltReason::Indeterminate(_)) => {
            state.leaf_with_pattern(pattern, halt_reason, observation_log)
        }
        Ok(Err(error)) => {
            state.leaf_with_pattern(pattern, HaltReason::Simplification(error), observation_log)
        }
        Err(stop) => {
            // Kept outcome: the decided reason, with the unsimplified pattern. The normalisation
            // only refines it (at most the constraints simplify to `\bottom` and the leaf becomes
            // `Trivial`), and none of these reasons claims the instance set is non-empty
            // (`HaltReason::Stuck` holds of an empty set too). A stop of the request or of the
            // solver's prelude stays raised, and the next state's first poll publishes it; a
            // passed step deadline or an exhausted stack ends this step, whose reason is decided.
            stop.forgo_refinement();
            state.leaf_with_pattern(pattern, halt_reason, observation_log)
        }
    }
}

/// Commit a proposed successor's effects to the state that reports it as a cut point, with the
/// trace of its higher-priority remainder's simplifications, as a cut-point leaf always has.
fn commit_proposed_effects(state: &mut ExecutionState, applied: &AppliedRule) {
    for simplification in &applied.remainder_simplifications {
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
}

/// Extend `head` with an applied candidate's observations: the evaluations of the higher-priority
/// remainder it was applied to, then its transition.
fn applied_observation(
    definition: &BackendDefinition,
    mut head: ObservationHead,
    applied: &AppliedRule,
    observation_log: &mut ObservationLog,
    observation_options: Option<&ObservationOptions>,
) -> ObservationHead {
    for simplification in &applied.remainder_simplifications {
        head = observation_log.append_simplification(
            head,
            definition,
            simplification.before.clone(),
            &simplification.after,
            &simplification.applied_rules,
            &simplification.effects,
            observation_options,
        );
    }
    observation_log.append_applied(head, applied, observation_options)
}

/// Extend `head` with a remainder candidate's observations: its transition from `before`, then
/// the evaluations of the simplifications it went through in the step.
fn remainder_observation(
    definition: &BackendDefinition,
    head: ObservationHead,
    before: Pattern,
    remainder: &RemainderBranch,
    observation_log: &mut ObservationLog,
    observation_options: Option<&ObservationOptions>,
) -> ObservationHead {
    let transition_pattern = remainder
        .simplifications
        .first()
        .map_or_else(|| remainder.pattern.clone(), |record| record.before.clone());
    let transition_remainder = RemainderBranch {
        pattern: transition_pattern,
        ..remainder.clone()
    };
    let mut head =
        observation_log.append_remainder(head, before, &transition_remainder, observation_options);
    for simplification in &remainder.simplifications {
        head = observation_log.append_simplification(
            head,
            definition,
            simplification.before.clone(),
            &simplification.after,
            &simplification.applied_rules,
            &simplification.effects,
            observation_options,
        );
    }
    head
}

fn next_state(
    definition: &BackendDefinition,
    state: ExecutionState,
    applied: AppliedRule,
    observation_log: &mut ObservationLog,
    observation_options: Option<&ObservationOptions>,
) -> ExecutionState {
    let observation = applied_observation(
        definition,
        state.observation,
        &applied,
        observation_log,
        observation_options,
    );
    commit_applied(state, applied, observation)
}

/// The successor of `state` by `applied`, whose observations `observation` already records.
fn commit_applied(
    mut state: ExecutionState,
    applied: AppliedRule,
    observation: ObservationHead,
) -> ExecutionState {
    if !state.retain_trace {
        state.trace.clear();
    }
    state.diagnostics.extend(&applied.diagnostics);
    for simplification in &applied.remainder_simplifications {
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
    state.observation = observation;
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
    state.defined_where = Vec::new();
    state
}

fn remaining_state(
    definition: &BackendDefinition,
    state: ExecutionState,
    before: Pattern,
    remainder: RemainderBranch,
    observation_log: &mut ObservationLog,
    observation_options: Option<&ObservationOptions>,
) -> ExecutionState {
    let observation = remainder_observation(
        definition,
        state.observation,
        before,
        &remainder,
        observation_log,
        observation_options,
    );
    commit_remainder(state, remainder, observation)
}

/// The remainder successor of `state`, whose observations `observation` already records.
fn commit_remainder(
    mut state: ExecutionState,
    remainder: RemainderBranch,
    observation: ObservationHead,
) -> ExecutionState {
    state.diagnostics.extend(&remainder.diagnostics);
    state.observation = observation;
    state.trace.push(TraceEntry {
        depth: state.depth,
        kind: TraceKind::Remainder,
        label: None,
        unique_id: remainder.rule_ids.join(","),
    });
    for simplification in &remainder.simplifications {
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
    state.defined_where = Vec::new();
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
    /// The path's trace, shared with the paths it forked from; with `retain_trace` false only
    /// the entries since the latest rewrite step, which the halts naming that step read.
    trace: PathTrace,
    retain_trace: bool,
    kind: ExecutionStateKind,
    observation: ObservationHead,
    effects: EffectJournal,
    io: ExecutionIoState,
    /// Whether the console capability remains available on this concrete execution prefix.
    io_enabled: bool,
    is_initial_input: bool,
    /// The decided definedness of an initial configuration the run does not assume defined
    /// (`Execution::restrict_to_defined_instances`), which restricts what its step leaves over;
    /// empty on every other state.
    defined_where: Vec<Predicate>,
    /// The backend diagnostics of the work this path went through so far, shared with the
    /// paths it forked from.
    diagnostics: PathDiagnostics,
    /// The step that produced this state, until the state's first normalization, which may find
    /// that step undefined ([`Producer`]); `None` on every other state.
    producer: Option<std::rc::Rc<Producer>>,
}

/// The step that produced a successor, kept on it until its first normalization.
///
/// A step whose result a `total` (or `functional`) function's equation reduces to `\bottom`
/// carries no definedness obligation, since the attribute is trusted, so the step applies and
/// only the successor's normalization finds its result undefined. The step is then undefined on
/// the configuration it was taken from, and its `Trivial` leaf is that configuration, at its depth,
/// restricted to the instances no other applied candidate of the step takes to a defined
/// successor, as for an undefined result the step itself finds.
struct Producer {
    /// The state the step was taken from, before the step.
    parent: ExecutionState,
    /// The pattern the rule was applied to.
    before: Pattern,
    /// The successor as the step built it, before normalization: its constraints are the
    /// condition under which this candidate applies.
    successor: Pattern,
    rule_id: String,
    label: Option<String>,
    effects: Vec<BuiltinEffect>,
    /// The simplifications of a higher-priority remainder that led to `before`, which the leaf's
    /// path goes through, as an undefined step the step itself finds does.
    remainder_simplifications: Vec<RemainderSimplification>,
    /// The successors of the step's other applied candidates, as the step built them, whose
    /// definedness is decided only if this successor turns out undefined.
    siblings: Vec<Pattern>,
    /// The successors of the step's other applied candidates already normalized and not
    /// undefined, as the step built them.
    defined_siblings: Vec<Pattern>,
    /// The normalization of `successor` the step already did, which the successor's own
    /// normalization takes instead of repeating it.
    normalization: Option<std::sync::Arc<SuccessorNormalization>>,
}

impl Producer {
    fn of(parent: &ExecutionState, applied: &AppliedRule, siblings: Vec<Pattern>) -> Self {
        Self {
            parent: ExecutionState {
                producer: None,
                ..parent.clone()
            },
            before: applied.before.clone(),
            successor: applied.pattern.clone(),
            rule_id: applied.unique_id.clone(),
            label: applied.label.clone(),
            effects: applied.effects.clone(),
            remainder_simplifications: applied.remainder_simplifications.clone(),
            siblings,
            defined_siblings: Vec::new(),
            // A step's normalization stands for the successor only when it is of the pattern
            // the step committed; any other is dropped and the successor normalizes itself.
            normalization: applied
                .normalized
                .0
                .clone()
                .filter(|normalization| normalization.built == applied.pattern),
        }
    }
}

impl ExecutionState {
    fn leaf(self, halt_reason: HaltReason, observation_log: &ObservationLog) -> ExecutionLeaf {
        let (branch, observations) = observation_log.materialize(self.observation);
        ExecutionLeaf {
            pattern: self.pattern,
            depth: self.depth,
            trace: if self.retain_trace {
                self.trace.into_vec()
            } else {
                Vec::new()
            },
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

/// The free variables of `pattern`'s term and constraints.
fn pattern_variables(pattern: &Pattern) -> BTreeSet<crate::term::Variable> {
    let mut variables = pattern.term.attributes().variables.to_btree_set();
    for predicate in &pattern.constraints {
        variables.extend(predicate.free_variables());
    }
    variables
}

/// The members of `constraints` not among `base`.
fn beyond(constraints: &[Predicate], base: &[Predicate]) -> Vec<Predicate> {
    constraints
        .iter()
        .filter(|predicate| !base.contains(predicate))
        .cloned()
        .collect()
}

/// `predicates` with the variables they mention outside `bound` (a rule's fresh variables)
/// existentially closed: the conjunction under one `\exists` per such variable.
fn closed_over(
    predicates: Vec<Predicate>,
    bound: &BTreeSet<crate::term::Variable>,
) -> Vec<Predicate> {
    let fresh = predicates
        .iter()
        .flat_map(Predicate::free_variables)
        .filter(|variable| !bound.contains(variable))
        .collect::<BTreeSet<_>>();
    if fresh.is_empty() {
        return predicates;
    }
    vec![
        fresh
            .into_iter()
            .fold(conjunction(predicates), |body, variable| {
                Predicate::Exists(variable, Box::new(body))
            }),
    ]
}

fn conjunction(mut predicates: Vec<Predicate>) -> Predicate {
    match predicates.len() {
        0 => Predicate::True,
        1 => predicates.pop().expect("one predicate"),
        _ => Predicate::And(predicates),
    }
}

fn extend_unique_predicates(target: &mut Vec<Predicate>, predicates: Vec<Predicate>) {
    for predicate in predicates {
        if !target.contains(&predicate) {
            target.push(predicate);
        }
    }
}

#[cfg(test)]
mod tests {
    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    use super::*;

    thread_local! {
        /// Calls of `merge_final_leaves` on this thread.
        pub(super) static FINAL_MERGES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
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

    /// `probe(X)` rewrites to `done` where `X ==Int 0`, a condition only the solver decides, and
    /// `stuck(X)`, under the constraint `X >Int 0`, has no rule; `wrap(X)` rewrites to itself
    /// forever, asking the solver nothing.
    fn prelude_definition() -> BackendDefinition {
        let source = r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                sort SortS{} []
                symbol probe{}(SortInt{}) : SortS{} [constructor{}()]
                symbol stuck{}(SortInt{}) : SortS{} [constructor{}()]
                symbol wrap{}(SortInt{}) : SortS{} [constructor{}()]
                symbol done{}() : SortS{} [constructor{}()]
                hooked-symbol eqInt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.eq"), smt-hook{}("=")]
                hooked-symbol gtInt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.gt"), smt-hook{}(">")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(
                        probe{}(X:SortInt{}),
                        \equals{SortBool{}, SortS{}}(
                            eqInt{}(X:SortInt{}, \dv{SortInt{}}("0")),
                            \dv{SortBool{}}("true")
                        )
                    ),
                    done{}()
                ) [label{}("probe")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(wrap{}(X:SortInt{}), \top{SortS{}}()),
                    wrap{}(X:SortInt{})
                ) [label{}("wrap")]
            endmodule []"#;
        let syntax = parse_definition(source).expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    /// A solver whose prelude turns out inconsistent at its first query, as `Z3Solver` finds it:
    /// that query and every later one raise its prelude signal and return the prelude's stop.
    #[derive(Default)]
    struct InconsistentPrelude {
        signal: crate::stop::PreludeSignal,
        queries: std::sync::atomic::AtomicUsize,
    }

    impl InconsistentPrelude {
        fn fail<T>(&self) -> Stoppable<T> {
            self.queries
                .fetch_add(1, std::sync::atomic::Ordering::SeqCst);
            self.signal.raise(crate::stop::PreludeFailure::Inconsistent);
            Err(Stop::solver_prelude(
                crate::stop::PreludeFailure::Inconsistent,
            ))
        }
    }

    impl SmtSolver for InconsistentPrelude {
        fn is_sat(
            &self,
            _predicates: &[Predicate],
            _substitution: &crate::substitution::Substitution,
        ) -> Stoppable<Result<crate::smt::Satisfiability, crate::smt::SmtError>> {
            self.fail()
        }

        fn check_predicates(
            &self,
            _known: &[Predicate],
            _substitution: &crate::substitution::Substitution,
            _checked: &[Predicate],
        ) -> Stoppable<Result<crate::smt::Validity, crate::smt::SmtError>> {
            self.fail()
        }

        fn prelude_signal(&self) -> Option<&crate::stop::PreludeSignal> {
            Some(&self.signal)
        }
    }

    /// An inconsistent prelude found by the first solver query of an execution ends it with one
    /// `Stopped(SolverPrelude(Inconsistent))` leaf, although its other states would go on
    /// without asking the solver (`wrap` loops; the depth bound only guards against a hang). The
    /// cause reaches the leaf as the step's or the poll's stop, never as a cancellation read from
    /// a flag, and the operation boundary reports it too.
    #[test]
    fn an_inconsistent_prelude_found_by_the_first_query_ends_the_execution() {
        let definition = prelude_definition();
        let term = |source: &str| {
            definition
                .internalize_term(&parse_pattern(source).expect("term should parse"), &[])
                .expect("term should internalize")
        };
        let gt_zero = Predicate::Equals(
            term(r#"gtInt{}(X:SortInt{}, \dv{SortInt{}}("0"))"#),
            term(r#"\dv{SortBool{}}("true")"#),
        );
        let wrap = Pattern {
            term: term(r#"wrap{}(\dv{SortInt{}}("0"))"#),
            constraints: Vec::new(),
        };
        let prelude = || {
            HaltReason::Stopped(StopCause::SolverPrelude(
                crate::stop::PreludeFailure::Inconsistent,
            ))
        };
        // The first query is posed by `probe`'s step, which the stop ends: `probe` is the stopped
        // leaf. Or it is posed by the normalisation of `stuck`'s decided leaf, which dismisses the
        // stop and keeps `Stuck`: `wrap`'s first poll then observes the raised prelude signal,
        // and `wrap` is the stopped leaf.
        let cases = [
            (
                Pattern {
                    term: term("probe{}(X:SortInt{})"),
                    constraints: Vec::new(),
                },
                vec![("probe", prelude())],
            ),
            (
                Pattern {
                    term: term("stuck{}(X:SortInt{})"),
                    constraints: vec![gt_zero],
                },
                vec![("stuck", HaltReason::Stuck), ("wrap", prelude())],
            ),
        ];
        let head = |leaf: &ExecutionLeaf| match leaf.pattern.term.kind() {
            crate::term::TermKind::Application { symbol, .. } => symbol.name.to_string(),
            other => panic!("expected an application, found {other:?}"),
        };
        for (first, expected) in cases {
            let solver = InconsistentPrelude::default();
            let mut result = None;
            let operation = crate::stop::operation(&solver, || {
                result = Some(super::super::execute_disjunction_with_solver_and_observer(
                    &definition,
                    vec![first.clone(), wrap.clone()],
                    ExecutionOptions {
                        max_depth: 64,
                        ..ExecutionOptions::default()
                    },
                    &solver,
                    |_| {},
                ));
            });
            assert_eq!(
                operation.map_err(Stop::into_cause),
                Err(StopCause::SolverPrelude(
                    crate::stop::PreludeFailure::Inconsistent
                ))
            );
            let result = result.expect("the operation ran the execution");
            assert_eq!(
                solver.queries.load(std::sync::atomic::Ordering::SeqCst),
                1,
                "{result:#?}"
            );
            let leaves = result
                .leaves
                .iter()
                .map(|leaf| (head(leaf), leaf.halt_reason.clone()))
                .collect::<Vec<_>>();
            let expected = expected
                .into_iter()
                .map(|(head, reason)| (head.to_string(), reason))
                .collect::<Vec<_>>();
            assert_eq!(leaves, expected, "{result:#?}");
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

        let leaves = merge_equal_final_leaves(
            &RequestNames::default(),
            vec![
                leaf("depth-before", HaltReason::DepthBound),
                leaf("stuck", HaltReason::Stuck),
                leaf("depth-after", HaltReason::DepthBound),
            ],
        );

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

    // Three leaves of one configuration merge into the first, a stuck leaf that stands for the
    // later stuck and depth-bound ones: it keeps its own depth and halt reason and collects every
    // merged leaf's diagnostics, its own first, then each new one in the order the merged leaves
    // are met; a leaf of another configuration between them keeps only its own.
    #[test]
    fn a_merged_final_leaf_collects_the_diagnostics_of_every_merged_leaf() {
        let definition = definition("");
        let exhausted = |limit| BackendDiagnostic::SimplificationBudgetExhausted {
            limit,
            subject: crate::simplify::BudgetSubject::Term,
        };
        let leaf = |name, depth, halt_reason, diagnostics| ExecutionLeaf {
            pattern: subject(&definition, name),
            depth,
            trace: Vec::new(),
            branch: Vec::new(),
            observations: Vec::new(),
            effects: Vec::new(),
            io: ExecutionIoState::default(),
            halt_reason,
            diagnostics,
        };

        let leaves = merge_equal_final_leaves(
            &RequestNames::default(),
            vec![
                leaf("same", 1, HaltReason::Stuck, vec![exhausted(1)]),
                leaf("other", 2, HaltReason::Stuck, vec![exhausted(4)]),
                leaf(
                    "same",
                    2,
                    HaltReason::Stuck,
                    vec![exhausted(2), exhausted(1)],
                ),
                leaf("same", 3, HaltReason::DepthBound, vec![exhausted(3)]),
            ],
        );

        let [same, other] = leaves.as_slice() else {
            panic!("expected one leaf per configuration: {leaves:?}");
        };
        assert_eq!(same.pattern, subject(&definition, "same"));
        assert_eq!((same.depth, &same.halt_reason), (1, &HaltReason::Stuck));
        assert_eq!(same.diagnostics, [exhausted(1), exhausted(2), exhausted(3)]);
        assert_eq!(other.pattern, subject(&definition, "other"));
        assert_eq!(other.diagnostics, [exhausted(4)]);
    }

    // A key is computed only to compare a leaf with another one carrying a configuration: a
    // leaf beside trivial or vacuous ones (which carry none) gets none, two such leaves get one
    // each. Seeded: computing the key of every leaf makes the first count 1.
    #[test]
    fn a_final_leaf_alone_among_configurations_gets_no_state_key() {
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
        let vacuous = HaltReason::Vacuous {
            depth: 1,
            rule_id: None,
            label: None,
            constraint: Predicate::False,
            contradicted_total: None,
        };
        let keys = |leaves| {
            let before = crate::fresh::STATE_KEYS.with(std::cell::Cell::get);
            let kept = merge_equal_final_leaves(&RequestNames::default(), leaves).len();
            (
                kept,
                crate::fresh::STATE_KEYS.with(std::cell::Cell::get) - before,
            )
        };

        assert_eq!(
            keys(vec![
                leaf("stuck", HaltReason::Stuck),
                leaf("vacuous", vacuous.clone())
            ]),
            (2, 0)
        );
        assert_eq!(keys(vec![leaf("stuck", HaltReason::Stuck)]), (1, 0));
        assert_eq!(
            keys(vec![
                leaf("same", HaltReason::Stuck),
                leaf("same", HaltReason::DepthBound)
            ]),
            (1, 2)
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

        let cursor_leaves = merge_equal_final_leaves(
            &RequestNames::default(),
            vec![leaf(cursor_zero), leaf(cursor_one)],
        );
        assert_eq!(cursor_leaves.len(), 2);

        let transcript_leaves = merge_equal_final_leaves(
            &RequestNames::default(),
            vec![leaf(left_io), leaf(right_io)],
        );

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

    // A path's trace is shared, not copied, by a fork: the forked state holds the same entries,
    // stored once, an entry appended on one path is not an entry of the other, and each path's
    // leaf returns its entries in order, as a trace kept in a vector of its own would. This pins
    // the representation's contract (`PathTrace`); it is not a regression test that fails at a
    // base where forks copied a vector.
    #[test]
    fn a_fork_shares_its_parents_trace_and_extends_it_apart() {
        let definition = definition("");
        let entry = |depth, kind, unique_id: &str| TraceEntry {
            depth,
            kind,
            label: None,
            unique_id: unique_id.to_owned(),
        };
        let prefix = (1..=500)
            .flat_map(|depth| {
                [
                    entry(depth, TraceKind::Rewrite, &format!("step-{depth}")),
                    entry(
                        depth,
                        TraceKind::Simplification,
                        &format!("simplified-{depth}"),
                    ),
                ]
            })
            .collect::<Vec<_>>();
        let mut parent = state_with_trace(&definition, &prefix, true);

        let mut child = parent.clone();
        assert!(child.trace.shares_entries_with(&parent.trace));

        let rewrite = entry(501, TraceKind::Rewrite, "child-step");
        let remainder = entry(500, TraceKind::Remainder, "parent-remainder");
        child.trace.push(rewrite.clone());
        parent.trace.push(remainder.clone());
        assert!(!child.trace.shares_entries_with(&parent.trace));
        assert_eq!(child.trace.last_rewrite(), Some(&rewrite));
        // A remainder entry is no rewrite: the parent's latest rewrite is still its own.
        assert_eq!(parent.trace.last_rewrite(), prefix.iter().rev().nth(1));

        // A leaf moves out the entries its path holds alone and clones those a pending path
        // shares: a moved entry keeps its text's buffer, a cloned one gets a new buffer.
        let buffers = |trace: &[TraceEntry]| {
            trace
                .iter()
                .map(|entry| entry.unique_id.as_ptr())
                .collect::<Vec<_>>()
        };
        let child_buffers = child.trace.unique_id_buffers();
        let parent_buffers = parent.trace.unique_id_buffers();
        let log = ObservationLog::default();
        let child_leaf = child.leaf(HaltReason::Stuck, &log);
        assert_eq!(child_leaf.trace, [prefix.as_slice(), &[rewrite]].concat());
        let child_leaf_buffers = buffers(&child_leaf.trace);
        // The parent is still pending: the shared prefix was cloned, the child's own entry moved.
        assert!(
            child_leaf_buffers[..prefix.len()]
                .iter()
                .zip(&child_buffers)
                .all(|(leaf, path)| leaf != path)
        );
        assert_eq!(child_leaf_buffers.last(), child_buffers.last());
        // The child has ended, so the parent holds its whole trace alone and moves all of it.
        let parent_leaf = parent.leaf(HaltReason::Stuck, &log);
        assert_eq!(
            parent_leaf.trace,
            [prefix.as_slice(), &[remainder]].concat()
        );
        assert_eq!(buffers(&parent_leaf.trace), parent_buffers);

        // Clearing one path, as a step does when the trace is not retained, leaves the other.
        let mut kept = state_with_trace(&definition, &prefix, false);
        let other = kept.clone();
        kept.trace.clear();
        assert_eq!(kept.trace.last_rewrite(), None);
        assert_eq!(other.trace.to_vec(), prefix);
        assert_eq!(kept.leaf(HaltReason::Stuck, &log).trace, []);
    }

    fn state_with_trace(
        definition: &BackendDefinition,
        prefix: &[TraceEntry],
        retain_trace: bool,
    ) -> ExecutionState {
        let mut trace = PathTrace::default();
        trace.extend(prefix.iter().cloned());
        ExecutionState {
            pattern: subject(definition, "state"),
            depth: 500,
            trace,
            retain_trace,
            kind: ExecutionStateKind::Rewritable,
            observation: None,
            effects: EffectJournal::default(),
            io: ExecutionIoState::default(),
            io_enabled: false,
            is_initial_input: false,
            defined_where: Vec::new(),
            diagnostics: PathDiagnostics::new_request(),
            producer: None,
        }
    }

    /// A solver that cancels the request at its first query and then answers it, so the stop is
    /// observed by the next poll.
    struct CancelOnFirstQuery {
        token: crate::stop::CancellationToken,
    }

    impl SmtSolver for CancelOnFirstQuery {
        fn is_sat(
            &self,
            _predicates: &[Predicate],
            _substitution: &crate::substitution::Substitution,
        ) -> Stoppable<Result<crate::smt::Satisfiability, crate::smt::SmtError>> {
            self.token.cancel();
            Ok(Ok(crate::smt::Satisfiability::Sat))
        }

        fn check_predicates(
            &self,
            _known: &[Predicate],
            _substitution: &crate::substitution::Substitution,
            _checked: &[Predicate],
        ) -> Stoppable<Result<crate::smt::Validity, crate::smt::SmtError>> {
            self.token.cancel();
            Ok(Ok(crate::smt::Validity::Contingent))
        }
    }

    /// A stop that ends the run (a cancellation, or an inconsistent solver prelude) is reported
    /// by the leaf of the state it stopped, and that leaf also stands for the pending states the
    /// run dropped (`wrap(0)`, which never ends): under `StateSet` it is kept beside an earlier
    /// leaf of the same configuration (`done`), as under `PathSet`, so the result never reads as
    /// a complete exploration. The first solver query is posed by `stuck`'s normalisation, which
    /// keeps `Stuck`; the second `done` observes the stop at its first poll.
    #[test]
    fn a_state_set_merge_keeps_the_leaf_of_a_stop_that_ended_the_run() {
        let definition = prelude_definition();
        let term = |source: &str| {
            definition
                .internalize_term(&parse_pattern(source).expect("term should parse"), &[])
                .expect("term should internalize")
        };
        let gt_zero = Predicate::Equals(
            term(r#"gtInt{}(X:SortInt{}, \dv{SortInt{}}("0"))"#),
            term(r#"\dv{SortBool{}}("true")"#),
        );
        let pattern = |source: &str, constraints: Vec<Predicate>| Pattern {
            term: term(source),
            constraints,
        };
        let initial = vec![
            pattern("done{}()", Vec::new()),
            pattern("stuck{}(X:SortInt{})", vec![gt_zero]),
            pattern("done{}()", Vec::new()),
            pattern(r#"wrap{}(\dv{SortInt{}}("0"))"#, Vec::new()),
        ];
        let options = |result_modality| ExecutionOptions {
            max_depth: 64,
            result_modality,
            ..ExecutionOptions::default()
        };
        let head = |leaf: &ExecutionLeaf| match leaf.pattern.term.kind() {
            crate::term::TermKind::Application { symbol, .. } => symbol.name.to_string(),
            other => panic!("expected an application, found {other:?}"),
        };
        let leaves = |result: &ExecutionResult| {
            result
                .leaves
                .iter()
                .map(|leaf| (head(leaf), leaf.halt_reason.clone()))
                .collect::<Vec<_>>()
        };
        let stops = [
            StopCause::Cancelled,
            StopCause::SolverPrelude(crate::stop::PreludeFailure::Inconsistent),
        ];
        for stop in stops {
            let expected = vec![
                ("done".to_owned(), HaltReason::Stuck),
                ("stuck".to_owned(), HaltReason::Stuck),
                ("done".to_owned(), HaltReason::Stopped(stop.clone())),
            ];
            for modality in [ResultModality::PathSet, ResultModality::StateSet] {
                let result = match &stop {
                    StopCause::Cancelled => {
                        let token = crate::stop::CancellationToken::new();
                        let solver = CancelOnFirstQuery {
                            token: token.clone(),
                        };
                        token.scope(|| {
                            super::super::execute_disjunction_with_solver_and_observer(
                                &definition,
                                initial.clone(),
                                options(modality),
                                &solver,
                                |_| {},
                            )
                        })
                    }
                    _ => {
                        let solver = InconsistentPrelude::default();
                        let mut result = None;
                        let operation = crate::stop::operation(&solver, || {
                            result =
                                Some(super::super::execute_disjunction_with_solver_and_observer(
                                    &definition,
                                    initial.clone(),
                                    options(modality),
                                    &solver,
                                    |_| {},
                                ));
                        });
                        assert_eq!(operation.map_err(Stop::into_cause), Err(stop.clone()));
                        result.expect("the operation ran the execution")
                    }
                };
                assert_eq!(leaves(&result), expected, "{stop:?} {modality:?}");
            }
        }
    }

    // A bound or stop leaf is absorbed only by an earlier leaf whose halt its configuration
    // determines: a terminal-rule leaf records the rule its path arrived by, so it keeps a later
    // deadline leaf of its configuration beside it and absorbs only a leaf final in its own right.
    // A leaf of a stop that ended the run is never merged.
    #[test]
    fn a_state_set_merge_keeps_bound_and_run_ending_leaves_a_terminal_or_earlier_leaf_cannot_stand_for()
     {
        let definition = definition("");
        let leaf = |depth, halt_reason| ExecutionLeaf {
            pattern: subject(&definition, "same"),
            depth,
            trace: Vec::new(),
            branch: Vec::new(),
            observations: Vec::new(),
            effects: Vec::new(),
            io: ExecutionIoState::default(),
            halt_reason,
            diagnostics: Vec::new(),
        };
        let terminal = HaltReason::TerminalRule {
            rule: "to-same".to_owned(),
        };
        let deadline = HaltReason::Stopped(StopCause::Deadline(
            crate::timeout::StepTimeoutMode::Manual(std::time::Duration::from_millis(1)),
        ));
        let halts = |leaves: Vec<ExecutionLeaf>| {
            merge_equal_final_leaves(&RequestNames::default(), leaves)
                .into_iter()
                .map(|leaf| (leaf.depth, leaf.halt_reason))
                .collect::<Vec<_>>()
        };

        assert_eq!(
            halts(vec![
                leaf(1, terminal.clone()),
                leaf(2, deadline.clone()),
                leaf(3, HaltReason::Stuck),
            ]),
            [(1, terminal.clone()), (2, deadline.clone())]
        );
        assert_eq!(
            halts(vec![
                leaf(1, HaltReason::Stuck),
                leaf(2, HaltReason::Stopped(StopCause::Cancelled)),
                leaf(3, HaltReason::Stuck),
            ]),
            [
                (1, HaltReason::Stuck),
                (2, HaltReason::Stopped(StopCause::Cancelled))
            ]
        );
        // An earlier leaf whose halt its configuration determines absorbs a later bound or stop
        // leaf of that configuration, as before.
        let breadth = HaltReason::BreadthBound;
        let stack = HaltReason::Stopped(StopCause::StackExhausted(
            crate::stop::StackLimit::ThreadBudget(1),
        ));
        for unexplored in [deadline.clone(), breadth.clone(), stack.clone()] {
            assert_eq!(
                halts(vec![
                    leaf(1, HaltReason::Stuck),
                    leaf(2, unexplored.clone())
                ]),
                [(1, HaltReason::Stuck)],
                "{unexplored:?}"
            );
        }
        // A terminal leaf says its configuration is final, which a stuck leaf says too and a
        // bound, stop or branching leaf does not: it is absorbed only by a stuck or terminal
        // leaf, in either order.
        for earlier in [
            HaltReason::DepthBound,
            breadth,
            stack,
            deadline,
            HaltReason::Indeterminate(IndeterminateReason::SurvivingMacroOrAlias {
                symbol: "m".into(),
            }),
        ] {
            assert_eq!(
                halts(vec![leaf(1, earlier.clone()), leaf(2, terminal.clone())]),
                [(1, earlier.clone()), (2, terminal.clone())],
                "{earlier:?}"
            );
        }
        assert_eq!(
            halts(vec![leaf(1, HaltReason::Stuck), leaf(2, terminal.clone())]),
            [(1, HaltReason::Stuck)]
        );
        assert_eq!(
            halts(vec![leaf(1, terminal.clone()), leaf(2, HaltReason::Stuck)]),
            [(1, terminal.clone())]
        );
        assert_eq!(
            halts(vec![leaf(1, terminal.clone()), leaf(2, terminal.clone())]),
            [(1, terminal)]
        );
        // An undecided, failed, bound or stopped leaf does not say what its configuration's
        // subtree holds, so it does not stand for a later stuck leaf of it, which does; a stuck
        // leaf first stands for it; and two leaves that both leave the subtree open merge.
        let undecided = HaltReason::Indeterminate(IndeterminateReason::SurvivingMacroOrAlias {
            symbol: "m".into(),
        });
        let failed = HaltReason::Simplification(SimplificationError::IterationLimit {
            limit: 1,
            term: subject(&definition, "same").term,
        });
        let deadline = HaltReason::Stopped(StopCause::Deadline(
            crate::timeout::StepTimeoutMode::Manual(std::time::Duration::from_millis(1)),
        ));
        for open in [
            undecided.clone(),
            failed.clone(),
            HaltReason::DepthBound,
            deadline.clone(),
        ] {
            assert_eq!(
                halts(vec![leaf(1, open.clone()), leaf(2, HaltReason::Stuck)]),
                [(1, open.clone()), (2, HaltReason::Stuck)],
                "{open:?}"
            );
            assert_eq!(
                halts(vec![leaf(1, HaltReason::Stuck), leaf(2, open.clone())]),
                [(1, HaltReason::Stuck)],
                "{open:?}"
            );
        }
        assert_eq!(
            halts(vec![leaf(1, undecided.clone()), leaf(2, failed.clone())]),
            [(1, undecided)]
        );
        assert_eq!(
            halts(vec![leaf(1, deadline), leaf(2, HaltReason::DepthBound)]),
            [(
                1,
                HaltReason::Stopped(StopCause::Deadline(
                    crate::timeout::StepTimeoutMode::Manual(std::time::Duration::from_millis(1)),
                ))
            )]
        );
    }

    /// `wrap("s{i}")` rewrites to `wrap("l{i}")` and `wrap("r{i}")`, both of which rewrite to
    /// `wrap("s{i + 1}")`, for `diamonds` diamonds.
    fn diamond_chain_axioms(diamonds: usize) -> String {
        let rule = |label: String, from: String, to: String| {
            format!(
                r#"axiom{{}} \rewrites{{SortS{{}}}}(
                    \and{{SortS{{}}}}(wrap{{}}(\dv{{SortS{{}}}}("{from}")), \top{{SortS{{}}}}()),
                    wrap{{}}(\dv{{SortS{{}}}}("{to}"))
                ) [label{{}}("{label}")]
                "#
            )
        };
        (0..diamonds)
            .flat_map(|i| {
                let (s, l, r, next) = (
                    format!("s{i}"),
                    format!("l{i}"),
                    format!("r{i}"),
                    format!("s{}", i + 1),
                );
                [
                    rule(format!("{s}-l"), s.clone(), l.clone()),
                    rule(format!("{s}-r"), s, r.clone()),
                    rule(format!("{l}-s"), l, next.clone()),
                    rule(format!("{r}-s"), r, next),
                ]
            })
            .collect()
    }

    /// Run `initial` under `options` to its end, returning the execution for inspection.
    fn explored<'a>(
        definition: &'a BackendDefinition,
        initial: Vec<Pattern>,
        options: ExecutionOptions,
        solver: &'a dyn SmtSolver,
        observe: &'a mut dyn FnMut(&BuiltinEffect),
    ) -> Execution<'a> {
        let timeout_controller = StepTimeoutController::new(StepTimeoutOptions {
            manual: None,
            moving_average: false,
        });
        let mut execution =
            Execution::seed(definition, initial, options, solver, None, None, observe);
        execution.run(&timeout_controller);
        execution
    }

    /// Under depth-first exploration the merge table holds no depth below the back of
    /// `pending`, at which no state can arrive any more, and is empty whenever `pending` is: on
    /// a chain of 200 diamonds, where the right branch of every diamond stays pending while the
    /// left one runs to the end, every right branch's successor is merged, once.
    #[test]
    fn the_merge_table_keeps_only_the_depths_a_state_can_still_arrive_at() {
        let definition = definition(&diamond_chain_axioms(200));
        let mut observe = |_: &BuiltinEffect| {};
        let before = measure::snapshot();
        let execution = explored(
            &definition,
            vec![subject(&definition, "s0")],
            ExecutionOptions::default(),
            &crate::smt::NoSolver,
            &mut observe,
        );
        let merged = measure::snapshot()
            .delta(&before)
            .get(Counter::ExecutionStatesMerged);
        assert_eq!(merged, 200);
        let [leaf] = execution.leaves.as_slice() else {
            panic!("expected one leaf: {:?}", execution.leaves);
        };
        assert_eq!(leaf.pattern, subject(&definition, "s200"));
        assert!(!execution.merge_census.is_empty());
        let mut largest = 0;
        for &(recorded, shallowest, back) in &execution.merge_census {
            largest = largest.max(recorded);
            match back {
                None => assert_eq!(recorded, 0),
                Some(back) => assert!(shallowest.is_none_or(|depth| depth >= back)),
            }
        }
        // Every state of the left spine is recorded while the first right branch is pending.
        assert!(largest >= 400, "{largest}");
        assert_eq!(execution.merge_census.last(), Some(&(0, None, None)));
    }

    /// A chain that never converges, the configuration holding `vars` variables the run minted:
    /// `init` rewrites to `st(L, 0)`, `L` the list of the minted variables; `st(B, N)` rewrites
    /// to `st(B, N + 1)` while `N < chain`, and `st(B, 0)` also to `side`, which stays pending
    /// while the chain runs to its end.
    fn minted_chain_definition(vars: usize, chain: usize) -> BackendDefinition {
        let mut list = String::from("nil{}()");
        for i in (0..vars).rev() {
            list = format!("cons{{}}(Y{i}:SortInt{{}}, {list})");
        }
        let source = format!(
            r#"[]
            module MAIN
                hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
                hooked-sort SortBool{{}} [hook{{}}("BOOL.Bool"), hasDomainValues{{}}()]
                sort SortK{{}} []
                sort SortL{{}} []
                symbol nil{{}}() : SortL{{}} [constructor{{}}()]
                symbol cons{{}}(SortInt{{}}, SortL{{}}) : SortL{{}} [constructor{{}}()]
                symbol init{{}}() : SortK{{}} [constructor{{}}()]
                symbol side{{}}() : SortK{{}} [constructor{{}}()]
                symbol st{{}}(SortL{{}}, SortInt{{}}) : SortK{{}} [constructor{{}}()]
                hooked-symbol addInt{{}}(SortInt{{}}, SortInt{{}}) : SortInt{{}}
                    [function{{}}(), total{{}}(), hook{{}}("INT.add"), smt-hook{{}}("+")]
                hooked-symbol ltInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
                    [function{{}}(), total{{}}(), hook{{}}("INT.lt"), smt-hook{{}}("<")]
                axiom{{}} \rewrites{{SortK{{}}}}(\and{{SortK{{}}}}(init{{}}(), \top{{SortK{{}}}}()),
                    \and{{SortK{{}}}}(st{{}}({list}, \dv{{SortInt{{}}}}("0")), \top{{SortK{{}}}}()))
                    [label{{}}("init")]
                axiom{{}} \rewrites{{SortK{{}}}}(
                    \and{{SortK{{}}}}(st{{}}(B:SortL{{}}, N:SortInt{{}}),
                        \equals{{SortBool{{}}, SortK{{}}}}(
                            ltInt{{}}(N:SortInt{{}}, \dv{{SortInt{{}}}}("{chain}")),
                            \dv{{SortBool{{}}}}("true"))),
                    \and{{SortK{{}}}}(
                        st{{}}(B:SortL{{}}, addInt{{}}(N:SortInt{{}}, \dv{{SortInt{{}}}}("1"))),
                        \top{{SortK{{}}}}())) [label{{}}("next")]
                axiom{{}} \rewrites{{SortK{{}}}}(
                    \and{{SortK{{}}}}(st{{}}(B:SortL{{}}, \dv{{SortInt{{}}}}("0")), \top{{SortK{{}}}}()),
                    \and{{SortK{{}}}}(side{{}}(), \top{{SortK{{}}}}())) [label{{}}("side")]
            endmodule []"#
        );
        let syntax = parse_definition(&source).expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    /// On a run in which no two states of one depth are alike, the merge table records every
    /// state of the chain (the pending `side` keeps them reachable) and computes nothing from
    /// their patterns while each is alone at its depth. Only `side`, arriving last at the depth
    /// of `st(L, 1)`, has company: the two are hashed, and their hashes differ, so no key is
    /// built. The only keys are the final merge's, one per leaf, and the result is the path-set
    /// run's.
    #[test]
    fn a_state_set_run_that_never_converges_computes_nothing_from_its_states() {
        let (vars, chain) = (20, 60);
        let definition = minted_chain_definition(vars, chain);
        let initial = || {
            let syntax = parse_pattern("init{}()").expect("pattern should parse");
            Pattern {
                term: definition
                    .internalize_term(&syntax, &[])
                    .expect("pattern should internalize"),
                constraints: Vec::new(),
            }
        };
        let run = |result_modality| {
            let mut observe = |_: &BuiltinEffect| {};
            let keys = crate::fresh::STATE_KEYS.with(std::cell::Cell::get);
            let hashes = crate::fresh::SHAPE_HASHES.with(std::cell::Cell::get);
            let execution = explored(
                &definition,
                vec![initial()],
                ExecutionOptions {
                    result_modality,
                    ..ExecutionOptions::default()
                },
                &crate::smt::NoSolver,
                &mut observe,
            );
            let largest = execution
                .merge_census
                .iter()
                .map(|&(recorded, _, _)| recorded)
                .max();
            let configurations =
                merge_equal_final_leaves(execution.fresh_counter.request(), execution.leaves)
                    .into_iter()
                    .map(|leaf| (leaf.pattern, leaf.halt_reason))
                    .collect::<Vec<_>>();
            (
                configurations,
                largest,
                crate::fresh::STATE_KEYS.with(std::cell::Cell::get) - keys,
                crate::fresh::SHAPE_HASHES.with(std::cell::Cell::get) - hashes,
            )
        };
        let (state_set, largest, keys, hashes) = run(ResultModality::StateSet);
        let (path_set, unmerged, _, _) = run(ResultModality::PathSet);
        assert_eq!(state_set, path_set);
        assert_eq!(state_set.len(), 2, "{state_set:?}");
        assert_eq!(unmerged, None, "a path-set run keeps no merge table");
        assert!(largest >= Some(chain), "{largest:?}");
        assert_eq!(hashes, 2, "`side` and `st(L, 1)`");
        assert_eq!(keys, 2, "one key per final leaf, in the final merge");
    }

    /// A merged arrival takes no rewrite step, so the moving-average step timeout does not take
    /// its time in: on a chain of 20 diamonds, every popped state but the 20 merged arrivals is
    /// recorded.
    #[test]
    fn a_merged_arrival_is_not_timed_as_a_step() {
        let definition = definition(&diamond_chain_axioms(20));
        let mut observe = |_: &BuiltinEffect| {};
        // The controller records every step's time whether or not a timeout is set; none is
        // set, so that no step can time out.
        let timeout_controller = StepTimeoutController::new(StepTimeoutOptions::default());
        let before = measure::snapshot();
        let mut execution = Execution::seed(
            &definition,
            vec![subject(&definition, "s0")],
            ExecutionOptions::default(),
            &crate::smt::NoSolver,
            None,
            None,
            &mut observe,
        );
        execution.run(&timeout_controller);
        let delta = measure::snapshot().delta(&before);
        assert_eq!(delta.get(Counter::ExecutionStatesMerged), 20);
        assert_eq!(
            timeout_controller.recorded.get() as u64,
            delta.get(Counter::RewriteSteps) - 20
        );
    }

    /// A run that merged states and is then cancelled ends with the cancelled leaf: merging
    /// changes nothing about how a stop ends a run. The diamond chain merges twice; `probe`'s
    /// step asks the solver, which cancels the request.
    #[test]
    fn a_merged_run_cancelled_through_its_token_ends_with_the_cancelled_leaf() {
        // Constant constructors for the chain's states, so that only `probe` asks the solver.
        let constants = ["s0", "l0", "r0", "s1", "l1", "r1", "s2"]
            .map(|name| format!("symbol {name}{{}}() : SortS{{}} [constructor{{}}()]\n"))
            .concat();
        let chain = [
            ("s0", "l0"),
            ("s0", "r0"),
            ("l0", "s1"),
            ("r0", "s1"),
            ("s1", "l1"),
            ("s1", "r1"),
            ("l1", "s2"),
            ("r1", "s2"),
        ]
        .map(|(from, to)| {
            format!(
                "axiom{{}} \\rewrites{{SortS{{}}}}(\\and{{SortS{{}}}}({from}{{}}(), \\top{{SortS{{}}}}()), {to}{{}}()) [label{{}}(\"{from}-{to}\")]\n"
            )
        })
        .concat();
        let source = format!(
            r#"[]
            module MAIN
                hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
                hooked-sort SortBool{{}} [hook{{}}("BOOL.Bool"), hasDomainValues{{}}()]
                sort SortS{{}} []
                {constants}
                symbol probe{{}}(SortInt{{}}) : SortS{{}} [constructor{{}}()]
                symbol done{{}}() : SortS{{}} [constructor{{}}()]
                hooked-symbol eqInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
                    [function{{}}(), total{{}}(), hook{{}}("INT.eq"), smt-hook{{}}("=")]
                axiom{{}} \rewrites{{SortS{{}}}}(
                    \and{{SortS{{}}}}(
                        probe{{}}(X:SortInt{{}}),
                        \equals{{SortBool{{}}, SortS{{}}}}(
                            eqInt{{}}(X:SortInt{{}}, \dv{{SortInt{{}}}}("0")),
                            \dv{{SortBool{{}}}}("true")
                        )
                    ),
                    done{{}}()
                ) [label{{}}("probe")]
                {chain}
            endmodule []"#
        );
        let syntax = parse_definition(&source).expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let term = |source: &str| {
            definition
                .internalize_term(&parse_pattern(source).expect("term should parse"), &[])
                .expect("term should internalize")
        };
        let initial = vec![
            Pattern {
                term: term("s0{}()"),
                constraints: Vec::new(),
            },
            Pattern {
                term: term("probe{}(X:SortInt{})"),
                constraints: Vec::new(),
            },
        ];
        let token = crate::stop::CancellationToken::new();
        let solver = CancelOnFirstQuery {
            token: token.clone(),
        };
        let before = measure::snapshot();
        let result = token.scope(|| {
            super::super::execute_disjunction_with_solver_and_observer(
                &definition,
                initial,
                ExecutionOptions::default(),
                &solver,
                |_| {},
            )
        });
        let merged = measure::snapshot()
            .delta(&before)
            .get(Counter::ExecutionStatesMerged);
        assert_eq!(merged, 2);
        let halts = result
            .leaves
            .iter()
            .map(|leaf| leaf.halt_reason.clone())
            .collect::<Vec<_>>();
        assert_eq!(
            halts,
            [HaltReason::Stuck, HaltReason::Stopped(StopCause::Cancelled)],
            "{result:#?}"
        );
        assert_eq!(result.leaves[1].pattern.term, term("probe{}(X:SortInt{})"));
    }

    /// A solver that raises a passed step deadline at its `nth` query (counting from 1), once,
    /// and otherwise decides nothing.
    struct DeadlineAtQuery {
        nth: usize,
        queries: std::cell::Cell<usize>,
    }

    impl DeadlineAtQuery {
        fn query(&self) -> Stoppable<()> {
            self.queries.set(self.queries.get() + 1);
            if self.queries.get() != self.nth {
                return Ok(());
            }
            let _deadline = crate::stop::arm_deadline(
                std::time::Instant::now(),
                crate::timeout::StepTimeoutMode::Manual(std::time::Duration::ZERO),
            );
            crate::stop::check()
        }
    }

    impl SmtSolver for DeadlineAtQuery {
        fn is_sat(
            &self,
            _predicates: &[Predicate],
            _substitution: &crate::substitution::Substitution,
        ) -> Stoppable<Result<crate::smt::Satisfiability, crate::smt::SmtError>> {
            self.query()?;
            Ok(Ok(crate::smt::Satisfiability::Sat))
        }

        fn check_predicates(
            &self,
            _known: &[Predicate],
            _substitution: &crate::substitution::Substitution,
            _checked: &[Predicate],
        ) -> Stoppable<Result<crate::smt::Validity, crate::smt::SmtError>> {
            self.query()?;
            Ok(Ok(crate::smt::Validity::Contingent))
        }
    }

    /// `start(X)` rewrites to `l(X)` and `r(X)`, both of which rewrite to `m(X)`; `m(X)` rewrites
    /// to `t(f(X))` by `m-to-t`, where `f(X) = 1` where `X == 1`, which normalising `t(f(X))` asks
    /// the solver; unless `terminal`, `m(X)` also rewrites to `done` where `X == 0`, which its step
    /// asks the solver, at a higher priority.
    fn stopped_merge_definition(terminal: bool) -> BackendDefinition {
        // A terminal rule ends a path only as its state's unique successor, so with `m-to-t`
        // terminal `m-done` is left out.
        let m_done = if terminal {
            ""
        } else {
            r#"
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(
                        m{}(X:SortInt{}),
                        \equals{SortBool{}, SortS{}}(
                            eqInt{}(X:SortInt{}, \dv{SortInt{}}("0")),
                            \dv{SortBool{}}("true")
                        )
                    ),
                    done{}()
                ) [label{}("m-done"), priority{}("10")]"#
        };
        let source = r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                sort SortS{} []
                symbol start{}(SortInt{}) : SortS{} [constructor{}()]
                symbol l{}(SortInt{}) : SortS{} [constructor{}()]
                symbol r{}(SortInt{}) : SortS{} [constructor{}()]
                symbol m{}(SortInt{}) : SortS{} [constructor{}()]
                symbol t{}(SortInt{}) : SortS{} [constructor{}()]
                symbol f{}(SortInt{}) : SortInt{} [function{}(), total{}()]
                symbol done{}() : SortS{} [constructor{}()]
                hooked-symbol eqInt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.eq"), smt-hook{}("=")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(start{}(X:SortInt{}), \top{SortS{}}()), l{}(X:SortInt{})
                ) [label{}("start-l")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(start{}(X:SortInt{}), \top{SortS{}}()), r{}(X:SortInt{})
                ) [label{}("start-r")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(l{}(X:SortInt{}), \top{SortS{}}()), m{}(X:SortInt{})
                ) [label{}("l-m")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(r{}(X:SortInt{}), \top{SortS{}}()), m{}(X:SortInt{})
                ) [label{}("r-m")]
                M_DONE
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(m{}(X:SortInt{}), \top{SortS{}}()),
                    t{}(f{}(X:SortInt{}))
                ) [label{}("m-to-t"), priority{}("50")]
                axiom{R} \implies{R}(
                    \and{R}(
                        \equals{SortBool{}, R}(
                            eqInt{}(X:SortInt{}, \dv{SortInt{}}("1")),
                            \dv{SortBool{}}("true")
                        ),
                        \and{R}(\in{SortInt{}, R}(X0:SortInt{}, X:SortInt{}), \top{R}())
                    ),
                    \equals{SortInt{}, R}(
                        f{}(X0:SortInt{}),
                        \and{SortInt{}}(\dv{SortInt{}}("1"), \top{SortInt{}}())
                    )
                ) [label{}("f-one")]
            endmodule []"#
            .replace("M_DONE", m_done);
        let syntax = parse_definition(&source).expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    /// The two equal arrivals `m(X)` of the diamond merge: the first is recorded once its
    /// expansion completes, and the second is merged into it. A stop during the first one's
    /// expansion, in its step or after its step while normalising its terminal successor
    /// (`m-to-t`), leaves it unrecorded, so the second is expanded itself and its leaves are
    /// reported: a stopped expansion never stands for an equal state's subtree.
    #[test]
    fn an_expansion_a_stop_cut_short_is_not_recorded_for_merging() {
        let definitions = [false, true].map(stopped_merge_definition);
        let start = |definition: &BackendDefinition| Pattern {
            term: definition
                .internalize_term(&parse_pattern("start{}(X:SortInt{})").unwrap(), &[])
                .unwrap(),
            constraints: Vec::new(),
        };
        let head = |leaf: &ExecutionLeaf| match leaf.pattern.term.kind() {
            crate::term::TermKind::Application { symbol, .. } => symbol.name.to_string(),
            other => panic!("expected an application, found {other:?}"),
        };
        let deadline = || {
            HaltReason::Stopped(StopCause::Deadline(
                crate::timeout::StepTimeoutMode::Manual(std::time::Duration::ZERO),
            ))
        };
        let run = |nth, terminal: bool| {
            let solver = DeadlineAtQuery {
                nth,
                queries: std::cell::Cell::new(0),
            };
            let before = measure::snapshot();
            let definition = &definitions[usize::from(terminal)];
            let result = super::super::execute_disjunction_with_solver_and_observer(
                definition,
                vec![start(definition)],
                ExecutionOptions {
                    terminal_rules: if terminal {
                        BTreeSet::from(["m-to-t".to_owned()])
                    } else {
                        BTreeSet::new()
                    },
                    ..ExecutionOptions::default()
                },
                &solver,
                |_| {},
            );
            let merged = measure::snapshot()
                .delta(&before)
                .get(Counter::ExecutionStatesMerged);
            (result, merged, solver.queries.get())
        };

        for terminal in [false, true] {
            // Without a stop the second `m(X)` is merged.
            let (unstopped, merged, queries) = run(0, terminal);
            assert_eq!(merged, 1, "{unstopped:#?}");
            // A stop at each query of the first `m(X)`'s expansion leaves it unrecorded: its
            // stopped leaf is reported, and the second `m(X)` is expanded into the leaves the
            // unstopped run reports.
            let mut stopped_in_the_step = false;
            let mut stopped_after_the_step = false;
            for nth in 1..=queries {
                let (result, merged, _) = run(nth, terminal);
                let Some(stopped) = result
                    .leaves
                    .iter()
                    .find(|leaf| leaf.halt_reason == deadline())
                else {
                    continue;
                };
                match (head(stopped).as_str(), terminal) {
                    // The remainder of `m-done`, `m(X)` where `X =/= 0`, is a state of its own:
                    // a stop in its expansion leaves the first `m(X)` recorded.
                    ("m", _) if !stopped.pattern.constraints.is_empty() => {
                        assert_eq!(merged, 1, "query {nth}: {result:#?}");
                        continue;
                    }
                    ("m", _) => stopped_in_the_step = true,
                    // A terminal successor is normalised by the expansion of the `m(X)` it
                    // succeeds.
                    ("t", true) => stopped_after_the_step = true,
                    // Otherwise `t(f(X))` is a state of its own, and the stop is in its own
                    // expansion: the first `m(X)` was recorded and the second merged into it.
                    ("t", false) => {
                        assert_eq!(merged, 1, "query {nth}: {result:#?}");
                        continue;
                    }
                    (other, _) => panic!("query {nth} stopped `{other}`: {result:#?}"),
                }
                assert_eq!(merged, 0, "query {nth}: {result:#?}");
                let rest = result
                    .leaves
                    .iter()
                    .filter(|leaf| leaf.halt_reason != deadline())
                    .cloned()
                    .collect::<Vec<_>>();
                assert_eq!(
                    rest.iter().map(head).collect::<Vec<_>>(),
                    unstopped.leaves.iter().map(head).collect::<Vec<_>>(),
                    "query {nth}, terminal {terminal}: {result:#?}"
                );
            }
            // Without the terminal rule the first `m(X)`'s step asks the solver; with it, only
            // the normalisation of its terminal successor does.
            assert_eq!(stopped_in_the_step, !terminal);
            assert_eq!(stopped_after_the_step, terminal);
        }
    }

    /// A leaf whose reason is decided is normalised before it is published; a normalisation
    /// that runs out of native stack is dismissed (the leaf keeps its reason and its unsimplified
    /// pattern) and still counted (`stop::counting_stack_stops`).
    #[test]
    fn a_leaf_normalisation_that_runs_out_of_stack_keeps_the_leaf_and_is_counted() {
        let source = r#"[] module MAIN
            hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
            hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
            hooked-symbol subInt{}(SortInt{}, SortInt{}) : SortInt{}
                [function{}(), total{}(), hook{}("INT.sub"), smt-hook{}("-")]
            hooked-symbol addInt{}(SortInt{}, SortInt{}) : SortInt{}
                [function{}(), total{}(), hook{}("INT.add"), smt-hook{}("+")]
            hooked-symbol gtInt{}(SortInt{}, SortInt{}) : SortBool{}
                [function{}(), total{}(), hook{}("INT.gt"), smt-hook{}(">")]
            symbol deep{}(SortInt{}) : SortInt{} [function{}(), total{}()]
            sort SortS{} []
            symbol done{}(SortInt{}) : SortS{} [constructor{}(), functional{}(), injective{}()]
            axiom{R} \implies{R}(\and{R}(\top{R}(), \and{R}(\in{SortInt{}, R}(X0:SortInt{}, \dv{SortInt{}}("0")), \top{R}())), \equals{SortInt{}, R}(deep{}(X0:SortInt{}), \and{SortInt{}}(\dv{SortInt{}}("0"), \top{SortInt{}}()))) []
            axiom{R} \implies{R}(\and{R}(\equals{SortBool{}, R}(gtInt{}(VarN:SortInt{}, \dv{SortInt{}}("0")), \dv{SortBool{}}("true")), \and{R}(\in{SortInt{}, R}(X0:SortInt{}, VarN:SortInt{}), \top{R}())), \equals{SortInt{}, R}(deep{}(X0:SortInt{}), \and{SortInt{}}(addInt{}(deep{}(subInt{}(VarN:SortInt{}, \dv{SortInt{}}("1"))), \dv{SortInt{}}("1")), \top{SortInt{}}()))) []
        endmodule []"#;
        let syntax = parse_definition(source).expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let pattern = Pattern {
            term: definition
                .internalize_term(
                    &parse_pattern(r#"done{}(deep{}(\dv{SortInt{}}("100000")))"#)
                        .expect("the leaf parses"),
                    &[],
                )
                .expect("the leaf internalizes"),
            constraints: Vec::new(),
        };
        let (kept_reason, kept_pattern, stops) = std::thread::scope(|scope| {
            std::thread::Builder::new()
                .stack_size(8 << 20)
                .spawn_scoped(scope, || {
                    // The state holds thread-confined values, so it is made on the thread.
                    let state = ExecutionState {
                        pattern: pattern.clone(),
                        depth: 0,
                        trace: PathTrace::default(),
                        retain_trace: false,
                        kind: ExecutionStateKind::Rewritable,
                        observation: None,
                        effects: EffectJournal::default(),
                        io: ExecutionIoState::default(),
                        io_enabled: false,
                        is_initial_input: true,
                        defined_where: Vec::new(),
                        diagnostics: PathDiagnostics::new_request(),
                        producer: None,
                    };
                    let (leaf, stops) = crate::stop::with_segment_budget(0, || {
                        crate::stop::counting_stack_stops(|| {
                            externalise_leaf(
                                &definition,
                                state,
                                pattern.clone(),
                                HaltReason::Stuck,
                                64,
                                &crate::smt::NoSolver,
                                &mut ObservationLog::default(),
                                None,
                            )
                        })
                    });
                    (
                        leaf.halt_reason == HaltReason::Stuck,
                        leaf.pattern == pattern,
                        stops,
                    )
                })
                .expect("the thread starts")
                .join()
                .expect("the normalisation does not panic")
        });
        assert!(stops >= 1, "no stack stop was counted");
        assert!(kept_reason, "the leaf did not keep its reason");
        assert!(
            kept_pattern,
            "the leaf did not keep its unsimplified pattern"
        );
    }

    /// Under `discard_stopped` a run that a cancellation ended builds no result: no leaves, no
    /// final merge, and the cause in `stopped`. Without it the same run returns the leaves
    /// finished before the cancellation and the cancelled leaf, with the cause in `stopped` too.
    /// The initial disjunction is that of `a_state_set_merge_keeps_the_leaf_of_a_stop_that_ended_
    /// the_run`: `stuck`'s normalisation asks the solver, which cancels the request.
    #[test]
    fn a_run_a_cancellation_ended_builds_no_result_when_asked_to_discard_it() {
        let definition = prelude_definition();
        let term = |source: &str| {
            definition
                .internalize_term(&parse_pattern(source).expect("term should parse"), &[])
                .expect("term should internalize")
        };
        let gt_zero = Predicate::Equals(
            term(r#"gtInt{}(X:SortInt{}, \dv{SortInt{}}("0"))"#),
            term(r#"\dv{SortBool{}}("true")"#),
        );
        let initial = vec![
            Pattern {
                term: term("done{}()"),
                constraints: Vec::new(),
            },
            Pattern {
                term: term("stuck{}(X:SortInt{})"),
                constraints: vec![gt_zero],
            },
            Pattern {
                term: term("done{}()"),
                constraints: Vec::new(),
            },
            Pattern {
                term: term(r#"wrap{}(\dv{SortInt{}}("0"))"#),
                constraints: Vec::new(),
            },
        ];
        let run = |discard_stopped| {
            let token = crate::stop::CancellationToken::new();
            let solver = CancelOnFirstQuery {
                token: token.clone(),
            };
            let merges = FINAL_MERGES.with(std::cell::Cell::get);
            let result = token.scope(|| {
                super::super::execute_disjunction_with_solver_and_observer(
                    &definition,
                    initial.clone(),
                    ExecutionOptions {
                        max_depth: 64,
                        discard_stopped,
                        ..ExecutionOptions::default()
                    },
                    &solver,
                    |_| {},
                )
            });
            (result, FINAL_MERGES.with(std::cell::Cell::get) - merges)
        };

        let (discarded, merges) = run(true);
        assert_eq!(discarded.leaves, []);
        assert_eq!(discarded.stopped, Some(StopCause::Cancelled));
        assert_eq!(merges, 0, "a discarded run does no final merge");

        let (kept, merges) = run(false);
        assert_eq!(kept.stopped, Some(StopCause::Cancelled));
        assert_eq!(merges, 1);
        assert_eq!(
            kept.leaves
                .iter()
                .map(|leaf| leaf.halt_reason.clone())
                .collect::<Vec<_>>(),
            [
                HaltReason::Stuck,
                HaltReason::Stuck,
                HaltReason::Stopped(StopCause::Cancelled)
            ]
        );
    }

    /// Under `discard_stopped` the final merge polls once per leaf: a cancellation that arrives
    /// after the exploration ended, while the leaves are merged, discards them. Without it the
    /// merge polls nothing and returns the merged leaves.
    #[test]
    fn a_cancellation_during_the_final_merge_discards_the_leaves_when_asked_to() {
        let definition = definition("");
        let leaves = ["a", "b", "a"].map(|name| ExecutionLeaf {
            pattern: subject(&definition, name),
            depth: 1,
            trace: Vec::new(),
            branch: Vec::new(),
            observations: Vec::new(),
            effects: Vec::new(),
            io: ExecutionIoState::default(),
            halt_reason: HaltReason::Stuck,
            diagnostics: Vec::new(),
        });
        let token = crate::stop::CancellationToken::new();
        token.cancel();
        let polled = token.scope(|| {
            merge_final_leaves(&RequestNames::default(), leaves.to_vec(), run_ending_stop)
        });
        assert_eq!(polled, Err(StopCause::Cancelled));
        let unpolled =
            token.scope(|| merge_equal_final_leaves(&RequestNames::default(), leaves.to_vec()));
        assert_eq!(unpolled.len(), 2);
    }
}
