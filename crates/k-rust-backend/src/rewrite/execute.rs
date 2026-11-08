//! ```toml algorithm
//! id = "backend.rewrite.execute"
//! name = "depth-first exploration of a rewrite tree"
//! sites = ["execute_using", "Execution::run", "Execution::expand", "Execution::merged", "commit_applied", "ExecutionState::leaf", "merge_equal_final_leaves", "enqueue_execution_states", "Execution::match_state"]
//! variable = "s = states the selected strategy would take from pending without max_work; d = maximum rewrite depth; L = final leaves; K = recorded arrivals in one depth/shape-hash bucket; J = diagnostic entries compared by one absorption test"
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
//! bound = "O(min(s, max_work)) state pops, plus initialization and callee work below; max_depth limits rewrite depth and max_breadth limits the queued frontier, not the per-state branching factor, so neither gives a b^d total-state bound (remainders can also be queued at the same depth). Exploration is unbounded under the defaults (max_depth = u64::MAX, max_breadth = None, max_work = None); one integer comparison per state for the work budget; each state performs one term simplification, predicate pass, and rewrite step (a successor whose step already normalized it under strategy any takes that normalization instead), plus one predicate simplification and one satisfiability query per undefined-step (trivial) entry of its step; a step with such entries and an applied candidate (unless it stops at a branch with several candidates or a remainder), or one exploring all paths with several candidates, no remainder and a candidate a cut-point or terminal rule selects, normalizes each candidate's successor, which a defined one's successor takes instead of normalizing itself; a successor that normalizes to bottom, the first of its step to do so, normalizes each sibling candidate not yet normalized; and a step's undefined step, whichever route finds its candidates undefined (the step itself, stopping at branches, or a successor's normalization), takes one predicate simplification and one satisfiability query per undefined candidate, and one more predicate simplification when several candidates are left non-empty over one term; under strategy any, a step the sequential step takes by a cut-point or terminal rule selected also takes one all-path rewrite step from its state, with the condition and normal-form memos set aside so that it is served from none and fills none, and normalizes the successors of that step's candidates until two are defined (Execution::siblings); under an in-process successor reading, each candidate and remainder of a step holding a selected rule's candidate is externalized once, its path condition only, and read once (Execution::read_stop_step); and a state stopped at max_depth is simplified once more; an initial state the run does not assume defined also walks its term's definedness once and simplifies the obligations that walk finds once"
//!
//! [[cost]]
//! mode = "final leaf merge (merge_equal_final_leaves)"
//! bound = "nothing with fewer than two leaves carrying a configuration; otherwise one RequestNames::state_key (backend.fresh.variables) and one console observation (linear in the leaf's transcript) per such leaf, and O(L^2) key comparisons; each merged leaf's diagnostics are appended to the retained leaf's without repeats, in time the product of the two lists' lengths; a leaf is merged only into a retained leaf of its configuration that may absorb it (merge_class), and a run-ending leaf is kept as is"
//!
//! [[cost]]
//! mode = "state-set exploration merge (Execution::merged)"
//! bound = "one expansion per distinct (depth, RequestNames::state_key, effects, observed console, console availability) class, times the maximal diagnostic sets recorded for it (one set unless converging paths carry incomparable diagnostics); one E2/E3 simplification per arriving state; nothing computed from a state while it is alone at its depth; once a second state arrives there, one RequestNames::shape_hash per state of the depth (linear in its nodes that hold variables), and one RequestNames::state_key per state whose hash another state of the depth shares, each computed once; each arriving state scans up to K recorded arrivals of its depth/shape hash, O(K) absorption tests and O(K^2) across K non-absorbing arrivals, including incomparable diagnostic histories without a hash collision; each test charges diagnostic subset comparisons over J, structural key equality and shared-history comparisons; the effects and consoles of two arrivals are compared by fingerprint in O(1) and then back to their shared history; memory: the states recorded at depths not below the shallowest pending state, each a record of about 300 bytes (64-bit) and a copy of its constraint list, holding its term by its shared nodes, not a copy, so the sum of the recorded constraint-list lengths: quadratic in path length when the path condition grows by a conjunct per step"
//!
//! [[cost]]
//! mode = "reached-state matching (match_states)"
//! bound = "only for eligible reached states until a clean reach without a term conjunction: one isolated leaf-form normalization when constraints remain, one target-disjunction match in Execution mode and, when proof_agreement requires and the first answer decided, one in Proof mode, plus ground_defined for a proposed reach. Each match pays backend.search.patterns, including simplification/solver work. Absorbed arrivals reuse the stored verdict. At most five state summaries are retained, with their configurations and prefix diagnostics; isolation stays on the step clock."
//!
//! [[cost]]
//! mode = "condition recording (collect_conditions)"
//! bound = "per entry of a selected rule: collect/sort the condition-read bindings, clone path/match knowledge and hash/compare the EntryKey, even for a duplicate or capped entry; per admitted record, one isolated bottom-up evaluation of its condition with NoSolver, substitutions and capped output-value checks; at most the configured record limit per rule, with record_polls per evaluation and max_value_size per stored value. Polls do not bound the byte cost of bigint hooks or intermediate terms. This extra evaluation is off the step clock but costs wall time (coverage::conditions)."
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
//! an equal-leaf merge; the result covers paths until the configured depth, frontier or work
//! limit. The card counts state pops separately from their callee work: each state one term simplification,
//! one predicate pass, and one rewrite step; `Counter::RewriteSteps`. A state-set run that explores
//! every branch also merges each state equal at its depth to a recorded one
//! (`exploration_merge`), so its states are the distinct states of each depth;
//! `Counter::ExecutionStatesMerged`. Not breadth-first: `enqueue_execution_states` pushes
//! successors to the front, so children are visited before siblings.

// The phase methods return `Phase<T>` (below), whose `Err` is the finished `ExecutionLeaf`,
// boxed: one leaf per state, moved once into `leaves`.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::sync::Arc;

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

use super::probe::{
    self, CycleWatch, Probe, ProbeArrival, ProbeCycle, ProbeDecision, ProbeLeaf, ProbeState,
    Watched,
};
use super::refutation_memo::RefutationMemo;
use super::stop_condition::{
    self, Arrival as StopArrival, InProcess, StopCondition, StopConditionRefusal, StopDecision,
    StopSide, SuccessorReading,
};
use super::work::Work;
use super::{
    AppliedRule, ExecutionBranchMode, ExecutionLeaf, ExecutionMode, ExecutionOptions,
    ExecutionResult, HaltReason, IndeterminateReason, InitialDefinedness,
    InitialSimplificationStatus, NormalizedSuccessor, PassedStop, Pattern, RemainderBranch,
    RemainderSimplification, RewriteResult, SubjectDefinedness, TraceEntry, TraceKind,
    TrivialApplication, Truth, UndecidedStep, applied_trivial_halt,
    exploration_merge::{Arrival, ExplorationMerge},
    initial_definedness, normalize_pattern_substitution,
    path_trace::PathTrace,
    predicate_truth, predicates_truth, retain_substitution_predicates,
    rewrite_step_with_optional_execution,
    state_match::{MatchMark, StateMatcher},
    stuck, trivial_halt, vacuous_halt,
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
    match execute_asking(
        definition,
        initial,
        options,
        solver,
        initial_io,
        observation,
        observe,
        InProcess::default(),
    ) {
        Ok(outcome) => outcome,
        Err(refusal) => unreachable!("a run without a stop condition has no refusal: {refusal}"),
    }
}

/// [`execute_using`] with what an in-process caller adds (`stop_condition`): a stop condition
/// asked at each arrival at a stop, whose refusal fails the run, and a reading of a stop rule's
/// step's candidates.
pub(super) fn execute_with_condition(
    definition: &BackendDefinition,
    initial: Vec<Pattern>,
    options: ExecutionOptions,
    solver: &dyn SmtSolver,
    observation: Option<&ObservationOptions>,
    in_process: InProcess<'_>,
) -> Result<ExecutionResult, StopConditionRefusal> {
    execute_asking(
        definition,
        initial,
        options,
        solver,
        None,
        observation,
        |_| {},
        in_process,
    )
    .map(|(result, _)| result)
}

#[allow(clippy::too_many_arguments)]
fn execute_asking(
    definition: &BackendDefinition,
    initial: Vec<Pattern>,
    options: ExecutionOptions,
    solver: &dyn SmtSolver,
    initial_io: Option<ExecutionIoState>,
    observation: Option<&ObservationOptions>,
    observe: impl FnMut(&BuiltinEffect),
    in_process: InProcess<'_>,
) -> Result<(ExecutionResult, InitialSimplificationStatus), StopConditionRefusal> {
    // Every stack stop of the run is counted, those that end a state and those a refinement
    // dismisses alike (`ExecutionResult::stack_stops`), and so is every undecided answer the
    // solver delivers to a decision of the run (`ExecutionResult::smt_unknowns`).
    let counting = crate::smt::UndecidedCounting::new(solver);
    let (outcome, stack_stops) = crate::stop::counting_stack_stops(|| {
        execute_counted(
            definition,
            initial,
            options,
            &counting,
            solver,
            initial_io,
            observation,
            observe,
            in_process,
        )
    });
    let (mut result, status) = outcome?;
    result.stack_stops = stack_stops;
    result.smt_unknowns = counting.undecided();
    Ok((result, status))
}

/// [`execute_using`] inside its count of stack stops. `solver` counts the run's undecided
/// answers; `match_solver`, the same solver without that count, answers the state matcher,
/// which counts its own (`state_match`).
#[allow(clippy::too_many_arguments)]
fn execute_counted(
    definition: &BackendDefinition,
    initial: Vec<Pattern>,
    options: ExecutionOptions,
    solver: &dyn SmtSolver,
    match_solver: &dyn SmtSolver,
    initial_io: Option<ExecutionIoState>,
    observation: Option<&ObservationOptions>,
    mut observe: impl FnMut(&BuiltinEffect),
    in_process: InProcess<'_>,
) -> Result<(ExecutionResult, InitialSimplificationStatus), StopConditionRefusal> {
    let InProcess {
        condition,
        reading,
        probe,
    } = in_process;
    let _span = measure::algorithm_span(Algorithm::BackendRewriteExecute);
    let _apart = crate::rule::ApartScope::enter();
    // Every evaluation of the run, its rule and equation conditions included, runs in the mode
    // the request asks for (`crate::evaluation`), and knows whether the run has a console.
    let _evaluation =
        crate::evaluation::EvaluationScope::enter_run(options.evaluation, initial_io.is_some());
    let _domain = crate::term::domain::DomainScope::enter(definition);
    let _hook_values = crate::deferred::HookValueScope::enter(definition);
    let timeout_controller = StepTimeoutController::new(StepTimeoutOptions {
        manual: options.step_timeout,
        moving_average: options.moving_average_timeout,
    });
    let collect_coverage = options.collect_coverage;
    let collect_offered = options.collect_offered;
    let collect_counts = options.collect_counts;
    let collect_conditions = options.collect_conditions.clone();
    let collect_guards = options.collect_guards.clone();
    let collect_bindings = options.collect_bindings.clone();
    let collect_committed = options.collect_committed;
    // Whether a bound that counts the whole run's exploration can end it: then every leaf rests
    // on the work of every path, off its own included.
    let bounded_by_run = options.max_work.is_some() || options.max_breadth.is_some();
    // Under state-set, the standing of every halt a leaf of the run can have.
    let replaceable_halts =
        (options.result_modality == ResultModality::StateSet).then(|| Standing::possible(&options));
    // The condition's refusal, which fails the run: its leaves are no result.
    let refused = std::cell::RefCell::new(None);
    let run = || {
        let mut execution = Execution::seed(
            definition,
            initial,
            options,
            solver,
            match_solver,
            initial_io,
            observation,
            &mut observe,
            // Reborrowed for the run alone, which ends inside this call.
            condition.map(|condition| -> &mut dyn StopCondition { &mut *condition }),
            reading,
            probe.map(|probe| -> &mut dyn Probe { &mut *probe }),
        );
        if execution.options.max_breadth == Some(0) {
            return execution.collect_at_breadth_zero();
        }
        execution.run(&timeout_controller);
        *refused.borrow_mut() = execution.refusal.take();
        execution.collect()
    };
    // Every mark the run notes, whatever becomes of the work that noted it.
    let run = || {
        let ((mut result, status), facts) = crate::path_facts::run(run);
        result.implementation_chosen_values = facts
            .iter()
            .filter_map(crate::path_facts::PathFact::chosen_value)
            .cloned()
            .collect();
        // What undone work never rolls back, of the load and then of the run.
        let record =
            crate::path_facts::RunRecord::of(definition.load_record().iter().chain(&facts));
        result.contradicted_claims = record.contradicted_claims;
        result.allowance_refusals = record.allowance_refusals;
        result.unsupported_hooks = record.unsupported_hooks;
        result.short_circuit_readings = record.short_circuit_readings;
        // `max_work` and `max_breadth` count the states of every path: whether either bound
        // fires, and where, rests on exploration off a leaf's path, so in another model a leaf
        // may be cut elsewhere or not at all. Every leaf of such a run carries every mark the
        // run noted.
        //
        // Under state-set, the final merge lets the first leaf of a configuration it meets stand
        // for a later one whose halt it may absorb, and the first can come from a path that
        // exists only in another model: a leaf whose halt another class can absorb rests on
        // every path, and carries every mark the run noted (`replaceable_in_state_set`).
        let rests_on_every_path = |leaf: &ExecutionLeaf| {
            bounded_by_run
                || replaceable_halts
                    .as_deref()
                    .is_some_and(|possible| replaceable_in_state_set(possible, &leaf.halt_reason))
        };
        if !facts.is_empty() && result.leaves.iter().any(rests_on_every_path) {
            let facts = crate::path_facts::diagnostics(
                &facts
                    .iter()
                    .cloned()
                    .collect::<crate::path_facts::FactSet>(),
            );
            for leaf in &mut result.leaves {
                if rests_on_every_path(leaf) {
                    extend_distinct(&mut leaf.diagnostics, &facts);
                }
            }
        }
        (result, status)
    };
    if !collect_coverage {
        let outcome = run();
        return match refused.into_inner() {
            Some(refusal) => Err(refusal),
            None => Ok(outcome),
        };
    }
    // The definition is selected and internalized before this call, so the collection holds
    // what the run applied and nothing a module's construction did (`crate::coverage`).
    let ((mut result, status), coverage) = crate::coverage::collect_all(
        collect_offered,
        collect_counts,
        collect_committed,
        collect_conditions,
        collect_guards,
        collect_bindings,
        run,
    );
    if let Some(refusal) = refused.into_inner() {
        return Err(refusal);
    }
    result.coverage = Some(coverage);
    Ok((result, status))
}

/// A phase either hands the state on or ends it as a leaf.
///
/// The leaf is boxed: a state ends as a leaf once, but every phase result, a leaf or not, is
/// moved through the collection scopes around the phases (`crate::path_facts::observed_by`,
/// `collect_with_diagnostics`, ...), and an unboxed leaf made each of them hundreds of bytes.
type Phase<T> = Result<T, Box<ExecutionLeaf>>;

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
    /// Each selected stop rule the run went on past, by the name the request selected it by,
    /// with the shallowest depth at which it did (`ExecutionResult::passed_stops`).
    passed_stops: BTreeMap<String, u64>,
    /// The states visited and the budget (`work::Work`).
    work: Work,
    /// The refutations of rule attempts the sequential step reuses across the run's states
    /// (`refutation_memo`): the run fixes the definition, the solver and the simplification
    /// options every stored refutation was decided under.
    refutations: RefutationMemo,
    /// The merge table of a state-set run that explores every branch; `None` otherwise.
    merge: Option<ExplorationMerge>,
    /// The state being expanded, as the merge table would record it once its expansion
    /// completes; `None` when it takes no part in merging.
    arrival: Option<Arrival>,
    /// Whether the state being expanded was merged ([`Execution::merged`]).
    merged_arrival: bool,
    /// The state matcher of a run that asks for state matches ([`ExecutionOptions::match_states`]).
    matcher: Option<StateMatcher<'a>>,
    /// The stop condition of an in-process run that has one (`stop_condition`).
    condition: Option<&'a mut dyn StopCondition>,
    /// The caller's reading of a stop rule's step's candidates, where it gives one
    /// (`stop_condition`, "Successors read by the caller").
    reading: Option<&'a dyn SuccessorReading>,
    /// The condition's refusal, once it refused: the run ends there, with no result.
    refusal: Option<StopConditionRefusal>,
    /// The probe of an in-process run that has one (`probe`).
    probe: Option<&'a mut dyn Probe>,
    /// Whether the probe is still asked: it is, until the path splits, ends, or the probe's
    /// own answer ends it (`probe`, "One path").
    probing: bool,
    /// The states the probe's path keeps to recognize a return, while the probe keeps some and
    /// has not been told of one (`probe`, "Cycles").
    cycles: Option<CycleWatch>,
    /// The number of leaves before the expansion of the state being expanded: a leaf pushed
    /// since is the expansion's own, so the state has split once its step leaves another path.
    expansion_leaves: usize,
    /// After each expansion: the merge table's size, its shallowest recorded depth, and the
    /// depth of the back of `pending`.
    #[cfg(test)]
    merge_census: Vec<(usize, Option<u64>, Option<u64>)>,
}

impl<'a> Execution<'a> {
    /// E0: `pending` holds the initial patterns at depth 0 in input order, each marked as an
    /// initial input.
    #[allow(clippy::too_many_arguments)]
    fn seed(
        definition: &'a BackendDefinition,
        initial: Vec<Pattern>,
        mut options: ExecutionOptions,
        solver: &'a dyn SmtSolver,
        match_solver: &'a dyn SmtSolver,
        initial_io: Option<ExecutionIoState>,
        observation: Option<&'a ObservationOptions>,
        observe: &'a mut dyn FnMut(&BuiltinEffect),
        condition: Option<&'a mut dyn StopCondition>,
        reading: Option<&'a dyn SuccessorReading>,
        probe: Option<&'a mut dyn Probe>,
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
                    stops: 0,
                    arrivals: 0,
                    arriving: None,
                    probing: None,
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
            let (resumed, facts) = crate::path_facts::collect(|| {
                // The request's own open literals are read by every path (`crate::literal`).
                for literal in &options.request_literals {
                    crate::path_facts::note(crate::path_facts::PathFact::ChosenValue(
                        crate::literal::mark(literal),
                    ));
                }
                crate::deferred::resumed_constraints(
                    definition,
                    std::mem::take(&mut state.pattern.constraints),
                )
            });
            state
                .diagnostics
                .extend(&crate::path_facts::diagnostics(&facts.all()));
            match resumed {
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
        let matcher = options.match_states.take().map(|match_states| {
            StateMatcher::new(
                match_states,
                match_solver,
                options.max_simplification_iterations,
            )
        });
        let merge = (options.result_modality == ResultModality::StateSet
            && options.branch_mode == ExecutionBranchMode::ExploreAll)
            .then(ExplorationMerge::default);
        // Under strategy `any` a state the path leaves by one successor may have others in the
        // definition, so no return is recognized there (`probe`, "Cycles").
        let cycles = probe
            .as_deref()
            .filter(|_| options.mode == ExecutionMode::All)
            .and_then(|probe| CycleWatch::new(probe::isolated(|| probe.cycle_states())));
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
            passed_stops: BTreeMap::new(),
            work,
            refutations: RefutationMemo::default(),
            merge,
            arrival: None,
            merged_arrival: false,
            matcher,
            condition,
            reading,
            refusal: None,
            probing: probe.is_some(),
            probe,
            cycles,
            expansion_leaves: 0,
            #[cfg(test)]
            merge_census: Vec::new(),
        }
    }

    /// `max_breadth = Some(0)`: every initial pattern is a `BreadthBound` leaf.
    fn collect_at_breadth_zero(mut self) -> (ExecutionResult, InitialSimplificationStatus) {
        self.drain_at_breadth_bound();
        self.probe_seed();
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
                expanded: self.work.expanded(),
                stack_stops: 0,
                smt_unknowns: 0,
                stopped: self.stopped,
                implementation_chosen_values: Vec::new(),
                contradicted_claims: Vec::new(),
                allowance_refusals: Vec::new(),
                unsupported_hooks: Vec::new(),
                short_circuit_readings: Vec::new(),
                passed_stops: passed_stops_in_order(self.passed_stops),
                state_matches: self.matcher.map(StateMatcher::finish),
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
    /// apply, an alternative refuted to bottom, a group the sequential step does not follow. Its
    /// path facts are not dropped with its diagnostics (`crate::path_facts`): the marks of open
    /// values the step noted outside a candidate's own right-hand side are on the state's path,
    /// every successor's, and every mark of the run is on its list
    /// (`ExecutionResult::implementation_chosen_values`). A
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
        self.probe_seed();
        while let Some(state) = self.pending.pop_front() {
            // A refused stop condition ends the run: the request has no result.
            if self.refusal.is_some() {
                break;
            }
            // What the state's expansion leaves, for the probe (`probe`, "One path").
            let depth = state.depth;
            let leaves_from = self.leaves.len();
            self.expansion_leaves = leaves_from;
            // The work budget: a run that has visited `max_work` states ends at the next one,
            // which is reported unvisited; the other pending states are dropped (`work`).
            if !self.work.visit() {
                self.leaves
                    .push(state.leaf(HaltReason::WorkBound, &self.observation_log));
                self.pending.clear();
                self.probe_paths(depth, leaves_from, 0);
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
                    if self.refusal.is_some() {
                        break;
                    }
                    self.probe_paths(depth, leaves_from, successors.len());
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
                    self.leaves.push(*leaf);
                    self.probe_paths(depth, leaves_from, 0);
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
            (state.stops, state.arrivals),
            state.pattern.clone(),
            state.effects.clone(),
            state.io.clone(),
            state.io_enabled,
            state.diagnostics.clone(),
        );
        if let Some(mark) = merge.absorbs(&mut arrival, self.fresh_counter.request()) {
            measure::bump(Counter::ExecutionStatesMerged);
            self.merged_arrival = true;
            if let Some(matcher) = &mut self.matcher {
                matcher.absorbed(mark, state.depth, &state.pattern, &state.diagnostics);
            }
            return true;
        }
        self.arrival = Some(arrival);
        false
    }

    /// Match a reached, normalized state against the target of
    /// [`ExecutionOptions::match_states`] (`state_match`), when the run asks for it; returns what
    /// the merge table keeps of the verdict.
    fn match_state(&mut self, state: &ExecutionState) -> MatchMark {
        match &mut self.matcher {
            Some(matcher) => matcher.observe(
                self.definition,
                state.depth,
                &state.pattern,
                &state.diagnostics,
            ),
            None => MatchMark::Other,
        }
    }

    /// Report a successor whose own normalization showed it defined: the rule of its step is
    /// committed ([`crate::coverage::note_committed`]), and what its instance bound is recorded
    /// ([`crate::coverage::note_bindings`], read by the step into its producer). The rule is the
    /// path's last rewrite entry, the one at the state's depth, which every trace keeps
    /// (`commit_applied`); an initial state and a remainder were built by no rule of this depth.
    fn note_committed(state: &ExecutionState) {
        let binding = crate::coverage::records_bindings();
        if !(crate::coverage::committing() || binding)
            || state.is_initial_input
            || !matches!(state.kind, ExecutionStateKind::Rewritable)
        {
            return;
        }
        if let Some(entry) = state.trace.last_rewrite()
            && entry.depth == state.depth
        {
            crate::coverage::note_committed(&entry.unique_id);
            if binding
                && let Some(fired) = state
                    .producer
                    .as_ref()
                    .and_then(|producer| producer.bindings.0.as_deref())
            {
                debug_assert_eq!(producer_rule_id(state), Some(entry.unique_id.as_str()));
                crate::coverage::note_bindings(&entry.unique_id, fired);
            }
        }
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
            return Err(Box::new(state.leaf(
                HaltReason::Indeterminate(IndeterminateReason::SurvivingMacroOrAlias { symbol }),
                &self.observation_log,
            )));
        }
        // A successor whose normalization shows its step undefined everywhere another candidate
        // of the step is defined vanishes: those instances are on the other candidates' paths.
        //
        // A successor's normalization is the work of the rule that produced it: a contradicted
        // claim it observes names that rule (`crate::path_facts`).
        let producer_rule = state
            .producer
            .as_ref()
            .map(|producer| producer.rule.clone());
        // One normalization in two phases: what a record the term phase observes rests on is
        // asked from the constraints' phase on (`crate::path_facts::observed_from`).
        let normalization = crate::path_facts::marker();
        let Some((state, deferred_initial_vacuity)) = crate::path_facts::observed_by(
            || producer_rule.clone(),
            || self.normalise_constraints(state),
        )?
        else {
            return Ok(Vec::new());
        };
        let Some(state) = crate::path_facts::observed_from(
            normalization,
            || producer_rule,
            || self.simplify_term(state, deferred_initial_vacuity.is_some()),
        )?
        else {
            return Ok(Vec::new());
        };
        if self.merged(&state) {
            return Ok(Vec::new());
        }
        if let ExecutionStateKind::Rewritable = state.kind {
            let mark = self.match_state(&state);
            if let Some(arrival) = &mut self.arrival {
                arrival.mark = mark;
            }
        }
        let state = self.watch_cycle(state)?;
        // A `Finished` or `Branch` step attributes its diagnostics to its candidates; any other
        // result halts the state, whose leaf takes the step's whole collection.
        //
        // Path facts (`crate::path_facts`) the step noted outside a candidate's own right-hand
        // side are on this state's path whatever the step's answer: they include the attempts
        // that did not apply, the alternatives refuted to bottom and the groups not followed,
        // on which every successor's existence rests. A candidate's own facts travel with its
        // diagnostics (`apply.rs`).
        let ((rewritten, step_diagnostics), step_facts) = crate::path_facts::collect(|| {
            diagnostic::collect(|| match &state.kind {
                ExecutionStateKind::Rewritable => self.step(&state),
                ExecutionStateKind::Remaining(None) => stuck(self.definition, &state.pattern),
                ExecutionStateKind::Remaining(Some(undecided)) => {
                    Ok(undecided.clone().into_result(state.pattern.clone()))
                }
            })
        });
        let mut state = state;
        state
            .diagnostics
            .extend(&crate::path_facts::diagnostics(&step_facts.shared));
        // A leaf the step ends, or a stop cuts off, takes the candidates' own facts too.
        let owned_step_facts = crate::path_facts::diagnostics(&step_facts.owned);
        let leaves_from = self.leaves.len();
        // A stopped step has no successor set: the state is the leaf, with the step's work.
        let rewritten = match rewritten {
            Ok(rewritten) => rewritten,
            Err(stop) => {
                if self.may_halt_on_successor_count() {
                    state.diagnostics.extend(&owned_step_facts);
                }
                return Err(interrupted_with(
                    Box::new(self.stopped_leaf(state, stop)),
                    &[&step_diagnostics, &owned_step_facts],
                ));
            }
        };
        // Where a halt rests on how many candidates survive, every candidate's own work decides
        // what becomes of each other: whether this state branches, or its one successor is a
        // cut point or terminal (`halts_on_successor_count`). Its facts are then this state's.
        let halts_on_successor_count = self.halts_on_successor_count(&rewritten);
        if halts_on_successor_count {
            state.diagnostics.extend(&owned_step_facts);
        }
        // The step answered, whatever its answer: the state is expanded (`Work::expand`). A stop
        // inside the step returned above without an answer; a remainder takes no step.
        if let ExecutionStateKind::Rewritable = state.kind {
            self.work.expand();
        }
        let mut state = match self.check_interrupted(state) {
            Ok(state) => state,
            Err(leaf) => {
                return Err(interrupted_with(
                    leaf,
                    &[&step_diagnostics, &owned_step_facts],
                ));
            }
        };
        match rewritten {
            RewriteResult::Stuck(_)
            | RewriteResult::Trivial(_, _)
            | RewriteResult::Vacuous(_)
            | RewriteResult::Indeterminate { .. }
            | RewriteResult::Simplification { .. } => {
                state.diagnostics.extend(&step_diagnostics);
                state.diagnostics.extend(&owned_step_facts);
                Err(Box::new(self.halt_leaf(
                    state,
                    rewritten,
                    deferred_initial_vacuity,
                )))
            }
            RewriteResult::Finished(applied) => {
                let (expanded, diagnostics) = crate::path_facts::collect_with_diagnostics(|| {
                    self.finished(state, applied, &Exclusion::default())
                });
                let expanded = expanded.map_err(|leaf| {
                    interrupted_with(leaf, &[&step_diagnostics, &owned_step_facts, &diagnostics])
                });
                if halts_on_successor_count {
                    self.spread_facts(expanded, &diagnostics, leaves_from)
                } else {
                    expanded
                }
            }
            RewriteResult::Branch {
                original,
                branches,
                remainder,
                trivial,
            } => {
                let (expanded, diagnostics) = crate::path_facts::collect_with_diagnostics(|| {
                    self.branch(state, original, branches, remainder, trivial)
                });
                let expanded = expanded.map_err(|leaf| {
                    interrupted_with(leaf, &[&step_diagnostics, &owned_step_facts, &diagnostics])
                });
                if halts_on_successor_count {
                    self.spread_facts(expanded, &diagnostics, leaves_from)
                } else {
                    expanded
                }
            }
        }
    }

    /// Whether the request's options let a state's halt rest on how many of its step's
    /// candidates survive: under `StopAtBranch` a state with one surviving candidate goes on and
    /// one with several is a `Branch` leaf, and a cut-point or terminal rule stops a run only as
    /// the state's one successor.
    fn may_halt_on_successor_count(&self) -> bool {
        self.options.branch_mode == ExecutionBranchMode::StopAtBranch
            || !self.options.cut_point_rules.is_empty()
            || !self.options.terminal_rules.is_empty()
    }

    /// Whether the halt of the state whose step answered `rewritten` can rest on how many of the
    /// step's candidates survive ([`Self::may_halt_on_successor_count`]). A candidate's survival
    /// rests on its own right-hand side and normalization, so there every candidate's work is on
    /// the path of whatever the state becomes.
    ///
    /// Without `StopAtBranch`, only a cut-point or terminal rule makes the count matter, as the
    /// one survivor. Under strategy all the step tries every candidate of every priority group it
    /// visits, and lists each that applied, defined (`Finished`, `Branch::branches`) or not
    /// (`Branch::trivial`); which groups it visits, and which candidates apply, rests on the
    /// matching and conditions, whose work is on the state's path anyway. A state none of whose
    /// listed candidates is a selected stop rule cannot halt by one, whatever survives, so its
    /// candidates' facts stay on their own paths. The sequential step does not try a candidate
    /// whose instances an earlier one took, and in another model the earlier one may be
    /// undefined there: under strategy any every state keeps the rule above. A result that halts
    /// the state gives its leaf every fact of the step anyway.
    fn halts_on_successor_count(&self, rewritten: &RewriteResult) -> bool {
        if !self.may_halt_on_successor_count() {
            return false;
        }
        if self.options.branch_mode == ExecutionBranchMode::StopAtBranch
            || self.options.mode == ExecutionMode::Any
        {
            return true;
        }
        let stop_rule = |label: &Option<String>, unique_id: &String| {
            [&self.options.cut_point_rules, &self.options.terminal_rules]
                .into_iter()
                .any(|selected| {
                    label.as_ref().is_some_and(|label| selected.contains(label))
                        || selected.contains(unique_id)
                })
        };
        match rewritten {
            RewriteResult::Finished(applied) => stop_rule(&applied.label, &applied.unique_id),
            RewriteResult::Branch {
                branches, trivial, ..
            } => {
                branches
                    .iter()
                    .any(|applied| stop_rule(&applied.label, &applied.unique_id))
                    || trivial
                        .iter()
                        .any(|entry| stop_rule(&entry.label, &entry.rule_id))
            }
            RewriteResult::Stuck(_)
            | RewriteResult::Trivial(_, _)
            | RewriteResult::Vacuous(_)
            | RewriteResult::Indeterminate { .. }
            | RewriteResult::Simplification { .. } => true,
        }
    }

    /// Under [`Self::halts_on_successor_count`], give the path facts among `phase_diagnostics`,
    /// those of the phase that derived what `expanded` holds from a state's step (its candidates'
    /// normalizations and their stop rules), to all of it: the leaves the phase pushed from
    /// `leaves_from` on, the successors, and the leaf it ended the state with. Which of them
    /// exist rests on every candidate's normalization.
    fn spread_facts(
        &mut self,
        expanded: Phase<Vec<ExecutionState>>,
        phase_diagnostics: &[BackendDiagnostic],
        leaves_from: usize,
    ) -> Phase<Vec<ExecutionState>> {
        let facts = phase_diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.is_path_fact())
            .cloned()
            .collect::<Vec<_>>();
        if facts.is_empty() {
            return expanded;
        }
        for leaf in &mut self.leaves[leaves_from..] {
            extend_distinct(&mut leaf.diagnostics, &facts);
        }
        match expanded {
            Ok(mut successors) => {
                for successor in &mut successors {
                    successor.diagnostics.extend(&facts);
                }
                Ok(successors)
            }
            Err(mut leaf) => {
                extend_distinct(&mut leaf.diagnostics, &facts);
                Err(leaf)
            }
        }
    }

    /// Poll for a stop between two phases of the state's expansion: a cancelled request, a
    /// failed solver prelude, or the step's passed deadline turns the state into a `Stopped`
    /// leaf ([`Self::stopped_leaf`]).
    fn check_interrupted(&self, state: ExecutionState) -> Phase<ExecutionState> {
        match stop::check() {
            Ok(()) => Ok(state),
            Err(stop) => Err(Box::new(self.stopped_leaf(state, stop))),
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
            None => crate::path_facts::collect_with_diagnostics(|| {
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
            Err(stop) => return Err(Box::new(self.stopped_leaf(state, stop))),
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
                return Err(Box::new(
                    state.leaf(HaltReason::Simplification(error), &self.observation_log),
                ));
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
                    return self
                        .report_undefined_successor(state, halt_reason)
                        .map(|()| None);
                }
                // A successor that denotes no state is no successor of its step, however its
                // constraints became `\bottom`: the step is undefined on the instances no other
                // candidate takes to a defined successor. Only a pre-step state that itself has
                // no instance gives a `Vacuous` leaf, at this state's depth.
                if state.producer.is_some() {
                    let undefined = trivial_halt(state.depth, &state.pattern);
                    return self
                        .report_undefined_successor(state, undefined)
                        .map(|()| None);
                }
                return Err(Box::new(state.leaf(halt_reason, &self.observation_log)));
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
            None => crate::path_facts::collect_with_diagnostics(|| {
                let simplified = match io_evaluation.as_mut() {
                    Some(execution) => simplify_in_execution_with_solver(
                        self.definition,
                        &state.pattern.term,
                        &state.pattern.constraints,
                        SimplificationOptions::keep_partial(
                            self.options.max_simplification_iterations,
                        ),
                        self.solver,
                        execution,
                    ),
                    None => simplify_with_solver(
                        self.definition,
                        &state.pattern.term,
                        &state.pattern.constraints,
                        SimplificationOptions::keep_partial(
                            self.options.max_simplification_iterations,
                        ),
                        self.solver,
                    ),
                };
                // A successor's normalization is its producing rule's work
                // (`crate::path_facts::observed_by` in `expand`), whose result term is the one
                // the step built.
                if let (Ok(Ok(simplified)), Some(producer)) = (&simplified, &state.producer) {
                    note_undefined_result(
                        &producer.successor.term,
                        &state.pattern.constraints,
                        simplified,
                    );
                }
                simplified
            }),
        };
        state.diagnostics.extend(&diagnostics);
        let simplified = match simplified {
            Ok(simplified) => simplified,
            Err(stop) => return Err(Box::new(self.stopped_leaf(state, stop))),
        };
        let mut state = self.check_interrupted(state)?;
        let (undefined_term, contradicted_total, found_bottom) = match simplified {
            Ok(simplified) => {
                let found_bottom = simplified.bottom.as_ref().map(|found| found.term.clone());
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
                (undefined_term, contradicted_total, found_bottom)
            }
            Err(error) => {
                return Err(Box::new(
                    state.leaf(HaltReason::Simplification(error), &self.observation_log),
                ));
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
                return Err(Box::new(state.leaf(halt_reason, &self.observation_log)));
            }
            if !vacuity_deferred {
                // The initial configuration is the caller's pattern `t ∧ φ`, which denotes
                // `⌈t⌉ ∧ t ∧ φ`, and nothing has decided its own facts (I7'). A refuted fact
                // means it has no instance, exactly as constraints simplified to `\bottom` do;
                // that holds as well when the caller asserts the facts
                // (`assume_initial_defined`), since asserting a false fact leaves nothing. A
                // successor needs no such decision: its step decided its right-hand side's
                // definedness, and term simplification conjoins its own obligations.
                let (verdict, diagnostics) = crate::path_facts::collect_with_diagnostics(|| {
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
                        return Err(Box::new(state.leaf(halt_reason, &self.observation_log)));
                    }
                    Ok(FactsVerdict::NotRefuted(_)) => {}
                    Err(stop) => return Err(Box::new(self.stopped_leaf(state, stop))),
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
            return self
                .report_undefined_successor(state, halt_reason)
                .map(|()| None);
        }
        // Any other `\bottom` the term simplification conjoined (an equation whose own result is
        // `\bottom`, a refuted equation `ensures`) makes the successor denote no state as well:
        // it is no successor of its step, as above.
        if predicates_truth(&state.pattern.constraints) == Truth::False && state.producer.is_some()
        {
            let undefined = term_phase_undefinedness(None, None, found_bottom, &state.pattern)
                .halt(state.depth);
            return self
                .report_undefined_successor(state, undefined)
                .map(|()| None);
        }
        if let Some(execution) = io_evaluation {
            state.io = execution.commit();
        } else if let Some(io) = normalized_io {
            state.io = io;
        }
        state.io_enabled &= pattern_supports_execution_io(&state.pattern);
        // The successor is normalized and defined: its step is a transition of the run, and an
        // arrival at a stop where it was a stop rule's step the path goes on past
        // ([`ExecutionOptions::stop_count`]).
        Self::note_committed(&state);
        match state.arriving.take() {
            None => {}
            Some(Arriving::Counted) => {
                state.stops += 1;
                state.arrivals += 1;
            }
            Some(Arriving::Asked { event }) => {
                state.arrivals += 1;
                state.stops += u64::from(event);
            }
        }
        // The step's points, now that its successor is shown defined (`probe`).
        let mut state = match state.probing.take() {
            Some(probing) => self.probe_step(state, *probing)?,
            None => state,
        };
        if state.depth >= self.options.max_depth {
            // A state the depth bound stops is reached; it takes no part in merging.
            if let ExecutionStateKind::Rewritable = state.kind {
                self.match_state(&state);
            }
            let pattern = state.pattern.clone();
            return Err(Box::new(externalise_leaf(
                self.definition,
                state,
                pattern,
                HaltReason::DepthBound,
                self.options.max_simplification_iterations,
                self.solver,
                &mut self.observation_log,
                self.observation,
            )));
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
        let (definedness, diagnostics) = crate::path_facts::collect_with_diagnostics(|| {
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
                Err(Box::new(state.leaf(halt_reason, &self.observation_log)))
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
            Ok(InitialDefinedness::Unsupported(error)) => Err(Box::new(
                state.leaf(HaltReason::Simplification(error), &self.observation_log),
            )),
            Err(stop) => Err(Box::new(self.stopped_leaf(state, stop))),
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
            Some(&mut self.refutations),
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
                if let Some(empty) = deferred_initial_vacuity {
                    // The step was taken from a configuration already shown to have no
                    // instance: there is no step to be undefined.
                    let constraint = super::false_constraint(&empty);
                    let depth = state.depth + 1;
                    return self.empty_leaf(ExecutionState { depth, ..state }, empty, constraint);
                }
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

    /// E6: one rule applied. At the arrival the path ends at ([`Self::ends_at_arrival`]), a
    /// cut-point rule ends the state as a `CutPointRule` leaf with the simplified successor and
    /// a terminal rule ends the successor as a `TerminalRule` (or `Trivial`) leaf; otherwise the
    /// successor is returned, an arrival once its normalization shows it defined where a stop
    /// rule took it.
    fn finished(
        &mut self,
        mut state: ExecutionState,
        mut applied: AppliedRule,
        excluded: &Exclusion,
    ) -> Phase<Vec<ExecutionState>> {
        let normalized = match self.shows_stop_successor_defined(&state, &mut applied) {
            Ok(true) => applied.normalized.0.clone(),
            Ok(false) => None,
            Err(stop) => return Err(Box::new(self.stopped_leaf(state, stop))),
        };
        let successor = normalized
            .as_ref()
            .and_then(|normalization| normalization.term.as_ref())
            .map(|term| &term.simplified.term);
        let StopPlan {
            ends_before,
            deferred,
            arriving,
            terminal: terminal_rule,
            undecided,
        } = match self.stop_plan(&state, &applied, successor) {
            Ok(plan) => plan,
            Err(stop) => return Err(Box::new(self.stopped_leaf(state, stop))),
        };
        if let Some((halt, diagnostics)) = undecided {
            return Err(Box::new(self.undecided_siblings(state, halt, &diagnostics)));
        }
        if let Some(rule) = ends_before {
            if let Some(decision) = deferred {
                // The condition answered neither yes nor no at a cut-point rule's arrival: the
                // path ends at the state before the step, which the undefined step stands for
                // some instances of.
                excluded.exclude_from(&mut state.pattern);
                return self.deferred_answer(state, rule, StopSide::Before, decision);
            }
            let producer = Producer::of(&state, &applied);
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
            let (simplified, diagnostics) = crate::path_facts::collect_with_diagnostics(|| {
                crate::path_facts::observed_by(
                    || Some(producer.rule.clone()),
                    || {
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
                    },
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
                    return Err(Box::new(state.leaf_with_pattern(
                        applied.pattern,
                        HaltReason::Simplification(error),
                        &self.observation_log,
                    )));
                }
                // The proposed successor is not normalised: the state is the leaf.
                Err(stop) => return Err(Box::new(self.stopped_leaf(state, stop))),
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
                    &producer.rule,
                    &producer.before.constraints,
                    io,
                    state.depth + 1,
                    &applied.pattern,
                    &mut state.diagnostics,
                ) {
                    Ok(halt_reason) => halt_reason,
                    Err(stop) => return Err(Box::new(self.stopped_leaf(state, stop))),
                };
                // Reported as the successor would be: at its depth, on its observation head.
                let successor = ExecutionState {
                    depth: state.depth + 1,
                    observation: candidate_observation,
                    pattern: applied.pattern,
                    producer: Some(std::rc::Rc::new(producer)),
                    ..state
                };
                return self
                    .report_undefined_successor(successor, halt_reason)
                    .map(|()| Vec::new());
            }
            // The step's undefined step stands for some instances of this state: the leaf stands
            // for the others, the candidate's own.
            excluded.exclude_from(&mut state.pattern);
            return Err(Box::new(self.cut_point_leaf(
                state,
                rule,
                applied,
                candidate_observation,
            )));
        }
        let producer = Producer::of(&state, &applied);
        let probing = self.probing(&state, &applied);
        let mut next = next_state(
            self.definition,
            state,
            applied,
            &mut self.observation_log,
            self.observation,
        );
        next.producer = Some(std::rc::Rc::new(producer));
        next.arriving = arriving;
        next.probing = probing;
        if let Some(rule) = terminal_rule {
            let producer_rule = next.producer.as_ref().map(|producer| producer.rule.clone());
            let (simplified, diagnostics) = crate::path_facts::collect_with_diagnostics(|| {
                crate::path_facts::observed_by(
                    || producer_rule,
                    || {
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
                    },
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
                    return Err(Box::new(
                        next.leaf(HaltReason::Simplification(error), &self.observation_log),
                    ));
                }
                Err(stop) => return Err(Box::new(self.stopped_leaf(next, stop))),
            };
            let mut next = self.check_interrupted(next)?;
            if predicates_truth(&next.pattern.constraints) == Truth::False {
                let producer = next
                    .producer
                    .clone()
                    .expect("the successor's producer is set");
                let halt_reason = match self.bottom_successor_halt(
                    &producer.successor,
                    &producer.rule,
                    &producer.before.constraints,
                    next.io_enabled.then_some(&next.io),
                    next.depth,
                    &next.pattern,
                    &mut next.diagnostics,
                ) {
                    Ok(halt_reason) => halt_reason,
                    Err(stop) => return Err(Box::new(self.stopped_leaf(next, stop))),
                };
                return self
                    .report_undefined_successor(next, halt_reason)
                    .map(|()| Vec::new());
            }
            // The successor is normalized and defined: committed and reached, the path's last
            // arrival.
            return self.terminal_end(next, rule, deferred);
        }
        Ok(vec![next])
    }

    /// The end of a path at a terminal rule `rule`'s arrival, whose successor `next` is
    /// normalized, defined and committed: a `TerminalRule` leaf, its last event; or, where the
    /// stop condition answered `deferred` there, neither yes nor no, that answer's end
    /// ([`Self::deferred_answer`]).
    fn terminal_end(
        &mut self,
        mut next: ExecutionState,
        rule: String,
        deferred: Option<StopDecision>,
    ) -> Phase<Vec<ExecutionState>> {
        Self::note_committed(&next);
        // The step is taken: its points are asked before the path ends at the terminal rule.
        if let Some(probing) = next.probing.take() {
            next = self.probe_step(next, *probing)?;
        }
        if let Some(decision) = deferred {
            return self.deferred_answer(next, rule, StopSide::After, decision);
        }
        self.match_state(&next);
        next.stops += 1;
        next.arrivals += 1;
        Err(Box::new(next.leaf(
            HaltReason::TerminalRule { rule },
            &self.observation_log,
        )))
    }

    /// The points a probe observes of a step by `applied` from `state`, which the path takes:
    /// its before point with the state before the step, and its after point (`probe`). `None`
    /// where the run has no probe still asked, the rule is selected on neither side, or the
    /// step already left a leaf beside this successor (instances of an undefined candidate): the
    /// state splits there, which the probe is told once the expansion ends
    /// ([`Self::probe_paths`]), so no point of either path is asked before it.
    fn probing(&self, state: &ExecutionState, applied: &AppliedRule) -> Option<Box<Probing>> {
        if !self.probing || self.leaves.len() > self.expansion_leaves {
            return None;
        }
        let rules = &self.options.probe_rules;
        let before = selected_stop_rule(applied, &rules.before);
        let after = selected_stop_rule(applied, &rules.after);
        if before.is_none() && after.is_none() {
            return None;
        }
        Some(Box::new(Probing {
            before: before.map(|rule| {
                let before = ExecutionState {
                    producer: None,
                    probing: None,
                    arriving: None,
                    ..state.clone()
                };
                (rule, before)
            }),
            after,
        }))
    }

    /// Ask the probe about the points `probing` of the step that produced `successor`, whose
    /// normalization showed it defined: the before point, then the after point (`probe`). A
    /// `Differs` answer ends the request and a `Done` answer the path, each with a leaf of the
    /// point's observed state; otherwise `successor` goes on.
    ///
    /// Either point exists only because the step's successor is defined, so the leaf carries
    /// the successor's diagnostics, which hold the state's own and every one the step and the
    /// successor's normalization added (a spent simplification budget, a path fact): what the
    /// point rests on. A before point's leaf is otherwise the state before the step. The
    /// successor is reached either way, so it is matched (`state_match`) before the path ends.
    fn probe_step(
        &mut self,
        successor: ExecutionState,
        probing: Probing,
    ) -> Result<ExecutionState, Box<ExecutionLeaf>> {
        if !self.probing {
            return Ok(successor);
        }
        if let Some((rule, before)) = probing.before {
            let decision =
                self.observe(&rule, StopSide::Before, before.depth, &before.pattern.term);
            if let Some(halt) = self.probe_end(rule, StopSide::Before, decision) {
                self.match_reached(&successor);
                let before = ExecutionState {
                    diagnostics: successor.diagnostics,
                    ..before
                };
                return Err(Box::new(before.leaf(halt, &self.observation_log)));
            }
        }
        if let Some(rule) = probing.after {
            let decision = self.observe(
                &rule,
                StopSide::After,
                successor.depth,
                &successor.pattern.term,
            );
            if let Some(halt) = self.probe_end(rule, StopSide::After, decision) {
                self.match_reached(&successor);
                return Err(Box::new(successor.leaf(halt, &self.observation_log)));
            }
        }
        Ok(successor)
    }

    /// Match `successor`, a step's normalized and defined successor at which a probe's answer
    /// ends the path, which takes part in no merging (`state_match`).
    fn match_reached(&mut self, successor: &ExecutionState) {
        if let ExecutionStateKind::Rewritable = successor.kind {
            self.match_state(successor);
        }
    }

    /// Ask the probe about the point of `rule` on `side` whose observed state, at `depth`, has
    /// the term `term`, isolated from the run (`probe::isolated`).
    fn observe(
        &mut self,
        rule: &str,
        side: StopSide,
        depth: u64,
        term: &crate::term::Term,
    ) -> ProbeDecision {
        let Some(probe) = self.probe.as_deref_mut() else {
            unreachable!("only a run with a probe asks one");
        };
        probe::isolated(|| {
            probe.observe(&ProbeArrival {
                rule,
                side,
                state: ProbeState { depth, term },
            })
        })
    }

    /// Compare `state`, reached, normalized and about to take its step, with the states the
    /// probe's path keeps (`probe`, "Cycles"). Where it returns to one, the probe is told, and its
    /// answer, read as at an after point of the rule whose step reached `state`, may end the path
    /// or the request with a leaf of `state`; either way the probe is not told of a return again.
    fn watch_cycle(&mut self, state: ExecutionState) -> Phase<ExecutionState> {
        if !self.probing
            || state.is_initial_input
            || !matches!(state.kind, ExecutionStateKind::Rewritable)
            || !state.pattern.constraints.is_empty()
            || !state.defined_where.is_empty()
            || !state.pattern.term.attributes().variables.is_empty()
        {
            return Ok(state);
        }
        let (Some(watch), Some(probe)) = (self.cycles.as_mut(), self.probe.as_deref_mut()) else {
            return Ok(state);
        };
        let progress = probe::isolated(|| probe.progress());
        let watched = Watched {
            depth: state.depth,
            term: &state.pattern.term,
            stops: (state.stops, state.arrivals),
            effects: &state.effects,
            io: state.io_enabled.then_some(&state.io),
        };
        let Some(first) = watch.returns(&watched, progress) else {
            return Ok(state);
        };
        self.cycles = None;
        // A reached state that is no initial input was reached by a step, which its trace keeps.
        let Some(rule) = state.trace.last_rewrite().map(|entry| {
            entry
                .label
                .clone()
                .unwrap_or_else(|| entry.unique_id.clone())
        }) else {
            return Ok(state);
        };
        let decision = probe::isolated(|| {
            probe.cycled(&ProbeCycle {
                first,
                rule: &rule,
                state: ProbeState {
                    depth: state.depth,
                    term: &state.pattern.term,
                },
            })
        });
        match self.probe_end(rule, StopSide::After, decision) {
            Some(halt) => Err(Box::new(state.leaf(halt, &self.observation_log))),
            None => Ok(state),
        }
    }

    /// The halt a probe's `decision` at the point of `rule` on `side` ends the path with, if
    /// any: `Differs` also ends the request, dropping every pending state, and either ends the
    /// probe's questions.
    fn probe_end(
        &mut self,
        rule: String,
        side: StopSide,
        decision: ProbeDecision,
    ) -> Option<HaltReason> {
        let halt = match decision {
            ProbeDecision::Continue => return None,
            ProbeDecision::Differs(reason) => {
                self.pending.clear();
                HaltReason::ProbeDifference { rule, side, reason }
            }
            ProbeDecision::Done => HaltReason::ProbeDone { rule, side },
        };
        self.probing = false;
        Some(halt)
    }

    /// Before the first expansion, or in place of every expansion (`max_breadth = 0`): what the
    /// seed leaves, for the probe ([`Self::probe_paths`]). Several initial states are several
    /// paths from the start.
    fn probe_seed(&mut self) {
        let pending = self.pending.len();
        self.probe_paths(0, 0, pending);
    }

    /// Tell the probe what the expansion of the state at `depth` left (`probe`, "One path"):
    /// the leaves pushed from `leaves_from` on and `successors` states to expand. More than one
    /// path, or a branch leaf, is a split ([`Probe::branched`]); one leaf is the path's end
    /// ([`Probe::ended`]), unless the probe's own answer made it. Either ends the probe's
    /// questions.
    fn probe_paths(&mut self, depth: u64, leaves_from: usize, successors: usize) {
        if !self.probing {
            return;
        }
        let Some(probe) = self.probe.as_deref_mut() else {
            return;
        };
        let leaves = &self.leaves[leaves_from..];
        match (leaves, successors) {
            ([], 0 | 1) => return,
            ([leaf], 0) if !matches!(leaf.halt_reason, HaltReason::Branch { .. }) => {
                probe::isolated(|| {
                    probe.ended(&ProbeLeaf {
                        halt: &leaf.halt_reason,
                        state: ProbeState {
                            depth: leaf.depth,
                            term: &leaf.pattern.term,
                        },
                    });
                });
            }
            _ => probe::isolated(|| probe.branched(depth)),
        }
        self.probing = false;
    }

    /// Whether a stop event at `state`'s arrival ends the path: it is the path's
    /// `stop_count`th ([`ExecutionOptions::stop_count`]). Without a stop condition every arrival
    /// is an event.
    fn ends_at_arrival(&self, state: &ExecutionState) -> bool {
        state.stops.saturating_add(1) >= self.options.stop_count.get()
    }

    /// Whether the successor of `applied`, its state's one candidate, is shown defined where the
    /// step is by a stop rule under a stop condition, so that the step is an arrival the
    /// condition may be asked about ([`Self::stop_plan`]): by the step's own normalization
    /// ([`AppliedRule::normalized`]), else by normalizing the successor here
    /// ([`normalize_successor`]), which the successor then takes instead of repeating it, so
    /// that the condition costs the run no state visit and no normalization of a successor that
    /// goes on. Any other step asks nothing, and is answered `false`.
    fn shows_stop_successor_defined(
        &self,
        state: &ExecutionState,
        applied: &mut AppliedRule,
    ) -> Stoppable<bool> {
        if self.condition.is_none() || !self.selects_stop(applied) {
            return Ok(false);
        }
        if applied
            .normalized
            .0
            .as_ref()
            .is_some_and(|normalization| normalization.built == applied.pattern)
        {
            return Ok(true);
        }
        let rule = applied.observing_rule();
        let io = applied
            .io
            .as_ref()
            .or(state.io_enabled.then_some(&state.io));
        // A result found `\bottom` is reported, not noted: the successor's own normalization,
        // which goes on as if nothing were asked, notes it.
        let (checked, _) = crate::path_facts::observed_by(
            || Some(rule.clone()),
            || {
                normalize_successor_with(
                    self.definition,
                    &applied.pattern,
                    &applied.before.constraints,
                    SimplificationOptions::keep_partial(self.options.max_simplification_iterations),
                    self.solver,
                    io,
                    ResultClaim::Report,
                )
            },
        )?;
        Ok(match (checked.undefined, checked.normalization) {
            (None, Some(normalization)) => {
                applied.normalized = NormalizedSuccessor(Some(Arc::new(normalization)));
                true
            }
            // Undefined, or not normalized: no arrival, whatever its own normalization finds.
            _ => false,
        })
    }

    /// What a step by `applied` from `state`, its state's one successor, does at the stop rules:
    /// whether it ends the path before the step, is an arrival the path goes on past, or ends
    /// the path after the step ([`ExecutionOptions::stop_count`]).
    ///
    /// Under a stop condition (`stop_condition`) the condition is asked here, once the step is an
    /// arrival: when `successor`, the normalized successor's term, shows the successor defined
    /// ([`Self::shows_stop_successor_defined`]). A cut-point rule's stop state is `state`, a
    /// terminal rule's the normalized successor. A step by a stop rule whose successor is not
    /// shown defined is no arrival, and goes on as a step whose successor's own normalization
    /// ends its path.
    ///
    /// Under strategy any, `applied` is the one successor the sequential step took, not
    /// necessarily its state's one successor: where it is a stop rule's and the state has another
    /// ([`Self::siblings`]), the step is no arrival but a passed stop, which stops nothing, is not
    /// counted and is not asked the condition, and the path goes on through `applied` as through
    /// any other step; where whether it has another is undecided, the path ends at `state`
    /// ([`StopPlan::undecided`]).
    fn stop_plan(
        &mut self,
        state: &ExecutionState,
        applied: &AppliedRule,
        successor: Option<&crate::term::Term>,
    ) -> Result<StopPlan, Stop> {
        if self.options.mode == ExecutionMode::Any && self.selects_stop(applied) {
            match self.siblings(state)? {
                Siblings::None => {}
                Siblings::Another => {
                    self.note_passed_stop(applied, state.depth);
                    return Ok(StopPlan::default());
                }
                Siblings::Undecided(undecided) => {
                    return Ok(StopPlan {
                        undecided: Some(*undecided),
                        ..StopPlan::default()
                    });
                }
            }
        }
        let ends = self.ends_at_arrival(state);
        let cut_point = selected_stop_rule(applied, &self.options.cut_point_rules);
        if self.condition.is_none() {
            return Ok(match cut_point {
                Some(rule) if ends => StopPlan {
                    ends_before: Some(rule),
                    ..StopPlan::default()
                },
                _ => StopPlan {
                    arriving: (!ends && self.selects_stop(applied)).then_some(Arriving::Counted),
                    terminal: ends
                        .then(|| selected_stop_rule(applied, &self.options.terminal_rules))
                        .flatten(),
                    ..StopPlan::default()
                },
            });
        }
        let Some(successor) = successor else {
            return Ok(StopPlan::default());
        };
        let (rule, side, depth, term) = match cut_point {
            Some(rule) => (rule, StopSide::Before, state.depth, &state.pattern.term),
            None => match selected_stop_rule(applied, &self.options.terminal_rules) {
                Some(rule) => (rule, StopSide::After, state.depth + 1, successor),
                None => return Ok(StopPlan::default()),
            },
        };
        let decision = self.ask(&rule, side, depth, term)?;
        let event = match decision {
            StopDecision::Holds if ends => {
                return Ok(match side {
                    StopSide::Before => StopPlan {
                        ends_before: Some(rule),
                        ..StopPlan::default()
                    },
                    StopSide::After => StopPlan {
                        terminal: Some(rule),
                        ..StopPlan::default()
                    },
                });
            }
            StopDecision::Holds => true,
            StopDecision::Fails => false,
            deferred @ (StopDecision::Undecided(_) | StopDecision::Refused(_)) => {
                return Ok(match side {
                    StopSide::Before => StopPlan {
                        ends_before: Some(rule),
                        deferred: Some(deferred),
                        ..StopPlan::default()
                    },
                    StopSide::After => StopPlan {
                        terminal: Some(rule),
                        deferred: Some(deferred),
                        ..StopPlan::default()
                    },
                });
            }
        };
        Ok(StopPlan {
            arriving: Some(Arriving::Asked { event }),
            ..StopPlan::default()
        })
    }

    /// Ask the run's stop condition about the arrival at `rule` on `side` whose stop state, at
    /// `depth`, has the term `term` (`stop_condition::ask`). An undecided answer whose evaluation
    /// met a stop of the request (a cancellation, a failed solver prelude), which stays raised,
    /// is that stop: the arrival is not left undecided by the condition but by the request.
    fn ask(
        &mut self,
        rule: &str,
        side: StopSide,
        depth: u64,
        term: &crate::term::Term,
    ) -> Result<StopDecision, Stop> {
        let Some(condition) = self.condition.as_deref_mut() else {
            unreachable!("only a run with a stop condition asks one");
        };
        let decision = stop_condition::ask(
            condition,
            &StopArrival {
                rule,
                side,
                depth,
                term,
            },
        );
        if matches!(decision, StopDecision::Undecided(_)) {
            stop::check()?;
        }
        Ok(decision)
    }

    /// The end of a path at `state`, where whether a stop rule's step from it is its one
    /// successor is undecided ([`Siblings::Undecided`]): the all-path step's `halt`, with the
    /// diagnostics of its work.
    fn undecided_siblings(
        &mut self,
        mut state: ExecutionState,
        halt: HaltReason,
        diagnostics: &[BackendDiagnostic],
    ) -> ExecutionLeaf {
        state.diagnostics.extend(diagnostics);
        state.leaf(halt, &self.observation_log)
    }

    /// The end of a path at the arrival at `rule` on `side` whose stop state is `state`, where
    /// the step's successor is shown defined and the condition answered `decision`, neither yes
    /// nor no: a `stop-undecided` leaf of `state`, or the request's refusal.
    fn deferred_answer(
        &mut self,
        mut state: ExecutionState,
        rule: String,
        side: StopSide,
        decision: StopDecision,
    ) -> Phase<Vec<ExecutionState>> {
        state.arrivals += 1;
        match decision {
            StopDecision::Undecided(reason) => Err(Box::new(state.leaf(
                HaltReason::StopUndecided { rule, reason },
                &self.observation_log,
            ))),
            StopDecision::Refused(reason) => {
                self.refuse(rule, side, state.depth, reason);
                Ok(Vec::new())
            }
            StopDecision::Holds | StopDecision::Fails => {
                unreachable!("a decided answer is acted on at the step")
            }
        }
    }

    /// The stop condition refused at an arrival: the run ends, with no result.
    fn refuse(&mut self, rule: String, side: StopSide, depth: u64, reason: String) {
        self.refusal.get_or_insert(StopConditionRefusal {
            rule,
            side,
            depth,
            reason,
        });
        self.pending.clear();
    }

    /// Whether `applied` is a step by a rule the cut-point or terminal rules select.
    fn selects_stop(&self, applied: &AppliedRule) -> bool {
        selected_stop_name(applied, &self.options.cut_point_rules).is_some()
            || selected_stop_name(applied, &self.options.terminal_rules).is_some()
    }

    /// Record that the run went on past a step by `applied` from a state at `depth` that is not
    /// its state's one successor, once per selected rule at its shallowest depth
    /// ([`ExecutionResult::passed_stops`]): the record grows with the selected rules, not with
    /// the run.
    fn note_passed_stop(&mut self, applied: &AppliedRule, depth: u64) {
        for selected in [&self.options.cut_point_rules, &self.options.terminal_rules] {
            if let Some(rule) = selected_stop_name(applied, selected) {
                match self.passed_stops.get_mut(rule) {
                    Some(passed) => *passed = (*passed).min(depth),
                    None => {
                        self.passed_stops.insert(rule.to_owned(), depth);
                    }
                }
            }
        }
    }

    /// Under strategy any, whether `state` has a successor besides the one the sequential step
    /// took ([`Self::stop_plan`]).
    ///
    /// The sequential step offers each instance to the rules of a priority in turn and stops at
    /// the first that gives it a defined result, so it never tries the later rules there: its
    /// answer cannot say whether another rule of that priority applies too. That is a fact of
    /// the definition, not of the strategy, so it is the all-path step's: the state's successors
    /// are that step's candidates whose successors are not shown undefined, with its remainder,
    /// as a step under strategy all reads them where a stop rule may select one of several
    /// candidates ([`Self::branch`]), and less those the caller's reading says denote no state
    /// ([`Self::read_stop_step`]). One such successor is the one the sequential step took, and
    /// a step that shows no successor at all (no rule applies, no candidate's result is
    /// defined, or the state has no instance) shows none beside it either. A step that does not
    /// decide the state's successors (`Indeterminate`, `Simplification`) leaves the question
    /// undecided, and the path ends at the state with that step's halt ([`Siblings::Undecided`]):
    /// going on would claim no arrival, and stopping an arrival, neither of which was shown.
    ///
    /// The step is the run's work at a stop rule's step and decides where the path ends, so a
    /// fact it notes (a value the definition leaves open, a contradicted claim) is a fact of
    /// the path, as every candidate's is under strategy all, and the names it mints are the
    /// run's, so no later name of the run repeats one a kept fact may mention; its work is the
    /// run's at that step, on the step's clock and in the run's measures. Otherwise it changes
    /// nothing in the run: it reports to no coverage set, emits no diagnostic unless it ends the
    /// path, and fills no memo the run is later served from.
    fn siblings(&mut self, state: &ExecutionState) -> Stoppable<Siblings> {
        let definition = self.definition;
        let solver = self.solver;
        let reading = self.reading;
        let options =
            SimplificationOptions::keep_partial(self.options.max_simplification_iterations);
        let subject_definedness = if self.options.assume_initial_defined {
            SubjectDefinedness::Assumed
        } else {
            SubjectDefinedness::Where(&state.defined_where)
        };
        let io = state.io_enabled.then_some(&state.io);
        let fresh_counter = &mut self.fresh_counter;
        let ask = || -> Stoppable<Siblings> {
            let rewritten = rewrite_step_with_optional_execution(
                definition,
                &state.pattern,
                fresh_counter,
                options,
                solver,
                ExecutionMode::All,
                subject_definedness,
                io,
                true,
                None,
            )?;
            let (branches, remainder) = match rewritten {
                RewriteResult::Branch {
                    branches,
                    remainder,
                    ..
                } => (branches, remainder),
                RewriteResult::Finished(_)
                | RewriteResult::Stuck(_)
                | RewriteResult::Trivial(_, _)
                | RewriteResult::Vacuous(_) => return Ok(Siblings::None),
                RewriteResult::Indeterminate { reason, .. } => {
                    return Ok(Siblings::Undecided(Box::new((
                        HaltReason::Indeterminate(reason),
                        Vec::new(),
                    ))));
                }
                RewriteResult::Simplification { error, .. } => {
                    return Ok(Siblings::Undecided(Box::new((
                        HaltReason::Simplification(error),
                        Vec::new(),
                    ))));
                }
            };
            let reading = reading.map(|reading| {
                (
                    reading,
                    crate::path_facts::run_left_hook_unsupported(definition.load_record()),
                )
            });
            let rejects = |pattern: &Pattern| {
                reading.is_some_and(|(reading, hooks)| denotes_no_state(reading, pattern, hooks))
            };
            let mut successors = usize::from(
                remainder
                    .as_ref()
                    .is_some_and(|remainder| !rejects(&remainder.pattern)),
            );
            for applied in &branches {
                if rejects(&applied.pattern) {
                    continue;
                }
                let rule = applied.observing_rule();
                let checked = crate::path_facts::observed_by(
                    || Some(rule.clone()),
                    || {
                        normalize_successor(
                            definition,
                            &applied.pattern,
                            &applied.before.constraints,
                            options,
                            solver,
                            applied.io.as_ref().or(io),
                        )
                    },
                )?;
                if checked.undefined.is_none() {
                    successors += 1;
                    if successors > 1 {
                        return Ok(Siblings::Another);
                    }
                }
            }
            Ok(Siblings::None)
        };
        let (siblings, diagnostics) = crate::coverage::suspend(|| {
            crate::diagnostic::discarded(|| {
                crate::diagnostic::collect(|| {
                    crate::rule::with_apart_names_restored(|| {
                        crate::deferred::hook_values_aside(|| {
                            crate::simplify::unspecified_values_aside(|| {
                                crate::simplify::condition_memo_aside(|| {
                                    crate::simplify::normal_forms::aside(ask)
                                })
                            })
                        })
                    })
                })
            })
        });
        Ok(match siblings? {
            Siblings::Undecided(undecided) => {
                Siblings::Undecided(Box::new((undecided.0, diagnostics)))
            }
            siblings => siblings,
        })
    }

    /// Under a caller's reading ([`SuccessorReading`]), a step that holds a selected stop rule's
    /// candidate without the candidates, and the remainder, the reading says denote no state:
    /// they are no successors of the step, so a stop rule's candidate left alone is its state's
    /// one successor (`stop_condition`, "Successors read by the caller"). A dropped candidate's
    /// transition is rolled back, as an undefined one's is. The step is returned as built where
    /// there is no reading, no selected stop rule's candidate, nothing the reading drops, or
    /// nothing it keeps: a reading that leaves the step no successor contradicts the step.
    fn read_stop_step(
        &mut self,
        branches: Vec<AppliedRule>,
        remainder: Option<RemainderBranch>,
    ) -> (Vec<AppliedRule>, Option<RemainderBranch>) {
        let Some(reading) = self.reading else {
            return (branches, remainder);
        };
        if !branches.iter().any(|applied| self.selects_stop(applied)) {
            return (branches, remainder);
        }
        let hooks = crate::path_facts::run_left_hook_unsupported(self.definition.load_record());
        let kept = branches
            .iter()
            .map(|applied| !denotes_no_state(reading, &applied.pattern, hooks))
            .collect::<Vec<_>>();
        let remainder_kept = remainder
            .as_ref()
            .is_some_and(|remainder| !denotes_no_state(reading, &remainder.pattern, hooks));
        let all = kept.iter().all(|kept| *kept) && remainder_kept == remainder.is_some();
        let none = !kept.iter().any(|kept| *kept) && !remainder_kept;
        if all || none {
            return (branches, remainder);
        }
        let mut survivors = Vec::with_capacity(branches.len());
        for (applied, kept) in branches.into_iter().zip(kept) {
            if kept {
                survivors.push(applied);
            } else {
                self.roll_back(
                    &applied.unique_id,
                    &applied.label,
                    &applied.pattern,
                    &applied.effects,
                );
            }
        }
        (survivors, remainder.filter(|_| remainder_kept))
    }

    /// The `CutPointRule` leaf for a proposed successor that is normalized, on its own
    /// observation head `candidate`, and not bottom, once its effects are committed to `state`.
    /// The leaf is this state: it keeps this state's depth, branch and diagnostics; the
    /// successor, carried in `next_states`, owns its diagnostics and the events it would add to
    /// this branch. Its step is the path's last arrival, which the leaf counts.
    fn cut_point_leaf(
        &self,
        mut state: ExecutionState,
        rule: String,
        mut applied: AppliedRule,
        candidate: ObservationHead,
    ) -> ExecutionLeaf {
        applied.observations = self
            .observation_log
            .events_since(candidate, state.observation);
        state.stops += 1;
        state.arrivals += 1;
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
        remainder: Option<RemainderBranch>,
        trivial: Vec<TrivialApplication>,
    ) -> Phase<Vec<ExecutionState>> {
        record_trivial_candidates(&mut self.discarded, &trivial, &original, self.observation);
        let (branches, mut remainder) = self.read_stop_step(branches, remainder);
        // The instances the step itself left without a defined successor (its trivial entries)
        // are parts of its undefined step, with those of the candidates whose successors
        // normalize to `\bottom`: the step has one `Trivial` leaf, standing for every instance on
        // which a candidate applies and every candidate that applies is undefined.
        let depth = state.depth + 1;
        let mut parts = Vec::new();
        for (index, entry) in trivial.iter().enumerate() {
            match self.entry_part(index, entry, depth) {
                Ok(Some(part)) => parts.push(part),
                Ok(None) => {}
                Err(stop) => return Err(Box::new(self.stopped_leaf(state, stop))),
            }
        }
        let offset = trivial.len();
        let single = branches.len() == 1 && remainder.is_none();
        let stopping = self.options.branch_mode == ExecutionBranchMode::StopAtBranch;
        // Whether a stop rule may select one of several candidates, which then stops the run
        // only if it is the step's one successor.
        let stop_rule_selects = !single
            && remainder.is_none()
            && branches.iter().any(|applied| {
                selected_stop_name(applied, &self.options.cut_point_rules).is_some()
                    || selected_stop_name(applied, &self.options.terminal_rules).is_some()
            });
        let entries_decide = !trivial.is_empty()
            && (!parts.is_empty() || (branches.is_empty() && remainder.is_none()));
        if !stopping && (entries_decide || stop_rule_selects) || single && entries_decide {
            // What the step does next rests on which candidates are undefined: the undefined
            // step it reports beside its trivial entries, or whether a stop rule's candidate is
            // its one successor. Each candidate's successor is normalized here, and a defined
            // one's successor takes that normalization instead of repeating it.
            let defined = match self.normalize_candidates(&state, branches, offset, &mut parts) {
                Ok(defined) => defined,
                Err(stop) => return Err(Box::new(self.stopped_leaf(state, stop))),
            };
            let parent = state.clone();
            return self.conclude_step(
                state,
                &parent,
                original,
                parts,
                Survivors::Normalized(defined),
                remainder,
                offset,
            );
        }
        if single {
            // The only candidate is the unique successor of this state, whatever the branch
            // mode: the step is no branch point, and it goes on exactly as a `Finished` step
            // does, the stop rules included. Its successor is normalised by its own expansion,
            // where a `\bottom` makes it this step's undefined step rather than leaving this
            // state stuck.
            let applied = branches.into_iter().next().expect("one branch remains");
            return self.finished(state, applied, &Exclusion::default());
        }
        if self.options.branch_mode == ExecutionBranchMode::StopAtBranch {
            // The configuration the step was taken from, on its path: the leaf of a candidate
            // whose normalization shows it undefined.
            let parent = state.clone();
            // The branch leaf is the parent state: its diagnostics are the parent path's and its
            // pattern's simplification; each candidate it reports carries its own.
            let (simplified_original, diagnostics) =
                crate::path_facts::collect_with_diagnostics(|| {
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
                    return Err(Box::new(state.leaf_with_pattern(
                        original,
                        HaltReason::Simplification(error),
                        &self.observation_log,
                    )));
                }
                Err(stop) => return Err(Box::new(self.stopped_leaf(state, stop))),
            };
            if predicates_truth(&original.constraints) == Truth::False {
                // The configuration has no instance, which the step exposed.
                let constraint = super::false_constraint(&original);
                let empty = ExecutionState { depth, ..state };
                return Err(Box::new(self.empty_leaf(empty, original, constraint)));
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
            for (candidate, mut applied) in branches.into_iter().enumerate() {
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
                let rule = applied.observing_rule();
                let (simplified, diagnostics) = crate::path_facts::collect_with_diagnostics(|| {
                    crate::path_facts::observed_by(
                        || Some(rule.clone()),
                        || {
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
                        },
                    )
                });
                extend_distinct(&mut applied.diagnostics, &diagnostics);
                match simplified {
                    Ok(Ok(simplified)) => {
                        applied.pattern = simplified.pattern;
                        applied.effects.extend(simplified.effects);
                        if predicates_truth(&applied.pattern.constraints) != Truth::False {
                            simplified_branches.push((applied, observation, built));
                            continue;
                        }
                        // A candidate normalized to `\bottom` is no successor, however the
                        // `\bottom` was found: an undefined step of this state where no defined
                        // candidate applies, reported below once every candidate is known.
                        let io = applied
                            .io
                            .as_ref()
                            .or(state.io_enabled.then_some(&state.io));
                        let (undefined, work) = crate::path_facts::collect_with_diagnostics(|| {
                            crate::path_facts::observed_by(
                                || Some(rule),
                                || {
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
                                },
                            )
                        });
                        extend_distinct(&mut applied.diagnostics, &work);
                        let undefined = match undefined {
                            Ok(Some(undefined)) => undefined,
                            // The successor's own normalization did not finish, or did not
                            // reach `\bottom`; this one did, so the obligation named is its
                            // false constraint.
                            Ok(None) => UndefinedSuccessor {
                                obligation: super::false_constraint(&applied.pattern),
                                contradicted_total: None,
                            },
                            Err(stop) => return Err(Box::new(self.stopped_leaf(state, stop))),
                        };
                        self.roll_back(
                            &applied.unique_id,
                            &applied.label,
                            &built,
                            &applied.effects,
                        );
                        parts.push(UndefinedPart::candidate(
                            offset + candidate,
                            &applied.before,
                            &built,
                            &applied.unique_id,
                            &applied.label,
                            applied.observing_rule(),
                            undefined.halt(depth),
                            applied.diagnostics.to_vec(),
                            applied.remainder_simplifications,
                        ));
                    }
                    Ok(Err(error)) => {
                        // The failure is reported on the parent's leaf, with the diagnostics of
                        // the work on the candidate that failed.
                        state.diagnostics.extend(&applied.diagnostics);
                        failed_branch = Some(error);
                        break;
                    }
                    // A candidate is not normalised: the state is the leaf.
                    Err(stop) => return Err(Box::new(self.stopped_leaf(state, stop))),
                }
            }
            if let Some(error) = failed_branch {
                let state = self.check_interrupted(state)?;
                return Err(Box::new(state.leaf_with_pattern(
                    original,
                    HaltReason::Simplification(error),
                    &self.observation_log,
                )));
            }
            let branches = simplified_branches;
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
                let (simplified, diagnostics) = crate::path_facts::collect_with_diagnostics(|| {
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
                        return Err(Box::new(state.leaf_with_pattern(
                            original,
                            HaltReason::Simplification(error),
                            &self.observation_log,
                        )));
                    }
                    // The remainder is not normalised: the state is the leaf.
                    Err(stop) => return Err(Box::new(self.stopped_leaf(state, stop))),
                };
                if predicates_truth(&candidate.pattern.constraints) == Truth::False {
                    remainder = None;
                }
            }
            let state = self.check_interrupted(state)?;
            return self.conclude_step(
                state,
                &parent,
                original,
                parts,
                Survivors::Simplified(branches, remainder_observation_head),
                remainder,
                offset,
            );
        }
        Ok(self.successors(state, branches, remainder, offset))
    }

    /// The successors of a step exploring all paths: one per applied candidate, each knowing the
    /// others for its undefined step ([`Self::successor_step`]), and the remainder's.
    fn successors(
        &mut self,
        state: ExecutionState,
        branches: Vec<AppliedRule>,
        remainder: Option<RemainderBranch>,
        offset: usize,
    ) -> Vec<ExecutionState> {
        // The step goes on through every successor, and it is no lone candidate without a
        // remainder (such a step goes on as `finished`), so a candidate of a selected stop rule
        // among them has another successor beside it and is not its state's one successor: the
        // run passes that stop.
        for applied in &branches {
            self.note_passed_stop(applied, state.depth);
        }
        let mut next = Vec::with_capacity(branches.len() + usize::from(remainder.is_some()));
        let candidates = branches
            .iter()
            .enumerate()
            .map(|(index, applied)| Sibling::of(offset + index, applied))
            .collect::<Vec<_>>();
        let reported = std::rc::Rc::new(std::cell::Cell::new(false));
        for (index, applied) in branches.into_iter().enumerate() {
            let siblings = candidates
                .iter()
                .filter(|sibling| sibling.index != offset + index)
                .cloned()
                .collect();
            let producer = Producer::of_step(
                &state,
                &applied,
                offset + index,
                siblings,
                remainder.is_some(),
                reported.clone(),
            );
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
        next
    }

    /// Normalize each candidate's successor within the step: an undefined one becomes a part of
    /// the step's undefined step (`parts`), with its transition rolled back; a defined one is
    /// returned, carrying its normalization, which its successor takes instead of repeating it.
    fn normalize_candidates(
        &mut self,
        state: &ExecutionState,
        branches: Vec<AppliedRule>,
        offset: usize,
        parts: &mut Vec<UndefinedPart>,
    ) -> Stoppable<Vec<AppliedRule>> {
        let depth = state.depth + 1;
        let mut defined = Vec::with_capacity(branches.len());
        for (candidate, mut applied) in branches.into_iter().enumerate() {
            let rule = applied.observing_rule();
            let io = applied
                .io
                .as_ref()
                .or(state.io_enabled.then_some(&state.io));
            let checked = crate::path_facts::observed_by(
                || Some(rule.clone()),
                || {
                    normalize_successor(
                        self.definition,
                        &applied.pattern,
                        &applied.before.constraints,
                        SimplificationOptions::keep_partial(
                            self.options.max_simplification_iterations,
                        ),
                        self.solver,
                        io,
                    )
                },
            )?;
            match checked.undefined {
                Some(undefined) => {
                    let mut work = applied.diagnostics.to_vec();
                    if let Some(normalization) = &checked.normalization {
                        extend_distinct(&mut work, &normalization.diagnostics());
                    }
                    self.roll_back(
                        &applied.unique_id,
                        &applied.label,
                        &applied.pattern,
                        &applied.effects,
                    );
                    parts.push(UndefinedPart::candidate(
                        offset + candidate,
                        &applied.before,
                        &applied.pattern,
                        &applied.unique_id,
                        &applied.label,
                        rule,
                        undefined.halt(depth),
                        work,
                        applied.remainder_simplifications.clone(),
                    ));
                }
                None => {
                    applied.normalized = NormalizedSuccessor(checked.normalization.map(Arc::new));
                    defined.push(applied);
                }
            }
        }
        Ok(defined)
    }

    /// What a step does once each of its candidates is known defined or undefined: every
    /// decision that rests on its successor set is taken here, on the defined candidates
    /// (`survivors`) and the remainder only. A candidate whose successor is `\bottom` is no
    /// successor.
    ///
    /// The undefined step of `parts` is reported first ([`Self::undefined_step`]); a step with
    /// no instance is one `Vacuous` leaf. Then: no survivor and no remainder ends the state, as
    /// `Stuck` only when no candidate applied; one survivor and no remainder is the state's one
    /// successor, to which the cut-point and terminal rules apply; otherwise the state
    /// branches, as successors when exploring all paths, or as a `Branch` leaf when stopping at
    /// branches. A cut-point or `Branch` leaf, which is the configuration the step was taken
    /// from, excludes the undefined step's instances ([`Exclusion`], built from the instances
    /// each undefined part stands for, whatever its term), so the step's leaves partition its
    /// instances. `parent` is the state as the step was taken from it.
    #[allow(clippy::too_many_arguments)]
    fn conclude_step(
        &mut self,
        state: ExecutionState,
        parent: &ExecutionState,
        original: Pattern,
        parts: Vec<UndefinedPart>,
        survivors: Survivors,
        mut remainder: Option<RemainderBranch>,
        offset: usize,
    ) -> Phase<Vec<ExecutionState>> {
        let depth = state.depth + 1;
        let undefined = !parts.is_empty();
        let built = survivors.built();
        // The undefined step's instances, which the step's other leaves exclude.
        let mut excluded = Exclusion::default();
        if undefined {
            let others = !built.is_empty() || remainder.is_some();
            match self.undefined_step(
                parent,
                parent.diagnostics.clone(),
                parts,
                &built.iter().collect::<Vec<_>>(),
                others,
            ) {
                Ok(UndefinedStep::Leaves(leaves, parts)) => {
                    excluded = parts;
                    self.leaves.extend(leaves);
                }
                Ok(UndefinedStep::Covered) => {}
                Ok(UndefinedStep::NoInstance) => {
                    let constraint = super::false_constraint(&original);
                    let empty = ExecutionState { depth, ..state };
                    return Err(Box::new(self.empty_leaf(empty, original, constraint)));
                }
                Err(stop) => return Err(Box::new(self.stopped_leaf(state, stop))),
            }
        }
        match survivors {
            Survivors::Normalized(mut defined) => match (defined.len(), remainder.is_some()) {
                (0, false) if undefined => Ok(Vec::new()),
                (0, false) => Err(Box::new(state.leaf_with_pattern(
                    original,
                    HaltReason::Stuck,
                    &self.observation_log,
                ))),
                (1, false) => {
                    let applied = defined.pop().expect("one defined candidate");
                    self.finished(state, applied, &excluded)
                }
                _ => Ok(self.successors(state, defined, remainder, offset)),
            },
            Survivors::Simplified(mut branches, remainder_observation_head) => {
                match (branches.len(), remainder.is_some()) {
                    // Every instance of the state is on the undefined step's leaf.
                    (0, false) if undefined => Ok(Vec::new()),
                    (0, false) => Err(Box::new(state.leaf_with_pattern(
                        original,
                        HaltReason::Stuck,
                        &self.observation_log,
                    ))),
                    (1, false) => {
                        // The only surviving candidate is the unique successor of this state,
                        // as a `Finished` step's application is: the stop rules apply to it
                        // alike. It is already normalized, on its own head, and not bottom.
                        let (applied, observation, _) = branches.pop().expect("one branch remains");
                        let plan =
                            match self.stop_plan(&state, &applied, Some(&applied.pattern.term)) {
                                Ok(plan) => plan,
                                Err(stop) => return Err(Box::new(self.stopped_leaf(state, stop))),
                            };
                        if let Some((halt, diagnostics)) = plan.undecided {
                            return Err(Box::new(self.undecided_siblings(
                                state,
                                halt,
                                &diagnostics,
                            )));
                        }
                        if let Some(rule) = plan.ends_before {
                            let mut state = state;
                            // The undefined step stands for some instances of this state: the
                            // leaf stands for the others, the candidate's own.
                            excluded.exclude_from(&mut state.pattern);
                            if let Some(decision) = plan.deferred {
                                return self.deferred_answer(
                                    state,
                                    rule,
                                    StopSide::Before,
                                    decision,
                                );
                            }
                            commit_proposed_effects(&mut state, &applied);
                            return Err(Box::new(self.cut_point_leaf(
                                state,
                                rule,
                                applied,
                                observation,
                            )));
                        }
                        let probing = self.probing(&state, &applied);
                        let mut next = commit_applied(state, applied, observation);
                        next.arriving = plan.arriving;
                        next.probing = probing;
                        if let Some(rule) = plan.terminal {
                            // Normalized within the step and not bottom: committed and reached,
                            // the path's last arrival.
                            return self.terminal_end(next, rule, plan.deferred);
                        }
                        Ok(vec![next])
                    }
                    (0, true) => {
                        let remainder = remainder.take().expect("one remainder remains");
                        Ok(vec![commit_remainder(
                            state,
                            remainder,
                            remainder_observation_head,
                        )])
                    }
                    _ => {
                        // The reported candidates are not committed: each carries the events it
                        // would add to the parent's branch.
                        let branches = branches
                            .into_iter()
                            .map(|(mut applied, observation, _)| {
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
                        // The branch leaf stands for the instances the step does not leave
                        // undefined.
                        let mut original = original;
                        excluded.exclude_from(&mut original);
                        Err(Box::new(state.leaf_with_pattern(
                            original,
                            HaltReason::Branch {
                                branches,
                                remainder,
                            },
                            &self.observation_log,
                        )))
                    }
                }
            }
        }
    }

    /// The `Trivial` halt at `depth` of a step whose successor, `built` as the step built it from
    /// a pattern with the constraints `base`, normalized to `normalized`, whose constraints are `\bottom`: the failing obligation and
    /// the contradicted attribute when [`successor_undefinedness`] shows the successor undefined,
    /// the false constraint of `normalized` otherwise. The deciding work is `diagnostics`'.
    #[allow(clippy::too_many_arguments)]
    fn bottom_successor_halt(
        &self,
        built: &Pattern,
        rule: &crate::path_facts::ObservingRule,
        base: &[Predicate],
        io: Option<&ExecutionIoState>,
        depth: u64,
        normalized: &Pattern,
        diagnostics: &mut PathDiagnostics,
    ) -> Stoppable<HaltReason> {
        let (undefined, work) = crate::path_facts::collect_with_diagnostics(|| {
            crate::path_facts::observed_by(
                || Some(rule.clone()),
                || {
                    successor_undefinedness(
                        self.definition,
                        built,
                        base,
                        SimplificationOptions::keep_partial(
                            self.options.max_simplification_iterations,
                        ),
                        self.solver,
                        io,
                    )
                },
            )
        });
        diagnostics.extend(&work);
        Ok(undefined?.map_or_else(
            || trivial_halt(depth, normalized),
            |undefined| undefined.halt(depth),
        ))
    }

    /// Report `state`, a successor whose normalization showed it undefined (`halt_reason`, at
    /// the successor's depth): it denotes no state, so it is no successor of its step, and its
    /// instances go to the step's undefined step ([`Self::successor_step`]). `Err` carries the
    /// leaf that reports them: the step's `Trivial` leaf, or, when the configuration the step was
    /// taken from has no instance, this state's `Vacuous` leaf, which names no rule. `Ok` when no
    /// leaf is due: another candidate or the remainder takes every instance, or another
    /// successor of the step reported its undefined step. A state with no recorded producer (no
    /// step produced it) is its own leaf.
    fn report_undefined_successor(
        &mut self,
        mut state: ExecutionState,
        halt_reason: HaltReason,
    ) -> Phase<()> {
        let Some(producer) = state.producer.take() else {
            return Err(Box::new(state.leaf(halt_reason, &self.observation_log)));
        };
        match self.successor_step(state.diagnostics.clone(), &producer, halt_reason) {
            Ok(UndefinedStep::Leaves(leaves, _)) => {
                let mut leaves = leaves.into_iter();
                let first = leaves.next().expect("a reported step has a leaf");
                self.leaves.extend(leaves);
                Err(Box::new(first))
            }
            Ok(UndefinedStep::Covered) => Ok(()),
            Ok(UndefinedStep::NoInstance) => {
                let pattern = state.pattern.clone();
                let constraint = super::false_constraint(&pattern);
                Err(Box::new(self.empty_leaf(state, pattern, constraint)))
            }
            Err(stop) => Err(Box::new(self.stopped_leaf(state, stop))),
        }
    }

    /// The `Vacuous` leaf of `state`, which has no instance: `pattern` with `constraint`
    /// refuted, at `state`'s depth. No rule is named: nothing applied to an instance.
    fn empty_leaf(
        &self,
        state: ExecutionState,
        pattern: Pattern,
        constraint: Predicate,
    ) -> ExecutionLeaf {
        let halt_reason = HaltReason::Vacuous {
            depth: state.depth,
            rule_id: None,
            label: None,
            constraint,
            contradicted_total: None,
        };
        let pattern = Pattern {
            term: pattern.term,
            constraints: vec![Predicate::False],
        };
        ExecutionState {
            producer: None,
            ..state
        }
        .leaf_with_pattern(pattern, halt_reason, &self.observation_log)
    }

    /// The undefined step of `producer`'s step, found when its successor's normalization
    /// showed it undefined (`halt_reason`). `diagnostics` are the path's up to the finding.
    ///
    /// The step's other applied candidates not yet normalized are normalized here: the
    /// undefined ones are parts of the same undefined step, and the defined ones exclude the
    /// instances they take. The first successor of a step to report this reports the step's one
    /// undefined step; the others report nothing ([`Producer::reported`]). Each successor's
    /// transition is rolled back (`discarded`). A stop is returned.
    fn successor_step(
        &mut self,
        mut diagnostics: PathDiagnostics,
        producer: &Producer,
        halt_reason: HaltReason,
    ) -> Stoppable<UndefinedStep> {
        self.roll_back(
            &producer.rule.unique_id,
            &producer.rule.label,
            &producer.successor,
            &producer.effects,
        );
        if producer.reported.replace(true) {
            return Ok(UndefinedStep::Covered);
        }
        let depth = match &halt_reason {
            HaltReason::Trivial { depth, .. } => *depth,
            _ => producer.parent.depth + 1,
        };
        let mut parts = vec![UndefinedPart::candidate(
            producer.index,
            &producer.before,
            &producer.successor,
            &producer.rule.unique_id,
            &producer.rule.label,
            producer.rule.clone(),
            halt_reason,
            Vec::new(),
            producer.remainder_simplifications.clone(),
        )];
        let parent_io = producer.parent.io_enabled.then_some(&producer.parent.io);
        let mut defined = Vec::with_capacity(producer.siblings.len());
        sibling_undefined_parts(
            self.definition,
            self.options.max_simplification_iterations,
            self.solver,
            parent_io,
            &producer.siblings,
            depth,
            &mut parts,
            &mut defined,
            &mut diagnostics,
        )?;
        let others = producer.has_remainder || !defined.is_empty();
        let defined = defined
            .iter()
            .map(|sibling| sibling.built())
            .collect::<Vec<_>>();
        self.undefined_step(&producer.parent, diagnostics, parts, &defined, others)
    }

    /// Record a candidate's transition from `target`'s producer as rolled back, when observed.
    fn roll_back(
        &mut self,
        rule_id: &str,
        label: &Option<String>,
        target: &Pattern,
        effects: &[BuiltinEffect],
    ) {
        if let Some(options) = self.observation
            && options.observes(rule_id)
        {
            self.discarded.push(UncommittedObservation {
                id: TransitionId {
                    rule: rule_id.to_owned(),
                    target: PatternDigest::of(target),
                },
                rule_label: label.clone(),
                effects: effects.to_vec(),
                reason: UncommittedReason::RolledBack,
            });
        }
    }

    /// The undefined step of a step taken from `parent`: the instances on which a candidate of
    /// the step applies and every candidate that applies is undefined (`parts`), outside the
    /// instances its defined candidates take (`defined`, their successors as the step built
    /// them). `diagnostics` are the path's; every part's work is added, since the leaf rests on
    /// every candidate being undefined. `others` says whether a defined candidate or a remainder
    /// takes some instance.
    ///
    /// Each part not already decided is restricted, simplified and checked for emptiness. The
    /// non-empty parts make one `Trivial` leaf: the configuration before the step, at its depth,
    /// on its path through the remainder simplifications of the first part, naming the first
    /// part's rule, under the disjunction of the parts' conditions (their common conjuncts kept
    /// as they are). Parts applied to patterns with different terms make one leaf per term.
    /// With no non-empty part the step is [`UndefinedStep::Covered`] when another candidate or
    /// the remainder takes some instance, and otherwise has no instance at all
    /// ([`UndefinedStep::NoInstance`]): every instance of a configuration either has a rule of
    /// its first applicable priority that applies, or is the remainder's. A stop is returned.
    fn undefined_step(
        &mut self,
        parent: &ExecutionState,
        mut diagnostics: PathDiagnostics,
        parts: Vec<UndefinedPart>,
        defined: &[&Pattern],
        others: bool,
    ) -> Stoppable<UndefinedStep> {
        let decision = decide_undefined_step(
            self.definition,
            self.options.max_simplification_iterations,
            self.solver,
            parts,
            defined,
            others,
            &mut diagnostics,
        )?;
        let (groups, excluded) = match decision {
            UndefinedDecision::Groups(groups, excluded) => (groups, excluded),
            UndefinedDecision::Covered => return Ok(UndefinedStep::Covered),
            UndefinedDecision::NoInstance => return Ok(UndefinedStep::NoInstance),
        };
        let mut leaves = Vec::with_capacity(groups.len());
        for group in groups {
            let mut leaf = ExecutionState {
                diagnostics: diagnostics.clone(),
                ..parent.clone()
            };
            for simplification in &group.remainder_simplifications {
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
            leaves.push(leaf.leaf_with_pattern(group.pattern, group.halt, &self.observation_log));
        }
        Ok(UndefinedStep::Leaves(leaves, excluded))
    }

    /// [`entry_undefined_part`] with this run's simplifier and solver.
    fn entry_part(
        &mut self,
        index: usize,
        entry: &TrivialApplication,
        depth: u64,
    ) -> Stoppable<Option<UndefinedPart>> {
        entry_undefined_part(
            self.definition,
            self.options.max_simplification_iterations,
            self.solver,
            index,
            entry,
            depth,
        )
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
                crate::coverage::suspend(|| {
                    crate::path_facts::suspend(|| (self.observe)(effect));
                });
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
                expanded: self.work.expanded(),
                stack_stops: 0,
                smt_unknowns: 0,
                stopped: self.stopped,
                implementation_chosen_values: Vec::new(),
                contradicted_claims: Vec::new(),
                allowance_refusals: Vec::new(),
                unsupported_hooks: Vec::new(),
                short_circuit_readings: Vec::new(),
                passed_stops: passed_stops_in_order(self.passed_stops),
                state_matches: self.matcher.map(StateMatcher::finish),
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
fn interrupted_with(
    mut leaf: Box<ExecutionLeaf>,
    lists: &[&[BackendDiagnostic]],
) -> Box<ExecutionLeaf> {
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
/// Absorbing a later unexplored or undecided leaf into an earlier stuck leaf loses no
/// configuration: the stuck halt is decided from the configuration (its term, constraints, effects
/// and console), so the later leaf's subtree is that configuration alone, which the stuck leaf
/// reports. Console availability and the state's kind, which the key leaves out, do not change a
/// stuck verdict: a stuck step performs no console operation (a rule's condition is not evaluated
/// with the console, so a console hook there is the unsupported-hook failure with the console on
/// or off, and the console is read only while a successor is built), so a step that reaches a
/// console hook with the console off ends as a simplification failure, not stuck; and a
/// remainder's stuck verdict is its parent step's over every priority. A result whose bound and
/// undecided leaves were all absorbed this way is complete (docs/compatibility.md, "Search
/// results"). When an unexplored or undecided leaf absorbs another, the key's omission of console
/// availability loses no configuration either, as the kept leaf is not complete, but its halt
/// describes its own path's console.
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
            arrivals_before_halt(&leaf),
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
    /// A stop condition was left undecided at the path's arrival (`StopUndecided`): the leaf
    /// says that the run to its stop has no answer there, so it is never merged.
    StopUndecided,
    /// A probe's answer ended the path or the request (`ProbeDifference`, `ProbeDone`): the
    /// leaf says where the probe stopped the run, nothing about the configuration, so it is
    /// never merged.
    ProbeAnswer,
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
        HaltReason::StopUndecided { .. } => MergeClass::StopUndecided,
        HaltReason::ProbeDifference { .. } | HaltReason::ProbeDone { .. } => {
            MergeClass::ProbeAnswer
        }
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
///   first then stands for both. Absorbing an unexplored or undecided leaf loses no configuration:
///   its subtree is the configuration alone, which the absorbing leaf reports, whatever the
///   console availability or the kind of the later leaf's state ([`merge_equal_final_leaves`]).
/// - A leaf that marks its configuration's subtree unexplored or undecided (a bound, a stop local
///   to the state, an undecided step, a failed simplification) stands only for another such leaf:
///   it does not say what the subtree holds, so it does not stand for a later stuck, branching or
///   cut-point leaf, which does.
/// - A terminal-rule leaf's halt records the rule by which its path arrived, not a property of the
///   configuration, which reached otherwise may have successors: exploring from another leaf of
///   it does not recover that it is final. A terminal-rule leaf therefore absorbs, and is absorbed
///   by, only leaves that also say the configuration is final (stuck or terminal-rule).
fn may_absorb(retained: &HaltReason, later: &HaltReason) -> bool {
    Standing::of(retained).absorbs(Standing::of(later))
}

/// What of a leaf's halt [`may_absorb`] reads: its merge class, and whether the halt says the
/// configuration is final in its own right (stuck or terminal-rule).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Standing {
    class: MergeClass,
    final_in_its_own_right: bool,
}

impl Standing {
    fn of(halt: &HaltReason) -> Self {
        Self {
            class: merge_class(halt),
            final_in_its_own_right: matches!(
                halt,
                HaltReason::Stuck | HaltReason::TerminalRule { .. }
            ),
        }
    }

    /// The table of [`may_absorb`].
    fn absorbs(self, later: Self) -> bool {
        match (self.class, later.class) {
            (MergeClass::ByArrival, _) | (_, MergeClass::ByArrival) => {
                self.final_in_its_own_right && later.final_in_its_own_right
            }
            (MergeClass::ByConfiguration, _) | (MergeClass::Unexplored, MergeClass::Unexplored) => {
                true
            }
            (MergeClass::Unexplored, _)
            | (
                MergeClass::NoConfiguration
                | MergeClass::RunEnding
                | MergeClass::StopUndecided
                | MergeClass::ProbeAnswer,
                _,
            ) => false,
        }
    }

    /// The standing of every halt a leaf of a run under `options` can have: those every run can
    /// reach (trivial and vacuous, a run-ending stop, an unexplored or undecided subtree, stuck),
    /// and those only an option gives (branch, cut point, terminal rule).
    fn possible(options: &ExecutionOptions) -> Vec<Self> {
        let standing = |class, final_in_its_own_right| Self {
            class,
            final_in_its_own_right,
        };
        let mut possible = vec![
            standing(MergeClass::NoConfiguration, false),
            standing(MergeClass::RunEnding, false),
            standing(MergeClass::Unexplored, false),
            standing(MergeClass::ByConfiguration, true),
        ];
        if options.branch_mode == ExecutionBranchMode::StopAtBranch
            || !options.cut_point_rules.is_empty()
        {
            possible.push(standing(MergeClass::ByConfiguration, false));
        }
        if !options.terminal_rules.is_empty() {
            possible.push(standing(MergeClass::ByArrival, true));
        }
        possible
    }
}

/// Whether, in a state-set result, a leaf of halt `halt` may be absorbed into a leaf of another
/// merge class (`possible`, the [`Standing::possible`] of the request's options): in another
/// model of the definition, the path of such a leaf may exist and be met first, and the leaf's
/// configuration is then reported with that other halt.
///
/// Absorption within one class needs nothing more. An unexplored or undecided leaf can also be
/// absorbed by a stuck one, so it carries the list anyway. Two leaves of the by-configuration
/// class with one configuration have the halt that the configuration's own step decides (the
/// same step on the same configuration), and that step's work is on both leaves' paths. A leaf
/// that absorbs another keeps its configuration and halt: which path's witness (depth, trace,
/// observations) the configuration is reported with depends on the path met first, which the
/// state-set guarantee does not cover, so that direction needs nothing either.
fn replaceable_in_state_set(possible: &[Standing], halt: &HaltReason) -> bool {
    let standing = Standing::of(halt);
    standing.class.mergeable()
        && possible
            .iter()
            .any(|other| other.class != standing.class && other.absorbs(standing))
}

/// The stop events and the arrivals at a stop `leaf`'s path passed before its own halt
/// ([`ExecutionOptions::stop_count`]): its counts, less the arrival a cut-point or terminal-rule
/// leaf ends at, which is an event.
///
/// A configuration's subtree under a count rests on the arrivals passed before it: a cut-point
/// leaf's configuration is final only at the last count, while at an earlier one the path goes
/// on from it, so an unexplored leaf of that configuration with fewer arrivals stands for more
/// than the configuration. A leaf is therefore merged only into a leaf of the same count before
/// its halt. Without a count every leaf has passed none, so the merge is unchanged.
fn arrivals_before_halt(leaf: &ExecutionLeaf) -> (u64, u64) {
    let own = u64::from(matches!(
        leaf.halt_reason,
        HaltReason::CutPointRule { .. } | HaltReason::TerminalRule { .. }
    ));
    (
        leaf.stops.saturating_sub(own),
        leaf.arrivals.saturating_sub(own),
    )
}

fn selected_stop_rule(applied: &AppliedRule, selected: &BTreeSet<String>) -> Option<String> {
    selected_stop_name(applied, selected).map(str::to_owned)
}

/// The name by which `selected` selects `applied`'s rule, its label before its `UNIQUE_ID`.
fn selected_stop_name<'a>(
    applied: &'a AppliedRule,
    selected: &BTreeSet<String>,
) -> Option<&'a str> {
    applied
        .label
        .as_deref()
        .filter(|label| selected.contains(*label))
        .or_else(|| {
            selected
                .contains(&applied.unique_id)
                .then_some(applied.unique_id.as_str())
        })
}

/// The passed stops of a run ([`ExecutionResult::passed_stops`]), each rule with the shallowest
/// depth at which the run passed it, in order of depth and then of name.
fn passed_stops_in_order(passed: BTreeMap<String, u64>) -> Vec<PassedStop> {
    let mut passed = passed
        .into_iter()
        .map(|(rule, depth)| PassedStop { depth, rule })
        .collect::<Vec<_>>();
    passed.sort();
    passed
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
    pub(crate) fn halt(self, depth: u64) -> HaltReason {
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
    /// The successor's constraints after both phases, with the conditions its term
    /// simplification conjoined: the constraints of the state built from it, whose
    /// satisfiability a one-path proof's sequential step asks (`rewrite::step`). `None` when a
    /// phase failed or the constraint phase showed the successor undefined.
    pub(crate) constraints: Option<Vec<Predicate>>,
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
/// (`Execution::normalise_constraints`), then the term is simplified under them
/// (`Execution::simplify_term`), with the console evaluation of `io` when the successor admits
/// one. Constraints that either phase makes `\bottom` show the successor undefined, however the
/// `\bottom` was found: a successor that denotes no state is no successor of its step. The
/// obligation named is the definedness condition the step added that the constraints refute,
/// else the undefined term (with the contradicted `total` attribute that produced it), else the
/// term where the simplification found `\bottom` (an equation whose own result is `\bottom`, a
/// refuted equation `ensures`), else the false constraint. A successor whose simplification
/// fails is not shown undefined. Diagnostics are not emitted; the normalization holds them.
///
/// A contradicted `preserves-definedness` of the rule whose work the normalization is
/// (`crate::path_facts::observed_by`) is noted when its result term is found `\bottom`
/// ([`note_undefined_result`]).
pub(crate) fn normalize_successor(
    definition: &BackendDefinition,
    successor: &Pattern,
    base: &[Predicate],
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
    io: Option<&ExecutionIoState>,
) -> Stoppable<SuccessorCheck> {
    normalize_successor_with(
        definition,
        successor,
        base,
        options,
        solver,
        io,
        ResultClaim::Note,
    )
    .map(|(check, _)| check)
}

/// What [`normalize_successor_with`] does with a result term found `\bottom`.
#[derive(Clone, Copy)]
enum ResultClaim {
    /// Note the contradicted `preserves-definedness` of the rule whose work the normalization is,
    /// when it claims one.
    Note,
    /// Note nothing, and report where the result was found `\bottom` ([`result_bottom`]): the
    /// caller decides on one alternative of a disjunctive right-hand side
    /// ([`alternatives_bottom`]).
    Report,
}

/// [`normalize_successor`], with `claim` saying what is done with a result term found
/// `\bottom`; the second part is the report [`ResultClaim::Report`] asks for.
fn normalize_successor_with(
    definition: &BackendDefinition,
    successor: &Pattern,
    base: &[Predicate],
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
    io: Option<&ExecutionIoState>,
    claim: ResultClaim,
) -> Stoppable<(SuccessorCheck, Option<(crate::term::Term, bool)>)> {
    let failed = SuccessorCheck {
        undefined: None,
        normalization: None,
        constraints: None,
    };
    let mut pattern = successor.clone();
    let retained_substitution =
        normalize_pattern_substitution(&mut pattern, definition.sort_graph());
    let added = beyond(&pattern.constraints, base);
    let (simplified, constraint_diagnostics) = crate::path_facts::collect_with_diagnostics(|| {
        simplify_predicates_with_solver(definition, &pattern.constraints, &[], options, solver)
    });
    let Ok(simplified) = simplified? else {
        return Ok((failed, None));
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
        // The successor denotes no state: the obligation named is the definedness condition the
        // step added that the constraints refute, else the false constraint.
        let obligation = added
            .into_iter()
            .find(|predicate| matches!(predicate, Predicate::Ceil(_) | Predicate::Defined(_)))
            .unwrap_or_else(|| super::false_constraint(&pattern));
        return Ok((
            SuccessorCheck {
                undefined: Some(UndefinedSuccessor {
                    obligation,
                    contradicted_total: None,
                }),
                normalization: Some(normalization),
                constraints: None,
            },
            None,
        ));
    }
    let mut evaluation = io
        .filter(|_| pattern_supports_execution_io(&pattern))
        .map(ExecutionIoState::begin_evaluation);
    let ((simplified, bottom), diagnostics) = crate::path_facts::collect_with_diagnostics(|| {
        let simplified = match evaluation.as_mut() {
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
        };
        let bottom = match (&simplified, claim) {
            (Ok(Ok(simplified)), ResultClaim::Note) => {
                note_undefined_result(&successor.term, &pattern.constraints, simplified);
                None
            }
            (Ok(Ok(simplified)), ResultClaim::Report) => {
                result_bottom(&pattern.constraints, simplified)
            }
            _ => None,
        };
        (simplified, bottom)
    });
    let Ok(simplified) = simplified? else {
        return Ok((failed, None));
    };
    let found_bottom = simplified.bottom.as_ref().map(|found| found.term.clone());
    let parts = simplified.clone().into_parts();
    normalization.term = Some(TermNormalization {
        simplified,
        diagnostics,
        io: evaluation.map(|evaluation| evaluation.commit()),
    });
    pattern.constraints.extend(parts.conditions);
    let undefined = (predicates_truth(&pattern.constraints) == Truth::False).then(|| {
        term_phase_undefinedness(
            parts.undefined_term,
            parts.contradicted_total,
            found_bottom,
            &pattern,
        )
    });
    Ok((
        SuccessorCheck {
            undefined,
            normalization: Some(normalization),
            constraints: Some(pattern.constraints),
        },
        bottom,
    ))
}

/// Why a successor whose term simplification, under the constraints and the conditions it
/// conjoined (`normalized`'s), made it `\bottom` is undefined: the undefined term, with the
/// contradicted `total` attribute that produced it, else the term where the simplification found
/// `\bottom` (`Simplification::bottom`: an equation whose own result is `\bottom`, a refuted
/// equation `ensures`, any other conjoined `\bottom`), else the false constraint. How the
/// `\bottom` was found is diagnosis only: the successor denotes no state either way.
/// `contradictedTotal` names an undefined builtin result only.
fn term_phase_undefinedness(
    undefined_term: Option<crate::term::Term>,
    contradicted_total: Option<Box<ContradictedTotal>>,
    found_bottom: Option<crate::term::Term>,
    normalized: &Pattern,
) -> UndefinedSuccessor {
    match (undefined_term, found_bottom) {
        (Some(term), _) => UndefinedSuccessor {
            obligation: Predicate::Ceil(term),
            contradicted_total,
        },
        (None, Some(term)) => UndefinedSuccessor {
            obligation: Predicate::Ceil(term),
            contradicted_total: None,
        },
        (None, None) => UndefinedSuccessor {
            obligation: super::false_constraint(normalized),
            contradicted_total: None,
        },
    }
}

/// Note a contradicted `preserves-definedness` (`crate::path_facts::note_contradicted_preservation`)
/// when `simplified`, the simplification of a successor's term under `constraints`, shows the
/// result term `\bottom` ([`result_bottom`]). `instance` is the result term as the step that
/// produced the successor built it. The claim is that of the rule whose work the normalization
/// is (`crate::path_facts::observed_by`), when it makes one; [`result_bottom`] runs only then,
/// and only while claims are checked and a note has somewhere to go, so a successor of a rule
/// that claims nothing costs nothing here.
pub(crate) fn note_undefined_result(
    instance: &crate::term::Term,
    constraints: &[Predicate],
    simplified: &Simplification,
) {
    crate::path_facts::note_contradicted_preservation(instance, || {
        result_bottom(constraints, simplified)
    });
}

/// Where a successor's result term is `\bottom`, and whether the step's premises are known to
/// hold, when `simplified`, the simplification of the term under `constraints` (the successor's
/// constraints after their own simplification), is `\bottom` while `constraints` are not: by
/// any route, an undefined builtin application or repeated collection (`undefined_term`), an
/// equation whose own result is `\bottom`, or anything else the simplification conjoins
/// `\bottom` for. The term named is the undefined term, else where the simplification found
/// `\bottom` (`FoundBottom`), else the simplified result.
///
/// The premises hold when every constraint is `\top`: the step's match and `requires` were then
/// decided on the instance alone, as was everything the step added (a carried `requires`,
/// `ensures` or definedness obligation stays a constraint). A constraint left open, the
/// pre-step state's included, restricts the models the step applies in, so a `\bottom` result
/// under it shows the claim false only where the constraint is satisfiable.
pub(crate) fn result_bottom(
    constraints: &[Predicate],
    simplified: &Simplification,
) -> Option<(crate::term::Term, bool)> {
    // The term phase's own conditions first: a result that conjoins no `\bottom` is the common
    // case, and the constraints are not read for it.
    if !simplified
        .conjoined()
        .any(|predicate| predicate_truth(predicate) == Truth::False)
    {
        return None;
    }
    let truth = predicates_truth(constraints);
    if truth == Truth::False {
        return None;
    }
    let undefined = simplified
        .undefined_term
        .clone()
        .or_else(|| simplified.bottom.as_ref().map(|found| found.term.clone()))
        .unwrap_or_else(|| simplified.term.clone());
    Some((undefined, truth == Truth::True))
}

/// Whether every alternative of a disjunctive right-hand side, each a successor `built` from a
/// pattern with the constraints `base`, has a result term found `\bottom` ([`result_bottom`]),
/// and where for each: the definedness of a disjunction is the disjunction of its alternatives'
/// definedness, so a declared `preserves-definedness` of such a rule is refuted only then
/// (`apply`). The normalizations are taken aside: they decide nothing in the run, so what they
/// observe reaches no path and no list, what they emit is dropped, they use no console and they
/// cover nothing; the successors' own normalizations observe and emit it where the run decides
/// on them.
pub(crate) fn alternatives_bottom(
    definition: &BackendDefinition,
    built: &[&Pattern],
    base: &[Predicate],
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Stoppable<Option<Vec<(crate::term::Term, bool)>>> {
    crate::coverage::suspend(|| {
        crate::path_facts::aside(|| {
            // Held and dropped, never committed: the run emits what its own normalizations do.
            let (found, _dropped) = diagnostic::buffer(|| {
                let mut found = Vec::with_capacity(built.len());
                for successor in built {
                    let (_, bottom) = normalize_successor_with(
                        definition,
                        successor,
                        base,
                        options,
                        solver,
                        None,
                        ResultClaim::Report,
                    )?;
                    match bottom {
                        Some(bottom) => found.push(bottom),
                        None => return Ok(None),
                    }
                }
                Ok(Some(found))
            });
            found
        })
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
    let (simplified, diagnostics) = crate::path_facts::collect_with_diagnostics(|| {
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
    /// (`Execution::restrict_to_defined_instances`), which restricts what its step produces and
    /// leaves over; empty on every other state.
    defined_where: Vec<Predicate>,
    /// The backend diagnostics of the work this path went through so far, shared with the
    /// paths it forked from.
    diagnostics: PathDiagnostics,
    /// The step that produced this state, until the state's first normalization, which may find
    /// that step undefined ([`Producer`]); `None` on every other state.
    producer: Option<std::rc::Rc<Producer>>,
    /// The stop events this state's path passed ([`ExecutionOptions::stop_count`]): its
    /// arrivals at a stop where the stop condition held, every arrival without a condition.
    stops: u64,
    /// The arrivals at a stop this state's path passed, whatever the stop condition answered.
    arrivals: u64,
    /// How the step that produced this state is an arrival at a stop the path goes on past,
    /// counted once the state's normalization shows it defined; `None` on every other state.
    arriving: Option<Arriving>,
    /// The probe's points of the step that produced this state, asked once the state's
    /// normalization shows it defined (`probe`); `None` on every other state.
    probing: Option<Box<Probing>>,
}

/// The points of a step a probe observes ([`ExecutionState::probing`]): the rule of its before
/// point with the state before the step, and the rule of its after point, each by the name the
/// request selected it by.
#[derive(Clone)]
struct Probing {
    before: Option<(String, ExecutionState)>,
    after: Option<String>,
}

/// How a step is an arrival at a stop that does not end the path at the step
/// ([`ExecutionState::arriving`]), counted once its successor's normalization shows it defined.
#[derive(Clone)]
enum Arriving {
    /// A run without a stop condition: every arrival is an event.
    Counted,
    /// A run with a stop condition, asked at the step ([`Execution::stop_plan`]): whether it
    /// held, which makes the arrival an event.
    Asked { event: bool },
}

/// What a step by a stop rule, its state's one successor, does at the stop rules
/// ([`Execution::stop_plan`]).
#[derive(Default)]
struct StopPlan {
    /// The path ends before the step, at this cut-point rule, once the successor is shown
    /// defined.
    ends_before: Option<String>,
    /// With [`Self::ends_before`] or [`Self::terminal`]: the condition's answer there, neither
    /// yes nor no, which ends the path otherwise ([`Execution::deferred_answer`]).
    deferred: Option<StopDecision>,
    /// The step is an arrival the path goes on past.
    arriving: Option<Arriving>,
    /// The path ends after the step, at this terminal rule, once the successor is shown defined.
    terminal: Option<String>,
    /// Under strategy any, whether the step is its state's one successor is undecided: the path
    /// ends at the state before the step with this halt and the diagnostics of the work that
    /// left it undecided ([`Execution::siblings`]).
    undecided: Option<(HaltReason, Vec<BackendDiagnostic>)>,
}

/// Whether a stop rule's step taken under strategy any has a sibling ([`Execution::siblings`]).
enum Siblings {
    /// The step is its state's one successor.
    None,
    /// The state has another successor.
    Another,
    /// The all-path step at the state did not decide its successors: its halt, with the
    /// diagnostics of its work.
    Undecided(Box<(HaltReason, Vec<BackendDiagnostic>)>),
}

/// Whether `reading` says the candidate (or remainder) `pattern` denotes no state, its path
/// condition's conjuncts externalized; `hooks` is whether the run so far left a hook unevaluated.
fn denotes_no_state(reading: &dyn SuccessorReading, pattern: &Pattern, hooks: bool) -> bool {
    let sort = pattern.term.sort();
    let path_condition = pattern
        .constraints
        .iter()
        .map(|predicate| crate::externalize::predicate_pattern(predicate, &sort))
        .collect::<Vec<_>>();
    reading.denotes_no_state(&stop_condition::Candidate {
        path_condition: &path_condition,
        hooks_unevaluated: hooks,
    })
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
    /// The rule, as the contradicted claims the successor's normalization observes name it
    /// (`crate::path_facts`).
    rule: crate::path_facts::ObservingRule,
    effects: Vec<BuiltinEffect>,
    /// The simplifications of a higher-priority remainder that led to `before`, which the leaf's
    /// path goes through, as an undefined step the step itself finds does.
    remainder_simplifications: Vec<RemainderSimplification>,
    /// This candidate's position among the step's candidates: the undefined step's leaf names
    /// the first undefined one.
    index: usize,
    /// The step's other applied candidates, as the step built them, whose definedness is
    /// decided only if this successor turns out undefined.
    siblings: Vec<Sibling>,
    /// Whether the step also left a remainder, which some instances reach.
    has_remainder: bool,
    /// Set once the step's undefined step has been reported by one of its successors: the
    /// step has one such leaf, standing for every instance on which all its candidates that
    /// apply are undefined, so its other undefined successors report none.
    reported: std::rc::Rc<std::cell::Cell<bool>>,
    /// The normalization of `successor` the step already did, which the successor's own
    /// normalization takes instead of repeating it.
    normalization: Option<std::sync::Arc<SuccessorNormalization>>,
    /// What the step's instance bound that the run's binding collection records, recorded when
    /// the successor is committed (`Execution::note_committed`).
    bindings: crate::coverage::CarriedBindings,
}

/// The id of the rule whose step built `state`, by its producer.
fn producer_rule_id(state: &ExecutionState) -> Option<&str> {
    state
        .producer
        .as_ref()
        .map(|producer| producer.rule.unique_id.as_str())
}

/// Another applied candidate of a successor's step ([`Producer::siblings`]).
#[derive(Clone)]
pub(crate) struct Sibling {
    pub(crate) index: usize,
    before: Pattern,
    built: Pattern,
    rule: crate::path_facts::ObservingRule,
    remainder_simplifications: Vec<RemainderSimplification>,
}

impl Sibling {
    /// This candidate as a part of its step's undefined step, its successor undefined (`halt`,
    /// named for it here).
    pub(crate) fn part(&self, halt: HaltReason) -> UndefinedPart {
        UndefinedPart::candidate(
            self.index,
            &self.before,
            &self.built,
            &self.rule.unique_id,
            &self.rule.label,
            self.rule.clone(),
            halt,
            Vec::new(),
            self.remainder_simplifications.clone(),
        )
    }

    /// The candidate's successor as the step built it.
    pub(crate) fn built(&self) -> &Pattern {
        &self.built
    }

    pub(crate) fn of(index: usize, applied: &AppliedRule) -> Self {
        Self {
            index,
            before: applied.before.clone(),
            built: applied.pattern.clone(),
            rule: applied.observing_rule(),
            remainder_simplifications: applied.remainder_simplifications.clone(),
        }
    }
}

impl Producer {
    /// The producer of `applied`'s successor, the step's only candidate.
    fn of(parent: &ExecutionState, applied: &AppliedRule) -> Self {
        Self::of_step(parent, applied, 0, Vec::new(), false, Default::default())
    }

    fn of_step(
        parent: &ExecutionState,
        applied: &AppliedRule,
        index: usize,
        siblings: Vec<Sibling>,
        has_remainder: bool,
        reported: std::rc::Rc<std::cell::Cell<bool>>,
    ) -> Self {
        Self {
            parent: ExecutionState {
                producer: None,
                ..parent.clone()
            },
            before: applied.before.clone(),
            successor: applied.pattern.clone(),
            rule: applied.observing_rule(),
            effects: applied.effects.clone(),
            remainder_simplifications: applied.remainder_simplifications.clone(),
            index,
            siblings,
            has_remainder,
            reported,
            // A step's normalization stands for the successor only when it is of the pattern
            // the step committed; any other is dropped and the successor normalizes itself.
            normalization: applied
                .normalized
                .0
                .clone()
                .filter(|normalization| normalization.built == applied.pattern),
            bindings: applied.bindings.clone(),
        }
    }
}

/// One way a step leaves some of its instances without a successor: an applied candidate whose
/// result is `\bottom`, found by the step itself (a trivial entry) or by its successor's
/// normalization ([`Execution::undefined_step`]).
pub(crate) struct UndefinedPart {
    /// The candidate's position among the step's reported candidates.
    index: usize,
    /// The instances the candidate leaves without a successor before the defined candidates
    /// are excluded: the pattern it was applied to under its condition.
    pattern: Pattern,
    /// The constraints of the pattern the candidate was applied to; a defined candidate's
    /// condition is taken beyond them.
    base: Vec<Predicate>,
    /// The variables of the pattern the candidate was applied to: the others its condition
    /// mentions are its rule's, existentially closed.
    bound: BTreeSet<crate::term::Variable>,
    /// Whether `pattern` is the step's own decided, non-empty set (a trivial entry).
    decided: bool,
    /// The `Trivial` halt naming the candidate's rule.
    halt: HaltReason,
    /// The rule whose work deciding the leaf is, when it is a candidate's.
    rule: Option<crate::path_facts::ObservingRule>,
    /// The work that showed the candidate undefined.
    diagnostics: Vec<BackendDiagnostic>,
    remainder_simplifications: Vec<RemainderSimplification>,
}

impl UndefinedPart {
    /// The part of a candidate applied to `before` whose successor, `built` as the step built
    /// it, is undefined (`halt`, named for the candidate here).
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn candidate(
        index: usize,
        before: &Pattern,
        built: &Pattern,
        rule_id: &str,
        label: &Option<String>,
        rule: crate::path_facts::ObservingRule,
        halt: HaltReason,
        diagnostics: Vec<BackendDiagnostic>,
        remainder_simplifications: Vec<RemainderSimplification>,
    ) -> Self {
        let bound = pattern_variables(before);
        let mut constraints = before.constraints.clone();
        let branch = beyond(&built.constraints, &before.constraints);
        extend_unique_predicates(&mut constraints, closed_over(branch, &bound));
        let halt = match halt {
            HaltReason::Trivial {
                depth,
                obligation,
                contradicted_total,
                ..
            } => HaltReason::Trivial {
                depth,
                rule_id: Some(rule_id.to_owned()),
                label: label.clone(),
                obligation,
                contradicted_total,
            },
            other => other,
        };
        Self {
            index,
            pattern: Pattern {
                term: before.term.clone(),
                constraints,
            },
            base: before.constraints.clone(),
            bound,
            decided: false,
            halt,
            rule: Some(rule),
            diagnostics,
            remainder_simplifications,
        }
    }
}

/// One `Trivial` leaf of a step's undefined step ([`decide_undefined_step`]): the configuration
/// the step was taken from under the joined conditions of its parts over one term, the halt of
/// its first part, and the higher-priority remainder simplifications that part went through.
pub(crate) struct UndefinedGroup {
    pub(crate) pattern: Pattern,
    pub(crate) halt: HaltReason,
    pub(crate) remainder_simplifications: Vec<RemainderSimplification>,
}

/// What a step's undefined parts come to, before any route builds its leaves from them.
pub(crate) enum UndefinedDecision {
    /// The undefined step's leaves, one per pre-step term, and the instances they stand for.
    Groups(Vec<UndefinedGroup>, Exclusion),
    /// Every part is shown empty while a defined candidate or a remainder is left.
    Covered,
    /// Every part is shown empty and nothing else is left: the configuration has no instance.
    NoInstance,
}

/// The undefined step of a step: the instances on which a candidate of the step applies and
/// every candidate that applies is undefined (`parts`), outside the instances its defined
/// candidates take (`defined`, their successors as the step built them). `others` says whether
/// a defined candidate or a remainder takes some instance. Every part's work is added to
/// `diagnostics`, since the leaf rests on every candidate being undefined. This is the one
/// decision every route takes (executions and proofs alike); each builds its own leaves from
/// the groups.
///
/// Each part not already decided is restricted, simplified and checked for emptiness. The
/// non-empty parts make one leaf per pre-step term, under the disjunction of their conditions
/// (their common conjuncts kept as they are), naming the first part. With no non-empty part the
/// step is [`UndefinedDecision::Covered`] when another candidate or the remainder takes some
/// instance, and otherwise has no instance at all ([`UndefinedDecision::NoInstance`]): every
/// instance of a configuration either has a rule of its first applicable priority that
/// applies, or is the remainder's. A stop is returned.
pub(crate) fn decide_undefined_step(
    definition: &BackendDefinition,
    max_iterations: usize,
    solver: &dyn SmtSolver,
    parts: Vec<UndefinedPart>,
    defined: &[&Pattern],
    others: bool,
    diagnostics: &mut PathDiagnostics,
) -> Stoppable<UndefinedDecision> {
    let mut found = Vec::with_capacity(parts.len());
    for mut part in parts {
        diagnostics.extend(&part.diagnostics);
        if part.decided {
            found.push(part);
            continue;
        }
        for sibling in defined {
            let applies = beyond(&sibling.constraints, &part.base);
            part.pattern
                .constraints
                .push(Predicate::Not(Arc::new(conjunction(closed_over(
                    applies,
                    &part.bound,
                )))));
        }
        let rule = part.rule.clone();
        let (simplified, work) = crate::path_facts::collect_with_diagnostics(|| {
            crate::path_facts::observed_by(
                || rule,
                || {
                    simplify_predicates_with_solver(
                        definition,
                        &part.pattern.constraints,
                        &[],
                        SimplificationOptions::keep_partial(max_iterations),
                        solver,
                    )
                },
            )
        });
        diagnostics.extend(&work);
        match simplified {
            Ok(Ok(simplified)) => part.pattern.constraints = simplified,
            // A failed simplification only loses precision.
            Ok(Err(_failure)) => {}
            Err(stop) => stop.forgo_refinement(),
        }
        let empty = predicates_truth(&part.pattern.constraints) == Truth::False
            || matches!(
                solver.is_sat(&part.pattern.constraints, &Substitution::new())?,
                Ok(Satisfiability::Unsat)
            );
        if !empty {
            found.push(part);
        }
    }
    if found.is_empty() {
        return Ok(if others {
            UndefinedDecision::Covered
        } else {
            UndefinedDecision::NoInstance
        });
    }
    found.sort_by_key(|part| part.index);
    // The instances the leaves stand for, part by part, whatever their terms.
    let excluded = Exclusion(
        found
            .iter()
            .map(|part| part.pattern.constraints.clone())
            .collect(),
    );
    // One leaf per pre-step term, in the order of their first parts.
    let mut groups: Vec<Vec<UndefinedPart>> = Vec::new();
    for part in found {
        match groups
            .iter_mut()
            .find(|group| group[0].pattern.term == part.pattern.term)
        {
            Some(group) => group.push(part),
            None => groups.push(vec![part]),
        }
    }
    let mut leaves = Vec::with_capacity(groups.len());
    for group in groups {
        let constraints = joined_conditions(definition, max_iterations, solver, &group)?;
        let first = group.into_iter().next().expect("a group has a part");
        leaves.push(UndefinedGroup {
            pattern: Pattern {
                term: first.pattern.term,
                constraints,
            },
            halt: first.halt,
            remainder_simplifications: first.remainder_simplifications,
        });
    }
    Ok(UndefinedDecision::Groups(leaves, excluded))
}

/// The constraints of one leaf for the non-empty `group` of parts over one term: the part's
/// own for one part; for several, the conjuncts they all have, and the disjunction of what
/// remains of each, simplified.
fn joined_conditions(
    definition: &BackendDefinition,
    max_iterations: usize,
    solver: &dyn SmtSolver,
    group: &[UndefinedPart],
) -> Stoppable<Vec<Predicate>> {
    if let [part] = group {
        return Ok(part.pattern.constraints.clone());
    }
    let common = group[0]
        .pattern
        .constraints
        .iter()
        .filter(|predicate| {
            group
                .iter()
                .all(|part| part.pattern.constraints.contains(predicate))
        })
        .cloned()
        .collect::<Vec<_>>();
    let rests = group
        .iter()
        .map(|part| beyond(&part.pattern.constraints, &common))
        .collect::<Vec<_>>();
    if rests.iter().any(Vec::is_empty) {
        return Ok(common);
    }
    let mut constraints = common;
    constraints.push(Predicate::Or(
        rests
            .into_iter()
            .map(conjunction)
            .collect::<Vec<_>>()
            .into(),
    ));
    let rule = group[0].rule.clone();
    let (simplified, _work) = crate::path_facts::collect_with_diagnostics(|| {
        crate::path_facts::observed_by(
            || rule,
            || {
                simplify_predicates_with_solver(
                    definition,
                    &constraints,
                    &[],
                    SimplificationOptions::keep_partial(max_iterations),
                    solver,
                )
            },
        )
    });
    Ok(match simplified? {
        Ok(simplified) => simplified,
        Err(_failure) => constraints,
    })
}

/// The part of `entry`, a bottom-result sub-case of a step the step itself found (at the
/// successor's `depth`): the pattern it was applied to, restricted to `entry.undefined`, on the
/// path through the higher-priority remainder simplifications it went through. `None` when that
/// set is shown empty ([`TrivialApplication::decided_undefined_instances`]).
pub(crate) fn entry_undefined_part(
    definition: &BackendDefinition,
    max_iterations: usize,
    solver: &dyn SmtSolver,
    index: usize,
    entry: &TrivialApplication,
    depth: u64,
) -> Stoppable<Option<UndefinedPart>> {
    let (pattern, work) = crate::path_facts::collect_with_diagnostics(|| {
        entry.decided_undefined_instances(definition, max_iterations, solver)
    });
    let Some(pattern) = pattern? else {
        return Ok(None);
    };
    let mut diagnostics = entry.diagnostics.clone();
    extend_distinct(&mut diagnostics, &work);
    Ok(Some(UndefinedPart {
        index,
        base: entry.before.constraints.clone(),
        bound: pattern_variables(&entry.before),
        pattern,
        decided: true,
        halt: applied_trivial_halt(depth, entry),
        rule: None,
        diagnostics,
        remainder_simplifications: entry.remainder_simplifications.clone(),
    }))
}

/// Normalize the step's other candidates `siblings` (not yet normalized) for the undefined step
/// of a successor of it at `depth`: an undefined one is a part of it, added to `parts`; a defined
/// one is added to `defined` (its successor as the step built it excludes the instances it
/// takes), and the work of normalizing it to `diagnostics`. A contradiction a sibling's normalization observes is its own rule's.
#[allow(clippy::too_many_arguments)]
pub(crate) fn sibling_undefined_parts<'s>(
    definition: &BackendDefinition,
    max_iterations: usize,
    solver: &dyn SmtSolver,
    io: Option<&ExecutionIoState>,
    siblings: &'s [Sibling],
    depth: u64,
    parts: &mut Vec<UndefinedPart>,
    defined: &mut Vec<&'s Sibling>,
    diagnostics: &mut PathDiagnostics,
) -> Stoppable<()> {
    for sibling in siblings {
        let (undefined, work) = crate::path_facts::collect_with_diagnostics(|| {
            crate::path_facts::observed_by(
                || Some(sibling.rule.clone()),
                || {
                    successor_undefinedness(
                        definition,
                        &sibling.built,
                        &sibling.before.constraints,
                        SimplificationOptions::keep_partial(max_iterations),
                        solver,
                        io,
                    )
                },
            )
        });
        match undefined? {
            Some(undefined) => parts.push(UndefinedPart::candidate(
                sibling.index,
                &sibling.before,
                &sibling.built,
                &sibling.rule.unique_id,
                &sibling.rule.label,
                sibling.rule.clone(),
                undefined.halt(depth),
                work,
                sibling.remainder_simplifications.clone(),
            )),
            None => {
                diagnostics.extend(&work);
                defined.push(sibling);
            }
        }
    }
    Ok(())
}

/// The candidates a step is left with once each is known defined or undefined
/// ([`Execution::conclude_step`]).
enum Survivors {
    /// Exploring all paths: normalized within the step, each successor taking that
    /// normalization.
    Normalized(Vec<AppliedRule>),
    /// Stopping at branches: each simplified for the branch leaf, on its own observation head,
    /// with its successor as the step built it; and the remainder's observation head.
    Simplified(
        Vec<(AppliedRule, ObservationHead, Pattern)>,
        ObservationHead,
    ),
}

impl Survivors {
    /// The defined candidates' successors as the step built them.
    fn built(&self) -> Vec<Pattern> {
        match self {
            Survivors::Normalized(defined) => defined
                .iter()
                .map(|applied| applied.pattern.clone())
                .collect(),
            Survivors::Simplified(branches, _) => {
                branches.iter().map(|(_, _, built)| built.clone()).collect()
            }
        }
    }
}

/// What a step's undefined candidates come to ([`Execution::undefined_step`]).
enum UndefinedStep {
    /// The step's `Trivial` leaves: one, unless its undefined candidates were applied to
    /// patterns with different terms (one per term then).
    /// With the instances they stand for, which the step's other leaves exclude.
    Leaves(Vec<ExecutionLeaf>, Exclusion),
    /// No instance is left undefined: the step's defined candidates or its remainder take every
    /// instance its undefined candidates apply to.
    Covered,
    /// The step has no instance at all: every candidate is undefined, none is left any instance,
    /// and no remainder is left. The configuration it was taken from has no instance, which
    /// only the step exposed.
    NoInstance,
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
            stops: self.stops,
            arrivals: self.arrivals,
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
///
/// A fresh element variable that a conjunct equates with a defined term (`?Y = t`, `t` free of
/// `?Y`, of the other fresh variables and of anything undefined) is eliminated first:
/// `∃?Y. (?Y = t ∧ ψ)` is `ψ[t/?Y]`, since an element variable denotes a defined element and
/// `t` is one. So an `ensures` that binds a rule's existential to the configuration's value
/// states that value, not an existential over it.
fn closed_over(
    predicates: Vec<Predicate>,
    bound: &BTreeSet<crate::term::Variable>,
) -> Vec<Predicate> {
    let free = |predicates: &[Predicate]| {
        predicates
            .iter()
            .flat_map(Predicate::free_variables)
            .filter(|variable| !bound.contains(variable))
            .collect::<BTreeSet<_>>()
    };
    let predicates = super::predicates::eliminate_equated_variables(predicates, free);
    let fresh = free(&predicates);
    if fresh.is_empty() {
        return predicates;
    }
    vec![
        fresh
            .into_iter()
            .fold(conjunction(predicates), |body, variable| {
                Predicate::Exists(variable, Arc::new(body))
            }),
    ]
}

/// The instances of a step's undefined step, which its other leaves exclude so that the step's
/// leaves partition its instances: one condition per non-empty undefined part, the constraints
/// of the instances that part stands for. A statement about instances: it is read over the
/// variables of the configuration the step was taken from, whatever term the part was applied
/// to (a lower priority's simplified remainder has the same instances under another term). No
/// part means nothing is excluded.
#[derive(Clone, Default)]
pub(crate) struct Exclusion(Vec<Vec<Predicate>>);

impl Exclusion {
    /// Restrict `pattern`, a leaf of the step over the configuration it was taken from, to the
    /// instances outside every part: for each, the negation of its conditions beyond `pattern`'s
    /// own. A part none of whose conditions goes beyond `pattern`'s stands for all its instances,
    /// so none is left.
    fn exclude_from(&self, pattern: &mut Pattern) {
        for conditions in &self.0 {
            let extra = beyond(conditions, &pattern.constraints);
            pattern
                .constraints
                .push(Predicate::Not(Arc::new(conjunction(extra))));
        }
    }
}

fn conjunction(mut predicates: Vec<Predicate>) -> Predicate {
    match predicates.len() {
        0 => Predicate::True,
        1 => predicates.pop().expect("one predicate"),
        _ => Predicate::And(predicates.into()),
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
    use std::num::NonZeroU64;

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

    /// A solver that answers every query `unknown`.
    struct Undecided;

    impl SmtSolver for Undecided {
        fn is_sat(
            &self,
            _predicates: &[Predicate],
            _substitution: &crate::substitution::Substitution,
        ) -> Stoppable<Result<crate::smt::Satisfiability, crate::smt::SmtError>> {
            Ok(Ok(crate::smt::Satisfiability::Unknown("test".to_owned())))
        }

        fn check_predicates(
            &self,
            _known: &[Predicate],
            _substitution: &crate::substitution::Substitution,
            _checked: &[Predicate],
        ) -> Stoppable<Result<crate::smt::Validity, crate::smt::SmtError>> {
            Ok(Ok(crate::smt::Validity::Unknown("test".to_owned())))
        }
    }

    /// The state matcher's undecided solver answers are its own: a ground run that asks the
    /// solver nothing reports no `smt_unknowns`, while matching its end against a target whose
    /// constraint only the solver could decide (`done /\ Y >Int 0`, `Y` unbound) counts the
    /// matcher's `unknown`s on the summary and leaves the match undecided. Every other field is
    /// the run's without matching.
    #[test]
    fn the_matcher_s_undecided_answers_are_kept_off_the_run_s_count() {
        let source = r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                sort SortS{} []
                symbol start{}() : SortS{} [constructor{}()]
                symbol done{}() : SortS{} [constructor{}()]
                hooked-symbol gtInt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.gt"), smt-hook{}(">")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(start{}(), \top{SortS{}}()),
                    done{}()
                ) [label{}("go")]
            endmodule []"#;
        let definition = BackendDefinition::internalize(
            &parse_definition(source).expect("definition should parse"),
            "MAIN",
        )
        .expect("definition should internalize");
        let internal = |text: &str| {
            definition
                .admit_unverified(&parse_pattern(text).expect("pattern should parse"), &[])
                .internalize_pattern()
                .expect("pattern should internalize")
        };
        let start = internal("start{}()");
        let target = internal(
            r#"\and{SortS{}}(done{}(), \equals{SortBool{}, SortS{}}(gtInt{}(Y:SortInt{}, \dv{SortInt{}}("0")), \dv{SortBool{}}("true")))"#,
        );
        let run = |match_states| {
            execute_using(
                &definition,
                vec![start.clone()],
                ExecutionOptions {
                    match_states,
                    ..ExecutionOptions::default()
                },
                &Undecided,
                None,
                None,
                |_| {},
            )
            .0
        };
        let plain = run(None);
        let mut matched = run(Some(crate::rewrite::StateMatchOptions {
            target,
            proof_agreement: false,
        }));
        let found = matched
            .state_matches
            .take()
            .expect("the run matched states");
        assert_eq!(plain.smt_unknowns, 0);
        assert!(found.smt_unknowns > 0, "{found:?}");
        assert_eq!(found.matched, 2);
        assert_eq!(found.undecided.len(), 1, "{found:?}");
        assert_eq!(
            found.undecided[0].reason,
            crate::rewrite::UndecidedMatchReason::UndecidedMatch
        );
        assert_eq!(matched, plain);
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
            stops: 0,
            arrivals: 0,
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
            stops: 0,
            arrivals: 0,
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
            stops: 0,
            arrivals: 0,
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
            stops: 0,
            arrivals: 0,
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
    /// Every step of a rule names it by one identity, built once from its attributes: a rule
    /// attempt, an applied candidate, its successor's producer and each rule scope share it.
    /// A renaming of the rule's variables keeps it; a copy of the rule, which may be changed
    /// before it is used, builds its own, equal one.
    #[test]
    fn a_rules_steps_share_one_identity() {
        use crate::path_facts::ObservingRule;
        let definition = definition(
            r#"axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                wrap{}(X:SortS{})
            ) [label{}("loop")]"#,
        );
        let rule = definition
            .rewrite_theory()
            .values()
            .flat_map(|groups| groups.values().flatten())
            .find(|rule| rule.rule.attributes.label.as_deref() == Some("loop"))
            .map(|rule| Arc::clone(&rule.rule))
            .expect("the rule is in the definition");
        let first = ObservingRule::of(&rule);
        let second = ObservingRule::of(&rule);
        assert!(std::ptr::eq(&*first, &*second));
        assert_eq!(first.label.as_deref(), Some("loop"));
        assert_eq!(first.unique_id, rule.attributes.unique_id);

        // A subject holding the rule's own variables makes the rule be renamed apart.
        let (renamed, _) = crate::rule::rename_apart(&rule, &rule.lhs.attributes().variables, &[])
            .expect("the rule shares its variables with such a subject");
        assert!(std::ptr::eq(&*ObservingRule::of(&renamed), &*first));

        let copy = crate::rule::RewriteRule::clone(&rule);
        let copied = ObservingRule::of(&copy);
        assert!(!std::ptr::eq(&*copied, &*first));
        assert_eq!(copied, first);
    }

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
            stops: 0,
            arrivals: 0,
            arriving: None,
            probing: None,
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
            stops: 0,
            arrivals: 0,
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
        let mut execution = Execution::seed(
            definition, initial, options, solver, solver, None, None, observe, None, None, None,
        );
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
            &crate::smt::NoSolver,
            None,
            None,
            &mut observe,
            None,
            None,
            None,
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
        // The states visited are the chain's nine (`s0`, `l0`, `s1`, `l1`, `s2`, `r1`, `s2`
        // merged, `r0`, `s1` merged) and `probe`. The chain's seven unmerged states are stepped; `probe`'s step is interrupted by the cancellation it
        // raises, so it has no answer and is not expanded.
        assert_eq!((result.work, result.expanded), (10, 7), "{result:#?}");
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
                    // The stop interrupted the first `m(X)`'s step, which has no answer: that
                    // `m(X)` is visited but not expanded, as the merged second `m(X)` of the
                    // unstopped run is, and the second one, expanded instead, has the first
                    // one's unstopped subtree. So both counts are the unstopped run's.
                    ("m", _) => {
                        stopped_in_the_step = true;
                        assert_eq!(
                            (result.work, result.expanded),
                            (unstopped.work, unstopped.expanded),
                            "query {nth}: {result:#?}"
                        );
                    }
                    // A terminal successor is normalised by the expansion of the `m(X)` it
                    // succeeds. The stop came after the first `m(X)`'s step answered, so that
                    // `m(X)` is expanded, and the second one is expanded instead of merged: one
                    // more expanded state than the unstopped run, over as many visits.
                    ("t", true) => {
                        stopped_after_the_step = true;
                        assert_eq!(
                            (result.work, result.expanded),
                            (unstopped.work, unstopped.expanded + 1),
                            "query {nth}: {result:#?}"
                        );
                    }
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
                        stops: 0,
                        arrivals: 0,
                        arriving: None,
                        probing: None,
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
            stops: 0,
            arrivals: 0,
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

    /// The initial disjunction `[done, done, stuck(X) where X > 0]` of `prelude_definition`, the
    /// states `names` picks from it in that order.
    fn done_and_stuck(definition: &BackendDefinition, names: &[&str]) -> Vec<Pattern> {
        let term = |source: &str| {
            definition
                .internalize_term(&parse_pattern(source).expect("term should parse"), &[])
                .expect("term should internalize")
        };
        names
            .iter()
            .map(|name| match *name {
                "done" => Pattern {
                    term: term("done{}()"),
                    constraints: Vec::new(),
                },
                _ => Pattern {
                    term: term("stuck{}(X:SortInt{})"),
                    constraints: vec![Predicate::Equals(
                        term(r#"gtInt{}(X:SortInt{}, \dv{SortInt{}}("0"))"#),
                        term(r#"\dv{SortBool{}}("true")"#),
                    )],
                },
            })
            .collect()
    }

    /// Run `initial` of `prelude_definition` with `options` and `solver` in `token`'s scope,
    /// with the number of final merges it did.
    fn run_in_scope(
        definition: &BackendDefinition,
        initial: Vec<Pattern>,
        options: ExecutionOptions,
        solver: &dyn SmtSolver,
        token: &crate::stop::CancellationToken,
    ) -> (ExecutionResult, usize) {
        let merges = FINAL_MERGES.with(std::cell::Cell::get);
        let result = token.scope(|| {
            super::super::execute_disjunction_with_solver_and_observer(
                definition,
                initial,
                options,
                solver,
                |_| {},
            )
        });
        (result, FINAL_MERGES.with(std::cell::Cell::get) - merges)
    }

    /// A run with `max_breadth` 0 visits no state and drains every initial state as a
    /// breadth-bound leaf. Under `discard_stopped` the drain polls, so a cancellation of the
    /// request discards the leaves and becomes the run's cause; without it the same run in the
    /// same cancelled scope returns the drained leaves and no cause.
    #[test]
    fn a_cancellation_observed_by_the_breadth_drain_discards_its_leaves_when_asked_to() {
        let definition = prelude_definition();
        let initial = done_and_stuck(&definition, &["done", "stuck", "done"]);
        let token = crate::stop::CancellationToken::new();
        token.cancel();
        // Path-set, so that no final merge polls after the drain.
        let options = |discard_stopped| ExecutionOptions {
            max_breadth: Some(0),
            discard_stopped,
            result_modality: ResultModality::PathSet,
            ..ExecutionOptions::default()
        };
        let (discarded, _) = run_in_scope(
            &definition,
            initial.clone(),
            options(true),
            &crate::smt::NoSolver,
            &token,
        );
        assert_eq!(discarded.leaves, []);
        assert_eq!(discarded.stopped, Some(StopCause::Cancelled));
        let (kept, _) = run_in_scope(
            &definition,
            initial,
            options(false),
            &crate::smt::NoSolver,
            &token,
        );
        assert_eq!(kept.stopped, None);
        assert_eq!(
            kept.leaves
                .iter()
                .map(|leaf| leaf.halt_reason.clone())
                .collect::<Vec<_>>(),
            [
                HaltReason::BreadthBound,
                HaltReason::BreadthBound,
                HaltReason::BreadthBound
            ]
        );
    }

    /// A cancellation only the final merge observes: `stuck`'s normalisation, the last state's,
    /// asks the solver, which cancels the request; the refinement sets the stop aside and the run
    /// ends by itself with nothing pending. Under `discard_stopped` the state-set final merge
    /// polls (`selected_leaves` passes it `run_ending_stop`), so it discards the leaves and the
    /// cancellation becomes the run's cause; without it the run returns its leaves after one
    /// unpolled merge, with no cause.
    #[test]
    fn a_cancellation_only_the_final_merge_observes_discards_the_leaves_when_asked_to() {
        let definition = prelude_definition();
        let initial = done_and_stuck(&definition, &["done", "done", "stuck"]);
        let run = |discard_stopped| {
            let token = crate::stop::CancellationToken::new();
            let solver = CancelOnFirstQuery {
                token: token.clone(),
            };
            run_in_scope(
                &definition,
                initial.clone(),
                ExecutionOptions {
                    discard_stopped,
                    ..ExecutionOptions::default()
                },
                &solver,
                &token,
            )
        };
        let (discarded, _) = run(true);
        assert_eq!(discarded.leaves, []);
        assert_eq!(discarded.stopped, Some(StopCause::Cancelled));
        let (kept, merges) = run(false);
        assert_eq!(kept.stopped, None);
        assert_eq!(merges, 1);
        assert_eq!(
            kept.leaves
                .iter()
                .map(|leaf| leaf.halt_reason.clone())
                .collect::<Vec<_>>(),
            [HaltReason::Stuck, HaltReason::Stuck]
        );
    }

    /// A stop condition asked at each arrival at a stop (`stop_condition`), on a run of `0` to
    /// `6` by alternating selected `tick-*` and unselected `work-*` steps; with `choice`, `3`
    /// also has a selected `tick-x` successor beside `work-b` (a passed stop under strategy
    /// `all`), and `4x` goes on to `5` by `work-x`, so two paths meet at `5` at depth 5 with
    /// different arrivals.
    mod stop_condition {
        use super::*;
        use crate::rewrite::{StopArrival, StopConditionRefusal, StopDecision, StopSide};

        /// The stop states a condition was asked about, with their side and depth, in order.
        type Asked = Vec<(StopSide, u64, String)>;

        pub(super) fn steps(choice: bool) -> BackendDefinition {
            steps_then(choice, "")
        }

        /// [`steps`], with the axioms `then` besides.
        pub(super) fn steps_then(choice: bool, then: &str) -> BackendDefinition {
            let step = |from: &str, to: &str, label: &str| {
                format!(
                    r#"axiom{{}} \rewrites{{SortS{{}}}}(
                        \and{{SortS{{}}}}(\dv{{SortS{{}}}}("{from}"), \top{{SortS{{}}}}()),
                        \dv{{SortS{{}}}}("{to}")
                    ) [label{{}}("{label}")]"#
                )
            };
            let mut axioms = vec![
                step("0", "1", "tick-a"),
                step("1", "2", "work-a"),
                step("2", "3", "tick-b"),
                step("3", "4", "work-b"),
                step("4", "5", "tick-c"),
                step("5", "6", "work-c"),
            ];
            if choice {
                axioms.push(step("3", "4x", "tick-x"));
                axioms.push(step("4x", "5", "work-x"));
            }
            axioms.push(then.to_owned());
            definition(&axioms.join("\n"))
        }

        pub(super) fn state(definition: &BackendDefinition, value: &str) -> Pattern {
            Pattern {
                term: definition
                    .internalize_term(
                        &parse_pattern(&format!(r#"\dv{{SortS{{}}}}("{value}")"#)).unwrap(),
                        &[],
                    )
                    .unwrap(),
                constraints: Vec::new(),
            }
        }

        /// The value of a stop state of this definition.
        fn value(arrival: &StopArrival<'_>) -> String {
            match &arrival.configuration() {
                k_rust_kore::kore::ast::Pattern::DomainValue { value, .. } => {
                    value.as_utf8().unwrap().to_owned()
                }
                other => panic!("{other:?}"),
            }
        }

        fn options(terminal: bool, count: u64) -> ExecutionOptions {
            let selected =
                BTreeSet::from(["tick-a", "tick-b", "tick-c", "tick-x"].map(str::to_owned));
            let (cut_point_rules, terminal_rules) = if terminal {
                (BTreeSet::new(), selected)
            } else {
                (selected, BTreeSet::new())
            };
            ExecutionOptions {
                cut_point_rules,
                terminal_rules,
                stop_count: NonZeroU64::new(count).unwrap(),
                ..ExecutionOptions::default()
            }
        }

        /// A run under `options` from `0` whose condition holds of the stop states `holds`,
        /// is undecided at `undecided` and refuses at `refused`; also the stop states it was
        /// asked about, with their side and depth, in order.
        fn run(
            definition: &BackendDefinition,
            options: ExecutionOptions,
            holds: &[&str],
            undecided: &[&str],
            refused: &[&str],
        ) -> (Result<ExecutionResult, StopConditionRefusal>, Asked) {
            let mut asked = Vec::new();
            let mut condition = |arrival: &StopArrival<'_>| {
                let value = value(arrival);
                asked.push((arrival.side(), arrival.depth(), value.clone()));
                if undecided.contains(&value.as_str()) {
                    StopDecision::Undecided(format!("undecided at {value}"))
                } else if refused.contains(&value.as_str()) {
                    StopDecision::Refused(format!("no value at {value}"))
                } else if holds.contains(&value.as_str()) {
                    StopDecision::Holds
                } else {
                    StopDecision::Fails
                }
            };
            let result = crate::rewrite::execute_with_stop_condition(
                definition,
                state(definition, "0"),
                options,
                &crate::smt::NoSolver,
                None,
                &mut condition,
            );
            (result, asked)
        }

        /// Each leaf's value, depth, halt, stop events and arrivals.
        fn ends(result: &ExecutionResult) -> Vec<(String, u64, &'static str, u64, u64)> {
            let mut ends = result
                .leaves
                .iter()
                .map(|leaf| {
                    let value = match &crate::externalize::term(&leaf.pattern.term) {
                        k_rust_kore::kore::ast::Pattern::DomainValue { value, .. } => {
                            value.as_utf8().unwrap().to_owned()
                        }
                        other => format!("{other:?}"),
                    };
                    let halt = match &leaf.halt_reason {
                        HaltReason::StopUndecided { .. } => "stop-undecided",
                        halt => halt_name(halt),
                    };
                    (value, leaf.depth, halt, leaf.stops, leaf.arrivals)
                })
                .collect::<Vec<_>>();
            ends.sort();
            ends
        }

        #[test]
        fn a_failed_condition_takes_the_arrival_as_a_step() {
            let definition = steps(false);
            // Before: the arrival at `0` fails and is stepped; the one at `2` holds and ends.
            let (result, _) = run(&definition, options(false, 1), &["2"], &[], &[]);
            assert_eq!(ends(&result.unwrap()), [("2".into(), 2, "stop", 1, 2)]);
            // After: the arrival at `1` fails and the path goes on; the one at `3` holds.
            let (result, _) = run(&definition, options(true, 1), &["3"], &[], &[]);
            assert_eq!(ends(&result.unwrap()), [("3".into(), 3, "stop", 1, 2)]);
            // A condition that never holds: the run ends on its own, past every arrival.
            for terminal in [false, true] {
                let (result, _) = run(&definition, options(terminal, 1), &[], &[], &[]);
                assert_eq!(ends(&result.unwrap()), [("6".into(), 6, "stuck", 0, 3)]);
            }
        }

        #[test]
        fn the_count_counts_arrivals_where_the_condition_holds() {
            let definition = steps(false);
            let (result, _) = run(&definition, options(false, 2), &["0", "4"], &[], &[]);
            assert_eq!(ends(&result.unwrap()), [("4".into(), 4, "stop", 2, 3)]);
            let (result, _) = run(&definition, options(true, 2), &["1", "5"], &[], &[]);
            assert_eq!(ends(&result.unwrap()), [("5".into(), 5, "stop", 2, 3)]);
            // Fewer events than the count: the run ends on its own, having counted them.
            let (result, _) = run(&definition, options(false, 3), &["0", "4"], &[], &[]);
            assert_eq!(ends(&result.unwrap()), [("6".into(), 6, "stuck", 2, 3)]);
        }

        /// A condition that holds everywhere is no condition: the same leaves, each arrival an
        /// event.
        #[test]
        fn a_condition_that_always_holds_changes_nothing() {
            let definition = steps(true);
            for terminal in [false, true] {
                for count in 1..=4 {
                    for mode in [ExecutionMode::Any, ExecutionMode::All] {
                        let options = ExecutionOptions {
                            mode,
                            retain_trace: true,
                            ..options(terminal, count)
                        };
                        let plain = super::super::super::execute(
                            &definition,
                            state(&definition, "0"),
                            options.clone(),
                        );
                        let all = ["0", "1", "2", "3", "4", "4x", "5", "6"];
                        let (asked, _) = run(&definition, options.clone(), &all, &[], &[]);
                        // The same work too: the condition is asked within the step, of a
                        // successor normalized there, and costs the run no state visit, so a
                        // work bound the run without it meets exactly cuts neither run short.
                        let asked = asked.unwrap();
                        assert_eq!(asked, plain, "terminal={terminal} count={count} {mode:?}");
                        assert!(asked.leaves.iter().all(|leaf| leaf.arrivals == leaf.stops));
                        let bounded = ExecutionOptions {
                            max_work: Some(plain.work),
                            ..options
                        };
                        let (asked, _) = run(&definition, bounded.clone(), &all, &[], &[]);
                        let plain = super::super::super::execute(
                            &definition,
                            state(&definition, "0"),
                            bounded,
                        );
                        assert!(
                            plain
                                .leaves
                                .iter()
                                .all(|leaf| leaf.halt_reason != HaltReason::WorkBound)
                        );
                        assert_eq!(
                            asked.unwrap(),
                            plain,
                            "terminal={terminal} count={count} {mode:?} max_work"
                        );
                    }
                }
            }
        }

        #[test]
        fn a_before_condition_reads_the_state_and_an_after_condition_the_successor() {
            let definition = steps(false);
            let (_, asked) = run(&definition, options(false, 1), &[], &[], &[]);
            assert_eq!(
                asked,
                [
                    (StopSide::Before, 0, "0".into()),
                    (StopSide::Before, 2, "2".into()),
                    (StopSide::Before, 4, "4".into())
                ]
            );
            let (_, asked) = run(&definition, options(true, 1), &[], &[], &[]);
            assert_eq!(
                asked,
                [
                    (StopSide::After, 1, "1".into()),
                    (StopSide::After, 3, "3".into()),
                    (StopSide::After, 5, "5".into())
                ]
            );
        }

        /// The condition is asked once per arrival, and not at a stop rule's step that has
        /// another successor beside it (a passed stop) nor at any other step.
        #[test]
        fn the_condition_is_asked_only_at_arrivals() {
            let definition = steps(true);
            for terminal in [false, true] {
                let options = ExecutionOptions {
                    mode: ExecutionMode::All,
                    result_modality: ResultModality::PathSet,
                    ..options(terminal, 1)
                };
                let (result, asked) = run(&definition, options, &[], &[], &[]);
                let result = result.unwrap();
                let rule = |stop: &PassedStop| (stop.rule.clone(), stop.depth);
                assert_eq!(
                    result.passed_stops.iter().map(rule).collect::<Vec<_>>(),
                    [("tick-x".to_owned(), 3)]
                );
                let values = asked
                    .iter()
                    .map(|(_, _, value)| value.as_str())
                    .collect::<Vec<_>>();
                // Before: the arrivals at `0` and `2` are on both paths, the one at `4` on one;
                // after, `1`, `3` and `5`. The paths share their prefix, asked once.
                let expected = if terminal {
                    ["1", "3", "5"]
                } else {
                    ["0", "2", "4"]
                };
                assert_eq!(values, expected, "terminal={terminal}");
                // Each leaf counts the arrivals of its own path.
                assert_eq!(
                    ends(&result)
                        .iter()
                        .map(|(value, _, _, _, arrivals)| (value.clone(), *arrivals))
                        .collect::<Vec<_>>(),
                    [("6".to_owned(), 2), ("6".to_owned(), 3)]
                );
            }
        }

        /// Under strategy any the sequential step takes `tick-x`'s successor of `1`, its first
        /// rule, and never tries `work-x`; but `1` has two successors, so that step is no
        /// arrival and the condition is not asked there. The path goes on through it, and its
        /// arrivals are `tick-a`'s and `tick-b`'s.
        #[test]
        fn under_strategy_any_the_condition_is_not_asked_at_a_passed_stop() {
            let step = |from: &str, to: &str, label: &str| {
                format!(
                    r#"axiom{{}} \rewrites{{SortS{{}}}}(
                        \and{{SortS{{}}}}(\dv{{SortS{{}}}}("{from}"), \top{{SortS{{}}}}()),
                        \dv{{SortS{{}}}}("{to}")
                    ) [label{{}}("{label}")]"#
                )
            };
            let definition = definition(
                &[
                    step("0", "1", "tick-a"),
                    step("1", "2", "tick-x"),
                    step("1", "9", "work-x"),
                    step("2", "3", "tick-b"),
                ]
                .join("\n"),
            );
            for terminal in [false, true] {
                let options = ExecutionOptions {
                    mode: ExecutionMode::Any,
                    ..options(terminal, 1)
                };
                let (result, asked) = run(&definition, options.clone(), &[], &[], &[]);
                let result = result.unwrap();
                let values = asked
                    .iter()
                    .map(|(_, _, value)| value.as_str())
                    .collect::<Vec<_>>();
                let expected = if terminal { ["1", "3"] } else { ["0", "2"] };
                assert_eq!(values, expected, "terminal={terminal}");
                assert_eq!(ends(&result), [("3".into(), 3, "stuck", 0, 2)]);
                let rule = |stop: &PassedStop| (stop.rule.clone(), stop.depth);
                assert_eq!(
                    result.passed_stops.iter().map(rule).collect::<Vec<_>>(),
                    [("tick-x".to_owned(), 1)]
                );
                // A condition that holds at the passed stop's stop state, and at the next
                // arrival's: the run stops at that arrival, not at the passed stop.
                let (holds, stop) = if terminal {
                    (["2", "3"], ("3".into(), 3, "stop", 1, 2))
                } else {
                    (["1", "2"], ("2".into(), 2, "stop", 1, 2))
                };
                let (result, _) = run(&definition, options, &holds, &[], &[]);
                assert_eq!(ends(&result.unwrap()), [stop], "terminal={terminal}");
            }
        }

        /// A selected step whose one successor is undefined is no arrival: the condition is not
        /// asked of its stop state, whatever it would answer, and the path ends at the undefined
        /// step. `tick-d` takes `6` to `dead(7)`, which `dead`'s equation reduces to `\bottom`.
        #[test]
        fn the_condition_is_not_asked_at_a_step_without_a_defined_successor() {
            let definition = steps_then(
                false,
                r#"symbol dead{}(SortS{}) : SortS{} [function{}(), total{}()]
                axiom{R} \implies{R}(
                    \top{R}(),
                    \equals{SortS{}, R}(
                        dead{}(X:SortS{}),
                        \and{SortS{}}(\dv{SortS{}}("dead"), \bottom{SortS{}}())
                    )
                ) [label{}("dead"), simplification{}()]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(\dv{SortS{}}("6"), \top{SortS{}}()),
                    dead{}(\dv{SortS{}}("7"))
                ) [label{}("tick-d")]"#,
            );
            for terminal in [false, true] {
                // The count is reached at the first event, or not before the last arrival.
                for count in [1, 4] {
                    let mut options = options(terminal, count);
                    for selected in [&mut options.cut_point_rules, &mut options.terminal_rules] {
                        if !selected.is_empty() {
                            selected.insert("tick-d".to_owned());
                        }
                    }
                    // `6` would be undecided, were it asked.
                    let (result, asked) = run(&definition, options, &[], &["6"], &[]);
                    let values = asked
                        .iter()
                        .map(|(_, _, value)| value.as_str())
                        .collect::<Vec<_>>();
                    let expected = if terminal {
                        ["1", "3", "5"]
                    } else {
                        ["0", "2", "4"]
                    };
                    assert_eq!(values, expected, "terminal={terminal} count={count}");
                    let result = result.unwrap();
                    let [leaf] = result.leaves.as_slice() else {
                        panic!("one leaf: {:?}", result.leaves);
                    };
                    assert!(
                        matches!(leaf.halt_reason, HaltReason::Trivial { .. }),
                        "terminal={terminal} count={count}: {:?}",
                        leaf.halt_reason
                    );
                    assert_eq!(
                        ends(&result),
                        [("6".into(), 6, "other", 0, 3)],
                        "terminal={terminal} count={count}"
                    );
                }
            }
        }

        #[test]
        fn an_undecided_condition_ends_the_path_stop_undecided() {
            let definition = steps(false);
            let (result, _) = run(&definition, options(false, 1), &[], &["2"], &[]);
            let result = result.unwrap();
            assert_eq!(ends(&result), [("2".into(), 2, "stop-undecided", 0, 2)]);
            assert_eq!(
                result.leaves[0].halt_reason,
                HaltReason::StopUndecided {
                    rule: "tick-b".into(),
                    reason: "undecided at 2".into()
                }
            );
            let (result, _) = run(&definition, options(true, 1), &[], &["3"], &[]);
            assert_eq!(
                ends(&result.unwrap()),
                [("3".into(), 3, "stop-undecided", 0, 2)]
            );
            // An undecided answer short of the count still ends the path: it may be an event.
            let (result, _) = run(&definition, options(false, 3), &["0"], &["2"], &[]);
            assert_eq!(
                ends(&result.unwrap()),
                [("2".into(), 2, "stop-undecided", 1, 2)]
            );
        }

        #[test]
        fn a_refused_condition_fails_the_request() {
            let definition = steps(false);
            let (result, asked) = run(&definition, options(false, 1), &[], &[], &["2"]);
            assert_eq!(
                result,
                Err(StopConditionRefusal {
                    rule: "tick-b".into(),
                    side: StopSide::Before,
                    depth: 2,
                    reason: "no value at 2".into()
                })
            );
            // The run ends there: no later arrival is asked.
            assert_eq!(asked.len(), 2);
            let (result, _) = run(&definition, options(true, 1), &[], &[], &["5"]);
            assert_eq!(
                result.unwrap_err().to_string(),
                "the stop condition has no value at the arrival after `tick-c` at depth 5: no value at 5"
            );
        }

        /// Under `state-set` a state merges only into one of the same events and arrivals: the
        /// paths meet at `5` at depth 5 with as many events (the arrival at `4` fails) and
        /// different arrivals, and their leaves stay apart, as under `path-set`.
        #[test]
        fn state_set_with_a_condition_equals_path_set() {
            let definition = steps(true);
            let holds_cases: [&[&str]; 4] = [&[], &["0", "2"], &["2", "4"], &["1", "5"]];
            for terminal in [false, true] {
                for count in 1..=3 {
                    for holds in holds_cases {
                        let run_in = |result_modality| {
                            let options = ExecutionOptions {
                                mode: ExecutionMode::All,
                                result_modality,
                                ..options(terminal, count)
                            };
                            ends(&run(&definition, options, holds, &[], &[]).0.unwrap())
                        };
                        assert_eq!(
                            run_in(ResultModality::StateSet),
                            run_in(ResultModality::PathSet),
                            "terminal={terminal} count={count} holds={holds:?}"
                        );
                    }
                }
            }
        }

        /// The condition's work is not the run's: it runs off the step clock, in a proof scope,
        /// with its own operation record and poll budget, reporting to no coverage set of the
        /// run, and the run's result is the one without that work.
        #[test]
        fn the_condition_runs_off_the_step_clock_in_its_own_operation() {
            let definition = steps(false);
            let options = ExecutionOptions {
                evaluation: crate::evaluation::EvaluationMode::Execution,
                collect_coverage: true,
                ..options(false, 1)
            };
            let mut inside = Vec::new();
            let mut condition = |arrival: &StopArrival<'_>| {
                let mode = crate::evaluation::current();
                crate::coverage::note_matched("condition-work");
                let ((spent, ()), record) = crate::stop::with_operation_record(|| {
                    crate::stop::dismiss_a_stack_stop();
                    let ((), budget) = crate::stop::with_poll_budget(
                        2,
                        crate::timeout::StepTimeoutMode::Manual(std::time::Duration::ZERO),
                        || {
                            // The stop is the condition's own, which it dismisses.
                            loop {
                                if let Err(stop) = crate::stop::check() {
                                    stop.forgo_refinement();
                                    break;
                                }
                            }
                        },
                    );
                    (budget.budget_exhausted, ())
                });
                std::thread::sleep(std::time::Duration::from_millis(5));
                inside.push((mode, spent, record.stack_stops));
                if value(arrival) == "2" {
                    StopDecision::Holds
                } else {
                    StopDecision::Fails
                }
            };
            let off_before = crate::stop::time_off_the_clock();
            let result = crate::rewrite::execute_with_stop_condition(
                &definition,
                state(&definition, "0"),
                options.clone(),
                &crate::smt::NoSolver,
                None,
                &mut condition,
            )
            .unwrap();
            let off = crate::stop::time_off_the_clock() - off_before;
            assert_eq!(
                inside,
                [
                    (crate::evaluation::EvaluationMode::Proof, true, 1),
                    (crate::evaluation::EvaluationMode::Proof, true, 1)
                ]
            );
            assert!(off >= std::time::Duration::from_millis(10), "{off:?}");
            assert_eq!(result.stack_stops, 0);
            assert_eq!(result.stopped, None);
            assert!(
                !result
                    .coverage
                    .as_ref()
                    .unwrap()
                    .matched
                    .contains("condition-work")
            );
            assert_eq!(ends(&result), [("2".into(), 2, "stop", 1, 2)]);
        }

        /// A cell is read by its path of cell symbols from the configuration's top, each a direct
        /// argument of the one before; nothing else of the configuration is converted.
        #[test]
        fn a_cell_is_read_by_its_path() {
            let source = r#"[]
                module MAIN
                    sort SortS{} [hasDomainValues{}()]
                    sort SortT{} []
                    sort SortC{} []
                    symbol top{}(SortC{}, SortC{}) : SortT{} [constructor{}(), functional{}(), injective{}()]
                    symbol left{}(SortS{}) : SortC{} [constructor{}(), functional{}(), injective{}()]
                    symbol right{}(SortS{}) : SortC{} [constructor{}(), functional{}(), injective{}()]
                    axiom{} \rewrites{SortT{}}(
                        \and{SortT{}}(top{}(left{}(\dv{SortS{}}("0")), right{}(\dv{SortS{}}("r"))), \top{SortT{}}()),
                        top{}(left{}(\dv{SortS{}}("1")), right{}(\dv{SortS{}}("r")))
                    ) [label{}("tick")]
                endmodule []"#;
            let syntax = parse_definition(source).unwrap();
            let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
            let start = Pattern {
                term: definition
                    .internalize_term(
                        &parse_pattern(
                            r#"top{}(left{}(\dv{SortS{}}("0")), right{}(\dv{SortS{}}("r")))"#,
                        )
                        .unwrap(),
                        &[],
                    )
                    .unwrap(),
                constraints: Vec::new(),
            };
            let mut read = Vec::new();
            let mut condition = |arrival: &StopArrival<'_>| {
                read.push((
                    arrival.cell(&["top", "left"]).map(|cell| cell.to_string()),
                    arrival.cell(&["top", "right"]).map(|cell| cell.to_string()),
                    arrival.cell(&["left"]),
                    arrival.cell(&["top", "middle"]),
                ));
                StopDecision::Holds
            };
            let result = crate::rewrite::execute_with_stop_condition(
                &definition,
                start,
                ExecutionOptions {
                    cut_point_rules: BTreeSet::from(["tick".to_owned()]),
                    ..ExecutionOptions::default()
                },
                &crate::smt::NoSolver,
                None,
                &mut condition,
            )
            .unwrap();
            assert_eq!(result.leaves.len(), 1);
            assert_eq!(
                read,
                [(
                    Some(r#"left{}(\dv{SortS{}}("0"))"#.to_owned()),
                    Some(r#"right{}(\dv{SortS{}}("r"))"#.to_owned()),
                    None,
                    None
                )]
            );
        }
    }

    /// A probe asked at the points of selected rules (`probe`), on the stop condition's run of
    /// `0` to `6` by alternating `tick-*` and `work-*` steps; with `choice`, `3` also has a
    /// `tick-x` successor beside `work-b`.
    mod probe {
        use std::cell::RefCell;

        use super::stop_condition::{state, steps, steps_then};
        use super::*;
        use crate::rewrite::{
            Probe, ProbeArrival, ProbeCycle, ProbeDecision, ProbeLeaf, ProbeRules, ProbeState,
            StateMatchOptions, StopArrival, StopDecision, StopSide,
        };

        /// What a probe was asked, in order.
        #[derive(Clone, Debug, Eq, PartialEq)]
        enum Asked {
            /// A point: its side, the observed state's depth and value, and its rule.
            Point(StopSide, u64, String, String),
            /// The path split at the state of this depth.
            Branched(u64),
            /// The path ended at a leaf of this depth, value and halt.
            Ended(u64, String, &'static str),
            /// A stop condition was asked about the stop state of this value.
            Condition(String),
        }

        fn value(state: &ProbeState<'_>) -> String {
            match state.configuration() {
                k_rust_kore::kore::ast::Pattern::DomainValue { ref value, .. } => {
                    value.as_utf8().unwrap().to_owned()
                }
                other => format!("{other:?}"),
            }
        }

        fn halt(halt: &HaltReason) -> &'static str {
            match halt {
                HaltReason::CutPointRule { .. } => "cut-point",
                HaltReason::TerminalRule { .. } => "terminal",
                HaltReason::Stuck => "stuck",
                HaltReason::Trivial { .. } => "trivial",
                HaltReason::Branch { .. } => "branch",
                HaltReason::DepthBound => "depth-bound",
                HaltReason::WorkBound => "work-bound",
                HaltReason::ProbeDifference { .. } => "probe-difference",
                HaltReason::ProbeDone { .. } => "probe-done",
                _ => "other",
            }
        }

        /// A probe that records what it is asked into `log` and answers `answers` (by the
        /// observed state's value and side), else continues.
        struct Recorder<'a> {
            log: &'a RefCell<Vec<Asked>>,
            answers: Vec<(String, StopSide, ProbeDecision)>,
        }

        impl Probe for Recorder<'_> {
            fn observe(&mut self, point: &ProbeArrival<'_>) -> ProbeDecision {
                let value = value(point);
                self.log.borrow_mut().push(Asked::Point(
                    point.side(),
                    point.depth(),
                    value.clone(),
                    point.rule().to_owned(),
                ));
                self.answers
                    .iter()
                    .find(|(answer, side, _)| *answer == value && *side == point.side())
                    .map_or(ProbeDecision::Continue, |(_, _, decision)| decision.clone())
            }

            fn branched(&mut self, depth: u64) {
                self.log.borrow_mut().push(Asked::Branched(depth));
            }

            fn ended(&mut self, leaf: &ProbeLeaf<'_>) {
                self.log.borrow_mut().push(Asked::Ended(
                    leaf.depth(),
                    value(leaf),
                    halt(leaf.halt()),
                ));
            }
        }

        fn names(names: &[&str]) -> BTreeSet<String> {
            names.iter().map(|name| (*name).to_owned()).collect()
        }

        fn probing(before: &[&str], after: &[&str]) -> ExecutionOptions {
            ExecutionOptions {
                probe_rules: ProbeRules {
                    before: names(before),
                    after: names(after),
                },
                ..ExecutionOptions::default()
            }
        }

        fn point(side: StopSide, depth: u64, value: &str, rule: &str) -> Asked {
            Asked::Point(side, depth, value.to_owned(), rule.to_owned())
        }

        fn ended(depth: u64, value: &str, halt: &'static str) -> Asked {
            Asked::Ended(depth, value.to_owned(), halt)
        }

        /// A run from `0` under `options` with a probe answering `answers`; also what it asked.
        fn run(
            definition: &BackendDefinition,
            options: ExecutionOptions,
            answers: &[(&str, StopSide, ProbeDecision)],
        ) -> (ExecutionResult, Vec<Asked>) {
            let log = RefCell::new(Vec::new());
            let mut probe = Recorder {
                log: &log,
                answers: answers
                    .iter()
                    .map(|(value, side, decision)| ((*value).to_owned(), *side, decision.clone()))
                    .collect(),
            };
            let result = crate::rewrite::execute_with_probe(
                definition,
                state(definition, "0"),
                options,
                &crate::smt::NoSolver,
                None,
                None,
                &mut probe,
            )
            .unwrap();
            (result, log.into_inner())
        }

        /// Each leaf's value, depth and halt.
        fn ends(result: &ExecutionResult) -> Vec<(String, u64, &'static str)> {
            result
                .leaves
                .iter()
                .map(|leaf| {
                    let state = ProbeState {
                        depth: leaf.depth,
                        term: &leaf.pattern.term,
                    };
                    (value(&state), leaf.depth, halt(&leaf.halt_reason))
                })
                .collect()
        }

        #[test]
        fn a_probe_is_asked_at_each_taken_step_of_a_point_rule_before_and_after() {
            let definition = steps(false);
            for mode in [ExecutionMode::All, ExecutionMode::Any] {
                for branch_mode in [
                    ExecutionBranchMode::ExploreAll,
                    ExecutionBranchMode::StopAtBranch,
                ] {
                    let options = ExecutionOptions {
                        mode,
                        branch_mode,
                        ..probing(&["tick-a", "tick-b", "tick-c"], &["work-a", "tick-b"])
                    };
                    let (result, asked) = run(&definition, options, &[]);
                    assert_eq!(
                        asked,
                        [
                            point(StopSide::Before, 0, "0", "tick-a"),
                            point(StopSide::After, 2, "2", "work-a"),
                            // One rule on both sides: before, then after.
                            point(StopSide::Before, 2, "2", "tick-b"),
                            point(StopSide::After, 3, "3", "tick-b"),
                            point(StopSide::Before, 4, "4", "tick-c"),
                            ended(6, "6", "stuck"),
                        ],
                        "{mode:?} {branch_mode:?}"
                    );
                    assert_eq!(ends(&result), [("6".into(), 6, "stuck")]);
                }
            }
        }

        /// No unselected rule's step is a point, and neither is a selected step whose one
        /// successor is undefined: `tick-d` takes `6` to `dead(7)`, which `dead`'s equation
        /// reduces to `\bottom`. The path ends at the undefined step, which the probe is told.
        #[test]
        fn not_at_other_steps_nor_at_an_undefined_successor() {
            let definition = steps_then(
                false,
                r#"symbol dead{}(SortS{}) : SortS{} [function{}(), total{}()]
                axiom{R} \implies{R}(
                    \top{R}(),
                    \equals{SortS{}, R}(
                        dead{}(X:SortS{}),
                        \and{SortS{}}(\dv{SortS{}}("dead"), \bottom{SortS{}}())
                    )
                ) [label{}("dead"), simplification{}()]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(\dv{SortS{}}("6"), \top{SortS{}}()),
                    dead{}(\dv{SortS{}}("7"))
                ) [label{}("tick-d")]"#,
            );
            let (result, asked) = run(
                &definition,
                probing(&["tick-a", "tick-d"], &["tick-d"]),
                &[],
            );
            assert_eq!(
                asked,
                [
                    point(StopSide::Before, 0, "0", "tick-a"),
                    ended(6, "6", "trivial"),
                ]
            );
            assert_eq!(ends(&result), [("6".into(), 6, "trivial")]);
        }

        /// The stop's `stop_count`th event of a cut-point rule is not taken, so it has no point;
        /// an earlier arrival is a step like any other, and a terminal rule's last step is
        /// taken, so its points are asked before the path ends there.
        #[test]
        fn a_before_stop_nth_event_emits_no_point() {
            let definition = steps(false);
            let (result, asked) = run(
                &definition,
                ExecutionOptions {
                    cut_point_rules: names(&["tick-b"]),
                    ..probing(&["tick-a", "tick-b"], &["tick-b"])
                },
                &[],
            );
            assert_eq!(
                asked,
                [
                    point(StopSide::Before, 0, "0", "tick-a"),
                    ended(2, "2", "cut-point"),
                ]
            );
            assert_eq!(ends(&result), [("2".into(), 2, "cut-point")]);
            // The second arrival ends the path: the first is taken, and is a point.
            let (_, asked) = run(
                &definition,
                ExecutionOptions {
                    cut_point_rules: names(&["tick-a", "tick-b"]),
                    stop_count: NonZeroU64::new(2).unwrap(),
                    ..probing(&["tick-a", "tick-b"], &["tick-a", "tick-b"])
                },
                &[],
            );
            assert_eq!(
                asked,
                [
                    point(StopSide::Before, 0, "0", "tick-a"),
                    point(StopSide::After, 1, "1", "tick-a"),
                    ended(2, "2", "cut-point"),
                ]
            );
            let (result, asked) = run(
                &definition,
                ExecutionOptions {
                    terminal_rules: names(&["tick-b"]),
                    ..probing(&["tick-b"], &["tick-b"])
                },
                &[],
            );
            assert_eq!(
                asked,
                [
                    point(StopSide::Before, 2, "2", "tick-b"),
                    point(StopSide::After, 3, "3", "tick-b"),
                    ended(3, "3", "terminal"),
                ]
            );
            assert_eq!(ends(&result), [("3".into(), 3, "terminal")]);
        }

        #[test]
        fn differs_ends_the_request_with_its_observed_state() {
            let definition = steps(false);
            let options = || probing(&["tick-b"], &["work-b"]);
            let differs = ProbeDecision::Differs("two".to_owned());
            let (result, asked) = run(
                &definition,
                options(),
                &[("2", StopSide::Before, differs.clone())],
            );
            // Nothing is asked after the difference, and the probe is not told of its own end.
            assert_eq!(asked, [point(StopSide::Before, 2, "2", "tick-b")]);
            assert_eq!(ends(&result), [("2".into(), 2, "probe-difference")]);
            assert_eq!(
                result.leaves[0].halt_reason,
                HaltReason::ProbeDifference {
                    rule: "tick-b".into(),
                    side: StopSide::Before,
                    reason: "two".into()
                }
            );
            // After: the leaf is the normalized successor.
            let (result, asked) = run(&definition, options(), &[("4", StopSide::After, differs)]);
            assert_eq!(
                asked,
                [
                    point(StopSide::Before, 2, "2", "tick-b"),
                    point(StopSide::After, 4, "4", "work-b"),
                ]
            );
            assert_eq!(ends(&result), [("4".into(), 4, "probe-difference")]);
        }

        #[test]
        fn done_ends_the_path() {
            let definition = steps(false);
            let options = || probing(&["tick-b"], &["tick-b", "tick-c"]);
            let (result, asked) = run(
                &definition,
                options(),
                &[("3", StopSide::After, ProbeDecision::Done)],
            );
            assert_eq!(
                asked,
                [
                    point(StopSide::Before, 2, "2", "tick-b"),
                    point(StopSide::After, 3, "3", "tick-b"),
                ]
            );
            assert_eq!(ends(&result), [("3".into(), 3, "probe-done")]);
            assert_eq!(
                result.leaves[0].halt_reason,
                HaltReason::ProbeDone {
                    rule: "tick-b".into(),
                    side: StopSide::After
                }
            );
            // Before: the leaf is the state before the step, and the after point is not asked.
            let (result, asked) = run(
                &definition,
                options(),
                &[("2", StopSide::Before, ProbeDecision::Done)],
            );
            assert_eq!(asked, [point(StopSide::Before, 2, "2", "tick-b")]);
            assert_eq!(ends(&result), [("2".into(), 2, "probe-done")]);
        }

        /// `3` has two successors: the probe is told once, at `3`, and asked nothing after,
        /// neither at the points of either path nor at their ends.
        #[test]
        fn branched_is_asked_once_at_the_first_state_with_two_successors() {
            let definition = steps(true);
            let before = ["tick-a", "tick-b", "tick-c", "tick-x"];
            for result_modality in [ResultModality::PathSet, ResultModality::StateSet] {
                let options = ExecutionOptions {
                    result_modality,
                    ..probing(&before, &["work-x", "work-b"])
                };
                let (_, asked) = run(&definition, options, &[]);
                assert_eq!(
                    asked,
                    [
                        point(StopSide::Before, 0, "0", "tick-a"),
                        point(StopSide::Before, 2, "2", "tick-b"),
                        Asked::Branched(3),
                    ],
                    "{result_modality:?}"
                );
            }
            // A branch leaf reports the state's successors: the path splits there.
            let options = ExecutionOptions {
                branch_mode: ExecutionBranchMode::StopAtBranch,
                ..probing(&before, &[])
            };
            let (result, asked) = run(&definition, options, &[]);
            assert_eq!(
                asked,
                [
                    point(StopSide::Before, 0, "0", "tick-a"),
                    point(StopSide::Before, 2, "2", "tick-b"),
                    Asked::Branched(3),
                ]
            );
            assert_eq!(ends(&result), [("3".into(), 3, "branch")]);
        }

        /// A probe that always continues is no probe: the same result, coverage, traces and
        /// work included, under every strategy, branch mode, result modality and stop rule,
        /// and a work bound the run without it meets exactly cuts neither short.
        #[test]
        fn a_continue_probe_leaves_leaves_coverage_and_work_unchanged() {
            let all = [
                "tick-a", "tick-b", "tick-c", "tick-x", "work-a", "work-b", "work-c", "work-x",
            ];
            let stops: [(&[&str], &[&str], u64); 4] = [
                (&[], &[], 1),
                (&["tick-b"], &[], 1),
                (&[], &["tick-b"], 1),
                (&["tick-a", "tick-b", "tick-c"], &[], 2),
            ];
            for choice in [false, true] {
                let definition = steps(choice);
                for mode in [ExecutionMode::All, ExecutionMode::Any] {
                    for branch_mode in [
                        ExecutionBranchMode::ExploreAll,
                        ExecutionBranchMode::StopAtBranch,
                    ] {
                        for result_modality in [ResultModality::StateSet, ResultModality::PathSet] {
                            for (cut, terminal, count) in stops {
                                let options = ExecutionOptions {
                                    mode,
                                    branch_mode,
                                    result_modality,
                                    cut_point_rules: names(cut),
                                    terminal_rules: names(terminal),
                                    stop_count: NonZeroU64::new(count).unwrap(),
                                    retain_trace: true,
                                    collect_coverage: true,
                                    collect_counts: true,
                                    collect_committed: true,
                                    ..probing(&all, &all)
                                };
                                let context = format!(
                                    "choice={choice} {mode:?} {branch_mode:?} \
                                     {result_modality:?} cut={cut:?} terminal={terminal:?} \
                                     count={count}"
                                );
                                let plain = crate::rewrite::execute(
                                    &definition,
                                    state(&definition, "0"),
                                    options.clone(),
                                );
                                let (probed, _) = run(&definition, options.clone(), &[]);
                                assert!(plain.coverage.is_some(), "{context}");
                                assert_eq!(probed, plain, "{context}");
                                let bounded = ExecutionOptions {
                                    max_work: Some(plain.work),
                                    ..options
                                };
                                let plain = crate::rewrite::execute(
                                    &definition,
                                    state(&definition, "0"),
                                    bounded.clone(),
                                );
                                assert!(
                                    plain
                                        .leaves
                                        .iter()
                                        .all(|leaf| leaf.halt_reason != HaltReason::WorkBound),
                                    "{context}"
                                );
                                let (probed, _) = run(&definition, bounded, &[]);
                                assert_eq!(probed, plain, "{context} max_work");
                            }
                        }
                    }
                }
            }
        }

        /// `top(left(N), right(R))`: `tick-0` and `tick-1` rewrite `left` and keep `right` by a
        /// variable, so the cell `right` is the same node at both points, and `left` is not.
        #[test]
        fn cell_handle_is_stable_for_an_unchanged_cell() {
            let source = r#"[]
                module MAIN
                    sort SortS{} [hasDomainValues{}()]
                    sort SortT{} []
                    sort SortC{} []
                    symbol top{}(SortC{}, SortC{}) : SortT{} [constructor{}(), functional{}(), injective{}()]
                    symbol left{}(SortS{}) : SortC{} [constructor{}(), functional{}(), injective{}()]
                    symbol right{}(SortS{}) : SortC{} [constructor{}(), functional{}(), injective{}()]
                    axiom{} \rewrites{SortT{}}(
                        \and{SortT{}}(top{}(left{}(\dv{SortS{}}("0")), R:SortC{}), \top{SortT{}}()),
                        top{}(left{}(\dv{SortS{}}("1")), R:SortC{})
                    ) [label{}("tick-0")]
                    axiom{} \rewrites{SortT{}}(
                        \and{SortT{}}(top{}(left{}(\dv{SortS{}}("1")), R:SortC{}), \top{SortT{}}()),
                        top{}(left{}(\dv{SortS{}}("2")), R:SortC{})
                    ) [label{}("tick-1")]
                endmodule []"#;
            let syntax = parse_definition(source).unwrap();
            let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
            let start = Pattern {
                term: definition
                    .internalize_term(
                        &parse_pattern(
                            r#"top{}(left{}(\dv{SortS{}}("0")), right{}(\dv{SortS{}}("r")))"#,
                        )
                        .unwrap(),
                        &[],
                    )
                    .unwrap(),
                constraints: Vec::new(),
            };
            struct Handles(Vec<(crate::rewrite::CellHandle, crate::rewrite::CellHandle)>);
            impl Probe for Handles {
                fn observe(&mut self, point: &ProbeArrival<'_>) -> ProbeDecision {
                    assert!(point.cell_handle(&["top", "middle"]).is_none());
                    self.0.push((
                        point.cell_handle(&["top", "left"]).unwrap(),
                        point.cell_handle(&["top", "right"]).unwrap(),
                    ));
                    ProbeDecision::Continue
                }

                fn ended(&mut self, _: &ProbeLeaf<'_>) {}
            }
            let mut handles = Handles(Vec::new());
            crate::rewrite::execute_with_probe(
                &definition,
                start,
                probing(&[], &["tick-0", "tick-1"]),
                &crate::smt::NoSolver,
                None,
                None,
                &mut handles,
            )
            .unwrap();
            let [(left_1, right_1), (left_2, right_2)] = handles.0.as_slice() else {
                panic!("two points");
            };
            assert!(right_1.same(right_2));
            assert!(!left_1.same(left_2));
            assert_eq!(left_2.kore().to_string(), r#"left{}(\dv{SortS{}}("2"))"#);
            assert_eq!(right_1.kore().to_string(), r#"right{}(\dv{SortS{}}("r"))"#);
        }

        /// `top(n(N), out(L))`: `emit-0` and `emit-1` append `a` and then `b` to the list `out`
        /// holds; a probe that reads the list from its last length on reads each appended item
        /// once.
        #[test]
        fn list_items_reads_only_the_appended_part() {
            let source = r#"[]
                module MAIN
                    sort SortS{} [hasDomainValues{}()]
                    sort SortT{} []
                    sort SortN{} []
                    sort SortOut{} []
                    hooked-sort SortList{}
                        [hook{}("LIST.List"), unit{}(listUnit{}()), element{}(listItem{}()), concat{}(listConcat{}())]
                    hooked-symbol listUnit{}() : SortList{} [function{}(), total{}(), hook{}("LIST.unit")]
                    hooked-symbol listItem{}(SortS{}) : SortList{} [function{}(), total{}(), hook{}("LIST.element")]
                    hooked-symbol listConcat{}(SortList{}, SortList{}) : SortList{} [function{}(), total{}(), hook{}("LIST.concat"), assoc{}()]
                    symbol top{}(SortN{}, SortOut{}) : SortT{} [constructor{}(), functional{}(), injective{}()]
                    symbol n{}(SortS{}) : SortN{} [constructor{}(), functional{}(), injective{}()]
                    symbol out{}(SortList{}) : SortOut{} [constructor{}(), functional{}(), injective{}()]
                    axiom{} \rewrites{SortT{}}(
                        \and{SortT{}}(top{}(n{}(\dv{SortS{}}("0")), out{}(L:SortList{})), \top{SortT{}}()),
                        top{}(n{}(\dv{SortS{}}("1")), out{}(listConcat{}(L:SortList{}, listItem{}(\dv{SortS{}}("a")))))
                    ) [label{}("emit-0")]
                    axiom{} \rewrites{SortT{}}(
                        \and{SortT{}}(top{}(n{}(\dv{SortS{}}("1")), out{}(L:SortList{})), \top{SortT{}}()),
                        top{}(n{}(\dv{SortS{}}("2")), out{}(listConcat{}(L:SortList{}, listItem{}(\dv{SortS{}}("b")))))
                    ) [label{}("emit-1")]
                endmodule []"#;
            let syntax = parse_definition(source).unwrap();
            let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
            let start = Pattern {
                term: definition
                    .internalize_term(
                        &parse_pattern(r#"top{}(n{}(\dv{SortS{}}("0")), out{}(listUnit{}()))"#)
                            .unwrap(),
                        &[],
                    )
                    .unwrap(),
                constraints: Vec::new(),
            };
            #[derive(Default)]
            struct Log {
                read: usize,
                items: Vec<(Option<usize>, Vec<String>)>,
                end: Option<(Option<usize>, Option<Vec<String>>)>,
            }
            impl Probe for Log {
                fn observe(&mut self, point: &ProbeArrival<'_>) -> ProbeDecision {
                    let path = ["top", "out"];
                    let length = point.list_len(&path);
                    let items = point.list_items(&path, self.read).unwrap();
                    self.read = length.unwrap();
                    self.items
                        .push((length, items.iter().map(ToString::to_string).collect()));
                    // Not a list, and no such cell.
                    assert_eq!(point.list_len(&["top", "n"]), None);
                    assert_eq!(point.list_items(&["top", "missing"], 0), None);
                    ProbeDecision::Continue
                }

                fn ended(&mut self, leaf: &ProbeLeaf<'_>) {
                    let path = ["top", "out"];
                    self.end = Some((
                        leaf.list_len(&path),
                        leaf.list_items(&path, 5)
                            .map(|items| items.iter().map(ToString::to_string).collect()),
                    ));
                }
            }
            let mut log = Log::default();
            crate::rewrite::execute_with_probe(
                &definition,
                start,
                probing(&[], &["emit-0", "emit-1"]),
                &crate::smt::NoSolver,
                None,
                None,
                &mut log,
            )
            .unwrap();
            let item = |value: &str| format!(r#"\dv{{SortS{{}}}}("{value}")"#);
            assert_eq!(
                log.items,
                [(Some(1), vec![item("a")]), (Some(2), vec![item("b")])]
            );
            // Read past its end at the leaf: no item.
            assert_eq!(log.end, Some((Some(2), Some(Vec::new()))));
        }

        /// The probe's work is not the run's: it runs off the step clock, in a proof scope,
        /// with its own operation record and poll budget, reporting to no coverage set of the
        /// run, and the run's result is the one without that work.
        #[test]
        fn the_probe_runs_isolated_off_the_clock() {
            struct Working(Vec<(crate::evaluation::EvaluationMode, bool, usize)>);
            impl Probe for Working {
                fn observe(&mut self, _: &ProbeArrival<'_>) -> ProbeDecision {
                    let mode = crate::evaluation::current();
                    crate::coverage::note_matched("probe-work");
                    let ((spent, ()), record) = crate::stop::with_operation_record(|| {
                        crate::stop::dismiss_a_stack_stop();
                        let ((), budget) = crate::stop::with_poll_budget(
                            2,
                            crate::timeout::StepTimeoutMode::Manual(std::time::Duration::ZERO),
                            || loop {
                                if let Err(stop) = crate::stop::check() {
                                    stop.forgo_refinement();
                                    break;
                                }
                            },
                        );
                        (budget.budget_exhausted, ())
                    });
                    // A lower bound on the time the run does not charge: no clock decides it.
                    std::thread::sleep(std::time::Duration::from_millis(5));
                    self.0.push((mode, spent, record.stack_stops));
                    ProbeDecision::Continue
                }

                fn ended(&mut self, _: &ProbeLeaf<'_>) {
                    crate::coverage::note_matched("probe-end");
                }
            }
            let definition = steps(false);
            let options = ExecutionOptions {
                evaluation: crate::evaluation::EvaluationMode::Execution,
                collect_coverage: true,
                ..probing(&["tick-a", "tick-b"], &[])
            };
            let mut probe = Working(Vec::new());
            let off_before = crate::stop::time_off_the_clock();
            let result = crate::rewrite::execute_with_probe(
                &definition,
                state(&definition, "0"),
                options.clone(),
                &crate::smt::NoSolver,
                None,
                None,
                &mut probe,
            )
            .unwrap();
            let off = crate::stop::time_off_the_clock() - off_before;
            assert_eq!(
                probe.0,
                [
                    (crate::evaluation::EvaluationMode::Proof, true, 1),
                    (crate::evaluation::EvaluationMode::Proof, true, 1)
                ]
            );
            assert!(off >= std::time::Duration::from_millis(10), "{off:?}");
            assert_eq!(result.stack_stops, 0);
            assert_eq!(result.stopped, None);
            let matched = &result.coverage.as_ref().unwrap().matched;
            assert!(!matched.contains("probe-work") && !matched.contains("probe-end"));
            let plain = crate::rewrite::execute(&definition, state(&definition, "0"), options);
            assert_eq!(result, plain);
        }

        /// A probe and a stop condition on one run, each asked where it is asked alone: the
        /// condition at each arrival as the step is taken, the probe once the step's successor
        /// is shown defined. A stop's last event of a cut-point rule ends the path before the
        /// step, with no point; a terminal rule's last step has its points, then its end. A
        /// probe that continues leaves the condition's run as it is.
        #[test]
        fn probe_and_stop_condition_compose() {
            let definition = steps(false);
            let ticks = ["tick-a", "tick-b", "tick-c"];
            let compose = |terminal: bool, probe_answers: &[(&str, StopSide, ProbeDecision)]| {
                let log = RefCell::new(Vec::new());
                let holds = if terminal { "3" } else { "2" };
                let mut condition = |arrival: &StopArrival<'_>| {
                    let value = match arrival.configuration() {
                        k_rust_kore::kore::ast::Pattern::DomainValue { ref value, .. } => {
                            value.as_utf8().unwrap().to_owned()
                        }
                        other => format!("{other:?}"),
                    };
                    log.borrow_mut().push(Asked::Condition(value.clone()));
                    if value == holds {
                        StopDecision::Holds
                    } else {
                        StopDecision::Fails
                    }
                };
                let mut probe = Recorder {
                    log: &log,
                    answers: probe_answers
                        .iter()
                        .map(|(value, side, decision)| {
                            ((*value).to_owned(), *side, decision.clone())
                        })
                        .collect(),
                };
                let (cut_point_rules, terminal_rules) = if terminal {
                    (BTreeSet::new(), names(&ticks))
                } else {
                    (names(&ticks), BTreeSet::new())
                };
                let options = ExecutionOptions {
                    cut_point_rules,
                    terminal_rules,
                    ..probing(&["tick-a", "tick-b"], &["tick-a", "tick-b", "work-a"])
                };
                let probed = crate::rewrite::execute_with_probe(
                    &definition,
                    state(&definition, "0"),
                    options.clone(),
                    &crate::smt::NoSolver,
                    None,
                    Some(&mut condition),
                    &mut probe,
                )
                .unwrap();
                let asked = log.borrow().clone();
                let mut condition = |arrival: &StopArrival<'_>| match arrival.configuration() {
                    k_rust_kore::kore::ast::Pattern::DomainValue { ref value, .. }
                        if value.as_utf8().unwrap() == holds =>
                    {
                        StopDecision::Holds
                    }
                    _ => StopDecision::Fails,
                };
                let alone = crate::rewrite::execute_with_stop_condition(
                    &definition,
                    state(&definition, "0"),
                    options,
                    &crate::smt::NoSolver,
                    None,
                    &mut condition,
                )
                .unwrap();
                (probed, alone, asked)
            };
            let condition = |value: &str| Asked::Condition(value.to_owned());
            // Cut point: the condition fails at `0`, whose step is taken, and holds at `2`, the
            // last event, whose step is not.
            let (probed, alone, asked) = compose(false, &[]);
            assert_eq!(
                asked,
                [
                    condition("0"),
                    point(StopSide::Before, 0, "0", "tick-a"),
                    point(StopSide::After, 1, "1", "tick-a"),
                    point(StopSide::After, 2, "2", "work-a"),
                    condition("2"),
                    ended(2, "2", "cut-point"),
                ]
            );
            assert_eq!(probed, alone);
            // Terminal: the condition fails at `1` and holds at `3`, whose step is taken.
            let (probed, alone, asked) = compose(true, &[]);
            assert_eq!(
                asked,
                [
                    condition("1"),
                    point(StopSide::Before, 0, "0", "tick-a"),
                    point(StopSide::After, 1, "1", "tick-a"),
                    point(StopSide::After, 2, "2", "work-a"),
                    condition("3"),
                    point(StopSide::Before, 2, "2", "tick-b"),
                    point(StopSide::After, 3, "3", "tick-b"),
                    ended(3, "3", "terminal"),
                ]
            );
            assert_eq!(probed, alone);
            // A difference at the terminal rule's last step ends the request before its end.
            let differs = ProbeDecision::Differs("three".to_owned());
            let (probed, _, asked) = compose(true, &[("3", StopSide::After, differs)]);
            assert_eq!(
                asked.last(),
                Some(&point(StopSide::After, 3, "3", "tick-b"))
            );
            assert_eq!(ends(&probed), [("3".into(), 3, "probe-difference")]);
        }

        /// `tick-d` takes `6` to `g(7)`, which simplification equations rewrite to `g2(7)` and
        /// that to `g3(7)`, where no equation applies. With a budget of one simplification the
        /// successor's normalization spends it, and the successor, an application of total
        /// functions, is defined, so the step has its points; the leaf an answer makes at either point carries that spent budget, the
        /// point resting on the normalization that showed the successor defined. With the
        /// default budget no leaf carries it.
        #[test]
        fn a_probe_leaf_carries_the_diagnostics_of_its_successors_normalization() {
            let simplifies = |from: &str, to: &str| {
                format!(
                    r#"axiom{{R}} \implies{{R}}(
                        \top{{R}}(),
                        \equals{{SortS{{}}, R}}(
                            {from}{{}}(X:SortS{{}}),
                            \and{{SortS{{}}}}({to}{{}}(X:SortS{{}}), \top{{SortS{{}}}}())
                        )
                    ) [label{{}}("{from}"), simplification{{}}()]"#
                )
            };
            let definition = steps_then(
                false,
                &format!(
                    r#"symbol g{{}}(SortS{{}}) : SortS{{}} [function{{}}(), total{{}}()]
                    symbol g2{{}}(SortS{{}}) : SortS{{}} [function{{}}(), total{{}}()]
                    symbol g3{{}}(SortS{{}}) : SortS{{}} [function{{}}(), total{{}}()]
                    {g}
                    {g2}
                    axiom{{}} \rewrites{{SortS{{}}}}(
                        \and{{SortS{{}}}}(\dv{{SortS{{}}}}("6"), \top{{SortS{{}}}}()),
                        g{{}}(\dv{{SortS{{}}}}("7"))
                    ) [label{{}}("tick-d")]"#,
                    g = simplifies("g", "g2"),
                    g2 = simplifies("g2", "g3"),
                ),
            );
            let exhausted = BackendDiagnostic::SimplificationBudgetExhausted {
                limit: 1,
                subject: crate::simplify::BudgetSubject::Term,
            };
            /// Answers `decision` at every point of `side`, recording what it is asked.
            struct BySide<'p, 'l> {
                inner: &'p mut Recorder<'l>,
                side: StopSide,
                decision: ProbeDecision,
            }
            impl Probe for BySide<'_, '_> {
                fn observe(&mut self, point: &ProbeArrival<'_>) -> ProbeDecision {
                    let _ = self.inner.observe(point);
                    if point.side() == self.side {
                        self.decision.clone()
                    } else {
                        ProbeDecision::Continue
                    }
                }

                fn ended(&mut self, leaf: &ProbeLeaf<'_>) {
                    self.inner.ended(leaf);
                }
            }
            let default_budget = ExecutionOptions::default().max_simplification_iterations;
            for (budget, side, decision, expected) in [
                (
                    1,
                    StopSide::Before,
                    ProbeDecision::Differs("six".to_owned()),
                    "probe-difference",
                ),
                (1, StopSide::Before, ProbeDecision::Done, "probe-done"),
                (1, StopSide::After, ProbeDecision::Done, "probe-done"),
                (
                    default_budget,
                    StopSide::Before,
                    ProbeDecision::Differs("six".to_owned()),
                    "probe-difference",
                ),
            ] {
                let context = format!("budget={budget} {side:?} {decision:?}");
                let log = RefCell::new(Vec::new());
                let mut probe = Recorder {
                    log: &log,
                    answers: Vec::new(),
                };
                let result = crate::rewrite::execute_with_probe(
                    &definition,
                    state(&definition, "0"),
                    ExecutionOptions {
                        max_simplification_iterations: budget,
                        ..probing(&["tick-d"], &["tick-d"])
                    },
                    &crate::smt::NoSolver,
                    None,
                    None,
                    &mut BySide {
                        inner: &mut probe,
                        side,
                        decision,
                    },
                )
                .unwrap();
                let [leaf] = result.leaves.as_slice() else {
                    panic!("{context}: one leaf: {result:#?}");
                };
                assert_eq!(halt(&leaf.halt_reason), expected, "{context}");
                let depth = if side == StopSide::Before { 6 } else { 7 };
                assert_eq!(leaf.depth, depth, "{context}");
                if side == StopSide::Before {
                    let observed = ProbeState {
                        depth: leaf.depth,
                        term: &leaf.pattern.term,
                    };
                    assert_eq!(value(&observed), "6", "{context}");
                }
                assert_eq!(
                    leaf.diagnostics.contains(&exhausted),
                    budget == 1,
                    "{context}: {:#?}",
                    leaf.diagnostics
                );
            }
        }

        /// The successor of a step at whose point a probe's answer ends the path is reached,
        /// normalized and defined, so it is matched: at the after point it is the leaf, at the
        /// before point the leaf is the state before the step. The target `3` is reached at
        /// depth 3 by `tick-b`, at whose points the answer is `Done`.
        #[test]
        fn the_successor_where_a_probe_answer_ends_the_path_is_matched() {
            let definition = steps(false);
            let target = state(&definition, "3");
            for (side, observed, depth) in [(StopSide::After, "3", 3), (StopSide::Before, "2", 2)] {
                for result_modality in [ResultModality::PathSet, ResultModality::StateSet] {
                    let options = ExecutionOptions {
                        result_modality,
                        match_states: Some(StateMatchOptions {
                            target: target.clone(),
                            proof_agreement: false,
                        }),
                        ..probing(&["tick-b"], &["tick-b"])
                    };
                    let (result, _) = run(
                        &definition,
                        options,
                        &[(observed, side, ProbeDecision::Done)],
                    );
                    let context = format!("{side:?} {result_modality:?}");
                    assert_eq!(
                        ends(&result),
                        [(observed.to_owned(), depth, "probe-done")],
                        "{context}"
                    );
                    let matches = result.state_matches.as_ref().expect("matched");
                    // `0`, `1` and `2` are expanded; `3` is the step's successor.
                    assert_eq!(matches.matched, 4, "{context}");
                    let reach = matches.first_clean_reach.as_ref().expect("a reach");
                    assert_eq!(reach.depth, 3, "{context}");
                    assert_eq!(reach.pattern, target, "{context}");
                }
            }
        }

        /// Under `StateSet` an answer ends the request or the path at its observed state as
        /// under `PathSet`, and its leaf is never merged.
        #[test]
        fn differs_and_done_under_state_set() {
            let definition = steps(false);
            for result_modality in [ResultModality::StateSet, ResultModality::PathSet] {
                let options = || ExecutionOptions {
                    result_modality,
                    ..probing(&["tick-b"], &["tick-b"])
                };
                let differs = ProbeDecision::Differs("two".to_owned());
                let (result, asked) =
                    run(&definition, options(), &[("2", StopSide::Before, differs)]);
                assert_eq!(asked, [point(StopSide::Before, 2, "2", "tick-b")]);
                assert_eq!(
                    ends(&result),
                    [("2".into(), 2, "probe-difference")],
                    "{result_modality:?}"
                );
                let (result, asked) = run(
                    &definition,
                    options(),
                    &[("3", StopSide::After, ProbeDecision::Done)],
                );
                assert_eq!(
                    asked,
                    [
                        point(StopSide::Before, 2, "2", "tick-b"),
                        point(StopSide::After, 3, "3", "tick-b"),
                    ]
                );
                assert_eq!(
                    ends(&result),
                    [("3".into(), 3, "probe-done")],
                    "{result_modality:?}"
                );
            }
        }

        /// Several initial states are several paths from the start: the probe is told once, at
        /// depth 0, asked nothing after, and the result is the run's without it.
        #[test]
        fn several_initial_states_are_a_split_at_the_start() {
            let definition = steps(false);
            let options = ExecutionOptions {
                result_modality: ResultModality::PathSet,
                ..probing(&["tick-a", "tick-b", "tick-c"], &["work-a", "work-b"])
            };
            let initial = || vec![state(&definition, "0"), state(&definition, "3")];
            let log = RefCell::new(Vec::new());
            let mut probe = Recorder {
                log: &log,
                answers: Vec::new(),
            };
            let probed = execute_with_condition(
                &definition,
                initial(),
                options.clone(),
                &crate::smt::NoSolver,
                None,
                InProcess {
                    condition: None,
                    reading: None,
                    probe: Some(&mut probe),
                },
            )
            .unwrap();
            assert_eq!(log.into_inner(), [Asked::Branched(0)]);
            let plain = execute_with_condition(
                &definition,
                initial(),
                options,
                &crate::smt::NoSolver,
                None,
                InProcess::default(),
            )
            .unwrap();
            assert_eq!(probed, plain);
            assert_eq!(ends(&probed).len(), 2);
        }

        /// A path the work budget ends is ended at its `work-bound` leaf, the state the run took
        /// from its worklist unexpanded, which the probe is told of.
        #[test]
        fn ended_is_told_of_a_work_bound_leaf() {
            let definition = steps(false);
            let options = ExecutionOptions {
                max_work: Some(3),
                ..probing(&["tick-a", "tick-b"], &[])
            };
            let (result, asked) = run(&definition, options, &[]);
            // `tick-b`'s successor `3` is the work-bound leaf, never normalized, so that step
            // has no point.
            assert_eq!(
                asked,
                [
                    point(StopSide::Before, 0, "0", "tick-a"),
                    ended(3, "3", "work-bound"),
                ]
            );
            assert_eq!(ends(&result), [("3".into(), 3, "work-bound")]);
        }

        /// `c(0)` counts up to `c(3)` by `count` (`N <Int 3`), and also by `again` while
        /// `N <Int 1`, so `c(0)` has two equal successors, which a state-set run merges; `c(3)`
        /// ends at `done(3)` by `finish` (`2 <Int N`).
        fn counter() -> BackendDefinition {
            let rule = |label: &str, rhs: &str, condition: &str| {
                format!(
                    r#"axiom{{}} \rewrites{{SortS{{}}}}(
                        \and{{SortS{{}}}}(
                            c{{}}(N:SortInt{{}}),
                            \equals{{SortBool{{}}, SortS{{}}}}({condition}, \dv{{SortBool{{}}}}("true"))
                        ),
                        \and{{SortS{{}}}}({rhs}, \top{{SortS{{}}}}())
                    ) [label{{}}("{label}")]"#
                )
            };
            let next = r#"c{}(addInt{}(N:SortInt{}, \dv{SortInt{}}("1")))"#;
            let source = format!(
                r#"[]
                module MAIN
                    hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
                    hooked-sort SortBool{{}} [hook{{}}("BOOL.Bool"), hasDomainValues{{}}()]
                    sort SortS{{}} []
                    symbol c{{}}(SortInt{{}}) : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
                    symbol done{{}}(SortInt{{}}) : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
                    hooked-symbol ltInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
                        [function{{}}(), total{{}}(), hook{{}}("INT.lt"), smt-hook{{}}("<")]
                    hooked-symbol addInt{{}}(SortInt{{}}, SortInt{{}}) : SortInt{{}}
                        [function{{}}(), total{{}}(), hook{{}}("INT.add"), smt-hook{{}}("+")]
                    {count}
                    {again}
                    {finish}
                endmodule []"#,
                count = rule(
                    "count",
                    next,
                    r#"ltInt{}(N:SortInt{}, \dv{SortInt{}}("3"))"#
                ),
                again = rule(
                    "again",
                    next,
                    r#"ltInt{}(N:SortInt{}, \dv{SortInt{}}("1"))"#
                ),
                finish = rule(
                    "finish",
                    "done{}(N:SortInt{})",
                    r#"ltInt{}(\dv{SortInt{}}("2"), N:SortInt{})"#
                ),
            );
            let syntax = parse_definition(&source).expect("definition should parse");
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
        }

        fn counter_state(definition: &BackendDefinition, source: &str) -> Pattern {
            Pattern {
                term: definition
                    .internalize_term(&parse_pattern(source).unwrap(), &[])
                    .unwrap(),
                constraints: Vec::new(),
            }
        }

        /// A probe that always continues is no probe with every collection on (guards,
        /// conditions, bindings, offered axioms), state matching, and a stop condition, under
        /// both strategies and modalities: the same result, coverage and matches included.
        #[test]
        fn a_continue_probe_leaves_collections_matches_and_a_stop_condition_unchanged() {
            let definition = counter();
            let rules = ["count", "again", "finish"];
            let c = |n: u64| format!(r#"c{{}}(\dv{{SortInt{{}}}}("{n}"))"#);
            let initial = || counter_state(&definition, &c(0));
            let stop_at = crate::externalize::term(&counter_state(&definition, &c(2)).term);
            for mode in [ExecutionMode::All, ExecutionMode::Any] {
                for result_modality in [ResultModality::StateSet, ResultModality::PathSet] {
                    for (cut, target) in [
                        (false, r#"done{}(\dv{SortInt{}}("3"))"#.to_owned()),
                        (true, c(2)),
                    ] {
                        let options = ExecutionOptions {
                            mode,
                            result_modality,
                            cut_point_rules: if cut { names(&["count"]) } else { names(&[]) },
                            retain_trace: true,
                            collect_coverage: true,
                            collect_counts: true,
                            collect_committed: true,
                            collect_offered: true,
                            collect_guards: Some(crate::coverage::GuardCollection::new(rules)),
                            collect_conditions: Some(crate::coverage::ConditionCollection::new(
                                rules,
                            )),
                            collect_bindings: Some(
                                crate::coverage::BindingCollection::new(["Lblc"])
                                    .with_binder("count", "N", 8),
                            ),
                            match_states: Some(StateMatchOptions {
                                target: counter_state(&definition, &target),
                                proof_agreement: true,
                            }),
                            ..probing(&rules, &rules)
                        };
                        let context = format!("{mode:?} {result_modality:?} cut={cut}");
                        let condition = |arrival: &StopArrival<'_>| {
                            if arrival.configuration() == stop_at {
                                StopDecision::Holds
                            } else {
                                StopDecision::Fails
                            }
                        };
                        let log = RefCell::new(Vec::new());
                        let mut probe = Recorder {
                            log: &log,
                            answers: Vec::new(),
                        };
                        let mut probed_condition = condition;
                        let probed = crate::rewrite::execute_with_probe(
                            &definition,
                            initial(),
                            options.clone(),
                            &crate::smt::NoSolver,
                            None,
                            cut.then_some(
                                &mut probed_condition as &mut dyn crate::rewrite::StopCondition,
                            ),
                            &mut probe,
                        )
                        .unwrap();
                        let plain = if cut {
                            let mut condition = condition;
                            crate::rewrite::execute_with_stop_condition(
                                &definition,
                                initial(),
                                options,
                                &crate::smt::NoSolver,
                                None,
                                &mut condition,
                            )
                            .unwrap()
                        } else {
                            crate::rewrite::execute(&definition, initial(), options)
                        };
                        let coverage = plain.coverage.as_ref().expect("coverage");
                        assert!(
                            coverage
                                .guards
                                .as_ref()
                                .is_some_and(|guards| !guards.is_empty()),
                            "{context}"
                        );
                        assert!(
                            coverage
                                .conditions
                                .as_ref()
                                .is_some_and(|conditions| !conditions.is_empty()),
                            "{context}"
                        );
                        assert!(
                            plain
                                .state_matches
                                .as_ref()
                                .is_some_and(|matches| matches.first_clean_reach.is_some()),
                            "{context}"
                        );
                        assert!(!log.borrow().is_empty(), "{context}");
                        assert_eq!(probed, plain, "{context}");
                    }
                }
            }
        }

        /// What a watching probe was told of a return: the earlier state's depth, the state's
        /// depth and value, and the rule whose step reached it.
        type Told = Vec<(u64, u64, String, String)>;

        /// A probe that keeps `room` states, whose progress is the number of points it was asked
        /// about at the rules of `progressing`, and that answers a return with `answer`.
        struct Watcher<'a> {
            room: usize,
            progressing: BTreeSet<String>,
            points: u64,
            answer: ProbeDecision,
            told: &'a RefCell<Told>,
        }

        impl Probe for Watcher<'_> {
            fn observe(&mut self, point: &ProbeArrival<'_>) -> ProbeDecision {
                if self.progressing.contains(point.rule()) {
                    self.points += 1;
                }
                ProbeDecision::Continue
            }

            fn ended(&mut self, _: &ProbeLeaf<'_>) {}

            fn cycle_states(&self) -> usize {
                self.room
            }

            fn progress(&self) -> u64 {
                self.points
            }

            fn cycled(&mut self, cycle: &ProbeCycle<'_>) -> ProbeDecision {
                self.told.borrow_mut().push((
                    cycle.first(),
                    cycle.depth(),
                    value(cycle),
                    cycle.rule().to_owned(),
                ));
                self.answer.clone()
            }
        }

        /// The steps `0` to `6`, then `loop-a` from `6` to `7` and `loop-b` back to `6`, forever.
        fn looping() -> BackendDefinition {
            let step = |from: &str, to: &str, label: &str| {
                format!(
                    r#"axiom{{}} \rewrites{{SortS{{}}}}(
                        \and{{SortS{{}}}}(\dv{{SortS{{}}}}("{from}"), \top{{SortS{{}}}}()),
                        \dv{{SortS{{}}}}("{to}")
                    ) [label{{}}("{label}")]"#
                )
            };
            steps_then(
                false,
                &[step("6", "7", "loop-a"), step("7", "6", "loop-b")].join("\n"),
            )
        }

        const TICKS: [&str; 3] = ["tick-a", "tick-b", "tick-c"];

        /// [`probing`] the ticks before their steps and `after` after theirs, to depth 20.
        fn watching(after: &[&str]) -> ExecutionOptions {
            ExecutionOptions {
                max_depth: 20,
                ..probing(&TICKS, after)
            }
        }

        /// A run from `initial` under `options` with a [`Watcher`]; also what it was told.
        fn watch(
            definition: &BackendDefinition,
            initial: Pattern,
            options: ExecutionOptions,
            room: usize,
            progressing: &[&str],
            answer: ProbeDecision,
        ) -> (ExecutionResult, Told) {
            let told = RefCell::new(Vec::new());
            let mut probe = Watcher {
                room,
                progressing: names(progressing),
                points: 0,
                answer,
                told: &told,
            };
            let result = crate::rewrite::execute_with_probe(
                definition,
                initial,
                options,
                &crate::smt::NoSolver,
                None,
                None,
                &mut probe,
            )
            .unwrap();
            (result, told.into_inner())
        }

        fn told(first: u64, depth: u64, value: &str, rule: &str) -> (u64, u64, String, String) {
            (first, depth, value.to_owned(), rule.to_owned())
        }

        /// The path `0`, …, `6`, `7`, `6` returns at depth 8 to its state at depth 6, with the
        /// probe's progress unchanged since `tick-c`'s point. The probe is told once, with the
        /// rule whose step reached the state, and its answer is read as at that rule's after
        /// point: `Done` ends the path and `Differs` the request, each with a leaf of the state.
        /// `Continue` changes nothing: the result is the run's without the probe.
        #[test]
        fn a_return_with_unchanged_progress_is_told_once_and_answered_at_the_state() {
            let definition = looping();
            for answer in [ProbeDecision::Done, ProbeDecision::Differs("loops".into())] {
                let (result, told_) = watch(
                    &definition,
                    state(&definition, "0"),
                    watching(&[]),
                    8,
                    &TICKS,
                    answer.clone(),
                );
                assert_eq!(told_, [told(6, 8, "6", "loop-b")], "{answer:?}");
                let (halt, rule, side) = match &result.leaves[0].halt_reason {
                    HaltReason::ProbeDone { rule, side } => ("probe-done", rule, side),
                    HaltReason::ProbeDifference { rule, side, .. } => {
                        ("probe-difference", rule, side)
                    }
                    other => panic!("{other:?}"),
                };
                assert_eq!(ends(&result), [("6".into(), 8, halt)], "{answer:?}");
                assert_eq!((rule.as_str(), *side), ("loop-b", StopSide::After));
            }
            let (result, told_) = watch(
                &definition,
                state(&definition, "0"),
                watching(&[]),
                8,
                &TICKS,
                ProbeDecision::Continue,
            );
            assert_eq!(told_, [told(6, 8, "6", "loop-b")]);
            let plain =
                crate::rewrite::execute(&definition, state(&definition, "0"), watching(&[]));
            assert_eq!(result, plain);
            assert_eq!(ends(&result), [("6".into(), 20, "depth-bound")]);
        }

        /// A change of the probe's progress forgets the states kept before it: a probe whose
        /// progress moves at each `loop-a` point is in another state at every pass, and is never
        /// told of a return.
        #[test]
        fn a_change_of_progress_forgets_the_kept_states() {
            let definition = looping();
            let (result, told_) = watch(
                &definition,
                state(&definition, "0"),
                watching(&["loop-a"]),
                8,
                &["tick-a", "tick-b", "tick-c", "loop-a"],
                ProbeDecision::Done,
            );
            assert_eq!(told_, Told::new());
            assert_eq!(ends(&result), [("6".into(), 20, "depth-bound")]);
        }

        /// After `tick-c`'s point the path reaches `5`, `6`, `7`, `6`, … with the progress
        /// unchanged. With room for two states `5` and `6` are kept, and the second `6` returns.
        /// With room for one only `5` is kept: `6` and `7` are compared past the room but not
        /// kept, so no later state returns to a kept one and no return is claimed. With no room
        /// nothing is compared.
        #[test]
        fn past_the_room_no_return_is_claimed() {
            let definition = looping();
            let watched = |room: usize| {
                watch(
                    &definition,
                    state(&definition, "0"),
                    watching(&[]),
                    room,
                    &TICKS,
                    ProbeDecision::Done,
                )
            };
            let (result, told_) = watched(2);
            assert_eq!(told_, [told(6, 8, "6", "loop-b")]);
            assert_eq!(ends(&result), [("6".into(), 8, "probe-done")]);
            for room in [1, 0] {
                let (result, told_) = watched(room);
                assert_eq!(told_, Told::new(), "{room}");
                assert_eq!(ends(&result), [("6".into(), 20, "depth-bound")], "{room}");
            }
        }

        /// Equal configurations with different stop events or arrivals are two states: with
        /// `loop-a` a terminal rule whose count is never reached, each pass arrives at the stop
        /// once more, so no state returns. Under strategy `any` nothing is compared. In both the
        /// result is the run's without the probe.
        #[test]
        fn stop_arrivals_between_equal_configurations_and_strategy_any_claim_no_return() {
            let definition = looping();
            let arriving = ExecutionOptions {
                terminal_rules: names(&["loop-a"]),
                stop_count: NonZeroU64::new(1000).unwrap(),
                ..watching(&[])
            };
            let any = ExecutionOptions {
                mode: ExecutionMode::Any,
                ..watching(&[])
            };
            for options in [arriving, any] {
                let (result, told_) = watch(
                    &definition,
                    state(&definition, "0"),
                    options.clone(),
                    8,
                    &TICKS,
                    ProbeDecision::Done,
                );
                assert_eq!(told_, Told::new());
                let plain = crate::rewrite::execute(&definition, state(&definition, "0"), options);
                assert_eq!(result, plain);
            }
        }

        /// `wrap(X)` rewrites to itself: from the ground `wrap(3)` the path returns at depth 2
        /// to its state at depth 1 (the initial input is not kept), and from `wrap(X)` it repeats
        /// the same symbolic state forever, which is never compared: an equality the run does
        /// not decide in every model is no return.
        #[test]
        fn a_symbolic_repeat_is_never_a_return() {
            let definition = prelude_definition();
            let pattern = |text: &str| Pattern {
                term: definition
                    .internalize_term(&parse_pattern(text).unwrap(), &[])
                    .unwrap(),
                constraints: Vec::new(),
            };
            let options = ExecutionOptions {
                max_depth: 6,
                ..ExecutionOptions::default()
            };
            let (result, told_) = watch(
                &definition,
                pattern(r#"wrap{}(\dv{SortInt{}}("3"))"#),
                options.clone(),
                8,
                &[],
                ProbeDecision::Done,
            );
            assert_eq!(
                told_
                    .iter()
                    .map(|(first, depth, _, rule)| (*first, *depth, rule.as_str()))
                    .collect::<Vec<_>>(),
                [(1, 2, "wrap")]
            );
            assert_eq!(result.leaves[0].depth, 2);
            let (result, told_) = watch(
                &definition,
                pattern("wrap{}(X:SortInt{})"),
                options,
                8,
                &[],
                ProbeDecision::Done,
            );
            assert_eq!(told_, Told::new());
            assert!(matches!(
                result.leaves.as_slice(),
                [leaf] if leaf.halt_reason == HaltReason::DepthBound && leaf.depth == 6
            ));
        }
    }

    /// What a counted run's leaf is compared by: its configuration (as `Debug` text, to sort
    /// by), the path's depth, its halt (`stop` for a cut-point or terminal-rule leaf), its
    /// arrivals, and the labels of the path's rewrite steps.
    type CountedLeaf = (String, u64, &'static str, u64, Vec<String>);

    fn halt_name(halt: &HaltReason) -> &'static str {
        match halt {
            HaltReason::CutPointRule { .. } | HaltReason::TerminalRule { .. } => "stop",
            HaltReason::Stuck => "stuck",
            HaltReason::DepthBound => "depth-bound",
            _ => "other",
        }
    }

    fn rewrite_labels(trace: &[TraceEntry]) -> Vec<String> {
        trace
            .iter()
            .filter(|entry| entry.kind == TraceKind::Rewrite)
            .map(|entry| entry.label.clone().unwrap_or_default())
            .collect()
    }

    /// A run to the Nth arrival at a stop takes exactly the steps of the run to the first
    /// arrival resumed from each arrival before the Nth, each piece a request of its own (a
    /// cut-point piece resumed at its proposed successor, the proposed step counted), with no
    /// count anywhere: the same ends, at the same depths, by the same steps, with the same
    /// passed stops (at the depth along the whole path), and each end's count of arrivals.
    ///
    /// The definition runs `0` to `6` by alternating selected `tick-*` and unselected `work-*`
    /// steps, except that `3` also has a selected `tick-x` successor beside `work-b`: a choice,
    /// which strategy `all` takes both sides of and passes, and strategy `any` resolves to
    /// `work-b`, the first rule. Every count from 1 past the number of arrivals, both kinds of
    /// stop rule, both strategies and both modalities, and depth bounds that cut before, at and
    /// after arrivals are run.
    #[test]
    fn a_counted_run_takes_the_steps_of_its_staged_pieces() {
        let step = |from: &str, to: &str, label: &str| {
            format!(
                r#"axiom{{}} \rewrites{{SortS{{}}}}(
                    \and{{SortS{{}}}}(\dv{{SortS{{}}}}("{from}"), \top{{SortS{{}}}}()),
                    \dv{{SortS{{}}}}("{to}")
                ) [label{{}}("{label}")]"#
            )
        };
        let axioms = [
            step("0", "1", "tick-a"),
            step("1", "2", "work-a"),
            step("2", "3", "tick-b"),
            step("3", "4", "work-b"),
            step("3", "4x", "tick-x"),
            step("4", "5", "tick-c"),
            step("5", "6", "work-c"),
            step("4x", "6x", "work-x"),
        ]
        .join("\n");
        let definition = definition(&axioms);
        let selected = BTreeSet::from(["tick-a", "tick-b", "tick-c", "tick-x"].map(str::to_owned));
        let run = |start: Pattern,
                   terminal: bool,
                   count: u64,
                   max_depth: u64,
                   mode: ExecutionMode,
                   result_modality: ResultModality| {
            let (cut_point_rules, terminal_rules) = if terminal {
                (BTreeSet::new(), selected.clone())
            } else {
                (selected.clone(), BTreeSet::new())
            };
            super::super::execute(
                &definition,
                start,
                ExecutionOptions {
                    cut_point_rules,
                    terminal_rules,
                    stop_count: NonZeroU64::new(count).unwrap(),
                    max_depth,
                    mode,
                    result_modality,
                    ..ExecutionOptions::default()
                },
            )
        };
        let start = Pattern {
            term: definition
                .internalize_term(&parse_pattern(r#"\dv{SortS{}}("0")"#).unwrap(), &[])
                .unwrap(),
            constraints: Vec::new(),
        };
        let configurations = |mode, modality| {
            [false, true].into_iter().flat_map(move |terminal| {
                (1..=5).flat_map(move |count| {
                    [u64::MAX, 0, 1, 2, 3, 4, 5]
                        .into_iter()
                        .map(move |depth| (terminal, count, depth, mode, modality))
                })
            })
        };
        let mut arrivals_seen = BTreeSet::new();
        for (mode, modality) in [
            (ExecutionMode::Any, ResultModality::StateSet),
            (ExecutionMode::All, ResultModality::StateSet),
            (ExecutionMode::All, ResultModality::PathSet),
        ] {
            for (terminal, count, max_depth, mode, modality) in configurations(mode, modality) {
                let context = format!(
                    "terminal={terminal} count={count} depth={max_depth} {mode:?} {modality:?}"
                );
                let counted = run(start.clone(), terminal, count, max_depth, mode, modality);
                let mut counted_leaves = counted
                    .leaves
                    .iter()
                    .map(|leaf| {
                        (
                            format!("{:?}", leaf.pattern),
                            leaf.depth,
                            halt_name(&leaf.halt_reason),
                            leaf.stops,
                            rewrite_labels(&leaf.trace),
                        )
                    })
                    .collect::<Vec<CountedLeaf>>();
                // The staged run: each piece to its first arrival, from where the one before it
                // stopped, with the depth the pieces before it left.
                let mut staged_leaves = Vec::<CountedLeaf>::new();
                let mut passed = BTreeMap::<String, u64>::new();
                let mut pieces = vec![(start.clone(), 0_u64, 0_u64, Vec::<String>::new())];
                while let Some((from, offset, arrivals, mut trace)) = pieces.pop() {
                    let piece = run(
                        from,
                        terminal,
                        1,
                        max_depth.saturating_sub(offset),
                        mode,
                        modality,
                    );
                    for stop in piece.passed_stops {
                        let depth = offset + stop.depth;
                        let entry = passed.entry(stop.rule).or_insert(depth);
                        *entry = (*entry).min(depth);
                    }
                    for leaf in piece.leaves {
                        assert_eq!(
                            leaf.stops,
                            u64::from(halt_name(&leaf.halt_reason) == "stop"),
                            "{context}"
                        );
                        let mut path = trace.clone();
                        path.extend(rewrite_labels(&leaf.trace));
                        let depth = offset + leaf.depth;
                        let stopped = halt_name(&leaf.halt_reason) == "stop";
                        if stopped && arrivals + 1 < count {
                            match leaf.halt_reason {
                                HaltReason::CutPointRule { next_states, .. } => {
                                    let [taken] = next_states.as_slice() else {
                                        panic!("{context}: {next_states:?}")
                                    };
                                    path.push(taken.label.clone().unwrap_or_default());
                                    pieces.push((
                                        taken.pattern.clone(),
                                        depth + 1,
                                        arrivals + 1,
                                        path,
                                    ));
                                }
                                _ => pieces.push((leaf.pattern, depth, arrivals + 1, path)),
                            }
                            continue;
                        }
                        staged_leaves.push((
                            format!("{:?}", leaf.pattern),
                            depth,
                            halt_name(&leaf.halt_reason),
                            arrivals + u64::from(stopped),
                            path,
                        ));
                    }
                    trace.clear();
                }
                counted_leaves.sort();
                staged_leaves.sort();
                assert_eq!(counted_leaves, staged_leaves, "{context}");
                let counted_passed = counted
                    .passed_stops
                    .iter()
                    .map(|stop| (stop.rule.clone(), stop.depth))
                    .collect::<BTreeMap<_, _>>();
                assert_eq!(counted_passed, passed, "{context}");
                arrivals_seen.extend(counted_leaves.iter().map(|leaf| leaf.3));
            }
        }
        // The table reaches every count of arrivals the definition has, and a passed stop.
        assert_eq!(arrivals_seen, BTreeSet::from([0, 1, 2, 3]));
    }

    /// Under `state-set` a state merges only into a state whose path passed as many arrivals:
    /// from `s`, `m1` reaches `z` by the selected `stop-a` and `m2` by the unselected `plain`,
    /// both at depth 2, so at a count of 2 the `stop-b` step from `z` ends the first path (its
    /// second arrival, a cut-point leaf at `z`) and is the second path's first, which goes on to
    /// `end`. Merging the second `z` into the first would lose `end`. With a count of 1 the first
    /// path ends before `stop-a` and the second before `stop-b`, as without a count.
    #[test]
    fn a_state_set_run_merges_only_states_of_one_count_of_arrivals() {
        let step = |from: &str, to: &str, label: &str| {
            format!(
                r#"axiom{{}} \rewrites{{SortS{{}}}}(
                    \and{{SortS{{}}}}(\dv{{SortS{{}}}}("{from}"), \top{{SortS{{}}}}()),
                    \dv{{SortS{{}}}}("{to}")
                ) [label{{}}("{label}")]"#
            )
        };
        let axioms = [
            step("s", "m1", "x1"),
            step("s", "m2", "x2"),
            step("m1", "z", "stop-a"),
            step("m2", "z", "plain"),
            step("z", "end", "stop-b"),
        ]
        .join("\n");
        let definition = definition(&axioms);
        let start = Pattern {
            term: definition
                .internalize_term(&parse_pattern(r#"\dv{SortS{}}("s")"#).unwrap(), &[])
                .unwrap(),
            constraints: Vec::new(),
        };
        let run = |count| {
            super::super::execute(
                &definition,
                start.clone(),
                ExecutionOptions {
                    cut_point_rules: BTreeSet::from(["stop-a", "stop-b"].map(str::to_owned)),
                    stop_count: NonZeroU64::new(count).unwrap(),
                    result_modality: ResultModality::StateSet,
                    ..ExecutionOptions::default()
                },
            )
        };
        let ends = |result: &ExecutionResult| {
            let mut ends = result
                .leaves
                .iter()
                .map(|leaf| (leaf.depth, halt_name(&leaf.halt_reason), leaf.stops))
                .collect::<Vec<_>>();
            ends.sort_unstable();
            ends
        };
        let counted = run(2);
        assert_eq!(
            ends(&counted),
            [(2, "stop", 2), (3, "stuck", 1)],
            "{counted:#?}"
        );
        let first = run(1);
        assert_eq!(ends(&first), [(1, "stop", 1), (2, "stop", 1)], "{first:#?}");
    }

    /// A cut-point or terminal rule stops a run only as its state's one successor. From `a`
    /// the step has two defined successors, `b` by `to-b` and `c` by `to-c`, so selecting
    /// `to-b` stops nothing there: the run goes on through both, and lists the step it passed,
    /// at the depth of the state it was taken from. From `one` and from `u` the selected rule's
    /// step is the one successor (`u-bottom`'s successor is undefined, so it is no successor),
    /// so the run stops and passes nothing; and under `StopAtBranch` the step from `a` ends its
    /// path as a `Branch` leaf, which goes on past nothing. From `p` the run reaches `a` at depth 1
    /// and again at depth 2, through `q`, and passes `to-b` from both: the list names the rule
    /// once, at the shallower depth.
    #[test]
    fn passed_stop_is_listed_where_a_stop_rule_is_one_of_several_successors() {
        let definition = definition(
            r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(\dv{SortS{}}("s"), \top{SortS{}}()), \dv{SortS{}}("a")
            ) [label{}("s-a")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(\dv{SortS{}}("a"), \top{SortS{}}()), \dv{SortS{}}("b")
            ) [label{}("to-b")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(\dv{SortS{}}("a"), \top{SortS{}}()), \dv{SortS{}}("c")
            ) [label{}("to-c")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(\dv{SortS{}}("one"), \top{SortS{}}()), \dv{SortS{}}("b")
            ) [label{}("one-b")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(\dv{SortS{}}("u"), \top{SortS{}}()),
                \and{SortS{}}(\dv{SortS{}}("x"), \bottom{SortS{}}())
            ) [label{}("u-bottom")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(\dv{SortS{}}("u"), \top{SortS{}}()), \dv{SortS{}}("b")
            ) [label{}("u-b")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(\dv{SortS{}}("p"), \top{SortS{}}()), \dv{SortS{}}("a")
            ) [label{}("p-a")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(\dv{SortS{}}("p"), \top{SortS{}}()), \dv{SortS{}}("q")
            ) [label{}("p-q")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(\dv{SortS{}}("q"), \top{SortS{}}()), \dv{SortS{}}("a")
            ) [label{}("q-a")]
            "#,
        );
        let state = |value: &str| Pattern {
            term: definition
                .internalize_term(
                    &parse_pattern(&format!(r#"\dv{{SortS{{}}}}("{value}")"#)).unwrap(),
                    &[],
                )
                .unwrap(),
            constraints: Vec::new(),
        };
        let selected = || BTreeSet::from(["to-b".to_owned(), "one-b".to_owned(), "u-b".to_owned()]);
        let run = |start: &str, terminal: bool, branch_mode, result_modality| {
            let (cut_point_rules, terminal_rules) = if terminal {
                (BTreeSet::new(), selected())
            } else {
                (selected(), BTreeSet::new())
            };
            super::super::execute(
                &definition,
                state(start),
                ExecutionOptions {
                    cut_point_rules,
                    terminal_rules,
                    branch_mode,
                    result_modality,
                    ..ExecutionOptions::default()
                },
            )
        };
        let halts = |result: &ExecutionResult| {
            result
                .leaves
                .iter()
                .map(|leaf| (leaf.depth, leaf.halt_reason.clone()))
                .collect::<Vec<_>>()
        };
        let passed = |rule: &str, depth| PassedStop {
            depth,
            rule: rule.to_owned(),
        };
        for terminal in [false, true] {
            for modality in [ResultModality::StateSet, ResultModality::PathSet] {
                // Both successors of `a` are explored and stuck: the stop was passed.
                for (start, depth) in [("a", 0), ("s", 1)] {
                    let result = run(start, terminal, ExecutionBranchMode::ExploreAll, modality);
                    assert_eq!(
                        halts(&result),
                        [
                            (depth + 1, HaltReason::Stuck),
                            (depth + 1, HaltReason::Stuck)
                        ],
                        "{start} terminal={terminal} {modality:?}: {result:#?}"
                    );
                    assert_eq!(
                        result.passed_stops,
                        [passed("to-b", depth)],
                        "{start} terminal={terminal} {modality:?}"
                    );
                }
                // `to-b` is passed from `a` at depth 1 and at depth 2: one entry, at depth 1.
                let result = run("p", terminal, ExecutionBranchMode::ExploreAll, modality);
                assert_eq!(
                    result.passed_stops,
                    [passed("to-b", 1)],
                    "p terminal={terminal} {modality:?}: {result:#?}"
                );
                // The selected rule's step is the one defined successor: the run stops there.
                for (start, rule) in [("one", "one-b"), ("u", "u-b")] {
                    let result = run(start, terminal, ExecutionBranchMode::ExploreAll, modality);
                    let stop = if terminal {
                        (
                            1,
                            HaltReason::TerminalRule {
                                rule: rule.to_owned(),
                            },
                        )
                    } else {
                        (0, result.leaves.last().unwrap().halt_reason.clone())
                    };
                    assert!(
                        halts(&result).contains(&stop),
                        "{start} terminal={terminal} {modality:?}: {result:#?}"
                    );
                    assert!(
                        terminal
                            || matches!(
                                &stop.1,
                                HaltReason::CutPointRule { rule: name, .. } if name == rule
                            ),
                        "{start} {modality:?}: {result:#?}"
                    );
                    assert_eq!(result.passed_stops, [], "{start} terminal={terminal}");
                }
                // A step with several successors ends its path as a `Branch` leaf.
                let result = run("a", terminal, ExecutionBranchMode::StopAtBranch, modality);
                assert!(
                    matches!(halts(&result).as_slice(), [(0, HaltReason::Branch { .. })]),
                    "terminal={terminal} {modality:?}: {result:#?}"
                );
                assert_eq!(result.passed_stops, [], "terminal={terminal} {modality:?}");
            }
        }
    }

    /// A step with one candidate of a selected stop rule and a remainder goes on through both,
    /// so it passes that stop. `n(X)` rewrites to `done` by `n-zero` where `X == 0`, and the
    /// solver decides nothing, so the step keeps the rest of `n(X)` as a remainder beside the
    /// candidate: the remainder is a successor (stuck, since no other rule applies to it), and the
    /// candidate is not the one successor. The remainder route leaves the candidate's normalization to its own expansion, and the list
    /// names the rule there too; under `StopAtBranch` the step is a `Branch` leaf.
    #[test]
    fn passed_stop_is_listed_where_a_stop_rule_has_a_remainder_beside_it() {
        let source = r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                sort SortS{} []
                symbol n{}(SortInt{}) : SortS{} [constructor{}()]
                symbol done{}() : SortS{} [constructor{}()]
                hooked-symbol eqInt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.eq"), smt-hook{}("=")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(
                        n{}(X:SortInt{}),
                        \equals{SortBool{}, SortS{}}(
                            eqInt{}(X:SortInt{}, \dv{SortInt{}}("0")),
                            \dv{SortBool{}}("true")
                        )
                    ),
                    done{}()
                ) [label{}("n-zero")]
            endmodule []"#;
        let syntax = parse_definition(source).expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let start = Pattern {
            term: definition
                .internalize_term(&parse_pattern("n{}(X:SortInt{})").unwrap(), &[])
                .unwrap(),
            constraints: Vec::new(),
        };
        for terminal in [false, true] {
            for branch_mode in [
                ExecutionBranchMode::ExploreAll,
                ExecutionBranchMode::StopAtBranch,
            ] {
                let selected = BTreeSet::from(["n-zero".to_owned()]);
                let (cut_point_rules, terminal_rules) = if terminal {
                    (BTreeSet::new(), selected)
                } else {
                    (selected, BTreeSet::new())
                };
                let solver = DeadlineAtQuery {
                    nth: 0,
                    queries: std::cell::Cell::new(0),
                };
                let result = super::super::execute_disjunction_with_solver_and_observer(
                    &definition,
                    vec![start.clone()],
                    ExecutionOptions {
                        cut_point_rules,
                        terminal_rules,
                        branch_mode,
                        ..ExecutionOptions::default()
                    },
                    &solver,
                    |_| {},
                );
                let label = format!("terminal={terminal} {branch_mode:?}: {result:#?}");
                if branch_mode == ExecutionBranchMode::StopAtBranch {
                    assert!(
                        matches!(
                            result.leaves.as_slice(),
                            [ExecutionLeaf {
                                halt_reason: HaltReason::Branch { .. },
                                ..
                            }]
                        ),
                        "{label}"
                    );
                    assert_eq!(result.passed_stops, [], "{label}");
                } else {
                    // `done` at depth 1, and the remainder, where no rule applies, at depth 0.
                    let mut halts = result
                        .leaves
                        .iter()
                        .map(|leaf| (leaf.depth, leaf.halt_reason.clone()))
                        .collect::<Vec<_>>();
                    halts.sort_by_key(|(depth, _)| *depth);
                    assert_eq!(
                        halts,
                        [(0, HaltReason::Stuck), (1, HaltReason::Stuck)],
                        "{label}"
                    );
                    assert_eq!(
                        result.passed_stops,
                        [PassedStop {
                            depth: 0,
                            rule: "n-zero".to_owned(),
                        }],
                        "{label}"
                    );
                }
            }
        }
    }

    /// Under strategy any the sequential step takes one successor of `a`, `to-b`'s (its first
    /// rule), and never tries `to-c`; but `a` has two successors, so that step is no arrival.
    /// The run goes on through it as through any other step, without counting it, and lists it
    /// as a passed stop; its one arrival is `to-e`'s, the one successor of `d`, so a count of 2
    /// is never reached. From `u` the selected `u-b` is the one successor, since `u-bottom`'s
    /// successor is undefined, so the run stops there. Every end of the one path is an end of
    /// the same run under strategy all, which passes the same stop.
    #[test]
    fn a_stop_rule_the_sequential_step_takes_beside_another_successor_is_passed() {
        let definition = definition(
            r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(\dv{SortS{}}("a"), \top{SortS{}}()), \dv{SortS{}}("b")
            ) [label{}("to-b")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(\dv{SortS{}}("a"), \top{SortS{}}()), \dv{SortS{}}("c")
            ) [label{}("to-c")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(\dv{SortS{}}("b"), \top{SortS{}}()), \dv{SortS{}}("d")
            ) [label{}("b-d")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(\dv{SortS{}}("d"), \top{SortS{}}()), \dv{SortS{}}("e")
            ) [label{}("to-e")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(\dv{SortS{}}("u"), \top{SortS{}}()),
                \and{SortS{}}(\dv{SortS{}}("x"), \bottom{SortS{}}())
            ) [label{}("u-bottom")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(\dv{SortS{}}("u"), \top{SortS{}}()), \dv{SortS{}}("b")
            ) [label{}("u-b")]
            "#,
        );
        let state = |value: &str| Pattern {
            term: definition
                .internalize_term(
                    &parse_pattern(&format!(r#"\dv{{SortS{{}}}}("{value}")"#)).unwrap(),
                    &[],
                )
                .unwrap(),
            constraints: Vec::new(),
        };
        let selected = || BTreeSet::from(["to-b".to_owned(), "to-e".to_owned(), "u-b".to_owned()]);
        let run = |start: &str, terminal: bool, count: u64, mode| {
            let (cut_point_rules, terminal_rules) = if terminal {
                (BTreeSet::new(), selected())
            } else {
                (selected(), BTreeSet::new())
            };
            super::super::execute(
                &definition,
                state(start),
                ExecutionOptions {
                    cut_point_rules,
                    terminal_rules,
                    stop_count: NonZeroU64::new(count).unwrap(),
                    mode,
                    retain_trace: true,
                    result_modality: ResultModality::StateSet,
                    ..ExecutionOptions::default()
                },
            )
        };
        let ends = |result: &ExecutionResult| {
            let mut ends = result
                .leaves
                .iter()
                .map(|leaf| {
                    let value = match &crate::externalize::term(&leaf.pattern.term) {
                        k_rust_kore::kore::ast::Pattern::DomainValue { value, .. } => {
                            value.as_utf8().unwrap().to_owned()
                        }
                        other => format!("{other:?}"),
                    };
                    (value, leaf.depth, halt_name(&leaf.halt_reason), leaf.stops)
                })
                .collect::<Vec<_>>();
            ends.sort();
            ends
        };
        let passed = |depth| {
            vec![PassedStop {
                depth,
                rule: "to-b".to_owned(),
            }]
        };
        for terminal in [false, true] {
            let context = format!("terminal={terminal}");
            // The one arrival: before `to-e` at `d`, or after it at `e`.
            let stop = if terminal {
                ("e".to_owned(), 3, "stop", 1)
            } else {
                ("d".to_owned(), 2, "stop", 1)
            };
            let one = run("a", terminal, 1, ExecutionMode::Any);
            assert_eq!(
                ends(&one),
                std::slice::from_ref(&stop),
                "{context}: {one:#?}"
            );
            assert_eq!(one.passed_stops, passed(0), "{context}");
            let trace = &one.leaves[0].trace;
            assert_eq!(
                rewrite_labels(trace)[..2],
                ["to-b".to_owned(), "b-d".to_owned()],
                "{context}: the passed step is taken"
            );
            // The count counts `to-e`'s arrival only.
            let two = run("a", terminal, 2, ExecutionMode::Any);
            assert_eq!(
                ends(&two),
                [("e".to_owned(), 3, "stuck", 1)],
                "{context}: {two:#?}"
            );
            assert_eq!(two.passed_stops, passed(0), "{context}");
            // Strategy all takes both successors of `a`, passing the same stop; the one path's
            // end is among its ends.
            let all = run("a", terminal, 1, ExecutionMode::All);
            assert_eq!(
                ends(&all),
                [("c".to_owned(), 1, "stuck", 0), stop],
                "{context}: {all:#?}"
            );
            assert_eq!(all.passed_stops, passed(0), "{context}");
            // An undefined sibling is no successor: `u-b`'s step is an arrival.
            let sole = run("u", terminal, 1, ExecutionMode::Any);
            let stop = if terminal {
                ("b".to_owned(), 1, "stop", 1)
            } else {
                ("u".to_owned(), 0, "stop", 1)
            };
            assert_eq!(ends(&sole), [stop], "{context}: {sole:#?}");
            assert_eq!(sole.passed_stops, [], "{context}");
        }
    }

    /// A reading that marks the candidates whose path condition applies `gate` as denoting no
    /// state, and records whether each question said the run left a hook unevaluated.
    #[derive(Default)]
    struct NoGate {
        asked: std::cell::RefCell<Vec<bool>>,
    }

    impl SuccessorReading for NoGate {
        fn denotes_no_state(&self, candidate: &super::stop_condition::Candidate<'_>) -> bool {
            self.asked.borrow_mut().push(candidate.hooks_unevaluated());
            let mut pending = candidate.path_condition().iter().collect::<Vec<_>>();
            while let Some(pattern) = pending.pop() {
                if matches!(
                    pattern,
                    k_rust_kore::kore::ast::Pattern::Application { symbol, .. }
                        if symbol.name == "gate"
                ) {
                    return true;
                }
                pending.extend(k_rust_kore::kore::walk::children(pattern));
            }
            false
        }
    }

    /// A solver that shows neither a condition nor its negation, so that a rule's condition
    /// over an unevaluated application is the condition of a candidate.
    struct Contingent;

    impl SmtSolver for Contingent {
        fn is_sat(
            &self,
            _predicates: &[Predicate],
            _substitution: &crate::substitution::Substitution,
        ) -> Stoppable<Result<crate::smt::Satisfiability, crate::smt::SmtError>> {
            Ok(Ok(crate::smt::Satisfiability::Sat))
        }

        fn check_predicates(
            &self,
            _known: &[Predicate],
            _substitution: &crate::substitution::Substitution,
            _checked: &[Predicate],
        ) -> Stoppable<Result<crate::smt::Validity, crate::smt::SmtError>> {
            Ok(Ok(crate::smt::Validity::Contingent))
        }
    }

    /// `tick` and `leap` both rewrite `s(0)`, `tick` (the first, which the sequential step
    /// takes) to `s(1)` and `leap` to `s(5)` where `gate(0) == 1`, over a partial `gate` with no
    /// equation. The backend reads `leap`'s candidate as a successor under that condition, so
    /// `tick`'s step is no arrival and is passed, under either strategy; a caller's reading that
    /// says `leap`'s candidate denotes no state makes `tick`'s step the state's one successor,
    /// an arrival where the path stops, before or after `tick`, under either strategy. Where the
    /// all-path step does not decide `leap`'s condition (no solver), whether `tick`'s step taken
    /// under strategy any is an arrival is undecided, and the path ends at `s(0)` with that
    /// step's halt instead of going on past a possible stop.
    #[test]
    fn a_callers_reading_decides_whether_a_stop_rules_step_is_an_arrival() {
        let source = r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                sort SortS{} []
                symbol s{}(SortInt{}) : SortS{} [constructor{}()]
                symbol gate{}(SortInt{}) : SortInt{} [function{}()]
                hooked-symbol eqInt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.eq"), smt-hook{}("=")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(s{}(\dv{SortInt{}}("0")), \top{SortS{}}()),
                    s{}(\dv{SortInt{}}("1"))
                ) [label{}("tick")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(
                        s{}(\dv{SortInt{}}("0")),
                        \equals{SortBool{}, SortS{}}(
                            eqInt{}(gate{}(\dv{SortInt{}}("0")), \dv{SortInt{}}("1")),
                            \dv{SortBool{}}("true")
                        )
                    ),
                    s{}(\dv{SortInt{}}("5"))
                ) [label{}("leap")]
            endmodule []"#;
        let syntax = parse_definition(source).expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let start = Pattern {
            term: definition
                .internalize_term(&parse_pattern(r#"s{}(\dv{SortInt{}}("0"))"#).unwrap(), &[])
                .unwrap(),
            constraints: Vec::new(),
        };
        let run = |terminal: bool, mode, solver: &dyn SmtSolver, reading: Option<&NoGate>| {
            let selected = BTreeSet::from(["tick".to_owned()]);
            let (cut_point_rules, terminal_rules) = if terminal {
                (BTreeSet::new(), selected)
            } else {
                (selected, BTreeSet::new())
            };
            crate::rewrite::execute_in_process(
                &definition,
                start.clone(),
                ExecutionOptions {
                    cut_point_rules,
                    terminal_rules,
                    mode,
                    ..ExecutionOptions::default()
                },
                solver,
                None,
                InProcess {
                    condition: None,
                    reading: reading.map(|reading| -> &dyn SuccessorReading { reading }),
                    probe: None,
                },
            )
            .unwrap()
        };
        let ends = |result: &ExecutionResult| {
            let mut ends = result
                .leaves
                .iter()
                .map(|leaf| {
                    let value = match &crate::externalize::term(&leaf.pattern.term) {
                        k_rust_kore::kore::ast::Pattern::Application { arguments, .. } => {
                            match arguments.as_slice() {
                                [k_rust_kore::kore::ast::Pattern::DomainValue { value, .. }] => {
                                    value.as_utf8().unwrap().to_owned()
                                }
                                other => format!("{other:?}"),
                            }
                        }
                        other => format!("{other:?}"),
                    };
                    let halt = match &leaf.halt_reason {
                        HaltReason::Indeterminate(IndeterminateReason::Requires { .. }) => {
                            "indeterminate"
                        }
                        halt => halt_name(halt),
                    };
                    (value, leaf.depth, halt, leaf.stops)
                })
                .collect::<Vec<_>>();
            ends.sort();
            ends
        };
        let passed = || {
            vec![PassedStop {
                depth: 0,
                rule: "tick".to_owned(),
            }]
        };
        for terminal in [false, true] {
            for mode in [ExecutionMode::Any, ExecutionMode::All] {
                let context = format!("terminal={terminal}, mode={mode:?}");
                // The backend's own reading: `leap`'s conditional candidate is a successor.
                let open = run(terminal, mode, &Contingent, None);
                let expected = match mode {
                    ExecutionMode::Any => vec![("1".to_owned(), 1, "stuck", 0)],
                    ExecutionMode::All => vec![
                        ("1".to_owned(), 1, "stuck", 0),
                        ("5".to_owned(), 1, "stuck", 0),
                    ],
                };
                assert_eq!(ends(&open), expected, "{context}: {open:#?}");
                assert_eq!(open.passed_stops, passed(), "{context}");
                // The caller's reading: `leap`'s candidate denotes no state, so `tick`'s step is
                // the state's one successor.
                let reading = NoGate::default();
                let read = run(terminal, mode, &Contingent, Some(&reading));
                let stop = if terminal {
                    ("1".to_owned(), 1, "stop", 1)
                } else {
                    ("0".to_owned(), 0, "stop", 1)
                };
                assert_eq!(ends(&read), [stop], "{context}: {read:#?}");
                assert_eq!(read.passed_stops, [], "{context}");
                let asked = reading.asked.borrow();
                assert!(
                    !asked.is_empty() && asked.iter().all(|hooks| !hooks),
                    "{context}: {asked:?}"
                );
            }
            // Under strategy any with no solver, `leap`'s condition is undecided in the
            // all-path step, so whether `tick`'s step is an arrival is too: the path ends at
            // `s(0)`, neither stopping nor passing.
            for reading in [None, Some(&NoGate::default())] {
                let undecided = run(terminal, ExecutionMode::Any, &crate::smt::NoSolver, reading);
                assert_eq!(
                    ends(&undecided),
                    [("0".to_owned(), 0, "indeterminate", 0)],
                    "terminal={terminal}: {undecided:#?}"
                );
                assert_eq!(undecided.passed_stops, [], "terminal={terminal}");
            }
        }
    }
}
