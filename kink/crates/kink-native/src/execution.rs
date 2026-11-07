//! Time-bounded execution through the public k-rust facade (re-pin lane 1, L1-1).
//!
//! A result run ([`ExecutionAdapter::execute`], [`ExecutionAdapter::execute_result`]) is one
//! unobserved run whose leaves are, by default, k-rust's state set: structurally equal final
//! configurations merged ([`ResultModality::StateSet`]), whatever its leaves (fz26
//! KINK-PATHSET-FALLBACK). A state set's undefined steps (`Trivial`) and `Vacuous` leaves are
//! never merged: the leaf of an undefined step names the rule of the step from its own
//! configuration, which every path to that configuration and depth takes, and every contradicted
//! claim the run met, absorbed arrivals' included, is on its `contradictedClaims` list, which the
//! exclusions read ([`crate::exclusion`]). A stepped run ([`ExecutionAdapter::execute_steps`])
//! stays an observed path set: one leaf per path, each with its own configuration sequence.
//! Every run carries no trace and collects k-rust's run coverage ([`RunCoverage`]), and a
//! cancelled run answers an error, so a timed-out run publishes no leaf. A watchdog cancels
//! execution when the time budget expires; a result run may also carry a work budget
//! (`max_work`), whose `work-bound` leaf makes the run incomplete.
//! Each leaf also records whether its state is shown feasible or infeasible, and an
//! indeterminate leaf its structured cause; the execution records the definition facts the
//! bridge needs to use them ([`crate::feasibility`]).
//! Every run also carries k-rust's run-level facts ([`RunFacts`], re-pin adoption A-1): the lists
//! of open values read, contradicted claims, allowance refusals, unsupported hooks and
//! short-circuit readings, and the count of undecided solver answers, which the exclusions read
//! ([`crate::exclusion`]), with what the adapter knows of the recording ([`RecordedRun`]).
//! A result run may also carry stop rules ([`StopRules`]): its paths then end at a step of a
//! selected rule that is its state's one successor, and its facts list each selected rule it went
//! on past because the step had another successor ([`RunFacts::passed_stops`]). Such a run may
//! also carry an in-process stop condition ([`StopCondition`], k-rust
//! `Backend::execute_kore_with_condition`), which k-rust asks at each arrival at a stop: a path
//! then ends at its `count`th arrival where the condition holds, a leaf where it was left
//! undecided is `stop-undecided`, and a refusal fails the run
//! ([`ExecutionAdapterFailure::StopCondition`]).

use std::{
    cell::Cell,
    collections::{BTreeMap, BTreeSet},
    num::{NonZeroU64, NonZeroUsize},
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
        mpsc,
    },
    thread,
    time::Duration,
};

use k_rust::backend::BackendErrorKind;
use k_rust::backend::{
    AxiomGuardOutput, BACKEND_SCHEMA_VERSION, Backend, BackendCapabilities,
    BackendDiagnosticOutput, BackendError, CancelledResultOutput, ChosenValueOutput,
    ContradictedClaimOutput, ContradictedTotalOutput, EffectOutput, ExecuteRequest,
    ExecutionStrategy, GuardCollection, HaltReasonOutput, KoreExecutionLeaf, KoreExecutionResult,
    ObservationEventOutput, ObservedInOutput, ObservedRequest, PassedStopOutput,
    ResultModalityOutput, RunCoverageOutput, SearchFailureOutput, ShortCircuitReadingOutput,
    TraceEntry, TransitionClassOutput, TransitionIdOutput, UnevaluatedHookOutput,
};
pub use k_rust::backend::{StopArrival, StopCondition, StopDecision, StopSide};
use k_rust::kore::ast::Pattern;
use k_rust_backend::stop::{CancellationToken, StopCause};
use kink_pattern::ExecutionBounds;

use crate::feasibility::{Inhabitation, LeafFeasibility, leaf_feasibility, uninhabited_variable};
use crate::observation::AdaptedBranch;

/// The closed halt reasons of an execution leaf.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum HaltClass {
    Stuck,
    Trivial,
    Vacuous,
    Branch,
    CutPoint,
    TerminalRule,
    DepthBound,
    BreadthBound,
    Indeterminate,
    UnsupportedHook,
    SimplificationError,
    Timeout,
    Cancelled,
    /// k-rust's `work-bound` halt (`max_work` reached): the state as taken from the worklist,
    /// unexpanded and unnormalised, and the pending states dropped. The adapter admits it only
    /// for a request that set `max_work` ([`HaltClass::admitted_by`]); it never completes a run.
    WorkBound,
    /// k-rust's `stop-undecided` halt: a stop condition was left undecided at an arrival, and
    /// the path ends there, its state the arrival's stop state. Only an in-process request with
    /// a stop condition has it ([`ExecutionAdapter::execute_result_counted`]): the adapter admits
    /// it exactly for such a request ([`Requested::admits`]), never by [`HaltClass::admitted_by`],
    /// which judges the wire request alone. It never completes a run.
    StopUndecided,
}

impl HaltClass {
    pub const ALL: [Self; 15] = [
        Self::Stuck,
        Self::Trivial,
        Self::Vacuous,
        Self::Branch,
        Self::CutPoint,
        Self::TerminalRule,
        Self::DepthBound,
        Self::BreadthBound,
        Self::Indeterminate,
        Self::UnsupportedHook,
        Self::SimplificationError,
        Self::Timeout,
        Self::Cancelled,
        Self::WorkBound,
        Self::StopUndecided,
    ];

    /// Whether the adapter's request can yield this halt under `budget`, for a request without
    /// a work budget and without stop rules (every stepped run, and a result run without
    /// `max_work` or a [`StopRules`]).
    #[must_use]
    pub const fn adapter_admits(self, budget: &ExecutionBudget) -> bool {
        self.admitted_by(budget, None, &NO_STOP_RULES)
    }

    /// Whether the adapter's request can yield this halt under `budget`, `max_work` and `stop`.
    /// A `Cancelled` leaf never: every request answers a cancellation with an error
    /// (`cancelled_result: error`, re-pin finding A-03). A `Branch` leaf never: the request does
    /// not stop at a branch. A `work-bound` leaf exactly when the request set `max_work`; a
    /// `cut-point` leaf exactly when `stop` names a rule to stop before (`cut_point_rules`), and
    /// a `terminal` leaf exactly when it names one to stop after (`terminal_rules`): k-rust stops
    /// a path at no other rule.
    #[must_use]
    pub const fn admitted_by(
        self,
        budget: &ExecutionBudget,
        max_work: Option<u64>,
        stop: &StopRules,
    ) -> bool {
        match self {
            Self::Stuck
            | Self::Trivial
            | Self::Vacuous
            | Self::Indeterminate
            | Self::UnsupportedHook
            | Self::SimplificationError => true,
            Self::DepthBound => budget.max_depth.is_some(),
            Self::BreadthBound => budget.max_breadth.is_some(),
            Self::WorkBound => max_work.is_some(),
            Self::CutPoint => !stop.before.is_empty(),
            Self::TerminalRule => !stop.after.is_empty(),
            Self::Branch | Self::Timeout | Self::Cancelled | Self::StopUndecided => false,
        }
    }

    /// Convert the public backend enum exhaustively.
    #[must_use]
    pub const fn from_output(reason: HaltReasonOutput) -> Self {
        match reason {
            HaltReasonOutput::Stuck => Self::Stuck,
            HaltReasonOutput::Trivial => Self::Trivial,
            HaltReasonOutput::Vacuous => Self::Vacuous,
            HaltReasonOutput::Branch => Self::Branch,
            HaltReasonOutput::CutPoint => Self::CutPoint,
            HaltReasonOutput::Terminal => Self::TerminalRule,
            HaltReasonOutput::DepthBound => Self::DepthBound,
            HaltReasonOutput::BreadthBound => Self::BreadthBound,
            HaltReasonOutput::Indeterminate => Self::Indeterminate,
            HaltReasonOutput::UnsupportedHook => Self::UnsupportedHook,
            HaltReasonOutput::SimplificationError => Self::SimplificationError,
            HaltReasonOutput::Timeout => Self::Timeout,
            HaltReasonOutput::Cancelled => Self::Cancelled,
            HaltReasonOutput::WorkBound => Self::WorkBound,
            HaltReasonOutput::StopUndecided => Self::StopUndecided,
        }
    }
}

// One build is one profile only while this crate's `z3` feature and k-rust's `z3-inference` are
// on together: in a workspace where another member enables k-rust's default features (k-rust's
// own workspace), k-rust would run Z3 under a kink that selects and expects no-Z3. Fail the build
// rather than reject every backend at run time.
const _: () = assert!(
    cfg!(feature = "z3") == k_rust::Z3_INFERENCE,
    "kink-native's `z3` feature must be on exactly when k-rust's `z3-inference` is"
);

/// The solver profile of a backend. k-rust chooses its solver at compile time, so one build is
/// one profile: `NoZ3` without the `z3` feature of this crate, `Z3` with it.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum SolverProfile {
    /// k-rust's `NoSolver`: every SMT query is unavailable. The qualified profile.
    NoZ3,
    /// k-rust built with `z3-inference`.
    Z3,
}

impl SolverProfile {
    /// The profile this build of kink-native selects: `Z3` exactly when its `z3` feature is
    /// on. The feature forwards to k-rust, so a backend of this build reports the same profile
    /// unless another crate changed k-rust's features, which the adapter then rejects.
    pub const BUILD: Self = if cfg!(feature = "z3") {
        Self::Z3
    } else {
        Self::NoZ3
    };

    /// The profile whose backend reports `smt` capability `smt`.
    #[must_use]
    pub const fn from_smt(smt: bool) -> Self {
        if smt { Self::Z3 } else { Self::NoZ3 }
    }

    /// The profile `backend` actually runs in.
    #[must_use]
    pub fn of(backend: &Backend) -> Self {
        Self::from_smt(backend.capabilities().smt)
    }

    /// The report name: `"no-z3"` or `"z3"`.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::NoZ3 => "no-z3",
            Self::Z3 => "z3",
        }
    }
}

/// Limits of one execution.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ExecutionBudget {
    /// Wall-clock budget of one run (the watchdog's).
    pub time: Duration,
    /// Simplifier iterations per rewrite step. Exhaustion is a backend diagnostic.
    pub max_simplification_iterations: usize,
    /// Maximum rewrite depth of each path.
    pub max_depth: Option<u64>,
    /// Maximum pending-frontier width.
    pub max_breadth: Option<NonZeroUsize>,
}

impl ExecutionBudget {
    /// Pattern bounds. `branches` is k-rust's pending-frontier width, not a total branch count.
    #[must_use]
    pub fn bounds(&self) -> ExecutionBounds {
        ExecutionBounds {
            depth: self.max_depth,
            time_ms: Some(u64::try_from(self.time.as_millis()).unwrap_or(u64::MAX)),
            branches: self.max_breadth.map(|breadth| breadth.get() as u64),
            results: None,
        }
    }
}

/// The result modality of a result run (k-rust `result_modality`).
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ResultModality {
    /// One leaf per explored path.
    PathSet,
    /// Structurally equal final configurations merged, each distinct state of a depth expanded
    /// once (k-rust's default). Its complete results have exactly the distinct final
    /// configurations of the path set of the same request, diagnostics included (re-pin
    /// decision 3: k-rust executes the definition correctly, its merge included). It has fewer
    /// leaves where paths converge, and it can be complete where the path set of the same
    /// bounds is not: an earlier stuck leaf absorbs a later depth-bound or indeterminate leaf of
    /// its configuration (k-rust `docs/backend-port.md`, "Final search depth cuts"; re-pin
    /// L1-1-fix-1).
    #[default]
    StateSet,
}

impl ResultModality {
    const fn output(self) -> ResultModalityOutput {
        match self {
            Self::PathSet => ResultModalityOutput::PathSet,
            Self::StateSet => ResultModalityOutput::StateSet,
        }
    }

    /// The report name: `"path-set"` or `"state-set"`.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::PathSet => "path-set",
            Self::StateSet => "state-set",
        }
    }
}

/// How a result run is requested besides its [`ExecutionBudget`]: its modality, its work
/// budget (k-rust `max_work`: the most states the run may visit across all its paths), and
/// whether its coverage collects guard outcomes (`guards`). The default is a state set without a
/// work budget or guard outcomes.
///
/// With `guards`, the request names every rewrite rule and function equation of the definition
/// whose `requires` is not empty (k-rust `collect_guards`), and the run's coverage carries their
/// guard outcomes ([`RunCoverage::guards`]). k-rust states that asking changes no other field of
/// the result (docs/compatibility.md, "Run coverage"), so no leaf, list, set, verdict or
/// schedule differs from a run without it.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct ResultRun {
    pub modality: ResultModality,
    pub max_work: Option<u64>,
    pub guards: bool,
}

/// The stop rules of a result run (k-rust `cut_point_rules` and `terminal_rules`), each rule
/// named as k-rust selects it: by its label or its `UNIQUE_ID`. The names are passed as given;
/// that each selects a rewrite rule of the definition run is the caller's to check.
///
/// A selected rule stops a path only where its step is the state's one successor
/// (k-rust `docs/compatibility.md`, "Passed stops"):
/// - a rule of `before` ends the path at the state the step leaves, as a `cut-point` leaf that
///   proposes the step's successor without taking it ([`AdaptedLeaf::proposal`]);
/// - a rule of `after` ends the path at the step's successor, as a `terminal` leaf.
///
/// Each such leaf is a final configuration of the truncated system, the system that ends a path
/// at every step of a selected rule: a cut-point leaf's one successor is by a rule of `before`,
/// and a terminal leaf was reached by a step of a rule of `after`. Neither is a fact of the
/// order in which the run explored its states, so the bridge reads both as it reads a stuck leaf
/// ([`crate::bridge::halt_stop`]). A step of a selected rule that has another successor stops
/// nothing, and k-rust lists the rule ([`RunFacts::passed_stops`]); the run's leaves are then not
/// the truncated system's final configurations, and the run is excluded
/// ([`crate::exclusion::Exclusion::PassedStop`]).
///
/// The default names no rule: the run ends where its paths end, as before stop rules existed.
#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct StopRules {
    /// The rules a path stops before (`cut_point_rules`).
    pub before: Vec<String>,
    /// The rules a path stops after (`terminal_rules`).
    pub after: Vec<String>,
}

impl StopRules {
    /// No stop rule: the run ends where its paths end.
    pub const NONE: Self = Self {
        before: Vec::new(),
        after: Vec::new(),
    };

    /// Whether this names no rule.
    #[must_use]
    pub const fn is_none(&self) -> bool {
        self.before.is_empty() && self.after.is_empty()
    }
}

/// No stop rule ([`StopRules::NONE`]), for a request that selects none.
static NO_STOP_RULES: StopRules = StopRules::NONE;

/// What one request asks for besides its [`ExecutionBudget`]: `run`'s modality and work budget,
/// the stop rules `stop`, the arrival at a stop at which a path ends, `count`, and whether an
/// in-process stop condition is asked at the arrivals (`conditioned`). The request is built from
/// it ([`request`]; the condition is no field of it), and the halts its result may hold and the
/// arrivals each leaf reports are read from it ([`Self::admits`], [`Self::admits_arrivals`]).
#[derive(Clone, Copy, Debug)]
struct Requested<'a> {
    run: ResultRun,
    stop: &'a StopRules,
    count: NonZeroU64,
    conditioned: bool,
    /// The axioms whose guard outcomes the request collects, when `run.guards` asks for them.
    guards: Option<&'a BTreeSet<String>>,
}

impl Requested<'static> {
    /// `run` without stop rules.
    const fn unstopped(run: ResultRun) -> Self {
        Self {
            run,
            stop: &NO_STOP_RULES,
            count: NonZeroU64::MIN,
            conditioned: false,
            guards: None,
        }
    }
}

impl Requested<'_> {
    /// The count the request sends (k-rust `stop_count`): `count` when it is past the first
    /// arrival and some rule is selected, `None` otherwise. A path ends at its first arrival
    /// without a count, and has no arrival without a selected rule, so leaving the count out
    /// there asks for exactly the run it names, with the request of a run without a count.
    fn stop_count(self) -> Option<NonZeroU64> {
        (self.count > NonZeroU64::MIN && !self.stop.is_none()).then_some(self.count)
    }

    /// Whether the request can yield a leaf of halt `halt` under `budget`: as
    /// [`HaltClass::admitted_by`] judges the wire request, and a `stop-undecided` leaf exactly
    /// when a stop condition was asked, which only that halt reveals.
    const fn admits(self, halt: HaltClass, budget: &ExecutionBudget) -> bool {
        match halt {
            HaltClass::StopUndecided => self.conditioned && !self.stop.is_none(),
            _ => halt.admitted_by(budget, self.run.max_work, self.stop),
        }
    }

    /// Whether a leaf of halt `halt` that reports `stops` arrivals at a stop (k-rust
    /// `ExecutionLeaf::stops`) is one the request can yield. Without a count k-rust reports
    /// none. With one, a `cut-point` or `terminal` leaf ends its path at the count's arrival, so
    /// it reports the count, and any other leaf ended its path before it, so it reports fewer.
    /// A stop leaf short of the count would otherwise be read as an end of the truncated system
    /// that its path has not reached.
    ///
    /// With a stop condition k-rust reports each leaf's events (`stops`) whatever the count,
    /// the first included, and every arrival its path passed (`ExecutionLeaf::arrivals`),
    /// whatever the condition answered there; a leaf that reports arrivals where no condition was
    /// asked, or none where one was, is not the answer to this request. A `stop-undecided` leaf
    /// ends its path at an arrival that is no event, so it reports fewer events than the count,
    /// as any other leaf that is not a stop leaf.
    fn admits_arrivals(self, halt: HaltClass, stops: Option<u64>, arrivals: Option<u64>) -> bool {
        if arrivals.is_some() != self.conditioned {
            return false;
        }
        let counted = self
            .stop_count()
            .or_else(|| (self.conditioned && !self.stop.is_none()).then_some(self.count));
        match (counted, stops) {
            (None, None) => true,
            (None, Some(_)) | (Some(_), None) => false,
            (Some(count), Some(stops)) => match halt {
                HaltClass::CutPoint | HaltClass::TerminalRule => stops == count.get(),
                _ => stops < count.get(),
            },
        }
    }
}

/// k-rust's run coverage of one run (`collect_coverage`, `RunCoverageOutput`), by `UNIQUE_ID`:
/// every rule and equation the run applied, every one whose condition it began to decide
/// (`matched`, a superset; the two are what kink schedules by, [`crate::coverage::TestCoverage`]),
/// the rewrite rules among `applied`: those for which a step built a successor or found the step
/// undefined, which a stepped path set's branch identities also name (the L1-1 differential
/// compares them), and the rewrite rules whose successor the run committed to (`committed`,
/// `collect_committed`, a subset of `applied`): a step built a successor of the rule that its own
/// normalization showed defined, so some explored path takes the rule's step. A candidate rolled
/// back because its successor was undefined and an undefined step's rule are in `applied` only:
/// no path takes them. It covers every state the run explored, including leaves a state set
/// merges away. Coverage is a scheduling and report input only.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct RunCoverage {
    pub applied: BTreeSet<String>,
    pub matched: BTreeSet<String>,
    pub applied_rewrites: BTreeSet<String>,
    /// Empty when the run's coverage did not report it (every run [`request`] builds asks).
    pub committed: BTreeSet<String>,
    /// The guard outcomes of the axioms the request named ([`ResultRun::guards`]), by id;
    /// empty when the run did not collect them.
    pub guards: Vec<AxiomGuardOutput<Pattern>>,
}

impl RunCoverage {
    fn of(output: RunCoverageOutput<Pattern>, rewrites: &BTreeSet<String>) -> Self {
        let applied = output.applied.into_iter().collect::<BTreeSet<_>>();
        let applied_rewrites = applied.intersection(rewrites).cloned().collect();
        Self {
            applied,
            matched: output.matched.into_iter().collect(),
            applied_rewrites,
            committed: output.committed.into_iter().flatten().collect(),
            guards: output.guards.unwrap_or_default(),
        }
    }
}

/// The run-level facts of one run (re-pin adoption A-1):
/// the lists and the count k-rust 58720d2e5 added to `ExecutionResult` (KINK-17/1, KINK-18/2,
/// KINK-19/1), as k-rust answers them, for every run kink judges: a result run, a stepped run and
/// an unobserved run. Each list holds what the run's leaves
/// carry and also what no leaf carries (k-rust `docs/compatibility.md` at 0068938b1, lines 92,
/// 1659 and 1913): work that ended on no reported leaf (a candidate a defined sibling covered, a
/// state a state-set merge absorbed), an attempt undone or an equation passed over, and the load of
/// the definition (`observedIn: load`). kink reads the lists, not the leaves' marks, for every
/// exclusion ([`crate::exclusion::DefinitionExclusions::run_exclusion`]). A timed-out run has none:
/// it is a timeout before it is anything else.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct RunFacts {
    /// The undecided answers the solver gave the run's decisions (`smtUnknowns`); always 0 in a
    /// build without a solver. Reported, never an exclusion (decision D-7 (a1): kink re-decides
    /// every leaf's feasibility itself, so an undecided answer can make a comparison unknown,
    /// never a kill).
    pub smt_unknowns: usize,
    /// kink's own count beside k-rust's: the undecided answers the solver gave the questions the
    /// adapter asked about the run's leaves (their feasibility, `crate::feasibility`, "Undecided
    /// answers"), outside the run's request; 0 in a build without a solver, for a timed-out run
    /// and for a result adapted from outside ([`ExecutionAdapter::adapt_result`]) unless its
    /// caller states the count ([`AdaptedExecution::with_decider_smt_unknowns`]). Reported,
    /// never an exclusion, for the reason `smt_unknowns` is not one.
    pub decider_smt_unknowns: usize,
    /// Every distinct value the definition leaves open that the run read
    /// (`implementationChosenValues`): its hook and class.
    pub implementation_chosen_values: Vec<ChosenValueOutput>,
    /// Every distinct contradicted claim the run or its definition's load observed
    /// (`contradictedClaims`), ground or not.
    pub contradicted_claims: Vec<ContradictedClaimOutput<Pattern>>,
    /// Every distinct `Bytes` result the memory allowance refused in the run or its load
    /// (`allowanceRefusals`), kept or dropped work alike.
    pub allowance_refusals: Vec<UnevaluatedHookOutput>,
    /// Every other application the run or its load left unevaluated as an unsupported hook
    /// (`unsupportedHooks`), whatever became of the work that met it.
    pub unsupported_hooks: Vec<UnevaluatedHookOutput>,
    /// Every distinct place where the run, or the load of its definition, used the strict
    /// definedness of an operand that a short-circuiting reading skips and did not find it
    /// defined (`shortCircuitReadings`, k-rust `docs/compatibility.md`, "Short-circuit
    /// readings"): each is a reading of the operand after the deciding one of `#if`,
    /// `andThenBool`, `orElseBool`, `andBool`, `orBool` or `impliesBool`, with the rewrite rule
    /// whose work used it. `None` when the backend that recorded the run does not list them
    /// (its `short_circuit_readings` capability is off): the result's absent field is then no
    /// list, and a run that listed nothing cannot be told from one that was never asked
    /// ([`RecordedRun`]).
    pub short_circuit_readings: Option<Vec<ShortCircuitReadingOutput<Pattern>>>,
    /// Every selected stop rule the run went on past at a step where the rule was not its
    /// state's one successor, each once with the shallowest depth at which it did
    /// (`passedStops`, k-rust `docs/compatibility.md`, "Passed stops"), in order of depth and
    /// name. Empty for a run without stop rules ([`StopRules`]). Any entry excludes the run
    /// ([`crate::exclusion::Exclusion::PassedStop`]); the entries name the step.
    pub passed_stops: Vec<PassedStopOutput>,
    /// Whether the run started from a state without free variables ([`RecordedRun::ground`]).
    pub ground: bool,
}

/// What kink knows of how a run was recorded, beside what its result says: the facts
/// [`RunFacts`] takes from the recording, not from the result. The adapter knows both for every
/// run it makes; a client that adapts a result it holds ([`ExecutionAdapter::adapt_result`])
/// states them.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RecordedRun {
    /// The `short_circuit_readings` capability of the backend that recorded the result
    /// (`BackendCapabilities::short_circuit_readings`): whether its result lists the run's
    /// short-circuit readings. The list's wire field is omitted when empty, so a result recorded
    /// without the capability reads back as an empty list; only the capability tells a run that
    /// listed nothing from one whose backend never listed anything.
    pub short_circuit_readings: bool,
    /// Whether the run's initial state has no free variables.
    pub ground: bool,
}

impl RecordedRun {
    /// A run `backend` makes from `state`.
    #[must_use]
    pub fn of(backend: &Backend, state: &Pattern) -> Self {
        Self {
            short_circuit_readings: backend.capabilities().short_circuit_readings,
            ground: state.free_variables().is_empty(),
        }
    }
}

impl RunFacts {
    /// The facts of `result`, taken out of it, as `recorded` was recorded.
    fn take(result: &mut KoreExecutionResult, recorded: RecordedRun) -> Self {
        let short_circuit_readings = std::mem::take(&mut result.short_circuit_readings);
        Self {
            smt_unknowns: result.smt_unknowns,
            decider_smt_unknowns: 0,
            implementation_chosen_values: std::mem::take(&mut result.implementation_chosen_values),
            contradicted_claims: std::mem::take(&mut result.contradicted_claims),
            allowance_refusals: std::mem::take(&mut result.allowance_refusals),
            unsupported_hooks: std::mem::take(&mut result.unsupported_hooks),
            short_circuit_readings: recorded
                .short_circuit_readings
                .then_some(short_circuit_readings),
            passed_stops: std::mem::take(&mut result.passed_stops),
            ground: recorded.ground,
        }
    }

    /// The contradicted-claim records the definition's load observed (`observedIn: load`): facts
    /// about the definition, on every run's list (decision D-6).
    pub fn load_records(&self) -> impl Iterator<Item = &ContradictedClaimOutput<Pattern>> {
        self.contradicted_claims
            .iter()
            .filter(|record| record.observed_in == ObservedInOutput::Load)
    }
}

/// One execution leaf with its typed halt class, diagnostics, adapted branch, and state
/// feasibility.
///
/// A `Stuck` halt says that no instance of the state under its constraints has a rewrite
/// successor, in both profiles; it does not say that the state has an instance, which is what
/// `feasibility` records.
#[derive(Clone, Debug, PartialEq)]
pub struct AdaptedLeaf {
    pub halt: HaltClass,
    pub branch: AdaptedBranch,
    /// `Unknown` for every leaf of a timed-out run, whose states are not read.
    pub feasibility: LeafFeasibility,
    /// Why the step stopped, exactly for an `Indeterminate` halt.
    pub cause: Option<SearchFailureOutput<Pattern>>,
    pub diagnostics: Vec<BackendDiagnosticOutput<Pattern>>,
    pub candidate_diagnostics: Vec<Vec<BackendDiagnosticOutput<Pattern>>>,
    pub remainder_diagnostics: Vec<BackendDiagnosticOutput<Pattern>>,
    /// The rule responsible for the undefined step of a `Trivial` leaf, when k-rust names one;
    /// `None` for every other halt.
    pub undefined_rule: Option<UndefinedStepRule>,
    /// The `total` (or `functional`) claim this leaf's undefined step contradicts, when k-rust
    /// names one (`contradictedTotal`, a `Trivial` or `Vacuous` leaf): the definition is
    /// inconsistent there, so the run is no evidence (re-pin decision 2, finding A-13;
    /// [`crate::exclusion::Exclusion::ContradictedClaim`]).
    pub contradicted_total: Option<ContradictedTotalOutput<Pattern>>,
    /// The step a `CutPoint` leaf stopped before, exactly for that halt ([`StopRules::before`]).
    pub proposal: Option<StopProposal>,
}

/// The step a `cut-point` leaf stopped before: its one successor, by a rule the request selected
/// to stop before. The successor is normalized and defined, as every successor a step keeps, but
/// the run did not take the step: no path commits it, so the rule is applied but not committed in
/// the run's coverage ([`RunCoverage`]). A run to a later arrival at a stop takes the step there
/// ([`ExecutionAdapter::execute_result_counted`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StopProposal {
    /// The successor the step would reach.
    pub successor: Pattern,
    /// The rule's `UNIQUE_ID`.
    pub rule_id: String,
    /// The rule's label, when it has one.
    pub label: Option<String>,
}

impl StopProposal {
    /// The proposal of a leaf of halt `halt` whose step candidates are `candidates`: `None` for
    /// every halt but `CutPoint`, whose one candidate it is. A cut-point leaf with another number
    /// of candidates is outside k-rust's contract (a cut point is a step with one successor).
    fn of(
        halt: HaltClass,
        candidates: Option<&[k_rust::backend::ExecutionCandidateOutput<Pattern>]>,
    ) -> Result<Option<Self>, ExecutionAdapterFailure> {
        if halt != HaltClass::CutPoint {
            return Ok(None);
        }
        match candidates {
            Some([candidate]) => Ok(Some(Self {
                successor: candidate.state.clone(),
                rule_id: candidate.unique_id.clone(),
                label: candidate.label.clone(),
            })),
            _ => Err(ExecutionAdapterFailure::ContractViolation(halt)),
        }
    }
}

/// The rule whose application a `Trivial` leaf's undefined step is: it applies to every
/// instance of the pre-step state under the leaf's predicate, and its result is `\bottom` there.
/// The step commits no transition, so this is the only place the rule is named.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UndefinedStepRule {
    /// k-rust's compiled rule identity, the one `Backend::rule_catalog` and a committed
    /// transition's `TransitionIdOutput::rule` use.
    pub id: String,
    /// The compiled qualified label (`MODULE.label`), when the rule has one.
    pub label: Option<String>,
}

impl UndefinedStepRule {
    /// The rule a facade leaf names, kept only for a `Trivial` halt: the facade gives
    /// `rule_id`/`rule_label` exactly for the rule of an undefined step.
    fn of(halt: HaltClass, rule_id: Option<String>, rule_label: Option<String>) -> Option<Self> {
        (halt == HaltClass::Trivial)
            .then_some(())
            .and(rule_id)
            .map(|id| Self {
                id,
                label: rule_label,
            })
    }
}

/// The adapted leaves of one execution. Built only by [`ExecutionAdapter::execute`] and its
/// siblings.
#[derive(Clone, Debug, PartialEq)]
pub struct AdaptedExecution {
    pub(crate) leaves: Vec<AdaptedLeaf>,
    pub(crate) effects: Vec<EffectOutput>,
    pub(crate) timed_out: bool,
    /// k-rust's count of the stops for lack of native stack the run met (`stackStops`), whether
    /// or not a site dismissed them (re-pin finding A-06).
    pub(crate) stack_stops: usize,
    /// The modality of `leaves`: the request's.
    pub(crate) modality: ResultModality,
    /// k-rust's count of the states the run visited (`work`, the unit `max_work` bounds); 0 for
    /// a timed-out run, which reports no result.
    pub(crate) work: u64,
    /// k-rust's run coverage; `None` for a timed-out run.
    pub(crate) coverage: Option<RunCoverage>,
    /// k-rust's run-level facts (re-pin adoption A-1); empty for a timed-out run.
    pub(crate) facts: RunFacts,
}

/// An observation-layer failure of a stepped run. The execution itself can still be used
/// through an event-free run.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum StepRunFailure {
    AmbiguousRule(String),
    Unobservable,
}

/// One observed run's leaves and configuration sequence for each leaf.
#[derive(Clone, Debug, PartialEq)]
pub struct SteppedExecution {
    pub adapted: AdaptedExecution,
    pub states: Vec<Vec<Pattern>>,
}

/// The leaves of one run without observation rules ([`ExecutionAdapter::execute_unobserved`]).
#[derive(Clone, Debug, PartialEq)]
pub struct UnobservedExecution {
    pub leaves: Vec<BaselineLeaf>,
    /// The watchdog fired before the run ended, as [`AdaptedExecution::timed_out`]: the run is a
    /// timeout and `leaves` is not its path set, whether the backend then returned leaves or an
    /// error (which leaves none).
    pub timed_out: bool,
    /// k-rust's count of the run's stops for lack of native stack, as
    /// [`AdaptedExecution::stack_stops`].
    pub stack_stops: usize,
    /// k-rust's run coverage, as [`AdaptedExecution::coverage`].
    pub coverage: Option<RunCoverage>,
    /// k-rust's run-level facts, as [`AdaptedExecution::facts`].
    pub facts: RunFacts,
}

/// A path-set leaf after observation state is erased: every field of the backend leaf that
/// observation does not produce, and its branch identity.
#[derive(Clone, Debug, PartialEq)]
pub struct BaselineLeaf {
    pub halt: HaltClass,
    pub state: Pattern,
    pub depth: u64,
    pub trace: Vec<TraceEntry>,
    pub cause: Option<SearchFailureOutput<Pattern>>,
    pub diagnostics: Vec<BackendDiagnosticOutput<Pattern>>,
    pub candidate_diagnostics: Vec<Vec<BackendDiagnosticOutput<Pattern>>>,
    pub remainder_diagnostics: Vec<BackendDiagnosticOutput<Pattern>>,
    /// The transition identities of the branch. Empty for an unobserved leaf: k-rust's
    /// unobserved execution does not compute them.
    pub branch: Vec<TransitionIdOutput>,
    pub undefined_rule: Option<UndefinedStepRule>,
    pub contradicted_total: Option<ContradictedTotalOutput<Pattern>>,
}

impl AdaptedExecution {
    /// Erases observations from every leaf while retaining its backend result.
    #[must_use]
    pub fn erased(&self) -> Vec<BaselineLeaf> {
        self.leaves
            .iter()
            .map(|leaf| {
                let branch = leaf.branch.erase_observations();
                BaselineLeaf {
                    halt: leaf.halt,
                    state: branch.state,
                    depth: branch.depth,
                    trace: branch.trace,
                    cause: leaf.cause.clone(),
                    diagnostics: leaf.diagnostics.clone(),
                    candidate_diagnostics: leaf.candidate_diagnostics.clone(),
                    remainder_diagnostics: leaf.remainder_diagnostics.clone(),
                    branch: branch.identity,
                    undefined_rule: leaf.undefined_rule.clone(),
                    contradicted_total: leaf.contradicted_total.clone(),
                }
            })
            .collect()
    }

    #[must_use]
    pub fn leaves(&self) -> &[AdaptedLeaf] {
        &self.leaves
    }

    #[must_use]
    pub fn effects(&self) -> &[EffectOutput] {
        &self.effects
    }

    /// The run timed out: the watchdog fired, or k-rust reports the run cancelled (an error whose
    /// stop cause is `Cancelled`, or a `Cancelled` leaf). Its leaf states must not be read: a
    /// cancelled run can leave an arbitrarily deep term.
    #[must_use]
    pub const fn timed_out(&self) -> bool {
        self.timed_out
    }

    /// k-rust's count of the run's stops for lack of native stack (`stackStops`). A run with any
    /// is no evidence ([`crate::exclusion::Exclusion::StackStop`]).
    #[must_use]
    pub const fn stack_stops(&self) -> usize {
        self.stack_stops
    }

    /// The modality the leaves were computed under.
    #[must_use]
    pub const fn modality(&self) -> ResultModality {
        self.modality
    }

    /// The states the run visited (k-rust `work`); 0 for a timed-out run.
    #[must_use]
    pub const fn work(&self) -> u64 {
        self.work
    }

    /// k-rust's run coverage; `None` for a timed-out run.
    #[must_use]
    pub const fn coverage(&self) -> Option<&RunCoverage> {
        self.coverage.as_ref()
    }

    /// k-rust's run-level facts (re-pin adoption A-1): its lists of open values read,
    /// contradicted claims, allowance refusals, unsupported hooks and short-circuit readings, and
    /// its count of undecided solver answers; empty for a timed-out run.
    #[must_use]
    pub const fn facts(&self) -> &RunFacts {
        &self.facts
    }

    /// This execution with `count` added to [`RunFacts::decider_smt_unknowns`]: the undecided
    /// solver answers that the caller of [`ExecutionAdapter::adapt_result`] took when it judged
    /// the leaf feasibility it gave there, which the result does not carry.
    #[must_use]
    pub const fn with_decider_smt_unknowns(mut self, count: usize) -> Self {
        self.facts.decider_smt_unknowns = self.facts.decider_smt_unknowns.saturating_add(count);
        self
    }
}

impl StopRules {
    /// The names of `self` that select no rewrite rule of `backend`'s definition for its default
    /// module, in the order written (`before`'s, then `after`'s). A name selects a rule here when
    /// it is the rule's label, exactly. k-rust also selects a rule by its `UNIQUE_ID`, but a stop
    /// names one observation on a baseline and on each of its mutants, and a `UNIQUE_ID` is a
    /// digest of one rule's text that any edit of the rule changes, so it names no observation.
    /// A name that labels only an equation selects nothing: k-rust stops only at rewrite steps.
    pub fn unresolved(
        &self,
        backend: &mut Backend,
    ) -> Result<Vec<String>, ExecutionAdapterFailure> {
        let labels = with_definition(backend, |definition| Ok(rewrite_labels(definition)))?;
        Ok(self
            .before
            .iter()
            .chain(&self.after)
            .filter(|name| !labels.contains(name.as_str()))
            .cloned()
            .collect())
    }
}

/// The labels of the definition's rewrite rules.
fn rewrite_labels(definition: &k_rust_backend::definition::BackendDefinition) -> BTreeSet<String> {
    definition
        .rewrite_theory()
        .values()
        .flat_map(|priorities| priorities.values())
        .flatten()
        .filter_map(|rule| rule.rule.attributes.label.clone())
        .collect()
}

/// Execution adapter failure. No adapted execution is returned.
#[derive(Clone, Debug, PartialEq)]
pub enum ExecutionAdapterFailure {
    /// The backend's solver profile ([`SolverProfile::of`]) differs from the profile the adapter
    /// expects ([`ExecutionAdapter::profile`]), in either direction.
    SolverProfileMismatch,
    InvalidState(String),
    Backend(String),
    /// A leaf reports a halt excluded by the adapter's request.
    ContractViolation(HaltClass),
    /// A free element variable of the initial state has a sort with no value shown by the
    /// definition, so the state may have no instance.
    UninhabitedVariable(k_rust::kore::ast::Variable),
    /// The run's stop condition ([`StopCondition`]) gave no answer the run can rest on: it
    /// refused at an arrival (the observation has no value at that stop state, k-rust
    /// `StopConditionRefused`, which names the rule, the depth and the reason), or the caller
    /// could not give the run its condition. The stop criterion is not defined on this run, so it
    /// has no result.
    StopCondition(String),
}

/// The bounded request of one run. Strategy `all` is what makes the leaves the whole path set (or,
/// merged, the whole state set): every instance's every successor is followed, so a `Trivial`
/// leaf is an undefined step for each of its instances and the leaves cover the initial state.
/// Under `any` a step gives an instance one successor, from the first rule of its highest
/// applicable priority that is defined there (k-rust KK-73), so the events of the other
/// successors are missing; and it follows one collection candidate per rule, so an instance
/// matched only through another candidate may have a defined successor although its leaf is
/// `Trivial`. Stop-at-branch is off, so no leaf stops at a branch. The cut-point and terminal
/// rules are `requested.stop`'s ([`StopRules`]), none by default, so a leaf stops at a selected
/// rule only where the caller asked for it; a request without a stop is the request before stop
/// rules existed, field for field. `stop_count` is the count past a first arrival at a stop
/// ([`Requested::stop_count`]), absent otherwise, so a request whose paths end at their first
/// arrival is the request before counts existed, field for field.
///
/// The request is a full struct literal with no struct-update base (no defaults taken from
/// `ExecuteRequest::new`), so a field k-rust adds at a later pin is a compile error that forces a
/// decision here instead of a silent wire default (re-pin findings D-05, D-07). The four fields
/// k-rust 501f18b9 added are chosen for re-pin lane 1 (L1-1):
/// - `trace: false`: kink reads no trace; rule coverage and the leaf census read `coverage`
///   instead (findings A-02, D-04), and k-rust changes no other field of the result;
/// - `collect_coverage: true` on every run, so coverage is never empty where a run returns a
///   result; collecting changes no other field of the result;
/// - `cancelled_result: error`: a cancelled run answers `Err` with stop cause `Cancelled`, which
///   [`settle`] makes a timeout, and k-rust builds none of the leaves a timed-out run's caller
///   never reads (finding A-03);
/// - `max_work`: `requested.run.max_work` (none for a stepped run and by default); its
///   `work-bound` leaf is admitted exactly then ([`HaltClass::admitted_by`]).
///
/// - `collect_offered: false` (k-rust 58720d2e5, KINK-04/3): no offered coverage is asked for,
///   which is the behaviour before that field existed; asking changes no other field of the
///   result, and adopting it is for the round-D re-pin (probe P-1).
/// - `collect_counts: false`: no applied counts are asked for (they are part of the coverage
///   k-rust reports only when asked, and asking changes no other field of the result).
/// - `collect_conditions: None`: no condition records are asked for (they are part of the
///   coverage k-rust reports only when asked, and asking changes no other field of the result).
/// - `match_states: None`: kink matches no reached state inside the run; asking changes no other
///   field of the result, so its absence keeps every run as before.
/// - `collect_committed: true` (KINK-R4): the run's coverage also reports the rewrite rules whose
///   successor it committed to ([`RunCoverage::committed`]), which kink-flow's `fired_by` reads.
///   k-rust states that asking changes no other field of the result (docs/compatibility.md,
///   "Committed transitions"), so no leaf, list, `applied` or `matched` set, and so no verdict or
///   schedule, differs from a run without it.
///
/// Step timeouts stay off: a step deadline is host-dependent, which an Execute-promise run must
/// not be (finding A-03).
fn request(state: Pattern, budget: ExecutionBudget, requested: Requested<'_>) -> ExecuteRequest {
    let stop_count = requested.stop_count();
    let Requested {
        run, stop, guards, ..
    } = requested;
    ExecuteRequest {
        state,
        module_name: None,
        max_depth: budget.max_depth,
        max_breadth: budget.max_breadth.map(NonZeroUsize::get),
        max_simplification_iterations: budget.max_simplification_iterations,
        strategy: ExecutionStrategy::All,
        stop_at_branch: false,
        cut_point_rules: stop.before.clone(),
        terminal_rules: stop.after.clone(),
        stop_count,
        step_timeout_ms: None,
        moving_average_timeout: false,
        assume_state_defined: false,
        result_modality: run.modality.output(),
        collect_coverage: true,
        collect_offered: false,
        collect_counts: false,
        collect_conditions: None,
        collect_guards: guards.map(|axioms| GuardCollection::new(axioms.iter().cloned())),
        collect_bindings: None,
        max_work: run.max_work,
        trace: false,
        cancelled_result: CancelledResultOutput::Error,
        match_states: None,
        collect_committed: true,
        schema_version: BACKEND_SCHEMA_VERSION,
    }
}

/// The version of the execution request kink sends for a run, and of how a result run's
/// modality and work budget are chosen: a run's leaves, and so a verdict, depend on it, so kink's
/// semantics identity names it (kink-campaign `identity`). Bump it whenever `request`,
/// [`ExecutionAdapter::execute_result`]'s choice of the run it returns, or kink-campaign's choice
/// of a test's modality and of a mutant's work budget (`RunOptions`, `WorkBudget`) changes what a
/// run returns. v1 (re-pin L1-1 and L1-1-fix-1; L1-1 review 1 minor 5): a result run is a state
/// set (path-set replacement on an undefined step, a vacuous leaf or a contradicted claim, decided
/// per side), a stepped run an observed path set; no trace; run coverage collected; a cancellation
/// answers an error; `max_work` only on a mutant's result run, calibrated from the baseline's run
/// of the test. v2 (fz26 KINK-PATHSET-FALLBACK): a result run is the state set k-rust answers,
/// whatever its leaves; no path-set replacement, so a baseline with an undefined step also
/// calibrates a mutant's `max_work` from its state set. A campaign that stores reports
/// (kink-corpus, replay) runs the default `RunOptions`; kink-flow's tier-1 context names its work
/// budget. Builds before packet CACHE-ID name no version (1ee9955 ran path sets with traces).
/// KINK-R4 asks for the committed transitions within v2: k-rust states that asking changes no
/// other field of the result, and nothing that decides a verdict or a schedule reads them; the one
/// store that holds them, kink-flow's result records, moved its own `RESULT_SCHEMA_VERSION`.
/// v3 (CF-21): a result run may carry stop rules ([`StopRules`],
/// [`ExecutionAdapter::execute_result_stopped`]), which the request sends as `cut_point_rules` and
/// `terminal_rules`; their leaves are admitted exactly then and read as final configurations of
/// the truncated system, and a run that passed a stop is excluded. A run without a stop sends the
/// request of v2, field for field, and is adapted and judged as under v2. A result run may also
/// end its paths at a later arrival at a stop than the first
/// ([`ExecutionAdapter::execute_result_counted`]), which the request sends as `stop_count` and
/// whose leaves must report their arrivals accordingly; only kink-campaign's counted stop asks for
/// one, and its version (kink-campaign `STOP_VERSION` v2) names that change, since every request
/// of v3 is sent and adapted as it was. v4: a result run with stop rules may carry an in-process
/// stop condition ([`StopCondition`], [`ExecutionAdapter::execute_result_counted`]), which k-rust
/// asks at each arrival (`Backend::execute_kore_with_condition`; the wire request is unchanged):
/// its paths count the arrivals where the condition holds, each leaf reports every arrival its
/// path passed, a `stop-undecided` leaf is admitted exactly then, and a refusal of the condition
/// fails the run as [`ExecutionAdapterFailure::StopCondition`]. A run without a condition sends
/// and adapts the request of v3, field for field. Within v4, a baseline's result run also asks
/// for the guard outcomes of the definition's guarded rewrite rules and function equations
/// (`collect_guards`, [`ResultRun::guards`]): k-rust states that asking changes no other field of
/// the result, as for the committed transitions, nothing that decides a verdict or a schedule
/// reads them, and a mutant's run and a stepped run ask for none; the one store that holds them,
/// kink-flow's result records, moved its `RESULT_SCHEMA_VERSION`.
pub const EXECUTION_REQUEST_VERSION: &str = "kink-native/execution-request/v4";

/// The request of a stepped run: an observed path set without a work budget or stop rules.
const STEPPED: Requested<'static> = Requested::unstopped(ResultRun {
    modality: ResultModality::PathSet,
    max_work: None,
    guards: false,
});

/// The tables a result run reads from its backend's definition, built once per backend and
/// kept for every later request to it ([`ExecutionAdapter::execute_result_counted`]): which sorts
/// have values (a leaf's feasibility and the initial state's inhabitation, [`Inhabitation`]) and
/// the `UNIQUE_ID`s of the rewrite rules (the rewrite rules among a run's coverage,
/// [`RunCoverage::applied_rewrites`]). Both are functions of the definition alone, so building
/// them per request would compute the same tables again; a request reads them, and nothing else
/// of a request changes them.
///
/// A value holds the tables of the first backend it is used with, and must be used with that
/// backend only: the caller that owns a backend owns its tables beside it. A new value builds them
/// on its first request; a failure to build them is not kept.
#[derive(Clone, Debug, Default)]
pub struct DefinitionTables {
    built: Option<BuiltTables>,
}

#[derive(Clone, Debug)]
struct BuiltTables {
    inhabitation: Inhabitation,
    rewrites: BTreeSet<String>,
    /// The axioms a run that collects guard outcomes names ([`guarded_unique_ids`]).
    guarded: BTreeSet<String>,
}

impl DefinitionTables {
    /// No table built yet.
    #[must_use]
    pub const fn new() -> Self {
        Self { built: None }
    }

    /// The tables of `backend`'s definition, built on the first call.
    fn of(&mut self, backend: &mut Backend) -> Result<&BuiltTables, ExecutionAdapterFailure> {
        if self.built.is_none() {
            let built = with_definition(backend, |definition| {
                Ok(BuiltTables {
                    inhabitation: Inhabitation::of(definition),
                    rewrites: rewrite_unique_ids(definition),
                    guarded: guarded_unique_ids(definition),
                })
            })?;
            self.built = Some(built);
        }
        Ok(self.built.as_ref().expect("built above"))
    }
}

/// Event-free and stepped execution in one expected solver profile.
#[derive(Clone, Debug, PartialEq)]
pub struct ExecutionAdapter {
    profile: SolverProfile,
}

impl ExecutionAdapter {
    /// An adapter that expects `profile`.
    #[must_use]
    pub const fn new(profile: SolverProfile) -> Self {
        Self::with_profile(profile)
    }

    /// An adapter that expects `profile`; a backend of the other profile is
    /// [`ExecutionAdapterFailure::SolverProfileMismatch`].
    #[must_use]
    pub const fn with_profile(profile: SolverProfile) -> Self {
        Self { profile }
    }

    /// The solver profile this adapter accepts.
    #[must_use]
    pub const fn profile(&self) -> SolverProfile {
        self.profile
    }

    fn check_profile(&self, backend: &Backend) -> Result<(), ExecutionAdapterFailure> {
        if SolverProfile::of(backend) == self.profile {
            Ok(())
        } else {
            Err(ExecutionAdapterFailure::SolverProfileMismatch)
        }
    }

    /// Executes `state` from the backend's default module as one result run with the default
    /// [`ResultRun`]: a state set without a work budget ([`Self::execute_result`]).
    pub fn execute(
        &self,
        backend: &mut Backend,
        state: &Pattern,
        budget: ExecutionBudget,
    ) -> Result<AdaptedExecution, ExecutionAdapterFailure> {
        self.execute_result(backend, state, budget, ResultRun::default())
    }

    /// Executes `state` from the backend's default module as one unobserved result run under
    /// `run`, exactly as k-rust answers it, in the request's modality whatever its leaves (fz26
    /// KINK-PATHSET-FALLBACK, which removed the replacement of a state set with an undefined,
    /// vacuous or contradicted leaf by its path set). In a run with no work or breadth bound, every
    /// `Trivial` and `Vacuous` leaf of the state set is a leaf of the path set of the same request,
    /// and the run's lists hold every record k-rust observes, absorbed arrivals' included. The one
    /// state-set leaf whose rule can differ from a path-set leaf's is a refuted remainder's, which
    /// names its parent's producing rule; its refutation rests on constraints a
    /// `preserves-definedness` producer does not add, so it shows no contradiction of that
    /// producer's claim on either run (D40, [`crate::exclusion`]). Under a work bound the state set
    /// can reach past the path set; only a mutant's run is bounded, and any exclusion makes it
    /// `Unknown`.
    pub fn execute_result(
        &self,
        backend: &mut Backend,
        state: &Pattern,
        budget: ExecutionBudget,
        run: ResultRun,
    ) -> Result<AdaptedExecution, ExecutionAdapterFailure> {
        self.execute_result_stopped(backend, state, budget, run, &StopRules::NONE)
    }

    /// [`Self::execute_result`] with the stop rules `stop` ([`StopRules`]): its paths also end at a
    /// step of a selected rule that is its state's one successor, as a `cut-point` leaf before
    /// the step ([`AdaptedLeaf::proposal`] names it) or a `terminal` leaf after it, and the run's
    /// facts list each selected rule it went on past because the step had another successor
    /// ([`RunFacts::passed_stops`]). With [`StopRules::NONE`] it is [`Self::execute_result`].
    ///
    /// A backend that does not list passed stops (its `passed_stops` capability off) cannot be
    /// asked for a stop: an empty list would not tell a run that passed none from one whose
    /// backend lists none, so the adapter answers [`ExecutionAdapterFailure::Backend`] and runs
    /// nothing.
    pub fn execute_result_stopped(
        &self,
        backend: &mut Backend,
        state: &Pattern,
        budget: ExecutionBudget,
        run: ResultRun,
        stop: &StopRules,
    ) -> Result<AdaptedExecution, ExecutionAdapterFailure> {
        self.execute_result_counted(
            backend,
            &mut DefinitionTables::new(),
            state,
            budget,
            run,
            stop,
            NonZeroU64::MIN,
            None,
        )
    }

    /// [`Self::execute_result_stopped`] whose paths end at their `count`th arrival at a stop
    /// instead of their first, reading the definition's tables from `tables`, which is filled on
    /// the first request that needs it and must hold the tables of `backend`'s definition
    /// ([`DefinitionTables`]).
    ///
    /// An *arrival* is a step at which a selected rule stops a path: the rule's step is its
    /// state's one successor, and that successor is defined (k-rust `docs/compatibility.md`,
    /// "Stop count"). A path takes each arrival before its `count`th as it takes any other step,
    /// and ends at the `count`th as a path without a count ends at its first: before the step as
    /// a `cut-point` leaf, after it as a `terminal` leaf. So the run is one request whose paths
    /// are the paths of the system truncated at the `count`th arrival, from `state`: its depth
    /// bound, work budget and watchdog bound each whole path and the whole run, its coverage is
    /// the coverage of those paths (an earlier arrival's step is committed where the path takes
    /// it), and its state set merges a state only into one whose path passed as many arrivals.
    /// Each leaf reports its arrivals, and a leaf whose report the request cannot yield is a
    /// [`ExecutionAdapterFailure::ContractViolation`]: a stop leaf must report `count`, any other
    /// leaf fewer. With `count` 1 the request is [`Self::execute_result_stopped`]'s, field for
    /// field.
    ///
    /// A backend that does not count arrivals (its `stop_count` capability off) cannot be asked
    /// for a count past the first: it would end every path at its first arrival, which is another
    /// observation, so the adapter answers [`ExecutionAdapterFailure::Backend`] and runs nothing.
    ///
    /// With a stop condition `condition` (and stop rules), an arrival counts only where the
    /// condition holds of its stop state (k-rust `Backend::execute_kore_with_condition`): the
    /// state before a cut-point rule's step, the successor of a terminal rule's. An arrival where
    /// it fails is taken as any other step; one where it is left undecided ends its path as a
    /// `stop-undecided` leaf, which completes nothing; a refusal fails the run
    /// ([`ExecutionAdapterFailure::StopCondition`]). Every leaf then reports the arrivals its path
    /// passed beside the events it counted. The request sent is the one without a condition,
    /// field for field. Without stop rules a condition is asked nowhere, and is not passed.
    #[expect(
        clippy::too_many_arguments,
        reason = "one request's inputs: the backend and its tables, the start, the budget, the run, \
                  the stop rules, their count and their condition, none of which belong to another"
    )]
    pub fn execute_result_counted(
        &self,
        backend: &mut Backend,
        tables: &mut DefinitionTables,
        state: &Pattern,
        budget: ExecutionBudget,
        run: ResultRun,
        stop: &StopRules,
        count: NonZeroU64,
        condition: Option<&mut dyn StopCondition>,
    ) -> Result<AdaptedExecution, ExecutionAdapterFailure> {
        self.check_profile(backend)?;
        let condition = condition.filter(|_| !stop.is_none());
        let built = tables.of(backend)?;
        let requested = Requested {
            run,
            stop,
            count,
            conditioned: condition.is_some(),
            guards: run.guards.then_some(&built.guarded),
        };
        stops_listed(requested, backend.capabilities())?;
        with_definition(backend, |definition| {
            match uninhabited_variable(definition, &built.inhabitation, state) {
                Ok(None) => Ok(()),
                Ok(Some(variable)) => Err(ExecutionAdapterFailure::UninhabitedVariable(variable)),
                Err(error) => Err(ExecutionAdapterFailure::InvalidState(error)),
            }
        })?;
        self.result_once(
            backend,
            state,
            budget,
            requested,
            condition,
            &built.inhabitation,
            &built.rewrites,
        )
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "Self::execute_result_counted's request with the definition's tables it read"
    )]
    fn result_once(
        &self,
        backend: &mut Backend,
        state: &Pattern,
        budget: ExecutionBudget,
        requested: Requested<'_>,
        condition: Option<&mut dyn StopCondition>,
        inhabitation: &Inhabitation,
        rewrites: &BTreeSet<String>,
    ) -> Result<AdaptedExecution, ExecutionAdapterFailure> {
        let recorded = RecordedRun::of(backend, state);
        let (result, timed_out) = match condition {
            None => execute_with_watchdog(
                backend,
                state.clone(),
                budget,
                requested,
                Backend::execute_kore,
            )?,
            Some(condition) => execute_with_watchdog(
                backend,
                state.clone(),
                budget,
                requested,
                |backend, request| backend.execute_kore_with_condition(request, condition),
            )?,
        };
        let undecided = Cell::new(0);
        let feasibility = if timed_out {
            vec![LeafFeasibility::Unknown; result.leaves.len()]
        } else {
            backend.with_solver(None, |definition, solver| {
                result
                    .leaves
                    .iter()
                    .map(|leaf| {
                        leaf_feasibility(definition, solver, inhabitation, &leaf.state, &undecided)
                            .map_err(host_stack_refused)
                    })
                    .collect::<Result<Vec<_>, _>>()
            })?
        };
        let mut adapted = Self::adapt(
            result,
            timed_out,
            &budget,
            requested,
            feasibility,
            rewrites,
            recorded,
        )?;
        adapted.facts.decider_smt_unknowns = undecided.get();
        Ok(adapted)
    }

    /// Execute once with every rewrite transition observed, retaining the states of each step:
    /// an observed path set without a work budget. An observation failure is returned
    /// separately from an execution failure.
    pub fn execute_steps(
        &self,
        backend: &mut Backend,
        state: &Pattern,
        budget: ExecutionBudget,
    ) -> Result<Result<SteppedExecution, StepRunFailure>, ExecutionAdapterFailure> {
        self.check_profile(backend)?;
        let encoded = state.clone();
        let (inhabitation, ids, rewrites) = with_definition(backend, |definition| {
            let inhabitation = Inhabitation::of(definition);
            match uninhabited_variable(definition, &inhabitation, state) {
                Ok(None) => Ok((
                    inhabitation,
                    rewrite_ids(definition),
                    rewrite_unique_ids(definition),
                )),
                Ok(Some(variable)) => Err(ExecutionAdapterFailure::UninhabitedVariable(variable)),
                Err(error) => Err(ExecutionAdapterFailure::InvalidState(error)),
            }
        })?;
        let ids = match ids {
            Ok(ids) => ids,
            Err(failure) => return Ok(Err(failure)),
        };
        let recorded = RecordedRun::of(backend, state);
        let (result, timed_out) =
            execute_with_watchdog(backend, encoded, budget, STEPPED, |backend, request| {
                backend.execute_observed_kore(ObservedRequest {
                    request,
                    rules: Some(ids),
                })
            })?;
        if timed_out {
            let feasibility = vec![LeafFeasibility::Unknown; result.leaves.len()];
            let mut result = result;
            for leaf in &mut result.leaves {
                leaf.observations.clear();
            }
            return Ok(Ok(SteppedExecution {
                adapted: Self::adapt(
                    result,
                    true,
                    &budget,
                    STEPPED,
                    feasibility,
                    &rewrites,
                    recorded,
                )?,
                states: Vec::new(),
            }));
        }
        let mut result = result;
        let states = match result
            .leaves
            .iter_mut()
            .map(step_states)
            .collect::<Result<Vec<_>, _>>()
        {
            Ok(states) => states,
            Err(failure) => return Ok(Err(failure)),
        };
        let undecided = Cell::new(0);
        let feasibility = backend.with_solver(None, |definition, solver| {
            result
                .leaves
                .iter()
                .map(|leaf| {
                    leaf_feasibility(definition, solver, &inhabitation, &leaf.state, &undecided)
                        .map_err(host_stack_refused)
                })
                .collect::<Result<Vec<_>, _>>()
        })?;
        // Step observations are consumed only by the configuration sequence, which took them.
        let mut adapted = Self::adapt(
            result,
            false,
            &budget,
            STEPPED,
            feasibility,
            &rewrites,
            recorded,
        )?;
        adapted.facts.decider_smt_unknowns = undecided.get();
        Ok(Ok(SteppedExecution { adapted, states }))
    }

    /// Executes the stepped run's path-set request without observation rules.
    pub fn execute_unobserved(
        &self,
        backend: &mut Backend,
        state: &Pattern,
        budget: ExecutionBudget,
    ) -> Result<UnobservedExecution, ExecutionAdapterFailure> {
        self.check_profile(backend)?;
        let rewrites = with_definition(backend, |definition| Ok(rewrite_unique_ids(definition)))?;
        let encoded = state.clone();
        let recorded = RecordedRun::of(backend, state);
        let (result, timed_out) =
            execute_with_watchdog(backend, encoded, budget, STEPPED, Backend::execute_kore)?;
        let mut result = result;
        // A timed-out run has no facts: it is a timeout before it is anything else.
        let facts = if timed_out {
            RunFacts::default()
        } else {
            RunFacts::take(&mut result, recorded)
        };
        let leaves = result
            .leaves
            .into_iter()
            .map(|leaf| {
                let halt = HaltClass::from_output(leaf.reason);
                if !halt.adapter_admits(&budget) {
                    return Err(ExecutionAdapterFailure::ContractViolation(halt));
                }
                Ok(BaselineLeaf {
                    halt,
                    state: leaf.state,
                    depth: leaf.depth,
                    trace: leaf.trace,
                    cause: leaf.cause,
                    diagnostics: leaf.diagnostics,
                    candidate_diagnostics: leaf
                        .candidates
                        .unwrap_or_default()
                        .into_iter()
                        .map(|candidate| candidate.diagnostics)
                        .collect(),
                    remainder_diagnostics: leaf
                        .remainder
                        .map_or_else(Vec::new, |remainder| remainder.diagnostics),
                    branch: leaf.branch,
                    undefined_rule: UndefinedStepRule::of(halt, leaf.rule_id, leaf.rule_label),
                    contradicted_total: leaf.contradicted_total,
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(UnobservedExecution {
            leaves,
            timed_out,
            stack_stops: result.stack_stops,
            coverage: result
                .coverage
                .map(|coverage| RunCoverage::of(coverage, &rewrites)),
            facts,
        })
    }

    /// The adapted execution of `result`, the answer to a request of `budget` and `requested`,
    /// which give the halts its leaves may hold ([`HaltClass::admitted_by`]); the result names
    /// its own modality.
    fn adapt(
        result: KoreExecutionResult,
        timed_out: bool,
        budget: &ExecutionBudget,
        requested: Requested<'_>,
        feasibility: Vec<LeafFeasibility>,
        rewrites: &BTreeSet<String>,
        recorded: RecordedRun,
    ) -> Result<AdaptedExecution, ExecutionAdapterFailure> {
        let modality = match result.modality {
            ResultModalityOutput::PathSet => ResultModality::PathSet,
            ResultModalityOutput::StateSet => ResultModality::StateSet,
        };
        let mut result = result;
        // A timed-out run has no facts: it is a timeout before it is anything else.
        let facts = if timed_out {
            RunFacts::default()
        } else {
            RunFacts::take(&mut result, recorded)
        };
        let leaves = result
            .leaves
            .into_iter()
            .zip(feasibility)
            .map(|(leaf, feasibility)| {
                let halt = HaltClass::from_output(leaf.reason);
                if !requested.admits(halt, budget)
                    || !requested.admits_arrivals(halt, leaf.stops, leaf.arrivals)
                {
                    return Err(ExecutionAdapterFailure::ContractViolation(halt));
                }
                let proposal = StopProposal::of(halt, leaf.candidates.as_deref())?;
                Ok(AdaptedLeaf {
                    halt,
                    feasibility,
                    proposal,
                    undefined_rule: UndefinedStepRule::of(halt, leaf.rule_id, leaf.rule_label),
                    contradicted_total: leaf.contradicted_total,
                    cause: leaf.cause,
                    diagnostics: leaf.diagnostics,
                    candidate_diagnostics: leaf
                        .candidates
                        .unwrap_or_default()
                        .into_iter()
                        .map(|candidate| candidate.diagnostics)
                        .collect(),
                    remainder_diagnostics: leaf
                        .remainder
                        .map_or_else(Vec::new, |remainder| remainder.diagnostics),
                    branch: AdaptedBranch {
                        identity: leaf.branch,
                        state: leaf.state,
                        depth: leaf.depth,
                        trace: leaf.trace,
                    },
                })
            })
            .collect::<Result<Vec<_>, ExecutionAdapterFailure>>()?;
        Ok(AdaptedExecution {
            leaves,
            effects: result.effects,
            timed_out,
            stack_stops: result.stack_stops,
            modality,
            work: result.work,
            coverage: result
                .coverage
                .map(|coverage| RunCoverage::of(coverage, rewrites)),
            facts,
        })
    }

    /// The adapted execution of a raw backend `result`, exactly as [`Self::execute`] adapts the
    /// result of its run: every halt is checked against `budget`'s request (without a work
    /// budget), and `feasibility` gives each leaf's state feasibility in leaf order. Coverage, if
    /// the result carries any, has no rewrite rules named (`applied_rewrites` is empty).
    /// `recorded` says how the result was recorded: the capability of the backend that returned
    /// it and whether its initial state was ground, which the result does not carry. For tests
    /// and tools that hold a result k-rust returned; a value built here is no more evidence than
    /// the result it is built from.
    pub fn adapt_result(
        result: KoreExecutionResult,
        timed_out: bool,
        budget: &ExecutionBudget,
        feasibility: Vec<LeafFeasibility>,
        recorded: RecordedRun,
    ) -> Result<AdaptedExecution, ExecutionAdapterFailure> {
        Self::adapt_bounded_result(result, timed_out, budget, None, feasibility, recorded)
    }

    /// [`Self::adapt_result`] of a result whose request set `max_work`, so a `work-bound` leaf is
    /// admitted exactly when `max_work` is set ([`HaltClass::admitted_by`]; re-pin L1-2: tests of
    /// the one-sided kill hold a work-bound result).
    pub fn adapt_bounded_result(
        result: KoreExecutionResult,
        timed_out: bool,
        budget: &ExecutionBudget,
        max_work: Option<u64>,
        feasibility: Vec<LeafFeasibility>,
        recorded: RecordedRun,
    ) -> Result<AdaptedExecution, ExecutionAdapterFailure> {
        let run = ResultRun {
            max_work,
            ..ResultRun::default()
        };
        Self::adapt(
            result,
            timed_out,
            budget,
            Requested::unstopped(run),
            feasibility,
            &BTreeSet::new(),
            recorded,
        )
    }
}

/// Refuses stop rules `stop` on a backend whose `capabilities` do not list passed stops
/// (`BackendCapabilities::passed_stops`): such a backend answers an empty list whether or not the
/// run went on past a stop rule, so a run that passed one could not be told from one that passed
/// none, and its leaves could be read as ends of the truncated system they need not be. A
/// request without stop rules passes none, so it needs nothing. Refuses a count past the first
/// arrival ([`Requested::stop_count`]) on a backend that does not count arrivals
/// (`BackendCapabilities::stop_count`), which would end every path at its first.
fn stops_listed(
    requested: Requested<'_>,
    capabilities: BackendCapabilities,
) -> Result<(), ExecutionAdapterFailure> {
    if !requested.stop.is_none() && !capabilities.passed_stops {
        Err(ExecutionAdapterFailure::Backend(
            "a run with stop rules needs a backend that lists passed stops".to_owned(),
        ))
    } else if requested.stop_count().is_some() && !capabilities.stop_count {
        Err(ExecutionAdapterFailure::Backend(
            "a run to a later stop than the first needs a backend that counts stops".to_owned(),
        ))
    } else {
        Ok(())
    }
}

fn execute_with_watchdog(
    backend: &mut Backend,
    state: Pattern,
    budget: ExecutionBudget,
    requested: Requested<'_>,
    execute: impl FnOnce(&mut Backend, ExecuteRequest) -> Result<KoreExecutionResult, BackendError>,
) -> Result<(KoreExecutionResult, bool), ExecutionAdapterFailure> {
    let token = CancellationToken::new();
    let fired = Arc::new(AtomicBool::new(false));
    // A zero budget has already expired; do not race the solver's entry poll against
    // scheduling the watchdog thread.
    if budget.time.is_zero() {
        fired.store(true, Ordering::Release);
        token.cancel();
    }
    let (done, finished) = mpsc::channel::<()>();
    let watchdog = {
        let token = token.clone();
        let fired = Arc::clone(&fired);
        thread::spawn(move || {
            if finished.recv_timeout(budget.time) == Err(mpsc::RecvTimeoutError::Timeout) {
                fired.store(true, Ordering::Release);
                token.cancel();
            }
        })
    };
    let outcome = token.scope(|| execute(backend, request(state, budget, requested)));
    // Stop the watchdog, then read whether it fired before the run ended.
    drop(done);
    watchdog.join().expect("watchdog thread does not panic");
    let modality = requested.run.modality;
    let (result, timed_out) = settle(outcome, fired.load(Ordering::Acquire), modality)?;
    assert_eq!(result.modality, modality.output());
    Ok((result, timed_out))
}

/// How a run ended (re-pin finding A-04/A-05, answers section 2.3): a timeout exactly when kink's
/// watchdog `fired`, or k-rust answers an error whose stop cause is `Cancelled` (every request
/// sets `cancelled_result: error`, so this is how k-rust answers a cancellation, and the
/// portable build answers a token already cancelled at entry that way, section_2_2_summary
/// (5)), or an `Ok` result with a `Cancelled` leaf (which the request excludes; the adapter then
/// refuses the leaf, [`HaltClass::admitted_by`]). A timed-out run publishes no completed state:
/// after an error it has no leaves, and its leaves are never read. A refusal of the run's stop
/// condition (k-rust `StopConditionRefused`) is [`ExecutionAdapterFailure::StopCondition`].
/// Every other error, a stack or deadline stop included, is an infrastructure failure, never a
/// timeout.
fn settle(
    outcome: Result<KoreExecutionResult, BackendError>,
    fired: bool,
    modality: ResultModality,
) -> Result<(KoreExecutionResult, bool), ExecutionAdapterFailure> {
    match outcome {
        Ok(result) => {
            let cancelled = result
                .leaves
                .iter()
                .any(|leaf| leaf.reason == HaltReasonOutput::Cancelled);
            Ok((result, fired || cancelled))
        }
        Err(error) if fired || matches!(error.stop_cause(), Some(StopCause::Cancelled)) => Ok((
            KoreExecutionResult {
                modality: modality.output(),
                leaves: Vec::new(),
                effects: Vec::new(),
                discarded: Vec::new(),
                coverage: None,
                work: 0,
                expanded: 0,
                stack_stops: 0,
                // A timed-out run publishes nothing (k-rust 58720d2e5 added these lists,
                // KINK-19/1, KINK-17/1, KINK-18/2); its leaves are never read.
                smt_unknowns: 0,
                implementation_chosen_values: Vec::new(),
                contradicted_claims: Vec::new(),
                allowance_refusals: Vec::new(),
                unsupported_hooks: Vec::new(),
                short_circuit_readings: Vec::new(),
                passed_stops: Vec::new(),
                state_matches: None,
            },
            true,
        )),
        Err(error) if error.kind() == Some(BackendErrorKind::StopConditionRefused) => {
            Err(ExecutionAdapterFailure::StopCondition(error.to_string()))
        }
        Err(error) => Err(ExecutionAdapterFailure::Backend(error.to_string())),
    }
}

/// The `UNIQUE_ID`s of the definition's rewrite rules and function equations whose `requires`
/// is not empty: the axioms whose guard outcomes a run that collects them names
/// ([`ResultRun::guards`]). Simplifications, ceil and predicate equations are no sentence of the
/// definition's runs in coverage's sense, so they are not named.
fn guarded_unique_ids(
    definition: &k_rust_backend::definition::BackendDefinition,
) -> BTreeSet<String> {
    let rewrites = definition
        .rewrite_theory()
        .values()
        .flat_map(|priorities| priorities.values())
        .flatten()
        .map(|rule| rule.rule.as_ref());
    let equations = definition
        .function_theory()
        .values()
        .flat_map(|priorities| priorities.values())
        .flatten()
        .map(|rule| rule.as_ref());
    rewrites
        .chain(equations)
        .filter(|rule| !rule.requires.is_empty())
        .map(|rule| rule.attributes.unique_id.clone())
        .collect()
}

/// The `UNIQUE_ID`s of the definition's rewrite rules: the ids [`RunCoverage::applied_rewrites`]
/// keeps.
fn rewrite_unique_ids(
    definition: &k_rust_backend::definition::BackendDefinition,
) -> BTreeSet<String> {
    definition
        .rewrite_theory()
        .values()
        .flat_map(|priorities| priorities.values())
        .flatten()
        .map(|rule| rule.rule.attributes.unique_id.clone())
        .collect()
}

/// Mirror the ambiguity checks of k-rust's observation allow-list before a run, so a
/// rejected observation filter is reported as a step failure rather than a backend error.
fn rewrite_ids(
    definition: &k_rust_backend::definition::BackendDefinition,
) -> Result<Vec<String>, StepRunFailure> {
    let mut available = BTreeMap::<(String, Option<usize>), usize>::new();
    let mut identities = BTreeMap::<&str, usize>::new();
    for axiom in definition.classified_axioms() {
        *identities
            .entry(axiom.attributes().unique_id.as_str())
            .or_default() += 1;
    }
    let mut selected = BTreeSet::new();
    for priorities in definition.rewrite_theory().values() {
        for rules in priorities.values() {
            for rule in rules {
                let id = &rule.rule.attributes.unique_id;
                selected.insert(id.clone());
                *available
                    .entry((id.clone(), rule.rule.lhs_alternative))
                    .or_default() += 1;
            }
        }
    }
    for theory in [
        definition.function_theory(),
        definition.simplification_theory(),
        definition.ceil_theory(),
    ] {
        for priorities in theory.values() {
            for rules in priorities.values() {
                for rule in rules {
                    *available
                        .entry((rule.attributes.unique_id.clone(), rule.lhs_alternative))
                        .or_default() += 1;
                }
            }
        }
    }
    for id in &selected {
        if available
            .iter()
            .any(|((available_id, _), count)| available_id == id && *count > 1)
            || identities.get(id.as_str()).is_some_and(|count| *count > 1)
        {
            return Err(StepRunFailure::AmbiguousRule(id.clone()));
        }
    }
    Ok(selected.into_iter().collect())
}

/// The configuration sequence of `leaf`: the state before each committed rewrite, taken out of
/// its observations (which only this sequence consumes), then the leaf's own state; every
/// reported id must equal its branch entry.
fn step_states(leaf: &mut KoreExecutionLeaf) -> Result<Vec<Pattern>, StepRunFailure> {
    let mut reported = Vec::new();
    let mut states = Vec::new();
    for event in std::mem::take(&mut leaf.observations) {
        if let ObservationEventOutput::Transition {
            id, class, before, ..
        } = event
        {
            match class {
                TransitionClassOutput::Rewrite => {
                    reported.push(id);
                    states.push(before);
                }
                TransitionClassOutput::Remainder | TransitionClassOutput::Claim => {
                    return Err(StepRunFailure::Unobservable);
                }
            }
        }
    }
    if leaf
        .branch
        .iter()
        .filter(|id| !id.rule.starts_with("remainder:"))
        .cloned()
        .collect::<Vec<_>>()
        != reported
    {
        return Err(StepRunFailure::Unobservable);
    }
    // The leaf keeps its state as its branch's end; the sequence's last configuration is a copy.
    states.push(leaf.state.clone());
    Ok(states)
}

/// Runs `operation` on the definition of `backend`'s default module.
fn with_definition<T>(
    backend: &mut Backend,
    operation: impl FnOnce(
        &k_rust_backend::definition::BackendDefinition,
    ) -> Result<T, ExecutionAdapterFailure>,
) -> Result<T, ExecutionAdapterFailure> {
    backend.with_solver(None, |definition, _| operation(definition))
}

impl From<BackendError> for ExecutionAdapterFailure {
    fn from(value: BackendError) -> Self {
        Self::Backend(value.to_string())
    }
}

/// A stop of the solver operation (cancellation, deadline, exhausted stack or a failed solver
/// prelude) is a backend failure: the adapter returns no execution.
impl From<StopCause> for ExecutionAdapterFailure {
    fn from(value: StopCause) -> Self {
        Self::Backend(value.to_string())
    }
}

/// The host's refusal to map the stack a leaf's feasibility needs is a backend failure, as the
/// facade's own refusal of a request's stack is: it is a fact about the host, never an answer
/// about the leaf, so the adapter returns no execution.
fn host_stack_refused(refused: k_rust_backend::nesting::SegmentRefused) -> ExecutionAdapterFailure {
    ExecutionAdapterFailure::Backend(format!("leaf feasibility: {refused}"))
}

#[cfg(test)]
mod tests {
    use super::*;

    use k_rust::kore::ast::Symbol;

    #[test]
    fn stepped_run_failure_is_reported_as_step_run_failure() {
        let state = Pattern::Application {
            symbol: Symbol {
                name: "Lblunit".into(),
                sort_parameters: Vec::new(),
            },
            arguments: Vec::new(),
        };
        let before = Pattern::Application {
            symbol: Symbol {
                name: "Lblstart".into(),
                sort_parameters: Vec::new(),
            },
            arguments: Vec::new(),
        };
        let id = TransitionIdOutput {
            rule: "rewrite".into(),
            target: "target".into(),
        };
        let event = |class, before| ObservationEventOutput::Transition {
            id: id.clone(),
            class,
            rule_label: None,
            bindings: Vec::new(),
            introduced_predicates: Vec::new(),
            before,
            after: state.clone(),
            effects: Vec::new(),
        };
        let mut leaf = KoreExecutionLeaf {
            state: state.clone(),
            diagnostics: Vec::new(),
            candidates: None,
            remainder: None,
            depth: 1,
            reason: HaltReasonOutput::Stuck,
            rule_id: None,
            rule_label: None,
            contradicted_total: None,
            cause: None,
            detail: None,
            trace: Vec::new(),
            branch: vec![id.clone()],
            effects: Vec::new(),
            observations: vec![event(TransitionClassOutput::Remainder, state.clone())],
            stops: None,
            arrivals: None,
        };
        assert_eq!(step_states(&mut leaf), Err(StepRunFailure::Unobservable));
        leaf.observations = vec![event(TransitionClassOutput::Rewrite, state.clone())];
        leaf.branch[0].target = "other".into();
        assert_eq!(step_states(&mut leaf), Err(StepRunFailure::Unobservable));
        // A committed rewrite's state before it, then the leaf's state; the observations are
        // taken out of the leaf.
        leaf.branch[0] = id.clone();
        leaf.observations = vec![event(TransitionClassOutput::Rewrite, before.clone())];
        assert_eq!(step_states(&mut leaf), Ok(vec![before, state]));
        assert!(leaf.observations.is_empty());
    }

    #[test]
    fn every_halt_variant_is_classified_exhaustively() {
        let actual = HaltReasonOutput::ALL.map(HaltClass::from_output);
        assert_eq!(actual.len(), HaltClass::ALL.len());
        for class in HaltClass::ALL {
            assert!(actual.contains(&class), "{class:?}");
        }
    }

    /// The adapter refuses an initial state with a variable of an uninhabited sort before it
    /// executes anything.
    #[test]
    fn uninhabited_initial_variable_is_rejected() {
        use k_rust::backend::BackendOptions;
        use k_rust::kore::ast::{Sort, Variable, VariableKind};
        let mut backend = Backend::new(
            r"[]
            module MAIN
                sort SortS{} []
                sort SortEmpty{} []
                symbol Lbla{}() : SortS{} [constructor{}()]
                symbol Lblwrap{}(SortEmpty{}) : SortS{} [constructor{}()]
            endmodule []",
            "MAIN",
            BackendOptions::default(),
        )
        .expect("backend");
        let adapter = ExecutionAdapter::with_profile(SolverProfile::BUILD);
        let variable = Variable {
            kind: VariableKind::Element,
            name: "VarE".to_owned(),
            sort: Sort::Application {
                name: "SortEmpty".to_owned(),
                arguments: Vec::new(),
            },
        };
        let state = Pattern::Application {
            symbol: k_rust::kore::ast::Symbol {
                name: "Lblwrap".to_owned(),
                sort_parameters: Vec::new(),
            },
            arguments: vec![Pattern::Variable(variable.clone())],
        };
        let budget = ExecutionBudget {
            time: Duration::from_secs(10),
            max_simplification_iterations: 10,
            max_depth: None,
            max_breadth: None,
        };
        assert_eq!(
            adapter.execute(&mut backend, &state, budget),
            Err(ExecutionAdapterFailure::UninhabitedVariable(variable))
        );
    }

    /// The adapter accepts exactly the backend profile it expects: a no-Z3 adapter rejects a Z3
    /// backend and a Z3 adapter rejects a no-Z3 backend. One build has one backend profile, so
    /// each gate exercises one rejection direction (`cargo test` the Z3-expecting adapter, the
    /// Z3 gate the no-Z3 adapter).
    #[test]
    fn z3_build_rejects_no_z3_profile_and_vice_versa() {
        use k_rust::backend::BackendOptions;
        let build = SolverProfile::BUILD;
        assert_eq!(build == SolverProfile::Z3, cfg!(feature = "z3"));
        let mut backend = Backend::new(
            r"[]
            module MAIN
                sort SortS{} []
                symbol Lbla{}() : SortS{} [constructor{}()]
            endmodule []",
            "MAIN",
            BackendOptions::default(),
        )
        .expect("backend");
        assert_eq!(SolverProfile::of(&backend), build);
        let state = Pattern::Application {
            symbol: k_rust::kore::ast::Symbol {
                name: "Lbla".to_owned(),
                sort_parameters: Vec::new(),
            },
            arguments: Vec::new(),
        };
        let budget = ExecutionBudget {
            time: Duration::from_secs(10),
            max_simplification_iterations: 10,
            max_depth: None,
            max_breadth: None,
        };
        assert_eq!(
            ExecutionAdapter::new(SolverProfile::NoZ3).profile(),
            SolverProfile::NoZ3
        );
        for profile in [SolverProfile::NoZ3, SolverProfile::Z3] {
            let adapter = ExecutionAdapter::with_profile(profile);
            assert_eq!(adapter.profile(), profile);
            let observed = adapter.execute(&mut backend, &state, budget);
            let unobserved = adapter.execute_unobserved(&mut backend, &state, budget);
            if profile == build {
                let observed = observed.expect("matching profile executes");
                assert_eq!(observed.leaves().len(), 1);
                let unobserved = unobserved.expect("matching profile executes");
                assert!(!unobserved.timed_out);
                assert_eq!(unobserved.leaves.len(), 1);
            } else {
                assert_eq!(
                    observed,
                    Err(ExecutionAdapterFailure::SolverProfileMismatch)
                );
                assert_eq!(
                    unobserved,
                    Err(ExecutionAdapterFailure::SolverProfileMismatch)
                );
            }
        }
    }

    /// VI-03F review minor M1 (routed to VI-06): a fired watchdog makes the unobserved run a
    /// timeout, as it does for `execute` and `execute_steps`, whether the backend then returns
    /// leaves or an error. It is never a complete run.
    #[test]
    fn zero_budget_unobserved_execution_is_timeout() {
        use k_rust::backend::BackendOptions;
        let mut backend = Backend::new(
            r"[]
            module MAIN
                sort SortS{} []
                symbol Lbla{}() : SortS{} [constructor{}()]
            endmodule []",
            "MAIN",
            BackendOptions::default(),
        )
        .expect("backend");
        let state = Pattern::Application {
            symbol: Symbol {
                name: "Lbla".to_owned(),
                sort_parameters: Vec::new(),
            },
            arguments: Vec::new(),
        };
        let budget = ExecutionBudget {
            time: Duration::ZERO,
            max_simplification_iterations: 10,
            max_depth: None,
            max_breadth: None,
        };
        let unobserved = ExecutionAdapter::with_profile(SolverProfile::BUILD).execute_unobserved(
            &mut backend,
            &state,
            budget,
        );
        // Before the fix (measured): no-Z3 `Ok([one Cancelled leaf])`, Z3 `Ok([])` (the backend's
        // cancellation error mapped to no leaves), both indistinguishable from a complete run.
        let unobserved = unobserved.expect("a timeout is not an adapter failure");
        assert!(unobserved.timed_out, "a fired watchdog is a timeout");
        // Re-pin R0a (finding E-14; answers section_2_2_summary (5)): at 927b9ce6 the no-Z3
        // build kept the cancelled leaf (1 leaf) and Z3 returned the cancellation error. At
        // 501f18b9 both builds return the error for a cancellation seen at the operation's entry,
        // so no leaf is published; the fired watchdog still makes the run a Timeout.
        assert_eq!(
            unobserved.leaves.len(),
            0,
            "a cancellation at entry returns the error in both profiles"
        );
    }

    /// Re-pin R0b deliverable 3 (findings A-04, A-05; answers section 2.3): a run is a timeout
    /// exactly when the watchdog fired, k-rust answers an error whose stop cause is `Cancelled`,
    /// or an `Ok` result has a `Cancelled` leaf; every other error is an infrastructure failure.
    /// The cancelled-at-entry error is real: a token already cancelled when the request enters
    /// makes the backend answer `Err` with stop cause `Cancelled` in both profiles
    /// (section_2_2_summary (5)), and it is a timeout even when kink's own watchdog did not fire.
    #[test]
    fn timeouts_are_exactly_cancellations() {
        use k_rust::backend::BackendOptions;
        let mut backend = Backend::new(
            r"[]
            module MAIN
                sort SortS{} []
                symbol Lbla{}() : SortS{} [constructor{}()]
            endmodule []",
            "MAIN",
            BackendOptions::default(),
        )
        .expect("backend");
        let state = Pattern::Application {
            symbol: Symbol {
                name: "Lbla".to_owned(),
                sort_parameters: Vec::new(),
            },
            arguments: Vec::new(),
        };
        let budget = ExecutionBudget {
            time: Duration::from_secs(10),
            max_simplification_iterations: 10,
            max_depth: None,
            max_breadth: None,
        };
        // An `Err` whose stop cause is `Cancelled`, with the watchdog not fired: Timeout.
        let token = CancellationToken::new();
        token.cancel();
        let cancelled = token.scope(|| {
            backend.execute_kore(request(
                state.clone(),
                budget,
                Requested::unstopped(ResultRun::default()),
            ))
        });
        let error = cancelled
            .as_ref()
            .expect_err("a cancelled entry answers Err");
        assert_eq!(error.stop_cause(), Some(&StopCause::Cancelled));
        let (result, timed_out) =
            settle(cancelled, false, ResultModality::StateSet).expect("a timeout");
        assert!(timed_out && result.leaves.is_empty());
        // An `Err` that is no stop at all (an unknown symbol), the watchdog not fired: an
        // infrastructure failure, never a timeout; with the watchdog fired it is a timeout.
        let unknown = Pattern::Application {
            symbol: Symbol {
                name: "Lblnowhere".to_owned(),
                sort_parameters: Vec::new(),
            },
            arguments: Vec::new(),
        };
        let failed = backend.execute_kore(request(
            unknown.clone(),
            budget,
            Requested::unstopped(ResultRun::default()),
        ));
        let error = failed.as_ref().expect_err("an unknown symbol fails");
        assert_eq!(error.stop_cause(), None);
        assert!(matches!(
            settle(failed, false, ResultModality::StateSet),
            Err(ExecutionAdapterFailure::Backend(_))
        ));
        assert!(
            settle(
                backend.execute_kore(request(
                    unknown,
                    budget,
                    Requested::unstopped(ResultRun::default())
                )),
                true,
                ResultModality::StateSet
            )
            .is_ok_and(|(_, t)| t)
        );
        // An `Ok` result: a timeout exactly when the watchdog fired or a leaf is `Cancelled`.
        let complete = backend
            .execute_kore(request(
                state.clone(),
                budget,
                Requested::unstopped(ResultRun::default()),
            ))
            .unwrap();
        assert!(
            complete
                .leaves
                .iter()
                .all(|leaf| leaf.reason != HaltReasonOutput::Cancelled)
        );
        let state_set = ResultModality::StateSet;
        assert!(!settle(Ok(complete.clone()), false, state_set).unwrap().1);
        assert!(settle(Ok(complete.clone()), true, state_set).unwrap().1);
        let mut cancelled_leaf = complete;
        cancelled_leaf.leaves[0].reason = HaltReasonOutput::Cancelled;
        assert!(
            settle(Ok(cancelled_leaf.clone()), false, state_set)
                .unwrap()
                .1
        );
        // Re-pin L1-1 (finding A-03): the request answers a cancellation with an error, so a
        // `Cancelled` leaf is outside its contract and the adapter refuses it.
        assert_eq!(
            ExecutionAdapter::adapt_result(
                cancelled_leaf,
                true,
                &budget,
                vec![LeafFeasibility::Unknown],
                RecordedRun {
                    short_circuit_readings: true,
                    ground: true,
                },
            ),
            Err(ExecutionAdapterFailure::ContractViolation(
                HaltClass::Cancelled
            ))
        );
    }

    /// Re-pin L1-1: the request kink sends, field by field. Every run collects coverage and
    /// carries no trace, a cancellation answers an error, step timeouts stay off, and the result
    /// run's modality and work budget are the caller's.
    #[test]
    fn the_request_sets_the_lane_1_options() {
        let state = Pattern::Application {
            symbol: Symbol {
                name: "Lbla".to_owned(),
                sort_parameters: Vec::new(),
            },
            arguments: Vec::new(),
        };
        let budget = ExecutionBudget {
            time: Duration::from_secs(1),
            max_simplification_iterations: 7,
            max_depth: Some(3),
            max_breadth: None,
        };
        for run in [
            ResultRun::default(),
            STEPPED.run,
            ResultRun {
                guards: false,
                modality: ResultModality::StateSet,
                max_work: Some(11),
            },
        ] {
            // A stop is sent as the backend's stop rules, before as cut points and after as
            // terminal rules, and changes no other field.
            let stop = StopRules {
                before: vec!["before".to_owned()],
                after: vec!["after".to_owned(), "MAIN.after".to_owned()],
            };
            // A count is sent past the first arrival, and only with a stop rule: a request to
            // the first arrival, or with no rule to arrive at, is the request before counts.
            let three = NonZeroU64::new(3).unwrap();
            for (stop, before, after, count, sent) in [
                (
                    &StopRules::NONE,
                    Vec::new(),
                    Vec::new(),
                    NonZeroU64::MIN,
                    None,
                ),
                (&StopRules::NONE, Vec::new(), Vec::new(), three, None),
                (
                    &stop,
                    stop.before.clone(),
                    stop.after.clone(),
                    NonZeroU64::MIN,
                    None,
                ),
                (
                    &stop,
                    stop.before.clone(),
                    stop.after.clone(),
                    three,
                    Some(three),
                ),
            ] {
                let request = request(
                    state.clone(),
                    budget,
                    Requested {
                        run,
                        stop,
                        count,
                        conditioned: false,
                        guards: None,
                    },
                );
                assert_eq!(request.stop_count, sent);
                assert_eq!(request.result_modality, run.modality.output());
                assert_eq!(request.max_work, run.max_work);
                assert!(request.collect_coverage);
                assert!(request.collect_committed);
                assert!(!request.trace);
                assert_eq!(request.cancelled_result, CancelledResultOutput::Error);
                assert_eq!(request.step_timeout_ms, None);
                assert!(!request.moving_average_timeout);
                assert_eq!(request.max_depth, Some(3));
                assert_eq!(request.max_simplification_iterations, 7);
                assert!(matches!(request.strategy, ExecutionStrategy::All));
                assert!(!request.stop_at_branch);
                // Without a stop the request selects no stop rule: the request of v2.
                assert_eq!(request.cut_point_rules, before);
                assert_eq!(request.terminal_rules, after);
            }
        }
        assert_eq!(ResultRun::default().modality, ResultModality::StateSet);
        assert_eq!(ResultRun::default().max_work, None);
        assert_eq!(STEPPED.run.modality, ResultModality::PathSet);
        assert_eq!(STEPPED.run.max_work, None);
        assert!(STEPPED.stop.is_none());
    }

    /// A stop is refused on a backend that does not list passed stops, before anything runs: its
    /// empty list would not tell a run that passed a stop rule from one that passed none. A
    /// request without stop rules needs no list. The in-process backend lists them.
    #[test]
    fn a_stop_needs_a_backend_that_lists_passed_stops() {
        use k_rust::backend::BackendOptions;
        let mut backend = Backend::new(
            r"[]
            module MAIN
                sort SortS{} []
                symbol Lbla{}() : SortS{} [constructor{}()]
            endmodule []",
            "MAIN",
            BackendOptions::default(),
        )
        .expect("backend");
        let listing = backend.capabilities();
        assert!(listing.passed_stops);
        let unlisting = BackendCapabilities {
            passed_stops: false,
            ..listing
        };
        let stop = StopRules {
            before: Vec::new(),
            after: vec!["next".to_owned()],
        };
        let requested = |stop, count| Requested {
            run: ResultRun::default(),
            stop,
            count: NonZeroU64::new(count).unwrap(),
            conditioned: false,
            guards: None,
        };
        assert_eq!(stops_listed(requested(&NO_STOP_RULES, 1), listing), Ok(()));
        assert_eq!(stops_listed(requested(&stop, 1), listing), Ok(()));
        assert_eq!(
            stops_listed(requested(&NO_STOP_RULES, 1), unlisting),
            Ok(())
        );
        assert!(matches!(
            stops_listed(requested(&stop, 1), unlisting),
            Err(ExecutionAdapterFailure::Backend(_))
        ));
        // A count past the first arrival needs a backend that counts arrivals, which the
        // in-process backend does; to the first arrival, or without a rule, it needs nothing.
        assert!(listing.stop_count);
        let uncounting = BackendCapabilities {
            stop_count: false,
            ..listing
        };
        assert_eq!(stops_listed(requested(&stop, 3), listing), Ok(()));
        assert_eq!(stops_listed(requested(&stop, 1), uncounting), Ok(()));
        assert_eq!(
            stops_listed(requested(&NO_STOP_RULES, 3), uncounting),
            Ok(())
        );
        assert!(matches!(
            stops_listed(requested(&stop, 3), uncounting),
            Err(ExecutionAdapterFailure::Backend(_))
        ));
        // With a listing backend the stopped run goes ahead.
        let state = Pattern::Application {
            symbol: Symbol {
                name: "Lbla".to_owned(),
                sort_parameters: Vec::new(),
            },
            arguments: Vec::new(),
        };
        let budget = ExecutionBudget {
            time: Duration::from_secs(10),
            max_simplification_iterations: 10,
            max_depth: None,
            max_breadth: None,
        };
        let adapter = ExecutionAdapter::new(SolverProfile::of(&backend));
        let stopped = adapter
            .execute_result_stopped(&mut backend, &state, budget, ResultRun::default(), &stop)
            .expect("a listing backend runs a stop");
        assert!(stopped.facts().passed_stops.is_empty());
    }

    /// CF-21: a stop halt is admitted exactly for a request that selected a rule in its
    /// direction, a cut point before and a terminal leaf after; under any other request it is a
    /// contract violation and the adapter publishes no leaf. A cut-point leaf exposes the one step
    /// it stopped before, and one that proposes another number of successors is outside k-rust's
    /// contract. The run's passed stops reach its facts as k-rust lists them.
    #[test]
    fn unrequested_stop_halts_are_contract_violations() {
        let constant = |name: &str| Pattern::Application {
            symbol: Symbol {
                name: name.to_owned(),
                sort_parameters: Vec::new(),
            },
            arguments: Vec::new(),
        };
        let candidate = |name: &str| k_rust::backend::ExecutionCandidateOutput {
            state: constant(name),
            unique_id: format!("id-{name}"),
            label: Some(name.to_owned()),
            diagnostics: Vec::new(),
        };
        let leaf = |reason, candidates| KoreExecutionLeaf {
            state: constant("Lblunit"),
            diagnostics: Vec::new(),
            candidates,
            remainder: None,
            depth: 1,
            reason,
            rule_id: None,
            rule_label: None,
            contradicted_total: None,
            cause: None,
            detail: None,
            trace: Vec::new(),
            branch: Vec::new(),
            effects: Vec::new(),
            observations: Vec::new(),
            stops: None,
            arrivals: None,
        };
        let result = |leaf, passed_stops| KoreExecutionResult {
            modality: ResultModalityOutput::StateSet,
            leaves: vec![leaf],
            effects: Vec::new(),
            discarded: Vec::new(),
            coverage: None,
            work: 2,
            expanded: 1,
            stack_stops: 0,
            smt_unknowns: 0,
            implementation_chosen_values: Vec::new(),
            contradicted_claims: Vec::new(),
            allowance_refusals: Vec::new(),
            unsupported_hooks: Vec::new(),
            short_circuit_readings: Vec::new(),
            passed_stops,
            state_matches: None,
        };
        let budget = ExecutionBudget {
            time: Duration::from_secs(1),
            max_simplification_iterations: 1,
            max_depth: None,
            max_breadth: None,
        };
        let adapt = |leaf, passed_stops, stop: &StopRules| {
            ExecutionAdapter::adapt(
                result(leaf, passed_stops),
                false,
                &budget,
                Requested {
                    run: ResultRun::default(),
                    stop,
                    count: NonZeroU64::MIN,
                    conditioned: false,
                    guards: None,
                },
                vec![LeafFeasibility::Syntactic],
                &BTreeSet::new(),
                RecordedRun {
                    short_circuit_readings: true,
                    ground: true,
                },
            )
        };
        let before = StopRules {
            before: vec!["next".to_owned()],
            after: Vec::new(),
        };
        let after = StopRules {
            before: Vec::new(),
            after: vec!["next".to_owned()],
        };
        let cut = || leaf(HaltReasonOutput::CutPoint, Some(vec![candidate("Lblnext")]));
        let terminal = || leaf(HaltReasonOutput::Terminal, None);
        let violation = ExecutionAdapterFailure::ContractViolation;
        for stop in [&StopRules::NONE, &after] {
            assert_eq!(
                adapt(cut(), Vec::new(), stop),
                Err(violation(HaltClass::CutPoint))
            );
        }
        for stop in [&StopRules::NONE, &before] {
            assert_eq!(
                adapt(terminal(), Vec::new(), stop),
                Err(violation(HaltClass::TerminalRule))
            );
        }
        let stopped = adapt(cut(), Vec::new(), &before).expect("a requested cut point");
        assert_eq!(stopped.leaves()[0].halt, HaltClass::CutPoint);
        assert_eq!(
            stopped.leaves()[0].proposal,
            Some(StopProposal {
                successor: constant("Lblnext"),
                rule_id: "id-Lblnext".to_owned(),
                label: Some("Lblnext".to_owned()),
            })
        );
        let ended = adapt(terminal(), Vec::new(), &after).expect("a requested terminal leaf");
        assert_eq!(ended.leaves()[0].halt, HaltClass::TerminalRule);
        assert_eq!(ended.leaves()[0].proposal, None);
        for candidates in [
            None,
            Some(Vec::new()),
            Some(vec![candidate("Lbla"), candidate("Lblb")]),
        ] {
            assert_eq!(
                adapt(
                    leaf(HaltReasonOutput::CutPoint, candidates.clone()),
                    Vec::new(),
                    &before
                ),
                Err(violation(HaltClass::CutPoint)),
                "{candidates:?}"
            );
        }
        // A stuck leaf proposes nothing, under a stop as without one.
        for stop in [&StopRules::NONE, &before, &after] {
            let stuck = adapt(leaf(HaltReasonOutput::Stuck, None), Vec::new(), stop).unwrap();
            assert_eq!(stuck.leaves()[0].proposal, None);
            assert!(stuck.facts().passed_stops.is_empty());
        }
        let passed = vec![PassedStopOutput {
            rule: "next".to_owned(),
            depth: 3,
        }];
        let listed = adapt(terminal(), passed.clone(), &after).unwrap();
        assert_eq!(listed.facts().passed_stops, passed);
    }

    /// CF-21, end to end on k-rust: a run that stops before a rule ends at the state its step
    /// leaves, a cut point proposing the step's successor, which the run's coverage applies but
    /// does not commit; a run that stops after it ends at the successor; the bridge reads both as
    /// complete ends, and neither run is excluded. Where the stop rule's step has another
    /// successor, the run stops nothing, lists the rule as passed with the step's depth, and is
    /// excluded (`passed-stop`), in both directions.
    #[test]
    fn requested_stop_leaves_are_complete() {
        use crate::bridge::{BridgeContext, paths_from_execution};
        use crate::exclusion::{DefinitionExclusions, Exclusion};
        use k_rust::backend::BackendOptions;
        use kink_pattern::{CollectionStop, ExecutionTerminalKind, PathStop, SymbolSorts};
        let constructor = |name: &str| {
            format!(
                "symbol Lbl{name}{{}}() : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]"
            )
        };
        let rule = |from: &str, to: &str| {
            format!(
                r#"axiom{{}} \rewrites{{SortS{{}}}}(\and{{SortS{{}}}}(Lbl{from}{{}}(), \top{{SortS{{}}}}()), Lbl{to}{{}}()) [label{{}}("{from}-{to}"), UNIQUE'Unds'ID{{}}("id-{from}-{to}")]"#
            )
        };
        let source = format!(
            "[]\nmodule MAIN\n    sort SortS{{}} []\n    {}\n    {}\nendmodule []",
            ["a", "b", "c", "x", "y", "z"]
                .map(constructor)
                .join("\n    "),
            [
                rule("a", "b"),
                rule("b", "c"),
                rule("x", "y"),
                rule("x", "z")
            ]
            .join("\n    "),
        );
        let kore = k_rust::kore::parser::parse_definition(&source).expect("KORE");
        let mut backend = Backend::from_definition(kore.clone(), "MAIN", BackendOptions::default())
            .expect("backend");
        let exclusions = {
            let selected = backend.select_definition(None).expect("definition");
            DefinitionExclusions::of(&kore, &selected, &[])
        };
        let sorts = SymbolSorts::from_definition(&kore);
        let context = BridgeContext {
            test_id: "t",
            classify: &|_| ExecutionTerminalKind::Normal,
            sorts: &sorts,
        };
        let constant = |name: &str| Pattern::Application {
            symbol: Symbol {
                name: format!("Lbl{name}"),
                sort_parameters: Vec::new(),
            },
            arguments: Vec::new(),
        };
        let budget = ExecutionBudget {
            time: Duration::from_secs(30),
            max_simplification_iterations: 100,
            max_depth: None,
            max_breadth: None,
        };
        let adapter = ExecutionAdapter::with_profile(SolverProfile::BUILD);
        let mut run = |start: &str, before: &[&str], after: &[&str]| {
            let stop = StopRules {
                before: before.iter().map(|name| (*name).to_owned()).collect(),
                after: after.iter().map(|name| (*name).to_owned()).collect(),
            };
            adapter
                .execute_result_stopped(
                    &mut backend,
                    &constant(start),
                    budget,
                    ResultRun::default(),
                    &stop,
                )
                .expect("the run is adapted")
        };
        let summary = |execution: &AdaptedExecution| {
            execution
                .leaves()
                .iter()
                .map(|leaf| (leaf.halt, leaf.branch.state.clone(), leaf.branch.depth))
                .collect::<Vec<_>>()
        };
        let ends = |execution: &AdaptedExecution| {
            let bridged = paths_from_execution(execution, &context, &|_| true).expect("bridged");
            assert_eq!(bridged.collection.stop, CollectionStop::SearchExhausted);
            bridged
                .paths
                .into_iter()
                .map(|path| {
                    assert!(path.complete);
                    assert_eq!(path.stop, PathStop::Terminal);
                    path.execution_terminal.expect("terminal").state
                })
                .collect::<Vec<_>>()
        };

        // Without a stop: the run's own end.
        let own = run("a", &[], &[]);
        assert_eq!(summary(&own), [(HaltClass::Stuck, constant("c"), 2)]);
        assert_eq!(exclusions.run_exclusion(&own), None);

        // Before `b-c`: a cut point at `b`, proposing `c` by `b-c`, which is applied and not
        // committed.
        let cut = run("a", &["b-c"], &[]);
        assert_eq!(summary(&cut), [(HaltClass::CutPoint, constant("b"), 1)]);
        let proposal = cut.leaves()[0].proposal.as_ref().expect("a proposal");
        assert_eq!(proposal.successor, constant("c"));
        assert_eq!(proposal.rule_id, "id-b-c");
        assert!(cut.facts().passed_stops.is_empty());
        assert_eq!(exclusions.run_exclusion(&cut), None);
        assert_eq!(ends(&cut), [constant("b")]);
        let coverage = cut.coverage().expect("coverage");
        assert!(coverage.applied.contains("id-b-c"));
        assert!(!coverage.committed.contains("id-b-c"));
        assert!(coverage.committed.contains("id-a-b"));

        // After `b-c`: a terminal leaf at `c`, which the run committed.
        let terminal = run("a", &[], &["b-c"]);
        assert_eq!(
            summary(&terminal),
            [(HaltClass::TerminalRule, constant("c"), 2)]
        );
        assert_eq!(terminal.leaves()[0].proposal, None);
        assert_eq!(exclusions.run_exclusion(&terminal), None);
        assert_eq!(ends(&terminal), [constant("c")]);
        assert!(
            terminal
                .coverage()
                .expect("coverage")
                .committed
                .contains("id-b-c")
        );

        // `x-y` is one of two successors of `x`: no stop, the rule is passed at depth 0, and the
        // run is excluded.
        for (before, after) in [(&["x-y"][..], &[][..]), (&[][..], &["x-y"][..])] {
            let passed = run("x", before, after);
            assert!(
                passed
                    .leaves()
                    .iter()
                    .all(|leaf| leaf.halt == HaltClass::Stuck),
                "{before:?} {after:?}"
            );
            assert_eq!(
                passed.facts().passed_stops,
                [PassedStopOutput {
                    rule: "x-y".to_owned(),
                    depth: 0,
                }]
            );
            assert_eq!(
                exclusions.run_exclusion(&passed),
                Some(Exclusion::PassedStop)
            );
        }

        // Counted, with both steps selected and one table for every request: after the second
        // arrival the run ends at `c`, having committed both steps; before it, at `b`, proposing
        // `c` by `b-c` and having committed `a-b`, whose arrival it took; past the arrivals, the
        // run's own end. Each is one request, whose leaf reports its arrivals.
        let mut tables = DefinitionTables::new();
        let mut counted = |before: &[&str], after: &[&str], count: u64| {
            let stop = StopRules {
                before: before.iter().map(|name| (*name).to_owned()).collect(),
                after: after.iter().map(|name| (*name).to_owned()).collect(),
            };
            adapter
                .execute_result_counted(
                    &mut backend,
                    &mut tables,
                    &constant("a"),
                    budget,
                    ResultRun::default(),
                    &stop,
                    NonZeroU64::new(count).unwrap(),
                    None,
                )
                .expect("the run is adapted")
        };
        let both = ["a-b", "b-c"];
        let second = counted(&[], &both, 2);
        assert_eq!(
            summary(&second),
            [(HaltClass::TerminalRule, constant("c"), 2)]
        );
        assert_eq!(ends(&second), [constant("c")]);
        let committed = &second.coverage().expect("coverage").committed;
        assert!(committed.contains("id-a-b") && committed.contains("id-b-c"));
        let cut = counted(&both, &[], 2);
        assert_eq!(summary(&cut), [(HaltClass::CutPoint, constant("b"), 1)]);
        assert_eq!(
            cut.leaves()[0].proposal.as_ref().map(|p| &p.successor),
            Some(&constant("c"))
        );
        let coverage = cut.coverage().expect("coverage");
        assert!(coverage.committed.contains("id-a-b"));
        assert!(!coverage.committed.contains("id-b-c"));
        assert_eq!(ends(&cut), [constant("b")]);
        for (before, after) in [(&both[..], &[][..]), (&[][..], &both[..])] {
            let past = counted(before, after, 5);
            assert_eq!(summary(&past), [(HaltClass::Stuck, constant("c"), 2)]);
            assert_eq!(ends(&past), [constant("c")]);
        }
    }

    /// A leaf's arrivals at a stop must be ones its request can yield: none reported without a
    /// count; with one, a stop leaf at the count and any other leaf short of it. Otherwise a stop
    /// leaf short of the count would be read as an end its path has not reached.
    #[test]
    fn a_leaf_reports_the_arrivals_its_request_counts() {
        let stop = StopRules {
            before: vec!["r".to_owned()],
            after: Vec::new(),
        };
        let requested = |stop, count| Requested {
            run: ResultRun::default(),
            stop,
            count: NonZeroU64::new(count).unwrap(),
            conditioned: false,
            guards: None,
        };
        for halt in [HaltClass::CutPoint, HaltClass::Stuck] {
            for request in [requested(&NO_STOP_RULES, 3), requested(&stop, 1)] {
                assert!(request.admits_arrivals(halt, None, None));
                assert!(!request.admits_arrivals(halt, Some(1), None));
                // Arrivals are reported exactly when a condition was asked.
                assert!(!request.admits_arrivals(halt, None, Some(1)));
            }
            assert!(!requested(&stop, 3).admits_arrivals(halt, None, None));
        }
        let conditioned = Requested {
            conditioned: true,
            ..requested(&stop, 3)
        };
        assert!(conditioned.admits_arrivals(HaltClass::StopUndecided, Some(2), Some(5)));
        assert!(!conditioned.admits_arrivals(HaltClass::StopUndecided, Some(3), Some(5)));
        assert!(!conditioned.admits_arrivals(HaltClass::CutPoint, Some(3), None));
        // With a condition the events are reported at the count 1 too.
        let first = Requested {
            conditioned: true,
            ..requested(&stop, 1)
        };
        assert!(first.admits_arrivals(HaltClass::CutPoint, Some(1), Some(4)));
        assert!(first.admits_arrivals(HaltClass::StopUndecided, Some(0), Some(4)));
        assert!(!first.admits_arrivals(HaltClass::CutPoint, None, Some(4)));
        let budget = ExecutionBudget {
            time: Duration::from_secs(1),
            max_simplification_iterations: 1,
            max_depth: None,
            max_breadth: None,
        };
        assert!(conditioned.admits(HaltClass::StopUndecided, &budget));
        assert!(!requested(&stop, 3).admits(HaltClass::StopUndecided, &budget));
        let three = requested(&stop, 3);
        for (halt, admitted) in [
            (HaltClass::CutPoint, [false, false, false, true, false]),
            (HaltClass::TerminalRule, [false, false, false, true, false]),
            (HaltClass::Stuck, [true, true, true, false, false]),
            (HaltClass::DepthBound, [true, true, true, false, false]),
        ] {
            for (stops, admitted) in admitted.into_iter().enumerate() {
                assert_eq!(
                    three.admits_arrivals(halt, Some(stops as u64), None),
                    admitted,
                    "{halt:?} {stops}"
                );
            }
        }
    }

    #[test]
    fn unrequested_depth_bound_is_a_contract_violation() {
        let budget = ExecutionBudget {
            time: Duration::from_secs(1),
            max_simplification_iterations: 1,
            max_depth: None,
            max_breadth: None,
        };
        assert!(!HaltClass::DepthBound.adapter_admits(&budget));
    }

    /// Re-pin R0a (findings E-02, E-05), L1-1: a request without `max_work` (every stepped run,
    /// and a result run without a work budget) never admits a `work-bound` leaf: whatever the
    /// budget and whatever leaves surround it, the adapter answers `ContractViolation` and
    /// publishes no leaf. A request with `max_work` admits it, and the bridge makes its path
    /// incomplete without a real prefix (bridge `halt_stop`; oracles.rs
    /// `work_bound_leaf_never_yields_distinguish`).
    #[test]
    fn work_bound_leaf_is_a_contract_violation_under_every_budget() {
        let state = Pattern::Application {
            symbol: Symbol {
                name: "Lblunit".into(),
                sort_parameters: Vec::new(),
            },
            arguments: Vec::new(),
        };
        let leaf = |reason| KoreExecutionLeaf {
            state: state.clone(),
            diagnostics: Vec::new(),
            candidates: None,
            remainder: None,
            depth: 0,
            reason,
            rule_id: None,
            rule_label: None,
            contradicted_total: None,
            cause: None,
            detail: None,
            trace: Vec::new(),
            branch: Vec::new(),
            effects: Vec::new(),
            observations: Vec::new(),
            stops: None,
            arrivals: None,
        };
        let result = |leaves: Vec<KoreExecutionLeaf>| KoreExecutionResult {
            modality: ResultModalityOutput::PathSet,
            leaves,
            effects: Vec::new(),
            discarded: Vec::new(),
            coverage: None,
            work: 1,
            expanded: 0,
            stack_stops: 0,
            smt_unknowns: 0,
            implementation_chosen_values: Vec::new(),
            contradicted_claims: Vec::new(),
            allowance_refusals: Vec::new(),
            unsupported_hooks: Vec::new(),
            short_circuit_readings: Vec::new(),
            passed_stops: Vec::new(),
            state_matches: None,
        };
        let one = NonZeroUsize::new(1).expect("nonzero");
        for (max_depth, max_breadth) in [
            (None, None),
            (Some(1), None),
            (None, Some(one)),
            (Some(1), Some(one)),
        ] {
            let budget = ExecutionBudget {
                time: Duration::from_secs(1),
                max_simplification_iterations: 1,
                max_depth,
                max_breadth,
            };
            assert!(!HaltClass::WorkBound.adapter_admits(&budget), "{budget:?}");
            assert!(
                HaltClass::WorkBound.admitted_by(&budget, Some(1), &StopRules::NONE),
                "{budget:?}"
            );
            for leaves in [
                vec![leaf(HaltReasonOutput::WorkBound)],
                vec![
                    leaf(HaltReasonOutput::Stuck),
                    leaf(HaltReasonOutput::WorkBound),
                ],
            ] {
                let feasibility = vec![LeafFeasibility::Syntactic; leaves.len()];
                for timed_out in [false, true] {
                    assert_eq!(
                        ExecutionAdapter::adapt(
                            result(leaves.clone()),
                            timed_out,
                            &budget,
                            Requested::unstopped(ResultRun::default()),
                            feasibility.clone(),
                            &BTreeSet::new(),
                            RecordedRun {
                                short_circuit_readings: true,
                                ground: true,
                            },
                        ),
                        Err(ExecutionAdapterFailure::ContractViolation(
                            HaltClass::WorkBound
                        )),
                        "{budget:?} timed_out={timed_out}"
                    );
                    let admitted = ExecutionAdapter::adapt(
                        result(leaves.clone()),
                        timed_out,
                        &budget,
                        Requested::unstopped(ResultRun {
                            max_work: Some(1),
                            ..ResultRun::default()
                        }),
                        feasibility.clone(),
                        &BTreeSet::new(),
                        RecordedRun {
                            short_circuit_readings: true,
                            ground: true,
                        },
                    )
                    .expect("a work budget admits its leaf");
                    assert_eq!(
                        admitted.leaves().last().map(|leaf| leaf.halt),
                        Some(HaltClass::WorkBound)
                    );
                }
            }
        }
    }
}
