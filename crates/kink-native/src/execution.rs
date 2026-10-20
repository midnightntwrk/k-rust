//! Time-bounded execution through the public k-rust facade (re-pin lane 1, L1-1).
//!
//! A result run ([`ExecutionAdapter::execute`], [`ExecutionAdapter::execute_result`]) is one
//! unobserved run whose leaves are, by default, k-rust's state set: structurally equal final
//! configurations merged ([`ResultModality::StateSet`]). A state set whose leaves include an
//! undefined step (`Trivial`), a `Vacuous` leaf or a contradicted `total` claim is replaced by the
//! path set of the same request, because under StateSet such a leaf's rule is witness metadata
//! and its multiplicity differs (k-rust section_2_2_summary (4)), while kink's exclusions read
//! that rule ([`crate::exclusion`]). A stepped run ([`ExecutionAdapter::execute_steps`]) stays an
//! observed path set: one leaf per path, each with its own configuration sequence.
//! Every run carries no trace and collects k-rust's run coverage ([`RunCoverage`]), and a
//! cancelled run answers an error, so a timed-out run publishes no leaf. A watchdog cancels
//! execution when the time budget expires; a result run may also carry a work budget
//! (`max_work`), whose `work-bound` leaf makes the run incomplete.
//! Each leaf also records whether its state is shown feasible or infeasible, and an
//! indeterminate leaf its structured cause; the execution records the definition facts the
//! bridge needs to use them ([`crate::feasibility`]).
//! Every run also carries k-rust's run-level facts ([`RunFacts`], re-pin adoption A-1): the lists
//! of open values read, contradicted claims, allowance refusals and unsupported hooks, and the
//! count of undecided solver answers, which the exclusions read ([`crate::exclusion`]).

use std::{
    collections::{BTreeMap, BTreeSet},
    num::NonZeroUsize,
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
        mpsc,
    },
    thread,
    time::Duration,
};

use k_rust::backend::{
    BACKEND_SCHEMA_VERSION, Backend, BackendDiagnosticOutput, BackendError, CancelledResultOutput,
    ChosenValueOutput, ContradictedClaimOutput, ContradictedTotalOutput, EffectOutput,
    ExecuteRequest, ExecutionLeaf, ExecutionResult, ExecutionStrategy, HaltReasonOutput,
    ObservationEventOutput, ObservedInOutput, ObservedRequest, ResultModalityOutput,
    RunCoverageOutput, SearchFailureOutput, TraceEntry, TransitionClassOutput, TransitionIdOutput,
    UnevaluatedHookOutput,
};
use k_rust::kore::{ast::Pattern, codec};
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
}

impl HaltClass {
    pub const ALL: [Self; 14] = [
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
    ];

    /// Whether the adapter's request can yield this halt under `budget`, for a request without
    /// a work budget (every stepped run, and a result run without `max_work`).
    #[must_use]
    pub const fn adapter_admits(self, budget: &ExecutionBudget) -> bool {
        self.admitted_by(budget, None)
    }

    /// Whether the adapter's request can yield this halt under `budget` and `max_work`. A
    /// `Cancelled` leaf never: every request answers a cancellation with an error
    /// (`cancelled_result: error`, re-pin finding A-03). A `work-bound` leaf exactly when the
    /// request set `max_work`.
    #[must_use]
    pub const fn admitted_by(self, budget: &ExecutionBudget, max_work: Option<u64>) -> bool {
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
            Self::Branch
            | Self::CutPoint
            | Self::TerminalRule
            | Self::Timeout
            | Self::Cancelled => false,
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
        }
    }
}

/// The solver profile of a backend. k-rust chooses its solver at compile time, so one build is
/// one profile: `NoZ3` without the `z3` feature of this crate, `Z3` with it (README section 9 of
/// `draft/tasks/symbolic-branching`).
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
    /// Wall-clock budget of one run (the watchdog's). A result run whose state set is replaced
    /// by its path set ([`ExecutionAdapter::execute_result`]) is two runs, each with this whole
    /// budget and a fresh watchdog, so it can take up to twice as long.
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

/// How a result run is requested besides its [`ExecutionBudget`]: its modality and its work
/// budget (k-rust `max_work`: the most states the run may visit across all its paths). The
/// default is a state set without a work budget.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct ResultRun {
    pub modality: ResultModality,
    pub max_work: Option<u64>,
}

/// k-rust's run coverage of one run (`collect_coverage`, `RunCoverageOutput`), by `UNIQUE_ID`:
/// every rule and equation the run applied, every one whose condition it began to decide
/// (`matched`, a superset; the two are what kink schedules by, [`crate::coverage::TestCoverage`]),
/// and the rewrite rules among `applied`: those for which a step built a successor or found the
/// step undefined, which a stepped path set's branch identities also name (the L1-1 differential
/// compares them). It covers every state the run explored, including leaves a state set merges
/// away. Coverage is a scheduling and report input only.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct RunCoverage {
    pub applied: BTreeSet<String>,
    pub matched: BTreeSet<String>,
    pub applied_rewrites: BTreeSet<String>,
}

impl RunCoverage {
    fn of(output: RunCoverageOutput, rewrites: &BTreeSet<String>) -> Self {
        let applied = output.applied.into_iter().collect::<BTreeSet<_>>();
        let applied_rewrites = applied.intersection(rewrites).cloned().collect();
        Self {
            applied,
            matched: output.matched.into_iter().collect(),
            applied_rewrites,
        }
    }
}

/// The run-level facts of one run (re-pin adoption A-1, `draft/tasks/repin-58720d2e/ADOPTION.md`):
/// the lists and the count k-rust 58720d2e5 added to `ExecutionResult` (KINK-17/1, KINK-18/2,
/// KINK-19/1), as k-rust answers them, for every run kink judges: a result run, the path set that
/// replaces a state set, a stepped run and an unobserved run. Each list holds what the run's leaves
/// carry and also what no leaf carries (k-rust `docs/compatibility.md` at 8f8ad57c5, lines 92,
/// 1536 and 1790): work that ended on no reported leaf (a candidate a defined sibling covered, a
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
    /// Every distinct value the definition leaves open that the run read
    /// (`implementationChosenValues`): its hook and class.
    pub implementation_chosen_values: Vec<ChosenValueOutput>,
    /// Every distinct contradicted claim the run or its definition's load observed
    /// (`contradictedClaims`), ground or not.
    pub contradicted_claims: Vec<ContradictedClaimOutput>,
    /// Every distinct `Bytes` result the memory allowance refused in the run or its load
    /// (`allowanceRefusals`), kept or dropped work alike.
    pub allowance_refusals: Vec<UnevaluatedHookOutput>,
    /// Every other application the run or its load left unevaluated as an unsupported hook
    /// (`unsupportedHooks`), whatever became of the work that met it.
    pub unsupported_hooks: Vec<UnevaluatedHookOutput>,
}

impl RunFacts {
    /// The facts of `result`, taken out of it.
    fn take(result: &mut ExecutionResult) -> Self {
        Self {
            smt_unknowns: result.smt_unknowns,
            implementation_chosen_values: std::mem::take(&mut result.implementation_chosen_values),
            contradicted_claims: std::mem::take(&mut result.contradicted_claims),
            allowance_refusals: std::mem::take(&mut result.allowance_refusals),
            unsupported_hooks: std::mem::take(&mut result.unsupported_hooks),
        }
    }

    /// The facts of two runs of one request together: each list without repeats, in first
    /// order, and the counts summed. A state set replaced by its path set keeps what the
    /// discarded state set noted ([`ExecutionAdapter::execute_result`]), so nothing either run
    /// met is lost.
    fn union(mut self, other: Self) -> Self {
        fn extend<T: PartialEq>(into: &mut Vec<T>, from: Vec<T>) {
            for item in from {
                if !into.contains(&item) {
                    into.push(item);
                }
            }
        }
        self.smt_unknowns += other.smt_unknowns;
        extend(
            &mut self.implementation_chosen_values,
            other.implementation_chosen_values,
        );
        extend(&mut self.contradicted_claims, other.contradicted_claims);
        extend(&mut self.allowance_refusals, other.allowance_refusals);
        extend(&mut self.unsupported_hooks, other.unsupported_hooks);
        self
    }

    /// The contradicted-claim records the definition's load observed (`observedIn: load`): facts
    /// about the definition, on every run's list (decision D-6).
    pub fn load_records(&self) -> impl Iterator<Item = &ContradictedClaimOutput> {
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
    /// `Unknown` for every leaf of a timed-out run, whose states are not decoded.
    pub feasibility: LeafFeasibility,
    /// Why the step stopped, exactly for an `Indeterminate` halt.
    pub cause: Option<SearchFailureOutput>,
    pub diagnostics: Vec<BackendDiagnosticOutput>,
    pub candidate_diagnostics: Vec<Vec<BackendDiagnosticOutput>>,
    pub remainder_diagnostics: Vec<BackendDiagnosticOutput>,
    /// The rule responsible for the undefined step of a `Trivial` leaf, when k-rust names one;
    /// `None` for every other halt.
    pub undefined_rule: Option<UndefinedStepRule>,
    /// The `total` (or `functional`) claim this leaf's undefined step contradicts, when k-rust
    /// names one (`contradictedTotal`, a `Trivial` or `Vacuous` leaf): the definition is
    /// inconsistent there, so the run is no evidence (re-pin decision 2, finding A-13;
    /// [`crate::exclusion::Exclusion::ContradictedClaim`]).
    pub contradicted_total: Option<ContradictedTotalOutput>,
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
    /// The modality of `leaves`: the request's, or `PathSet` when a state set was replaced by
    /// the path set of the same request ([`ExecutionAdapter::execute_result`]).
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
    Decode(String),
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
    pub state: serde_json::Value,
    pub depth: u64,
    pub trace: Vec<TraceEntry>,
    pub cause: Option<SearchFailureOutput>,
    pub diagnostics: Vec<BackendDiagnosticOutput>,
    pub candidate_diagnostics: Vec<Vec<BackendDiagnosticOutput>>,
    pub remainder_diagnostics: Vec<BackendDiagnosticOutput>,
    /// The transition identities of the branch. Empty for an unobserved leaf: k-rust's
    /// unobserved execution does not compute them.
    pub branch: Vec<TransitionIdOutput>,
    pub undefined_rule: Option<UndefinedStepRule>,
    pub contradicted_total: Option<ContradictedTotalOutput>,
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
    /// stop cause is `Cancelled`, or a `Cancelled` leaf). Its leaf states must not be decoded: a
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
    /// contradicted claims, allowance refusals and unsupported hooks, and its count of undecided
    /// solver answers; empty for a timed-out run.
    #[must_use]
    pub const fn facts(&self) -> &RunFacts {
        &self.facts
    }
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
}

/// The bounded request of one run. Strategy `all` is what makes the leaves the whole path set (or,
/// merged, the whole state set): every instance's every successor is followed, so a `Trivial`
/// leaf is an undefined step for each of its instances and the leaves cover the initial state.
/// Under `any` a step gives an instance one successor, from the first rule of its highest
/// applicable priority that is defined there (k-rust KK-73), so the events of the other
/// successors are missing; and it follows one collection candidate per rule, so an instance
/// matched only through another candidate may have a defined successor although its leaf is
/// `Trivial`. Stop-at-branch, cut-point and terminal rules are off, so no leaf stops at a branch or
/// a designated rule.
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
/// - `max_work`: `run.max_work` (none for a stepped run and by default); its `work-bound` leaf
///   is admitted exactly then ([`HaltClass::admitted_by`]).
///
/// - `collect_offered: false` (k-rust 58720d2e5, KINK-04/3): no offered coverage is asked for,
///   which is the behaviour before that field existed; asking changes no other field of the
///   result, and adopting it is for the round-D re-pin (probe P-1, draft/tasks/repin-58720d2e).
///
/// Step timeouts stay off: a step deadline is host-dependent, which an Execute-promise run must
/// not be (finding A-03).
fn request(state: Pattern, budget: ExecutionBudget, run: ResultRun) -> ExecuteRequest {
    ExecuteRequest {
        state,
        module_name: None,
        max_depth: budget.max_depth,
        max_breadth: budget.max_breadth.map(NonZeroUsize::get),
        max_simplification_iterations: budget.max_simplification_iterations,
        strategy: ExecutionStrategy::All,
        stop_at_branch: false,
        cut_point_rules: Vec::new(),
        terminal_rules: Vec::new(),
        step_timeout_ms: None,
        moving_average_timeout: false,
        assume_state_defined: false,
        result_modality: run.modality.output(),
        collect_coverage: true,
        collect_offered: false,
        max_work: run.max_work,
        trace: false,
        cancelled_result: CancelledResultOutput::Error,
        schema_version: BACKEND_SCHEMA_VERSION,
    }
}

/// The version of the execution request kink sends for a run, and of how a result run's
/// modality and work budget are chosen: a run's leaves, and so a verdict, depend on it, so kink's
/// semantics identity names it (kink-campaign `identity`). Bump it whenever `request`,
/// [`ExecutionAdapter::execute_result`]'s path-set replacement, or kink-campaign's choice of a
/// test's modality and of a mutant's work budget (`RunOptions`, `WorkBudget`) changes what a run
/// returns. v1 (re-pin L1-1 and L1-1-fix-1; L1-1 review 1 minor 5): a result run is a state set
/// (path-set replacement on an undefined step, a vacuous leaf or a contradicted claim, decided per
/// side), a stepped run an observed path set; no trace; run coverage collected; a cancellation
/// answers an error; `max_work` only on a mutant's result run, calibrated from the baseline's run
/// of the test. A campaign that stores reports (kink-corpus, replay) runs the default
/// `RunOptions`; kink-flow's tier-1 context names its work budget. Builds before packet CACHE-ID
/// name no version (1ee9955 ran path sets with traces).
pub const EXECUTION_REQUEST_VERSION: &str = "kink-native/execution-request/v1";

/// The request of a stepped run: an observed path set without a work budget.
const STEPPED: ResultRun = ResultRun {
    modality: ResultModality::PathSet,
    max_work: None,
};

/// Whether a state-set leaf is one whose rule or multiplicity kink's exclusions read, which
/// k-rust's state set reports only as witness metadata (k-rust section_2_2_summary (4); KINK-01
/// criterion 2: Trivial and Vacuous leaves agree with the path set as sets of (depth, state,
/// obligation), their rule ids as witness metadata): an undefined step (decision 2's
/// `preserves-definedness` check and the short-circuit check read its rule), a vacuous leaf, or a
/// leaf naming a contradicted `total` claim.
fn path_set_leaf(leaf: &AdaptedLeaf) -> bool {
    matches!(leaf.halt, HaltClass::Trivial | HaltClass::Vacuous)
        || leaf.contradicted_total.is_some()
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
    /// `run`. A state set none of whose leaves is an undefined step, a vacuous leaf or a
    /// contradicted claim ([`path_set_leaf`]) is returned as it is; otherwise the path set of the
    /// same request replaces it, so every such leaf kink's exclusions read has its own rule and
    /// multiplicity. A timed-out state set is returned as it is: it publishes no leaf. The
    /// replacement reads this run's leaves only, so the baseline's and a mutant's runs of one
    /// test can end in different modalities ([`AdaptedExecution::modality`]); a replaced run
    /// takes up to twice `budget.time` ([`ExecutionBudget::time`]).
    pub fn execute_result(
        &self,
        backend: &mut Backend,
        state: &Pattern,
        budget: ExecutionBudget,
        run: ResultRun,
    ) -> Result<AdaptedExecution, ExecutionAdapterFailure> {
        self.check_profile(backend)?;
        let (inhabitation, rewrites) = with_definition(backend, |definition| {
            let inhabitation = Inhabitation::of(definition);
            match uninhabited_variable(definition, &inhabitation, state) {
                Ok(None) => Ok((inhabitation, rewrite_unique_ids(definition))),
                Ok(Some(variable)) => Err(ExecutionAdapterFailure::UninhabitedVariable(variable)),
                Err(error) => Err(ExecutionAdapterFailure::InvalidState(error)),
            }
        })?;
        let execution = self.result_once(backend, state, budget, run, &inhabitation, &rewrites)?;
        if run.modality == ResultModality::StateSet
            && !execution.timed_out
            && execution.leaves.iter().any(path_set_leaf)
        {
            let mut replaced = self.result_once(
                backend,
                state,
                budget,
                ResultRun {
                    modality: ResultModality::PathSet,
                    ..run
                },
                &inhabitation,
                &rewrites,
            )?;
            // Re-pin adoption A-1: the replacement keeps the run-level facts of the state set it
            // replaces, so nothing the discarded run noted is lost (a timed-out replacement keeps
            // none: it is a timeout).
            if !replaced.timed_out {
                replaced.facts = execution.facts.union(std::mem::take(&mut replaced.facts));
            }
            return Ok(replaced);
        }
        Ok(execution)
    }

    /// One result run under `run` exactly as k-rust answers it, without replacing a state set
    /// whose leaves the exclusions read by its path set (`execute_result` does that). For the
    /// modality differential (re-pin decision 3, finding A-01) and for tools; never a verdict's
    /// run.
    pub fn execute_once(
        &self,
        backend: &mut Backend,
        state: &Pattern,
        budget: ExecutionBudget,
        run: ResultRun,
    ) -> Result<AdaptedExecution, ExecutionAdapterFailure> {
        self.check_profile(backend)?;
        let (inhabitation, rewrites) = with_definition(backend, |definition| {
            let inhabitation = Inhabitation::of(definition);
            match uninhabited_variable(definition, &inhabitation, state) {
                Ok(None) => Ok((inhabitation, rewrite_unique_ids(definition))),
                Ok(Some(variable)) => Err(ExecutionAdapterFailure::UninhabitedVariable(variable)),
                Err(error) => Err(ExecutionAdapterFailure::InvalidState(error)),
            }
        })?;
        self.result_once(backend, state, budget, run, &inhabitation, &rewrites)
    }

    fn result_once(
        &self,
        backend: &mut Backend,
        state: &Pattern,
        budget: ExecutionBudget,
        run: ResultRun,
        inhabitation: &Inhabitation,
        rewrites: &BTreeSet<String>,
    ) -> Result<AdaptedExecution, ExecutionAdapterFailure> {
        let (result, timed_out) =
            execute_with_watchdog(backend, state.clone(), budget, run, Backend::execute)?;
        let feasibility = if timed_out {
            vec![LeafFeasibility::Unknown; result.leaves.len()]
        } else {
            backend.with_solver(None, |definition, solver| {
                Ok::<_, ExecutionAdapterFailure>(
                    result
                        .leaves
                        .iter()
                        .map(|leaf| leaf_feasibility(definition, solver, inhabitation, &leaf.state))
                        .collect(),
                )
            })?
        };
        Self::adapt(
            result,
            timed_out,
            &budget,
            run.max_work,
            feasibility,
            rewrites,
        )
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
        let (result, timed_out) =
            execute_with_watchdog(backend, encoded, budget, STEPPED, |backend, request| {
                backend.execute_observed(ObservedRequest {
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
                adapted: Self::adapt(result, true, &budget, None, feasibility, &rewrites)?,
                states: Vec::new(),
            }));
        }
        let states = match result
            .leaves
            .iter()
            .map(step_states)
            .collect::<Result<Vec<_>, _>>()
        {
            Ok(states) => states,
            Err(failure) => return Ok(Err(failure)),
        };
        let feasibility = backend.with_solver(None, |definition, solver| {
            Ok::<_, ExecutionAdapterFailure>(
                result
                    .leaves
                    .iter()
                    .map(|leaf| leaf_feasibility(definition, solver, &inhabitation, &leaf.state))
                    .collect(),
            )
        })?;
        // Step observations are consumed only by the configuration sequence.
        let mut result = result;
        for leaf in &mut result.leaves {
            leaf.observations.clear();
        }
        let adapted = Self::adapt(result, false, &budget, None, feasibility, &rewrites)?;
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
        let (result, timed_out) =
            execute_with_watchdog(backend, encoded, budget, STEPPED, Backend::execute)?;
        let mut result = result;
        // A timed-out run has no facts: it is a timeout before it is anything else.
        let facts = if timed_out {
            RunFacts::default()
        } else {
            RunFacts::take(&mut result)
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

    fn adapt(
        result: ExecutionResult,
        timed_out: bool,
        budget: &ExecutionBudget,
        max_work: Option<u64>,
        feasibility: Vec<LeafFeasibility>,
        rewrites: &BTreeSet<String>,
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
            RunFacts::take(&mut result)
        };
        let leaves = result
            .leaves
            .into_iter()
            .zip(feasibility)
            .map(|(leaf, feasibility)| {
                let halt = HaltClass::from_output(leaf.reason);
                if !halt.admitted_by(budget, max_work) {
                    return Err(ExecutionAdapterFailure::ContractViolation(halt));
                }
                Ok(AdaptedLeaf {
                    halt,
                    feasibility,
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
    /// the result carries any, has no rewrite rules named (`applied_rewrites` is empty). For
    /// tests and tools that hold a result k-rust returned; a value built here is no more
    /// evidence than the result it is built from.
    pub fn adapt_result(
        result: ExecutionResult,
        timed_out: bool,
        budget: &ExecutionBudget,
        feasibility: Vec<LeafFeasibility>,
    ) -> Result<AdaptedExecution, ExecutionAdapterFailure> {
        Self::adapt_bounded_result(result, timed_out, budget, None, feasibility)
    }

    /// [`Self::adapt_result`] of a result whose request set `max_work`, so a `work-bound` leaf is
    /// admitted exactly when `max_work` is set ([`HaltClass::admitted_by`]; re-pin L1-2: tests of
    /// the one-sided kill hold a work-bound result).
    pub fn adapt_bounded_result(
        result: ExecutionResult,
        timed_out: bool,
        budget: &ExecutionBudget,
        max_work: Option<u64>,
        feasibility: Vec<LeafFeasibility>,
    ) -> Result<AdaptedExecution, ExecutionAdapterFailure> {
        Self::adapt(
            result,
            timed_out,
            budget,
            max_work,
            feasibility,
            &BTreeSet::new(),
        )
    }
}

fn execute_with_watchdog(
    backend: &mut Backend,
    state: Pattern,
    budget: ExecutionBudget,
    run: ResultRun,
    execute: impl FnOnce(&mut Backend, ExecuteRequest) -> Result<ExecutionResult, BackendError>,
) -> Result<(ExecutionResult, bool), ExecutionAdapterFailure> {
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
    let outcome = token.scope(|| execute(backend, request(state, budget, run)));
    // Stop the watchdog, then read whether it fired before the run ended.
    drop(done);
    watchdog.join().expect("watchdog thread does not panic");
    let (result, timed_out) = settle(outcome, fired.load(Ordering::Acquire), run.modality)?;
    assert_eq!(result.modality, run.modality.output());
    Ok((result, timed_out))
}

/// How a run ended (re-pin finding A-04/A-05, answers section 2.3): a timeout exactly when kink's
/// watchdog `fired`, or k-rust answers an error whose stop cause is `Cancelled` (every request
/// sets `cancelled_result: error`, so this is how k-rust answers a cancellation, and the
/// portable build answers a token already cancelled at entry that way, section_2_2_summary
/// (5)), or an `Ok` result with a `Cancelled` leaf (which the request excludes; the adapter then
/// refuses the leaf, [`HaltClass::admitted_by`]). A timed-out run publishes no completed state:
/// after an error it has no leaves, and its leaves are never decoded. Every other error, a stack
/// or deadline stop included, is an infrastructure failure, never a timeout.
fn settle(
    outcome: Result<ExecutionResult, BackendError>,
    fired: bool,
    modality: ResultModality,
) -> Result<(ExecutionResult, bool), ExecutionAdapterFailure> {
    match outcome {
        Ok(result) => {
            let cancelled = result
                .leaves
                .iter()
                .any(|leaf| leaf.reason == HaltReasonOutput::Cancelled);
            Ok((result, fired || cancelled))
        }
        Err(error) if fired || matches!(error.stop_cause(), Some(StopCause::Cancelled)) => Ok((
            ExecutionResult {
                modality: modality.output(),
                leaves: Vec::new(),
                effects: Vec::new(),
                discarded: Vec::new(),
                coverage: None,
                work: 0,
                expanded: 0,
                stack_stops: 0,
                // A timed-out run publishes nothing (k-rust 58720d2e5 added these lists,
                // KINK-19/1, KINK-17/1, KINK-18/2); its leaves are never decoded.
                smt_unknowns: 0,
                implementation_chosen_values: Vec::new(),
                contradicted_claims: Vec::new(),
                allowance_refusals: Vec::new(),
                unsupported_hooks: Vec::new(),
            },
            true,
        )),
        Err(error) => Err(ExecutionAdapterFailure::Backend(error.to_string())),
    }
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

/// Decode only committed rewrites; every reported id must equal its branch entry.
fn step_states(leaf: &ExecutionLeaf) -> Result<Vec<Pattern>, StepRunFailure> {
    let mut reported = Vec::new();
    let mut states = Vec::new();
    for event in &leaf.observations {
        if let ObservationEventOutput::Transition {
            id, class, before, ..
        } = event
        {
            match class {
                TransitionClassOutput::Rewrite => {
                    reported.push(id.clone());
                    states.push(
                        codec::from_value(before)
                            .map_err(|error| StepRunFailure::Decode(error.to_string()))?,
                    );
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
    states.push(
        codec::from_value(&leaf.state)
            .map_err(|error| StepRunFailure::Decode(error.to_string()))?,
    );
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

#[cfg(test)]
mod tests {
    use super::*;

    use k_rust::kore::ast::Symbol;

    #[test]
    fn stepped_run_failure_is_reported_as_step_run_failure() {
        let state = codec::to_value(&Pattern::Application {
            symbol: Symbol {
                name: "Lblunit".into(),
                sort_parameters: Vec::new(),
            },
            arguments: Vec::new(),
        })
        .expect("encode state");
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
        let mut leaf = ExecutionLeaf {
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
        };
        assert_eq!(step_states(&leaf), Err(StepRunFailure::Unobservable));
        leaf.observations = vec![event(TransitionClassOutput::Rewrite, state.clone())];
        leaf.branch[0].target = "other".into();
        assert_eq!(step_states(&leaf), Err(StepRunFailure::Unobservable));
        leaf.branch[0] = id.clone();
        leaf.observations = vec![event(
            TransitionClassOutput::Rewrite,
            serde_json::Value::Null,
        )];
        assert!(matches!(step_states(&leaf), Err(StepRunFailure::Decode(_))));
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
        let cancelled =
            token.scope(|| backend.execute(request(state.clone(), budget, ResultRun::default())));
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
        let failed = backend.execute(request(unknown.clone(), budget, ResultRun::default()));
        let error = failed.as_ref().expect_err("an unknown symbol fails");
        assert_eq!(error.stop_cause(), None);
        assert!(matches!(
            settle(failed, false, ResultModality::StateSet),
            Err(ExecutionAdapterFailure::Backend(_))
        ));
        assert!(
            settle(
                backend.execute(request(unknown, budget, ResultRun::default())),
                true,
                ResultModality::StateSet
            )
            .is_ok_and(|(_, t)| t)
        );
        // An `Ok` result: a timeout exactly when the watchdog fired or a leaf is `Cancelled`.
        let complete = backend
            .execute(request(state.clone(), budget, ResultRun::default()))
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
                vec![LeafFeasibility::Unknown]
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
            STEPPED,
            ResultRun {
                modality: ResultModality::StateSet,
                max_work: Some(11),
            },
        ] {
            let request = request(state.clone(), budget, run);
            assert_eq!(request.result_modality, run.modality.output());
            assert_eq!(request.max_work, run.max_work);
            assert!(request.collect_coverage);
            assert!(!request.trace);
            assert_eq!(request.cancelled_result, CancelledResultOutput::Error);
            assert_eq!(request.step_timeout_ms, None);
            assert!(!request.moving_average_timeout);
            assert_eq!(request.max_depth, Some(3));
            assert_eq!(request.max_simplification_iterations, 7);
        }
        assert_eq!(ResultRun::default().modality, ResultModality::StateSet);
        assert_eq!(ResultRun::default().max_work, None);
        assert_eq!(STEPPED.modality, ResultModality::PathSet);
        assert_eq!(STEPPED.max_work, None);
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
        let state = codec::to_value(&Pattern::Application {
            symbol: Symbol {
                name: "Lblunit".into(),
                sort_parameters: Vec::new(),
            },
            arguments: Vec::new(),
        })
        .expect("encode state");
        let leaf = |reason| ExecutionLeaf {
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
        };
        let result = |leaves: Vec<ExecutionLeaf>| ExecutionResult {
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
                HaltClass::WorkBound.admitted_by(&budget, Some(1)),
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
                            None,
                            feasibility.clone(),
                            &BTreeSet::new(),
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
                        Some(1),
                        feasibility.clone(),
                        &BTreeSet::new(),
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
