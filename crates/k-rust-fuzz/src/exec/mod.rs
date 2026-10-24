//! Per-case execution and classification: the execute request, clean leaves, natural ends,
//! outcome classes and the determinism counters (ARCHITECTURE 5). Owner: FZ-04.
//!
//! Every case runs through the public `Backend::execute` (ARCHITECTURE 5.1). Leaf patterns
//! (the normal-termination pattern, a `pattern` target) are judged with the leaf matcher
//! `krun --pattern` uses, `k_rust_backend::search::match_disjunction_with_solver` under
//! `Backend::with_solver_over` in execution mode, and a match counts only with empty
//! constraints. `Backend::match_patterns` is the proof route and is never used to judge.
//!
//! The judgement of a leaf (`Executor::run`) and the class of a case (`classify`) are split
//! so that every target kind shares one precedence: the target's judge decides which leaves
//! reach it, and `classify` decides what that makes the case.

pub mod comparable;
pub mod reasons;
pub(crate) mod run;
#[cfg(test)]
mod tests;
#[cfg(not(target_arch = "wasm32"))]
mod watchdog;

use k_rust::{
    backend::{
        CancelledResultOutput, ConditionCollection, ExecuteRequest, ExecutionStrategy,
        HaltReasonOutput, ResultModalityOutput, RunCoverageOutput, StopCause,
    },
    kore::ast::Pattern as KorePattern,
};
use serde::{Deserialize, Serialize};

pub use comparable::{ComparableCondition, LeafDiagnostic};
pub use reasons::UnjudgedReason;
pub(crate) use run::{
    CompiledPattern, ConfigurationVerdict, Executor, LeafMatcher, NormalEnd, PatternCompiler,
    PlannedConfiguration,
};

use crate::{
    report::{EngineDefect, LoadRecord},
    spec::{CaseOptions, PathMode},
};

/// The `LoadRecord::kind` of a stop for lack of stack in the definition's load (its critical-pair
/// check or its discharge of rewrite-rule definedness), which puts every case of the definition
/// outside the determinism contract (ARCHITECTURE 5.4, `docs/compatibility.md`, "Determinism and
/// concurrency").
pub const LOAD_STACK_STOP: &str = "stack-stop";

/// The `LoadRecord::kind` of a `Bytes` result the memory allowance refused in the definition's
/// load. Like a load-time stack stop, it taints no leaf (T-5) but puts every case of the
/// definition outside the determinism contract, since the load's result depended on the host's
/// allowance (ARCHITECTURE 5.4).
pub const LOAD_ALLOWANCE_REFUSAL: &str = "allowance-refusal";

/// The one class every case receives (GOAL.md "Results", amended by decision D10;
/// ARCHITECTURE 5.3, amended by decision D13).
///
/// # The class of one leaf
///
/// A target's judge says which leaves reach the target (`classify`'s `reached`). A leaf is
/// *unclean by its halt* when [`UncleanReason::Halt`] is its only reason, and *unclean beyond its
/// halt* when it has any other reason (an implementation-chosen value, a contradicted claim,
/// iteration exhaustion or a simplification failure on the leaf, an undecided match, remaining
/// constraints or variables, a term that is not ceil-free, a failed internalization, or the run's
/// `stackStops`, `smtUnknowns` or allowance refusals). Then:
///
/// - a leaf unclean beyond its halt is `unsupported`, whether or not it reaches the target: such
///   a leaf may hide a reaching state, so `miss` or `stuck` would be unsound (D13);
/// - a clean leaf (`stuck`, or `terminal` on the target's own stop rule) that reaches the target
///   is a `hit` candidate, and under `run-to-completion` only if it is a natural end; when its
///   natural end cannot be judged ([`UncleanReason::NaturalEndUndecided`], which is not a
///   cleanliness defect) it is a `hit` candidate without `run-to-completion` and `unsupported`
///   with it;
/// - under `run-to-completion`, a reaching leaf that is clean in every respect except its halt,
///   where the halt is neither a natural end nor an unsupported halt (a clean abnormal stop, an
///   undefined step, or a cut: `depth-bound`, `breadth-bound`, `work-bound`, `timeout`,
///   `cancelled`), is `reached-unfinished`;
/// - any other reaching leaf is `unsupported` (a target-reaching leaf that is not clean: without
///   `run-to-completion` an undefined step or a cut run, and in every mode an unsupported or
///   `vacuous` halt);
/// - a leaf that does not reach the target takes its halt's class: `stuck` gives `miss` for a
///   natural end, `unsupported` when the natural end cannot be judged, and `stuck` otherwise; `trivial` gives `undefined`; `depth-bound` and
///   `breadth-bound` give `depth-bound`; `work-bound` gives `work-bound`; `timeout` and
///   `cancelled` give `timeout`; `indeterminate`, `unsupported-hook`, `simplification-error` and
///   `vacuous` give `unsupported`; `branch` and `cut-point`, which the request never asks for,
///   and a `terminal` leaf that does not reach the target, which only the target's rule can
///   cause, are engine defects.
///
/// # The class of a case
///
/// The case takes the first of these that some leaf has: `hit`, `unsupported`,
/// `reached-unfinished`, `timeout`, `work-bound`, `depth-bound`, `undefined`, `stuck`, `miss`.
/// This is ARCHITECTURE 5.3's order, where `reached-unfinished` applies only when no leaf is
/// `unsupported`. Further:
///
/// - a `hit` candidate in a case outside the determinism contract
///   ([`CaseResult::determinism_breaks`]) is never a hit: it counts as `timeout` when a clock
///   stopped part of the case, and as `unsupported` otherwise (a stack stop in the definition's
///   load);
/// - the per-case safety limit adds `timeout`;
/// - when the run noted an implementation-chosen value or a contradicted claim that no leaf
///   carries ([`CaseResult::run_facts_off_leaves`]), a case that would be `miss` or `stuck` is
///   `unsupported`: some path that vanished in k-rust's model may give a leaf, possibly a
///   reaching one, in another model (D16, review B3). A hit on a clean, unmarked leaf stays a
///   hit;
/// - a result whose every leaf is `vacuous` at depth 0, or that has no leaf, is `rejected`: the
///   backend refuses the initial state;
/// - an `Err` result is classed by its [`CaseFailure`]: a cancellation or step deadline is
///   `timeout`, a refused initial state is `rejected`, anything else is `unsupported`.
///
/// `rejected` for a hole value is decided before execution; `baseline-incomplete` is decided by
/// the differential judge before the mutant's leaves are looked at.
///
/// The declaration order of this enum is the report's key order, not the precedence.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum OutcomeClass {
    /// A clean leaf reaches the target and confirmation agrees; reported as a property failure
    /// for a negated property.
    Hit,
    /// The run ended naturally on every leaf without reaching the target.
    Miss,
    /// A clean leaf is an abnormal stop (stuck, but not a natural end), and no leaf reaches the
    /// target.
    Stuck,
    /// Under `run-to-completion`, the target was reached on a leaf that is clean except for its
    /// halt, which is neither a natural end nor an unsupported halt (an abnormal stop, an
    /// undefined step, a bound, a timeout or a cancellation); and no leaf is `unsupported`.
    ReachedUnfinished,
    /// A `depth-bound` or `breadth-bound` halt.
    DepthBound,
    /// A `work-bound` halt; deterministic, distinct from timeouts.
    WorkBound,
    /// A `timeout` or `cancelled` halt, a cancellation or step deadline that ended the run as an
    /// `Err`, or the per-case safety limit.
    Timeout,
    /// A `trivial` halt: an undefined step.
    Undefined,
    /// `unsupported-hook`, `simplification-error`, `indeterminate`, `vacuous` after depth 0, an
    /// `Err` result other than a clock stop or a refused state, a leaf unclean for a reason other
    /// than its halt, or a target-reaching leaf that is not clean (and not `reached-unfinished`).
    Unsupported,
    /// A hole value violates its sort or constraints, does not round-trip through the program's
    /// syntax, or the backend refuses the initial state (`vacuous` at depth 0, or an invalid
    /// state).
    Rejected,
    /// Differential only: the baseline's set of ends is incomplete (ARCHITECTURE 4.3).
    BaselineIncomplete,
}

impl OutcomeClass {
    /// Every class, in declaration order.
    pub const ALL: [Self; 11] = [
        Self::Hit,
        Self::Miss,
        Self::Stuck,
        Self::ReachedUnfinished,
        Self::DepthBound,
        Self::WorkBound,
        Self::Timeout,
        Self::Undefined,
        Self::Unsupported,
        Self::Rejected,
        Self::BaselineIncomplete,
    ];

    /// The class's report name (`"reached-unfinished"`, …).
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Self::Hit => "hit",
            Self::Miss => "miss",
            Self::Stuck => "stuck",
            Self::ReachedUnfinished => "reached-unfinished",
            Self::DepthBound => "depth-bound",
            Self::WorkBound => "work-bound",
            Self::Timeout => "timeout",
            Self::Undefined => "undefined",
            Self::Unsupported => "unsupported",
            Self::Rejected => "rejected",
            Self::BaselineIncomplete => "baseline-incomplete",
        }
    }

    /// The class's place in the precedence of a case with several leaves (ARCHITECTURE 5.3,
    /// D13): lower wins. `rejected` and `baseline-incomplete` are never chosen by precedence.
    fn precedence(self) -> u8 {
        match self {
            Self::Hit => 0,
            Self::Unsupported => 1,
            Self::ReachedUnfinished => 2,
            Self::Timeout => 3,
            Self::WorkBound => 4,
            Self::DepthBound => 5,
            Self::Undefined => 6,
            Self::Stuck => 7,
            Self::Miss => 8,
            Self::Rejected => 9,
            Self::BaselineIncomplete => 10,
        }
    }
}

/// Why a leaf is not clean (ARCHITECTURE 5.2). The list is sorted and holds each reason once. A
/// leaf is clean when it holds no reason but [`Self::NaturalEndUndecided`], which says only that
/// the natural end cannot be judged on the leaf.
#[derive(Clone, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum UncleanReason {
    /// Its halt is neither `stuck` nor `terminal` for the target's own stop rule.
    Halt,
    /// It has constraints or variables, or its path carries `undefined-initial-instances`: the
    /// initial configuration is defined only where obligations hold that the backend keeps apart
    /// from the constraints (`ExecutionState::defined_where`), so the leaf may denote nothing
    /// (D16, review B2). Not a decided state.
    Undecided,
    /// Its internalized term is not `ceil_free`: an application of a partial function, a
    /// term-level `\and` of two different sides, or a malformed map or set (T-1). The K label of
    /// the first partial function application found (in preorder), or `\and` when a conjunction
    /// is found first (`run::AND_NOTE`), when there is one.
    NotCeilFree(Option<String>),
    /// Its diagnostics carry an implementation-chosen value.
    ImplementationChosenValue,
    /// Its diagnostics carry a contradicted claim.
    ContradictedClaim,
    /// Its diagnostics record simplification-iteration exhaustion
    /// (`simplification-budget-exhausted`, `rule-condition-unsimplified`).
    IterationExhaustion,
    /// The run has nonzero `stackStops`.
    StackStops,
    /// The run has nonzero `smtUnknowns`.
    SmtUnknowns,
    /// The run observed an allowance refusal (`observedIn: run`).
    AllowanceRefusal,
    /// The run left an application unevaluated as an unsupported hook (`observedIn: run`;
    /// D21). An equation whose condition is over such a value is undecided, so the simplifier
    /// applies another equation of its priority group, and the leaf may rest on that choice with
    /// no mark (FZ-08 review 2, `steer.k`). A run-level fact, on every leaf of the run.
    UnsupportedHook,
    /// The leaf could not be internalized in its definition; the message.
    Internalization(String),
    /// Its diagnostics record a rule whose side conditions failed to simplify
    /// (`rule-condition-failed`): the rule may have been left unapplied for that failure rather
    /// than because its condition is false, as with iteration exhaustion.
    SimplificationFailure,
    /// A leaf pattern (the normal-termination pattern or a target's) could not be decided on the
    /// leaf: the matcher answered undecided or only under constraints, or its match holds in
    /// k-rust's execution mode but not as a consequence of the definition alone (it rests on a
    /// value the definition leaves to the implementation).
    UndecidedMatch,
    /// Not a cleanliness defect: whether this `stuck` leaf is a natural end cannot be judged.
    /// Either the default `<k> .K </k>` does not apply, because it is meaningful only for a
    /// configuration with exactly one `<k>` cell (ARCHITECTURE 5.2, R-2; the campaign must
    /// supply a pattern), or the normal-termination pattern's match is undecided on the leaf. It
    /// matters only where the natural end does: `run-to-completion`, and `miss` against `stuck`
    /// (FZ-05 review N6).
    NaturalEndUndecided,
}

/// Which normal end a campaign's classes rest on (ARCHITECTURE 5.2): what makes a clean
/// `stuck` leaf a natural end (`miss`, a run-to-completion hit, a differential end) rather than
/// an abnormal stop (`stuck`).
#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum NormalEndKind {
    /// The default for a configuration with one `<k>` cell, not under a multiplicity cell: the
    /// leaf matches `<k> .K </k>` with the rest of the configuration free.
    SingleK,
    /// The default for a configuration whose `<k>` cell lies under a cell of multiplicity `*`
    /// or `?` (threads): every `<k>` cell of the leaf holds `.K`, and a leaf with no `<k>` cell
    /// left (every thread finished and was removed) is a natural end too when the initial
    /// configuration had a `<k>` cell. A semantics that
    /// removes a thread on error, or leaves a result in a finished thread's `<k>`, needs its own
    /// pattern.
    EveryK,
    /// The campaign's normal-end pattern.
    Pattern,
}

/// A fact of a case that puts it outside the determinism contract (ARCHITECTURE 5.4). Such a
/// case is never a hit and is counted in the report.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum DeterminismBreak {
    /// A step timeout, a cancellation or the per-case safety limit.
    Clock,
    /// Nonzero `smtUnknowns`.
    SmtUnknowns,
    /// Nonzero `stackStops`, a stop for lack of stack that ended the run, or stack stops during
    /// the definition's load.
    StackStops,
    /// An allowance refusal observed in the run, or in the definition's load.
    AllowanceRefusal,
}

/// One leaf of a case's result with its clean-leaf and natural-end judgements
/// (ARCHITECTURE 5.2).
#[derive(Clone, Debug)]
pub struct LeafReport {
    /// The leaf's halt, as the backend reports it.
    pub halt: HaltReasonOutput,
    /// The leaf's depth (rewrite steps on its path).
    pub depth: u64,
    /// The leaf's configuration as KORE, after k-rust's normalization. For a `work-bound`,
    /// `timeout` or `cancelled` leaf it is the stopped state as taken from the worklist,
    /// unexpanded and unnormalised: not a reached configuration, so no target, observer or
    /// coverage attribution may treat it as reached (review 2, S1).
    pub state: KorePattern,
    /// Why the leaf is not clean. Sorted, each reason once; a clean leaf holds none but
    /// [`UncleanReason::NaturalEndUndecided`].
    pub unclean: Vec<UncleanReason>,
    /// The leaf is a clean `stuck` leaf that matches the normal-termination pattern with empty
    /// constraints.
    pub natural_end: bool,
    /// For each extra matcher passed to `Executor::run`, in order: the leaf matches it with
    /// empty constraints. Judged on every end leaf (`stuck`, `trivial` or `terminal`; a leaf cut
    /// by a bound is not a final state, D16) whose state can be decided (it internalizes, with no
    /// constraints and no variables), clean or not, so that a reaching leaf that is not clean is
    /// visible (D13). `false` on any other leaf, and on a leaf whose match was undecided
    /// ([`UncleanReason::UndecidedMatch`]).
    pub matches: Vec<bool>,
    /// The unique ids of the `Rewrite` entries of the leaf's trace whose step results exist, in
    /// order; empty unless the request asked for traces. For a `work-bound`, `timeout` or
    /// `cancelled` leaf the last entry is left out: it built the stopped, unnormalised state,
    /// which may normalize to `\bottom` (review 2, S1).
    pub rewrites: Vec<String>,
    /// When the request asked for it and the leaf is a decided end: the leaf's internalized
    /// configuration is data (`k_rust_backend::definition::BackendDefinition::is_data`): free
    /// constructors, injections, domain values, well-formed collections and irreducible
    /// applications of the definition's overload data heads, no member of a broken overload
    /// family, so that it denotes itself and differs from every other data term; in a
    /// differential pair, data in the other definition too (differential condition 4,
    /// ARCHITECTURE 4.3, T-16;
    /// the data-end requirement of rule and pattern targets, [`crate::Target::data_end`]).
    /// `None` otherwise.
    pub data_end: Option<bool>,
    /// The kinds of every diagnostic the leaf carries, and its `contradictedTotal`, sorted,
    /// each once, whether or not the clean-leaf rule counts them: kink makes any diagnosed leaf
    /// incomplete ([`comparable`], P7-ADDENDUM section 4, P1).
    pub diagnostics: Vec<LeafDiagnostic>,
    /// The leaf is a decided end (`stuck`, `trivial` or `terminal`, internalized with no
    /// constraint and no variable) whose term holds a term-level `\and` anywhere, which kink's
    /// query refuses even with equal sides ([`comparable::query_conditions`], Q4'); one of
    /// different sides also makes the leaf not ceil-free. `false` on every other leaf.
    pub term_conjunction: bool,
}

impl LeafReport {
    /// Whether the leaf is clean (ARCHITECTURE 5.2).
    #[must_use]
    pub fn is_clean(&self) -> bool {
        self.unclean
            .iter()
            .all(|reason| *reason == UncleanReason::NaturalEndUndecided)
    }

    /// Whether the leaf is unclean for a reason other than its halt (D13).
    #[must_use]
    pub fn unclean_beyond_halt(&self) -> bool {
        self.unclean.iter().any(|reason| {
            !matches!(
                reason,
                UncleanReason::Halt | UncleanReason::NaturalEndUndecided
            )
        })
    }

    /// Whether the leaf's natural end cannot be judged ([`UncleanReason::NaturalEndUndecided`]).
    #[must_use]
    pub fn natural_end_undecided(&self) -> bool {
        self.unclean.contains(&UncleanReason::NaturalEndUndecided)
    }
}

/// Why `Backend::execute`, or the judgement of its leaves, answered `Err` (FZ-01 review S8).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CaseFailure {
    /// The error's text.
    pub message: String,
    /// What kind of failure it is.
    pub cause: FailureCause,
}

impl CaseFailure {
    /// A failure that is neither a stop nor a refused state; the case is `unsupported`.
    #[must_use]
    pub fn other(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            cause: FailureCause::Other,
        }
    }
}

/// The kind of an `Err` result (FZ-01 review S8).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FailureCause {
    /// The operation stopped (`BackendError::stop_cause`): a cancellation or step deadline is
    /// `timeout` and a [`DeterminismBreak::Clock`]; a stop for lack of stack is `unsupported` and
    /// a [`DeterminismBreak::StackStops`]. A failed solver prelude never reaches a case: it
    /// aborts the campaign.
    Stop(StopCause),
    /// The backend refused the initial state (`invalid executable state`, or it could not be
    /// internalized): the case is `rejected`.
    StateRefused,
    /// Any other failure: the case is `unsupported`.
    Other,
}

/// The result of executing one case (ARCHITECTURE 5, 6.1): the leaves with their judgements,
/// the work, the coverage and the run-level facts.
#[derive(Clone, Debug)]
pub struct CaseResult {
    /// The leaves, in the backend's order; empty when [`Self::failure`] is set.
    pub leaves: Vec<LeafReport>,
    /// `ExecutionResult::work`, charged to `Budget::Work`; 0 for an `Err` result, which reports
    /// none.
    pub work: u64,
    /// The run's coverage (`applied`, `matched`), when collected.
    pub coverage: Option<RunCoverageOutput>,
    /// `ExecutionResult::stack_stops`.
    pub stack_stops: usize,
    /// `ExecutionResult::smt_unknowns`, plus the solver `unknown`s the leaf matching met in
    /// either evaluation mode, which depend on the clock as much as the run's do (review 2,
    /// NI-2).
    pub smt_unknowns: usize,
    /// Allowance refusals the run observed (`observedIn: run`).
    pub run_allowance_refusals: usize,
    /// Records the definition's load observed (`observedIn: load`, and [`LOAD_STACK_STOP`] for
    /// load-time stack stops); they taint no leaf and are reported once per campaign (T-5).
    pub load_records: Vec<LoadRecord>,
    /// The per-case safety limit stopped the run.
    pub safety_limit_hit: bool,
    /// Why `Backend::execute` or the judgement of its leaves answered `Err`; the leaves are then
    /// empty.
    pub failure: Option<CaseFailure>,
    /// The run noted an implementation-chosen value or a contradicted claim
    /// (`ExecutionResult::implementation_chosen_values`, the `observedIn: run` entries of
    /// `contradicted_claims`) that no leaf's diagnostics carry. That happens without `max_work`
    /// or `max_breadth` under all paths, when work that read a value or met a claim ended on no
    /// reported leaf (a candidate that vanished); in another model of the definition such work
    /// may give a leaf. So the leaves are not every end of every model: the case cannot be `miss`
    /// or `stuck` (`classify`), and a differential baseline with the flag is incomplete
    /// (D16, review B3).
    pub run_facts_off_leaves: bool,
}

impl CaseResult {
    /// The facts that put this case outside the determinism contract (ARCHITECTURE 5.4), sorted,
    /// each once.
    #[must_use]
    pub fn determinism_breaks(&self) -> Vec<DeterminismBreak> {
        let mut breaks = Vec::new();
        let stop = self
            .failure
            .as_ref()
            .and_then(|failure| match &failure.cause {
                FailureCause::Stop(cause) => Some(cause),
                FailureCause::StateRefused | FailureCause::Other => None,
            });
        if self.safety_limit_hit
            || matches!(stop, Some(StopCause::Cancelled | StopCause::Deadline(_)))
            || self.leaves.iter().any(|leaf| {
                matches!(
                    leaf.halt,
                    HaltReasonOutput::Cancelled | HaltReasonOutput::Timeout
                )
            })
        {
            breaks.push(DeterminismBreak::Clock);
        }
        if self.smt_unknowns > 0 {
            breaks.push(DeterminismBreak::SmtUnknowns);
        }
        if self.stack_stops > 0
            || matches!(stop, Some(StopCause::StackExhausted(_)))
            || self
                .load_records
                .iter()
                .any(|record| record.kind == LOAD_STACK_STOP)
        {
            breaks.push(DeterminismBreak::StackStops);
        }
        if self.run_allowance_refusals > 0
            || self
                .load_records
                .iter()
                .any(|record| record.kind == LOAD_ALLOWANCE_REFUSAL)
        {
            breaks.push(DeterminismBreak::AllowanceRefusal);
        }
        breaks
    }
}

/// A failure that ends the campaign rather than classing a case: a failed solver prelude,
/// which the backend would repeat for every case (ARCHITECTURE 5.3).
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Abort {
    /// Why.
    pub(crate) reason: String,
}

/// What a target needs from every execute request (ARCHITECTURE 5.1).
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct TargetNeeds {
    /// Leaves carry traces (a `fired` rule target).
    pub(crate) trace: bool,
    /// The request's terminal rules (a `fired` rule target without `run-to-completion`).
    pub(crate) terminal_rules: Vec<String>,
    /// Leaves carry [`LeafReport::data_end`] (both differential sides, and a rule or pattern
    /// target that requires a data end).
    pub(crate) data_end: bool,
    /// Override of the path mode (the differential baseline runs all paths).
    pub(crate) paths: Option<PathMode>,
    /// Ask for `result_modality: state-set` instead of `path-set` (both differential sides,
    /// ARCHITECTURE 4.3 as amended by FZ-DIFFEND): the set of final configurations is the same
    /// (`docs/compatibility.md`, "Search results"), without exploring the paths that converge.
    pub(crate) state_set: bool,
}

/// The execute request every case of one definition uses, without its state
/// (ARCHITECTURE 5.1): `strategy` from the path mode, `result_modality: path-set` (`state-set`
/// when the target asks for it, [`TargetNeeds::state_set`]), the bounds,
/// `collect_coverage: true`, `trace` and `terminal_rules` only as the target needs, no step
/// timeouts, `cancelledResult: partial`.
#[derive(Clone, Debug)]
pub(crate) struct CaseRequestShape {
    request: ExecuteRequest,
    data_end: bool,
}

impl CaseRequestShape {
    /// The shape for `options` and `needs`.
    pub(crate) fn new(options: &CaseOptions, needs: &TargetNeeds) -> Self {
        let placeholder = k_rust::kore::parser::parse_pattern(r"\top{SortGeneratedTopCell{}}()")
            .expect("the placeholder state is a KORE pattern");
        let strategy = match needs.paths.unwrap_or(options.paths) {
            PathMode::OnePath => ExecutionStrategy::Any,
            PathMode::AllPaths => ExecutionStrategy::All,
        };
        let request = ExecuteRequest {
            max_depth: options.max_depth,
            max_work: options.effective_max_work(),
            max_breadth: None,
            max_simplification_iterations: options.max_simplification_iterations,
            strategy,
            stop_at_branch: false,
            cut_point_rules: Vec::new(),
            terminal_rules: needs.terminal_rules.clone(),
            step_timeout_ms: None,
            moving_average_timeout: false,
            assume_state_defined: false,
            result_modality: if needs.state_set {
                ResultModalityOutput::StateSet
            } else {
                ResultModalityOutput::PathSet
            },
            collect_coverage: true,
            collect_offered: false,
            trace: needs.trace,
            cancelled_result: CancelledResultOutput::Partial,
            ..ExecuteRequest::new(placeholder)
        };
        Self {
            request,
            data_end: needs.data_end,
        }
    }

    /// This shape, with the request also recording the condition entries of `rules`
    /// (`collectConditions` with the default caps); `collect_coverage` is already set.
    pub(crate) fn with_conditions(&self, rules: Vec<String>) -> Self {
        let mut shape = self.clone();
        shape.request.collect_conditions = Some(ConditionCollection::new(rules));
        shape
    }

    /// This shape, with the request also counting how many times the run applied each rule
    /// (`collectCounts`); `collect_coverage` is already set.
    pub(crate) fn with_counts(&self) -> Self {
        let mut shape = self.clone();
        shape.request.collect_counts = true;
        shape
    }

    /// The request for one initial configuration.
    pub(crate) fn request(&self, state: KorePattern) -> ExecuteRequest {
        ExecuteRequest {
            state,
            ..self.request.clone()
        }
    }

    /// Whether the request explores every path (strategy `all`).
    pub(crate) fn all_paths(&self) -> bool {
        matches!(self.request.strategy, ExecutionStrategy::All)
    }

    /// Whether the request names terminal rules, so that a `terminal` halt is the target's
    /// own stop.
    pub(crate) fn has_terminal_rules(&self) -> bool {
        !self.request.terminal_rules.is_empty()
    }

    /// This shape for the program's own run of every path (`crate::target::Target::comparable`):
    /// strategy `all`, a path set, the same bounds and options, the data judgement (P3), and
    /// nothing the target asked for (no terminal rule, no trace, no condition entries, no
    /// counts). A campaign that bounds only the depth sets no work bound on its cases; this run
    /// gets [`crate::spec::DEFAULT_MAX_WORK`] then, so that it explores every path of a
    /// nondeterministic program within a bounded work and not to the depth bound alone (INT9
    /// review S2). A bound the run meets makes it not comparable, never a hit.
    pub(crate) fn every_path(&self) -> Self {
        let mut shape = self.clone();
        shape.request.strategy = ExecutionStrategy::All;
        shape.request.result_modality = ResultModalityOutput::PathSet;
        shape.request.max_work = shape
            .request
            .max_work
            .or(Some(crate::spec::DEFAULT_MAX_WORK));
        shape.request.terminal_rules = Vec::new();
        shape.request.trace = false;
        shape.request.collect_conditions = None;
        shape.request.collect_counts = false;
        shape.data_end = true;
        shape
    }
}

/// Whether a leaf with `halt` holds the stopped, unnormalised state the worklist held rather
/// than a reached configuration: `work-bound`, `timeout` and `cancelled` (review 2, S1). A
/// judge may mark such a leaf reaching only from its [`LeafReport::rewrites`] ([`classify`]).
pub(crate) fn stopped_state(halt: HaltReasonOutput) -> bool {
    matches!(
        halt,
        HaltReasonOutput::WorkBound | HaltReasonOutput::Timeout | HaltReasonOutput::Cancelled
    )
}

/// Class `result` (ARCHITECTURE 5.3, D13; the rules are in the [`OutcomeClass`] rustdoc).
///
/// `reached[i]` says whether leaf `i` reaches the target, as the target judge decided
/// ([`crate::target`]): per leaf for leaf-judged targets (traces, terminal halts, pattern
/// matches), and for the run-level coverage modes the judge marks the leaves that may carry the
/// run's fact (with several leaves, every leaf only when every leaf could carry a hit; D13).
/// `run_to_completion` additionally requires a target-reaching clean leaf to be a natural end,
/// and makes a reaching leaf that is cut, undefined or an abnormal stop `reached-unfinished`.
///
/// Contract on `reached` for `work-bound`, `timeout` and `cancelled` leaves (review 2, S1): their
/// state is the stopped, unnormalised state, not a reached configuration. A judge may mark such
/// a leaf reaching only from its [`LeafReport::rewrites`], which leave out the last step's
/// entry; a reach attributed from run coverage or from an observer that read the stopped state
/// must not be marked on it. Such a leaf then takes its halt's class (`work-bound`, `timeout`)
/// instead of `reached-unfinished`. A `terminal`
/// leaf is a hit candidate only because the target's rule is the only stop rule (T-14).
///
/// # Errors
///
/// [`EngineDefect`] for a `branch` or `cut-point` halt, which the request never asks for, a
/// `terminal` leaf that does not reach the target, or a `reached` of the wrong length.
pub(crate) fn classify(
    result: &CaseResult,
    reached: &[bool],
    run_to_completion: bool,
) -> Result<OutcomeClass, EngineDefect> {
    classify_explained(result, reached, run_to_completion).map(|(class, _)| class)
}

/// [`classify`], with the reason of an `unsupported` class ([`reasons`]): `Some` exactly when the
/// class is `unsupported`. Of the reasons of the leaves that are `unsupported` (or of the fact
/// that lifts the case to `unsupported`), the first in [`UnjudgedReason`]'s order.
///
/// # Errors
///
/// As [`classify`].
pub(crate) fn classify_explained(
    result: &CaseResult,
    reached: &[bool],
    run_to_completion: bool,
) -> Result<(OutcomeClass, Option<UnjudgedReason>), EngineDefect> {
    classify_ends_explained(result, reached, run_to_completion, false)
}

/// [`classify_explained`], where under `run_to_completion` and `data_end` a reaching natural end
/// is a hit only when its configuration is data ([`LeafReport::data_end`]; a rule or pattern
/// target's [`crate::Target::data_end`]); a reaching natural end that is not data is
/// `unsupported`, with the reason [`UnjudgedReason::ReachedEndNotData`], as the differential
/// judge classes a mutant end it cannot compare.
///
/// # Errors
///
/// As [`classify`].
pub(crate) fn classify_ends_explained(
    result: &CaseResult,
    reached: &[bool],
    run_to_completion: bool,
    data_end: bool,
) -> Result<(OutcomeClass, Option<UnjudgedReason>), EngineDefect> {
    if let Some(failure) = &result.failure {
        let class = failure_class(result, failure);
        return Ok((
            class,
            (class == OutcomeClass::Unsupported).then(|| UnjudgedReason::of_failure(failure)),
        ));
    }
    if reached.len() != result.leaves.len() {
        return Err(defect(format!(
            "{} reach judgements for {} leaves",
            reached.len(),
            result.leaves.len()
        )));
    }
    if result
        .leaves
        .iter()
        .all(|leaf| leaf.halt == HaltReasonOutput::Vacuous && leaf.depth == 0)
    {
        // Also a result with no leaf: the initial state has no instance.
        return Ok((OutcomeClass::Rejected, None));
    }
    let breaks = result.determinism_breaks();
    let mut best = None::<OutcomeClass>;
    let mut consider = |class: OutcomeClass| {
        if best.is_none_or(|current| class.precedence() < current.precedence()) {
            best = Some(class);
        }
    };
    if result.safety_limit_hit {
        consider(OutcomeClass::Timeout);
    }
    let mut reasons = Vec::new();
    for (index, (leaf, reached)) in result.leaves.iter().zip(reached).enumerate() {
        let class = leaf_class(leaf, *reached, run_to_completion)
            .map_err(|description| defect(format!("leaf {index}: {description}")))?;
        let class = if class == OutcomeClass::Hit
            && run_to_completion
            && data_end
            && leaf.data_end != Some(true)
        {
            // The demotion's own reason: the leaf is clean, so `leaf_reason` would name its
            // natural end, which is decided.
            reasons.push(UnjudgedReason::ReachedEndNotData);
            consider(OutcomeClass::Unsupported);
            continue;
        } else {
            class
        };
        let class = if class == OutcomeClass::Hit && !breaks.is_empty() {
            if breaks.contains(&DeterminismBreak::Clock) {
                OutcomeClass::Timeout
            } else {
                reasons.extend(breaks.iter().copied().map(UnjudgedReason::of_break));
                OutcomeClass::Unsupported
            }
        } else {
            if class == OutcomeClass::Unsupported {
                reasons.push(leaf_reason(leaf, *reached));
            }
            class
        };
        consider(class);
    }
    let best = best.expect("a result with a leaf has a class");
    if result.run_facts_off_leaves && matches!(best, OutcomeClass::Miss | OutcomeClass::Stuck) {
        return Ok((
            OutcomeClass::Unsupported,
            Some(UnjudgedReason::RunFactOffLeaves),
        ));
    }
    let reason = (best == OutcomeClass::Unsupported).then(|| {
        reasons
            .into_iter()
            .min()
            .unwrap_or(UnjudgedReason::EngineDefect)
    });
    Ok((best, reason))
}

/// Why a leaf whose class is `unsupported` is so (the [`OutcomeClass`] rustdoc, "The class of
/// one leaf"): a reason beyond its halt; for a clean leaf, its undecided natural end; for a
/// leaf unclean by its halt alone, that halt, or, when it reaches the target, that the target
/// was reached on no end.
fn leaf_reason(leaf: &LeafReport, reached: bool) -> UnjudgedReason {
    if let Some(reason) = reasons::beyond_halt(leaf) {
        return reason;
    }
    if leaf.is_clean() {
        return UnjudgedReason::NaturalEndUndecided;
    }
    match UnjudgedReason::of_halt(leaf.halt) {
        None if reached && leaf.halt == HaltReasonOutput::Trivial => {
            UnjudgedReason::ReachedUndefinedStep
        }
        Some(
            UnjudgedReason::WorkBound
            | UnjudgedReason::DepthBound
            | UnjudgedReason::Clock
            | UnjudgedReason::Cancelled,
        ) if reached => UnjudgedReason::ReachedCutPath,
        Some(reason) => reason,
        None => UnjudgedReason::EngineDefect,
    }
}

/// The class of an `Err` result (FZ-01 review S8).
fn failure_class(result: &CaseResult, failure: &CaseFailure) -> OutcomeClass {
    if result.safety_limit_hit {
        return OutcomeClass::Timeout;
    }
    match &failure.cause {
        FailureCause::Stop(StopCause::Cancelled | StopCause::Deadline(_)) => OutcomeClass::Timeout,
        FailureCause::StateRefused => OutcomeClass::Rejected,
        FailureCause::Stop(StopCause::StackExhausted(_) | StopCause::SolverPrelude(_))
        | FailureCause::Other => OutcomeClass::Unsupported,
    }
}

/// The class one leaf contributes (the [`OutcomeClass`] rustdoc, "The class of one leaf"); the
/// error is an engine defect's description.
#[deny(clippy::wildcard_enum_match_arm)]
fn leaf_class(
    leaf: &LeafReport,
    reached: bool,
    run_to_completion: bool,
) -> Result<OutcomeClass, &'static str> {
    use HaltReasonOutput as H;
    if matches!(leaf.halt, H::Branch | H::CutPoint) {
        return Err("a branch or cut-point halt, which the request never asks for");
    }
    if leaf.unclean_beyond_halt() {
        return Ok(OutcomeClass::Unsupported);
    }
    if leaf.is_clean() {
        // A `stuck` leaf, or a `terminal` one on the target's own stop rule.
        let undecided = leaf.natural_end_undecided();
        return if reached {
            Ok(if !run_to_completion {
                OutcomeClass::Hit
            } else if undecided {
                OutcomeClass::Unsupported
            } else if leaf.natural_end {
                OutcomeClass::Hit
            } else {
                OutcomeClass::ReachedUnfinished
            })
        } else if leaf.halt == H::Terminal {
            Err("a terminal leaf that does not reach the target, whose rule is the only stop rule")
        } else if undecided {
            Ok(OutcomeClass::Unsupported)
        } else if leaf.natural_end {
            Ok(OutcomeClass::Miss)
        } else {
            Ok(OutcomeClass::Stuck)
        };
    }
    // Unclean by its halt alone: a halt that is neither an end nor unsupported leaves the
    // reaching run unfinished.
    let unfinished = matches!(
        leaf.halt,
        H::DepthBound | H::BreadthBound | H::WorkBound | H::Timeout | H::Cancelled | H::Trivial
    );
    if reached {
        return Ok(if run_to_completion && unfinished {
            OutcomeClass::ReachedUnfinished
        } else {
            OutcomeClass::Unsupported
        });
    }
    match leaf.halt {
        H::Cancelled | H::Timeout => Ok(OutcomeClass::Timeout),
        H::WorkBound => Ok(OutcomeClass::WorkBound),
        H::DepthBound | H::BreadthBound => Ok(OutcomeClass::DepthBound),
        H::Trivial => Ok(OutcomeClass::Undefined),
        H::Vacuous | H::Indeterminate | H::UnsupportedHook | H::SimplificationError => {
            Ok(OutcomeClass::Unsupported)
        }
        H::Terminal => Err("a terminal halt in a request without terminal rules"),
        // A clean `stuck` leaf is decided above, and `stuck` is never unclean by its halt.
        H::Stuck => Err("a stuck leaf unclean by its halt"),
        H::Branch | H::CutPoint => Err("a branch or cut-point halt"),
    }
}

fn defect(description: String) -> EngineDefect {
    EngineDefect {
        case: None,
        description,
    }
}
