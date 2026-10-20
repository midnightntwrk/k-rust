//! Per-case execution and classification: the execute request, clean leaves, natural ends,
//! outcome classes and the determinism counters (ARCHITECTURE 5). Owner: FZ-04.
//!
//! Every case runs through the public `Backend::execute` (ARCHITECTURE 5.1). Leaf patterns
//! (the normal-termination pattern, a `pattern` target) are judged with the leaf matcher
//! `krun --pattern` uses, `k_rust_backend::search::match_disjunction_with_solver` under
//! `Backend::with_solver_over` in execution mode, and a match counts only with empty
//! constraints. `Backend::match_patterns` is the proof route and is never used to judge.

use k_rust::{
    backend::{Backend, CancellationToken, ExecuteRequest, HaltReasonOutput, RunCoverageOutput},
    kore::ast::Pattern as KorePattern,
};
use serde::{Deserialize, Serialize};

use crate::{
    assemble::ProgramAssembly,
    error::CampaignError,
    report::{EngineDefect, LoadRecord},
    spec::{CaseOptions, CompiledDefinition, PathMode},
};

/// The one class every case receives (GOAL.md "Results", amended by decision D10;
/// ARCHITECTURE 5.3).
///
/// When a result has several leaves, the class follows this precedence (ARCHITECTURE 5.3,
/// R-6): `hit` if some clean leaf reaches the target; otherwise `unsupported` if any leaf is
/// (or the run returned `Err`, or a target-reaching leaf is not clean); otherwise `timeout`,
/// then `work-bound`, then `depth-bound`; otherwise `stuck` if any clean leaf is an abnormal
/// stop; otherwise `miss`. `rejected` is decided before execution; `baseline-incomplete` is
/// decided by the differential judge before the mutant's leaves are looked at.
/// `reached-unfinished` and `undefined` are placed by FZ-04 (see `workers/interfaces.md`, open
/// question 1); the declaration order of this enum is not the precedence.
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
    /// Under `run-to-completion`, the target was reached but the run did not end naturally.
    ReachedUnfinished,
    /// A `depth-bound` or `breadth-bound` halt.
    DepthBound,
    /// A `work-bound` halt; deterministic, distinct from timeouts.
    WorkBound,
    /// A `timeout` or `cancelled` halt, or the per-case safety limit.
    Timeout,
    /// A `trivial` halt: an undefined step.
    Undefined,
    /// `unsupported-hook`, `simplification-error`, `indeterminate`, `vacuous` after depth 0, an
    /// `Err` result, or a target-reaching leaf that is not clean.
    Unsupported,
    /// A hole value violates its sort or constraints, does not round-trip through the program's
    /// syntax, or the backend refuses the initial state (`vacuous` at depth 0).
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
}

/// Why a leaf is not clean (ARCHITECTURE 5.2). A leaf is clean when the list is empty.
#[derive(Clone, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum UncleanReason {
    /// Its halt is neither `stuck` nor `terminal` for the target's own stop rule.
    Halt,
    /// It has constraints or variables: not a decided state.
    Undecided,
    /// Its internalized term is not `ceil_free`: an application of a partial function or a
    /// malformed map or set (T-1).
    NotCeilFree,
    /// Its diagnostics carry an implementation-chosen value.
    ImplementationChosenValue,
    /// Its diagnostics carry a contradicted claim.
    ContradictedClaim,
    /// Its diagnostics record simplification-iteration exhaustion.
    IterationExhaustion,
    /// The run has nonzero `stackStops`.
    StackStops,
    /// The run has nonzero `smtUnknowns`.
    SmtUnknowns,
    /// The run observed an allowance refusal (`observedIn: run`).
    AllowanceRefusal,
    /// The leaf could not be internalized in its definition; the message.
    Internalization(String),
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
    /// Nonzero `stackStops`, or stack stops during the definition's load.
    StackStops,
    /// An allowance refusal observed in the run.
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
    /// The leaf's configuration as KORE, after k-rust's normalization.
    pub state: KorePattern,
    /// Why the leaf is not clean; empty for a clean leaf.
    pub unclean: Vec<UncleanReason>,
    /// The leaf is a clean `stuck` leaf that matches the normal-termination pattern with empty
    /// constraints.
    pub natural_end: bool,
    /// For each extra matcher passed to [`Executor::run`], in order: the leaf is clean and
    /// matches it with empty constraints. Not judged (all `false`) on an unclean leaf.
    pub matches: Vec<bool>,
    /// The unique ids of the `Rewrite` entries of the leaf's trace, in order; empty unless the
    /// request asked for traces.
    pub rewrites: Vec<String>,
    /// When the request asked for it: the leaf's internalized configuration consists only of
    /// constructor applications, injections, domain values and well-formed collections
    /// (differential condition 4, ARCHITECTURE 4.3, T-16).
    pub constructor_only: Option<bool>,
}

impl LeafReport {
    /// Whether the leaf is clean (ARCHITECTURE 5.2).
    #[must_use]
    pub fn is_clean(&self) -> bool {
        self.unclean.is_empty()
    }
}

/// The result of executing one case (ARCHITECTURE 5, 6.1): the leaves with their judgements,
/// the work, the coverage and the run-level facts.
#[derive(Clone, Debug)]
pub struct CaseResult {
    /// The leaves, in the backend's order; empty when [`Self::failure`] is set.
    pub leaves: Vec<LeafReport>,
    /// `ExecutionResult::work`, charged to `Budget::Work`.
    pub work: u64,
    /// The run's coverage (`applied`, `matched`), when collected.
    pub coverage: Option<RunCoverageOutput>,
    /// `ExecutionResult::stack_stops`.
    pub stack_stops: usize,
    /// `ExecutionResult::smt_unknowns`.
    pub smt_unknowns: usize,
    /// Allowance refusals the run observed (`observedIn: run`).
    pub run_allowance_refusals: usize,
    /// Records the definition's load observed (`observedIn: load`); they taint no leaf and are
    /// reported once per campaign (T-5).
    pub load_records: Vec<LoadRecord>,
    /// The per-case safety limit stopped the run.
    pub safety_limit_hit: bool,
    /// The message of an `Err` result of `Backend::execute`; the case is `unsupported`.
    pub failure: Option<String>,
}

impl CaseResult {
    /// The facts that put this case outside the determinism contract (ARCHITECTURE 5.4).
    #[must_use]
    pub fn determinism_breaks(&self) -> Vec<DeterminismBreak> {
        unimplemented!("FZ-04")
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
    /// Leaves carry [`LeafReport::constructor_only`] (the differential mutant side).
    pub(crate) constructor_only: bool,
    /// Override of the path mode (the differential baseline runs all paths).
    pub(crate) paths: Option<PathMode>,
}

/// The execute request every case of one definition uses, without its state
/// (ARCHITECTURE 5.1): `strategy` from the path mode, `result_modality: path-set`, the bounds,
/// `collect_coverage: true`, `trace` and `terminal_rules` only as the target needs, no step
/// timeouts.
#[derive(Clone, Debug)]
pub(crate) struct CaseRequestShape {
    request: ExecuteRequest,
}

impl CaseRequestShape {
    /// The shape for `options` and `needs`.
    pub(crate) fn new(options: &CaseOptions, needs: &TargetNeeds) -> Self {
        unimplemented!("FZ-04")
    }

    /// The request for one initial configuration.
    pub(crate) fn request(&self, state: KorePattern) -> ExecuteRequest {
        unimplemented!("FZ-04")
    }
}

/// A pattern prepared for leaf matching in one definition: `compile_search_pattern` over the
/// program grammar and the execution definition, then `prepare_backend_match_target`
/// (ARCHITECTURE 4.1, 5.2; `crates/k-rust/src/backend/execution.rs:1673-1686`). It holds
/// internal terms of one backend's definition, so it is used only with the [`Executor`] whose
/// backend prepared it.
pub(crate) struct LeafMatcher {
    _target: (),
}

impl LeafMatcher {
    /// Compile `pattern` (krun's `--pattern` surface syntax, `requires` allowed) for leaves of
    /// `executor`'s backend.
    ///
    /// # Errors
    ///
    /// The compiler's or backend's message.
    pub(crate) fn compile(
        executor: &mut Executor,
        definition: &CompiledDefinition,
        assembly: &ProgramAssembly,
        pattern: &str,
    ) -> Result<Self, String> {
        unimplemented!("FZ-04")
    }
}

/// One definition's backend and normal-termination matcher; runs and judges cases.
pub(crate) struct Executor {
    backend: Backend,
    normal_end: Option<LeafMatcher>,
}

impl Executor {
    /// Build the backend on `definition`'s route ([`crate::assemble::build_backend`]) and
    /// compile the normal-termination pattern of `options` (`<k> .K </k>` with the rest free
    /// when absent, which needs exactly one `<k>` cell; ARCHITECTURE 5.2, R-2).
    ///
    /// # Errors
    ///
    /// [`CampaignError::Definition`] when the backend cannot be built;
    /// [`CampaignError::NormalEndPattern`] when the pattern is missing or does not compile.
    pub(crate) fn new(
        definition: &CompiledDefinition,
        assembly: &ProgramAssembly,
        options: &CaseOptions,
    ) -> Result<Self, CampaignError> {
        unimplemented!("FZ-04")
    }

    /// The backend, for target resolution (`rule_catalog`) and pattern compilation.
    pub(crate) fn backend_mut(&mut self) -> &mut Backend {
        &mut self.backend
    }

    /// Execute `initial` with `shape` through `Backend::execute`, within `cancel`'s scope and
    /// the per-case safety limit, then judge every leaf: clean (ARCHITECTURE 5.2), natural end,
    /// and each of `matchers` (prepared by this executor). Load-time records go to
    /// [`CaseResult::load_records`], never onto leaves. An `Err` result becomes
    /// [`CaseResult::failure`].
    ///
    /// # Errors
    ///
    /// [`Abort`] for a failed solver prelude.
    pub(crate) fn run(
        &mut self,
        initial: &KorePattern,
        shape: &CaseRequestShape,
        matchers: &[&LeafMatcher],
        cancel: Option<&CancellationToken>,
    ) -> Result<CaseResult, Abort> {
        unimplemented!("FZ-04")
    }
}

/// Class `result` (ARCHITECTURE 5.3). `reached[i]` says whether leaf `i` reaches the target, as
/// the target judge decided ([`crate::target`]); `run_to_completion` additionally requires a
/// target-reaching clean leaf to be a natural end, and makes a reaching leaf that is not one
/// `reached-unfinished`. A `terminal` leaf is a hit candidate only because the target's rule is
/// the only stop rule (T-14).
///
/// # Errors
///
/// [`EngineDefect`] for a `branch` or `cut-point` halt, which the request never asks for, or a
/// `reached` of the wrong length.
pub(crate) fn classify(
    result: &CaseResult,
    reached: &[bool],
    run_to_completion: bool,
) -> Result<OutcomeClass, EngineDefect> {
    unimplemented!("FZ-04")
}
