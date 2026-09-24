//! Observed, time-bounded execution through the public k-rust `execute` facade.
//!
//! k-rust merges execution leaves that reach equal final states without regard to their
//! branch identities or observations, so an explore-all leaf set is complete for final states
//! but not for traces: a merged branch's events are lost. The adapter therefore runs
//! `stop_at_branch` first. A ground initial state that ends in exactly one `stuck` leaf, with
//! no backend diagnostic and within the time budget, never branched: that one path is the
//! whole execution ([`ExecutionRoute::SinglePath`]). Otherwise it reruns exploring every
//! branch ([`ExecutionRoute::ExploreAll`]), whose traces are real but may be incomplete.
//!
//! Execution has no depth bound: a finite `max_depth` would let k-rust drop depth-bounded
//! leaves once another leaf is stuck. A watchdog cancels the run when the time budget expires
//! instead, and a run it cancelled is reported as timed out whatever its leaves say.

use std::{
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
        mpsc,
    },
    thread,
    time::Duration,
};

use k_rust::backend::{
    Backend, EffectOutput, ExecuteRequest, ExecutionResult, ExecutionStrategy, ObservedRequest,
};
use k_rust::kore::{ast::Pattern, codec};
use k_rust_backend::{cancellation::CancellationToken, diagnostic::BackendDiagnostic};

use crate::observation::{
    AdaptedBranch, InstalledObservationManifest, ObservationFailure, adapt_branch,
};

/// The closed halt reasons of an execution leaf, parsed from their exact k-rust spellings.
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
}

impl HaltClass {
    pub const ALL: [Self; 13] = [
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
    ];

    /// The `ExecutionLeaf.reason` spelling k-rust writes for this class.
    #[must_use]
    pub const fn spelling(self) -> &'static str {
        match self {
            Self::Stuck => "stuck",
            Self::Trivial => "trivial",
            Self::Vacuous => "vacuous",
            Self::Branch => "branch",
            Self::CutPoint => "cut-point",
            Self::TerminalRule => "terminal",
            Self::DepthBound => "depth-bound",
            Self::BreadthBound => "breadth-bound",
            Self::Indeterminate => "indeterminate",
            Self::UnsupportedHook => "unsupported-hook",
            Self::SimplificationError => "simplification-error",
            Self::Timeout => "timeout",
            Self::Cancelled => "cancelled",
        }
    }

    /// The class spelled exactly `reason`; any other string is `None`.
    #[must_use]
    pub fn parse(reason: &str) -> Option<Self> {
        Self::ALL
            .into_iter()
            .find(|class| class.spelling() == reason)
    }
}

/// How the reported leaves were obtained.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ExecutionRoute {
    /// One `stuck` leaf of a run that stopped at any branch: the complete execution.
    SinglePath,
    /// Every branch explored; converging branches may have been merged.
    ExploreAll,
}

/// Limits of one execution.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ExecutionBudget {
    /// Wall-clock budget for both runs together.
    pub time: Duration,
    /// Simplifier iterations per rewrite step. Exhaustion is a backend diagnostic.
    pub max_simplification_iterations: usize,
}

/// One execution leaf with its parsed halt class and adapted branch.
#[derive(Clone, Debug, PartialEq)]
pub struct AdaptedLeaf {
    pub halt: HaltClass,
    pub branch: AdaptedBranch,
}

/// The adapted leaves of one execution. Built only by [`ExecutionAdapter::execute`].
#[derive(Clone, Debug, PartialEq)]
pub struct AdaptedExecution {
    pub(crate) route: ExecutionRoute,
    pub(crate) leaves: Vec<AdaptedLeaf>,
    pub(crate) effects: Vec<EffectOutput>,
    pub(crate) diagnostics: Vec<BackendDiagnostic>,
    pub(crate) timed_out: bool,
}

impl AdaptedExecution {
    #[must_use]
    pub const fn route(&self) -> ExecutionRoute {
        self.route
    }

    #[must_use]
    pub fn leaves(&self) -> &[AdaptedLeaf] {
        &self.leaves
    }

    #[must_use]
    pub fn effects(&self) -> &[EffectOutput] {
        &self.effects
    }

    /// Backend diagnostics of the reported run. Any diagnostic makes the run incomplete.
    #[must_use]
    pub fn diagnostics(&self) -> &[BackendDiagnostic] {
        &self.diagnostics
    }

    /// The watchdog cancelled the run. Its leaf states must not be decoded: a cancelled run
    /// can leave an arbitrarily deep term.
    #[must_use]
    pub const fn timed_out(&self) -> bool {
        self.timed_out
    }
}

/// Execution adapter failure. No adapted execution is returned.
#[derive(Clone, Debug, PartialEq)]
pub enum ExecutionAdapterFailure {
    /// The backend was built with an SMT solver; only the no-Z3 profile is qualified.
    SolverProfileMismatch,
    InvalidState(String),
    Backend(String),
    UnknownHaltReason(String),
    /// An explore-all run without cut points or terminal rules stopped at a branch, a cut
    /// point or a terminal rule.
    ContractViolation(HaltClass),
    Observation(ObservationFailure),
}

impl From<ObservationFailure> for ExecutionAdapterFailure {
    fn from(value: ObservationFailure) -> Self {
        Self::Observation(value)
    }
}

/// Observed execution for one installed manifest.
#[derive(Clone, Debug, PartialEq)]
pub struct ExecutionAdapter {
    manifest: InstalledObservationManifest,
}

impl ExecutionAdapter {
    #[must_use]
    pub const fn new(manifest: InstalledObservationManifest) -> Self {
        Self { manifest }
    }

    #[must_use]
    pub const fn manifest(&self) -> &InstalledObservationManifest {
        &self.manifest
    }

    /// Executes `state` from the backend's default module; see the module documentation for
    /// the two routes.
    pub fn execute(
        &self,
        backend: &mut Backend,
        state: &Pattern,
        budget: ExecutionBudget,
    ) -> Result<AdaptedExecution, ExecutionAdapterFailure> {
        if backend.capabilities().smt {
            return Err(ExecutionAdapterFailure::SolverProfileMismatch);
        }
        let encoded = codec::to_value(state)
            .map_err(|error| ExecutionAdapterFailure::InvalidState(error.to_string()))?;
        let ground = state.free_variables().is_empty();
        let token = CancellationToken::new();
        let fired = Arc::new(AtomicBool::new(false));
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
        let run = |backend: &mut Backend, stop_at_branch: bool| {
            let request = ExecuteRequest {
                state: encoded.clone(),
                max_depth: None,
                max_breadth: None,
                max_simplification_iterations: budget.max_simplification_iterations,
                strategy: ExecutionStrategy::All,
                stop_at_branch,
                cut_point_rules: Vec::new(),
                terminal_rules: Vec::new(),
                step_timeout_ms: None,
                ..ExecuteRequest::default()
            };
            let (result, diagnostics) = k_rust_backend::diagnostic::collect(|| {
                token.scope(|| {
                    backend.execute_observed(ObservedRequest {
                        request,
                        rules: Some(self.manifest.backend_rule_ids()),
                    })
                })
            });
            result
                .map(|result| (result, diagnostics))
                .map_err(|error| ExecutionAdapterFailure::Backend(error.to_string()))
        };
        let outcome: Result<_, ExecutionAdapterFailure> = (|| {
            let (first, diagnostics) = run(backend, true)?;
            let single_path = ground
                && diagnostics.is_empty()
                && !fired.load(Ordering::Acquire)
                && matches!(first.leaves.as_slice(), [leaf] if leaf.reason == HaltClass::Stuck.spelling());
            if single_path {
                return Ok((ExecutionRoute::SinglePath, first, diagnostics));
            }
            let (all, diagnostics) = run(backend, false)?;
            Ok((ExecutionRoute::ExploreAll, all, diagnostics))
        })();
        // Stop the watchdog, then read whether it fired before the run ended.
        drop(done);
        watchdog.join().expect("watchdog thread does not panic");
        let (route, result, diagnostics) = outcome?;
        let timed_out = fired.load(Ordering::Acquire);
        self.adapt(route, result, diagnostics, timed_out)
    }

    fn adapt(
        &self,
        route: ExecutionRoute,
        result: ExecutionResult,
        diagnostics: Vec<BackendDiagnostic>,
        timed_out: bool,
    ) -> Result<AdaptedExecution, ExecutionAdapterFailure> {
        let leaves = result
            .leaves
            .into_iter()
            .map(|leaf| {
                let halt = HaltClass::parse(&leaf.reason).ok_or_else(|| {
                    ExecutionAdapterFailure::UnknownHaltReason(leaf.reason.clone())
                })?;
                if route == ExecutionRoute::ExploreAll
                    && matches!(
                        halt,
                        HaltClass::Branch | HaltClass::CutPoint | HaltClass::TerminalRule
                    )
                {
                    return Err(ExecutionAdapterFailure::ContractViolation(halt));
                }
                Ok(AdaptedLeaf {
                    halt,
                    branch: adapt_branch(
                        Some(&self.manifest),
                        leaf.branch,
                        leaf.state,
                        leaf.depth,
                        leaf.trace,
                        leaf.observations,
                    )?,
                })
            })
            .collect::<Result<Vec<_>, ExecutionAdapterFailure>>()?;
        Ok(AdaptedExecution {
            route,
            leaves,
            effects: result.effects,
            diagnostics,
            timed_out,
        })
    }
}
