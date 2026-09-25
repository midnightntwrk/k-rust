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
//! Every adapted leaf must have a halt the adapter's own unbounded request can yield.

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

    /// Whether the adapter's own unbounded request can yield this halt.
    #[must_use]
    pub const fn adapter_admits(self) -> bool {
        match self {
            Self::Stuck
            | Self::Trivial
            | Self::Vacuous
            | Self::Indeterminate
            | Self::UnsupportedHook
            | Self::SimplificationError
            | Self::Cancelled => true,
            Self::Branch
            | Self::CutPoint
            | Self::TerminalRule
            | Self::DepthBound
            | Self::BreadthBound
            | Self::Timeout => false,
        }
    }

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
    /// A leaf reports a halt excluded by the adapter's own request on either route.
    ContractViolation(HaltClass),
    Observation(ObservationFailure),
}

impl From<ObservationFailure> for ExecutionAdapterFailure {
    fn from(value: ObservationFailure) -> Self {
        Self::Observation(value)
    }
}

/// The unbounded request issued on either execution route.
fn request(
    state: serde_json::Value,
    budget: ExecutionBudget,
    stop_at_branch: bool,
) -> ExecuteRequest {
    ExecuteRequest {
        state,
        max_depth: None,
        max_breadth: None,
        max_simplification_iterations: budget.max_simplification_iterations,
        strategy: ExecutionStrategy::All,
        stop_at_branch,
        cut_point_rules: Vec::new(),
        terminal_rules: Vec::new(),
        step_timeout_ms: None,
        moving_average_timeout: false,
        ..ExecuteRequest::default()
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
            let request = request(encoded.clone(), budget, stop_at_branch);
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
                if !halt.adapter_admits() {
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

#[cfg(test)]
mod tests {
    use super::*;
    use k_rust::backend::BackendOptions;
    use k_rust::kore::parser::parse_pattern;

    const BUDGET: ExecutionBudget = ExecutionBudget {
        time: Duration::from_secs(30),
        max_simplification_iterations: 1000,
    };

    /// A KORE definition with one route to each halt reason. `gone` rewrites to `\bottom`; `g`
    /// applies to a symbolic argument only with a solver, which the no-Z3 profile lacks; `missing`
    /// has an unimplemented hook; and `or-equation` has two live right-hand sides.
    const HALTS: &str = r#"[]
    module HALTS
        sort SortS{} []
        sort SortV{} [hasDomainValues{}()]
        symbol a{}() : SortS{} [constructor{}()]
        symbol b{}() : SortS{} [constructor{}()]
        symbol done{}() : SortS{} [constructor{}()]
        symbol start{}() : SortS{} [constructor{}()]
        symbol spin{}() : SortS{} [constructor{}()]
        symbol gone{}() : SortS{} [constructor{}()]
        symbol g{}(SortS{}) : SortS{} [constructor{}()]
        symbol open{}(SortS{}) : SortS{} [function{}()]
        symbol f{}(SortS{}) : SortS{} [function{}()]
        symbol k{}() : SortS{} [function{}(), total{}(), injective{}(), no-evaluators{}()]
        hooked-symbol missing{}(SortV{}) : SortS{} [function{}(), hook{}("TEST.missing")]
        axiom{} \rewrites{SortS{}}(\and{SortS{}}(a{}(), \top{SortS{}}()), b{}()) [label{}("ab")]
        axiom{} \rewrites{SortS{}}(\and{SortS{}}(start{}(), \top{SortS{}}()), a{}()) [label{}("left")]
        axiom{} \rewrites{SortS{}}(\and{SortS{}}(start{}(), \top{SortS{}}()), done{}()) [label{}("right")]
        axiom{} \rewrites{SortS{}}(\and{SortS{}}(spin{}(), \top{SortS{}}()), spin{}()) [label{}("spin")]
        axiom{} \rewrites{SortS{}}(\and{SortS{}}(gone{}(), \top{SortS{}}()), \and{SortS{}}(done{}(), \bottom{SortS{}}())) [label{}("gone")]
        axiom{} \rewrites{SortS{}}(\and{SortS{}}(g{}(open{}(X:SortS{})), \top{SortS{}}()), done{}()) [label{}("g")]
        axiom{R} \implies{R}(\top{R}(), \equals{SortS{}, R}(f{}(X:SortS{}), \and{SortS{}}(\or{SortS{}}(X:SortS{}, k{}()), \top{SortS{}}()))) [label{}("or-equation"), simplification{}()]
    endmodule []"#;

    /// How a live row reaches k-rust.
    enum Via {
        /// `ExecutionAdapter::execute` with an empty manifest, which parses each leaf's spelling.
        Adapter(ExecutionBudget, ExecutionRoute),
        /// `Backend::execute_observed` with one field of the adapter's request changed.
        Excluded(fn(&mut ExecuteRequest)),
    }

    /// Makes k-rust produce each of the 13 spellings over `HALTS` and checks that each maps to its
    /// class. Six are produced only through the public facade, because the adapter's request fixes
    /// the options that yield them: it never sets `max_depth` (`depth-bound`), `max_breadth`
    /// (`breadth-bound`), `step_timeout_ms` (`timeout`), cut-point rules (`cut-point`) or terminal
    /// rules (`terminal`), and it discards its `stop_at_branch` run unless that run ended in one
    /// `stuck` leaf (`branch`). Each excluded result is rejected by `adapt` on either route.
    /// `cancelled` is the watchdog's, as in `nonterminating_execution_is_timeout`.
    #[test]
    fn every_halt_spelling_is_produced_live() {
        use ExecutionRoute::{ExploreAll, SinglePath};
        let short = ExecutionBudget {
            time: Duration::from_millis(200),
            ..BUDGET
        };
        // (class, initial state, how k-rust is reached)
        #[rustfmt::skip]
    let rows: [(HaltClass, &str, Via); 13] = [
        (HaltClass::Stuck, "b{}()", Via::Adapter(BUDGET, SinglePath)),
        (HaltClass::Trivial, "gone{}()", Via::Adapter(BUDGET, ExploreAll)),
        (HaltClass::Vacuous, r"\and{SortS{}}(a{}(), \bottom{SortS{}}())", Via::Adapter(BUDGET, ExploreAll)),
        (HaltClass::Branch, "start{}()", Via::Excluded(|request| request.stop_at_branch = true)),
        (HaltClass::CutPoint, "a{}()", Via::Excluded(|request| request.cut_point_rules = vec!["ab".to_owned()])),
        (HaltClass::TerminalRule, "a{}()", Via::Excluded(|request| request.terminal_rules = vec!["ab".to_owned()])),
        (HaltClass::DepthBound, "spin{}()", Via::Excluded(|request| request.max_depth = Some(2))),
        (HaltClass::BreadthBound, "start{}()", Via::Excluded(|request| request.max_breadth = Some(1))),
        (HaltClass::Indeterminate, "g{}(VarX:SortS{})", Via::Adapter(BUDGET, ExploreAll)),
        (HaltClass::UnsupportedHook, r#"missing{}(\dv{SortV{}}("v"))"#, Via::Adapter(BUDGET, ExploreAll)),
        (HaltClass::SimplificationError, "f{}(a{}())", Via::Adapter(BUDGET, ExploreAll)),
        (HaltClass::Timeout, "a{}()", Via::Excluded(|request| request.step_timeout_ms = Some(0))),
        (HaltClass::Cancelled, "spin{}()", Via::Adapter(short, ExploreAll)),
    ];
        let mut covered = Vec::new();
        for (class, state, via) in rows {
            let state = parse_pattern(state).expect("state parses");
            let mut backend =
                Backend::new(HALTS, "HALTS", BackendOptions::default()).expect("backend");
            let halts = match via {
                Via::Adapter(budget, route) => {
                    let manifest =
                        InstalledObservationManifest::install(Vec::new()).expect("empty");
                    let execution = ExecutionAdapter::new(manifest)
                        .execute(&mut backend, &state, budget)
                        .unwrap_or_else(|failure| panic!("{class:?}: {failure:?}"));
                    assert_eq!(execution.route(), route, "{class:?}");
                    assert_eq!(
                        execution.timed_out(),
                        class == HaltClass::Cancelled,
                        "{class:?}"
                    );
                    assert!(execution.diagnostics().is_empty(), "{class:?}");
                    execution.leaves().iter().map(|leaf| leaf.halt).collect()
                }
                Via::Excluded(set) => {
                    let mut request = request(
                        codec::to_value(&state).expect("state encodes"),
                        BUDGET,
                        false,
                    );
                    set(&mut request);
                    let result = backend
                        .execute_observed(ObservedRequest {
                            request,
                            rules: Some(Vec::new()),
                        })
                        .unwrap_or_else(|error| panic!("{class:?}: {error}"));
                    let classes = result
                        .leaves
                        .iter()
                        .map(|leaf| {
                            HaltClass::parse(&leaf.reason)
                                .unwrap_or_else(|| panic!("{class:?}: {:?}", leaf.reason))
                        })
                        .collect::<Vec<_>>();
                    let manifest =
                        InstalledObservationManifest::install(Vec::new()).expect("empty");
                    let adapter = ExecutionAdapter::new(manifest);
                    assert_eq!(
                        adapter.adapt(ExploreAll, result, Vec::new(), false),
                        Err(ExecutionAdapterFailure::ContractViolation(class)),
                        "{class:?}"
                    );
                    classes
                }
            };
            assert!(!halts.is_empty(), "{class:?}: no leaf");
            assert!(
                halts.iter().all(|halt| *halt == class),
                "{class:?}: {halts:?}"
            );
            covered.push(class);
        }
        assert_eq!(covered, HaltClass::ALL, "one live row per class, in order");
    }
}
