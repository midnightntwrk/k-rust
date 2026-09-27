//! Observed, time-bounded path-set execution through the public k-rust facade.
//! Each explored path retains its own halt, observations, effects, and diagnostics.
//! A watchdog cancels execution when the time budget expires.
//! Each leaf also records whether its state is shown feasible or infeasible, and whether its
//! stuckness holds for every instance of its state; the execution records the definition facts
//! the bridge needs to use them ([`crate::feasibility`]).

use std::{
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
    Backend, BackendDiagnosticOutput, BackendError, EffectOutput, ExecuteRequest, ExecutionResult,
    ExecutionStrategy, HaltReasonOutput, ObservedRequest, ResultModalityOutput, TransitionIdOutput,
};
use k_rust::kore::{ast::Pattern, codec};
use k_rust_backend::cancellation::CancellationToken;
use kink_pattern::ExecutionBounds;

use crate::feasibility::{
    DefinitionFacts, Inhabitation, LeafFeasibility, every_instance_stuck, leaf_feasibility,
    uninhabited_variable,
};
use crate::observation::{
    AdaptedBranch, InstalledObservationManifest, ObservationFailure, adapt_branch,
};

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

    /// Whether the adapter's request can yield this halt under `budget`.
    #[must_use]
    pub const fn adapter_admits(self, budget: &ExecutionBudget) -> bool {
        match self {
            Self::Stuck
            | Self::Trivial
            | Self::Vacuous
            | Self::Indeterminate
            | Self::UnsupportedHook
            | Self::SimplificationError
            | Self::Cancelled => true,
            Self::DepthBound => budget.max_depth.is_some(),
            Self::BreadthBound => budget.max_breadth.is_some(),
            Self::Branch | Self::CutPoint | Self::TerminalRule | Self::Timeout => false,
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
    /// Wall-clock budget for the PathSet run.
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

/// One execution leaf with its typed halt class, diagnostics, adapted branch, and state
/// feasibility.
#[derive(Clone, Debug, PartialEq)]
pub struct AdaptedLeaf {
    pub halt: HaltClass,
    pub branch: AdaptedBranch,
    /// `Unknown` for every leaf of a timed-out run, whose states are not decoded.
    pub feasibility: LeafFeasibility,
    /// For a `Stuck` leaf: its stuckness holds for every instance of its state
    /// ([`crate::feasibility::every_instance_stuck`]). `false` for every other halt and for
    /// every leaf of a timed-out run.
    pub every_instance_stuck: bool,
    pub diagnostics: Vec<BackendDiagnosticOutput>,
    pub candidate_diagnostics: Vec<Vec<BackendDiagnosticOutput>>,
    pub remainder_diagnostics: Vec<BackendDiagnosticOutput>,
}

/// The adapted leaves of one execution. Built only by [`ExecutionAdapter::execute`].
#[derive(Clone, Debug, PartialEq)]
pub struct AdaptedExecution {
    pub(crate) leaves: Vec<AdaptedLeaf>,
    pub(crate) effects: Vec<EffectOutput>,
    pub(crate) timed_out: bool,
    pub(crate) definition: DefinitionFacts,
    /// Every rule condition the run relied on is kept in its leaf predicates: the initial state
    /// is ground (k-rust evaluates ground conditions), or no rewrite rule mentions a partial
    /// function (`DefinitionFacts::total_rules`, README R18).
    pub(crate) conditions_kept: bool,
}

/// A path-set leaf after observation state is erased.
#[derive(Clone, Debug, PartialEq)]
pub struct BaselineLeaf {
    pub halt: HaltClass,
    pub state: serde_json::Value,
    pub depth: u64,
    pub branch: Vec<TransitionIdOutput>,
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
                    branch: branch.identity,
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

    /// The facts about the executed definition's rewrite rules.
    #[must_use]
    pub const fn definition_facts(&self) -> DefinitionFacts {
        self.definition
    }

    /// Whether every rule condition the run relied on is kept in its leaf predicates (the
    /// initial state is ground, or `DefinitionFacts::total_rules` holds). Without it no leaf
    /// below depth 0 is a real prefix (README R18).
    #[must_use]
    pub const fn conditions_kept(&self) -> bool {
        self.conditions_kept
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
    Observation(ObservationFailure),
}

impl From<ObservationFailure> for ExecutionAdapterFailure {
    fn from(value: ObservationFailure) -> Self {
        Self::Observation(value)
    }
}

/// The bounded PathSet request.
fn request(state: serde_json::Value, budget: ExecutionBudget) -> ExecuteRequest {
    ExecuteRequest {
        state,
        max_depth: budget.max_depth,
        max_breadth: budget.max_breadth.map(NonZeroUsize::get),
        max_simplification_iterations: budget.max_simplification_iterations,
        strategy: ExecutionStrategy::All,
        stop_at_branch: false,
        result_modality: ResultModalityOutput::PathSet,
        cut_point_rules: Vec::new(),
        terminal_rules: Vec::new(),
        step_timeout_ms: None,
        moving_average_timeout: false,
        ..ExecuteRequest::default()
    }
}

/// Observed execution for one installed manifest, in one expected solver profile.
#[derive(Clone, Debug, PartialEq)]
pub struct ExecutionAdapter {
    manifest: InstalledObservationManifest,
    profile: SolverProfile,
}

impl ExecutionAdapter {
    /// An adapter that expects the qualified no-Z3 profile.
    #[must_use]
    pub const fn new(manifest: InstalledObservationManifest) -> Self {
        Self::with_profile(manifest, SolverProfile::NoZ3)
    }

    /// An adapter that expects `profile`; a backend of the other profile is
    /// [`ExecutionAdapterFailure::SolverProfileMismatch`].
    #[must_use]
    pub const fn with_profile(
        manifest: InstalledObservationManifest,
        profile: SolverProfile,
    ) -> Self {
        Self { manifest, profile }
    }

    #[must_use]
    pub const fn manifest(&self) -> &InstalledObservationManifest {
        &self.manifest
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

    /// Executes `state` from the backend's default module as one observed PathSet run.
    pub fn execute(
        &self,
        backend: &mut Backend,
        state: &Pattern,
        budget: ExecutionBudget,
    ) -> Result<AdaptedExecution, ExecutionAdapterFailure> {
        self.check_profile(backend)?;
        let encoded = codec::to_value(state)
            .map_err(|error| ExecutionAdapterFailure::InvalidState(error.to_string()))?;
        let (inhabitation, facts) = with_definition(backend, |definition| {
            let inhabitation = Inhabitation::of(definition);
            match uninhabited_variable(definition, &inhabitation, state) {
                Ok(None) => Ok((inhabitation, DefinitionFacts::of(definition))),
                Ok(Some(variable)) => Err(ExecutionAdapterFailure::UninhabitedVariable(variable)),
                Err(error) => Err(ExecutionAdapterFailure::InvalidState(error)),
            }
        })?;
        let (result, timed_out) =
            execute_with_watchdog(backend, encoded, budget, |backend, request| {
                backend.execute_observed(ObservedRequest {
                    request,
                    rules: Some(self.manifest.backend_rule_ids()),
                })
            })?;
        let evidence = if timed_out {
            vec![(LeafFeasibility::Unknown, false); result.leaves.len()]
        } else {
            backend.with_solver(None, |definition, solver| {
                Ok::<_, ExecutionAdapterFailure>(
                    result
                        .leaves
                        .iter()
                        .map(|leaf| {
                            let stuck = HaltClass::from_output(leaf.reason) == HaltClass::Stuck
                                && every_instance_stuck(
                                    definition,
                                    solver,
                                    facts,
                                    &inhabitation,
                                    &leaf.state,
                                );
                            (
                                leaf_feasibility(definition, solver, &inhabitation, &leaf.state),
                                stuck,
                            )
                        })
                        .collect(),
                )
            })?
        };
        let conditions_kept = facts.total_rules || state.free_variables().is_empty();
        self.adapt(result, timed_out, &budget, evidence, facts)
            .map(|execution| AdaptedExecution {
                conditions_kept,
                ..execution
            })
    }

    /// Executes the same PathSet request without observation rules.
    pub fn execute_unobserved(
        &self,
        backend: &mut Backend,
        state: &Pattern,
        budget: ExecutionBudget,
    ) -> Result<Vec<BaselineLeaf>, ExecutionAdapterFailure> {
        self.check_profile(backend)?;
        let encoded = codec::to_value(state)
            .map_err(|error| ExecutionAdapterFailure::InvalidState(error.to_string()))?;
        let (result, _) = execute_with_watchdog(backend, encoded, budget, Backend::execute)?;
        result
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
                    branch: leaf.branch,
                })
            })
            .collect()
    }

    fn adapt(
        &self,
        result: ExecutionResult,
        timed_out: bool,
        budget: &ExecutionBudget,
        evidence: Vec<(LeafFeasibility, bool)>,
        definition: DefinitionFacts,
    ) -> Result<AdaptedExecution, ExecutionAdapterFailure> {
        let leaves = result
            .leaves
            .into_iter()
            .zip(evidence)
            .map(|(leaf, (feasibility, every_instance_stuck))| {
                let halt = HaltClass::from_output(leaf.reason);
                if !halt.adapter_admits(budget) {
                    return Err(ExecutionAdapterFailure::ContractViolation(halt));
                }
                Ok(AdaptedLeaf {
                    halt,
                    feasibility,
                    every_instance_stuck,
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
            leaves,
            effects: result.effects,
            timed_out,
            definition,
            conditions_kept: definition.total_rules,
        })
    }
}

fn execute_with_watchdog(
    backend: &mut Backend,
    state: serde_json::Value,
    budget: ExecutionBudget,
    execute: impl FnOnce(&mut Backend, ExecuteRequest) -> Result<ExecutionResult, BackendError>,
) -> Result<(ExecutionResult, bool), ExecutionAdapterFailure> {
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
    let outcome = token.scope(|| execute(backend, request(state, budget)));
    // Stop the watchdog, then read whether it fired before the run ended.
    drop(done);
    watchdog.join().expect("watchdog thread does not panic");
    let result = outcome.map_err(|error| ExecutionAdapterFailure::Backend(error.to_string()))?;
    assert_eq!(result.modality, ResultModalityOutput::PathSet);
    Ok((result, fired.load(Ordering::Acquire)))
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

#[cfg(test)]
mod tests {
    use super::*;

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
        let adapter = ExecutionAdapter::with_profile(
            InstalledObservationManifest::install_with_authors(
                Vec::new(),
                std::collections::BTreeMap::new(),
            )
            .expect("empty manifest"),
            SolverProfile::BUILD,
        );
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
        let manifest = || {
            InstalledObservationManifest::install_with_authors(
                Vec::new(),
                std::collections::BTreeMap::new(),
            )
            .expect("empty manifest")
        };
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
            ExecutionAdapter::new(manifest()).profile(),
            SolverProfile::NoZ3
        );
        for profile in [SolverProfile::NoZ3, SolverProfile::Z3] {
            let adapter = ExecutionAdapter::with_profile(manifest(), profile);
            assert_eq!(adapter.profile(), profile);
            let observed = adapter.execute(&mut backend, &state, budget);
            let unobserved = adapter.execute_unobserved(&mut backend, &state, budget);
            if profile == build {
                let observed = observed.expect("matching profile executes");
                assert_eq!(observed.leaves().len(), 1);
                assert_eq!(unobserved.expect("matching profile executes").len(), 1);
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
}
