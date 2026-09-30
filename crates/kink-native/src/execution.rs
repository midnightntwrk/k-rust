//! Observed, time-bounded path-set execution through the public k-rust facade.
//! Each explored path retains its own halt, observations, effects, and diagnostics.
//! A watchdog cancels execution when the time budget expires.
//! Each leaf also records whether its state is shown feasible or infeasible, and an
//! indeterminate leaf its structured cause; the execution records the definition facts the
//! bridge needs to use them ([`crate::feasibility`]).

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
    Backend, BackendDiagnosticOutput, BackendError, EffectOutput, ExecuteRequest, ExecutionLeaf,
    ExecutionResult, ExecutionStrategy, HaltReasonOutput, ObservationEventOutput, ObservedRequest,
    ResultModalityOutput, SearchFailureOutput, TraceEntry, TransitionClassOutput,
    TransitionIdOutput,
};
use k_rust::kore::{ast::Pattern, codec};
use k_rust_backend::cancellation::CancellationToken;
use kink_pattern::ExecutionBounds;

use crate::execution_difference::{NotProvedReason, StateSequence, StateSequences};
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

/// The adapted leaves of one execution. Built only by [`ExecutionAdapter::execute`].
#[derive(Clone, Debug, PartialEq)]
pub struct AdaptedExecution {
    pub(crate) leaves: Vec<AdaptedLeaf>,
    pub(crate) effects: Vec<EffectOutput>,
    pub(crate) timed_out: bool,
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

impl SteppedExecution {
    /// The sequence view used by the temporary execution-difference certificate.
    pub fn certificate_sequences(&self) -> Result<StateSequences, NotProvedReason> {
        if self.adapted.timed_out {
            return Err(NotProvedReason::Timeout);
        }
        Ok(StateSequences {
            leaves: self
                .adapted
                .leaves
                .iter()
                .zip(&self.states)
                .map(|(leaf, states)| StateSequence {
                    halt: leaf.halt,
                    states: states.clone(),
                    feasibility: leaf.feasibility,
                })
                .collect(),
        })
    }
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
}

/// The bounded PathSet request. Strategy `all` is what makes the leaves the whole path set: every
/// instance's every successor is followed, so a `Trivial` leaf is an undefined step for each of
/// its instances and the leaves cover the initial state. Under `any` a step gives an instance one
/// successor, from the first rule of its highest applicable priority that is defined there
/// (k-rust KK-73), so the events of the other successors are missing; and it follows one
/// collection candidate per rule, so an instance matched only through another candidate may have
/// a defined successor although its leaf is `Trivial`. Stop-at-branch, cut-point and terminal
/// rules are off, so no leaf stops at a branch or a designated rule.
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
        let inhabitation = with_definition(backend, |definition| {
            let inhabitation = Inhabitation::of(definition);
            match uninhabited_variable(definition, &inhabitation, state) {
                Ok(None) => Ok(inhabitation),
                Ok(Some(variable)) => Err(ExecutionAdapterFailure::UninhabitedVariable(variable)),
                Err(error) => Err(ExecutionAdapterFailure::InvalidState(error)),
            }
        })?;
        let (result, timed_out) =
            execute_with_watchdog(backend, encoded, budget, |backend, request| {
                backend.execute_observed(ObservedRequest {
                    request,
                    rules: Some(Vec::new()),
                })
            })?;
        let feasibility = if timed_out {
            vec![LeafFeasibility::Unknown; result.leaves.len()]
        } else {
            backend.with_solver(None, |definition, solver| {
                Ok::<_, ExecutionAdapterFailure>(
                    result
                        .leaves
                        .iter()
                        .map(|leaf| {
                            leaf_feasibility(definition, solver, &inhabitation, &leaf.state)
                        })
                        .collect(),
                )
            })?
        };
        Self::adapt(result, timed_out, &budget, feasibility)
    }

    /// Execute once with every rewrite transition observed, retaining the states of each step.
    /// An observation failure is returned separately from an execution failure.
    pub fn execute_steps(
        &self,
        backend: &mut Backend,
        state: &Pattern,
        budget: ExecutionBudget,
    ) -> Result<Result<SteppedExecution, StepRunFailure>, ExecutionAdapterFailure> {
        self.check_profile(backend)?;
        let encoded = codec::to_value(state)
            .map_err(|error| ExecutionAdapterFailure::InvalidState(error.to_string()))?;
        let (inhabitation, ids) = with_definition(backend, |definition| {
            let inhabitation = Inhabitation::of(definition);
            match uninhabited_variable(definition, &inhabitation, state) {
                Ok(None) => Ok((inhabitation, rewrite_ids(definition))),
                Ok(Some(variable)) => Err(ExecutionAdapterFailure::UninhabitedVariable(variable)),
                Err(error) => Err(ExecutionAdapterFailure::InvalidState(error)),
            }
        })?;
        let ids = match ids {
            Ok(ids) => ids,
            Err(failure) => return Ok(Err(failure)),
        };
        let (result, timed_out) =
            execute_with_watchdog(backend, encoded, budget, |backend, request| {
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
                adapted: Self::adapt(result, true, &budget, feasibility)?,
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
        let adapted = Self::adapt(result, false, &budget, feasibility)?;
        Ok(Ok(SteppedExecution { adapted, states }))
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
                })
            })
            .collect()
    }

    fn adapt(
        result: ExecutionResult,
        timed_out: bool,
        budget: &ExecutionBudget,
        feasibility: Vec<LeafFeasibility>,
    ) -> Result<AdaptedExecution, ExecutionAdapterFailure> {
        let leaves = result
            .leaves
            .into_iter()
            .zip(feasibility)
            .map(|(leaf, feasibility)| {
                let halt = HaltClass::from_output(leaf.reason);
                if !halt.adapter_admits(budget) {
                    return Err(ExecutionAdapterFailure::ContractViolation(halt));
                }
                Ok(AdaptedLeaf {
                    halt,
                    feasibility,
                    undefined_rule: UndefinedStepRule::of(halt, leaf.rule_id, leaf.rule_label),
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

/// Mirror the ambiguity checks of k-rust's observation allow-list before a run, so a
/// rejected observation filter is reported as a step failure rather than a backend error.
fn rewrite_ids(
    definition: &k_rust_backend::definition::BackendDefinition,
) -> Result<Vec<String>, StepRunFailure> {
    let mut available = BTreeMap::<(String, Option<usize>), usize>::new();
    let mut identities = BTreeMap::<&str, usize>::new();
    for axiom in &definition.classified_axioms {
        *identities
            .entry(axiom.attributes().unique_id.as_str())
            .or_default() += 1;
    }
    let mut selected = BTreeSet::new();
    for priorities in definition.rewrite_theory.values() {
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
        &definition.function_theory,
        &definition.simplification_theory,
        &definition.ceil_theory,
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
