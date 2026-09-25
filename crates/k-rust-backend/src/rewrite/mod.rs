//! Rewrite steps and execution over internalized theories, the set of homes of
//! backend.rewrite.apply, backend.rewrite.step, and backend.rewrite.execute of the CQ-10
//! architecture picture: `apply` (one-rule conditional rewriting, backend.rewrite.apply),
//! `recover` (its indeterminate-match recovery ladder, backend.rewrite.apply), `step` (the
//! priority-grouped step with remainder, backend.rewrite.step), `execute` (depth-first
//! exploration of the rewrite tree, backend.rewrite.execute), and `predicates` (predicate
//! truth, alpha equivalence, and constructor-domain coverage). This file holds the shared
//! types, the public entry points, and the re-exports that keep every `crate::rewrite::` path
//! of the tests unchanged; each home's head states its cost and counters. In one line: O(c)
//! rule attempts per step for c candidates and O(states) steps per execution;
//! `Counter::RewriteRuleAttempts`, `Counter::RewriteRulesApplied`, `Counter::RewriteSteps`.

mod apply;
mod execute;
mod predicates;
mod recover;
mod step;

use apply::{
    BooleanSplit, EqualitySplit, MapNotInKeysSplit, PartialRuleMatch, RuleAttempt, apply_rule,
};
use execute::execute_using;
pub(crate) use execute::{simplify_leaf_pattern, simplify_result_pattern};
pub use predicates::substitute_predicates;
pub(crate) use predicates::{
    check_concreteness, conjunctively_contains_alpha_equivalent, predicates_truth,
    quantify_introduced_variables, violates_finite_constructor_domain,
};
use predicates::{extend_unique, pattern_variable_names};
use recover::{
    GeneralUnificationRecovery, freshen_unbound_rule_variables, is_functional_pattern,
    recover_boolean_matches, recover_equality_matches, recover_function_equality_match,
    recover_functional_symbolic_match, recover_general_unification, recover_ite_matches,
    recover_map_not_in_keys_matches, recover_overload_symbolic_match,
    recover_symbolic_map_key_matches, solve_collection_remainders_with_narrowing,
};
pub(crate) use recover::{collection_unification_definedness, recover_indeterminate_match};
#[cfg(test)]
pub(crate) use step::rewrite_step_all_first_group_for_tests;
use step::{rewrite_step_all, rewrite_step_any};

use std::{collections::BTreeSet, hash::Hash, time::Duration};

use crate::{
    builtin::BuiltinEffect,
    definition::BackendDefinition,
    diagnostic::BackendDiagnostic,
    matching::SortGraph,
    rule::Predicate,
    search::ResultModality,
    simplify::{DEFAULT_MAX_SIMPLIFICATION_ITERATIONS, SimplificationError, SimplificationOptions},
    smt::{NoSolver, Satisfiability, SmtError, SmtSolver},
    substitution::{Substitution, extract_substitution, substitute, substitution_binding},
    term::{Term, Variable},
    timeout::StepTimeoutMode,
    transition::{
        ExecutionIoState, ObservationEvent, ObservationOptions, TransitionId,
        UncommittedObservation,
    },
};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Pattern {
    pub term: Term,
    pub constraints: Vec<Predicate>,
}

impl Pattern {
    pub(crate) fn macro_or_alias_symbol(&self) -> Option<crate::term::Name> {
        if let Some(symbol) = self.term.macro_or_alias_symbol() {
            return Some(symbol);
        }
        let mut found = None;
        for predicate in &self.constraints {
            predicate.visit_terms(&mut |term| {
                if found.is_none() {
                    found = term.macro_or_alias_symbol();
                }
            });
            if found.is_some() {
                break;
            }
        }
        found
    }
}

/// Apply the acyclic substitution encoded by a pattern's equality constraints while retaining
/// canonical equality predicates for later RPC projection.
pub fn normalize_pattern_substitution(pattern: &mut Pattern, sorts: &SortGraph) -> Substitution {
    let (substitution, remaining) = extract_substitution(&pattern.constraints, sorts);
    if substitution.is_empty() {
        return substitution;
    }
    pattern.term = substitute(&pattern.term, &substitution);
    let mut constraints = substitution_predicates(&substitution);
    for predicate in substitute_predicates(&remaining, &substitution) {
        if !constraints.contains(&predicate) {
            constraints.push(predicate);
        }
    }
    pattern.constraints = constraints;
    substitution
}

fn substitution_predicates(substitution: &Substitution) -> Vec<Predicate> {
    substitution
        .iter()
        .map(|(variable, value)| Predicate::Equals(Term::variable(variable.clone()), value.clone()))
        .collect()
}

pub(crate) fn retain_substitution_predicates(
    constraints: &mut Vec<Predicate>,
    substitution: &Substitution,
    sorts: &SortGraph,
) {
    for (variable, value) in substitution {
        let represented = constraints.iter().any(|predicate| {
            substitution_binding(predicate, sorts)
                .is_some_and(|(represented, _)| represented == *variable)
        });
        if !represented {
            constraints.insert(
                0,
                Predicate::Equals(Term::variable(variable.clone()), value.clone()),
            );
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AppliedRule {
    /// The constrained pattern against which this application was constructed.
    pub before: Pattern,
    pub pattern: Pattern,
    pub label: Option<String>,
    pub unique_id: String,
    pub substitution: Substitution,
    /// Rule-variable bindings suitable for execution diagnostics. Variables introduced solely as
    /// term aliases (`P #as X`) are implementation details and are omitted from this view.
    pub rule_substitution: Substitution,
    /// Conditions introduced by this rule application, before they are merged with the incoming
    /// path constraints. RPC diagnostics use this provenance to report `rule-predicate` exactly.
    pub rule_predicates: Vec<Predicate>,
    pub effects: Vec<BuiltinEffect>,
    /// Simplifications of a higher-priority remainder that precede this lower-priority rewrite.
    pub(crate) remainder_simplifications: Vec<RemainderSimplification>,
    /// Console state tentatively produced while evaluating this candidate's right-hand side.
    pub(crate) io: Option<ExecutionIoState>,
    /// The backend diagnostics of the work this candidate's path went through in the step that
    /// produced it: its own construction and simplification, the step work on the part of the
    /// subject it was derived from (a lower-priority candidate inherits its remainder's), and
    /// the step work shared by every candidate. Each distinct diagnostic once, in emission order.
    pub diagnostics: Vec<BackendDiagnostic>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RemainderSimplification {
    pub before: Pattern,
    pub after: Pattern,
    pub applied_rules: Vec<String>,
    pub effects: Vec<BuiltinEffect>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RemainderBranch {
    pub pattern: Pattern,
    pub rule_ids: Vec<String>,
    /// Effects pending on this remainder candidate.
    pub effects: Vec<BuiltinEffect>,
    /// Simplifications performed while folding this remainder through lower priority groups.
    pub simplifications: Vec<RemainderSimplification>,
    /// A lower priority group that could not be decided. Earlier branches remain valid, while
    /// this remainder alone is reported as undecided.
    pub indeterminate: Option<UndecidedStep>,
    /// The backend diagnostics of the work this remainder's path went through in the step: the
    /// simplification of its conditions and term, the lower-priority attempts on it, and the
    /// step work shared by every candidate. Each distinct diagnostic once, in emission order.
    pub diagnostics: Vec<BackendDiagnostic>,
}

/// Why a rewrite step could not decide the successors of a pattern.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum UndecidedStep {
    /// The rules' applicability could not be decided for the pattern.
    Indeterminate(IndeterminateReason),
    /// Simplifying a term or condition of a rule application failed.
    Simplification(SimplificationError),
}

impl UndecidedStep {
    /// The step result that reports this undecided step for `pattern`.
    pub fn into_result(self, pattern: Pattern) -> RewriteResult {
        match self {
            Self::Indeterminate(reason) => RewriteResult::Indeterminate { pattern, reason },
            Self::Simplification(error) => RewriteResult::Simplification { pattern, error },
        }
    }
}

/// A rule that unified but whose rewritten result is bottom. Kore retains its unifier in the
/// priority-group remainder even though execution and search have no successor to enqueue.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TrivialApplication {
    pub rule_id: String,
    pub label: Option<String>,
    /// The definedness or ensures obligation refuted by this application.
    pub obligation: Predicate,
    /// The sub-case that rewrites to bottom: the incoming constraints and this predicate.
    pub applicability: Predicate,
    /// The complementary sub-case retained in the priority-group remainder.
    pub remainder: Predicate,
    /// Effects produced while constructing the candidate that simplified to bottom.
    pub effects: Vec<BuiltinEffect>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RewriteResult {
    Stuck(Pattern),
    Trivial(Pattern, Vec<TrivialApplication>),
    Vacuous(Pattern),
    Finished(AppliedRule),
    Branch {
        original: Pattern,
        branches: Vec<AppliedRule>,
        remainder: Option<RemainderBranch>,
        /// Bottom-result sub-cases, ignored by execution/search and consumed by proof vacuity.
        trivial: Vec<TrivialApplication>,
    },
    Indeterminate {
        pattern: Pattern,
        reason: IndeterminateReason,
    },
    /// Simplifying a term or condition of a rule application failed, so the step's successors
    /// are unknown; `pattern` is the configuration (or remainder) being rewritten.
    Simplification {
        pattern: Pattern,
        error: SimplificationError,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum IndeterminateReason {
    /// A preprocessing symbol survived into an executable backend term.
    SurvivingMacroOrAlias {
        symbol: crate::term::Name,
    },
    Match {
        rule_id: String,
        substitution: Substitution,
        remainder: Vec<(Term, Term)>,
    },
    /// Concrete execution must instantiate every free variable on the rule's left-hand side.
    Instantiation {
        rule_id: String,
        missing_variables: BTreeSet<Variable>,
    },
    Requires {
        rule_id: String,
        predicates: Vec<Predicate>,
    },
    Smt {
        rule_id: String,
        error: SmtError,
    },
    Remainder {
        rule_ids: Vec<String>,
        predicates: Vec<Predicate>,
        satisfiability: Result<Satisfiability, SmtError>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExecutionOptions {
    pub max_depth: u64,
    pub max_breadth: Option<usize>,
    pub max_simplification_iterations: usize,
    pub mode: ExecutionMode,
    pub branch_mode: ExecutionBranchMode,
    pub cut_point_rules: BTreeSet<String>,
    pub terminal_rules: BTreeSet<String>,
    pub step_timeout: Option<Duration>,
    pub moving_average_timeout: bool,
    /// Treat the current configuration and its partial subterms as defined while matching rules.
    pub assume_initial_defined: bool,
    /// How the result reads its leaves.
    ///
    /// `StateSet` (the default) is a disjunction of configurations: structurally equal final
    /// configurations collapse into the first leaf in depth-first order. `PathSet` keeps one leaf
    /// per explored path, so paths that converge on one configuration keep their own trace,
    /// branch identity, and observations. Exploration is the same under both; only the final
    /// merge differs. `ExecutionMode::Any` commits one rule per step but keeps that rule's
    /// right-hand-side alternatives and a symbolic remainder, so it can yield several leaves;
    /// the two readings coincide only when no two leaves share a configuration.
    pub result_modality: ResultModality,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ExecutionMode {
    All,
    Any,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ExecutionBranchMode {
    StopAtBranch,
    ExploreAll,
}

impl Default for ExecutionOptions {
    fn default() -> Self {
        Self {
            max_depth: u64::MAX,
            max_breadth: None,
            max_simplification_iterations: DEFAULT_MAX_SIMPLIFICATION_ITERATIONS,
            mode: ExecutionMode::All,
            branch_mode: ExecutionBranchMode::ExploreAll,
            cut_point_rules: BTreeSet::new(),
            terminal_rules: BTreeSet::new(),
            step_timeout: None,
            moving_average_timeout: false,
            assume_initial_defined: false,
            result_modality: ResultModality::StateSet,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TraceEntry {
    pub depth: u64,
    pub kind: TraceKind,
    pub label: Option<String>,
    pub unique_id: String,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TraceKind {
    Simplification,
    Rewrite,
    Claim,
    Remainder,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum HaltReason {
    Cancelled,
    Stuck,
    Trivial {
        /// Semantic depth after the rule that produced the empty successor.
        depth: u64,
        rule_id: Option<String>,
        label: Option<String>,
        obligation: Predicate,
    },
    Vacuous {
        /// Semantic depth at which the path constraint became false.
        depth: u64,
        rule_id: Option<String>,
        label: Option<String>,
        constraint: Predicate,
    },
    Branch {
        branches: Vec<AppliedRule>,
        remainder: Option<RemainderBranch>,
    },
    CutPointRule {
        rule: String,
        next_states: Vec<AppliedRule>,
    },
    TerminalRule {
        rule: String,
    },
    DepthBound,
    BreadthBound,
    Indeterminate(IndeterminateReason),
    Simplification(SimplificationError),
    Timeout(StepTimeoutMode),
}

fn false_constraint(pattern: &Pattern) -> Predicate {
    match pattern.constraints.as_slice() {
        [] => Predicate::False,
        [constraint] => constraint.clone(),
        constraints => Predicate::And(constraints.to_vec()),
    }
}

fn trivial_halt(depth: u64, pattern: &Pattern) -> HaltReason {
    HaltReason::Trivial {
        depth,
        rule_id: None,
        label: None,
        obligation: false_constraint(pattern),
    }
}

fn applied_trivial_halt(depth: u64, application: &TrivialApplication) -> HaltReason {
    HaltReason::Trivial {
        depth,
        rule_id: Some(application.rule_id.clone()),
        label: application.label.clone(),
        obligation: application.obligation.clone(),
    }
}

fn vacuous_halt(depth: u64, pattern: &Pattern, trace: &[TraceEntry]) -> HaltReason {
    let applied = trace
        .iter()
        .rev()
        .find(|entry| entry.kind == TraceKind::Rewrite);
    HaltReason::Vacuous {
        depth,
        rule_id: applied.map(|entry| entry.unique_id.clone()),
        label: applied.and_then(|entry| entry.label.clone()),
        constraint: false_constraint(pattern),
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExecutionLeaf {
    pub pattern: Pattern,
    pub depth: u64,
    pub trace: Vec<TraceEntry>,
    /// Stable semantic path prefix for this leaf when observation was enabled.
    pub branch: Vec<TransitionId>,
    /// Ordered structured events retained for this branch: transition events name the elements
    /// of `branch` in order, and evaluation events are anchored between them.
    pub observations: Vec<ObservationEvent>,
    /// Ordered effects committed by this branch.
    pub effects: Vec<BuiltinEffect>,
    /// Buffered console state retained by this branch.
    pub io: ExecutionIoState,
    pub halt_reason: HaltReason,
    /// The backend diagnostics of the work this leaf's path went through, in the order the path
    /// first met them, each distinct diagnostic once.
    ///
    /// A non-empty list means the leaf's pattern may not be the normal form a larger budget
    /// would reach, or that a condition or predicate was left undecided on the path: the
    /// configuration is equivalent to the one reached, but not known normalized and its
    /// constraints not known refuted. A `Branch` or `CutPointRule` leaf is the parent state: the
    /// candidates it reports carry their own diagnostics (`AppliedRule::diagnostics`,
    /// `RemainderBranch::diagnostics`). A `RuleConditionUnsimplified` qualifies an earlier
    /// `SimplificationBudgetExhausted` over `Predicates` with the same limit. A caller collecting
    /// with `diagnostic::collect` around the execution still receives every diagnostic.
    pub diagnostics: Vec<BackendDiagnostic>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExecutionResult {
    /// The reading of `leaves` selected by `ExecutionOptions::result_modality`.
    pub modality: ResultModality,
    pub leaves: Vec<ExecutionLeaf>,
    /// The committed transcript when final selection retained exactly one leaf.
    ///
    /// Multi-leaf executions expose one transcript on each `ExecutionLeaf` and leave this
    /// single-stream compatibility field empty.
    pub effects: Vec<BuiltinEffect>,
    /// Attempted transitions discarded before they could belong to a surviving branch.
    pub discarded: Vec<UncommittedObservation>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct InitialSimplificationStatus {
    simplified_to_bottom: bool,
}

impl InitialSimplificationStatus {
    /// Whether every nonempty input disjunct completed initial simplification as false.
    pub fn simplified_to_bottom(self) -> bool {
        self.simplified_to_bottom
    }
}

pub fn execute(
    definition: &BackendDefinition,
    initial: Pattern,
    options: ExecutionOptions,
) -> ExecutionResult {
    execute_with_solver(definition, initial, options, &NoSolver)
}

/// Execute one ordinary branch set with pre-buffered console input.
///
/// Console hooks are available only through this ordinary-execution entry point.
pub fn execute_with_io_state(
    definition: &BackendDefinition,
    initial: Pattern,
    options: ExecutionOptions,
    io: ExecutionIoState,
) -> ExecutionResult {
    execute_using(
        definition,
        vec![initial],
        options,
        &NoSolver,
        Some(io),
        None,
        |_| {},
    )
    .0
}

pub fn execute_with_solver(
    definition: &BackendDefinition,
    initial: Pattern,
    options: ExecutionOptions,
    solver: &dyn SmtSolver,
) -> ExecutionResult {
    execute_with_solver_and_observer(definition, initial, options, solver, |_| {})
}

/// Execute with branch-local structured transition observation enabled.
pub fn execute_observed(
    definition: &BackendDefinition,
    initial: Pattern,
    options: ExecutionOptions,
    observation: &ObservationOptions,
) -> ExecutionResult {
    execute_observed_with_solver(definition, initial, options, &NoSolver, observation)
}

/// Execute with structured observation and the supplied SMT solver.
pub fn execute_observed_with_solver(
    definition: &BackendDefinition,
    initial: Pattern,
    options: ExecutionOptions,
    solver: &dyn SmtSolver,
    observation: &ObservationOptions,
) -> ExecutionResult {
    execute_using(
        definition,
        vec![initial],
        options,
        solver,
        None,
        Some(observation),
        |_| {},
    )
    .0
}

pub fn execute_with_solver_and_observer(
    definition: &BackendDefinition,
    initial: Pattern,
    options: ExecutionOptions,
    solver: &dyn SmtSolver,
    observe: impl FnMut(&BuiltinEffect),
) -> ExecutionResult {
    execute_using(
        definition,
        vec![initial],
        options,
        solver,
        None,
        None,
        observe,
    )
    .0
}

pub fn execute_disjunction_with_solver_and_observer(
    definition: &BackendDefinition,
    initial: Vec<Pattern>,
    options: ExecutionOptions,
    solver: &dyn SmtSolver,
    observe: impl FnMut(&BuiltinEffect),
) -> ExecutionResult {
    execute_using(definition, initial, options, solver, None, None, observe).0
}

/// Execute a disjunction and report the outcome of its initial simplification phase.
pub fn execute_disjunction_with_solver_and_observer_with_initial_status(
    definition: &BackendDefinition,
    initial: Vec<Pattern>,
    options: ExecutionOptions,
    solver: &dyn SmtSolver,
    observe: impl FnMut(&BuiltinEffect),
) -> (ExecutionResult, InitialSimplificationStatus) {
    execute_using(definition, initial, options, solver, None, None, observe)
}

/// Execute an ordinary disjunction with pre-buffered console input and report initial
/// simplification status.
///
/// The caller remains responsible for selecting one retained transcript and delivering it to
/// host descriptors. Search and protocol callers use the context-free entry points above.
pub fn execute_disjunction_with_solver_and_io_state_and_observer_with_initial_status(
    definition: &BackendDefinition,
    initial: Vec<Pattern>,
    options: ExecutionOptions,
    solver: &dyn SmtSolver,
    io: ExecutionIoState,
    observe: impl FnMut(&BuiltinEffect),
) -> (ExecutionResult, InitialSimplificationStatus) {
    execute_using(
        definition,
        initial,
        options,
        solver,
        Some(io),
        None,
        observe,
    )
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) enum Truth {
    True,
    False,
    #[default]
    Unknown,
}

pub fn rewrite_step(
    definition: &BackendDefinition,
    pattern: &Pattern,
    fresh_counter: &mut u64,
) -> RewriteResult {
    rewrite_step_with_solver(definition, pattern, fresh_counter, &NoSolver)
}

pub fn rewrite_step_with_solver(
    definition: &BackendDefinition,
    pattern: &Pattern,
    fresh_counter: &mut u64,
    solver: &dyn SmtSolver,
) -> RewriteResult {
    rewrite_step_with_options(
        definition,
        pattern,
        fresh_counter,
        SimplificationOptions::default(),
        solver,
    )
}

/// Apply rewrite rules sequentially, feeding each rule only the remainder left by earlier rules.
///
/// This is Kore's `applyRewriteRulesSequence`, used for one-path reachability proofs.
pub fn rewrite_step_sequential_with_solver(
    definition: &BackendDefinition,
    pattern: &Pattern,
    fresh_counter: &mut u64,
    solver: &dyn SmtSolver,
) -> RewriteResult {
    rewrite_step_with_mode(
        definition,
        pattern,
        fresh_counter,
        SimplificationOptions::default(),
        solver,
        ExecutionMode::Any,
        false,
    )
}

pub(crate) fn rewrite_step_with_options(
    definition: &BackendDefinition,
    pattern: &Pattern,
    fresh_counter: &mut u64,
    simplification_options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> RewriteResult {
    rewrite_step_with_mode(
        definition,
        pattern,
        fresh_counter,
        simplification_options,
        solver,
        ExecutionMode::All,
        false,
    )
}

pub(crate) fn rewrite_step_sequential_with_options(
    definition: &BackendDefinition,
    pattern: &Pattern,
    fresh_counter: &mut u64,
    simplification_options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> RewriteResult {
    rewrite_step_with_mode(
        definition,
        pattern,
        fresh_counter,
        simplification_options,
        solver,
        ExecutionMode::Any,
        false,
    )
}

/// The sequential step of [`rewrite_step_sequential_with_options`], and whether it may have
/// dropped a successor of some configuration of `pattern` (`step::SequentialDeterminism`).
/// When it did not, every configuration of `pattern` has exactly the successors the result
/// keeps, as in the all-path step.
pub(crate) fn rewrite_step_sequential_tracking_dropped(
    definition: &BackendDefinition,
    pattern: &Pattern,
    fresh_counter: &mut u64,
    simplification_options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> (RewriteResult, bool) {
    if let Some(symbol) = pattern.macro_or_alias_symbol() {
        let result = RewriteResult::Indeterminate {
            pattern: pattern.clone(),
            reason: IndeterminateReason::SurvivingMacroOrAlias { symbol },
        };
        return (result, true);
    }
    if predicates_truth(&pattern.constraints) == Truth::False {
        return (RewriteResult::Vacuous(pattern.clone()), true);
    }
    let mut determinism = step::SequentialDeterminism::default();
    let result = rewrite_step_any(
        definition,
        pattern,
        fresh_counter,
        simplification_options,
        solver,
        None,
        Some(&mut determinism),
    );
    (result, determinism.dropped)
}

pub(crate) fn rewrite_step_with_mode(
    definition: &BackendDefinition,
    pattern: &Pattern,
    fresh_counter: &mut u64,
    simplification_options: SimplificationOptions,
    solver: &dyn SmtSolver,
    mode: ExecutionMode,
    assume_initial_defined: bool,
) -> RewriteResult {
    rewrite_step_with_optional_execution(
        definition,
        pattern,
        fresh_counter,
        simplification_options,
        solver,
        mode,
        assume_initial_defined,
        None,
    )
}

#[allow(clippy::too_many_arguments)]
fn rewrite_step_with_optional_execution(
    definition: &BackendDefinition,
    pattern: &Pattern,
    fresh_counter: &mut u64,
    simplification_options: SimplificationOptions,
    solver: &dyn SmtSolver,
    mode: ExecutionMode,
    assume_initial_defined: bool,
    io: Option<&ExecutionIoState>,
) -> RewriteResult {
    if let Some(symbol) = pattern.macro_or_alias_symbol() {
        return RewriteResult::Indeterminate {
            pattern: pattern.clone(),
            reason: IndeterminateReason::SurvivingMacroOrAlias { symbol },
        };
    }
    if predicates_truth(&pattern.constraints) == Truth::False {
        return RewriteResult::Vacuous(pattern.clone());
    }
    match mode {
        ExecutionMode::All => rewrite_step_all(
            definition,
            pattern,
            fresh_counter,
            simplification_options,
            solver,
            assume_initial_defined,
            io,
        ),
        ExecutionMode::Any => rewrite_step_any(
            definition,
            pattern,
            fresh_counter,
            simplification_options,
            solver,
            io,
            None,
        ),
    }
}
