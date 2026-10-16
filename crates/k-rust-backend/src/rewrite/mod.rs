//! Rewrite steps and execution over internalized theories, the set of homes of
//! backend.rewrite.apply, backend.rewrite.step, and backend.rewrite.execute:
//! `apply` (one-rule conditional rewriting, backend.rewrite.apply),
//! `recover` (its indeterminate-match recovery ladder, backend.rewrite.apply), `step` (the
//! priority-grouped step with remainder, backend.rewrite.step), `execute` (depth-first
//! exploration of the rewrite tree, backend.rewrite.execute, with `path_trace`, the trace an
//! execution path shares with the paths it forked from), and `predicates` (predicate
//! truth, alpha equivalence, and constructor-domain coverage). This file holds the shared
//! types, the public entry points, and the re-exports that keep every `crate::rewrite::` path
//! of the tests unchanged; each home's head states its cost and counters. In one line: O(c)
//! rule attempts per step for c candidates and O(states) steps per execution;
//! `Counter::RewriteRuleAttempts`, `Counter::RewriteRulesApplied`, `Counter::RewriteSteps`.

mod apply;
mod execute;
mod exploration_merge;
pub(crate) mod path_trace;
mod predicates;
mod recover;
mod roles;
mod step;
mod work;

use apply::{
    BooleanSplit, EqualitySplit, MapNotInKeysSplit, PartialRuleMatch, RuleAttempt, apply_rule,
};
use execute::execute_using;
pub(crate) use execute::{simplify_leaf_pattern, simplify_result_pattern};
pub use predicates::substitute_predicates;
use predicates::{StateNames, extend_unique, pattern_variable_names};
pub(crate) use predicates::{
    check_concreteness, conjunctively_contains_alpha_equivalent, predicate_root_truth,
    predicate_truth, predicates_truth, quantify_introduced_variables,
    violates_finite_constructor_domain,
};
use recover::{
    GeneralUnificationRecovery, freshen_unbound_rule_variables, is_functional_pattern,
    recover_boolean_matches, recover_equality_matches, recover_function_equality_match,
    recover_functional_symbolic_match, recover_general_unification, recover_ite_matches,
    recover_map_not_in_keys_matches, recover_overload_symbolic_match,
    recover_symbolic_map_key_matches, solve_collection_remainders_with_narrowing,
};
pub(crate) use recover::{
    RecoveredMatch, collection_unification_definedness, recover_indeterminate_match,
};
use roles::{Applicability, Remainder};
#[cfg(test)]
pub(crate) use step::rewrite_step_all_first_group_for_tests;
use step::{rewrite_step_all, rewrite_step_any};

use std::{collections::BTreeSet, hash::Hash, sync::Arc, time::Duration};

use crate::{
    builtin::BuiltinEffect,
    definition::BackendDefinition,
    diagnostic::BackendDiagnostic,
    evaluation::EvaluationMode,
    fresh::{FreshCounter, RequestNames},
    matching::SortGraph,
    rule::Predicate,
    search::ResultModality,
    simplify::{
        ContradictedTotal, DEFAULT_MAX_SIMPLIFICATION_ITERATIONS, SimplificationError,
        SimplificationOptions, refuse_uncomputed_applications, simplify_predicates_with_solver,
    },
    smt::{NoSolver, Satisfiability, SmtError, SmtSolver},
    stop::{StopCause, Stoppable},
    substitution::{Substitution, extract_substitution, substitute, substitution_binding},
    term::{Term, Variable},
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
    #[expect(
        clippy::disallowed_methods,
        reason = "the pattern's own equalities, which stay among its constraints and state that their values are defined"
    )]
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

#[derive(Clone, Eq, PartialEq)]
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
    /// The normalization of `pattern` its step already did, which the successor state reuses.
    pub(crate) normalized: NormalizedSuccessor,
    /// The backend diagnostics of the work this candidate's path went through in the step that
    /// produced it: its own construction and simplification, the step work on the part of the
    /// subject it was derived from (a lower-priority candidate inherits its remainder's), and
    /// the step work shared by every candidate. Each distinct diagnostic once, in emission order.
    pub diagnostics: Vec<BackendDiagnostic>,
    /// Under observation, the events this candidate adds to its parent's branch when an
    /// execution reports it without committing it (a `Branch` or `CutPointRule` halt): the
    /// evaluations of its higher-priority remainder, its transition, and the evaluations of its
    /// normalization, anchored as on the branch it would extend. Empty otherwise.
    pub observations: Vec<ObservationEvent>,
}

/// Every field but the `normalized` cache, which is work derived from `pattern`.
impl std::fmt::Debug for AppliedRule {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("AppliedRule")
            .field("before", &self.before)
            .field("pattern", &self.pattern)
            .field("label", &self.label)
            .field("unique_id", &self.unique_id)
            .field("substitution", &self.substitution)
            .field("rule_substitution", &self.rule_substitution)
            .field("rule_predicates", &self.rule_predicates)
            .field("effects", &self.effects)
            .field("remainder_simplifications", &self.remainder_simplifications)
            .field("io", &self.io)
            .field("diagnostics", &self.diagnostics)
            .field("observations", &self.observations)
            .finish()
    }
}

/// The normalization of an applied candidate's successor that its step already did
/// ([`execute::SuccessorNormalization`]), for the successor state to take instead of repeating
/// it. It is a cache of work derived from the candidate's `pattern`: equality ignores it, and a
/// step that changes the pattern after the normalization drops it.
#[derive(Clone, Default)]
pub(crate) struct NormalizedSuccessor(pub(crate) Option<Arc<execute::SuccessorNormalization>>);

impl PartialEq for NormalizedSuccessor {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

impl Eq for NormalizedSuccessor {}

impl std::fmt::Debug for NormalizedSuccessor {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(if self.0.is_some() { "Some(..)" } else { "None" })
    }
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
    /// Under observation, the events this remainder adds to its parent's branch when a `Branch`
    /// halt reports it: its transition and the evaluations of its simplifications and
    /// normalization, anchored as on the branch it would extend. Empty otherwise.
    pub observations: Vec<ObservationEvent>,
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

/// Which part of a rule application's sub-case a [`TrivialApplication`] stands for.
///
/// Tests only: a consumer decides on an entry by its `undefined` instances, whichever kind
/// produced them, so no production code reads the kind.
#[cfg(test)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum TrivialKind {
    /// The application's result is bottom on its whole sub-case: its right-hand side, a
    /// definedness obligation or its `ensures` was refuted, or the right-hand side is `\bottom`.
    /// The rule has no applied candidate for this sub-case.
    Refuted,
    /// The application's result condition was carried, not decided: the right-hand side's
    /// simplification constraints, an undischarged definedness obligation, or an `ensures` that
    /// neither holds nor fails on every instance. The applied candidate of the same rule and
    /// sub-case keeps the instances where that condition holds; this entry is the rest of the
    /// sub-case, where the result is bottom.
    Carried,
}

/// A rule application whose rewritten result is bottom on some instances. Its applicability
/// condition still removes those instances from the priority group's remainder, so lower
/// priorities never see them.
///
/// Such an instance is not stuck, since a rule applies to it and blocks the lower priorities,
/// and it has no successor from this rule: its step is undefined.
///
/// Outside `rewrite` the entry's verdict is `undefined`, the instances whose step is undefined.
/// The sub-case `applicability` and its complement `remainder` are inputs of the priority
/// group's remainder, which `rewrite` alone builds, so they cannot be read outside it:
///
/// ```compile_fail,E0616
/// use k_rust_backend::{rewrite::TrivialApplication, rule::Predicate};
///
/// fn undefined_instances(trivial: &TrivialApplication) -> &Predicate {
///     &trivial.applicability
/// }
/// ```
///
/// The entry's verdict is readable:
///
/// ```
/// use k_rust_backend::{rewrite::TrivialApplication, rule::Predicate};
///
/// fn undefined_instances(trivial: &TrivialApplication) -> &Predicate {
///     &trivial.undefined
/// }
/// ```
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TrivialApplication {
    pub rule_id: String,
    pub label: Option<String>,
    /// Which sub-case this entry stands for; no consumer's decision depends on it.
    #[cfg(test)]
    pub(crate) kind: TrivialKind,
    /// The definedness or ensures obligation that fails on the instances this entry stands for:
    /// either the obligation refuted on the application's whole sub-case, or the carried result
    /// condition whose failure leaves the instances in `undefined`.
    pub obligation: Predicate,
    /// The sub-case this application rewrites to bottom, under `before`'s constraints.
    ///
    /// For an entry whose obligation was refuted on the whole sub-case it is the rule's
    /// applicability `A` (match conditions and undecided `requires`, existentially closed over
    /// the variables the match introduced). For an entry left by a carried result condition it
    /// is `A /\ not D`, where `D` is the existential closure, over those variables and the
    /// rule's freshened existentials (`?X`), of the match conditions, undecided `requires` and
    /// carried result condition: `D` is the sub-case with a defined result of this application.
    pub(in crate::rewrite) applicability: Applicability,
    /// The complementary sub-case retained in the priority-group remainder: `not A` in either
    /// case, so an entry left by a carried result condition does not change the group remainder.
    pub(in crate::rewrite) remainder: Remainder,
    /// The instances of `before` whose step is undefined because of this entry: `applicability`
    /// conjoined with `not D_j` for every applied candidate `j` of the same priority group, so
    /// that an instance another rule (or another right-hand-side alternative) takes to a defined
    /// successor is excluded. The sequential (`Any`) step offers the entry's instances to the
    /// later rules of the same priority and restricts it by the candidates it follows of its own
    /// rule and of those later rules (`before` already excludes the earlier rules' defined
    /// sub-cases). Not checked for satisfiability; it may be syntactically `\bottom`.
    pub undefined: Predicate,
    /// The pattern the rule was applied to: the step's subject for the first productive priority
    /// group, the (simplified) remainder of the higher groups for a lower one.
    pub before: Pattern,
    /// Effects produced while constructing the candidate that simplified to bottom.
    pub effects: Vec<BuiltinEffect>,
    /// The backend diagnostics of the work `undefined` was derived from: the matching, conditions
    /// and right-hand sides of every application of its priority group, after the work on the
    /// remainder it was applied to. Each distinct diagnostic once, in emission order.
    pub diagnostics: Vec<BackendDiagnostic>,
    /// Simplifications of a higher-priority remainder that precede this lower-priority attempt.
    pub(crate) remainder_simplifications: Vec<RemainderSimplification>,
    /// Set when the result is bottom because an equation of a `total` symbol reduced an
    /// application of it to bottom: a diagnostic about the definition that changes nothing else
    /// about the entry ([`ContradictedTotal`]).
    pub contradicted_total: Option<Box<ContradictedTotal>>,
}

impl TrivialApplication {
    /// The instances whose step is undefined because of this entry: the pattern the rule was
    /// applied to (`before`), its constraints conjoined with the conjuncts of `undefined`.
    /// `None` when the result is syntactically `\bottom`; no solver is asked, so the pattern may
    /// have no instance (the crate-internal `decided_undefined_instances` asks).
    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "Predicate is syntax; only the listed variants are special here"
    )]
    pub fn undefined_instances(&self) -> Option<Pattern> {
        let mut pattern = self.before.clone();
        match &self.undefined {
            Predicate::And(conjuncts) => {
                extend_unique(&mut pattern.constraints, conjuncts.iter().cloned());
            }
            Predicate::True => {}
            predicate => {
                extend_unique(&mut pattern.constraints, std::iter::once(predicate.clone()))
            }
        }
        (predicates_truth(&pattern.constraints) != Truth::False).then_some(pattern)
    }

    /// [`Self::undefined_instances`], its constraints simplified, or `None` when they are shown
    /// to have no instance.
    ///
    /// Unlike a successor, this set is not one the step found non-empty: it is the complement of
    /// the defined sub-cases, and it is empty whenever they cover the rule's applicability, for
    /// example when an `ensures ?X >Int 0` always has a witness. An empty set holds no instance,
    /// so a caller reports nothing for it; a set not shown empty (satisfiable or undecided) is
    /// kept. A failed or stopped simplification only loses precision, so the unsimplified
    /// constraints are kept then; a stop of the emptiness query itself is returned, since
    /// keeping the set would then report an undefined step from a missing answer.
    pub(crate) fn decided_undefined_instances(
        &self,
        definition: &BackendDefinition,
        max_simplification_iterations: usize,
        solver: &dyn SmtSolver,
    ) -> Stoppable<Option<Pattern>> {
        let Some(mut pattern) = self.undefined_instances() else {
            return Ok(None);
        };
        match simplify_predicates_with_solver(
            definition,
            &pattern.constraints,
            &[],
            SimplificationOptions::keep_partial(max_simplification_iterations),
            solver,
        ) {
            Ok(Ok(constraints)) => pattern.constraints = constraints,
            // A failed simplification only loses precision: the unsimplified constraints are kept.
            Ok(Err(_failure)) => {}
            // Kept outcome: the unsimplified constraints, which are the same condition; the
            // simplification only refines them. The emptiness query below takes a stop of its
            // own.
            Err(stop) => stop.forgo_refinement(),
        }
        let empty = predicates_truth(&pattern.constraints) == Truth::False
            || matches!(
                solver.is_sat(&pattern.constraints, &Substitution::new())?,
                Ok(Satisfiability::Unsat)
            );
        Ok((!empty).then_some(pattern))
    }
}

/// Alpha equality of trivial entries for the cascade differential tests. It compares and
/// renames every field, including the rewrite-internal `applicability` and `remainder`, so it
/// lives where those fields are visible.
#[cfg(test)]
impl crate::tests::alpha::AlphaComparable for TrivialApplication {
    fn collect_alpha(
        &self,
        other: &Self,
        context: &mut crate::tests::alpha::AlphaContext,
    ) -> Result<(), String> {
        use crate::tests::alpha::collect_predicate;
        collect_predicate(&self.obligation, &other.obligation, context)?;
        self.applicability
            .collect_alpha(&other.applicability, context)?;
        self.remainder.collect_alpha(&other.remainder, context)?;
        collect_predicate(&self.undefined, &other.undefined, context)?;
        self.before.collect_alpha(&other.before, context)?;
        self.remainder_simplifications
            .collect_alpha(&other.remainder_simplifications, context)?;
        if self.rule_id != other.rule_id
            || self.label != other.label
            || self.kind != other.kind
            || self.effects != other.effects
        {
            return Err("non-predicate trivial-application fields differ".into());
        }
        self.diagnostics
            .collect_alpha(&other.diagnostics, context)?;
        Ok(())
    }

    fn rename_alpha(&self, context: &crate::tests::alpha::AlphaContext) -> Result<Self, String> {
        use crate::tests::alpha::rename_predicate;
        Ok(Self {
            rule_id: self.rule_id.clone(),
            label: self.label.clone(),
            kind: self.kind,
            obligation: rename_predicate(&self.obligation, context),
            applicability: self.applicability.rename_alpha(context)?,
            remainder: self.remainder.rename_alpha(context)?,
            undefined: rename_predicate(&self.undefined, context),
            before: self.before.rename_alpha(context)?,
            effects: self.effects.clone(),
            diagnostics: self.diagnostics.rename_alpha(context)?,
            remainder_simplifications: self.remainder_simplifications.rename_alpha(context)?,
            contradicted_total: self.contradicted_total.clone(),
        })
    }
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
        /// Bottom-result sub-cases: execution reports each as a `Trivial` leaf over its
        /// `undefined` instances, search ignores them, and a proof makes each one it does not
        /// show empty a `Trivial` leaf, which the vacuity policy rejects.
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
    /// `StateSet` (the default) is a disjunction of configurations: a final configuration equal to
    /// an earlier one merges into the first earlier leaf that stands for it (a leaf of a stop that
    /// ended the run is never merged, and a terminal-rule leaf merges only with stuck and
    /// terminal-rule leaves), which carries the diagnostics of every leaf merged into it. `PathSet`
    /// keeps one leaf per explored path, so paths that converge on one configuration keep their own
    /// trace, branch identity, and observations. A `StateSet` run that explores every branch also
    /// expands each distinct state of a depth once: a state equal at its depth to one whose
    /// expansion completed, with the same effects, console and console availability and no
    /// diagnostic the other's path lacks, is merged into it, so converging paths cost the distinct
    /// states; exploration stays depth-first, and the leaves are those of the unmerged run but for
    /// the duplicates of `Trivial` and `Vacuous` leaves in a merged subtree. Such a run's
    /// `max_breadth` bounds the pending states of the merged exploration, so where the unmerged run
    /// exceeds the bound the merged run reaches it later or not at all, and its frontier can lie
    /// deeper, so a state the unmerged run ends as `BreadthBound` can be missing from the result. `ExecutionMode::Any`
    /// gives each configuration the successors of the first rule, in priority then definition
    /// order, that gives it a defined result (and a symbolic remainder where none applies), keeping
    /// that rule's right-hand-side alternatives, so it can yield several leaves; the two readings
    /// coincide only when no two leaves share a configuration.
    pub result_modality: ResultModality,
    /// Retain the full path trace in each result leaf. Callers that only consume the final
    /// configuration can discard previous entries while keeping the latest rewrite for halts.
    pub retain_trace: bool,
    /// Further names of the request: the spellings of its patterns as the caller received them
    /// (`RequestNames::of_received`), which unfolding their aliases may have dropped from the
    /// internalized patterns, and of its patterns other than the initial ones, such as a target
    /// the caller matches the results against. The execution mints no name spelled like one of
    /// them, nor like a variable of the initial patterns (`fresh::FreshCounter`).
    pub request_names: RequestNames,
    /// Whether the run is an execution of a program (`Execution`), which lists the items of
    /// `keys_list`, `values` and `Set2List` in k-rust's documented order, or a request whose
    /// results may decide a proof (`Proof`, the default), which leaves such a listing of two or
    /// more items unevaluated, as a defined value the definition does not determine
    /// ([`crate::evaluation`]). Every evaluation of the run sees it, the conditions of rules and
    /// equations included. A caller that runs a program sets `Execution`; the states of a
    /// `Proof` run are the ones a prover may read.
    pub evaluation: EvaluationMode,
    /// Collect the run's coverage: the rules and equations it applied, and those whose condition
    /// it began to decide for a matched instance, reported as [`ExecutionResult::coverage`]
    /// ([`crate::coverage::RunCoverage`] states the contract). Off by default; collecting
    /// changes nothing else in the result. The collection opens after the definition has been
    /// selected and covers seeding, exploration and final leaf selection, whatever the result
    /// modality, so the sets include what was applied on paths whose leaves a state-set merge
    /// drops.
    pub collect_coverage: bool,
    /// The most states the run may visit across all its paths (`None`, the default: no bound).
    ///
    /// A state is visited when the run takes it from its worklist, whatever becomes of it, so an
    /// initial state taken from the worklist, a state that ends as a leaf and a state that
    /// reaches a configuration another path reached each count once; the count is
    /// [`ExecutionResult::work`]. The run takes states in a fixed order, so it stops at the same
    /// state, with the same leaves finished before it, wherever its result is the same: within
    /// the execution determinism contract and its exclusions (docs/compatibility.md,
    /// "Determinism and concurrency", "Execute"), which leave out, among others, a run in which
    /// an SMT query timed out. When a state remains after `max_work` states, that state becomes
    /// the one [`HaltReason::WorkBound`] leaf, the last of the result, and the other pending
    /// states are dropped unexplored; a budget at least the unbounded run's count changes
    /// nothing, and a budget of 0 makes the first initial state, as given, that leaf.
    ///
    /// The budget bounds the states, the leaves and the worklist; it does not bound the work of
    /// one state's step (a ground function evaluation runs to its value), the size of values, or
    /// the length of traces. Under `StateSet` a leaf finished before the stop carries the
    /// diagnostics of the paths merged into it before the stop only, so they may differ from the
    /// same leaf's in a run with a larger budget.
    pub max_work: Option<u64>,
    /// Build no result after a stop that ends the run (a cancellation, a failed solver prelude),
    /// for a caller that will not read a stopped run's leaves (`false`, the default: the leaves
    /// finished before the stop are returned, with the stopped state's leaf).
    ///
    /// When it is set, a run that such a stop ended returns no leaves and does no final merge,
    /// with the cause in [`ExecutionResult::stopped`]; and every pass after the exploration that
    /// builds or compares leaves (draining the frontier at the breadth bound, the state-set final
    /// merge) polls for a stop once per state or leaf, so a cancellation that arrives during it
    /// ends it the same way. Without it nothing polls there.
    pub discard_stopped: bool,
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
            retain_trace: true,
            request_names: RequestNames::default(),
            evaluation: EvaluationMode::Proof,
            collect_coverage: false,
            max_work: None,
            discard_stopped: false,
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
    /// The state's step, or the request, stopped before the step produced its answer: the leaf
    /// is the state as it stood when the stop was observed. `Cancelled` and `SolverPrelude` end
    /// the execution; `Deadline` and `StackExhausted` end this state only.
    Stopped(StopCause),
    /// No sort-correct ground substitution satisfying the leaf pattern's constraints gives
    /// its term a rewrite successor. The set of satisfying instances may be empty.
    Stuck,
    /// An undefined step: under the leaf pattern's constraints, some rule applies to every
    /// instance (it matches, its `requires` holds, and it blocks the lower priorities), and no
    /// instance has a defined successor. `ExecutionMode::Any` offers such instances to every
    /// later application group of the rule and every later rule of the same priority, so there
    /// too no rule of that priority gives an instance a defined successor.
    /// `rule_id` names the rule when one application is responsible. The set of satisfying
    /// instances may be empty.
    Trivial {
        /// Semantic depth after the rule that produced the empty successor.
        depth: u64,
        rule_id: Option<String>,
        label: Option<String>,
        obligation: Predicate,
        /// Set when the undefined result comes from an equation of a `total` symbol that
        /// reduced an application of it to bottom ([`ContradictedTotal`]). A diagnostic about
        /// the definition only: the leaf is the same with or without it.
        contradicted_total: Option<Box<ContradictedTotal>>,
    },
    Vacuous {
        /// Semantic depth at which the path constraint became false.
        depth: u64,
        rule_id: Option<String>,
        label: Option<String>,
        constraint: Predicate,
        /// As for `Trivial`: set when the constraint became false because an equation of a
        /// `total` symbol reduced an application of it to bottom.
        contradicted_total: Option<Box<ContradictedTotal>>,
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
    /// The request's `ExecutionOptions::max_work` was reached before this state was visited: the
    /// leaf's pattern is the state where exploration stopped, as it was taken from the worklist,
    /// unexpanded and unnormalised. It is no result: its term may be unnormalised and its
    /// constraints unsatisfiable. The states still pending were not explored, so the result is
    /// incomplete; the leaf is the last of the result and never merged with another.
    WorkBound,
    Indeterminate(IndeterminateReason),
    Simplification(SimplificationError),
}

/// The result of a step on `pattern` that no rule rewrites: `Stuck`, except that a pattern
/// carrying an application whose value the backend does not compute halts with the
/// unsupported-hook error that names it (`simplify::refuse_uncomputed_applications`).
///
/// No rule's applicability depended on that value (a match or condition over it is refused when
/// the rule is attempted), so the pattern is stuck whatever the value is; but a run that ends
/// there would report a final configuration holding a value the backend did not compute, which
/// reads as the semantics' answer. The error says instead that the backend could not finish it.
pub(crate) fn stuck(definition: &BackendDefinition, pattern: &Pattern) -> Stoppable<RewriteResult> {
    Ok(
        match refuse_uncomputed_applications(definition, Some(&pattern.term), &pattern.constraints)?
        {
            Ok(()) => RewriteResult::Stuck(pattern.clone()),
            Err(error) => RewriteResult::Simplification {
                pattern: pattern.clone(),
                error,
            },
        },
    )
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
        contradicted_total: None,
    }
}

fn applied_trivial_halt(depth: u64, application: &TrivialApplication) -> HaltReason {
    HaltReason::Trivial {
        depth,
        rule_id: Some(application.rule_id.clone()),
        label: application.label.clone(),
        obligation: application.obligation.clone(),
        contradicted_total: application.contradicted_total.clone(),
    }
}

/// The `Vacuous` halt of a state at `depth` whose constraints are false, naming `applied`, the
/// latest rewrite entry of its path, as the rule that produced it.
fn vacuous_halt(
    depth: u64,
    pattern: &Pattern,
    applied: Option<&TraceEntry>,
    contradicted_total: Option<Box<ContradictedTotal>>,
) -> HaltReason {
    HaltReason::Vacuous {
        depth,
        rule_id: applied.map(|entry| entry.unique_id.clone()),
        label: applied.and_then(|entry| entry.label.clone()),
        constraint: false_constraint(pattern),
        contradicted_total,
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
/// One explored path's final constrained pattern.
///
/// Its predicate implies the definedness of every partial term that a `requires`, `ensures`,
/// right-hand side, or simplified state relied on along that path, with or without a solver,
/// subject to any initial-state definedness assumption.
/// Builtin hooks are strict in all arguments, and rule and equation conditions state the
/// definedness of their Boolean terms when instantiated.
/// This guarantee uses the definition's `total`, `functional`, and `preserves-definedness`
/// attributes as axioms; a partial function declared total is outside the contract.
pub struct ExecutionLeaf {
    pub pattern: Pattern,
    pub depth: u64,
    pub trace: Vec<TraceEntry>,
    /// Stable semantic path prefix when observation was enabled, independent of its rule filter.
    /// Unobserved execution leaves this empty; an empty allowlist retains every identity.
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
    /// A leaf of a `StateSet` result into which leaves of other paths with the same configuration
    /// were merged also carries their diagnostics: its own first, then each new one in the order
    /// the merged leaves were met. Such a list may name work that is not on the leaf's own trace,
    /// and the result is free of diagnostics exactly when the `PathSet` result of the same
    /// request is. A merged diagnostic names variables as the path that met it named them, so a
    /// variable the request does not name may not occur in this leaf's state (it is never one of
    /// the leaf's own variables), and diagnostics equal up to such names are each listed.
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
    /// The run's coverage when [`ExecutionOptions::collect_coverage`] asked for it, `None`
    /// otherwise. A run that a stop or a bound cut short carries what it collected before it
    /// ended.
    pub coverage: Option<crate::coverage::RunCoverage>,
    /// The states the run visited across all its paths, the unit
    /// [`ExecutionOptions::max_work`] bounds; reported whether or not a budget was set.
    pub work: u64,
    /// The visited states whose rewrite step ran and answered, whatever the answer (successors, a
    /// branch or cut-point report, or a stuck, trivial, vacuous, indeterminate or
    /// simplification-failure verdict); at most [`ExecutionResult::work`]. The step's guards
    /// answer a state whose constraints are `\bottom` (vacuous) or that carries a surviving
    /// macro or alias (indeterminate) without matching a rule, and such a state is expanded too;
    /// so is a depth-0 state whose contradiction only the input substitution exposes, which is
    /// stepped from its unsimplified pattern. A visited state whose step does not run (the run
    /// ended it before the step, or it is a remainder, decided by its parent's step) or does not
    /// answer (a stop interrupted it) is not expanded, and the state a work budget stopped at is
    /// neither visited nor expanded. Reported whether or not a budget was set, and deterministic
    /// exactly where `work` is (docs/compatibility.md, "Work budget").
    pub expanded: u64,
    /// The stops for lack of native stack the run met in the states it explored (a state-set run
    /// skips a state equal to one of its depth already expanded, and the stops of its subtree):
    /// those that ended a state (a leaf halted
    /// with [`crate::stop::StopCause::StackExhausted`]) and those met while a result was only
    /// refined (normalising a leaf's state, simplifying a definedness condition, folding a
    /// hook, deciding an undefined instance), which a site dismisses, keeping the sound but less
    /// simplified result. Whether such a stop happens depends on the thread's stack, on
    /// `nesting::with_simplification_stack_budget`, and on the stack other threads of the process
    /// hold, so a run's result is a function of its inputs only when this is zero.
    pub stack_stops: usize,
    /// The cause of the stop that ended the run (a cancellation or a failed solver prelude), if
    /// one did; `None` when the run ended by itself, by a bound or by its work budget, unless,
    /// under [`ExecutionOptions::discard_stopped`], a pass after the exploration (the breadth
    /// drain or the state-set final merge) observed such a stop. Under `discard_stopped` a run
    /// with a cause here has no leaves.
    pub stopped: Option<StopCause>,
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

/// What a rewrite step knows of its subject's definedness.
#[derive(Clone, Copy, Debug)]
pub(crate) enum SubjectDefinedness<'a> {
    /// The caller assumes the subject defined: its `⌈t⌉` is known while the rules' conditions
    /// are decided (`ExecutionOptions::assume_initial_defined`).
    Assumed,
    /// Not assumed. The subject denotes its defined instances only, those where these decided
    /// obligations hold ([`initial_definedness`]); none are given when nothing beyond its
    /// constraints is decided. The rules of the first priority that applies see the subject as
    /// it is, so a successor carries the obligations its own step states; what the step leaves
    /// over (its remainder, the part offered to lower priorities or to the later rules of an
    /// `Any` step, a subject no rule applies to) is restricted to the instances where they hold,
    /// since the others are no configuration to rewrite or to report.
    Where(&'a [Predicate]),
}

impl<'a> SubjectDefinedness<'a> {
    pub(crate) const NOTHING_DECIDED: Self = Self::Where(&[]);

    pub(crate) const fn of_assumption(assumed: bool) -> Self {
        if assumed {
            Self::Assumed
        } else {
            Self::NOTHING_DECIDED
        }
    }

    pub(crate) const fn assumed(self) -> bool {
        matches!(self, Self::Assumed)
    }

    /// The obligations that restrict what the step leaves over; none when assumed, since the
    /// rules then decide their conditions under the subject's whole definedness.
    pub(crate) const fn restriction(self) -> &'a [Predicate] {
        match self {
            Self::Assumed => &[],
            Self::Where(obligations) => obligations,
        }
    }
}

/// `pattern` restricted to the instances where `obligations` hold.
pub(crate) fn restricted_to(pattern: &Pattern, obligations: &[Predicate]) -> Pattern {
    let mut restricted = pattern.clone();
    extend_unique(&mut restricted.constraints, obligations.iter().cloned());
    restricted
}

/// Where the initial configuration of a run that does not assume it defined is defined
/// ([`initial_definedness`]).
pub(crate) enum InitialDefinedness {
    /// No instance satisfying the constraints is defined: the configuration denotes nothing.
    Undefined,
    /// The configuration is defined exactly on its instances where these obligations hold; none
    /// when its constraints establish its definedness.
    Where(Vec<Predicate>),
    /// Its definedness depends on an impure application in an operand a conditional never
    /// evaluates (`crate::deferred`): the unsupported-hook outcome.
    Unsupported(crate::simplify::SimplificationError),
}

/// The definedness of the initial configuration `t ∧ φ` of an execution or a search that does
/// not assume it defined.
///
/// A configuration pattern denotes its defined instances only, `⌈t⌉ ∧ t ∧ φ`: where a subterm
/// of `t` is undefined (a partial application outside its domain, a map whose keys coincide) the
/// application holding it is undefined too, and the instance is no configuration. Such an
/// instance has no successor, so no rule is stuck on it, and it is no result. The obligations
/// `⌈t⌉` are therefore decided under `φ` before the first step: refuted, the configuration has no
/// instance; otherwise the obligations left open restrict what its step leaves over
/// ([`SubjectDefinedness::Where`]), so that no remainder, lower priority or stuck leaf is given
/// the instances where they fail. A rule's own conditions are not obligations of `t`: an
/// instance on which a `requires` is undefined is a configuration all the same, and stays stuck
/// where no rule applies to it. A failed simplification states the obligations as `⌈t⌉` gives
/// them, which denote the same instances.
pub(crate) fn initial_definedness(
    definition: &BackendDefinition,
    pattern: &Pattern,
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Stoppable<InitialDefinedness> {
    let obligations = match crate::definedness::ceil_term(definition, &pattern.term) {
        Ok(obligations) => obligations,
        Err(outcome) => return Ok(InitialDefinedness::Unsupported(outcome.into())),
    };
    let obligations = obligations
        .into_iter()
        .filter(|obligation| !pattern.constraints.contains(obligation))
        .collect::<Vec<_>>();
    if obligations.is_empty() {
        return Ok(InitialDefinedness::Where(obligations));
    }
    let open = match simplify_predicates_with_solver(
        definition,
        &obligations,
        &pattern.constraints,
        options,
        solver,
    )? {
        Ok(simplified) if predicates_truth(&simplified) == Truth::False => {
            return Ok(InitialDefinedness::Undefined);
        }
        Ok(simplified) => simplified
            .into_iter()
            .filter(|obligation| {
                obligation != &Predicate::True && !pattern.constraints.contains(obligation)
            })
            .collect::<Vec<_>>(),
        Err(_failure) => obligations,
    };
    if open.is_empty() {
        return Ok(InitialDefinedness::Where(open));
    }
    // The simplification decides each obligation alone; the solver decides them together under
    // `φ`. No instance where they all hold: the configuration has no instance. No instance where
    // one fails: `φ` establishes the definedness, so there is nothing to restrict or to name.
    let mut defined = pattern.constraints.clone();
    defined.extend(open.iter().cloned());
    if matches!(
        solver.is_sat(&defined, &Substitution::new())?,
        Ok(Satisfiability::Unsat)
    ) {
        return Ok(InitialDefinedness::Undefined);
    }
    let all_hold = match open.as_slice() {
        [obligation] => obligation.clone(),
        _ => Predicate::And(open.clone()),
    };
    let mut undefined = pattern.constraints.clone();
    undefined.push(Predicate::Not(Box::new(all_hold)));
    if matches!(
        solver.is_sat(&undefined, &Substitution::new())?,
        Ok(Satisfiability::Unsat)
    ) {
        return Ok(InitialDefinedness::Where(Vec::new()));
    }
    Ok(InitialDefinedness::Where(open))
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
    fresh_counter: &mut FreshCounter,
) -> Stoppable<RewriteResult> {
    rewrite_step_with_solver(definition, pattern, fresh_counter, &NoSolver)
}

pub fn rewrite_step_with_solver(
    definition: &BackendDefinition,
    pattern: &Pattern,
    fresh_counter: &mut FreshCounter,
    solver: &dyn SmtSolver,
) -> Stoppable<RewriteResult> {
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
/// Each instance of the configuration takes the successors of at most one rule
/// (`ExecutionMode::Any`), chosen among the rules of the highest priority that applies to it:
/// the first of them, in the order rule selection lists that priority's rules, that gives it a
/// defined result. Rules of one priority are alternatives, so any of them is a valid choice and
/// that order is not part of the semantics. An instance to which the rules of that priority
/// apply only with undefined results has no successor, since a rule that applies blocks the
/// lower priorities whether or not its result is defined. A one-path reachability claim needs
/// some path to reach its target, so following one rule per instance is enough to establish it.
pub fn rewrite_step_sequential_with_solver(
    definition: &BackendDefinition,
    pattern: &Pattern,
    fresh_counter: &mut FreshCounter,
    solver: &dyn SmtSolver,
) -> Stoppable<RewriteResult> {
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
    fresh_counter: &mut FreshCounter,
    simplification_options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Stoppable<RewriteResult> {
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

/// [`rewrite_step_with_options`] on a subject defined where `defined_where` holds
/// ([`SubjectDefinedness::Where`]), reading a variable-free subject as one state when
/// `ground_halt` is set (search's step).
pub(crate) fn rewrite_step_restricted(
    definition: &BackendDefinition,
    pattern: &Pattern,
    fresh_counter: &mut FreshCounter,
    simplification_options: SimplificationOptions,
    solver: &dyn SmtSolver,
    defined_where: &[Predicate],
    ground_halt: bool,
) -> Stoppable<RewriteResult> {
    rewrite_step_with_optional_execution(
        definition,
        pattern,
        fresh_counter,
        simplification_options,
        solver,
        ExecutionMode::All,
        SubjectDefinedness::Where(defined_where),
        None,
        ground_halt,
    )
}

pub(crate) fn rewrite_step_sequential_with_options(
    definition: &BackendDefinition,
    pattern: &Pattern,
    fresh_counter: &mut FreshCounter,
    simplification_options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Stoppable<RewriteResult> {
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
    fresh_counter: &mut FreshCounter,
    simplification_options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Stoppable<(RewriteResult, bool)> {
    if let Some(symbol) = pattern.macro_or_alias_symbol() {
        let result = RewriteResult::Indeterminate {
            pattern: pattern.clone(),
            reason: IndeterminateReason::SurvivingMacroOrAlias { symbol },
        };
        return Ok((result, true));
    }
    if predicates_truth(&pattern.constraints) == Truth::False {
        return Ok((RewriteResult::Vacuous(pattern.clone()), true));
    }
    let mut determinism = step::SequentialDeterminism::default();
    let result = rewrite_step_any(
        definition,
        pattern,
        fresh_counter,
        simplification_options,
        solver,
        &[],
        None,
        false,
        Some(&mut determinism),
    )?;
    Ok((result, determinism.dropped))
}

pub(crate) fn rewrite_step_with_mode(
    definition: &BackendDefinition,
    pattern: &Pattern,
    fresh_counter: &mut FreshCounter,
    simplification_options: SimplificationOptions,
    solver: &dyn SmtSolver,
    mode: ExecutionMode,
    assume_initial_defined: bool,
) -> Stoppable<RewriteResult> {
    rewrite_step_with_optional_execution(
        definition,
        pattern,
        fresh_counter,
        simplification_options,
        solver,
        mode,
        SubjectDefinedness::of_assumption(assume_initial_defined),
        None,
        false,
    )
}

/// One rewrite step under `mode`. `ground_halt` reads a variable-free subject as one state
/// (`RuleContext::one_state` in apply.rs): execution and search set it, and the proof steps and
/// the public step functions do not.
#[allow(clippy::too_many_arguments)]
fn rewrite_step_with_optional_execution(
    definition: &BackendDefinition,
    pattern: &Pattern,
    fresh_counter: &mut FreshCounter,
    simplification_options: SimplificationOptions,
    solver: &dyn SmtSolver,
    mode: ExecutionMode,
    subject_definedness: SubjectDefinedness<'_>,
    io: Option<&ExecutionIoState>,
    ground_halt: bool,
) -> Stoppable<RewriteResult> {
    if let Some(symbol) = pattern.macro_or_alias_symbol() {
        return Ok(RewriteResult::Indeterminate {
            pattern: pattern.clone(),
            reason: IndeterminateReason::SurvivingMacroOrAlias { symbol },
        });
    }
    if predicates_truth(&pattern.constraints) == Truth::False {
        return Ok(RewriteResult::Vacuous(pattern.clone()));
    }
    match mode {
        ExecutionMode::All => rewrite_step_all(
            definition,
            pattern,
            fresh_counter,
            simplification_options,
            solver,
            subject_definedness,
            io,
            ground_halt,
        ),
        // The sequential step decides its rules' conditions without assuming the subject
        // defined, whatever the caller assumes.
        ExecutionMode::Any => rewrite_step_any(
            definition,
            pattern,
            fresh_counter,
            simplification_options,
            solver,
            subject_definedness.restriction(),
            io,
            ground_halt,
            None,
        ),
    }
}
