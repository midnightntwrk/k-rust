//! ```toml algorithm
//! id = "backend.simplify.term"
//! name = "innermost equational simplification to a budgeted fixed point"
//! sites = ["simplify_with_optional_execution", "simplify_term_entry", "simplify", "simplify_with_solver", "simplify_with_budget", "simplify_children", "simplify_root", "hook_argument_definedness", "apply_theory"]
//! variable = "r = rounds; t = term nodes; c = candidate equations per node"
//! counters = ["SimplifyInvocations", "SimplifyRounds", "SimplifyEquationAttempts", "SimplifyBuiltinEvaluations", "SimplifyNodesSkippedEvaluated", "SimplifyRetractionNodes"]
//! span = "per call"
//! consumes = [{ type = "k_rust_backend::matching::MatchResult", role = "match result" }]
//!
//! [[cost]]
//! mode = "one term lineage"
//! bound = "O(r x |t| x c), with the rounds that are not determined ground function-theory steps bounded by max_iterations; determined ground steps are bounded only by the definition's own computation, the caller's interrupt, and the stack guard"
//!
//! [[cost]]
//! mode = "rule condition"
//! bound = "one nested predicate simplification per evaluated rule condition, with its own budget of max_iterations, skipped when the (rule, term) key is already active"
//!
//! [[cost]]
//! mode = "report retraction (retract_dropped)"
//! bound = "only when the call raised a report of an equation passed over on a kept subterm: one search of the result's conditions and of the term nodes, in both, that lack the evaluated attribute (the part the simplifier walks), each shared node once, stopping when every subject is found"
//! ```
//!
//! ```toml algorithm
//! id = "backend.simplify.predicates"
//! name = "conjunct-set predicate normalization"
//! sites = ["simplify_predicates_with_solver", "simplify_predicates_entry", "predicate_conjunct_index", "simplify_predicates_with_budget", "simplify_predicate_with_budget"]
//! variable = "b = simplification budget; n = conjuncts; e = equalities among the known and additional conjuncts"
//! counters = ["SimplifyInvocations"]
//! span = "per call"
//! consumes = [{ type = "k_rust_backend::matching::MatchResult", role = "match result" }]
//!
//! [[cost]]
//! mode = "one round"
//! bound = "n predicate simplifications plus up to n rebuilds of PathConditionReplacements from e equalities, for at most b + 1 rounds"
//!
//! [[cost]]
//! mode = "report retraction (retract_dropped)"
//! bound = "only when the call raised a report of an equation passed over on a kept subject: one search of the resulting predicates and of their term nodes that lack the evaluated attribute, each shared node once, stopping when every subject is found"
//! ```
//!
//! Innermost (bottom-up) equational rewriting to a budgeted fixed point with priority groups,
//! builtin hooks, and evaluated-attribute memoisation (Booster ApplyEquations): cost O(rounds x
//! |term| x candidates per node), rounds that are not determined ground function-theory steps
//! <= `max_iterations` per lineage (`RootStep`);
//! `Counter::SimplifyInvocations`, `Counter::SimplifyRounds`,
//! `Counter::SimplifyEquationAttempts`, `Counter::SimplifyBuiltinEvaluations`,
//! `Counter::SimplifyNodesSkippedEvaluated`, `Counter::SimplifyRetractionNodes`.
//! Conjunct-set predicate normalisation with an `FxHashSet` conjunct index, one predicate
//! simplification per conjunct per round, budget-bounded re-entry through the ceil and
//! predicate theories.

use std::{cell::Cell, collections::BTreeSet, fmt, sync::Arc};

use k_rust_kore::measure::{self, Algorithm, Counter};
use k_rust_kore::names::{BuiltinSort, WellKnownSymbol};
use rustc_hash::FxHashSet;

use crate::{
    builtin::{
        BuiltinEffect, BuiltinError, BuiltinResult, UnsupportedHookReason,
        evaluate_in_definition as evaluate_builtin,
        evaluate_in_execution as evaluate_builtin_in_execution, k_sequence_item,
    },
    condition::{DecidedEquation, EquationInstance, InstantiatedCondition, MatchedEquation},
    definedness::{ceil_term, terms_apart},
    definition::BackendDefinition,
    diagnostic::{self, BackendDiagnostic, Occurrences, Subject},
    matching::{
        CollectionMatches, InjectionEquality, MatchFailed, MatchMode, MatchResult,
        match_collection_remainders_all_in_definition, match_injection_equality,
        match_term_pairs_in_definition, match_terms_in_definition,
    },
    rewrite::{
        Pattern, Truth, check_concreteness, normalize_pattern_substitution, predicates_truth,
        retain_substitution_predicates, violates_finite_constructor_domain,
    },
    rule::{
        Absence, Predicate, PredicateRewriteRule, RewriteRule, RuleOrigin, RuleRhs,
        applicable_groups, mentions_free, rename_apart, rename_predicate_rule_apart, term_index,
    },
    smt::{NoSolver, SmtError, SmtSolver, TranslationError, Validity},
    stop::{self, Layered, Stoppable, Unwind},
    substitution::{Substitution, compose, substitute, substitution_binding},
    term::{
        FunctionType, HeadRole, Sort, SymbolType, Term, TermKind, Variable, VariableKind,
        head::{
            CertifiedOnly, Head, NormalFormCertificate, RootComparison, classify_value,
            compare_roots,
        },
    },
    transition::ExecutionEvaluationContext,
};

mod result;
pub(crate) mod scan;

use result::{Accumulated, HookOutcome};
pub use result::{Simplification, SimplificationParts};
use scan::{
    EquationAttempt, FunctionTheory, GroupScan, IndeterminateAttempts, SimplificationTheory,
    TermTheory, TheoryScan, scan_group, scan_term_theory,
};

/// Default equation iterations allowed for each simplification fixed point.
///
/// The budget counts the rounds of one lineage whose root rewrite is a simplification rule, a
/// builtin, or a function equation on a symbolic redex or with residual constraints. A function
/// equation applied to a variable-free redex with a determined result is the definition's own
/// computation and is not counted; its divergence ends through cancellation, the step deadline,
/// or the stack guard, each returned as a stop on the outer layer of the simplifier's result.
pub const DEFAULT_MAX_SIMPLIFICATION_ITERATIONS: usize = 100;

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum BudgetPolicy {
    #[default]
    Fail,
    KeepPartial,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum BudgetSubject {
    Term,
    Predicates,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BudgetExhaustion {
    pub limit: usize,
    pub subject: BudgetSubject,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SimplificationOptions {
    pub max_iterations: usize,
    pub budget: BudgetPolicy,
}

impl Default for SimplificationOptions {
    fn default() -> Self {
        Self {
            max_iterations: DEFAULT_MAX_SIMPLIFICATION_ITERATIONS,
            budget: BudgetPolicy::Fail,
        }
    }
}

impl SimplificationOptions {
    /// Evaluate to a fixed point with no bound on equation iterations.
    ///
    /// The default bound ([`DEFAULT_MAX_SIMPLIFICATION_ITERATIONS`]) stops a lineage that needs
    /// more counted rounds, even when its evaluation would terminate; this mode removes that
    /// bound, so the iteration counter never interrupts evaluation. Evaluation can still stop
    /// before the normal form: through cancellation tokens and step deadlines, and through the
    /// stack guard, which stops an evaluation that nests deeper than the stack it has left with
    /// [`StopCause::StackExhausted`](crate::stop::StopCause::StackExhausted), even when that
    /// evaluation would terminate.
    pub const fn unbounded() -> Self {
        Self {
            max_iterations: usize::MAX,
            budget: BudgetPolicy::Fail,
        }
    }

    pub const fn keep_partial(max_iterations: usize) -> Self {
        Self {
            max_iterations,
            budget: BudgetPolicy::KeepPartial,
        }
    }
}

/// An application of a symbol the definition declares `total` (or `functional`) that one of the
/// symbol's own equations reduced to `\bottom`.
///
/// The attribute states that every application of the symbol to defined arguments denotes
/// exactly one element; the equation `f(args) = rhs` is an axiom of the same definition. When
/// the arguments are defined (they were simplified before the equation fired, without becoming
/// `\bottom`) and the instantiated `rhs` simplifies to `\bottom` (`undefined_term` is the
/// innermost undefined builtin application or repeated collection it reached), the two axioms
/// contradict each other on this application. The backend keeps trusting the attribute
/// elsewhere, so this is a diagnostic about the definition, not a change of any verdict: it
/// only names the symbol, the equation and the input on which the definition is inconsistent.
///
/// Only the equation applied last to a `total` application before the undefined term appeared
/// in the same lineage is named, and an application nested in the result reports itself first
/// (innermost), so the named equation is the one whose own result is undefined.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ContradictedTotal {
    /// The application the equation rewrote, with its arguments already simplified.
    pub application: Term,
    /// The equation's `UNIQUE_ID`.
    pub rule_id: String,
    /// The equation's label, when it has one.
    pub label: Option<String>,
    /// Where the equation is written (its first origin), when the KORE carries it.
    pub origin: Option<RuleOrigin>,
    /// The undefined term the equation's result reached.
    pub undefined_term: Term,
}

impl ContradictedTotal {
    /// The symbol whose `total` (or `functional`) attribute is contradicted.
    pub fn symbol(&self) -> &str {
        match self.application.kind() {
            TermKind::Application { symbol, .. } => symbol.name.as_ref(),
            _ => unreachable!("a contradicted total is recorded only for an application"),
        }
    }

    fn new(application: Term, rule: &RewriteRule, undefined_term: Term) -> Box<Self> {
        Box::new(Self {
            application,
            rule_id: rule.attributes.unique_id.clone(),
            label: rule.attributes.label.clone(),
            origin: rule.attributes.origins.first().cloned(),
            undefined_term,
        })
    }
}

/// Whether `term` is an application of a symbol the definition declares `total` or `functional`.
fn is_total_application(term: &Term) -> bool {
    matches!(
        term.kind(),
        TermKind::Application { symbol, .. }
            if symbol.attributes.symbol_type == SymbolType::Function(FunctionType::Total)
    )
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct PatternSimplification {
    pub pattern: Pattern,
    pub applied_rules: Vec<String>,
    pub effects: Vec<BuiltinEffect>,
}

/// Why a simplification could not produce its answer, a fact about the term or predicates asked
/// about under the definition and the backend's capabilities.
///
/// A stop (a cancelled request, a passed step deadline, a failed solver prelude, an exhausted
/// native stack) is not a failure of the simplification: it is returned on the outer layer of
/// every entry point's result (design CBC-04), and this type has no variant that can spell one,
/// so a caller's fallback on a failure cannot turn a missing answer into a decision:
///
/// ```compile_fail,E0599
/// use k_rust_backend::{simplify::SimplificationError, stop::StopCause};
///
/// let _ = SimplificationError::Stopped(StopCause::Cancelled);
/// ```
///
/// A failure is a value of the failure layer:
///
/// ```
/// use k_rust_backend::simplify::SimplificationError;
///
/// let _ = SimplificationError::TopEquationOutsideConjunction { rule_id: "rule".into() };
/// ```
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum SimplificationError {
    Builtin(BuiltinError),
    DisjunctiveResult {
        rule_id: String,
        alternatives: usize,
    },
    TopEquationOutsideConjunction {
        rule_id: String,
    },
    Smt {
        rule_id: String,
        error: SmtError,
    },
    SmtPredicate {
        predicate: Box<Predicate>,
        error: SmtError,
    },
    IterationLimit {
        limit: usize,
        term: Term,
    },
    PredicateIterationLimit {
        limit: usize,
        predicate: Predicate,
    },
    InvalidBuiltinResultSymbol {
        hook: &'static str,
        symbol: &'static str,
    },
    UnsupportedHook {
        hook: String,
        reason: UnsupportedHookReason,
        term: Term,
    },
}

impl fmt::Display for SimplificationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnsupportedHook { hook, reason, .. } => write!(
                formatter,
                "unsupported hook '{hook}' on constructor-like arguments: {reason}"
            ),
            _ => write!(formatter, "{self:?}"),
        }
    }
}

/// The result of a simplification inside this module: `?` propagates a stop and a failure alike.
/// Every entry point returns it layered ([`Layered::layered`]): the stop outside, the failure
/// inside, so that a caller's fallback on a failure cannot see a stop.
type SimplifyResult<T> = Result<T, Unwind<SimplificationError>>;

/// Simplify `term` without a solver.
///
/// Like every entry point of the simplifier, the result has two layers: the outer `Err` is a
/// [`Stop`](crate::stop::Stop) (the request was cancelled, the step deadline passed, the
/// solver's prelude failed, or the thread's stack ran low), for which no answer exists; the
/// inner `Result` is the simplification or its failure. A fallback on a failure is written
/// against the inner layer, after `?` (see [`simplify_predicates_with_solver`]).
pub fn simplify(
    definition: &BackendDefinition,
    term: &Term,
    options: SimplificationOptions,
) -> Stoppable<Result<Simplification, SimplificationError>> {
    simplify_with_solver(definition, term, &[], options, &NoSolver)
}

pub fn simplify_with_solver(
    definition: &BackendDefinition,
    term: &Term,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Stoppable<Result<Simplification, SimplificationError>> {
    simplify_with_optional_execution(definition, term, known_predicates, options, solver, None)
        .layered()
}

pub(crate) fn simplify_in_execution_with_solver(
    definition: &BackendDefinition,
    term: &Term,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
    execution: &mut ExecutionEvaluationContext,
) -> Stoppable<Result<Simplification, SimplificationError>> {
    simplify_with_optional_execution(
        definition,
        term,
        known_predicates,
        options,
        solver,
        Some(execution),
    )
    .layered()
}

/// The term simplifier's entry: a report of an equation passed over on a subterm survives only if
/// the result, its term or the conditions it carries, still holds that subterm
/// ([`diagnostic::retract_dropped`]).
fn simplify_with_optional_execution(
    definition: &BackendDefinition,
    term: &Term,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
    execution: Option<&mut ExecutionEvaluationContext>,
) -> SimplifyResult<Simplification> {
    diagnostic::retract_dropped(
        || {
            simplify_term_entry(
                definition,
                term,
                known_predicates,
                options,
                solver,
                execution,
            )
        },
        |result| {
            result.as_ref().ok().map(|simplified| {
                Occurrences::of([&simplified.term], simplified.conditions().as_slice())
            })
        },
    )
}

fn simplify_term_entry(
    definition: &BackendDefinition,
    term: &Term,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
    execution: Option<&mut ExecutionEvaluationContext>,
) -> SimplifyResult<Simplification> {
    let _apart = crate::rule::ApartScope::enter();
    let _span = measure::algorithm_span(Algorithm::BackendSimplifyTerm);
    measure::bump(Counter::SimplifyInvocations);
    let mut remaining = options.max_iterations;
    let active_conditions = BTreeSet::new();
    let path_condition = PathConditionReplacements::new(known_predicates);
    let assumptions = TermAssumptions {
        predicates: known_predicates,
        path_condition: &path_condition,
    };
    let result = simplify_with_budget(
        definition,
        term,
        &assumptions,
        options,
        &mut remaining,
        &active_conditions,
        solver,
        execution,
    )?;
    if let Some(exhausted) = result.exhausted {
        diagnostic::emit(BackendDiagnostic::SimplificationBudgetExhausted {
            limit: exhausted.limit,
            subject: exhausted.subject,
        });
    }
    Ok(result)
}

/// Simplify a constrained term while retaining and normalizing its path constraints.
pub fn simplify_pattern_with_solver(
    definition: &BackendDefinition,
    pattern: &Pattern,
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Stoppable<Result<Pattern, SimplificationError>> {
    Ok(
        simplify_pattern_details_with_solver(definition, pattern, options, solver)?
            .map(|simplified| simplified.pattern),
    )
}

/// Simplify a constrained term while retaining the equation trace and builtin effects produced
/// by term simplification. Execution needs this richer form when normalizing terminal, cut-point,
/// and branching payloads before returning them to a caller.
pub(crate) fn simplify_pattern_details_with_solver(
    definition: &BackendDefinition,
    pattern: &Pattern,
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Stoppable<Result<PatternSimplification, SimplificationError>> {
    diagnostic::retract_dropped(
        || simplify_pattern_details(definition, pattern, options, solver),
        |result| {
            result.as_ref().ok().map(|simplified| {
                Occurrences::of([&simplified.pattern.term], &simplified.pattern.constraints)
            })
        },
    )
    .layered()
}

fn simplify_pattern_details(
    definition: &BackendDefinition,
    pattern: &Pattern,
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> SimplifyResult<PatternSimplification> {
    let mut pattern = pattern.clone();
    let retained_substitution =
        normalize_pattern_substitution(&mut pattern, definition.sort_graph());
    let simplified = simplify_with_optional_execution(
        definition,
        &pattern.term,
        &pattern.constraints,
        options,
        solver,
        None,
    )?
    .into_parts();
    let mut constraints = pattern.constraints;
    for constraint in simplified.conditions {
        if !constraints.contains(&constraint) {
            constraints.push(constraint);
        }
    }
    let mut constraints =
        simplify_predicates_with_solver(definition, &constraints, &[], options, solver)??;
    if constraints
        .iter()
        .any(|constraint| predicate_refutes_term(constraint, &simplified.term))
    {
        constraints = vec![Predicate::False];
    }
    constraints.retain(|constraint| !ceil_entailed_by_term(constraint, &simplified.term));
    let mut constraints = discharge_valid_constraints(definition, constraints, solver)?;
    retain_substitution_predicates(
        &mut constraints,
        &retained_substitution,
        definition.sort_graph(),
    );
    let mut pattern = Pattern {
        term: simplified.term,
        constraints,
    };
    normalize_pattern_substitution(&mut pattern, definition.sort_graph());
    Ok(PatternSimplification {
        pattern,
        applied_rules: simplified.applied_rules,
        effects: simplified.effects,
    })
}

/// Whether `predicate` is `\ceil(t)` for a `t` whose definedness `term` already entails.
///
/// Symbol application is strict, so the pattern `C[t] /\ P` has an element only where `t` has
/// one, and `\ceil(t) /\ C[t] /\ P = C[t] /\ P`. The port drops the conjunct only when the
/// context `C` consists of total symbols (constructors, cells, injections, `kseq`, `dotk`, and
/// collections), whose own definedness is not an open obligation. Under a partial application
/// the conjunct stays explicit, as the obligation `ceil_term` reports for that application.
fn ceil_entailed_by_term(predicate: &Predicate, term: &Term) -> bool {
    let Predicate::Ceil(subject) = predicate else {
        return false;
    };
    occurs_under_total_context(term, subject)
}

fn occurs_under_total_context(term: &Term, subject: &Term) -> bool {
    if term == subject {
        return true;
    }
    let occurs = |term: &Term| occurs_under_total_context(term, subject);
    match term.kind() {
        TermKind::Application {
            symbol, arguments, ..
        } => {
            symbol.attributes.symbol_type != SymbolType::Function(FunctionType::Partial)
                && arguments.iter().any(occurs)
        }
        TermKind::Injection { term, .. } => occurs(term),
        TermKind::And(left, right) => occurs(left) || occurs(right),
        TermKind::Map { entries, rest, .. } => {
            entries
                .iter()
                .any(|(key, value)| occurs(key) || occurs(value))
                || rest.as_ref().is_some_and(occurs)
        }
        TermKind::List { heads, rest, .. } => {
            heads.iter().any(occurs)
                || rest
                    .as_ref()
                    .is_some_and(|(middle, tails)| occurs(middle) || tails.iter().any(occurs))
        }
        TermKind::Set { elements, rest, .. } => {
            elements.iter().any(occurs) || rest.as_ref().is_some_and(occurs)
        }
        TermKind::DomainValue { .. } | TermKind::Variable(_) => false,
    }
}

/// Drop every residual constraint that the other constraints and the definition's `smt-lemma`
/// axioms make valid, and collapse the constraints to `\bottom` when the solver refutes one.
///
/// The equation fixed point has evaluated what hooks and equations decide; a residual conjunct
/// `P` of `t /\ P /\ Q` is then a question for the theories of the hooked sorts and for the
/// lemma axioms, which only the solver answers. When `Q => P` is valid, `t /\ P /\ Q = t /\ Q`.
/// When `P /\ Q` is unsatisfiable the pattern is empty, and so it is when `Q` alone is. An
/// `Unknown` verdict and an unavailable solver keep the conjunct.
///
/// Cost: one validity query per residual constraint, each bounded by the solver's timeout and
/// retry options (`--smt-timeout`, `--smt-retry-limit`), once per pattern simplification after
/// the equation fixed point. The pass is deliberately not part of the predicate fixed point or
/// of rule-condition evaluation, which run once per equation attempt. Substitution bindings
/// `V = t` are not candidates: after `normalize_pattern_substitution` the variable `V` occurs
/// nowhere else, so `V = t` and its negation are both satisfiable under the other conjuncts and
/// the query could decide nothing.
fn discharge_valid_constraints(
    definition: &BackendDefinition,
    constraints: Vec<Predicate>,
    solver: &dyn SmtSolver,
) -> SimplifyResult<Vec<Predicate>> {
    let mut pending = std::collections::VecDeque::from(constraints);
    let mut retained = Vec::with_capacity(pending.len());
    // Invariant: `retained` holds, in order, the popped constraints that are substitution bindings or that the solver left undecided, and `pending` holds the unexamined ones; each iteration pops one constraint and pushes none, so the loop runs at most |constraints| times.
    while let Some(constraint) = pending.pop_front() {
        if substitution_binding(&constraint, definition.sort_graph()).is_some() {
            retained.push(constraint);
            continue;
        }
        let known = retained
            .iter()
            .chain(pending.iter())
            .cloned()
            .collect::<Vec<_>>();
        // A stop of the query propagates on its own layer; only a failure is the constraint's.
        match decide_condition(std::slice::from_ref(&constraint), &known, solver)? {
            Ok(RuleCondition::Satisfied) => {}
            Ok(
                RuleCondition::Refuted
                | RuleCondition::Indeterminate(ConditionIndeterminacy::InconsistentPathCondition),
            ) => return Ok(vec![Predicate::False]),
            Ok(RuleCondition::Indeterminate(reason)) => {
                report_undecided_predicate(&constraint, reason);
                retained.push(constraint);
            }
            Err(error) => {
                return Err(SimplificationError::SmtPredicate {
                    predicate: Box::new(constraint),
                    error,
                }
                .into());
            }
        }
    }
    Ok(retained)
}

fn predicate_refutes_term(predicate: &Predicate, term: &Term) -> bool {
    match predicate {
        Predicate::Not(inner) => {
            matches!(inner.as_ref(), Predicate::Term(candidate) if candidate == term)
        }
        Predicate::And(conjuncts) => conjuncts
            .iter()
            .any(|conjunct| predicate_refutes_term(conjunct, term)),
        _ => false,
    }
}

/// Simplify a conjunction of predicates under `known_predicates`.
///
/// The result has two layers: the outer `Err` is a [`Stop`](crate::stop::Stop), for which no
/// simplified form exists; the inner `Result` is the simplified conjunction or the
/// simplification's failure. The unsimplified predicates are the same condition, so a caller
/// may keep them on a failure, but not on a stop: a stop says nothing about the predicates, and
/// the owner of the exhausted resource publishes it. The single-layer fallback, which kept the
/// predicates on a stop, no longer compiles:
///
/// ```compile_fail,E0308
/// use k_rust_backend::{
///     definition::BackendDefinition,
///     rule::Predicate,
///     simplify::{SimplificationOptions, simplify_predicates_with_solver},
///     smt::NoSolver,
/// };
///
/// fn f(definition: &BackendDefinition, predicates: Vec<Predicate>) -> Vec<Predicate> {
///     simplify_predicates_with_solver(
///         definition,
///         &predicates,
///         &[],
///         SimplificationOptions::default(),
///         &NoSolver,
///     )
///     .unwrap_or(predicates)
/// }
/// ```
///
/// The same fallback with the stop propagated first, so that it applies to a failure only:
///
/// ```
/// use k_rust_backend::{
///     definition::BackendDefinition,
///     rule::Predicate,
///     simplify::{SimplificationOptions, simplify_predicates_with_solver},
///     smt::NoSolver,
///     stop::Stoppable,
/// };
///
/// fn f(definition: &BackendDefinition, predicates: Vec<Predicate>) -> Stoppable<Vec<Predicate>> {
///     Ok(simplify_predicates_with_solver(
///         definition,
///         &predicates,
///         &[],
///         SimplificationOptions::default(),
///         &NoSolver,
///     )?
///     .unwrap_or(predicates))
/// }
/// ```
pub fn simplify_predicates_with_solver(
    definition: &BackendDefinition,
    predicates: &[Predicate],
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Stoppable<Result<Vec<Predicate>, SimplificationError>> {
    diagnostic::retract_dropped(
        || simplify_predicates_entry(definition, predicates, known_predicates, options, solver),
        |result| match result {
            Ok(Ok(simplified)) => Some(Occurrences::of([], simplified)),
            Ok(Err(_)) | Err(_) => None,
        },
    )
}

fn simplify_predicates_entry(
    definition: &BackendDefinition,
    predicates: &[Predicate],
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Stoppable<Result<Vec<Predicate>, SimplificationError>> {
    let _span = measure::algorithm_span(Algorithm::BackendSimplifyPredicates);
    measure::bump(Counter::SimplifyInvocations);
    let mut remaining = options.max_iterations;
    let active_conditions = BTreeSet::new();
    match simplify_predicates_with_budget(
        definition,
        predicates,
        known_predicates,
        options.max_iterations,
        &mut remaining,
        &active_conditions,
        solver,
    ) {
        // A stop is handled first and propagates: the unsimplified predicates answer an
        // exhausted budget, never a stop.
        Err(Unwind::Stop(stop)) => Err(Unwind::Stop(stop)),
        Err(Unwind::Fail(
            SimplificationError::IterationLimit { .. }
            | SimplificationError::PredicateIterationLimit { .. },
        )) if options.budget == BudgetPolicy::KeepPartial => {
            diagnostic::emit(BackendDiagnostic::SimplificationBudgetExhausted {
                limit: options.max_iterations,
                subject: BudgetSubject::Predicates,
            });
            Ok(predicates.to_vec())
        }
        result => result,
    }
    .layered()
}

struct TermAssumptions<'a> {
    predicates: &'a [Predicate],
    path_condition: &'a PathConditionReplacements,
}

struct PredicateAssumptions<'a> {
    terms: TermAssumptions<'a>,
    conjuncts: &'a FxHashSet<Predicate>,
    excluded: Option<&'a Predicate>,
}

impl PredicateAssumptions<'_> {
    fn contains(&self, predicate: &Predicate) -> bool {
        self.conjuncts.contains(predicate)
            && self.excluded.is_none_or(|excluded| excluded != predicate)
    }
}

/// The assumptions that hold under a quantifier binding `variable`: those that do not
/// mention `variable` free. Facts about a free variable of the bound variable's name speak of
/// another variable.
struct UnshadowedAssumptions {
    predicates: Vec<Predicate>,
    path_condition: PathConditionReplacements,
    conjuncts: FxHashSet<Predicate>,
}

impl UnshadowedAssumptions {
    /// `None` when no assumption mentions `variable` free, so every one of them holds under
    /// the binder as it is.
    fn under_binder(variable: &Variable, assumptions: &PredicateAssumptions<'_>) -> Option<Self> {
        let holds = |predicate: &Predicate| !crate::rule::mentions_free(predicate, variable);
        let shadowed = !assumptions.terms.predicates.iter().all(holds)
            || !assumptions.conjuncts.iter().all(holds);
        if !shadowed {
            return None;
        }
        let predicates = assumptions
            .terms
            .predicates
            .iter()
            .filter(|predicate| holds(predicate))
            .cloned()
            .collect::<Vec<_>>();
        let path_condition = PathConditionReplacements::new(&predicates);
        let conjuncts = assumptions
            .conjuncts
            .iter()
            .filter(|predicate| assumptions.contains(predicate) && holds(predicate))
            .cloned()
            .collect();
        Some(Self {
            predicates,
            path_condition,
            conjuncts,
        })
    }

    fn view(&self) -> PredicateAssumptions<'_> {
        PredicateAssumptions {
            terms: TermAssumptions {
                predicates: &self.predicates,
                path_condition: &self.path_condition,
            },
            conjuncts: &self.conjuncts,
            excluded: None,
        }
    }
}

fn predicate_conjunct_index(predicates: &[Predicate]) -> FxHashSet<Predicate> {
    let mut index = FxHashSet::default();
    for predicate in predicates {
        insert_conjuncts(predicate, &mut index);
    }
    index
}

/// Insert the conjuncts of `predicate`: itself, or those of a nested `And`.
fn insert_conjuncts(predicate: &Predicate, index: &mut FxHashSet<Predicate>) {
    if let Predicate::And(conjuncts) = predicate {
        for conjunct in conjuncts {
            insert_conjuncts(conjunct, index);
        }
    } else {
        index.insert(predicate.clone());
    }
}

fn simplify_predicates_with_budget(
    definition: &BackendDefinition,
    predicates: &[Predicate],
    known_predicates: &[Predicate],
    limit: usize,
    remaining: &mut usize,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
) -> SimplifyResult<Vec<Predicate>> {
    let _apart = crate::rule::ApartScope::enter();
    let mut conjuncts = Vec::new();
    let mut conjunct_index = FxHashSet::default();
    for predicate in predicates {
        extend_conjuncts(&mut conjuncts, &mut conjunct_index, predicate);
    }
    let known_index = predicate_conjunct_index(known_predicates);
    let mut all_assumptions = known_index.clone();
    all_assumptions.extend(conjunct_index.iter().cloned());
    // Each conjunct is simplified under the known predicates and the other conjuncts as they
    // stand when its turn comes: the earlier ones already simplified, the later ones as given.
    // A conjunct replaced by a form equivalent to it under the rest of the current conjunction
    // leaves the conjunction equivalent, so every round is. Simplifying each conjunct under the
    // others as given is not: in `X = 1 ∧ 1 = X` each equality is discharged by the other,
    // and `X = 1` is lost.
    let mut assumptions = known_predicates.to_vec();
    let additional_positions = conjuncts
        .iter()
        .map(|predicate| {
            if known_index.contains(predicate) {
                None
            } else {
                let position = assumptions.len();
                assumptions.push(predicate.clone());
                Some(position)
            }
        })
        .collect::<Vec<_>>();
    let mut known_equalities = Vec::new();
    collect_conjunctive_equalities(known_predicates, &mut known_equalities);
    let known_equalities = owned_equalities(known_equalities);
    // The equalities of each additional conjunct as it currently stands.
    let mut conjunct_equalities = conjuncts
        .iter()
        .enumerate()
        .map(|(index, predicate)| {
            if additional_positions[index].is_none() {
                return Vec::new();
            }
            let mut equalities = Vec::new();
            collect_conjunctive_equalities(std::slice::from_ref(predicate), &mut equalities);
            owned_equalities(equalities)
        })
        .collect::<Vec<_>>();
    let path_condition_excluding = |conjunct_equalities: &[Vec<(Term, Term)>],
                                    excluded: Option<usize>| {
        PathConditionReplacements::from_equalities(
            known_equalities
                .iter()
                .chain(
                    conjunct_equalities
                        .iter()
                        .enumerate()
                        .filter(|(position, _)| Some(*position) != excluded)
                        .flat_map(|(_, equalities)| equalities.iter()),
                )
                .map(|(left, right)| (left, right)),
        )
    };
    // The path condition of every current equality, rebuilt only after one of them changed.
    let mut full_path_condition = None;
    // The conjunct parts of the additional conjuncts simplified so far.
    let mut simplified_conjuncts = FxHashSet::default();
    let mut simplified = Vec::with_capacity(conjuncts.len());
    for (index, predicate) in conjuncts.iter().enumerate() {
        // The conjunct is not an assumption of its own simplification.
        if let Some(position) = additional_positions[index] {
            assumptions[position] = Predicate::True;
        }
        let result = {
            let excluded_path_condition = (!conjunct_equalities[index].is_empty())
                .then(|| path_condition_excluding(&conjunct_equalities, Some(index)));
            let path_condition = match &excluded_path_condition {
                Some(path_condition) => path_condition,
                None => full_path_condition
                    .get_or_insert_with(|| path_condition_excluding(&conjunct_equalities, None)),
            };
            let assumptions = PredicateAssumptions {
                terms: TermAssumptions {
                    predicates: &assumptions,
                    path_condition,
                },
                conjuncts: &all_assumptions,
                excluded: (!known_index.contains(predicate)).then_some(predicate),
            };
            let mut predicate_remaining = *remaining;
            simplify_predicate_with_budget(
                definition,
                predicate,
                &assumptions,
                limit,
                &mut predicate_remaining,
                active_conditions,
                solver,
            )
        }?;
        if let Some(position) = additional_positions[index] {
            assumptions[position] = result.clone();
            insert_conjuncts(&result, &mut simplified_conjuncts);
            if result != *predicate {
                let mut equalities = Vec::new();
                collect_conjunctive_equalities(std::slice::from_ref(&result), &mut equalities);
                let equalities = owned_equalities(equalities);
                if equalities != conjunct_equalities[index] {
                    conjunct_equalities[index] = equalities;
                    full_path_condition = None;
                }
                // The original conjuncts are distinct, so the replaced one remains an
                // assumption only as a part of a simplified conjunct.
                if !simplified_conjuncts.contains(predicate) {
                    all_assumptions.remove(predicate);
                }
                insert_conjuncts(&result, &mut all_assumptions);
            }
        }
        simplified.push(result);
    }
    let mut simplified = if violates_finite_constructor_domain(definition, &simplified) {
        vec![Predicate::False]
    } else {
        simplified
    };
    if simplified.contains(&Predicate::False) {
        simplified = vec![Predicate::False];
    } else {
        simplified.retain(|predicate| predicate != &Predicate::True);
    }
    if simplified == conjuncts {
        return Ok(simplified);
    }
    if *remaining == 0 {
        return Err(SimplificationError::PredicateIterationLimit {
            limit,
            predicate: Predicate::And(simplified),
        }
        .into());
    }
    *remaining -= 1;
    // Invariant: `remaining` was decremented just above, so nesting depth <= the budget.
    simplify_predicates_with_budget(
        definition,
        &simplified,
        known_predicates,
        limit,
        remaining,
        active_conditions,
        solver,
    )
}

fn extend_conjuncts(
    conjuncts: &mut Vec<Predicate>,
    index: &mut FxHashSet<Predicate>,
    predicate: &Predicate,
) {
    if let Predicate::And(nested) = predicate {
        for predicate in nested {
            extend_conjuncts(conjuncts, index, predicate);
        }
    } else if index.insert(predicate.clone()) {
        conjuncts.push(predicate.clone());
    }
}

fn simplify_rule_predicates(
    definition: &BackendDefinition,
    condition_key: (&str, &Term),
    predicates: &[Predicate],
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
) -> SimplifyResult<Vec<Predicate>> {
    let key = (condition_key.0.to_owned(), condition_key.1.clone());
    if active_conditions.contains(&key) {
        return Ok(predicates.to_vec());
    }
    let mut active_conditions = active_conditions.clone();
    active_conditions.insert(key);
    let mut remaining = options.max_iterations;
    simplify_predicates_with_budget(
        definition,
        predicates,
        known_predicates,
        options.max_iterations,
        &mut remaining,
        &active_conditions,
        solver,
    )
}

/// Simplify the side-condition predicates of an application attempt of `rule_id`, keeping
/// them unsimplified when simplification fails.
///
/// The unsimplified predicates are the same condition, so deciding them instead is sound; it
/// is only weaker, and may leave the condition undecided where the simplified form would have
/// been decided. Every weakening is recorded with its cause (`record_rule_condition_failure`),
/// because otherwise an equation left unapplied because simplifying its condition failed is
/// indistinguishable from one whose condition is open.
///
/// A stop is matched first and propagates; the fallback matches failures only (`Unwind::Fail`).
/// A failure is a fact about simplifying this condition (the budget is a bound the simplifier
/// chose, a hook or a solver query that cannot be evaluated is a limit of the backend), and a
/// weaker condition is a fit answer to it; a cancelled request, a passed deadline, a failed solver
/// prelude, or an exhausted stack says
/// nothing about the condition, and deciding the unsimplified predicates would leave the equation
/// blocked and report a silent `Stuck` one level up, a wrong answer in place of the stop.
///
/// The match is on the module's own result rather than on its layered form: this function is a
/// frame of the simplifier's recursion through equation conditions, and converting to the
/// layered form here would add its temporaries to that frame.
#[allow(clippy::too_many_arguments)]
fn simplify_rule_predicates_or_keep(
    definition: &BackendDefinition,
    rule_id: &str,
    anchor: &Term,
    predicates: Vec<Predicate>,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
) -> SimplifyResult<Vec<Predicate>> {
    match simplify_rule_predicates(
        definition,
        (rule_id, anchor),
        &predicates,
        known_predicates,
        options,
        active_conditions,
        solver,
    ) {
        Ok(simplified) => Ok(simplified),
        Err(Unwind::Stop(stop)) => Err(Unwind::Stop(stop)),
        Err(Unwind::Fail(failure)) => {
            record_rule_condition_failure(rule_id, failure);
            Ok(predicates)
        }
    }
}

/// Record why the side conditions of an application attempt of `rule_id` are kept unsimplified,
/// so that an equation left unapplied because of `failure` is distinguishable from one whose
/// condition is open.
///
/// Every failure is disposed of by name: the match is on the plain enum, where
/// `clippy::wildcard_enum_match_arm` sees a wildcard arm, so a new failure kind must be given its
/// diagnostic here instead of being absorbed silently.
///
/// - The iteration budget is a bound the simplifier chose: the budget exhaustion over
///   `Predicates` qualified by `RuleConditionUnsimplified`.
/// - An unsupported hook on constructor-like arguments is the hook left unevaluated, the
///   diagnostic the hook gets on symbolic arguments.
/// - Every other failure is a `RuleConditionFailed` carrying it.
#[deny(clippy::wildcard_enum_match_arm)]
#[cold]
#[inline(never)]
fn record_rule_condition_failure(rule_id: &str, failure: SimplificationError) {
    match failure {
        SimplificationError::IterationLimit { limit, .. }
        | SimplificationError::PredicateIterationLimit { limit, .. } => {
            diagnostic::emit_rule_condition_budget_exhausted(rule_id, limit);
        }
        SimplificationError::UnsupportedHook { hook, reason, .. } => {
            diagnostic::emit(BackendDiagnostic::UnsupportedHookUnevaluated { hook, reason });
        }
        failure @ (SimplificationError::Smt { .. }
        | SimplificationError::SmtPredicate { .. }
        | SimplificationError::Builtin(..)
        | SimplificationError::DisjunctiveResult { .. }
        | SimplificationError::TopEquationOutsideConjunction { .. }
        | SimplificationError::InvalidBuiltinResultSymbol { .. }) => {
            diagnostic::emit(BackendDiagnostic::RuleConditionFailed {
                rule_id: rule_id.to_owned(),
                failure,
            });
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ConditionIndeterminacy {
    NoSolver,
    ImplicationIndeterminate,
    SmtUnknown(String),
    InconsistentPathCondition,
    /// The SMT encoding could not pose the query. The limit belongs to the encoding, not to
    /// the pattern: the predicates are still constraints, and the verdict is open.
    Untranslatable(TranslationError),
    /// The match binds an element variable to a pattern that contains a set variable, so the
    /// binding is not known to be functional and the equation's instance is not justified;
    /// see `binds_element_variable_to_set_pattern`.
    NonFunctionalBinding,
    /// The equation's right-hand side or `ensures` has variables, named here as the definition
    /// spells them, that its left-hand side does not bind
    /// (`ComputedRuleAttributes::unbound_result_variables`), and its `requires` is not refuted.
    /// Matching fixes no value for them, so the instance is not a term of the request; see
    /// `evaluate_equation_condition`, which reports it as an `UndecidedCondition` diagnostic of
    /// the attempt.
    UnboundResultVariables(Vec<String>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum RuleCondition {
    Satisfied,
    Refuted,
    Indeterminate(ConditionIndeterminacy),
}

/// The verdict on an equation instance's `requires`.
#[must_use]
enum EquationCondition {
    /// The `requires` holds; the instance, with its binding obligations still to decide.
    Satisfied(MatchedEquation),
    Refuted,
    Indeterminate(ConditionIndeterminacy),
}

/// Decide the `requires` of an equation `instance` under the path condition. It is simplified
/// first, keyed by `anchor` against re-entry, and a verdict the solver could not reach is
/// reported as a diagnostic of `rule_id`; without an anchor the definedness of its terms is
/// stated and it is decided as it is.
///
/// An equation whose result has variables its left-hand side does not bind
/// (`unbound_result`, from `ComputedRuleAttributes::unbound_result_variables`) is satisfied by
/// no instance: the equation states `l = r` for every value of those variables that satisfies
/// the `requires`, and matching `l` fixes none of them, so the instance `r` has no witness among
/// the request's terms. Its `requires` is still decided, with those variables free: refuted, it
/// holds for no value of them and the equation says nothing about the subject, as for any
/// equation; otherwise the verdict is `Indeterminate(UnboundResultVariables)`, which keeps the
/// subject, and for a function blocks the lower-priority equations, as an open `requires` does.
/// That verdict is reported as an `UndecidedCondition` diagnostic of `rule_id` with the decided
/// `requires`. Every caller that uses an equation's result reaches it through `Satisfied`.
///
/// The diagnostics emitted here belong to the attempt: its caller buffers them and keeps them
/// only with an outcome that is kept (`scan::scan_group`, `matches_top_equation`).
///
/// `rule_variables` are the variables of the equation, as renamed apart for this attempt, that
/// its left-hand side does not bind (`ComputedRuleAttributes::unbound_variables`). Renaming
/// apart keeps them out of the subject and the path condition, so those free in the decided
/// `requires` are exactly the equation's own; a diagnostic names them as such.
#[allow(clippy::too_many_arguments)]
fn evaluate_equation_condition(
    definition: &BackendDefinition,
    rule_id: &str,
    unbound_result: &[String],
    rule_variables: &BTreeSet<Variable>,
    anchor: Option<&Term>,
    instance: EquationInstance,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
) -> SimplifyResult<EquationCondition> {
    let (requires, matched) = instance.into_requires();
    // `R[t]` must hold on the element `t` denotes, and holds there only where its terms are
    // defined, so their definedness joins the requires. The definedness of the bound terms
    // themselves is the `\ceil(t)` factor, which is carried rather than decided, so it is taken
    // as known and not restated as a requires.
    let bound_definedness = matched.bindings().as_known();
    let definedness_known = if bound_definedness.is_empty() {
        None
    } else {
        let mut known = known_predicates.to_vec();
        known.extend(bound_definedness.iter().cloned());
        Some(known)
    };
    let definedness_known = definedness_known.as_deref().unwrap_or(known_predicates);
    let predicates = if let Some(anchor) = anchor {
        requires.simplify(
            definition,
            known_predicates,
            definedness_known,
            |predicates, known, first_attempt| {
                if first_attempt {
                    simplify_rule_predicates(
                        definition,
                        (rule_id, anchor),
                        &predicates,
                        known,
                        options,
                        active_conditions,
                        solver,
                    )
                    .layered()
                } else {
                    simplify_rule_predicates_or_keep(
                        definition,
                        rule_id,
                        anchor,
                        predicates,
                        known,
                        options,
                        active_conditions,
                        solver,
                    )
                    .layered()
                }
            },
        )??
    } else {
        requires.with_definedness(definition, definedness_known)
    };
    Ok(
        match decide_rule_condition(
            rule_id,
            &predicates,
            rule_variables,
            known_predicates,
            solver,
        )? {
            RuleCondition::Refuted => EquationCondition::Refuted,
            RuleCondition::Satisfied | RuleCondition::Indeterminate(_)
                if !unbound_result.is_empty() =>
            {
                let reason =
                    ConditionIndeterminacy::UnboundResultVariables(unbound_result.to_vec());
                diagnostic::emit(BackendDiagnostic::UndecidedCondition {
                    rule_id: rule_id.to_owned(),
                    reason: reason.clone(),
                    rule_variables: condition_rule_variables(&predicates, rule_variables),
                    predicates,
                });
                EquationCondition::Indeterminate(reason)
            }
            RuleCondition::Satisfied => EquationCondition::Satisfied(matched),
            RuleCondition::Indeterminate(reason) => EquationCondition::Indeterminate(reason),
        },
    )
}

/// Decide already simplified condition predicates under the path condition, reporting a
/// verdict the solver could not reach as a diagnostic of `rule_id` that lists those of
/// `rule_variables` free in `predicates` (see `evaluate_equation_condition`).
fn decide_rule_condition(
    rule_id: &str,
    predicates: &[Predicate],
    rule_variables: &BTreeSet<Variable>,
    known_predicates: &[Predicate],
    solver: &dyn SmtSolver,
) -> SimplifyResult<RuleCondition> {
    let condition = decide_condition(predicates, known_predicates, solver)?.map_err(|error| {
        SimplificationError::Smt {
            rule_id: rule_id.to_owned(),
            error,
        }
    })?;
    if let RuleCondition::Indeterminate(reason) = &condition
        && solver_could_not_answer(reason)
    {
        diagnostic::emit(BackendDiagnostic::UndecidedCondition {
            rule_id: rule_id.to_owned(),
            reason: reason.clone(),
            predicates: predicates.to_vec(),
            rule_variables: condition_rule_variables(predicates, rule_variables),
        });
    }
    Ok(condition)
}

/// The members of `rule_variables` free in `predicates`, in order.
fn condition_rule_variables(
    predicates: &[Predicate],
    rule_variables: &BTreeSet<Variable>,
) -> Vec<Variable> {
    if rule_variables.is_empty() {
        return Vec::new();
    }
    rule_variables
        .iter()
        .filter(|variable| {
            predicates
                .iter()
                .any(|predicate| mentions_free(predicate, variable))
        })
        .cloned()
        .collect()
}

/// Decide whether `predicates` hold under `known_predicates` and the definition's `smt-lemma`
/// axioms.
///
/// Syntactic truth and membership in `known_predicates` are decided without the solver. The
/// solver answers the rest within the timeout and retry bounds it was created with; the
/// `Indeterminate` verdict names why it did not decide, including a query the SMT encoding
/// could not pose, which leaves the predicates as open constraints. `Ok(Err)` reports a solver
/// failure other than those. `Err` is a stop the solver observed: no verdict exists, and none
/// of the others may stand in for it. The rewriter's `requires` check, standalone predicate
/// simplification, and the residual-constraint discharge of pattern simplification all share
/// this decision.
#[deny(clippy::wildcard_enum_match_arm)]
pub(crate) fn decide_condition(
    predicates: &[Predicate],
    known_predicates: &[Predicate],
    solver: &dyn SmtSolver,
) -> Stoppable<Result<RuleCondition, SmtError>> {
    match predicates_truth(predicates) {
        Truth::False => return Ok(Ok(RuleCondition::Refuted)),
        Truth::True => return Ok(Ok(RuleCondition::Satisfied)),
        Truth::Unknown => {}
    }
    if predicates
        .iter()
        .all(|predicate| known_predicates.contains(predicate))
    {
        return Ok(Ok(RuleCondition::Satisfied));
    }
    Ok(
        match solver.check_predicates(known_predicates, &Substitution::new(), predicates)? {
            Ok(validity) => Ok(match validity {
                Validity::Valid => RuleCondition::Satisfied,
                Validity::Refuted => RuleCondition::Refuted,
                Validity::Contingent => {
                    RuleCondition::Indeterminate(ConditionIndeterminacy::ImplicationIndeterminate)
                }
                Validity::InconsistentGroundTruth => {
                    RuleCondition::Indeterminate(ConditionIndeterminacy::InconsistentPathCondition)
                }
                Validity::Unknown(message) => {
                    RuleCondition::Indeterminate(ConditionIndeterminacy::SmtUnknown(message))
                }
            }),
            Err(SmtError::Unavailable) => Ok(RuleCondition::Indeterminate(
                ConditionIndeterminacy::NoSolver,
            )),
            Err(SmtError::Translation(error)) => Ok(RuleCondition::Indeterminate(
                ConditionIndeterminacy::Untranslatable(error),
            )),
            Err(error) => Err(error),
        },
    )
}

/// Whether an indeterminate verdict came from a solver that was asked and did not answer,
/// including a query its encoding could not pose, as opposed to a missing solver or an
/// implication that is genuinely open.
fn solver_could_not_answer(reason: &ConditionIndeterminacy) -> bool {
    matches!(
        reason,
        ConditionIndeterminacy::InconsistentPathCondition
            | ConditionIndeterminacy::SmtUnknown(_)
            | ConditionIndeterminacy::Untranslatable(_)
    )
}

fn report_undecided_predicate(predicate: &Predicate, reason: ConditionIndeterminacy) {
    if solver_could_not_answer(&reason) {
        diagnostic::emit(BackendDiagnostic::UndecidedPredicate {
            predicate: predicate.clone(),
            reason,
        });
    }
}

pub fn simplify_predicate_with_solver(
    definition: &BackendDefinition,
    predicate: &Predicate,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Stoppable<Result<Predicate, SimplificationError>> {
    diagnostic::retract_dropped(
        || simplify_predicate(definition, predicate, known_predicates, options, solver),
        |result| {
            result
                .as_ref()
                .ok()
                .map(|simplified| Occurrences::of([], [simplified]))
        },
    )
    .layered()
}

fn simplify_predicate(
    definition: &BackendDefinition,
    predicate: &Predicate,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> SimplifyResult<Predicate> {
    let mut remaining = options.max_iterations;
    let active_conditions = BTreeSet::new();
    let known_index = predicate_conjunct_index(known_predicates);
    let path_condition = PathConditionReplacements::new(known_predicates);
    let assumptions = PredicateAssumptions {
        terms: TermAssumptions {
            predicates: known_predicates,
            path_condition: &path_condition,
        },
        conjuncts: &known_index,
        excluded: None,
    };
    simplify_predicate_with_budget(
        definition,
        predicate,
        &assumptions,
        options.max_iterations,
        &mut remaining,
        &active_conditions,
        solver,
    )
}

/// Simplify a standalone predicate and ask SMT whether the residual is globally true or false.
pub fn simplify_and_decide_predicate_with_solver(
    definition: &BackendDefinition,
    predicate: &Predicate,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Stoppable<Result<Predicate, SimplificationError>> {
    diagnostic::retract_dropped(
        || simplify_and_decide_predicate(definition, predicate, known_predicates, options, solver),
        |result| {
            result
                .as_ref()
                .ok()
                .map(|decided| Occurrences::of([], [decided]))
        },
    )
    .layered()
}

fn simplify_and_decide_predicate(
    definition: &BackendDefinition,
    predicate: &Predicate,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> SimplifyResult<Predicate> {
    let simplified = simplify_predicate(definition, predicate, known_predicates, options, solver)?;
    if matches!(simplified, Predicate::True | Predicate::False) {
        return Ok(simplified);
    }
    match decide_condition(std::slice::from_ref(&simplified), known_predicates, solver)? {
        Ok(RuleCondition::Satisfied) => Ok(Predicate::True),
        Ok(RuleCondition::Refuted) => Ok(Predicate::False),
        Ok(RuleCondition::Indeterminate(reason)) => {
            report_undecided_predicate(&simplified, reason);
            Ok(simplified)
        }
        Err(error) => Err(SimplificationError::SmtPredicate {
            predicate: Box::new(simplified),
            error,
        }
        .into()),
    }
}

/// Decompose equality of two applications of one free constructor, or one equation head
/// whose applications are certified normal forms and whose role excludes algebraic facts, with equal
/// sort arguments and arity, when unary or one side is provably defined.
/// With one side defined, the images are equal exactly when their argument patterns are;
/// a unary image also preserves emptiness. For an n-ary symbol with both sides possibly
/// empty this is inexact: `c(\bottom, 1) = c(\bottom, 2)` is true although `1 = 2` is false.
/// Flatten eligible nested applications before re-simplifying the leaf conjunction once.
/// A defined image has defined arguments on that same side; unary decomposition alone
/// does not establish definedness, so a nested n-ary pair still needs its own witness.
fn decompose_free_application(
    left: &Term,
    right: &Term,
    defined: impl Fn(&Term) -> bool,
) -> Option<Predicate> {
    let mut pending = vec![(left, right, false, false)];
    let mut equalities = Vec::new();
    let mut decomposed = false;
    while let Some((left, right, left_defined, right_defined)) = pending.pop() {
        if let (Head::Fixed(left_head), Head::Fixed(right_head)) = (
            classify_value(left, &mut CertifiedOnly),
            classify_value(right, &mut CertifiedOnly),
        ) && let RootComparison::SameApplication(same) = compare_roots(left_head, right_head)
        {
            let unary = same.pairs().count() == 1;
            let left_defined = left_defined || (!unary && !right_defined && defined(left));
            let right_defined = right_defined || (!unary && !left_defined && defined(right));
            if unary || left_defined || right_defined {
                decomposed = true;
                let start = pending.len();
                pending.extend(
                    same.pairs()
                        .filter(|(left, right)| left != right)
                        .map(|(left, right)| (left, right, left_defined, right_defined)),
                );
                // Visit arguments in their original order with the LIFO work list.
                pending[start..].reverse();
                continue;
            }
        }
        if !decomposed {
            return None;
        }
        equalities.push(Predicate::Equals(left.clone(), right.clone()));
    }
    Some(match equalities.len() {
        0 => Predicate::True,
        1 => equalities.pop().unwrap(),
        _ => Predicate::And(equalities),
    })
}

fn simplify_predicate_with_budget(
    definition: &BackendDefinition,
    predicate: &Predicate,
    assumptions: &PredicateAssumptions<'_>,
    limit: usize,
    remaining: &mut usize,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
) -> SimplifyResult<Predicate> {
    let _apart = crate::rule::ApartScope::enter();
    stop::check()?;
    stop::check_stack()?;
    if assumptions.contains(predicate) {
        return Ok(Predicate::True);
    }
    if assumptions.contains(&Predicate::Not(Box::new(predicate.clone()))) {
        return Ok(Predicate::False);
    }
    let simplify_term = |term: &Term| {
        let mut term_remaining = *remaining;
        simplify_with_budget(
            definition,
            term,
            &assumptions.terms,
            SimplificationOptions {
                max_iterations: limit,
                budget: BudgetPolicy::Fail,
            },
            &mut term_remaining,
            active_conditions,
            solver,
            None,
        )
    };
    let simplified = match predicate {
        Predicate::True => Predicate::True,
        Predicate::False => Predicate::False,
        Predicate::Term(term) => {
            let simplified = simplify_term(term)?.into_parts();
            with_simplification_constraints(
                simplified.conditions.into_predicates(),
                Predicate::Term(simplified.term),
            )
        }
        Predicate::Equals(left, right) => {
            let simplified_left = simplify_term(left)?;
            let simplified_right = simplify_term(right)?;
            // A side rewritten to `C /\ l'` is used, with `C` conjoined, only when the other
            // side is provably defined: `\equals(C /\ l', r)` is `C /\ \equals(l', r)` when
            // `r` is not empty and `\not \ceil(r)` when `C` fails and `r` is empty, since
            // `\equals(\bottom, \bottom)` is `\top`. The other side is witnessed by its own
            // rewritten term when that carried no constraint (the two are equal) and by its
            // original term otherwise. A side that fails the check stays as it was.
            let provably_defined = |term: &Term| {
                term_is_provably_defined(definition, term, |obligation| {
                    assumptions.contains(obligation)
                })
            };
            let witness = |original: &'_ Term, simplified: &'_ Simplification| -> Term {
                if simplified.conditions().is_empty() {
                    simplified.term.clone()
                } else {
                    original.clone()
                }
            };
            let use_left = simplified_left.conditions().is_empty()
                || provably_defined(&witness(right, &simplified_right));
            let use_right = simplified_right.conditions().is_empty()
                || provably_defined(&witness(left, &simplified_left));
            let mut constraints = Vec::new();
            let left = if use_left {
                let simplified_left = simplified_left.into_parts();
                constraints.extend(simplified_left.conditions);
                simplified_left.term
            } else {
                left.clone()
            };
            let right = if use_right {
                let simplified_right = simplified_right.into_parts();
                constraints.extend(simplified_right.conditions);
                simplified_right.term
            } else {
                right.clone()
            };
            let equality =
                normalize_hooked_boolean_predicate(definition, Predicate::Equals(left, right));
            let equality = normalize_injection_equality(definition, equality);
            let equality = match equality {
                Predicate::Equals(left, right) => {
                    let (equality, resimplify) =
                        match terms_apart(Some(definition.sort_graph()), &left, &right) {
                            // R-eq: disjoint denotations are equal exactly where both are empty;
                            // a provably defined side makes that condition false.
                            Some(apart) => {
                                let equality = apart.equality(left, right, provably_defined);
                                let resimplify = matches!(equality, Predicate::And(_));
                                (equality, resimplify)
                            }
                            // Decomposition is an equivalence, so with the budget spent
                            // the equality is kept as it is.
                            None if *remaining > 0 => {
                                match decompose_free_application(&left, &right, provably_defined) {
                                    Some(decomposed) => (decomposed, true),
                                    None => (Predicate::Equals(left, right), false),
                                }
                            }
                            None => (Predicate::Equals(left, right), false),
                        };
                    if resimplify {
                        // Re-enter under the same budget so negated ceils reach ceil theory
                        // and argument equalities reach injection and path-condition theory.
                        let conjunction = with_simplification_constraints(constraints, equality);
                        if *remaining == 0 {
                            return Err(SimplificationError::PredicateIterationLimit {
                                limit,
                                predicate: conjunction,
                            }
                            .into());
                        }
                        *remaining -= 1;
                        return simplify_predicate_with_budget(
                            definition,
                            &conjunction,
                            assumptions,
                            limit,
                            remaining,
                            active_conditions,
                            solver,
                        );
                    }
                    equality
                }
                equality => equality,
            };
            with_simplification_constraints(constraints, equality)
        }
        Predicate::Ceil(term) => {
            let simplified = simplify_term(term)?.into_parts();
            let unchanged = Predicate::Ceil(simplified.term.clone());
            let mut expanded = ceil_term(definition, &simplified.term);
            // An opaque parent ceil remains a conjunct after expansion. Do not repeatedly
            // add child ceils already supplied by the surrounding conjunction.
            expanded.retain(|predicate| !assumptions.contains(predicate));
            if expanded.as_slice() == [unchanged.clone()] {
                with_simplification_constraints(simplified.conditions.into_predicates(), unchanged)
            } else {
                // The expansion supplies the definedness of the subterms as sibling conjuncts,
                // and a conditional ceil equation on the parent is decided under them only by
                // a further pass over the conjunction. Take that pass here, so that an entry
                // without a surrounding conjunction fixed point reaches the equation too.
                let mut constraints = simplified.conditions.into_predicates();
                constraints.extend(expanded);
                let conjunction = Predicate::And(constraints);
                if *remaining == 0 {
                    return Err(SimplificationError::PredicateIterationLimit {
                        limit,
                        predicate: conjunction,
                    }
                    .into());
                }
                *remaining -= 1;
                return simplify_predicate_with_budget(
                    definition,
                    &conjunction,
                    assumptions,
                    limit,
                    remaining,
                    active_conditions,
                    solver,
                );
            }
        }
        Predicate::Floor(term) => {
            let simplified = simplify_term(term)?;
            // `\floor(C /\ t')` is `\not C \/ \floor(t')`, not `C /\ \floor(t')`, because
            // `\floor(\bottom)` is `\top`; a rewrite that carries constraints is not used.
            if simplified.conditions().is_empty() {
                Predicate::Floor(simplified.term)
            } else {
                Predicate::Floor(term.clone())
            }
        }
        Predicate::In(left, right) => {
            let left = simplify_term(left)?.into_parts();
            let right = simplify_term(right)?.into_parts();
            let mut constraints = left.conditions.into_predicates();
            constraints.extend(right.conditions);
            with_simplification_constraints(constraints, Predicate::In(left.term, right.term))
        }
        Predicate::Absent(absence) => {
            // The absence is the definedness of its joined collection, whose value, if any, is
            // a variable: `ceil_term` of it states the same fact through the key and the rest
            // alone. Over an opaque rest that is the atom again beside the key's and the rest's
            // own obligations; over a rest that has become a collection with entries it is the
            // key's disequalities from those entries and its absence from their rest.
            let key = simplify_term(absence.key())?.into_parts();
            let rest = simplify_term(absence.rest())?.into_parts();
            let mut constraints = key.conditions.into_predicates();
            constraints.extend(rest.conditions);
            let simplified = Absence::predicate(absence.collection(), key.term, rest.term);
            let joined = match &simplified {
                Predicate::Absent(absence) => absence.joined(),
                Predicate::Ceil(joined) => joined,
                _ => unreachable!("an absence is an atom or the ceil of its joined set"),
            };
            let mut expanded = ceil_term(definition, joined);
            // As for `\ceil` above: an opaque atom remains a conjunct of its expansion.
            expanded.retain(|predicate| !assumptions.contains(predicate));
            if expanded.as_slice() == std::slice::from_ref(&simplified) {
                with_simplification_constraints(constraints, simplified)
            } else {
                constraints.extend(expanded);
                let conjunction = Predicate::And(constraints);
                if *remaining == 0 {
                    return Err(SimplificationError::PredicateIterationLimit {
                        limit,
                        predicate: conjunction,
                    }
                    .into());
                }
                *remaining -= 1;
                return simplify_predicate_with_budget(
                    definition,
                    &conjunction,
                    assumptions,
                    limit,
                    remaining,
                    active_conditions,
                    solver,
                );
            }
        }
        Predicate::Not(inner) => {
            let mut inner_remaining = *remaining;
            Predicate::Not(Box::new(simplify_predicate_with_budget(
                definition,
                inner,
                assumptions,
                limit,
                &mut inner_remaining,
                active_conditions,
                solver,
            )?))
        }
        Predicate::And(inner) => {
            let mut inner_remaining = *remaining;
            let inner = simplify_predicates_with_budget(
                definition,
                inner,
                assumptions.terms.predicates,
                limit,
                &mut inner_remaining,
                active_conditions,
                solver,
            )?;
            Predicate::And(inner)
        }
        Predicate::Or(inner) => {
            let inner = inner
                .iter()
                .map(|predicate| {
                    let mut predicate_remaining = *remaining;
                    simplify_predicate_with_budget(
                        definition,
                        predicate,
                        assumptions,
                        limit,
                        &mut predicate_remaining,
                        active_conditions,
                        solver,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?;
            Predicate::Or(inner)
        }
        Predicate::Implies(left, right) | Predicate::Iff(left, right) => {
            let mut left_remaining = *remaining;
            let left = simplify_predicate_with_budget(
                definition,
                left,
                assumptions,
                limit,
                &mut left_remaining,
                active_conditions,
                solver,
            )?;
            let mut right_remaining = *remaining;
            let right = simplify_predicate_with_budget(
                definition,
                right,
                assumptions,
                limit,
                &mut right_remaining,
                active_conditions,
                solver,
            )?;
            if matches!(predicate, Predicate::Implies(..)) {
                Predicate::Implies(Box::new(left), Box::new(right))
            } else {
                Predicate::Iff(Box::new(left), Box::new(right))
            }
        }
        Predicate::Exists(variable, inner) | Predicate::Forall(variable, inner) => {
            let mut inner_remaining = *remaining;
            // The quantifier shadows its variable: a fact about a free variable of the same
            // name is not a fact about the bound one, so the body is simplified without the
            // facts that mention that variable free. With the fact `X = a`, `\exists X.
            // \not(X = a)` would otherwise become `\bottom`.
            let unshadowed = UnshadowedAssumptions::under_binder(variable, assumptions);
            let unshadowed_view;
            let inner_assumptions = match &unshadowed {
                Some(unshadowed) => {
                    unshadowed_view = unshadowed.view();
                    &unshadowed_view
                }
                None => assumptions,
            };
            let inner = simplify_predicate_with_budget(
                definition,
                inner,
                inner_assumptions,
                limit,
                &mut inner_remaining,
                active_conditions,
                solver,
            )?;
            if matches!(predicate, Predicate::Exists(..)) {
                Predicate::Exists(variable.clone(), Box::new(inner))
            } else {
                Predicate::Forall(variable.clone(), Box::new(inner))
            }
        }
    };
    let simplified =
        normalize_predicate(normalize_hooked_boolean_predicate(definition, simplified));
    if assumptions.contains(&simplified) {
        return Ok(Predicate::True);
    }
    if assumptions.contains(&Predicate::Not(Box::new(simplified.clone()))) {
        return Ok(Predicate::False);
    }
    // The diagnostics of the indeterminate ceil and predicate equation attempts, committed only
    // if neither theory rewrites the predicate.
    let mut indeterminate = IndeterminateAttempts::default();
    if let Some(simplified) = apply_ceil_theory(
        definition,
        &simplified,
        assumptions.terms.predicates,
        SimplificationOptions {
            max_iterations: limit,
            budget: BudgetPolicy::Fail,
        },
        active_conditions,
        solver,
        &mut indeterminate,
    )? {
        if *remaining == 0 {
            return Err(SimplificationError::PredicateIterationLimit {
                limit,
                predicate: simplified,
            }
            .into());
        }
        *remaining -= 1;
        // Invariant: `remaining` was decremented just above, so nesting depth <= the budget.
        return simplify_predicate_with_budget(
            definition,
            &simplified,
            assumptions,
            limit,
            remaining,
            active_conditions,
            solver,
        );
    }
    let Some(simplified) = apply_predicate_theory(
        definition,
        &simplified,
        assumptions.terms.predicates,
        SimplificationOptions {
            max_iterations: limit,
            budget: BudgetPolicy::Fail,
        },
        active_conditions,
        solver,
        &mut indeterminate,
    )?
    else {
        indeterminate.commit(|| Subject::Predicate(simplified.clone()));
        return Ok(simplified);
    };
    if *remaining == 0 {
        return Err(SimplificationError::PredicateIterationLimit {
            limit,
            predicate: simplified,
        }
        .into());
    }
    *remaining -= 1;
    // Invariant: `remaining` was decremented just above, so nesting depth <= the budget.
    simplify_predicate_with_budget(
        definition,
        &simplified,
        assumptions,
        limit,
        remaining,
        active_conditions,
        solver,
    )
}

fn normalize_injection_equality(definition: &BackendDefinition, predicate: Predicate) -> Predicate {
    let Predicate::Equals(left, right) = predicate else {
        return predicate;
    };
    match match_injection_equality(Some(definition.sort_graph()), &left, &right) {
        Some(InjectionEquality::Direct(left, right) | InjectionEquality::Split(left, right)) => {
            normalize_hooked_boolean_predicate(definition, Predicate::Equals(left, right))
        }
        // Separated injections are apart; the caller reads that through `terms_apart`
        // (R-eq), which states the definedness a refutation requires.
        Some(InjectionEquality::Distinct | InjectionEquality::Unknown) | None => {
            Predicate::Equals(left, right)
        }
    }
}

/// Conjoin the constraints `C` a term simplification `t = C /\ t'` carried to the predicate
/// `p[t']` built from its rewritten term. The result equals `p[t]` only when `p` is strict in
/// that operand (`p[\bottom]` is `\bottom`), so that `p[C /\ t']` is `C /\ p[t']`: the `Term`,
/// `\ceil`, and `\in` arms of `simplify_predicate_with_budget` are strict and call this
/// unconditionally; the `\equals` arm calls it only for a side whose other side is provably
/// defined (`term_is_provably_defined`), and the `\floor` arm never does.
fn with_simplification_constraints(
    mut constraints: Vec<Predicate>,
    predicate: Predicate,
) -> Predicate {
    if constraints.is_empty() {
        predicate
    } else {
        constraints.push(predicate);
        Predicate::And(constraints)
    }
}

/// Rewrite `\ceil(t)` by the first ceil equation that applies, in priority order; `None` when
/// none does. The diagnostics of the indeterminate attempts are held in `indeterminate`, which
/// the caller commits if the predicate is kept.
#[allow(clippy::too_many_arguments)]
fn apply_ceil_theory(
    definition: &BackendDefinition,
    predicate: &Predicate,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
    indeterminate: &mut IndeterminateAttempts,
) -> SimplifyResult<Option<Predicate>> {
    let Predicate::Ceil(term) = predicate else {
        return Ok(None);
    };
    let groups = applicable_groups(definition.ceil_theory(), &term_index(term));
    for rules in groups.values() {
        match scan_group(rules, indeterminate, |rule| {
            apply_ceil_equation(
                definition,
                rule,
                term,
                known_predicates,
                options,
                active_conditions,
                solver,
            )
        })? {
            GroupScan::Applied(result) => return Ok(Some(result)),
            GroupScan::Blocked => return Ok(None),
            GroupScan::NotCacheable | GroupScan::NotApplicable => {}
        }
    }
    Ok(None)
}

fn apply_ceil_equation(
    definition: &BackendDefinition,
    rule: &RewriteRule,
    term: &Term,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
) -> SimplifyResult<EquationAttempt<Predicate, ()>> {
    if let Some((renamed, _)) = rename_apart(rule, &term.attributes().variables, known_predicates) {
        return apply_ceil_equation(
            definition,
            &renamed,
            term,
            known_predicates,
            options,
            active_conditions,
            solver,
        );
    }
    let substitution =
        match match_terms_in_definition(MatchMode::Evaluate, definition, &rule.lhs, term) {
            MatchResult::Failed(_) => return Ok(EquationAttempt::NotApplicable(())),
            MatchResult::Indeterminate {
                substitution,
                remainder,
            } => match match_collection_remainders_all_in_definition(
                MatchMode::Evaluate,
                definition,
                substitution,
                &remainder,
            ) {
                CollectionMatches::Solutions(solutions) => solutions
                    .into_iter()
                    .next()
                    .expect("collection solutions are never empty"),
                CollectionMatches::NoSolution(_) => return Ok(EquationAttempt::NotApplicable(())),
                CollectionMatches::Undecided => {
                    return Ok(EquationAttempt::Indeterminate(
                        ConditionIndeterminacy::ImplicationIndeterminate,
                    ));
                }
            },
            MatchResult::Success(substitution) => substitution,
        };
    if substitution
        .keys()
        .any(|variable| !rule.lhs.attributes().variables.contains(variable))
        || check_concreteness(rule, &substitution).is_some()
    {
        return Ok(EquationAttempt::NotApplicable(()));
    }
    if binds_element_variable_to_set_pattern(&substitution) {
        return Ok(EquationAttempt::Indeterminate(
            ConditionIndeterminacy::NonFunctionalBinding,
        ));
    }

    let instance = EquationInstance::new(definition, &rule.requires, substitution);
    let matched = match evaluate_equation_condition(
        definition,
        &rule.attributes.unique_id,
        &rule.computed_attributes.unbound_result_variables,
        &rule.computed_attributes.unbound_variables,
        Some(term),
        instance,
        known_predicates,
        options,
        active_conditions,
        solver,
    )? {
        EquationCondition::Satisfied(matched) => matched,
        EquationCondition::Refuted => return Ok(EquationAttempt::NotApplicable(())),
        EquationCondition::Indeterminate(reason) => {
            return Ok(EquationAttempt::Indeterminate(reason));
        }
    };

    let RuleRhs::Predicates(rhs) = &rule.rhs else {
        return Ok(EquationAttempt::NotApplicable(()));
    };
    // The subject `\ceil(f(t))` is strict in every term `t` bound to an element variable:
    // `\ceil(\bottom)` is `\bottom`. So `\ceil(f(t)) = \ceil(t) /\ q[t]` under the equation
    // `\ceil(f(X)) = q[X]`, an open obligation is conjoined to the result and a refuted one
    // makes the subject `\bottom`.
    let defined = match decide_equation_bindings(
        definition,
        &rule.attributes.unique_id,
        Some(term),
        matched,
        known_predicates,
        options,
        active_conditions,
        solver,
    )? {
        DecidedEquation::Defined(defined) => defined,
        DecidedEquation::Refuted(_) => return Ok(EquationAttempt::Applied(Predicate::False)),
    };
    Ok(EquationAttempt::Applied(normalize_predicate(
        Predicate::And(defined.into_result(rhs)),
    )))
}

/// Rewrite `predicate` by the first predicate equation that applies, in priority order; `None`
/// when none does. The diagnostics of the indeterminate attempts are held in `indeterminate`,
/// which the caller commits if the predicate is kept.
#[allow(clippy::too_many_arguments)]
fn apply_predicate_theory(
    definition: &BackendDefinition,
    predicate: &Predicate,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
    indeterminate: &mut IndeterminateAttempts,
) -> SimplifyResult<Option<Predicate>> {
    for rules in definition.predicate_simplification_theory().values() {
        match scan_group(rules, indeterminate, |rule| {
            apply_predicate_equation(
                definition,
                rule,
                predicate,
                known_predicates,
                options,
                active_conditions,
                solver,
            )
        })? {
            GroupScan::Applied(result) => return Ok(Some(result)),
            GroupScan::Blocked => return Ok(None),
            GroupScan::NotCacheable | GroupScan::NotApplicable => {}
        }
    }
    Ok(None)
}

fn apply_predicate_equation(
    definition: &BackendDefinition,
    rule: &PredicateRewriteRule,
    predicate: &Predicate,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
) -> SimplifyResult<EquationAttempt<Predicate, ()>> {
    if let Some((renamed, _)) = rename_predicate_rule_apart(rule, predicate, known_predicates) {
        return apply_predicate_equation(
            definition,
            &renamed,
            predicate,
            known_predicates,
            options,
            active_conditions,
            solver,
        );
    }
    // A left-hand side matches only a predicate of its own top-level connective
    // (`collect_predicate_term_pairs`), so an equation of another connective does not apply,
    // whatever the rest of the attempt would decide. The check follows the renaming, which a full
    // attempt makes too, so the `!apart` counter and the fresh names of later renamings do not
    // move. For the `\top` and `\bottom` subjects left by condition evaluation, most subjects
    // here, the renaming finds no clash from the cached variable sets and builds nothing.
    if !same_connective(&rule.lhs, predicate) {
        return Ok(EquationAttempt::NotApplicable(()));
    }
    let substitution = match match_predicate(definition, &rule.lhs, predicate) {
        PredicateMatch::Failed => return Ok(EquationAttempt::NotApplicable(())),
        PredicateMatch::Indeterminate => {
            return Ok(EquationAttempt::Indeterminate(
                ConditionIndeterminacy::ImplicationIndeterminate,
            ));
        }
        PredicateMatch::Success(substitution) => substitution,
    };
    if binds_element_variable_to_set_pattern(&substitution) {
        return Ok(EquationAttempt::Indeterminate(
            ConditionIndeterminacy::NonFunctionalBinding,
        ));
    }
    let instance = EquationInstance::new(definition, &rule.requires, substitution);
    let matched = match evaluate_equation_condition(
        definition,
        &rule.attributes.unique_id,
        &rule.unbound_result_variables,
        &rule.variables.unbound,
        first_predicate_term(predicate),
        instance,
        known_predicates,
        options,
        active_conditions,
        solver,
    )? {
        EquationCondition::Satisfied(matched) => matched,
        EquationCondition::Refuted => return Ok(EquationAttempt::NotApplicable(())),
        EquationCondition::Indeterminate(reason) => {
            return Ok(EquationAttempt::Indeterminate(reason));
        }
    };
    // The equation `p[X] = q[X] requires R[X]` is an axiom over every element `X`, and the
    // subject `p[t]` equals `\ceil(t) /\ q[t]` only when `p` is strict in `X`, that is
    // `p[\bottom]` is `\bottom`: a functional `t` is either empty, where the strict `p[t]` and
    // `\ceil(t)` are both `\bottom`, or one element, where the axiom applies. A predicate is
    // not strict in general: `\equals(\bottom, \bottom)`, `\floor(\bottom)`, and
    // `\not(\bottom)` are `\top`, so `{f(X) #Equals g(X)} = \top` on `{f(t) #Equals g(t)}`
    // with `t` empty has the subject `\top` where the conjoined form would be `\bottom`. An
    // open or refuted obligation is therefore used only when `p` is strict in every element
    // variable whose binding raised it (`strict_variables`); otherwise the attempt stays
    // indeterminate on an open obligation and does not apply on a refuted one.
    let obligated = obligated_variables(
        definition,
        matched.substitution(),
        matched.bindings().as_known(),
    );
    match decide_equation_bindings(
        definition,
        &rule.attributes.unique_id,
        first_predicate_term(predicate),
        matched,
        known_predicates,
        options,
        active_conditions,
        solver,
    )? {
        DecidedEquation::Defined(defined) => {
            if !defined.is_discharged() {
                let strict = strict_variables(
                    definition,
                    &rule.lhs,
                    defined.substitution(),
                    known_predicates,
                );
                if !obligated.is_subset(&strict) {
                    return Ok(EquationAttempt::Indeterminate(
                        ConditionIndeterminacy::ImplicationIndeterminate,
                    ));
                }
            }
            Ok(EquationAttempt::Applied(normalize_predicate(
                Predicate::And(defined.into_result(&rule.rhs)),
            )))
        }
        DecidedEquation::Refuted(substitution) => {
            let strict = strict_variables(definition, &rule.lhs, &substitution, known_predicates);
            if !obligated.is_subset(&strict) {
                return Ok(EquationAttempt::NotApplicable(()));
            }
            Ok(EquationAttempt::Applied(Predicate::False))
        }
    }
}

/// The element variables of `substitution` whose binding raised one of the obligations in
/// `definedness` (`BindingDefinedness::as_known`): those bound to a term that may be empty
/// under the path condition.
fn obligated_variables(
    definition: &BackendDefinition,
    substitution: &Substitution,
    definedness: &[Predicate],
) -> BTreeSet<Variable> {
    substitution
        .iter()
        .filter(|(variable, value)| {
            variable.kind == VariableKind::Element
                && ceil_term(definition, value)
                    .iter()
                    .any(|obligation| definedness.contains(obligation))
        })
        .map(|(variable, _)| variable.clone())
        .collect()
}

/// The variables of a predicate-equation left-hand side `lhs` in which `lhs` is strict under
/// the match `substitution`: those `X` with `lhs[X := \bottom]` equal to `\bottom`.
///
/// The set is a conservative under-approximation. A term is strict in every variable it
/// contains (applications, injections, collections, and `\and` are strict), so `\ceil` and
/// `\in` are strict in the variables of their operands, and `\equals(l, r)` is strict in the
/// variables of `l` when the instantiated `r` is provably defined, because
/// `\equals(\bottom, r)` is `\bottom` exactly when `r` is not empty, and symmetrically. A
/// conjunction is strict in the variables of any conjunct, a disjunction in the variables of
/// every disjunct. Every other shape is taken as strict in nothing: `\not`, `\floor`, and the
/// implications are not strict, and a term used as a predicate is left out for conservatism.
fn strict_variables(
    definition: &BackendDefinition,
    lhs: &Predicate,
    substitution: &Substitution,
    known_predicates: &[Predicate],
) -> BTreeSet<Variable> {
    let provably_defined = |side: &Term| {
        term_is_provably_defined(definition, &substitute(side, substitution), |obligation| {
            known_predicates.contains(obligation)
        })
    };
    match lhs {
        Predicate::Ceil(term) => term.attributes().variables.clone(),
        Predicate::In(left, right) => left
            .attributes()
            .variables
            .union(&right.attributes().variables)
            .cloned()
            .collect(),
        // The absence of an undefined key, or from an undefined rest, is false.
        Predicate::Absent(absence) => absence
            .key()
            .attributes()
            .variables
            .union(&absence.rest().attributes().variables)
            .cloned()
            .collect(),
        Predicate::Equals(left, right) => {
            let mut strict = BTreeSet::new();
            if provably_defined(right) {
                strict.extend(left.attributes().variables.iter().cloned());
            }
            if provably_defined(left) {
                strict.extend(right.attributes().variables.iter().cloned());
            }
            strict
        }
        Predicate::And(inner) => inner
            .iter()
            .flat_map(|predicate| {
                strict_variables(definition, predicate, substitution, known_predicates)
            })
            .collect(),
        Predicate::Or(inner) => {
            let mut strict = inner
                .iter()
                .map(|predicate| {
                    strict_variables(definition, predicate, substitution, known_predicates)
                })
                .collect::<Vec<_>>();
            let Some(mut intersection) = strict.pop() else {
                return BTreeSet::new();
            };
            for other in strict {
                intersection = intersection.intersection(&other).cloned().collect();
            }
            intersection
        }
        Predicate::True
        | Predicate::False
        | Predicate::Term(_)
        | Predicate::Floor(_)
        | Predicate::Not(_)
        | Predicate::Implies(..)
        | Predicate::Iff(..)
        | Predicate::Exists(..)
        | Predicate::Forall(..) => BTreeSet::new(),
    }
}

/// Whether `term` is provably defined under the path condition: every obligation `ceil_term`
/// derives for it is `known`. `ceil_term` derives nothing for a term built from constructors,
/// total symbols, domain values, and element variables. A term-level `\and` is the
/// intersection of its operands and has no definedness witness of its own (`Y /\ Z` over two
/// element variables is empty unless `Y = Z`), while `ceil_term` only collects its operands'
/// obligations, so a term that contains one anywhere is never provably defined here.
pub(crate) fn term_is_provably_defined(
    definition: &BackendDefinition,
    term: &Term,
    known: impl Fn(&Predicate) -> bool,
) -> bool {
    !contains_term_conjunction(term) && ceil_term(definition, term).iter().all(known)
}

/// Whether `term` contains a term-level `\and` anywhere.
fn contains_term_conjunction(term: &Term) -> bool {
    match term.kind() {
        TermKind::And(..) => true,
        TermKind::Application { arguments, .. } => arguments.iter().any(contains_term_conjunction),
        TermKind::Injection { term, .. } => contains_term_conjunction(term),
        TermKind::Map { entries, rest, .. } => {
            entries.iter().any(|(key, value)| {
                contains_term_conjunction(key) || contains_term_conjunction(value)
            }) || rest.as_ref().is_some_and(contains_term_conjunction)
        }
        TermKind::List { heads, rest, .. } => {
            heads.iter().any(contains_term_conjunction)
                || rest.as_ref().is_some_and(|(middle, tails)| {
                    contains_term_conjunction(middle) || tails.iter().any(contains_term_conjunction)
                })
        }
        TermKind::Set { elements, rest, .. } => {
            elements.iter().any(contains_term_conjunction)
                || rest.as_ref().is_some_and(contains_term_conjunction)
        }
        TermKind::DomainValue { .. } | TermKind::Variable(_) => false,
    }
}

enum PredicateMatch {
    Success(Substitution),
    Failed,
    Indeterminate,
}

/// Match a predicate equation's left-hand side against a predicate.
///
/// The two predicates must have one logical shape; their terms are matched as one problem.
/// Quantifiers are matched by scope. First every quantifier of either side gets its own fresh
/// variable (`rename_binders_apart`), distinct from every other variable of both sides, so a
/// bound variable shares its name with no free variable and no other binder, and an occurrence
/// of it is exactly an occurrence under its quantifier. Corresponding quantifiers relate their
/// variables: the rule's is matched as a pattern variable and must be bound to the subject's
/// exactly, and a binding of a free rule variable may not mention a subject quantifier's
/// variable, which would move that variable out of its scope. The quantifier variables'
/// bindings are not part of the result.
fn match_predicate(
    definition: &BackendDefinition,
    pattern: &Predicate,
    subject: &Predicate,
) -> PredicateMatch {
    let renamed;
    let (pattern, subject) = if has_quantifier(pattern) || has_quantifier(subject) {
        let mut variables = BTreeSet::new();
        crate::rule::collect_all_variables(&[pattern.clone(), subject.clone()], &mut variables);
        let mut avoid = variables
            .into_iter()
            .map(|variable| variable.name)
            .collect::<BTreeSet<_>>();
        let mut counter = 0;
        renamed = (
            rename_binders_apart(pattern, &mut avoid, &mut counter, &mut Vec::new()),
            rename_binders_apart(subject, &mut avoid, &mut counter, &mut Vec::new()),
        );
        (&renamed.0, &renamed.1)
    } else {
        (pattern, subject)
    };
    let mut pairs = Vec::new();
    let mut binders = Vec::new();
    if !collect_predicate_term_pairs(pattern, subject, &mut pairs, &mut binders) {
        return PredicateMatch::Failed;
    }
    match match_term_pairs_in_definition(
        MatchMode::Evaluate,
        definition,
        pairs
            .into_iter()
            .map(|(pattern, subject)| (pattern.clone(), subject.clone())),
    ) {
        MatchResult::Success(mut substitution) => {
            for (pattern_bound, subject_bound) in &binders {
                match substitution.remove(*pattern_bound) {
                    None => {}
                    Some(bound) if bound == Term::variable((*subject_bound).clone()) => {}
                    Some(_) => return PredicateMatch::Failed,
                }
            }
            if substitution.values().any(|value| {
                binders
                    .iter()
                    .any(|(_, bound)| value.attributes().variables.contains(*bound))
            }) {
                return PredicateMatch::Failed;
            }
            PredicateMatch::Success(substitution)
        }
        MatchResult::Failed(_) => PredicateMatch::Failed,
        MatchResult::Indeterminate { .. } => PredicateMatch::Indeterminate,
    }
}

fn has_quantifier(predicate: &Predicate) -> bool {
    match predicate {
        Predicate::Exists(..) | Predicate::Forall(..) => true,
        Predicate::Not(inner) => has_quantifier(inner),
        Predicate::And(inner) | Predicate::Or(inner) => inner.iter().any(has_quantifier),
        Predicate::Implies(left, right) | Predicate::Iff(left, right) => {
            has_quantifier(left) || has_quantifier(right)
        }
        Predicate::True
        | Predicate::False
        | Predicate::Term(_)
        | Predicate::Equals(..)
        | Predicate::Ceil(_)
        | Predicate::Floor(_)
        | Predicate::In(..)
        | Predicate::Absent(_) => false,
    }
}

/// `predicate` with each quantifier's variable renamed to `{name}!binder{counter}`, a name not
/// in `avoid` (which receives it), at the quantifier and at the occurrences it binds; `scope`
/// holds the renamings of the enclosing quantifiers, innermost last.
#[deny(
    clippy::wildcard_enum_match_arm,
    clippy::match_wildcard_for_single_variants
)]
fn rename_binders_apart(
    predicate: &Predicate,
    avoid: &mut BTreeSet<crate::term::Name>,
    counter: &mut u64,
    scope: &mut Vec<(Variable, Variable)>,
) -> Predicate {
    let term = |term: &Term, scope: &[(Variable, Variable)]| {
        if scope.is_empty() {
            return term.clone();
        }
        let renaming = scope
            .iter()
            .map(|(bound, fresh)| (bound.clone(), Term::variable(fresh.clone())))
            .collect::<Substitution>();
        substitute(term, &renaming)
    };
    let mut recurse = |inner: &Predicate, scope: &mut Vec<(Variable, Variable)>| {
        Box::new(rename_binders_apart(inner, avoid, counter, scope))
    };
    match predicate {
        Predicate::True => Predicate::True,
        Predicate::False => Predicate::False,
        Predicate::Term(inner) => Predicate::Term(term(inner, scope)),
        Predicate::Ceil(inner) => Predicate::Ceil(term(inner, scope)),
        Predicate::Floor(inner) => Predicate::Floor(term(inner, scope)),
        Predicate::Equals(left, right) => Predicate::Equals(term(left, scope), term(right, scope)),
        Predicate::In(left, right) => Predicate::In(term(left, scope), term(right, scope)),
        Predicate::Absent(absence) => absence.map_terms(|inner| term(inner, scope)),
        Predicate::Not(inner) => Predicate::Not(recurse(inner, scope)),
        Predicate::And(inner) => {
            Predicate::And(inner.iter().map(|inner| *recurse(inner, scope)).collect())
        }
        Predicate::Or(inner) => {
            Predicate::Or(inner.iter().map(|inner| *recurse(inner, scope)).collect())
        }
        Predicate::Implies(left, right) => {
            Predicate::Implies(recurse(left, scope), recurse(right, scope))
        }
        Predicate::Iff(left, right) => Predicate::Iff(recurse(left, scope), recurse(right, scope)),
        Predicate::Exists(bound, inner) | Predicate::Forall(bound, inner) => {
            // Invariant: `counter` only grows, so at most |avoid| + 1 names are tried.
            let name = loop {
                let name = crate::term::names::with_fresh_marker(
                    &bound.name,
                    crate::term::names::FreshMarker::Binder,
                    *counter,
                );
                *counter += 1;
                if avoid.insert(name.as_str().into()) {
                    break name;
                }
            };
            let fresh = bound.with_name(name);
            // The innermost binding of a name wins: `term` collects `scope` in order, so a
            // shadowing quantifier's entry overrides an enclosing one for its body only.
            scope.push((bound.clone(), fresh.clone()));
            let body = Box::new(rename_binders_apart(inner, avoid, counter, scope));
            scope.pop();
            if matches!(predicate, Predicate::Exists(..)) {
                Predicate::Exists(fresh, body)
            } else {
                Predicate::Forall(fresh, body)
            }
        }
    }
}

fn collect_predicate_term_pairs<'a>(
    pattern: &'a Predicate,
    subject: &'a Predicate,
    pairs: &mut Vec<(&'a Term, &'a Term)>,
    binders: &mut Vec<(&'a Variable, &'a Variable)>,
) -> bool {
    match (pattern, subject) {
        (Predicate::True, Predicate::True) | (Predicate::False, Predicate::False) => true,
        (Predicate::Term(left), Predicate::Term(right))
        | (Predicate::Ceil(left), Predicate::Ceil(right))
        | (Predicate::Floor(left), Predicate::Floor(right)) => {
            pairs.push((left, right));
            true
        }
        (Predicate::Equals(left_a, left_b), Predicate::Equals(right_a, right_b))
        | (Predicate::In(left_a, left_b), Predicate::In(right_a, right_b)) => {
            pairs.push((left_a, right_a));
            pairs.push((left_b, right_b));
            true
        }
        (Predicate::Absent(left), Predicate::Absent(right))
            if left.collection() == right.collection() =>
        {
            pairs.push((left.key(), right.key()));
            pairs.push((left.rest(), right.rest()));
            true
        }
        (Predicate::Not(left), Predicate::Not(right)) => {
            collect_predicate_term_pairs(left, right, pairs, binders)
        }
        (Predicate::And(left), Predicate::And(right))
        | (Predicate::Or(left), Predicate::Or(right))
            if left.len() == right.len() =>
        {
            left.iter()
                .zip(right)
                .all(|(left, right)| collect_predicate_term_pairs(left, right, pairs, binders))
        }
        (Predicate::Implies(left_a, left_b), Predicate::Implies(right_a, right_b))
        | (Predicate::Iff(left_a, left_b), Predicate::Iff(right_a, right_b)) => {
            collect_predicate_term_pairs(left_a, right_a, pairs, binders)
                && collect_predicate_term_pairs(left_b, right_b, pairs, binders)
        }
        (Predicate::Exists(left_var, left), Predicate::Exists(right_var, right))
        | (Predicate::Forall(left_var, left), Predicate::Forall(right_var, right))
            if left_var.kind == right_var.kind && left_var.sort == right_var.sort =>
        {
            binders.push((left_var, right_var));
            collect_predicate_term_pairs(left, right, pairs, binders)
        }
        _ => false,
    }
}

/// Whether `pattern` and `subject` have one top-level connective, the first thing
/// `collect_predicate_term_pairs` requires of them.
fn same_connective(pattern: &Predicate, subject: &Predicate) -> bool {
    std::mem::discriminant(pattern) == std::mem::discriminant(subject)
}

fn first_predicate_term(predicate: &Predicate) -> Option<&Term> {
    match predicate {
        Predicate::True | Predicate::False => None,
        Predicate::Term(term) | Predicate::Ceil(term) | Predicate::Floor(term) => Some(term),
        Predicate::Equals(left, _) | Predicate::In(left, _) => Some(left),
        Predicate::Absent(absence) => Some(absence.key()),
        Predicate::Not(inner) | Predicate::Exists(_, inner) | Predicate::Forall(_, inner) => {
            first_predicate_term(inner)
        }
        Predicate::And(inner) | Predicate::Or(inner) => inner.iter().find_map(first_predicate_term),
        Predicate::Implies(left, right) | Predicate::Iff(left, right) => {
            first_predicate_term(left).or_else(|| first_predicate_term(right))
        }
    }
}

/// Apply symbolic BOOL and `K-EQUAL-KORE` equations directly to predicate IR.
///
/// The frontend represents K operands as singleton K sequences, while collection definedness
/// compares their underlying KItems. Lowering both to the item makes those logically identical
/// conditions share one internal representation. The ceil obligations retain strictness: a
/// Boolean result from K equality implies that both operands were defined.
fn normalize_hooked_boolean_predicate(
    definition: &BackendDefinition,
    predicate: Predicate,
) -> Predicate {
    if let Predicate::Term(term) = &predicate {
        let normalized = normalize_hooked_boolean_predicate(
            definition,
            Predicate::Equals(
                term.clone(),
                Term::domain_value(Sort::builtin(BuiltinSort::Bool), "true"),
            ),
        );
        return match &normalized {
            Predicate::Equals(left, right) if left == term && bool_value(right) == Some(true) => {
                Predicate::Term(term.clone())
            }
            _ => normalized,
        };
    }
    let Predicate::Equals(left, right) = predicate else {
        return predicate;
    };
    let (application, value) = if let Some(value) = bool_value(&right) {
        (&left, value)
    } else if let Some(value) = bool_value(&left) {
        (&right, value)
    } else {
        return Predicate::Equals(left, right);
    };
    let TermKind::Application {
        symbol, arguments, ..
    } = application.kind()
    else {
        return boolean_literal_equality(application, value)
            .unwrap_or(Predicate::Equals(left, right));
    };
    if let Some(operator) = symbol.attributes.hook.as_deref() {
        let bool_operand = |term: &Term, value| {
            normalize_hooked_boolean_predicate(
                definition,
                Predicate::Equals(
                    term.clone(),
                    Term::domain_value(
                        Sort::builtin(BuiltinSort::Bool),
                        if value { "true" } else { "false" },
                    ),
                ),
            )
        };
        match (operator, arguments.as_slice()) {
            ("BOOL.and", [first, second]) => {
                let operands = vec![bool_operand(first, value), bool_operand(second, value)];
                return normalize_predicate(if value {
                    Predicate::And(operands)
                } else {
                    Predicate::Or(operands)
                });
            }
            ("BOOL.or", [first, second]) => {
                let operands = vec![bool_operand(first, value), bool_operand(second, value)];
                return normalize_predicate(if value {
                    Predicate::Or(operands)
                } else {
                    Predicate::And(operands)
                });
            }
            ("BOOL.not", [operand]) => return bool_operand(operand, !value),
            _ => {}
        }
    }
    let (negate, unwrap_k_sequence) = match symbol.attributes.hook.as_deref() {
        Some("KEQUAL.eq") => (!value, true),
        Some("KEQUAL.ne") => (value, true),
        Some("INT.eq") => (!value, false),
        Some("INT.ne") => (value, false),
        _ => {
            return boolean_literal_equality(application, value)
                .unwrap_or(Predicate::Equals(left, right));
        }
    };
    let [left_operand, right_operand] = arguments.as_slice() else {
        return Predicate::Equals(left, right);
    };
    let (left_operand, right_operand) = if unwrap_k_sequence {
        let (Some(left_operand), Some(right_operand)) = (
            k_sequence_item(left_operand),
            k_sequence_item(right_operand),
        ) else {
            return Predicate::Equals(left, right);
        };
        let Some(aligned) = align_subsort_operands(definition, left_operand, right_operand) else {
            return Predicate::Equals(left, right);
        };
        aligned
    } else {
        (left_operand.clone(), right_operand.clone())
    };
    let equality = Predicate::Equals(left_operand.clone(), right_operand.clone());
    let condition = if negate {
        Predicate::Not(Box::new(equality))
    } else {
        equality
    };
    let mut predicates = ceil_term(definition, &left_operand);
    predicates.extend(ceil_term(definition, &right_operand));
    predicates.push(condition);
    normalize_predicate(Predicate::And(predicates))
}

fn boolean_literal_equality(term: &Term, value: bool) -> Option<Predicate> {
    if !term.sort().is_builtin(BuiltinSort::Bool) || bool_value(term).is_some() {
        return None;
    }
    Some(if value {
        Predicate::Term(term.clone())
    } else {
        Predicate::Not(Box::new(Predicate::Term(term.clone())))
    })
}

fn align_subsort_operands(
    definition: &BackendDefinition,
    left: &Term,
    right: &Term,
) -> Option<(Term, Term)> {
    let left_sort = left.sort();
    let right_sort = right.sort();
    if left_sort == right_sort {
        return Some((left.clone(), right.clone()));
    }
    if definition
        .sort_graph()
        .check_subsort(&left_sort, &right_sort)
        .ok()?
    {
        return Some((
            Term::injection(left_sort, right_sort, left.clone()),
            right.clone(),
        ));
    }
    if definition
        .sort_graph()
        .check_subsort(&right_sort, &left_sort)
        .ok()?
    {
        return Some((
            left.clone(),
            Term::injection(right_sort, left_sort, right.clone()),
        ));
    }
    None
}

fn bool_value(term: &Term) -> Option<bool> {
    let TermKind::DomainValue { sort, value } = term.kind() else {
        return None;
    };
    if !sort.is_builtin(BuiltinSort::Bool) {
        return None;
    }
    match value.as_utf8().ok()? {
        "true" => Some(true),
        "false" => Some(false),
        _ => None,
    }
}

pub(crate) fn normalize_predicate(predicate: Predicate) -> Predicate {
    match predicate {
        Predicate::Equals(left, right) => {
            match predicates_truth(&[Predicate::Equals(left.clone(), right.clone())]) {
                Truth::True => Predicate::True,
                Truth::False => Predicate::False,
                Truth::Unknown => Predicate::Equals(left, right),
            }
        }
        Predicate::Not(inner) => match *inner {
            Predicate::True => Predicate::False,
            Predicate::False => Predicate::True,
            Predicate::Not(inner) => *inner,
            Predicate::And(inner) => Predicate::Not(Box::new(Predicate::And(inner))),
            Predicate::Or(inner) => normalize_predicate(Predicate::And(
                inner
                    .into_iter()
                    .map(|predicate| Predicate::Not(Box::new(predicate)))
                    .collect(),
            )),
            inner => match predicates_truth(std::slice::from_ref(&inner)) {
                Truth::True => Predicate::False,
                Truth::False => Predicate::True,
                Truth::Unknown => Predicate::Not(Box::new(inner)),
            },
        },
        Predicate::And(inner) => {
            let mut normalized = Vec::new();
            for predicate in inner {
                match normalize_predicate(predicate) {
                    Predicate::True => {}
                    Predicate::False => return Predicate::False,
                    Predicate::And(nested) => {
                        for predicate in nested {
                            if !normalized.contains(&predicate) {
                                normalized.push(predicate);
                            }
                        }
                    }
                    predicate if !normalized.contains(&predicate) => normalized.push(predicate),
                    _ => {}
                }
            }
            match normalized.len() {
                0 => Predicate::True,
                1 => normalized.pop().unwrap(),
                _ => Predicate::And(normalized),
            }
        }
        Predicate::Or(inner) => {
            let mut normalized = Vec::new();
            for predicate in inner {
                match normalize_predicate(predicate) {
                    Predicate::False => {}
                    Predicate::True => return Predicate::True,
                    Predicate::Or(nested) => normalized.extend(nested),
                    predicate => normalized.push(predicate),
                }
            }
            match normalized.len() {
                0 => Predicate::False,
                1 => normalized.pop().unwrap(),
                _ => Predicate::Or(normalized),
            }
        }
        Predicate::Implies(left, right) => match (
            predicates_truth(std::slice::from_ref(&left)),
            predicates_truth(std::slice::from_ref(&right)),
        ) {
            (Truth::False, _) | (_, Truth::True) => Predicate::True,
            (Truth::True, Truth::False) => Predicate::False,
            (Truth::True, Truth::Unknown) => *right,
            (Truth::Unknown, Truth::False) => normalize_predicate(Predicate::Not(left)),
            _ => Predicate::Implies(left, right),
        },
        Predicate::Iff(left, right) => match (
            predicates_truth(std::slice::from_ref(&left)),
            predicates_truth(std::slice::from_ref(&right)),
        ) {
            (Truth::True, Truth::True) | (Truth::False, Truth::False) => Predicate::True,
            (Truth::True, Truth::False) | (Truth::False, Truth::True) => Predicate::False,
            (Truth::True, Truth::Unknown) => *right,
            (Truth::Unknown, Truth::True) => *left,
            (Truth::False, Truth::Unknown) => normalize_predicate(Predicate::Not(right)),
            (Truth::Unknown, Truth::False) => normalize_predicate(Predicate::Not(left)),
            _ => Predicate::Iff(left, right),
        },
        Predicate::Exists(_, ref inner) | Predicate::Forall(_, ref inner)
            if predicates_truth(std::slice::from_ref(inner)) == Truth::True =>
        {
            Predicate::True
        }
        Predicate::Exists(_, ref inner) | Predicate::Forall(_, ref inner)
            if predicates_truth(std::slice::from_ref(inner)) == Truth::False =>
        {
            Predicate::False
        }
        predicate => match predicates_truth(std::slice::from_ref(&predicate)) {
            Truth::True => Predicate::True,
            Truth::False => Predicate::False,
            Truth::Unknown => predicate,
        },
    }
}

#[allow(clippy::too_many_arguments)]
fn simplify_with_budget(
    definition: &BackendDefinition,
    term: &Term,
    assumptions: &TermAssumptions<'_>,
    options: SimplificationOptions,
    remaining: &mut usize,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
    mut execution: Option<&mut ExecutionEvaluationContext>,
) -> SimplifyResult<Simplification> {
    let mut term = term.clone();
    let mut accumulated = Accumulated::default();
    // The last equation applied in this lineage to an application of a `total` symbol, before
    // any undefined term appeared: an undefined term reached afterwards lies in that equation's
    // result, whose arguments were defined when it fired (`ContradictedTotal`).
    let mut total_step: Option<(Term, Arc<RewriteRule>)> = None;
    // Each round simplifies the children then the root; the loop exits on a fixed point, an
    // `evaluated` term, an exhausted budget, or a child's exhaustion; `remaining` never grows.
    // Invariant: `term` equals the input modulo `applied_rules` under the accumulated conditions.
    loop {
        measure::bump(Counter::SimplifyRounds);
        // Neither the request's cancellation nor the step's deadline is bounded by the iteration
        // budget, which counts rewrites of one lineage rather than time, so every round polls.
        stop::check()?;
        stop::check_stack()?;
        if term.attributes().evaluated && !assumptions.path_condition.can_change(&term) {
            measure::bump(Counter::SimplifyNodesSkippedEvaluated);
            return Ok(accumulated.finish(term));
        }
        term = assumptions.path_condition.apply(&term);
        if term.attributes().evaluated {
            measure::bump(Counter::SimplifyNodesSkippedEvaluated);
            return Ok(accumulated.finish(term));
        }
        let children = simplify_children(
            definition,
            &term,
            assumptions,
            options,
            remaining,
            active_conditions,
            solver,
            execution.as_deref_mut(),
        )?;
        let (root, root_step, root_equation) = simplify_root(
            definition,
            &children.term,
            assumptions.predicates,
            options,
            active_conditions,
            solver,
            execution.as_deref_mut(),
        )?;
        let children = accumulated.absorb(children);
        let root = accumulated.absorb(root);
        if accumulated.undefined_term.is_none() {
            // A child's own report comes first: it names the innermost equation. Otherwise the
            // undefined term arose in this lineage, after the last `total` step if there was one.
            // The root step of this round is not that step's cause: an equation's result carries
            // no undefined term, so a root report comes from a builtin or a repeated collection.
            let (undefined, contradicted) = match children.undefined_term {
                Some(term) => (Some(term), children.contradicted_total),
                None => (root.undefined_term, None),
            };
            if let Some(undefined) = &undefined {
                accumulated.contradicted_total = contradicted.or_else(|| {
                    total_step.as_ref().map(|(application, rule)| {
                        ContradictedTotal::new(application.clone(), rule, undefined.clone())
                    })
                });
            }
            accumulated.undefined_term = undefined;
        }
        if accumulated.undefined_term.is_none()
            && let Some(rule) = root_equation
            && is_total_application(&children.term)
        {
            total_step = Some((children.term.clone(), rule));
        }
        if root.term.ptr_eq(&children.term)
            || root.term == children.term
            || root.term.attributes().evaluated
        {
            return Ok(accumulated.finish(root.term));
        }
        // A determined function step is the definition's own computation, not a rewrite the
        // simplifier chose, so it neither needs nor consumes budget (`RootStep`).
        let charged = root_step != RootStep::DeterminedFunctionStep;
        if charged && *remaining == 0 {
            return match options.budget {
                BudgetPolicy::Fail => Err(SimplificationError::IterationLimit {
                    limit: options.max_iterations,
                    term: root.term,
                }
                .into()),
                BudgetPolicy::KeepPartial => {
                    accumulated.exhausted = Some(BudgetExhaustion {
                        limit: options.max_iterations,
                        subject: BudgetSubject::Term,
                    });
                    Ok(accumulated.finish(root.term))
                }
            };
        }
        if accumulated.exhausted.is_some() {
            return Ok(accumulated.finish(root.term));
        }
        if charged {
            *remaining -= 1;
        }
        term = root.term;
    }
}

struct PathConditionReplacements {
    substitution: Substitution,
    replacements: Vec<(Term, Term)>,
}

impl PathConditionReplacements {
    fn new(predicates: &[Predicate]) -> Self {
        let mut equalities = Vec::new();
        collect_conjunctive_equalities(predicates, &mut equalities);
        Self::from_equalities(equalities)
    }

    fn from_equalities<'a>(equalities: impl IntoIterator<Item = (&'a Term, &'a Term)>) -> Self {
        let mut substitution = Substitution::new();
        let mut replacements = Vec::new();
        for (left, right) in equalities {
            let binding = match (left.kind(), right.kind()) {
                (TermKind::Variable(variable), _) => Some((variable, right)),
                (_, TermKind::Variable(variable)) => Some((variable, left)),
                _ => None,
            };
            if let Some((variable, replacement)) = binding {
                let replacement = substitute(replacement, &substitution);
                if !replacement.attributes().variables.contains(variable) {
                    let binding = Substitution::from([(variable.clone(), replacement)]);
                    substitution = compose(&binding, &substitution);
                }
            } else if is_scalar_domain_value(left) {
                replacements.push((right.clone(), left.clone()));
            } else if is_scalar_domain_value(right) {
                replacements.push((left.clone(), right.clone()));
            }
        }
        let replacements = replacements
            .into_iter()
            .map(|(original, replacement)| {
                (
                    substitute(&original, &substitution),
                    substitute(&replacement, &substitution),
                )
            })
            .collect::<Vec<_>>();
        Self {
            substitution,
            replacements,
        }
    }

    fn apply(&self, term: &Term) -> Term {
        if self.substitution.is_empty() && self.replacements.is_empty() {
            return term.clone();
        }
        let term = substitute(term, &self.substitution);
        if self.replacements.is_empty() {
            return term;
        }
        replace_terms_bottom_up(&term, &self.replacements)
    }

    fn can_change(&self, term: &Term) -> bool {
        term.attributes()
            .variables
            .iter()
            .any(|variable| self.substitution.contains_key(variable))
            || (!self.replacements.is_empty()
                && term_contains_replacement_original(term, &self.replacements))
    }
}

fn owned_equalities(equalities: Vec<(&Term, &Term)>) -> Vec<(Term, Term)> {
    equalities
        .into_iter()
        .map(|(left, right)| (left.clone(), right.clone()))
        .collect()
}

fn collect_conjunctive_equalities<'a>(
    predicates: &'a [Predicate],
    equalities: &mut Vec<(&'a Term, &'a Term)>,
) {
    for predicate in predicates {
        match predicate {
            Predicate::Equals(left, right) => equalities.push((left, right)),
            Predicate::And(inner) => collect_conjunctive_equalities(inner, equalities),
            _ => {}
        }
    }
}

fn is_scalar_domain_value(term: &Term) -> bool {
    matches!(
        term.kind(),
        TermKind::DomainValue { sort, .. }
            if sort.is_builtin(BuiltinSort::Int)
                || sort.is_builtin(BuiltinSort::Bool)
    )
}

fn replace_terms_bottom_up(term: &Term, replacements: &[(Term, Term)]) -> Term {
    let rebuilt = term
        .try_map_children(|child| {
            Ok::<_, std::convert::Infallible>(replace_terms_bottom_up(child, replacements))
        })
        .expect("an infallible term transformation cannot fail");
    replacements
        .iter()
        .find_map(|(original, replacement)| (original == &rebuilt).then(|| replacement.clone()))
        .unwrap_or(rebuilt)
}

fn term_contains_replacement_original(term: &Term, replacements: &[(Term, Term)]) -> bool {
    let mut pending = vec![term];
    // Invariant: no popped subterm equals an original in `replacements`, and `pending` holds unexamined subterm occurrences of `term`; each pop pushes only its direct children, so each occurrence is popped at most once.
    while let Some(term) = pending.pop() {
        if replacements.iter().any(|(original, _)| original == term) {
            return true;
        }
        match term.kind() {
            TermKind::And(left, right) => pending.extend([left, right]),
            TermKind::Application { arguments, .. } => pending.extend(arguments),
            TermKind::Injection { term, .. } => pending.push(term),
            TermKind::Map { entries, rest, .. } => {
                pending.extend(entries.iter().flat_map(|(key, value)| [key, value]));
                pending.extend(rest);
            }
            TermKind::List { heads, rest, .. } => {
                pending.extend(heads);
                if let Some((middle, tails)) = rest {
                    pending.push(middle);
                    pending.extend(tails);
                }
            }
            TermKind::Set { elements, rest, .. } => {
                pending.extend(elements);
                pending.extend(rest);
            }
            TermKind::DomainValue { .. } | TermKind::Variable(_) => {}
        }
    }
    false
}

fn matches_top_equation(
    definition: &BackendDefinition,
    term: &Term,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
) -> SimplifyResult<Option<(String, Vec<Predicate>)>> {
    for rules in applicable_groups(definition.simplification_theory(), &term_index(term)).values() {
        for rule in rules {
            if !matches!(rule.rhs, RuleRhs::Top) {
                continue;
            }
            let renamed = rename_apart(rule, &term.attributes().variables, known_predicates);
            let rule = renamed.as_ref().map_or(&**rule, |(renamed, _)| renamed);
            let substitution =
                match match_terms_in_definition(MatchMode::Evaluate, definition, &rule.lhs, term) {
                    MatchResult::Failed(_) => continue,
                    MatchResult::Indeterminate {
                        substitution,
                        remainder,
                    } => match match_collection_remainders_all_in_definition(
                        MatchMode::Evaluate,
                        definition,
                        substitution,
                        &remainder,
                    ) {
                        CollectionMatches::Solutions(solutions) => solutions
                            .into_iter()
                            .next()
                            .expect("collection solutions are never empty"),
                        CollectionMatches::NoSolution(_) | CollectionMatches::Undecided => {
                            continue;
                        }
                    },
                    MatchResult::Success(substitution) => substitution,
                };
            if substitution
                .keys()
                .any(|variable| !rule.lhs.attributes().variables.contains(variable))
                || check_concreteness(rule, &substitution).is_some()
                // A non-functional binding leaves the equation undecided; this path has no
                // indeterminate channel and passes over it as it does an undecided `requires`.
                || binds_element_variable_to_set_pattern(&substitution)
            {
                continue;
            }
            let instance = EquationInstance::new(definition, &rule.requires, substitution);
            // The attempt is speculative: its diagnostics are kept only if the equation is used.
            // An equation not used here is attempted again when the conjunct is simplified as a
            // child, and that attempt's diagnostics follow the child's own scan.
            let used = diagnostic::attempt(
                || {
                    let EquationCondition::Satisfied(matched) = evaluate_equation_condition(
                        definition,
                        &rule.attributes.unique_id,
                        &rule.computed_attributes.unbound_result_variables,
                        &rule.computed_attributes.unbound_variables,
                        Some(term),
                        instance,
                        known_predicates,
                        options,
                        active_conditions,
                        solver,
                    )?
                    else {
                        return Ok(None);
                    };
                    // The operand `f(t)` of a term-level `\and` is strict in every `t` bound to
                    // an element variable, so `u /\ f(t) = u /\ \ceil(t)` under `f(X) = \top`:
                    // an open obligation becomes a constraint of the conjunction and a refuted
                    // one makes it `\bottom`.
                    let constraints = match decide_equation_bindings(
                        definition,
                        &rule.attributes.unique_id,
                        Some(term),
                        matched,
                        known_predicates,
                        options,
                        active_conditions,
                        solver,
                    )? {
                        DecidedEquation::Defined(defined) => {
                            defined.into_carried().into_predicates()
                        }
                        DecidedEquation::Refuted(_) => vec![Predicate::False],
                    };
                    Ok(Some(constraints))
                },
                |used: &SimplifyResult<Option<Vec<Predicate>>>| !matches!(used, Ok(None)),
            )?;
            if let Some(constraints) = used {
                return Ok(Some((rule.attributes.unique_id.clone(), constraints)));
            }
        }
    }
    Ok(None)
}

#[allow(clippy::too_many_arguments)]
fn simplify_children(
    definition: &BackendDefinition,
    term: &Term,
    assumptions: &TermAssumptions<'_>,
    options: SimplificationOptions,
    remaining: &mut usize,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
    mut execution: Option<&mut ExecutionEvaluationContext>,
) -> SimplifyResult<Simplification> {
    let mut accumulated = Accumulated::default();
    let children_unchanged = Cell::new(true);
    let mut child = |term: &Term| {
        if term.attributes().evaluated && !assumptions.path_condition.can_change(term) {
            measure::bump(Counter::SimplifyNodesSkippedEvaluated);
            return Ok::<_, Unwind<SimplificationError>>(term.clone());
        }
        // The iteration limit bounds one fixed-point lineage, not the total amount of productive
        // work in an entire term. Siblings receive independent copies of the current budget, while
        // descendants produced by a rewrite inherit that rewrite's reduced budget. This permits
        // wide finite constructor trees without allowing an expanding equation to reset its cap.
        let mut child_remaining = *remaining;
        let result = simplify_with_budget(
            definition,
            term,
            assumptions,
            options,
            &mut child_remaining,
            active_conditions,
            solver,
            execution.as_deref_mut(),
        )?;
        let result = accumulated.absorb(result);
        if accumulated.undefined_term.is_none() {
            accumulated.undefined_term = result.undefined_term;
            accumulated.contradicted_total = result.contradicted_total;
        }
        children_unchanged.set(children_unchanged.get() && term.ptr_eq(&result.term));
        Ok::<_, Unwind<SimplificationError>>(result.term)
    };
    let rebuilt = match term.kind() {
        TermKind::And(left, right) => {
            let left_top = matches_top_equation(
                definition,
                left,
                assumptions.predicates,
                options,
                active_conditions,
                solver,
            )?;
            let right_top = matches_top_equation(
                definition,
                right,
                assumptions.predicates,
                options,
                active_conditions,
                solver,
            )?;
            match (left_top, right_top) {
                (Some((rule_id, obligations)), None) => {
                    children_unchanged.set(false);
                    let retained = child(right)?;
                    accumulated.top_equation(rule_id, obligations);
                    retained
                }
                (None, Some((rule_id, obligations))) => {
                    children_unchanged.set(false);
                    let retained = child(left)?;
                    accumulated.top_equation(rule_id, obligations);
                    retained
                }
                (None, None) => Term::and(child(left)?, child(right)?),
                (Some((rule_id, _)), Some(_)) => {
                    return Err(
                        SimplificationError::TopEquationOutsideConjunction { rule_id }.into(),
                    );
                }
            }
        }
        TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } => Term::application(
            symbol.clone(),
            sort_arguments.clone(),
            arguments
                .iter()
                .map(&mut child)
                .collect::<Result<Vec<_>, _>>()?,
        ),
        TermKind::Injection {
            source,
            target,
            term,
        } => Term::injection(source.clone(), target.clone(), child(term)?),
        TermKind::Map {
            definition,
            entries,
            rest,
        } => Term::map(
            definition.clone(),
            entries
                .iter()
                .map(|(key, value)| Ok((child(key)?, child(value)?)))
                .collect::<SimplifyResult<Vec<_>>>()?,
            rest.as_ref().map(&mut child).transpose()?,
        ),
        TermKind::List {
            definition,
            heads,
            rest,
        } => Term::list(
            definition.clone(),
            heads
                .iter()
                .map(&mut child)
                .collect::<Result<Vec<_>, _>>()?,
            rest.as_ref()
                .map(|(middle, tails)| {
                    Ok::<_, Unwind<SimplificationError>>((
                        child(middle)?,
                        tails
                            .iter()
                            .map(&mut child)
                            .collect::<SimplifyResult<Vec<_>>>()?,
                    ))
                })
                .transpose()?,
        ),
        TermKind::Set {
            definition,
            elements,
            rest,
        } => Term::set(
            definition.clone(),
            elements
                .iter()
                .map(&mut child)
                .collect::<Result<Vec<_>, _>>()?,
            rest.as_ref().map(&mut child).transpose()?,
        ),
        TermKind::DomainValue { .. } | TermKind::Variable(_) => term.clone(),
    };
    let term = if children_unchanged.get() {
        term.clone()
    } else {
        rebuilt
    };
    Ok(accumulated.finish(term))
}

/// What produced the result of `simplify_root`, as far as the iteration budget is concerned.
///
/// The budget bounds the simplifier's own fixed point: which simplification rules it orients
/// and applies, and how far it unfolds a function over a symbolic argument. Whether that
/// rewriting terminates is a property of the simplifier's strategy, and cutting it leaves a term
/// equal to the input, a sound weaker result.
/// A function equation applied to a variable-free redex whose conditions were decided and whose
/// result carries no constraint (no open definedness or `ensures` obligation, no `\bottom`) is
/// instead a step of the definition's own computation with a determined value. Cutting it can
/// only leave the application unevaluated, which makes conditions over it undecidable and
/// execution stop at a configuration the definition does not produce. Such a step is exempt from
/// the budget; if the computation diverges, it ends through the caller's interrupt
/// (cancellation or step deadline, checked at every round) or through the stack guard's
/// `StackExhausted` error, as divergence of the definition's rewrite rules does.
#[derive(Clone, Copy, Eq, PartialEq)]
enum RootStep {
    /// A determined function-theory step on a ground redex.
    DeterminedFunctionStep,
    /// Any other result: a builtin, a simplification rule, a function step on a symbolic redex
    /// or with residual constraints, or no rewrite.
    Other,
}

/// One root step: a builtin hook, else the function theory, else the simplification theory.
///
/// A hooked symbol is a function symbol, and a KORE application is strict: `f(t1, .., tn)` is
/// `\bottom` wherever some `ti` is. When the hook evaluates the application to `v`, the exact
/// result is therefore `\ceil(t1) /\ .. /\ \ceil(tn) /\ v`, not `v`: a hook that returns
/// `v` without inspecting a symbolic argument (`t ==Int t`, `true orBool b`, `#if true #then a
/// #else b #fi`, `M <=Map M`) would otherwise yield a value defined on instances where the
/// application is not. A hook returns a value only where its own domain condition holds on the
/// arguments it was given; what it cannot establish without inspecting an argument is that
/// argument's definedness. That definedness is returned as obligations of the result
/// (`Simplification::hook`, which states them through `ResultConditions::hook_arguments`), which
/// every caller conjoins as it conjoins the open definedness obligations of a function equation.
///
/// Every hook is strict in every argument, `BOOL.andThen`, `BOOL.orElse` and `KEQUAL.ite`
/// included: ground simplification already is, since children are simplified before the root and
/// an undefined argument makes the whole term `\bottom` before the hook sees it, so symbolic
/// evaluation must agree with it on every instance.
fn simplify_root(
    definition: &BackendDefinition,
    term: &Term,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
    execution: Option<&mut ExecutionEvaluationContext>,
) -> SimplifyResult<(Simplification, RootStep, Option<Arc<RewriteRule>>)> {
    // A set holding an element twice, or a map binding a key twice (with the same value or
    // not), is `\bottom`: concatenation of sets and of maps is defined only on disjoint
    // elements and keys, and syntactically equal terms denote the same element on every
    // instance. The constructors keep the repeat (`Term::set`, `Term::map`) and leave such a
    // node unevaluated, so it reaches this root step wherever it was built (a rule's
    // right-hand side, a function equation's result, a substitution), and it is reported here
    // as `\bottom`, the way a builtin's undefined result is below. Elements that are not
    // syntactically equal may still denote one element; that stays the definedness condition
    // `ceil_term` states for the node. A `ceil_free` collection has pairwise distinct
    // elements and keys, so only other collections are scanned.
    if !term.attributes().ceil_free() && term.repeated_collection_key().is_some() {
        return Ok((
            Simplification::repeated_collection(term),
            RootStep::Other,
            None,
        ));
    }
    let builtin = match execution {
        Some(execution) => evaluate_builtin_in_execution(term, definition, execution),
        None => evaluate_builtin(term, definition),
    }?
    .map_err(SimplificationError::Builtin)?;
    let unsupported = match builtin {
        BuiltinResult::NotApplicable => None,
        BuiltinResult::Unsupported(reason) => Some(reason),
        builtin => {
            measure::bump(Counter::SimplifyBuiltinEvaluations);
            let TermKind::Application { symbol, .. } = term.kind() else {
                unreachable!("only applications have builtin hooks")
            };
            let outcome = match builtin {
                BuiltinResult::Value(result) => HookOutcome::Value(result),
                BuiltinResult::Bottom => HookOutcome::Bottom,
                BuiltinResult::Effect(effect) => {
                    HookOutcome::Effect(builtin_effect_result(definition, term, &effect)?, effect)
                }
                BuiltinResult::NotApplicable | BuiltinResult::Unsupported(_) => unreachable!(),
            };
            let hook = symbol
                .attributes
                .hook
                .as_deref()
                .expect("evaluated builtin has a hook");
            return Ok((
                Simplification::hook(definition, term, outcome, hook, known_predicates),
                RootStep::Other,
                None,
            ));
        }
    };
    // The diagnostics of the indeterminate equation attempts of either theory, committed only if
    // neither theory rewrites the term.
    let mut indeterminate = IndeterminateAttempts::default();
    let function_scan = match apply_theory::<FunctionTheory>(
        definition,
        term,
        known_predicates,
        options,
        active_conditions,
        solver,
        &mut indeterminate,
    )? {
        TheoryScan::Applied(result, rule) => {
            let step = if term.attributes().variables.is_empty() && result.conditions().is_empty() {
                RootStep::DeterminedFunctionStep
            } else {
                RootStep::Other
            };
            return Ok((result, step, Some(rule)));
        }
        scan => scan,
    };
    let simplification_scan = match apply_theory::<SimplificationTheory>(
        definition,
        term,
        known_predicates,
        options,
        active_conditions,
        solver,
        &mut indeterminate,
    )? {
        TheoryScan::Applied(result, rule) => return Ok((result, RootStep::Other, Some(rule))),
        scan => scan,
    };
    // No equation rewrote the term, which is kept: the indeterminate attempts explain why.
    indeterminate.commit(|| Subject::Term(term.clone()));
    let TermKind::Application {
        symbol, arguments, ..
    } = term.kind()
    else {
        debug_assert!(unsupported.is_none());
        return Ok((
            Simplification::irreducible(term.clone()),
            RootStep::Other,
            None,
        ));
    };
    let builtin_supported = unsupported.is_none();
    if let Some(hook) = symbol.attributes.hook.as_deref() {
        if arguments
            .iter()
            .all(|argument| argument.attributes().constructor_like)
        {
            let index = term_index(term);
            let has_equations = definition.function_theory().contains_key(&index)
                || definition.simplification_theory().contains_key(&index);
            let reason = match unsupported {
                Some(UnsupportedHookReason::NotImplemented) if has_equations => None,
                Some(reason) => Some(reason),
                None => Some(UnsupportedHookReason::ArgumentOutOfRange {
                    detail: "the evaluator did not reduce constructor-like arguments".into(),
                }),
            };
            if let Some(reason) = reason {
                return Err(SimplificationError::UnsupportedHook {
                    hook: hook.to_owned(),
                    reason,
                    term: term.clone(),
                }
                .into());
            }
        } else if let Some(reason) = unsupported {
            diagnostic::emit(BackendDiagnostic::UnsupportedHookUnevaluated {
                hook: hook.to_owned(),
                reason,
            });
        }
    }
    // The fixed point is recorded only when both scans are `NotApplicable`, in a definition
    // whose equation selection reaches every term equation: every equation of the definition
    // failed to match the term, which holds on every path (`Term::with_evaluated_cache`).
    let term = if let TheoryScan::NotApplicable(function_scan) = function_scan
        && let TheoryScan::NotApplicable(simplification_scan) = simplification_scan
        && builtin_supported
        && cacheable_equation_head(definition, term)
        && let Some(selection) = definition.equation_selection_complete()
    {
        term.with_evaluated_cache(
            definition,
            NormalFormCertificate::new(selection, function_scan, simplification_scan),
        )
    } else {
        term.clone()
    };
    Ok((Simplification::irreducible(term), RootStep::Other, None))
}

/// The definedness of the arguments of a hooked application the hook has evaluated: the
/// `ceil_term` obligations of every argument, without duplicates and without those already among
/// `known_predicates`, which the caller's result is taken under.
///
/// The obligations are open, not a refutation: the application is not `\bottom`, so no
/// `undefined_term` is reported. A `ceil_free` argument contributes nothing, so evaluation over
/// values and constructor terms is unchanged. An obligation whose term also occurs in the
/// hook's value is kept: it is redundant there, and a redundant conjunct is sound. A hook's
/// result receives them only through `condition::ResultConditions::hook_arguments`, which records
/// every member as an obligation.
pub(crate) fn hook_argument_definedness(
    definition: &BackendDefinition,
    application: &Term,
    known_predicates: &[Predicate],
) -> Vec<Predicate> {
    let TermKind::Application { arguments, .. } = application.kind() else {
        unreachable!("only applications have builtin hooks")
    };
    let mut obligations = Vec::new();
    for argument in arguments {
        if argument.attributes().ceil_free() {
            continue;
        }
        for obligation in ceil_term(definition, argument) {
            if !known_predicates.contains(&obligation) && !obligations.contains(&obligation) {
                obligations.push(obligation);
            }
        }
    }
    obligations
}

fn builtin_effect_result(
    definition: &BackendDefinition,
    application: &Term,
    effect: &BuiltinEffect,
) -> Result<Term, SimplificationError> {
    match effect {
        BuiltinEffect::UserLog(_) => {
            let Some(dotk) = definition.symbols().get(WellKnownSymbol::DotK.as_str()) else {
                return Err(SimplificationError::InvalidBuiltinResultSymbol {
                    hook: "IO.logString",
                    symbol: WellKnownSymbol::DotK.as_str(),
                });
            };
            if !dotk.sort_variables.is_empty() || !dotk.argument_sorts.is_empty() {
                return Err(SimplificationError::InvalidBuiltinResultSymbol {
                    hook: "IO.logString",
                    symbol: WellKnownSymbol::DotK.as_str(),
                });
            }
            let mut dotk = dotk.as_ref().clone();
            dotk.result_sort = application.sort();
            Ok(Term::application(Arc::new(dotk), Vec::new(), Vec::new()))
        }
    }
}

/// Whether `term` is one of the normalized value-like equation heads whose fixed point can be
/// retained in the term itself. Fully evaluated children exclude a closed parent whose child
/// scan was blocked, and the empty variable set keeps a symbolic application out of the cache.
/// The caller separately needs a [`NormalFormCertificate`]: complete equation selection and two
/// scans that ended in failed matches only (`TheoryScan::NotCacheable` and `TheoryScan::Blocked`
/// give none).
fn cacheable_equation_head(definition: &BackendDefinition, term: &Term) -> bool {
    let TermKind::Application {
        symbol, arguments, ..
    } = term.kind()
    else {
        return false;
    };
    term.attributes().variables.is_empty()
        && arguments
            .iter()
            .all(|argument| argument.attributes().evaluated)
        && (symbol.attributes.head_role() == HeadRole::EquationHead
            || definition.overloads().is_overloaded(&symbol.name))
}

#[allow(clippy::too_many_arguments)]
fn apply_theory<K: TermTheory>(
    definition: &BackendDefinition,
    term: &Term,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
    indeterminate: &mut IndeterminateAttempts,
) -> SimplifyResult<TheoryScan<K>> {
    scan_term_theory::<K>(definition, term, indeterminate, |rule| {
        apply_equation(
            definition,
            rule,
            term,
            known_predicates,
            options,
            active_conditions,
            solver,
        )
    })
}

/// Decide the binding obligations of an equation instance whose `requires` holds
/// ([`MatchedEquation::decide`]). The obligations are simplified under the path condition first,
/// keyed by `anchor` against re-entry as `evaluate_equation_condition` does, and a verdict the
/// solver could not reach is reported as a diagnostic of `rule_id`.
#[allow(clippy::too_many_arguments)]
fn decide_equation_bindings(
    definition: &BackendDefinition,
    rule_id: &str,
    anchor: Option<&Term>,
    matched: MatchedEquation,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
) -> SimplifyResult<DecidedEquation> {
    let decided = matched.decide(|obligations| {
        let decide = || {
            let obligations = if let Some(anchor) = anchor {
                simplify_rule_predicates_or_keep(
                    definition,
                    rule_id,
                    anchor,
                    obligations,
                    known_predicates,
                    options,
                    active_conditions,
                    solver,
                )?
            } else {
                obligations
            };
            // The obligations state the definedness of terms of the subject, which the
            // equation's variables are renamed apart from: none of them is the equation's.
            let verdict = decide_rule_condition(
                rule_id,
                &obligations,
                &BTreeSet::new(),
                known_predicates,
                solver,
            )?;
            Ok((verdict, obligations))
        };
        decide().layered()
    })??;
    Ok(decided)
}

/// Whether `substitution` binds an element variable to a pattern containing a set variable.
///
/// An element variable ranges over elements; a set variable over arbitrary patterns. An
/// equation `f(I) = rhs[I] requires R[I]` over an element variable `I` is an axiom for every
/// element `i`, and `f(t) = rhs[t]` for a term `t` follows only when `t` is functional: applied
/// to `f(@Y)`, the equation gives the union over the elements `y` of `@Y` of `rhs[y]`, which is
/// `rhs[@Y]` only when `rhs` and `R` are linear in `I`. The binding `I := t` with a set variable
/// in `t` therefore does not justify the substitution and the attempt stays indeterminate: the
/// subject is retained, and no other equation of the group fires in its place. The converse
/// direction, a rule-side set variable bound to any subject pattern, is sound and unaffected.
pub(crate) fn binds_element_variable_to_set_pattern(substitution: &Substitution) -> bool {
    substitution.iter().any(|(variable, value)| {
        variable.kind == VariableKind::Element
            && value
                .attributes()
                .variables
                .iter()
                .any(|bound| bound.kind == VariableKind::Set)
    })
}

fn apply_equation(
    definition: &BackendDefinition,
    rule: &RewriteRule,
    term: &Term,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
) -> SimplifyResult<EquationAttempt<Simplification, MatchFailed>> {
    if let Some((renamed, _)) = rename_apart(rule, &term.attributes().variables, known_predicates) {
        return apply_equation(
            definition,
            &renamed,
            term,
            known_predicates,
            options,
            active_conditions,
            solver,
        );
    }
    measure::bump(Counter::SimplifyEquationAttempts);
    let matched = match_terms_in_definition(MatchMode::Evaluate, definition, &rule.lhs, term);
    let substitution = match matched {
        MatchResult::Failed(_) => {
            let failed = matched
                .refutation()
                .expect("a failed match states its refutation");
            return Ok(EquationAttempt::NotApplicable(failed));
        }
        MatchResult::Indeterminate {
            substitution,
            remainder,
        } => {
            let solutions = match match_collection_remainders_all_in_definition(
                MatchMode::Evaluate,
                definition,
                substitution.clone(),
                &remainder,
            ) {
                CollectionMatches::Solutions(solutions) => solutions,
                CollectionMatches::NoSolution(failed) => {
                    return Ok(EquationAttempt::NotApplicable(failed));
                }
                CollectionMatches::Undecided => {
                    return Ok(EquationAttempt::Indeterminate(
                        ConditionIndeterminacy::ImplicationIndeterminate,
                    ));
                }
            };
            // K function equations are required to be functional. AC matching may expose
            // several equivalent decompositions, so use the first substitution from the
            // helper's stable sorted order rather than turning evaluation into execution
            // branching.
            solutions
                .into_iter()
                .next()
                .expect("collection solutions are never empty")
        }
        MatchResult::Success(substitution) => substitution,
    };
    // The left-hand side matched. The two checks below decide whether the evaluator uses the
    // equation here, not whether it holds, so a rejection is `Unused`, never `NotApplicable`.
    if substitution
        .keys()
        .any(|variable| !rule.lhs.attributes().variables.contains(variable))
    {
        return Ok(EquationAttempt::Unused);
    }
    if check_concreteness(rule, &substitution).is_some() {
        return Ok(EquationAttempt::Unused);
    }
    if binds_element_variable_to_set_pattern(&substitution) {
        return Ok(EquationAttempt::Indeterminate(
            ConditionIndeterminacy::NonFunctionalBinding,
        ));
    }
    let instance = EquationInstance::new(definition, &rule.requires, substitution);
    // The equation `f(X) = rhs requires R` is an axiom over every element `X`. A term `t` bound
    // to `X` is a functional pattern (at most one element), so `f(t) = \ceil(t) /\ rhs[t]` when
    // `R[t]` holds on that element: both sides are empty when `t` is, and equal to `rhs[t]`
    // otherwise. An unknown `R[t]` must stay indeterminate, because applying the equation would
    // narrow the subject to the part where `R` holds. A refuted `R[t]` remains context dependent:
    // it permits lower-priority equations in this scan but cannot justify caching the term across
    // simplifier calls with different path conditions.
    let matched = match evaluate_equation_condition(
        definition,
        &rule.attributes.unique_id,
        &rule.computed_attributes.unbound_result_variables,
        &rule.computed_attributes.unbound_variables,
        Some(term),
        instance,
        known_predicates,
        options,
        active_conditions,
        solver,
    )? {
        EquationCondition::Satisfied(matched) => matched,
        EquationCondition::Refuted => return Ok(EquationAttempt::ContextDependent),
        EquationCondition::Indeterminate(reason) => {
            return Ok(EquationAttempt::Indeterminate(reason));
        }
    };
    // The definedness obligations are not a reason to refuse the equation: an obligation the
    // path condition does not decide is carried as a constraint of the result, where it keeps
    // the `\ceil(t)` factor of the equality explicit. A refuted obligation means `t` is empty
    // under the path condition, and the subject reaches `t` only through applications,
    // injections, collections, and `\and`, all strict, so the subject is empty whichever
    // equation is tried; the result reports it as `\bottom`. Only the equation's own `requires`,
    // decided above, says nothing about the subject when refuted.
    let defined = match decide_equation_bindings(
        definition,
        &rule.attributes.unique_id,
        Some(term),
        matched,
        known_predicates,
        options,
        active_conditions,
        solver,
    )? {
        DecidedEquation::Defined(defined) => defined,
        DecidedEquation::Refuted(_) => {
            return Ok(EquationAttempt::Applied(Simplification::bottom_subject(
                rule, term,
            )));
        }
    };
    let (alternatives, is_disjunction) = match &rule.rhs {
        RuleRhs::Term(rhs) => (
            vec![(
                substitute(rhs, defined.substitution()),
                rule.ensures.clone(),
                false,
            )],
            false,
        ),
        RuleRhs::Bottom => (vec![(term.clone(), rule.ensures.clone(), true)], false),
        RuleRhs::Disjunction(alternatives) => (
            alternatives
                .iter()
                .map(|alternative| {
                    let ensures = rule.ensures.merged(&alternative.ensures);
                    (
                        substitute(&alternative.term, defined.substitution()),
                        ensures,
                        false,
                    )
                })
                .collect(),
            true,
        ),
        RuleRhs::Top => {
            return Err(SimplificationError::TopEquationOutsideConjunction {
                rule_id: rule.attributes.unique_id.clone(),
            }
            .into());
        }
        RuleRhs::Predicates(_) => return Ok(EquationAttempt::Unused),
    };
    let mut live = Vec::new();
    for (rhs, ensures, rhs_is_bottom) in alternatives {
        match evaluate_ensures(
            definition,
            rule,
            term,
            defined.instantiate_ensures(&ensures),
            known_predicates,
            options,
            active_conditions,
            solver,
        )? {
            EnsuresVerdict::Refuted => {
                if !is_disjunction {
                    live.push((rhs, vec![Predicate::False]));
                }
            }
            EnsuresVerdict::Holds => live.push((
                rhs,
                if rhs_is_bottom {
                    vec![Predicate::False]
                } else {
                    Vec::new()
                },
            )),
            EnsuresVerdict::Open(mut constraints) => {
                if rhs_is_bottom {
                    constraints.push(Predicate::False);
                }
                live.push((rhs, constraints));
            }
        }
    }
    match live.len() {
        0 => Ok(EquationAttempt::Applied(Simplification::bottom_subject(
            rule, term,
        ))),
        1 => {
            let (term, ensures) = live.pop().expect("one live alternative");
            // The open `ensures` is what the equation asserts of its result; a `\bottom` here
            // is a refuted `ensures` or a bottom right-hand side, the subject's own emptiness.
            Ok(EquationAttempt::Applied(Simplification::equation(
                rule,
                term,
                ensures,
                defined.into_carried(),
            )))
        }
        alternatives => Err(SimplificationError::DisjunctiveResult {
            rule_id: rule.attributes.unique_id.clone(),
            alternatives,
        }
        .into()),
    }
}

enum EnsuresVerdict {
    Refuted,
    Holds,
    Open(Vec<Predicate>),
}

#[allow(clippy::too_many_arguments)]
fn evaluate_ensures(
    definition: &BackendDefinition,
    rule: &RewriteRule,
    term: &Term,
    ensures: InstantiatedCondition,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
) -> SimplifyResult<EnsuresVerdict> {
    // An `ensures` constrains the result only where its terms are defined.
    let ensures = ensures.simplify(
        definition,
        known_predicates,
        known_predicates,
        |ensures, known, first_attempt| {
            if first_attempt {
                simplify_rule_predicates(
                    definition,
                    (&rule.attributes.unique_id, term),
                    &ensures,
                    known,
                    options,
                    active_conditions,
                    solver,
                )
                .layered()
            } else {
                simplify_rule_predicates_or_keep(
                    definition,
                    &rule.attributes.unique_id,
                    term,
                    ensures,
                    known,
                    options,
                    active_conditions,
                    solver,
                )
                .layered()
            }
        },
    )??;
    // An `ensures` is a conjunct of the result by definition, so every verdict the solver does
    // not reach carries it: an open implication, no solver, a query the encoding cannot pose,
    // and an inconsistent path condition, which under the path condition alone says nothing
    // about the equation. No diagnostic is emitted here, as none was before.
    match decide_condition(&ensures, known_predicates, solver)? {
        Ok(RuleCondition::Satisfied) => Ok(EnsuresVerdict::Holds),
        Ok(RuleCondition::Refuted) => Ok(EnsuresVerdict::Refuted),
        Ok(RuleCondition::Indeterminate(_)) => Ok(EnsuresVerdict::Open(ensures)),
        Err(error) => Err(SimplificationError::Smt {
            rule_id: rule.attributes.unique_id.clone(),
            error,
        }
        .into()),
    }
}

#[cfg(test)]
mod tests {
    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    use super::*;
    use crate::{
        stop::{Stop, StopCause},
        term::{CollectionSymbols, ListDefinition, MapDefinition},
    };

    /// The inner layer of an entry point's result, for the tests that arm no stop: a stop is a
    /// test failure, reported with its cause.
    fn unstopped<T>(
        result: Stoppable<Result<T, SimplificationError>>,
    ) -> Result<T, SimplificationError> {
        result.unwrap_or_else(|stop| {
            panic!(
                "the simplification stopped although no stop was armed: {}",
                stop.into_cause()
            )
        })
    }

    fn term(definition: &BackendDefinition, source: &str) -> Term {
        let syntax = parse_pattern(source).expect("term should parse");
        definition
            .internalize_term(&syntax, &[])
            .expect("term should internalize")
    }

    fn collection_symbols(prefix: &str) -> CollectionSymbols {
        CollectionSymbols {
            unit: format!("{prefix}Unit").into(),
            element: format!("{prefix}Element").into(),
            concat: format!("{prefix}Concat").into(),
        }
    }

    #[test]
    fn path_condition_replacements_preserve_unaffected_term_identity() {
        let int = Sort::builtin(BuiltinSort::Int);
        let one = Term::domain_value(int.clone(), "1");
        let two = Term::domain_value(int.clone(), "2");
        let subject = Term::injection(int.clone(), Sort::simple("SortKItem"), one.clone());

        let empty = PathConditionReplacements {
            substitution: Substitution::new(),
            replacements: Vec::new(),
        };
        assert!(empty.apply(&subject).ptr_eq(&subject));

        let unrelated = PathConditionReplacements {
            substitution: Substitution::new(),
            replacements: vec![(two, Term::domain_value(int.clone(), "3"))],
        };
        assert!(unrelated.apply(&subject).ptr_eq(&subject));

        let substitution = PathConditionReplacements {
            substitution: Substitution::from([(
                Variable::new("X", int.clone()),
                Term::domain_value(int, "4"),
            )]),
            replacements: Vec::new(),
        };
        assert!(substitution.apply(&subject).ptr_eq(&subject));
    }

    #[test]
    fn path_condition_replacements_descend_through_injections_and_collections() {
        let int = Sort::builtin(BuiltinSort::Int);
        let one = Term::domain_value(int.clone(), "1");
        let two = Term::domain_value(int.clone(), "2");
        let key = Term::domain_value(Sort::simple("SortKey"), "key");
        let map_definition = Arc::new(MapDefinition {
            symbols: collection_symbols("map"),
            key_sort: "SortKey".into(),
            value_sort: "SortInt".into(),
            map_sort: "SortMap".into(),
        });
        let list_definition = Arc::new(ListDefinition {
            symbols: collection_symbols("list"),
            element_sort: "SortInt".into(),
            list_sort: "SortList".into(),
        });
        let set_definition = Arc::new(ListDefinition {
            symbols: collection_symbols("set"),
            element_sort: "SortInt".into(),
            list_sort: "SortSet".into(),
        });
        let composite = Term::and(
            Term::injection(int.clone(), Sort::simple("SortKItem"), one.clone()),
            Term::and(
                Term::map(
                    map_definition.clone(),
                    vec![(key.clone(), one.clone())],
                    None,
                ),
                Term::and(
                    Term::list(list_definition.clone(), vec![one.clone()], None),
                    Term::set(set_definition.clone(), vec![one.clone()], None),
                ),
            ),
        );
        let attributes = composite.attributes().clone();
        let replacements = PathConditionReplacements {
            substitution: Substitution::new(),
            replacements: vec![(one, two.clone())],
        };
        let replaced = replacements.apply(&composite);
        let expected = Term::and(
            Term::injection(int, Sort::simple("SortKItem"), two.clone()),
            Term::and(
                Term::map(map_definition, vec![(key, two.clone())], None),
                Term::and(
                    Term::list(list_definition, vec![two.clone()], None),
                    Term::set(set_definition, vec![two], None),
                ),
            ),
        );

        assert_eq!(replaced, expected);
        assert_eq!(replaced.attributes().variables, attributes.variables);
        assert_eq!(replaced.attributes().evaluated, attributes.evaluated);
        assert_eq!(
            replaced.attributes().constructor_like,
            attributes.constructor_like
        );
        assert_eq!(
            replaced.attributes().concrete_after_normalization,
            attributes.concrete_after_normalization
        );
        assert_eq!(
            replaced.attributes().can_be_evaluated,
            attributes.can_be_evaluated
        );
        assert!(!replaced.ptr_eq(&composite));
    }

    #[test]
    fn applies_the_canonically_first_same_priority_ceil_equation() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortS{} [hasDomainValues{}()]
                symbol f{}(SortS{}) : SortS{} [function{}()]
                axiom{R, Q} \implies{R}(
                    \top{R}(),
                    \equals{Q, R}(
                        \ceil{SortS{}, Q}(f{}(X:SortS{})),
                        \and{Q}(\top{Q}(), \top{Q}())
                    )
                ) [label{}("ceil-first"), simplification{}()]
                axiom{R, Q} \implies{R}(
                    \top{R}(),
                    \equals{Q, R}(
                        \ceil{SortS{}, Q}(f{}(X:SortS{})),
                        \and{Q}(\bottom{Q}(), \top{Q}())
                    )
                ) [label{}("ceil-second"), simplification{}()]
            endmodule []"#,
        )
        .expect("ceil definition should parse");
        let definition = BackendDefinition::internalize(&syntax, "MAIN")
            .expect("ceil definition should internalize");
        let predicate = Predicate::Ceil(term(&definition, r#"f{}(\dv{SortS{}}("value"))"#));
        assert_eq!(
            definition
                .ceil_theory()
                .values()
                .flat_map(|groups| groups.values())
                .flatten()
                .count(),
            2
        );

        let result = apply_ceil_theory(
            &definition,
            &predicate,
            &[],
            SimplificationOptions::default(),
            &BTreeSet::new(),
            &NoSolver,
            &mut IndeterminateAttempts::default(),
        )
        .expect("the first applicable ceil equation should win")
        .expect("the first ceil equation should apply");

        assert_eq!(result, Predicate::True);
    }

    /// `wrap` is a constructor, `partial` and `opaque` are partial functions without equations,
    /// `discard` and `guarded` are total functions whose equations discard their argument;
    /// `guarded` additionally requires its argument to be the value `expected`.
    fn definedness_definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortS{} [hasDomainValues{}()]
                sort SortC{} []
                symbol wrap{}(SortS{}) : SortC{} [constructor{}(), functional{}(), injective{}()]
                symbol partial{}(SortS{}) : SortS{} [function{}()]
                symbol opaque{}(SortS{}) : SortS{} [function{}()]
                symbol discard{}(SortS{}) : SortS{} [function{}(), total{}()]
                symbol guarded{}(SortS{}) : SortS{} [function{}(), total{}()]
                axiom{R} \implies{R}(
                    \top{R}(),
                    \equals{SortS{}, R}(
                        discard{}(X:SortS{}),
                        \and{SortS{}}(\dv{SortS{}}("done"), \top{SortS{}}())
                    )
                ) [label{}("discard"), simplification{}()]
                axiom{R} \implies{R}(
                    \and{R}(
                        \equals{SortS{}, R}(X:SortS{}, \dv{SortS{}}("expected")),
                        \top{R}()
                    ),
                    \equals{SortS{}, R}(
                        guarded{}(X:SortS{}),
                        \and{SortS{}}(\dv{SortS{}}("done"), \top{SortS{}}())
                    )
                ) [label{}("guarded"), simplification{}()]
            endmodule []"#,
        )
        .expect("definedness definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN")
            .expect("definedness definition should internalize")
    }

    #[test]
    fn applies_an_equation_under_an_open_definedness_obligation() {
        let definition = definedness_definition();
        let argument = term(&definition, "partial{}(Y:SortS{})");
        let input = term(&definition, "discard{}(partial{}(Y:SortS{}))");
        let done = term(&definition, r#"\dv{SortS{}}("done")"#);

        // `discard(t) = \ceil(t) /\ "done"`: nothing decides `\ceil(partial(Y))`, so the
        // equation applies and the obligation becomes a constraint of the result.
        let result = unstopped(simplify(
            &definition,
            &input,
            SimplificationOptions::default(),
        ))
        .expect("the equation should apply");
        assert_eq!(result.term, done);
        assert_eq!(
            result.constraints(),
            vec![Predicate::Ceil(argument.clone())]
        );
        assert_eq!(result.applied_rules, vec!["discard".to_owned()]);

        // A path condition that already carries the obligation discharges it.
        let result = unstopped(simplify_with_solver(
            &definition,
            &input,
            &[Predicate::Ceil(argument)],
            SimplificationOptions::default(),
            &NoSolver,
        ))
        .expect("the equation should apply");
        assert_eq!(result.term, done);
        assert!(result.constraints().is_empty());
    }

    #[test]
    fn an_unknown_requires_keeps_the_equation_indeterminate() {
        let definition = definedness_definition();
        let done = term(&definition, r#"\dv{SortS{}}("done")"#);

        // Negative control: the same open definedness obligation, but the equation's own
        // `requires` is undecided, so applying it would narrow the subject.
        let input = term(&definition, "guarded{}(partial{}(Y:SortS{}))");
        let result = unstopped(simplify(
            &definition,
            &input,
            SimplificationOptions::default(),
        ))
        .expect("an indeterminate equation retains the subject");
        assert_eq!(result.term, input);
        assert!(result.constraints().is_empty());
        assert!(result.applied_rules.is_empty());

        // Positive control: the equation itself applies once `requires` is decided.
        let input = term(&definition, r#"guarded{}(\dv{SortS{}}("expected"))"#);
        let result = unstopped(simplify(
            &definition,
            &input,
            SimplificationOptions::default(),
        ))
        .expect("the guarded equation should apply");
        assert_eq!(result.term, done);
        assert!(result.constraints().is_empty());
    }

    #[test]
    fn drops_a_ceil_conjunct_entailed_by_the_pattern_term() {
        let definition = definedness_definition();
        let argument = term(&definition, "partial{}(Y:SortS{})");
        let obligation = Predicate::Ceil(argument.clone());
        let simplify_pattern = |source: &str| {
            unstopped(simplify_pattern_with_solver(
                &definition,
                &Pattern {
                    term: term(&definition, source),
                    constraints: vec![obligation.clone()],
                },
                SimplificationOptions::default(),
                &NoSolver,
            ))
            .expect("the pattern should simplify")
        };

        // `wrap` is a constructor: `\ceil(t) /\ wrap(t) = wrap(t)`.
        let entailed = simplify_pattern("wrap{}(partial{}(Y:SortS{}))");
        assert_eq!(
            entailed.term,
            term(&definition, "wrap{}(partial{}(Y:SortS{}))")
        );
        assert!(entailed.constraints.is_empty());

        // Negative control: under a partial function symbol the conjunct is kept.
        let under_function = simplify_pattern("opaque{}(partial{}(Y:SortS{}))");
        assert_eq!(
            under_function.term,
            term(&definition, "opaque{}(partial{}(Y:SortS{}))")
        );
        assert_eq!(under_function.constraints, vec![obligation.clone()]);

        // Negative control: a term that does not contain `t` entails nothing about it.
        let unrelated = simplify_pattern("wrap{}(Y:SortS{})");
        assert_eq!(unrelated.constraints, vec![obligation.clone()]);

        // An equation that discards `t` leaves the carried obligation as the only witness.
        let discarded = unstopped(simplify_pattern_with_solver(
            &definition,
            &Pattern {
                term: term(&definition, "wrap{}(discard{}(partial{}(Y:SortS{})))"),
                constraints: Vec::new(),
            },
            SimplificationOptions::default(),
            &NoSolver,
        ))
        .expect("the pattern should simplify");
        assert_eq!(
            discarded.term,
            term(&definition, r#"wrap{}(\dv{SortS{}}("done"))"#)
        );
        assert_eq!(discarded.constraints, vec![obligation]);
    }

    /// A solver that refutes every query.
    struct RefutingSolver;

    impl SmtSolver for RefutingSolver {
        fn is_sat(
            &self,
            _predicates: &[Predicate],
            _substitution: &Substitution,
        ) -> Stoppable<Result<crate::smt::Satisfiability, SmtError>> {
            unreachable!()
        }

        fn check_predicates(
            &self,
            _known: &[Predicate],
            _substitution: &Substitution,
            _checked: &[Predicate],
        ) -> Stoppable<Result<Validity, SmtError>> {
            Ok(Ok(Validity::Refuted))
        }
    }

    /// `f`, `h`, and `partial` are partial functions; `\ceil(f(X))` rewrites to `X = "ok"`
    /// unconditionally and `\ceil(h(X))` to `\top` when `X = "expected"`.
    fn conditional_ceil_definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortS{} [hasDomainValues{}()]
                symbol f{}(SortS{}) : SortS{} [function{}()]
                symbol h{}(SortS{}) : SortS{} [function{}()]
                symbol partial{}(SortS{}) : SortS{} [function{}()]
                axiom{R, Q} \implies{R}(
                    \top{R}(),
                    \equals{Q, R}(
                        \ceil{SortS{}, Q}(f{}(X:SortS{})),
                        \and{Q}(
                            \equals{SortS{}, Q}(X:SortS{}, \dv{SortS{}}("ok")),
                            \top{Q}()
                        )
                    )
                ) [label{}("ceil-f"), simplification{}()]
                axiom{R, Q} \implies{R}(
                    \and{R}(
                        \equals{SortS{}, R}(X:SortS{}, \dv{SortS{}}("expected")),
                        \top{R}()
                    ),
                    \equals{Q, R}(
                        \ceil{SortS{}, Q}(h{}(X:SortS{})),
                        \and{Q}(\top{Q}(), \top{Q}())
                    )
                ) [label{}("ceil-h"), simplification{}()]
            endmodule []"#,
        )
        .expect("conditional ceil definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN")
            .expect("conditional ceil definition should internalize")
    }

    #[test]
    fn ceil_equations_carry_open_element_binding_definedness() {
        let definition = conditional_ceil_definition();
        let argument = term(&definition, r#"partial{}(\dv{SortS{}}("v"))"#);
        let obligation = Predicate::Ceil(argument.clone());
        let subject = Predicate::Ceil(term(&definition, r#"f{}(partial{}(\dv{SortS{}}("v")))"#));
        let rhs = Predicate::Equals(argument, term(&definition, r#"\dv{SortS{}}("ok")"#));
        let apply = |known: &[Predicate], solver: &dyn SmtSolver| {
            apply_ceil_theory(
                &definition,
                &subject,
                known,
                SimplificationOptions::default(),
                &BTreeSet::new(),
                solver,
                &mut IndeterminateAttempts::default(),
            )
            .expect("the ceil equation should not fail")
        };

        // `\ceil(f(t)) = \ceil(t) /\ q[t]`: the open obligation is conjoined to the result.
        assert_eq!(
            apply(&[], &NoSolver),
            Some(Predicate::And(vec![rhs.clone(), obligation.clone()]))
        );
        // A path condition that carries the obligation discharges it.
        assert_eq!(
            apply(std::slice::from_ref(&obligation), &NoSolver),
            Some(rhs.clone())
        );
        // A refuted obligation means `t` is empty, and so is the subject `\ceil(f(t))`.
        assert_eq!(apply(&[], &RefutingSolver), Some(Predicate::False));

        // The standalone predicate entry reaches the equation in one call: the ceil arm's
        // expansion supplies `\ceil(t)` as a sibling, and the conjunction is simplified again.
        assert_eq!(
            unstopped(simplify_predicate_with_solver(
                &definition,
                &subject,
                &[],
                SimplificationOptions::default(),
                &NoSolver,
            ))
            .expect("the predicate should simplify"),
            Predicate::And(vec![rhs, obligation])
        );

        // Negative control: an undecided `requires` still refuses, obligation or not.
        let guarded = Predicate::Ceil(term(&definition, r#"h{}(partial{}(\dv{SortS{}}("v")))"#));
        assert_eq!(
            apply_ceil_theory(
                &definition,
                &guarded,
                &[],
                SimplificationOptions::default(),
                &BTreeSet::new(),
                &NoSolver,
                &mut IndeterminateAttempts::default(),
            )
            .expect("an indeterminate ceil equation should not fail"),
            None
        );
    }

    #[test]
    fn strict_variables_is_a_conservative_under_approximation() {
        let definition = conditional_ceil_definition();
        let x = Variable::new("X", Sort::simple("SortS"));
        let f_x = term(&definition, "f{}(X:SortS{})");
        let h_x = term(&definition, "h{}(X:SortS{})");
        let value = term(&definition, r#"\dv{SortS{}}("c")"#);
        let substitution = Substitution::from_iter([(
            x.clone(),
            term(&definition, r#"partial{}(\dv{SortS{}}("v"))"#),
        )]);
        let strict = |lhs: &Predicate, known: &[Predicate]| {
            strict_variables(&definition, lhs, &substitution, known)
        };
        let only_x = BTreeSet::from([x.clone()]);
        let none = BTreeSet::new();

        // `\ceil` and `\in` are strict in their operands.
        assert_eq!(strict(&Predicate::Ceil(f_x.clone()), &[]), only_x);
        assert_eq!(
            strict(&Predicate::In(f_x.clone(), value.clone()), &[]),
            only_x
        );
        // `\equals(f(X), "c")` is strict in `X`: the other side is a defined value.
        assert_eq!(
            strict(&Predicate::Equals(f_x.clone(), value.clone()), &[]),
            only_x
        );
        // `\equals(f(X), h(X))` is not: with `X` empty both sides are, and the equality holds.
        let both_sides = Predicate::Equals(f_x.clone(), h_x.clone());
        assert_eq!(strict(&both_sides, &[]), none);
        // It becomes strict once the path condition defines the other side.
        let h_defined = [
            Predicate::Ceil(term(&definition, r#"h{}(partial{}(\dv{SortS{}}("v")))"#)),
            Predicate::Ceil(term(&definition, r#"partial{}(\dv{SortS{}}("v"))"#)),
        ];
        assert_eq!(strict(&both_sides, &h_defined), only_x);
        // A term-level `\and` has no definedness witness: `Y /\ Z` is empty unless `Y = Z`, so
        // `\equals(f(X), Y /\ Z)` is not strict in `X` even though `ceil_term` derives nothing
        // for the conjunction of two element variables.
        let conjunction = term(&definition, r"\and{SortS{}}(Y:SortS{}, Z:SortS{})");
        assert_eq!(
            strict(&Predicate::Equals(f_x.clone(), conjunction.clone()), &[]),
            none
        );
        assert_eq!(
            strict(&Predicate::Equals(f_x.clone(), conjunction), &h_defined),
            none
        );
        // `\not(\equals(f(X), "c"))` is not: `\not(\bottom)` is `\top`.
        let negated = Predicate::Not(Box::new(Predicate::Equals(f_x.clone(), value.clone())));
        assert_eq!(strict(&negated, &[]), none);
        assert_eq!(strict(&Predicate::Floor(f_x.clone()), &[]), none);
        // A conjunction is strict in the variables of any conjunct, a disjunction only in
        // those of every disjunct.
        assert_eq!(
            strict(
                &Predicate::And(vec![negated.clone(), Predicate::Ceil(f_x.clone())]),
                &[]
            ),
            only_x
        );
        assert_eq!(
            strict(
                &Predicate::Or(vec![negated, Predicate::Ceil(f_x.clone())]),
                &[]
            ),
            none
        );
        assert_eq!(
            strict(
                &Predicate::Or(vec![Predicate::Ceil(h_x), Predicate::Ceil(f_x)]),
                &[]
            ),
            only_x
        );
    }

    /// B5: the fixed-point cache keeps equation heads and overloaded heads. An `anywhere`
    /// symbol that is a declared function is a function, evaluated on each simplification, so a
    /// closed application whose equation does not apply is returned unchanged and unmarked.
    #[test]
    fn anywhere_declared_function_is_not_cached_as_a_normal_form() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortS{} [hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                symbol cached{}(SortBool{}) : SortS{}
                    [anywhere{}(), function{}(), total{}(), no-evaluators{}()]
                axiom{R} \implies{R}(
                    \and{R}(
                        \top{R}(),
                        \and{R}(
                            \in{SortBool{}, R}(B:SortBool{}, \dv{SortBool{}}("true")),
                            \top{R}()
                        )
                    ),
                    \equals{SortS{}, R}(
                        cached{}(B:SortBool{}),
                        \and{SortS{}}(\dv{SortS{}}("result"), \top{SortS{}}())
                    )
                ) [label{}("cached-true"), anywhere{}()]
            endmodule []"#,
        )
        .expect("anywhere function definition should parse");
        let definition = BackendDefinition::internalize(&syntax, "MAIN")
            .expect("anywhere function definition should internalize");
        let input = term(&definition, r#"cached{}(\dv{SortBool{}}("false"))"#);

        let result = unstopped(simplify(
            &definition,
            &input,
            SimplificationOptions::default(),
        ))
        .expect("the incompatible equation should reach a fixed point");

        assert_eq!(result.term, input);
        assert!(result.applied_rules.is_empty());
        assert!(!result.term.attributes().evaluated);
    }

    /// A cancellation observed by the predicate simplifier is returned on the outer layer with
    /// its cause: no simplified conjunction and no failure stands in for it.
    #[test]
    fn a_stop_is_returned_on_the_outer_layer_with_its_cause() {
        let definition = definedness_definition();
        let predicates = vec![Predicate::Ceil(term(&definition, "partial{}(Y:SortS{})"))];
        let simplify = || {
            simplify_predicates_with_solver(
                &definition,
                &predicates,
                &[],
                SimplificationOptions::default(),
                &NoSolver,
            )
            .map_err(Stop::into_cause)
        };

        assert!(matches!(simplify(), Ok(Ok(_))), "{:?}", simplify());
        let token = stop::CancellationToken::new();
        token.cancel();
        assert_eq!(token.scope(simplify), Err(StopCause::Cancelled));
    }

    /// The layering rejects a fallback written against the single-layer result at compile time
    /// (the `compile_fail` example on `simplify_predicates_with_solver`), but a two-layer
    /// wildcard compiles and absorbs the stop as that fallback did. The unreported-stop checker
    /// catches it at run time: the stop the wildcard drops is dropped armed.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "was dropped without being propagated or published")]
    fn a_two_layer_wildcard_fallback_over_a_simplification_stop_panics() {
        let definition = definedness_definition();
        let predicates = vec![Predicate::Ceil(term(&definition, "partial{}(Y:SortS{})"))];
        let fallback = predicates.clone();
        let token = stop::CancellationToken::new();
        token.cancel();
        let _kept = token.scope(|| {
            match simplify_predicates_with_solver(
                &definition,
                &predicates,
                &[],
                SimplificationOptions::default(),
                &NoSolver,
            ) {
                Ok(Ok(simplified)) => simplified,
                _ => fallback,
            }
        });
    }
}
