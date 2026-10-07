//! ```toml algorithm
//! id = "backend.simplify.term"
//! name = "innermost equational simplification to a budgeted fixed point"
//! sites = ["simplify_with_optional_execution", "simplify_term_entry", "simplify", "simplify_with_solver", "simplify_with_budget", "simplify_children", "simplify_root", "failed_unspecified_frame", "hook_argument_definedness", "apply_theory", "apply_theory_noting_cuts"]
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
//! mode = "Unspecified application (UnspecifiedEvaluation)"
//! bound = "only at a root whose hook is Unspecified: one hash lookup in the stack of Unspecified applications with an open attempt (one not found is added to the innermost attempt's reads, at most 256 applications and keys), one in the records, each recorded evaluation checked against what it read (options, solver and console position, assumptions by content, the stack up to the deepest open attempt it reached, one pointer comparison while that prefix stands, the active rule-condition keys, the applications open now above that prefix, one pointer comparison while the stack it began on stands); per step taken on one, a frame of constant size (marks into the lineage's result, the console state); at the lineage's end, per frame that cut an occurrence, one walk of the outcome and of the conditions added since its step, each shared node once. Within one evaluation of an application each equation's step is taken at most once (a failed one is excluded for the rest of it); the value a nested lineage computed, and an evaluation that ended unevaluated after a failed attempt, are recorded with what they read until the outermost lineage that took such a step ends, and are not computed again wherever an evaluation would read the same (a failed one's later evaluation re-decides only the other equations' conditions), rule conditions included. Every rule condition adds its key to the innermost open attempt's reads (one thread-local access, nothing when none is open), as does a console hook at a root; at any root while an attempt is open, each equation attempt notes the lowest depth cut while it ran (one thread-local push and pop)"
//!
//! [[cost]]
//! mode = "report retraction (retract_dropped)"
//! bound = "only when the call raised a report of an equation passed over on a kept subterm: one search of the result's conditions and of the term nodes, in both, that lack the evaluated attribute (the part the simplifier walks), each shared node once, stopping when every subject is found"
//! ```
//!
//! ```toml algorithm
//! id = "backend.simplify.predicates"
//! name = "conjunct-set predicate normalization"
//! sites = ["simplify_predicates_with_solver", "simplify_predicates_entry", "predicate_conjunct_index", "simplify_predicates_with_budget", "known_defined_subterms", "simplify_predicate_with_budget"]
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
//! mode = "ceil conjunct (known_defined_subterms)"
//! bound = "only in a round with a \\ceil conjunct: one walk of the known predicates' asserted terms down to their ceil_free subterms, each distinct subterm hashed once, then one set lookup per \\ceil conjunct"
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

use std::{
    cell::{Cell, RefCell},
    collections::BTreeSet,
    fmt,
    sync::Arc,
};

use k_rust_kore::measure::{self, Algorithm, Counter};
use k_rust_kore::names::{BuiltinSort, WellKnownSymbol};
use rustc_hash::{FxHashMap, FxHashSet};

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
        FunctionType, HeadRole, Sort, Symbol, SymbolType, Term, TermKind, Variable, VariableKind,
        head::{
            CertifiedOnly, Head, NormalFormCertificate, RootComparison, classify_value,
            compare_roots,
        },
    },
    transition::{ExecutionEvaluationContext, ExecutionIoState},
};

mod result;
pub(crate) mod scan;

use result::{Accumulated, AccumulatedMark, HookOutcome};
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

/// The subterms of the terms that `known` states defined, as far as their definedness can be an
/// open obligation (`ceil_free` subterms are left out, since no `\ceil` of one is ever open).
///
/// Every KORE application is strict (`σ(.., \bottom, ..)` is `\bottom`), and so is a term-level
/// `\and` and a collection, so a term that denotes an element has defined subterms at every depth,
/// under partial symbols too. A known predicate states its term defined when it asserts that term
/// equal to a defined value: a Boolean term read as `true = P`, an equality one side of which is
/// provably defined (both sides then are), or `\ceil` of the term. A negation or a disjunction
/// states no term defined (`\not(t = 0)` holds where `t` is undefined), nor does a predicate
/// under a binder, whose variable it does not fix.
fn known_defined_subterms(definition: &BackendDefinition, known: &[Predicate]) -> FxHashSet<Term> {
    fn collect(term: &Term, subterms: &mut FxHashSet<Term>) {
        if term.attributes().ceil_free() || !subterms.insert(term.clone()) {
            return;
        }
        match term.kind() {
            TermKind::Application { arguments, .. } => {
                arguments
                    .iter()
                    .for_each(|argument| collect(argument, subterms));
            }
            TermKind::Injection { term, .. } => collect(term, subterms),
            TermKind::And(left, right) => {
                collect(left, subterms);
                collect(right, subterms);
            }
            TermKind::Map { entries, rest, .. } => {
                for (key, value) in entries {
                    collect(key, subterms);
                    collect(value, subterms);
                }
                if let Some(rest) = rest {
                    collect(rest, subterms);
                }
            }
            TermKind::List { heads, rest, .. } => {
                heads.iter().for_each(|head| collect(head, subterms));
                if let Some((middle, tails)) = rest {
                    collect(middle, subterms);
                    tails.iter().for_each(|tail| collect(tail, subterms));
                }
            }
            TermKind::Set { elements, rest, .. } => {
                elements
                    .iter()
                    .for_each(|element| collect(element, subterms));
                if let Some(rest) = rest {
                    collect(rest, subterms);
                }
            }
            TermKind::DomainValue { .. } | TermKind::Variable(_) => {}
        }
    }

    fn visit(
        definition: &BackendDefinition,
        known: &[Predicate],
        predicate: &Predicate,
        subterms: &mut FxHashSet<Term>,
    ) {
        let defined = |term: &Term| {
            term_is_provably_defined(definition, term, |obligation| known.contains(obligation))
        };
        match predicate {
            Predicate::And(conjuncts) => {
                for conjunct in conjuncts {
                    visit(definition, known, conjunct, subterms);
                }
            }
            Predicate::Term(term) | Predicate::Ceil(term) => collect(term, subterms),
            Predicate::Equals(left, right) if defined(left) || defined(right) => {
                collect(left, subterms);
                collect(right, subterms);
            }
            _ => {}
        }
    }

    let mut subterms = FxHashSet::default();
    for predicate in known {
        visit(definition, known, predicate, &mut subterms);
    }
    subterms
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
    // The path condition of the known predicates alone, under which a `\ceil` conjunct is
    // simplified: a sibling equality `t = c` would turn `\ceil(t)` into `\ceil(c)`, which
    // holds, and leave the definedness of `t` stated only by that equality. The equality is a
    // conjunct the solver may later decide valid with `t`'s SMT reading and drop; that reading
    // is exact only where `t` is defined, so the decision is a K one only while `\ceil(t)` is
    // stated beside it. The known predicates are kept by the caller, so their equalities may
    // rewrite it.
    let mut known_path_condition = None;
    // The terms the known predicates state defined, with their subterms, built at the first
    // `\ceil` conjunct: such a conjunct over one of them holds (`known_defined_subterms`). The
    // known predicates are kept by the caller, so the definedness stays stated by them.
    let mut known_defined = None;
    // The conjunct parts of the additional conjuncts simplified so far.
    let mut simplified_conjuncts = FxHashSet::default();
    let mut simplified = Vec::with_capacity(conjuncts.len());
    for (index, predicate) in conjuncts.iter().enumerate() {
        // The conjunct is not an assumption of its own simplification.
        if let Some(position) = additional_positions[index] {
            assumptions[position] = Predicate::True;
        }
        let result = if let Predicate::Ceil(subject) = predicate
            && known_defined
                .get_or_insert_with(|| known_defined_subterms(definition, known_predicates))
                .contains(subject)
        {
            Ok(Predicate::True)
        } else {
            let excluded_path_condition = (!conjunct_equalities[index].is_empty())
                .then(|| path_condition_excluding(&conjunct_equalities, Some(index)));
            let path_condition = if matches!(predicate, Predicate::Ceil(_)) {
                &*known_path_condition.get_or_insert_with(|| {
                    PathConditionReplacements::from_equalities(
                        known_equalities.iter().map(|(left, right)| (left, right)),
                    )
                })
            } else {
                match &excluded_path_condition {
                    Some(path_condition) => path_condition,
                    None => full_path_condition.get_or_insert_with(|| {
                        path_condition_excluding(&conjunct_equalities, None)
                    }),
                }
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
    let active = active_conditions.contains(&key);
    // An evaluation reused elsewhere must find the key as it found it here (`Reads`).
    UnspecifiedEvaluation::read_key(&key, active);
    if active {
        note_condition_reentry();
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
                let defined = size_bound_refusal(definition, &simplified.term)?.is_some();
                with_simplification_constraints(
                    simplified.conditions.into_predicates(),
                    if defined { Predicate::True } else { unchanged },
                )
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

/// The reason a hook's evaluator gives when `term`, a hooked application on constructor-like
/// arguments, has a result above a result size bound (`ResultTooLarge`); `None` for any other
/// term or outcome. An evaluator reports `ResultTooLarge` only where the hook has a value, so
/// such an application is defined: its `\ceil` holds although the value is not computed.
fn size_bound_refusal(
    definition: &BackendDefinition,
    term: &Term,
) -> SimplifyResult<Option<UnsupportedHookReason>> {
    let TermKind::Application {
        symbol, arguments, ..
    } = term.kind()
    else {
        return Ok(None);
    };
    if symbol.attributes.hook.is_none()
        || !arguments
            .iter()
            .all(|argument| argument.attributes().constructor_like)
    {
        return Ok(None);
    }
    Ok(
        match evaluate_builtin(term, definition)?.map_err(SimplificationError::Builtin)? {
            BuiltinResult::Unsupported(reason @ UnsupportedHookReason::ResultTooLarge { .. }) => {
                Some(reason)
            }
            _ => None,
        },
    )
}

/// Whether the backend leaves an application of the hooked `symbol` on constructor-like
/// arguments, which neither its evaluator nor an equation reduced, unevaluated with the
/// `UnsupportedHookUnevaluated` warning and refuses it only where a run uses its value
/// ([`refuse_uncomputed_applications`]), instead of failing with the unsupported-hook error at
/// once.
///
/// It does when the application denotes a value whatever the arguments and is not an effect:
/// the symbol is `total`, it is not declared `impure` (K's mark of an effect), and its hook is not
/// an `IO` operation (K's console and file operations, which this backend performs as effects
/// whatever the declaration says). Such an application is a value the backend does not compute,
/// as a result above a size bound is, and an error where the simplifier reaches it bottom-up
/// would fail a run on a subterm the semantics never consults (`false andBool B` is `false` for
/// every `B`). A partial hook's application is the error at once: its definedness is unknown
/// too, and every hook is strict, so even a discarded one would leave its `\ceil` as an undecided
/// condition the run refuses in the end. An effect is the error at once: left unevaluated, later
/// steps would run before it.
fn defers_uncomputed(definition: &BackendDefinition, symbol: &Symbol, hook: &str) -> bool {
    symbol.attributes.symbol_type == SymbolType::Function(FunctionType::Total)
        && !definition.is_impure(&symbol.name)
        && !hook.starts_with("IO.")
}

/// Why a hooked application on constructor-like arguments that neither its evaluator (whose
/// `outcome` is `None` for `NotApplicable`) nor an equation reduced has a value this backend
/// does not compute: no evaluator and no equations (`NotImplemented`), arguments the evaluator
/// does not support (`ArgumentOutOfRange`), an evaluator that did not reduce constructor-like
/// arguments, or a result above a size bound (`ResultTooLarge`). `None` when the definition
/// leaves the value open (`Unspecified`) or the symbol's equations define it (a hook without an
/// evaluator but with equations is an ordinary function).
fn uncomputed_reason(
    outcome: Option<UnsupportedHookReason>,
    has_equations: bool,
) -> Option<UnsupportedHookReason> {
    match outcome {
        Some(UnsupportedHookReason::NotImplemented) if has_equations => None,
        Some(UnsupportedHookReason::Unspecified { .. }) => None,
        Some(reason) => Some(reason),
        None => Some(UnsupportedHookReason::ArgumentOutOfRange {
            detail: "the evaluator did not reduce constructor-like arguments".into(),
        }),
    }
}

/// Whether the definition has function or simplification equations for `term`'s head.
fn has_equations(definition: &BackendDefinition, term: &Term) -> bool {
    let index = term_index(term);
    definition.function_theory().contains_key(&index)
        || definition.simplification_theory().contains_key(&index)
}

/// The reason to refuse `term`, a hooked application on constructor-like arguments that term
/// simplification left unevaluated although its value is determined: a result above a size
/// bound, or an uncomputed application the backend defers ([`defers_uncomputed`]). `None` for
/// any other term.
fn uncomputed_refusal(
    definition: &BackendDefinition,
    term: &Term,
) -> SimplifyResult<Option<UnsupportedHookReason>> {
    let TermKind::Application {
        symbol, arguments, ..
    } = term.kind()
    else {
        return Ok(None);
    };
    let Some(hook) = symbol.attributes.hook.as_deref() else {
        return Ok(None);
    };
    if !arguments
        .iter()
        .all(|argument| argument.attributes().constructor_like)
    {
        return Ok(None);
    }
    let outcome = match evaluate_builtin(term, definition)?.map_err(SimplificationError::Builtin)? {
        BuiltinResult::NotApplicable => None,
        BuiltinResult::Unsupported(reason) => Some(reason),
        BuiltinResult::Value(_) | BuiltinResult::Bottom | BuiltinResult::Effect(_) => {
            return Ok(None);
        }
    };
    Ok(
        match uncomputed_reason(outcome, has_equations(definition, term)) {
            Some(reason @ UnsupportedHookReason::ResultTooLarge { .. }) => Some(reason),
            Some(reason) if defers_uncomputed(definition, symbol, hook) => Some(reason),
            _ => None,
        },
    )
}

/// Fail with the unsupported-hook error of the first application in `term` or `predicates` whose
/// value is determined but not computed ([`uncomputed_refusal`]): a result above a result size
/// bound ([`UnsupportedHookReason::ResultTooLarge`]), or an application of a `total` pure hook
/// that neither an evaluator nor an equation reduced ([`defers_uncomputed`]).
///
/// Term simplification leaves such an application unevaluated without an error, so that a
/// subterm the simplification discards (`false andBool B`) neither costs nor fails anything,
/// and a state may carry one through steps that do not depend on its value. Its value is
/// determined but not computed, though, so a rule condition over it that the solver cannot
/// decide would let rules fire whose conditions are false (a branch the semantics does not
/// have), and a final configuration holding it would read as the semantics' answer. A rule
/// attempt checks the conditions it would carry (`rewrite::apply`), a search-pattern match the
/// condition it would report (`search`), and a step that finds the state stuck checks the state
/// (`rewrite::stuck`); each halts the state with the error. A condition the solver decided is not
/// carried and so never reaches this check.
///
/// The `\ceil` of such an application is not a use of its value: it holds (an evaluator reports
/// a size bound only where the hook is defined, `size_bound_refusal`, and the other kind is
/// `total`), and term simplification leaves it as the obligation of a discarded partial subterm
/// (`false andBool (2 ^Int N >Int 0)` is `false` under `\ceil(2 ^Int N)`).
///
/// Only subterms that are not `evaluated` are visited: an `evaluated` term is built from
/// constructors and domain values, or is certified a normal form, and neither holds such an
/// application. A state that is a value costs one look at its root.
pub(crate) fn refuse_uncomputed_applications(
    definition: &BackendDefinition,
    term: Option<&Term>,
    predicates: &[Predicate],
) -> Stoppable<Result<(), SimplificationError>> {
    let scan = || -> SimplifyResult<()> {
        let mut pending = term.into_iter().cloned().collect::<Vec<_>>();
        for predicate in predicates {
            push_predicate_terms(definition, predicate, &mut pending)?;
        }
        while let Some(term) = pending.pop() {
            if term.attributes().evaluated {
                continue;
            }
            if let Some(reason) = uncomputed_refusal(definition, &term)? {
                let TermKind::Application { symbol, .. } = term.kind() else {
                    unreachable!("only a hooked application is refused");
                };
                return Err(SimplificationError::UnsupportedHook {
                    hook: symbol
                        .attributes
                        .hook
                        .as_deref()
                        .expect("a hooked application")
                        .to_owned(),
                    reason,
                    term: term.clone(),
                }
                .into());
            }
            push_children(&term, &mut pending);
        }
        Ok(())
    };
    scan().layered()
}

/// Push the terms `predicate` carries onto `pending`, except the term of a `\ceil` that is itself
/// an application whose `\ceil` holds although its value is not computed: one above a result
/// size bound, or one of a `total` symbol.
fn push_predicate_terms(
    definition: &BackendDefinition,
    predicate: &Predicate,
    pending: &mut Vec<Term>,
) -> SimplifyResult<()> {
    match predicate {
        Predicate::Ceil(term) => {
            let total = matches!(term.kind(), TermKind::Application { symbol, .. }
                if symbol.attributes.symbol_type == SymbolType::Function(FunctionType::Total));
            if !total && size_bound_refusal(definition, term)?.is_none() {
                pending.push(term.clone());
            }
        }
        Predicate::Not(inner) | Predicate::Exists(_, inner) | Predicate::Forall(_, inner) => {
            push_predicate_terms(definition, inner, pending)?;
        }
        Predicate::And(inner) | Predicate::Or(inner) => {
            for predicate in inner {
                push_predicate_terms(definition, predicate, pending)?;
            }
        }
        Predicate::Implies(left, right) | Predicate::Iff(left, right) => {
            push_predicate_terms(definition, left, pending)?;
            push_predicate_terms(definition, right, pending)?;
        }
        Predicate::True
        | Predicate::False
        | Predicate::Term(_)
        | Predicate::Equals(..)
        | Predicate::Floor(_)
        | Predicate::In(..)
        | Predicate::Absent(_) => predicate.visit_terms(&mut |term| pending.push(term.clone())),
    }
    Ok(())
}

/// Push the immediate subterms of `term` onto `pending`.
fn push_children(term: &Term, pending: &mut Vec<Term>) {
    match term.kind() {
        TermKind::Application { arguments, .. } => pending.extend(arguments.iter().cloned()),
        TermKind::And(left, right) => pending.extend([left.clone(), right.clone()]),
        TermKind::Injection { term, .. } => pending.push(term.clone()),
        TermKind::Map { entries, rest, .. } => {
            for (key, value) in entries {
                pending.extend([key.clone(), value.clone()]);
            }
            pending.extend(rest.iter().cloned());
        }
        TermKind::List { heads, rest, .. } => {
            pending.extend(heads.iter().cloned());
            if let Some((middle, tails)) = rest {
                pending.push(middle.clone());
                pending.extend(tails.iter().cloned());
            }
        }
        TermKind::Set { elements, rest, .. } => {
            pending.extend(elements.iter().cloned());
            pending.extend(rest.iter().cloned());
        }
        TermKind::DomainValue { .. } | TermKind::Variable(_) => {}
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
    // The function-equation steps this lineage took on `Unspecified` applications, oldest first,
    // each an attempt that lasts to the end of the lineage (`UnspecifiedFrame`), and, after one
    // failed, the equations its application is retried without.
    let mut frames: Vec<UnspecifiedFrame> = Vec::new();
    let mut retry: Option<UnspecifiedRetry> = None;
    // The values this lineage's nested lineages computed for `Unspecified` applications, open
    // from the first such step on (`UnspecifiedValues`).
    let mut values: Option<UnspecifiedValues> = None;
    // Each round simplifies the children then the root; the rounds end on a fixed point, an
    // `evaluated` term, an exhausted budget, or a child's exhaustion; `remaining` grows only when
    // a failed attempt is undone. Invariant: `term` equals the input modulo `applied_rules` under
    // the accumulated conditions.
    loop {
        let end = 'rounds: loop {
            measure::bump(Counter::SimplifyRounds);
            // Neither the request's cancellation nor the step's deadline is bounded by the
            // iteration budget, which counts rewrites of one lineage rather than time, so every
            // round polls.
            stop::check()?;
            stop::check_stack()?;
            // A retried application is the subject of the step that failed: its children were
            // simplified in that round, and only its root is tried again.
            let retried = retry.take();
            let children = if retried.is_some() {
                Simplification::irreducible(term.clone())
            } else {
                if term.attributes().evaluated && !assumptions.path_condition.can_change(&term) {
                    measure::bump(Counter::SimplifyNodesSkippedEvaluated);
                    break 'rounds term;
                }
                term = assumptions.path_condition.apply(&term);
                if term.attributes().evaluated {
                    measure::bump(Counter::SimplifyNodesSkippedEvaluated);
                    break 'rounds term;
                }
                simplify_children(
                    definition,
                    &term,
                    assumptions,
                    options,
                    remaining,
                    active_conditions,
                    solver,
                    execution.as_deref_mut(),
                )?
            };
            let (root, root_step, root_equation, unspecified) = simplify_root(
                definition,
                &children.term,
                assumptions,
                options,
                active_conditions,
                solver,
                execution.as_deref_mut(),
                retried,
            )?;
            let children = accumulated.absorb(children);
            let mut before_step = unspecified.as_ref().map(|_| accumulated.mark());
            let root = accumulated.absorb(root);
            if accumulated.undefined_term.is_none() {
                // A child's own report comes first: it names the innermost equation. Otherwise
                // the undefined term arose in this lineage, after the last `total` step if there
                // was one. The root step of this round is not that step's cause: an equation's
                // result carries no undefined term, so a root report comes from a builtin or a
                // repeated collection.
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
            if let (Some(step), Some(mut before)) = (unspecified, before_step.take()) {
                // The step's own result carries no report, so the reports now are those of the
                // state the step was taken from.
                before.refresh_reports(&accumulated);
                let rule = root_equation
                    .clone()
                    .expect("an Unspecified step applies an equation");
                values.get_or_insert_with(UnspecifiedValues::open);
                frames.push(UnspecifiedFrame {
                    evaluation: step.evaluation,
                    application: children.term.clone(),
                    rule,
                    history: step.history,
                    before: LineageState {
                        accumulated: before,
                        total_step: total_step.clone(),
                        remaining: *remaining,
                        io: execution
                            .as_deref()
                            .map(ExecutionEvaluationContext::snapshot),
                        diagnostics: step.diagnostics,
                    },
                });
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
                break 'rounds root.term;
            }
            // A determined function step is the definition's own computation, not a rewrite the
            // simplifier chose, so it neither needs nor consumes budget (`RootStep`).
            let charged = root_step != RootStep::DeterminedFunctionStep;
            if charged && *remaining == 0 {
                match options.budget {
                    BudgetPolicy::Fail => {
                        return Err(SimplificationError::IterationLimit {
                            limit: options.max_iterations,
                            term: root.term,
                        }
                        .into());
                    }
                    BudgetPolicy::KeepPartial => {
                        accumulated.exhausted = Some(BudgetExhaustion {
                            limit: options.max_iterations,
                            subject: BudgetSubject::Term,
                        });
                        break 'rounds root.term;
                    }
                }
            }
            if accumulated.exhausted.is_some() {
                break 'rounds root.term;
            }
            if charged {
                *remaining -= 1;
            }
            term = root.term;
        };
        // The lineage has its outcome; each of its `Unspecified` steps is decided on it, the
        // latest first. A failed one is undone and its application tried again without it.
        let Some(failed) = failed_unspecified_frame(&frames, &end, &accumulated) else {
            if let Some(values) = &values
                && let Some(first) = frames.first()
            {
                values.record_in_enclosing(
                    first,
                    &end,
                    &accumulated,
                    execution.as_deref(),
                    &EvaluationGiven {
                        assumptions,
                        options,
                        active: active_conditions,
                        // Effect-free: the console is where it was when the evaluation began.
                        console: execution.as_deref().map(ExecutionEvaluationContext::cursor),
                        solver,
                    },
                );
            }
            return Ok(accumulated.finish(end));
        };
        frames.truncate(failed.index + 1);
        let frame = frames.pop().expect("the failed frame is the last one kept");
        let UnspecifiedFrame {
            evaluation,
            application,
            rule,
            mut history,
            before,
        } = frame;
        // What the failed attempt reached and whether its lineage ran out of budget stay facts
        // of the application's evaluation after the attempt is undone.
        history.reads.merge(&evaluation.reads_below(), usize::MAX);
        history.exhausted |= accumulated.exhausted.is_some();
        drop(evaluation);
        accumulated.rewind(&before.accumulated);
        total_step = before.total_step;
        *remaining = before.remaining;
        if let (Some(execution), Some(io)) = (execution.as_deref_mut(), before.io) {
            execution.restore(io);
        }
        diagnostic::discard_since(before.diagnostics);
        history.excluded.push(rule);
        history.contingent = min_depth(history.contingent, failed.contingent);
        retry = Some(history);
        term = application;
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

/// What `simplify_root` made of a root: the result, what produced it, the equation it applied,
/// and, for a function equation applied to an `Unspecified` application, the attempt the lineage
/// keeps open until it ends (`UnspecifiedFrame`).
type RootResult = (
    Simplification,
    RootStep,
    Option<Arc<RewriteRule>>,
    Option<UnspecifiedStep>,
);

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
#[allow(clippy::too_many_arguments)]
fn simplify_root(
    definition: &BackendDefinition,
    term: &Term,
    assumptions: &TermAssumptions<'_>,
    options: SimplificationOptions,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
    mut execution: Option<&mut ExecutionEvaluationContext>,
    retry: Option<UnspecifiedRetry>,
) -> SimplifyResult<RootResult> {
    let known_predicates = assumptions.predicates;
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
            None,
        ));
    }
    // A console hook reads the console when there is one, so an evaluation that reaches one
    // depends on whether it runs with it (`Reads`).
    if let TermKind::Application { symbol, .. } = term.kind()
        && let Some(hook) = symbol.attributes.hook.as_deref()
        && hook.starts_with("IO.")
        && matches!(hook, "IO.getc" | "IO.read" | "IO.putc" | "IO.write")
    {
        UnspecifiedEvaluation::read_console();
    }
    let builtin = match execution.as_deref_mut() {
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
                None,
            ));
        }
    };
    // The diagnostics of the indeterminate equation attempts of either theory, committed only if
    // neither theory rewrites the term.
    let mut indeterminate = IndeterminateAttempts::default();
    // An `Unspecified` verdict comes from the builtin documentation alone; the definition's
    // function equations are axioms about the symbol and give the application the value they
    // state. An equation is tried as an attempt that lasts from its `requires` to the end of the
    // lineage that takes its step (`UnspecifiedFrame`); one whose outcome still needs the
    // application's value gives none (`countAllOccurrences(S, "") = 1 +Int
    // countAllOccurrences(S, "")`) and is undone, and the others are still tried. The
    // application stays unevaluated, as the verdict leaves it, only if none gives a value.
    let unspecified = matches!(unsupported, Some(UnsupportedHookReason::Unspecified { .. }));
    // The lowest depth of the evaluation stack that this application is left unevaluated for
    // want of (`UnspecifiedEvaluation`): a failed attempt on it was contingent on an enclosing
    // attempt, or an undecided condition of one of its equations reached an occurrence cut for an
    // open attempt. Handed on if the application stays unevaluated.
    let mut contingent = None;
    // Whether this occurrence was cut: an attempt on the same application is open, which reports
    // the application if it stays unevaluated, while this occurrence only holds its place.
    let mut cut = false;
    let function_scan = if !unspecified {
        apply_theory_noting_cuts::<FunctionTheory>(
            definition,
            term,
            known_predicates,
            options,
            active_conditions,
            solver,
            &mut indeterminate,
            &mut contingent,
        )?
    } else if UnspecifiedEvaluation::reenter(term) {
        cut = true;
        TheoryScan::NotCacheable
    } else {
        // The console the evaluation would read: its position, when there is one. A failed
        // attempt's reads are undone, so an evaluation that ends unevaluated ends where it began.
        let given = EvaluationGiven {
            assumptions,
            options,
            active: active_conditions,
            console: execution.as_deref().map(ExecutionEvaluationContext::cursor),
            solver,
        };
        let recorded = UnspecifiedValues::recorded(term, &given);
        // A recorded value is the value an evaluation now would give; a recorded failure is where
        // its evaluation would end, so only its last scan is repeated (`UnspecifiedValues`). A
        // retry continues the application's evaluation.
        let mut history = match (retry, recorded) {
            (Some(history), _) => history,
            (None, Some((RecordedOutcome::Value(result, rule), reads))) => {
                UnspecifiedEvaluation::reach(&reads);
                let step =
                    if term.attributes().variables.is_empty() && result.conditions().is_empty() {
                        RootStep::DeterminedFunctionStep
                    } else {
                        RootStep::Other
                    };
                return Ok((result, step, Some(rule), None));
            }
            (
                None,
                Some((
                    RecordedOutcome::Failed {
                        excluded,
                        contingent,
                    },
                    reads,
                )),
            ) => {
                UnspecifiedEvaluation::reach(&reads);
                UnspecifiedRetry {
                    excluded,
                    contingent,
                    reads,
                    exhausted: false,
                }
            }
            (None, None) => UnspecifiedRetry::default(),
        };
        let diagnostics = diagnostic::mark();
        let mut opened = None;
        let scan =
            scan_term_theory::<FunctionTheory>(definition, term, &mut indeterminate, |rule| {
                // An equation whose attempt failed on this application is not tried again; it was
                // not refuted, so it keeps lower-priority equations from applying in its place.
                if history
                    .excluded
                    .iter()
                    .any(|failed| Arc::ptr_eq(failed, rule))
                {
                    return Ok(EquationAttempt::Recurred);
                }
                let evaluation = UnspecifiedEvaluation::enter(term);
                let attempt = apply_equation(
                    definition,
                    rule,
                    term,
                    known_predicates,
                    options,
                    active_conditions,
                    solver,
                )?;
                match attempt {
                    // The `requires` holds, with whatever it reached left as it is, so it holds for
                    // every value of what it reached; the attempt goes on in the lineage, which
                    // decides it on its outcome, the conditions its `ensures` left open included.
                    // A result that keeps the subject (`Simplification::bottom_subject`) states it
                    // empty and has no lineage.
                    EquationAttempt::Applied(result) => {
                        if result.term != *term {
                            opened = Some(evaluation);
                        } else if !result.constraints().contains(&Predicate::False) {
                            // The equation's result is the application itself (`A = A`): it
                            // states the application through itself and gives no value, as a
                            // result that still holds it after more steps does.
                            history.reads.merge(&evaluation.reads_below(), usize::MAX);
                            history.excluded.push(Arc::clone(rule));
                            return Ok(EquationAttempt::Recurred);
                        }
                        Ok(EquationAttempt::Applied(result))
                    }
                    // An undecided `requires` keeps the application unevaluated; if what it reached
                    // was an application below this one on the stack, that is contingent on the
                    // attempt that application is in.
                    EquationAttempt::Indeterminate(reason) => {
                        history.contingent =
                            min_depth(history.contingent, evaluation.contingent_cut());
                        history.reads.merge(&evaluation.reads_below(), usize::MAX);
                        Ok(EquationAttempt::Indeterminate(reason))
                    }
                    // A refuted `requires` was refuted with whatever it reached left as it is, so it
                    // is refuted for every value of it.
                    attempt => {
                        history.reads.merge(&evaluation.reads_below(), usize::MAX);
                        Ok(attempt)
                    }
                }
            })?;
        if let TheoryScan::Applied(result, rule) = scan {
            let step = if term.attributes().variables.is_empty() && result.conditions().is_empty() {
                RootStep::DeterminedFunctionStep
            } else {
                RootStep::Other
            };
            let unspecified = opened.map(|evaluation| UnspecifiedStep {
                evaluation,
                history,
                diagnostics,
            });
            return Ok((result, step, Some(rule), unspecified));
        }
        // The evaluation ends with the application unevaluated. If an attempt failed in it, it is
        // recorded with what it read, for later evaluations that would read the same.
        if !history.excluded.is_empty() && !history.exhausted {
            UnspecifiedValues::record_failed(term, &history, &given);
        }
        contingent = history.contingent;
        scan
    };
    if let TheoryScan::Applied(result, rule) = function_scan {
        let step = if term.attributes().variables.is_empty() && result.conditions().is_empty() {
            RootStep::DeterminedFunctionStep
        } else {
            RootStep::Other
        };
        return Ok((result, step, Some(rule), None));
    }
    let simplification_scan = match apply_theory_noting_cuts::<SimplificationTheory>(
        definition,
        term,
        known_predicates,
        options,
        active_conditions,
        solver,
        &mut indeterminate,
        &mut contingent,
    )? {
        TheoryScan::Applied(result, rule) => {
            return Ok((result, RootStep::Other, Some(rule), None));
        }
        scan => scan,
    };
    // No equation rewrote the term, which is kept: the indeterminate attempts explain why.
    indeterminate.commit(|| Subject::Term(term.clone()));
    // Kept only for want of a value an open attempt is computing, it is an occurrence cut for the
    // attempt that holds it (`UnspecifiedEvaluation`), and like a reentered occurrence it only
    // holds the place of an application reported where it stays unevaluated.
    if let Some(depth) = contingent {
        UnspecifiedEvaluation::cut(term, depth);
    }
    let placeholder = cut || (unspecified && contingent.is_some());
    let TermKind::Application {
        symbol, arguments, ..
    } = term.kind()
    else {
        debug_assert!(unsupported.is_none());
        return Ok((
            Simplification::irreducible(term.clone()),
            RootStep::Other,
            None,
            None,
        ));
    };
    let mut builtin_supported = unsupported.is_none();
    if let Some(hook) = symbol.attributes.hook.as_deref() {
        if arguments
            .iter()
            .all(|argument| argument.attributes().constructor_like)
        {
            let has_equations = has_equations(definition, term);
            // The application denotes a value the backend does not compute, and stays as that
            // unevaluated application, with a warning: a value the definition leaves open (no
            // implementation could compute it), one above a result size bound (a resource limit,
            // not a gap to fix), or one of a `total` pure hook neither an evaluator nor an
            // equation reduced (`defers_uncomputed`). Arguments are simplified bottom-up whether
            // or not their values are used, so an error here would fail a run on a subterm the
            // semantics never consults (`false andBool B` is `false` for every `B`). A run never
            // decides a condition over the last two kinds, nor ends stuck on them; see
            // `refuse_uncomputed_applications`. Any other uncomputed application is the error.
            let unevaluated = |reason| {
                diagnostic::emit(BackendDiagnostic::UnsupportedHookUnevaluated {
                    hook: hook.to_owned(),
                    reason,
                });
                None
            };
            let reason = match unsupported {
                Some(UnsupportedHookReason::Unspecified { .. }) if placeholder => None,
                Some(reason @ UnsupportedHookReason::Unspecified { .. }) => unevaluated(reason),
                outcome => match uncomputed_reason(outcome, has_equations) {
                    Some(reason @ UnsupportedHookReason::ResultTooLarge { .. }) => {
                        unevaluated(reason)
                    }
                    Some(reason) if defers_uncomputed(definition, symbol, hook) => {
                        builtin_supported = false;
                        unevaluated(reason)
                    }
                    reason => reason,
                },
            };
            if let Some(reason) = reason {
                return Err(SimplificationError::UnsupportedHook {
                    hook: hook.to_owned(),
                    reason,
                    term: term.clone(),
                }
                .into());
            }
        } else if let Some(reason) = unsupported
            && !placeholder
        {
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
    Ok((
        Simplification::irreducible(term),
        RootStep::Other,
        None,
        None,
    ))
}

/// A function equation applied to an `Unspecified` application by `simplify_root`, with what the
/// lineage needs to keep it as an [`UnspecifiedFrame`]: the application's entry on the
/// evaluation stack, the application's evaluation so far ([`UnspecifiedRetry`]), and the extent
/// of the diagnostics before the attempt.
struct UnspecifiedStep {
    evaluation: UnspecifiedEvaluation,
    history: UnspecifiedRetry,
    diagnostics: diagnostic::EmissionMark,
}

/// The evaluation of an `Unspecified` application so far, from its first scan: what a retry
/// after a failed attempt continues from, and what a failed evaluation leaves recorded
/// ([`UnspecifiedValues::record_failed`]).
///
/// `excluded` are the equations whose attempts failed, `contingent` the lowest stack depth any
/// failure, or any undecided `requires`, was contingent on, `reads` what its attempts read of
/// their surroundings ([`Reads`]), and `exhausted` whether an attempt's lineage ran out of
/// iteration budget, in which case its failure may be the budget's and it is not recorded.
#[derive(Default)]
struct UnspecifiedRetry {
    excluded: Vec<Arc<RewriteRule>>,
    contingent: Option<usize>,
    reads: Reads,
    exhausted: bool,
}

/// A rule condition being evaluated (`simplify_rule_predicates`): the rule and the term it is
/// evaluated for.
type ConditionKey = (String, Term);

/// The number of applications and condition keys a [`Reads`] lists before it keeps only the
/// sufficient check of its absences.
const READS_BOUND: usize = 256;

/// What an evaluation read of its surroundings, besides the term, the definition and what it is
/// given ([`EvaluationGiven`]): everything else that can make the same evaluation elsewhere
/// differ ([`UnspecifiedValues`]).
///
/// - `reached`: the deepest open attempt it reached below where it began (an occurrence cut for
///   it, or a record it reused that had reached it); the stack up to there is read.
/// - `absent`: the `Unspecified` applications it found with no attempt open (and evaluated, or
///   reused a record for).
/// - `active`: the rule-condition keys it found active, whose condition it left unsimplified;
///   `inserted`: those it found inactive, and evaluated.
/// - `console`: whether it reached a console hook, which reads the console when there is one: a
///   read takes the input from the console's position.
///
/// `absent` and `inserted` together hold at most [`READS_BOUND`] entries; past that `unbounded`
/// is set and they are dropped, and a record keeps only the sufficient check that nothing is open
/// or active now that was not when it began.
#[derive(Clone, Default)]
struct Reads {
    reached: Option<usize>,
    absent: FxHashSet<Term>,
    active: FxHashSet<ConditionKey>,
    inserted: FxHashSet<ConditionKey>,
    unbounded: bool,
    console: bool,
}

impl Reads {
    fn absent(&mut self, application: &Term) {
        if !self.unbounded {
            self.absent.insert(application.clone());
            self.bound();
        }
    }

    fn key(&mut self, key: &ConditionKey, active: bool) {
        if active {
            self.active.insert(key.clone());
        } else if !self.unbounded {
            self.inserted.insert(key.clone());
            self.bound();
        }
    }

    fn bound(&mut self) {
        if self.absent.len() + self.inserted.len() > reads_bound() {
            self.unbounded = true;
            self.absent = FxHashSet::default();
            self.inserted = FxHashSet::default();
        }
    }

    /// Add what `other` read, keeping of its `reached` only a depth below `below`.
    fn merge(&mut self, other: &Reads, below: usize) {
        self.reached = max_depth(self.reached, other.reached.filter(|&depth| depth < below));
        self.active.extend(other.active.iter().cloned());
        self.console |= other.console;
        if other.unbounded {
            self.unbounded = true;
            self.absent = FxHashSet::default();
            self.inserted = FxHashSet::default();
        } else if !self.unbounded {
            self.absent.extend(other.absent.iter().cloned());
            self.inserted.extend(other.inserted.iter().cloned());
            self.bound();
        }
    }
}

/// One attempt of a function equation `rule` on an `Unspecified` `application`, which a lineage
/// took as a step and keeps open until it reaches its outcome: the attempt is the equation's
/// `requires`, its step, and every round of the lineage after it.
///
/// The equation `application = rhs requires R` gives the application a value only if its
/// derivation does not state it through an application whose value is still being computed.
/// While the attempt is open, the application is on the evaluation stack, and evaluation leaves
/// every occurrence it reaches of an application on that stack as it is
/// (`UnspecifiedEvaluation`). Leaving an occurrence as it is, is the identity, so every result
/// of the lineage is still equal to the application; but a result that holds such an occurrence
/// states the application through itself (`c = 1 +Int c`), or through an application an
/// enclosing attempt is computing, and is no value of it. So the lineage decides the attempt on
/// its outcome (`failed_unspecified_frame`): it fails exactly when the outcome, its term or a
/// condition added since the step, holds an occurrence cut while the attempt was the innermost
/// one open. A failed attempt is undone entirely: the lineage returns to `before`, the state it
/// had before the step (its result so far, the provenance of an undefined term, the budget, the
/// console, the diagnostics), so a discarded attempt has no effect, and the application is
/// tried again without `rule`, continuing its evaluation `history` (`UnspecifiedRetry`); as it
/// applied, `rule` still keeps lower-priority equations from applying in its place.
struct UnspecifiedFrame {
    evaluation: UnspecifiedEvaluation,
    application: Term,
    rule: Arc<RewriteRule>,
    history: UnspecifiedRetry,
    before: LineageState,
}

/// The state of a lineage before a step on an `Unspecified` application, to which it returns if
/// that attempt fails.
struct LineageState {
    accumulated: AccumulatedMark,
    total_step: Option<(Term, Arc<RewriteRule>)>,
    remaining: usize,
    io: Option<ExecutionIoState>,
    diagnostics: diagnostic::EmissionMark,
}

/// The latest attempt of `frames` that fails on the lineage's outcome `end`, with the conditions
/// accumulated since its step (`UnspecifiedFrame`), and the lowest depth below its own it was
/// contingent on; `None` when every attempt gives its application a value.
///
/// The latest attempt is decided first: the earlier ones are open around it, and its retry may
/// change the outcome they are decided on.
fn failed_unspecified_frame(
    frames: &[UnspecifiedFrame],
    end: &Term,
    accumulated: &Accumulated,
) -> Option<FailedFrame> {
    frames.iter().enumerate().rev().find_map(|(index, frame)| {
        let cuts = frame.evaluation.cuts();
        if cuts.is_empty() {
            return None;
        }
        let held = held_cuts(
            &cuts,
            end,
            accumulated.constraints_since(&frame.before.accumulated),
        );
        (!held.is_empty()).then(|| FailedFrame {
            index,
            contingent: held
                .into_iter()
                .filter(|&depth| depth < frame.evaluation.depth)
                .min(),
        })
    })
}

/// An attempt that failed ([`failed_unspecified_frame`]): its index in the lineage's frames, and
/// the lowest stack depth below its own that an occurrence held by its outcome was cut at.
struct FailedFrame {
    index: usize,
    contingent: Option<usize>,
}

/// The stack depths of the cut occurrences `cuts` that `term` or `conditions` still hold.
fn held_cuts(cuts: &[(Term, usize)], term: &Term, conditions: &[Predicate]) -> Vec<usize> {
    let cut = cuts.iter().cloned().collect::<FxHashMap<Term, usize>>();
    let mut held = Vec::new();
    let mut visited = FxHashSet::default();
    let mut pending = vec![term.clone()];
    for condition in conditions {
        condition.visit_terms(&mut |term| pending.push(term.clone()));
    }
    while let Some(term) = pending.pop() {
        if !visited.insert(term.clone()) {
            continue;
        }
        if let Some(&depth) = cut.get(&term) {
            held.push(depth);
            continue;
        }
        push_children(&term, &mut pending);
    }
    held
}

fn min_depth(left: Option<usize>, right: Option<usize>) -> Option<usize> {
    match (left, right) {
        (Some(left), Some(right)) => Some(left.min(right)),
        (depth, None) | (None, depth) => depth,
    }
}

fn max_depth(left: Option<usize>, right: Option<usize>) -> Option<usize> {
    left.max(right)
}

thread_local! {
    /// The applications whose hook left them `Unspecified` and on which this thread has an
    /// equation attempt open, outermost first.
    static UNSPECIFIED_EVALUATIONS: RefCell<UnspecifiedStack> =
        RefCell::new(UnspecifiedStack::default());

    /// The records of [`UnspecifiedValues`], kept while a scope is open.
    static UNSPECIFIED_VALUES: RefCell<RecordTable> = RefCell::new(RecordTable::default());
}

#[cfg(feature = "test-switches")]
thread_local! {
    /// Whether this thread reuses evaluations of `Unspecified` applications
    /// ([`without_unspecified_reuse`]).
    static UNSPECIFIED_REUSE: Cell<bool> = const { Cell::new(true) };
}

/// Run `action` with the reuse of `Unspecified` evaluations turned off on this thread: no value a
/// nested lineage computed and no failed evaluation is recorded or served
/// ([`UnspecifiedValues`]), so every application is evaluated afresh where it is reached. Reuse is
/// memoization, so the results must not change; tests compare the two. Only with the
/// `test-switches` feature, which no normal build enables.
#[cfg(feature = "test-switches")]
pub fn without_unspecified_reuse<T>(action: impl FnOnce() -> T) -> T {
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            UNSPECIFIED_REUSE.set(self.0);
        }
    }
    let _restore = Restore(UNSPECIFIED_REUSE.replace(false));
    action()
}

#[cfg(feature = "test-switches")]
thread_local! {
    /// The bound of a [`Reads`] on this thread ([`with_reads_bound`]).
    static READS_BOUND_NOW: Cell<usize> = const { Cell::new(READS_BOUND) };
}

/// Run `action` with [`Reads`] bounded at `bound` entries on this thread in place of
/// [`READS_BOUND`], so that a test reaches the check a record keeps past its bound with small
/// definitions. Only with the `test-switches` feature.
#[cfg(feature = "test-switches")]
pub fn with_reads_bound<T>(bound: usize, action: impl FnOnce() -> T) -> T {
    struct Restore(usize);
    impl Drop for Restore {
        fn drop(&mut self) {
            READS_BOUND_NOW.set(self.0);
        }
    }
    let _restore = Restore(READS_BOUND_NOW.replace(bound));
    action()
}

/// The number of entries a [`Reads`] lists before it keeps only the sufficient check:
/// [`READS_BOUND`], except under [`with_reads_bound`].
#[inline(always)]
fn reads_bound() -> usize {
    #[cfg(feature = "test-switches")]
    {
        READS_BOUND_NOW.get()
    }
    #[cfg(not(feature = "test-switches"))]
    {
        READS_BOUND
    }
}

#[cfg(feature = "test-switches")]
thread_local! {
    /// How many times this thread found a rule condition it was asked to evaluate already being
    /// evaluated ([`condition_reentries`]).
    static CONDITION_REENTRIES: Cell<u64> = const { Cell::new(0) };
}

/// How many times this thread found a rule condition it was asked to evaluate already being
/// evaluated for the same term, and left it unsimplified (`simplify_rule_predicates`). Only with
/// the `test-switches` feature: a test uses it to tell an outcome that this re-entry left
/// undecided.
#[cfg(feature = "test-switches")]
pub fn condition_reentries() -> u64 {
    CONDITION_REENTRIES.get()
}

#[inline(always)]
fn note_condition_reentry() {
    #[cfg(feature = "test-switches")]
    CONDITION_REENTRIES.set(CONDITION_REENTRIES.get() + 1);
}

/// Whether evaluations of `Unspecified` applications are reused: always, except under
/// [`without_unspecified_reuse`].
#[inline(always)]
fn unspecified_reuse() -> bool {
    #[cfg(feature = "test-switches")]
    {
        UNSPECIFIED_REUSE.get()
    }
    #[cfg(not(feature = "test-switches"))]
    {
        true
    }
}

#[derive(Default)]
struct UnspecifiedStack {
    entries: Vec<StackEntry>,
    /// The depth of each entry's application; an application is entered only when it is not on
    /// the stack, so each has one depth.
    depths: FxHashMap<Term, usize>,
    /// At each depth, the prefix of the entry last removed there, which an entry for the same
    /// application on the same prefix shares, so that equal prefixes are mostly one object.
    vacated: Vec<Option<Arc<StackPrefix>>>,
    /// The equation attempts that note the lowest depth of an occurrence cut while they run,
    /// innermost last ([`CutWatch`]).
    watches: Vec<CutWatchState>,
}

/// An open attempt's application, with the occurrences evaluation cut while that attempt was the
/// innermost one open: each occurrence with the depth of the stack entry it was cut for.
/// `prefix` is the applications of this entry and every entry below it, and `reads` what the
/// evaluation read of its surroundings while this entry was the innermost one open, or in an
/// entry above it that was removed ([`Reads`], `reached` below this entry's own depth).
struct StackEntry {
    application: Term,
    cuts: Vec<(Term, usize)>,
    prefix: Arc<StackPrefix>,
    reads: Reads,
}

/// The applications on the evaluation stack from the bottom up to one entry, as a list sharing
/// its tail with the entries below.
struct StackPrefix {
    application: Term,
    below: Option<Arc<StackPrefix>>,
}

impl StackPrefix {
    /// Whether the two prefixes hold the same applications at the same depths.
    fn same(left: &Arc<Self>, right: &Arc<Self>) -> bool {
        let (mut left, mut right) = (left, right);
        loop {
            if Arc::ptr_eq(left, right) {
                return true;
            }
            if left.application != right.application {
                return false;
            }
            match (&left.below, &right.below) {
                (Some(below_left), Some(below_right)) => {
                    left = below_left;
                    right = below_right;
                }
                (None, None) => return true,
                _ => return false,
            }
        }
    }
}

/// An `Unspecified` application with an equation attempt open on it, from the equation's
/// `requires` to the end of the lineage that took its step ([`UnspecifiedFrame`]).
///
/// Evaluation that reaches an application on the stack leaves that occurrence as it is
/// ([`Self::reenter`]): its value is what an open attempt is computing. The occurrence is
/// recorded as cut for the innermost open attempt, whose outcome then gives no value if it still
/// holds it. If the reached application is that attempt's own, the attempt states it through
/// itself. If it is one below, an enclosing attempt's, the innermost attempt has failed only for
/// want of a value an enclosing attempt is computing; that failure is contingent, and the
/// innermost attempt's application is tried with its other equations. If none gives a value, the
/// application stays unevaluated, and that occurrence is in turn cut, at the reached depth, for
/// the attempt that holds it ([`Self::cut`], from `simplify_root`), so contingency is handed down
/// one open attempt at a time, and a failed attempt's cuts are dropped with it. An application of
/// any other kind whose equation's condition stayed undecided after reaching a cut occurrence is
/// left unevaluated for want of that value too, and is cut in the same way ([`CutWatch`]).
///
/// Each attempt is nested in the ones open when it started, so the entries form a stack;
/// dropping an entry removes it and every entry above it.
struct UnspecifiedEvaluation {
    depth: usize,
}

impl UnspecifiedEvaluation {
    fn enter(application: &Term) -> Self {
        UNSPECIFIED_EVALUATIONS.with_borrow_mut(|stack| {
            let depth = stack.entries.len();
            let below = stack.entries.last().map(|entry| Arc::clone(&entry.prefix));
            let prefix = match stack.vacated.get(depth) {
                Some(Some(vacated))
                    if vacated.application == *application
                        && match (&vacated.below, &below) {
                            (Some(left), Some(right)) => Arc::ptr_eq(left, right),
                            (None, None) => true,
                            _ => false,
                        } =>
                {
                    Arc::clone(vacated)
                }
                _ => Arc::new(StackPrefix {
                    application: application.clone(),
                    below,
                }),
            };
            stack.entries.push(StackEntry {
                application: application.clone(),
                cuts: Vec::new(),
                prefix,
                reads: Reads::default(),
            });
            stack.depths.insert(application.clone(), depth);
            Self { depth }
        })
    }

    /// Whether an attempt is open on `application`; if so, the occurrence is cut for the
    /// innermost open attempt.
    fn reenter(application: &Term) -> bool {
        UNSPECIFIED_EVALUATIONS.with_borrow_mut(|stack| {
            let Some(&depth) = stack.depths.get(application) else {
                if let Some(innermost) = stack.entries.last_mut() {
                    innermost.reads.absent(application);
                }
                return false;
            };
            record_cut(stack, application, depth);
            true
        })
    }

    /// Record that `application` was left unevaluated only for want of the value an attempt at
    /// `depth` is computing: it is cut, at that depth, for the innermost open attempt.
    fn cut(application: &Term, depth: usize) {
        UNSPECIFIED_EVALUATIONS.with_borrow_mut(|stack| record_cut(stack, application, depth));
    }

    /// Record that the innermost open attempt read what a record it reused read
    /// ([`UnspecifiedValues::recorded`]).
    fn reach(reads: &Reads) {
        UNSPECIFIED_EVALUATIONS.with_borrow_mut(|stack| {
            let depth = stack.entries.len().saturating_sub(1);
            if let Some(innermost) = stack.entries.last_mut() {
                innermost.reads.merge(reads, depth);
            }
        });
    }

    /// Record that the innermost open attempt found the rule-condition `key` active, or not.
    fn read_key(key: &ConditionKey, active: bool) {
        UNSPECIFIED_EVALUATIONS.with_borrow_mut(|stack| {
            if let Some(innermost) = stack.entries.last_mut() {
                innermost.reads.key(key, active);
            }
        });
    }

    /// Record that the innermost open attempt reached a console hook.
    fn read_console() {
        UNSPECIFIED_EVALUATIONS.with_borrow_mut(|stack| {
            if let Some(innermost) = stack.entries.last_mut() {
                innermost.reads.console = true;
            }
        });
    }

    /// Whether any attempt is open.
    fn any_open() -> bool {
        UNSPECIFIED_EVALUATIONS.with_borrow(|stack| !stack.entries.is_empty())
    }

    /// The occurrences cut for this attempt so far.
    fn cuts(&self) -> Vec<(Term, usize)> {
        UNSPECIFIED_EVALUATIONS.with_borrow(|stack| {
            stack
                .entries
                .get(self.depth)
                .map(|entry| entry.cuts.clone())
                .unwrap_or_default()
        })
    }

    /// The lowest depth below this attempt's own at which an occurrence was cut for it.
    fn contingent_cut(&self) -> Option<usize> {
        self.cuts()
            .into_iter()
            .map(|(_, depth)| depth)
            .filter(|&depth| depth < self.depth)
            .min()
    }

    /// What this attempt read of its surroundings while it was open, an open attempt reached
    /// counting only below its own depth.
    fn reads_below(&self) -> Reads {
        UNSPECIFIED_EVALUATIONS.with_borrow(|stack| {
            let mut reads = Reads::default();
            if let Some(entry) = stack.entries.get(self.depth) {
                reads.merge(&entry.reads, self.depth);
            }
            reads
        })
    }
}

fn record_cut(stack: &mut UnspecifiedStack, application: &Term, depth: usize) {
    let level = stack.entries.len();
    if let Some(watch) = stack.watches.last_mut()
        && watch.level == level
    {
        watch.lowest = min_depth(watch.lowest, Some(depth));
    }
    if let Some(innermost) = stack.entries.last_mut() {
        // An occurrence of its own application is its own work; only an attempt below it is a
        // read of its surroundings.
        if depth + 1 < level {
            innermost.reads.reached = max_depth(innermost.reads.reached, Some(depth));
        }
        if !innermost.cuts.iter().any(|(cut, _)| cut == application) {
            innermost.cuts.push((application.clone(), depth));
        }
    }
}

impl Drop for UnspecifiedEvaluation {
    fn drop(&mut self) {
        UNSPECIFIED_EVALUATIONS.with_borrow_mut(|stack| {
            let UnspecifiedStack {
                entries,
                depths,
                vacated,
                ..
            } = stack;
            let start = self.depth.min(entries.len());
            let mut reads = Reads::default();
            for (depth, entry) in entries.drain(start..).enumerate() {
                let depth = start + depth;
                depths.remove(&entry.application);
                if vacated.len() <= depth {
                    vacated.resize(depth + 1, None);
                }
                vacated[depth] = Some(entry.prefix);
                // What a removed attempt read (an open attempt reached below this one) was read
                // by the work of the attempt now innermost.
                reads.merge(&entry.reads, start);
            }
            if let Some(innermost) = entries.last_mut() {
                innermost.reads.merge(&reads, start - 1);
            }
        });
    }
}

/// What a [`CutWatch`] has noted.
struct CutWatchState {
    level: usize,
    lowest: Option<usize>,
}

/// The lowest stack depth of an occurrence cut, while one equation attempt runs that opens no
/// entry of its own (`apply_theory_noting_cuts`: every root scan but an `Unspecified`
/// application's function equations), for the innermost attempt open when it started. An
/// occurrence cut for an attempt opened during it is that attempt's own, and reaches this one only
/// if that application is left unevaluated for want of it ([`UnspecifiedEvaluation::cut`]).
struct CutWatch;

impl CutWatch {
    fn start() -> Self {
        UNSPECIFIED_EVALUATIONS.with_borrow_mut(|stack| {
            let level = stack.entries.len();
            stack.watches.push(CutWatchState {
                level,
                lowest: None,
            });
        });
        CutWatch
    }

    fn lowest(&self) -> Option<usize> {
        UNSPECIFIED_EVALUATIONS
            .with_borrow(|stack| stack.watches.last().and_then(|watch| watch.lowest))
    }
}

impl Drop for CutWatch {
    fn drop(&mut self) {
        UNSPECIFIED_EVALUATIONS.with_borrow_mut(|stack| {
            stack.watches.pop();
        });
    }
}

/// The assumptions of an evaluation by content: its known predicates other than `\top` (an
/// assumption that holds trivially assumes nothing) and its path-condition replacements.
struct AssumptionContent {
    predicates: Vec<Predicate>,
    substitution: Substitution,
    replacements: Vec<(Term, Term)>,
}

impl AssumptionContent {
    fn of(assumptions: &TermAssumptions<'_>) -> Self {
        Self {
            predicates: assumptions
                .predicates
                .iter()
                .filter(|predicate| **predicate != Predicate::True)
                .cloned()
                .collect(),
            substitution: assumptions.path_condition.substitution.clone(),
            replacements: assumptions.path_condition.replacements.clone(),
        }
    }

    fn holds(&self, assumptions: &TermAssumptions<'_>) -> bool {
        self.predicates.iter().eq(assumptions
            .predicates
            .iter()
            .filter(|predicate| **predicate != Predicate::True))
            && self.replacements == assumptions.path_condition.replacements
            && self.substitution == assumptions.path_condition.substitution
    }
}

/// The evaluation of an `Unspecified` application recorded for reuse: the value a nested lineage
/// gave it, with the equation of its first step, or a failed evaluation, which ended with it
/// unevaluated after some attempt failed: the equations that failed and the contingency it
/// handed on ([`UnspecifiedRetry`]).
#[derive(Clone)]
enum RecordedOutcome {
    Value(Simplification, Arc<RewriteRule>),
    Failed {
        excluded: Vec<Arc<RewriteRule>>,
        contingent: Option<usize>,
    },
}

/// What an evaluation of an `Unspecified` application is given besides the application and the
/// definition: the assumptions, the options and the active rule-condition keys it runs under,
/// the console's read position (if there is a console) and the solver that decides its
/// conditions.
struct EvaluationGiven<'a> {
    assumptions: &'a TermAssumptions<'a>,
    options: SimplificationOptions,
    active: &'a BTreeSet<ConditionKey>,
    console: Option<usize>,
    solver: &'a dyn SmtSolver,
}

/// The solver by address: a nested simplification (a ceil equation's predicates) decides its
/// conditions with another solver than the evaluation around it, which may decide fewer.
fn solver_address(solver: &dyn SmtSolver) -> usize {
    std::ptr::from_ref(solver).cast::<()>().addr()
}

/// One recorded evaluation, with everything a fresh evaluation at another point would read
/// differently ([`UnspecifiedValues`]).
struct Record {
    outcome: RecordedOutcome,
    assumptions: AssumptionContent,
    options: SimplificationOptions,
    solver: usize,
    /// The console's read position when the evaluation began, if there was a console.
    console: Option<usize>,
    reads: Reads,
    /// The stack up to `reads.reached`.
    reached: Option<Arc<StackPrefix>>,
    /// The stack and the active rule-condition keys when the evaluation began.
    stack: Option<Arc<StackPrefix>>,
    active: BTreeSet<ConditionKey>,
}

impl Record {
    /// Whether an evaluation of the application now would read what this one read at every step,
    /// and so compute the same outcome.
    fn holds(&self, stack: &UnspecifiedStack, given: &EvaluationGiven<'_>) -> bool {
        if self.options != given.options
            || self.solver != solver_address(given.solver)
            || (self.reads.console && self.console != given.console)
            || !self.assumptions.holds(given.assumptions)
        {
            return false;
        }
        let active = given.active;
        // The open attempts it reached are open at the same depths.
        let same_reached = match (self.reads.reached, &self.reached) {
            (Some(depth), Some(prefix)) => stack
                .entries
                .get(depth)
                .is_some_and(|entry| StackPrefix::same(&entry.prefix, prefix)),
            (None, None) => true,
            _ => false,
        };
        if !same_reached || !self.reads.active.iter().all(|key| active.contains(key)) {
            return false;
        }
        // No key it inserted is active now: none is active that was not when it began, or none of
        // those it inserted.
        let keys = active.iter().all(|key| self.active.contains(key))
            || (!self.reads.unbounded
                && active.iter().all(|key| !self.reads.inserted.contains(key)));
        if !keys {
            return false;
        }
        // No application it found not open is open now. Up to `reached` the stack is the one it
        // began on, whose applications it found open; above, every application open now was open
        // when it began, or is none of those it found not open.
        let above = &stack.entries[self.reads.reached.map_or(0, |depth| depth + 1)..];
        if above.is_empty() {
            return true;
        }
        let top = &stack.entries[stack.entries.len() - 1].prefix;
        if let Some(begun) = &self.stack
            && StackPrefix::same(top, begun)
        {
            return true;
        }
        let mut begun = FxHashSet::default();
        let mut prefix = self.stack.as_ref();
        while let Some(link) = prefix {
            begun.insert(&link.application);
            prefix = link.below.as_ref();
        }
        above.iter().all(|entry| begun.contains(&entry.application))
            || (!self.reads.unbounded
                && above
                    .iter()
                    .all(|entry| !self.reads.absent.contains(&entry.application)))
    }
}

/// The records of evaluations of `Unspecified` applications ([`UnspecifiedValues`]).
#[derive(Default)]
struct RecordTable {
    scopes: usize,
    records: FxHashMap<Term, Vec<Record>>,
}

/// The evaluations of `Unspecified` applications kept for reuse while a lineage that took a step
/// on one is open, so that an application evaluated in an attempt that failed is not evaluated
/// again when the next equation, or a rule condition, reaches it.
///
/// A lineage opens a scope when it takes its first step on an `Unspecified` application, the
/// only kind of lineage that retries, and closes it when it ends; the records are kept until the
/// outermost scope closes. A nested lineage whose first step was on such an application, and
/// whose attempts all gave values, records the application's value
/// ([`Self::record_in_enclosing`]); an evaluation that ended with the application unevaluated
/// after some attempt failed records the equations that failed and the contingency it handed on
/// ([`Self::record_failed`]). A value is recorded only if its derivation had no console effect,
/// no exhausted budget and no undefined term, a failure only if no attempt ran out of budget.
///
/// Reuse is memoization: a record is served ([`Self::recorded`]) only where an evaluation of the
/// application would read of its surroundings what the recorded one read ([`Reads`]): the open
/// attempts it reached at the same depths, none of the applications it found not open, the
/// rule-condition keys it found active and none of those it inserted, the console at the same
/// position (or no console) if it reached a console hook, the same options, the same solver and
/// the same assumptions by content (`\top` being no assumption) ([`EvaluationGiven`]). The
/// evaluation is a function of those reads, so it would compute the recorded outcome; a served
/// value is that evaluation's value, and a served failure starts the evaluation as its last
/// retry, the failed equations excluded and the same contingency handed on. The one difference
/// is the budget: a reused outcome does not spend what the evaluation would. What the record
/// read is added to the evaluation that serves it ([`UnspecifiedEvaluation::reach`]).
struct UnspecifiedValues;

impl UnspecifiedValues {
    fn open() -> Self {
        UNSPECIFIED_VALUES.with_borrow_mut(|table| table.scopes += 1);
        Self
    }

    /// The recorded evaluation of `application` that an evaluation now would repeat, with what it
    /// read.
    fn recorded(
        application: &Term,
        given: &EvaluationGiven<'_>,
    ) -> Option<(RecordedOutcome, Reads)> {
        if !unspecified_reuse() {
            return None;
        }
        UNSPECIFIED_VALUES.with_borrow(|table| {
            let records = table.records.get(application)?;
            UNSPECIFIED_EVALUATIONS.with_borrow(|stack| {
                records
                    .iter()
                    .find(|record| record.holds(stack, given))
                    .map(|record| (record.outcome.clone(), record.reads.clone()))
            })
        })
    }

    fn record(
        application: &Term,
        outcome: RecordedOutcome,
        mut reads: Reads,
        begun_below: usize,
        given: &EvaluationGiven<'_>,
    ) {
        if !unspecified_reuse() || UNSPECIFIED_VALUES.with_borrow(|table| table.scopes == 0) {
            return;
        }
        // A key it found active that it had inserted itself, and that was not active when it
        // began, is a read of its own work: it was active only inside its own evaluation of that
        // condition. A key active when it began is a read of its surroundings wherever it was
        // found active, even if the evaluation also met it where it was not (a condition decided
        // with no rule condition active).
        if !reads.unbounded {
            let inserted = std::mem::take(&mut reads.inserted);
            reads
                .active
                .retain(|key| !inserted.contains(key) || given.active.contains(key));
            reads.inserted = inserted;
        }
        let (reached, stack) = UNSPECIFIED_EVALUATIONS.with_borrow(|stack| {
            let prefix = |depth: usize| {
                stack
                    .entries
                    .get(depth)
                    .map(|entry| Arc::clone(&entry.prefix))
            };
            (
                reads.reached.and_then(prefix),
                begun_below.checked_sub(1).and_then(prefix),
            )
        });
        if reads.reached.is_some() && reached.is_none() {
            return;
        }
        let record = Record {
            outcome,
            assumptions: AssumptionContent::of(given.assumptions),
            options: given.options,
            solver: solver_address(given.solver),
            console: given.console,
            reads,
            reached,
            stack,
            active: given.active.clone(),
        };
        UNSPECIFIED_VALUES.with_borrow_mut(|table| {
            table
                .records
                .entry(application.clone())
                .or_default()
                .push(record);
        });
    }

    /// Record the evaluation `history` of `application`, which ended with the application
    /// unevaluated, begun on the stack as it is now.
    fn record_failed(application: &Term, history: &UnspecifiedRetry, given: &EvaluationGiven<'_>) {
        let depth = UNSPECIFIED_EVALUATIONS.with_borrow(|stack| stack.entries.len());
        Self::record(
            application,
            RecordedOutcome::Failed {
                excluded: history.excluded.clone(),
                contingent: history.contingent,
            },
            history.reads.clone(),
            depth,
            given,
        );
    }

    /// Record the value this lineage gave the application of its first `Unspecified` step
    /// `first`: the outcome `end` with what was accumulated since that step.
    fn record_in_enclosing(
        &self,
        first: &UnspecifiedFrame,
        end: &Term,
        accumulated: &Accumulated,
        execution: Option<&ExecutionEvaluationContext>,
        given: &EvaluationGiven<'_>,
    ) {
        if !unspecified_reuse() {
            return;
        }
        let effect_free = match (execution, &first.before.io) {
            (Some(execution), Some(io)) => execution.unchanged_since(io),
            (None, None) => true,
            _ => false,
        };
        if !effect_free
            || accumulated.exhausted.is_some()
            || accumulated.undefined_term.is_some()
            || *end == first.application
        {
            return;
        }
        // What the evaluation read: its failed attempts, and the attempts of this lineage still
        // open, the first one's and those above it.
        let depth = first.evaluation.depth;
        let mut reads = first.history.reads.clone();
        UNSPECIFIED_EVALUATIONS.with_borrow(|stack| {
            for entry in stack.entries.iter().skip(depth) {
                reads.merge(&entry.reads, depth);
            }
        });
        Self::record(
            &first.application,
            RecordedOutcome::Value(
                accumulated.since(&first.before.accumulated, end.clone()),
                Arc::clone(&first.rule),
            ),
            reads,
            depth,
            given,
        );
    }
}

impl Drop for UnspecifiedValues {
    fn drop(&mut self) {
        UNSPECIFIED_VALUES.with_borrow_mut(|table| {
            table.scopes -= 1;
            if table.scopes == 0 {
                table.records.clear();
            }
        });
    }
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

/// [`apply_theory`] at a root step while an `Unspecified` attempt is open, noting in `contingent`
/// the lowest stack depth of an occurrence cut while an equation whose condition then stayed
/// undecided was tried ([`CutWatch`]).
///
/// That condition may hold for some values of the occurrence, which an open attempt is computing,
/// and be refuted for others, so the term it keeps unrewritten is kept for want of that value
/// (`UnspecifiedEvaluation`). A condition that held, or was refuted, with the occurrence as it is
/// holds, or is refuted, for every value of it.
#[allow(clippy::too_many_arguments)]
fn apply_theory_noting_cuts<K: TermTheory>(
    definition: &BackendDefinition,
    term: &Term,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
    indeterminate: &mut IndeterminateAttempts,
    contingent: &mut Option<usize>,
) -> SimplifyResult<TheoryScan<K>> {
    if !UnspecifiedEvaluation::any_open() {
        return apply_theory::<K>(
            definition,
            term,
            known_predicates,
            options,
            active_conditions,
            solver,
            indeterminate,
        );
    }
    scan_term_theory::<K>(definition, term, indeterminate, |rule| {
        let watch = CutWatch::start();
        let attempt = apply_equation(
            definition,
            rule,
            term,
            known_predicates,
            options,
            active_conditions,
            solver,
        )?;
        if let EquationAttempt::Indeterminate(_) = attempt {
            *contingent = min_depth(*contingent, watch.lowest());
        }
        Ok(attempt)
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

    /// A value recorded with what its evaluation read: one computed with the console after
    /// reaching a console hook is not reused where there is none. `T = substr("abc", 4, 1)`
    /// reads the console (empty: nothing changes), `A = substr("abc", 2, 1) = g(T)` and `g(Z) =
    /// "seen" requires lengthString(T) == 0`: the condition is decided without the console, where
    /// `T` cannot be read, so `g("")` stays unevaluated, as it does with reuse turned off.
    #[cfg(feature = "test-switches")]
    #[test]
    fn a_value_read_from_the_console_is_not_reused_without_it() {
        let guard = |index: &str| {
            format!(
                r#"andBool{{}}(eqInt{{}}(I:SortInt{{}}, \dv{{SortInt{{}}}}("{index}")), eqInt{{}}(J:SortInt{{}}, \dv{{SortInt{{}}}}("1")))"#
            )
        };
        let t = r#"substr{}(\dv{SortString{}}("abc"), \dv{SortInt{}}("4"), \dv{SortInt{}}("1"))"#;
        let equation = |lhs: &str, requires: &str, rhs: &str, label: &str| {
            format!(
                r#"
                axiom{{R}} \implies{{R}}(
                    \and{{R}}(
                        \top{{R}}(),
                        \and{{R}}(
                            \equals{{SortBool{{}}, R}}({requires}, \dv{{SortBool{{}}}}("true")),
                            \top{{R}}()
                        )
                    ),
                    \equals{{SortString{{}}, R}}({lhs}, \and{{SortString{{}}}}({rhs}, \top{{SortString{{}}}}()))
                ) [label{{}}("{label}")]"#
            )
        };
        let substr = "substr{}(S:SortString{}, I:SortInt{}, J:SortInt{})";
        let source = format!(
            r#"[]
            module MAIN
                hooked-sort SortBool{{}} [hook{{}}("BOOL.Bool"), hasDomainValues{{}}()]
                hooked-sort SortString{{}} [hook{{}}("STRING.String"), hasDomainValues{{}}()]
                hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
                hooked-symbol substr{{}}(SortString{{}}, SortInt{{}}, SortInt{{}}) : SortString{{}}
                    [function{{}}(), total{{}}(), hook{{}}("STRING.substr")]
                hooked-symbol lengthString{{}}(SortString{{}}) : SortInt{{}}
                    [function{{}}(), total{{}}(), hook{{}}("STRING.length")]
                hooked-symbol eqInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
                    [function{{}}(), total{{}}(), hook{{}}("INT.eq")]
                hooked-symbol andBool{{}}(SortBool{{}}, SortBool{{}}) : SortBool{{}}
                    [function{{}}(), total{{}}(), hook{{}}("BOOL.and")]
                hooked-symbol readConsole{{}}(SortInt{{}}, SortInt{{}}) : SortString{{}}
                    [function{{}}(), hook{{}}("IO.read"), impure{{}}()]
                symbol g{{}}(SortString{{}}) : SortString{{}} [function{{}}(), total{{}}()]
                {g}
                {t_reads}
                {a_is_g}
            endmodule []"#,
            g = equation(
                "g{}(Z:SortString{})",
                &format!(r#"eqInt{{}}(lengthString{{}}({t}), \dv{{SortInt{{}}}}("0"))"#),
                r#"\dv{SortString{}}("seen")"#,
                "g"
            ),
            t_reads = equation(
                substr,
                &guard("4"),
                r#"readConsole{}(\dv{SortInt{}}("0"), \dv{SortInt{}}("1"))"#,
                "t"
            ),
            a_is_g = equation(substr, &guard("2"), &format!("g{{}}({t})"), "a"),
        );
        let syntax = parse_definition(&source).expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let a = term(
            &definition,
            r#"substr{}(\dv{SortString{}}("abc"), \dv{SortInt{}}("2"), \dv{SortInt{}}("1"))"#,
        );
        let run = || {
            let mut execution =
                crate::transition::ExecutionIoState::new(Vec::new()).begin_evaluation();
            let (result, _) = diagnostic::collect(|| {
                simplify_in_execution_with_solver(
                    &definition,
                    &a,
                    &[],
                    SimplificationOptions::default(),
                    &NoSolver,
                    &mut execution,
                )
            });
            unstopped(result).expect("no error").term
        };
        let reused = run();
        let fresh = without_unspecified_reuse(run);
        assert_eq!(reused, term(&definition, r#"g{}(\dv{SortString{}}(""))"#));
        assert_eq!(reused, fresh);
    }

    /// A failed evaluation that read the console is not reused once the console has moved on:
    /// its attempts read input that a later evaluation would not read. `F = substr("abc", 4, 1)
    /// = g(read())` with `g("x") = F ++ ""` (no value) and `g("y") = "v"`, inside `T =
    /// substr("abc", 5, 1) = F ++ read() ++ F` on the input `"xy"`: the first `F` reads `"x"`
    /// and fails (its read undone), `T` reads `"x"`, and the second `F` reads `"y"` and is `"v"`,
    /// as it is with reuse turned off.
    #[cfg(feature = "test-switches")]
    #[test]
    fn a_failed_evaluation_that_read_the_console_is_not_reused_after_it_moved_on() {
        let guard = |index: &str| {
            format!(
                r#"andBool{{}}(eqInt{{}}(I:SortInt{{}}, \dv{{SortInt{{}}}}("{index}")), eqInt{{}}(J:SortInt{{}}, \dv{{SortInt{{}}}}("1")))"#
            )
        };
        let f = r#"substr{}(\dv{SortString{}}("abc"), \dv{SortInt{}}("4"), \dv{SortInt{}}("1"))"#;
        let read = r#"readConsole{}(\dv{SortInt{}}("0"), \dv{SortInt{}}("1"))"#;
        let equation = |lhs: &str, requires: &str, rhs: &str, label: &str| {
            format!(
                r#"
                axiom{{R}} \implies{{R}}(
                    \and{{R}}(
                        \top{{R}}(),
                        \and{{R}}(
                            \equals{{SortBool{{}}, R}}({requires}, \dv{{SortBool{{}}}}("true")),
                            \top{{R}}()
                        )
                    ),
                    \equals{{SortString{{}}, R}}({lhs}, \and{{SortString{{}}}}({rhs}, \top{{SortString{{}}}}()))
                ) [label{{}}("{label}")]"#
            )
        };
        let substr = "substr{}(S:SortString{}, I:SortInt{}, J:SortInt{})";
        let is = |value: &str| {
            format!(r#"eqString{{}}(Z:SortString{{}}, \dv{{SortString{{}}}}("{value}"))"#)
        };
        let source = format!(
            r#"[]
            module MAIN
                hooked-sort SortBool{{}} [hook{{}}("BOOL.Bool"), hasDomainValues{{}}()]
                hooked-sort SortString{{}} [hook{{}}("STRING.String"), hasDomainValues{{}}()]
                hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
                hooked-symbol substr{{}}(SortString{{}}, SortInt{{}}, SortInt{{}}) : SortString{{}}
                    [function{{}}(), total{{}}(), hook{{}}("STRING.substr")]
                hooked-symbol concatString{{}}(SortString{{}}, SortString{{}}) : SortString{{}}
                    [function{{}}(), total{{}}(), hook{{}}("STRING.concat")]
                hooked-symbol eqString{{}}(SortString{{}}, SortString{{}}) : SortBool{{}}
                    [function{{}}(), total{{}}(), hook{{}}("STRING.eq")]
                hooked-symbol eqInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
                    [function{{}}(), total{{}}(), hook{{}}("INT.eq")]
                hooked-symbol andBool{{}}(SortBool{{}}, SortBool{{}}) : SortBool{{}}
                    [function{{}}(), total{{}}(), hook{{}}("BOOL.and")]
                hooked-symbol readConsole{{}}(SortInt{{}}, SortInt{{}}) : SortString{{}}
                    [function{{}}(), hook{{}}("IO.read"), impure{{}}()]
                symbol g{{}}(SortString{{}}) : SortString{{}} [function{{}}()]
                {g_x}
                {g_y}
                {f_is_g}
                {t_reads}
            endmodule []"#,
            g_x = equation(
                "g{}(Z:SortString{})",
                &is("x"),
                &format!(r#"concatString{{}}({f}, \dv{{SortString{{}}}}(""))"#),
                "g-x"
            ),
            g_y = equation(
                "g{}(Z:SortString{})",
                &is("y"),
                r#"\dv{SortString{}}("v")"#,
                "g-y"
            ),
            f_is_g = equation(substr, &guard("4"), &format!("g{{}}({read})"), "f"),
            t_reads = equation(
                substr,
                &guard("5"),
                &format!("concatString{{}}({f}, concatString{{}}({read}, {f}))"),
                "t"
            ),
        );
        let syntax = parse_definition(&source).expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let t = term(
            &definition,
            r#"substr{}(\dv{SortString{}}("abc"), \dv{SortInt{}}("5"), \dv{SortInt{}}("1"))"#,
        );
        let run = || {
            let mut execution =
                crate::transition::ExecutionIoState::new(b"xy".to_vec()).begin_evaluation();
            let (result, _) = diagnostic::collect(|| {
                simplify_in_execution_with_solver(
                    &definition,
                    &t,
                    &[],
                    SimplificationOptions::default(),
                    &NoSolver,
                    &mut execution,
                )
            });
            unstopped(result).expect("no error").term
        };
        let reused = run();
        let fresh = without_unspecified_reuse(run);
        let expected = term(
            &definition,
            &format!(r#"concatString{{}}({f}, \dv{{SortString{{}}}}("xv"))"#),
        );
        assert_eq!(reused, expected);
        assert_eq!(fresh, expected);
    }

    /// A value recorded under one solver is not reused under another, which may decide fewer of
    /// its conditions. `U = substr("abc", 4, 1)` is `"a"` if `g(3) > 0` (first priority), else
    /// `"v"`, with `g` given no equation: a solver that refutes every condition gives `"v"`; with
    /// none, the first equation's condition is undecided and `U` stays unevaluated, as it does
    /// when nothing was recorded before.
    #[test]
    fn a_value_computed_with_a_solver_is_not_reused_without_it() {
        /// Refutes every condition; not zero-sized, so it has an address of its own.
        struct Refuting(#[allow(dead_code)] u8);
        impl SmtSolver for Refuting {
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
        let equation = |requires: &str, rhs: &str, priority: &str| {
            format!(
                r#"
                axiom{{R}} \implies{{R}}(
                    \and{{R}}(
                        \equals{{SortBool{{}}, R}}({requires}, \dv{{SortBool{{}}}}("true")),
                        \and{{R}}(
                            \in{{SortString{{}}, R}}(X0:SortString{{}}, S:SortString{{}}),
                            \and{{R}}(
                                \in{{SortInt{{}}, R}}(X1:SortInt{{}}, \dv{{SortInt{{}}}}("4")),
                                \and{{R}}(
                                    \in{{SortInt{{}}, R}}(X2:SortInt{{}}, \dv{{SortInt{{}}}}("1")),
                                    \top{{R}}()
                                )
                            )
                        )
                    ),
                    \equals{{SortString{{}}, R}}(
                        substr{{}}(X0:SortString{{}}, X1:SortInt{{}}, X2:SortInt{{}}),
                        \and{{SortString{{}}}}({rhs}, \top{{SortString{{}}}}())
                    )
                ) [priority{{}}("{priority}")]"#
            )
        };
        let source = format!(
            r#"[]
            module MAIN
                hooked-sort SortBool{{}} [hook{{}}("BOOL.Bool"), hasDomainValues{{}}()]
                hooked-sort SortString{{}} [hook{{}}("STRING.String"), hasDomainValues{{}}()]
                hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
                hooked-symbol substr{{}}(SortString{{}}, SortInt{{}}, SortInt{{}}) : SortString{{}}
                    [function{{}}(), total{{}}(), hook{{}}("STRING.substr")]
                hooked-symbol gtInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
                    [function{{}}(), total{{}}(), hook{{}}("INT.gt"), smt-hook{{}}(">")]
                symbol g{{}}(SortInt{{}}) : SortInt{{}} [function{{}}(), total{{}}()]
                {}
                {}
            endmodule []"#,
            equation(
                r#"gtInt{}(g{}(\dv{SortInt{}}("3")), \dv{SortInt{}}("0"))"#,
                r#"\dv{SortString{}}("a")"#,
                "10"
            ),
            equation(
                r#"\dv{SortBool{}}("true")"#,
                r#"\dv{SortString{}}("v")"#,
                "20"
            ),
        );
        let syntax = parse_definition(&source).expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let u = term(
            &definition,
            r#"substr{}(\dv{SortString{}}("abc"), \dv{SortInt{}}("4"), \dv{SortInt{}}("1"))"#,
        );
        let evaluate = |solver: &dyn SmtSolver| {
            let (result, _) = diagnostic::collect(|| {
                simplify_with_solver(
                    &definition,
                    &u,
                    &[],
                    SimplificationOptions::default(),
                    solver,
                )
            });
            unstopped(result).expect("no error").term
        };
        let fresh = evaluate(&NoSolver);
        assert_eq!(fresh, u);
        let _scope = UnspecifiedValues::open();
        assert_eq!(
            evaluate(&Refuting(0)),
            term(&definition, r#"\dv{SortString{}}("v")"#)
        );
        assert_eq!(evaluate(&NoSolver), fresh);
    }

    /// A rule-condition key that was active around an evaluation stays among what it read, even
    /// if the evaluation also found it inactive (in a nested simplification with no rule
    /// condition active, as a ceil equation's predicates are): where that key is not active, a
    /// fresh evaluation decides the condition it left unsimplified, so the record is not served.
    /// A key it found active only inside its own evaluation of that condition is its own work.
    #[test]
    fn a_record_keeps_a_rule_condition_key_active_around_it_among_its_reads() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortString{} [hook{}("STRING.String"), hasDomainValues{}()]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let application = term(&definition, r#"\dv{SortString{}}("application")"#);
        let around: ConditionKey = (
            "around".to_owned(),
            term(&definition, r#"\dv{SortString{}}("k")"#),
        );
        let own: ConditionKey = (
            "own".to_owned(),
            term(&definition, r#"\dv{SortString{}}("k")"#),
        );
        let path_condition = PathConditionReplacements::new(&[]);
        let assumptions = TermAssumptions {
            predicates: &[],
            path_condition: &path_condition,
        };
        let given = |active: &BTreeSet<ConditionKey>| {
            UnspecifiedValues::recorded(
                &application,
                &EvaluationGiven {
                    assumptions: &assumptions,
                    options: SimplificationOptions::default(),
                    active,
                    console: None,
                    solver: &NoSolver,
                },
            )
            .is_some()
        };
        let _scope = UnspecifiedValues::open();
        // It found both keys inactive, then both active; `around` was active when it began.
        let mut reads = Reads::default();
        reads.key(&around, false);
        reads.key(&own, false);
        reads.key(&around, true);
        reads.key(&own, true);
        let began = BTreeSet::from([around.clone()]);
        UnspecifiedValues::record(
            &application,
            RecordedOutcome::Failed {
                excluded: Vec::new(),
                contingent: None,
            },
            reads,
            0,
            &EvaluationGiven {
                assumptions: &assumptions,
                options: SimplificationOptions::default(),
                active: &began,
                console: None,
                solver: &NoSolver,
            },
        );
        assert!(given(&began));
        assert!(!given(&BTreeSet::new()));
    }

    /// A recorded evaluation carries everything its evaluation read, and serving it adds that to
    /// the evaluation that serves it. `Z = substr("abc", 4, 1) = "z"` is evaluated, and so read
    /// not open, by `X = keep(Z, "x")` (a value, in its attempt), by `X2 = keep(Z, X2)` (a
    /// failure, in its failed attempt), and by the refuted `requires` (`lengthString(Z) == 5`) of
    /// `V`'s first equation, which is the first priority, before `V = "v"` (a value, in an
    /// attempt before its own). Each equation is stated for its application alone, so no other
    /// evaluation reads `Z`. Evaluated twice inside the same open attempt, the second evaluation
    /// of each is served from its record, and the attempt has read that `Z` was not open.
    #[test]
    fn a_served_evaluation_adds_what_it_read_to_the_attempt_that_serves_it() {
        let at = |index: &str| {
            format!(
                r#"substr{{}}(\dv{{SortString{{}}}}("abc"), \dv{{SortInt{{}}}}("{index}"), \dv{{SortInt{{}}}}("1"))"#
            )
        };
        // The arguments are matched through `\in` constraints before the `requires` is decided.
        let equation = |index: &str, requires: &str, rhs: &str, attributes: &str| {
            format!(
                r#"
                axiom{{R}} \implies{{R}}(
                    \and{{R}}(
                        \equals{{SortBool{{}}, R}}({requires}, \dv{{SortBool{{}}}}("true")),
                        \and{{R}}(
                            \in{{SortString{{}}, R}}(X0:SortString{{}}, S:SortString{{}}),
                            \and{{R}}(
                                \in{{SortInt{{}}, R}}(X1:SortInt{{}}, \dv{{SortInt{{}}}}("{index}")),
                                \and{{R}}(
                                    \in{{SortInt{{}}, R}}(X2:SortInt{{}}, \dv{{SortInt{{}}}}("1")),
                                    \top{{R}}()
                                )
                            )
                        )
                    ),
                    \equals{{SortString{{}}, R}}(
                        substr{{}}(X0:SortString{{}}, X1:SortInt{{}}, X2:SortInt{{}}),
                        \and{{SortString{{}}}}({rhs}, \top{{SortString{{}}}}())
                    )
                ) [{attributes}]"#
            )
        };
        let z = at("4");
        let always = r#"\dv{SortBool{}}("true")"#;
        let source = format!(
            r#"[]
            module MAIN
                hooked-sort SortBool{{}} [hook{{}}("BOOL.Bool"), hasDomainValues{{}}()]
                hooked-sort SortString{{}} [hook{{}}("STRING.String"), hasDomainValues{{}}()]
                hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
                hooked-symbol substr{{}}(SortString{{}}, SortInt{{}}, SortInt{{}}) : SortString{{}}
                    [function{{}}(), total{{}}(), hook{{}}("STRING.substr")]
                hooked-symbol lengthString{{}}(SortString{{}}) : SortInt{{}}
                    [function{{}}(), total{{}}(), hook{{}}("STRING.length")]
                hooked-symbol eqInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
                    [function{{}}(), total{{}}(), hook{{}}("INT.eq")]
                symbol keep{{}}(SortString{{}}, SortString{{}}) : SortString{{}} [function{{}}(), total{{}}()]
                axiom{{R}} \implies{{R}}(
                    \and{{R}}(\top{{R}}(), \and{{R}}(\top{{R}}(), \top{{R}}())),
                    \equals{{SortString{{}}, R}}(
                        keep{{}}(K:SortString{{}}, L:SortString{{}}),
                        \and{{SortString{{}}}}(L:SortString{{}}, \top{{SortString{{}}}}())
                    )
                ) [label{{}}("keep")]
                {}
            endmodule []"#,
            [
                equation("4", always, r#"\dv{SortString{}}("z")"#, r#"label{}("z")"#),
                equation(
                    "3",
                    always,
                    &format!(r#"keep{{}}({z}, \dv{{SortString{{}}}}("x"))"#),
                    r#"label{}("x")"#
                ),
                equation(
                    "5",
                    always,
                    &format!("keep{{}}({z}, {})", at("5")),
                    r#"label{}("x2")"#
                ),
                equation(
                    "7",
                    &format!(r#"eqInt{{}}(lengthString{{}}({z}), \dv{{SortInt{{}}}}("5"))"#),
                    r#"\dv{SortString{}}("a")"#,
                    r#"label{}("v-refuted"), priority{}("10")"#
                ),
                equation(
                    "7",
                    always,
                    r#"\dv{SortString{}}("v")"#,
                    r#"label{}("v"), priority{}("20")"#
                ),
            ]
            .concat()
        );
        let syntax = parse_definition(&source).expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let z = term(&definition, &z);
        let open = term(&definition, &at("9"));
        let _scope = UnspecifiedValues::open();
        for (index, value) in [("3", Some("x")), ("5", None), ("7", Some("v"))] {
            let input = term(&definition, &at(index));
            let evaluate = || {
                let attempt = UnspecifiedEvaluation::enter(&open);
                let (result, _) = diagnostic::collect(|| {
                    simplify(&definition, &input, SimplificationOptions::default())
                });
                let result = unstopped(result).expect("no error").term;
                (result, attempt.reads_below())
            };
            let expected = match value {
                Some(value) => term(&definition, &format!(r#"\dv{{SortString{{}}}}("{value}")"#)),
                None => input.clone(),
            };
            let (first, first_reads) = evaluate();
            assert_eq!(first, expected, "substr(abc, {index}, 1), first");
            assert!(
                first_reads.absent.contains(&z),
                "substr(abc, {index}, 1), first"
            );
            let (served, served_reads) = evaluate();
            assert_eq!(served, expected, "substr(abc, {index}, 1), served");
            assert!(
                served_reads.absent.contains(&z),
                "substr(abc, {index}, 1), served"
            );
        }
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
