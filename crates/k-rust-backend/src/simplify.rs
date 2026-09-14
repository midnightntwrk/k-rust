//! Innermost (bottom-up) equational rewriting to a budgeted fixed point with priority groups,
//! builtin hooks, and evaluated-attribute memoisation (Booster ApplyEquations): cost O(rounds x
//! |term| x candidates per node), rounds <= `max_iterations` per lineage;
//! `Counter::SimplifyRounds`, `Counter::SimplifyEquationAttempts`,
//! `Counter::SimplifyBuiltinEvaluations` (row B7).
//! Conjunct-set predicate normalisation with an `FxHashSet` conjunct index, O(1) membership per
//! conjunct, budget-bounded re-entry through the ceil and predicate theories (row B8).

use std::{
    cell::Cell,
    collections::{BTreeMap, BTreeSet},
    fmt,
    sync::Arc,
};

use k_rust_kore::measure::{self, Counter};
use k_rust_kore::names::{BuiltinSort, WellKnownSymbol};
use rustc_hash::FxHashSet;

use crate::{
    builtin::{
        BuiltinEffect, BuiltinError, BuiltinResult, UnsupportedHookReason,
        evaluate_in_definition as evaluate_builtin,
        evaluate_in_execution as evaluate_builtin_in_execution, k_sequence_item,
    },
    cancellation::cancellation_requested,
    definedness::ceil_term,
    definition::BackendDefinition,
    diagnostic::{self, BackendDiagnostic},
    matching::{
        InjectionEquality, MatchMode, MatchResult, match_collection_remainders_all_in_definition,
        match_injection_equality, match_term_pairs_in_definition, match_terms_in_definition,
    },
    rewrite::{
        Pattern, Truth, check_concreteness, normalize_pattern_substitution, predicates_truth,
        retain_substitution_predicates, substitute_predicates, violates_finite_constructor_domain,
    },
    rule::{
        Predicate, PredicateRewriteRule, RewriteRule, RuleRhs, Theory, applicable_groups,
        term_index,
    },
    smt::{NoSolver, SmtError, SmtSolver, TranslationError, Validity},
    substitution::{Substitution, compose, substitute, substitution_binding},
    term::{FunctionType, Sort, SymbolType, Term, TermKind, Variable, VariableKind},
    transition::ExecutionEvaluationContext,
};

/// Default equation iterations allowed for each simplification fixed point.
pub const DEFAULT_MAX_SIMPLIFICATION_ITERATIONS: usize = 100;

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum BudgetPolicy {
    #[default]
    Fail,
    KeepPartial,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
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
    /// Evaluate to a fixed point without Booster's equation-iteration bound.
    ///
    /// This mirrors the legacy Kore simplifier used as the complete fallback by
    /// `kore-rpc-booster`. Cancellation tokens and step deadlines still interrupt
    /// evaluation; the iteration counter itself does not.
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Simplification {
    pub term: Term,
    pub constraints: Vec<Predicate>,
    pub applied_rules: Vec<String>,
    pub effects: Vec<BuiltinEffect>,
    pub exhausted: Option<BudgetExhaustion>,
    /// The innermost partial builtin application that evaluated to bottom.
    ///
    /// Rewrite execution uses this provenance to report the exact definedness
    /// obligation that made a successor empty. It is deliberately separate from
    /// `constraints`: other simplification paths can also produce `false`.
    pub undefined_term: Option<Term>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct PatternSimplification {
    pub pattern: Pattern,
    pub applied_rules: Vec<String>,
    pub effects: Vec<BuiltinEffect>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SimplificationError {
    Cancelled,
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

pub fn simplify(
    definition: &BackendDefinition,
    term: &Term,
    options: SimplificationOptions,
) -> Result<Simplification, SimplificationError> {
    simplify_with_solver(definition, term, &[], options, &NoSolver)
}

pub fn simplify_with_solver(
    definition: &BackendDefinition,
    term: &Term,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Result<Simplification, SimplificationError> {
    simplify_with_optional_execution(definition, term, known_predicates, options, solver, None)
}

pub(crate) fn simplify_in_execution_with_solver(
    definition: &BackendDefinition,
    term: &Term,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
    execution: &mut ExecutionEvaluationContext,
) -> Result<Simplification, SimplificationError> {
    simplify_with_optional_execution(
        definition,
        term,
        known_predicates,
        options,
        solver,
        Some(execution),
    )
}

fn simplify_with_optional_execution(
    definition: &BackendDefinition,
    term: &Term,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
    execution: Option<&mut ExecutionEvaluationContext>,
) -> Result<Simplification, SimplificationError> {
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
) -> Result<Pattern, SimplificationError> {
    Ok(simplify_pattern_details_with_solver(definition, pattern, options, solver)?.pattern)
}

/// Simplify a constrained term while retaining the equation trace and builtin effects produced
/// by term simplification. Execution needs this richer form when normalizing terminal, cut-point,
/// and branching payloads before returning them to a caller.
pub(crate) fn simplify_pattern_details_with_solver(
    definition: &BackendDefinition,
    pattern: &Pattern,
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Result<PatternSimplification, SimplificationError> {
    let mut pattern = pattern.clone();
    let retained_substitution =
        normalize_pattern_substitution(&mut pattern, &definition.sort_graph);
    let simplified = simplify_with_solver(
        definition,
        &pattern.term,
        &pattern.constraints,
        options,
        solver,
    )?;
    let mut constraints = pattern.constraints;
    for constraint in simplified.constraints {
        if !constraints.contains(&constraint) {
            constraints.push(constraint);
        }
    }
    let mut constraints =
        simplify_predicates_with_solver(definition, &constraints, &[], options, solver)?;
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
        &definition.sort_graph,
    );
    let mut pattern = Pattern {
        term: simplified.term,
        constraints,
    };
    normalize_pattern_substitution(&mut pattern, &definition.sort_graph);
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
) -> Result<Vec<Predicate>, SimplificationError> {
    let mut pending = std::collections::VecDeque::from(constraints);
    let mut retained = Vec::with_capacity(pending.len());
    while let Some(constraint) = pending.pop_front() {
        if substitution_binding(&constraint, &definition.sort_graph).is_some() {
            retained.push(constraint);
            continue;
        }
        let known = retained
            .iter()
            .chain(pending.iter())
            .cloned()
            .collect::<Vec<_>>();
        match decide_condition(std::slice::from_ref(&constraint), &known, solver) {
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
                });
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

pub fn simplify_predicates_with_solver(
    definition: &BackendDefinition,
    predicates: &[Predicate],
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Result<Vec<Predicate>, SimplificationError> {
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
        Err(
            SimplificationError::IterationLimit { .. }
            | SimplificationError::PredicateIterationLimit { .. },
        ) if options.budget == BudgetPolicy::KeepPartial => {
            diagnostic::emit(BackendDiagnostic::SimplificationBudgetExhausted {
                limit: options.max_iterations,
                subject: BudgetSubject::Predicates,
            });
            Ok(predicates.to_vec())
        }
        result => result,
    }
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

fn predicate_conjunct_index(predicates: &[Predicate]) -> FxHashSet<Predicate> {
    fn insert(predicate: &Predicate, index: &mut FxHashSet<Predicate>) {
        if let Predicate::And(conjuncts) = predicate {
            for conjunct in conjuncts {
                insert(conjunct, index);
            }
        } else {
            index.insert(predicate.clone());
        }
    }

    let mut index = FxHashSet::default();
    for predicate in predicates {
        insert(predicate, &mut index);
    }
    index
}

fn simplify_predicates_with_budget(
    definition: &BackendDefinition,
    predicates: &[Predicate],
    known_predicates: &[Predicate],
    limit: usize,
    remaining: &mut usize,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
) -> Result<Vec<Predicate>, SimplificationError> {
    let mut conjuncts = Vec::new();
    let mut conjunct_index = FxHashSet::default();
    for predicate in predicates {
        extend_conjuncts(&mut conjuncts, &mut conjunct_index, predicate);
    }
    let known_index = predicate_conjunct_index(known_predicates);
    let mut all_assumptions = known_index.clone();
    all_assumptions.extend(conjunct_index.iter().cloned());
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
    let mut all_equalities = known_equalities;
    let additional_equality_positions = conjuncts
        .iter()
        .enumerate()
        .map(|(index, predicate)| {
            additional_positions[index]?;
            let Predicate::Equals(left, right) = predicate else {
                return None;
            };
            let position = all_equalities.len();
            all_equalities.push((left, right));
            Some(position)
        })
        .collect::<Vec<_>>();
    let full_path_condition =
        PathConditionReplacements::from_equalities(all_equalities.iter().copied());
    let mut simplified = Vec::with_capacity(conjuncts.len());
    for (index, predicate) in conjuncts.iter().enumerate() {
        let excluded = additional_positions[index]
            .map(|position| std::mem::replace(&mut assumptions[position], Predicate::True));
        let result = {
            let excluded_path_condition = additional_equality_positions[index].map(|excluded| {
                PathConditionReplacements::from_equalities(
                    all_equalities
                        .iter()
                        .enumerate()
                        .filter_map(|(position, equality)| {
                            (position != excluded).then_some(*equality)
                        }),
                )
            });
            let path_condition = excluded_path_condition
                .as_ref()
                .unwrap_or(&full_path_condition);
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
        };
        if let (Some(position), Some(excluded)) = (additional_positions[index], excluded) {
            assumptions[position] = excluded;
        }
        simplified.push(result?);
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
        });
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
) -> Result<Vec<Predicate>, SimplificationError> {
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

#[derive(Clone, Debug, Eq, PartialEq)]
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
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum RuleCondition {
    Satisfied,
    Refuted,
    Indeterminate(ConditionIndeterminacy),
}

#[allow(clippy::too_many_arguments)]
fn evaluate_rule_condition(
    definition: &BackendDefinition,
    rule_id: &str,
    anchor: Option<&Term>,
    predicates: Vec<Predicate>,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
) -> Result<RuleCondition, SimplificationError> {
    let predicates = if let Some(anchor) = anchor {
        simplify_rule_predicates(
            definition,
            (rule_id, anchor),
            &predicates,
            known_predicates,
            options,
            active_conditions,
            solver,
        )
        .unwrap_or(predicates)
    } else {
        predicates
    };
    decide_rule_condition(rule_id, &predicates, known_predicates, solver)
}

/// Decide already simplified condition predicates under the path condition, reporting a
/// verdict the solver could not reach as a diagnostic of `rule_id`.
fn decide_rule_condition(
    rule_id: &str,
    predicates: &[Predicate],
    known_predicates: &[Predicate],
    solver: &dyn SmtSolver,
) -> Result<RuleCondition, SimplificationError> {
    let condition = decide_condition(predicates, known_predicates, solver).map_err(|error| {
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
        });
    }
    Ok(condition)
}

/// Decide whether `predicates` hold under `known_predicates` and the definition's `smt-lemma`
/// axioms.
///
/// Syntactic truth and membership in `known_predicates` are decided without the solver. The
/// solver answers the rest within the timeout and retry bounds it was created with; the
/// `Indeterminate` verdict names why it did not decide, including a query the SMT encoding
/// could not pose, which leaves the predicates as open constraints. `Err` reports a solver
/// failure other than those. The rewriter's `requires` check, standalone predicate
/// simplification, and the residual-constraint discharge of pattern simplification all share
/// this decision.
pub(crate) fn decide_condition(
    predicates: &[Predicate],
    known_predicates: &[Predicate],
    solver: &dyn SmtSolver,
) -> Result<RuleCondition, SmtError> {
    match predicates_truth(predicates) {
        Truth::False => return Ok(RuleCondition::Refuted),
        Truth::True => return Ok(RuleCondition::Satisfied),
        Truth::Unknown => {}
    }
    if predicates
        .iter()
        .all(|predicate| known_predicates.contains(predicate))
    {
        return Ok(RuleCondition::Satisfied);
    }
    match solver.check_predicates(known_predicates, &Substitution::new(), predicates) {
        Ok(Validity::Valid) => Ok(RuleCondition::Satisfied),
        Ok(Validity::Invalid) => Ok(RuleCondition::Refuted),
        Ok(Validity::Indeterminate) => Ok(RuleCondition::Indeterminate(
            ConditionIndeterminacy::ImplicationIndeterminate,
        )),
        Ok(Validity::InconsistentGroundTruth) => Ok(RuleCondition::Indeterminate(
            ConditionIndeterminacy::InconsistentPathCondition,
        )),
        Ok(Validity::Unknown(message)) => Ok(RuleCondition::Indeterminate(
            ConditionIndeterminacy::SmtUnknown(message),
        )),
        Err(SmtError::Unavailable) => Ok(RuleCondition::Indeterminate(
            ConditionIndeterminacy::NoSolver,
        )),
        Err(SmtError::Translation(error)) => Ok(RuleCondition::Indeterminate(
            ConditionIndeterminacy::Untranslatable(error),
        )),
        Err(error) => Err(error),
    }
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
) -> Result<Predicate, SimplificationError> {
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
) -> Result<Predicate, SimplificationError> {
    let simplified =
        simplify_predicate_with_solver(definition, predicate, known_predicates, options, solver)?;
    if matches!(simplified, Predicate::True | Predicate::False) {
        return Ok(simplified);
    }
    match decide_condition(std::slice::from_ref(&simplified), known_predicates, solver) {
        Ok(RuleCondition::Satisfied) => Ok(Predicate::True),
        Ok(RuleCondition::Refuted) => Ok(Predicate::False),
        Ok(RuleCondition::Indeterminate(reason)) => {
            report_undecided_predicate(&simplified, reason);
            Ok(simplified)
        }
        Err(error) => Err(SimplificationError::SmtPredicate {
            predicate: Box::new(simplified),
            error,
        }),
    }
}

fn simplify_predicate_with_budget(
    definition: &BackendDefinition,
    predicate: &Predicate,
    assumptions: &PredicateAssumptions<'_>,
    limit: usize,
    remaining: &mut usize,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
) -> Result<Predicate, SimplificationError> {
    if cancellation_requested() {
        return Err(SimplificationError::Cancelled);
    }
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
            let simplified = simplify_term(term)?;
            with_simplification_constraints(
                simplified.constraints,
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
                if simplified.constraints.is_empty() {
                    simplified.term.clone()
                } else {
                    original.clone()
                }
            };
            let use_left = simplified_left.constraints.is_empty()
                || provably_defined(&witness(right, &simplified_right));
            let use_right = simplified_right.constraints.is_empty()
                || provably_defined(&witness(left, &simplified_left));
            let mut constraints = Vec::new();
            let left = if use_left {
                constraints.extend(simplified_left.constraints);
                simplified_left.term
            } else {
                left.clone()
            };
            let right = if use_right {
                constraints.extend(simplified_right.constraints);
                simplified_right.term
            } else {
                right.clone()
            };
            let equality =
                normalize_hooked_boolean_predicate(definition, Predicate::Equals(left, right));
            let equality = normalize_injection_equality(definition, equality);
            let equality = match equality {
                Predicate::Equals(left, right)
                    if left.structurally_distinct_after_normalization(&right) =>
                {
                    Predicate::False
                }
                equality => equality,
            };
            with_simplification_constraints(constraints, equality)
        }
        Predicate::Ceil(term) => {
            let simplified = simplify_term(term)?;
            let unchanged = Predicate::Ceil(simplified.term.clone());
            let mut expanded = ceil_term(definition, &simplified.term);
            // An opaque parent ceil remains a conjunct after expansion. Do not repeatedly
            // add child ceils already supplied by the surrounding conjunction.
            expanded.retain(|predicate| !assumptions.contains(predicate));
            if expanded.as_slice() == [unchanged.clone()] {
                with_simplification_constraints(simplified.constraints, unchanged)
            } else {
                // The expansion supplies the definedness of the subterms as sibling conjuncts,
                // and a conditional ceil equation on the parent is decided under them only by
                // a further pass over the conjunction. Take that pass here, so that an entry
                // without a surrounding conjunction fixed point reaches the equation too.
                let mut constraints = simplified.constraints;
                constraints.extend(expanded);
                let conjunction = Predicate::And(constraints);
                if *remaining == 0 {
                    return Err(SimplificationError::PredicateIterationLimit {
                        limit,
                        predicate: conjunction,
                    });
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
            if simplified.constraints.is_empty() {
                Predicate::Floor(simplified.term)
            } else {
                Predicate::Floor(term.clone())
            }
        }
        Predicate::In(left, right) => {
            let left = simplify_term(left)?;
            let right = simplify_term(right)?;
            let mut constraints = left.constraints;
            constraints.extend(right.constraints);
            with_simplification_constraints(constraints, Predicate::In(left.term, right.term))
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
            let inner = simplify_predicate_with_budget(
                definition,
                inner,
                assumptions,
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
    )? {
        if *remaining == 0 {
            return Err(SimplificationError::PredicateIterationLimit {
                limit,
                predicate: simplified,
            });
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
    )?
    else {
        return Ok(simplified);
    };
    if *remaining == 0 {
        return Err(SimplificationError::PredicateIterationLimit {
            limit,
            predicate: simplified,
        });
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
    match match_injection_equality(Some(&definition.sort_graph), &left, &right) {
        Some(InjectionEquality::Direct(left, right) | InjectionEquality::Split(left, right)) => {
            normalize_hooked_boolean_predicate(definition, Predicate::Equals(left, right))
        }
        Some(InjectionEquality::Distinct) => Predicate::False,
        Some(InjectionEquality::Unknown) | None => Predicate::Equals(left, right),
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

fn apply_ceil_theory(
    definition: &BackendDefinition,
    predicate: &Predicate,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
) -> Result<Option<Predicate>, SimplificationError> {
    let Predicate::Ceil(term) = predicate else {
        return Ok(None);
    };
    let groups = applicable_groups(&definition.ceil_theory, &term_index(term));
    for rules in groups.values() {
        match scan_group(rules, |rule| {
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
            GroupScan::ContextDependent | GroupScan::NotApplicable => {}
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
) -> Result<EquationAttempt<Predicate>, SimplificationError> {
    let substitution =
        match match_terms_in_definition(MatchMode::Evaluate, definition, &rule.lhs, term) {
            MatchResult::Failed(_) => return Ok(EquationAttempt::NotApplicable),
            MatchResult::Indeterminate {
                substitution,
                remainder,
            } => {
                let Some(matches) = match_collection_remainders_all_in_definition(
                    MatchMode::Evaluate,
                    definition,
                    substitution,
                    &remainder,
                ) else {
                    return Ok(EquationAttempt::Indeterminate(
                        ConditionIndeterminacy::ImplicationIndeterminate,
                    ));
                };
                let Some(substitution) = matches.into_iter().next() else {
                    return Ok(EquationAttempt::NotApplicable);
                };
                substitution
            }
            MatchResult::Success(substitution) => substitution,
        };
    if substitution
        .keys()
        .any(|variable| !rule.lhs.attributes().variables.contains(variable))
        || check_concreteness(rule, &substitution).is_some()
    {
        return Ok(EquationAttempt::NotApplicable);
    }
    if binds_element_variable_to_set_pattern(&substitution) {
        return Ok(EquationAttempt::Indeterminate(
            ConditionIndeterminacy::NonFunctionalBinding,
        ));
    }

    let conditions = equation_match_conditions(definition, &rule.requires, &substitution);
    match evaluate_rule_condition(
        definition,
        &rule.attributes.unique_id,
        Some(term),
        conditions.requires,
        known_predicates,
        options,
        active_conditions,
        solver,
    )? {
        RuleCondition::Satisfied => {}
        RuleCondition::Refuted => return Ok(EquationAttempt::NotApplicable),
        RuleCondition::Indeterminate(reason) => {
            return Ok(EquationAttempt::Indeterminate(reason));
        }
    }

    let RuleRhs::Predicates(rhs) = &rule.rhs else {
        return Ok(EquationAttempt::NotApplicable);
    };
    // The subject `\ceil(f(t))` is strict in every term `t` bound to an element variable:
    // `\ceil(\bottom)` is `\bottom`. So `\ceil(f(t)) = \ceil(t) /\ q[t]` under the equation
    // `\ceil(f(X)) = q[X]`, an open obligation is conjoined to the result and a refuted one
    // makes the subject `\bottom`.
    let mut result = substitute_predicates(rhs, &substitution);
    match decide_definedness(
        definition,
        &rule.attributes.unique_id,
        Some(term),
        conditions.definedness,
        known_predicates,
        options,
        active_conditions,
        solver,
    )? {
        DefinednessVerdict::Discharged => {}
        DefinednessVerdict::Open(obligations) => result.extend(obligations),
        DefinednessVerdict::Refuted => return Ok(EquationAttempt::Applied(Predicate::False)),
    }
    Ok(EquationAttempt::Applied(normalize_predicate(
        Predicate::And(result),
    )))
}

fn apply_predicate_theory(
    definition: &BackendDefinition,
    predicate: &Predicate,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
) -> Result<Option<Predicate>, SimplificationError> {
    for rules in definition.predicate_simplification_theory.values() {
        match scan_group(rules, |rule| {
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
            GroupScan::ContextDependent | GroupScan::NotApplicable => {}
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
) -> Result<EquationAttempt<Predicate>, SimplificationError> {
    let substitution = match match_predicate(definition, &rule.lhs, predicate) {
        PredicateMatch::Failed => return Ok(EquationAttempt::NotApplicable),
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
    let conditions = equation_match_conditions(definition, &rule.requires, &substitution);
    match evaluate_rule_condition(
        definition,
        &rule.attributes.unique_id,
        first_predicate_term(predicate),
        conditions.requires,
        known_predicates,
        options,
        active_conditions,
        solver,
    )? {
        RuleCondition::Satisfied => {}
        RuleCondition::Refuted => return Ok(EquationAttempt::NotApplicable),
        RuleCondition::Indeterminate(reason) => {
            return Ok(EquationAttempt::Indeterminate(reason));
        }
    }
    let mut result = substitute_predicates(&rule.rhs, &substitution);
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
    let obligated = obligated_variables(definition, &substitution, &conditions.definedness);
    match decide_definedness(
        definition,
        &rule.attributes.unique_id,
        first_predicate_term(predicate),
        conditions.definedness,
        known_predicates,
        options,
        active_conditions,
        solver,
    )? {
        DefinednessVerdict::Discharged => {}
        DefinednessVerdict::Open(obligations) => {
            let strict = strict_variables(definition, &rule.lhs, &substitution, known_predicates);
            if !obligated.is_subset(&strict) {
                return Ok(EquationAttempt::Indeterminate(
                    ConditionIndeterminacy::ImplicationIndeterminate,
                ));
            }
            result.extend(obligations);
        }
        DefinednessVerdict::Refuted => {
            let strict = strict_variables(definition, &rule.lhs, &substitution, known_predicates);
            if !obligated.is_subset(&strict) {
                return Ok(EquationAttempt::NotApplicable);
            }
            return Ok(EquationAttempt::Applied(Predicate::False));
        }
    }
    Ok(EquationAttempt::Applied(normalize_predicate(
        Predicate::And(result),
    )))
}

/// The element variables of `substitution` whose binding raised one of the obligations in
/// `definedness` (`EquationConditions::definedness`): those bound to a term that may be empty
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
fn term_is_provably_defined(
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

fn match_predicate(
    definition: &BackendDefinition,
    pattern: &Predicate,
    subject: &Predicate,
) -> PredicateMatch {
    let mut pairs = Vec::new();
    if !collect_predicate_term_pairs(pattern, subject, &mut pairs) {
        return PredicateMatch::Failed;
    }
    match match_term_pairs_in_definition(
        MatchMode::Evaluate,
        definition,
        pairs
            .into_iter()
            .map(|(pattern, subject)| (pattern.clone(), subject.clone())),
    ) {
        MatchResult::Success(substitution) => PredicateMatch::Success(substitution),
        MatchResult::Failed(_) => PredicateMatch::Failed,
        MatchResult::Indeterminate { .. } => PredicateMatch::Indeterminate,
    }
}

fn collect_predicate_term_pairs<'a>(
    pattern: &'a Predicate,
    subject: &'a Predicate,
    pairs: &mut Vec<(&'a Term, &'a Term)>,
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
        (Predicate::Not(left), Predicate::Not(right)) => {
            collect_predicate_term_pairs(left, right, pairs)
        }
        (Predicate::And(left), Predicate::And(right))
        | (Predicate::Or(left), Predicate::Or(right))
            if left.len() == right.len() =>
        {
            left.iter()
                .zip(right)
                .all(|(left, right)| collect_predicate_term_pairs(left, right, pairs))
        }
        (Predicate::Implies(left_a, left_b), Predicate::Implies(right_a, right_b))
        | (Predicate::Iff(left_a, left_b), Predicate::Iff(right_a, right_b)) => {
            collect_predicate_term_pairs(left_a, right_a, pairs)
                && collect_predicate_term_pairs(left_b, right_b, pairs)
        }
        (Predicate::Exists(left_var, left), Predicate::Exists(right_var, right))
        | (Predicate::Forall(left_var, left), Predicate::Forall(right_var, right))
            if left_var == right_var =>
        {
            collect_predicate_term_pairs(left, right, pairs)
        }
        _ => false,
    }
}

fn first_predicate_term(predicate: &Predicate) -> Option<&Term> {
    match predicate {
        Predicate::True | Predicate::False => None,
        Predicate::Term(term) | Predicate::Ceil(term) | Predicate::Floor(term) => Some(term),
        Predicate::Equals(left, _) | Predicate::In(left, _) => Some(left),
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
        .sort_graph
        .check_subsort(&left_sort, &right_sort)
        .ok()?
    {
        return Some((
            Term::injection(left_sort, right_sort, left.clone()),
            right.clone(),
        ));
    }
    if definition
        .sort_graph
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
) -> Result<Simplification, SimplificationError> {
    let mut term = term.clone();
    let mut constraints = Vec::new();
    let mut applied_rules = Vec::new();
    let mut effects = Vec::new();
    let mut exhausted = None;
    let mut undefined_term = None;
    // Each round simplifies the children then the root; the loop exits on a fixed point, an
    // `evaluated` term, an exhausted budget, or a child's exhaustion; `remaining` never grows.
    // Invariant: `term` equals the input modulo `applied_rules` under `constraints`.
    loop {
        measure::bump(Counter::SimplifyRounds);
        if cancellation_requested() {
            return Err(SimplificationError::Cancelled);
        }
        if term.attributes().evaluated && !assumptions.path_condition.can_change(&term) {
            measure::bump(Counter::SimplifyNodesSkippedEvaluated);
            return Ok(Simplification {
                term,
                constraints,
                applied_rules,
                effects,
                exhausted,
                undefined_term,
            });
        }
        term = assumptions.path_condition.apply(&term);
        if term.attributes().evaluated {
            measure::bump(Counter::SimplifyNodesSkippedEvaluated);
            return Ok(Simplification {
                term,
                constraints,
                applied_rules,
                effects,
                exhausted,
                undefined_term,
            });
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
        let root = simplify_root(
            definition,
            &children.term,
            assumptions.predicates,
            options,
            active_conditions,
            solver,
            execution.as_deref_mut(),
        )?;
        constraints.extend(children.constraints);
        constraints.extend(root.constraints);
        applied_rules.extend(children.applied_rules);
        applied_rules.extend(root.applied_rules);
        effects.extend(children.effects);
        effects.extend(root.effects);
        exhausted = exhausted.or(children.exhausted).or(root.exhausted);
        if undefined_term.is_none() {
            undefined_term = children.undefined_term.or(root.undefined_term);
        }
        if root.term.ptr_eq(&children.term)
            || root.term == children.term
            || root.term.attributes().evaluated
        {
            return Ok(Simplification {
                term: root.term,
                constraints,
                applied_rules,
                effects,
                exhausted,
                undefined_term,
            });
        }
        if *remaining == 0 {
            return match options.budget {
                BudgetPolicy::Fail => Err(SimplificationError::IterationLimit {
                    limit: options.max_iterations,
                    term: root.term,
                }),
                BudgetPolicy::KeepPartial => Ok(Simplification {
                    term: root.term,
                    constraints,
                    applied_rules,
                    effects,
                    exhausted: Some(BudgetExhaustion {
                        limit: options.max_iterations,
                        subject: BudgetSubject::Term,
                    }),
                    undefined_term,
                }),
            };
        }
        if exhausted.is_some() {
            return Ok(Simplification {
                term: root.term,
                constraints,
                applied_rules,
                effects,
                exhausted,
                undefined_term,
            });
        }
        *remaining -= 1;
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
) -> Result<Option<(String, Vec<Predicate>)>, SimplificationError> {
    for rules in applicable_groups(&definition.simplification_theory, &term_index(term)).values() {
        for rule in rules {
            if !matches!(rule.rhs, RuleRhs::Top) {
                continue;
            }
            let substitution =
                match match_terms_in_definition(MatchMode::Evaluate, definition, &rule.lhs, term) {
                    MatchResult::Failed(_) => continue,
                    MatchResult::Indeterminate {
                        substitution,
                        remainder,
                    } => {
                        let Some(matches) = match_collection_remainders_all_in_definition(
                            MatchMode::Evaluate,
                            definition,
                            substitution,
                            &remainder,
                        ) else {
                            continue;
                        };
                        let Some(substitution) = matches.into_iter().next() else {
                            continue;
                        };
                        substitution
                    }
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
            let conditions = equation_match_conditions(definition, &rule.requires, &substitution);
            if !matches!(
                evaluate_rule_condition(
                    definition,
                    &rule.attributes.unique_id,
                    Some(term),
                    conditions.requires,
                    known_predicates,
                    options,
                    active_conditions,
                    solver,
                )?,
                RuleCondition::Satisfied
            ) {
                continue;
            }
            // The operand `f(t)` of a term-level `\and` is strict in every `t` bound to an
            // element variable, so `u /\ f(t) = u /\ \ceil(t)` under `f(X) = \top`: an open
            // obligation becomes a constraint of the conjunction and a refuted one makes it
            // `\bottom`.
            let constraints = match decide_definedness(
                definition,
                &rule.attributes.unique_id,
                Some(term),
                conditions.definedness,
                known_predicates,
                options,
                active_conditions,
                solver,
            )? {
                DefinednessVerdict::Discharged => Vec::new(),
                DefinednessVerdict::Open(obligations) => obligations,
                DefinednessVerdict::Refuted => vec![Predicate::False],
            };
            return Ok(Some((rule.attributes.unique_id.clone(), constraints)));
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
) -> Result<Simplification, SimplificationError> {
    let mut constraints = Vec::new();
    let mut applied_rules = Vec::new();
    let mut effects = Vec::new();
    let mut exhausted = None;
    let mut undefined_term = None;
    let children_unchanged = Cell::new(true);
    let mut child = |term: &Term| {
        if term.attributes().evaluated && !assumptions.path_condition.can_change(term) {
            measure::bump(Counter::SimplifyNodesSkippedEvaluated);
            return Ok::<_, SimplificationError>(term.clone());
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
        constraints.extend(result.constraints);
        applied_rules.extend(result.applied_rules);
        effects.extend(result.effects);
        exhausted = exhausted.or(result.exhausted);
        if undefined_term.is_none() {
            undefined_term = result.undefined_term;
        }
        children_unchanged.set(children_unchanged.get() && term.ptr_eq(&result.term));
        Ok::<_, SimplificationError>(result.term)
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
                    applied_rules.push(rule_id);
                    constraints.extend(obligations);
                    retained
                }
                (None, Some((rule_id, obligations))) => {
                    children_unchanged.set(false);
                    let retained = child(left)?;
                    applied_rules.push(rule_id);
                    constraints.extend(obligations);
                    retained
                }
                (None, None) => Term::and(child(left)?, child(right)?),
                (Some((rule_id, _)), Some(_)) => {
                    return Err(SimplificationError::TopEquationOutsideConjunction { rule_id });
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
                .collect::<Result<Vec<_>, SimplificationError>>()?,
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
                    Ok((
                        child(middle)?,
                        tails
                            .iter()
                            .map(&mut child)
                            .collect::<Result<Vec<_>, SimplificationError>>()?,
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
    Ok(Simplification {
        term,
        constraints,
        applied_rules,
        effects,
        exhausted,
        undefined_term,
    })
}

fn simplify_root(
    definition: &BackendDefinition,
    term: &Term,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
    execution: Option<&mut ExecutionEvaluationContext>,
) -> Result<Simplification, SimplificationError> {
    let builtin = match execution {
        Some(execution) => evaluate_builtin_in_execution(term, definition, execution),
        None => evaluate_builtin(term, definition),
    }
    .map_err(SimplificationError::Builtin)?;
    let unsupported = match builtin {
        BuiltinResult::NotApplicable => None,
        BuiltinResult::Unsupported(reason) => Some(reason),
        builtin => {
            measure::bump(Counter::SimplifyBuiltinEvaluations);
            let TermKind::Application { symbol, .. } = term.kind() else {
                unreachable!("only applications have builtin hooks")
            };
            let (term, constraints, effects, undefined_term) = match builtin {
                BuiltinResult::Value(result) => (result, Vec::new(), Vec::new(), None),
                BuiltinResult::Bottom => (
                    term.clone(),
                    vec![Predicate::False],
                    Vec::new(),
                    Some(term.clone()),
                ),
                BuiltinResult::Effect(effect) => (
                    builtin_effect_result(definition, term, &effect)?,
                    Vec::new(),
                    vec![effect],
                    None,
                ),
                BuiltinResult::NotApplicable | BuiltinResult::Unsupported(_) => unreachable!(),
            };
            return Ok(Simplification {
                term,
                constraints,
                applied_rules: vec![format!(
                    "builtin:{}",
                    symbol
                        .attributes
                        .hook
                        .as_deref()
                        .expect("evaluated builtin has a hook")
                )],
                effects,
                exhausted: None,
                undefined_term,
            });
        }
    };
    let function_scan = match apply_theory(
        definition,
        (&definition.function_theory, IndeterminateEquation::Block),
        term,
        known_predicates,
        options,
        active_conditions,
        solver,
    )? {
        TheoryScan::Applied(result) => return Ok(result),
        scan => scan,
    };
    let simplification_scan = match apply_theory(
        definition,
        (
            &definition.simplification_theory,
            IndeterminateEquation::Continue,
        ),
        term,
        known_predicates,
        options,
        active_conditions,
        solver,
    )? {
        TheoryScan::Applied(result) => return Ok(result),
        scan => scan,
    };
    let TermKind::Application {
        symbol, arguments, ..
    } = term.kind()
    else {
        debug_assert!(unsupported.is_none());
        return Ok(Simplification {
            term: term.clone(),
            constraints: Vec::new(),
            applied_rules: Vec::new(),
            effects: Vec::new(),
            exhausted: None,
            undefined_term: None,
        });
    };
    let builtin_supported = unsupported.is_none();
    if let Some(hook) = symbol.attributes.hook.as_deref() {
        if arguments
            .iter()
            .all(|argument| argument.attributes().constructor_like)
        {
            let index = term_index(term);
            let has_equations = definition.function_theory.contains_key(&index)
                || definition.simplification_theory.contains_key(&index);
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
                });
            }
        } else if let Some(reason) = unsupported {
            diagnostic::emit(BackendDiagnostic::UnsupportedHookUnevaluated {
                hook: hook.to_owned(),
                reason,
            });
        }
    }
    let equation_fixed_point = matches!(function_scan, TheoryScan::NotApplicable)
        && matches!(simplification_scan, TheoryScan::NotApplicable);
    let term =
        if equation_fixed_point && builtin_supported && cacheable_equation_head(definition, term) {
            term.with_evaluated_cache()
        } else {
            term.clone()
        };
    Ok(Simplification {
        term,
        constraints: Vec::new(),
        applied_rules: Vec::new(),
        effects: Vec::new(),
        exhausted: None,
        undefined_term: None,
    })
}

fn builtin_effect_result(
    definition: &BackendDefinition,
    application: &Term,
    effect: &BuiltinEffect,
) -> Result<Term, SimplificationError> {
    match effect {
        BuiltinEffect::UserLog(_) => {
            let Some(dotk) = definition.symbols.get(WellKnownSymbol::DotK.as_str()) else {
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

#[derive(Clone, Copy, Eq, PartialEq)]
enum IndeterminateEquation {
    Block,
    Continue,
}

enum TheoryScan {
    Applied(Simplification),
    Blocked,
    ContextDependent,
    NotApplicable,
}

/// Whether `term` is one of the normalized value-like equation heads whose fixed point can be
/// retained in the term itself. Fully evaluated children exclude a closed parent whose child
/// scan was blocked, and the empty variable set keeps a symbolic application out of the cache.
/// The caller separately rejects a scan whose result depended on the current path condition.
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
        && (symbol.attributes.anywhere || definition.overloads.is_overloaded(&symbol.name))
}

fn apply_theory(
    definition: &BackendDefinition,
    theory: (&Theory, IndeterminateEquation),
    term: &Term,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
) -> Result<TheoryScan, SimplificationError> {
    let (theory, indeterminate_equation) = theory;
    let groups = applicable_groups(theory, &term_index(term));
    let mut blocked = false;
    let mut context_dependent = false;
    for rules in groups.values() {
        match scan_group(rules, |rule| {
            apply_equation(
                definition,
                rule,
                term,
                known_predicates,
                options,
                active_conditions,
                solver,
            )
        })? {
            GroupScan::Applied(result) => return Ok(TheoryScan::Applied(result)),
            GroupScan::Blocked if indeterminate_equation == IndeterminateEquation::Block => {
                // A rule at this priority may apply after the symbolic subject becomes more
                // concrete. Function evaluation must preserve the application and must not fall
                // through to an owise or otherwise lower-priority equation.
                return Ok(TheoryScan::Blocked);
            }
            GroupScan::Blocked => blocked = true,
            GroupScan::ContextDependent => context_dependent = true,
            GroupScan::NotApplicable => {}
        }
    }
    Ok(if blocked {
        TheoryScan::Blocked
    } else if context_dependent {
        TheoryScan::ContextDependent
    } else {
        TheoryScan::NotApplicable
    })
}

enum EquationAttempt<T> {
    NotApplicable,
    /// The equation is inapplicable under the current path condition, but may apply if the same
    /// term is simplified under different assumptions. Unlike `Indeterminate`, this does not
    /// block lower-priority equations in the current scan.
    ContextDependent,
    Indeterminate(ConditionIndeterminacy),
    Applied(T),
}

enum GroupScan<T> {
    Applied(T),
    Blocked,
    ContextDependent,
    NotApplicable,
}

fn scan_group<R, T>(
    rules: &[Arc<R>],
    mut attempt: impl FnMut(&R) -> Result<EquationAttempt<T>, SimplificationError>,
) -> Result<GroupScan<T>, SimplificationError> {
    let mut indeterminate = false;
    let mut context_dependent = false;
    for rule in rules {
        match attempt(rule)? {
            EquationAttempt::Applied(result) => return Ok(GroupScan::Applied(result)),
            EquationAttempt::Indeterminate(_reason) => indeterminate = true,
            EquationAttempt::ContextDependent => context_dependent = true,
            EquationAttempt::NotApplicable => {}
        }
    }
    Ok(if indeterminate {
        GroupScan::Blocked
    } else if context_dependent {
        GroupScan::ContextDependent
    } else {
        GroupScan::NotApplicable
    })
}

/// The conditions an equation must discharge once its left-hand side has matched.
struct EquationConditions {
    /// The equation's own `requires`, instantiated by the match.
    requires: Vec<Predicate>,
    /// Definedness of every term bound to an element variable.
    ///
    /// An element variable ranges over elements, so binding it to a term `t` asserts `\ceil(t)`;
    /// a set variable binds an arbitrary pattern and imposes no obligation. `ceil_term` already
    /// discharges constructors, total symbols, and element variables, so this list names only
    /// partial applications, set variables, and collection distinctness.
    definedness: Vec<Predicate>,
}

/// The verdict on `EquationConditions::definedness` under the path condition.
enum DefinednessVerdict {
    /// Every obligation holds: the bound terms are defined.
    Discharged,
    /// The residual obligations the path condition does not decide; the equation's caller
    /// carries them, because they keep the `\ceil(t)` factor of the instance explicit.
    Open(Vec<Predicate>),
    /// An obligation is refuted: a bound term is empty under the path condition.
    Refuted,
}

/// Decide the definedness obligations of an equation's element-variable bindings, after the
/// equation's own `requires` has been decided separately. The obligations are simplified under
/// the path condition first, keyed by `anchor` against re-entry as `evaluate_rule_condition`
/// does, and a verdict the solver could not reach is reported as a diagnostic of `rule_id`.
#[allow(clippy::too_many_arguments)]
fn decide_definedness(
    definition: &BackendDefinition,
    rule_id: &str,
    anchor: Option<&Term>,
    definedness: Vec<Predicate>,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
) -> Result<DefinednessVerdict, SimplificationError> {
    if definedness.is_empty() {
        return Ok(DefinednessVerdict::Discharged);
    }
    let definedness = if let Some(anchor) = anchor {
        simplify_rule_predicates(
            definition,
            (rule_id, anchor),
            &definedness,
            known_predicates,
            options,
            active_conditions,
            solver,
        )
        .unwrap_or(definedness)
    } else {
        definedness
    };
    Ok(
        match decide_rule_condition(rule_id, &definedness, known_predicates, solver)? {
            RuleCondition::Satisfied => DefinednessVerdict::Discharged,
            RuleCondition::Refuted => DefinednessVerdict::Refuted,
            RuleCondition::Indeterminate(_) => DefinednessVerdict::Open(definedness),
        },
    )
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

fn equation_match_conditions(
    definition: &BackendDefinition,
    requires: &[Predicate],
    substitution: &Substitution,
) -> EquationConditions {
    let requires = substitute_predicates(requires, substitution);
    let mut definedness = Vec::new();
    for (variable, value) in substitution {
        if variable.kind == VariableKind::Element {
            for predicate in ceil_term(definition, value) {
                if !requires.contains(&predicate) && !definedness.contains(&predicate) {
                    definedness.push(predicate);
                }
            }
        }
    }
    EquationConditions {
        requires,
        definedness,
    }
}

fn apply_equation(
    definition: &BackendDefinition,
    rule: &RewriteRule,
    term: &Term,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
) -> Result<EquationAttempt<Simplification>, SimplificationError> {
    measure::bump(Counter::SimplifyEquationAttempts);
    let substitution =
        match match_terms_in_definition(MatchMode::Evaluate, definition, &rule.lhs, term) {
            MatchResult::Failed(_) => return Ok(EquationAttempt::NotApplicable),
            MatchResult::Indeterminate {
                substitution,
                remainder,
            } => {
                let Some(matches) = match_collection_remainders_all_in_definition(
                    MatchMode::Evaluate,
                    definition,
                    substitution.clone(),
                    &remainder,
                ) else {
                    return Ok(EquationAttempt::Indeterminate(
                        ConditionIndeterminacy::ImplicationIndeterminate,
                    ));
                };
                let Some(substitution) = matches.into_iter().next() else {
                    return Ok(EquationAttempt::NotApplicable);
                };
                // K function equations are required to be functional. AC matching may expose
                // several equivalent decompositions, so use the first substitution from the
                // helper's stable sorted order rather than turning evaluation into execution
                // branching.
                substitution
            }
            MatchResult::Success(substitution) => substitution,
        };
    if substitution
        .keys()
        .any(|variable| !rule.lhs.attributes().variables.contains(variable))
    {
        return Ok(EquationAttempt::NotApplicable);
    }
    if check_concreteness(rule, &substitution).is_some() {
        return Ok(EquationAttempt::NotApplicable);
    }
    if binds_element_variable_to_set_pattern(&substitution) {
        return Ok(EquationAttempt::Indeterminate(
            ConditionIndeterminacy::NonFunctionalBinding,
        ));
    }
    let conditions = equation_match_conditions(definition, &rule.requires, &substitution);
    // The equation `f(X) = rhs requires R` is an axiom over every element `X`. A term `t` bound
    // to `X` is a functional pattern (at most one element), so `f(t) = \ceil(t) /\ rhs[t]` when
    // `R[t]` holds on that element: both sides are empty when `t` is, and equal to `rhs[t]`
    // otherwise. An unknown `R[t]` must stay indeterminate, because applying the equation would
    // narrow the subject to the part where `R` holds. A refuted `R[t]` remains context dependent:
    // it permits lower-priority equations in this scan but cannot justify caching the term across
    // simplifier calls with different path conditions.
    match evaluate_rule_condition(
        definition,
        &rule.attributes.unique_id,
        Some(term),
        conditions.requires,
        known_predicates,
        options,
        active_conditions,
        solver,
    )? {
        RuleCondition::Satisfied => {}
        RuleCondition::Refuted => return Ok(EquationAttempt::ContextDependent),
        RuleCondition::Indeterminate(reason) => {
            return Ok(EquationAttempt::Indeterminate(reason));
        }
    }
    // The definedness obligations are not a reason to refuse the equation: an obligation the
    // path condition does not decide is carried as a constraint of the result, where it keeps
    // the `\ceil(t)` factor of the equality explicit. A refuted obligation means `t` is empty
    // under the path condition, and the subject reaches `t` only through applications,
    // injections, collections, and `\and`, all strict, so the subject is empty whichever
    // equation is tried; the result reports it as `\bottom`. Only the equation's own `requires`,
    // decided above, says nothing about the subject when refuted.
    let definedness = match decide_definedness(
        definition,
        &rule.attributes.unique_id,
        Some(term),
        conditions.definedness,
        known_predicates,
        options,
        active_conditions,
        solver,
    )? {
        DefinednessVerdict::Discharged => Vec::new(),
        DefinednessVerdict::Open(obligations) => obligations,
        DefinednessVerdict::Refuted => {
            return Ok(EquationAttempt::Applied(bottom_subject(rule, term)));
        }
    };
    let (alternatives, is_disjunction) = match &rule.rhs {
        RuleRhs::Term(rhs) => (
            vec![(substitute(rhs, &substitution), rule.ensures.clone(), false)],
            false,
        ),
        RuleRhs::Bottom => (vec![(term.clone(), rule.ensures.clone(), true)], false),
        RuleRhs::Disjunction(alternatives) => (
            alternatives
                .iter()
                .map(|alternative| {
                    let mut ensures = rule.ensures.clone();
                    for predicate in &alternative.ensures {
                        if !ensures.contains(predicate) {
                            ensures.push(predicate.clone());
                        }
                    }
                    (substitute(&alternative.term, &substitution), ensures, false)
                })
                .collect(),
            true,
        ),
        RuleRhs::Top => {
            return Err(SimplificationError::TopEquationOutsideConjunction {
                rule_id: rule.attributes.unique_id.clone(),
            });
        }
        RuleRhs::Predicates(_) => return Ok(EquationAttempt::NotApplicable),
    };
    let mut live = Vec::new();
    for (rhs, ensures, rhs_is_bottom) in alternatives {
        match evaluate_ensures(
            definition,
            rule,
            term,
            &substitution,
            &ensures,
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
        0 => Ok(EquationAttempt::Applied(bottom_subject(rule, term))),
        1 => {
            let (term, mut constraints) = live.pop().expect("one live alternative");
            if !constraints.contains(&Predicate::False) {
                for predicate in definedness {
                    if !constraints.contains(&predicate) {
                        constraints.push(predicate);
                    }
                }
            }
            Ok(EquationAttempt::Applied(Simplification {
                term,
                constraints,
                applied_rules: vec![rule.attributes.unique_id.clone()],
                effects: Vec::new(),
                exhausted: None,
                undefined_term: None,
            }))
        }
        alternatives => Err(SimplificationError::DisjunctiveResult {
            rule_id: rule.attributes.unique_id.clone(),
            alternatives,
        }),
    }
}

/// The result of `rule` on a subject `term` that is empty under the path condition: the subject
/// is retained and `\bottom` is its only constraint, so the caller merges it as it merges any
/// other constraint set and the pattern becomes `\bottom` as a whole.
fn bottom_subject(rule: &RewriteRule, term: &Term) -> Simplification {
    Simplification {
        term: term.clone(),
        constraints: vec![Predicate::False],
        applied_rules: vec![rule.attributes.unique_id.clone()],
        effects: Vec::new(),
        exhausted: None,
        undefined_term: None,
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
    substitution: &Substitution,
    ensures: &[Predicate],
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
) -> Result<EnsuresVerdict, SimplificationError> {
    let ensures = substitute_predicates(ensures, substitution);
    let ensures = simplify_rule_predicates(
        definition,
        (&rule.attributes.unique_id, term),
        &ensures,
        known_predicates,
        options,
        active_conditions,
        solver,
    )
    .unwrap_or(ensures);
    // An `ensures` is a conjunct of the result by definition, so every verdict the solver does
    // not reach carries it: an open implication, no solver, a query the encoding cannot pose,
    // and an inconsistent path condition, which under the path condition alone says nothing
    // about the equation. No diagnostic is emitted here, as none was before.
    match decide_condition(&ensures, known_predicates, solver) {
        Ok(RuleCondition::Satisfied) => Ok(EnsuresVerdict::Holds),
        Ok(RuleCondition::Refuted) => Ok(EnsuresVerdict::Refuted),
        Ok(RuleCondition::Indeterminate(_)) => Ok(EnsuresVerdict::Open(ensures)),
        Err(error) => Err(SimplificationError::Smt {
            rule_id: rule.attributes.unique_id.clone(),
            error,
        }),
    }
}

#[cfg(test)]
mod tests {
    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    use super::*;
    use crate::term::{CollectionSymbols, ListDefinition, MapDefinition};

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
                .ceil_theory
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
        let result = simplify(&definition, &input, SimplificationOptions::default())
            .expect("the equation should apply");
        assert_eq!(result.term, done);
        assert_eq!(result.constraints, vec![Predicate::Ceil(argument.clone())]);
        assert_eq!(result.applied_rules, vec!["discard".to_owned()]);

        // A path condition that already carries the obligation discharges it.
        let result = simplify_with_solver(
            &definition,
            &input,
            &[Predicate::Ceil(argument)],
            SimplificationOptions::default(),
            &NoSolver,
        )
        .expect("the equation should apply");
        assert_eq!(result.term, done);
        assert!(result.constraints.is_empty());
    }

    #[test]
    fn an_unknown_requires_keeps_the_equation_indeterminate() {
        let definition = definedness_definition();
        let done = term(&definition, r#"\dv{SortS{}}("done")"#);

        // Negative control: the same open definedness obligation, but the equation's own
        // `requires` is undecided, so applying it would narrow the subject.
        let input = term(&definition, "guarded{}(partial{}(Y:SortS{}))");
        let result = simplify(&definition, &input, SimplificationOptions::default())
            .expect("an indeterminate equation retains the subject");
        assert_eq!(result.term, input);
        assert!(result.constraints.is_empty());
        assert!(result.applied_rules.is_empty());

        // Positive control: the equation itself applies once `requires` is decided.
        let input = term(&definition, r#"guarded{}(\dv{SortS{}}("expected"))"#);
        let result = simplify(&definition, &input, SimplificationOptions::default())
            .expect("the guarded equation should apply");
        assert_eq!(result.term, done);
        assert!(result.constraints.is_empty());
    }

    #[test]
    fn drops_a_ceil_conjunct_entailed_by_the_pattern_term() {
        let definition = definedness_definition();
        let argument = term(&definition, "partial{}(Y:SortS{})");
        let obligation = Predicate::Ceil(argument.clone());
        let simplify_pattern = |source: &str| {
            simplify_pattern_with_solver(
                &definition,
                &Pattern {
                    term: term(&definition, source),
                    constraints: vec![obligation.clone()],
                },
                SimplificationOptions::default(),
                &NoSolver,
            )
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
        let discarded = simplify_pattern_with_solver(
            &definition,
            &Pattern {
                term: term(&definition, "wrap{}(discard{}(partial{}(Y:SortS{})))"),
                constraints: Vec::new(),
            },
            SimplificationOptions::default(),
            &NoSolver,
        )
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
        ) -> Result<crate::smt::Satisfiability, SmtError> {
            unreachable!()
        }

        fn check_predicates(
            &self,
            _known: &[Predicate],
            _substitution: &Substitution,
            _checked: &[Predicate],
        ) -> Result<Validity, SmtError> {
            Ok(Validity::Invalid)
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
            simplify_predicate_with_solver(
                &definition,
                &subject,
                &[],
                SimplificationOptions::default(),
                &NoSolver,
            )
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
}
