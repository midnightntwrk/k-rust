//! Recursive equation simplification to a bounded fixed point.

use std::{
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
        evaluate_in_definition as evaluate_builtin, k_sequence_item,
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
    rule::{Predicate, PredicateRewriteRule, RewriteRule, RuleRhs, TermIndex, Theory, term_index},
    smt::{NoSolver, SmtError, SmtSolver, Validity},
    substitution::{Substitution, compose, substitute},
    term::{Sort, Term, TermKind, VariableKind},
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
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum RuleCondition {
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
    match predicates_truth(&predicates) {
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
    match solver.check_predicates(known_predicates, &Substitution::new(), &predicates) {
        Ok(Validity::Valid) => Ok(RuleCondition::Satisfied),
        Ok(Validity::Invalid) => Ok(RuleCondition::Refuted),
        Ok(Validity::Indeterminate) => Ok(RuleCondition::Indeterminate(
            ConditionIndeterminacy::ImplicationIndeterminate,
        )),
        Err(SmtError::Unavailable) => Ok(RuleCondition::Indeterminate(
            ConditionIndeterminacy::NoSolver,
        )),
        Ok(Validity::InconsistentGroundTruth) => {
            let reason = ConditionIndeterminacy::InconsistentPathCondition;
            diagnostic::emit(BackendDiagnostic::UndecidedCondition {
                rule_id: rule_id.to_owned(),
                reason: reason.clone(),
                predicates,
            });
            Ok(RuleCondition::Indeterminate(reason))
        }
        Ok(Validity::Unknown(message)) => {
            let reason = ConditionIndeterminacy::SmtUnknown(message);
            diagnostic::emit(BackendDiagnostic::UndecidedCondition {
                rule_id: rule_id.to_owned(),
                reason: reason.clone(),
                predicates,
            });
            Ok(RuleCondition::Indeterminate(reason))
        }
        Err(error) => Err(SimplificationError::Smt {
            rule_id: rule_id.to_owned(),
            error,
        }),
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
    match solver.check_predicates(
        known_predicates,
        &Substitution::new(),
        std::slice::from_ref(&simplified),
    ) {
        Ok(Validity::Valid) => Ok(Predicate::True),
        Ok(Validity::Invalid) => Ok(Predicate::False),
        Ok(Validity::Indeterminate) | Err(SmtError::Unavailable) => Ok(simplified),
        Ok(Validity::InconsistentGroundTruth) => {
            diagnostic::emit(BackendDiagnostic::UndecidedPredicate {
                predicate: simplified.clone(),
                reason: ConditionIndeterminacy::InconsistentPathCondition,
            });
            Ok(simplified)
        }
        Ok(Validity::Unknown(message)) => {
            diagnostic::emit(BackendDiagnostic::UndecidedPredicate {
                predicate: simplified.clone(),
                reason: ConditionIndeterminacy::SmtUnknown(message),
            });
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
            let left = simplify_term(left)?;
            let right = simplify_term(right)?;
            let mut constraints = left.constraints;
            constraints.extend(right.constraints);
            let equality = normalize_hooked_boolean_predicate(
                definition,
                Predicate::Equals(left.term, right.term),
            );
            let equality = normalize_injection_equality(definition, equality);
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
                let mut constraints = simplified.constraints;
                constraints.extend(expanded);
                Predicate::And(constraints)
            }
        }
        Predicate::Floor(term) => {
            let simplified = simplify_term(term)?;
            with_simplification_constraints(
                simplified.constraints,
                Predicate::Floor(simplified.term),
            )
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
            GroupScan::NotApplicable => {}
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

    let requires = equation_match_conditions(definition, &rule.requires, &substitution);
    match evaluate_rule_condition(
        definition,
        &rule.attributes.unique_id,
        Some(term),
        requires,
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
    Ok(EquationAttempt::Applied(normalize_predicate(
        Predicate::And(substitute_predicates(rhs, &substitution)),
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
            GroupScan::NotApplicable => {}
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
    let requires = equation_match_conditions(definition, &rule.requires, &substitution);
    match evaluate_rule_condition(
        definition,
        &rule.attributes.unique_id,
        first_predicate_term(predicate),
        requires,
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
    let rhs = substitute_predicates(&rule.rhs, &substitution);
    Ok(EquationAttempt::Applied(normalize_predicate(
        Predicate::And(rhs),
    )))
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
    match value.as_ref() {
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

fn simplify_with_budget(
    definition: &BackendDefinition,
    term: &Term,
    assumptions: &TermAssumptions<'_>,
    options: SimplificationOptions,
    remaining: &mut usize,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
) -> Result<Simplification, SimplificationError> {
    let mut term = term.clone();
    let mut constraints = Vec::new();
    let mut applied_rules = Vec::new();
    let mut effects = Vec::new();
    let mut exhausted = None;
    loop {
        measure::bump(Counter::SimplifyRounds);
        if cancellation_requested() {
            return Err(SimplificationError::Cancelled);
        }
        term = assumptions.path_condition.apply(&term);
        if term.attributes().evaluated {
            return Ok(Simplification {
                term,
                constraints,
                applied_rules,
                effects,
                exhausted,
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
        )?;
        let root = simplify_root(
            definition,
            &children.term,
            assumptions.predicates,
            options,
            active_conditions,
            solver,
        )?;
        constraints.extend(children.constraints);
        constraints.extend(root.constraints);
        applied_rules.extend(children.applied_rules);
        applied_rules.extend(root.applied_rules);
        effects.extend(children.effects);
        effects.extend(root.effects);
        exhausted = exhausted.or(children.exhausted).or(root.exhausted);
        if root.term == children.term || root.term.attributes().evaluated {
            return Ok(Simplification {
                term: root.term,
                constraints,
                applied_rules,
                effects,
                exhausted,
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
        let term = substitute(term, &self.substitution);
        replace_terms_bottom_up(&term, &self.replacements)
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
    let replace = |term: &Term| replace_terms_bottom_up(term, replacements);
    let rebuilt = match term.kind() {
        TermKind::And(left, right) => Term::and(replace(left), replace(right)),
        TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } => Term::application(
            symbol.clone(),
            sort_arguments.clone(),
            arguments.iter().map(replace).collect(),
        ),
        TermKind::Injection {
            source,
            target,
            term,
        } => Term::injection(source.clone(), target.clone(), replace(term)),
        TermKind::Map {
            definition,
            entries,
            rest,
        } => Term::map(
            definition.clone(),
            entries
                .iter()
                .map(|(key, value)| (replace(key), replace(value)))
                .collect(),
            rest.as_ref().map(replace),
        ),
        TermKind::List {
            definition,
            heads,
            rest,
        } => Term::list(
            definition.clone(),
            heads.iter().map(replace).collect(),
            rest.as_ref().map(|(middle, tails)| {
                (
                    replace(middle),
                    tails.iter().map(replace).collect::<Vec<_>>(),
                )
            }),
        ),
        TermKind::Set {
            definition,
            elements,
            rest,
        } => Term::set(
            definition.clone(),
            elements.iter().map(replace).collect(),
            rest.as_ref().map(replace),
        ),
        TermKind::DomainValue { .. } | TermKind::Variable(_) => term.clone(),
    };
    replacements
        .iter()
        .find_map(|(original, replacement)| (original == &rebuilt).then(|| replacement.clone()))
        .unwrap_or(rebuilt)
}

fn matches_top_equation(
    definition: &BackendDefinition,
    term: &Term,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
) -> Result<Option<String>, SimplificationError> {
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
            {
                continue;
            }
            let requires = equation_match_conditions(definition, &rule.requires, &substitution);
            if matches!(
                evaluate_rule_condition(
                    definition,
                    &rule.attributes.unique_id,
                    Some(term),
                    requires,
                    known_predicates,
                    options,
                    active_conditions,
                    solver,
                )?,
                RuleCondition::Satisfied
            ) {
                return Ok(Some(rule.attributes.unique_id.clone()));
            }
        }
    }
    Ok(None)
}

fn simplify_children(
    definition: &BackendDefinition,
    term: &Term,
    assumptions: &TermAssumptions<'_>,
    options: SimplificationOptions,
    remaining: &mut usize,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
) -> Result<Simplification, SimplificationError> {
    let mut constraints = Vec::new();
    let mut applied_rules = Vec::new();
    let mut effects = Vec::new();
    let mut exhausted = None;
    let mut child = |term: &Term| {
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
        )?;
        constraints.extend(result.constraints);
        applied_rules.extend(result.applied_rules);
        effects.extend(result.effects);
        exhausted = exhausted.or(result.exhausted);
        Ok::<_, SimplificationError>(result.term)
    };
    let term = match term.kind() {
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
                (Some(rule_id), None) => {
                    let retained = child(right)?;
                    applied_rules.push(rule_id);
                    retained
                }
                (None, Some(rule_id)) => {
                    let retained = child(left)?;
                    applied_rules.push(rule_id);
                    retained
                }
                (None, None) => Term::and(child(left)?, child(right)?),
                (Some(rule_id), Some(_)) => {
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
    Ok(Simplification {
        term,
        constraints,
        applied_rules,
        effects,
        exhausted,
    })
}

fn simplify_root(
    definition: &BackendDefinition,
    term: &Term,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
) -> Result<Simplification, SimplificationError> {
    let builtin = evaluate_builtin(term, definition).map_err(SimplificationError::Builtin)?;
    let unsupported = match builtin {
        BuiltinResult::NotApplicable => None,
        BuiltinResult::Unsupported(reason) => Some(reason),
        builtin => {
            measure::bump(Counter::SimplifyBuiltinEvaluations);
            let TermKind::Application { symbol, .. } = term.kind() else {
                unreachable!("only applications have builtin hooks")
            };
            let (term, constraints, effects) = match builtin {
                BuiltinResult::Value(result) => (result, Vec::new(), Vec::new()),
                BuiltinResult::Bottom => (term.clone(), vec![Predicate::False], Vec::new()),
                BuiltinResult::Effect(effect) => (
                    builtin_effect_result(definition, term, &effect)?,
                    Vec::new(),
                    vec![effect],
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
            });
        }
    };
    if let Some(result) = apply_theory(
        definition,
        (&definition.function_theory, IndeterminateEquation::Block),
        term,
        known_predicates,
        options,
        active_conditions,
        solver,
    )? {
        return Ok(result);
    }
    if let Some(result) = apply_theory(
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
        return Ok(result);
    }
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
        });
    };
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
    Ok(Simplification {
        term: term.clone(),
        constraints: Vec::new(),
        applied_rules: Vec::new(),
        effects: Vec::new(),
        exhausted: None,
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

fn apply_theory(
    definition: &BackendDefinition,
    theory: (&Theory, IndeterminateEquation),
    term: &Term,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
) -> Result<Option<Simplification>, SimplificationError> {
    let (theory, indeterminate_equation) = theory;
    let groups = applicable_groups(theory, &term_index(term));
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
            GroupScan::Applied(result) => return Ok(Some(result)),
            GroupScan::Blocked if indeterminate_equation == IndeterminateEquation::Block => {
                // A rule at this priority may apply after the symbolic subject becomes more
                // concrete. Function evaluation must preserve the application and must not fall
                // through to an owise or otherwise lower-priority equation.
                return Ok(None);
            }
            GroupScan::Blocked | GroupScan::NotApplicable => {}
        }
    }
    Ok(None)
}

fn applicable_groups(theory: &Theory, index: &TermIndex) -> BTreeMap<u8, Vec<Arc<RewriteRule>>> {
    let mut result = BTreeMap::new();
    let indexes = if index == &TermIndex::Variable {
        vec![index]
    } else {
        vec![index, &TermIndex::Variable]
    };
    for index in indexes {
        if let Some(groups) = theory.get(index) {
            for (priority, rules) in groups {
                result
                    .entry(*priority)
                    .or_insert_with(Vec::new)
                    .extend(rules.iter().cloned());
            }
        }
    }
    result
}

enum EquationAttempt<T> {
    NotApplicable,
    Indeterminate(ConditionIndeterminacy),
    Applied(T),
}

enum GroupScan<T> {
    Applied(T),
    Blocked,
    NotApplicable,
}

fn scan_group<R, T>(
    rules: &[Arc<R>],
    mut attempt: impl FnMut(&R) -> Result<EquationAttempt<T>, SimplificationError>,
) -> Result<GroupScan<T>, SimplificationError> {
    let mut indeterminate = false;
    for rule in rules {
        match attempt(rule)? {
            EquationAttempt::Applied(result) => return Ok(GroupScan::Applied(result)),
            EquationAttempt::Indeterminate(_reason) => indeterminate = true,
            EquationAttempt::NotApplicable => {}
        }
    }
    Ok(if indeterminate {
        GroupScan::Blocked
    } else {
        GroupScan::NotApplicable
    })
}

/// Matching an element variable requires a defined value, even when an equation discards it.
/// This is the predicate returned by Kore.Rewrite.Axiom.Matcher.isTermDefined; set variables
/// may bind arbitrary patterns and do not impose this obligation.
fn equation_match_conditions(
    definition: &BackendDefinition,
    requires: &[Predicate],
    substitution: &Substitution,
) -> Vec<Predicate> {
    let mut conditions = substitute_predicates(requires, substitution);
    for (variable, value) in substitution {
        if variable.kind == VariableKind::Element {
            for predicate in ceil_term(definition, value) {
                if !conditions.contains(&predicate) {
                    conditions.push(predicate);
                }
            }
        }
    }
    conditions
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
    let requires = equation_match_conditions(definition, &rule.requires, &substitution);
    match evaluate_rule_condition(
        definition,
        &rule.attributes.unique_id,
        Some(term),
        requires,
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
        0 => Ok(EquationAttempt::Applied(Simplification {
            term: term.clone(),
            constraints: vec![Predicate::False],
            applied_rules: vec![rule.attributes.unique_id.clone()],
            effects: Vec::new(),
            exhausted: None,
        })),
        1 => {
            let (term, constraints) = live.pop().expect("one live alternative");
            Ok(EquationAttempt::Applied(Simplification {
                term,
                constraints,
                applied_rules: vec![rule.attributes.unique_id.clone()],
                effects: Vec::new(),
                exhausted: None,
            }))
        }
        alternatives => Err(SimplificationError::DisjunctiveResult {
            rule_id: rule.attributes.unique_id.clone(),
            alternatives,
        }),
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
    match predicates_truth(&ensures) {
        Truth::False => Ok(EnsuresVerdict::Refuted),
        Truth::True => Ok(EnsuresVerdict::Holds),
        Truth::Unknown => {
            match solver.check_predicates(known_predicates, &Substitution::new(), &ensures) {
                Ok(Validity::Invalid) => return Ok(EnsuresVerdict::Refuted),
                Ok(Validity::Valid) => return Ok(EnsuresVerdict::Holds),
                Ok(
                    Validity::Indeterminate
                    | Validity::InconsistentGroundTruth
                    | Validity::Unknown(_),
                )
                | Err(SmtError::Unavailable) => {}
                Err(error) => {
                    return Err(SimplificationError::Smt {
                        rule_id: rule.attributes.unique_id.clone(),
                        error,
                    });
                }
            }
            Ok(EnsuresVerdict::Open(ensures))
        }
    }
}

#[cfg(test)]
mod tests {
    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    use super::*;

    fn term(definition: &BackendDefinition, source: &str) -> Term {
        let syntax = parse_pattern(source).expect("term should parse");
        definition
            .internalize_term(&syntax, &[])
            .expect("term should internalize")
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
}
