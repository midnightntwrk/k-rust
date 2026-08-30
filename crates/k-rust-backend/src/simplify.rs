//! Recursive equation simplification to a bounded fixed point.

use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use rustc_hash::FxHashSet;

use crate::{
    builtin::{
        BuiltinEffect, BuiltinError, BuiltinResult, evaluate as evaluate_builtin, k_sequence_item,
    },
    cancellation::cancellation_requested,
    definedness::ceil_term,
    definition::BackendDefinition,
    matching::{
        MatchMode, MatchResult, match_collection_remainders_all_in_definition,
        match_term_pairs_in_definition, match_terms_in_definition,
    },
    rewrite::{
        Pattern, Truth, check_concreteness, normalize_pattern_substitution, predicates_truth,
        retain_substitution_predicates, substitute_predicates, violates_finite_constructor_domain,
    },
    rule::{Predicate, PredicateRewriteRule, RewriteRule, RuleRhs, TermIndex, Theory, term_index},
    smt::{NoSolver, SmtError, SmtSolver, Validity},
    substitution::{Substitution, compose, substitute},
    term::{Term, TermKind},
};

/// Default equation iterations allowed for each simplification fixed point.
pub const DEFAULT_MAX_SIMPLIFICATION_ITERATIONS: usize = 100;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SimplificationOptions {
    pub max_iterations: usize,
}

impl Default for SimplificationOptions {
    fn default() -> Self {
        Self {
            max_iterations: DEFAULT_MAX_SIMPLIFICATION_ITERATIONS,
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
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Simplification {
    pub term: Term,
    pub constraints: Vec<Predicate>,
    pub applied_rules: Vec<String>,
    pub effects: Vec<BuiltinEffect>,
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
    ConflictingResults {
        rule_ids: Vec<String>,
    },
    Smt {
        rule_id: String,
        error: SmtError,
    },
    SmtPredicate {
        predicate: Box<Predicate>,
        error: SmtError,
    },
    InconsistentGroundTruth {
        rule_id: String,
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
    simplify_with_budget(
        definition,
        term,
        &assumptions,
        options.max_iterations,
        &mut remaining,
        &active_conditions,
        solver,
    )
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
    let retained_substitution = normalize_pattern_substitution(&mut pattern);
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
    retain_substitution_predicates(&mut constraints, &retained_substitution);
    let mut pattern = Pattern {
        term: simplified.term,
        constraints,
    };
    normalize_pattern_substitution(&mut pattern);
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RuleCondition {
    Satisfied,
    Refuted,
    Indeterminate,
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
        Ok(Validity::Indeterminate) | Err(SmtError::Unavailable) => {
            Ok(RuleCondition::Indeterminate)
        }
        Ok(Validity::InconsistentGroundTruth) => {
            Err(SimplificationError::InconsistentGroundTruth {
                rule_id: rule_id.to_owned(),
            })
        }
        Ok(Validity::Unknown(reason)) => Err(SimplificationError::Smt {
            rule_id: rule_id.to_owned(),
            error: SmtError::Unknown(reason),
        }),
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
        Ok(Validity::InconsistentGroundTruth) => Err(SimplificationError::SmtPredicate {
            predicate: Box::new(simplified),
            error: SmtError::InconsistentGroundTruth,
        }),
        Ok(Validity::Unknown(reason)) => Err(SimplificationError::SmtPredicate {
            predicate: Box::new(simplified),
            error: SmtError::Unknown(reason),
        }),
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
            limit,
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
            with_simplification_constraints(constraints, equality)
        }
        Predicate::Ceil(term) => {
            let simplified = simplify_term(term)?;
            let unchanged = Predicate::Ceil(simplified.term.clone());
            let expanded = ceil_term(definition, &simplified.term);
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

enum CeilEquationAttempt {
    NotApplicable,
    Indeterminate,
    Applied(Predicate),
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
        let mut results = Vec::new();
        let mut rule_ids = Vec::new();
        let mut indeterminate = false;
        for rule in rules {
            match apply_ceil_equation(
                definition,
                rule,
                term,
                known_predicates,
                options,
                active_conditions,
                solver,
            )? {
                CeilEquationAttempt::NotApplicable => {}
                CeilEquationAttempt::Indeterminate => indeterminate = true,
                CeilEquationAttempt::Applied(result) => {
                    results.push(result);
                    rule_ids.push(rule.attributes.unique_id.clone());
                }
            }
        }
        if indeterminate && results.is_empty() {
            return Ok(None);
        }
        match results.len() {
            0 => {}
            1 => return Ok(results.pop()),
            _ if results.windows(2).all(|pair| pair[0] == pair[1]) => {
                return Ok(results.into_iter().next());
            }
            _ => return Err(SimplificationError::ConflictingResults { rule_ids }),
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
) -> Result<CeilEquationAttempt, SimplificationError> {
    let substitution =
        match match_terms_in_definition(MatchMode::Evaluate, definition, &rule.lhs, term) {
            MatchResult::Failed(_) => return Ok(CeilEquationAttempt::NotApplicable),
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
                    return Ok(CeilEquationAttempt::Indeterminate);
                };
                let Some(substitution) = matches.into_iter().next() else {
                    return Ok(CeilEquationAttempt::NotApplicable);
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
        return Ok(CeilEquationAttempt::NotApplicable);
    }

    let requires = substitute_predicates(&rule.requires, &substitution);
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
        RuleCondition::Refuted => return Ok(CeilEquationAttempt::NotApplicable),
        RuleCondition::Indeterminate => return Ok(CeilEquationAttempt::Indeterminate),
    }

    let RuleRhs::Predicates(rhs) = &rule.rhs else {
        return Ok(CeilEquationAttempt::NotApplicable);
    };
    Ok(CeilEquationAttempt::Applied(normalize_predicate(
        Predicate::And(substitute_predicates(rhs, &substitution)),
    )))
}

enum PredicateEquationAttempt {
    NotApplicable,
    Indeterminate,
    Applied(Predicate),
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
        let mut results = Vec::new();
        let mut rule_ids = Vec::new();
        let mut indeterminate = false;
        for rule in rules {
            match apply_predicate_equation(
                definition,
                rule,
                predicate,
                known_predicates,
                options,
                active_conditions,
                solver,
            )? {
                PredicateEquationAttempt::NotApplicable => {}
                PredicateEquationAttempt::Indeterminate => indeterminate = true,
                PredicateEquationAttempt::Applied(result) => {
                    results.push(result);
                    rule_ids.push(rule.attributes.unique_id.clone());
                }
            }
        }
        if indeterminate && results.is_empty() {
            return Ok(None);
        }
        match results.len() {
            0 => {}
            1 => return Ok(results.pop()),
            _ if results.windows(2).all(|pair| pair[0] == pair[1]) => {
                return Ok(results.into_iter().next());
            }
            _ => return Err(SimplificationError::ConflictingResults { rule_ids }),
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
) -> Result<PredicateEquationAttempt, SimplificationError> {
    let substitution = match match_predicate(definition, &rule.lhs, predicate) {
        PredicateMatch::Failed => return Ok(PredicateEquationAttempt::NotApplicable),
        PredicateMatch::Indeterminate => return Ok(PredicateEquationAttempt::Indeterminate),
        PredicateMatch::Success(substitution) => substitution,
    };
    let requires = substitute_predicates(&rule.requires, &substitution);
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
        RuleCondition::Refuted => return Ok(PredicateEquationAttempt::NotApplicable),
        RuleCondition::Indeterminate => return Ok(PredicateEquationAttempt::Indeterminate),
    }
    let rhs = substitute_predicates(&rule.rhs, &substitution);
    Ok(PredicateEquationAttempt::Applied(normalize_predicate(
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
                Term::domain_value(crate::term::Sort::simple("SortBool"), "true"),
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
        return Predicate::Equals(left, right);
    };
    if let Some(operator) = symbol.attributes.hook.as_deref() {
        let bool_operand = |term: &Term, value| {
            normalize_hooked_boolean_predicate(
                definition,
                Predicate::Equals(
                    term.clone(),
                    Term::domain_value(
                        crate::term::Sort::simple("SortBool"),
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
        _ => return Predicate::Equals(left, right),
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
    if sort != &crate::term::Sort::simple("SortBool") {
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
    limit: usize,
    remaining: &mut usize,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
) -> Result<Simplification, SimplificationError> {
    let mut term = term.clone();
    let mut constraints = Vec::new();
    let mut applied_rules = Vec::new();
    let mut effects = Vec::new();
    loop {
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
            });
        }
        let children = simplify_children(
            definition,
            &term,
            assumptions,
            limit,
            remaining,
            active_conditions,
            solver,
        )?;
        let root = simplify_root(
            definition,
            &children.term,
            assumptions.predicates,
            SimplificationOptions {
                max_iterations: limit,
            },
            active_conditions,
            solver,
        )?;
        constraints.extend(children.constraints);
        constraints.extend(root.constraints);
        applied_rules.extend(children.applied_rules);
        applied_rules.extend(root.applied_rules);
        effects.extend(children.effects);
        effects.extend(root.effects);
        if root.term == children.term || root.term.attributes().evaluated {
            return Ok(Simplification {
                term: root.term,
                constraints,
                applied_rules,
                effects,
            });
        }
        if *remaining == 0 {
            return Err(SimplificationError::IterationLimit {
                limit,
                term: root.term,
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
            if sort == &crate::term::Sort::simple("SortInt")
                || sort == &crate::term::Sort::simple("SortBool")
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

fn simplify_children(
    definition: &BackendDefinition,
    term: &Term,
    assumptions: &TermAssumptions<'_>,
    limit: usize,
    remaining: &mut usize,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
) -> Result<Simplification, SimplificationError> {
    let mut constraints = Vec::new();
    let mut applied_rules = Vec::new();
    let mut effects = Vec::new();
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
            limit,
            &mut child_remaining,
            active_conditions,
            solver,
        )?;
        constraints.extend(result.constraints);
        applied_rules.extend(result.applied_rules);
        effects.extend(result.effects);
        Ok::<_, SimplificationError>(result.term)
    };
    let term = match term.kind() {
        TermKind::And(left, right) => Term::and(child(left)?, child(right)?),
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
    let builtin = evaluate_builtin(term).map_err(SimplificationError::Builtin)?;
    if !matches!(builtin, BuiltinResult::NotApplicable) {
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
            BuiltinResult::NotApplicable => unreachable!(),
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
        });
    }
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
    Ok(Simplification {
        term: term.clone(),
        constraints: Vec::new(),
        applied_rules: Vec::new(),
        effects: Vec::new(),
    })
}

fn builtin_effect_result(
    definition: &BackendDefinition,
    application: &Term,
    effect: &BuiltinEffect,
) -> Result<Term, SimplificationError> {
    match effect {
        BuiltinEffect::UserLog(_) => {
            let Some(dotk) = definition.symbols.get("dotk") else {
                return Err(SimplificationError::InvalidBuiltinResultSymbol {
                    hook: "IO.logString",
                    symbol: "dotk",
                });
            };
            if !dotk.sort_variables.is_empty() || !dotk.argument_sorts.is_empty() {
                return Err(SimplificationError::InvalidBuiltinResultSymbol {
                    hook: "IO.logString",
                    symbol: "dotk",
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
        let mut results = Vec::new();
        let mut indeterminate = false;
        for rule in rules {
            match apply_equation(
                definition,
                rule,
                term,
                known_predicates,
                options,
                active_conditions,
                solver,
            )? {
                EquationAttempt::NotApplicable => {}
                EquationAttempt::Indeterminate => indeterminate = true,
                EquationAttempt::Applied(result) => results.push(result),
            }
        }
        if indeterminate
            && results.is_empty()
            && indeterminate_equation == IndeterminateEquation::Block
        {
            // A rule at this priority may apply after the symbolic subject becomes more concrete.
            // Function evaluation must preserve the application and must not fall through to an
            // owise or otherwise lower-priority equation. K simplification equations are hints:
            // the reference backend continues past indeterminate matches in that theory.
            return Ok(None);
        }
        match results.len() {
            0 => {}
            1 => return Ok(results.pop()),
            _ => {
                let first = &results[0].term;
                if results.iter().all(|result| &result.term == first) {
                    return Ok(results.into_iter().next());
                }
                return Err(SimplificationError::ConflictingResults {
                    rule_ids: results
                        .into_iter()
                        .flat_map(|result| result.applied_rules)
                        .collect(),
                });
            }
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

enum EquationAttempt {
    NotApplicable,
    Indeterminate,
    Applied(Simplification),
}

fn apply_equation(
    definition: &BackendDefinition,
    rule: &RewriteRule,
    term: &Term,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
) -> Result<EquationAttempt, SimplificationError> {
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
                    return Ok(EquationAttempt::Indeterminate);
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
    let requires = substitute_predicates(&rule.requires, &substitution);
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
        RuleCondition::Indeterminate => return Ok(EquationAttempt::Indeterminate),
    }
    let (rhs, rhs_is_bottom) = match &rule.rhs {
        RuleRhs::Term(rhs) => (substitute(rhs, &substitution), false),
        RuleRhs::Bottom => (term.clone(), true),
        RuleRhs::Predicates(_) => return Ok(EquationAttempt::NotApplicable),
    };
    let ensures = substitute_predicates(&rule.ensures, &substitution);
    let mut ensures = simplify_rule_predicates(
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
        Truth::False => Ok(EquationAttempt::Applied(Simplification {
            term: rhs,
            constraints: vec![Predicate::False],
            applied_rules: vec![rule.attributes.unique_id.clone()],
            effects: Vec::new(),
        })),
        Truth::True => Ok(EquationAttempt::Applied(Simplification {
            term: rhs,
            constraints: if rhs_is_bottom {
                vec![Predicate::False]
            } else {
                Vec::new()
            },
            applied_rules: vec![rule.attributes.unique_id.clone()],
            effects: Vec::new(),
        })),
        Truth::Unknown => {
            match solver.check_predicates(known_predicates, &Substitution::new(), &ensures) {
                Ok(Validity::Invalid) => {
                    return Ok(EquationAttempt::Applied(Simplification {
                        term: rhs,
                        constraints: vec![Predicate::False],
                        applied_rules: vec![rule.attributes.unique_id.clone()],
                        effects: Vec::new(),
                    }));
                }
                Ok(Validity::Valid) => ensures.clear(),
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
            let mut constraints = ensures;
            if rhs_is_bottom {
                constraints.push(Predicate::False);
            }
            Ok(EquationAttempt::Applied(Simplification {
                term: rhs,
                constraints,
                applied_rules: vec![rule.attributes.unique_id.clone()],
                effects: Vec::new(),
            }))
        }
    }
}

#[cfg(test)]
mod tests {
    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    use super::*;
    use crate::term::{Sort, Variable};

    fn definition(axioms: &str) -> BackendDefinition {
        let source = format!(
            r#"[]
            module MAIN
                sort SortS{{}} [hasDomainValues{{}}()]
                sort SortBool{{}} [hook{{}}("BOOL.Bool"), hasDomainValues{{}}()]
                symbol wrap{{}}(SortS{{}}) : SortS{{}} [constructor{{}}()]
                symbol budgetPair{{}}(SortS{{}}, SortS{{}}) : SortS{{}} [constructor{{}}()]
                symbol f{{}}(SortS{{}}) : SortS{{}} [function{{}}()]
                {axioms}
            endmodule []"#
        );
        let syntax = parse_definition(&source).expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    fn term(definition: &BackendDefinition, source: &str) -> Term {
        let syntax = parse_pattern(source).expect("term should parse");
        definition
            .internalize_term(&syntax, &[])
            .expect("term should internalize")
    }

    const IDENTITY: &str = r#"
        axiom{R} \implies{R}(
            \top{R}(),
            \equals{SortS{}, R}(
                f{}(X:SortS{}),
                \and{SortS{}}(X:SortS{}, \top{SortS{}}())
            )
        ) [label{}("identity"), simplification{}()]
    "#;

    #[test]
    fn evaluates_overload_axioms_before_the_overloaded_function() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                sort SortGas{} []
                symbol inj{From, To}(From) : To [sortInjection{}(), injective{}()]
                symbol intAdd{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), total{}(), hook{}("INT.add")]
                symbol gasAdd{}(SortGas{}, SortGas{}) : SortGas{}
                    [function{}(), total{}()]
                axiom{}
                    \equals{SortGas{}, SortGas{}}(
                        gasAdd{}(
                            inj{SortInt{}, SortGas{}}(K0:SortInt{}),
                            inj{SortInt{}, SortGas{}}(K1:SortInt{})
                        ),
                        inj{SortInt{}, SortGas{}}(intAdd{}(K0:SortInt{}, K1:SortInt{}))
                    )
                    [symbol-overload{}(gasAdd{}(), intAdd{}())]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let frontend_term = |source: &str| {
            let syntax = parse_pattern(source).expect("term should parse");
            definition
                .internalize_frontend_term(&syntax, &[])
                .expect("frontend term should internalize")
        };
        let input = frontend_term(
            r#"gasAdd{}(
                inj{SortInt{}, SortGas{}}(\dv{SortInt{}}("2")),
                inj{SortInt{}, SortGas{}}(\dv{SortInt{}}("3"))
            )"#,
        );
        let expected = frontend_term(r#"inj{SortInt{}, SortGas{}}(\dv{SortInt{}}("5"))"#);

        let result = simplify(&definition, &input, SimplificationOptions::default())
            .expect("overloaded function should simplify");

        assert_eq!(result.term, expected);
        assert_eq!(result.applied_rules, ["UNKNOWN", "builtin:INT.add"]);
    }

    #[test]
    fn simplifies_children_before_their_parent_to_a_fixed_point() {
        let definition = definition(IDENTITY);
        let input = term(&definition, r#"wrap{}(f{}(f{}(\dv{SortS{}}("value"))))"#);
        let expected = term(&definition, r#"wrap{}(\dv{SortS{}}("value"))"#);

        let result = simplify(&definition, &input, SimplificationOptions::default()).unwrap();
        assert_eq!(result.term, expected);
        assert_eq!(result.applied_rules, vec!["identity", "identity"]);
        assert!(result.constraints.is_empty());
    }

    #[test]
    fn does_not_apply_equations_to_evaluated_terms() {
        let definition = definition(
            r#"
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    X:SortS{},
                    \and{SortS{}}(f{}(X:SortS{}), \top{SortS{}}())
                )
            ) [label{}("expand-anything"), simplification{}()]
            "#,
        );
        let input = term(&definition, r#"\dv{SortS{}}("value")"#);

        let result = simplify(
            &definition,
            &input,
            SimplificationOptions { max_iterations: 1 },
        )
        .expect("evaluated terms should already be at a fixed point");

        assert_eq!(result.term, input);
        assert!(result.applied_rules.is_empty());
    }

    #[test]
    fn accepts_an_evaluated_result_at_the_iteration_boundary() {
        let definition = definition(
            r#"
            symbol next{}(SortS{}) : SortS{} [function{}()]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    f{}(X:SortS{}),
                    \and{SortS{}}(next{}(X:SortS{}), \top{SortS{}}())
                )
            ) [label{}("first"), simplification{}()]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    next{}(X:SortS{}),
                    \and{SortS{}}(X:SortS{}, \top{SortS{}}())
                )
            ) [label{}("second"), simplification{}()]
            "#,
        );
        let input = term(&definition, r#"f{}(\dv{SortS{}}("value"))"#);
        let expected = term(&definition, r#"\dv{SortS{}}("value")"#);

        let result = simplify(
            &definition,
            &input,
            SimplificationOptions { max_iterations: 1 },
        )
        .expect("an evaluated boundary result should not require another iteration");

        assert_eq!(result.term, expected);
        assert_eq!(result.applied_rules, ["first", "second"]);
    }

    #[test]
    fn propagates_symbolic_path_equalities_into_terms() {
        let definition = definition("");
        let x = term(&definition, "X:SortS{}");
        let y = term(&definition, "Y:SortS{}");
        let value = term(&definition, r#"\dv{SortS{}}("value")"#);
        let input = term(&definition, "wrap{}(X:SortS{})");
        let known = [Predicate::And(vec![
            Predicate::Equals(x, y.clone()),
            Predicate::Equals(y, value.clone()),
        ])];

        let result = simplify_with_solver(
            &definition,
            &input,
            &known,
            SimplificationOptions::default(),
            &NoSolver,
        )
        .unwrap();

        assert_eq!(
            result.term,
            term(&definition, r#"wrap{}(\dv{SortS{}}("value"))"#)
        );
    }

    #[test]
    fn simplifies_conjuncts_under_sibling_assumptions() {
        let definition = definition("");
        let x = term(&definition, "X:SortS{}");
        let y = term(&definition, "Y:SortS{}");
        let wrap_x = term(&definition, "wrap{}(X:SortS{})");
        let wrap_y = term(&definition, "wrap{}(Y:SortS{})");
        let predicate = Predicate::And(vec![
            Predicate::Iff(Box::new(Predicate::True), Box::new(Predicate::Equals(x, y))),
            Predicate::Not(Box::new(Predicate::Equals(wrap_x, wrap_y))),
        ]);

        let result = simplify_predicate_with_solver(
            &definition,
            &predicate,
            &[],
            SimplificationOptions::default(),
            &NoSolver,
        )
        .unwrap();

        assert_eq!(result, Predicate::False);
    }

    #[test]
    fn deduplicates_conjuncts_without_discharging_them() {
        let definition = definition("");
        let disequality = Predicate::Not(Box::new(Predicate::Equals(
            term(&definition, "X:SortS{}"),
            term(&definition, "Y:SortS{}"),
        )));
        let predicate = Predicate::And(vec![disequality.clone(), disequality.clone()]);

        let result = simplify_predicate_with_solver(
            &definition,
            &predicate,
            &[],
            SimplificationOptions::default(),
            &NoSolver,
        )
        .unwrap();

        assert_eq!(result, disequality);
    }

    #[test]
    fn flattens_overlapping_conjunctions_before_using_sibling_assumptions() {
        let definition = definition("");
        let x = term(&definition, "X:SortS{}");
        let y = term(&definition, "Y:SortS{}");
        let value = term(&definition, r#"\dv{SortS{}}("value")"#);
        let defined = Predicate::Ceil(term(&definition, "f{}(X:SortS{})"));
        let first = Predicate::Not(Box::new(Predicate::Equals(x.clone(), y)));
        let second = Predicate::Not(Box::new(Predicate::Equals(x, value)));

        let result = simplify_predicates_with_solver(
            &definition,
            &[
                Predicate::And(vec![defined.clone(), first.clone()]),
                Predicate::And(vec![defined.clone(), second.clone()]),
            ],
            &[],
            SimplificationOptions::default(),
            &NoSolver,
        )
        .unwrap();

        assert_eq!(result, [defined, first, second]);
    }

    #[test]
    fn applies_simplification_rules_to_ml_predicates() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                symbol add{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), total{}(), hook{}("INT.add")]
                axiom{R, Q} \implies{R}(
                    \not{R}(\equals{SortInt{}, R}(J:SortInt{}, K:SortInt{})),
                    \equals{Q, R}(
                        \equals{SortInt{}, Q}(
                            add{}(I:SortInt{}, J:SortInt{}),
                            add{}(I:SortInt{}, K:SortInt{})
                        ),
                        \and{Q}(\bottom{Q}(), \top{Q}())
                    )
                ) [label{}("different-offsets"), simplification{}()]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let predicate = Predicate::Equals(
            term(&definition, r#"add{}(X:SortInt{}, \dv{SortInt{}}("5"))"#),
            term(&definition, r#"add{}(X:SortInt{}, \dv{SortInt{}}("7"))"#),
        );

        let result = simplify_predicate_with_solver(
            &definition,
            &predicate,
            &[],
            SimplificationOptions::default(),
            &NoSolver,
        )
        .unwrap();

        assert_eq!(result, Predicate::False);
        assert_eq!(definition.predicate_simplification_theory.len(), 1);
    }

    #[test]
    fn applies_conditional_ceil_equations_under_known_predicates() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                symbol isFun{}(SortInt{}) : SortBool{} [function{}(), total{}()]
                symbol fun{}(SortInt{}) : SortInt{} [function{}()]
                axiom{R, Q} \implies{R}(
                    \equals{SortBool{}, R}(
                        isFun{}(X:SortInt{}),
                        \dv{SortBool{}}("true")
                    ),
                    \equals{Q, R}(
                        \ceil{SortInt{}, Q}(fun{}(X:SortInt{})),
                        \and{Q}(\top{Q}(), \top{Q}())
                    )
                ) [label{}("ceil-fun"), simplification{}()]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let is_fun = term(&definition, "isFun{}(X:SortInt{})");
        let truth = term(&definition, r#"\dv{SortBool{}}("true")"#);
        let predicate = Predicate::Ceil(term(&definition, "fun{}(X:SortInt{})"));
        let known = [Predicate::Equals(is_fun, truth)];

        assert_eq!(
            simplify_predicate_with_solver(
                &definition,
                &predicate,
                &known,
                SimplificationOptions::default(),
                &NoSolver,
            )
            .unwrap(),
            Predicate::True,
        );
        assert_eq!(
            simplify_predicate_with_solver(
                &definition,
                &predicate,
                &[],
                SimplificationOptions::default(),
                &NoSolver,
            )
            .unwrap(),
            predicate,
        );
        let ceil_rule = definition
            .ceil_theory
            .values()
            .flat_map(|groups| groups.values())
            .flatten()
            .next()
            .expect("ceil equation should be indexed");
        assert_eq!(ceil_rule.requires.len(), 1);
    }

    #[test]
    fn constructor_ceil_distinguishes_element_and_set_variables() {
        let definition = definition("");
        let fresh_constructor = Term::application(
            definition.symbols["wrap"].clone(),
            Vec::new(),
            vec![Term::variable(Variable::new("Ex#X", Sort::simple("SortS")))],
        );
        let ordinary_constructor = term(&definition, "wrap{}(X:SortS{})");
        let set_variable = Term::variable(Variable::set("X", Sort::simple("SortS")));
        let set_constructor = Term::application(
            definition.symbols["wrap"].clone(),
            Vec::new(),
            vec![set_variable.clone()],
        );

        assert_eq!(
            simplify_predicate_with_solver(
                &definition,
                &Predicate::Ceil(fresh_constructor),
                &[],
                SimplificationOptions::default(),
                &NoSolver,
            )
            .unwrap(),
            Predicate::True,
        );
        assert_eq!(
            simplify_predicate_with_solver(
                &definition,
                &Predicate::Ceil(ordinary_constructor),
                &[],
                SimplificationOptions::default(),
                &NoSolver,
            )
            .unwrap(),
            Predicate::True,
        );
        assert_eq!(
            simplify_predicate_with_solver(
                &definition,
                &Predicate::Ceil(set_constructor),
                &[],
                SimplificationOptions::default(),
                &NoSolver,
            )
            .unwrap(),
            Predicate::Ceil(set_variable),
        );
    }

    #[test]
    fn keeps_unknown_ensures_as_result_constraints() {
        let definition = definition(
            r#"
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    f{}(X:SortS{}),
                    \and{SortS{}}(
                        X:SortS{},
                        \equals{SortS{}, SortS{}}(X:SortS{}, Y:SortS{})
                    )
                )
            ) [label{}("constrained"), simplification{}()]
            "#,
        );
        let input = term(&definition, r#"f{}(\dv{SortS{}}("value"))"#);

        let result = simplify(&definition, &input, SimplificationOptions::default()).unwrap();
        assert_eq!(result.constraints.len(), 1);
        assert!(matches!(result.constraints[0], Predicate::Equals(..)));
    }

    #[test]
    fn refuted_ensures_make_the_equation_result_bottom() {
        let definition = definition(
            r#"
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    f{}(X:SortS{}),
                    \and{SortS{}}(
                        X:SortS{},
                        \equals{SortBool{}, SortS{}}(
                            \dv{SortBool{}}("true"),
                            \dv{SortBool{}}("false")
                        )
                    )
                )
            ) [label{}("contradictory-result"), simplification{}()]
            "#,
        );
        let value = term(&definition, r#"\dv{SortS{}}("value")"#);
        let input = term(&definition, r#"f{}(\dv{SortS{}}("value"))"#);

        let result = simplify(&definition, &input, SimplificationOptions::default()).unwrap();

        assert_eq!(result.term, value);
        assert_eq!(result.constraints, [Predicate::False]);
        assert_eq!(result.applied_rules, ["contradictory-result"]);
    }

    #[test]
    fn predicate_term_simplification_preserves_result_constraints() {
        let definition = definition(
            r#"
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    f{}(X:SortS{}),
                    \and{SortS{}}(
                        X:SortS{},
                        \equals{SortS{}, SortS{}}(X:SortS{}, Y:SortS{})
                    )
                )
            ) [label{}("constrained"), simplification{}()]
            "#,
        );
        let value = term(&definition, r#"\dv{SortS{}}("value")"#);
        let input = term(&definition, r#"f{}(\dv{SortS{}}("value"))"#);
        let term_result = simplify(&definition, &input, SimplificationOptions::default()).unwrap();

        let predicate_result = simplify_predicate_with_solver(
            &definition,
            &Predicate::Equals(input, value),
            &[],
            SimplificationOptions::default(),
            &NoSolver,
        )
        .unwrap();

        assert_eq!(term_result.constraints.len(), 1);
        assert_eq!(predicate_result, term_result.constraints[0]);
    }

    #[test]
    fn evaluates_hooked_functions_bottom_up() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortInt{} [hasDomainValues{}()]
                symbol add{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), total{}(), hook{}("INT.add")]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let input = term(
            &definition,
            r#"add{}(add{}(\dv{SortInt{}}("20"), \dv{SortInt{}}("21")), \dv{SortInt{}}("1"))"#,
        );
        let expected = term(&definition, r#"\dv{SortInt{}}("42")"#);

        let result = simplify(&definition, &input, SimplificationOptions::default()).unwrap();

        assert_eq!(result.term, expected);
        assert_eq!(
            result.applied_rules,
            vec!["builtin:INT.add", "builtin:INT.add"]
        );
    }

    #[test]
    fn evaluates_function_equations_with_symbolic_map_selection() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortKey{} [hasDomainValues{}()]
                sort SortValue{} [hasDomainValues{}()]
                sort SortBool{} [hasDomainValues{}()]
                hooked-sort SortMap{}
                    [hook{}("MAP.Map"), unit{}(mapUnit{}()), element{}(mapItem{}()), concat{}(mapConcat{}())]
                symbol mapUnit{}() : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.unit")]
                symbol mapItem{}(SortKey{}, SortValue{}) : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.element")]
                symbol mapConcat{}(SortMap{}, SortMap{}) : SortMap{}
                    [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
                symbol nonEmpty{}(SortMap{}) : SortBool{} [function{}()]
                axiom{R} \implies{R}(
                    \top{R}(),
                    \equals{SortBool{}, R}(
                        nonEmpty{}(
                            mapConcat{}(
                                mapItem{}(KEY:SortKey{}, VALUE:SortValue{}),
                                REST:SortMap{}
                            )
                        ),
                        \and{SortBool{}}(
                            \dv{SortBool{}}("true"),
                            \top{SortBool{}}()
                        )
                    )
                ) [label{}("non-empty-map"), simplification{}()]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let input = term(
            &definition,
            r#"nonEmpty{}(
                mapConcat{}(
                    mapItem{}(\dv{SortKey{}}("a"), \dv{SortValue{}}("1")),
                    mapItem{}(\dv{SortKey{}}("b"), \dv{SortValue{}}("2"))
                )
            )"#,
        );

        let result = simplify(&definition, &input, SimplificationOptions::default()).unwrap();

        assert_eq!(result.term, term(&definition, r#"\dv{SortBool{}}("true")"#));
        assert_eq!(result.applied_rules, ["non-empty-map"]);
    }

    #[test]
    fn does_not_rebind_configuration_variables_during_equation_matching() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortKey{} []
                sort SortValue{} []
                hooked-sort SortMap{}
                    [hook{}("MAP.Map"), unit{}(mapUnit{}()), element{}(mapItem{}()), concat{}(mapConcat{}())]
                sort SortResult{} []
                symbol mapUnit{}() : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.unit")]
                symbol mapItem{}(SortKey{}, SortValue{}) : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.element")]
                symbol mapConcat{}(SortMap{}, SortMap{}) : SortMap{}
                    [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
                symbol select{}(SortMap{}, SortKey{}) : SortResult{} [function{}()]
                symbol exact{}() : SortResult{} [constructor{}()]
                symbol different{}() : SortResult{} [constructor{}()]
                axiom{R} \implies{R}(
                    \top{R}(),
                    \equals{SortResult{}, R}(
                        select{}(
                            mapConcat{}(
                                mapItem{}(KEY:SortKey{}, VALUE:SortValue{}),
                                REST:SortMap{}
                            ),
                            KEY:SortKey{}
                        ),
                        \and{SortResult{}}(exact{}(), \top{SortResult{}}())
                    )
                ) [label{}("exact"), simplification{}()]
                axiom{R} \implies{R}(
                    \not{R}(\equals{SortKey{}, R}(ENTRY:SortKey{}, REQUESTED:SortKey{})),
                    \equals{SortResult{}, R}(
                        select{}(
                            mapConcat{}(
                                mapItem{}(ENTRY:SortKey{}, VALUE:SortValue{}),
                                REST:SortMap{}
                            ),
                            REQUESTED:SortKey{}
                        ),
                        \and{SortResult{}}(different{}(), \top{SortResult{}}())
                    )
                ) [label{}("different"), simplification{}()]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let entry = term(&definition, "ENTRY:SortKey{}");
        let requested = term(&definition, "REQUESTED:SortKey{}");
        let known = Predicate::Not(Box::new(Predicate::Equals(entry, requested)));
        let input = term(
            &definition,
            "select{}(mapConcat{}(mapItem{}(ENTRY:SortKey{}, VALUE:SortValue{}), MAP:SortMap{}), REQUESTED:SortKey{})",
        );

        let result = simplify_with_solver(
            &definition,
            &input,
            std::slice::from_ref(&known),
            SimplificationOptions::default(),
            &NoSolver,
        )
        .unwrap();

        assert_eq!(result.term, term(&definition, "different{}()"));
        assert_eq!(result.applied_rules, ["different"]);
    }

    #[test]
    fn simplification_equations_continue_past_indeterminate_higher_priority_matches() {
        let definition = definition(
            r#"
            symbol a{}() : SortS{} [constructor{}()]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    f{}(a{}()),
                    \and{SortS{}}(\dv{SortS{}}("specific"), \top{SortS{}}())
                )
            ) [label{}("specific"), simplification{}("10")]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    f{}(X:SortS{}),
                    \and{SortS{}}(\dv{SortS{}}("fallback"), \top{SortS{}}())
                )
            ) [label{}("fallback"), simplification{}("50")]
            "#,
        );
        let input = term(&definition, "f{}(Y:SortS{})");

        let result = simplify(&definition, &input, SimplificationOptions::default()).unwrap();

        assert_eq!(
            result.term,
            term(&definition, r#"\dv{SortS{}}("fallback")"#)
        );
        assert_eq!(result.applied_rules, ["fallback"]);
    }

    #[test]
    fn skips_equations_with_violated_concreteness_constraints() {
        let definition = definition(
            r#"
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    f{}(X:SortS{}),
                    \and{SortS{}}(\dv{SortS{}}("concrete"), \top{SortS{}}())
                )
            ) [label{}("concrete-only"), concrete{}(X:SortS{}), simplification{}("10")]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    f{}(X:SortS{}),
                    \and{SortS{}}(\dv{SortS{}}("fallback"), \top{SortS{}}())
                )
            ) [label{}("fallback"), simplification{}("50")]
            "#,
        );
        let input = term(&definition, "f{}(Y:SortS{})");

        let result = simplify(&definition, &input, SimplificationOptions::default()).unwrap();

        assert_eq!(
            result.term,
            term(&definition, r#"\dv{SortS{}}("fallback")"#)
        );
        assert_eq!(result.applied_rules, ["fallback"]);
    }

    #[test]
    fn applies_concrete_symbolic_canonicalization_equations() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortInt{} [hasDomainValues{}()]
                symbol add{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), functional{}(), hook{}("INT.add")]
                axiom{R} \implies{R}(
                    \top{R}(),
                    \equals{SortInt{}, R}(
                        add{}(I:SortInt{}, B:SortInt{}),
                        \and{SortInt{}}(add{}(B:SortInt{}, I:SortInt{}), \top{SortInt{}}())
                    )
                ) [
                    label{}("concrete-left"),
                    concrete{}(I:SortInt{}),
                    symbolic{}(B:SortInt{}),
                    simplification{}("51")
                ]
            endmodule []"#,
        )
        .unwrap();
        let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
        let input = term(&definition, r#"add{}(\dv{SortInt{}}("1"), X:SortInt{})"#);
        let expected = term(&definition, r#"add{}(X:SortInt{}, \dv{SortInt{}}("1"))"#);

        let result = simplify(&definition, &input, SimplificationOptions::default()).unwrap();

        assert_eq!(result.term, expected);
        assert_eq!(result.applied_rules, ["concrete-left"]);
    }

    #[test]
    fn applies_a_same_priority_result_despite_indeterminate_sibling_heads() {
        let definition = definition(
            r#"
            symbol g{}(SortS{}) : SortS{} [function{}()]
            symbol h{}(SortS{}) : SortS{} [function{}()]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    f{}(g{}(X:SortS{})),
                    \and{SortS{}}(X:SortS{}, \top{SortS{}}())
                )
            ) [label{}("through-g"), simplification{}()]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    f{}(h{}(X:SortS{})),
                    \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}())
                )
            ) [label{}("through-h"), simplification{}()]
            "#,
        );
        let input = term(&definition, "f{}(g{}(Y:SortS{}))");

        let result = simplify(&definition, &input, SimplificationOptions::default()).unwrap();

        assert_eq!(result.term, term(&definition, "Y:SortS{}"));
        assert_eq!(result.applied_rules, ["through-g"]);
    }

    #[test]
    fn normalizes_boolean_k_disequality_conditions_to_native_predicates() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortBool{} [hasDomainValues{}()]
                sort SortElement{} []
                sort SortKItem{} []
                sort SortK{} []
                symbol dotk{}() : SortK{} [constructor{}()]
                symbol kseq{}(SortKItem{}, SortK{}) : SortK{}
                    [constructor{}(), injective{}()]
                symbol andBool{}(SortBool{}, SortBool{}) : SortBool{}
                    [function{}(), total{}(), hook{}("BOOL.and")]
                symbol notEqual{}(SortK{}, SortK{}) : SortBool{}
                    [function{}(), total{}(), hook{}("KEQUAL.ne")]
                symbol g{}(SortElement{}) : SortElement{} [function{}(), total{}()]
                symbol inj{From, To}(From) : To [sortInjection{}(), injective{}()]
                axiom{R} \exists{R}(
                    Value:SortKItem{},
                    \equals{SortKItem{}, R}(
                        Value:SortKItem{},
                        inj{SortElement{}, SortKItem{}}(From:SortElement{})
                    )
                ) [subsort{SortElement{}, SortKItem{}}()]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let x = term(&definition, "X:SortElement{}");
        let y = term(&definition, "Y:SortElement{}");
        let gx = term(&definition, "g{}(X:SortElement{})");
        let gy = term(&definition, "g{}(Y:SortElement{})");
        let condition = term(
            &definition,
            r#"andBool{}(
                notEqual{}(
                    kseq{}(inj{SortElement{}, SortKItem{}}(X:SortElement{}), dotk{}()),
                    kseq{}(inj{SortElement{}, SortKItem{}}(Y:SortElement{}), dotk{}())
                ),
                notEqual{}(
                    kseq{}(inj{SortElement{}, SortKItem{}}(g{}(X:SortElement{})), dotk{}()),
                    kseq{}(inj{SortElement{}, SortKItem{}}(g{}(Y:SortElement{})), dotk{}())
                )
            )"#,
        );
        let predicate = Predicate::Equals(
            condition,
            Term::domain_value(Sort::simple("SortBool"), "true"),
        );

        let result = simplify_predicate_with_solver(
            &definition,
            &predicate,
            &[],
            SimplificationOptions::default(),
            &NoSolver,
        )
        .unwrap();

        assert_eq!(
            result,
            Predicate::And(vec![
                Predicate::Not(Box::new(Predicate::Equals(x.clone(), y.clone()))),
                Predicate::Not(Box::new(Predicate::Equals(gx, gy))),
            ])
        );
    }

    #[test]
    fn aligns_singleton_k_equality_operands_at_their_declared_supersort() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortBool{} [hasDomainValues{}()]
                sort SortSubElement{} []
                sort SortElement{} []
                sort SortKItem{} []
                sort SortK{} []
                symbol sub{}() : SortSubElement{} [constructor{}()]
                symbol dotk{}() : SortK{} [constructor{}()]
                symbol kseq{}(SortKItem{}, SortK{}) : SortK{}
                    [constructor{}(), injective{}()]
                symbol notEqual{}(SortK{}, SortK{}) : SortBool{}
                    [function{}(), total{}(), hook{}("KEQUAL.ne")]
                symbol inj{From, To}(From) : To [sortInjection{}(), injective{}()]
                axiom{R} \exists{R}(
                    Value:SortElement{},
                    \equals{SortElement{}, R}(
                        Value:SortElement{},
                        inj{SortSubElement{}, SortElement{}}(From:SortSubElement{})
                    )
                ) [subsort{SortSubElement{}, SortElement{}}()]
                axiom{R} \exists{R}(
                    Value:SortKItem{},
                    \equals{SortKItem{}, R}(
                        Value:SortKItem{},
                        inj{SortElement{}, SortKItem{}}(From:SortElement{})
                    )
                ) [subsort{SortElement{}, SortKItem{}}()]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let element = term(&definition, "X:SortElement{}");
        let sub_element = term(&definition, "sub{}()");
        let condition = term(
            &definition,
            r#"notEqual{}(
                kseq{}(inj{SortElement{}, SortKItem{}}(X:SortElement{}), dotk{}()),
                kseq{}(inj{SortSubElement{}, SortKItem{}}(sub{}()), dotk{}())
            )"#,
        );

        let result = simplify_predicate_with_solver(
            &definition,
            &Predicate::Equals(
                condition,
                Term::domain_value(Sort::simple("SortBool"), "true"),
            ),
            &[],
            SimplificationOptions::default(),
            &NoSolver,
        )
        .unwrap();

        assert_eq!(
            result,
            Predicate::Not(Box::new(Predicate::Equals(
                element,
                Term::injection(
                    Sort::simple("SortSubElement"),
                    Sort::simple("SortElement"),
                    sub_element,
                ),
            )))
        );
    }

    #[test]
    fn normalizes_nested_boolean_term_negation_to_an_equality() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                symbol notBool{}(SortBool{}) : SortBool{}
                    [function{}(), total{}(), hook{}("BOOL.not")]
                symbol equalsInt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.eq")]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let variable = term(&definition, "X:SortInt{}");
        let zero = term(&definition, r#"\dv{SortInt{}}("0")"#);
        let condition = term(
            &definition,
            r#"notBool{}(notBool{}(equalsInt{}(X:SortInt{}, \dv{SortInt{}}("0"))))"#,
        );

        let result = simplify_predicate_with_solver(
            &definition,
            &Predicate::Term(condition),
            &[],
            SimplificationOptions::default(),
            &NoSolver,
        )
        .unwrap();

        assert_eq!(result, Predicate::Equals(variable, zero));
    }

    #[test]
    fn normalizes_symbolic_integer_equality_and_keeps_operand_definedness() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortBool{} [hasDomainValues{}()]
                sort SortInt{} [hasDomainValues{}()]
                symbol eq{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.eq")]
                symbol pow{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), hook{}("INT.pow")]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let variable = term(&definition, "X:SortInt{}");
        let power = term(&definition, r#"pow{}(X:SortInt{}, \dv{SortInt{}}("256"))"#);
        let predicate = Predicate::Equals(
            Term::domain_value(Sort::simple("SortBool"), "true"),
            term(
                &definition,
                r#"eq{}(X:SortInt{}, pow{}(X:SortInt{}, \dv{SortInt{}}("256")))"#,
            ),
        );

        let result = simplify_predicate_with_solver(
            &definition,
            &predicate,
            &[],
            SimplificationOptions::default(),
            &NoSolver,
        )
        .unwrap();

        assert_eq!(
            result,
            Predicate::And(vec![
                Predicate::Ceil(power.clone()),
                Predicate::Equals(variable, power),
            ])
        );
    }

    #[test]
    fn preserves_symbolic_equalities_between_matching_injective_symbols() {
        let definition = definition(
            r#"
            symbol pair{}(SortS{}, SortS{}) : SortS{}
                [constructor{}(), injective{}()]
            "#,
        );
        let one = term(&definition, r#"\dv{SortS{}}("1")"#);
        let left = term(&definition, r#"pair{}(X:SortS{}, \dv{SortS{}}("1"))"#);
        let right = term(&definition, r#"pair{}(Y:SortS{}, \dv{SortS{}}("1"))"#);
        let predicate = Predicate::Equals(left, right);

        let result = simplify_predicate_with_solver(
            &definition,
            &predicate,
            &[],
            SimplificationOptions::default(),
            &NoSolver,
        )
        .unwrap();

        assert_eq!(result, predicate);
        assert_eq!(
            simplify_predicate_with_solver(
                &definition,
                &Predicate::Equals(one.clone(), one),
                &[],
                SimplificationOptions::default(),
                &NoSolver,
            )
            .unwrap(),
            Predicate::True,
        );
    }

    #[test]
    fn preserves_a_symbolic_equality_between_singleton_k_sequences() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortState{} []
                sort SortKItem{} []
                sort SortK{} []
                symbol peng{}() : SortState{} [constructor{}()]
                symbol dotk{}() : SortK{} [constructor{}()]
                symbol kseq{}(SortKItem{}, SortK{}) : SortK{}
                    [constructor{}(), injective{}()]
                symbol inj{From, To}(From) : To [sortInjection{}(), injective{}()]
                axiom{R} \exists{R}(
                    Value:SortKItem{},
                    \equals{SortKItem{}, R}(
                        Value:SortKItem{},
                        inj{SortState{}, SortKItem{}}(From:SortState{})
                    )
                ) [subsort{SortState{}, SortKItem{}}()]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let syntax = parse_pattern(
            r#"\not{SortK{}}(
                \equals{SortK{}, SortK{}}(
                    kseq{}(inj{SortState{}, SortKItem{}}(STATE:SortState{}), dotk{}()),
                    kseq{}(inj{SortState{}, SortKItem{}}(peng{}()), dotk{}())
                )
            )"#,
        )
        .expect("predicate should parse");
        let (predicate, _) = definition
            .internalize_predicate(&syntax, &[])
            .expect("predicate should internalize");

        let result = simplify_predicate_with_solver(
            &definition,
            &predicate,
            &[],
            SimplificationOptions::default(),
            &NoSolver,
        )
        .unwrap();

        assert_eq!(result, predicate);
    }

    #[test]
    fn returns_user_logs_as_effects_and_the_reference_unit_term() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortString{} [hasDomainValues{}()]
                sort SortK{} []
                sort SortUnit{} []
                symbol dotk{}() : SortK{} [constructor{}()]
                symbol log{}(SortString{}) : SortUnit{}
                    [function{}(), total{}(), hook{}("IO.logString")]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let input = term(&definition, r#"log{}(\dv{SortString{}}("hello from K"))"#);

        let result = simplify(&definition, &input, SimplificationOptions::default()).unwrap();

        assert!(matches!(
            result.term.kind(),
            TermKind::Application { symbol, arguments, .. }
                if symbol.name.as_ref() == "dotk"
                    && symbol.result_sort == Sort::simple("SortUnit")
                    && arguments.is_empty()
        ));
        assert_eq!(
            result.effects,
            [BuiltinEffect::UserLog("hello from K".into())]
        );
        assert_eq!(result.applied_rules, ["builtin:IO.logString"]);
    }

    #[test]
    fn represents_undefined_partial_builtins_as_bottom_constraints() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortInt{} [hasDomainValues{}()]
                symbol tdiv{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), hook{}("INT.tdiv")]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let input = term(
            &definition,
            r#"tdiv{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("0"))"#,
        );

        let result = simplify(&definition, &input, SimplificationOptions::default()).unwrap();

        assert_eq!(result.term, input);
        assert_eq!(result.constraints, [Predicate::False]);
        assert_eq!(result.applied_rules, ["builtin:INT.tdiv"]);
    }

    #[cfg(feature = "z3")]
    #[test]
    fn z3_disambiguates_symbolic_equation_requires() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                symbol lt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), smt-hook{}("<")]
                symbol f{}(SortInt{}) : SortInt{} [function{}()]
                axiom{R} \implies{R}(
                    \equals{SortBool{}, R}(
                        lt{}(X:SortInt{}, \dv{SortInt{}}("10")),
                        \dv{SortBool{}}("true")
                    ),
                    \equals{SortInt{}, R}(
                        f{}(X:SortInt{}),
                        \and{SortInt{}}(X:SortInt{}, \top{SortInt{}}())
                    )
                ) [label{}("conditional-f"), simplification{}()]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let solver = crate::smt::Z3Solver::new(&definition).unwrap();
        let input = term(&definition, "f{}(Y:SortInt{})");
        let variable = Term::variable(crate::term::Variable::new(
            "Y",
            crate::term::Sort::simple("SortInt"),
        ));
        let run = |value: &str| {
            simplify_with_solver(
                &definition,
                &input,
                &[Predicate::Equals(
                    variable.clone(),
                    Term::domain_value(crate::term::Sort::simple("SortInt"), value),
                )],
                SimplificationOptions::default(),
                &solver,
            )
            .unwrap()
        };

        assert_eq!(
            run("5").term,
            Term::domain_value(crate::term::Sort::simple("SortInt"), "5")
        );
        assert_eq!(
            run("15").term,
            term(&definition, r#"f{}(\dv{SortInt{}}("15"))"#)
        );
    }

    #[test]
    fn simplification_equations_continue_past_unknown_conditions() {
        let definition = definition(
            r#"
            axiom{R} \implies{R}(
                \equals{SortS{}, R}(X:SortS{}, \dv{SortS{}}("zero")),
                \equals{SortS{}, R}(
                    f{}(X:SortS{}),
                    \and{SortS{}}(\dv{SortS{}}("conditional"), \top{SortS{}}())
                )
            ) [label{}("conditional"), simplification{}("10")]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    f{}(X:SortS{}),
                    \and{SortS{}}(\dv{SortS{}}("fallback"), \top{SortS{}}())
                )
            ) [label{}("fallback"), simplification{}("50")]
            "#,
        );
        let input = term(&definition, "f{}(Y:SortS{})");

        let result = simplify(&definition, &input, SimplificationOptions::default()).unwrap();

        assert_eq!(
            result.term,
            term(&definition, r#"\dv{SortS{}}("fallback")"#)
        );
        assert_eq!(result.applied_rules, ["fallback"]);
    }

    #[test]
    fn preserves_functions_with_complementary_unknown_equation_conditions() {
        let definition = definition(
            r#"
            axiom{R} \implies{R}(
                \equals{SortS{}, R}(X:SortS{}, \dv{SortS{}}("zero")),
                \equals{SortS{}, R}(
                    f{}(X:SortS{}),
                    \and{SortS{}}(\dv{SortS{}}("yes"), \top{SortS{}}())
                )
            ) [label{}("yes"), simplification{}()]
            axiom{R} \implies{R}(
                \not{R}(\equals{SortS{}, R}(X:SortS{}, \dv{SortS{}}("zero"))),
                \equals{SortS{}, R}(
                    f{}(X:SortS{}),
                    \and{SortS{}}(\dv{SortS{}}("no"), \top{SortS{}}())
                )
            ) [label{}("no"), simplification{}()]
            "#,
        );
        let input = term(&definition, "f{}(Y:SortS{})");

        let result = simplify(&definition, &input, SimplificationOptions::default()).unwrap();

        assert_eq!(result.term, input);
        assert!(result.applied_rules.is_empty());
    }

    #[test]
    fn recursive_side_condition_simplification_preserves_the_application() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                symbol loop{}(SortBool{}) : SortBool{} [function{}()]
                axiom{R} \implies{R}(
                    \equals{SortBool{}, R}(
                        loop{}(X:SortBool{}),
                        \dv{SortBool{}}("true")
                    ),
                    \equals{SortBool{}, R}(
                        loop{}(X:SortBool{}),
                        \and{SortBool{}}(
                            \dv{SortBool{}}("true"),
                            \top{SortBool{}}()
                        )
                    )
                ) [label{}("recursive-condition"), simplification{}()]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let input = term(&definition, r#"loop{}(\dv{SortBool{}}("true"))"#);

        let result = simplify(&definition, &input, SimplificationOptions::default()).unwrap();

        assert_eq!(result.term, input);
        assert!(result.applied_rules.is_empty());
    }

    #[test]
    fn detects_non_terminating_equation_sets_at_the_bound() {
        let definition = definition(
            r#"
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    f{}(X:SortS{}),
                    \and{SortS{}}(f{}(f{}(X:SortS{})), \top{SortS{}}())
                )
            ) [label{}("expand"), simplification{}()]
            "#,
        );
        let input = term(&definition, r#"f{}(\dv{SortS{}}("value"))"#);

        assert!(matches!(
            simplify(
                &definition,
                &input,
                SimplificationOptions { max_iterations: 3 },
            ),
            Err(SimplificationError::IterationLimit { limit: 3, .. })
        ));
    }

    fn long_fixed_point_chain() -> (BackendDefinition, Term, Term) {
        let mut theory = String::new();
        for index in 0..=128 {
            theory.push_str(&format!(
                "symbol chain{index}{{}}() : SortS{{}} [function{{}}()]\n"
            ));
        }
        for index in 0..128 {
            let next = index + 1;
            theory.push_str(&format!(
                r#"
                axiom{{R}} \implies{{R}}(
                    \top{{R}}(),
                    \equals{{SortS{{}}, R}}(
                        chain{index}{{}}(),
                        \and{{SortS{{}}}}(chain{next}{{}}(), \top{{SortS{{}}}}())
                    )
                ) [label{{}}("chain-{index}"), simplification{{}}()]
                "#
            ));
        }
        theory.push_str(
            r#"
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    chain128{}(),
                    \and{SortS{}}(\dv{SortS{}}("done"), \top{SortS{}}())
                )
            ) [label{}("chain-done"), simplification{}()]
            "#,
        );
        let definition = definition(&theory);
        let input = term(&definition, "chain0{}()");
        let expected = term(&definition, r#"\dv{SortS{}}("done")"#);

        (definition, input, expected)
    }

    #[test]
    fn default_budget_halts_a_long_chain_with_a_typed_error() {
        let (definition, input, _) = long_fixed_point_chain();

        assert!(matches!(
            simplify(&definition, &input, SimplificationOptions::default()),
            Err(SimplificationError::IterationLimit {
                limit: DEFAULT_MAX_SIMPLIFICATION_ITERATIONS,
                ..
            })
        ));
    }

    #[test]
    fn unbounded_simplification_completes_a_long_fixed_point_chain() {
        let (definition, input, expected) = long_fixed_point_chain();

        let result = simplify(&definition, &input, SimplificationOptions::unbounded())
            .expect("the complete Kore-style pass should finish finite computations");

        assert_eq!(result.term, expected);
        assert_eq!(result.applied_rules.len(), 129);
    }

    #[test]
    fn iteration_limit_is_local_to_each_fixed_point_chain() {
        // Distilled from the pinned backend's function-evaluation-demo/NatList.demo: that finite
        // computation performs well over 100 reductions across independent constructor branches.
        let definition = definition(IDENTITY);
        let mut inputs = vec![r#"f{}(\dv{SortS{}}("value"))"#.to_owned(); 128];
        let mut expected = vec![r#"\dv{SortS{}}("value")"#.to_owned(); 128];
        while inputs.len() > 1 {
            inputs = inputs
                .chunks_exact(2)
                .map(|pair| format!("budgetPair{{}}({}, {})", pair[0], pair[1]))
                .collect();
            expected = expected
                .chunks_exact(2)
                .map(|pair| format!("budgetPair{{}}({}, {})", pair[0], pair[1]))
                .collect();
        }
        let input = term(&definition, &inputs[0]);
        let expected = term(&definition, &expected[0]);

        let result = simplify(&definition, &input, SimplificationOptions::default()).unwrap();

        assert_eq!(result.term, expected);
        assert_eq!(result.applied_rules.len(), 128);
    }

    #[test]
    fn predicate_iteration_limit_is_local_to_each_branch() {
        let definition = definition(IDENTITY);
        let value = term(&definition, r#"\dv{SortS{}}("value")"#);
        let predicates = (0..128)
            .map(|_| {
                Predicate::Equals(
                    term(&definition, r#"f{}(\dv{SortS{}}("value"))"#),
                    value.clone(),
                )
            })
            .collect();

        let result = simplify_predicate_with_solver(
            &definition,
            &Predicate::Or(predicates),
            &[],
            SimplificationOptions::default(),
            &NoSolver,
        )
        .unwrap();

        assert_eq!(result, Predicate::True);
    }

    #[cfg(feature = "z3")]
    #[test]
    fn standalone_predicate_simplification_uses_smt_for_the_residual() {
        use crate::smt::Z3Solver;

        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                sort SortList{} []
                symbol size{}(SortList{}) : SortInt{}
                    [function{}(), total{}(), hook{}("LIST.size")]
                symbol add{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), total{}(), hook{}("INT.add"), smt-hook{}("+")]
                symbol gt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.gt"), smt-hook{}(">")]
            endmodule []"#,
        )
        .unwrap();
        let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
        let predicate = Predicate::Term(term(
            &definition,
            r#"gt{}(add{}(size{}(L:SortList{}), \dv{SortInt{}}("2")), \dv{SortInt{}}("0"))"#,
        ));

        let result = simplify_and_decide_predicate_with_solver(
            &definition,
            &predicate,
            &[],
            SimplificationOptions::default(),
            &Z3Solver::new(&definition).unwrap(),
        )
        .unwrap();

        assert_eq!(result, Predicate::True);
    }

    #[test]
    fn standalone_predicate_simplification_reports_smt_unknown() {
        struct UnknownSolver;

        impl SmtSolver for UnknownSolver {
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
                Ok(Validity::Unknown("incomplete arithmetic".into()))
            }
        }

        let definition = definition("");
        let predicate = Predicate::Term(term(&definition, "X:SortS{}"));
        let result = simplify_and_decide_predicate_with_solver(
            &definition,
            &predicate,
            &[],
            SimplificationOptions::default(),
            &UnknownSolver,
        );

        assert_eq!(
            result,
            Err(SimplificationError::SmtPredicate {
                predicate: Box::new(predicate),
                error: SmtError::Unknown("incomplete arithmetic".into()),
            })
        );
    }
}
