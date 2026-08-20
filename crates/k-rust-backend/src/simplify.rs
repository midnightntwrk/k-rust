//! Recursive equation simplification to a bounded fixed point.

use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use crate::{
    builtin::{
        BuiltinEffect, BuiltinError, BuiltinResult, evaluate as evaluate_builtin, k_sequence_item,
    },
    definedness::ceil_term,
    definition::BackendDefinition,
    matching::{
        MatchMode, MatchResult, match_collection_remainders_all_in_definition,
        match_term_pairs_in_definition, match_terms_in_definition,
    },
    rewrite::{
        Truth, check_concreteness, predicates_truth, substitute_predicates,
        violates_finite_constructor_domain,
    },
    rule::{Predicate, PredicateRewriteRule, RewriteRule, RuleRhs, TermIndex, Theory, term_index},
    smt::{NoSolver, SmtError, SmtSolver, Validity},
    substitution::{Substitution, substitute},
    term::{Term, TermKind, Variable},
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SimplificationOptions {
    pub max_iterations: usize,
}

impl Default for SimplificationOptions {
    fn default() -> Self {
        Self {
            max_iterations: 100,
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
pub enum SimplificationError {
    Builtin(BuiltinError),
    IndeterminateConcreteness {
        rule_id: String,
        variable: Variable,
    },
    ConflictingResults {
        rule_ids: Vec<String>,
    },
    Smt {
        rule_id: String,
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
    simplify_with_budget(
        definition,
        term,
        known_predicates,
        options.max_iterations,
        &mut remaining,
        &active_conditions,
        solver,
    )
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

fn simplify_predicates_with_budget(
    definition: &BackendDefinition,
    predicates: &[Predicate],
    known_predicates: &[Predicate],
    limit: usize,
    remaining: &mut usize,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
) -> Result<Vec<Predicate>, SimplificationError> {
    let simplified = predicates
        .iter()
        .map(|predicate| {
            simplify_predicate_with_budget(
                definition,
                predicate,
                known_predicates,
                limit,
                remaining,
                active_conditions,
                solver,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    if violates_finite_constructor_domain(definition, &simplified) {
        Ok(vec![Predicate::False])
    } else {
        Ok(simplified)
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

pub fn simplify_predicate_with_solver(
    definition: &BackendDefinition,
    predicate: &Predicate,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Result<Predicate, SimplificationError> {
    let mut remaining = options.max_iterations;
    let active_conditions = BTreeSet::new();
    simplify_predicate_with_budget(
        definition,
        predicate,
        known_predicates,
        options.max_iterations,
        &mut remaining,
        &active_conditions,
        solver,
    )
}

fn simplify_predicate_with_budget(
    definition: &BackendDefinition,
    predicate: &Predicate,
    known_predicates: &[Predicate],
    limit: usize,
    remaining: &mut usize,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
) -> Result<Predicate, SimplificationError> {
    if known_predicates.contains(predicate) {
        return Ok(Predicate::True);
    }
    if known_predicates.contains(&Predicate::Not(Box::new(predicate.clone()))) {
        return Ok(Predicate::False);
    }
    let mut simplify_term = |term: &Term| {
        simplify_with_budget(
            definition,
            term,
            known_predicates,
            limit,
            remaining,
            active_conditions,
            solver,
        )
        .map(|result| result.term)
    };
    let simplified = match predicate {
        Predicate::True => Predicate::True,
        Predicate::False => Predicate::False,
        Predicate::Term(term) => Predicate::Term(simplify_term(term)?),
        Predicate::Equals(left, right) => {
            Predicate::Equals(simplify_term(left)?, simplify_term(right)?)
        }
        Predicate::Ceil(term) => Predicate::Ceil(simplify_term(term)?),
        Predicate::Floor(term) => Predicate::Floor(simplify_term(term)?),
        Predicate::In(left, right) => Predicate::In(simplify_term(left)?, simplify_term(right)?),
        Predicate::Not(inner) => Predicate::Not(Box::new(simplify_predicate_with_budget(
            definition,
            inner,
            known_predicates,
            limit,
            remaining,
            active_conditions,
            solver,
        )?)),
        Predicate::And(inner) | Predicate::Or(inner) => {
            let inner = simplify_predicates_with_budget(
                definition,
                inner,
                known_predicates,
                limit,
                remaining,
                active_conditions,
                solver,
            )?;
            if matches!(predicate, Predicate::And(_)) {
                Predicate::And(inner)
            } else {
                Predicate::Or(inner)
            }
        }
        Predicate::Implies(left, right) | Predicate::Iff(left, right) => {
            let left = simplify_predicate_with_budget(
                definition,
                left,
                known_predicates,
                limit,
                remaining,
                active_conditions,
                solver,
            )?;
            let right = simplify_predicate_with_budget(
                definition,
                right,
                known_predicates,
                limit,
                remaining,
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
            let inner = simplify_predicate_with_budget(
                definition,
                inner,
                known_predicates,
                limit,
                remaining,
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
    let Some(simplified) = apply_predicate_theory(
        definition,
        &simplified,
        known_predicates,
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
        known_predicates,
        limit,
        remaining,
        active_conditions,
        solver,
    )
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
        if indeterminate {
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
    let requires = if let Some(anchor) = first_predicate_term(predicate) {
        simplify_rule_predicates(
            definition,
            (&rule.attributes.unique_id, anchor),
            &requires,
            known_predicates,
            options,
            active_conditions,
            solver,
        )
        .unwrap_or(requires)
    } else {
        requires
    };
    match predicates_truth(&requires) {
        Truth::False => return Ok(PredicateEquationAttempt::NotApplicable),
        Truth::Unknown => {
            if !requires
                .iter()
                .all(|predicate| known_predicates.contains(predicate))
            {
                match solver.check_predicates(known_predicates, &Substitution::new(), &requires) {
                    Ok(Validity::Valid) => {}
                    Ok(Validity::Invalid) => {
                        return Ok(PredicateEquationAttempt::NotApplicable);
                    }
                    Ok(Validity::Indeterminate) | Err(SmtError::Unavailable) => {
                        return Ok(PredicateEquationAttempt::Indeterminate);
                    }
                    Ok(Validity::InconsistentGroundTruth) => {
                        return Err(SimplificationError::InconsistentGroundTruth {
                            rule_id: rule.attributes.unique_id.clone(),
                        });
                    }
                    Ok(Validity::Unknown(reason)) => {
                        return Err(SimplificationError::Smt {
                            rule_id: rule.attributes.unique_id.clone(),
                            error: SmtError::Unknown(reason),
                        });
                    }
                    Err(error) => {
                        return Err(SimplificationError::Smt {
                            rule_id: rule.attributes.unique_id.clone(),
                            error,
                        });
                    }
                }
            }
        }
        Truth::True => {}
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
    let negate = match symbol.attributes.hook.as_deref() {
        Some("KEQUAL.eq") => !value,
        Some("KEQUAL.ne") => value,
        _ => return Predicate::Equals(left, right),
    };
    let [left_operand, right_operand] = arguments.as_slice() else {
        return Predicate::Equals(left, right);
    };
    let (Some(left_operand), Some(right_operand)) = (
        k_sequence_item(left_operand),
        k_sequence_item(right_operand),
    ) else {
        return Predicate::Equals(left, right);
    };
    let equality = Predicate::Equals(left_operand.clone(), right_operand.clone());
    let condition = if negate {
        Predicate::Not(Box::new(equality))
    } else {
        equality
    };
    let mut predicates = ceil_term(definition, left_operand);
    predicates.extend(ceil_term(definition, right_operand));
    predicates.push(condition);
    normalize_predicate(Predicate::And(predicates))
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

fn normalize_predicate(predicate: Predicate) -> Predicate {
    match predicate {
        Predicate::Equals(left, right) => match (left.kind(), right.kind()) {
            (
                TermKind::Injection {
                    source: left_source,
                    target: left_target,
                    term: left_term,
                },
                TermKind::Injection {
                    source: right_source,
                    target: right_target,
                    term: right_term,
                },
            ) if left_source == right_source && left_target == right_target => {
                normalize_predicate(Predicate::Equals(left_term.clone(), right_term.clone()))
            }
            _ => match predicates_truth(&[Predicate::Equals(left.clone(), right.clone())]) {
                Truth::True => Predicate::True,
                Truth::False => Predicate::False,
                Truth::Unknown => Predicate::Equals(left, right),
            },
        },
        Predicate::Not(inner) => match predicates_truth(std::slice::from_ref(&inner)) {
            Truth::True => Predicate::False,
            Truth::False => Predicate::True,
            Truth::Unknown => Predicate::Not(inner),
        },
        Predicate::And(inner) => {
            let mut normalized = Vec::new();
            for predicate in inner {
                match normalize_predicate(predicate) {
                    Predicate::True => {}
                    Predicate::False => return Predicate::False,
                    Predicate::And(nested) => normalized.extend(nested),
                    predicate => normalized.push(predicate),
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
    known_predicates: &[Predicate],
    limit: usize,
    remaining: &mut usize,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
) -> Result<Simplification, SimplificationError> {
    let term = replace_from_path_condition(term, known_predicates);
    let children = simplify_children(
        definition,
        &term,
        known_predicates,
        limit,
        remaining,
        active_conditions,
        solver,
    )?;
    let root = simplify_root(
        definition,
        &children.term,
        known_predicates,
        SimplificationOptions {
            max_iterations: limit,
        },
        active_conditions,
        solver,
    )?;
    let mut constraints = children.constraints;
    constraints.extend(root.constraints);
    let mut applied_rules = children.applied_rules;
    applied_rules.extend(root.applied_rules);
    let mut effects = children.effects;
    effects.extend(root.effects);
    if root.term == children.term {
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
    let next = simplify_with_budget(
        definition,
        &root.term,
        known_predicates,
        limit,
        remaining,
        active_conditions,
        solver,
    )?;
    constraints.extend(next.constraints);
    applied_rules.extend(next.applied_rules);
    effects.extend(next.effects);
    Ok(Simplification {
        term: next.term,
        constraints,
        applied_rules,
        effects,
    })
}

fn replace_from_path_condition(term: &Term, predicates: &[Predicate]) -> Term {
    let replacements = predicates
        .iter()
        .filter_map(|predicate| {
            let Predicate::Equals(left, right) = predicate else {
                return None;
            };
            if is_scalar_domain_value(left) {
                Some((right, left))
            } else if is_scalar_domain_value(right) {
                Some((left, right))
            } else {
                None
            }
        })
        .collect::<Vec<_>>();
    replace_terms_bottom_up(term, &replacements)
}

fn is_scalar_domain_value(term: &Term) -> bool {
    matches!(
        term.kind(),
        TermKind::DomainValue { sort, .. }
            if sort == &crate::term::Sort::simple("SortInt")
                || sort == &crate::term::Sort::simple("SortBool")
    )
}

fn replace_terms_bottom_up(term: &Term, replacements: &[(&Term, &Term)]) -> Term {
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
        .find_map(|(original, replacement)| (*original == &rebuilt).then(|| (*replacement).clone()))
        .unwrap_or(rebuilt)
}

fn simplify_children(
    definition: &BackendDefinition,
    term: &Term,
    known_predicates: &[Predicate],
    limit: usize,
    remaining: &mut usize,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
) -> Result<Simplification, SimplificationError> {
    let mut constraints = Vec::new();
    let mut applied_rules = Vec::new();
    let mut effects = Vec::new();
    let mut child = |term: &Term| {
        let result = simplify_with_budget(
            definition,
            term,
            known_predicates,
            limit,
            remaining,
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
        &definition.function_theory,
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
        &definition.simplification_theory,
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

fn apply_theory(
    definition: &BackendDefinition,
    theory: &Theory,
    term: &Term,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    active_conditions: &BTreeSet<(String, Term)>,
    solver: &dyn SmtSolver,
) -> Result<Option<Simplification>, SimplificationError> {
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
        if indeterminate {
            // A rule at this priority may apply after the symbolic subject becomes more concrete.
            // Preserve the application and do not fall through to lower-priority equations.
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
    if let Some(variable) = check_concreteness(rule, &substitution) {
        return Err(SimplificationError::IndeterminateConcreteness {
            rule_id: rule.attributes.unique_id.clone(),
            variable,
        });
    }
    let requires = substitute_predicates(&rule.requires, &substitution);
    let requires = simplify_rule_predicates(
        definition,
        (&rule.attributes.unique_id, term),
        &requires,
        known_predicates,
        options,
        active_conditions,
        solver,
    )
    .unwrap_or(requires);
    match predicates_truth(&requires) {
        Truth::False => return Ok(EquationAttempt::NotApplicable),
        Truth::Unknown => {
            if !requires
                .iter()
                .all(|predicate| known_predicates.contains(predicate))
            {
                match solver.check_predicates(known_predicates, &Substitution::new(), &requires) {
                    Ok(Validity::Valid) => {}
                    Ok(Validity::Invalid) => return Ok(EquationAttempt::NotApplicable),
                    Ok(Validity::InconsistentGroundTruth) => {
                        return Err(SimplificationError::InconsistentGroundTruth {
                            rule_id: rule.attributes.unique_id.clone(),
                        });
                    }
                    Ok(Validity::Indeterminate) | Err(SmtError::Unavailable) => {
                        return Ok(EquationAttempt::Indeterminate);
                    }
                    Ok(Validity::Unknown(reason)) => {
                        return Err(SimplificationError::Smt {
                            rule_id: rule.attributes.unique_id.clone(),
                            error: SmtError::Unknown(reason),
                        });
                    }
                    Err(error) => {
                        return Err(SimplificationError::Smt {
                            rule_id: rule.attributes.unique_id.clone(),
                            error,
                        });
                    }
                }
            }
        }
        Truth::True => {}
    }
    let RuleRhs::Term(rhs) = &rule.rhs else {
        return Ok(EquationAttempt::NotApplicable);
    };
    let rhs = substitute(rhs, &substitution);
    let ensures = substitute_predicates(&rule.ensures, &substitution);
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
        Truth::False => Ok(EquationAttempt::NotApplicable),
        Truth::True => Ok(EquationAttempt::Applied(Simplification {
            term: rhs,
            constraints: Vec::new(),
            applied_rules: vec![rule.attributes.unique_id.clone()],
            effects: Vec::new(),
        })),
        Truth::Unknown => {
            match solver.check_predicates(known_predicates, &Substitution::new(), &ensures) {
                Ok(Validity::Invalid) => {
                    return Ok(EquationAttempt::NotApplicable);
                }
                Ok(
                    Validity::Valid
                    | Validity::Indeterminate
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
            Ok(EquationAttempt::Applied(Simplification {
                term: rhs,
                constraints: ensures,
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
    use crate::term::Sort;

    fn definition(axioms: &str) -> BackendDefinition {
        let source = format!(
            r#"[]
            module MAIN
                sort SortS{{}} [hasDomainValues{{}}()]
                symbol wrap{{}}(SortS{{}}) : SortS{{}} [constructor{{}}()]
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
    fn preserves_symbolic_functions_blocked_by_a_higher_priority_match() {
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

        assert_eq!(result.term, input);
        assert!(result.applied_rules.is_empty());
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
                Predicate::Ceil(x.clone()),
                Predicate::Ceil(y.clone()),
                Predicate::Not(Box::new(Predicate::Equals(x.clone(), y.clone()))),
                Predicate::Ceil(x),
                Predicate::Ceil(y),
                Predicate::Not(Box::new(Predicate::Equals(gx, gy))),
            ])
        );
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
        let variable = Term::variable(Variable::new("Y", crate::term::Sort::simple("SortInt")));
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
    fn preserves_unknown_requires_without_falling_through_to_lower_priority() {
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

        assert_eq!(result.term, input);
        assert!(result.applied_rules.is_empty());
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
}
