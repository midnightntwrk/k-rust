//! The recovery ladder of the one-rule step (row B9): what Booster delegates to Kore when a
//! match is indeterminate, tried in order: simplification of the remainder pairs
//! (`Counter::RewriteIndeterminateRecoveries`), the six splitting strategies (boolean,
//! symbolic map key, map-not-in-keys, equality, ite, collection narrowing), overload and general
//! unification, functional-symbolic and function-equality witnesses. Each strategy either
//! produces partial matches with an empty or strictly shorter remainder or declines; the
//! symbolic-map-key search is O(n^k) for k pattern entries against n subject entries.

use std::{collections::BTreeSet, sync::Arc};

use k_rust_kore::measure::{self, Counter};
use k_rust_kore::names::BuiltinSort;

use crate::{
    definedness::ceil_term,
    definition::BackendDefinition,
    fresh::fresh_variable,
    ite::{IteSplit, SplitSide, split_ite_pair},
    matching::{
        CollectionSolution, FailReason, MatchMode, MatchResult, Narrowing,
        match_terms_in_definition, solve_collection_pairs_in_definition,
    },
    rule::{Predicate, RewriteRule},
    simplify::{SimplificationError, SimplificationOptions, simplify_with_solver},
    smt::SmtSolver,
    substitution::{Substitution, compose, substitute},
    term::{
        Sort, Symbol, SymbolType, Term, TermKind, Variable, VariableKind,
        names::{VariableProvenance, split_marker},
    },
    unification::{UnificationFailure, UnificationResult, unify_term_pairs},
};

use super::{
    BooleanSplit, EqualitySplit, MapNotInKeysSplit, PartialRuleMatch, Pattern, Truth,
    extend_unique, pattern_variable_names, predicates_truth, substitute_predicates,
};

pub(crate) struct RecoveredMatch {
    pub(crate) result: MatchResult,
    pub(crate) conditions: Vec<Predicate>,
}

/// Conservatively recover matches that Booster delegates to Kore.
///
/// Both sides of each remainder are simplified after applying the partial substitution, and any
/// conditions produced by simplification are retained. For a function pattern with one unbound
/// result-sorted variable, the concrete subject is also tried as a witness; the match is accepted
/// only when evaluating that witness reproduces the subject exactly. A failed witness remains
/// indeterminate because it does not prove that no other witness exists.
pub(crate) fn recover_indeterminate_match(
    definition: &BackendDefinition,
    mut substitution: Substitution,
    remainder: Vec<(Term, Term)>,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Result<RecoveredMatch, SimplificationError> {
    measure::bump(Counter::RewriteIndeterminateRecoveries);
    let mut unresolved = Vec::new();
    let mut conditions = Vec::new();
    for (pattern, subject) in remainder {
        let pattern = substitute(&pattern, &substitution);
        let subject = substitute(&subject, &substitution);
        let mut knowledge = known_predicates.to_vec();
        extend_unique(&mut knowledge, conditions.iter().cloned());
        let simplified_pattern =
            simplify_with_solver(definition, &pattern, &knowledge, options, solver)?;
        extend_unique(&mut conditions, simplified_pattern.constraints);
        let simplified_pattern = simplified_pattern.term;
        let mut knowledge = known_predicates.to_vec();
        extend_unique(&mut knowledge, conditions.iter().cloned());
        let simplified_subject =
            simplify_with_solver(definition, &subject, &knowledge, options, solver)?;
        extend_unique(&mut conditions, simplified_subject.constraints);
        let simplified_subject = simplified_subject.term;

        if !simplified_pattern
            .attributes()
            .variables
            .is_disjoint(&simplified_subject.attributes().variables)
        {
            match unify_term_pairs(
                definition,
                substitution.clone(),
                [(simplified_pattern.clone(), simplified_subject.clone())],
            ) {
                UnificationResult::Unified(unified) => {
                    substitution = unified.substitution;
                    extend_unique(&mut conditions, unified.constraints);
                    continue;
                }
                UnificationResult::Bottom(failure) => {
                    let reason = match failure {
                        UnificationFailure::VariableRecursion(variable, term) => {
                            FailReason::VariableRecursion(variable, term)
                        }
                        UnificationFailure::DifferentSorts(left, right) => {
                            FailReason::DifferentSorts(left, right)
                        }
                        UnificationFailure::DifferentValues(left, right) => {
                            FailReason::DifferentValues(left, right)
                        }
                        UnificationFailure::DifferentSymbols(left, right) => {
                            FailReason::DifferentSymbols(left, right)
                        }
                    };
                    return Ok(RecoveredMatch {
                        result: MatchResult::Failed(reason),
                        conditions,
                    });
                }
                UnificationResult::Unsupported { .. } => {}
            }
        }

        let pair_remainder = match match_terms_in_definition(
            MatchMode::Rewrite,
            definition,
            &simplified_pattern,
            &simplified_subject,
        ) {
            MatchResult::Success(found) => {
                substitution = compose(&found, &substitution);
                continue;
            }
            MatchResult::Failed(reason) => {
                return Ok(RecoveredMatch {
                    result: MatchResult::Failed(reason),
                    conditions,
                });
            }
            MatchResult::Indeterminate {
                substitution: found,
                remainder,
            } => {
                substitution = compose(&found, &substitution);
                remainder
            }
        };

        let TermKind::Application { symbol, .. } = simplified_pattern.kind() else {
            unresolved.extend(pair_remainder);
            continue;
        };
        if !matches!(symbol.attributes.symbol_type, SymbolType::Function(_))
            || !simplified_subject.attributes().constructor_like
        {
            unresolved.extend(pair_remainder);
            continue;
        }
        let candidates = simplified_pattern
            .attributes()
            .variables
            .iter()
            .filter(|variable| {
                !substitution.contains_key(*variable) && variable.sort == simplified_subject.sort()
            })
            .cloned()
            .collect::<Vec<_>>();
        let [candidate] = candidates.as_slice() else {
            unresolved.extend(pair_remainder);
            continue;
        };
        let witness = Substitution::from([(candidate.clone(), simplified_subject.clone())]);
        let candidate_substitution = compose(&witness, &substitution);
        let candidate_pattern = substitute(&pattern, &candidate_substitution);
        let mut witness_knowledge = known_predicates.to_vec();
        extend_unique(&mut witness_knowledge, conditions.iter().cloned());
        let candidate_pattern = simplify_with_solver(
            definition,
            &candidate_pattern,
            &witness_knowledge,
            options,
            solver,
        )?;
        extend_unique(&mut conditions, candidate_pattern.constraints);
        match match_terms_in_definition(
            MatchMode::Rewrite,
            definition,
            &candidate_pattern.term,
            &simplified_subject,
        ) {
            MatchResult::Success(found) => {
                substitution = compose(&found, &candidate_substitution);
                continue;
            }
            MatchResult::Failed(_) | MatchResult::Indeterminate { .. } => {}
        }
        unresolved.extend(pair_remainder);
    }

    let conditions = substitute_predicates(&conditions, &substitution);
    let result = if unresolved.is_empty() {
        MatchResult::Success(substitution)
    } else {
        MatchResult::Indeterminate {
            substitution,
            remainder: unresolved,
        }
    };
    Ok(RecoveredMatch { result, conditions })
}

pub(super) enum GeneralUnificationRecovery {
    Unified(Vec<(Substitution, Vec<Predicate>)>),
    Bottom,
    Unsupported,
}

pub(super) fn solve_collection_remainders_with_narrowing(
    definition: &BackendDefinition,
    pattern: &Pattern,
    substitution: Substitution,
    remainder: &[(Term, Term)],
    fresh_counter: &mut u64,
) -> Option<Vec<CollectionSolution>> {
    let mut names_to_avoid = pattern_variable_names(pattern);
    let mut fresh_frame = |sort: &Sort| {
        let seed =
            Variable::new("Frame", sort.clone()).with_provenance(VariableProvenance::Existential);
        let fresh = fresh_variable(&seed, &mut names_to_avoid, fresh_counter);
        let TermKind::Variable(variable) = fresh.kind() else {
            unreachable!("fresh terms are variables")
        };
        variable.clone()
    };
    let mut narrowing = Narrowing {
        fresh_frame: &mut fresh_frame,
    };
    solve_collection_pairs_in_definition(
        MatchMode::Rewrite,
        definition,
        substitution,
        remainder,
        Some(&mut narrowing),
    )
}

pub(super) fn recover_general_unification(
    definition: &BackendDefinition,
    rule: &RewriteRule,
    pattern: &Pattern,
    substitution: Substitution,
    remainder: &[(Term, Term)],
    fresh_counter: &mut u64,
) -> GeneralUnificationRecovery {
    match unify_term_pairs(definition, substitution, remainder.iter().cloned()) {
        UnificationResult::Bottom(_) => GeneralUnificationRecovery::Bottom,
        UnificationResult::Unsupported {
            substitution,
            constraints,
            remainder,
        } => {
            let Some(solutions) = solve_collection_remainders_with_narrowing(
                definition,
                pattern,
                substitution,
                &remainder,
                fresh_counter,
            ) else {
                return GeneralUnificationRecovery::Unsupported;
            };
            if solutions.is_empty() {
                return GeneralUnificationRecovery::Bottom;
            }
            GeneralUnificationRecovery::Unified(finalize_general_unification(
                definition,
                rule,
                pattern,
                solutions,
                &constraints,
                &remainder,
                fresh_counter,
            ))
        }
        UnificationResult::Unified(unified) => {
            GeneralUnificationRecovery::Unified(finalize_general_unification(
                definition,
                rule,
                pattern,
                vec![CollectionSolution {
                    substitution: unified.substitution,
                    constraints: Vec::new(),
                    fresh: BTreeSet::new(),
                }],
                &unified.constraints,
                &[],
                fresh_counter,
            ))
        }
    }
}

fn finalize_general_unification(
    definition: &BackendDefinition,
    rule: &RewriteRule,
    pattern: &Pattern,
    solutions: Vec<CollectionSolution>,
    constraints: &[Predicate],
    collection_pairs: &[(Term, Term)],
    fresh_counter: &mut u64,
) -> Vec<(Substitution, Vec<Predicate>)> {
    solutions
        .into_iter()
        .map(|solution| {
            let (substitution, _) =
                freshen_unbound_rule_variables(rule, pattern, solution.substitution, fresh_counter);
            let mut all_constraints = constraints.to_vec();
            extend_unique(&mut all_constraints, solution.constraints);
            let mut constraints = substitute_predicates(&all_constraints, &substitution);
            extend_unique(
                &mut constraints,
                collection_unification_definedness(definition, collection_pairs, &substitution),
            );
            (substitution, constraints)
        })
        .collect()
}

pub(crate) fn collection_unification_definedness(
    definition: &BackendDefinition,
    pairs: &[(Term, Term)],
    substitution: &Substitution,
) -> Vec<Predicate> {
    let mut conditions = Vec::new();
    for (left, right) in pairs {
        extend_unique(
            &mut conditions,
            ceil_term(definition, &substitute(left, substitution)),
        );
        extend_unique(
            &mut conditions,
            ceil_term(definition, &substitute(right, substitution)),
        );
    }
    conditions
}

/// Recover first-order narrowing when a functional pattern is matched by a symbolic
/// configuration variable.
///
/// Rule variables left unbound by ordinary matching become fresh variables in the successor. The
/// resulting equality is retained on the applied branch and negated on its complementary branch.
/// Function-like fragments additionally retain the definedness conditions produced by their
/// `ceil` theory.
pub(super) fn recover_functional_symbolic_match(
    definition: &BackendDefinition,
    rule: &RewriteRule,
    pattern: &Pattern,
    substitution: Substitution,
    remainder: &[(Term, Term)],
    fresh_counter: &mut u64,
) -> Option<(Substitution, Vec<Predicate>)> {
    for (rule_term, configuration_term) in remainder {
        let rule_term = substitute(rule_term, &substitution);
        let configuration_term = substitute(configuration_term, &substitution);
        let TermKind::Variable(configuration_variable) = configuration_term.kind() else {
            return None;
        };
        if !is_functional_pattern(&rule_term)
            || rule_term
                .attributes()
                .variables
                .contains(configuration_variable)
            || !definition
                .sort_graph
                .check_subsort(&rule_term.sort(), &configuration_variable.sort)
                .ok()?
        {
            return None;
        }
    }

    let (substitution, fresh_variables) =
        freshen_unbound_rule_variables(rule, pattern, substitution, fresh_counter);

    let mut conditions = Vec::new();
    for (rule_term, configuration_term) in remainder {
        let rule_term = substitute(rule_term, &substitution);
        let configuration_term = substitute(configuration_term, &substitution);
        if rule_term == configuration_term {
            continue;
        }
        let TermKind::Variable(configuration_variable) = configuration_term.kind() else {
            return None;
        };
        debug_assert!(is_functional_pattern(&rule_term));
        debug_assert!(
            definition
                .sort_graph
                .check_subsort(&rule_term.sort(), &configuration_variable.sort)
                .unwrap_or(false)
        );
        let definedness = if contains_function_pattern(&rule_term) {
            ceil_term(definition, &rule_term)
        } else {
            Vec::new()
        };
        conditions.push(Predicate::Equals(configuration_term, rule_term));
        for predicate in definedness {
            if matches!(
                &predicate,
                Predicate::Ceil(term)
                    if matches!(term.kind(), TermKind::Variable(variable) if fresh_variables.contains(variable))
            ) || conditions.contains(&predicate)
            {
                continue;
            }
            conditions.push(predicate);
        }
    }
    (!conditions.is_empty()).then_some((substitution, conditions))
}

pub(super) fn freshen_unbound_rule_variables(
    rule: &RewriteRule,
    pattern: &Pattern,
    mut substitution: Substitution,
    fresh_counter: &mut u64,
) -> (Substitution, BTreeSet<Variable>) {
    // Kore's checkSubstitutionCoverage permits narrowing only when the whole initial term is
    // not constructor-like. Keep concrete rule variables available for requires to bind, then
    // check coverage before constructing the successor in apply_rule_with_match.
    if pattern.term.concrete_after_normalization() {
        return (substitution, BTreeSet::new());
    }
    let mut names_to_avoid = pattern_variable_names(pattern)
        .into_iter()
        .chain(
            substitution
                .values()
                .flat_map(|term| term.attributes().variables.iter())
                .map(|variable| variable.name.clone()),
        )
        .collect::<BTreeSet<_>>();
    let unbound = rule
        .lhs
        .attributes()
        .variables
        .iter()
        .filter(|variable| !substitution.contains_key(*variable))
        .cloned()
        .collect::<Vec<_>>();
    let mut fresh_variables = BTreeSet::new();
    for variable in unbound {
        let (_, base_name) = split_marker(
            &variable.name,
            &[VariableProvenance::Rule, VariableProvenance::Equation],
        );
        let existential = variable
            .with_name(base_name)
            .with_provenance(VariableProvenance::Existential);
        let fresh = fresh_variable(&existential, &mut names_to_avoid, fresh_counter);
        let TermKind::Variable(fresh_variable) = fresh.kind() else {
            unreachable!("fresh terms are variables")
        };
        fresh_variables.insert(fresh_variable.clone());
        substitution = compose(&Substitution::from([(variable, fresh)]), &substitution);
    }
    (substitution, fresh_variables)
}

/// Preserve unresolved functional unification as equality conditions after simplification reaches
/// a fixed point. AC collection equations are deliberately excluded because they require their
/// own multi-solution theory rather than one opaque equality.
pub(super) fn recover_function_equality_match(
    rule: &RewriteRule,
    pattern: &Pattern,
    substitution: Substitution,
    remainder: &[(Term, Term)],
    fresh_counter: &mut u64,
) -> Option<(Substitution, Vec<Predicate>)> {
    if remainder.is_empty()
        || remainder.iter().any(|(left, right)| {
            left.sort() != right.sort()
                || is_collection_term(left)
                || is_collection_term(right)
                || (!contains_function_pattern(left) && !contains_function_pattern(right))
        })
    {
        return None;
    }
    let (substitution, _) =
        freshen_unbound_rule_variables(rule, pattern, substitution, fresh_counter);
    let conditions = remainder
        .iter()
        .filter_map(|(left, right)| {
            let left = substitute(left, &substitution);
            let right = substitute(right, &substitution);
            (left != right).then_some(Predicate::Equals(left, right))
        })
        .collect::<Vec<_>>();
    (!conditions.is_empty()).then_some((substitution, conditions))
}

fn is_collection_term(term: &Term) -> bool {
    matches!(
        term.kind(),
        TermKind::Map { .. } | TermKind::List { .. } | TermKind::Set { .. }
    )
}

pub(super) fn is_functional_pattern(term: &Term) -> bool {
    match term.kind() {
        TermKind::Application {
            symbol, arguments, ..
        } => {
            matches!(
                symbol.attributes.symbol_type,
                SymbolType::Constructor | SymbolType::Function(_)
            ) && arguments.iter().all(is_functional_pattern)
        }
        TermKind::Map { entries, rest, .. } => {
            entries
                .iter()
                .all(|(key, value)| is_functional_pattern(key) && is_functional_pattern(value))
                && rest.as_ref().is_none_or(is_functional_pattern)
        }
        TermKind::List { heads, rest, .. } => {
            heads.iter().all(is_functional_pattern)
                && rest.as_ref().is_none_or(|(middle, tails)| {
                    is_functional_pattern(middle) && tails.iter().all(is_functional_pattern)
                })
        }
        TermKind::Set { elements, rest, .. } => {
            elements.iter().all(is_functional_pattern)
                && rest.as_ref().is_none_or(is_functional_pattern)
        }
        TermKind::DomainValue { .. } => true,
        // An element variable denotes one element; a set variable denotes an arbitrary pattern.
        TermKind::Variable(variable) => variable.kind == VariableKind::Element,
        TermKind::Injection { term, .. } => is_functional_pattern(term),
        TermKind::And(..) => false,
    }
}

fn contains_function_pattern(term: &Term) -> bool {
    match term.kind() {
        TermKind::Application {
            symbol, arguments, ..
        } => {
            matches!(symbol.attributes.symbol_type, SymbolType::Function(_))
                || arguments.iter().any(contains_function_pattern)
        }
        TermKind::Injection { term, .. } => contains_function_pattern(term),
        TermKind::And(left, right) => {
            contains_function_pattern(left) || contains_function_pattern(right)
        }
        TermKind::Map { .. } | TermKind::List { .. } | TermKind::Set { .. } => true,
        TermKind::DomainValue { .. } | TermKind::Variable(_) => false,
    }
}

/// Narrow a concrete rule-map key against symbolic keys in a closed configuration map.
///
/// Booster leaves this shape for Kore's unifier. Each possible key selection becomes an applied
/// branch guarded by equality; ordinary rule remainder construction preserves the complementary
/// disequalities on the original configuration.
pub(super) fn recover_symbolic_map_key_matches(
    definition: &BackendDefinition,
    substitution: Substitution,
    remainder: &[(Term, Term)],
) -> Option<Vec<PartialRuleMatch>> {
    let protected_variables = substitution
        .values()
        .flat_map(|term| term.attributes().variables.iter().cloned())
        .collect::<BTreeSet<_>>();
    let (pair_index, map_definition, pattern_entries, pattern_rest, subject_entries) = remainder
        .iter()
        .enumerate()
        .find_map(|(index, (pattern, subject))| {
            let pattern = substitute(pattern, &substitution);
            let subject = substitute(subject, &substitution);
            let (
                TermKind::Map {
                    definition: pattern_definition,
                    entries: pattern_entries,
                    rest: Some(pattern_rest),
                },
                TermKind::Map {
                    definition: subject_definition,
                    entries: subject_entries,
                    rest: None,
                },
            ) = (pattern.kind(), subject.kind())
            else {
                return None;
            };
            if pattern_definition != subject_definition
                || pattern_entries.is_empty()
                || !pattern_entries.iter().all(|(key, _)| {
                    key.attributes().constructor_like
                        || (!key.attributes().variables.is_empty()
                            && key
                                .attributes()
                                .variables
                                .iter()
                                .all(|variable| protected_variables.contains(variable)))
                })
                || !matches!(pattern_rest.kind(), TermKind::Variable(variable)
                    if !protected_variables.contains(variable))
                || pattern_entries.len()
                    > subject_entries
                        .iter()
                        .filter(|(key, _)| matches!(key.kind(), TermKind::Variable(_)))
                        .count()
            {
                return None;
            }
            Some((
                index,
                pattern_definition.clone(),
                pattern_entries.clone(),
                pattern_rest.clone(),
                subject_entries.clone(),
            ))
        })?;
    let branch_remainder = remainder
        .iter()
        .enumerate()
        .filter(|(index, _)| *index != pair_index)
        .map(|(_, pair)| pair.clone())
        .collect::<Vec<_>>();
    let mut matches = Vec::new();
    search_symbolic_map_key_matches(
        definition,
        &map_definition,
        &pattern_entries,
        &pattern_rest,
        0,
        subject_entries,
        substitution,
        Vec::new(),
        branch_remainder,
        &mut matches,
    );
    Some(matches)
}

#[allow(clippy::too_many_arguments)]
fn search_symbolic_map_key_matches(
    definition: &BackendDefinition,
    map_definition: &Arc<crate::term::MapDefinition>,
    pattern_entries: &[(Term, Term)],
    pattern_rest: &Term,
    index: usize,
    remaining_subject: Vec<(Term, Term)>,
    substitution: Substitution,
    conditions: Vec<Predicate>,
    unresolved: Vec<(Term, Term)>,
    matches: &mut Vec<PartialRuleMatch>,
) {
    if index == pattern_entries.len() {
        let rest = substitute(pattern_rest, &substitution);
        let subject_rest = Term::map(map_definition.clone(), remaining_subject, None);
        let (substitution, unresolved) =
            match match_terms_in_definition(MatchMode::Rewrite, definition, &rest, &subject_rest) {
                MatchResult::Failed(_) => return,
                MatchResult::Success(found) => (compose(&found, &substitution), unresolved),
                MatchResult::Indeterminate {
                    substitution: found,
                    remainder,
                } => {
                    let mut unresolved = unresolved;
                    unresolved.extend(remainder);
                    (compose(&found, &substitution), unresolved)
                }
            };
        matches.push(PartialRuleMatch {
            substitution,
            conditions,
            remainder: unresolved,
        });
        return;
    }

    let (pattern_key, pattern_value) = &pattern_entries[index];
    let pattern_key = substitute(pattern_key, &substitution);
    // Invariant: each level drops one `remaining_subject` entry and extends the assignment.
    for subject_index in 0..remaining_subject.len() {
        let (subject_key, subject_value) = &remaining_subject[subject_index];
        if !matches!(subject_key.kind(), TermKind::Variable(_)) {
            continue;
        }
        let condition = Predicate::Equals(subject_key.clone(), pattern_key.clone());
        if predicates_truth(std::slice::from_ref(&condition)) == Truth::False {
            continue;
        }
        let pattern_value = substitute(pattern_value, &substitution);
        let (next_substitution, next_unresolved) = match match_terms_in_definition(
            MatchMode::Rewrite,
            definition,
            &pattern_value,
            subject_value,
        ) {
            MatchResult::Failed(_) => continue,
            MatchResult::Success(found) => (compose(&found, &substitution), unresolved.clone()),
            MatchResult::Indeterminate {
                substitution: found,
                remainder,
            } => {
                let mut next_unresolved = unresolved.clone();
                next_unresolved.extend(remainder);
                (compose(&found, &substitution), next_unresolved)
            }
        };
        let mut next_conditions = conditions.clone();
        if predicates_truth(std::slice::from_ref(&condition)) == Truth::Unknown
            && !next_conditions.contains(&condition)
        {
            next_conditions.push(condition);
        }
        let mut next_subject = remaining_subject.clone();
        next_subject.remove(subject_index);
        search_symbolic_map_key_matches(
            definition,
            map_definition,
            pattern_entries,
            pattern_rest,
            index + 1,
            next_subject,
            next_substitution,
            next_conditions,
            next_unresolved,
            matches,
        );
    }
}

/// Decompose the Boolean unification cases used by the pinned backend: conjunction with `true`,
/// disjunction with `false`, and negation with either Boolean value.
pub(super) fn recover_boolean_matches(
    definition: &BackendDefinition,
    mut substitution: Substitution,
    remainder: &[(Term, Term)],
) -> Option<Vec<PartialRuleMatch>> {
    let (index, split) = remainder
        .iter()
        .enumerate()
        .find_map(|(index, (left, right))| {
            let left = substitute(left, &substitution);
            let right = substitute(right, &substitution);
            split_boolean_pair(&left, &right).map(|split| (index, split))
        })?;
    let mut branch_remainder = remainder
        .iter()
        .enumerate()
        .filter(|(candidate, _)| *candidate != index)
        .map(|(_, pair)| pair.clone())
        .collect::<Vec<_>>();
    let expected = Term::domain_value(
        Sort::builtin(BuiltinSort::Bool),
        if split.expected { "true" } else { "false" },
    );

    if matches!(split.side, SplitSide::Pattern) {
        for operand in split.operands {
            let operand = substitute(&operand, &substitution);
            match match_terms_in_definition(MatchMode::Implies, definition, &operand, &expected) {
                MatchResult::Failed(_) => return Some(Vec::new()),
                MatchResult::Success(found) => {
                    substitution = compose(&found, &substitution);
                }
                MatchResult::Indeterminate {
                    substitution: found,
                    remainder,
                } => {
                    substitution = compose(&found, &substitution);
                    branch_remainder.extend(remainder);
                }
            }
        }
        return Some(vec![PartialRuleMatch {
            substitution,
            conditions: Vec::new(),
            remainder: branch_remainder,
        }]);
    }

    let mut conditions = Vec::new();
    for operand in split.operands {
        let condition = Predicate::Equals(operand, expected.clone());
        match predicates_truth(std::slice::from_ref(&condition)) {
            Truth::False => return Some(Vec::new()),
            Truth::True => {}
            Truth::Unknown => conditions.push(condition),
        }
    }
    Some(vec![PartialRuleMatch {
        substitution,
        conditions,
        remainder: branch_remainder,
    }])
}

fn split_boolean_pair(left: &Term, right: &Term) -> Option<BooleanSplit> {
    if let Some(value) = bool_domain_value(right)
        && let Some((expected, operands)) = boolean_operands(left, value)
    {
        return Some(BooleanSplit {
            side: SplitSide::Pattern,
            expected,
            operands,
        });
    }
    let value = bool_domain_value(left)?;
    let (expected, operands) = boolean_operands(right, value)?;
    Some(BooleanSplit {
        side: SplitSide::Subject,
        expected,
        operands,
    })
}

fn boolean_operands(term: &Term, value: bool) -> Option<(bool, Vec<Term>)> {
    let TermKind::Application {
        symbol, arguments, ..
    } = term.kind()
    else {
        return None;
    };
    match (
        symbol.attributes.hook.as_deref(),
        value,
        arguments.as_slice(),
    ) {
        (Some("BOOL.and"), true, [left, right]) => Some((true, vec![left.clone(), right.clone()])),
        (Some("BOOL.or"), false, [left, right]) => Some((false, vec![left.clone(), right.clone()])),
        (Some("BOOL.not"), value, [operand]) => Some((!value, vec![operand.clone()])),
        _ => None,
    }
}

/// Decompose `MAP.in_keys(key, map) = false` over the known entries of a normalized map.
pub(super) fn recover_map_not_in_keys_matches(
    definition: &BackendDefinition,
    rule: &RewriteRule,
    pattern: &Pattern,
    substitution: Substitution,
    remainder: &[(Term, Term)],
    fresh_counter: &mut u64,
) -> Option<Vec<PartialRuleMatch>> {
    let (index, split) = remainder
        .iter()
        .enumerate()
        .find_map(|(index, (left, right))| {
            let left = substitute(left, &substitution);
            let right = substitute(right, &substitution);
            split_map_not_in_keys_pair(&left, &right).map(|split| (index, split))
        })?;
    let substitution = if matches!(split.side, SplitSide::Pattern) {
        freshen_unbound_rule_variables(rule, pattern, substitution, fresh_counter).0
    } else {
        substitution
    };
    let key = substitute(&split.key, &substitution);
    let map = substitute(&split.map, &substitution);
    let TermKind::Map { entries, rest, .. } = map.kind() else {
        return None;
    };
    if entries.is_empty() && rest.is_some() {
        return None;
    }

    let untouched = remainder
        .iter()
        .enumerate()
        .filter(|(candidate, _)| *candidate != index)
        .map(|(_, pair)| pair.clone())
        .collect::<Vec<_>>();
    if entries.is_empty() {
        return Some(vec![PartialRuleMatch {
            substitution,
            conditions: Vec::new(),
            remainder: untouched,
        }]);
    }

    let mut conditions = ceil_term(definition, &key);
    extend_unique(&mut conditions, ceil_term(definition, &map));
    for (map_key, _) in entries {
        extend_unique(
            &mut conditions,
            [Predicate::Not(Box::new(Predicate::Equals(
                key.clone(),
                map_key.clone(),
            )))],
        );
    }
    if let Some(rest) = rest {
        let membership =
            Term::application(split.symbol, split.sort_arguments, vec![key, rest.clone()]);
        extend_unique(
            &mut conditions,
            [Predicate::Equals(
                membership,
                Term::domain_value(Sort::builtin(BuiltinSort::Bool), "false"),
            )],
        );
    }
    conditions.retain(|condition| {
        !matches!(
            predicates_truth(std::slice::from_ref(condition)),
            Truth::True
        )
    });
    if matches!(predicates_truth(&conditions), Truth::False) {
        return Some(Vec::new());
    }
    Some(vec![PartialRuleMatch {
        substitution,
        conditions,
        remainder: untouched,
    }])
}

fn split_map_not_in_keys_pair(left: &Term, right: &Term) -> Option<MapNotInKeysSplit> {
    if bool_domain_value(right) == Some(false)
        && let Some((symbol, sort_arguments, key, map)) = map_in_keys_arguments(left)
    {
        return Some(MapNotInKeysSplit {
            side: SplitSide::Pattern,
            symbol,
            sort_arguments,
            key,
            map,
        });
    }
    if bool_domain_value(left) != Some(false) {
        return None;
    }
    let (symbol, sort_arguments, key, map) = map_in_keys_arguments(right)?;
    Some(MapNotInKeysSplit {
        side: SplitSide::Subject,
        symbol,
        sort_arguments,
        key,
        map,
    })
}

fn map_in_keys_arguments(term: &Term) -> Option<(Arc<Symbol>, Vec<Sort>, Term, Term)> {
    let TermKind::Application {
        symbol,
        sort_arguments,
        arguments,
    } = term.kind()
    else {
        return None;
    };
    if symbol.attributes.hook.as_deref() != Some("MAP.in_keys") {
        return None;
    }
    let [key, map] = arguments.as_slice() else {
        return None;
    };
    Some((
        symbol.clone(),
        sort_arguments.clone(),
        key.clone(),
        map.clone(),
    ))
}

/// Normalize unification of a hooked equality application with a Boolean domain value.
///
/// The true case delegates to ordinary unification of the operands so useful substitutions are
/// retained. The false case is the complement of operand equality and therefore remains a path
/// condition. This is the same normalization used by the pinned backend's `unifyEq` hook.
pub(super) fn recover_equality_matches(
    definition: &BackendDefinition,
    rule: &RewriteRule,
    pattern: &Pattern,
    substitution: Substitution,
    remainder: &[(Term, Term)],
    fresh_counter: &mut u64,
) -> Option<Vec<PartialRuleMatch>> {
    let (index, split) = remainder
        .iter()
        .enumerate()
        .find_map(|(index, (left, right))| {
            let left = substitute(left, &substitution);
            let right = substitute(right, &substitution);
            split_equality_pair(&left, &right).map(|split| (index, split))
        })?;
    let mut untouched = remainder
        .iter()
        .enumerate()
        .filter(|(candidate, _)| *candidate != index)
        .map(|(_, pair)| pair.clone())
        .collect::<Vec<_>>();

    if split.value && matches!(split.side, SplitSide::Pattern) {
        return Some(
            match match_terms_in_definition(
                MatchMode::Implies,
                definition,
                &split.left,
                &split.right,
            ) {
                MatchResult::Failed(_) => Vec::new(),
                MatchResult::Success(found) => vec![PartialRuleMatch {
                    substitution: compose(&found, &substitution),
                    conditions: Vec::new(),
                    remainder: untouched,
                }],
                MatchResult::Indeterminate {
                    substitution: found,
                    remainder,
                } => {
                    untouched.extend(remainder);
                    vec![PartialRuleMatch {
                        substitution: compose(&found, &substitution),
                        conditions: Vec::new(),
                        remainder: untouched,
                    }]
                }
            },
        );
    }

    let substitution = if matches!(split.side, SplitSide::Pattern) {
        freshen_unbound_rule_variables(rule, pattern, substitution, fresh_counter).0
    } else {
        substitution
    };
    let left = substitute(&split.left, &substitution);
    let right = substitute(&split.right, &substitution);
    let equality = Predicate::Equals(left, right);
    let condition = if split.value {
        equality
    } else {
        Predicate::Not(Box::new(equality))
    };
    let conditions = match predicates_truth(std::slice::from_ref(&condition)) {
        Truth::False => return Some(Vec::new()),
        Truth::True => Vec::new(),
        Truth::Unknown => vec![condition],
    };
    Some(vec![PartialRuleMatch {
        substitution,
        conditions,
        remainder: untouched,
    }])
}

fn split_equality_pair(left: &Term, right: &Term) -> Option<EqualitySplit> {
    if let Some((operand1, operand2)) = equality_arguments(left)
        && let Some(value) = bool_domain_value(right)
    {
        return Some(EqualitySplit {
            side: SplitSide::Pattern,
            value,
            left: operand1,
            right: operand2,
        });
    }
    let (operand1, operand2) = equality_arguments(right)?;
    Some(EqualitySplit {
        side: SplitSide::Subject,
        value: bool_domain_value(left)?,
        left: operand1,
        right: operand2,
    })
}

fn equality_arguments(term: &Term) -> Option<(Term, Term)> {
    let TermKind::Application {
        symbol, arguments, ..
    } = term.kind()
    else {
        return None;
    };
    if !matches!(
        symbol.attributes.hook.as_deref(),
        Some("INT.eq" | "STRING.eq" | "KEQUAL.eq")
    ) || !is_functional_pattern(term)
    {
        return None;
    }
    let [left, right] = arguments.as_slice() else {
        return None;
    };
    Some((left.clone(), right.clone()))
}

fn bool_domain_value(term: &Term) -> Option<bool> {
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

/// Split symbolic `KEQUAL.ite` applications at the unification boundary.
///
/// Concrete conditions are handled by the builtin evaluator. When the condition remains
/// symbolic, each ITE branch is matched independently and guarded by the Boolean value which
/// selects it. This mirrors the pinned backend's `unifyIfThenElse` behavior without teaching the
/// syntax-directed matcher about branching.
pub(super) fn recover_ite_matches(
    definition: &BackendDefinition,
    substitution: Substitution,
    remainder: &[(Term, Term)],
) -> Option<Vec<PartialRuleMatch>> {
    let (index, side, condition, then_pair, else_pair) =
        remainder
            .iter()
            .enumerate()
            .find_map(|(index, (pattern, subject))| {
                let pattern = substitute(pattern, &substitution);
                let subject = substitute(subject, &substitution);
                split_ite_pair(&pattern, &subject).map(
                    |IteSplit {
                         side,
                         condition,
                         then_pair,
                         else_pair,
                     }| { (index, side, condition, then_pair, else_pair) },
                )
            })?;
    let untouched = remainder
        .iter()
        .enumerate()
        .filter(|(candidate, _)| *candidate != index)
        .map(|(_, pair)| pair.clone())
        .collect::<Vec<_>>();

    let mut recovered = Vec::new();
    for (value, (pattern, subject)) in [(true, then_pair), (false, else_pair)] {
        let matched = match_terms_in_definition(MatchMode::Rewrite, definition, &pattern, &subject);
        let (found, mut branch_remainder) = match matched {
            MatchResult::Failed(_) => continue,
            MatchResult::Success(found) => (found, Vec::new()),
            MatchResult::Indeterminate {
                substitution,
                remainder,
            } => (substitution, remainder),
        };
        let mut substitution = compose(&found, &substitution);
        branch_remainder.extend(untouched.iter().cloned());
        let value = Term::domain_value(
            Sort::builtin(BuiltinSort::Bool),
            if value { "true" } else { "false" },
        );
        let mut condition = substitute(&condition, &substitution);
        let mut conditions = Vec::new();
        if matches!(side, SplitSide::Pattern) {
            match match_terms_in_definition(MatchMode::Rewrite, definition, &condition, &value) {
                MatchResult::Failed(_) => continue,
                MatchResult::Success(found) => {
                    substitution = compose(&found, &substitution);
                }
                MatchResult::Indeterminate {
                    substitution: found,
                    remainder,
                } => {
                    substitution = compose(&found, &substitution);
                    branch_remainder.extend(remainder);
                    condition = substitute(&condition, &substitution);
                    conditions.push(Predicate::Equals(condition, value));
                }
            }
        } else {
            conditions.push(Predicate::Equals(condition, value));
        }
        recovered.push(PartialRuleMatch {
            substitution,
            conditions,
            remainder: branch_remainder,
        });
    }
    Some(recovered)
}

pub(super) fn recover_overload_symbolic_match(
    definition: &BackendDefinition,
    state: &Pattern,
    substitution: Substitution,
    remainder: &[(Term, Term)],
    fresh_counter: &mut u64,
) -> Option<(Substitution, Vec<Predicate>)> {
    let [(rule_term, configuration_term)] = remainder else {
        return None;
    };
    let rule_term = substitute(rule_term, &substitution);
    let configuration_term = substitute(configuration_term, &substitution);
    let rule_application = match rule_term.kind() {
        TermKind::Application { .. } => &rule_term,
        TermKind::Injection { term, .. } => term,
        _ => return None,
    };
    let TermKind::Application {
        symbol: rule_symbol,
        ..
    } = rule_application.kind()
    else {
        return None;
    };
    let TermKind::Injection {
        target,
        term: configuration_inner,
        ..
    } = configuration_term.kind()
    else {
        return None;
    };
    let TermKind::Variable(configuration_variable) = configuration_inner.kind() else {
        return None;
    };

    let mut candidates = definition
        .overloads
        .overloaded_by(&rule_symbol.name)
        .into_iter()
        .filter_map(|name| definition.symbols.get(&name).cloned())
        .filter(|symbol| {
            symbol.sort_variables.is_empty()
                && symbol.attributes.symbol_type == SymbolType::Constructor
                && definition
                    .sort_graph
                    .check_subsort(&symbol.result_sort, &configuration_variable.sort)
                    .unwrap_or(false)
        })
        .collect::<Vec<_>>();
    let exact = candidates
        .iter()
        .filter(|symbol| symbol.result_sort == configuration_variable.sort)
        .cloned()
        .collect::<Vec<_>>();
    if !exact.is_empty() {
        candidates = exact;
    }
    let [candidate] = candidates.as_slice() else {
        return None;
    };

    let mut names_to_avoid = pattern_variable_names(state)
        .into_iter()
        .chain(
            substitution
                .values()
                .flat_map(|term| term.attributes().variables.iter())
                .map(|variable| variable.name.clone()),
        )
        .collect::<BTreeSet<_>>();
    let arguments = candidate
        .argument_sorts
        .iter()
        .enumerate()
        .map(|(index, sort)| {
            fresh_variable(
                &Variable::new(format!("Overload{index}"), sort.clone())
                    .with_provenance(VariableProvenance::Existential),
                &mut names_to_avoid,
                fresh_counter,
            )
        })
        .collect::<Vec<_>>();
    let candidate_term = Term::application(candidate.clone(), Vec::new(), arguments);
    let configuration_value = if candidate.result_sort == configuration_variable.sort {
        candidate_term.clone()
    } else {
        Term::injection(
            candidate.result_sort.clone(),
            configuration_variable.sort.clone(),
            candidate_term.clone(),
        )
    };
    let lifted = if candidate.result_sort == *target {
        candidate_term
    } else {
        Term::injection(
            candidate.result_sort.clone(),
            target.clone(),
            candidate_term,
        )
    };
    let found = match match_terms_in_definition(MatchMode::Rewrite, definition, &rule_term, &lifted)
    {
        MatchResult::Success(found) => found,
        MatchResult::Failed(_) | MatchResult::Indeterminate { .. } => return None,
    };
    Some((
        compose(&found, &substitution),
        vec![Predicate::Equals(
            Term::variable(configuration_variable.clone()),
            configuration_value,
        )],
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn set_variables_are_not_functional_patterns() {
        let sort = Sort::simple("SortS");
        let element = Term::variable(Variable::new("X", sort.clone()));
        let set = Term::variable(Variable::set("Y", sort.clone()));
        let pair = |left: Term, right: Term| {
            Term::application(
                Arc::new(Symbol::constructor(
                    "pair",
                    vec![sort.clone(), sort.clone()],
                    sort.clone(),
                )),
                Vec::new(),
                vec![left, right],
            )
        };

        assert!(is_functional_pattern(&element));
        assert!(is_functional_pattern(&pair(
            element.clone(),
            element.clone()
        )));
        assert!(!is_functional_pattern(&set));
        assert!(!is_functional_pattern(&pair(element, set)));
    }
}
