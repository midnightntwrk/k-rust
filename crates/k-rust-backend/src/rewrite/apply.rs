//! One-rule conditional rewriting step (Booster applyRule with a Kore-style unification
//! fallback): match, recovery ladder, condition simplification, definedness, SAT narrowing,
//! requires, validity, applicability, RHS instantiation, the thirteen phases P1 to P13 of
//! `apply_rule_with_match`. Cost: one matching problem per attempt; on an indeterminate match up
//! to eleven recovery strategies, each re-entering once per split with an empty or strictly
//! shorter remainder (recursion depth <= |remainder| + 1); up to three SMT calls per attempt.
//! `Counter::RewriteRuleAttempts`, `Counter::RewriteMatchFailures`, `Counter::SmtQueries`
//! (row B9); O(c) attempts per step for the c candidates the step hands over.

use std::{collections::BTreeSet, sync::Arc};

use k_rust_kore::measure::{self, Counter};

use crate::{
    builtin::BuiltinEffect,
    definedness::ceil_term,
    definition::BackendDefinition,
    ite::SplitSide,
    matching::{MatchMode, MatchResult, match_terms_in_definition},
    rule::{Predicate, RewriteRule, RuleRhs},
    simplify::{
        ConditionIndeterminacy, RuleCondition, SimplificationOptions,
        binds_element_variable_to_set_pattern, decide_condition, simplify_in_execution_with_solver,
        simplify_predicates_with_solver, simplify_with_solver,
    },
    smt::{Satisfiability, SmtError, SmtSolver, Validity},
    substitution::{Substitution, compose, extract_substitution, substitute},
    term::{Sort, Symbol, Term, TermKind, Variable},
    transition::ExecutionIoState,
};

use super::{
    AppliedRule, GeneralUnificationRecovery, IndeterminateReason, Pattern, TrivialApplication,
    Truth, collection_unification_definedness, conjunctively_contains_alpha_equivalent,
    extend_unique, freshen_existentials, freshen_unbound_rule_variables, predicates_truth,
    quantify_introduced_variables, recover_boolean_matches, recover_equality_matches,
    recover_function_equality_match, recover_functional_symbolic_match,
    recover_general_unification, recover_indeterminate_match, recover_ite_matches,
    recover_map_not_in_keys_matches, recover_overload_symbolic_match,
    recover_symbolic_map_key_matches, solve_collection_remainders_with_narrowing,
    substitute_predicates,
};

pub(super) enum RuleAttempt {
    NotApplicable,
    /// The rule unified in at least one sub-case, including results that simplify to bottom.
    Unified {
        groups: Vec<RuleApplicationGroup>,
    },
    Indeterminate(IndeterminateReason),
}

pub(super) struct RuleApplicationGroup {
    pub(super) applied: Vec<RuleApplication>,
    pub(super) trivial: Vec<TrivialApplication>,
}

pub(super) struct RuleApplication {
    pub(super) applied: AppliedRule,
    pub(super) remainder: Predicate,
}

fn remainder_of(applicability: &Predicate) -> Predicate {
    if *applicability == Predicate::True {
        Predicate::False
    } else {
        Predicate::Not(Box::new(applicability.clone()))
    }
}

fn trivial_application(
    rule: &RewriteRule,
    applicability: &Predicate,
    obligation: Predicate,
    effects: Vec<BuiltinEffect>,
) -> TrivialApplication {
    TrivialApplication {
        rule_id: rule.attributes.unique_id.clone(),
        label: rule.attributes.label.clone(),
        obligation,
        applicability: applicability.clone(),
        remainder: remainder_of(applicability),
        effects,
    }
}

fn conjunction(predicates: &[Predicate]) -> Predicate {
    match predicates {
        [] => Predicate::True,
        [predicate] => predicate.clone(),
        predicates => Predicate::And(predicates.to_vec()),
    }
}

pub(super) struct PartialRuleMatch {
    pub(super) substitution: Substitution,
    pub(super) conditions: Vec<Predicate>,
    pub(super) remainder: Vec<(Term, Term)>,
}

pub(super) struct EqualitySplit {
    pub(super) side: SplitSide,
    pub(super) value: bool,
    pub(super) left: Term,
    pub(super) right: Term,
}

pub(super) struct BooleanSplit {
    pub(super) side: SplitSide,
    pub(super) expected: bool,
    pub(super) operands: Vec<Term>,
}

pub(super) struct MapNotInKeysSplit {
    pub(super) side: SplitSide,
    pub(super) symbol: Arc<Symbol>,
    pub(super) sort_arguments: Vec<Sort>,
    pub(super) key: Term,
    pub(super) map: Term,
}

pub(super) fn apply_rule(
    definition: &BackendDefinition,
    rule: &RewriteRule,
    pattern: &Pattern,
    fresh_counter: &mut u64,
    simplification_options: SimplificationOptions,
    solver: &dyn SmtSolver,
    assume_initial_defined: bool,
    io: Option<&ExecutionIoState>,
) -> RuleAttempt {
    apply_rule_with_match(
        definition,
        rule,
        pattern,
        fresh_counter,
        simplification_options,
        solver,
        assume_initial_defined,
        None,
        io,
    )
}

/// Invariant: every re-entry (the six recovery splits, the unification solutions, and the
/// bindings extracted from conditions) carries the accumulated `inherited_conditions`, which
/// only grow, and either an empty or strictly shorter `remainder` or a binding of a previously
/// unbound `lhs` variable, so the recursion depth is at most |remainder| + 1 and the
/// constructor-like re-entry cannot repeat.
#[allow(clippy::too_many_arguments)]
pub(super) fn apply_rule_with_match(
    definition: &BackendDefinition,
    rule: &RewriteRule,
    pattern: &Pattern,
    fresh_counter: &mut u64,
    simplification_options: SimplificationOptions,
    solver: &dyn SmtSolver,
    assume_initial_defined: bool,
    matched: Option<PartialRuleMatch>,
    io: Option<&ExecutionIoState>,
) -> RuleAttempt {
    measure::bump(Counter::RewriteRuleAttempts);
    let (matching, mut inherited_conditions) = if let Some(matched) = matched {
        let matching = if matched.remainder.is_empty() {
            MatchResult::Success(matched.substitution)
        } else {
            MatchResult::Indeterminate {
                substitution: matched.substitution,
                remainder: matched.remainder,
            }
        };
        (matching, matched.conditions)
    } else {
        (
            match_terms_in_definition(MatchMode::Rewrite, definition, &rule.lhs, &pattern.term),
            Vec::new(),
        )
    };
    let mut path_knowledge = pattern.constraints.clone();
    if assume_initial_defined {
        extend_unique(&mut path_knowledge, ceil_term(definition, &pattern.term));
    }
    let mut inherited_knowledge = path_knowledge.clone();
    extend_unique(
        &mut inherited_knowledge,
        inherited_conditions.iter().cloned(),
    );
    let (mut substitution, mut match_conditions) = match matching {
        MatchResult::Failed(_) => {
            measure::bump(Counter::RewriteMatchFailures);
            return RuleAttempt::NotApplicable;
        }
        MatchResult::Indeterminate {
            substitution,
            remainder,
        } => {
            let recovered = match recover_indeterminate_match(
                definition,
                substitution,
                remainder,
                &inherited_knowledge,
                simplification_options,
                solver,
            ) {
                Ok(recovered) => recovered,
                Err(error) => {
                    return RuleAttempt::Indeterminate(IndeterminateReason::simplification(
                        Some(&rule.attributes.unique_id),
                        error,
                    ));
                }
            };
            extend_unique(
                &mut inherited_conditions,
                recovered.conditions.iter().cloned(),
            );
            extend_unique(&mut inherited_knowledge, recovered.conditions);
            match recovered.result {
                MatchResult::Failed(_) => {
                    measure::bump(Counter::RewriteMatchFailures);
                    return RuleAttempt::NotApplicable;
                }
                MatchResult::Success(substitution) => (substitution, Vec::new()),
                MatchResult::Indeterminate {
                    substitution,
                    remainder,
                } => {
                    if let Some(matches) =
                        recover_boolean_matches(definition, substitution.clone(), &remainder)
                    {
                        return combine_rule_attempts(matches.into_iter().map(|mut matched| {
                            let mut conditions = inherited_conditions.clone();
                            conditions.append(&mut matched.conditions);
                            matched.conditions = conditions;
                            apply_rule_with_match(
                                definition,
                                rule,
                                pattern,
                                fresh_counter,
                                simplification_options,
                                solver,
                                assume_initial_defined,
                                Some(matched),
                                io,
                            )
                        }));
                    }
                    if let Some(matches) = recover_symbolic_map_key_matches(
                        definition,
                        substitution.clone(),
                        &remainder,
                    ) {
                        return combine_rule_attempts(matches.into_iter().map(|mut matched| {
                            let mut conditions = inherited_conditions.clone();
                            conditions.append(&mut matched.conditions);
                            matched.conditions = conditions;
                            apply_rule_with_match(
                                definition,
                                rule,
                                pattern,
                                fresh_counter,
                                simplification_options,
                                solver,
                                assume_initial_defined,
                                Some(matched),
                                io,
                            )
                        }));
                    }
                    if let Some(matches) = recover_map_not_in_keys_matches(
                        definition,
                        rule,
                        pattern,
                        substitution.clone(),
                        &remainder,
                        fresh_counter,
                    ) {
                        return combine_rule_attempts(matches.into_iter().map(|mut matched| {
                            let mut conditions = inherited_conditions.clone();
                            conditions.append(&mut matched.conditions);
                            matched.conditions = conditions;
                            apply_rule_with_match(
                                definition,
                                rule,
                                pattern,
                                fresh_counter,
                                simplification_options,
                                solver,
                                assume_initial_defined,
                                Some(matched),
                                io,
                            )
                        }));
                    }
                    if let Some(matches) = recover_equality_matches(
                        definition,
                        rule,
                        pattern,
                        substitution.clone(),
                        &remainder,
                        fresh_counter,
                    ) {
                        return combine_rule_attempts(matches.into_iter().map(|mut matched| {
                            let mut conditions = inherited_conditions.clone();
                            conditions.append(&mut matched.conditions);
                            matched.conditions = conditions;
                            apply_rule_with_match(
                                definition,
                                rule,
                                pattern,
                                fresh_counter,
                                simplification_options,
                                solver,
                                assume_initial_defined,
                                Some(matched),
                                io,
                            )
                        }));
                    }
                    if let Some(matches) =
                        recover_ite_matches(definition, substitution.clone(), &remainder)
                    {
                        return combine_rule_attempts(matches.into_iter().map(|mut matched| {
                            let mut conditions = inherited_conditions.clone();
                            conditions.append(&mut matched.conditions);
                            matched.conditions = conditions;
                            apply_rule_with_match(
                                definition,
                                rule,
                                pattern,
                                fresh_counter,
                                simplification_options,
                                solver,
                                assume_initial_defined,
                                Some(matched),
                                io,
                            )
                        }));
                    }
                    if let Some(matches) = solve_collection_remainders_with_narrowing(
                        definition,
                        pattern,
                        substitution.clone(),
                        &remainder,
                        fresh_counter,
                    ) {
                        if matches.is_empty() {
                            return RuleAttempt::NotApplicable;
                        }
                        return combine_rule_attempts(matches.into_iter().map(|solution| {
                            let (substitution, _) = freshen_unbound_rule_variables(
                                rule,
                                pattern,
                                solution.substitution,
                                fresh_counter,
                            );
                            let mut conditions = inherited_conditions.clone();
                            extend_unique(
                                &mut conditions,
                                substitute_predicates(&solution.constraints, &substitution),
                            );
                            extend_unique(
                                &mut conditions,
                                collection_unification_definedness(
                                    definition,
                                    &remainder,
                                    &substitution,
                                ),
                            );
                            apply_rule_with_match(
                                definition,
                                rule,
                                pattern,
                                fresh_counter,
                                simplification_options,
                                solver,
                                assume_initial_defined,
                                Some(PartialRuleMatch {
                                    substitution,
                                    conditions,
                                    remainder: Vec::new(),
                                }),
                                io,
                            )
                        }));
                    }
                    if let Some(recovered) = recover_overload_symbolic_match(
                        definition,
                        pattern,
                        substitution.clone(),
                        &remainder,
                        fresh_counter,
                    ) {
                        recovered
                    } else {
                        match recover_general_unification(
                            definition,
                            rule,
                            pattern,
                            substitution.clone(),
                            &remainder,
                            fresh_counter,
                        ) {
                            GeneralUnificationRecovery::Unified(mut solutions) => {
                                if solutions.len() == 1 {
                                    solutions.pop().expect("one unification solution")
                                } else {
                                    return combine_rule_attempts(solutions.into_iter().map(
                                        |(substitution, mut constraints)| {
                                            let mut conditions = inherited_conditions.clone();
                                            conditions.append(&mut constraints);
                                            apply_rule_with_match(
                                                definition,
                                                rule,
                                                pattern,
                                                fresh_counter,
                                                simplification_options,
                                                solver,
                                                assume_initial_defined,
                                                Some(PartialRuleMatch {
                                                    substitution,
                                                    conditions,
                                                    remainder: Vec::new(),
                                                }),
                                                io,
                                            )
                                        },
                                    ));
                                }
                            }
                            GeneralUnificationRecovery::Bottom => {
                                return RuleAttempt::NotApplicable;
                            }
                            GeneralUnificationRecovery::Unsupported => {
                                if let Some(recovered) = recover_functional_symbolic_match(
                                    definition,
                                    rule,
                                    pattern,
                                    substitution.clone(),
                                    &remainder,
                                    fresh_counter,
                                ) {
                                    recovered
                                } else if let Some(recovered) = recover_function_equality_match(
                                    rule,
                                    pattern,
                                    substitution.clone(),
                                    &remainder,
                                    fresh_counter,
                                ) {
                                    recovered
                                } else {
                                    let requires =
                                        substitute_predicates(&rule.requires, &substitution);
                                    let requires = match simplify_predicates_with_solver(
                                        definition,
                                        &requires,
                                        &inherited_knowledge,
                                        simplification_options,
                                        solver,
                                    ) {
                                        Ok(requires) => requires,
                                        Err(error) => {
                                            return RuleAttempt::Indeterminate(
                                                IndeterminateReason::simplification(
                                                    Some(&rule.attributes.unique_id),
                                                    error,
                                                ),
                                            );
                                        }
                                    };
                                    if predicates_truth(&requires) == Truth::False {
                                        return RuleAttempt::NotApplicable;
                                    }
                                    let unclear = requires
                                        .into_iter()
                                        .filter(|predicate| {
                                            predicates_truth(std::slice::from_ref(predicate))
                                                == Truth::Unknown
                                                && !inherited_knowledge.contains(predicate)
                                        })
                                        .collect::<Vec<_>>();
                                    if !unclear.is_empty()
                                        && matches!(
                                            solver.check_predicates(
                                                &inherited_knowledge,
                                                &Substitution::new(),
                                                &unclear,
                                            ),
                                            Ok(Validity::Invalid)
                                        )
                                    {
                                        return RuleAttempt::NotApplicable;
                                    }
                                    return RuleAttempt::Indeterminate(
                                        IndeterminateReason::Match {
                                            rule_id: rule.attributes.unique_id.clone(),
                                            substitution,
                                            remainder,
                                        },
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
        MatchResult::Success(substitution) => (substitution, Vec::new()),
    };
    // A rule over an element variable `I` is an axiom for every element; instantiating it at a
    // pattern that contains a set variable is justified only when the rule is linear in `I`
    // (`simplify::binds_element_variable_to_set_pattern`). The attempt stays indeterminate so
    // that no lower-priority rule fires in its place.
    if binds_element_variable_to_set_pattern(&substitution) {
        return RuleAttempt::Indeterminate(IndeterminateReason::Match {
            rule_id: rule.attributes.unique_id.clone(),
            substitution,
            remainder: Vec::new(),
        });
    }
    let configuration_bindings = substitution
        .iter()
        .filter(|(variable, _)| !rule.lhs.attributes().variables.contains(*variable))
        .map(|(variable, value)| {
            (
                variable.clone(),
                value.clone(),
                Predicate::Equals(Term::variable(variable.clone()), value.clone()),
            )
        })
        .collect::<Vec<_>>();
    for (variable, value, condition) in configuration_bindings {
        substitution.remove(&variable);
        if !match_conditions.contains(&condition) {
            match_conditions.push(condition);
        }
        extend_unique(&mut match_conditions, ceil_term(definition, &value));
    }
    inherited_conditions.append(&mut match_conditions);
    let inherited_conditions = match simplify_predicates_with_solver(
        definition,
        &inherited_conditions,
        &path_knowledge,
        simplification_options,
        solver,
    ) {
        Ok(conditions) => conditions,
        Err(error) => {
            return RuleAttempt::Indeterminate(IndeterminateReason::simplification(
                Some(&rule.attributes.unique_id),
                error,
            ));
        }
    };
    if predicates_truth(&inherited_conditions) == Truth::False {
        return RuleAttempt::NotApplicable;
    }
    let mut match_conditions = inherited_conditions
        .into_iter()
        .filter(|condition| predicates_truth(std::slice::from_ref(condition)) == Truth::Unknown)
        .collect::<Vec<_>>();

    let mut definedness_conditions = Vec::new();
    for value in substitution
        .values()
        .filter(|value| !matches!(value.kind(), TermKind::Variable(_)))
    {
        extend_unique(&mut definedness_conditions, ceil_term(definition, value));
    }
    let mut definedness_knowledge = path_knowledge.clone();
    extend_unique(&mut definedness_knowledge, match_conditions.iter().cloned());
    let definedness_conditions = match simplify_predicates_with_solver(
        definition,
        &definedness_conditions,
        &definedness_knowledge,
        simplification_options,
        solver,
    ) {
        Ok(conditions) => conditions,
        Err(error) => {
            return RuleAttempt::Indeterminate(IndeterminateReason::simplification(
                Some(&rule.attributes.unique_id),
                error,
            ));
        }
    };
    if predicates_truth(&definedness_conditions) == Truth::False {
        let applicability = quantify_introduced_variables(pattern, match_conditions);
        return RuleAttempt::Unified {
            groups: vec![RuleApplicationGroup {
                applied: Vec::new(),
                trivial: vec![trivial_application(
                    rule,
                    &applicability,
                    Predicate::False,
                    Vec::new(),
                )],
            }],
        };
    }
    extend_unique(
        &mut match_conditions,
        definedness_conditions.into_iter().filter(|condition| {
            predicates_truth(std::slice::from_ref(condition)) == Truth::Unknown
        }),
    );

    if !match_conditions.is_empty() {
        let mut narrowed = pattern.constraints.clone();
        extend_unique(&mut narrowed, match_conditions.iter().cloned());
        match solver.is_sat(&narrowed, &Substitution::new()) {
            Ok(Satisfiability::Sat) => {}
            Ok(Satisfiability::Unsat) => return RuleAttempt::NotApplicable,
            Ok(Satisfiability::Unknown(reason)) => {
                return RuleAttempt::Indeterminate(IndeterminateReason::Smt {
                    rule_id: rule.attributes.unique_id.clone(),
                    error: SmtError::Unknown(reason),
                });
            }
            Err(error) => {
                return RuleAttempt::Indeterminate(IndeterminateReason::Smt {
                    rule_id: rule.attributes.unique_id.clone(),
                    error,
                });
            }
        }
    }

    let requires = substitute_predicates(&rule.requires, &substitution);
    let mut match_knowledge = path_knowledge;
    extend_unique(&mut match_knowledge, match_conditions.iter().cloned());
    let requires = match simplify_predicates_with_solver(
        definition,
        &requires,
        &match_knowledge,
        simplification_options,
        solver,
    ) {
        Ok(requires) => requires,
        Err(error) => {
            return RuleAttempt::Indeterminate(IndeterminateReason::simplification(
                Some(&rule.attributes.unique_id),
                error,
            ));
        }
    };
    if predicates_truth(&requires) == Truth::False {
        return RuleAttempt::NotApplicable;
    }
    if pattern.term.concrete_after_normalization() {
        // Conditions can finish an otherwise incomplete match (for example, requires E = value).
        // Re-enter application with those bindings so the remaining functional equalities and
        // requires are simplified under the covering substitution before coverage is checked.
        let mut conditions = match_conditions.clone();
        extend_unique(&mut conditions, requires.iter().cloned());
        let (bindings, _) = extract_substitution(&conditions, &definition.sort_graph);
        let bindings = bindings
            .into_iter()
            .filter(|(variable, _)| {
                rule.lhs.attributes().variables.contains(variable)
                    && !substitution.contains_key(variable)
            })
            .collect::<Substitution>();
        if !bindings.is_empty() {
            return apply_rule_with_match(
                definition,
                rule,
                pattern,
                fresh_counter,
                simplification_options,
                solver,
                assume_initial_defined,
                Some(PartialRuleMatch {
                    substitution: compose(&bindings, &substitution),
                    conditions: substitute_predicates(&conditions, &bindings),
                    remainder: Vec::new(),
                }),
                io,
            );
        }
    }
    let mut unclear_requires = requires
        .into_iter()
        .filter(|predicate| {
            predicates_truth(std::slice::from_ref(predicate)) == Truth::Unknown
                && !pattern.constraints.contains(predicate)
        })
        .collect::<Vec<_>>();
    if !unclear_requires.is_empty() {
        match decide_condition(&unclear_requires, &match_knowledge, solver) {
            Ok(RuleCondition::Satisfied) => unclear_requires.clear(),
            Ok(RuleCondition::Refuted) => return RuleAttempt::NotApplicable,
            // `NonFunctionalBinding` is raised at a binding site, never by `decide_condition`;
            // it is listed for exhaustiveness and would be carried like an open implication.
            Ok(RuleCondition::Indeterminate(
                ConditionIndeterminacy::ImplicationIndeterminate
                | ConditionIndeterminacy::NonFunctionalBinding,
            )) => {}
            Ok(RuleCondition::Indeterminate(ConditionIndeterminacy::NoSolver)) => {
                return RuleAttempt::Indeterminate(IndeterminateReason::Requires {
                    rule_id: rule.attributes.unique_id.clone(),
                    predicates: unclear_requires,
                });
            }
            Ok(RuleCondition::Indeterminate(ConditionIndeterminacy::InconsistentPathCondition)) => {
                return RuleAttempt::Indeterminate(IndeterminateReason::Smt {
                    rule_id: rule.attributes.unique_id.clone(),
                    error: SmtError::InconsistentGroundTruth,
                });
            }
            Ok(RuleCondition::Indeterminate(ConditionIndeterminacy::SmtUnknown(reason))) => {
                return RuleAttempt::Indeterminate(IndeterminateReason::Smt {
                    rule_id: rule.attributes.unique_id.clone(),
                    error: SmtError::Unknown(reason),
                });
            }
            Ok(RuleCondition::Indeterminate(ConditionIndeterminacy::Untranslatable(error))) => {
                return RuleAttempt::Indeterminate(IndeterminateReason::Smt {
                    rule_id: rule.attributes.unique_id.clone(),
                    error: SmtError::Translation(error),
                });
            }
            Err(error) => {
                return RuleAttempt::Indeterminate(IndeterminateReason::Smt {
                    rule_id: rule.attributes.unique_id.clone(),
                    error,
                });
            }
        }
    }

    let mut applicability = match_conditions.clone();
    applicability.extend(unclear_requires.iter().cloned());
    let applicability = quantify_introduced_variables(pattern, applicability);
    if applicability != Predicate::True
        && conjunctively_contains_alpha_equivalent(
            &pattern.constraints,
            &Predicate::Not(Box::new(applicability.clone())),
        )
    {
        return RuleAttempt::NotApplicable;
    }

    if pattern.term.concrete_after_normalization() {
        let missing_variables = rule
            .lhs
            .attributes()
            .variables
            .iter()
            .filter(|variable| !substitution.contains_key(*variable))
            .cloned()
            .collect::<BTreeSet<_>>();
        if !missing_variables.is_empty() {
            return RuleAttempt::Indeterminate(IndeterminateReason::Instantiation {
                rule_id: rule.attributes.unique_id.clone(),
                missing_variables,
            });
        }
    }

    let existential_substitution = freshen_existentials(rule, pattern);
    let mut condition_knowledge = match_knowledge;
    extend_unique(&mut condition_knowledge, unclear_requires.iter().cloned());
    let alternatives = match &rule.rhs {
        RuleRhs::Term(rhs) => vec![(rhs, rule.ensures.as_slice())],
        RuleRhs::Disjunction(alternatives) => alternatives
            .iter()
            .map(|alternative| (&alternative.term, alternative.ensures.as_slice()))
            .collect(),
        RuleRhs::Top => return RuleAttempt::NotApplicable,
        RuleRhs::Bottom => {
            return RuleAttempt::Unified {
                groups: vec![RuleApplicationGroup {
                    applied: Vec::new(),
                    trivial: vec![trivial_application(
                        rule,
                        &applicability,
                        Predicate::False,
                        Vec::new(),
                    )],
                }],
            };
        }
        RuleRhs::Predicates(_) => return RuleAttempt::NotApplicable,
    };
    let mut applications = Vec::new();
    let mut trivial = Vec::new();
    for (rhs, alternative_ensures) in alternatives {
        let mut ensures = rule.ensures.clone();
        extend_unique(&mut ensures, alternative_ensures.iter().cloned());
        match apply_rhs_alternative(
            definition,
            rule,
            pattern,
            rhs,
            &ensures,
            &substitution,
            &existential_substitution,
            &condition_knowledge,
            &match_conditions,
            &unclear_requires,
            &applicability,
            simplification_options,
            solver,
            io,
        ) {
            RhsAlternativeAttempt::Applied(application) => applications.push(application),
            RhsAlternativeAttempt::Trivial {
                obligation,
                effects,
            } => {
                trivial.push(trivial_application(
                    rule,
                    &applicability,
                    obligation,
                    effects,
                ));
            }
            RhsAlternativeAttempt::Indeterminate(reason) => {
                return RuleAttempt::Indeterminate(reason);
            }
        }
    }
    RuleAttempt::Unified {
        groups: vec![RuleApplicationGroup {
            applied: applications,
            trivial,
        }],
    }
}

enum RhsAlternativeAttempt {
    Applied(RuleApplication),
    Trivial {
        obligation: Predicate,
        effects: Vec<BuiltinEffect>,
    },
    Indeterminate(IndeterminateReason),
}

/// The step's verdict on the definedness obligations of a rule instance's right-hand side.
enum ObligationVerdict {
    /// The obligations hold under the rule instance's knowledge.
    Discharged,
    /// The rule instance is empty: the step is trivial on the pre-step pattern.
    Trivial,
    /// The obligations are open and become constraints of the successor.
    Carried,
}

/// Map `decide_condition` on the RHS obligations to the step's verdict. The obligations are
/// decided under the rule instance's knowledge (path condition, match conditions, unclear
/// `requires`, and RHS constraints), so an inconsistent ground truth means the instance is
/// empty, as a refutation does. Every other undecided verdict, a solver failure included,
/// carries the obligations: `\ceil` of the successor is a conjunct of the successor by
/// definition. No diagnostic is emitted, as none was before.
fn rhs_obligation_verdict(condition: Result<RuleCondition, SmtError>) -> ObligationVerdict {
    match condition {
        Ok(RuleCondition::Satisfied) => ObligationVerdict::Discharged,
        Ok(
            RuleCondition::Refuted
            | RuleCondition::Indeterminate(ConditionIndeterminacy::InconsistentPathCondition),
        ) => ObligationVerdict::Trivial,
        Ok(RuleCondition::Indeterminate(_)) | Err(_) => ObligationVerdict::Carried,
    }
}

/// The step's verdict on the `ensures` of a rule instance.
enum EnsuresStepVerdict {
    /// The `ensures` holds under the rule instance's knowledge and is dropped.
    Cleared,
    /// The rule instance is empty: the step is trivial on the pre-step pattern.
    Trivial,
    /// The `ensures` is open and stays a constraint of the successor.
    Carried,
    /// The solver was asked and did not answer, or could not pose the query: the step is an
    /// `IndeterminateReason::Smt` leaf naming the error.
    Indeterminate(SmtError),
}

/// Map `decide_condition` on the `ensures` to the step's verdict. As for the RHS obligations,
/// an inconsistent ground truth under the rule instance's knowledge means the instance is
/// empty. An open implication or a missing solver carries the `ensures`; a solver that did
/// not answer, could not pose the query, or failed makes the step indeterminate. No
/// diagnostic is emitted, as none was before.
fn rhs_ensures_verdict(condition: Result<RuleCondition, SmtError>) -> EnsuresStepVerdict {
    match condition {
        Ok(RuleCondition::Satisfied) => EnsuresStepVerdict::Cleared,
        Ok(
            RuleCondition::Refuted
            | RuleCondition::Indeterminate(ConditionIndeterminacy::InconsistentPathCondition),
        ) => EnsuresStepVerdict::Trivial,
        // `NonFunctionalBinding` is raised at a binding site, never by `decide_condition`; it
        // is listed for exhaustiveness and would be carried like an open implication.
        Ok(RuleCondition::Indeterminate(
            ConditionIndeterminacy::ImplicationIndeterminate
            | ConditionIndeterminacy::NoSolver
            | ConditionIndeterminacy::NonFunctionalBinding,
        )) => EnsuresStepVerdict::Carried,
        Ok(RuleCondition::Indeterminate(ConditionIndeterminacy::SmtUnknown(reason))) => {
            EnsuresStepVerdict::Indeterminate(SmtError::Unknown(reason))
        }
        Ok(RuleCondition::Indeterminate(ConditionIndeterminacy::Untranslatable(error))) => {
            EnsuresStepVerdict::Indeterminate(SmtError::Translation(error))
        }
        Err(error) => EnsuresStepVerdict::Indeterminate(error),
    }
}

#[allow(clippy::too_many_arguments)]
fn apply_rhs_alternative(
    definition: &BackendDefinition,
    rule: &RewriteRule,
    pattern: &Pattern,
    rhs: &Term,
    ensures: &[Predicate],
    substitution: &Substitution,
    existential_substitution: &Substitution,
    condition_knowledge: &[Predicate],
    match_conditions: &[Predicate],
    unclear_requires: &[Predicate],
    applicability: &Predicate,
    simplification_options: SimplificationOptions,
    solver: &dyn SmtSolver,
    io: Option<&ExecutionIoState>,
) -> RhsAlternativeAttempt {
    let rhs = substitute(&substitute(rhs, substitution), existential_substitution);
    let io = io.filter(|_| {
        pattern.constraints.is_empty()
            && rhs.attributes().variables.is_empty()
            && condition_knowledge.is_empty()
            && match_conditions.is_empty()
            && unclear_requires.is_empty()
    });
    let mut condition_knowledge = condition_knowledge.to_vec();
    let mut io_evaluation = io.map(ExecutionIoState::begin_evaluation);
    let (rhs, mut rhs_constraints, effects, undefined_term) =
        if rule.computed_attributes.undefined_symbols.is_empty() && io_evaluation.is_none() {
            (rhs, Vec::new(), Vec::new(), None)
        } else {
            let simplified = match io_evaluation.as_mut() {
                Some(execution) => simplify_in_execution_with_solver(
                    definition,
                    &rhs,
                    &condition_knowledge,
                    simplification_options,
                    solver,
                    execution,
                ),
                None => simplify_with_solver(
                    definition,
                    &rhs,
                    &condition_knowledge,
                    simplification_options,
                    solver,
                ),
            };
            match simplified {
                Ok(simplified) => (
                    simplified.term,
                    simplified.constraints,
                    simplified.effects,
                    simplified.undefined_term,
                ),
                Err(error) => {
                    return RhsAlternativeAttempt::Indeterminate(
                        IndeterminateReason::simplification(
                            Some(&rule.attributes.unique_id),
                            error,
                        ),
                    );
                }
            }
        };
    if let Some(term) = undefined_term.clone() {
        return RhsAlternativeAttempt::Trivial {
            obligation: Predicate::Ceil(term),
            effects,
        };
    }
    if predicates_truth(&rhs_constraints) == Truth::False {
        return RhsAlternativeAttempt::Trivial {
            obligation: conjunction(&rhs_constraints),
            effects,
        };
    }
    extend_unique(&mut condition_knowledge, rhs_constraints.iter().cloned());
    if !rule.computed_attributes.undefined_symbols.is_empty() {
        let obligations = ceil_term(definition, &rhs);
        let reported_obligation = undefined_term
            .map(Predicate::Ceil)
            .unwrap_or_else(|| conjunction(&obligations));
        let obligations = match simplify_predicates_with_solver(
            definition,
            &obligations,
            &condition_knowledge,
            simplification_options,
            solver,
        ) {
            Ok(obligations) => obligations,
            Err(error) => {
                return RhsAlternativeAttempt::Indeterminate(IndeterminateReason::simplification(
                    Some(&rule.attributes.unique_id),
                    error,
                ));
            }
        };
        match rhs_obligation_verdict(decide_condition(&obligations, &condition_knowledge, solver)) {
            ObligationVerdict::Discharged => {}
            ObligationVerdict::Trivial => {
                return RhsAlternativeAttempt::Trivial {
                    obligation: reported_obligation,
                    effects,
                };
            }
            ObligationVerdict::Carried => extend_unique(&mut rhs_constraints, obligations),
        }
    }
    let ensures = substitute_predicates(
        &substitute_predicates(ensures, substitution),
        existential_substitution,
    );
    let reported_ensures = conjunction(&ensures);
    let mut ensures = match simplify_predicates_with_solver(
        definition,
        &ensures,
        &condition_knowledge,
        simplification_options,
        solver,
    ) {
        Ok(ensures) => ensures,
        Err(error) => {
            return RhsAlternativeAttempt::Indeterminate(IndeterminateReason::simplification(
                Some(&rule.attributes.unique_id),
                error,
            ));
        }
    };
    match rhs_ensures_verdict(decide_condition(&ensures, &condition_knowledge, solver)) {
        EnsuresStepVerdict::Cleared => ensures.clear(),
        EnsuresStepVerdict::Trivial => {
            return RhsAlternativeAttempt::Trivial {
                obligation: reported_ensures,
                effects,
            };
        }
        EnsuresStepVerdict::Carried => {}
        EnsuresStepVerdict::Indeterminate(error) => {
            return RhsAlternativeAttempt::Indeterminate(IndeterminateReason::Smt {
                rule_id: rule.attributes.unique_id.clone(),
                error,
            });
        }
    }
    let alias_variables = term_alias_variables(&rule.lhs);
    let rule_substitution = substitution
        .iter()
        .filter(|(variable, _)| !alias_variables.contains(*variable))
        .map(|(variable, value)| (variable.clone(), value.clone()))
        .collect();
    let mut rule_predicates = Vec::new();
    extend_unique(&mut rule_predicates, match_conditions.iter().cloned());
    extend_unique(&mut rule_predicates, unclear_requires.iter().cloned());
    extend_unique(&mut rule_predicates, rhs_constraints);
    extend_unique(&mut rule_predicates, ensures);
    let mut constraints = pattern.constraints.clone();
    extend_unique(&mut constraints, rule_predicates.iter().cloned());
    RhsAlternativeAttempt::Applied(RuleApplication {
        applied: AppliedRule {
            before: pattern.clone(),
            pattern: Pattern {
                term: rhs,
                constraints,
            },
            label: rule.attributes.label.clone(),
            unique_id: rule.attributes.unique_id.clone(),
            substitution: substitution.clone(),
            rule_substitution,
            rule_predicates,
            effects,
            io: io_evaluation.map(|execution| execution.commit()),
        },
        remainder: remainder_of(applicability),
    })
}

fn term_alias_variables(term: &Term) -> BTreeSet<Variable> {
    fn collect(term: &Term, output: &mut BTreeSet<Variable>) {
        match term.kind() {
            TermKind::And(left, right) => {
                if let TermKind::Variable(variable) = left.kind() {
                    output.insert(variable.clone());
                }
                if let TermKind::Variable(variable) = right.kind() {
                    output.insert(variable.clone());
                }
                collect(left, output);
                collect(right, output);
            }
            TermKind::Application { arguments, .. } => {
                for argument in arguments {
                    collect(argument, output);
                }
            }
            TermKind::Injection { term, .. } => collect(term, output),
            TermKind::Map { entries, rest, .. } => {
                for (key, value) in entries {
                    collect(key, output);
                    collect(value, output);
                }
                if let Some(rest) = rest {
                    collect(rest, output);
                }
            }
            TermKind::List { heads, rest, .. } => {
                for head in heads {
                    collect(head, output);
                }
                if let Some((middle, tails)) = rest {
                    collect(middle, output);
                    for tail in tails {
                        collect(tail, output);
                    }
                }
            }
            TermKind::Set { elements, rest, .. } => {
                for element in elements {
                    collect(element, output);
                }
                if let Some(rest) = rest {
                    collect(rest, output);
                }
            }
            TermKind::DomainValue { .. } | TermKind::Variable(_) => {}
        }
    }

    let mut variables = BTreeSet::new();
    collect(term, &mut variables);
    variables
}

fn combine_rule_attempts(attempts: impl IntoIterator<Item = RuleAttempt>) -> RuleAttempt {
    let mut groups = Vec::new();
    for attempt in attempts {
        match attempt {
            RuleAttempt::NotApplicable => {}
            RuleAttempt::Unified { groups: found } => groups.extend(found),
            RuleAttempt::Indeterminate(reason) => return RuleAttempt::Indeterminate(reason),
        }
    }
    if groups.is_empty() {
        RuleAttempt::NotApplicable
    } else {
        RuleAttempt::Unified { groups }
    }
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
                std::sync::Arc::new(Symbol::constructor(
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

    #[test]
    fn rule_diagnostics_omit_term_alias_binders() {
        let sort = Sort::simple("SortS");
        let alias = Variable::new("Rule#Alias", sort.clone());
        let ordinary = Variable::new("Rule#Ordinary", sort.clone());
        let lhs = Term::application(
            std::sync::Arc::new(Symbol::constructor(
                "pair",
                vec![sort.clone(), sort.clone()],
                sort.clone(),
            )),
            Vec::new(),
            vec![
                Term::and(
                    Term::domain_value(sort.clone(), "value"),
                    Term::variable(alias.clone()),
                ),
                Term::variable(ordinary.clone()),
            ],
        );

        assert_eq!(term_alias_variables(&lhs), BTreeSet::from([alias]));
        assert!(!term_alias_variables(&lhs).contains(&ordinary));
    }

    #[test]
    fn final_leaves_with_distinct_console_states_do_not_merge() {
        let definition = definition("");
        let cursor_zero = ExecutionIoState::new(Vec::from(&b"input"[..]));
        let mut cursor_evaluation = cursor_zero.begin_evaluation();
        assert_eq!(cursor_evaluation.read(1), b"i");
        let cursor_one = cursor_evaluation.commit();
        let mut left_evaluation = ExecutionIoState::default().begin_evaluation();
        left_evaluation.append("IO.write", 1, Vec::from(&b"left"[..]));
        let left_io = left_evaluation.commit();
        let mut right_evaluation = ExecutionIoState::default().begin_evaluation();
        right_evaluation.append("IO.write", 1, Vec::from(&b"right"[..]));
        let right_io = right_evaluation.commit();
        let leaf = |io| ExecutionLeaf {
            pattern: subject(&definition, "same"),
            depth: 1,
            trace: Vec::new(),
            branch: Vec::new(),
            observations: Vec::new(),
            effects: Vec::new(),
            io,
            halt_reason: HaltReason::Stuck,
        };

        let cursor_leaves = merge_equal_final_leaves(vec![leaf(cursor_zero), leaf(cursor_one)]);
        assert_eq!(cursor_leaves.len(), 2);

        let transcript_leaves = merge_equal_final_leaves(vec![leaf(left_io), leaf(right_io)]);

        assert_eq!(transcript_leaves.len(), 2);
        assert_eq!(
            transcript_leaves[0].io.transcript()[0].bytes.as_ref(),
            b"left"
        );
        assert_eq!(
            transcript_leaves[1].io.transcript()[0].bytes.as_ref(),
            b"right"
        );
    }
}
