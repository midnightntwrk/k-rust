//! Priority-aware rewrite steps over internalized backend theories.

use std::collections::{BTreeSet, VecDeque};

use crate::{
    definition::BackendDefinition,
    matching::{MatchMode, MatchResult, match_terms},
    rule::{Concreteness, ConstraintKind, Predicate, RewriteRule, RuleRhs, TermIndex, term_index},
    simplify::{
        SimplificationError, SimplificationOptions, simplify_predicates_with_solver,
        simplify_with_solver,
    },
    smt::{NoSolver, Satisfiability, SmtError, SmtSolver, Validity},
    substitution::{Substitution, compose, substitute},
    term::{Name, Sort, SymbolType, Term, TermKind, Variable},
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Pattern {
    pub term: Term,
    pub constraints: Vec<Predicate>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AppliedRule {
    pub pattern: Pattern,
    pub label: Option<String>,
    pub unique_id: String,
    pub substitution: Substitution,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RewriteResult {
    Stuck(Pattern),
    Trivial(Pattern),
    Finished(AppliedRule),
    Branch {
        original: Pattern,
        branches: Vec<AppliedRule>,
    },
    Indeterminate {
        pattern: Pattern,
        reason: IndeterminateReason,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum IndeterminateReason {
    Match {
        rule_id: String,
        substitution: Substitution,
        remainder: Vec<(Term, Term)>,
    },
    Requires {
        rule_id: String,
        predicates: Vec<Predicate>,
    },
    Concreteness {
        rule_id: String,
        variable: Variable,
    },
    Definedness {
        rule_id: String,
        symbols: Vec<Name>,
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ExecutionOptions {
    pub max_depth: u64,
    pub max_simplification_iterations: usize,
}

impl Default for ExecutionOptions {
    fn default() -> Self {
        Self {
            max_depth: 1_000,
            max_simplification_iterations: 100,
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
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum HaltReason {
    Stuck,
    Trivial,
    DepthBound,
    Indeterminate(IndeterminateReason),
    Simplification(SimplificationError),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExecutionLeaf {
    pub pattern: Pattern,
    pub depth: u64,
    pub trace: Vec<TraceEntry>,
    pub halt_reason: HaltReason,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExecutionResult {
    pub leaves: Vec<ExecutionLeaf>,
}

pub fn execute(
    definition: &BackendDefinition,
    initial: Pattern,
    options: ExecutionOptions,
) -> ExecutionResult {
    execute_with_solver(definition, initial, options, &NoSolver)
}

pub fn execute_with_solver(
    definition: &BackendDefinition,
    initial: Pattern,
    options: ExecutionOptions,
    solver: &dyn SmtSolver,
) -> ExecutionResult {
    let mut fresh_counter = 0;
    let mut pending = VecDeque::from([ExecutionState {
        pattern: initial,
        depth: 0,
        trace: Vec::new(),
    }]);
    let mut leaves = Vec::new();
    while let Some(mut state) = pending.pop_front() {
        match simplify_with_solver(
            definition,
            &state.pattern.term,
            &state.pattern.constraints,
            SimplificationOptions {
                max_iterations: options.max_simplification_iterations,
            },
            solver,
        ) {
            Ok(simplified) => {
                state.pattern.term = simplified.term;
                state.pattern.constraints.extend(simplified.constraints);
                state
                    .trace
                    .extend(
                        simplified
                            .applied_rules
                            .into_iter()
                            .map(|unique_id| TraceEntry {
                                depth: state.depth,
                                kind: TraceKind::Simplification,
                                label: None,
                                unique_id,
                            }),
                    );
            }
            Err(error) => {
                leaves.push(ExecutionLeaf {
                    pattern: state.pattern,
                    depth: state.depth,
                    trace: state.trace,
                    halt_reason: HaltReason::Simplification(error),
                });
                continue;
            }
        }
        if state.depth >= options.max_depth {
            leaves.push(ExecutionLeaf {
                pattern: state.pattern,
                depth: state.depth,
                trace: state.trace,
                halt_reason: HaltReason::DepthBound,
            });
            continue;
        }
        match rewrite_step_with_options(
            definition,
            &state.pattern,
            &mut fresh_counter,
            SimplificationOptions {
                max_iterations: options.max_simplification_iterations,
            },
            solver,
        ) {
            RewriteResult::Stuck(pattern) => leaves.push(ExecutionLeaf {
                pattern,
                depth: state.depth,
                trace: state.trace,
                halt_reason: HaltReason::Stuck,
            }),
            RewriteResult::Trivial(pattern) => leaves.push(ExecutionLeaf {
                pattern,
                depth: state.depth,
                trace: state.trace,
                halt_reason: HaltReason::Trivial,
            }),
            RewriteResult::Indeterminate { pattern, reason } => leaves.push(ExecutionLeaf {
                pattern,
                depth: state.depth,
                trace: state.trace,
                halt_reason: HaltReason::Indeterminate(reason),
            }),
            RewriteResult::Finished(applied) => {
                pending.push_back(next_state(state.depth, state.trace, applied))
            }
            RewriteResult::Branch { branches, .. } => {
                for applied in branches {
                    pending.push_back(next_state(state.depth, state.trace.clone(), applied));
                }
            }
        }
    }
    ExecutionResult { leaves }
}

fn next_state(depth: u64, mut trace: Vec<TraceEntry>, applied: AppliedRule) -> ExecutionState {
    trace.push(TraceEntry {
        depth: depth + 1,
        kind: TraceKind::Rewrite,
        label: applied.label,
        unique_id: applied.unique_id,
    });
    ExecutionState {
        pattern: applied.pattern,
        depth: depth + 1,
        trace,
    }
}

struct ExecutionState {
    pattern: Pattern,
    depth: u64,
    trace: Vec<TraceEntry>,
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

fn rewrite_step_with_options(
    definition: &BackendDefinition,
    pattern: &Pattern,
    fresh_counter: &mut u64,
    simplification_options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> RewriteResult {
    let index = term_index(&pattern.term);
    let priority_groups = applicable_groups(definition, &index);
    if priority_groups.is_empty() {
        return RewriteResult::Stuck(pattern.clone());
    }
    let mut saw_trivial = false;
    for rules in priority_groups.values() {
        let mut applied = Vec::new();
        for rule in rules {
            match apply_rule(
                definition,
                rule,
                pattern,
                fresh_counter,
                simplification_options,
                solver,
            ) {
                RuleAttempt::NotApplicable => {}
                RuleAttempt::Trivial => saw_trivial = true,
                RuleAttempt::Applied(result) => applied.push(result),
                RuleAttempt::Indeterminate(reason) => {
                    return RewriteResult::Indeterminate {
                        pattern: pattern.clone(),
                        reason,
                    };
                }
            }
        }
        let remainder = applied
            .iter()
            .map(|application| application.remainder.clone())
            .collect::<Vec<_>>();
        let remainder_result = if applied.is_empty() || predicates_truth(&remainder) == Truth::False
        {
            Ok(Satisfiability::Unsat)
        } else {
            let mut predicates = pattern.constraints.clone();
            predicates.extend(remainder.iter().cloned());
            solver.is_sat(&predicates, &Substitution::new())
        };
        if !matches!(remainder_result, Ok(Satisfiability::Unsat)) && !applied.is_empty() {
            return RewriteResult::Indeterminate {
                pattern: pattern.clone(),
                reason: IndeterminateReason::Remainder {
                    rule_ids: applied
                        .iter()
                        .map(|application| application.applied.unique_id.clone())
                        .collect(),
                    predicates: remainder,
                    satisfiability: remainder_result,
                },
            };
        }
        match applied.len() {
            0 => {}
            1 => return RewriteResult::Finished(applied.pop().unwrap().applied),
            _ => {
                return RewriteResult::Branch {
                    original: pattern.clone(),
                    branches: applied
                        .into_iter()
                        .map(|application| application.applied)
                        .collect(),
                };
            }
        }
    }
    if saw_trivial {
        RewriteResult::Trivial(pattern.clone())
    } else {
        RewriteResult::Stuck(pattern.clone())
    }
}

fn applicable_groups(
    definition: &BackendDefinition,
    index: &TermIndex,
) -> std::collections::BTreeMap<u8, Vec<std::sync::Arc<RewriteRule>>> {
    let mut groups = std::collections::BTreeMap::new();
    let covered = if index == &TermIndex::Variable {
        vec![index]
    } else {
        vec![index, &TermIndex::Variable]
    };
    for covered in covered {
        if let Some(found) = definition.rewrite_theory.get(covered) {
            for (priority, rules) in found {
                groups
                    .entry(*priority)
                    .or_insert_with(Vec::new)
                    .extend(rules.iter().cloned());
            }
        }
    }
    groups
}

enum RuleAttempt {
    NotApplicable,
    Trivial,
    Applied(RuleApplication),
    Indeterminate(IndeterminateReason),
}

/// Conservatively recover matches that Booster delegates to Kore.
///
/// Remainders are simplified after applying the partial substitution. For a function pattern with
/// one unbound result-sorted variable, the concrete subject is also tried as a witness; the match
/// is accepted only when evaluating that witness reproduces the subject exactly. A failed witness
/// remains indeterminate because it does not prove that no other witness exists.
fn recover_indeterminate_match(
    definition: &BackendDefinition,
    mut substitution: Substitution,
    remainder: Vec<(Term, Term)>,
    known_predicates: &[Predicate],
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> MatchResult {
    let mut unresolved = Vec::new();
    for (pattern, subject) in remainder {
        let pattern = substitute(&pattern, &substitution);
        let subject = substitute(&subject, &substitution);
        let simplified =
            simplify_with_solver(definition, &pattern, known_predicates, options, solver)
                .ok()
                .filter(|result| result.constraints.is_empty())
                .map_or_else(|| pattern.clone(), |result| result.term);

        let pair_remainder = match match_terms(
            MatchMode::Rewrite,
            &definition.sort_graph,
            &simplified,
            &subject,
        ) {
            MatchResult::Success(found) => {
                substitution = compose(&found, &substitution);
                continue;
            }
            MatchResult::Failed(reason) => return MatchResult::Failed(reason),
            MatchResult::Indeterminate {
                substitution: found,
                remainder,
            } => {
                substitution = compose(&found, &substitution);
                remainder
            }
        };

        let TermKind::Application { symbol, .. } = simplified.kind() else {
            unresolved.extend(pair_remainder);
            continue;
        };
        if !matches!(symbol.attributes.symbol_type, SymbolType::Function(_))
            || !subject.attributes().constructor_like
        {
            unresolved.extend(pair_remainder);
            continue;
        }
        let candidates = simplified
            .attributes()
            .variables
            .iter()
            .filter(|variable| {
                !substitution.contains_key(*variable) && variable.sort == subject.sort()
            })
            .cloned()
            .collect::<Vec<_>>();
        let [candidate] = candidates.as_slice() else {
            unresolved.extend(pair_remainder);
            continue;
        };
        let witness = Substitution::from([(candidate.clone(), subject.clone())]);
        let candidate_substitution = compose(&witness, &substitution);
        let candidate_pattern = substitute(&pattern, &candidate_substitution);
        let Ok(candidate_pattern) = simplify_with_solver(
            definition,
            &candidate_pattern,
            known_predicates,
            options,
            solver,
        ) else {
            unresolved.extend(pair_remainder);
            continue;
        };
        if !candidate_pattern.constraints.is_empty() {
            unresolved.extend(pair_remainder);
            continue;
        }
        match match_terms(
            MatchMode::Rewrite,
            &definition.sort_graph,
            &candidate_pattern.term,
            &subject,
        ) {
            MatchResult::Success(found) => {
                substitution = compose(&found, &candidate_substitution);
                continue;
            }
            MatchResult::Failed(_) | MatchResult::Indeterminate { .. } => {}
        }
        unresolved.extend(pair_remainder);
    }

    if unresolved.is_empty() {
        MatchResult::Success(substitution)
    } else {
        MatchResult::Indeterminate {
            substitution,
            remainder: unresolved,
        }
    }
}

struct RuleApplication {
    applied: AppliedRule,
    remainder: Predicate,
}

fn apply_rule(
    definition: &BackendDefinition,
    rule: &RewriteRule,
    pattern: &Pattern,
    fresh_counter: &mut u64,
    simplification_options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> RuleAttempt {
    let substitution = match match_terms(
        MatchMode::Rewrite,
        &definition.sort_graph,
        &rule.lhs,
        &pattern.term,
    ) {
        MatchResult::Failed(_) => return RuleAttempt::NotApplicable,
        MatchResult::Indeterminate {
            substitution,
            remainder,
        } => match recover_indeterminate_match(
            definition,
            substitution,
            remainder,
            &pattern.constraints,
            simplification_options,
            solver,
        ) {
            MatchResult::Failed(_) => return RuleAttempt::NotApplicable,
            MatchResult::Success(substitution) => substitution,
            MatchResult::Indeterminate {
                substitution,
                remainder,
            } => {
                let requires = substitute_predicates(&rule.requires, &substitution);
                let requires = simplify_predicates_with_solver(
                    definition,
                    &requires,
                    &pattern.constraints,
                    simplification_options,
                    solver,
                )
                .unwrap_or(requires);
                if predicates_truth(&requires) == Truth::False {
                    return RuleAttempt::NotApplicable;
                }
                let unclear = requires
                    .into_iter()
                    .filter(|predicate| {
                        predicates_truth(std::slice::from_ref(predicate)) == Truth::Unknown
                            && !pattern.constraints.contains(predicate)
                    })
                    .collect::<Vec<_>>();
                if !unclear.is_empty()
                    && matches!(
                        solver.check_predicates(
                            &pattern.constraints,
                            &Substitution::new(),
                            &unclear,
                        ),
                        Ok(Validity::Invalid)
                    )
                {
                    return RuleAttempt::NotApplicable;
                }
                return RuleAttempt::Indeterminate(IndeterminateReason::Match {
                    rule_id: rule.attributes.unique_id.clone(),
                    substitution,
                    remainder,
                });
            }
        },
        MatchResult::Success(substitution) => substitution,
    };

    if let Some(variable) = check_concreteness(rule, &substitution) {
        return RuleAttempt::Indeterminate(IndeterminateReason::Concreteness {
            rule_id: rule.attributes.unique_id.clone(),
            variable,
        });
    }
    if !rule.computed_attributes.undefined_symbols.is_empty() {
        return RuleAttempt::Indeterminate(IndeterminateReason::Definedness {
            rule_id: rule.attributes.unique_id.clone(),
            symbols: rule
                .computed_attributes
                .undefined_symbols
                .iter()
                .cloned()
                .collect(),
        });
    }
    let requires = substitute_predicates(&rule.requires, &substitution);
    let requires = simplify_predicates_with_solver(
        definition,
        &requires,
        &pattern.constraints,
        simplification_options,
        solver,
    )
    .unwrap_or(requires);
    if predicates_truth(&requires) == Truth::False {
        return RuleAttempt::NotApplicable;
    }
    let mut unclear_requires = requires
        .into_iter()
        .filter(|predicate| {
            predicates_truth(std::slice::from_ref(predicate)) == Truth::Unknown
                && !pattern.constraints.contains(predicate)
        })
        .collect::<Vec<_>>();
    if !unclear_requires.is_empty() {
        match solver.check_predicates(
            &pattern.constraints,
            &Substitution::new(),
            &unclear_requires,
        ) {
            Ok(Validity::Valid) => unclear_requires.clear(),
            Ok(Validity::Invalid) => return RuleAttempt::NotApplicable,
            Ok(Validity::Indeterminate) => {}
            Err(SmtError::Unavailable) => {
                return RuleAttempt::Indeterminate(IndeterminateReason::Requires {
                    rule_id: rule.attributes.unique_id.clone(),
                    predicates: unclear_requires,
                });
            }
            Ok(Validity::InconsistentGroundTruth) => {
                return RuleAttempt::Indeterminate(IndeterminateReason::Smt {
                    rule_id: rule.attributes.unique_id.clone(),
                    error: SmtError::InconsistentGroundTruth,
                });
            }
            Ok(Validity::Unknown(reason)) => {
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

    let RuleRhs::Term(rhs) = &rule.rhs else {
        return RuleAttempt::NotApplicable;
    };
    let existential_substitution = freshen_existentials(rule, pattern, fresh_counter);
    let rhs = substitute(&substitute(rhs, &substitution), &existential_substitution);
    let ensures = substitute_predicates(
        &substitute_predicates(&rule.ensures, &substitution),
        &existential_substitution,
    );
    let mut condition_knowledge = pattern.constraints.clone();
    extend_unique(&mut condition_knowledge, unclear_requires.iter().cloned());
    let ensures = simplify_predicates_with_solver(
        definition,
        &ensures,
        &condition_knowledge,
        simplification_options,
        solver,
    )
    .unwrap_or(ensures);
    match predicates_truth(&ensures) {
        Truth::False => return RuleAttempt::Trivial,
        Truth::True => {}
        Truth::Unknown => {
            match solver.check_predicates(&condition_knowledge, &Substitution::new(), &ensures) {
                Ok(Validity::Invalid | Validity::InconsistentGroundTruth) => {
                    return RuleAttempt::Trivial;
                }
                Ok(Validity::Valid | Validity::Indeterminate) | Err(SmtError::Unavailable) => {}
                Ok(Validity::Unknown(reason)) => {
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
    }
    let mut constraints = pattern.constraints.clone();
    extend_unique(&mut constraints, unclear_requires.iter().cloned());
    extend_unique(&mut constraints, ensures);
    let remainder = if unclear_requires.is_empty() {
        Predicate::False
    } else {
        Predicate::Not(Box::new(conjoin(unclear_requires)))
    };
    RuleAttempt::Applied(RuleApplication {
        applied: AppliedRule {
            pattern: Pattern {
                term: rhs,
                constraints,
            },
            label: rule.attributes.label.clone(),
            unique_id: rule.attributes.unique_id.clone(),
            substitution,
        },
        remainder,
    })
}

fn conjoin(mut predicates: Vec<Predicate>) -> Predicate {
    match predicates.len() {
        0 => Predicate::True,
        1 => predicates.pop().unwrap(),
        _ => Predicate::And(predicates),
    }
}

fn extend_unique(predicates: &mut Vec<Predicate>, added: impl IntoIterator<Item = Predicate>) {
    for predicate in added {
        if !predicates.contains(&predicate) {
            predicates.push(predicate);
        }
    }
}

pub(crate) fn check_concreteness(
    rule: &RewriteRule,
    substitution: &Substitution,
) -> Option<Variable> {
    let constrained = match &rule.attributes.concreteness {
        Concreteness::Unconstrained => return None,
        Concreteness::All(kind) => rule
            .lhs
            .attributes()
            .variables
            .iter()
            .cloned()
            .map(|variable| (variable, *kind))
            .collect::<Vec<_>>(),
        Concreteness::Some(constrained) => constrained
            .iter()
            .filter_map(|((name, sort), kind)| {
                rule.lhs
                    .attributes()
                    .variables
                    .iter()
                    .find(|variable| {
                        variable
                            .name
                            .as_ref()
                            .strip_prefix("Rule#")
                            .or_else(|| variable.name.as_ref().strip_prefix("Eq#"))
                            == Some(name.as_ref())
                            && sort_name(&variable.sort) == Some(sort.as_ref())
                    })
                    .cloned()
                    .map(|variable| (variable, *kind))
            })
            .collect(),
    };
    constrained.into_iter().find_map(|(variable, kind)| {
        let Some(term) = substitution.get(&variable) else {
            return Some(variable);
        };
        let concrete = term.attributes().constructor_like;
        let satisfied = match kind {
            ConstraintKind::Concrete => concrete,
            ConstraintKind::Symbolic => !concrete,
        };
        (!satisfied).then_some(variable)
    })
}

fn sort_name(sort: &Sort) -> Option<&str> {
    match sort {
        Sort::Application { name, .. } => Some(name.as_ref()),
        Sort::Variable(_) => None,
    }
}

fn freshen_existentials(
    rule: &RewriteRule,
    pattern: &Pattern,
    fresh_counter: &mut u64,
) -> Substitution {
    let mut names_to_avoid = pattern
        .term
        .attributes()
        .variables
        .iter()
        .map(|variable| variable.name.clone())
        .collect::<BTreeSet<_>>();
    rule.existentials
        .iter()
        .cloned()
        .map(|variable| {
            let name = loop {
                let name = format!("{}!{}", variable.name, *fresh_counter);
                *fresh_counter += 1;
                if names_to_avoid.insert(name.as_str().into()) {
                    break name;
                }
            };
            let term = Term::variable(Variable::new(name, variable.sort.clone()));
            (variable, term)
        })
        .collect()
}

pub(crate) fn substitute_predicates(
    predicates: &[Predicate],
    substitution: &Substitution,
) -> Vec<Predicate> {
    predicates
        .iter()
        .map(|predicate| substitute_predicate(predicate, substitution))
        .collect()
}

fn substitute_predicate(predicate: &Predicate, substitution: &Substitution) -> Predicate {
    match predicate {
        Predicate::True => Predicate::True,
        Predicate::False => Predicate::False,
        Predicate::Term(term) => Predicate::Term(substitute(term, substitution)),
        Predicate::Equals(left, right) => Predicate::Equals(
            substitute(left, substitution),
            substitute(right, substitution),
        ),
        Predicate::Ceil(term) => Predicate::Ceil(substitute(term, substitution)),
        Predicate::Floor(term) => Predicate::Floor(substitute(term, substitution)),
        Predicate::In(left, right) => Predicate::In(
            substitute(left, substitution),
            substitute(right, substitution),
        ),
        Predicate::Not(inner) => {
            Predicate::Not(Box::new(substitute_predicate(inner, substitution)))
        }
        Predicate::And(inner) => Predicate::And(substitute_predicates(inner, substitution)),
        Predicate::Or(inner) => Predicate::Or(substitute_predicates(inner, substitution)),
        Predicate::Implies(left, right) => Predicate::Implies(
            Box::new(substitute_predicate(left, substitution)),
            Box::new(substitute_predicate(right, substitution)),
        ),
        Predicate::Iff(left, right) => Predicate::Iff(
            Box::new(substitute_predicate(left, substitution)),
            Box::new(substitute_predicate(right, substitution)),
        ),
        Predicate::Exists(variable, inner) => Predicate::Exists(
            variable.clone(),
            Box::new(substitute_predicate(
                inner,
                &without_variable(substitution, variable),
            )),
        ),
        Predicate::Forall(variable, inner) => Predicate::Forall(
            variable.clone(),
            Box::new(substitute_predicate(
                inner,
                &without_variable(substitution, variable),
            )),
        ),
    }
}

fn without_variable(substitution: &Substitution, variable: &Variable) -> Substitution {
    let mut substitution = substitution.clone();
    substitution.remove(variable);
    substitution
}

pub(crate) fn predicates_truth(predicates: &[Predicate]) -> Truth {
    predicates.iter().fold(Truth::True, |result, predicate| {
        and_truth(result, predicate_truth(predicate))
    })
}

fn predicate_truth(predicate: &Predicate) -> Truth {
    match predicate {
        Predicate::True => Truth::True,
        Predicate::False => Truth::False,
        Predicate::Term(term) => bool_term_truth(term),
        Predicate::Equals(left, right) if left == right => Truth::True,
        Predicate::Equals(left, right)
            if left.attributes().constructor_like && right.attributes().constructor_like =>
        {
            Truth::False
        }
        Predicate::Not(inner) => match predicate_truth(inner) {
            Truth::True => Truth::False,
            Truth::False => Truth::True,
            Truth::Unknown => Truth::Unknown,
        },
        Predicate::And(inner) => predicates_truth(inner),
        Predicate::Or(inner) => inner.iter().fold(Truth::False, |result, predicate| {
            or_truth(result, predicate_truth(predicate))
        }),
        Predicate::Implies(left, right) => or_truth(
            match predicate_truth(left) {
                Truth::True => Truth::False,
                Truth::False => Truth::True,
                Truth::Unknown => Truth::Unknown,
            },
            predicate_truth(right),
        ),
        Predicate::Iff(left, right) => match (predicate_truth(left), predicate_truth(right)) {
            (Truth::True, Truth::True) | (Truth::False, Truth::False) => Truth::True,
            (Truth::True, Truth::False) | (Truth::False, Truth::True) => Truth::False,
            _ => Truth::Unknown,
        },
        Predicate::Ceil(term) if term.attributes().constructor_like => Truth::True,
        Predicate::Equals(..)
        | Predicate::Ceil(_)
        | Predicate::Floor(_)
        | Predicate::In(..)
        | Predicate::Exists(..)
        | Predicate::Forall(..) => Truth::Unknown,
    }
}

fn bool_term_truth(term: &Term) -> Truth {
    match term.kind() {
        TermKind::DomainValue { sort, value }
            if sort == &Sort::simple("SortBool") && value.as_ref() == "true" =>
        {
            Truth::True
        }
        TermKind::DomainValue { sort, value }
            if sort == &Sort::simple("SortBool") && value.as_ref() == "false" =>
        {
            Truth::False
        }
        _ => Truth::Unknown,
    }
}

fn and_truth(left: Truth, right: Truth) -> Truth {
    match (left, right) {
        (Truth::False, _) | (_, Truth::False) => Truth::False,
        (Truth::True, Truth::True) => Truth::True,
        _ => Truth::Unknown,
    }
}

fn or_truth(left: Truth, right: Truth) -> Truth {
    match (left, right) {
        (Truth::True, _) | (_, Truth::True) => Truth::True,
        (Truth::False, Truth::False) => Truth::False,
        _ => Truth::Unknown,
    }
}

#[cfg(test)]
mod tests {
    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    use super::*;

    fn definition(axioms: &str) -> BackendDefinition {
        let source = format!(
            r#"[]
            module MAIN
                sort SortS{{}} [hasDomainValues{{}}()]
                symbol wrap{{}}(SortS{{}}) : SortS{{}} [constructor{{}}()]
                {axioms}
            endmodule []"#
        );
        let syntax = parse_definition(&source).expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    fn subject(definition: &BackendDefinition, value: &str) -> Pattern {
        let syntax = parse_pattern(&format!(r#"wrap{{}}(\dv{{SortS{{}}}}("{value}"))"#))
            .expect("subject should parse");
        Pattern {
            term: definition
                .internalize_term(&syntax, &[])
                .expect("subject should internalize"),
            constraints: Vec::new(),
        }
    }

    #[cfg(feature = "z3")]
    fn symbolic_remainder_definition(rules: &str) -> BackendDefinition {
        let source = r#"[]
            module MAIN
                sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                symbol wrap{}(SortInt{}) : SortInt{} [constructor{}()]
                symbol lt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), smt-hook{}("<")]
                $RULES
            endmodule []"#
            .replace("$RULES", rules);
        let syntax = parse_definition(&source).expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    #[cfg(feature = "z3")]
    fn symbolic_subject(definition: &BackendDefinition) -> Pattern {
        Pattern {
            term: definition
                .internalize_term(&parse_pattern("wrap{}(X:SortInt{})").unwrap(), &[])
                .unwrap(),
            constraints: Vec::new(),
        }
    }

    fn rewritten_value(result: RewriteResult) -> String {
        let RewriteResult::Finished(applied) = result else {
            panic!("expected finished rewrite, found {result:?}");
        };
        let TermKind::DomainValue { value, .. } = applied.pattern.term.kind() else {
            panic!("expected domain value, found {:?}", applied.pattern.term);
        };
        value.to_string()
    }

    #[test]
    fn tries_priority_groups_in_ascending_numeric_order() {
        let definition = definition(
            r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(\dv{SortS{}}("zero")), \top{SortS{}}()),
                \dv{SortS{}}("high")
            ) [label{}("high"), priority{}("10")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                \dv{SortS{}}("low")
            ) [label{}("low"), priority{}("50")]
            "#,
        );
        let mut fresh = 0;

        assert_eq!(
            rewritten_value(rewrite_step(
                &definition,
                &subject(&definition, "zero"),
                &mut fresh,
            )),
            "high"
        );
        assert_eq!(
            rewritten_value(rewrite_step(
                &definition,
                &subject(&definition, "one"),
                &mut fresh,
            )),
            "low"
        );
    }

    #[test]
    fn retries_function_pattern_remainders_after_simplification() {
        let definition = definition(
            r#"
            symbol identity{}(SortS{}) : SortS{} [function{}(), total{}()]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortS{}, R}(
                    identity{}(X:SortS{}),
                    \and{SortS{}}(X:SortS{}, \top{SortS{}}())
                )
            ) [label{}("identity"), simplification{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(identity{}(X:SortS{})),
                    \top{SortS{}}()
                ),
                \dv{SortS{}}("done")
            ) [label{}("function-pattern")]
            "#,
        );
        let mut fresh = 0;

        assert_eq!(
            rewritten_value(rewrite_step(
                &definition,
                &subject(&definition, "value"),
                &mut fresh,
            )),
            "done"
        );
    }

    #[test]
    fn a_failed_function_pattern_witness_remains_indeterminate() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortS{} [hasDomainValues{}()]
                sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                symbol wrap{}(SortBool{}) : SortS{} [constructor{}()]
                symbol not{}(SortBool{}) : SortBool{}
                    [function{}(), total{}(), hook{}("BOOL.not")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(
                        wrap{}(not{}(X:SortBool{})),
                        \top{SortS{}}()
                    ),
                    \dv{SortS{}}("done")
                ) [label{}("negated")]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let term = definition
            .internalize_term(
                &parse_pattern(r#"wrap{}(\dv{SortBool{}}("true"))"#).unwrap(),
                &[],
            )
            .unwrap();
        let mut fresh = 0;

        assert!(matches!(
            rewrite_step(
                &definition,
                &Pattern {
                    term,
                    constraints: Vec::new(),
                },
                &mut fresh,
            ),
            RewriteResult::Indeterminate {
                reason: IndeterminateReason::Match { .. },
                ..
            }
        ));
    }

    #[test]
    fn simplifies_rule_conditions_with_backend_equations_before_rewriting() {
        let definition = definition(
            r#"
            sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
            symbol isZero{}(SortS{}) : SortBool{} [function{}(), total{}()]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortBool{}, R}(
                    isZero{}(\dv{SortS{}}("zero")),
                    \and{SortBool{}}(
                        \dv{SortBool{}}("true"),
                        \top{SortBool{}}()
                    )
                )
            ) [label{}("zero-is-zero"), simplification{}()]
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortBool{}, R}(
                    isZero{}(\dv{SortS{}}("one")),
                    \and{SortBool{}}(
                        \dv{SortBool{}}("false"),
                        \top{SortBool{}}()
                    )
                )
            ) [label{}("one-is-not-zero"), simplification{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(X:SortS{}),
                    \equals{SortBool{}, SortS{}}(
                        isZero{}(X:SortS{}),
                        \dv{SortBool{}}("true")
                    )
                ),
                \dv{SortS{}}("high")
            ) [label{}("conditional"), priority{}("10")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                \dv{SortS{}}("fallback")
            ) [label{}("fallback"), priority{}("50")]
            "#,
        );
        let mut fresh = 0;

        assert_eq!(
            rewritten_value(rewrite_step(
                &definition,
                &subject(&definition, "zero"),
                &mut fresh,
            )),
            "high"
        );
        assert_eq!(
            rewritten_value(rewrite_step(
                &definition,
                &subject(&definition, "one"),
                &mut fresh,
            )),
            "fallback"
        );
    }

    #[test]
    fn aborts_before_lower_priorities_when_requires_are_unknown() {
        let definition = definition(
            r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(X:SortS{}),
                    \equals{SortS{}, SortS{}}(X:SortS{}, \dv{SortS{}}("zero"))
                ),
                \dv{SortS{}}("conditional")
            ) [label{}("conditional"), priority{}("10")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                \dv{SortS{}}("fallback")
            ) [label{}("fallback"), priority{}("50")]
            "#,
        );
        let syntax = parse_pattern("wrap{}(Y:SortS{})").unwrap();
        let pattern = Pattern {
            term: definition.internalize_term(&syntax, &[]).unwrap(),
            constraints: Vec::new(),
        };
        let mut fresh = 0;

        assert!(matches!(
            rewrite_step(&definition, &pattern, &mut fresh),
            RewriteResult::Indeterminate {
                reason: IndeterminateReason::Requires { rule_id, .. },
                ..
            } if rule_id == "conditional"
        ));
    }

    #[test]
    fn false_requires_prune_a_rule_even_when_matching_is_indeterminate() {
        let definition = definition(
            r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(X:SortS{}),
                    \bottom{SortS{}}()
                ),
                \dv{SortS{}}("unreachable")
            ) [label{}("false-requires")]
            "#,
        );
        let rule = definition
            .rewrite_theory
            .values()
            .flat_map(|groups| groups.values())
            .flatten()
            .next()
            .expect("rewrite rule should be indexed");
        let pattern = Pattern {
            term: rule.lhs.clone(),
            constraints: Vec::new(),
        };
        let mut fresh = 0;

        assert!(matches!(
            rewrite_step(&definition, &pattern, &mut fresh),
            RewriteResult::Stuck(_)
        ));
    }

    #[cfg(feature = "z3")]
    #[test]
    fn z3_proves_or_refutes_symbolic_requires_before_priority_fallback() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                symbol wrap{}(SortInt{}) : SortInt{} [constructor{}()]
                symbol lt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), smt-hook{}("<")]
                axiom{} \rewrites{SortInt{}}(
                    \and{SortInt{}}(
                        wrap{}(X:SortInt{}),
                        \equals{SortBool{}, SortInt{}}(
                            lt{}(X:SortInt{}, \dv{SortInt{}}("10")),
                            \dv{SortBool{}}("true")
                        )
                    ),
                    \dv{SortInt{}}("high")
                ) [label{}("high"), priority{}("10")]
                axiom{} \rewrites{SortInt{}}(
                    \and{SortInt{}}(wrap{}(X:SortInt{}), \top{SortInt{}}()),
                    \dv{SortInt{}}("fallback")
                ) [label{}("fallback"), priority{}("50")]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let solver = crate::smt::Z3Solver::new(&definition).unwrap();
        let variable = Variable::new("Y", Sort::simple("SortInt"));
        let subject = definition
            .internalize_term(&parse_pattern("wrap{}(Y:SortInt{})").unwrap(), &[])
            .unwrap();
        let integer = |value: &str| Term::domain_value(Sort::simple("SortInt"), value);
        let run = |value: &str| {
            let pattern = Pattern {
                term: subject.clone(),
                constraints: vec![Predicate::Equals(
                    Term::variable(variable.clone()),
                    integer(value),
                )],
            };
            let mut fresh = 0;
            rewritten_value(rewrite_step_with_solver(
                &definition,
                &pattern,
                &mut fresh,
                &solver,
            ))
        };

        assert_eq!(run("5"), "high");
        assert_eq!(run("15"), "fallback");
    }

    #[cfg(feature = "z3")]
    #[test]
    fn rejects_a_satisfiable_remainder_from_one_symbolic_rule() {
        let definition = symbolic_remainder_definition(
            r#"
            axiom{} \rewrites{SortInt{}}(
                \and{SortInt{}}(
                    wrap{}(X:SortInt{}),
                    \equals{SortBool{}, SortInt{}}(
                        lt{}(X:SortInt{}, \dv{SortInt{}}("0")),
                        \dv{SortBool{}}("true")
                    )
                ),
                \dv{SortInt{}}("negative")
            ) [label{}("negative")]
            "#,
        );
        let solver = crate::smt::Z3Solver::new(&definition).unwrap();
        let mut fresh = 0;

        assert!(matches!(
            rewrite_step_with_solver(
                &definition,
                &symbolic_subject(&definition),
                &mut fresh,
                &solver,
            ),
            RewriteResult::Indeterminate {
                reason: IndeterminateReason::Remainder {
                    rule_ids,
                    satisfiability: Ok(Satisfiability::Sat),
                    ..
                },
                ..
            } if rule_ids == ["negative"]
        ));
    }

    #[cfg(feature = "z3")]
    #[test]
    fn branches_only_after_complementary_rules_make_the_remainder_unsatisfiable() {
        let definition = symbolic_remainder_definition(
            r#"
            axiom{} \rewrites{SortInt{}}(
                \and{SortInt{}}(
                    wrap{}(X:SortInt{}),
                    \equals{SortBool{}, SortInt{}}(
                        lt{}(X:SortInt{}, \dv{SortInt{}}("0")),
                        \dv{SortBool{}}("true")
                    )
                ),
                \dv{SortInt{}}("negative")
            ) [label{}("negative")]
            axiom{} \rewrites{SortInt{}}(
                \and{SortInt{}}(
                    wrap{}(X:SortInt{}),
                    \equals{SortBool{}, SortInt{}}(
                        lt{}(X:SortInt{}, \dv{SortInt{}}("0")),
                        \dv{SortBool{}}("false")
                    )
                ),
                \dv{SortInt{}}("nonnegative")
            ) [label{}("nonnegative")]
            "#,
        );
        let solver = crate::smt::Z3Solver::new(&definition).unwrap();
        let mut fresh = 0;

        let RewriteResult::Branch { branches, .. } = rewrite_step_with_solver(
            &definition,
            &symbolic_subject(&definition),
            &mut fresh,
            &solver,
        ) else {
            panic!("complementary rules should form a complete branch");
        };
        assert_eq!(
            branches
                .iter()
                .map(|branch| branch.label.as_deref().unwrap())
                .collect::<Vec<_>>(),
            ["negative", "nonnegative"]
        );
        assert!(
            branches
                .iter()
                .all(|branch| branch.pattern.constraints.len() == 1)
        );
    }

    #[test]
    fn branches_when_multiple_rules_in_one_priority_apply() {
        let definition = definition(
            r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                \dv{SortS{}}("left")
            ) [label{}("left")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                \dv{SortS{}}("right")
            ) [label{}("right")]
            "#,
        );
        let mut fresh = 0;

        let RewriteResult::Branch { branches, .. } =
            rewrite_step(&definition, &subject(&definition, "value"), &mut fresh)
        else {
            panic!("both rules should branch");
        };
        assert_eq!(
            branches
                .iter()
                .map(|branch| branch.label.as_deref().unwrap())
                .collect::<Vec<_>>(),
            vec!["left", "right"]
        );
    }

    #[test]
    fn freshens_existential_variables_on_each_application() {
        let definition = definition(
            r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                \exists{SortS{}}(Y:SortS{}, wrap{}(Y:SortS{}))
            ) [label{}("fresh")]
            "#,
        );
        let pattern = subject(&definition, "value");
        let mut fresh = 0;
        let first = rewrite_step(&definition, &pattern, &mut fresh);
        let second = rewrite_step(&definition, &pattern, &mut fresh);
        let names = [first, second].map(|result| {
            let RewriteResult::Finished(applied) = result else {
                panic!("rule should apply");
            };
            applied
                .pattern
                .term
                .attributes()
                .variables
                .iter()
                .next()
                .unwrap()
                .name
                .clone()
        });
        assert_ne!(names[0], names[1]);
    }

    #[test]
    fn executes_to_a_stuck_normal_form_and_records_the_trace() {
        let definition = definition(
            r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(\dv{SortS{}}("zero")), \top{SortS{}}()),
                wrap{}(\dv{SortS{}}("one"))
            ) [label{}("first")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(\dv{SortS{}}("one")), \top{SortS{}}()),
                \dv{SortS{}}("done")
            ) [label{}("second")]
            "#,
        );

        let result = execute(
            &definition,
            subject(&definition, "zero"),
            ExecutionOptions::default(),
        );
        assert_eq!(result.leaves.len(), 1);
        let leaf = &result.leaves[0];
        assert_eq!(leaf.depth, 2);
        assert_eq!(leaf.halt_reason, HaltReason::Stuck);
        assert_eq!(
            leaf.trace
                .iter()
                .map(|entry| (entry.depth, entry.label.as_deref().unwrap()))
                .collect::<Vec<_>>(),
            vec![(1, "first"), (2, "second")]
        );
        assert!(matches!(
            leaf.pattern.term.kind(),
            TermKind::DomainValue { value, .. } if value.as_ref() == "done"
        ));
    }

    #[test]
    fn stops_exactly_at_the_requested_depth_bound() {
        let definition = definition(
            r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                wrap{}(X:SortS{})
            ) [label{}("loop")]
            "#,
        );

        let result = execute(
            &definition,
            subject(&definition, "value"),
            ExecutionOptions {
                max_depth: 3,
                ..ExecutionOptions::default()
            },
        );
        assert_eq!(result.leaves.len(), 1);
        assert_eq!(result.leaves[0].depth, 3);
        assert_eq!(result.leaves[0].trace.len(), 3);
        assert_eq!(result.leaves[0].halt_reason, HaltReason::DepthBound);
    }

    #[test]
    fn carries_each_rewrite_branch_to_its_own_leaf() {
        let definition = definition(
            r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                \dv{SortS{}}("left")
            ) [label{}("left")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                \dv{SortS{}}("right")
            ) [label{}("right")]
            "#,
        );

        let result = execute(
            &definition,
            subject(&definition, "value"),
            ExecutionOptions::default(),
        );
        assert_eq!(result.leaves.len(), 2);
        assert!(
            result
                .leaves
                .iter()
                .all(|leaf| leaf.depth == 1 && leaf.halt_reason == HaltReason::Stuck)
        );
        assert_eq!(
            result
                .leaves
                .iter()
                .map(|leaf| leaf.trace[0].label.as_deref().unwrap())
                .collect::<Vec<_>>(),
            vec!["left", "right"]
        );
    }
}
