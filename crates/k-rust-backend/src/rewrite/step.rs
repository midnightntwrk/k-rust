//! Priority-grouped rewrite step with remainder: `All` mode folds the remainder through every
//! priority group (Kore `transitionAllRewrite`), while `Any` mode threads it through the rules
//! sequentially (Kore `applyRewriteRulesSequence`). The returned remainder is complete in both
//! modes. O(c) rule attempts per step for the c candidates of `rule::applicable_groups` plus one
//! SAT check per productive group (`All`) or per applied rule (`Any`);
//! `Counter::RewriteRulesApplied` (row B10).

use std::sync::Arc;

use k_rust_kore::measure::{self, Counter};

use crate::{
    definition::BackendDefinition,
    rule::{RewriteRule, applicable_groups, term_index},
    simplify::{SimplificationOptions, simplify_predicates_with_solver, simplify_with_solver},
    smt::{Satisfiability, SmtSolver},
    substitution::Substitution,
    transition::ExecutionIoState,
};

use super::{
    AppliedRule, IndeterminateReason, Pattern, RemainderBranch, RemainderSimplification,
    RewriteResult, RuleAttempt, TrivialApplication, Truth, apply_rule, extend_unique,
    predicates_truth, violates_finite_constructor_domain,
};

enum PriorityGroupOutcome {
    NotProductive,
    Productive {
        branches: Vec<AppliedRule>,
        trivial: Vec<TrivialApplication>,
        remainder: Option<RemainderBranch>,
    },
    Indeterminate(IndeterminateReason),
}

#[allow(clippy::too_many_arguments)]
fn apply_priority_group(
    definition: &BackendDefinition,
    pattern: &Pattern,
    rules: &[Arc<RewriteRule>],
    fresh_counter: &mut u64,
    simplification_options: SimplificationOptions,
    solver: &dyn SmtSolver,
    assume_initial_defined: bool,
    io: Option<&ExecutionIoState>,
) -> PriorityGroupOutcome {
    let mut applied = Vec::new();
    let mut trivial = Vec::new();
    for rule in rules {
        match apply_rule(
            definition,
            rule,
            pattern,
            fresh_counter,
            simplification_options,
            solver,
            assume_initial_defined,
            io,
        ) {
            RuleAttempt::NotApplicable => {}
            RuleAttempt::Unified { groups } => {
                measure::bump(Counter::RewriteRulesApplied);
                for group in groups {
                    applied.extend(group.applied);
                    trivial.extend(group.trivial);
                }
            }
            RuleAttempt::Indeterminate(reason) => {
                return PriorityGroupOutcome::Indeterminate(reason);
            }
        }
    }
    if applied.is_empty() && trivial.is_empty() {
        return PriorityGroupOutcome::NotProductive;
    }
    let rule_ids = applied
        .iter()
        .map(|application| application.applied.unique_id.clone())
        .chain(
            trivial
                .iter()
                .map(|application| application.rule_id.clone()),
        )
        .collect::<Vec<_>>();
    let raw_remainder = applied
        .iter()
        .map(|application| application.remainder.clone())
        .chain(
            trivial
                .iter()
                .map(|application| application.remainder.clone()),
        )
        .collect::<Vec<_>>();
    let remainder = match simplify_predicates_with_solver(
        definition,
        &raw_remainder,
        &pattern.constraints,
        simplification_options,
        solver,
    ) {
        Ok(remainder) => remainder,
        Err(error) => {
            return PriorityGroupOutcome::Indeterminate(IndeterminateReason::simplification(
                None, error,
            ));
        }
    };
    let remainder_result = if predicates_truth(&remainder) == Truth::False {
        Ok(Satisfiability::Unsat)
    } else {
        let mut predicates = pattern.constraints.clone();
        predicates.extend(remainder.iter().cloned());
        if violates_finite_constructor_domain(definition, &predicates) {
            Ok(Satisfiability::Unsat)
        } else {
            solver.is_sat(&predicates, &Substitution::new())
        }
    };
    if !matches!(
        remainder_result,
        Ok(Satisfiability::Unsat | Satisfiability::Sat)
    ) {
        return PriorityGroupOutcome::Indeterminate(IndeterminateReason::Remainder {
            rule_ids,
            predicates: remainder,
            satisfiability: remainder_result,
        });
    }
    let remainder = if matches!(remainder_result, Ok(Satisfiability::Sat)) {
        let mut remainder_pattern = pattern.clone();
        extend_unique(
            &mut remainder_pattern.constraints,
            remainder.iter().cloned(),
        );
        Some(RemainderBranch {
            pattern: remainder_pattern,
            rule_ids,
            effects: Vec::new(),
            simplifications: Vec::new(),
            indeterminate: None,
        })
    } else {
        None
    };
    PriorityGroupOutcome::Productive {
        branches: applied
            .into_iter()
            .map(|application| application.applied)
            .collect(),
        trivial,
        remainder,
    }
}

#[allow(clippy::too_many_arguments)]
fn first_productive_group(
    definition: &BackendDefinition,
    pattern: &Pattern,
    groups: &mut impl Iterator<Item = Vec<Arc<RewriteRule>>>,
    fresh_counter: &mut u64,
    simplification_options: SimplificationOptions,
    solver: &dyn SmtSolver,
    assume_initial_defined: bool,
    io: Option<&ExecutionIoState>,
) -> PriorityGroupOutcome {
    for rules in groups.by_ref() {
        match apply_priority_group(
            definition,
            pattern,
            &rules,
            fresh_counter,
            simplification_options,
            solver,
            assume_initial_defined,
            io,
        ) {
            PriorityGroupOutcome::NotProductive => {}
            outcome @ PriorityGroupOutcome::Indeterminate(_) => return outcome,
            outcome @ PriorityGroupOutcome::Productive { .. } => return outcome,
        }
    }
    PriorityGroupOutcome::NotProductive
}

fn classify_first_group(
    pattern: &Pattern,
    mut branches: Vec<AppliedRule>,
    trivial: Vec<TrivialApplication>,
    remainder: Option<RemainderBranch>,
) -> RewriteResult {
    match (branches.len(), trivial.is_empty(), remainder) {
        (0, false, None) => RewriteResult::Trivial(pattern.clone(), trivial),
        (1, true, None) => RewriteResult::Finished(branches.pop().unwrap()),
        (_, _, remainder) => RewriteResult::Branch {
            original: pattern.clone(),
            branches,
            remainder,
            trivial,
        },
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn rewrite_step_all(
    definition: &BackendDefinition,
    pattern: &Pattern,
    fresh_counter: &mut u64,
    simplification_options: SimplificationOptions,
    solver: &dyn SmtSolver,
    assume_initial_defined: bool,
    io: Option<&ExecutionIoState>,
) -> RewriteResult {
    let index = term_index(&pattern.term);
    let priority_groups = applicable_groups(&definition.rewrite_theory, &index);
    if priority_groups.is_empty() {
        return RewriteResult::Stuck(pattern.clone());
    }
    let mut groups = priority_groups.into_values();
    match first_productive_group(
        definition,
        pattern,
        &mut groups,
        fresh_counter,
        simplification_options,
        solver,
        assume_initial_defined,
        io,
    ) {
        PriorityGroupOutcome::NotProductive => RewriteResult::Stuck(pattern.clone()),
        PriorityGroupOutcome::Indeterminate(reason) => RewriteResult::Indeterminate {
            pattern: pattern.clone(),
            reason,
        },
        PriorityGroupOutcome::Productive {
            mut branches,
            mut trivial,
            mut remainder,
        } => {
            fold_lower_priority_groups(
                definition,
                &mut branches,
                &mut trivial,
                &mut remainder,
                groups,
                fresh_counter,
                simplification_options,
                solver,
                assume_initial_defined,
            );
            classify_first_group(pattern, branches, trivial, remainder)
        }
    }
}

/// The former lazy All-mode step, retained only as an independent differential-test oracle.
#[cfg(test)]
#[allow(clippy::too_many_arguments)]
pub(crate) fn rewrite_step_all_first_group_for_tests(
    definition: &BackendDefinition,
    pattern: &Pattern,
    fresh_counter: &mut u64,
    simplification_options: SimplificationOptions,
    solver: &dyn SmtSolver,
    assume_initial_defined: bool,
) -> RewriteResult {
    let index = term_index(&pattern.term);
    let priority_groups = applicable_groups(&definition.rewrite_theory, &index);
    if priority_groups.is_empty() {
        return RewriteResult::Stuck(pattern.clone());
    }
    match first_productive_group(
        definition,
        pattern,
        &mut priority_groups.into_values(),
        fresh_counter,
        simplification_options,
        solver,
        assume_initial_defined,
        None,
    ) {
        PriorityGroupOutcome::NotProductive => RewriteResult::Stuck(pattern.clone()),
        PriorityGroupOutcome::Indeterminate(reason) => RewriteResult::Indeterminate {
            pattern: pattern.clone(),
            reason,
        },
        PriorityGroupOutcome::Productive {
            branches,
            trivial,
            remainder,
        } => classify_first_group(pattern, branches, trivial, remainder),
    }
}

/// Complete Kore's `transitionAllRewrite` fold by feeding the remainder to each lower priority
/// group once. Applications and trivial sub-cases from later groups are retained in the same step.
/// No lower group receives execution IO because a remainder only carries constraints.
///
/// Invariant: `remainder` is the part of the parent pattern that no visited group covers.
#[allow(clippy::too_many_arguments)]
fn fold_lower_priority_groups(
    definition: &BackendDefinition,
    branches: &mut Vec<AppliedRule>,
    trivial: &mut Vec<TrivialApplication>,
    remainder: &mut Option<RemainderBranch>,
    lower_groups: impl Iterator<Item = Vec<Arc<RewriteRule>>>,
    fresh_counter: &mut u64,
    simplification_options: SimplificationOptions,
    solver: &dyn SmtSolver,
    assume_initial_defined: bool,
) {
    let mut needs_simplification = true;
    for rules in lower_groups {
        let Some(current) = remainder.as_mut() else {
            return;
        };
        if needs_simplification {
            let before = current.pattern.clone();
            match simplify_with_solver(
                definition,
                &before.term,
                &before.constraints,
                simplification_options,
                solver,
            ) {
                Ok(simplified) => {
                    current.pattern.term = simplified.term;
                    extend_unique(&mut current.pattern.constraints, simplified.constraints);
                    let effects = simplified.effects;
                    let applied_rules = simplified.applied_rules;
                    current.effects.extend(effects.iter().cloned());
                    if current.pattern != before || !applied_rules.is_empty() || !effects.is_empty()
                    {
                        current.simplifications.push(RemainderSimplification {
                            before,
                            after: current.pattern.clone(),
                            applied_rules,
                            effects,
                        });
                    }
                    if predicates_truth(&current.pattern.constraints) == Truth::False {
                        *remainder = None;
                        return;
                    }
                }
                Err(error) => {
                    current.indeterminate = Some(IndeterminateReason::simplification(None, error));
                    return;
                }
            }
            needs_simplification = false;
        }
        let current = remainder
            .as_ref()
            .expect("remainder survived simplification");
        match apply_priority_group(
            definition,
            &current.pattern,
            &rules,
            fresh_counter,
            simplification_options,
            solver,
            assume_initial_defined,
            None,
        ) {
            PriorityGroupOutcome::NotProductive => {}
            PriorityGroupOutcome::Indeterminate(reason) => {
                remainder
                    .as_mut()
                    .expect("the current remainder is present")
                    .indeterminate = Some(reason);
                return;
            }
            PriorityGroupOutcome::Productive {
                branches: mut lower,
                trivial: mut lower_trivial,
                remainder: lower_remainder,
            } => {
                let previous = remainder.take().expect("the current remainder is present");
                for application in &mut lower {
                    application
                        .remainder_simplifications
                        .splice(0..0, previous.simplifications.iter().cloned());
                }
                lower.append(branches);
                *branches = lower;
                lower_trivial.append(trivial);
                *trivial = lower_trivial;
                *remainder = lower_remainder.map(|mut next| {
                    next.effects.splice(0..0, previous.effects);
                    next.simplifications.splice(0..0, previous.simplifications);
                    next
                });
                needs_simplification = true;
            }
        }
    }
}

pub(super) fn rewrite_step_any(
    definition: &BackendDefinition,
    pattern: &Pattern,
    fresh_counter: &mut u64,
    simplification_options: SimplificationOptions,
    solver: &dyn SmtSolver,
    io: Option<&ExecutionIoState>,
) -> RewriteResult {
    let index = term_index(&pattern.term);
    let priority_groups = applicable_groups(&definition.rewrite_theory, &index);
    if priority_groups.is_empty() {
        return RewriteResult::Stuck(pattern.clone());
    }

    let mut remaining = pattern.clone();
    let mut remainder_conditions = Vec::new();
    let mut applied = Vec::new();
    let mut trivial = Vec::new();
    for rule in priority_groups.values().flatten() {
        if predicates_truth(&remaining.constraints) == Truth::False {
            break;
        }
        match apply_rule(
            definition,
            rule,
            &remaining,
            fresh_counter,
            simplification_options,
            solver,
            false,
            io,
        ) {
            RuleAttempt::NotApplicable => {}
            RuleAttempt::Unified { groups } => {
                measure::bump(Counter::RewriteRulesApplied);
                // `any` follows one deterministic collection candidate of the first applicable
                // rule.  Every right-hand-side alternative of that candidate remains a branch.
                let group = groups
                    .into_iter()
                    .next()
                    .expect("a unified rule has an application group");
                for application in group.applied {
                    extend_unique(
                        &mut remainder_conditions,
                        std::iter::once(application.remainder.clone()),
                    );
                    extend_unique(
                        &mut remaining.constraints,
                        std::iter::once(application.remainder),
                    );
                    applied.push(application.applied);
                }
                for application in group.trivial {
                    extend_unique(
                        &mut remainder_conditions,
                        std::iter::once(application.remainder.clone()),
                    );
                    extend_unique(
                        &mut remaining.constraints,
                        std::iter::once(application.remainder.clone()),
                    );
                    trivial.push(application);
                }
                match simplify_predicates_with_solver(
                    definition,
                    &remaining.constraints,
                    &pattern.constraints,
                    simplification_options,
                    solver,
                ) {
                    Ok(constraints) => {
                        remaining.constraints = pattern.constraints.clone();
                        extend_unique(&mut remaining.constraints, constraints);
                    }
                    Err(error) => {
                        return RewriteResult::Indeterminate {
                            pattern: remaining,
                            reason: IndeterminateReason::simplification(
                                Some(&rule.attributes.unique_id),
                                error,
                            ),
                        };
                    }
                }
            }
            RuleAttempt::Indeterminate(reason) => {
                return RewriteResult::Indeterminate {
                    pattern: remaining,
                    reason,
                };
            }
        }
    }

    if applied.is_empty() && trivial.is_empty() {
        return RewriteResult::Stuck(pattern.clone());
    }

    let remainder_result = if predicates_truth(&remaining.constraints) == Truth::False
        || violates_finite_constructor_domain(definition, &remaining.constraints)
    {
        Ok(Satisfiability::Unsat)
    } else {
        solver.is_sat(&remaining.constraints, &Substitution::new())
    };
    if !matches!(
        remainder_result,
        Ok(Satisfiability::Unsat | Satisfiability::Sat)
    ) {
        return RewriteResult::Indeterminate {
            pattern: pattern.clone(),
            reason: IndeterminateReason::Remainder {
                rule_ids: applied
                    .iter()
                    .map(|application| application.unique_id.clone())
                    .chain(
                        trivial
                            .iter()
                            .map(|application| application.rule_id.clone()),
                    )
                    .collect(),
                predicates: remainder_conditions,
                satisfiability: remainder_result,
            },
        };
    }
    let remainder = matches!(remainder_result, Ok(Satisfiability::Sat)).then(|| RemainderBranch {
        pattern: remaining,
        rule_ids: applied
            .iter()
            .map(|application| application.unique_id.clone())
            .chain(
                trivial
                    .iter()
                    .map(|application| application.rule_id.clone()),
            )
            .collect(),
        effects: Vec::new(),
        simplifications: Vec::new(),
        indeterminate: None,
    });
    match (applied.len(), trivial.is_empty(), remainder) {
        (0, false, None) => RewriteResult::Trivial(pattern.clone(), trivial),
        (1, true, None) => RewriteResult::Finished(applied.pop().unwrap()),
        (_, _, remainder) => RewriteResult::Branch {
            original: pattern.clone(),
            branches: applied,
            remainder,
            trivial,
        },
    }
}
