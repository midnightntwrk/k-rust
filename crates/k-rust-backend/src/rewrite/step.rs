//! Priority-grouped rewrite step with remainder: `All` mode applies the first productive priority
//! group and SAT-checks path ∧ ¬(∨ applicability) (Booster rewriteStep); `cascade_remainder`
//! continues Kore's `transitionAllRewrite` fold through the lower groups for stopped-branch
//! execution, each group once on the remainder of the groups before it; `Any` mode threads the
//! remainder through the rules sequentially (Kore applyRewriteRulesSequence). O(c) rule attempts
//! per step for the c candidates of `rule::applicable_groups` in every mode plus one SAT check per
//! productive group (`All`) or per applied rule (`Any`); `Counter::RewriteRulesApplied` (row B10).

use std::sync::Arc;

use k_rust_kore::measure::{self, Counter};

use crate::{
    definition::BackendDefinition,
    rule::{RewriteRule, applicable_groups, term_index},
    simplify::{SimplificationError, SimplificationOptions, simplify_predicates_with_solver},
    smt::{Satisfiability, SmtSolver},
    substitution::Substitution,
    transition::ExecutionIoState,
};

use super::{
    AppliedRule, IndeterminateReason, Pattern, RemainderBranch, RewriteResult, RuleAttempt,
    TrivialApplication, Truth, apply_rule, extend_unique, predicates_truth,
    violates_finite_constructor_domain,
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

/// Whether an `All` step hands back the priority groups it left unvisited.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum RemainderPolicy {
    /// Return at the first productive group; the caller owns the remainder (search, proof,
    /// `ExploreAll`, and the public entry points). The returned groups are always empty.
    Return,
    /// Return at the first productive group and hand back the lower groups so stopped-branch
    /// execution can cascade the remainder through them once (Kore `transitionAllRewrite`).
    Cascade,
}

/// The priority groups after the first productive one, ascending, each in declaration order;
/// empty when no group was productive, the step was `Indeterminate`, or the policy was `Return`.
/// Moved out of the `applicable_groups` map: no rule is cloned.
#[derive(Debug, Default)]
pub(super) struct LowerPriorityGroups(Vec<Vec<Arc<RewriteRule>>>);

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
    policy: RemainderPolicy,
) -> (RewriteResult, LowerPriorityGroups) {
    let index = term_index(&pattern.term);
    let priority_groups = applicable_groups(&definition.rewrite_theory, &index);
    if priority_groups.is_empty() {
        return (
            RewriteResult::Stuck(pattern.clone()),
            LowerPriorityGroups::default(),
        );
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
        PriorityGroupOutcome::NotProductive => (
            RewriteResult::Stuck(pattern.clone()),
            LowerPriorityGroups::default(),
        ),
        PriorityGroupOutcome::Indeterminate(reason) => (
            RewriteResult::Indeterminate {
                pattern: pattern.clone(),
                reason,
            },
            LowerPriorityGroups::default(),
        ),
        PriorityGroupOutcome::Productive {
            branches,
            trivial,
            remainder,
        } => {
            let result = classify_first_group(pattern, branches, trivial, remainder);
            let lower_groups = if policy == RemainderPolicy::Cascade {
                LowerPriorityGroups(groups.collect())
            } else {
                LowerPriorityGroups::default()
            };
            (result, lower_groups)
        }
    }
}

/// Continue Kore's `transitionAllRewrite` from the group after the first productive one: feed
/// `remainder` to each lower group in turn, once. A productive lower group's applications are
/// prepended to `branches` and its remainder replaces `remainder`; its trivial sub-cases are
/// dropped (as the replay dropped them). A group that is not productive leaves both unchanged. A
/// `Stuck` tail, or a lower-group `Indeterminate` other than a simplification error, keeps the
/// remainder and ends the cascade; a simplification error is the caller's `Simplification` leaf.
/// No lower group receives execution IO: a remainder carries constraints. At most one attempt per
/// candidate rule per step (row B10). Invariant: `remainder` is the part of the parent pattern that
/// `branches` does not cover, restricted to the groups visited so far.
#[allow(clippy::too_many_arguments)]
pub(super) fn cascade_remainder(
    definition: &BackendDefinition,
    branches: &mut Vec<AppliedRule>,
    remainder: &mut Option<RemainderBranch>,
    lower_groups: LowerPriorityGroups,
    fresh_counter: &mut u64,
    simplification_options: SimplificationOptions,
    solver: &dyn SmtSolver,
    assume_initial_defined: bool,
) -> Result<(), SimplificationError> {
    for rules in lower_groups.0 {
        let Some(current) = remainder.as_ref() else {
            return Ok(());
        };
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
            PriorityGroupOutcome::Indeterminate(IndeterminateReason::Simplification {
                error,
                ..
            }) => return Err(error),
            PriorityGroupOutcome::Indeterminate(_) => return Ok(()),
            PriorityGroupOutcome::Productive {
                branches: mut lower,
                trivial: _,
                remainder: lower_remainder,
            } => {
                lower.append(branches);
                *branches = lower;
                *remainder = lower_remainder;
            }
        }
    }
    Ok(())
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
