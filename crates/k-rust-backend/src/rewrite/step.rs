//! Priority-grouped rewrite step with remainder: `All` mode applies a whole priority group and
//! SAT-checks path ∧ ¬(∨ applicability) (Booster rewriteStep); `Any` mode threads the remainder
//! through the rules sequentially (Kore applyRewriteRulesSequence). O(c) rule attempts per step
//! for the c candidates of `rule::applicable_groups` plus one SAT check per step (`All`) or per
//! applied rule (`Any`); `Counter::RewriteRulesApplied` (row B10).

use k_rust_kore::measure::{self, Counter};

use crate::{
    definition::BackendDefinition,
    rule::{applicable_groups, term_index},
    simplify::{SimplificationOptions, simplify_predicates_with_solver},
    smt::{Satisfiability, SmtSolver},
    substitution::Substitution,
    transition::ExecutionIoState,
};

use super::{
    IndeterminateReason, Pattern, RemainderBranch, RewriteResult, RuleAttempt, Truth, apply_rule,
    extend_unique, predicates_truth, violates_finite_constructor_domain,
};

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
    for rules in priority_groups.values() {
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
                    return RewriteResult::Indeterminate {
                        pattern: pattern.clone(),
                        reason,
                    };
                }
            }
        }
        if applied.is_empty() && trivial.is_empty() {
            continue;
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
                return RewriteResult::Indeterminate {
                    pattern: pattern.clone(),
                    reason: IndeterminateReason::simplification(None, error),
                };
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
            return RewriteResult::Indeterminate {
                pattern: pattern.clone(),
                reason: IndeterminateReason::Remainder {
                    rule_ids,
                    predicates: remainder,
                    satisfiability: remainder_result,
                },
            };
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
        return match (applied.len(), trivial.is_empty(), remainder) {
            (0, false, None) => RewriteResult::Trivial(pattern.clone(), trivial),
            (1, true, None) => RewriteResult::Finished(applied.pop().unwrap().applied),
            (_, _, remainder) => RewriteResult::Branch {
                original: pattern.clone(),
                branches: applied
                    .into_iter()
                    .map(|application| application.applied)
                    .collect(),
                remainder,
                trivial,
            },
        };
    }
    RewriteResult::Stuck(pattern.clone())
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
