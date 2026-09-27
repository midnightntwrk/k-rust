//! ```toml algorithm
//! id = "backend.rewrite.step"
//! name = "priority-grouped rewriting with a complete remainder"
//! sites = ["rewrite_step_all", "rewrite_step_any", "apply_priority_group", "first_productive_group", "fold_lower_priority_groups", "SequentialDeterminism::record"]
//! variable = "c = candidate rules; k = sub-cases the dropped-successor tracker compares within one priority"
//! counters = ["RewriteRulesApplied"]
//! span = "per call"
//! consumes = [
//!   { type = "k_rust_backend::definition::BackendDefinition", role = "internalized theory" },
//!   { type = "k_rust_backend::rewrite::Pattern", role = "internalized pattern" },
//! ]
//! produces = [{ type = "k_rust_backend::rewrite::RewriteResult", role = "rewrite result" }]
//!
//! [[cost]]
//! mode = "All"
//! bound = "O(c) rule attempts plus one SAT check per productive group and one remainder term simplification before the first lower group and after each productive lower group"
//!
//! [[cost]]
//! mode = "Any"
//! bound = "O(c) rule attempts plus one predicate simplification per applied rule and one SAT check per step"
//!
//! [[cost]]
//! mode = "Any with dropped-successor tracking (SequentialDeterminism)"
//! bound = "the Any cost plus up to c rule attempts on the whole subject (one per candidate of a priority that already applied, including candidates after the remaining subject is refuted) and O(k^2) is_sat overlap queries, until the tracker first reports a possible drop"
//! ```
//!
//! Priority-grouped rewrite step with remainder: `All` mode folds the remainder through every
//! priority group (Kore `transitionAllRewrite`), while `Any` mode threads it through the rules
//! sequentially (Kore `applyRewriteRulesSequence`). The returned remainder is complete in both
//! modes. O(c) rule attempts per step for the c candidates of `rule::applicable_rewrite_groups`
//! plus one SAT check per productive group (`All`) or one predicate simplification per applied
//! rule and one SAT check per step (`Any`); `Counter::RewriteRulesApplied`. A one-path proof step
//! also asks `Any` whether it may have dropped a successor (`SequentialDeterminism`): a rule of a
//! priority that already applied is attempted once more on the whole subject, and the sub-cases of
//! one priority are compared pairwise for overlap.

use std::{collections::BTreeMap, sync::Arc};

use k_rust_kore::measure::{self, Algorithm, Counter};

use crate::{
    definition::BackendDefinition,
    diagnostic::{self, BackendDiagnostic, extend_distinct, in_emission_order},
    rule::{
        Predicate, RewriteRule, RuleIndex, RuleRhs, TermIndex, applicable_rewrite_groups,
        subject_index, term_index,
    },
    simplify::{SimplificationOptions, simplify_predicates_with_solver, simplify_with_solver},
    smt::{Satisfiability, SmtSolver},
    substitution::Substitution,
    transition::ExecutionIoState,
};

use super::{
    AppliedRule, IndeterminateReason, Pattern, RemainderBranch, RemainderSimplification,
    RewriteResult, RuleAttempt, TrivialApplication, Truth, UndecidedStep,
    apply::{RuleApplication, RuleApplicationGroup},
    apply_rule, extend_unique, predicates_truth, violates_finite_constructor_domain,
};

/// The outcome of one priority group. A `Productive` outcome attributes every diagnostic emitted
/// while it was computed to the candidates it concerns (`AppliedRule::diagnostics`,
/// `RemainderBranch::diagnostics`); the other outcomes attribute none, and the caller's own
/// collection holds them.
enum PriorityGroupOutcome {
    NotProductive,
    Productive {
        branches: Vec<AppliedRule>,
        trivial: Vec<TrivialApplication>,
        remainder: Option<RemainderBranch>,
    },
    Undecided(UndecidedStep),
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
    // The work every application of the group (candidate or refuted) depends on: the remainder
    // is built from the negation of each application's applicability, so it depends on all of it.
    let mut remainder_work = Vec::new();
    for rule in rules {
        // A rule attempt attributes its own work (`RuleApplicationGroup::common`,
        // `RuleApplication::diagnostics`); the work of an attempt that does not apply is on no
        // candidate's path, since no successor is derived from it.
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
                    let common = group.common.unwrap_or_default();
                    for mut application in group.applied {
                        application.applied.diagnostics =
                            in_emission_order([common.as_slice(), &application.diagnostics]);
                        applied.push(application);
                    }
                    trivial.extend(group.trivial);
                    remainder_work.extend(common);
                }
            }
            RuleAttempt::Indeterminate(reason) => {
                return PriorityGroupOutcome::Undecided(UndecidedStep::Indeterminate(reason));
            }
            RuleAttempt::Simplification(error) => {
                return PriorityGroupOutcome::Undecided(UndecidedStep::Simplification(error));
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
    let (remainder, remainder_diagnostics) = diagnostic::collect(|| {
        simplify_predicates_with_solver(
            definition,
            &raw_remainder,
            &pattern.constraints,
            simplification_options,
            solver,
        )
    });
    let remainder = match remainder {
        Ok(remainder) => remainder,
        Err(error) => {
            return PriorityGroupOutcome::Undecided(UndecidedStep::Simplification(error));
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
        return PriorityGroupOutcome::Undecided(UndecidedStep::Indeterminate(
            IndeterminateReason::Remainder {
                rule_ids,
                predicates: remainder,
                satisfiability: remainder_result,
            },
        ));
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
            diagnostics: {
                // The attempts all precede the remainder's simplification.
                let mut diagnostics = in_emission_order([remainder_work.as_slice()]);
                extend_distinct(&mut diagnostics, &remainder_diagnostics);
                diagnostics
            },
            observations: Vec::new(),
        })
    } else {
        // Without a remainder the work on it concerns no path: its conditions, possibly left
        // partially simplified, were refuted, and a refutation of an equivalent condition holds.
        None
    };
    let branches = applied
        .into_iter()
        .map(|application| application.applied)
        .collect::<Vec<_>>();
    PriorityGroupOutcome::Productive {
        branches,
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
    // An unproductive group's attempts did not apply: no successor depends on their work.
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
            outcome @ PriorityGroupOutcome::Undecided(_) => return outcome,
            outcome @ PriorityGroupOutcome::Productive { .. } => return outcome,
        }
    }
    PriorityGroupOutcome::NotProductive
}

/// Put `earlier`, the diagnostics of work every candidate was derived through and which all
/// precede the candidates' own, before each candidate's own.
fn inherit_diagnostics(
    branches: &mut [AppliedRule],
    remainder: Option<&mut RemainderBranch>,
    earlier: &[BackendDiagnostic],
) {
    if earlier.is_empty() {
        return;
    }
    let inherit = |diagnostics: &mut Vec<BackendDiagnostic>| {
        let mut inherited = earlier.to_vec();
        extend_distinct(&mut inherited, diagnostics);
        *diagnostics = inherited;
    };
    for branch in branches {
        inherit(&mut branch.diagnostics);
    }
    if let Some(remainder) = remainder {
        inherit(&mut remainder.diagnostics);
    }
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
    let _apart = crate::rule::ApartScope::enter();
    let _span = measure::algorithm_span(Algorithm::BackendRewriteStep);
    let index = term_index(&pattern.term);
    let subject = subject_index(definition, &pattern.term);
    let priority_groups = applicable_rewrite_groups(definition, &pattern.term, &subject);
    if priority_groups.is_empty() {
        return RewriteResult::Stuck(pattern.clone());
    }
    let mut groups = priority_groups.into_iter();
    let mut visited = 0;
    let outcome = first_productive_group(
        definition,
        pattern,
        &mut groups.by_ref().map(|(priority, rules)| {
            visited = priority;
            rules
        }),
        fresh_counter,
        simplification_options,
        solver,
        assume_initial_defined,
        io,
    );
    match outcome {
        PriorityGroupOutcome::NotProductive => RewriteResult::Stuck(pattern.clone()),
        PriorityGroupOutcome::Undecided(undecided) => undecided.into_result(pattern.clone()),
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
                LowerGroups {
                    selected_for: (index, subject),
                    visited,
                    groups: groups.collect(),
                },
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
    let _span = measure::algorithm_span(Algorithm::BackendRewriteStep);
    let subject = subject_index(definition, &pattern.term);
    let priority_groups = applicable_rewrite_groups(definition, &pattern.term, &subject);
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
        PriorityGroupOutcome::Undecided(undecided) => undecided.into_result(pattern.clone()),
        PriorityGroupOutcome::Productive {
            branches,
            trivial,
            remainder,
        } => classify_first_group(pattern, branches, trivial, remainder),
    }
}

/// The priority groups below the first productive one, with the rule-index keys of the term they
/// were selected for.
struct LowerGroups {
    selected_for: (TermIndex, RuleIndex),
    /// The priority of the last group applied.
    visited: u8,
    /// Every priority of the selection above `visited`, each with its candidates.
    groups: BTreeMap<u8, Vec<Arc<RewriteRule>>>,
}

/// Complete Kore's `transitionAllRewrite` fold by feeding the remainder to each lower priority
/// group once. Applications and trivial sub-cases from later groups are retained in the same step.
/// No lower group receives execution IO because a remainder only carries constraints.
///
/// The rule index drops a candidate only when matching it against the term the index keys were
/// computed from fails (`rule::rule_index`). A remainder is simplified under its own, stronger
/// path condition before a lower group sees it, and simplification can rewrite the very heads
/// the keys read: an `anywhere` equation turns an overloaded application into a different
/// constructor, a function evaluates to a constructor, a new `<k>` cell appears. So each lower
/// group's candidates are those selected for the term the group is applied to: whenever a
/// simplification changes the remainder's keys, the lower priorities are selected again for it,
/// from just above the last priority applied. Keys that did not change select the same rules.
///
/// Invariant: `remainder` is the part of the parent pattern that no visited group covers, and
/// `lower.groups` holds, for every priority above `lower.visited`, the candidates selected for
/// keys `lower.selected_for`, which are the current remainder term's once it is simplified.
#[allow(clippy::too_many_arguments)]
fn fold_lower_priority_groups(
    definition: &BackendDefinition,
    branches: &mut Vec<AppliedRule>,
    trivial: &mut Vec<TrivialApplication>,
    remainder: &mut Option<RemainderBranch>,
    mut lower: LowerGroups,
    fresh_counter: &mut u64,
    simplification_options: SimplificationOptions,
    solver: &dyn SmtSolver,
    assume_initial_defined: bool,
) {
    let mut needs_simplification = true;
    // Invariant: each pass either applies and removes one group of `lower.groups` or, at most
    // once per simplification, replaces the groups with a selection above the same `visited`,
    // after which `needs_simplification` is false until a group is applied.
    loop {
        // A priority all of whose rules the keys drop stays in the selection with no candidates
        // (`applicable_rewrite_groups` enters every priority stored under the term index), so an
        // empty selection means the term index has no priority above `visited`, whatever the
        // cell keys of a simplified remainder would be.
        if lower.groups.is_empty() {
            return;
        }
        let Some(current) = remainder.as_mut() else {
            return;
        };
        if needs_simplification {
            let before = current.pattern.clone();
            let (simplified, diagnostics) = diagnostic::collect(|| {
                simplify_with_solver(
                    definition,
                    &before.term,
                    &before.constraints,
                    simplification_options,
                    solver,
                )
            });
            extend_distinct(&mut current.diagnostics, &diagnostics);
            match simplified {
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
                    current.indeterminate = Some(UndecidedStep::Simplification(error));
                    return;
                }
            }
            needs_simplification = false;
            let keys = (
                term_index(&current.pattern.term),
                subject_index(definition, &current.pattern.term),
            );
            if keys != lower.selected_for {
                let mut groups =
                    applicable_rewrite_groups(definition, &current.pattern.term, &keys.1);
                let visited = lower.visited;
                groups.retain(|priority, _| *priority > visited);
                lower.groups = groups;
                lower.selected_for = keys;
                continue;
            }
        }
        let (priority, rules) = lower
            .groups
            .pop_first()
            .expect("the loop continues only while a group is left");
        lower.visited = priority;
        let current = remainder
            .as_ref()
            .expect("remainder survived simplification");
        let (outcome, diagnostics) = diagnostic::collect(|| {
            apply_priority_group(
                definition,
                &current.pattern,
                &rules,
                fresh_counter,
                simplification_options,
                solver,
                assume_initial_defined,
                None,
            )
        });
        match outcome {
            // The lower group did not apply to the remainder, which goes on unchanged.
            PriorityGroupOutcome::NotProductive => {}
            PriorityGroupOutcome::Undecided(undecided) => {
                let current = remainder
                    .as_mut()
                    .expect("the current remainder is present");
                extend_distinct(&mut current.diagnostics, &diagnostics);
                current.indeterminate = Some(undecided);
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
                let mut lower_remainder = lower_remainder;
                inherit_diagnostics(&mut lower, lower_remainder.as_mut(), &previous.diagnostics);
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

/// Whether a sequential step may have dropped a successor of some configuration of its subject.
///
/// The sequential step feeds each rule only the part of the subject that no earlier rule covered,
/// follows one collection candidate per rule, and keeps one symbolic successor for a rule whose
/// right-hand side chooses a value. A configuration then loses a successor exactly when two
/// applications of the same priority cover it (the later one is fed the complement of the
/// earlier), when a rule has a second collection candidate, or when one application stands for
/// several successors. The tracker is conservative: it reports `dropped` unless each of these is
/// excluded, a pairwise disjointness by a syntactic refutation or an `Unsat` answer (an
/// abstracted query can answer `Sat` spuriously, never `Unsat`). Lower-priority rules are not
/// alternatives where a higher-priority rule applies, so only equal priorities are compared.
#[derive(Default)]
pub(super) struct SequentialDeterminism {
    pub(super) dropped: bool,
    /// The sub-cases covered so far in this step, each with its priority: the constraints of the
    /// pattern the rule was applied to and the rule's applicability there.
    covered: Vec<(u8, Vec<Predicate>)>,
}

impl SequentialDeterminism {
    fn may_overlap(left: &[Predicate], right: &[Predicate], solver: &dyn SmtSolver) -> bool {
        let mut query = left.to_vec();
        extend_unique(&mut query, right.iter().cloned());
        match predicates_truth(&query) {
            Truth::False => false,
            Truth::True => true,
            Truth::Unknown => !matches!(
                solver.is_sat(&query, &Substitution::new()),
                Ok(Satisfiability::Unsat)
            ),
        }
    }

    /// The sub-cases of `group`, each the constraints of `subject` and one applicability.
    fn sub_cases(subject: &Pattern, group: &RuleApplicationGroup) -> Vec<Vec<Predicate>> {
        group
            .applied
            .iter()
            .map(RuleApplication::applicability)
            .chain(
                group
                    .trivial
                    .iter()
                    .map(|application| application.applicability.clone()),
            )
            .map(|applicability| {
                let mut case = subject.constraints.clone();
                extend_unique(&mut case, std::iter::once(applicability));
                case
            })
            .collect()
    }

    /// Record the attempt of `rule` (priority `priority`) on `remaining`, the subject minus the
    /// sub-cases covered earlier in the step. `pattern` is the whole subject.
    #[allow(clippy::too_many_arguments)]
    fn record(
        &mut self,
        definition: &BackendDefinition,
        rule: &RewriteRule,
        priority: u8,
        pattern: &Pattern,
        remaining: &Pattern,
        attempt: &RuleAttempt,
        fresh_counter: u64,
        simplification_options: SimplificationOptions,
        solver: &dyn SmtSolver,
    ) {
        if self.dropped {
            return;
        }
        // The rule may also cover a configuration an earlier rule of its priority covered, where
        // the step did not feed it. Try it on the whole subject, on a copy of the fresh-name
        // counter so that the step's own names do not move.
        if self.covered.iter().any(|(earlier, _)| *earlier == priority) {
            let mut counter = fresh_counter;
            match apply_rule(
                definition,
                rule,
                pattern,
                &mut counter,
                simplification_options,
                solver,
                false,
                None,
            ) {
                RuleAttempt::NotApplicable => {}
                RuleAttempt::Indeterminate(_) | RuleAttempt::Simplification(_) => {
                    self.dropped = true;
                    return;
                }
                RuleAttempt::Unified { groups } => {
                    for group in &groups {
                        for case in Self::sub_cases(pattern, group) {
                            if self.covered.iter().any(|(earlier, covered)| {
                                *earlier == priority && Self::may_overlap(covered, &case, solver)
                            }) {
                                self.dropped = true;
                                return;
                            }
                        }
                    }
                }
            }
        }
        let RuleAttempt::Unified { groups } = attempt else {
            return;
        };
        let [group] = groups.as_slice() else {
            self.dropped = true;
            return;
        };
        if !rule_has_one_successor(rule) {
            self.dropped = true;
            return;
        }
        let cases = Self::sub_cases(remaining, group);
        for (position, case) in cases.iter().enumerate() {
            if cases[..position]
                .iter()
                .any(|earlier| Self::may_overlap(earlier, case, solver))
            {
                self.dropped = true;
                return;
            }
        }
        self.covered
            .extend(cases.into_iter().map(|case| (priority, case)));
    }
}

/// A rule instance has one successor: its right-hand side is one term over the variables its
/// left-hand side binds, with no existential and no variable only the right-hand side or the
/// ensures clause mention.
fn rule_has_one_successor(rule: &RewriteRule) -> bool {
    let RuleRhs::Term(rhs) = &rule.rhs else {
        return false;
    };
    let bound = &rule.lhs.attributes().variables;
    rule.existentials.is_empty()
        && rhs.attributes().variables.is_subset(bound)
        && rule.ensures.iter().all(|predicate| {
            predicate
                .free_variables()
                .iter()
                .all(|variable| bound.contains(variable))
        })
}

#[allow(clippy::too_many_arguments)]
pub(super) fn rewrite_step_any(
    definition: &BackendDefinition,
    pattern: &Pattern,
    fresh_counter: &mut u64,
    simplification_options: SimplificationOptions,
    solver: &dyn SmtSolver,
    io: Option<&ExecutionIoState>,
    mut determinism: Option<&mut SequentialDeterminism>,
) -> RewriteResult {
    let _apart = crate::rule::ApartScope::enter();
    let _span = measure::algorithm_span(Algorithm::BackendRewriteStep);
    let subject = subject_index(definition, &pattern.term);
    let priority_groups = applicable_rewrite_groups(definition, &pattern.term, &subject);
    if priority_groups.is_empty() {
        return RewriteResult::Stuck(pattern.clone());
    }

    // Invariant: `remaining` narrows only the constraints of `pattern`, never its term, so the
    // rules selected for `pattern.term` above are the candidates for every attempt below and for
    // the dropped-successor tracker, which attempts rules on `pattern` itself.
    let mut remaining = pattern.clone();
    let mut remainder_conditions = Vec::new();
    let mut applied = Vec::new();
    let mut trivial = Vec::new();
    // Diagnostics of the work on `remaining`: every later candidate and the remainder, all
    // derived from it, share them.
    let mut remaining_diagnostics = Vec::new();
    let rules = priority_groups
        .iter()
        .flat_map(|(priority, rules)| rules.iter().map(move |rule| (*priority, rule)));
    for (priority, rule) in rules {
        if predicates_truth(&remaining.constraints) == Truth::False {
            // Nothing is left to feed the later rules; the tracker still asks whether they
            // cover a configuration an earlier rule took.
            if let Some(determinism) = determinism.as_deref_mut() {
                determinism.record(
                    definition,
                    rule,
                    priority,
                    pattern,
                    &remaining,
                    &RuleAttempt::NotApplicable,
                    *fresh_counter,
                    simplification_options,
                    solver,
                );
                continue;
            }
            break;
        }
        let attempt = apply_rule(
            definition,
            rule,
            &remaining,
            fresh_counter,
            simplification_options,
            solver,
            false,
            io,
        );
        if let Some(determinism) = determinism.as_deref_mut() {
            determinism.record(
                definition,
                rule,
                priority,
                pattern,
                &remaining,
                &attempt,
                *fresh_counter,
                simplification_options,
                solver,
            );
        }
        match attempt {
            RuleAttempt::NotApplicable => {}
            RuleAttempt::Unified { groups } => {
                measure::bump(Counter::RewriteRulesApplied);
                // `any` follows one deterministic collection candidate of the first applicable
                // rule; the other groups' work belongs to candidates it does not follow.
                let group = groups
                    .into_iter()
                    .next()
                    .expect("a unified rule has an application group");
                let common = group.common.unwrap_or_default();
                for application in group.applied {
                    extend_unique(
                        &mut remainder_conditions,
                        std::iter::once(application.remainder.clone()),
                    );
                    extend_unique(
                        &mut remaining.constraints,
                        std::iter::once(application.remainder),
                    );
                    // The work on `remaining` so far precedes this attempt.
                    let mut candidate = application.applied;
                    let mut diagnostics = remaining_diagnostics.clone();
                    extend_distinct(
                        &mut diagnostics,
                        &in_emission_order([common.as_slice(), &application.diagnostics]),
                    );
                    candidate.diagnostics = diagnostics;
                    applied.push(candidate);
                }
                // `remaining` is narrowed by the negation of this group's applicability.
                extend_distinct(
                    &mut remaining_diagnostics,
                    &in_emission_order([common.as_slice()]),
                );
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
                let (constraints, diagnostics) = diagnostic::collect(|| {
                    simplify_predicates_with_solver(
                        definition,
                        &remaining.constraints,
                        &pattern.constraints,
                        simplification_options,
                        solver,
                    )
                });
                extend_distinct(&mut remaining_diagnostics, &diagnostics);
                match constraints {
                    Ok(constraints) => {
                        remaining.constraints = pattern.constraints.clone();
                        extend_unique(&mut remaining.constraints, constraints);
                    }
                    Err(error) => {
                        return RewriteResult::Simplification {
                            pattern: remaining,
                            error,
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
            RuleAttempt::Simplification(error) => {
                return RewriteResult::Simplification {
                    pattern: remaining,
                    error,
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
        diagnostics: remaining_diagnostics,
        observations: Vec::new(),
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
