//! ```toml algorithm
//! id = "backend.rewrite.apply"
//! name = "one-rule conditional rewriting"
//! sites = ["apply_rule_with_match", "apply_rule", "apply_rule_phases", "reenter", "dispatch_match", "instantiate"]
//! variable = "r = unmatched remainder pairs; a = right-hand-side alternatives of the rule; f = partial matches returned by one recovery split"
//! counters = ["RewriteRuleAttempts", "RewriteMatchFailures", "SmtQueries"]
//! span = "per call"
//! consumes = [
//!   { type = "k_rust_backend::matching::MatchResult", role = "match result" },
//!   { type = "k_rust_backend::substitution::Substitution", role = "extracted substitution" },
//! ]
//!
//! [[cost]]
//! mode = "direct match"
//! bound = "one matching problem, at most one is_sat query, and at most 1 + 2a decide_condition calls of up to three solver queries each per attempt"
//!
//! [[cost]]
//! mode = "indeterminate recovery"
//! bound = "up to eleven recovery strategies with recursion depth at most |r| + 1 below one renaming-apart re-entry, each split re-entering once for each of its f partial matches"
//! ```
//!
//! One-rule conditional rewriting step (Booster applyRule with a Kore-style unification
//! fallback): match, recovery ladder, condition simplification, definedness, SAT narrowing,
//! requires, validity, applicability, RHS instantiation, the thirteen phases P1 to P13 of
//! `apply_rule_with_match`. Cost: one matching problem per attempt; on an indeterminate match up
//! to eleven recovery strategies, each re-entering once per split with an empty or strictly
//! shorter remainder (recursion depth <= |remainder| + 1, below the one re-entry with the rule
//! renamed apart from the subject); up to three SMT calls per attempt.
//! `Counter::RewriteRuleAttempts`, `Counter::RewriteMatchFailures`, `Counter::SmtQueries`;
//! O(c) attempts per step for the c candidates the step hands over.

// The phase functions return `Phase<T>` (below), whose `Err` is the `RuleAttempt` itself.
#![allow(clippy::result_large_err)]

use std::{cell::RefCell, collections::BTreeSet, ops::Range, sync::Arc};

use k_rust_kore::measure::{self, Algorithm, Counter};

use crate::{
    builtin::BuiltinEffect,
    definedness::ceil_term,
    definition::BackendDefinition,
    diagnostic::{self, Sequenced},
    fresh::freshen_existential,
    ite::SplitSide,
    matching::{MatchMode, MatchResult, match_terms_in_definition},
    rule::{Predicate, RewriteRule, RuleRhs, rename_apart},
    simplify::{
        BudgetPolicy, ConditionIndeterminacy, RuleCondition, SimplificationError,
        SimplificationOptions, binds_element_variable_to_set_pattern, decide_condition,
        simplify_condition, simplify_in_execution_with_solver, simplify_predicates_with_solver,
        simplify_with_solver,
    },
    smt::{Satisfiability, SmtError, SmtSolver, Validity},
    substitution::{Substitution, compose, extract_substitution, substitute},
    term::{Sort, Symbol, Term, TermKind, Variable},
    transition::ExecutionIoState,
};

use super::{
    AppliedRule, GeneralUnificationRecovery, IndeterminateReason, Pattern, TrivialApplication,
    TrivialKind, Truth, collection_unification_definedness,
    conjunctively_contains_alpha_equivalent, extend_unique, freshen_unbound_rule_variables,
    pattern_variable_names, predicates_truth, quantify_introduced_variables,
    recover_boolean_matches, recover_equality_matches, recover_function_equality_match,
    recover_functional_symbolic_match, recover_general_unification, recover_indeterminate_match,
    recover_ite_matches, recover_map_not_in_keys_matches, recover_overload_symbolic_match,
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
    /// Simplifying a term or condition of the rule failed, so the attempt could not be decided.
    Simplification(SimplificationError),
}

/// The applications of one sub-case of a rule attempt: one match (after any split) whose
/// conditions were decided once and whose right-hand-side alternatives were each instantiated.
pub(super) struct RuleApplicationGroup {
    pub(super) applied: Vec<RuleApplication>,
    pub(super) trivial: Vec<TrivialApplication>,
    /// The diagnostics of the attempt's work this sub-case's result depends on: the matching
    /// and recovery that led to it (including the splits above it) and the simplification and
    /// decision of its conditions. Its applications' candidates and the remainder its
    /// applicability is negated into are derived from that work. `None` until the attempt
    /// level that built the group attributes it (`apply_rule_with_match`).
    pub(super) common: Option<Vec<Sequenced>>,
    /// The diagnostics of the own construction of the right-hand-side alternatives refuted to
    /// bottom: no candidate derives from that work, but the `Trivial` leaf of each does.
    pub(super) trivial_work: Vec<Sequenced>,
}

pub(super) struct RuleApplication {
    pub(super) applied: AppliedRule,
    pub(super) remainder: Predicate,
    /// The sub-case of the subject where this application has a defined result: the existential
    /// closure, over the variables the pattern does not have (those the match introduced and
    /// the freshened existentials), of the applicability and the carried result condition.
    /// Equal to the applicability when nothing was carried.
    pub(super) defined: Predicate,
    /// The carried result condition, when the application's sub-case has instances outside
    /// `defined`: the obligation its `Carried` trivial entry reports.
    pub(super) carried: Option<Predicate>,
    /// The diagnostics of this right-hand-side alternative's own construction; its group's
    /// `common` work is not in it.
    pub(super) diagnostics: Vec<Sequenced>,
}

impl RuleApplication {
    /// The sub-case of the subject this application covers, the complement of `remainder`
    /// (the inverse of `remainder_of`).
    pub(super) fn applicability(&self) -> Predicate {
        match &self.remainder {
            Predicate::False => Predicate::True,
            Predicate::Not(applicability) => (**applicability).clone(),
            remainder => Predicate::Not(Box::new(remainder.clone())),
        }
    }
}

fn remainder_of(applicability: &Predicate) -> Predicate {
    if *applicability == Predicate::True {
        Predicate::False
    } else {
        Predicate::Not(Box::new(applicability.clone()))
    }
}

/// The `Refuted` entry of an application whose result is bottom on its whole sub-case
/// `applicability` of `pattern`.
fn trivial_application(
    rule: &RewriteRule,
    pattern: &Pattern,
    applicability: &Predicate,
    obligation: Predicate,
    effects: Vec<BuiltinEffect>,
) -> TrivialApplication {
    TrivialApplication {
        rule_id: rule.attributes.unique_id.clone(),
        label: rule.attributes.label.clone(),
        kind: TrivialKind::Refuted,
        obligation,
        applicability: applicability.clone(),
        remainder: remainder_of(applicability),
        undefined: applicability.clone(),
        before: pattern.clone(),
        effects,
        diagnostics: Vec::new(),
        remainder_simplifications: Vec::new(),
    }
}

/// The `Carried` entry of `application`, whose carried result condition `obligation` leaves the
/// instances of its sub-case `applicability` outside `application.defined` without a result.
fn carried_trivial_application(
    rule: &RewriteRule,
    pattern: &Pattern,
    applicability: &Predicate,
    application: &RuleApplication,
    obligation: Predicate,
) -> TrivialApplication {
    let undefined = conjoin_flat([applicability.clone(), negation(&application.defined)]);
    TrivialApplication {
        rule_id: rule.attributes.unique_id.clone(),
        label: rule.attributes.label.clone(),
        kind: TrivialKind::Carried,
        obligation,
        applicability: undefined.clone(),
        remainder: remainder_of(applicability),
        undefined,
        before: pattern.clone(),
        effects: application.applied.effects.clone(),
        diagnostics: Vec::new(),
        remainder_simplifications: Vec::new(),
    }
}

/// Restrict each entry of `trivial` to the instances that no applied candidate of its priority
/// group (`applied`) takes to a defined successor: `undefined` becomes the entry's
/// `applicability` conjoined with `not D_j` for each candidate `j`.
pub(super) fn restrict_to_undefined(
    trivial: &mut [TrivialApplication],
    applied: &[RuleApplication],
) {
    for entry in trivial {
        entry.undefined = conjoin_flat(
            std::iter::once(entry.applicability.clone())
                .chain(applied.iter().map(|sibling| negation(&sibling.defined))),
        );
    }
}

/// `not predicate`, with the double negation and the constants folded.
fn negation(predicate: &Predicate) -> Predicate {
    match predicate {
        Predicate::True => Predicate::False,
        Predicate::False => Predicate::True,
        Predicate::Not(inner) => (**inner).clone(),
        predicate => Predicate::Not(Box::new(predicate.clone())),
    }
}

/// The conjunction of `predicates` with nested conjunctions flattened, `True` and repeated
/// conjuncts dropped, and `False` absorbing, as does a conjunct beside its own negation.
fn conjoin_flat(predicates: impl IntoIterator<Item = Predicate>) -> Predicate {
    fn flatten(predicate: Predicate, conjuncts: &mut Vec<Predicate>) {
        match predicate {
            Predicate::And(inner) => {
                for predicate in inner {
                    flatten(predicate, conjuncts);
                }
            }
            Predicate::True => {}
            predicate => {
                if !conjuncts.contains(&predicate) {
                    conjuncts.push(predicate);
                }
            }
        }
    }
    let mut conjuncts = Vec::new();
    for predicate in predicates {
        flatten(predicate, &mut conjuncts);
    }
    let contradictory = conjuncts.iter().any(|conjunct| {
        *conjunct == Predicate::False
            || matches!(conjunct, Predicate::Not(inner) if conjuncts.contains(inner))
    });
    if contradictory {
        return Predicate::False;
    }
    conjunction(&conjuncts)
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

#[allow(clippy::too_many_arguments)]
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

/// What every phase of a rule attempt reads and none of them changes.
#[derive(Clone, Copy)]
struct RuleContext<'a> {
    definition: &'a BackendDefinition,
    rule: &'a RewriteRule,
    pattern: &'a Pattern,
    simplification_options: SimplificationOptions,
    solver: &'a dyn SmtSolver,
    assume_initial_defined: bool,
    io: Option<&'a ExecutionIoState>,
    /// The emission-position ranges of this attempt level's nested units of work (re-entered
    /// sub-attempts and right-hand-side alternatives), which attribute their own diagnostics.
    nested_units: &'a RefCell<Vec<Range<u64>>>,
}

impl RuleContext<'_> {
    /// Run `work` as a nested unit of this attempt level.
    fn nested<T>(&self, work: impl FnOnce() -> T) -> T {
        let start = diagnostic::next_position();
        let result = work();
        self.nested_units
            .borrow_mut()
            .push(start..diagnostic::next_position());
        result
    }
}

/// A phase either hands its result to the next phase or ends the attempt with the
/// `RuleAttempt` the caller reports. The exit is the attempt itself and not a boxed one: the
/// `NotApplicable` exit is the hottest path of the step (`Counter::RewriteMatchFailures`), and
/// an allocation per failed attempt would be a cost no phase needs.
type Phase<T> = Result<T, RuleAttempt>;

/// Invariant: every re-entry (the six recovery splits, the unification solutions, and the
/// bindings extracted from conditions) carries the accumulated `inherited_conditions`, which
/// only grow, and either an empty or strictly shorter `remainder` or a binding of a previously
/// unbound `lhs` variable, so the recursion depth is at most |remainder| + 1 and the
/// constructor-like re-entry cannot repeat. Before them, an attempt without a partial match
/// re-enters at most once with the rule renamed apart from the subject; the renamed rule meets
/// no scope variable, so it is not renamed again, and that re-entry counts no attempt.
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
    // A partial match was computed against the rule this attempt already applies, which is
    // renamed apart from the subject when it had to be.
    if matched.is_none()
        && let Some((renamed, _)) = rename_apart(
            rule,
            &pattern.term.attributes().variables,
            &pattern.constraints,
        )
    {
        return apply_rule_with_match(
            definition,
            &renamed,
            pattern,
            fresh_counter,
            simplification_options,
            solver,
            assume_initial_defined,
            None,
            io,
        );
    }
    let _span = measure::algorithm_span(Algorithm::BackendRewriteApply);
    measure::bump(Counter::RewriteRuleAttempts);
    let nested_units = RefCell::new(Vec::new());
    let context = RuleContext {
        definition,
        rule,
        pattern,
        simplification_options,
        solver,
        assume_initial_defined,
        io,
        nested_units: &nested_units,
    };
    let (mut attempt, level) =
        diagnostic::collect_unit(
            || match apply_rule_phases(context, fresh_counter, matched) {
                Ok(attempt) | Err(attempt) => attempt,
            },
        );
    // This level's own work (matching, recovery, conditions) is every emission outside its
    // nested units. Every group of the attempt, built here or by a sub-attempt re-entered from
    // here, depends on it. An attempt that produced no group attributes it to no candidate.
    if let RuleAttempt::Unified { groups } = &mut attempt {
        let nested_units = nested_units.into_inner();
        let own = level
            .into_iter()
            .filter(|sequenced| {
                !nested_units
                    .iter()
                    .any(|unit| unit.contains(&sequenced.position))
            })
            .collect::<Vec<_>>();
        for group in groups {
            group.common = Some(match group.common.take() {
                None => own.clone(),
                Some(nested) => diagnostic::merge_units(&[&own, &nested]),
            });
        }
    }
    attempt
}

/// The thirteen phases P1 to P13 in order; each phase's postcondition is what the next may
/// assume.
fn apply_rule_phases(
    context: RuleContext<'_>,
    fresh_counter: &mut u64,
    matched: Option<PartialRuleMatch>,
) -> Phase<RuleAttempt> {
    let (matching, mut inherited_conditions) = initial_match(context, matched);
    let (path_knowledge, mut inherited_knowledge) = knowledge(context, &inherited_conditions);
    let (mut substitution, mut match_conditions) = dispatch_match(
        context,
        fresh_counter,
        matching,
        &mut inherited_conditions,
        &mut inherited_knowledge,
    )?;
    if binds_element_variable_to_set_pattern(&substitution) {
        return Err(RuleAttempt::Indeterminate(IndeterminateReason::Match {
            rule_id: context.rule.attributes.unique_id.clone(),
            substitution,
            remainder: Vec::new(),
        }));
    }
    configuration_bindings(context, &mut substitution, &mut match_conditions);
    let mut match_conditions = simplify_conditions(
        context,
        inherited_conditions,
        match_conditions,
        &path_knowledge,
    )?;
    definedness(
        context,
        &substitution,
        &path_knowledge,
        &mut match_conditions,
    )?;
    narrowing_sat(context, &match_conditions)?;
    let (requires, match_knowledge) = requires(
        context,
        fresh_counter,
        &substitution,
        &match_conditions,
        path_knowledge,
    )?;
    let (unclear_requires, applicability) =
        validity_and_applicability(context, requires, &match_knowledge, &match_conditions)?;
    instantiate(
        context,
        substitution,
        match_conditions,
        match_knowledge,
        unclear_requires,
        applicability,
    )
}

/// Re-enter the attempt with a partial match, the recursion of the invariant above.
fn reenter(
    context: RuleContext<'_>,
    fresh_counter: &mut u64,
    matched: PartialRuleMatch,
) -> RuleAttempt {
    context.nested(|| {
        apply_rule_with_match(
            context.definition,
            context.rule,
            context.pattern,
            fresh_counter,
            context.simplification_options,
            context.solver,
            context.assume_initial_defined,
            Some(matched),
            context.io,
        )
    })
}

/// P1: the match of `rule.lhs` against the subject in `Rewrite` mode, or the caller's partial
/// match rebuilt as `Success` / `Indeterminate`; the caller's conditions come with it.
/// ```toml algorithm-site
/// id = "backend.matching.syntactic"
/// role = "part"
/// sites = ["initial_match"]
/// ```
fn initial_match(
    context: RuleContext<'_>,
    matched: Option<PartialRuleMatch>,
) -> (MatchResult, Vec<Predicate>) {
    if let Some(matched) = matched {
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
            match_terms_in_definition(
                MatchMode::Rewrite,
                context.definition,
                &context.rule.lhs,
                &context.pattern.term,
            ),
            Vec::new(),
        )
    }
}

/// P2: `path_knowledge` is the path (plus `ceil(subject)` when the initial subject is assumed
/// defined); `inherited_knowledge` adds the inherited conditions; both duplicate-free.
fn knowledge(
    context: RuleContext<'_>,
    inherited_conditions: &[Predicate],
) -> (Vec<Predicate>, Vec<Predicate>) {
    let mut path_knowledge = context.pattern.constraints.clone();
    if context.assume_initial_defined {
        extend_unique(
            &mut path_knowledge,
            ceil_term(context.definition, &context.pattern.term),
        );
    }
    let mut inherited_knowledge = path_knowledge.clone();
    extend_unique(
        &mut inherited_knowledge,
        inherited_conditions.iter().cloned(),
    );
    (path_knowledge, inherited_knowledge)
}

/// P3: `Failed` ends the attempt (`Counter::RewriteMatchFailures`), `Success` yields the
/// substitution with no match conditions, `Indeterminate` goes through the recovery ladder
/// (P4 to P6).
fn dispatch_match(
    context: RuleContext<'_>,
    fresh_counter: &mut u64,
    matching: MatchResult,
    inherited_conditions: &mut Vec<Predicate>,
    inherited_knowledge: &mut Vec<Predicate>,
) -> Phase<(Substitution, Vec<Predicate>)> {
    match matching {
        MatchResult::Failed(_) => {
            measure::bump(Counter::RewriteMatchFailures);
            Err(RuleAttempt::NotApplicable)
        }
        MatchResult::Indeterminate {
            substitution,
            remainder,
        } => {
            let recovered = recover_by_simplification(
                context,
                substitution,
                remainder,
                inherited_conditions,
                inherited_knowledge,
            )?;
            match recovered {
                MatchResult::Failed(_) => {
                    measure::bump(Counter::RewriteMatchFailures);
                    Err(RuleAttempt::NotApplicable)
                }
                MatchResult::Success(substitution) => Ok((substitution, Vec::new())),
                MatchResult::Indeterminate {
                    substitution,
                    remainder,
                } => {
                    if let Some(attempt) = recover_by_split(
                        context,
                        fresh_counter,
                        &substitution,
                        &remainder,
                        inherited_conditions,
                    ) {
                        return Err(attempt);
                    }
                    recover_by_unification(
                        context,
                        fresh_counter,
                        substitution,
                        remainder,
                        inherited_conditions,
                        inherited_knowledge,
                    )
                }
            }
        }
        MatchResult::Success(substitution) => Ok((substitution, Vec::new())),
    }
}

/// P4: `recover_indeterminate_match` (ladder step 0) runs once; its conditions join both
/// inherited lists; the result is `Failed`, `Success`, or an `Indeterminate` with a remainder
/// no larger than before.
fn recover_by_simplification(
    context: RuleContext<'_>,
    substitution: Substitution,
    remainder: Vec<(Term, Term)>,
    inherited_conditions: &mut Vec<Predicate>,
    inherited_knowledge: &mut Vec<Predicate>,
) -> Phase<MatchResult> {
    let recovered = match recover_indeterminate_match(
        context.definition,
        substitution,
        remainder,
        inherited_knowledge,
        context.simplification_options,
        context.solver,
    ) {
        Ok(recovered) => recovered,
        Err(error) => {
            return Err(RuleAttempt::Simplification(error));
        }
    };
    extend_unique(inherited_conditions, recovered.conditions.iter().cloned());
    extend_unique(inherited_knowledge, recovered.conditions);
    Ok(recovered.result)
}

/// P5: the six splitting strategies (boolean, symbolic map key, map-not-in-keys, equality,
/// ite, collection narrowing), each either producing partial matches that re-enter with an
/// empty or strictly shorter remainder (combined by `combine_rule_attempts`) or declining.
/// `None` means every strategy declined.
/// ```toml algorithm-site
/// id = "backend.rewrite.recover"
/// role = "part"
/// sites = ["recover_by_split", "recover_by_unification"]
/// ```
fn recover_by_split(
    context: RuleContext<'_>,
    fresh_counter: &mut u64,
    substitution: &Substitution,
    remainder: &[(Term, Term)],
    inherited_conditions: &[Predicate],
) -> Option<RuleAttempt> {
    let _span = measure::algorithm_span(Algorithm::BackendRewriteRecover);
    let definition = context.definition;
    let rule = context.rule;
    let pattern = context.pattern;
    let reenter_with = |fresh_counter: &mut u64, mut matched: PartialRuleMatch| {
        let mut conditions = inherited_conditions.to_vec();
        conditions.append(&mut matched.conditions);
        matched.conditions = conditions;
        reenter(context, fresh_counter, matched)
    };
    if let Some(matches) = recover_boolean_matches(definition, substitution.clone(), remainder) {
        return Some(combine_rule_attempts(
            matches
                .into_iter()
                .map(|matched| reenter_with(fresh_counter, matched)),
        ));
    }
    if let Some(matches) =
        recover_symbolic_map_key_matches(definition, substitution.clone(), remainder)
    {
        return Some(combine_rule_attempts(
            matches
                .into_iter()
                .map(|matched| reenter_with(fresh_counter, matched)),
        ));
    }
    if let Some(matches) = recover_map_not_in_keys_matches(
        definition,
        rule,
        pattern,
        substitution.clone(),
        remainder,
        fresh_counter,
    ) {
        return Some(combine_rule_attempts(
            matches
                .into_iter()
                .map(|matched| reenter_with(fresh_counter, matched)),
        ));
    }
    if let Some(matches) = recover_equality_matches(
        definition,
        rule,
        pattern,
        substitution.clone(),
        remainder,
        fresh_counter,
    ) {
        return Some(combine_rule_attempts(
            matches
                .into_iter()
                .map(|matched| reenter_with(fresh_counter, matched)),
        ));
    }
    if let Some(matches) = recover_ite_matches(definition, substitution.clone(), remainder) {
        return Some(combine_rule_attempts(
            matches
                .into_iter()
                .map(|matched| reenter_with(fresh_counter, matched)),
        ));
    }
    if let Some(matches) = solve_collection_remainders_with_narrowing(
        definition,
        pattern,
        substitution.clone(),
        remainder,
        fresh_counter,
    ) {
        if matches.is_empty() {
            return Some(RuleAttempt::NotApplicable);
        }
        return Some(combine_rule_attempts(matches.into_iter().map(|solution| {
            let (substitution, _) =
                freshen_unbound_rule_variables(rule, pattern, solution.substitution, fresh_counter);
            let mut conditions = inherited_conditions.to_vec();
            extend_unique(
                &mut conditions,
                substitute_predicates(&solution.constraints, &substitution),
            );
            extend_unique(
                &mut conditions,
                collection_unification_definedness(definition, remainder, &substitution),
            );
            reenter(
                context,
                fresh_counter,
                PartialRuleMatch {
                    substitution,
                    conditions,
                    remainder: Vec::new(),
                },
            )
        })));
    }
    None
}

/// P6: overload recovery, else general unification (one solution falls through as bindings
/// plus constraints, several re-enter, `Bottom` ends the attempt); when unification is
/// unsupported, the functional-symbolic and function-equality witnesses are tried, and
/// otherwise the attempt is `Indeterminate` unless the solver refutes the unclear `requires`.
fn recover_by_unification(
    context: RuleContext<'_>,
    fresh_counter: &mut u64,
    substitution: Substitution,
    remainder: Vec<(Term, Term)>,
    inherited_conditions: &[Predicate],
    inherited_knowledge: &[Predicate],
) -> Phase<(Substitution, Vec<Predicate>)> {
    let _span = measure::algorithm_span(Algorithm::BackendRewriteRecover);
    let definition = context.definition;
    let rule = context.rule;
    let pattern = context.pattern;
    if let Some(recovered) = recover_overload_symbolic_match(
        definition,
        pattern,
        substitution.clone(),
        &remainder,
        fresh_counter,
    ) {
        return Ok(recovered);
    }
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
                Ok(solutions.pop().expect("one unification solution"))
            } else {
                Err(combine_rule_attempts(solutions.into_iter().map(
                    |(substitution, mut constraints)| {
                        let mut conditions = inherited_conditions.to_vec();
                        conditions.append(&mut constraints);
                        reenter(
                            context,
                            fresh_counter,
                            PartialRuleMatch {
                                substitution,
                                conditions,
                                remainder: Vec::new(),
                            },
                        )
                    },
                )))
            }
        }
        GeneralUnificationRecovery::Bottom => Err(RuleAttempt::NotApplicable),
        GeneralUnificationRecovery::Unsupported => {
            if let Some(recovered) = recover_functional_symbolic_match(
                definition,
                rule,
                pattern,
                substitution.clone(),
                &remainder,
                fresh_counter,
            ) {
                return Ok(recovered);
            }
            if let Some(recovered) = recover_function_equality_match(
                rule,
                pattern,
                substitution.clone(),
                &remainder,
                fresh_counter,
            ) {
                return Ok(recovered);
            }
            let requires = match simplify_rule_condition(
                definition,
                substitute_predicates(&rule.requires, &substitution),
                inherited_knowledge,
                context.simplification_options,
                context.solver,
            ) {
                Ok(requires) => requires,
                Err(error) => {
                    return Err(RuleAttempt::Simplification(error));
                }
            };
            if predicates_truth(&requires) == Truth::False {
                return Err(RuleAttempt::NotApplicable);
            }
            let unclear = requires
                .into_iter()
                .filter(|predicate| {
                    predicates_truth(std::slice::from_ref(predicate)) == Truth::Unknown
                        && !inherited_knowledge.contains(predicate)
                })
                .collect::<Vec<_>>();
            if !unclear.is_empty()
                && matches!(
                    context.solver.check_predicates(
                        inherited_knowledge,
                        &Substitution::new(),
                        &unclear,
                    ),
                    Ok(Validity::Invalid)
                )
            {
                return Err(RuleAttempt::NotApplicable);
            }
            Err(RuleAttempt::Indeterminate(IndeterminateReason::Match {
                rule_id: rule.attributes.unique_id.clone(),
                substitution,
                remainder,
            }))
        }
    }
}

/// P7: the substitution binds only `rule.lhs` variables afterwards; every binding of a subject
/// variable became `Equals(variable, value)` plus `ceil(value)` among the match conditions.
fn configuration_bindings(
    context: RuleContext<'_>,
    substitution: &mut Substitution,
    match_conditions: &mut Vec<Predicate>,
) {
    let configuration_bindings = substitution
        .iter()
        .filter(|(variable, _)| !context.rule.lhs.attributes().variables.contains(*variable))
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
        extend_unique(match_conditions, ceil_term(context.definition, &value));
    }
}

/// P8: the inherited and match conditions simplified under the path; `False` ends the
/// attempt; what remains are the `Unknown` conditions.
fn simplify_conditions(
    context: RuleContext<'_>,
    mut inherited_conditions: Vec<Predicate>,
    mut match_conditions: Vec<Predicate>,
    path_knowledge: &[Predicate],
) -> Phase<Vec<Predicate>> {
    inherited_conditions.append(&mut match_conditions);
    let inherited_conditions = match simplify_predicates_with_solver(
        context.definition,
        &inherited_conditions,
        path_knowledge,
        context.simplification_options,
        context.solver,
    ) {
        Ok(conditions) => conditions,
        Err(error) => {
            return Err(RuleAttempt::Simplification(error));
        }
    };
    if predicates_truth(&inherited_conditions) == Truth::False {
        return Err(RuleAttempt::NotApplicable);
    }
    Ok(inherited_conditions
        .into_iter()
        .filter(|condition| predicates_truth(std::slice::from_ref(condition)) == Truth::Unknown)
        .collect::<Vec<_>>())
}

/// P9: `ceil` of every non-variable binding, simplified under the path and the match
/// conditions; `False` means the rule applies vacuously (`Unified { trivial }`); the `Unknown`
/// ones join the match conditions.
fn definedness(
    context: RuleContext<'_>,
    substitution: &Substitution,
    path_knowledge: &[Predicate],
    match_conditions: &mut Vec<Predicate>,
) -> Phase<()> {
    let mut definedness_conditions = Vec::new();
    for value in substitution
        .values()
        .filter(|value| !matches!(value.kind(), TermKind::Variable(_)))
    {
        extend_unique(
            &mut definedness_conditions,
            ceil_term(context.definition, value),
        );
    }
    let mut definedness_knowledge = path_knowledge.to_vec();
    extend_unique(&mut definedness_knowledge, match_conditions.iter().cloned());
    let definedness_conditions = match simplify_predicates_with_solver(
        context.definition,
        &definedness_conditions,
        &definedness_knowledge,
        context.simplification_options,
        context.solver,
    ) {
        Ok(conditions) => conditions,
        Err(error) => {
            return Err(RuleAttempt::Simplification(error));
        }
    };
    if predicates_truth(&definedness_conditions) == Truth::False {
        let applicability =
            quantify_introduced_variables(context.pattern, std::mem::take(match_conditions));
        return Err(RuleAttempt::Unified {
            groups: vec![RuleApplicationGroup {
                applied: Vec::new(),
                trivial: vec![trivial_application(
                    context.rule,
                    context.pattern,
                    &applicability,
                    Predicate::False,
                    Vec::new(),
                )],
                common: None,
                trivial_work: Vec::new(),
            }],
        });
    }
    extend_unique(
        match_conditions,
        definedness_conditions.into_iter().filter(|condition| {
            predicates_truth(std::slice::from_ref(condition)) == Truth::Unknown
        }),
    );
    Ok(())
}

/// P10: with match conditions present, the path plus the conditions must be satisfiable;
/// `Unsat` ends the attempt, `Unknown` or a solver error makes it `Indeterminate`.
fn narrowing_sat(context: RuleContext<'_>, match_conditions: &[Predicate]) -> Phase<()> {
    if match_conditions.is_empty() {
        return Ok(());
    }
    let mut narrowed = context.pattern.constraints.clone();
    extend_unique(&mut narrowed, match_conditions.iter().cloned());
    match context.solver.is_sat(&narrowed, &Substitution::new()) {
        Ok(Satisfiability::Sat) => Ok(()),
        Ok(Satisfiability::Unsat) => Err(RuleAttempt::NotApplicable),
        Ok(Satisfiability::Unknown(reason)) => {
            Err(RuleAttempt::Indeterminate(IndeterminateReason::Smt {
                rule_id: context.rule.attributes.unique_id.clone(),
                error: SmtError::Unknown(reason),
            }))
        }
        Err(error) => Err(RuleAttempt::Indeterminate(IndeterminateReason::Smt {
            rule_id: context.rule.attributes.unique_id.clone(),
            error,
        })),
    }
}

/// P11: `requires` under the substitution, simplified under the path plus the match
/// conditions (the `match_knowledge` returned with it); `False` ends the attempt; for a
/// constructor-like subject, bindings of still-unbound `lhs` variables found in the
/// conditions re-enter the attempt once with them composed in.
fn requires(
    context: RuleContext<'_>,
    fresh_counter: &mut u64,
    substitution: &Substitution,
    match_conditions: &[Predicate],
    path_knowledge: Vec<Predicate>,
) -> Phase<(Vec<Predicate>, Vec<Predicate>)> {
    let rule = context.rule;
    let mut match_knowledge = path_knowledge;
    extend_unique(&mut match_knowledge, match_conditions.iter().cloned());
    // The instance satisfies `requires` only where its terms are defined; state that before the
    // simplifier or a solver can answer for instances where they are not.
    let requires = match simplify_rule_condition(
        context.definition,
        substitute_predicates(&rule.requires, substitution),
        &match_knowledge,
        context.simplification_options,
        context.solver,
    ) {
        Ok(requires) => requires,
        Err(error) => {
            return Err(RuleAttempt::Simplification(error));
        }
    };
    if predicates_truth(&requires) == Truth::False {
        return Err(RuleAttempt::NotApplicable);
    }
    if context.pattern.term.concrete_after_normalization() {
        // Conditions can finish an otherwise incomplete match (for example, requires E = value).
        // Re-enter application with those bindings so the remaining functional equalities and
        // requires are simplified under the covering substitution before coverage is checked.
        let mut conditions = match_conditions.to_vec();
        extend_unique(&mut conditions, requires.iter().cloned());
        let (bindings, _) = extract_substitution(&conditions, &context.definition.sort_graph);
        let bindings = bindings
            .into_iter()
            .filter(|(variable, _)| {
                rule.lhs.attributes().variables.contains(variable)
                    && !substitution.contains_key(variable)
            })
            .collect::<Substitution>();
        if !bindings.is_empty() {
            return Err(reenter(
                context,
                fresh_counter,
                PartialRuleMatch {
                    substitution: compose(&bindings, substitution),
                    conditions: substitute_predicates(&conditions, &bindings),
                    remainder: Vec::new(),
                },
            ));
        }
    }
    Ok((requires, match_knowledge))
}

/// A rewrite rule's `requires` or `ensures`, instantiated, simplified under `known` with the
/// definedness of its Boolean terms explicit (`simplify::simplify_condition`).
fn simplify_rule_condition(
    definition: &BackendDefinition,
    conditions: Vec<Predicate>,
    known: &[Predicate],
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Result<Vec<Predicate>, SimplificationError> {
    simplify_condition(
        definition,
        conditions,
        known,
        known,
        |conditions, known, first_attempt| {
            let options = if first_attempt {
                SimplificationOptions {
                    budget: BudgetPolicy::Fail,
                    ..options
                }
            } else {
                options
            };
            simplify_predicates_with_solver(definition, &conditions, known, options, solver)
        },
    )
}

/// P12: the unclear `requires` are checked for validity (`Valid` empties them, `Invalid` ends
/// the attempt, solver trouble makes it `Indeterminate`); the applicability is the
/// existential closure of the match conditions and the unclear `requires`, and an attempt
/// whose negated applicability is already on the path (alpha-equivalently) ends.
fn validity_and_applicability(
    context: RuleContext<'_>,
    requires: Vec<Predicate>,
    match_knowledge: &[Predicate],
    match_conditions: &[Predicate],
) -> Phase<(Vec<Predicate>, Predicate)> {
    let rule = context.rule;
    let pattern = context.pattern;
    let mut unclear_requires = requires
        .into_iter()
        .filter(|predicate| {
            predicates_truth(std::slice::from_ref(predicate)) == Truth::Unknown
                && !pattern.constraints.contains(predicate)
        })
        .collect::<Vec<_>>();
    if !unclear_requires.is_empty() {
        match decide_condition(&unclear_requires, match_knowledge, context.solver) {
            Ok(RuleCondition::Satisfied) => unclear_requires.clear(),
            Ok(RuleCondition::Refuted) => return Err(RuleAttempt::NotApplicable),
            Ok(RuleCondition::Indeterminate(
                ConditionIndeterminacy::ImplicationIndeterminate
                | ConditionIndeterminacy::NonFunctionalBinding,
            )) => {}
            Ok(RuleCondition::Indeterminate(ConditionIndeterminacy::NoSolver)) => {
                return Err(RuleAttempt::Indeterminate(IndeterminateReason::Requires {
                    rule_id: rule.attributes.unique_id.clone(),
                    predicates: unclear_requires,
                }));
            }
            Ok(RuleCondition::Indeterminate(ConditionIndeterminacy::InconsistentPathCondition)) => {
                return Err(RuleAttempt::Indeterminate(IndeterminateReason::Smt {
                    rule_id: rule.attributes.unique_id.clone(),
                    error: SmtError::InconsistentGroundTruth,
                }));
            }
            Ok(RuleCondition::Indeterminate(ConditionIndeterminacy::SmtUnknown(reason))) => {
                return Err(RuleAttempt::Indeterminate(IndeterminateReason::Smt {
                    rule_id: rule.attributes.unique_id.clone(),
                    error: SmtError::Unknown(reason),
                }));
            }
            Ok(RuleCondition::Indeterminate(ConditionIndeterminacy::Untranslatable(error))) => {
                return Err(RuleAttempt::Indeterminate(IndeterminateReason::Smt {
                    rule_id: rule.attributes.unique_id.clone(),
                    error: SmtError::Translation(error),
                }));
            }
            Err(error) => {
                return Err(RuleAttempt::Indeterminate(IndeterminateReason::Smt {
                    rule_id: rule.attributes.unique_id.clone(),
                    error,
                }));
            }
        }
    }

    let mut applicability = match_conditions.to_vec();
    applicability.extend(unclear_requires.iter().cloned());
    let applicability = quantify_introduced_variables(pattern, applicability);
    if applicability != Predicate::True
        && conjunctively_contains_alpha_equivalent(
            &pattern.constraints,
            &Predicate::Not(Box::new(applicability.clone())),
        )
    {
        return Err(RuleAttempt::NotApplicable);
    }
    Ok((unclear_requires, applicability))
}

/// P13: a constructor-like subject with an unbound `lhs` variable is `Indeterminate`
/// (`Instantiation`); the existentials are freshened; every right-hand-side alternative goes
/// through `apply_rhs_alternative`, and the attempt is `Unified` with the applications and
/// trivial results collected (an `Indeterminate` alternative ends it).
fn instantiate(
    context: RuleContext<'_>,
    substitution: Substitution,
    match_conditions: Vec<Predicate>,
    match_knowledge: Vec<Predicate>,
    unclear_requires: Vec<Predicate>,
    applicability: Predicate,
) -> Phase<RuleAttempt> {
    let rule = context.rule;
    let pattern = context.pattern;
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
            return Err(RuleAttempt::Indeterminate(
                IndeterminateReason::Instantiation {
                    rule_id: rule.attributes.unique_id.clone(),
                    missing_variables,
                },
            ));
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
        RuleRhs::Top => return Err(RuleAttempt::NotApplicable),
        RuleRhs::Bottom => {
            return Err(RuleAttempt::Unified {
                groups: vec![RuleApplicationGroup {
                    applied: Vec::new(),
                    trivial: vec![trivial_application(
                        rule,
                        pattern,
                        &applicability,
                        Predicate::False,
                        Vec::new(),
                    )],
                    common: None,
                    trivial_work: Vec::new(),
                }],
            });
        }
        RuleRhs::Predicates(_) => return Err(RuleAttempt::NotApplicable),
    };
    let mut applications = Vec::new();
    let mut trivial = Vec::new();
    let mut trivial_work = Vec::new();
    for (rhs, alternative_ensures) in alternatives {
        let mut ensures = rule.ensures.clone();
        extend_unique(&mut ensures, alternative_ensures.iter().cloned());
        let (attempt, own_diagnostics) = context.nested(|| {
            diagnostic::collect_unit(|| {
                apply_rhs_alternative(
                    context.definition,
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
                    context.simplification_options,
                    context.solver,
                    context.io,
                )
            })
        });
        match attempt {
            RhsAlternativeAttempt::Applied(mut application) => {
                if let Some(obligation) = application.carried.take() {
                    trivial.push(carried_trivial_application(
                        rule,
                        pattern,
                        &applicability,
                        &application,
                        obligation,
                    ));
                }
                application.diagnostics = own_diagnostics;
                applications.push(application);
            }
            RhsAlternativeAttempt::Trivial {
                obligation,
                effects,
            } => {
                trivial.push(trivial_application(
                    rule,
                    pattern,
                    &applicability,
                    obligation,
                    effects,
                ));
                trivial_work.extend(own_diagnostics);
            }
            RhsAlternativeAttempt::Indeterminate(reason) => {
                return Err(RuleAttempt::Indeterminate(reason));
            }
            RhsAlternativeAttempt::Simplification(error) => {
                return Err(RuleAttempt::Simplification(error));
            }
        }
    }
    Ok(RuleAttempt::Unified {
        groups: vec![RuleApplicationGroup {
            applied: applications,
            trivial,
            common: None,
            trivial_work,
        }],
    })
}

// Returned once per right-hand-side alternative and unpacked at once; `Applied` is the common
// variant, and boxing it would add an allocation per candidate to save stack in a short-lived value.
#[allow(clippy::large_enum_variant)]
enum RhsAlternativeAttempt {
    Applied(RuleApplication),
    Trivial {
        obligation: Predicate,
        effects: Vec<BuiltinEffect>,
    },
    Indeterminate(IndeterminateReason),
    Simplification(SimplificationError),
}

enum ObligationVerdict {
    Discharged,
    Trivial,
    Carried,
}

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

enum EnsuresStepVerdict {
    Cleared,
    Trivial,
    Carried,
    Indeterminate(SmtError),
}

fn rhs_ensures_verdict(condition: Result<RuleCondition, SmtError>) -> EnsuresStepVerdict {
    match condition {
        Ok(RuleCondition::Satisfied) => EnsuresStepVerdict::Cleared,
        Ok(
            RuleCondition::Refuted
            | RuleCondition::Indeterminate(ConditionIndeterminacy::InconsistentPathCondition),
        ) => EnsuresStepVerdict::Trivial,
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
                    return RhsAlternativeAttempt::Simplification(error);
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
                return RhsAlternativeAttempt::Simplification(error);
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
    // An `ensures` constrains the successor only where its terms are defined, as a `requires`
    // constrains the instance.
    let mut ensures = match simplify_rule_condition(
        definition,
        ensures,
        &condition_knowledge,
        simplification_options,
        solver,
    ) {
        Ok(ensures) => ensures,
        Err(error) => {
            return RhsAlternativeAttempt::Simplification(error);
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
    let applicability_conditions = rule_predicates.len();
    extend_unique(&mut rule_predicates, rhs_constraints);
    extend_unique(&mut rule_predicates, ensures);
    // What the result adds to the applicability: the right-hand side's simplification
    // constraints, its carried definedness obligations and the carried `ensures`. The instances
    // of the applicability where it fails have no result from this alternative.
    let added = rule_predicates[applicability_conditions..]
        .iter()
        .filter(|predicate| **predicate != Predicate::True)
        .cloned()
        .collect::<Vec<_>>();
    let carried = (!added.is_empty()).then(|| conjunction(&added));
    let defined = if carried.is_some() {
        quantify_introduced_variables(pattern, rule_predicates.clone())
    } else {
        applicability.clone()
    };
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
            remainder_simplifications: Vec::new(),
            io: io_evaluation.map(|execution| execution.commit()),
            diagnostics: Vec::new(),
            observations: Vec::new(),
        },
        remainder: remainder_of(applicability),
        defined,
        carried,
        diagnostics: Vec::new(),
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
            attempt @ (RuleAttempt::Indeterminate(_) | RuleAttempt::Simplification(_)) => {
                return attempt;
            }
        }
    }
    if groups.is_empty() {
        RuleAttempt::NotApplicable
    } else {
        RuleAttempt::Unified { groups }
    }
}

/// The rule's existentials renamed apart from every variable of `pattern`, each through
/// `fresh::freshen_existential`.
fn freshen_existentials(rule: &RewriteRule, pattern: &Pattern) -> Substitution {
    let mut names_to_avoid = pattern_variable_names(pattern);
    rule.existentials
        .iter()
        .cloned()
        .map(|variable| {
            let fresh = freshen_existential(&variable, &mut names_to_avoid);
            (variable, fresh)
        })
        .collect()
}

#[cfg(test)]
mod tests {

    use super::*;

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
}
