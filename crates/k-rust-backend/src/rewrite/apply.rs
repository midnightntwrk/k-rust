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
//! One-rule conditional rewriting step (matching, with unification as a fallback): match, recovery
//! ladder, condition simplification, definedness, SAT narrowing, requires, validity, applicability,
//! RHS instantiation, the thirteen phases P1 to P13 of `apply_rule_with_match`. Cost: one matching
//! problem per attempt; on an indeterminate match up to eleven recovery strategies, each
//! re-entering once per split with an empty or strictly shorter remainder (recursion depth <=
//! |remainder| + 1, below the one re-entry with the rule renamed apart from the subject); up to
//! three SMT calls per attempt. An attempt that applies has the conditions it adds scanned once for
//! an application above a result size bound (`refuse_carried_uncomputed_applications`),
//! visiting only their unevaluated subterms. `Counter::RewriteRuleAttempts`,
//! `Counter::RewriteMatchFailures`, `Counter::SmtQueries`; O(c) attempts per step for the c
//! candidates the step hands over.

// The phase functions return `Phase<T>` (below), whose `Err` is the `RuleAttempt` itself.
#![allow(clippy::result_large_err)]

use std::{cell::RefCell, collections::BTreeSet, ops::Range, sync::Arc};

use k_rust_kore::measure::{self, Algorithm, Counter};

use crate::{
    builtin::BuiltinEffect,
    condition::{
        Condition, InstantiatedCondition, MatchSolution, Obligation, ResultConditions,
        RhsDefinedness,
    },
    definedness::ceil_term,
    definition::BackendDefinition,
    diagnostic::{self, Occurrences, Sequenced},
    fresh::{FreshCounter, fresh_variable},
    ite::SplitSide,
    matching::{MatchResult, match_rule_in_definition},
    rule::{Predicate, RewriteRule, RuleRhs, rename_apart},
    simplify::{
        BudgetPolicy, ConditionIndeterminacy, ContradictedTotal, RuleCondition,
        SimplificationError, SimplificationOptions, binds_element_variable_to_set_pattern,
        decide_condition, refuse_uncomputed_applications, simplify_in_execution_with_solver,
        simplify_predicates_with_solver, simplify_with_solver,
    },
    smt::{Satisfiability, SmtError, SmtSolver, Validity},
    stop::{Stop, Stoppable},
    substitution::{Substitution, compose, extract_substitution, substitute},
    term::{
        Sort, Symbol, Term, TermKind, Variable,
        names::{VariableProvenance, split_marker},
    },
    transition::ExecutionIoState,
};

use super::{
    AppliedRule, GeneralUnificationRecovery, IndeterminateReason, Pattern, RecoveredMatch,
    StateNames, TrivialApplication, Truth, collection_unification_definedness,
    conjunctively_contains_alpha_equivalent, extend_unique, freshen_unbound_rule_variables,
    predicates_truth, recover_boolean_matches, recover_equality_matches,
    recover_function_equality_match, recover_functional_symbolic_match,
    recover_general_unification, recover_indeterminate_match, recover_ite_matches,
    recover_map_not_in_keys_matches, recover_overload_symbolic_match,
    recover_symbolic_map_key_matches,
    roles::{Applicability, CarriedCondition, DefinedSubcase, Remainder},
    solve_collection_remainders_with_narrowing, substitute_predicates,
};

/// The outcome of one rule attempt. A stop is not an outcome: an attempt that stopped has none,
/// and [`apply_rule`] returns the stop on the outer layer instead.
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

impl RuleAttempt {
    /// What the attempt's outcome holds, for the retraction of the reports raised while it was
    /// made (`apply_rule_with_match`, [`diagnostic::retract_dropped_reporting`]).
    ///
    /// A report that an equation was passed over explains why its subject is left unevaluated,
    /// so it is kept only while the outcome holds that subject: the step reads the successor of
    /// each application (its term and the constraints it adds to the path), the remainder its
    /// applicability leaves to lower priorities, and the sub-case and obligation of each
    /// application whose result is bottom. A refuted attempt (`NotApplicable`) holds nothing:
    /// the step derives nothing from it. An undecided attempt and a failed one keep every
    /// report, as no outcome replaced the work they describe.
    fn outcome(&self) -> Option<Occurrences<'_>> {
        match self {
            Self::NotApplicable => Some(Occurrences::of([], [])),
            Self::Unified { groups } => {
                let mut terms = Vec::new();
                let mut predicates = Vec::new();
                for group in groups {
                    for application in &group.applied {
                        terms.push(&application.applied.pattern.term);
                        predicates.extend(&application.applied.pattern.constraints);
                        predicates.push(application.remainder.as_predicate());
                    }
                    for trivial in &group.trivial {
                        predicates.push(&trivial.obligation);
                        predicates.push(trivial.applicability.as_predicate());
                    }
                }
                Some(Occurrences::of(terms, predicates))
            }
            Self::Indeterminate(_) | Self::Simplification(_) => None,
        }
    }
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
    /// The complement of the applicability: the instances of the subject the rule does not
    /// apply to.
    pub(super) remainder: Remainder,
    /// The sub-case of the subject where this application has a defined result: the existential
    /// closure, over the variables the pattern does not have (those the match introduced and
    /// the freshened existentials), of the applicability and the carried result condition.
    /// Equal to the applicability when nothing was carried.
    pub(super) defined: DefinedSubcase,
    /// The carried result condition, when the application's sub-case has instances outside
    /// `defined`: its conjunction is the obligation its `Carried` trivial entry reports.
    pub(super) carried: Option<CarriedCondition>,
    /// The diagnostics of this right-hand-side alternative's own construction; its group's
    /// `common` work is not in it.
    pub(super) diagnostics: Vec<Sequenced>,
}

/// The `Refuted` entry of an application whose result is bottom on its whole sub-case
/// `applicability` of `pattern`.
fn trivial_application(
    rule: &RewriteRule,
    pattern: &Pattern,
    applicability: &Applicability,
    obligation: Predicate,
    effects: Vec<BuiltinEffect>,
    contradicted_total: Option<Box<ContradictedTotal>>,
) -> TrivialApplication {
    crate::coverage::note_applied(&rule.attributes.unique_id);
    TrivialApplication {
        rule_id: rule.attributes.unique_id.clone(),
        label: rule.attributes.label.clone(),
        #[cfg(test)]
        kind: super::TrivialKind::Refuted,
        obligation,
        applicability: applicability.clone(),
        remainder: applicability.remainder(),
        undefined: applicability.as_predicate().clone(),
        before: pattern.clone(),
        effects,
        diagnostics: Vec::new(),
        remainder_simplifications: Vec::new(),
        contradicted_total,
    }
}

/// The `Refuted` entry of `application`, whose result the step took as defined on its defined
/// sub-case `D` but whose successor's normalization shows undefined (`obligation`, with
/// `contradicted_total` when an equation of a `total` symbol produced the undefined term): the
/// entry stands for `D`, the rest of the application's applicability being its carried entry's.
pub(super) fn undefined_successor_application(
    application: RuleApplication,
    obligation: Predicate,
    contradicted_total: Option<Box<ContradictedTotal>>,
) -> TrivialApplication {
    let applicability = application.defined.undefined_after_all();
    TrivialApplication {
        rule_id: application.applied.unique_id,
        label: application.applied.label,
        #[cfg(test)]
        kind: super::TrivialKind::Refuted,
        obligation,
        undefined: applicability.as_predicate().clone(),
        applicability,
        remainder: application.remainder,
        before: application.applied.before,
        effects: application.applied.effects,
        diagnostics: Vec::new(),
        remainder_simplifications: application.applied.remainder_simplifications,
        contradicted_total,
    }
}

/// The `Carried` entry of `application`, whose carried result condition `obligation` leaves the
/// instances of its sub-case `applicability` outside `application.defined` without a result.
fn carried_trivial_application(
    rule: &RewriteRule,
    pattern: &Pattern,
    applicability: &Applicability,
    application: &RuleApplication,
    obligation: Predicate,
) -> TrivialApplication {
    crate::coverage::note_applied(&rule.attributes.unique_id);
    let undefined = applicability.outside(&application.defined);
    TrivialApplication {
        rule_id: rule.attributes.unique_id.clone(),
        label: rule.attributes.label.clone(),
        #[cfg(test)]
        kind: super::TrivialKind::Carried,
        obligation,
        undefined: undefined.as_predicate().clone(),
        applicability: undefined,
        remainder: applicability.remainder(),
        before: pattern.clone(),
        effects: application.applied.effects.clone(),
        diagnostics: Vec::new(),
        remainder_simplifications: Vec::new(),
        contradicted_total: None,
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
            std::iter::once(entry.applicability.as_predicate().clone())
                .chain(applied.iter().map(|sibling| sibling.defined.negation())),
        );
    }
}

/// Further restrict each entry of `trivial` by `defined`, the defined sub-cases of candidates
/// of its priority that took the entry's instances there: `undefined` gains `not D_j` for each.
pub(super) fn exclude_defined<'a>(
    trivial: &mut [TrivialApplication],
    defined: impl IntoIterator<Item = &'a DefinedSubcase>,
) {
    let negations = defined
        .into_iter()
        .map(DefinedSubcase::negation)
        .collect::<Vec<_>>();
    if negations.is_empty() {
        return;
    }
    for entry in trivial {
        entry.undefined =
            conjoin_flat(std::iter::once(entry.undefined.clone()).chain(negations.iter().cloned()));
    }
}

/// `not predicate`, with the double negation and the constants folded.
pub(super) fn negation(predicate: &Predicate) -> Predicate {
    match predicate {
        Predicate::True => Predicate::False,
        Predicate::False => Predicate::True,
        Predicate::Not(inner) => (**inner).clone(),
        predicate => Predicate::Not(Box::new(predicate.clone())),
    }
}

/// The conjunction of `predicates` with nested conjunctions flattened, `True` and repeated
/// conjuncts dropped, and `False` absorbing, as does a negated conjunction beside all of its
/// conjuncts (up to alpha-equivalence).
pub(super) fn conjoin_flat(predicates: impl IntoIterator<Item = Predicate>) -> Predicate {
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
    // `not (p1 /\ .. /\ pn)` beside every `pi` is `\bottom`. The comparison is syntactic up to
    // the renaming of bound variables: two alpha-equivalent closures denote the same set, and a
    // free name denotes one variable throughout one conjunction. So the fold never drops a
    // satisfiable conjunction.
    let contradictory = conjuncts.iter().any(|conjunct| match conjunct {
        Predicate::False => true,
        Predicate::Not(inner) => {
            let mut negated = Vec::new();
            flatten((**inner).clone(), &mut negated);
            negated
                .iter()
                .all(|predicate| conjunctively_contains_alpha_equivalent(&conjuncts, predicate))
        }
        _ => false,
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
    fresh_counter: &mut FreshCounter,
    simplification_options: SimplificationOptions,
    solver: &dyn SmtSolver,
    assume_initial_defined: bool,
    io: Option<&ExecutionIoState>,
    ground_halt: bool,
) -> Stoppable<RuleAttempt> {
    let attempt = apply_rule_with_match(
        definition,
        rule,
        pattern,
        fresh_counter,
        simplification_options,
        solver,
        assume_initial_defined,
        None,
        io,
        ground_halt,
    )?;
    refuse_carried_uncomputed_applications(definition, attempt)
}

/// An attempt whose conditions carry an application whose value the backend does not compute
/// becomes the unsupported-hook failure that names it, so the step halts on its subject instead
/// of branching on a value it did not compute (`simplify::refuse_uncomputed_applications`):
/// the conditions each successor adds to its path (the match conditions, the `requires` the
/// solver did not decide, the right-hand side's carried obligations and `ensures`), and the
/// applicability, whose negation is the priority group's remainder. A condition the solver
/// decided is in none of them. The successor's configuration may carry one; it is checked if
/// the run would end on it (`rewrite::stuck`).
fn refuse_carried_uncomputed_applications(
    definition: &BackendDefinition,
    attempt: RuleAttempt,
) -> Stoppable<RuleAttempt> {
    let RuleAttempt::Unified { groups } = &attempt else {
        return Ok(attempt);
    };
    let conditions = groups.iter().flat_map(|group| {
        group
            .applied
            .iter()
            .flat_map(|application| {
                [
                    application.applied.rule_predicates.as_slice(),
                    std::slice::from_ref(application.remainder.as_predicate()),
                ]
            })
            .chain(
                group
                    .trivial
                    .iter()
                    .map(|trivial| std::slice::from_ref(trivial.remainder.as_predicate())),
            )
    });
    for predicates in conditions {
        if let Err(error) = refuse_uncomputed_applications(definition, None, predicates)? {
            return Ok(RuleAttempt::Simplification(error));
        }
    }
    Ok(attempt)
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
    /// Whether a variable-free configuration is read as one state, so that a rule applying to
    /// it only by narrowing ends the attempt as `Instantiation` ([`Self::one_state`]): true on
    /// the execution and search steps, false on the proof steps and the public step functions.
    ground_halt: bool,
    /// The emission-position ranges of this attempt level's nested units of work (re-entered
    /// sub-attempts and right-hand-side alternatives), which attribute their own diagnostics.
    nested_units: &'a RefCell<Vec<Range<u64>>>,
}

impl RuleContext<'_> {
    /// Whether the configuration denotes at most one state, so that a left-hand-side variable
    /// the match leaves unbound is not replaced by a minted existential.
    ///
    /// A term with no variable denotes at most one element. Wherever the rule applies to it,
    /// that element fixes every left-hand-side variable, so an existential minted for one adds
    /// no successor the configuration does not determine: it restates a part of the
    /// configuration the match could not decide (an application no equation evaluates, an
    /// operation whose axioms the matcher does not apply) as a fresh unknown, which the
    /// successor carries into the next step. A term concrete after normalization is
    /// variable-free and is one state on every route; any other variable-free term is one state
    /// where `ground_halt` is set. A variable makes the configuration a set of states, and
    /// narrowing it states which of them the rule applies to.
    fn one_state(&self) -> bool {
        self.pattern.term.concrete_after_normalization()
            || (self.ground_halt && self.pattern.term.attributes().variables.is_empty())
    }

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

/// A phase either hands its result to the next phase or ends the attempt early (`PhaseExit`).
type Phase<T> = Result<T, PhaseExit>;

/// How a phase ends a rule attempt early: with the `RuleAttempt` the caller reports, or with a
/// stop, which leaves the attempt without an outcome, so that no condition of the rule is decided
/// (applicable, refuted or undecided) from a missing answer; the stop unwinds to the step. The
/// exit is the attempt itself and not a boxed one: the `NotApplicable` exit is the hottest path
/// of the step (`Counter::RewriteMatchFailures`), and an allocation per failed attempt would be a
/// cost no phase needs.
enum PhaseExit {
    Attempt(RuleAttempt),
    Stop(Stop),
}

impl From<Stop> for PhaseExit {
    fn from(stop: Stop) -> Self {
        Self::Stop(stop)
    }
}

/// A definedness whose decision would need an impure application in an operand a conditional
/// never evaluates ends the attempt with the unsupported-hook failure (`crate::deferred`).
impl From<crate::deferred::DeferredOutcome> for PhaseExit {
    fn from(outcome: crate::deferred::DeferredOutcome) -> Self {
        Self::Attempt(RuleAttempt::Simplification(outcome.into()))
    }
}

/// Invariant: every re-entry (the six recovery splits, the unification solutions, and the
/// bindings extracted from conditions) carries the accumulated `inherited_conditions`, which
/// only grow, and either an empty or strictly shorter `remainder` or a binding of a previously
/// unbound `lhs` variable, so the recursion depth is at most |remainder| + 1 and the
/// one-state re-entry ([`RuleContext::one_state`]) cannot repeat. Before them, an attempt without a partial match
/// re-enters at most once with the rule renamed apart from the subject; the renamed rule meets
/// no scope variable, so it is not renamed again, and that re-entry counts no attempt.
#[allow(clippy::too_many_arguments)]
pub(super) fn apply_rule_with_match(
    definition: &BackendDefinition,
    rule: &RewriteRule,
    pattern: &Pattern,
    fresh_counter: &mut FreshCounter,
    simplification_options: SimplificationOptions,
    solver: &dyn SmtSolver,
    assume_initial_defined: bool,
    matched: Option<PartialRuleMatch>,
    io: Option<&ExecutionIoState>,
    ground_halt: bool,
) -> Stoppable<RuleAttempt> {
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
            ground_halt,
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
        ground_halt,
        nested_units: &nested_units,
    };
    // The attempt is one retraction scope: a report raised while it was made (of a call left
    // unevaluated in its `requires`, say) is kept only if the attempt's outcome still holds the
    // report's subject, whichever of its conditions, decided by the simplifier or by the solver,
    // dropped it (`RuleAttempt::outcome`).
    let ((attempt, retracted), level) = diagnostic::collect_unit(|| {
        diagnostic::retract_dropped_reporting(
            || match apply_rule_phases(context, fresh_counter, matched) {
                Ok(attempt) | Err(PhaseExit::Attempt(attempt)) => Ok(attempt),
                Err(PhaseExit::Stop(stop)) => Err(stop),
            },
            |attempt| attempt.as_ref().ok().and_then(RuleAttempt::outcome),
        )
    });
    let mut attempt = attempt?;
    // This level's own work (matching, recovery, conditions) is every emission outside its
    // nested units. Every group of the attempt, built here or by a sub-attempt re-entered from
    // here, depends on it. An attempt that produced no group attributes it to no candidate.
    if let RuleAttempt::Unified { groups } = &mut attempt {
        // The nested units attributed their emissions before this scope decided on them.
        for group in groups.iter_mut() {
            if let Some(nested) = &mut group.common {
                retracted.remove_from(nested);
            }
            for application in &mut group.applied {
                retracted.remove_from(&mut application.diagnostics);
            }
            retracted.remove_from(&mut group.trivial_work);
        }
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
    Ok(attempt)
}

/// The thirteen phases P1 to P13 in order; each phase's postcondition is what the next may
/// assume.
fn apply_rule_phases(
    context: RuleContext<'_>,
    fresh_counter: &mut FreshCounter,
    matched: Option<PartialRuleMatch>,
) -> Phase<RuleAttempt> {
    let (matching, mut inherited_conditions) = initial_match(context, matched);
    let (path_knowledge, mut inherited_knowledge) = knowledge(context, &inherited_conditions);
    let (substitution, match_conditions) = dispatch_match(
        context,
        fresh_counter,
        matching,
        &mut inherited_conditions,
        &mut inherited_knowledge,
    )?;
    if binds_element_variable_to_set_pattern(&substitution) {
        return Err(PhaseExit::Attempt(RuleAttempt::Indeterminate(
            IndeterminateReason::Match {
                rule_id: context.rule.attributes.unique_id.clone(),
                substitution,
                remainder: Vec::new(),
            },
        )));
    }
    let (substitution, conditions) = configuration_bindings(
        context,
        substitution,
        inherited_conditions,
        match_conditions,
    )?
    .into_parts();
    let mut match_conditions = simplify_conditions(context, conditions, &path_knowledge)?;
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
        fresh_counter,
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
    fresh_counter: &mut FreshCounter,
    matched: PartialRuleMatch,
) -> Stoppable<RuleAttempt> {
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
            context.ground_halt,
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
            // `apply_rule_with_match` renamed the rule apart from the subject's variables
            // before reaching this match, or found it apart.
            match_rule_in_definition(context.definition, &context.rule.lhs, &context.pattern.term),
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
        // Assumed facts: a definedness that depends on an impure application in an operand a
        // conditional never evaluates is left out, which only weakens them.
        extend_unique(
            &mut path_knowledge,
            ceil_term(context.definition, &context.pattern.term).unwrap_or_default(),
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
    fresh_counter: &mut FreshCounter,
    matching: MatchResult,
    inherited_conditions: &mut Vec<Predicate>,
    inherited_knowledge: &mut Vec<Predicate>,
) -> Phase<(Substitution, Vec<Predicate>)> {
    match matching {
        MatchResult::Failed(_) => {
            measure::bump(Counter::RewriteMatchFailures);
            Err(PhaseExit::Attempt(RuleAttempt::NotApplicable))
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
                    Err(PhaseExit::Attempt(RuleAttempt::NotApplicable))
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
                        return Err(PhaseExit::Attempt(attempt?));
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
    )? {
        Ok(recovered) => recovered,
        Err(error) => {
            return Err(PhaseExit::Attempt(RuleAttempt::Simplification(error)));
        }
    };
    match recovered {
        RecoveredMatch::Failed(reason) => Ok(MatchResult::Failed(reason)),
        RecoveredMatch::Matched {
            solution,
            remainder,
        } => {
            let (substitution, conditions) = solution.into_parts();
            extend_unique(inherited_conditions, conditions.iter().cloned());
            extend_unique(inherited_knowledge, conditions);
            Ok(if remainder.is_empty() {
                MatchResult::Success(substitution)
            } else {
                MatchResult::Indeterminate {
                    substitution,
                    remainder,
                }
            })
        }
    }
}

/// P5: the six splitting strategies (boolean, symbolic map key, map-not-in-keys, equality,
/// ite, collection narrowing), each either producing partial matches that re-enter with an
/// empty or strictly shorter remainder (combined by `combine_rule_attempts`) or declining.
/// `None` means every strategy declined; a stop of a re-entered attempt is the split's result.
/// ```toml algorithm-site
/// id = "backend.rewrite.recover"
/// role = "part"
/// sites = ["recover_by_split", "recover_by_unification"]
/// ```
fn recover_by_split(
    context: RuleContext<'_>,
    fresh_counter: &mut FreshCounter,
    substitution: &Substitution,
    remainder: &[(Term, Term)],
    inherited_conditions: &[Predicate],
) -> Option<Stoppable<RuleAttempt>> {
    let _span = measure::algorithm_span(Algorithm::BackendRewriteRecover);
    let definition = context.definition;
    let rule = context.rule;
    let pattern = context.pattern;
    let reenter_with = |fresh_counter: &mut FreshCounter, mut matched: PartialRuleMatch| {
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
        context.one_state(),
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
        context.one_state(),
    ) {
        return Some(combine_rule_attempts(
            matches
                .into_iter()
                .map(|matched| reenter_with(fresh_counter, matched)),
        ));
    }
    // A branch whose condition the path refutes, by its known predicates or then by the
    // solver, is dropped before its operand is matched (`recover_ite_matches`).
    let mut refuted = |condition: &Predicate| -> Stoppable<bool> {
        let mut known = pattern.constraints.clone();
        extend_unique(&mut known, inherited_conditions.iter().cloned());
        let simplified = match simplify_predicates_with_solver(
            definition,
            std::slice::from_ref(condition),
            &known,
            context.simplification_options,
            context.solver,
        )? {
            Ok(simplified) => simplified,
            Err(_) => vec![condition.clone()],
        };
        if predicates_truth(&simplified) == Truth::False {
            return Ok(true);
        }
        known.extend(simplified);
        Ok(matches!(
            context.solver.is_sat(&known, &Substitution::new())?,
            Ok(Satisfiability::Unsat)
        ))
    };
    if let Some(matches) =
        recover_ite_matches(definition, substitution.clone(), remainder, &mut refuted)
    {
        let matches = match matches {
            Ok(matches) => matches,
            Err(stop) => return Some(Err(stop)),
        };
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
            return Some(Ok(RuleAttempt::NotApplicable));
        }
        return Some(combine_rule_attempts(matches.into_iter().map(|solution| {
            let (substitution, solution_conditions) = solution.matched.into_parts();
            let (substitution, _) = freshen_unbound_rule_variables(
                rule,
                pattern,
                substitution,
                fresh_counter,
                context.one_state(),
            );
            let (substitution, solution_conditions) =
                MatchSolution::from_parts(substitution, solution_conditions).into_parts();
            let mut conditions = inherited_conditions.to_vec();
            extend_unique(&mut conditions, solution_conditions);
            match collection_unification_definedness(definition, remainder, &substitution) {
                Ok(definedness) => extend_unique(&mut conditions, definedness),
                Err(outcome) => return Ok(RuleAttempt::Simplification(outcome.into())),
            }
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
#[deny(clippy::wildcard_enum_match_arm)]
fn recover_by_unification(
    context: RuleContext<'_>,
    fresh_counter: &mut FreshCounter,
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
        context.one_state(),
    ) {
        GeneralUnificationRecovery::Unified(mut solutions) => {
            if solutions.len() == 1 {
                Ok(solutions.pop().expect("one unification solution"))
            } else {
                Err(PhaseExit::Attempt(combine_rule_attempts(
                    solutions
                        .into_iter()
                        .map(|(substitution, mut constraints)| {
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
                        }),
                )?))
            }
        }
        GeneralUnificationRecovery::Bottom => Err(PhaseExit::Attempt(RuleAttempt::NotApplicable)),
        GeneralUnificationRecovery::Outcome(outcome) => Err(outcome.into()),
        GeneralUnificationRecovery::Unsupported => {
            if let Some(recovered) = recover_functional_symbolic_match(
                definition,
                rule,
                pattern,
                substitution.clone(),
                &remainder,
                fresh_counter,
                context.one_state(),
            ) {
                return Ok(recovered);
            }
            if let Some(recovered) = recover_function_equality_match(
                rule,
                pattern,
                substitution.clone(),
                &remainder,
                fresh_counter,
                context.one_state(),
            ) {
                return Ok(recovered);
            }
            let requires = match simplify_rule_condition(
                definition,
                rule.requires.instantiate(&substitution),
                inherited_knowledge,
                context.simplification_options,
                context.solver,
            )? {
                Ok(requires) => requires,
                Err(error) => {
                    return Err(PhaseExit::Attempt(RuleAttempt::Simplification(error)));
                }
            };
            if predicates_truth(&requires) == Truth::False {
                return Err(PhaseExit::Attempt(RuleAttempt::NotApplicable));
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
                        &unclear
                    )?,
                    Ok(Validity::Refuted)
                )
            {
                return Err(PhaseExit::Attempt(RuleAttempt::NotApplicable));
            }
            Err(PhaseExit::Attempt(RuleAttempt::Indeterminate(
                IndeterminateReason::Match {
                    rule_id: rule.attributes.unique_id.clone(),
                    substitution,
                    remainder,
                },
            )))
        }
    }
}

/// P7: the substitution binds only `rule.lhs` variables afterwards; every binding of a subject
/// variable became `Equals(variable, value)` plus `ceil(value)` among the match conditions.
/// The inherited conditions, then the match conditions, leave under that substitution
/// ([`MatchSolution`]): they were recorded while later recovery steps (a split strategy's match,
/// the collection solver, unification, the freshening of unbound rule variables) still bound rule
/// variables, and the attempt instantiates the rule by the substitution and uses its bindings up.
fn configuration_bindings(
    context: RuleContext<'_>,
    mut substitution: Substitution,
    mut inherited_conditions: Vec<Predicate>,
    mut match_conditions: Vec<Predicate>,
) -> Phase<MatchSolution> {
    let configuration_bindings = substitution
        .iter()
        .filter(|(variable, _)| !context.rule.lhs.attributes().variables.contains(variable))
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
        extend_unique(
            &mut match_conditions,
            ceil_term(context.definition, &value)?,
        );
    }
    inherited_conditions.append(&mut match_conditions);
    Ok(MatchSolution::from_parts(
        substitution,
        inherited_conditions,
    ))
}

/// P8: the conditions of P7 simplified under the path; `False` ends the attempt; what remains
/// are the `Unknown` conditions.
fn simplify_conditions(
    context: RuleContext<'_>,
    conditions: Vec<Predicate>,
    path_knowledge: &[Predicate],
) -> Phase<Vec<Predicate>> {
    let conditions = match simplify_predicates_with_solver(
        context.definition,
        &conditions,
        path_knowledge,
        context.simplification_options,
        context.solver,
    )? {
        Ok(conditions) => conditions,
        Err(error) => {
            return Err(PhaseExit::Attempt(RuleAttempt::Simplification(error)));
        }
    };
    if predicates_truth(&conditions) == Truth::False {
        return Err(PhaseExit::Attempt(RuleAttempt::NotApplicable));
    }
    Ok(conditions
        .into_iter()
        .filter(|condition| predicates_truth(std::slice::from_ref(condition)) == Truth::Unknown)
        .collect::<Vec<_>>())
}

/// P9: `ceil` of every non-variable binding and of every subject collection the left-hand side
/// consumes by a collection pattern ([`consumed_collections`]), simplified under the path and
/// the match conditions; `False` means the rule applies vacuously (`Unified { trivial }`); the
/// `Unknown` ones join the match conditions.
fn definedness(
    context: RuleContext<'_>,
    substitution: &Substitution,
    path_knowledge: &[Predicate],
    match_conditions: &mut Vec<Predicate>,
) -> Phase<()> {
    // A consumed collection is the subject's, so it may hold a subject variable the match bound
    // (P7 left `X = value` among the match conditions, as when unification splits a symbolic
    // map). The step's instances are those of the binding, so the obligation is stated of the
    // collection they hold, which the simplifier decomposes against what the binding's own
    // definedness already states, rather than of the variable.
    let configuration = match_conditions
        .iter()
        .filter_map(|condition| match condition {
            Predicate::Equals(left, right) => match left.kind() {
                TermKind::Variable(variable)
                    if !context.rule.lhs.attributes().variables.contains(variable) =>
                {
                    Some((variable.clone(), right.clone()))
                }
                _ => None,
            },
            _ => None,
        })
        .collect::<Substitution>();
    let subject = if configuration.is_empty() {
        context.pattern.term.clone()
    } else {
        substitute(&context.pattern.term, &configuration)
    };
    let mut definedness_conditions = Vec::new();
    consumed_collections(
        context.definition,
        &context.rule.lhs,
        &subject,
        &mut definedness_conditions,
    )?;
    for value in substitution
        .values()
        .filter(|value| !matches!(value.kind(), TermKind::Variable(_)))
    {
        extend_unique(
            &mut definedness_conditions,
            ceil_term(context.definition, value)?,
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
    )? {
        Ok(conditions) => conditions,
        Err(error) => {
            return Err(PhaseExit::Attempt(RuleAttempt::Simplification(error)));
        }
    };
    if predicates_truth(&definedness_conditions) == Truth::False {
        let applicability = Applicability::close(context.pattern, std::mem::take(match_conditions));
        return Err(PhaseExit::Attempt(RuleAttempt::Unified {
            groups: vec![RuleApplicationGroup {
                applied: Vec::new(),
                trivial: vec![trivial_application(
                    context.rule,
                    context.pattern,
                    &applicability,
                    Predicate::False,
                    Vec::new(),
                    None,
                )],
                common: None,
                trivial_work: Vec::new(),
            }],
        }));
    }
    extend_unique(
        match_conditions,
        definedness_conditions.into_iter().filter(|condition| {
            predicates_truth(std::slice::from_ref(condition)) == Truth::Unknown
        }),
    );
    Ok(())
}

/// The definedness of each collection of `subject` that a collection pattern of `lhs` consumes,
/// appended to `conditions`.
///
/// A rewrite step is a transition: its successor may denote only states its predecessor reaches.
/// A map or set is defined only where its keys (elements) are distinct, so a pattern that splits
/// one, such as `(c |-> V) M`, matches `{c |-> 1, Y |-> 2}` only where `Y` is not `c`; the
/// bindings `V = 1` and `M = Y |-> 2` are defined everywhere and do not state it, so the step
/// takes `\ceil` of the consumed collection itself. A list's concatenation is total, but a list
/// pattern consumes its elements alike, so the same holds of it. A variable binds its subterm
/// whole and P9 charges the binding instead. The walk follows the positions where `lhs` and
/// `subject` share a constructor, the positions a syntactic match reads; a position the
/// matcher did not read structurally (unification, a domain value) is not charged here, and a
/// recovery that unifies collections states their definedness itself
/// (`collection_unification_definedness`). A subject collection whose stored `ceil_free`
/// attribute is set costs one read of it. The walk recurses over the left-hand side, whose
/// depth is that of the rule as written.
fn consumed_collections(
    definition: &BackendDefinition,
    lhs: &Term,
    subject: &Term,
    conditions: &mut Vec<Predicate>,
) -> Result<(), crate::deferred::DeferredOutcome> {
    match (lhs.kind(), subject.kind()) {
        (TermKind::And(left, right), _) => {
            consumed_collections(definition, left, subject, conditions)?;
            consumed_collections(definition, right, subject, conditions)?;
        }
        (TermKind::Map { .. } | TermKind::Set { .. } | TermKind::List { .. }, _) => {
            if !subject.attributes().ceil_free() {
                extend_unique(conditions, ceil_term(definition, subject)?);
            }
        }
        (
            TermKind::Application {
                symbol,
                arguments: patterns,
                ..
            },
            TermKind::Application {
                symbol: subject_symbol,
                arguments,
                ..
            },
        ) if symbol == subject_symbol && patterns.len() == arguments.len() => {
            for (pattern, argument) in patterns.iter().zip(arguments) {
                consumed_collections(definition, pattern, argument, conditions)?;
            }
        }
        (
            TermKind::Injection {
                source,
                target,
                term,
            },
            TermKind::Injection {
                source: subject_source,
                target: subject_target,
                term: subject_term,
            },
        ) if source == subject_source && target == subject_target => {
            consumed_collections(definition, term, subject_term, conditions)?;
        }
        _ => {}
    }
    Ok(())
}

/// P10: with match conditions present, the path plus the conditions must be satisfiable;
/// `Unsat` ends the attempt, `Unknown` or a solver error makes it `Indeterminate`, and a stop
/// ends it with the stop.
#[deny(clippy::wildcard_enum_match_arm)]
fn narrowing_sat(context: RuleContext<'_>, match_conditions: &[Predicate]) -> Phase<()> {
    if match_conditions.is_empty() {
        return Ok(());
    }
    let mut narrowed = context.pattern.constraints.clone();
    extend_unique(&mut narrowed, match_conditions.iter().cloned());
    match context.solver.is_sat(&narrowed, &Substitution::new())? {
        Ok(Satisfiability::Sat) => Ok(()),
        Ok(Satisfiability::Unsat) => Err(PhaseExit::Attempt(RuleAttempt::NotApplicable)),
        Ok(Satisfiability::Unknown(reason)) => Err(PhaseExit::Attempt(RuleAttempt::Indeterminate(
            IndeterminateReason::Smt {
                rule_id: context.rule.attributes.unique_id.clone(),
                error: SmtError::Unknown(reason),
            },
        ))),
        Err(error) => Err(PhaseExit::Attempt(RuleAttempt::Indeterminate(
            IndeterminateReason::Smt {
                rule_id: context.rule.attributes.unique_id.clone(),
                error,
            },
        ))),
    }
}

/// P11: `requires` under the substitution, simplified under the path plus the match
/// conditions (the `match_knowledge` returned with it); `False` ends the attempt; for a
/// one-state subject ([`RuleContext::one_state`]), bindings of still-unbound `lhs` variables
/// found in the conditions re-enter the attempt once with them composed in.
fn requires(
    context: RuleContext<'_>,
    fresh_counter: &mut FreshCounter,
    substitution: &Substitution,
    match_conditions: &[Predicate],
    path_knowledge: Vec<Predicate>,
) -> Phase<(Vec<Predicate>, Vec<Predicate>)> {
    let rule = context.rule;
    crate::coverage::note_matched(&rule.attributes.unique_id);
    // The equations that discharged the rule's definedness at load stand for the obligations
    // this attempt would otherwise decide (`ComputedRuleAttributes::discharged_by`).
    crate::coverage::replay(&rule.computed_attributes.discharged_by);
    let mut match_knowledge = path_knowledge;
    extend_unique(&mut match_knowledge, match_conditions.iter().cloned());
    // The instance satisfies `requires` only where its terms are defined; state that before the
    // simplifier or a solver can answer for instances where they are not.
    let requires = match simplify_rule_condition(
        context.definition,
        rule.requires.instantiate(substitution),
        &match_knowledge,
        context.simplification_options,
        context.solver,
    )? {
        Ok(requires) => requires,
        Err(error) => {
            return Err(PhaseExit::Attempt(RuleAttempt::Simplification(error)));
        }
    };
    if predicates_truth(&requires) == Truth::False {
        return Err(PhaseExit::Attempt(RuleAttempt::NotApplicable));
    }
    if context.one_state() {
        // Conditions can finish an otherwise incomplete match (for example, requires E = value).
        // Re-enter application with those bindings so the remaining functional equalities and
        // requires are simplified under the covering substitution before coverage is checked.
        let mut conditions = match_conditions.to_vec();
        extend_unique(&mut conditions, requires.iter().cloned());
        let (bindings, _) = extract_substitution(&conditions, context.definition.sort_graph());
        let bindings = bindings
            .into_iter()
            .filter(|(variable, _)| {
                rule.lhs.attributes().variables.contains(variable)
                    && !substitution.contains_key(variable)
            })
            .collect::<Substitution>();
        if !bindings.is_empty() {
            #[expect(
                clippy::disallowed_methods,
                reason = "bindings extracted from these conditions; the re-entered attempt states their definedness in phase P9"
            )]
            return Err(PhaseExit::Attempt(reenter(
                context,
                fresh_counter,
                PartialRuleMatch {
                    substitution: compose(&bindings, substitution),
                    conditions: substitute_predicates(&conditions, &bindings),
                    remainder: Vec::new(),
                },
            )?));
        }
    }
    Ok((requires, match_knowledge))
}

/// A rewrite rule's `requires` or `ensures`, instantiated, simplified under `known` with the
/// definedness of its Boolean terms explicit (`InstantiatedCondition::simplify`).
fn simplify_rule_condition(
    definition: &BackendDefinition,
    conditions: InstantiatedCondition,
    known: &[Predicate],
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Stoppable<Result<Vec<Predicate>, SimplificationError>> {
    conditions.simplify(
        definition,
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

/// P12: the unclear `requires` are checked for validity (`Valid` empties them, `Refuted` ends
/// the attempt, solver trouble makes it `Indeterminate`, a stop ends it with the stop); the
/// applicability is the
/// existential closure of the match conditions and the unclear `requires`, and an attempt
/// whose negated applicability is already on the path (alpha-equivalently) ends.
#[deny(clippy::wildcard_enum_match_arm)]
fn validity_and_applicability(
    context: RuleContext<'_>,
    requires: Vec<Predicate>,
    match_knowledge: &[Predicate],
    match_conditions: &[Predicate],
) -> Phase<(Vec<Predicate>, Applicability)> {
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
        match decide_condition(&unclear_requires, match_knowledge, context.solver)? {
            Ok(RuleCondition::Satisfied) => unclear_requires.clear(),
            Ok(RuleCondition::Refuted) => {
                return Err(PhaseExit::Attempt(RuleAttempt::NotApplicable));
            }
            Ok(RuleCondition::Indeterminate(
                ConditionIndeterminacy::ImplicationIndeterminate
                | ConditionIndeterminacy::NonFunctionalBinding
                | ConditionIndeterminacy::UnboundResultVariables(_),
            )) => {}
            Ok(RuleCondition::Indeterminate(ConditionIndeterminacy::NoSolver)) => {
                return Err(PhaseExit::Attempt(RuleAttempt::Indeterminate(
                    IndeterminateReason::Requires {
                        rule_id: rule.attributes.unique_id.clone(),
                        predicates: unclear_requires,
                    },
                )));
            }
            Ok(RuleCondition::Indeterminate(ConditionIndeterminacy::InconsistentPathCondition)) => {
                return Err(PhaseExit::Attempt(RuleAttempt::Indeterminate(
                    IndeterminateReason::Smt {
                        rule_id: rule.attributes.unique_id.clone(),
                        error: SmtError::InconsistentGroundTruth,
                    },
                )));
            }
            Ok(RuleCondition::Indeterminate(ConditionIndeterminacy::SmtUnknown(reason))) => {
                return Err(PhaseExit::Attempt(RuleAttempt::Indeterminate(
                    IndeterminateReason::Smt {
                        rule_id: rule.attributes.unique_id.clone(),
                        error: SmtError::Unknown(reason),
                    },
                )));
            }
            Ok(RuleCondition::Indeterminate(ConditionIndeterminacy::Untranslatable(error))) => {
                return Err(PhaseExit::Attempt(RuleAttempt::Indeterminate(
                    IndeterminateReason::Smt {
                        rule_id: rule.attributes.unique_id.clone(),
                        error: SmtError::Translation(error),
                    },
                )));
            }
            Err(error) => {
                return Err(PhaseExit::Attempt(RuleAttempt::Indeterminate(
                    IndeterminateReason::Smt {
                        rule_id: rule.attributes.unique_id.clone(),
                        error,
                    },
                )));
            }
        }
    }

    let mut applicability = match_conditions.to_vec();
    applicability.extend(unclear_requires.iter().cloned());
    let applicability = Applicability::close(pattern, applicability);
    if *applicability.as_predicate() != Predicate::True
        && conjunctively_contains_alpha_equivalent(
            &pattern.constraints,
            &Predicate::Not(Box::new(applicability.as_predicate().clone())),
        )
    {
        return Err(PhaseExit::Attempt(RuleAttempt::NotApplicable));
    }
    Ok((unclear_requires, applicability))
}

/// P13: a one-state subject ([`RuleContext::one_state`]) with an unbound `lhs` variable is
/// `Indeterminate` (`Instantiation`); the existentials are freshened; every right-hand-side alternative goes
/// through `apply_rhs_alternative`, and the attempt is `Unified` with the applications and
/// trivial results collected (an `Indeterminate` alternative ends it).
#[deny(clippy::wildcard_enum_match_arm)]
fn instantiate(
    context: RuleContext<'_>,
    fresh_counter: &mut FreshCounter,
    substitution: Substitution,
    match_conditions: Vec<Predicate>,
    match_knowledge: Vec<Predicate>,
    unclear_requires: Vec<Predicate>,
    applicability: Applicability,
) -> Phase<RuleAttempt> {
    let rule = context.rule;
    let pattern = context.pattern;
    if context.one_state() {
        let missing_variables = rule
            .lhs
            .attributes()
            .variables
            .iter()
            .filter(|variable| !substitution.contains_key(*variable))
            .cloned()
            .collect::<BTreeSet<_>>();
        if !missing_variables.is_empty() {
            return Err(PhaseExit::Attempt(RuleAttempt::Indeterminate(
                IndeterminateReason::Instantiation {
                    rule_id: rule.attributes.unique_id.clone(),
                    missing_variables,
                },
            )));
        }
    }

    // A rule variable that neither the match nor the requires bound denotes, at each
    // application, some value the rule introduces; so does a right-hand-side existential. Each
    // is minted from the request's counter, here, before the successor and every condition it
    // carries are instantiated, so they all name the same new variable and no other variable of
    // the request or of an earlier application.
    let minted = mint_unbound_rule_variables(rule, pattern, &substitution, fresh_counter);
    let (substitution, match_conditions, match_knowledge, unclear_requires) = if minted.is_empty() {
        (
            substitution,
            match_conditions,
            match_knowledge,
            unclear_requires,
        )
    } else {
        #[expect(
            clippy::disallowed_methods,
            reason = "renaming rule variables to fresh variables preserves definedness"
        )]
        let rename = |predicates: &[Predicate]| substitute_predicates(predicates, &minted);
        (
            compose(&minted, &substitution),
            rename(&match_conditions),
            rename(&match_knowledge),
            rename(&unclear_requires),
        )
    };
    let existential_substitution = freshen_existentials(rule, pattern, fresh_counter);
    let mut condition_knowledge = match_knowledge;
    extend_unique(&mut condition_knowledge, unclear_requires.iter().cloned());
    let alternatives = match &rule.rhs {
        RuleRhs::Term(rhs) => vec![(rhs, &rule.ensures)],
        RuleRhs::Disjunction(alternatives) => alternatives
            .iter()
            .map(|alternative| (&alternative.term, &alternative.ensures))
            .collect(),
        RuleRhs::Top => return Err(PhaseExit::Attempt(RuleAttempt::NotApplicable)),
        RuleRhs::Bottom => {
            return Err(PhaseExit::Attempt(RuleAttempt::Unified {
                groups: vec![RuleApplicationGroup {
                    applied: Vec::new(),
                    trivial: vec![trivial_application(
                        rule,
                        pattern,
                        &applicability,
                        Predicate::False,
                        Vec::new(),
                        None,
                    )],
                    common: None,
                    trivial_work: Vec::new(),
                }],
            }));
        }
        RuleRhs::Predicates(_) => return Err(PhaseExit::Attempt(RuleAttempt::NotApplicable)),
    };
    let mut applications = Vec::new();
    let mut trivial = Vec::new();
    let mut trivial_work = Vec::new();
    for (rhs, alternative_ensures) in alternatives {
        let ensures = rule.ensures.merged(alternative_ensures);
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
        match attempt? {
            RhsAlternativeAttempt::Applied(mut application) => {
                if let Some(carried) = application.carried.take() {
                    trivial.push(carried_trivial_application(
                        rule,
                        pattern,
                        &applicability,
                        &application,
                        carried.conjunction(),
                    ));
                }
                application.diagnostics = own_diagnostics;
                applications.push(application);
            }
            RhsAlternativeAttempt::Trivial {
                obligation,
                effects,
                contradicted_total,
            } => {
                trivial.push(trivial_application(
                    rule,
                    pattern,
                    &applicability,
                    obligation,
                    effects,
                    contradicted_total,
                ));
                trivial_work.extend(own_diagnostics);
            }
            RhsAlternativeAttempt::Indeterminate(reason) => {
                return Err(PhaseExit::Attempt(RuleAttempt::Indeterminate(reason)));
            }
            RhsAlternativeAttempt::Simplification(error) => {
                return Err(PhaseExit::Attempt(RuleAttempt::Simplification(error)));
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
        contradicted_total: Option<Box<ContradictedTotal>>,
    },
    Indeterminate(IndeterminateReason),
    Simplification(SimplificationError),
}

enum ObligationVerdict {
    Discharged,
    Trivial,
    Carried,
}

#[deny(clippy::wildcard_enum_match_arm)]
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

#[deny(clippy::wildcard_enum_match_arm)]
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
            | ConditionIndeterminacy::NonFunctionalBinding
            | ConditionIndeterminacy::UnboundResultVariables(_),
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
    ensures: &Condition,
    substitution: &Substitution,
    existential_substitution: &Substitution,
    condition_knowledge: &[Predicate],
    match_conditions: &[Predicate],
    unclear_requires: &[Predicate],
    applicability: &Applicability,
    simplification_options: SimplificationOptions,
    solver: &dyn SmtSolver,
    io: Option<&ExecutionIoState>,
) -> Stoppable<RhsAlternativeAttempt> {
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
    let (rhs, rhs_conditions, effects, undefined_term, contradicted_total) =
        if rule.computed_attributes.undefined_symbols.is_empty() && io_evaluation.is_none() {
            (rhs, ResultConditions::default(), Vec::new(), None, None)
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
            }?;
            match simplified {
                Ok(simplified) => {
                    let simplified = simplified.into_parts();
                    (
                        simplified.term,
                        simplified.conditions,
                        simplified.effects,
                        simplified.undefined_term,
                        simplified.contradicted_total,
                    )
                }
                Err(error) => {
                    return Ok(RhsAlternativeAttempt::Simplification(error));
                }
            }
        };
    if let Some(term) = undefined_term.clone() {
        return Ok(RhsAlternativeAttempt::Trivial {
            obligation: Predicate::Ceil(term),
            effects,
            contradicted_total,
        });
    }
    if predicates_truth(rhs_conditions.as_slice()) == Truth::False {
        return Ok(RhsAlternativeAttempt::Trivial {
            obligation: conjunction(rhs_conditions.as_slice()),
            effects,
            contradicted_total: None,
        });
    }
    extend_unique(
        &mut condition_knowledge,
        rhs_conditions.as_slice().iter().cloned(),
    );
    // The definedness of the instantiated right-hand side that the condition knowledge leaves
    // open: obligations the result carries after the right-hand side's own conditions (those it
    // repeats are not restated).
    let mut rhs_definedness = None;
    if !rule.computed_attributes.undefined_symbols.is_empty() {
        let obligations = match RhsDefinedness::of(definition, &rhs) {
            Ok(obligations) => obligations,
            Err(outcome) => return Ok(RhsAlternativeAttempt::Simplification(outcome.into())),
        };
        let reported_obligation = undefined_term
            .map(Predicate::Ceil)
            .unwrap_or_else(|| conjunction(obligations.as_slice()));
        let obligations = match obligations.simplify(|obligations| {
            simplify_predicates_with_solver(
                definition,
                obligations,
                &condition_knowledge,
                simplification_options,
                solver,
            )
        })? {
            Ok(obligations) => obligations,
            Err(error) => {
                return Ok(RhsAlternativeAttempt::Simplification(error));
            }
        };
        match rhs_obligation_verdict(decide_condition(
            obligations.as_slice(),
            &condition_knowledge,
            solver,
        )?) {
            ObligationVerdict::Discharged => {}
            ObligationVerdict::Trivial => {
                return Ok(RhsAlternativeAttempt::Trivial {
                    obligation: reported_obligation,
                    effects,
                    contradicted_total: None,
                });
            }
            ObligationVerdict::Carried => rhs_definedness = Some(obligations),
        }
    }
    let ensures = ensures
        .instantiate(substitution)
        .rename(existential_substitution);
    let reported_ensures = ensures.report();
    // An `ensures` constrains the successor only where its terms are defined, as a `requires`
    // constrains the instance.
    let mut ensures = match simplify_rule_condition(
        definition,
        ensures,
        &condition_knowledge,
        simplification_options,
        solver,
    )? {
        Ok(ensures) => ensures,
        Err(error) => {
            return Ok(RhsAlternativeAttempt::Simplification(error));
        }
    };
    match rhs_ensures_verdict(decide_condition(&ensures, &condition_knowledge, solver)?) {
        EnsuresStepVerdict::Cleared => ensures.clear(),
        EnsuresStepVerdict::Trivial => {
            return Ok(RhsAlternativeAttempt::Trivial {
                obligation: reported_ensures,
                effects,
                contradicted_total: None,
            });
        }
        EnsuresStepVerdict::Carried => {}
        EnsuresStepVerdict::Indeterminate(error) => {
            return Ok(RhsAlternativeAttempt::Indeterminate(
                IndeterminateReason::Smt {
                    rule_id: rule.attributes.unique_id.clone(),
                    error,
                },
            ));
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
    extend_unique(
        &mut rule_predicates,
        rhs_conditions.as_slice().iter().cloned().chain(
            rhs_definedness
                .iter()
                .flat_map(|definedness| definedness.as_slice())
                .cloned(),
        ),
    );
    // What the result adds to the applicability: the right-hand side's obligations, its carried
    // definedness obligations and the carried `ensures`. The instances of the applicability
    // where it fails have no result from this alternative. An assumption of the right-hand
    // side's simplification (an applied equation's open `ensures`) is not among them: it is what
    // the definition asserts of that equation's result wherever the equation applies, a trusted
    // axiom rather than a condition for the result to exist. The successor keeps it.
    let carried = CarriedCondition::collect(
        rhs_conditions
            .obligations()
            .chain(
                rhs_definedness
                    .into_iter()
                    .flat_map(RhsDefinedness::into_obligations),
            )
            .chain(ensures.iter().cloned().map(Obligation::of_rule_ensures)),
        &rule_predicates[..applicability_conditions],
        &rhs_conditions,
    );
    extend_unique(&mut rule_predicates, ensures);
    let defined = match &carried {
        Some(carried) => DefinedSubcase::restricted(
            pattern,
            &rule_predicates[..applicability_conditions],
            carried,
        ),
        None => DefinedSubcase::whole(applicability),
    };
    let mut constraints = pattern.constraints.clone();
    extend_unique(&mut constraints, rule_predicates.iter().cloned());
    crate::coverage::note_applied(&rule.attributes.unique_id);
    Ok(RhsAlternativeAttempt::Applied(RuleApplication {
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
        remainder: applicability.remainder(),
        defined,
        carried,
        diagnostics: Vec::new(),
    }))
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

/// Combine the attempts of a split's sub-cases, evaluated in order: the first undecided
/// sub-case, or the first stop, ends the combination before the later sub-cases are attempted.
#[deny(clippy::wildcard_enum_match_arm)]
fn combine_rule_attempts(
    attempts: impl IntoIterator<Item = Stoppable<RuleAttempt>>,
) -> Stoppable<RuleAttempt> {
    let mut groups = Vec::new();
    for attempt in attempts {
        match attempt? {
            RuleAttempt::NotApplicable => {}
            RuleAttempt::Unified { groups: found } => groups.extend(found),
            attempt @ (RuleAttempt::Indeterminate(_) | RuleAttempt::Simplification(_)) => {
                return Ok(attempt);
            }
        }
    }
    Ok(if groups.is_empty() {
        RuleAttempt::NotApplicable
    } else {
        RuleAttempt::Unified { groups }
    })
}

/// The rule variables that the left-hand side does not bind and that the match and the
/// requires left unbound, each renamed to a mint of the request's counter that keeps its name
/// as the base, with the `Ex#` marker in place of `Rule#`.
fn mint_unbound_rule_variables(
    rule: &RewriteRule,
    pattern: &Pattern,
    substitution: &Substitution,
    fresh_counter: &mut FreshCounter,
) -> Substitution {
    let unbound = rule
        .computed_attributes
        .unbound_variables
        .iter()
        .filter(|variable| !substitution.contains_key(*variable))
        .collect::<Vec<_>>();
    if unbound.is_empty() {
        return Substitution::new();
    }
    let mut names_to_avoid = substitution
        .values()
        .fold(StateNames::of(pattern), StateNames::with_variables_of);
    unbound
        .into_iter()
        .map(|variable| {
            let (_, base) = split_marker(
                &variable.name,
                &[VariableProvenance::Rule, VariableProvenance::Equation],
            );
            let seed = variable
                .with_name(base.into_owned())
                .with_provenance(VariableProvenance::Existential);
            (
                variable.clone(),
                fresh_variable(&seed, &mut names_to_avoid, fresh_counter),
            )
        })
        .collect()
}

/// The rule's existentials, each renamed to a mint of the request's counter that keeps its
/// `Ex#` marker (`Ex#Var'Ques'X!3`).
///
/// A rule without one returns at once, as `mint_unbound_rule_variables` does; with one, each
/// candidate name is looked up in the state's variable sets ([`StateNames`]), so a step pays
/// for the names it tries, not for the configuration's variables.
fn freshen_existentials(
    rule: &RewriteRule,
    pattern: &Pattern,
    fresh_counter: &mut FreshCounter,
) -> Substitution {
    if rule.existentials.is_empty() {
        return Substitution::new();
    }
    let mut names_to_avoid = StateNames::of(pattern);
    rule.existentials
        .iter()
        .cloned()
        .map(|variable| {
            let fresh = fresh_variable(&variable, &mut names_to_avoid, fresh_counter);
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
                    Term::raw_domain_value(sort.clone(), "value"),
                    Term::variable(alias.clone()),
                ),
                Term::variable(ordinary.clone()),
            ],
        );

        assert_eq!(term_alias_variables(&lhs), BTreeSet::from([alias]));
        assert!(!term_alias_variables(&lhs).contains(&ordinary));
    }

    /// A rule whose right-hand side is `\bottom` and an unconditional rule of the same priority
    /// both match `wrap(value)`. The survivor alone empties the group remainder and the entry's
    /// `undefined`, so only the rewrite-internal fields show the trivial rule's own sub-case:
    /// the whole subject, with an empty complement.
    #[test]
    fn a_mixed_group_trivial_entry_covers_the_whole_subject() {
        use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

        use crate::rewrite::{RewriteResult, TrivialKind, rewrite_step};

        let source = r#"[]
            module MAIN
                sort SortS{} [hasDomainValues{}()]
                symbol wrap{}(SortS{}) : SortS{}
                    [function{}(), total{}(), injective{}(), no-evaluators{}()]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                    \and{SortS{}}(\dv{SortS{}}("discarded"), \bottom{SortS{}}())
                ) [label{}("trivial")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                    \dv{SortS{}}("survivor")
                ) [label{}("survivor")]
            endmodule []"#;
        let definition = BackendDefinition::internalize(
            &parse_definition(source).expect("definition should parse"),
            "MAIN",
        )
        .expect("definition should internalize");
        let initial = Pattern {
            term: definition
                .internalize_term(
                    &parse_pattern(r#"wrap{}(\dv{SortS{}}("value"))"#).unwrap(),
                    &[],
                )
                .expect("subject should internalize"),
            constraints: Vec::new(),
        };
        let mut fresh = crate::fresh::FreshCounter::default();

        let RewriteResult::Branch {
            branches,
            remainder: None,
            trivial,
            ..
        } = rewrite_step(&definition, &initial, &mut fresh).expect("no stop is armed")
        else {
            panic!("a mixed group must retain its bottom sub-case");
        };
        assert_eq!(branches.len(), 1);
        let [entry] = trivial.as_slice() else {
            panic!("one trivial entry: {trivial:?}");
        };
        assert_eq!(entry.rule_id, "trivial");
        assert_eq!(entry.before, initial);
        assert_eq!(entry.kind, TrivialKind::Refuted);
        assert_eq!(*entry.applicability.as_predicate(), Predicate::True);
        assert_eq!(*entry.remainder.as_predicate(), Predicate::False);
        assert_eq!(entry.undefined, Predicate::False);
    }
}
