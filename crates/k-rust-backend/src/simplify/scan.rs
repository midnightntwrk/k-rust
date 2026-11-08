//! Equation scans: the outcome of one equation attempt, the scan of one priority group, and the
//! priority loop over the groups a term theory offers a term.
//!
//! The loop is the only place that states "no equation offered this term matched it"
//! ([`NoOfferedEquationMatched`]), the premise of the simplifier's normal-form certificate
//! (`term::head::NormalFormCertificate`). It selects the groups itself, so the statement covers
//! every group equation selection offers the term, and it states it only when every attempt of
//! every group ended in a failed match of the equation's left-hand side
//! ([`EquationAttempt::NotApplicable`] carrying a [`MatchFailed`]).

use std::{cell::Cell, marker::PhantomData, sync::Arc};

use crate::{
    coverage::{Selection, every},
    definition::BackendDefinition,
    diagnostic::{self, Buffered, Subject},
    matching::MatchFailed,
    rule::{Predicate, RewriteRule, Theory, applicable_groups, term_index},
    substitution::Substitution,
    term::Term,
};

use super::{
    ConditionIndeterminacy, EquationInstances, EquationRule, Instance, Simplification,
    SimplificationOptions, SimplifyResult, equation_instances, subject_equalities,
};

#[derive(Clone, Copy, Eq, PartialEq)]
pub(super) enum IndeterminateEquation {
    Block,
    Continue,
}

/// Whether an equation attempt decides the condition of an instance the evaluator does not use,
/// or reads the instance as [`EquationAttempt::Unused`] without deciding it: the `requires` of an
/// instance a `concrete` or `symbolic` attribute set aside, and the subject equalities, with the
/// `requires`, of an instance that matches only where variables of the subject equal the terms
/// the match bound them to (`simplify::Instance::Conditional`).
///
/// Decided, such a condition gives `ContextDependent` when refuted and `Unused` otherwise, and
/// the two differ in one place only: in the function theory, whether the groups after the
/// equation's group are tried ([`scan_term_theory`]). Everywhere else they lead to the same
/// outcome, so [`scan_term_theory`] asks for the decision only there:
/// - in the simplification theory both make the group, and the scan, `NotCacheable`: a lemma
///   states nothing about the lemmas after it, which are tried either way;
/// - in the function theory's last offered group, `Unused` makes the scan `Blocked` and
///   `ContextDependent` makes it `NotCacheable`, and no group follows that either would let
///   apply. The two are read alike after the scan: neither gives a result, neither records the
///   term as evaluated or certifies it (only `NotApplicable` does), and neither commits the
///   attempt's diagnostics, which an attempt that does not apply drops ([`scan_alternatives`]);
/// - within one group or one equation's instances, the precedence of [`Combined`] makes the
///   whole `Unused` when an undecided set-aside instance is read as `Unused`, which the two
///   points above make equivalent to what the decision would give.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum SetAsideRequires {
    /// Decide the condition: a lower function group follows, which applies only if every
    /// equation of this group is refuted.
    Decide,
    /// Read the instance as `Unused` without deciding the condition.
    Unused,
}

/// One of the two term theories whose scans the evaluated mark rests on, as a type, so that a
/// statement about one theory's scan cannot stand in for the other's.
pub(super) trait TermTheory {
    /// What an equation that is not refuted and not applied does to the lower-priority groups of
    /// the scan: one whose `requires` (or matching) is undecided, and one that matched and was
    /// set aside ([`EquationAttempt::Unused`]).
    const INDETERMINATE_EQUATION: IndeterminateEquation;

    /// The equations of the theory.
    fn theory(definition: &BackendDefinition) -> &Theory;
}

/// The function equations: an undecided equation, and one that matched and was set aside, block
/// the lower-priority groups. Each holds, or may hold, of the application, while an `owise` or
/// otherwise lower-priority equation states its value only where no higher equation applies, so
/// function evaluation must keep the application rather than fall through to it.
pub(crate) struct FunctionTheory;

impl TermTheory for FunctionTheory {
    const INDETERMINATE_EQUATION: IndeterminateEquation = IndeterminateEquation::Block;

    fn theory(definition: &BackendDefinition) -> &Theory {
        definition.function_theory()
    }
}

/// The simplification equations: an undecided or set-aside equation does not keep the
/// lower-priority groups from applying, since a lemma states nothing about the lemmas after it.
pub(crate) struct SimplificationTheory;

impl TermTheory for SimplificationTheory {
    const INDETERMINATE_EQUATION: IndeterminateEquation = IndeterminateEquation::Continue;

    fn theory(definition: &BackendDefinition) -> &Theory {
        definition.simplification_theory()
    }
}

/// Every equation that selection offers a term in theory `K`, under the term's index and under
/// a bare variable, failed to match it: its left-hand side has no instance in common with the
/// term. Minted only by [`scan_term_theory`]; neither `Clone` nor `Copy`, so one scan yields
/// one statement.
pub(crate) struct NoOfferedEquationMatched<K>(PhantomData<K>);

pub(super) enum TheoryScan<K> {
    /// The result of the equation that applied, boxed (it is carried up every frame of a
    /// recursion through an equation's `requires`), and that equation.
    Applied(Box<Simplification>, Arc<RewriteRule>),
    Blocked,
    /// No equation applied, but some equation was passed over for a reason other than a failed
    /// match (see [`GroupScan::NotCacheable`] and [`GroupScan::Unused`]); the term is not a
    /// fixed point to record.
    NotCacheable,
    /// Every equation offered the term failed to match it.
    NotApplicable(NoOfferedEquationMatched<K>),
}

/// The priority loop of term theory `K`: scan the groups equation selection offers `term` in
/// priority order, trying each equation with `attempt`, until one applies or a group blocks the
/// scan. `attempt` is told whether to decide the `requires` of a set-aside instance
/// ([`SetAsideRequires`]): only in the function theory, and only in a group another group follows. The diagnostics of each indeterminate attempt are held in `indeterminate` (see
/// [`scan_group`]). The only mint of [`NoOfferedEquationMatched`]: it is
/// returned when every attempt of every offered group ended `NotApplicable`, which for a term
/// theory carries a [`MatchFailed`].
///
/// ```toml algorithm-site
/// id = "backend.simplify.term"
/// role = "part"
/// sites = ["scan_term_theory", "scan_alternatives", "scan_group", "scan_instances"]
/// ```
/// Inlined: each instance has one caller (its `attempt` is a closure of that caller), and the
/// scan is a frame of a recursion through an equation's `requires` (`tests::recursion_stack`).
///
/// In the function theory, when the run collects guards, the instances of the group that applied
/// whose guard the scan did not enter get untried entries ([`enter_untried_guards`]), with what
/// `untried` gives. `attempt` sets the cell it is given to the position, in matcher order, of
/// the instance that applied when it applies; the scan resets it to 0 before each attempt.
#[deny(clippy::wildcard_enum_match_arm)]
#[inline]
pub(super) fn scan_term_theory<K: TermTheory>(
    definition: &BackendDefinition,
    term: &Term,
    indeterminate: &mut IndeterminateAttempts,
    untried: &UntriedGuards<'_>,
    mut attempt: impl FnMut(
        &Arc<RewriteRule>,
        SetAsideRequires,
        &Cell<usize>,
    ) -> SimplifyResult<EquationAttempt<Box<Simplification>, MatchFailed>>,
) -> SimplifyResult<TheoryScan<K>> {
    let groups = applicable_groups(K::theory(definition), &term_index(term));
    // The groups in priority order, as a slice: a selection over the map's own iterator would
    // hold that iterator twice in this frame, which is part of every frame of a recursion through
    // an equation's `requires` (`tests::recursion_stack`).
    let groups = groups
        .iter()
        .map(|(priority, rules)| (*priority, rules.as_slice()))
        .collect::<Vec<_>>();
    // The scan stops at the group that applies or blocks: the equations it never tries are
    // offered (`crate::coverage::Selection`).
    let selection = Selection::new(
        groups.iter().copied(),
        every,
        equation_probe(definition, term),
    );
    let mut blocked = false;
    let mut not_cacheable = false;
    let last = groups.len().saturating_sub(1);
    let applied_instance = Cell::new(0);
    for (position, (_, rules)) in selection.groups().enumerate() {
        let set_aside =
            if K::INDETERMINATE_EQUATION == IndeterminateEquation::Block && position < last {
                SetAsideRequires::Decide
            } else {
                SetAsideRequires::Unused
            };
        match scan_group(rules, indeterminate, |rule| {
            // An equation holding a literal whose element the definition leaves open: marked in
            // an execution, undecided elsewhere, so that no lower group fires in its place
            // (`crate::literal`).
            if crate::literal::withheld(
                &rule.computed_attributes.open_literals,
                &rule.attributes.unique_id,
            ) {
                return Ok(EquationAttempt::Indeterminate(
                    ConditionIndeterminacy::ImplicationIndeterminate,
                ));
            }
            applied_instance.set(0);
            Ok(match attempt(rule, set_aside, &applied_instance)? {
                EquationAttempt::Applied(result) => {
                    EquationAttempt::Applied((result, Arc::clone(rule)))
                }
                EquationAttempt::NotApplicable(failed) => EquationAttempt::NotApplicable(failed),
                EquationAttempt::ContextDependent => EquationAttempt::ContextDependent,
                EquationAttempt::Unused => EquationAttempt::Unused,
                EquationAttempt::Indeterminate(reason) => EquationAttempt::Indeterminate(reason),
                EquationAttempt::Recurred => EquationAttempt::Recurred,
            })
        })? {
            GroupScan::Applied((result, rule)) => {
                // A function application is decided by the first group that applies or blocks;
                // a lemma states nothing about the lemmas after it.
                if K::INDETERMINATE_EQUATION == IndeterminateEquation::Block
                    && crate::coverage::records_guards()
                {
                    enter_untried_guards(
                        definition,
                        term,
                        groups[position].1,
                        &rule,
                        applied_instance.get(),
                        set_aside,
                        untried,
                    );
                }
                return Ok(TheoryScan::Applied(result, rule));
            }
            GroupScan::Blocked if K::INDETERMINATE_EQUATION == IndeterminateEquation::Block => {
                // A rule at this priority may apply after the symbolic subject becomes more
                // concrete. Function evaluation must preserve the application and must not fall
                // through to an owise or otherwise lower-priority equation.
                return Ok(TheoryScan::Blocked);
            }
            GroupScan::Blocked => blocked = true,
            // An equation of the group matched and holds (or may hold) of the term but was not
            // used: the lower-priority function equations' premises exclude the term, so they
            // must not apply in its place.
            GroupScan::Unused if K::INDETERMINATE_EQUATION == IndeterminateEquation::Block => {
                return Ok(TheoryScan::Blocked);
            }
            GroupScan::NotCacheable | GroupScan::Unused => not_cacheable = true,
            GroupScan::NotApplicable => {}
        }
    }
    Ok(if blocked {
        TheoryScan::Blocked
    } else if not_cacheable {
        TheoryScan::NotCacheable
    } else {
        // Every group of `groups`, the whole of what selection offers `term` in `K`, ended
        // `GroupScan::NotApplicable`: each of its attempts was `NotApplicable(MatchFailed)`.
        TheoryScan::NotApplicable(NoOfferedEquationMatched(PhantomData))
    })
}

/// What a term scan's untried entries are made under ([`enter_untried_guards`]): the path
/// conditions and options its attempts decide under, and the equations the scan does not try
/// at this application (those whose attempt failed in an earlier evaluation of it,
/// `simplify::UnspecifiedRetry`).
pub(super) struct UntriedGuards<'a> {
    pub(super) known_predicates: &'a [Predicate],
    pub(super) options: SimplificationOptions,
    pub(super) excluded: &'a [Arc<RewriteRule>],
}

/// The untried entries of the function application `term`, which the instance at position
/// `instance` of the equation `applied` of `group` applied to, the scan of the group deciding
/// set-aside instances as `set_aside` says (`coverage::guards`).
///
/// An equation states its value at the arguments its left-hand side matches where its
/// `requires` holds and no equation of a higher group applies, so its guard decides something
/// at every application its left-hand side matches whose deciding group is its own, under each
/// instance whose matching is decided: a usable instance, one a `concrete` or `symbolic`
/// attribute set aside, and one that matches under equalities of the subject's variables. The
/// scan enters the guard of some of those instances and not of others, by an order the
/// definition does not state and by what deciding a set-aside instance can change:
/// - the equations of the group after `applied`, and the instances of `applied` after the one
///   that applied, are not tried (the group and the equation's instances stop at the first
///   that applies, in declaration and matcher order);
/// - a set-aside or conditional instance of an equation the scan tried is not decided where no
///   lower function group follows or the equation has an undecided instance
///   ([`SetAsideRequires::Unused`]), whatever its place in the group.
///
/// Each of those instances of an equation the run collects the guard of gets an untried entry,
/// under the path conditions and the conditions its match holds under, with the outcome its
/// evaluation gives (`coverage::enter_untried`); every other one has the entry its attempt
/// made. So every instance of the group's equations has one entry, and the guard outcomes of a
/// group's equations do not depend on the order in which the scan or the matcher reaches them.
/// Lower groups, `owise` included, state nothing where this group applies, and get none.
///
/// None is made for an equation the scan does not try at this application
/// ([`UntriedGuards::excluded`]), nor for one holding a literal whose element the definition
/// leaves open (`crate::literal`): an attempt of it would rest on k-rust's element, which an
/// untried entry cannot mark. An undecided matching makes none. The matching is work off the
/// run's clock (`stop::off_the_clock`), as the entries' evaluations are, so that it does not
/// move the point at which the run meets its step deadline. Out of line, so that its work is no
/// part of the frame of a scan, which a recursion through an equation's `requires` passes
/// through once per level (`tests::recursion_stack`).
#[inline(never)]
fn enter_untried_guards(
    definition: &BackendDefinition,
    term: &Term,
    group: &[Arc<RewriteRule>],
    applied: &Arc<RewriteRule>,
    instance: usize,
    set_aside: SetAsideRequires,
    untried: &UntriedGuards<'_>,
) {
    let Some(position) = group.iter().position(|rule| Arc::ptr_eq(rule, applied)) else {
        return;
    };
    // Each candidate equation with the number of its instances, in matcher order, the scan
    // tried: every one before `applied`, those of `applied` up to the one that applied, none
    // after it.
    let candidates = group
        .iter()
        .enumerate()
        .filter(|(_, rule)| {
            !rule.requires.is_empty()
                && rule.computed_attributes.open_literals.is_empty()
                && !untried
                    .excluded
                    .iter()
                    .any(|excluded| Arc::ptr_eq(excluded, rule))
                && crate::coverage::collects_guard_of(&rule.attributes)
        })
        .map(|(at, rule)| {
            let tried = match at.cmp(&position) {
                std::cmp::Ordering::Less => usize::MAX,
                std::cmp::Ordering::Equal => instance + 1,
                std::cmp::Ordering::Greater => 0,
            };
            (rule, tried)
        })
        .collect::<Vec<_>>();
    if candidates.is_empty() {
        return;
    }
    let known_predicates = untried.known_predicates;
    crate::coverage::untried_application(
        term,
        known_predicates,
        (position, instance),
        untried.excluded.is_empty(),
        || {
            let (entries, _) = crate::stop::off_the_clock(u64::MAX, || {
                candidates
                    .into_iter()
                    .filter_map(|(rule, tried)| {
                        untried_instances(
                            definition,
                            rule,
                            term,
                            known_predicates,
                            tried,
                            set_aside,
                        )
                    })
                    .collect::<Vec<_>>()
            });
            for (rule, instances) in entries {
                for (substitution, match_conditions) in instances {
                    let mut knowledge = known_predicates.to_vec();
                    knowledge.extend(match_conditions);
                    crate::coverage::enter_untried(
                        definition,
                        &rule.attributes,
                        rule.requires.conjuncts(),
                        &substitution,
                        &knowledge,
                        untried.options,
                    );
                }
            }
        },
    );
}

/// An instance whose guard the scan did not enter: its substitution and the conditions its
/// match holds under ([`untried_instances`]).
type UntriedInstance = (Substitution, Vec<Predicate>);

/// The instances of `rule` at `term` whose guard the scan did not enter ([`enter_untried_guards`]),
/// each with the conditions its match holds under, and the equation they instantiate; `None`
/// when there is none. `tried` is the number of instances, in matcher order, the scan tried,
/// deciding set-aside instances as `set_aside` says.
fn untried_instances<'r>(
    definition: &BackendDefinition,
    rule: &'r RewriteRule,
    term: &Term,
    known_predicates: &[Predicate],
    tried: usize,
    set_aside: SetAsideRequires,
) -> Option<(EquationRule<'r>, Vec<UntriedInstance>)> {
    let (rule, instances) = equation_instances(definition, rule, term, known_predicates);
    let EquationInstances::Matched(instances) = instances else {
        return None;
    };
    // The scan decides a tried set-aside instance only where a lower group follows and no
    // instance of the equation is undecided (`simplify::instances_to_scan`).
    let decided = set_aside == SetAsideRequires::Decide
        && !instances
            .iter()
            .any(|instance| matches!(instance, Instance::Undecided));
    let untried = instances
        .into_iter()
        .enumerate()
        .filter_map(|(at, instance)| match instance {
            Instance::Usable(substitution) => (at >= tried).then(|| (substitution, Vec::new())),
            Instance::SetAside(substitution) => {
                (at >= tried || !decided).then(|| (substitution, Vec::new()))
            }
            Instance::Conditional(substitution) => {
                (at >= tried || !decided).then(|| subject_equalities(&rule, substitution))
            }
            Instance::Unused | Instance::NonFunctionalBinding | Instance::Undecided => None,
        })
        .collect::<Vec<_>>();
    (!untried.is_empty()).then_some((rule, untried))
}

/// The probe of an equation a selection site selected for `term` and never tried
/// (`crate::coverage::Selection`): whether it has an instance at `term`, one whose left-hand
/// side matches it or whose matching is undecided, by the enumeration every use of an equation
/// shares (`simplify::equation_instances`), without deciding any `requires`. The known
/// predicates only widen the renaming to the variables they mention, which does not change
/// whether the left-hand side matches the term, so none are passed.
pub(crate) fn equation_probe(
    definition: &BackendDefinition,
    term: &Term,
) -> impl FnMut(&RewriteRule) -> bool {
    move |rule| has_instance(definition, rule, term)
}

/// Whether `rule` has an instance at `term` ([`equation_probe`]). Out of line, so that the
/// enumeration's rule and instances are no part of the frame of a scan that ends by offering
/// what it did not try (`tests::recursion_stack`).
#[inline(never)]
fn has_instance(definition: &BackendDefinition, rule: &RewriteRule, term: &Term) -> bool {
    !matches!(
        equation_instances(definition, rule, term, &[]).1,
        EquationInstances::NotMatched(_)
    )
}

/// The outcome of one equation attempt. `N` is the evidence a `NotApplicable` attempt carries:
/// [`MatchFailed`] for the term theories, whose scans the evaluated mark rests on, so that only
/// a failed match of the left-hand side can be `NotApplicable` there; `()` for the ceil and
/// predicate scans, which never feed the mark.
pub(super) enum EquationAttempt<T, N> {
    NotApplicable(N),
    /// The equation is inapplicable under the current path condition, but may apply if the same
    /// term is simplified under different assumptions. Unlike `Indeterminate`, this does not
    /// block lower-priority equations in the current scan.
    ContextDependent,
    /// The equation's left-hand side matched, or its shape keeps the evaluator from using it as
    /// a term rewrite, and the evaluator does not use it on this term: a `concrete` or
    /// `symbolic` attribute rejected the binding and its `requires` is not refuted, the match
    /// bound a variable of the subject and the equality that binding states (or the
    /// `requires`) is not refuted, or the right-hand side is a predicate or `\top` (a `\top`
    /// lemma is used only on an operand of a term-level conjunction). These
    /// are choices of when the evaluator uses an equation, not of what the definition means:
    /// the equation still holds, or may hold, so the term may equal its right-hand side. This
    /// keeps the term out of the evaluated cache and lets lower-priority simplification lemmas
    /// fire, and, as `Indeterminate` does, it keeps lower-priority function equations from
    /// firing, since their premises exclude the term ([`FunctionTheory`]).
    Unused,
    Indeterminate(ConditionIndeterminacy),
    /// The equation applied to the subject, an `Unspecified` application, in an attempt that
    /// failed: its outcome still needed a value being computed, so the attempt was undone and
    /// the subject is tried again without it (`simplify::UnspecifiedFrame`). The equation is not
    /// refuted: like `Indeterminate`, this keeps lower-priority groups from firing, while the
    /// other equations of its group are still tried.
    Recurred,
    Applied(T),
}

/// The diagnostics of the indeterminate equation attempts of the scans on one subject, held
/// until the caller knows whether the subject is kept.
///
/// A diagnostic emitted during an attempt (an undecided `requires` or obligation, an equation
/// passed over for its unbound result variables, or whatever simplifying its conditions
/// reported) is a claim about the subject's result. An indeterminate attempt does not use the
/// equation, so the subject is kept only if no other equation of the scan, or of a scan of
/// another theory on the same subject, rewrites it. The caller that sees the subject kept
/// commits the held diagnostics ([`IndeterminateAttempts::commit`]); a caller whose subject was
/// rewritten drops them, since the result they describe is not the one returned. Once committed,
/// they explain that subject, and the simplifier entry that returns the result keeps them only if
/// the result still holds it ([`diagnostic::retract_dropped`]).
#[derive(Default)]
pub(super) struct IndeterminateAttempts(Vec<Buffered>);

impl IndeterminateAttempts {
    /// The subject is kept at its node: record the held diagnostics, attempt by attempt in scan
    /// order, each explaining the subject, which is built only when there is one to record.
    pub(super) fn commit(self, subject: impl FnOnce() -> Subject) {
        if self.0.iter().all(Buffered::is_empty) {
            return;
        }
        let subject = subject();
        for attempt in self.0 {
            attempt.commit_kept(&subject);
        }
    }
}

pub(super) enum GroupScan<T> {
    Applied(T),
    Blocked,
    /// No equation applied, and some equation was `ContextDependent` and none `Unused`: the
    /// scan's answer may differ under another path condition, so the term must not be recorded
    /// as a fixed point.
    NotCacheable,
    /// No equation applied, none was undecided, and some equation matched but was not used
    /// ([`EquationAttempt::Unused`]): it holds or may hold of the term, so the term is not a
    /// fixed point to record, and in the function theory no lower-priority group applies.
    Unused,
    /// Every attempt of the group was `NotApplicable`.
    NotApplicable,
}

/// How alternatives tried in order combine when each is by itself enough to rewrite the subject:
/// the equations of one priority group ([`scan_group`]) and the instances of one equation
/// ([`scan_instances`]). The first alternative that applies gives the result. Otherwise an
/// undecided alternative (indeterminate or recurred) leaves the whole undecided, since it may
/// still apply, and the first such outcome is the whole's. Otherwise the whole is unused if one
/// alternative is, since that alternative holds or may hold of the subject whatever the others
/// say, else context dependent if one is, and not applicable only when every alternative is.
pub(super) enum Combined<T, N> {
    Applied(T),
    Indeterminate(ConditionIndeterminacy),
    Recurred,
    ContextDependent,
    Unused,
    /// Every alternative was `NotApplicable`: the evidence of the last one, none when there was
    /// no alternative.
    NotApplicable(Option<N>),
}

/// Try `alternatives` in order with `attempt` until one applies, and combine their outcomes
/// ([`Combined`]); also returns the diagnostics of the undecided attempts, in order.
///
/// Each attempt is speculative, so its diagnostics are buffered ([`diagnostic::buffer`]) and
/// follow its outcome. An applied attempt's are committed: its result is the subject's. An
/// undecided attempt's are returned, for the caller to commit where an undecided outcome is what
/// explains the subject. The diagnostics of an attempt that does not apply, its `requires`
/// refuted or the equation not used, are dropped: they explain no result. A failed attempt's
/// are committed, as the failure is what the scan returns.
#[deny(clippy::wildcard_enum_match_arm)]
#[inline]
fn scan_alternatives<A, T, N>(
    alternatives: impl IntoIterator<Item = A>,
    mut attempt: impl FnMut(A) -> SimplifyResult<EquationAttempt<T, N>>,
) -> SimplifyResult<(Combined<T, N>, Vec<Buffered>)> {
    let mut undecided: Option<Combined<T, N>> = None;
    let mut held = Vec::new();
    let mut context_dependent = false;
    let mut unused = false;
    let mut not_applicable = None;
    for alternative in alternatives {
        // A guard, not `diagnostic::buffer`, whose closure would take a frame of its own on every
        // level of a recursion through an equation's `requires`.
        let buffering = diagnostic::Buffering::start();
        let outcome = attempt(alternative);
        let diagnostics = buffering.finish();
        let outcome = match outcome {
            Ok(outcome) => outcome,
            Err(unwind) => {
                diagnostics.commit();
                return Err(unwind);
            }
        };
        match outcome {
            EquationAttempt::Applied(result) => {
                diagnostics.commit();
                return Ok((Combined::Applied(result), held));
            }
            EquationAttempt::Indeterminate(reason) => {
                super::note_undecided();
                held.push(diagnostics);
                undecided.get_or_insert(Combined::Indeterminate(reason));
            }
            EquationAttempt::Recurred => {
                super::note_undecided();
                held.push(diagnostics);
                undecided.get_or_insert(Combined::Recurred);
            }
            EquationAttempt::ContextDependent => context_dependent = true,
            EquationAttempt::Unused => unused = true,
            EquationAttempt::NotApplicable(evidence) => not_applicable = Some(evidence),
        }
    }
    let combined = if let Some(undecided) = undecided {
        undecided
    } else if unused {
        Combined::Unused
    } else if context_dependent {
        Combined::ContextDependent
    } else {
        Combined::NotApplicable(not_applicable)
    };
    Ok((combined, held))
}

/// Try the equations of one priority group in order until one applies ([`scan_alternatives`]).
/// An undecided group blocks; one with an unused equation is `Unused`, and one whose equations
/// were otherwise context dependent is not cacheable. The diagnostics of the undecided attempts are held in `indeterminate_attempts`,
/// for the caller to commit if the subject is kept.
#[deny(clippy::wildcard_enum_match_arm)]
#[inline]
pub(super) fn scan_group<'r, R: 'r, T, N>(
    rules: impl IntoIterator<Item = &'r Arc<R>>,
    indeterminate_attempts: &mut IndeterminateAttempts,
    attempt: impl FnMut(&'r Arc<R>) -> SimplifyResult<EquationAttempt<T, N>>,
) -> SimplifyResult<GroupScan<T>> {
    let (combined, undecided) = scan_alternatives(rules, attempt)?;
    indeterminate_attempts.0.extend(undecided);
    Ok(match combined {
        Combined::Applied(result) => GroupScan::Applied(result),
        Combined::Indeterminate(_) | Combined::Recurred => GroupScan::Blocked,
        Combined::ContextDependent => GroupScan::NotCacheable,
        Combined::Unused => GroupScan::Unused,
        Combined::NotApplicable(_evidence) => GroupScan::NotApplicable,
    })
}

/// Try the instances of one equation, one per matching of its left-hand side against the
/// subject, in the matcher's order, until one applies.
///
/// A left-hand side with a map or set pattern can match one subject in several ways, binding
/// `σ1, ..., σn`. Each instance `f(t) = rhs σi requires R σi` is by itself a consequence of the
/// equation, so the equation applies to `t` as soon as one instance does, and is passed over
/// only when every instance is. The instances therefore combine exactly as the equations of one
/// priority group do ([`scan_alternatives`]): the first instance that applies gives the result
/// (when several would apply with different results, the definition equates those results, and
/// the load-time check pairs the equation with itself unless its right-hand side and `ensures`
/// read only variables every matching binds alike); otherwise an undecided instance leaves the
/// equation undecided, and a set-aside instance that is not refuted leaves it unused, so that a
/// lower-priority group does not fire where this equation holds or may hold.
///
/// The undecided instances' diagnostics are committed to the enclosing collector only if the
/// equation ends undecided, as they explain that outcome. A single instance is attempted
/// directly.
#[deny(clippy::wildcard_enum_match_arm)]
pub(super) fn scan_instances<S, T, N>(
    mut instances: Vec<S>,
    mut attempt: impl FnMut(S) -> SimplifyResult<EquationAttempt<T, N>>,
) -> SimplifyResult<EquationAttempt<T, N>> {
    if instances.len() == 1 {
        return attempt(instances.pop().expect("one instance"));
    }
    scan_several_instances(instances, attempt)
}

/// [`scan_instances`] of more than one instance. Out of line: a recursion through an equation's
/// `requires` passes through the scan of its single instance once per level, so the combination
/// of several is no part of every frame of it (`tests::recursion_stack`).
#[deny(clippy::wildcard_enum_match_arm)]
#[inline(never)]
fn scan_several_instances<S, T, N>(
    instances: Vec<S>,
    attempt: impl FnMut(S) -> SimplifyResult<EquationAttempt<T, N>>,
) -> SimplifyResult<EquationAttempt<T, N>> {
    let (combined, undecided) = scan_alternatives(instances, attempt)?;
    let commit_undecided = |outcome| {
        for diagnostics in undecided {
            diagnostics.commit();
        }
        outcome
    };
    Ok(match combined {
        Combined::Applied(result) => EquationAttempt::Applied(result),
        Combined::Indeterminate(reason) => commit_undecided(EquationAttempt::Indeterminate(reason)),
        Combined::Recurred => commit_undecided(EquationAttempt::Recurred),
        Combined::ContextDependent => EquationAttempt::ContextDependent,
        Combined::Unused => EquationAttempt::Unused,
        Combined::NotApplicable(evidence) => {
            EquationAttempt::NotApplicable(evidence.expect("an equation has at least one instance"))
        }
    })
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::{EquationAttempt, GroupScan, IndeterminateAttempts, scan_group, scan_instances};
    use crate::{diagnostic, simplify::ConditionIndeterminacy};

    type Outcome = EquationAttempt<&'static str, ()>;

    /// Attempt alternative `index` of `outcomes`: emit a diagnostic naming it and end as given.
    fn replay(outcomes: &[Outcome], index: usize) -> Outcome {
        diagnostic::emit_rule_condition_budget_exhausted(&format!("alternative-{index}"), None, 1);
        match &outcomes[index] {
            EquationAttempt::Applied(result) => EquationAttempt::Applied(*result),
            EquationAttempt::NotApplicable(()) => EquationAttempt::NotApplicable(()),
            EquationAttempt::Indeterminate(_) => {
                EquationAttempt::Indeterminate(ConditionIndeterminacy::NoSolver)
            }
            EquationAttempt::ContextDependent => EquationAttempt::ContextDependent,
            EquationAttempt::Unused => EquationAttempt::Unused,
            EquationAttempt::Recurred => EquationAttempt::Recurred,
        }
    }

    /// The alternatives whose diagnostics reached the collector shown as `shown`.
    fn reached(outcomes: &[Outcome], shown: &str) -> Vec<usize> {
        (0..outcomes.len())
            .filter(|index| shown.contains(&format!("\"alternative-{index}\"")))
            .collect()
    }

    /// The instances of one equation, ending as `outcomes` in order; returns the scan's outcome
    /// and the instances whose diagnostics reached the collector.
    fn scan(outcomes: &[Outcome]) -> (String, Vec<usize>) {
        let (outcome, diagnostics) = diagnostic::collect(|| {
            scan_instances((0..outcomes.len()).collect(), |instance| {
                Ok(replay(outcomes, instance))
            })
        });
        let outcome = match outcome.expect("no attempt stops") {
            EquationAttempt::Applied(result) => format!("applied {result}"),
            EquationAttempt::NotApplicable(()) => "not applicable".to_owned(),
            EquationAttempt::Indeterminate(_) => "indeterminate".to_owned(),
            EquationAttempt::ContextDependent => "context dependent".to_owned(),
            EquationAttempt::Unused => "unused".to_owned(),
            EquationAttempt::Recurred => "recurred".to_owned(),
        };
        (outcome, reached(outcomes, &format!("{diagnostics:?}")))
    }

    /// The equations of one priority group, ending as `outcomes` in order; returns the scan's
    /// outcome, the equations whose diagnostics reached the collector, and how many attempts it
    /// held for the caller.
    fn scan_equations(outcomes: &[Outcome]) -> (String, Vec<usize>, usize) {
        let rules = (0..outcomes.len()).map(Arc::new).collect::<Vec<_>>();
        let mut held = IndeterminateAttempts::default();
        let (outcome, diagnostics) = diagnostic::collect(|| {
            scan_group(&rules, &mut held, |rule| Ok(replay(outcomes, **rule)))
        });
        let outcome = match outcome.expect("no attempt stops") {
            GroupScan::Applied(result) => format!("applied {result}"),
            GroupScan::Blocked => "blocked".to_owned(),
            GroupScan::NotCacheable => "not cacheable".to_owned(),
            GroupScan::Unused => "unused".to_owned(),
            GroupScan::NotApplicable => "not applicable".to_owned(),
        };
        (
            outcome,
            reached(outcomes, &format!("{diagnostics:?}")),
            held.0.len(),
        )
    }

    /// Diagnostics follow the outcome they explain: an instance passed over (refuted, unused)
    /// explains nothing, an applied instance explains the result, and undecided instances explain
    /// an undecided equation, but not one that a later instance applies.
    #[test]
    fn only_the_instances_that_explain_the_outcome_report_their_diagnostics() {
        use EquationAttempt::{Applied, Indeterminate, NotApplicable, Unused};
        let undecided = || Indeterminate(ConditionIndeterminacy::NoSolver);

        assert_eq!(
            scan(&[NotApplicable(()), Unused, Applied("r")]),
            ("applied r".to_owned(), vec![2])
        );
        assert_eq!(
            scan(&[undecided(), NotApplicable(()), Applied("r")]),
            ("applied r".to_owned(), vec![2])
        );
        assert_eq!(
            scan(&[NotApplicable(()), undecided(), Unused, undecided()]),
            ("indeterminate".to_owned(), vec![1, 3])
        );
        assert_eq!(
            scan(&[NotApplicable(()), Unused]),
            ("unused".to_owned(), vec![])
        );
        assert_eq!(
            scan(&[
                NotApplicable(()),
                EquationAttempt::Recurred,
                Unused,
                undecided()
            ]),
            ("recurred".to_owned(), vec![1, 3])
        );
    }

    /// Diagnostics follow the outcome they explain, as for the instances of one equation: an
    /// equation passed over (refuted, unused) explains nothing, an applied one explains the
    /// result, and undecided ones are held for the caller, which commits them only if the
    /// subject is kept.
    #[test]
    fn only_the_equations_that_explain_the_outcome_report_their_diagnostics() {
        use EquationAttempt::{Applied, Indeterminate, NotApplicable, Unused};
        let undecided = || Indeterminate(ConditionIndeterminacy::NoSolver);

        assert_eq!(
            scan_equations(&[NotApplicable(()), Unused, Applied("r")]),
            ("applied r".to_owned(), vec![2], 0)
        );
        assert_eq!(
            scan_equations(&[undecided(), NotApplicable(()), Applied("r")]),
            ("applied r".to_owned(), vec![2], 1)
        );
        assert_eq!(
            scan_equations(&[NotApplicable(()), undecided(), Unused, undecided()]),
            ("blocked".to_owned(), vec![], 2)
        );
        assert_eq!(
            scan_equations(&[NotApplicable(()), Unused]),
            ("unused".to_owned(), vec![], 0)
        );
        assert_eq!(
            scan_equations(&[NotApplicable(()), NotApplicable(())]),
            ("not applicable".to_owned(), vec![], 0)
        );
        assert_eq!(
            scan_equations(&[EquationAttempt::Recurred, Unused, undecided()]),
            ("blocked".to_owned(), vec![], 2)
        );
    }

    /// An equation the scan does not try at an application, one whose attempt failed in an
    /// earlier evaluation of it (`UntriedGuards::excluded`), gets no untried entry; beside the
    /// same application without it, it gets its entry.
    #[test]
    fn an_excluded_equation_gets_no_untried_entry() {
        use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

        use super::{SetAsideRequires, UntriedGuards, enter_untried_guards};
        use crate::{
            coverage::{GuardCollection, GuardOutcome},
            definition::BackendDefinition,
            rule::{applicable_groups, term_index},
            simplify::SimplificationOptions,
        };

        let equation = |label: &str, rhs: &str, hook: &str| {
            format!(
                r#"axiom{{R}} \implies{{R}}(
                    \and{{R}}(
                        \equals{{SortBool{{}}, R}}({hook}{{}}(X:SortInt{{}}, \dv{{SortInt{{}}}}("0")), \dv{{SortBool{{}}}}("true")),
                        \and{{R}}(\in{{SortInt{{}}, R}}(X0:SortInt{{}}, X:SortInt{{}}), \top{{R}}())
                    ),
                    \equals{{SortInt{{}}, R}}(f{{}}(X0:SortInt{{}}), \and{{SortInt{{}}}}(\dv{{SortInt{{}}}}("{rhs}"), \top{{SortInt{{}}}}()))
                ) [label{{}}("{label}")]"#
            )
        };
        let source = format!(
            r#"[] module MAIN
                hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
                hooked-sort SortBool{{}} [hook{{}}("BOOL.Bool"), hasDomainValues{{}}()]
                hooked-symbol eqInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
                    [function{{}}(), total{{}}(), hook{{}}("INT.eq"), smt-hook{{}}("=")]
                hooked-symbol geInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
                    [function{{}}(), total{{}}(), hook{{}}("INT.ge"), smt-hook{{}}(">=")]
                symbol f{{}}(SortInt{{}}) : SortInt{{}} [function{{}}(), total{{}}()]
                {}
                {}
            endmodule []"#,
            equation("a", "1", "eqInt"),
            equation("b", "2", "geInt"),
        );
        let definition =
            BackendDefinition::internalize(&parse_definition(&source).unwrap(), "MAIN").unwrap();
        let term = definition
            .internalize_term(&parse_pattern(r#"f{}(\dv{SortInt{}}("0"))"#).unwrap(), &[])
            .unwrap();
        let groups = applicable_groups(definition.function_theory(), &term_index(&term));
        let group = groups.values().next().expect("one group");
        let labelled = |label: &str| {
            group
                .iter()
                .find(|rule| rule.attributes.label.as_deref() == Some(label))
                .expect("the equation is in the group")
        };
        let (a, b) = (labelled("a"), labelled("b"));
        let entered = |excluded: &[Arc<crate::rule::RewriteRule>]| {
            let ((), coverage) = crate::coverage::collect_recording(
                false,
                false,
                false,
                None,
                Some(GuardCollection::new(["b"])),
                || {
                    enter_untried_guards(
                        &definition,
                        &term,
                        group,
                        a,
                        0,
                        SetAsideRequires::Unused,
                        &UntriedGuards {
                            known_predicates: &[],
                            options: SimplificationOptions::default(),
                            excluded,
                        },
                    );
                },
            );
            coverage
                .guards
                .expect("the collection collected guards")
                .into_iter()
                .map(|guard| (guard.axiom, guard.outcomes))
                .collect::<Vec<_>>()
        };
        assert_eq!(
            entered(&[]),
            [("b".to_owned(), [GuardOutcome::Held].into_iter().collect())]
        );
        assert_eq!(entered(std::slice::from_ref(b)), []);
    }

    /// An alternative that matched and was set aside holds, or may hold, of the subject; one
    /// whose `requires` is refuted says nothing about it. The set-aside one decides the whole,
    /// whichever comes first, among the instances of one equation and among the equations of
    /// one group, so that a lower-priority function equation does not apply in its place.
    #[test]
    fn a_set_aside_alternative_outranks_a_refuted_one() {
        use EquationAttempt::{ContextDependent, Unused};

        assert_eq!(
            scan(&[ContextDependent, Unused]),
            ("unused".to_owned(), vec![])
        );
        assert_eq!(
            scan(&[Unused, ContextDependent]),
            ("unused".to_owned(), vec![])
        );
        assert_eq!(
            scan_equations(&[ContextDependent, Unused]),
            ("unused".to_owned(), vec![], 0)
        );
        assert_eq!(
            scan_equations(&[Unused, ContextDependent]),
            ("unused".to_owned(), vec![], 0)
        );
        assert_eq!(
            scan_equations(&[ContextDependent, ContextDependent]),
            ("not cacheable".to_owned(), vec![], 0)
        );
    }
}
