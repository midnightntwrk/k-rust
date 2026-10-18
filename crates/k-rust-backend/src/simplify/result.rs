//! The result of simplifying a term, built only through constructors named for what produced it.
//!
//! A simplification `t = C ∧ t'` conjoins the conditions `C` to its term, and each conjunct of `C`
//! is an obligation or an assumption (I4, [`ResultConditions`]). The role is decided where the
//! conjunct is produced: a hooked application's value carries its arguments' definedness, an
//! applied equation carries its open `ensures` as assumptions and its open binding obligations,
//! a `\bottom` is a refutation. [`Simplification`] keeps its conditions private, so no code
//! outside this module assembles a result's conditions by hand: the parent module builds a result
//! through the constructors below and accumulates the parts of a fixed point through
//! [`Accumulated`], which appends whole results and keeps every role.
//!
//! A result's applied rules, effects and conditions are [`Log`]s, so appending a part's results
//! shares them: a level of a nested term pays for its own node, not for what the levels below it
//! produced, and the flat lists are built once, where a caller takes the result apart
//! ([`Simplification::into_parts`]).

use crate::{
    builtin::BuiltinEffect,
    condition::{CarriedObligations, Conjunct, ResultConditions},
    definition::BackendDefinition,
    rule::{Predicate, RewriteRule},
    term::Term,
};

use super::{BudgetExhaustion, ContradictedTotal, Log};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Simplification {
    pub term: Term,
    /// The conjuncts the simplification conjoins to `term`, each an obligation or an assumption.
    conditions: Log<Conjunct>,
    pub applied_rules: Log<String>,
    pub effects: Log<BuiltinEffect>,
    pub exhausted: Option<BudgetExhaustion>,
    /// The innermost partial builtin application that evaluated to bottom, or the innermost
    /// set or map that holds an element or key twice (`simplify_root`).
    ///
    /// Rewrite execution uses this provenance to report the exact definedness
    /// obligation that made a successor empty. It is deliberately separate from
    /// `conditions`: other simplification paths can also produce `false`.
    pub undefined_term: Option<Term>,
    /// Set together with `undefined_term` when the undefined term arose in the result of an
    /// equation for a symbol declared `total` (or `functional`): see [`ContradictedTotal`].
    pub contradicted_total: Option<Box<ContradictedTotal>>,
    /// Where the simplification found `\bottom` when no `undefined_term` reports it: an
    /// equation's own result (a `#Bottom` right-hand side, a refuted `ensures`) or a subject
    /// whose bindings an equation found empty ([`FoundBottom`]).
    pub(crate) bottom: Option<Box<FoundBottom>>,
}

/// The innermost term a simplification found `\bottom` at, other than through a builtin's
/// undefined result or a repeated collection (`Simplification::undefined_term`).
///
/// A subject whose bindings an equation found empty is reported by the equation's result
/// ([`Simplification::bottom_subject`]); the subject of a root step whose own result conjoins
/// `\bottom` is reported by the lineage that took the step (`simplify_on_stack`), which alone
/// knows that the subject's arguments were not `\bottom` already.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct FoundBottom {
    pub(crate) term: Term,
    /// The `total` applications whose contradicted claim was noted for it, so that an enclosing
    /// lineage names no second one (the innermost equation is the one contradicted): none, or
    /// the one `total` step whose result reached it. An evaluation recorded for reuse keeps only
    /// the namings its own steps made ([`Accumulated::since`]), so that the step it is served
    /// under names its own claim.
    pub(crate) named: Vec<Term>,
}

/// A [`Simplification`] taken apart, every field public. There is no conversion back: a
/// `Simplification` is built only by the simplifier.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SimplificationParts {
    pub term: Term,
    pub conditions: ResultConditions,
    pub applied_rules: Vec<String>,
    pub effects: Vec<BuiltinEffect>,
    pub exhausted: Option<BudgetExhaustion>,
    pub undefined_term: Option<Term>,
    pub contradicted_total: Option<Box<ContradictedTotal>>,
}

/// What a builtin hook made of an application it evaluated (`simplify_root`).
pub(super) enum HookOutcome {
    /// The application's value.
    Value(Term),
    /// The application's value and the effect the hook performed.
    Effect(Term, BuiltinEffect),
    /// The application is `\bottom`.
    Bottom,
}

impl Simplification {
    /// The conjuncts the simplification conjoins to its term, with their roles.
    pub fn conditions(&self) -> ResultConditions {
        ResultConditions::from_conjuncts(self.conditions.iter().cloned())
    }

    /// Whether the simplification conjoins nothing to its term.
    pub fn is_unconditional(&self) -> bool {
        self.conditions.is_empty()
    }

    /// Every conjunct the simplification conjoins to its term, in order.
    pub fn constraints(&self) -> Vec<Predicate> {
        self.conjoined().cloned().collect()
    }

    /// Every conjunct the simplification conjoins to its term, in order, read in place.
    pub(crate) fn conjoined(&self) -> impl ExactSizeIterator<Item = &Predicate> {
        self.conditions.iter().map(Conjunct::predicate)
    }

    /// The result taken apart, its lists built once.
    pub fn into_parts(self) -> SimplificationParts {
        SimplificationParts {
            term: self.term,
            conditions: ResultConditions::from_conjuncts(self.conditions),
            applied_rules: self.applied_rules.into_vec(),
            effects: self.effects.into_vec(),
            exhausted: self.exhausted,
            undefined_term: self.undefined_term,
            contradicted_total: self.contradicted_total,
        }
    }

    /// `term` with no step taken at its root: nothing conjoined, no rule applied.
    pub(super) fn irreducible(term: Term) -> Self {
        Self {
            term,
            conditions: Log::new(),
            applied_rules: Log::new(),
            effects: Log::new(),
            exhausted: None,
            undefined_term: None,
            contradicted_total: None,
            bottom: None,
        }
    }

    /// A set holding an element twice, or a map binding a key twice: `\bottom`, reported as the
    /// undefined term.
    pub(super) fn repeated_collection(term: &Term) -> Self {
        Self {
            term: term.clone(),
            conditions: conjuncts(ResultConditions::refuted()),
            applied_rules: Log::new(),
            effects: Log::new(),
            exhausted: None,
            undefined_term: Some(term.clone()),
            contradicted_total: None,
            bottom: None,
        }
    }

    /// The result of the builtin `hook` on `application`. A value carries the definedness of the
    /// application's arguments (I3, [`ResultConditions::hook_arguments`], minus `known`); a
    /// `\bottom` is a refutation that reports the application as the undefined term.
    pub(super) fn hook(
        definition: &BackendDefinition,
        application: &Term,
        before_children: Option<&Term>,
        outcome: HookOutcome,
        hook: &str,
        known: &[Predicate],
    ) -> Result<Self, crate::deferred::DeferredOutcome> {
        let (term, conditions, effects, undefined_term) = match outcome {
            HookOutcome::Value(value) => (
                value,
                ResultConditions::hook_arguments(definition, application, before_children, known)?,
                Vec::new(),
                None,
            ),
            HookOutcome::Effect(value, effect) => (
                value,
                ResultConditions::hook_arguments(definition, application, before_children, known)?,
                vec![effect],
                None,
            ),
            HookOutcome::Bottom => (
                application.clone(),
                ResultConditions::refuted(),
                Vec::new(),
                Some(application.clone()),
            ),
        };
        Ok(Self {
            term,
            conditions: conjuncts(conditions),
            applied_rules: Log::from(vec![format!("builtin:{hook}")]),
            effects: Log::from(effects),
            exhausted: None,
            undefined_term,
            contradicted_total: None,
            bottom: None,
        })
    }

    /// The result `term` of the function equation `rule`, with what its instance leaves of its
    /// `ensures` and its open binding obligations `carried`, which exist only once the instance's
    /// bindings are decided (`MatchedEquation::decide`); the conditions are built here by
    /// [`ResultConditions::equation`], which records the `ensures` as assumptions.
    pub(super) fn equation(
        rule: &RewriteRule,
        term: Term,
        ensures: Vec<Predicate>,
        carried: CarriedObligations,
    ) -> Self {
        crate::coverage::note_applied(&rule.attributes.unique_id);
        Self {
            term,
            conditions: conjuncts(ResultConditions::equation(ensures, carried)),
            applied_rules: Log::from(vec![rule.attributes.unique_id.clone()]),
            effects: Log::new(),
            exhausted: None,
            undefined_term: None,
            contradicted_total: None,
            bottom: None,
        }
    }

    /// The result of `rule` on a subject `term` that is empty under the path condition because
    /// a binding of the equation's instance is (a subterm of the subject): the subject is
    /// retained and `\bottom` is its only constraint, so the caller merges it as it merges any
    /// other constraint set and the pattern becomes `\bottom` as a whole. The subject is
    /// reported as where `\bottom` was found; the equation's own result is not that place.
    /// Only the claim check reads where, so it is reported only when `claims_checked`
    /// (`simplify::claims_checked_in`).
    pub(super) fn bottom_subject(rule: &RewriteRule, term: &Term, claims_checked: bool) -> Self {
        Self {
            bottom: claims_checked.then(|| {
                Box::new(FoundBottom {
                    term: term.clone(),
                    named: Vec::new(),
                })
            }),
            ..Self::bottom_result(rule, term)
        }
    }

    /// The result of `rule` on a subject `term` when the equation's own result is `\bottom`
    /// (every alternative's `ensures` refuted): as [`Self::bottom_subject`], but the lineage that
    /// applied the equation reports where (`FoundBottom`).
    pub(super) fn bottom_result(rule: &RewriteRule, term: &Term) -> Self {
        crate::coverage::note_applied(&rule.attributes.unique_id);
        Self {
            term: term.clone(),
            conditions: conjuncts(ResultConditions::refuted()),
            applied_rules: Log::from(vec![rule.attributes.unique_id.clone()]),
            effects: Log::new(),
            exhausted: None,
            undefined_term: None,
            contradicted_total: None,
            bottom: None,
        }
    }

    /// Whether the simplification conjoins `\bottom` to its term.
    pub(super) fn conjoins_bottom(&self) -> bool {
        self.conjoined()
            .any(|predicate| *predicate == Predicate::False)
    }
}

/// The conjuncts of `conditions` as a log.
fn conjuncts(conditions: ResultConditions) -> Log<Conjunct> {
    Log::from(conditions.into_conjuncts())
}

/// The running result of a fixed point over parts (`simplify_with_budget`, `simplify_children`).
///
/// [`Accumulated::absorb`] appends a part's conditions, applied rules and effects, and keeps the
/// first budget exhaustion; the caller resolves the part's undefined-term reports, which depend on
/// the lineage, and sets `undefined_term`, `contradicted_total` and `bottom` itself. Appending
/// shares the part's logs ([`Log::append`]), so absorbing a part costs the same whatever it holds.
///
/// The methods `simplify_on_stack` calls between its recursive calls are not inlined: inlined,
/// their temporaries would be part of every frame of that recursion, whose stack per level
/// `nesting::STACK_PER_LEVEL` bounds.
#[derive(Default)]
pub(super) struct Accumulated {
    conditions: Log<Conjunct>,
    applied_rules: Log<String>,
    effects: Log<BuiltinEffect>,
    pub(super) exhausted: Option<BudgetExhaustion>,
    pub(super) undefined_term: Option<Term>,
    pub(super) contradicted_total: Option<Box<ContradictedTotal>>,
    pub(super) bottom: Option<Box<FoundBottom>>,
}

/// A point of an [`Accumulated`] result ([`Accumulated::mark`]): its conditions, applied rules and
/// effects then, shared, and its reports then. The reports may be updated after the mark is taken
/// ([`AccumulatedMark::refresh_reports`]), for a caller that settles them later in the same step.
pub(super) struct AccumulatedMark {
    conditions: Log<Conjunct>,
    applied_rules: Log<String>,
    effects: Log<BuiltinEffect>,
    exhausted: Option<BudgetExhaustion>,
    undefined_term: Option<Term>,
    contradicted_total: Option<Box<ContradictedTotal>>,
    bottom: Option<Box<FoundBottom>>,
}

impl AccumulatedMark {
    /// Take `accumulated`'s current reports in place of those held at the mark.
    pub(super) fn refresh_reports(&mut self, accumulated: &Accumulated) {
        self.exhausted = accumulated.exhausted;
        self.undefined_term.clone_from(&accumulated.undefined_term);
        self.contradicted_total
            .clone_from(&accumulated.contradicted_total);
        self.bottom.clone_from(&accumulated.bottom);
    }
}

/// What [`Accumulated::absorb`] leaves of a part: its term and its undefined-term reports.
pub(super) struct Absorbed {
    pub(super) term: Term,
    pub(super) undefined_term: Option<Term>,
    pub(super) contradicted_total: Option<Box<ContradictedTotal>>,
    pub(super) bottom: Option<Box<FoundBottom>>,
}

impl Accumulated {
    /// Append `part`'s conditions, applied rules and effects, and keep the first exhaustion.
    /// It takes a whole [`Simplification`], so every conjunct keeps the role its producer gave it.
    #[inline(never)]
    pub(super) fn absorb(&mut self, part: Simplification) -> Absorbed {
        let Simplification {
            term,
            conditions,
            applied_rules,
            effects,
            exhausted,
            undefined_term,
            contradicted_total,
            bottom,
        } = part;
        self.conditions.append(conditions);
        self.applied_rules.append(applied_rules);
        self.effects.append(effects);
        self.exhausted = self.exhausted.or(exhausted);
        Absorbed {
            term,
            undefined_term,
            contradicted_total,
            bottom,
        }
    }

    /// The `\top` equation `rule_id` applied to an operand of a term-level `\and`, with its open
    /// binding obligations ([`ResultConditions::top_equation`]).
    pub(super) fn top_equation(&mut self, rule_id: String, obligations: Vec<Predicate>) {
        crate::coverage::note_applied(&rule_id);
        self.applied_rules.push(rule_id);
        self.conditions
            .append(conjuncts(ResultConditions::top_equation(obligations)));
    }

    /// Where the running result stands now, for [`Accumulated::rewind`] and
    /// [`Accumulated::since`].
    #[inline(never)]
    pub(super) fn mark(&self) -> AccumulatedMark {
        AccumulatedMark {
            conditions: self.conditions.clone(),
            applied_rules: self.applied_rules.clone(),
            effects: self.effects.clone(),
            exhausted: self.exhausted,
            undefined_term: self.undefined_term.clone(),
            contradicted_total: self.contradicted_total.clone(),
            bottom: self.bottom.clone(),
        }
    }

    /// Return to `mark`: every part absorbed since is dropped, and the reports are those `mark`
    /// holds.
    #[inline(never)]
    pub(super) fn rewind(&mut self, mark: &AccumulatedMark) {
        self.conditions.clone_from(&mark.conditions);
        self.applied_rules.clone_from(&mark.applied_rules);
        self.effects.clone_from(&mark.effects);
        self.exhausted = mark.exhausted;
        self.undefined_term.clone_from(&mark.undefined_term);
        self.contradicted_total.clone_from(&mark.contradicted_total);
        self.bottom.clone_from(&mark.bottom);
    }

    /// The conditions absorbed since `mark`.
    pub(super) fn constraints_since(&self, mark: &AccumulatedMark) -> Log<Conjunct> {
        self.conditions.since(&mark.conditions)
    }

    /// What was absorbed since `mark`, as the result for `term`, without undefined-term reports:
    /// the caller takes it only where none was raised. Where `\bottom` was found since `mark`
    /// ([`FoundBottom`]) is kept, without a naming by `outside`, the lineage's `total` step taken
    /// before `mark`: that naming was the step's, not the work since `mark`'s. It shares what was
    /// absorbed.
    pub(super) fn since(
        &self,
        mark: &AccumulatedMark,
        term: Term,
        outside: Option<&Term>,
    ) -> Simplification {
        Simplification {
            term,
            conditions: self.conditions.since(&mark.conditions),
            applied_rules: self.applied_rules.since(&mark.applied_rules),
            effects: self.effects.since(&mark.effects),
            exhausted: None,
            undefined_term: None,
            contradicted_total: None,
            // Where `\bottom` was found since `mark`, when it was: the part's own report, which a
            // lineage that takes the part as a step's result reads as it reads a fresh one's.
            bottom: if self.bottom == mark.bottom {
                None
            } else {
                self.bottom.clone().map(|mut found| {
                    if let Some(outside) = outside {
                        found.named.retain(|named| named != outside);
                    }
                    found
                })
            },
        }
    }

    /// The accumulated result for `term`.
    #[inline(never)]
    pub(super) fn finish(self, term: Term) -> Simplification {
        Simplification {
            term,
            conditions: self.conditions,
            applied_rules: self.applied_rules,
            effects: self.effects,
            exhausted: self.exhausted,
            undefined_term: self.undefined_term,
            contradicted_total: self.contradicted_total,
            bottom: self.bottom,
        }
    }
}
