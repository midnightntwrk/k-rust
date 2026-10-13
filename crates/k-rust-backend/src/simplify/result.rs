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
        Self {
            term,
            conditions: conjuncts(ResultConditions::equation(ensures, carried)),
            applied_rules: Log::from(vec![rule.attributes.unique_id.clone()]),
            effects: Log::new(),
            exhausted: None,
            undefined_term: None,
            contradicted_total: None,
        }
    }

    /// The result of `rule` on a subject `term` that is empty under the path condition: the
    /// subject is retained and `\bottom` is its only constraint, so the caller merges it as it
    /// merges any other constraint set and the pattern becomes `\bottom` as a whole.
    pub(super) fn bottom_subject(rule: &RewriteRule, term: &Term) -> Self {
        Self {
            term: term.clone(),
            conditions: conjuncts(ResultConditions::refuted()),
            applied_rules: Log::from(vec![rule.attributes.unique_id.clone()]),
            effects: Log::new(),
            exhausted: None,
            undefined_term: None,
            contradicted_total: None,
        }
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
/// the lineage, and sets `undefined_term` and `contradicted_total` itself. Appending shares the
/// part's logs ([`Log::append`]), so absorbing a part costs the same whatever it holds.
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
}

impl AccumulatedMark {
    /// Take `accumulated`'s current reports in place of those held at the mark.
    pub(super) fn refresh_reports(&mut self, accumulated: &Accumulated) {
        self.exhausted = accumulated.exhausted;
        self.undefined_term.clone_from(&accumulated.undefined_term);
        self.contradicted_total
            .clone_from(&accumulated.contradicted_total);
    }
}

/// What [`Accumulated::absorb`] leaves of a part: its term and its undefined-term reports.
pub(super) struct Absorbed {
    pub(super) term: Term,
    pub(super) undefined_term: Option<Term>,
    pub(super) contradicted_total: Option<Box<ContradictedTotal>>,
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
        } = part;
        self.conditions.append(conditions);
        self.applied_rules.append(applied_rules);
        self.effects.append(effects);
        self.exhausted = self.exhausted.or(exhausted);
        Absorbed {
            term,
            undefined_term,
            contradicted_total,
        }
    }

    /// The `\top` equation `rule_id` applied to an operand of a term-level `\and`, with its open
    /// binding obligations ([`ResultConditions::top_equation`]).
    pub(super) fn top_equation(&mut self, rule_id: String, obligations: Vec<Predicate>) {
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
    }

    /// The conditions absorbed since `mark`.
    pub(super) fn constraints_since(&self, mark: &AccumulatedMark) -> Log<Conjunct> {
        self.conditions.since(&mark.conditions)
    }

    /// What was absorbed since `mark`, as the result for `term`, without reports: the caller
    /// takes it only where no report was raised. It shares what was absorbed.
    pub(super) fn since(&self, mark: &AccumulatedMark, term: Term) -> Simplification {
        Simplification {
            term,
            conditions: self.conditions.since(&mark.conditions),
            applied_rules: self.applied_rules.since(&mark.applied_rules),
            effects: self.effects.since(&mark.effects),
            exhausted: None,
            undefined_term: None,
            contradicted_total: None,
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
        }
    }
}
