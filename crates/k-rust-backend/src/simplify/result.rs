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

use crate::{
    builtin::BuiltinEffect,
    condition::{CarriedObligations, ResultConditions},
    definition::BackendDefinition,
    rule::{Predicate, RewriteRule},
    term::Term,
};

use super::{BudgetExhaustion, ContradictedTotal};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Simplification {
    pub term: Term,
    /// The conjuncts the simplification conjoins to `term`, each an obligation or an assumption.
    conditions: ResultConditions,
    pub applied_rules: Vec<String>,
    pub effects: Vec<BuiltinEffect>,
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
    pub fn conditions(&self) -> &ResultConditions {
        &self.conditions
    }

    /// Every conjunct the simplification conjoins to its term, in order
    /// (`conditions().as_slice()`).
    pub fn constraints(&self) -> &[Predicate] {
        self.conditions.as_slice()
    }

    pub fn into_parts(self) -> SimplificationParts {
        SimplificationParts {
            term: self.term,
            conditions: self.conditions,
            applied_rules: self.applied_rules,
            effects: self.effects,
            exhausted: self.exhausted,
            undefined_term: self.undefined_term,
            contradicted_total: self.contradicted_total,
        }
    }

    /// `term` with no step taken at its root: nothing conjoined, no rule applied.
    pub(super) fn irreducible(term: Term) -> Self {
        Self {
            term,
            conditions: ResultConditions::default(),
            applied_rules: Vec::new(),
            effects: Vec::new(),
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
            conditions: ResultConditions::refuted(),
            applied_rules: Vec::new(),
            effects: Vec::new(),
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
        outcome: HookOutcome,
        hook: &str,
        known: &[Predicate],
    ) -> Self {
        let (term, conditions, effects, undefined_term) = match outcome {
            HookOutcome::Value(value) => (
                value,
                ResultConditions::hook_arguments(definition, application, known),
                Vec::new(),
                None,
            ),
            HookOutcome::Effect(value, effect) => (
                value,
                ResultConditions::hook_arguments(definition, application, known),
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
        Self {
            term,
            conditions,
            applied_rules: vec![format!("builtin:{hook}")],
            effects,
            exhausted: None,
            undefined_term,
            contradicted_total: None,
        }
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
            conditions: ResultConditions::equation(ensures, carried),
            applied_rules: vec![rule.attributes.unique_id.clone()],
            effects: Vec::new(),
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
            conditions: ResultConditions::refuted(),
            applied_rules: vec![rule.attributes.unique_id.clone()],
            effects: Vec::new(),
            exhausted: None,
            undefined_term: None,
            contradicted_total: None,
        }
    }
}

/// The running result of a fixed point over parts (`simplify_with_budget`, `simplify_children`).
///
/// [`Accumulated::absorb`] appends a part's conditions, applied rules and effects, and keeps the
/// first budget exhaustion; the caller resolves the part's undefined-term reports, which depend on
/// the lineage, and sets `undefined_term` and `contradicted_total` itself.
#[derive(Default)]
pub(super) struct Accumulated {
    conditions: ResultConditions,
    pub(super) applied_rules: Vec<String>,
    pub(super) effects: Vec<BuiltinEffect>,
    pub(super) exhausted: Option<BudgetExhaustion>,
    pub(super) undefined_term: Option<Term>,
    pub(super) contradicted_total: Option<Box<ContradictedTotal>>,
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
        self.applied_rules.extend(applied_rules);
        self.effects.extend(effects);
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
            .append(ResultConditions::top_equation(obligations));
    }

    /// The accumulated result for `term`.
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
