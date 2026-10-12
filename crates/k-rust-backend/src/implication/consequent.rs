//! The match of an implication's destination term against its antecedent's term, and the
//! obligations it leaves.
//!
//! In `∀x̄. A → ∃ē. C`, a match `σ` of `C`'s term against `A`'s term binds variables of `C`. For
//! an existential `e ∈ ē`, `σ(e)` is a witness the consequent may choose. For a universal
//! `u ∉ ē`, `u` denotes the same value on both sides of the implication, so `σ(u) = s` is the
//! equation `u = s`, which `A` must entail; applying `σ(u)` to the rest of `C` is sound only
//! together with that equation (I6).
//!
//! [`ConsequentMatch`] keeps the universal bindings in [`UniversalBindings`], whose field is
//! private to an inline module: the only view of them is
//! [`UniversalBindings::with_equations`], which hands out their equations with them, so no
//! obligation builder can apply a universal binding and leave out its equation by omission. The
//! obligations are a [`ConsequentObligations`], which only this module builds, and witness
//! elimination takes nothing else.

#![deny(clippy::wildcard_enum_match_arm)]

use std::collections::BTreeSet;

use crate::{
    condition::instantiate_constraints,
    definition::BackendDefinition,
    matching::expand_implication_remainders,
    rewrite::Pattern,
    rule::Predicate,
    substitution::{Substitution, substitute},
    term::{Term, Variable},
};

use super::{Destination, remainder_obligation};
use universal::UniversalBindings;

/// The match of a consequent's term against an antecedent's term (I6): the bindings of the
/// consequent's existentials (witnesses) apart from those of its universal variables.
pub(super) struct ConsequentMatch {
    witnesses: Substitution,
    universal: UniversalBindings,
}

impl ConsequentMatch {
    /// Partition the match `substitution` by the consequent's `existentials`, moving entries: a
    /// binding of an existential is a witness, any other binds a universal variable.
    pub(super) fn new(substitution: Substitution, existentials: &BTreeSet<Variable>) -> Self {
        let (witnesses, universal): (Substitution, Substitution) = substitution
            .into_iter()
            .partition(|(variable, _)| existentials.contains(variable));
        Self {
            witnesses,
            universal: UniversalBindings::new(universal),
        }
    }

    /// One obligation list per branch of `remainder`'s expansion: the equations of the
    /// universal bindings, the remainder's equations under the match, and the destination's
    /// constraints under the match with their definedness stated (I1), each listed once and
    /// none that `known` already holds.
    ///
    /// A branch is one entry assignment of a closed destination map, or one placement of a
    /// destination list's items between its parts at positions of the current list's items;
    /// when the current list has a part of its own, the list's equation itself is one more
    /// branch, so the branches together are equivalent to the remainder (`matching`'s
    /// `expand_implication_remainders`). No branch is a false remainder.
    ///
    /// `known` holds facts of the antecedent's instances (I7), on which every obligation is
    /// decided.
    pub(super) fn obligation_branches(
        &self,
        definition: &BackendDefinition,
        destination: &Destination,
        remainder: Vec<(Term, Term)>,
        known: &[Predicate],
    ) -> Vec<ConsequentObligations> {
        let (universal, equations) = self.universal.with_equations();
        // The whole match, applied to the remainder and to the destination's constraints: the
        // witnesses and the universal bindings, whose equations lead every branch. The two
        // maps have disjoint keys (`new` partitions one substitution).
        let mut substitution = self.witnesses.clone();
        substitution.extend(
            universal
                .iter()
                .map(|(variable, value)| (variable.clone(), value.clone())),
        );
        let branches = expand_implication_remainders(definition, &substitution, &remainder)
            .unwrap_or_else(|| vec![remainder]);
        branches
            .into_iter()
            .map(|remainder| {
                branch_obligations(
                    definition,
                    destination.pattern(),
                    &substitution,
                    &equations,
                    remainder,
                    known,
                )
            })
            .collect()
    }

    /// Every binding of the match, witnesses and universal bindings alike, as the check reports
    /// them.
    pub(super) fn into_reported(self) -> Substitution {
        let mut reported = self.witnesses;
        reported.extend(self.universal.into_substitution());
        reported
    }
}

/// The obligations of one remainder branch. `substitution` applies the universal bindings, so it
/// comes with their `equations`, which lead the list.
fn branch_obligations(
    definition: &BackendDefinition,
    consequent: &Pattern,
    substitution: &Substitution,
    equations: &[Predicate],
    remainder: Vec<(Term, Term)>,
    known: &[Predicate],
) -> ConsequentObligations {
    let mut obligations = Vec::new();
    for equation in equations {
        if !obligations.contains(equation) {
            obligations.push(equation.clone());
        }
    }
    for (left, right) in remainder {
        let predicate = remainder_obligation(
            &substitute(&left, substitution),
            &substitute(&right, substitution),
        );
        if !obligations.contains(&predicate) {
            obligations.push(predicate);
        }
    }
    // The consequent's constraints under the match are a condition on the antecedent's instances
    // (I1): an atom over a term undefined on some of them is `⊥` there, so its definedness is
    // stated before the condition is simplified or decided, except where `known` holds it.
    for predicate in instantiate_constraints(&consequent.constraints, substitution)
        .with_definedness(definition, known)
    {
        if !obligations.contains(&predicate) {
            obligations.push(predicate);
        }
    }
    obligations.retain(|predicate| !known.contains(predicate));
    ConsequentObligations(obligations)
}

mod universal {
    use crate::{rule::Predicate, substitution::Substitution, term::Term};

    /// Bindings of variables the implication quantifies universally (I6). The field is private
    /// to this module: the bindings are applied only through [`Self::with_equations`].
    pub(super) struct UniversalBindings(Substitution);

    impl UniversalBindings {
        pub(super) fn new(bindings: Substitution) -> Self {
            Self(bindings)
        }

        /// The bindings with their equations, the only view of them. A universal variable
        /// denotes the same value on both sides of the implication, so the value the match
        /// bound it to is an equation the antecedent must entail, not a witness the consequent
        /// may choose; applying a binding is sound only under its equation.
        pub(super) fn with_equations(&self) -> (&Substitution, Vec<Predicate>) {
            let equations = self
                .0
                .iter()
                .map(|(variable, value)| {
                    Predicate::Equals(Term::variable(variable.clone()), value.clone())
                })
                .collect();
            (&self.0, equations)
        }

        /// The bindings as the check reports them, after the obligations are built.
        pub(super) fn into_substitution(self) -> Substitution {
            self.0
        }
    }
}

/// The obligations of one remainder branch of a [`ConsequentMatch`], before its existential
/// witnesses are eliminated. Only this module builds one, from a match whose universal
/// bindings carry their equations.
#[must_use]
pub(super) struct ConsequentObligations(Vec<Predicate>);

impl ConsequentObligations {
    /// Add the constraints a collection remainder's solution states, except those listed
    /// already or held by `known`.
    pub(super) fn add_solved(&mut self, solved: &[Predicate], known: &[Predicate]) {
        for predicate in solved {
            if !self.0.contains(predicate) && !known.contains(predicate) {
                self.0.push(predicate.clone());
            }
        }
    }

    pub(super) fn into_predicates(self) -> Vec<Predicate> {
        self.0
    }
}
