//! The sub-cases of one rule application, each with its own type (I5).
//!
//! For one application of a rule to a subject `S`:
//!
//! - the applicability `A` ([`Applicability`]) is the existential closure, over the variables
//!   the match introduced, of the match conditions and the undecided `requires`: the instances
//!   of `S` the rule applies to;
//! - the defined sub-case `D` ([`DefinedSubcase`]) is the closure of those conditions and of
//!   what the result carries ([`CarriedCondition`]: the right-hand side's obligations, its
//!   definedness and the rule's own open `ensures`): the instances the application takes to a
//!   defined result. `D` implies `A`, and the instances of `A /\ not D` have no successor from
//!   this application;
//! - the remainder `R = not A` ([`Remainder`]) is what the application leaves to lower
//!   priorities.
//!
//! The sequential step offers the next rule of a priority `S /\ not D_j` over the earlier rules
//! `j` of that priority, because an instance where an earlier rule applies but its result is
//! undefined may get a successor from a later rule of the same priority; and it offers the next
//! priority `S /\ R_j`, because a rule that applies blocks the lower priorities whether its
//! result is defined or not. [`SequentialSubject`] is the only place where the step's subject
//! is narrowed, and it takes a `Remainder` into the subject only when the priority ends.

use crate::{
    condition::{Obligation, ResultConditions},
    rule::Predicate,
    simplify::SimplificationError,
    stop::Stoppable,
};

use super::{
    Pattern,
    apply::{conjoin_flat, negation},
    extend_unique, quantify_introduced_variables,
};

pub(super) use subject::SequentialSubject;

/// The applicability `A` of a rule application: the instances of the subject the rule applies
/// to.
#[repr(transparent)]
#[must_use]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(super) struct Applicability(Predicate);

/// The defined sub-case `D` of a rule application: the instances of the subject the application
/// takes to a defined result. It implies the application's [`Applicability`].
#[repr(transparent)]
#[must_use]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(super) struct DefinedSubcase(Predicate);

/// The remainder `R = not A` of a rule application: the instances of the subject the rule does
/// not apply to, which a lower priority may rewrite.
#[repr(transparent)]
#[must_use]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(super) struct Remainder(Predicate);

impl Applicability {
    /// The existential closure of `conditions` over the variables `pattern` does not have.
    pub(super) fn close(pattern: &Pattern, conditions: Vec<Predicate>) -> Self {
        Self(quantify_introduced_variables(pattern, conditions))
    }

    /// `not A`, with `not \top` written `\bottom`.
    pub(super) fn remainder(&self) -> Remainder {
        if self.0 == Predicate::True {
            Remainder(Predicate::False)
        } else {
            Remainder(Predicate::Not(Box::new(self.0.clone())))
        }
    }

    /// `A /\ not D`: the instances the rule applies to where this application's result is
    /// undefined. It is the sub-case a carried result condition leaves without a successor, so
    /// it is what the application rewrites to bottom there.
    pub(super) fn outside(&self, defined: &DefinedSubcase) -> Self {
        Self(conjoin_flat([self.0.clone(), negation(&defined.0)]))
    }

    pub(super) fn as_predicate(&self) -> &Predicate {
        &self.0
    }
}

impl Remainder {
    /// The applicability this remainder is the complement of (the inverse of
    /// [`Applicability::remainder`]).
    pub(super) fn applicability(&self) -> Applicability {
        Applicability(match &self.0 {
            Predicate::False => Predicate::True,
            Predicate::Not(applicability) => (**applicability).clone(),
            remainder => Predicate::Not(Box::new(remainder.clone())),
        })
    }

    pub(super) fn as_predicate(&self) -> &Predicate {
        &self.0
    }
}

impl DefinedSubcase {
    /// Nothing is carried: the application has a defined result wherever it applies, `D = A`.
    pub(super) fn whole(applicability: &Applicability) -> Self {
        Self(applicability.0.clone())
    }

    /// The existential closure, over the variables `pattern` does not have (those the match
    /// introduced and the freshened existentials), of the applicability's conditions and the
    /// carried condition.
    pub(super) fn restricted(
        pattern: &Pattern,
        applicability_conditions: &[Predicate],
        carried: &CarriedCondition,
    ) -> Self {
        let mut defining = applicability_conditions.to_vec();
        defining.extend(
            carried
                .0
                .iter()
                .map(|obligation| obligation.as_predicate().clone()),
        );
        Self(quantify_introduced_variables(pattern, defining))
    }

    /// `not D`, the instances the application does not take to a defined result. When `D` is
    /// the application's whole applicability that is its `remainder`, the form the remainder
    /// takes when the priority ends.
    pub(super) fn complement(&self, remainder: &Remainder) -> Predicate {
        if self.0 == remainder.applicability().0 {
            remainder.0.clone()
        } else {
            negation(&self.0)
        }
    }

    /// `not D` with double negation and the constants folded, the conjunct by which a trivial
    /// entry excludes the instances this application takes to a defined result.
    pub(super) fn negation(&self) -> Predicate {
        negation(&self.0)
    }

    pub(super) fn as_predicate(&self) -> &Predicate {
        &self.0
    }
}

/// What a rewrite result adds to its applicability: the obligations the result exists under
/// (the right-hand side's obligations, its carried definedness and the rule's own open
/// `ensures`), in that order, each once, without the applicability's own conditions and without
/// `\top`.
///
/// It is built only from [`Obligation`]s, so an assumption of the right-hand side's
/// simplification (an applied equation's open `ensures`, which the definition asserts wherever
/// that equation applies) cannot narrow the defined sub-case: `ResultConditions::obligations`
/// leaves the assumptions out, and an obligation equal to one of them is discharged by it.
#[must_use]
pub(super) struct CarriedCondition(Vec<Obligation>);

impl CarriedCondition {
    /// `None` when the result adds nothing to its applicability.
    pub(super) fn collect(
        obligations: impl IntoIterator<Item = Obligation>,
        applicability_conditions: &[Predicate],
        rhs_conditions: &ResultConditions,
    ) -> Option<Self> {
        let mut carried: Vec<Obligation> = Vec::new();
        for obligation in obligations {
            let predicate = obligation.as_predicate();
            if *predicate != Predicate::True
                && !applicability_conditions.contains(predicate)
                && !rhs_conditions.asserts(predicate)
                && !carried.contains(&obligation)
            {
                carried.push(obligation);
            }
        }
        (!carried.is_empty()).then_some(Self(carried))
    }

    /// The conjunction of the carried obligations, which a `Carried` trivial entry reports.
    pub(super) fn conjunction(&self) -> Predicate {
        match self.0.as_slice() {
            [obligation] => obligation.as_predicate().clone(),
            obligations => Predicate::And(
                obligations
                    .iter()
                    .map(|obligation| obligation.as_predicate().clone())
                    .collect(),
            ),
        }
    }
}

/// The part of a subject the sequential step offers to its next rule (I5).
///
/// Declared in its own module so that nothing outside it reaches the pattern it narrows: the
/// step reads the pattern through [`SequentialSubject::pattern`] and narrows it only through
/// [`SequentialSubject::exclude_defined`] within a priority and
/// [`SequentialSubject::enter_priority`] when a priority ends.
mod subject {
    use super::{
        DefinedSubcase, Pattern, Predicate, Remainder, SimplificationError, Stoppable,
        extend_unique,
    };

    pub(in crate::rewrite) struct SequentialSubject {
        pattern: Pattern,
        /// The remainders of the current priority's applications, which narrow the subject when
        /// the priority ends. Only a `Remainder` enters it.
        blocked: Vec<Predicate>,
        priority: Option<u8>,
    }

    /// What one [`SequentialSubject::exclude_defined`] did.
    #[must_use]
    pub(in crate::rewrite) struct Narrowing {
        /// The subject's constraints grew.
        pub(in crate::rewrite) grew: bool,
        /// The defined sub-case is narrower than the applicability, so the exclusion also
        /// derives from the work that decided what the result carries.
        pub(in crate::rewrite) restricted: bool,
    }

    impl SequentialSubject {
        /// The whole `subject`, before any priority.
        pub(in crate::rewrite) fn new(subject: &Pattern) -> Self {
            Self {
                pattern: subject.clone(),
                blocked: Vec::new(),
                priority: None,
            }
        }

        pub(in crate::rewrite) fn pattern(&self) -> &Pattern {
            &self.pattern
        }

        /// The priority whose rules the subject is being offered to.
        pub(in crate::rewrite) fn priority(&self) -> Option<u8> {
            self.priority
        }

        /// Within the current priority: drop the instances `defined` takes to a defined
        /// result, so the later rules of the priority are offered the instances where the
        /// application's result is undefined; `remainder` waits for the priority's end.
        pub(in crate::rewrite) fn exclude_defined(
            &mut self,
            defined: &DefinedSubcase,
            remainder: &Remainder,
        ) -> Narrowing {
            extend_unique(
                &mut self.blocked,
                std::iter::once(remainder.as_predicate().clone()),
            );
            let outside = defined.complement(remainder);
            let restricted = outside != *remainder.as_predicate();
            let before = self.pattern.constraints.len();
            extend_unique(&mut self.pattern.constraints, std::iter::once(outside));
            Narrowing {
                grew: self.pattern.constraints.len() != before,
                restricted,
            }
        }

        /// A refuted application of the current priority: it has no defined sub-case, and its
        /// `remainder` waits for the priority's end.
        pub(in crate::rewrite) fn block(&mut self, remainder: Remainder) {
            extend_unique(&mut self.blocked, std::iter::once(remainder.0));
        }

        /// End the current priority and move to `priority` (`None` after the last rule): every
        /// waiting remainder narrows the subject, since a rule that applies blocks the lower
        /// priorities whether its result is defined or not. Whether the subject's constraints
        /// grew.
        pub(in crate::rewrite) fn enter_priority(&mut self, priority: Option<u8>) -> bool {
            let before = self.pattern.constraints.len();
            extend_unique(&mut self.pattern.constraints, self.blocked.drain(..));
            self.priority = priority;
            self.pattern.constraints.len() != before
        }

        /// Replace the subject's constraints by `subject`'s followed by `simplify` of the
        /// current ones under `subject`'s, an equivalent condition on `subject`'s instances.
        /// A failed simplification leaves the subject as it is.
        pub(in crate::rewrite) fn resimplify(
            &mut self,
            subject: &Pattern,
            simplify: impl FnOnce(
                &[Predicate],
            ) -> Stoppable<Result<Vec<Predicate>, SimplificationError>>,
        ) -> Stoppable<Result<(), SimplificationError>> {
            let constraints = match simplify(&self.pattern.constraints)? {
                Ok(constraints) => constraints,
                Err(error) => return Ok(Err(error)),
            };
            self.pattern.constraints = subject.constraints.clone();
            extend_unique(&mut self.pattern.constraints, constraints);
            Ok(Ok(()))
        }

        pub(in crate::rewrite) fn into_pattern(self) -> Pattern {
            self.pattern
        }
    }
}

/// Alpha equality of the roles a trivial entry stores, for the cascade differential tests: a
/// renaming of bound variables keeps the role.
#[cfg(test)]
mod alpha {
    use super::{Applicability, Remainder};
    use crate::tests::alpha::{AlphaComparable, AlphaContext, collect_predicate, rename_predicate};

    impl AlphaComparable for Applicability {
        fn collect_alpha(&self, other: &Self, context: &mut AlphaContext) -> Result<(), String> {
            collect_predicate(&self.0, &other.0, context)
        }

        fn rename_alpha(&self, context: &AlphaContext) -> Result<Self, String> {
            Ok(Self(rename_predicate(&self.0, context)))
        }
    }

    impl AlphaComparable for Remainder {
        fn collect_alpha(&self, other: &Self, context: &mut AlphaContext) -> Result<(), String> {
            collect_predicate(&self.0, &other.0, context)
        }

        fn rename_alpha(&self, context: &AlphaContext) -> Result<Self, String> {
            Ok(Self(rename_predicate(&self.0, context)))
        }
    }
}
