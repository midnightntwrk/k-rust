//! The destination of one implication check, in the form the match against it assumes.
//!
//! The match compares both sides of the implication in the definition's normal form under the
//! antecedent's constraints: a destination term with an unevaluated function application leaves
//! an obligation the definition's equations could have discharged. The fields are private to
//! this module, so no other code, including the rest of `implication`, can build a
//! [`Destination`] except through its constructors (E0451); the match and the discharge take a
//! `&Destination`, so they compare against what a constructor prepared.

use std::collections::BTreeSet;

use crate::{
    definition::BackendDefinition,
    rewrite::Pattern,
    simplify::SimplificationOptions,
    smt::SmtSolver,
    stop::{Layered, Stoppable},
    term::Variable,
};

use super::{ImplicationError, freshen_existentials, simplify_consequent};

/// The destination of one implication check in the form the match against it assumes: its
/// existentials freshened apart from the antecedent, then simplified with the definition's
/// equations under the antecedent's constraints. A term that already carries the evaluated mark
/// is kept, and a simplification failure keeps the term as written (`simplify_consequent`); the
/// type records that simplification was attempted. The one exception is the temporary
/// [`Destination::unsimplified_disjunct`], which CBC-08-T12 removes.
pub(super) struct Destination {
    pattern: Pattern,
    existentials: BTreeSet<Variable>,
}

impl Destination {
    /// Freshen `consequent`'s `existentials` apart from `antecedent` (`freshen_existentials`),
    /// then simplify it under the antecedent's constraints (`simplify_consequent`).
    ///
    /// A stop is returned on the outer layer: it belongs to the operation that runs the check
    /// and says nothing about the destination.
    pub(super) fn prepare(
        definition: &BackendDefinition,
        antecedent: &Pattern,
        consequent: &Pattern,
        existentials: &BTreeSet<Variable>,
        options: SimplificationOptions,
        solver: &dyn SmtSolver,
    ) -> Stoppable<Result<Self, ImplicationError>> {
        let (pattern, existentials) = freshen_existentials(antecedent, consequent, existentials);
        simplify_consequent(definition, antecedent, pattern, options, solver)
            .map(|pattern| Self {
                pattern,
                existentials,
            })
            .layered()
    }

    /// One disjunct of a multi-destination check, freshened apart from `antecedent` but not
    /// simplified.
    ///
    /// Temporary: it keeps the multi-destination path's present behaviour until CBC-08-T12
    /// builds those disjuncts with [`Destination::prepare`] and removes this constructor.
    pub(super) fn unsimplified_disjunct(
        antecedent: &Pattern,
        consequent: &Pattern,
        existentials: &BTreeSet<Variable>,
    ) -> Self {
        let (pattern, existentials) = freshen_existentials(antecedent, consequent, existentials);
        Self {
            pattern,
            existentials,
        }
    }

    /// The prepared destination pattern.
    pub(super) fn pattern(&self) -> &Pattern {
        &self.pattern
    }

    /// The destination's existentials, freshened apart from the antecedent.
    pub(super) fn existentials(&self) -> &BTreeSet<Variable> {
        &self.existentials
    }
}
