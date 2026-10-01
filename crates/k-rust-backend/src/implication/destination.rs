//! The destination of one implication check, in the form the match against it assumes.
//!
//! The match compares both sides of the implication in the definition's normal form under the
//! antecedent's constraints: a destination term with an unevaluated function application leaves
//! an obligation the definition's equations could have discharged. The fields are private to
//! this module, so no other code, including the rest of `implication`, can build a
//! [`Destination`] except through [`Destination::prepare`] (E0451); the match and the discharge
//! take a `&Destination`, so every destination they compare against, on the single- and the
//! multi-destination path alike, has been simplified.

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
/// type records that simplification was attempted.
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

    /// The prepared destination pattern.
    pub(super) fn pattern(&self) -> &Pattern {
        &self.pattern
    }

    /// The destination's existentials, freshened apart from the antecedent.
    pub(super) fn existentials(&self) -> &BTreeSet<Variable> {
        &self.existentials
    }
}
