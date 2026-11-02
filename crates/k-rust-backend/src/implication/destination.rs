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

use super::{ImplicationError, freshen_existentials, rename_as_freshened, simplify_consequent};

/// One consequent of a check: the pattern the check simplifies and matches (`checked`), and the
/// pattern its caller wrote (`written`), which denote the same set on every valuation. They are
/// the same pattern ([`Consequent::as_written`]) except for a proof's destination, whose ground
/// subterms the proof has simplified once (`proof::prepare_destinations`); the written form then
/// decides what the check does where the prepared one would decide otherwise (whether the
/// destination is kept unsimplified, and what a failed simplification keeps), so that each check
/// takes the steps it would take on the written form.
#[derive(Clone, Copy)]
pub(crate) struct Consequent<'a> {
    pub(crate) checked: &'a Pattern,
    pub(crate) written: &'a Pattern,
}

impl<'a> Consequent<'a> {
    /// A consequent checked as written.
    pub(crate) fn as_written(pattern: &'a Pattern) -> Self {
        Self {
            checked: pattern,
            written: pattern,
        }
    }
}

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
    /// then simplify its checked form under the antecedent's constraints (`simplify_consequent`).
    ///
    /// A stop is returned on the outer layer: it belongs to the operation that runs the check
    /// and says nothing about the destination.
    pub(super) fn prepare(
        definition: &BackendDefinition,
        antecedent: &Pattern,
        consequent: Consequent<'_>,
        existentials: &BTreeSet<Variable>,
        options: SimplificationOptions,
        solver: &dyn SmtSolver,
    ) -> Stoppable<Result<Self, ImplicationError>> {
        // The renaming is chosen for the written form, as a check of it alone chooses it, and the
        // prepared form, which has the same variables, is renamed alike.
        let (written, existentials, renaming) =
            freshen_existentials(antecedent, consequent.written, existentials);
        let checked = if std::ptr::eq(consequent.checked, consequent.written) {
            written.clone()
        } else {
            rename_as_freshened(consequent.checked, &renaming)
        };
        simplify_consequent(definition, antecedent, checked, written, options, solver)
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
