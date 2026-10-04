//! This definition-layer module holds no algorithm; every function in it is constant time and has
//! no dedicated counter.
//!
//! The typed writer of `total` on a compiler-generated function production.
//!
//! `total` on a function symbol states that every application of it denotes exactly one value.
//! A pass that generates a function production may claim it only after discharging that
//! obligation, and [`Attributes::declare_total`] takes the discharge as a [`TotalityWitness`].
//! Three reasons carry evidence from a judgement; three named reasons state obligations that the
//! generating rules or hooks discharge.

use serde_json::Value;

use super::{Attributes, attribute_keys::AttributeKey};
use crate::kompile::{DefinedBody, DefinedInitializer, SoleGenerator};

/// Evidence, or a named reason, that every application of a compiler-generated function
/// production denotes exactly one value.
///
/// Its field is private, so a witness exists only through the constructors below. Three reasons
/// carry evidence that only the judgement discharging the obligation can mint:
/// [`TotalityWitness::defined_body`] takes a [`DefinedBody`],
/// [`TotalityWitness::sole_generator`] takes a [`SoleGenerator`], and
/// [`TotalityWitness::nullary_initializer`] takes a [`DefinedInitializer`]. The other three are named
/// reasons without evidence: they compile at any call site, so they force the writer to state
/// which obligation the generated rules or hook discharge, for review to check, but do not prove
/// that it is discharged.
#[must_use]
pub(crate) struct TotalityWitness(TotalityReason);

/// Why a generated function production is total; see [`TotalityWitness`].
enum TotalityReason {
    DefinedBody,
    SoleGenerator,
    CoveringPredicate,
    KEquality,
    Hooked,
    NullaryInitializer,
}

impl TotalityWitness {
    /// Evidence: the generated lambda covers every argument tuple and each equation builds
    /// a defined result with a trivial postcondition, so every application denotes one value.
    /// Deferred evidence binds the covering receipt to its own main-catalog equations.
    pub(crate) fn defined_body(_: DefinedBody) -> Self {
        Self(TotalityReason::DefinedBody)
    }

    /// Evidence: the projection's source is the only alternative of its sort's no-junk axiom, so
    /// every value of the sort is an application of the source and the projection's equation
    /// gives it exactly one value.
    pub(crate) fn sole_generator(_: SoleGenerator) -> Self {
        Self(TotalityReason::SoleGenerator)
    }

    /// Reason: a generated predicate whose rules decide every argument (a `true` rule and an
    /// `owise` `false` rule).
    pub(crate) fn covering_predicate() -> Self {
        Self(TotalityReason::CoveringPredicate)
    }

    /// Reason: `:=K` or `:/=K` on two defined K terms is `true` or `false`.
    pub(crate) fn k_equality() -> Self {
        Self(TotalityReason::KEquality)
    }

    /// Reason: a hooked function whose hook is defined on every argument.
    pub(crate) fn hooked() -> Self {
        Self(TotalityReason::Hooked)
    }

    /// Evidence: every generated rule of the nullary initializer has a defined right-hand side
    /// and a trivial postcondition, and an unconditional equation covers its only argument tuple.
    pub(crate) fn nullary_initializer(_: DefinedInitializer) -> Self {
        Self(TotalityReason::NullaryInitializer)
    }
}

impl Attributes {
    /// The only typed writer of `total` on a generated production; writes the bare marker
    /// through `insert`.
    ///
    /// Every reason discharges the same claim, so the witness decides whether the marker may be
    /// written, not what is written. The match has no wildcard arm, so a new reason must be
    /// placed among the evidence-carrying or the named reasons.
    pub(crate) fn declare_total(&mut self, witness: TotalityWitness) {
        let TotalityWitness(reason) = witness;
        match reason {
            // Evidence minted by the judgement that discharges the obligation.
            TotalityReason::DefinedBody
            | TotalityReason::SoleGenerator
            | TotalityReason::NullaryInitializer => {}
            // Named reasons without evidence.
            TotalityReason::CoveringPredicate
            | TotalityReason::KEquality
            | TotalityReason::Hooked => {}
        }
        self.insert(AttributeKey::Total.as_str(), Value::String(String::new()));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_named_reason_writes_the_bare_total_marker() {
        let mut expected = Attributes::default();
        expected.insert(AttributeKey::Total.as_str(), Value::String(String::new()));
        for witness in [
            TotalityWitness::covering_predicate(),
            TotalityWitness::k_equality(),
            TotalityWitness::hooked(),
        ] {
            let mut attributes = Attributes::default();
            attributes.declare_total(witness);
            assert_eq!(attributes, expected);
        }
    }
}
