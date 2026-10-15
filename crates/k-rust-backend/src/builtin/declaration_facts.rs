//! The facts about a definition's declarations that the evaluation of a hooked application reads,
//! beyond the application itself.
//!
//! The evaluators reachable from the `BOOL`, `INT`, `STRING` and `FLOAT` hooks, and the checks
//! the evaluation entry applies around them, read a definition's sorts only through these
//! facts: the kind of a sort's domain values (the `FLOAT` operands' kind check, the check of the
//! domain values a hook built, `STRING.string2token`'s result) and whether a sort has domain
//! values at all (`STRING.string2token`). The subsort order is the third fact: it decides where
//! a term of one sort stands at another, as an injection. So a caller that has the declarations
//! of a definition without having loaded it, such as the frontend's constant fold before it
//! emits the definition, evaluates such an application exactly as the loaded definition would
//! ([`super::evaluate_declared`]).
//!
//! The `KEQUAL`, collection, `KRYPTO`, `IO` and `SUBSTITUTION` evaluators read more of a loaded
//! definition (its sort graph's overlaps, its symbols, its collection metadata) and keep reading
//! it from the definition.

use crate::{
    definition::BackendDefinition,
    term::{DomainKind, Sort},
};

/// The declarations of a definition that decide how its hooked applications evaluate: the kind
/// of each sort's domain values, which sorts have domain values, and the subsort order.
///
/// A definition states them in its own sorts (`Sort`): a loaded definition in its KORE sorts,
/// the frontend in the sorts it emits. Every implementation must give the answers the emitted
/// definition gives once it is loaded, so that an evaluation over these facts and one over the
/// loaded definition agree.
pub trait DeclarationFacts {
    type Sort;

    /// How the domain values of `sort` denote its elements: the kind
    /// [`DomainKind::of_declared_sort`] derives from the sort head's declaration, or `None` when
    /// the sort has no domain values or no kind.
    fn domain_kind(&self, sort: &Self::Sort) -> Option<DomainKind>;

    /// Whether the head of `sort` is declared with domain values (`hasDomainValues`).
    fn has_domain_values(&self, sort: &Self::Sort) -> bool;

    /// Whether `sub` is `sup` or a subsort of it in the order the definition's subsort axioms
    /// state. An open question (a sort variable, an undeclared sort) is not a subsort.
    fn check_subsort(&self, sub: &Self::Sort, sup: &Self::Sort) -> bool;
}

impl DeclarationFacts for BackendDefinition {
    type Sort = Sort;

    fn domain_kind(&self, sort: &Sort) -> Option<DomainKind> {
        Self::domain_kind(self, sort)
    }

    fn has_domain_values(&self, sort: &Sort) -> bool {
        matches!(sort, Sort::Application { name, .. }
            if self.sorts().get(name).is_some_and(|info| info.has_domain_values))
    }

    fn check_subsort(&self, sub: &Sort, sup: &Sort) -> bool {
        matches!(self.sort_graph().check_subsort(sub, sup), Ok(true))
    }
}
