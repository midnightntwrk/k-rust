//! The scope every coverage family shares: which authored sentences are no obligation of any
//! family, and why (module documentation of [`crate::coverage`], "Families").
//!
//! An obligation is derived from the definition alone, so the scope is a function of the
//! definition and the front end's marks, never of what a program ran. A sentence is out of the
//! scope, in this order, when it is:
//!
//! - [`Excluded::OutOfScope`]: a simplification, a `symbolic` equation or a `#Ceil` equation,
//!   which states a fact of the definition's functions that the definition means the same
//!   without, so no step computes it;
//! - [`Excluded::NoCoverageSignal`]: a rule none of whose compiled ids k-rust's run coverage can
//!   name, so no program can be shown to reach it;
//! - [`Excluded::ClaimHelper`]: an equation of a function only claims apply
//!   ([`FlowManifest::is_claim_helper`]). No initializer, program production or sentence a run
//!   can take applies it, so a run reaches it only through an input that applies it, and an
//!   edit of it changes no step of any other run; the claims it serves are what tell its
//!   equations apart, and a proof of the claims checks them. Such a sentence is no obligation
//!   whatever the programs did: an item that became one because a program applied it would make
//!   the universe depend on the corpus.
//!
//! Every family reads this one predicate: the rules family gives the sentence the exclusion's
//! status; the requirements, syntax and field-value families read those statuses; the rule
//! windows family keeps only sentences in scope as nodes of its may-follow graph; and the flips
//! family moves a derived flip that changes a sentence outside the scope to `not_generated`
//! ([`crate::flips::scoped`]).

use super::{CLAIM_HELPER, NO_COVERAGE_SIGNAL, OUT_OF_SCOPE};
use crate::{admit::AdmittedSpec, manifest::FlowManifest, results::no_coverage_signal};
use k_rust::{
    definition::{AttributeKey, Sentence},
    kast::Term,
};
use kink_patch::SentenceRef;
use std::collections::BTreeMap;

/// Why a sentence is outside the scope of every coverage family.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Excluded {
    /// A simplification, `symbolic` or ceil equation ([`OUT_OF_SCOPE`]).
    OutOfScope,
    /// A rule k-rust's run coverage cannot name ([`NO_COVERAGE_SIGNAL`]), with why.
    NoCoverageSignal(&'static str),
    /// An equation of a function only claims apply ([`CLAIM_HELPER`]).
    ClaimHelper,
}

impl Excluded {
    /// The rules family's status of a sentence so excluded, and the `reason` of a flip moved to
    /// `not_generated` for it.
    pub(crate) fn status(self) -> &'static str {
        match self {
            Self::OutOfScope => OUT_OF_SCOPE,
            Self::NoCoverageSignal(_) => NO_COVERAGE_SIGNAL,
            Self::ClaimHelper => CLAIM_HELPER,
        }
    }

    /// Why the sentence is no obligation, as a rules item's `reason` states it.
    pub(crate) fn reason(self) -> &'static str {
        match self {
            Self::OutOfScope => {
                "a simplification, symbolic or ceil equation states a fact of the definition's \
                 functions, which the definition means the same without: no step computes it"
            }
            Self::NoCoverageSignal(reason) => reason,
            Self::ClaimHelper => {
                "an equation of a function only claims apply: no run of the definition reaches it \
                 except through an input that applies it, and a proof of the claims it serves \
                 checks it"
            }
        }
    }
}

/// The scope of a specification under a manifest's front-end marks.
pub(crate) struct Scope<'m> {
    no_signal: BTreeMap<SentenceRef, &'static str>,
    manifest: &'m FlowManifest,
}

impl<'m> Scope<'m> {
    /// The scope of `spec` with `manifest`'s claim helpers.
    pub(crate) fn of(spec: &AdmittedSpec, manifest: &'m FlowManifest) -> Self {
        Self {
            no_signal: no_coverage_signal(spec),
            manifest,
        }
    }

    /// Why the authored `sentence` at `at` is outside the scope, in the order out-of-scope,
    /// no-coverage-signal, claim-helper; `None` where it is in scope. Only a rule can be
    /// excluded.
    pub(crate) fn excludes(&self, at: &SentenceRef, sentence: &Sentence) -> Option<Excluded> {
        let Sentence::Rule {
            body, attributes, ..
        } = sentence
        else {
            return None;
        };
        if attributes.has(AttributeKey::Simplification)
            || attributes.has(AttributeKey::Symbolic)
            || ceil_left_side(body)
        {
            Some(Excluded::OutOfScope)
        } else if let Some(reason) = self.no_signal.get(at) {
            Some(Excluded::NoCoverageSignal(reason))
        } else if attributes
            .string(AttributeKey::Label)
            .is_some_and(|label| self.manifest.is_claim_helper(&at.module, label))
        {
            Some(Excluded::ClaimHelper)
        } else {
            None
        }
    }

    /// [`Self::excludes`] of the baseline sentence of `spec` at `at`; `None` where it is in
    /// scope or `spec` has no sentence there.
    pub(crate) fn excludes_at(&self, spec: &AdmittedSpec, at: &SentenceRef) -> Option<Excluded> {
        self.excludes(at, spec.loaded.baseline.sentence(at)?)
    }
}

/// Whether a rule's body rewrites a `#Ceil` application at its top.
fn ceil_left_side(body: &Term) -> bool {
    match body {
        Term::Annotated { term, .. } => ceil_left_side(term),
        Term::Rewrite { left, .. } => ceil_left_side(left),
        Term::Apply { label, .. } => label.name == "#Ceil",
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;

    /// A claim helper is named by its module and its label, bare or qualified by that module,
    /// and matches a sentence of that module that writes its label either way; a sentence of
    /// another module does not, whether its label is bare or qualified by the helper's module.
    #[test]
    fn a_claim_helper_matches_its_label_bare_or_qualified() {
        let manifest = FlowManifest::decode(
            "[spec]\nentry = \"m.k\"\nmain_module = \"M\"\n[[program]]\nid = \"a\"\ntext = \"a\"\n",
            Path::new("corpus"),
        )
        .unwrap()
        .with_claim_helpers([
            ("M".to_owned(), "bare".to_owned()),
            ("M".to_owned(), "M.qualified".to_owned()),
        ]);
        for (module, label) in [
            ("M", "bare"),
            ("M", "M.bare"),
            ("M", "qualified"),
            ("M", "M.qualified"),
        ] {
            assert!(manifest.is_claim_helper(module, label), "{module} {label}");
        }
        assert!(!manifest.is_claim_helper("N", "bare"));
        assert!(!manifest.is_claim_helper("N", "M.bare"));
        assert!(!manifest.is_claim_helper("N", "M.qualified"));
        assert!(!manifest.is_claim_helper("M", "N.bare"));
        assert!(!manifest.is_claim_helper("M", "other"));
    }

    /// Each exclusion is its rules status, and a claim helper's reason says why it is no
    /// obligation.
    #[test]
    fn each_exclusion_names_its_rules_status() {
        assert_eq!(Excluded::OutOfScope.status(), OUT_OF_SCOPE);
        let silent = Excluded::NoCoverageSignal("compiles to no rule");
        assert_eq!(silent.status(), NO_COVERAGE_SIGNAL);
        assert_eq!(silent.reason(), "compiles to no rule");
        assert_eq!(Excluded::ClaimHelper.status(), CLAIM_HELPER);
        assert!(Excluded::ClaimHelper.reason().contains("only claims apply"));
    }
}
