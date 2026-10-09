//! Result-scoped existentials, fresh values, and postconditions of
//! transitions (KF-040, KF-022).
//!
//! `#[k::exists(x: S, ..)]` declares binders that occur only in a transition's
//! result and `#[k::ensures(..)]` condition; K prints them as `?X:S`.
//! `#[k::fresh(x: S, ..)]` declares binders the step fills from K's
//! `<generatedCounter>` through the sort's `freshGenerator`; K prints them as
//! `!X:S`, and they too occur only in the result and the ensures condition.
//! `#[k::ensures(..)]` is an object-Bool postcondition over the result. The
//! helpers follow the claim helpers' payload grammar; a transition keeps its
//! own provenance roles (`RuleExistentialBinder*`, `RuleFreshBinder*`,
//! `RuleEnsures*`).

use syn::ext::IdentExt;
use syn::spanned::Spanned;
use syn::{Attribute, Ident, Meta, Path};

use super::pattern::{push_term_node_anchors, push_term_reference_candidates};
use crate::attribute::{ClaimBinder, ExistsAttribute};
use crate::parse::{KrsSyntax, checked_ordinal, unsupported_rule_signature};
use crate::term::push_record_field_anchors;
use crate::{
    ProvenanceAnchor, ProvenanceRole, ReferenceCandidate, SyntaxError, SyntaxErrorKind,
    TermExpression, TermSymbolKind, TokenRange,
};
use krs_ir::ProvenanceKey;

/// The `#[k::fresh]`, `#[k::exists]` and `#[k::ensures]` helpers of one transition.
#[derive(Clone, Debug, Default)]
pub struct RuleExistentials {
    exists: Option<ExistsAttribute>,
    fresh: Option<ExistsAttribute>,
    ensures: Option<TermExpression>,
    attributes: Vec<Attribute>,
}

/// Whether `attribute` is the `exists`, `fresh` or `ensures` helper (any path prefix).
fn is_existential_helper(attribute: &Attribute) -> bool {
    attribute.path().segments.len() >= 2
        && attribute.path().segments.last().is_some_and(|segment| {
            segment.ident == "exists" || segment.ident == "fresh" || segment.ident == "ensures"
        })
}

/// A misplaced, shadowing, or unused fresh binder.
fn fresh_position(reason: &'static str, span: proc_macro2::Span) -> SyntaxError {
    SyntaxError::new(SyntaxErrorKind::FreshBinderPosition { reason }, span)
}

impl RuleExistentials {
    /// Removes and parses the `exists` and `ensures` helpers from `attributes`,
    /// keeping the original attributes for verbatim re-emission.
    ///
    /// # Errors
    ///
    /// Rejects a repeated helper, an empty or malformed payload, or a host
    /// literal as the ensures condition.
    pub(crate) fn take(attributes: &mut Vec<Attribute>) -> Result<Self, SyntaxError> {
        let mut output = Self::default();
        let mut retained = Vec::with_capacity(attributes.len());
        for attribute in std::mem::take(attributes) {
            if !is_existential_helper(&attribute) {
                retained.push(attribute);
                continue;
            }
            let name = attribute
                .path()
                .segments
                .last()
                .map(|segment| segment.ident.to_string())
                .unwrap_or_default();
            let Meta::List(list) = &attribute.meta else {
                return Err(unsupported_rule_signature(
                    "`#[k::exists]`, `#[k::fresh]` and `#[k::ensures]` require a parenthesized payload",
                    attribute.span(),
                ));
            };
            if name == "exists" {
                if output.exists.is_some() {
                    return Err(unsupported_rule_signature(
                        "a rule may declare only one `#[k::exists(...)]` helper",
                        attribute.span(),
                    ));
                }
                output.exists = Some(ExistsAttribute::parse_tokens(list.tokens.clone())?);
            } else if name == "fresh" {
                if output.fresh.is_some() {
                    return Err(unsupported_rule_signature(
                        "a rule may declare only one `#[k::fresh(...)]` helper; list every fresh binder in it",
                        attribute.span(),
                    ));
                }
                output.fresh = Some(ExistsAttribute::parse_tokens(list.tokens.clone())?);
            } else {
                if output.ensures.is_some() {
                    return Err(unsupported_rule_signature(
                        "a rule may declare only one `#[k::ensures(...)]` condition",
                        attribute.span(),
                    ));
                }
                let term = TermExpression::parse_tokens(list.tokens.clone())?;
                if term.root_kind() == crate::TermRootKind::Literal {
                    return Err(unsupported_rule_signature(
                        "an ensures condition must be an object-Bool term, not a host literal",
                        term.expression().span(),
                    ));
                }
                output.ensures = Some(term);
            }
            output.attributes.push(attribute);
        }
        *attributes = retained;
        Ok(output)
    }

    /// Whether no helper was authored.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.exists.is_none() && self.fresh.is_none() && self.ensures.is_none()
    }

    /// The declared existential binders in source order.
    #[must_use]
    pub fn binders(&self) -> &[ClaimBinder] {
        self.exists.as_ref().map_or(&[], ExistsAttribute::binders)
    }

    /// The declared fresh binders (`#[k::fresh]`) in source order.
    #[must_use]
    pub fn fresh(&self) -> &[ClaimBinder] {
        self.fresh.as_ref().map_or(&[], ExistsAttribute::binders)
    }

    /// The result-scoped names in source order: the existentials, then the
    /// fresh binders.
    #[must_use]
    pub fn names(&self) -> Vec<Ident> {
        self.binders()
            .iter()
            .chain(self.fresh())
            .map(|binder| binder.name().clone())
            .collect()
    }

    /// The optional object-Bool postcondition.
    #[must_use]
    pub const fn ensures(&self) -> Option<&TermExpression> {
        self.ensures.as_ref()
    }

    /// The authored helper attributes, unchanged, in source order.
    #[must_use]
    pub fn attributes(&self) -> &[Attribute] {
        &self.attributes
    }

    /// Rejects an existential that repeats a subject binding.
    ///
    /// # Errors
    ///
    /// Names the first shadowing binder.
    pub(crate) fn check_shadowing(&self, subject: &[Ident]) -> Result<(), SyntaxError> {
        for binder in self.binders() {
            if subject
                .iter()
                .any(|binding| binding.unraw() == binder.name().unraw())
            {
                return Err(unsupported_rule_signature(
                    "an existential cannot shadow a subject binding; rename it",
                    binder.name().span(),
                ));
            }
        }
        for (index, binder) in self.fresh().iter().enumerate() {
            let name = binder.name().unraw();
            if subject.iter().any(|binding| binding.unraw() == name) {
                return Err(fresh_position(
                    "a fresh value cannot be matched: it does not exist until the step happens, so it cannot also be a pattern binding; rename it",
                    binder.name().span(),
                ));
            }
            if self
                .binders()
                .iter()
                .chain(&self.fresh()[..index])
                .any(|other| other.name().unraw() == name)
            {
                return Err(fresh_position(
                    "a fresh binder repeats another `#[k::fresh]` or `#[k::exists]` name; rename it",
                    binder.name().span(),
                ));
            }
        }
        Ok(())
    }

    /// Checks the scope of each existential: it never occurs in `requires`
    /// (it has no value before the step) and occurs in the result or the
    /// ensures condition (an unused existential declares nothing).
    ///
    /// # Errors
    ///
    /// Names the first misplaced or unused binder.
    pub(crate) fn check_scope(
        &self,
        requires: Option<&TermExpression>,
        result: &[&TermExpression],
    ) -> Result<(), SyntaxError> {
        for binder in self.binders() {
            if requires.is_some_and(|term| references(term, binder.name())) {
                return Err(unsupported_rule_signature(
                    "an existential cannot occur in `requires`: it names a value the step creates",
                    binder.name().span(),
                ));
            }
            let used = result.iter().any(|term| references(term, binder.name()))
                || self
                    .ensures
                    .as_ref()
                    .is_some_and(|term| references(term, binder.name()));
            if !used {
                return Err(unsupported_rule_signature(
                    "an existential must occur in the rule's result or ensures condition",
                    binder.name().span(),
                ));
            }
        }
        for binder in self.fresh() {
            if requires.is_some_and(|term| references(term, binder.name())) {
                return Err(fresh_position(
                    "a fresh value cannot occur in `requires`: the step allocates it only after deciding to apply",
                    binder.name().span(),
                ));
            }
            let used = result.iter().any(|term| references(term, binder.name()))
                || self
                    .ensures
                    .as_ref()
                    .is_some_and(|term| references(term, binder.name()));
            if !used {
                return Err(fresh_position(
                    "a fresh binder must occur in the rule's result or ensures condition",
                    binder.name().span(),
                ));
            }
        }
        Ok(())
    }

    /// Exact binder and postcondition anchors under the transition roles.
    ///
    /// # Errors
    ///
    /// Returns an endpoint or occurrence-overflow error.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut output = Vec::new();
        for (index, binder) in self.binders().iter().enumerate() {
            let ordinal = checked_ordinal(
                index,
                ProvenanceRole::RuleExistentialBinder,
                binder.name().span(),
            )?;
            output.push(ProvenanceAnchor::new(
                ProvenanceRole::RuleExistentialBinder,
                ordinal,
                TokenRange::for_tokens(binder.name())?,
            ));
            output.push(ProvenanceAnchor::new(
                ProvenanceRole::RuleExistentialBinderName,
                ordinal,
                TokenRange::for_tokens(binder.name())?,
            ));
            output.push(ProvenanceAnchor::new(
                ProvenanceRole::RuleExistentialBinderSort,
                ordinal,
                TokenRange::for_tokens(binder.sort())?,
            ));
        }
        for (index, binder) in self.fresh().iter().enumerate() {
            let ordinal =
                checked_ordinal(index, ProvenanceRole::RuleFreshBinder, binder.name().span())?;
            output.push(ProvenanceAnchor::new(
                ProvenanceRole::RuleFreshBinder,
                ordinal,
                TokenRange::for_tokens(binder.name())?,
            ));
            output.push(ProvenanceAnchor::new(
                ProvenanceRole::RuleFreshBinderName,
                ordinal,
                TokenRange::for_tokens(binder.name())?,
            ));
            output.push(ProvenanceAnchor::new(
                ProvenanceRole::RuleFreshBinderSort,
                ordinal,
                TokenRange::for_tokens(binder.sort())?,
            ));
        }
        if let Some(ensures) = &self.ensures {
            output.push(ProvenanceAnchor::new(
                ProvenanceRole::RuleEnsures,
                0,
                TokenRange::for_tokens(ensures.expression())?,
            ));
            for (ordinal, symbol) in ensures.symbols().iter().enumerate() {
                output.push(ProvenanceAnchor::new(
                    ProvenanceRole::RuleEnsuresPath,
                    checked_ordinal(
                        ordinal,
                        ProvenanceRole::RuleEnsuresPath,
                        symbol.path().span(),
                    )?,
                    TokenRange::for_tokens(symbol.path())?,
                ));
            }
            push_term_node_anchors(
                &mut output,
                ensures.nodes(),
                ProvenanceRole::RuleEnsuresApplicationHead,
                ProvenanceRole::RuleEnsuresReference,
                ProvenanceRole::RuleEnsuresLiteral,
            )?;
            push_record_field_anchors(
                &mut output,
                ensures.tree(),
                ProvenanceRole::RuleEnsuresRecordFieldName,
            )?;
        }
        Ok(output)
    }

    /// The binder sort paths, keyed by `RuleExistentialBinderSort` ordinals,
    /// then by `RuleFreshBinderSort` ordinals.
    ///
    /// # Errors
    ///
    /// Returns an occurrence-overflow error.
    pub fn sort_candidates(&self) -> Result<Vec<(ProvenanceKey, Path)>, SyntaxError> {
        let roles = [
            (ProvenanceRole::RuleExistentialBinderSort, self.binders()),
            (ProvenanceRole::RuleFreshBinderSort, self.fresh()),
        ];
        let mut output = Vec::new();
        for (role, binders) in roles {
            for (index, binder) in binders.iter().enumerate() {
                let ordinal = checked_ordinal(index, role, binder.sort().span())?;
                output.push((ProvenanceKey::new(role, ordinal), binder.sort().clone()));
            }
        }
        Ok(output)
    }

    /// Ensures-condition application and reference candidates; `bindings`
    /// are the subject bindings followed by the existentials.
    ///
    /// # Errors
    ///
    /// Returns an occurrence-overflow error.
    pub fn reference_candidates(
        &self,
        bindings: &[Ident],
    ) -> Result<Vec<ReferenceCandidate<TermSymbolKind>>, SyntaxError> {
        let mut candidates = Vec::new();
        if let Some(ensures) = &self.ensures {
            push_term_reference_candidates(
                &mut candidates,
                ensures.nodes(),
                bindings,
                ProvenanceRole::RuleEnsuresApplicationHead,
                ProvenanceRole::RuleEnsuresReference,
            )?;
        }
        Ok(candidates)
    }
}

/// Whether `term` references the bare name `name`.
pub(super) fn references(term: &TermExpression, name: &Ident) -> bool {
    term.nodes().iter().any(|node| {
        matches!(node, crate::TermNode::Reference(path)
            if path.leading_colon.is_none()
                && path.segments.len() == 1
                && path.segments[0].arguments.is_none()
                && path.segments[0].ident.unraw() == name.unraw())
    })
}
