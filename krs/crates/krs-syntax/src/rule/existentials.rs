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

use super::pattern::{allocate_term_node_keys, push_term_reference_candidates};
use crate::attribute::{ClaimBinder, ExistsAttribute};
use crate::parse::{KeyAllocator, KrsSyntax, unsupported_rule_signature};
use crate::term::allocate_record_field_keys;
use crate::{
    ProvenanceAnchor, ProvenanceRole, ReferenceCandidate, SyntaxError, SyntaxErrorKind,
    TermExpression, TermSymbolKind,
};
use krs_ir::ProvenanceKey;

/// The `#[k::fresh]`, `#[k::exists]` and `#[k::ensures]` helpers of one transition.
#[derive(Clone, Debug, Default)]
pub struct RuleExistentials {
    exists: Option<ExistsAttribute>,
    fresh: Option<ExistsAttribute>,
    ensures: Option<TermExpression>,
    attributes: Vec<Attribute>,
    /// The anchors of the helpers' standalone keying.
    anchors: Vec<ProvenanceAnchor>,
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
                let term = TermExpression::parse_tokens(crate::parse::strip_trailing_comma(
                    list.tokens.clone(),
                ))?;
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
        let mut keys = KeyAllocator::default();
        output.clear_keys();
        output.allocate_keys(&mut keys)?;
        output.anchors = keys.into_anchors();
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

    /// Exact binder and postcondition anchors under the transition roles, of
    /// the helpers' standalone keying.
    ///
    /// # Errors
    ///
    /// None: the helpers were keyed when they were parsed.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.anchors.clone())
    }

    /// Forgets the keys of the binders and of the ensures condition, before
    /// a sentence's pass keys them.
    pub(crate) fn clear_keys(&mut self) {
        for helper in self.exists.iter_mut().chain(&mut self.fresh) {
            for binder in helper.binders_mut() {
                binder.clear_keys();
            }
        }
        if let Some(ensures) = &mut self.ensures {
            ensures.clear_keys();
        }
    }

    /// A copy without keys, for a producer that computes its anchors on
    /// demand; the copy's keys are discarded with it.
    pub(crate) fn unkeyed(&self) -> Self {
        let mut copy = self.clone();
        copy.clear_keys();
        copy
    }

    /// Keys each existential binder with its name and sort, each fresh binder
    /// with its name and sort, then the ensures condition (its term's
    /// payload) with its paths, nodes, and record field names.
    pub(crate) fn allocate_keys(&mut self, keys: &mut KeyAllocator) -> Result<(), SyntaxError> {
        for binder in self
            .exists
            .iter_mut()
            .flat_map(ExistsAttribute::binders_mut)
        {
            binder.allocate_keys(
                keys,
                ProvenanceRole::RuleExistentialBinder,
                ProvenanceRole::RuleExistentialBinderName,
                ProvenanceRole::RuleExistentialBinderSort,
            )?;
        }
        for binder in self.fresh.iter_mut().flat_map(ExistsAttribute::binders_mut) {
            binder.allocate_keys(
                keys,
                ProvenanceRole::RuleFreshBinder,
                ProvenanceRole::RuleFreshBinderName,
                ProvenanceRole::RuleFreshBinderSort,
            )?;
        }
        if let Some(ensures) = &mut self.ensures {
            ensures.allocate_keys(
                keys,
                ProvenanceRole::RuleEnsures,
                ProvenanceRole::RuleEnsuresPath,
            )?;
            let (nodes, tree, term_keys) = ensures.keying();
            allocate_term_node_keys(
                keys,
                nodes,
                term_keys,
                ProvenanceRole::RuleEnsuresApplicationHead,
                ProvenanceRole::RuleEnsuresReference,
                ProvenanceRole::RuleEnsuresLiteral,
            )?;
            allocate_record_field_keys(
                keys,
                tree,
                term_keys,
                ProvenanceRole::RuleEnsuresRecordFieldName,
            )?;
        }
        Ok(())
    }

    /// The ensures condition, for a pass that keys it.
    pub(crate) const fn ensures_mut(&mut self) -> Option<&mut TermExpression> {
        self.ensures.as_mut()
    }

    /// The binder sort paths, keyed as their sentence keyed them: by
    /// `RuleExistentialBinderSort` ordinals, then by `RuleFreshBinderSort`
    /// ordinals.
    ///
    /// # Errors
    ///
    /// None: the binders were keyed when they were parsed.
    ///
    /// # Panics
    ///
    /// Never: parsing keys every binder sort.
    pub fn sort_candidates(&self) -> Result<Vec<(ProvenanceKey, Path)>, SyntaxError> {
        Ok(self
            .binders()
            .iter()
            .chain(self.fresh())
            .map(|binder| {
                let key = binder
                    .sort_key()
                    .expect("a keyed sentence keys every binder sort");
                (key.clone(), binder.sort().clone())
            })
            .collect())
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
                ensures.keys(),
                bindings,
            );
        }
        Ok(candidates)
    }
}

/// Whether `term` references the bare name `name`.
pub(super) fn references(term: &TermExpression, name: &Ident) -> bool {
    term.nodes().iter().any(|node| match node {
        crate::TermNode::Reference(path) => {
            path.leading_colon.is_none()
                && path.segments.len() == 1
                && path.segments[0].arguments.is_none()
                && path.segments[0].ident.unraw() == name.unraw()
        }
        crate::TermNode::As { binding, .. } => binding.unraw() == name.unraw(),
        _ => false,
    })
}
