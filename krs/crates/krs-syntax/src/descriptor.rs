//! Descriptors whose anchors combine several parsed pieces of one item.
//!
//! An item's parsers key each piece as a sentence of its own: a rule fn and
//! its attribute, a struct and its helper attributes. The descriptor the item
//! declares is one sentence over all of them. Its keying continues across the
//! pieces in descriptor order ([`KeyAllocator::append`]) and keys the nodes no
//! piece holds, such as the name of a clause fn. The macro and the
//! collector's reparse both take a descriptor's anchors from here, so the two
//! agree key for key by construction.

use krs_ir::ProvenanceKey;
use syn::Ident;

use crate::parse::KeyAllocator;
use crate::{
    ClaimAttribute, ContextAliasAttribute, ContextAttribute, DesugarAttribute, EquationAttribute,
    ProvenanceAnchor, ProvenanceRole, RuleAttribute, RuleClause, RuleItem, SimplificationAttribute,
    StateClaimItem, StateContextAliasItem, StateRuleItem, SyntaxError, TokenRange,
};

/// The attribute that makes a rule fn one kind of sentence.
#[derive(Clone, Copy, Debug)]
pub enum RuleSentence<'a> {
    /// `#[k::rule(..)]`: a transition.
    Transition(&'a RuleAttribute),
    /// `#[k::context(..)]` (KF-021): the fn's name marks its evaluation step.
    Context(&'a ContextAttribute),
    /// `#[k::equation(..)]`.
    Equation(&'a EquationAttribute),
    /// `#[k::simplification(..)]`: the fn's name marks it.
    Simplification(&'a SimplificationAttribute),
    /// An `#[k::alias]` clause (KF-028): the fn's name marks it.
    Alias,
    /// A `#[k::desugar(..)]` clause (KF-028, KF-046): the fn's name marks it.
    Desugar(&'a DesugarAttribute),
}

/// The descriptor of one rule fn: the rule, then its sentence's attribute
/// and the fn's name where it marks the sentence.
#[derive(Clone, Debug)]
pub struct RuleDescriptor {
    marker_key: Option<ProvenanceKey>,
    anchors: Vec<ProvenanceAnchor>,
}

impl RuleDescriptor {
    /// Keys the descriptor of a rule fn whose sides are terms: the rule's
    /// complete catalog, then `sentence`.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only if the fn's name emits no token leaves.
    pub fn new(rule: &RuleItem, sentence: RuleSentence<'_>) -> Result<Self, SyntaxError> {
        let mut keys = KeyAllocator::default();
        keys.append(&rule.full_provenance()?);
        Self::sentence(keys, &rule.item().sig.ident, sentence)
    }

    /// Keys the descriptor of a rule fn whose sides are `cells!`
    /// configurations: the rule, then `sentence`.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only if the fn's name emits no token leaves.
    pub fn state(rule: &StateRuleItem, sentence: RuleSentence<'_>) -> Result<Self, SyntaxError> {
        let mut keys = KeyAllocator::default();
        keys.append(&rule.provenance()?);
        Self::sentence(keys, &rule.item().sig.ident, sentence)
    }

    /// Continues `keys` with the sentence's attribute and, where it marks the
    /// sentence, the fn's `name`: a context's evaluation step is the name in
    /// the context's rule-attribute view, and an alias, desugar or
    /// simplification marker is the name keyed before the attribute.
    fn sentence(
        mut keys: KeyAllocator,
        name: &Ident,
        sentence: RuleSentence<'_>,
    ) -> Result<Self, SyntaxError> {
        let marker_key = match sentence {
            RuleSentence::Transition(attribute) => {
                keys.append(&attribute.provenance()?);
                None
            }
            RuleSentence::Context(context) => {
                let attribute = context.rule_attribute(name);
                keys.append(&attribute.provenance()?);
                attribute.evaluation_key().cloned()
            }
            RuleSentence::Equation(equation) => {
                keys.append(&equation.provenance()?);
                None
            }
            RuleSentence::Simplification(simplification) => {
                let key = keys.key(
                    ProvenanceRole::SimplificationMarker,
                    TokenRange::for_tokens(name)?,
                )?;
                keys.append(&simplification.provenance()?);
                Some(key)
            }
            RuleSentence::Alias => {
                Some(keys.key(ProvenanceRole::AliasClause, TokenRange::for_tokens(name)?)?)
            }
            RuleSentence::Desugar(desugar) => {
                let key = keys.key(ProvenanceRole::DesugarClause, TokenRange::for_tokens(name)?)?;
                keys.append(&desugar.provenance()?);
                Some(key)
            }
        };
        Ok(Self {
            marker_key,
            anchors: keys.into_anchors(),
        })
    }

    /// The key of the fn's name where it marks the sentence: the clause
    /// marker of an alias, desugar or simplification, or a context's
    /// evaluation step.
    #[must_use]
    pub const fn marker_key(&self) -> Option<&ProvenanceKey> {
        self.marker_key.as_ref()
    }

    /// The descriptor's anchors, in allocation order.
    #[must_use]
    pub fn anchors(&self) -> &[ProvenanceAnchor] {
        &self.anchors
    }
}

impl StateClaimItem {
    /// Returns the anchors of the claim's descriptor: the claim, then its
    /// `#[k::claim(..)]` attribute.
    ///
    /// # Errors
    ///
    /// None: both pieces were keyed when they were parsed.
    pub fn descriptor_provenance(
        &self,
        attribute: &ClaimAttribute,
    ) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut keys = KeyAllocator::default();
        keys.append(&self.provenance()?);
        keys.append(&attribute.provenance()?);
        Ok(keys.into_anchors())
    }
}

impl StateContextAliasItem {
    /// Returns the anchors of the context alias's descriptor: its attribute,
    /// the fn's name as the declaration, then the alias's configuration.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only if the fn's name emits no token leaves.
    pub fn descriptor_provenance(
        &self,
        attribute: &ContextAliasAttribute,
    ) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut keys = KeyAllocator::default();
        keys.append(&attribute.provenance()?);
        keys.key(
            ProvenanceRole::ContextAliasDeclaration,
            TokenRange::for_tokens(&self.item().sig.ident)?,
        )?;
        keys.append(&self.provenance()?);
        Ok(keys.into_anchors())
    }
}

impl RuleClause {
    /// Returns the anchors of the clause's descriptor: the clause, then its
    /// metadata attribute.
    ///
    /// # Errors
    ///
    /// None: the clause and its attribute were keyed when the block was
    /// parsed.
    pub fn descriptor_provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut keys = KeyAllocator::default();
        keys.append(&self.provenance()?);
        keys.append(&self.attribute_provenance()?);
        Ok(keys.into_anchors())
    }
}
