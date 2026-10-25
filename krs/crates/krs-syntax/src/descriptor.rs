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
    BracketAttribute, ClaimAttribute, ConfigurationAttribute, ConfigurationDeclaration,
    ContextAliasAttribute, ContextAttribute, DesugarAttribute, EquationAttribute, ProvenanceAnchor,
    ProvenanceRole, RuleAttribute, RuleClause, RuleItem, SimplificationAttribute, SortAttribute,
    SpecModuleAttribute, SpecModuleItem, StateClaimItem, StateContextAliasItem, StateRuleItem,
    SymbolAttribute, SyntaxError, TokenDeclaration, TokenRange, TokenStack,
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

impl SortAttribute {
    /// Returns the anchors of the sort's descriptor: the sort attribute,
    /// then the explicit symbol override, when the marker trait has one.
    ///
    /// # Errors
    ///
    /// Rejects a missing alias as [`Self::checked_alias`] does.
    pub fn descriptor_provenance(
        &self,
        marker: &Ident,
        symbol: Option<&SymbolAttribute>,
    ) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut keys = KeyAllocator::default();
        keys.append(&self.provenance(marker)?);
        if let Some(symbol) = symbol {
            keys.append(&symbol.provenance()?);
        }
        Ok(keys.into_anchors())
    }
}

impl BracketAttribute {
    /// Returns the anchors of the descriptor of a bracket on a sort's marker
    /// trait: the bracket, then the sort it brackets, named by the sort
    /// attribute's alias, or by the marker trait when no alias names it.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only if the sort's name emits no token
    /// leaves.
    pub fn sort_descriptor_provenance(
        &self,
        sort: Option<&SortAttribute>,
        marker: &Ident,
    ) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        bracket_anchors(self, sort.and_then(SortAttribute::alias).unwrap_or(marker))
    }
}

/// The anchors of a bracket's descriptor: the bracket's own keying, then the
/// name of the sort it brackets, which is the first of its role.
pub(crate) fn bracket_anchors(
    bracket: &BracketAttribute,
    sort: &Ident,
) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
    let mut keys = KeyAllocator::default();
    keys.append(&bracket.provenance()?);
    keys.key(
        ProvenanceRole::SortDeclaration,
        TokenRange::for_tokens(sort)?,
    )?;
    Ok(keys.into_anchors())
}

impl TokenStack {
    /// Returns the anchors of the token grammar's descriptor: the stack's
    /// productions, then the carrier's name.
    ///
    /// # Errors
    ///
    /// None: the stack and the carrier were keyed when they were parsed.
    pub fn descriptor_provenance(
        &self,
        declaration: &TokenDeclaration,
    ) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut keys = KeyAllocator::default();
        keys.append(&self.provenance()?);
        keys.append(&declaration.provenance()?);
        Ok(keys.into_anchors())
    }
}

impl SpecModuleItem {
    /// Returns the anchors of the spec module's descriptor: the module, then
    /// its `#[k::spec_module(..)]` attribute.
    ///
    /// # Errors
    ///
    /// None: the module and its attribute were keyed when they were parsed.
    pub fn descriptor_provenance(
        &self,
        attribute: &SpecModuleAttribute,
    ) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut keys = KeyAllocator::default();
        keys.append(&self.provenance());
        keys.append(&attribute.provenance()?);
        Ok(keys.into_anchors())
    }
}

impl ConfigurationDeclaration {
    /// Returns the anchors of the configuration's descriptor: the struct,
    /// then its `#[k::configuration(..)]` attribute.
    ///
    /// # Errors
    ///
    /// None: the struct and its attribute were keyed when they were parsed.
    pub fn descriptor_provenance(
        &self,
        attribute: &ConfigurationAttribute,
    ) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut keys = KeyAllocator::default();
        keys.append(&self.provenance()?);
        keys.append(&attribute.provenance()?);
        Ok(keys.into_anchors())
    }
}
