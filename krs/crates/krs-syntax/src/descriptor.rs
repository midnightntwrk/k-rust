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
    ConstructorAttribute, ConstructorDeclaration, ContextAliasAttribute, ContextAttribute,
    DesugarAttribute, EnumConstructorVariant, EquationAttribute, FunctionAttribute,
    ProvenanceAnchor, ProvenanceRole, RuleAttribute, RuleClause, RuleItem, SimplificationAttribute,
    SortAttribute, SpecModuleAttribute, SpecModuleItem, StateClaimItem, StateContextAliasItem,
    StateRuleItem, StaticProductionAttribute, StrictnessAttribute, SymbolAttribute, SyntaxError,
    TokenDeclaration, TokenRange, TokenStack,
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
        keys.append(&rule.full_provenance()?)?;
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
        keys.append(&rule.provenance()?)?;
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
                keys.append(&attribute.provenance()?)?;
                None
            }
            RuleSentence::Context(context) => {
                let attribute = context.rule_attribute(name);
                keys.append(&attribute.provenance()?)?;
                attribute.evaluation_key().cloned()
            }
            RuleSentence::Equation(equation) => {
                keys.append(&equation.provenance()?)?;
                None
            }
            RuleSentence::Simplification(simplification) => {
                let key = keys.key(
                    ProvenanceRole::SimplificationMarker,
                    TokenRange::for_tokens(name)?,
                )?;
                keys.append(&simplification.provenance()?)?;
                Some(key)
            }
            RuleSentence::Alias => {
                Some(keys.key(ProvenanceRole::AliasClause, TokenRange::for_tokens(name)?)?)
            }
            RuleSentence::Desugar(desugar) => {
                let key = keys.key(ProvenanceRole::DesugarClause, TokenRange::for_tokens(name)?)?;
                keys.append(&desugar.provenance()?)?;
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
        keys.append(&self.provenance()?)?;
        keys.append(&attribute.provenance()?)?;
        Ok(keys.into_anchors())
    }
}

impl StateContextAliasItem {
    /// Returns the anchors of the context alias's descriptor: its attribute,
    /// the fn's name as the declaration, then the alias's configuration.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only if the fn's name emits no token leaves,
    /// and a repeated-key error if two pieces hold one key.
    ///
    /// # Panics
    ///
    /// Never: parsing keys the fn's name.
    pub fn descriptor_provenance(
        &self,
        attribute: &ContextAliasAttribute,
    ) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut keys = KeyAllocator::default();
        keys.append(&attribute.provenance()?)?;
        keys.held(
            self.declaration_key()
                .expect("a context alias is keyed when it is parsed"),
            TokenRange::for_tokens(&self.item().sig.ident)?,
        )?;
        keys.append(&self.provenance()?)?;
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
        keys.append(&self.provenance()?)?;
        keys.append(&self.attribute_provenance()?)?;
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
        keys.append(&self.provenance(marker)?)?;
        if let Some(symbol) = symbol {
            keys.append(&symbol.provenance()?)?;
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
    keys.append(&bracket.provenance()?)?;
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
        keys.append(&self.provenance()?)?;
        keys.append(&declaration.provenance()?)?;
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
        keys.append(&self.provenance())?;
        keys.append(&attribute.provenance()?)?;
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
        keys.append(&self.provenance()?)?;
        keys.append(&attribute.provenance()?)?;
        Ok(keys.into_anchors())
    }
}

/// The attribute that makes a struct a production.
#[derive(Clone, Copy, Debug)]
pub enum ProductionAttribute<'a> {
    /// `#[k::constructor(..)]`.
    Constructor(&'a ConstructorAttribute),
    /// `#[k::function(..)]`, whose production arguments are its
    /// [`FunctionAttribute::production`].
    Function(&'a FunctionAttribute),
}

impl<'a> ProductionAttribute<'a> {
    /// The production arguments.
    #[must_use]
    pub const fn production(self) -> &'a ConstructorAttribute {
        match self {
            Self::Constructor(attribute) => attribute,
            Self::Function(function) => function.production(),
        }
    }
}

/// The parsed pieces of one production struct, which declares two
/// descriptors: the constructor of its sort and its grammar production.
#[derive(Clone, Copy, Debug)]
pub struct ProductionItem<'a> {
    /// The attribute that makes the struct a production.
    pub attribute: ProductionAttribute<'a>,
    /// The struct.
    pub declaration: &'a ConstructorDeclaration,
    /// The explicit stable-symbol override.
    pub symbol: Option<&'a SymbolAttribute>,
    /// The `#[k::alias]` and `#[k::desugar]` markers (KF-028), each with
    /// the name of its helper attribute, which anchors it. The macro accepts
    /// one; the collector's reparse records every marker it finds.
    pub static_markers: &'a [(StaticProductionAttribute, Ident)],
    /// The `#[k::strict]` and `#[k::seqstrict]` helpers.
    pub strictness: &'a [StrictnessAttribute],
}

impl ProductionItem<'_> {
    /// Returns the anchors of the constructor descriptor: the production's
    /// compact view, the struct, the element types of the result and of the
    /// fields, which only this descriptor references, then the symbol
    /// override.
    ///
    /// # Errors
    ///
    /// None: every piece was keyed when it was parsed.
    pub fn constructor_provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let production = self.attribute.production();
        let mut keys = KeyAllocator::default();
        keys.append(&production.provenance()?)?;
        keys.append(&self.declaration.provenance()?)?;
        keys.append(&production.sort_argument_provenance()?)?;
        keys.append(&self.declaration.argument_provenance()?)?;
        if let Some(symbol) = self.symbol {
            keys.append(&symbol.provenance()?)?;
        }
        Ok(keys.into_anchors())
    }

    /// Returns the anchors of the grammar descriptor: the production's full
    /// view, the struct's, the symbol override, the static marker's name
    /// and payload, a total function's name as its declaration and the
    /// function's own keys, then the strictness helpers.
    ///
    /// Each static marker and each strictness helper is numbered as a
    /// sentence of its own, a marker's name first: of the one marker and the
    /// one helper a production has, each key is the first of its role. A
    /// second marker or helper, which the macro rejects, repeats the first's
    /// keys, and the descriptor's keying refuses the repetition.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only if a name emits no token leaves, and a
    /// repeated-key error for a second static marker or strictness helper.
    pub fn grammar_provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut keys = KeyAllocator::default();
        keys.append(&self.attribute.production().full_provenance()?)?;
        keys.append(&self.declaration.full_provenance()?)?;
        if let Some(symbol) = self.symbol {
            keys.append(&symbol.provenance()?)?;
        }
        let mut markers = Vec::new();
        for (marker, name) in self.static_markers {
            let mut marker_keys = KeyAllocator::default();
            marker_keys.key(
                marker.mode().production_role(),
                TokenRange::for_tokens(name)?,
            )?;
            marker_keys.append(&marker.provenance())?;
            markers.extend(marker_keys.into_anchors());
        }
        keys.append(&markers)?;
        if let ProductionAttribute::Function(function) = self.attribute {
            if function.is_total() {
                keys.key(
                    ProvenanceRole::FunctionDeclaration,
                    TokenRange::for_tokens(self.declaration.name())?,
                )?;
            }
            keys.append(function.function_anchors())?;
        }
        let mut strictness = Vec::new();
        for helper in self.strictness {
            strictness.extend(helper.provenance()?);
        }
        keys.append(&strictness)?;
        Ok(keys.into_anchors())
    }
}

impl EnumConstructorVariant {
    /// Returns the anchors of the variant's constructor descriptor: its
    /// production, then the element types of its field sorts, which only
    /// this descriptor references.
    ///
    /// # Errors
    ///
    /// None: the variant was keyed when it was parsed.
    pub fn constructor_provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut keys = KeyAllocator::default();
        keys.append(&self.provenance()?)?;
        keys.append(&self.argument_provenance()?)?;
        Ok(keys.into_anchors())
    }
}
