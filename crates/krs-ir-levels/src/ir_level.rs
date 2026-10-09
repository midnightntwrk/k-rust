//! Shared target-neutral IR shapes and reference representations at each level.

use std::fmt::{Debug, Display};

use serde::{Deserialize, Serialize, de::DeserializeOwned};

use crate::{
    CollectionArityError, DefinitionValidationError, ListOperands, MapOperands,
    SemanticValidationError, SetOperands, SymbolId,
};
use krs_ir::{
    ApplicationRef, AtLeastTwo, BuiltinSort, FixedConfigurationPattern, FixedConfigurationRewrite,
    ListOperation, MapOperation, NodeOrigin, SemanticId, SetOperation, StableItemId,
};

/// Reference representations and local construction failures at one IR level.
/// Semantic references identify resolved authored declarations; Definition references identify generated symbols.
pub trait IrLevel: Clone + Debug + Eq + Ord + Sized {
    /// A declared or builtin sort reference.
    type Sort: Clone + Debug + Display + Eq + Ord + Serialize + DeserializeOwned;
    /// An authored declaration or generated application-symbol identity.
    type Declaration: Clone + Debug + Display + Eq + Ord + Serialize + DeserializeOwned;
    /// A fixed-cell identity before or after generated-symbol allocation.
    type Cell: Clone + Debug + Display + Eq + Ord + Serialize + DeserializeOwned;
    /// The wire representation of an ordinary rule-body term.
    /// Semantic rule bodies box terms; Definition rule bodies store terms directly.
    type RuleTerm: Clone + Debug + Eq + Ord + Serialize + DeserializeOwned;
    /// A construction or validation failure for this IR level.
    type Error: std::error::Error;

    /// Consumes the level's rule-body representation without cloning its term.
    fn into_rule_term(term: Self::RuleTerm) -> IrTerm<Self>;

    /// Constructs the level's reference to an intrinsic K sort.
    fn builtin_sort(sort: BuiltinSort) -> Self::Sort;
    /// Constructs the level's unchanged empty-text failure.
    fn empty_text(field: krs_ir::IrField) -> Self::Error;
}

/// Resolved authored identities in the Semantic IR.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SemanticLevel;

/// Generated symbol identities in the Definition IR.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DefinitionLevel;

impl IrLevel for SemanticLevel {
    type Sort = IrSortRef<StableItemId>;
    type Declaration = StableItemId;
    type Cell = SemanticId;
    type RuleTerm = Box<IrTerm<Self>>;
    type Error = SemanticValidationError;

    fn into_rule_term(term: Self::RuleTerm) -> IrTerm<Self> {
        *term
    }

    fn builtin_sort(sort: BuiltinSort) -> Self::Sort {
        IrSortRef::Builtin(sort)
    }

    fn empty_text(field: krs_ir::IrField) -> Self::Error {
        SemanticValidationError::EmptyText(field)
    }
}

impl IrLevel for DefinitionLevel {
    type Sort = IrSortRef<SymbolId>;
    type Declaration = SymbolId;
    type Cell = SymbolId;
    type RuleTerm = IrTerm<Self>;
    type Error = DefinitionValidationError;

    fn into_rule_term(term: Self::RuleTerm) -> IrTerm<Self> {
        term
    }

    fn builtin_sort(sort: BuiltinSort) -> Self::Sort {
        IrSortRef::Builtin(sort)
    }

    fn empty_text(field: krs_ir::IrField) -> Self::Error {
        DefinitionValidationError::EmptyText(field)
    }
}

/// A declared or builtin sort reference at one IR level.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(tag = "sort_source", content = "sort", rename_all = "snake_case")]
pub enum IrSortRef<D> {
    /// A sort declaration identity at this IR level.
    Declared(D),
    /// Sort intrinsic to the K language.
    Builtin(BuiltinSort),
    /// K's generated sort of one nested (group) cell, such as `FrameCell` for
    /// `<frame>`: the nominal `#[k::cell]` declaration at Semantic level and
    /// the group cell's symbol at Definition level. It is a subsort of `KItem`.
    Cell(D),
}

impl<D> IrSortRef<D> {
    /// Refers to a declared sort.
    #[must_use]
    pub const fn declared(sort: D) -> Self {
        Self::Declared(sort)
    }

    /// Refers to the builtin K computation-sequence sort.
    #[must_use]
    pub const fn k_sequence() -> Self {
        Self::Builtin(BuiltinSort::KSequence)
    }

    /// Refers to the compiler-provided integer sort.
    #[must_use]
    pub const fn int() -> Self {
        Self::Builtin(BuiltinSort::Int)
    }

    /// Refers to the compiler-provided Boolean sort.
    #[must_use]
    pub const fn bool() -> Self {
        Self::Builtin(BuiltinSort::Bool)
    }

    /// Stable identifier-token sort from `ID-SYNTAX`.
    #[must_use]
    pub const fn id() -> Self {
        Self::Builtin(BuiltinSort::Id)
    }

    /// Stable finite-map sort from `MAP`.
    #[must_use]
    pub const fn map() -> Self {
        Self::Builtin(BuiltinSort::Map)
    }

    /// Stable associative-list sort from `LIST`.
    #[must_use]
    pub const fn list() -> Self {
        Self::Builtin(BuiltinSort::List)
    }

    /// Stable associative-set sort from `SET`.
    #[must_use]
    pub const fn set() -> Self {
        Self::Builtin(BuiltinSort::Set)
    }
}

impl IrSortRef<SymbolId> {
    /// Refers to the compiler-provided byte-string sort.
    #[must_use]
    pub const fn bytes() -> Self {
        Self::Builtin(BuiltinSort::Bytes)
    }
}

/// A rule variable declaration at one IR level.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields, bound = "")]
pub struct IrVariable<L: IrLevel> {
    pub(crate) id: SemanticId,
    pub(crate) sort: L::Sort,
}

impl<L: IrLevel> IrVariable<L> {
    /// Declares a variable.
    #[must_use]
    pub const fn new(id: SemanticId, sort: L::Sort) -> Self {
        Self { id, sort }
    }
    /// Returns the stable variable ID.
    #[must_use]
    pub const fn id(&self) -> &SemanticId {
        &self.id
    }
    /// Returns its declared sort.
    #[must_use]
    pub const fn sort(&self) -> &L::Sort {
        &self.sort
    }
}

/// Whether a borrowed or owned slice is empty (serde `skip_serializing_if`).
#[expect(
    clippy::ptr_arg,
    reason = "serde passes `skip_serializing_if` a reference to the field, which is a `Cow`."
)]
pub(crate) fn is_empty_slice<T: Clone>(value: &std::borrow::Cow<'_, [T]>) -> bool {
    value.is_empty()
}

/// One provenance-bearing object-language Boolean rule condition.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields, bound = "")]
pub struct IrRuleCondition<L: IrLevel> {
    pub(crate) origin: NodeOrigin,
    pub(crate) term: IrTerm<L>,
}

/// One explicitly scoped binder declaration at one IR level: a claim universal, or a
/// result-scoped existential of a claim or transition.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields, bound = "")]
pub struct IrScopedBinder<L: IrLevel> {
    pub(crate) origin: NodeOrigin,
    pub(crate) name_origin: NodeOrigin,
    pub(crate) id: SemanticId,
    pub(crate) sort_origin: NodeOrigin,
    pub(crate) sort: L::Sort,
}

/// Typed reachability metadata which is present only on claims.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields, bound = "")]
pub struct IrClaim<L: IrLevel> {
    pub(crate) modality_origin: NodeOrigin,
    pub(crate) modality: krs_ir::ClaimModality,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) circularity_origin: Option<NodeOrigin>,
    pub(crate) universals: Vec<IrScopedBinder<L>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) trusted_origin: Option<NodeOrigin>,
}

impl<L: IrLevel> IrScopedBinder<L> {
    /// Creates one provenance-bearing scoped binder.
    #[must_use]
    pub const fn new(
        origin: NodeOrigin,
        name_origin: NodeOrigin,
        id: SemanticId,
        sort_origin: NodeOrigin,
        sort: L::Sort,
    ) -> Self {
        Self {
            origin,
            name_origin,
            id,
            sort_origin,
            sort,
        }
    }
    /// Declaration provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Name provenance.
    #[must_use]
    pub const fn name_origin(&self) -> &NodeOrigin {
        &self.name_origin
    }
    /// Stable binder identity.
    #[must_use]
    pub const fn id(&self) -> &SemanticId {
        &self.id
    }
    /// Sort provenance.
    #[must_use]
    pub const fn sort_origin(&self) -> &NodeOrigin {
        &self.sort_origin
    }
    /// Declared sort.
    #[must_use]
    pub const fn sort(&self) -> &L::Sort {
        &self.sort
    }
}

impl<L: IrLevel> IrClaim<L> {
    /// Creates typed claim adjunct metadata.
    #[must_use]
    pub const fn new(
        modality_origin: NodeOrigin,
        modality: krs_ir::ClaimModality,
        circularity_origin: Option<NodeOrigin>,
        universals: Vec<IrScopedBinder<L>>,
    ) -> Self {
        Self {
            modality_origin,
            modality,
            circularity_origin,
            universals,
            trusted_origin: None,
        }
    }
    /// Marks the claim trusted: it is assumed without proof.
    #[must_use]
    pub fn with_trusted_origin(mut self, trusted_origin: Option<NodeOrigin>) -> Self {
        self.trusted_origin = trusted_origin;
        self
    }
    /// Modality provenance.
    #[must_use]
    pub const fn modality_origin(&self) -> &NodeOrigin {
        &self.modality_origin
    }
    /// Reachability modality.
    #[must_use]
    pub const fn modality(&self) -> krs_ir::ClaimModality {
        self.modality
    }
    /// Optional circularity provenance.
    #[must_use]
    pub const fn circularity_origin(&self) -> Option<&NodeOrigin> {
        self.circularity_origin.as_ref()
    }
    /// Universal binders.
    #[must_use]
    pub fn universals(&self) -> &[IrScopedBinder<L>] {
        &self.universals
    }
    /// Optional trusted provenance: the claim is assumed without proof.
    #[must_use]
    pub const fn trusted_origin(&self) -> Option<&NodeOrigin> {
        self.trusted_origin.as_ref()
    }
}

/// One explicit equation or transition-rule priority.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct IrRulePriority {
    pub(crate) origin: NodeOrigin,
    pub(crate) value: u32,
}

/// Simplifier classification and optional ordering hint.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct IrSimplification {
    pub(crate) origin: NodeOrigin,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) priority: Option<IrSimplificationPriority>,
}

/// One numeric simplification ordering hint.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct IrSimplificationPriority {
    pub(crate) origin: NodeOrigin,
    pub(crate) value: u32,
}

impl IrSimplification {
    /// Creates typed simplification metadata.
    #[must_use]
    pub const fn new(origin: NodeOrigin, priority: Option<IrSimplificationPriority>) -> Self {
        Self { origin, priority }
    }
    /// Returns marker provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns an optional numeric hint.
    #[must_use]
    pub const fn priority(&self) -> Option<&IrSimplificationPriority> {
        self.priority.as_ref()
    }
}

/// `concrete`, `symbolic`, and `smt_lemma` keys of an equation or simplification (KF-043).
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct IrMatchRestriction {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) concrete: Option<IrRestriction>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) symbolic: Option<IrRestriction>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) smt_lemma: Option<NodeOrigin>,
}

/// One `concrete` or `symbolic` key: every left-hand binder when `variables`
/// is empty (the bare key), otherwise the listed binders.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct IrRestriction {
    pub(crate) origin: NodeOrigin,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub(crate) variables: Vec<IrRestrictionVariable>,
}

/// One left-hand binder named by `concrete(..)` or `symbolic(..)`.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct IrRestrictionVariable {
    pub(crate) origin: NodeOrigin,
    pub(crate) id: SemanticId,
}

impl IrMatchRestriction {
    /// Creates the keys of one equation or simplification.
    #[must_use]
    pub const fn new(
        concrete: Option<IrRestriction>,
        symbolic: Option<IrRestriction>,
        smt_lemma: Option<NodeOrigin>,
    ) -> Self {
        Self {
            concrete,
            symbolic,
            smt_lemma,
        }
    }
    /// Returns the `concrete` key.
    #[must_use]
    pub const fn concrete(&self) -> Option<&IrRestriction> {
        self.concrete.as_ref()
    }
    /// Returns the `symbolic` key.
    #[must_use]
    pub const fn symbolic(&self) -> Option<&IrRestriction> {
        self.symbolic.as_ref()
    }
    /// Returns the provenance of the `smt_lemma` flag.
    #[must_use]
    pub const fn smt_lemma(&self) -> Option<&NodeOrigin> {
        self.smt_lemma.as_ref()
    }
    /// Whether no key is present.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.concrete.is_none() && self.symbolic.is_none() && self.smt_lemma.is_none()
    }
    /// Every node origin, in source order: `concrete` with its binders, `symbolic` with its binders, `smt_lemma`.
    pub fn origins(&self) -> impl Iterator<Item = &NodeOrigin> {
        self.concrete
            .iter()
            .chain(&self.symbolic)
            .flat_map(|restriction| {
                std::iter::once(&restriction.origin).chain(
                    restriction
                        .variables
                        .iter()
                        .map(|variable| &variable.origin),
                )
            })
            .chain(&self.smt_lemma)
    }
}

impl IrRestriction {
    /// Creates one key; an empty `variables` is the bare key.
    #[must_use]
    pub const fn new(origin: NodeOrigin, variables: Vec<IrRestrictionVariable>) -> Self {
        Self { origin, variables }
    }
    /// Returns the key's provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns the listed binders; empty for the bare key.
    #[must_use]
    pub fn variables(&self) -> &[IrRestrictionVariable] {
        &self.variables
    }
    /// Whether the key is bare and restricts every left-hand binder.
    #[must_use]
    pub const fn is_bare(&self) -> bool {
        self.variables.is_empty()
    }
}

impl IrRestrictionVariable {
    /// Creates one named binder.
    #[must_use]
    pub const fn new(origin: NodeOrigin, id: SemanticId) -> Self {
        Self { origin, id }
    }
    /// Returns the identifier's provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns the binder's sentence-local identity.
    #[must_use]
    pub const fn id(&self) -> &SemanticId {
        &self.id
    }
}

/// `unbound_variables = [..]` of a desugar clause (KF-046): right-hand
/// variables the left-hand side does not bind, K's `unboundVariables`.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct IrUnboundVariables {
    pub(crate) origin: NodeOrigin,
    pub(crate) variables: Vec<IrUnboundVariable>,
}

/// One entry of `unbound_variables`: a right-hand variable, or `_` (no
/// identity) for every wildcard of the right-hand side.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct IrUnboundVariable {
    pub(crate) origin: NodeOrigin,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) id: Option<SemanticId>,
}

impl IrUnboundVariables {
    /// Creates the key with its entries in authored order.
    #[must_use]
    pub const fn new(origin: NodeOrigin, variables: Vec<IrUnboundVariable>) -> Self {
        Self { origin, variables }
    }
    /// Returns the provenance of the `unbound_variables` key.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns the entries in authored order.
    #[must_use]
    pub fn variables(&self) -> &[IrUnboundVariable] {
        &self.variables
    }
    /// Whether `_` is listed.
    #[must_use]
    pub fn lists_wildcard(&self) -> bool {
        self.variables.iter().any(IrUnboundVariable::is_wildcard)
    }
    /// Every node origin, in source order: the key, then each entry.
    pub fn origins(&self) -> impl Iterator<Item = &NodeOrigin> {
        std::iter::once(&self.origin).chain(self.variables.iter().map(|variable| &variable.origin))
    }
}

impl IrUnboundVariable {
    /// Creates one entry; `None` is `_`.
    #[must_use]
    pub const fn new(origin: NodeOrigin, id: Option<SemanticId>) -> Self {
        Self { origin, id }
    }
    /// Returns the entry's provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns the variable's sentence-local identity; `None` for `_`.
    #[must_use]
    pub const fn id(&self) -> Option<&SemanticId> {
        self.id.as_ref()
    }
    /// Whether the entry is `_`.
    #[must_use]
    pub const fn is_wildcard(&self) -> bool {
        self.id.is_none()
    }
}

impl IrSimplificationPriority {
    /// Creates a provenance-bearing hint.
    #[must_use]
    pub const fn new(origin: NodeOrigin, value: u32) -> Self {
        Self { origin, value }
    }
    /// Returns hint provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns the numeric hint.
    #[must_use]
    pub const fn value(&self) -> u32 {
        self.value
    }
}

impl IrRulePriority {
    /// Creates a provenance-bearing priority.
    #[must_use]
    pub const fn new(origin: NodeOrigin, value: u32) -> Self {
        Self { origin, value }
    }
    /// Returns priority provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns the explicit numeric priority.
    #[must_use]
    pub const fn value(&self) -> u32 {
        self.value
    }
}

impl<L: IrLevel> IrRuleCondition<L> {
    /// Creates a typed condition while retaining complete payload provenance.
    #[must_use]
    pub const fn new(origin: NodeOrigin, term: IrTerm<L>) -> Self {
        Self { origin, term }
    }
    /// Returns complete condition-payload provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns the structured object-language condition term.
    #[must_use]
    pub const fn term(&self) -> &IrTerm<L> {
        &self.term
    }
}

/// Structured relational body of an ordinary labeled rule at one IR level.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(untagged, bound = "")]
pub enum IrRuleBody<L: IrLevel> {
    /// One ordinary term rewrite in the level's rule-body representation.
    Term(IrRewrite<L>),
    /// One simultaneous fixed-configuration rewrite.
    Configuration(FixedConfigurationRewrite<L::Cell, IrTerm<L>>),
}

/// An ordinary rule body with explicit rewrite endpoints.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(bound = "", try_from = "IrTerm<L>", into = "IrTerm<L>")]
pub struct IrRewrite<L: IrLevel> {
    origin: NodeOrigin,
    sort: L::Sort,
    from: Box<IrTerm<L>>,
    to: Box<IrTerm<L>>,
}

impl<L: IrLevel> IrRewrite<L> {
    /// Creates a rewrite with its declared sort and endpoint provenance.
    #[must_use]
    pub fn new(origin: NodeOrigin, sort: L::Sort, from: IrTerm<L>, to: IrTerm<L>) -> Self {
        Self {
            origin,
            sort,
            from: Box::new(from),
            to: Box::new(to),
        }
    }
    /// Returns rewrite provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns the declared rewrite sort.
    #[must_use]
    pub const fn sort(&self) -> &L::Sort {
        &self.sort
    }
    /// Returns the pre-pattern.
    #[must_use]
    pub fn from(&self) -> &IrTerm<L> {
        &self.from
    }
    /// Returns the post-term.
    #[must_use]
    pub fn to(&self) -> &IrTerm<L> {
        &self.to
    }
}

impl<L: IrLevel> TryFrom<IrTerm<L>> for IrRewrite<L> {
    type Error = &'static str;
    fn try_from(term: IrTerm<L>) -> Result<Self, Self::Error> {
        match term.kind {
            IrTermKind::Rewrite { from, to } => Ok(Self {
                origin: term.origin,
                sort: term.sort,
                from,
                to,
            }),
            _ => Err("rule body must be a rewrite"),
        }
    }
}

impl<L: IrLevel> From<IrRewrite<L>> for IrTerm<L> {
    fn from(value: IrRewrite<L>) -> Self {
        Self {
            origin: value.origin,
            sort: value.sort,
            kind: IrTermKind::Rewrite {
                from: value.from,
                to: value.to,
            },
        }
    }
}

#[derive(Deserialize)]
#[serde(untagged, bound = "")]
pub(crate) enum RuleBodyWire<L: IrLevel> {
    Term(L::RuleTerm),
    Configuration(FixedConfigurationRewrite<L::Cell, IrTerm<L>>),
}

/// A borrowed rule body with the sentence kind refined for configuration rewrites.
#[derive(Clone, Debug)]
pub enum RuleBodyRef<'a, L: IrLevel> {
    /// One ordinary term rewrite.
    Term(&'a IrRewrite<L>),
    /// One configuration rewrite and its permitted sentence kind.
    Configuration {
        /// The configuration sentence classification.
        kind: krs_ir::ConfigurationSentenceKind,
        /// The simultaneous configuration rewrite.
        body: &'a FixedConfigurationRewrite<L::Cell, IrTerm<L>>,
    },
}

impl<L: IrLevel> Copy for RuleBodyRef<'_, L> {}

impl<L: IrLevel> Serialize for RuleBodyRef<'_, L> {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self {
            Self::Term(body) => body.serialize(serializer),
            Self::Configuration { body, .. } => body.serialize(serializer),
        }
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum RuleContent<L: IrLevel> {
    Term {
        kind: krs_ir::SentenceKind,
        body: IrRewrite<L>,
    },
    Configuration {
        kind: krs_ir::ConfigurationSentenceKind,
        body: FixedConfigurationRewrite<L::Cell, IrTerm<L>>,
    },
}

impl<L: IrLevel> RuleContent<L> {
    pub(crate) const fn kind(&self) -> krs_ir::SentenceKind {
        match self {
            Self::Term { kind, .. } => *kind,
            Self::Configuration { kind, .. } => kind.sentence_kind(),
        }
    }

    pub(crate) const fn body(&self) -> RuleBodyRef<'_, L> {
        match self {
            Self::Term { body, .. } => RuleBodyRef::Term(body),
            Self::Configuration { kind, body } => RuleBodyRef::Configuration { kind: *kind, body },
        }
    }
}

pub(crate) enum RuleBodyRefinementError {
    NotRewrite,
    InvalidConfigurationKind,
}

impl<L: IrLevel> RuleBodyWire<L> {
    pub(crate) fn refine(
        self,
        kind: krs_ir::SentenceKind,
    ) -> Result<RuleContent<L>, RuleBodyRefinementError> {
        match self {
            Self::Term(term) => Ok(RuleContent::Term {
                kind,
                body: L::into_rule_term(term)
                    .try_into()
                    .map_err(|_| RuleBodyRefinementError::NotRewrite)?,
            }),
            Self::Configuration(body) => Ok(RuleContent::Configuration {
                kind: kind
                    .try_into()
                    .map_err(|_| RuleBodyRefinementError::InvalidConfigurationKind)?,
                body,
            }),
        }
    }
}

/// A target-neutral term at one IR level.
/// Every nested node must carry its own origin and source-map key.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct IrTerm<L: IrLevel> {
    pub(crate) origin: NodeOrigin,
    pub(crate) sort: L::Sort,
    #[serde(flatten)]
    pub(crate) kind: IrTermKind<L>,
}

impl<L: IrLevel> IrTerm<L> {
    /// Creates a variable reference.
    #[must_use]
    pub const fn variable(origin: NodeOrigin, sort: L::Sort, variable: SemanticId) -> Self {
        Self {
            origin,
            sort,
            kind: IrTermKind::Variable { variable },
        }
    }
    /// Creates an application with arguments in declared production order.
    #[must_use]
    pub const fn application(
        origin: NodeOrigin,
        sort: L::Sort,
        application: ApplicationRef<L::Declaration, L::Sort>,
        arguments: Vec<Self>,
    ) -> Self {
        Self {
            origin,
            sort,
            kind: IrTermKind::Application {
                application,
                arguments,
            },
        }
    }
    /// Creates a domain token.
    ///
    /// # Errors
    ///
    /// Returns the level's empty-text error for an empty token payload.
    pub fn token(
        origin: NodeOrigin,
        sort: L::Sort,
        value: impl Into<String>,
    ) -> Result<Self, L::Error> {
        let value = value.into();
        if value.is_empty() {
            return Err(L::empty_text(krs_ir::IrField::TokenValue));
        }
        Ok(Self {
            origin,
            sort,
            kind: IrTermKind::Token { value },
        })
    }
    /// Creates a rewrite.
    /// Whole-IR validation requires both endpoint sorts to inject into the declared rewrite sort.
    ///
    /// # Errors
    ///
    /// Returns no local shape error; subsorting is a whole-IR property.
    pub fn rewrite(
        origin: NodeOrigin,
        sort: L::Sort,
        from: Self,
        to: Self,
    ) -> Result<Self, L::Error> {
        Ok(Self {
            origin,
            sort,
            kind: IrTermKind::Rewrite {
                from: Box::new(from),
                to: Box::new(to),
            },
        })
    }
    /// Creates `alias @ pattern` (K's `#as`) at the alias variable's sort,
    /// of which the pattern's sort must be a subsort.
    #[must_use]
    pub fn pattern_as(origin: NodeOrigin, sort: L::Sort, alias: SemanticId, pattern: Self) -> Self {
        Self {
            origin,
            sort,
            kind: IrTermKind::As {
                alias,
                pattern: Box::new(pattern),
            },
        }
    }
    /// Creates `A | B | ..` (K's `#Or`) at the least common sort of its
    /// alternatives.
    #[must_use]
    pub const fn pattern_or(
        origin: NodeOrigin,
        sort: L::Sort,
        alternatives: AtLeastTwo<Self>,
    ) -> Self {
        Self {
            origin,
            sort,
            kind: IrTermKind::Or { alternatives },
        }
    }
    /// Creates `k::matches!(subject, pattern)` (K's `( PATTERN :=K SUBJECT )`)
    /// at sort Bool; `binds` lists the pattern's local binders, declared in
    /// the sentence's variables and referenced only inside the pattern.
    #[must_use]
    pub fn matches(
        origin: NodeOrigin,
        sort: L::Sort,
        subject: Self,
        pattern: Self,
        binds: Vec<SemanticId>,
    ) -> Self {
        Self {
            origin,
            sort,
            kind: IrTermKind::Matches {
                subject: Box::new(subject),
                pattern: Box::new(pattern),
                binds,
            },
        }
    }
    /// Creates one `let pattern = value;` statement and the rest of its
    /// block (K's `( #let PATTERN = VALUE #in BODY )`) at the body's sort;
    /// `binds` lists the pattern's local binders, declared in the
    /// sentence's variables and referenced only in the pattern and body.
    #[must_use]
    pub fn let_binding(
        origin: NodeOrigin,
        sort: L::Sort,
        pattern: Self,
        value: Self,
        body: Self,
        binds: Vec<SemanticId>,
    ) -> Self {
        Self {
            origin,
            sort,
            kind: IrTermKind::Let {
                pattern: Box::new(pattern),
                value: Box::new(value),
                body: Box::new(body),
                binds,
            },
        }
    }
    /// Creates one typed Map-theory operation with an explicit result sort.
    #[must_use]
    pub fn typed_map(origin: NodeOrigin, sort: L::Sort, operands: MapOperands<Self>) -> Self {
        Self {
            origin,
            sort,
            kind: IrTermKind::Map(Box::new(operands)),
        }
    }
    /// Creates one typed builtin-List operation.
    #[must_use]
    pub fn list(origin: NodeOrigin, sort: L::Sort, operands: ListOperands<Self>) -> Self {
        Self {
            origin,
            sort,
            kind: IrTermKind::List(Box::new(operands)),
        }
    }
    /// Creates one typed builtin-Set operation.
    #[must_use]
    pub fn set(origin: NodeOrigin, sort: L::Sort, operands: SetOperands<Self>) -> Self {
        Self {
            origin,
            sort,
            kind: IrTermKind::Set(Box::new(operands)),
        }
    }
    /// Creates one complete generated configuration-cell term.
    #[must_use]
    pub const fn cell(
        origin: NodeOrigin,
        sort: L::Sort,
        cell: L::Cell,
        children: Vec<Self>,
    ) -> Self {
        Self {
            origin,
            sort,
            kind: IrTermKind::Cell { cell, children },
        }
    }
    /// Returns node provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns the declared sort.
    #[must_use]
    pub const fn sort(&self) -> &L::Sort {
        &self.sort
    }
    /// Returns the term form.
    #[must_use]
    pub const fn kind(&self) -> &IrTermKind<L> {
        &self.kind
    }
}

/// Structured target-neutral term forms at one IR level.
///
/// The JSON form is internally tagged by `term_kind`; Map, List, and Set terms
/// serialize their operation and their operands, in wire order, as `arguments`.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Deserialize)]
#[serde(try_from = "IrTermKindWire<L>", bound = "")]
pub enum IrTermKind<L: IrLevel> {
    /// Reference to a declared rule or initializer variable.
    Variable {
        /// Stable binder identity.
        variable: SemanticId,
    },
    /// Authored or compiler-provided application.
    Application {
        /// The application identity at this IR level.
        application: ApplicationRef<L::Declaration, L::Sort>,
        /// Arguments in production order.
        arguments: Vec<IrTerm<L>>,
    },
    /// Domain token with its sort on the enclosing term.
    Token {
        /// Exact token payload.
        value: String,
    },
    /// Explicit ordered K computation sequence.
    KSequence {
        /// Declared sort into which sequence items must inject (`KItem`).
        item_sort: L::Sort,
        /// Items in computation order.
        items: Vec<IrTerm<L>>,
    },
    /// Structured finite-map operation or associative item pattern.
    Map(Box<MapOperands<IrTerm<L>>>),
    /// Structured builtin-List operation.
    List(Box<ListOperands<IrTerm<L>>>),
    /// Structured builtin-Set operation.
    Set(Box<SetOperands<IrTerm<L>>>),
    /// Complete generated configuration-cell application.
    Cell {
        /// Stable fixed-cell identity.
        cell: L::Cell,
        /// Leaf content or ordered nested child-cell terms.
        children: Vec<IrTerm<L>>,
    },
    /// Relational pre/post rewrite.
    Rewrite {
        /// Pre-pattern.
        from: Box<IrTerm<L>>,
        /// Post-term.
        to: Box<IrTerm<L>>,
    },
    /// `alias @ pattern`: K's `( PATTERN #as Alias:Sort )`, admitted only in
    /// pre-patterns. The term's sort is the alias variable's sort, of which
    /// the pattern's sort is a subsort; the alias is a rule variable bound
    /// to the whole matched term.
    As {
        /// The alias variable, declared in the sentence's variables.
        alias: SemanticId,
        /// The aliased subpattern.
        pattern: Box<IrTerm<L>>,
    },
    /// `A | B | ..`: K's `( A #Or B #Or .. )`, admitted only in pre-patterns.
    /// The term's sort is the least common sort of the alternatives, and
    /// every alternative binds the same variables.
    Or {
        /// The alternatives, in source order.
        alternatives: AtLeastTwo<IrTerm<L>>,
    },
    /// `k::matches!(subject, pattern)`: K's `( PATTERN :=K SUBJECT )`, a
    /// Bool admitted only in post-terms and conditions. The pattern is
    /// pre-pattern shaped; its named variables are the local binders
    /// `binds` (BIND-1), declared in the sentence's variables and referenced
    /// nowhere else.
    Matches {
        /// The tested term.
        subject: Box<IrTerm<L>>,
        /// The pattern.
        pattern: Box<IrTerm<L>>,
        /// The pattern's local binders, in first-occurrence order.
        binds: Vec<SemanticId>,
    },
    /// One `let pattern = value;` statement and the rest of its block: K's
    /// `( #let PATTERN = VALUE #in BODY )`, at the body's sort, admitted
    /// only in post-terms and conditions. The pattern is pre-pattern
    /// shaped; its named variables are the local binders `binds` (BIND-1),
    /// declared in the sentence's variables and referenced only in the
    /// pattern and the body.
    Let {
        /// The pattern.
        pattern: Box<IrTerm<L>>,
        /// The matched term, outside the pattern's scope.
        value: Box<IrTerm<L>>,
        /// The rest of the block.
        body: Box<IrTerm<L>>,
        /// The pattern's local binders, in first-occurrence order.
        binds: Vec<SemanticId>,
    },
}

/// Owned decoding form of [`IrTermKind`]; collection operands arrive as one ordered list.
#[derive(Deserialize)]
#[serde(
    tag = "term_kind",
    rename_all = "snake_case",
    deny_unknown_fields,
    bound = ""
)]
pub(crate) enum IrTermKindWire<L: IrLevel> {
    Variable {
        variable: SemanticId,
    },
    Application {
        application: ApplicationRef<L::Declaration, L::Sort>,
        arguments: Vec<IrTerm<L>>,
    },
    Token {
        value: String,
    },
    KSequence {
        item_sort: L::Sort,
        items: Vec<IrTerm<L>>,
    },
    Map {
        operation: MapOperation,
        arguments: Vec<IrTerm<L>>,
    },
    List {
        operation: ListOperation,
        arguments: Vec<IrTerm<L>>,
    },
    Set {
        operation: SetOperation,
        arguments: Vec<IrTerm<L>>,
    },
    Cell {
        cell: L::Cell,
        children: Vec<IrTerm<L>>,
    },
    Rewrite {
        from: Box<IrTerm<L>>,
        to: Box<IrTerm<L>>,
    },
    As {
        alias: SemanticId,
        pattern: Box<IrTerm<L>>,
    },
    Or {
        alternatives: AtLeastTwo<IrTerm<L>>,
    },
    Matches {
        subject: Box<IrTerm<L>>,
        pattern: Box<IrTerm<L>>,
        binds: Vec<SemanticId>,
    },
    Let {
        pattern: Box<IrTerm<L>>,
        value: Box<IrTerm<L>>,
        body: Box<IrTerm<L>>,
        binds: Vec<SemanticId>,
    },
}

/// Borrowed encoding form of [`IrTermKind`], field for field the shape of [`IrTermKindWire`].
#[derive(Serialize)]
#[serde(tag = "term_kind", rename_all = "snake_case", bound = "")]
enum IrTermKindRef<'a, L: IrLevel> {
    Variable {
        variable: &'a SemanticId,
    },
    Application {
        application: &'a ApplicationRef<L::Declaration, L::Sort>,
        arguments: &'a [IrTerm<L>],
    },
    Token {
        value: &'a str,
    },
    KSequence {
        item_sort: &'a L::Sort,
        items: &'a [IrTerm<L>],
    },
    Map {
        operation: MapOperation,
        arguments: Vec<&'a IrTerm<L>>,
    },
    List {
        operation: ListOperation,
        arguments: Vec<&'a IrTerm<L>>,
    },
    Set {
        operation: SetOperation,
        arguments: Vec<&'a IrTerm<L>>,
    },
    Cell {
        cell: &'a L::Cell,
        children: &'a [IrTerm<L>],
    },
    Rewrite {
        from: &'a IrTerm<L>,
        to: &'a IrTerm<L>,
    },
    As {
        alias: &'a SemanticId,
        pattern: &'a IrTerm<L>,
    },
    Or {
        alternatives: Vec<&'a IrTerm<L>>,
    },
    Matches {
        subject: &'a IrTerm<L>,
        pattern: &'a IrTerm<L>,
        binds: &'a [SemanticId],
    },
    Let {
        pattern: &'a IrTerm<L>,
        value: &'a IrTerm<L>,
        body: &'a IrTerm<L>,
        binds: &'a [SemanticId],
    },
}

impl<L: IrLevel> TryFrom<IrTermKindWire<L>> for IrTermKind<L> {
    type Error = CollectionArityError;

    fn try_from(wire: IrTermKindWire<L>) -> Result<Self, Self::Error> {
        Ok(match wire {
            IrTermKindWire::Variable { variable } => Self::Variable { variable },
            IrTermKindWire::Application {
                application,
                arguments,
            } => Self::Application {
                application,
                arguments,
            },
            IrTermKindWire::Token { value } => Self::Token { value },
            IrTermKindWire::KSequence { item_sort, items } => Self::KSequence { item_sort, items },
            IrTermKindWire::Map {
                operation,
                arguments,
            } => Self::Map(Box::new(MapOperands::from_operands(operation, arguments)?)),
            IrTermKindWire::List {
                operation,
                arguments,
            } => Self::List(Box::new(ListOperands::from_operands(operation, arguments)?)),
            IrTermKindWire::Set {
                operation,
                arguments,
            } => Self::Set(Box::new(SetOperands::from_operands(operation, arguments)?)),
            IrTermKindWire::Cell { cell, children } => Self::Cell { cell, children },
            IrTermKindWire::Rewrite { from, to } => Self::Rewrite { from, to },
            IrTermKindWire::As { alias, pattern } => Self::As { alias, pattern },
            IrTermKindWire::Or { alternatives } => Self::Or { alternatives },
            IrTermKindWire::Matches {
                subject,
                pattern,
                binds,
            } => Self::Matches {
                subject,
                pattern,
                binds,
            },
            IrTermKindWire::Let {
                pattern,
                value,
                body,
                binds,
            } => Self::Let {
                pattern,
                value,
                body,
                binds,
            },
        })
    }
}

impl<L: IrLevel> Serialize for IrTermKind<L> {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self {
            Self::Variable { variable } => IrTermKindRef::Variable { variable },
            Self::Application {
                application,
                arguments,
            } => IrTermKindRef::Application {
                application,
                arguments,
            },
            Self::Token { value } => IrTermKindRef::Token { value },
            Self::KSequence { item_sort, items } => IrTermKindRef::KSequence { item_sort, items },
            Self::Map(operands) => IrTermKindRef::Map {
                operation: operands.operation(),
                arguments: operands.operands().collect(),
            },
            Self::List(operands) => IrTermKindRef::List {
                operation: operands.operation(),
                arguments: operands.operands().collect(),
            },
            Self::Set(operands) => IrTermKindRef::Set {
                operation: operands.operation(),
                arguments: operands.operands().collect(),
            },
            Self::Cell { cell, children } => IrTermKindRef::Cell { cell, children },
            Self::Rewrite { from, to } => IrTermKindRef::Rewrite { from, to },
            Self::As { alias, pattern } => IrTermKindRef::As { alias, pattern },
            Self::Or { alternatives } => IrTermKindRef::Or {
                alternatives: alternatives.iter().collect(),
            },
            Self::Matches {
                subject,
                pattern,
                binds,
            } => IrTermKindRef::Matches {
                subject,
                pattern,
                binds,
            },
            Self::Let {
                pattern,
                value,
                body,
                binds,
            } => IrTermKindRef::Let {
                pattern,
                value,
                body,
                binds,
            },
        }
        .serialize(serializer)
    }
}

impl<L> IrTerm<L>
where
    L: IrLevel<Sort = IrSortRef<<L as IrLevel>::Declaration>>,
{
    /// Creates an explicit source-level K computation sequence.
    /// The frontend remains responsible for inserting each item's injection into `KItem`.
    #[must_use]
    pub const fn k_sequence(origin: NodeOrigin, item_sort: L::Sort, items: Vec<Self>) -> Self {
        Self {
            origin,
            sort: IrSortRef::Builtin(BuiltinSort::KSequence),
            kind: IrTermKind::KSequence { item_sort, items },
        }
    }
    /// Creates one typed Map-theory operation of builtin `Map` sort.
    #[must_use]
    pub fn map(origin: NodeOrigin, operands: MapOperands<Self>) -> Self {
        Self {
            origin,
            sort: IrSortRef::Builtin(BuiltinSort::Map),
            kind: IrTermKind::Map(Box::new(operands)),
        }
    }
}

impl<L: IrLevel> AsRef<Self> for IrTerm<L> {
    fn as_ref(&self) -> &Self {
        self
    }
}

/// One direct typed subsort edge.
/// Either endpoint may be compiler-provided.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields, bound = "")]
pub struct IrSubsort<L: IrLevel> {
    pub(crate) origin: NodeOrigin,
    pub(crate) subsort: L::Sort,
    pub(crate) supersort: L::Sort,
}

impl<L: IrLevel> IrSubsort<L> {
    /// Creates a direct subsort edge.
    #[must_use]
    pub const fn new(origin: NodeOrigin, subsort: L::Sort, supersort: L::Sort) -> Self {
        Self {
            origin,
            subsort,
            supersort,
        }
    }
    /// Returns edge provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns the smaller sort.
    #[must_use]
    pub const fn subsort(&self) -> &L::Sort {
        &self.subsort
    }
    /// Returns the larger sort.
    #[must_use]
    pub const fn supersort(&self) -> &L::Sort {
        &self.supersort
    }
}

/// One source-level, one-sided reusable fixed-configuration context template.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields, bound = "")]
pub struct IrContextAlias<L: IrLevel> {
    pub(crate) origin: NodeOrigin,
    pub(crate) id: StableItemId,
    pub(crate) name_origin: NodeOrigin,
    pub(crate) name: String,
    pub(crate) here_origin: NodeOrigin,
    pub(crate) here: SemanticId,
    pub(crate) variables: Vec<IrVariable<L>>,
    pub(crate) body: FixedConfigurationPattern<L::Cell, IrTerm<L>>,
}

impl<L: IrLevel> IrContextAlias<L> {
    /// Creates one one-sided context template.
    #[must_use]
    #[expect(
        clippy::too_many_arguments,
        reason = "The alias constructor retains separate declaration, name, and HERE provenance."
    )]
    pub fn new(
        origin: NodeOrigin,
        id: StableItemId,
        name_origin: NodeOrigin,
        name: String,
        here_origin: NodeOrigin,
        here: SemanticId,
        variables: Vec<IrVariable<L>>,
        body: FixedConfigurationPattern<L::Cell, IrTerm<L>>,
    ) -> Self {
        Self {
            origin,
            id,
            name_origin,
            name,
            here_origin,
            here,
            variables,
            body,
        }
    }
    /// Returns declaration provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns stable declaration identity.
    #[must_use]
    pub const fn id(&self) -> &StableItemId {
        &self.id
    }
    /// Returns exact alias-name provenance.
    #[must_use]
    pub const fn name_origin(&self) -> &NodeOrigin {
        &self.name_origin
    }
    /// Returns target-neutral alias name.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }
    /// Returns exact HERE occurrence provenance.
    #[must_use]
    pub const fn here_origin(&self) -> &NodeOrigin {
        &self.here_origin
    }
    /// Returns selected HERE binding.
    #[must_use]
    pub const fn here(&self) -> &SemanticId {
        &self.here
    }
    /// Returns typed/frame variables.
    #[must_use]
    pub fn variables(&self) -> &[IrVariable<L>] {
        &self.variables
    }
    /// Returns the one-sided configuration pattern.
    #[must_use]
    pub const fn body(&self) -> &FixedConfigurationPattern<L::Cell, IrTerm<L>> {
        &self.body
    }
}
