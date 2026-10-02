//! Shared target-neutral IR shapes and reference representations at each level.

use std::fmt::{Debug, Display};

use serde::{Deserialize, Serialize, de::DeserializeOwned};

use crate::{
    ApplicationRef, BuiltinSort, DefinitionValidationError, FixedConfigurationPattern,
    FixedConfigurationRewrite, ListOperation, MapOperation, NodeOrigin, SemanticId,
    SemanticValidationError, SetOperation, StableItemId, SymbolId,
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
    fn empty_text(field: crate::IrField) -> Self::Error;
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

    fn empty_text(field: crate::IrField) -> Self::Error {
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

    fn empty_text(field: crate::IrField) -> Self::Error {
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

/// One provenance-bearing object-language Boolean rule condition.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields, bound = "")]
pub struct IrRuleCondition<L: IrLevel> {
    pub(crate) origin: NodeOrigin,
    pub(crate) term: IrTerm<L>,
}

/// One explicitly scoped claim binder declaration at one IR level.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields, bound = "")]
pub struct IrClaimBinder<L: IrLevel> {
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
    pub(crate) modality: crate::ClaimModality,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) circularity_origin: Option<NodeOrigin>,
    pub(crate) universals: Vec<IrClaimBinder<L>>,
    pub(crate) existentials: Vec<IrClaimBinder<L>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) ensures: Option<IrRuleCondition<L>>,
}

impl<L: IrLevel> IrClaimBinder<L> {
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
        modality: crate::ClaimModality,
        circularity_origin: Option<NodeOrigin>,
        universals: Vec<IrClaimBinder<L>>,
        existentials: Vec<IrClaimBinder<L>>,
        ensures: Option<IrRuleCondition<L>>,
    ) -> Self {
        Self {
            modality_origin,
            modality,
            circularity_origin,
            universals,
            existentials,
            ensures,
        }
    }
    /// Modality provenance.
    #[must_use]
    pub const fn modality_origin(&self) -> &NodeOrigin {
        &self.modality_origin
    }
    /// Reachability modality.
    #[must_use]
    pub const fn modality(&self) -> crate::ClaimModality {
        self.modality
    }
    /// Optional circularity provenance.
    #[must_use]
    pub const fn circularity_origin(&self) -> Option<&NodeOrigin> {
        self.circularity_origin.as_ref()
    }
    /// Universal binders.
    #[must_use]
    pub fn universals(&self) -> &[IrClaimBinder<L>] {
        &self.universals
    }
    /// RHS-scoped existential binders.
    #[must_use]
    pub fn existentials(&self) -> &[IrClaimBinder<L>] {
        &self.existentials
    }
    /// Object-Bool postcondition.
    #[must_use]
    pub const fn ensures(&self) -> Option<&IrRuleCondition<L>> {
        self.ensures.as_ref()
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
        kind: crate::ConfigurationSentenceKind,
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
        kind: crate::SentenceKind,
        body: IrRewrite<L>,
    },
    Configuration {
        kind: crate::ConfigurationSentenceKind,
        body: FixedConfigurationRewrite<L::Cell, IrTerm<L>>,
    },
}

impl<L: IrLevel> RuleContent<L> {
    pub(crate) const fn kind(&self) -> crate::SentenceKind {
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
        kind: crate::SentenceKind,
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
        application: ApplicationRef<L::Declaration>,
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
            return Err(L::empty_text(crate::IrField::TokenValue));
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
    /// Creates one typed Map-theory operation with a non-Map result sort.
    #[must_use]
    pub const fn typed_map(
        origin: NodeOrigin,
        sort: L::Sort,
        operation: MapOperation,
        arguments: Vec<Self>,
    ) -> Self {
        Self {
            origin,
            sort,
            kind: IrTermKind::Map {
                operation,
                arguments,
            },
        }
    }
    /// Creates one typed builtin-List operation.
    #[must_use]
    pub const fn list(
        origin: NodeOrigin,
        sort: L::Sort,
        operation: ListOperation,
        arguments: Vec<Self>,
    ) -> Self {
        Self {
            origin,
            sort,
            kind: IrTermKind::List {
                operation,
                arguments,
            },
        }
    }
    /// Creates one typed builtin-Set operation.
    #[must_use]
    pub const fn set(
        origin: NodeOrigin,
        sort: L::Sort,
        operation: SetOperation,
        arguments: Vec<Self>,
    ) -> Self {
        Self {
            origin,
            sort,
            kind: IrTermKind::Set {
                operation,
                arguments,
            },
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
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(
    tag = "term_kind",
    rename_all = "snake_case",
    deny_unknown_fields,
    bound = ""
)]
pub enum IrTermKind<L: IrLevel> {
    /// Reference to a declared rule or initializer variable.
    Variable {
        /// Stable binder identity.
        variable: SemanticId,
    },
    /// Authored or compiler-provided application.
    Application {
        /// The application identity at this IR level.
        application: ApplicationRef<L::Declaration>,
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
    Map {
        /// Exact compiler-known Map operation.
        operation: MapOperation,
        /// Ordered structured operands.
        arguments: Vec<IrTerm<L>>,
    },
    /// Structured builtin-List operation.
    List {
        /// Exact compiler-known List operation.
        operation: ListOperation,
        /// Ordered structured operands.
        arguments: Vec<IrTerm<L>>,
    },
    /// Structured builtin-Set operation.
    Set {
        /// Exact compiler-known Set operation.
        operation: SetOperation,
        /// Ordered structured operands.
        arguments: Vec<IrTerm<L>>,
    },
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
    /// Creates one typed Map-theory operation.
    #[must_use]
    pub const fn map(origin: NodeOrigin, operation: MapOperation, arguments: Vec<Self>) -> Self {
        Self {
            origin,
            sort: IrSortRef::Builtin(BuiltinSort::Map),
            kind: IrTermKind::Map {
                operation,
                arguments,
            },
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
