//! Target-neutral object-grammar contracts shared by semantic and Definition IR.
//!
//! These types classify every K attribute the expression grammar needs.
//! In particular, an adapter cannot smuggle raw attribute names, K labels, or
//! parser-internal production IDs through this layer.

use std::error::Error;
use std::fmt;

use serde::{Deserialize, Deserializer, Serialize};

use crate::{BuiltinSort, IrIdentityError, NodeOrigin, StableItemId, ir::validated_id};

/// Exact backend hook identities selected by qualified KRS semantics.
///
/// Textual hook names remain target-specific catalog data. Authored Rust,
/// descriptors, and IR carry only these closed identities.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum HookOperation {
    /// Raw 32-byte Keccak-256 digest (`KRYPTO.keccak256raw`).
    KryptoKeccak256Raw,
    /// Raw 32-byte SHA-256 digest (`KRYPTO.sha256raw`).
    KryptoSha256Raw,
    /// Raw 20-byte RIPEMD-160 digest (`KRYPTO.ripemd160raw`).
    KryptoRipemd160Raw,
    /// Recover 64-byte secp256k1 public-key coordinates (`KRYPTO.ecdsaRecover`).
    KryptoEcdsaRecover,
    /// Validate a concrete `alt_bn128` G1 point (`KRYPTO.bn128valid`).
    KryptoBn128Valid,
    /// Add two concrete `alt_bn128` G1 points (`KRYPTO.bn128add`).
    KryptoBn128Add,
    /// Multiply a concrete `alt_bn128` G1 point by an integer (`KRYPTO.bn128mul`).
    KryptoBn128Mul,
    /// Validate a concrete `alt_bn128` G2 point and subgroup membership (`KRYPTO.bn128g2valid`).
    KryptoBn128G2Valid,
    /// Test whether an `alt_bn128` pairing product is the target-group identity (`KRYPTO.bn128ate`).
    KryptoBn128Ate,
}

impl HookOperation {
    /// Complete hook catalog in stable semantic order.
    pub const ALL: [Self; 9] = [
        Self::KryptoKeccak256Raw,
        Self::KryptoSha256Raw,
        Self::KryptoRipemd160Raw,
        Self::KryptoEcdsaRecover,
        Self::KryptoBn128Valid,
        Self::KryptoBn128Add,
        Self::KryptoBn128Mul,
        Self::KryptoBn128G2Valid,
        Self::KryptoBn128Ate,
    ];

    /// Fixed builtin signature, when the hook does not operate on a
    /// definition-declared algebraic sort.
    #[must_use]
    pub const fn builtin_signature(self) -> Option<(BuiltinSort, &'static [BuiltinSort])> {
        match self {
            Self::KryptoKeccak256Raw | Self::KryptoSha256Raw | Self::KryptoRipemd160Raw => {
                Some((BuiltinSort::Bytes, &[BuiltinSort::Bytes]))
            }
            Self::KryptoEcdsaRecover => Some((
                BuiltinSort::Bytes,
                &[
                    BuiltinSort::Bytes,
                    BuiltinSort::Int,
                    BuiltinSort::Bytes,
                    BuiltinSort::Bytes,
                ],
            )),
            Self::KryptoBn128Ate => {
                Some((BuiltinSort::Bool, &[BuiltinSort::List, BuiltinSort::List]))
            }
            Self::KryptoBn128Valid
            | Self::KryptoBn128Add
            | Self::KryptoBn128Mul
            | Self::KryptoBn128G2Valid => None,
        }
    }
}

/// Exact compiler-provided operation identities for the pinned K 7.1.337
/// `INT`, `BOOL`, and selected `BYTES` builtins used by qualified semantics.
///
/// The textual K labels and hooks are deliberately absent. A pin-specific
/// compiler catalog maps these identities to frontend representations.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BuiltinOperation {
    /// `_+Int_` (`INT.add`).
    IntAdd,
    /// `_-Int_` (`INT.sub`).
    IntSub,
    /// `_*Int_` (`INT.mul`).
    IntMul,
    /// `_/Int_`, truncating division (`INT.tdiv`).
    IntTDiv,
    /// `_modInt_`, Euclidean modulus (`INT.mod`).
    IntMod,
    /// `_^%Int__`, modular exponentiation (`INT.powmod`).
    IntPowMod,
    /// `log2Int`, integer base-two logarithm (`INT.log2`).
    IntLog2,
    /// `_>>Int_`, arithmetic right shift (`INT.shr`).
    IntShiftRight,
    /// `_<<Int_`, left shift (`INT.shl`).
    IntShiftLeft,
    /// `_&Int_`, two's-complement bitwise conjunction (`INT.and`).
    IntBitAnd,
    /// `_xorInt_`, two's-complement bitwise exclusive disjunction (`INT.xor`).
    IntBitXor,
    /// `_|Int_`, two's-complement bitwise inclusive disjunction (`INT.or`).
    IntBitOr,
    /// `_>=Int_`.
    IntGreaterEqual,
    /// `_>Int_`.
    IntGreater,
    /// `_<=Int_`.
    IntLessEqual,
    /// `_<Int_`.
    IntLess,
    /// `_==Int_`.
    IntEqual,
    /// `_=/=Int_`.
    IntNotEqual,
    /// `notBool_`.
    BoolNot,
    /// `_==Bool_`.
    BoolEqual,
    /// `_=/=Bool_`.
    BoolNotEqual,
    /// `_andBool_`.
    BoolAnd,
    /// `_orBool_`.
    BoolOr,
    /// `lengthBytes` (`BYTES.length`).
    BytesLength,
    /// Byte lookup (`BYTES.get`).
    BytesGet,
    /// `.Bytes` (`BYTES.empty`).
    BytesEmpty,
    /// Byte update (`BYTES.update`).
    BytesUpdate,
    /// Right padding (`BYTES.padRight`).
    BytesPadRight,
    /// Half-open byte substring extraction (`BYTES.substr`).
    BytesSubstring,
}

impl BuiltinOperation {
    /// Complete protocol catalog in stable semantic order.
    pub const ALL: [Self; 29] = [
        Self::IntAdd,
        Self::IntSub,
        Self::IntMul,
        Self::IntTDiv,
        Self::IntMod,
        Self::IntPowMod,
        Self::IntLog2,
        Self::IntShiftRight,
        Self::IntShiftLeft,
        Self::IntBitAnd,
        Self::IntBitXor,
        Self::IntBitOr,
        Self::IntGreaterEqual,
        Self::IntGreater,
        Self::IntLessEqual,
        Self::IntLess,
        Self::IntEqual,
        Self::IntNotEqual,
        Self::BoolNot,
        Self::BoolEqual,
        Self::BoolNotEqual,
        Self::BoolAnd,
        Self::BoolOr,
        Self::BytesLength,
        Self::BytesGet,
        Self::BytesEmpty,
        Self::BytesUpdate,
        Self::BytesPadRight,
        Self::BytesSubstring,
    ];

    /// Returns the exact result sort from the pinned builtin signature.
    #[must_use]
    pub const fn result_sort(self) -> BuiltinSort {
        match self {
            Self::IntAdd
            | Self::IntSub
            | Self::IntMul
            | Self::IntTDiv
            | Self::IntMod
            | Self::IntPowMod
            | Self::IntLog2
            | Self::IntShiftRight
            | Self::IntShiftLeft
            | Self::IntBitAnd
            | Self::IntBitXor
            | Self::IntBitOr
            | Self::BytesLength
            | Self::BytesGet => BuiltinSort::Int,
            Self::BytesEmpty | Self::BytesUpdate | Self::BytesPadRight | Self::BytesSubstring => {
                BuiltinSort::Bytes
            }
            Self::IntGreaterEqual
            | Self::IntGreater
            | Self::IntLessEqual
            | Self::IntLess
            | Self::IntEqual
            | Self::IntNotEqual
            | Self::BoolNot
            | Self::BoolEqual
            | Self::BoolNotEqual
            | Self::BoolAnd
            | Self::BoolOr => BuiltinSort::Bool,
        }
    }

    /// Whether this pinned builtin is a K function and may root a simplifier lemma.
    ///
    /// This deliberately exhausts the catalog so adding an operation requires
    /// an explicit compatibility decision instead of silently widening the
    /// simplification contract.
    #[must_use]
    pub const fn is_functional(self) -> bool {
        match self {
            Self::IntAdd
            | Self::IntSub
            | Self::IntMul
            | Self::IntTDiv
            | Self::IntMod
            | Self::IntPowMod
            | Self::IntLog2
            | Self::IntShiftRight
            | Self::IntShiftLeft
            | Self::IntBitAnd
            | Self::IntBitXor
            | Self::IntBitOr
            | Self::IntGreaterEqual
            | Self::IntGreater
            | Self::IntLessEqual
            | Self::IntLess
            | Self::IntEqual
            | Self::IntNotEqual
            | Self::BoolNot
            | Self::BoolEqual
            | Self::BoolNotEqual
            | Self::BoolAnd
            | Self::BoolOr
            | Self::BytesLength
            | Self::BytesGet
            | Self::BytesEmpty
            | Self::BytesUpdate
            | Self::BytesPadRight
            | Self::BytesSubstring => true,
        }
    }

    /// Returns the ordered argument sorts from the pinned builtin signature.
    #[must_use]
    pub const fn argument_sorts(self) -> &'static [BuiltinSort] {
        const INT_INT: &[BuiltinSort] = &[BuiltinSort::Int, BuiltinSort::Int];
        const INT: &[BuiltinSort] = &[BuiltinSort::Int];
        const INT_INT_INT: &[BuiltinSort] = &[BuiltinSort::Int, BuiltinSort::Int, BuiltinSort::Int];
        const BOOL: &[BuiltinSort] = &[BuiltinSort::Bool];
        const BOOL_BOOL: &[BuiltinSort] = &[BuiltinSort::Bool, BuiltinSort::Bool];
        const BYTES: &[BuiltinSort] = &[BuiltinSort::Bytes];
        const BYTES_INT: &[BuiltinSort] = &[BuiltinSort::Bytes, BuiltinSort::Int];
        const BYTES_INT_INT: &[BuiltinSort] =
            &[BuiltinSort::Bytes, BuiltinSort::Int, BuiltinSort::Int];
        const EMPTY: &[BuiltinSort] = &[];
        match self {
            Self::IntAdd
            | Self::IntSub
            | Self::IntMul
            | Self::IntTDiv
            | Self::IntMod
            | Self::IntShiftRight
            | Self::IntShiftLeft
            | Self::IntBitAnd
            | Self::IntBitXor
            | Self::IntBitOr
            | Self::IntGreaterEqual
            | Self::IntGreater
            | Self::IntLessEqual
            | Self::IntLess
            | Self::IntEqual
            | Self::IntNotEqual => INT_INT,
            Self::IntPowMod => INT_INT_INT,
            Self::IntLog2 => INT,
            Self::BoolNot => BOOL,
            Self::BoolEqual | Self::BoolNotEqual | Self::BoolAnd | Self::BoolOr => BOOL_BOOL,
            Self::BytesLength => BYTES,
            Self::BytesGet => BYTES_INT,
            Self::BytesEmpty => EMPTY,
            Self::BytesUpdate | Self::BytesPadRight | Self::BytesSubstring => BYTES_INT_INT,
        }
    }
}

/// An application reference whose declared identity depends on the IR layer.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(
    tag = "application_source",
    content = "application",
    rename_all = "snake_case"
)]
pub enum ApplicationRef<D> {
    /// An authored production resolved by the compiler.
    Declared(D),
    /// A compiler-provided operation from the exact builtin catalog.
    Builtin(BuiltinOperation),
}

/// Stable nominal identity of a production group.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(transparent)]
pub struct ProductionGroupId(String);

impl ProductionGroupId {
    /// Creates a nonempty, path-free group identity.
    ///
    /// # Errors
    ///
    /// Returns [`IrIdentityError`] for blank or path-shaped input.
    pub fn new(value: impl Into<String>) -> Result<Self, IrIdentityError> {
        validated_id("production_group_id", value.into()).map(Self)
    }

    /// Returns the stable identity.
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl<'de> Deserialize<'de> for ProductionGroupId {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Self::new(String::deserialize(deserializer)?).map_err(serde::de::Error::custom)
    }
}

/// Stable name of one nonterminal field in a nominal production.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(transparent)]
pub struct ProductionFieldId(String);

impl ProductionFieldId {
    /// Creates a nonempty, path-free field identity.
    ///
    /// # Errors
    ///
    /// Returns [`IrIdentityError`] for blank or path-shaped input.
    pub fn new(value: impl Into<String>) -> Result<Self, IrIdentityError> {
        validated_id("production_field_id", value.into()).map(Self)
    }

    /// Returns the stable field name.
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl<'de> Deserialize<'de> for ProductionFieldId {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Self::new(String::deserialize(deserializer)?).map_err(serde::de::Error::custom)
    }
}

/// One grammar item with mandatory nested provenance.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub struct GrammarProductionItem<S> {
    origin: NodeOrigin,
    #[serde(flatten)]
    kind: GrammarProductionItemKind<S>,
}

impl<S> GrammarProductionItem<S> {
    /// Creates a literal terminal.
    ///
    /// # Errors
    ///
    /// Returns [`GrammarShapeError`] when the terminal is empty.
    pub fn terminal(
        origin: NodeOrigin,
        text: impl Into<String>,
    ) -> Result<Self, GrammarShapeError> {
        let text = text.into();
        if text.is_empty() {
            return Err(GrammarShapeError::EmptyText("production terminal"));
        }
        Ok(Self {
            origin,
            kind: GrammarProductionItemKind::Terminal { text },
        })
    }

    /// Creates a named nonterminal.
    #[must_use]
    pub const fn non_terminal(origin: NodeOrigin, field: ProductionFieldId, sort: S) -> Self {
        Self {
            origin,
            kind: GrammarProductionItemKind::NonTerminal { field, sort },
        }
    }

    /// Creates a K-compatible regex terminal with explicit lexical guards.
    ///
    /// # Errors
    ///
    /// Returns [`GrammarShapeError`] for an empty central regex or an empty
    /// present guard.
    pub fn regex_terminal(
        origin: NodeOrigin,
        precede_regex: Option<String>,
        regex: impl Into<String>,
        follow_regex: Option<String>,
    ) -> Result<Self, GrammarShapeError> {
        let regex = regex.into();
        if regex.is_empty() {
            return Err(GrammarShapeError::EmptyText("production regex"));
        }
        if precede_regex.as_deref() == Some("") {
            return Err(GrammarShapeError::EmptyText("precede regex"));
        }
        if follow_regex.as_deref() == Some("") {
            return Err(GrammarShapeError::EmptyText("follow regex"));
        }
        Ok(Self {
            origin,
            kind: GrammarProductionItemKind::RegexTerminal {
                precede_regex,
                regex,
                follow_regex,
            },
        })
    }

    /// Returns mandatory item provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }

    /// Returns the typed item form.
    #[must_use]
    pub const fn kind(&self) -> &GrammarProductionItemKind<S> {
        &self.kind
    }
}

/// The recognized grammar item families.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(tag = "item_kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum GrammarProductionItemKind<S> {
    /// Literal terminal text.
    Terminal {
        /// Exact source text.
        text: String,
    },
    /// A named nonterminal with a typed sort reference.
    NonTerminal {
        /// Stable field name used by strictness metadata.
        field: ProductionFieldId,
        /// Referenced sort.
        sort: S,
    },
    /// K regex terminal, including optional lexical lookaround guards.
    RegexTerminal {
        /// Regex which may not precede this token.
        #[serde(skip_serializing_if = "Option::is_none")]
        precede_regex: Option<String>,
        /// Central token regex.
        regex: String,
        /// Regex which may not follow this token.
        #[serde(skip_serializing_if = "Option::is_none")]
        follow_regex: Option<String>,
    },
}

/// Typed format fragment. Item positions are one-based K production-item
/// positions and are checked against the production shape.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(tag = "format_kind", content = "value", rename_all = "snake_case")]
pub enum FormatFragment {
    /// Literal output text.
    Literal(String),
    /// One-based production-item position (`%1`, `%2`, ... in K source).
    Item(u16),
    /// K's `%n` line-break control.
    Newline,
    /// K's `%i` indentation-increase control.
    Indent,
    /// K's `%d` indentation-decrease control.
    Dedent,
}

/// Strictness strategy for a production.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum StrictnessKind {
    /// Selected fields may heat independently.
    Strict,
    /// Selected fields heat in the declared order.
    SeqStrict,
}

/// One provenance-bearing selected production field.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProductionFieldReference {
    origin: NodeOrigin,
    field: ProductionFieldId,
}

impl ProductionFieldReference {
    /// Creates one selected field occurrence.
    #[must_use]
    pub const fn new(origin: NodeOrigin, field: ProductionFieldId) -> Self {
        Self { origin, field }
    }
    /// Returns exact selected-field provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns the selected field identity.
    #[must_use]
    pub const fn field(&self) -> &ProductionFieldId {
        &self.field
    }
}

/// One provenance-bearing typed context-alias reference.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProductionContextAliasReference {
    origin: NodeOrigin,
    alias: StableItemId,
}

impl ProductionContextAliasReference {
    /// Creates one resolved context-alias selection.
    #[must_use]
    pub const fn new(origin: NodeOrigin, alias: StableItemId) -> Self {
        Self { origin, alias }
    }
    /// Returns exact `using` occurrence provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns the selected declaration identity.
    #[must_use]
    pub const fn alias(&self) -> &StableItemId {
        &self.alias
    }
}

/// One provenance-bearing result-predicate sort selection.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProductionResultSort<S> {
    origin: NodeOrigin,
    sort: S,
}

impl<S> ProductionResultSort<S> {
    /// Creates one explicit result-sort occurrence.
    #[must_use]
    pub const fn new(origin: NodeOrigin, sort: S) -> Self {
        Self { origin, sort }
    }
    /// Returns exact result-sort provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns the selected sort.
    #[must_use]
    pub const fn sort(&self) -> &S {
        &self.sort
    }
}

/// One classified production attribute with mandatory provenance.
#[allow(clippy::large_enum_variant)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(tag = "attribute_kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum ProductionAttribute<S> {
    /// Literal documentation emitted as a K source comment.
    Documentation {
        /// Documentation provenance.
        origin: NodeOrigin,
        /// One normalized Rust rustdoc line.
        text: String,
    },
    /// Declares the production as a K function.
    Function {
        /// Attribute provenance.
        origin: NodeOrigin,
    },
    /// Declares a functional production as total.
    Total {
        /// Attribute provenance.
        origin: NodeOrigin,
    },
    /// Selects one exact backend hook for this function production.
    Hook {
        /// Attribute provenance.
        origin: NodeOrigin,
        /// Closed hook identity.
        operation: HookOperation,
    },
    /// Declares a constructor production as a reversible static alias.
    Alias {
        /// Attribute provenance.
        origin: NodeOrigin,
    },
    /// Declares a regex production as a token, with optional lexical priority.
    Token {
        /// Attribute provenance.
        origin: NodeOrigin,
        /// Pinned K lexical `prec` value.
        #[serde(skip_serializing_if = "Option::is_none")]
        lexical_precedence: Option<u32>,
    },
    /// Assigns the production to a nominal precedence/associativity group.
    Group {
        /// Attribute provenance.
        origin: NodeOrigin,
        /// Stable group identity.
        group: ProductionGroupId,
    },
    /// Syntax-only bracket production.
    Bracket {
        /// Attribute provenance.
        origin: NodeOrigin,
    },
    /// K's typed `avoid` parser preference.
    Avoid {
        /// Attribute provenance.
        origin: NodeOrigin,
    },
    /// Structured unparse formatting.
    Format {
        /// Attribute provenance.
        origin: NodeOrigin,
        /// Ordered typed fragments.
        fragments: Vec<FormatFragment>,
    },
    /// Strict or sequentially strict evaluation fields and result predicate.
    Strictness {
        /// Attribute provenance.
        origin: NodeOrigin,
        /// Evaluation strategy.
        kind: StrictnessKind,
        /// Optional typed context-alias declaration reference.
        #[serde(skip_serializing_if = "Option::is_none")]
        using: Option<ProductionContextAliasReference>,
        /// Named fields, preserving authored order for `seqstrict`.
        fields: Vec<ProductionFieldReference>,
        /// Sort whose values satisfy the cooling/result predicate.
        result_sort: ProductionResultSort<S>,
    },
}

impl<S> ProductionAttribute<S> {
    /// Returns mandatory attribute provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        match self {
            Self::Documentation { origin, .. }
            | Self::Function { origin }
            | Self::Total { origin }
            | Self::Hook { origin, .. }
            | Self::Alias { origin }
            | Self::Token { origin, .. }
            | Self::Group { origin, .. }
            | Self::Bracket { origin }
            | Self::Avoid { origin }
            | Self::Format { origin, .. }
            | Self::Strictness { origin, .. } => origin,
        }
    }

    /// Returns the stable diagnostic name for a non-repeatable attribute.
    #[must_use]
    pub(crate) const fn unique_name(&self) -> Option<&'static str> {
        match self {
            Self::Documentation { .. } => None,
            Self::Function { .. } => Some("function"),
            Self::Total { .. } => Some("total"),
            Self::Hook { .. } => Some("hook"),
            Self::Alias { .. } => Some("alias"),
            Self::Token { .. } => Some("token"),
            Self::Group { .. } => Some("group"),
            Self::Bracket { .. } => Some("bracket"),
            Self::Avoid { .. } => Some("avoid"),
            Self::Format { .. } => Some("format"),
            Self::Strictness { .. } => Some("strictness"),
        }
    }
}

/// Group associativity. This applies to all cross-products of productions in
/// the named groups and is distinct from a per-production self-association.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum GroupAssociativity {
    /// Left associative.
    Left,
    /// Right associative.
    Right,
    /// Neither side may associate.
    NonAssociative,
}

/// One direct partial-order edge between nonempty sets of production groups.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PrecedenceRelation {
    origin: NodeOrigin,
    higher: Vec<ProductionGroupId>,
    lower: Vec<ProductionGroupId>,
}

impl PrecedenceRelation {
    /// Creates one direct higher-than edge.
    ///
    /// # Errors
    ///
    /// Returns [`GrammarShapeError`] for empty sides or repeated groups.
    pub fn new(
        origin: NodeOrigin,
        higher: Vec<ProductionGroupId>,
        lower: Vec<ProductionGroupId>,
    ) -> Result<Self, GrammarShapeError> {
        if higher.is_empty() || lower.is_empty() {
            return Err(GrammarShapeError::EmptyPrecedenceSide);
        }
        if has_duplicates(&higher) || has_duplicates(&lower) {
            return Err(GrammarShapeError::DuplicateGroup);
        }
        Ok(Self {
            origin,
            higher,
            lower,
        })
    }

    /// Returns sentence provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }

    /// Returns groups on the tighter-binding side.
    #[must_use]
    pub fn higher(&self) -> &[ProductionGroupId] {
        &self.higher
    }

    /// Returns groups on the looser-binding side.
    #[must_use]
    pub fn lower(&self) -> &[ProductionGroupId] {
        &self.lower
    }
}

/// One group-associativity sentence.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GroupAssociativitySentence {
    origin: NodeOrigin,
    associativity: GroupAssociativity,
    groups: Vec<ProductionGroupId>,
}

impl GroupAssociativitySentence {
    /// Creates an associativity sentence over at least one distinct group.
    ///
    /// # Errors
    ///
    /// Returns [`GrammarShapeError`] for an empty or repeated group list.
    pub fn new(
        origin: NodeOrigin,
        associativity: GroupAssociativity,
        groups: Vec<ProductionGroupId>,
    ) -> Result<Self, GrammarShapeError> {
        if groups.is_empty() {
            return Err(GrammarShapeError::EmptyAssociativity);
        }
        if has_duplicates(&groups) {
            return Err(GrammarShapeError::DuplicateGroup);
        }
        Ok(Self {
            origin,
            associativity,
            groups,
        })
    }

    /// Returns sentence provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }

    /// Returns the group strategy.
    #[must_use]
    pub const fn associativity(&self) -> GroupAssociativity {
        self.associativity
    }

    /// Returns referenced groups.
    #[must_use]
    pub fn groups(&self) -> &[ProductionGroupId] {
        &self.groups
    }
}

/// Invalid target-neutral grammar shape.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum GrammarShapeError {
    /// A textual field was empty.
    EmptyText(&'static str),
    /// One side of a precedence relation was empty.
    EmptyPrecedenceSide,
    /// An associativity sentence named no groups.
    EmptyAssociativity,
    /// A set-valued group list repeated an identity.
    DuplicateGroup,
}

impl fmt::Display for GrammarShapeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyText(field) => write!(formatter, "{field} must not be empty"),
            Self::EmptyPrecedenceSide => {
                formatter.write_str("both precedence relation sides must be nonempty")
            }
            Self::EmptyAssociativity => {
                formatter.write_str("associativity must reference at least one group")
            }
            Self::DuplicateGroup => formatter.write_str("group list contains a duplicate"),
        }
    }
}

impl Error for GrammarShapeError {}

fn has_duplicates<T: Ord + Clone>(values: &[T]) -> bool {
    let mut canonical = values.to_vec();
    canonical.sort();
    canonical.windows(2).any(|pair| pair[0] == pair[1])
}
