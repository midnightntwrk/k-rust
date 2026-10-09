//! Target-neutral object-grammar contracts shared by semantic and Definition IR.
//!
//! These types classify every K attribute the expression grammar needs.
//! In particular, an adapter cannot smuggle raw attribute names, K labels, or
//! parser-internal production IDs through this layer.

use std::error::Error;
use std::fmt;

use serde::{Deserialize, Deserializer, Serialize};

use crate::{IrIdentityError, NodeOrigin, StableItemId, ir::validated_id};

pub use crate::catalog::{BuiltinOperation, HookOperation};

/// An application reference whose declared identity depends on the IR layer.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(
    tag = "application_source",
    content = "application",
    rename_all = "snake_case"
)]
pub enum ApplicationRef<D, S> {
    /// An authored production resolved by the compiler.
    Declared(D),
    /// A compiler-provided operation from the exact builtin catalog.
    Builtin(BuiltinOperation),
    /// An operation K generates for every sort, keyed by that sort.
    Generated(GeneratedOperation<S>),
}

/// A function K generates for every sort `S` (`k::is!` and `k::project!`).
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum GeneratedOperation<S> {
    /// K's total sort predicate `isS(T)`: one argument of sort `K`, result `Bool`.
    SortPredicate(S),
    /// K's partial projection `{T}:>S` (`project:S`): one argument of sort `K`,
    /// result `S`; undefined when the argument is not an `S`.
    SortProjection(S),
}

impl<S> GeneratedOperation<S> {
    /// Returns the sort the operation is generated for.
    #[must_use]
    pub const fn sort(&self) -> &S {
        match self {
            Self::SortPredicate(sort) | Self::SortProjection(sort) => sort,
        }
    }

    /// Applies `map` to the sort the operation is generated for.
    ///
    /// # Errors
    ///
    /// Returns the error of `map`.
    pub fn try_map_sort<T, E>(
        &self,
        map: impl FnOnce(&S) -> Result<T, E>,
    ) -> Result<GeneratedOperation<T>, E> {
        Ok(match self {
            Self::SortPredicate(sort) => GeneratedOperation::SortPredicate(map(sort)?),
            Self::SortProjection(sort) => GeneratedOperation::SortProjection(map(sort)?),
        })
    }
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
        validated_id(crate::IrIdentityKind::ProductionGroupId, value.into()).map(Self)
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
        validated_id(crate::IrIdentityKind::ProductionFieldId, value.into()).map(Self)
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
            return Err(GrammarShapeError::EmptyText(
                crate::IrField::ProductionTerminal,
            ));
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
            return Err(GrammarShapeError::EmptyText(
                crate::IrField::ProductionRegex,
            ));
        }
        if precede_regex.as_deref() == Some("") {
            return Err(GrammarShapeError::EmptyText(crate::IrField::PrecedeRegex));
        }
        if follow_regex.as_deref() == Some("") {
            return Err(GrammarShapeError::EmptyText(crate::IrField::FollowRegex));
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
    /// K's `%c` control: start printing in the production's next colour.
    ColorNext,
    /// K's `%r` control: reset the printing colour.
    ColorReset,
}

/// One fragment of a function's `smt_hook` SMT-LIB template (KF-044).
///
/// A field fragment stands for the production's argument at that field; K's
/// `smt-hook` spells it `#N`, the field's one-based nonterminal position.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(tag = "smt_kind", content = "value", rename_all = "snake_case")]
pub enum SmtFragment {
    /// Literal SMT-LIB text.
    Text(String),
    /// The argument at one named production field.
    Field(ProductionFieldId),
}

/// Whether `symbol` is an SMT-LIB simple symbol: a nonempty sequence of
/// ASCII letters, digits, and `~!@$%^&*_+=<>.?/-` that does not start with a
/// digit (SMT-LIB 2.6, section 3.1).
#[must_use]
pub fn is_smtlib_simple_symbol(symbol: &str) -> bool {
    const PUNCTUATION: &[u8] = b"~!@$%^&*_+=<>.?/-";
    let mut bytes = symbol.bytes();
    bytes
        .next()
        .is_some_and(|first| first.is_ascii_alphabetic() || PUNCTUATION.contains(&first))
        && bytes.all(|byte| byte.is_ascii_alphanumeric() || PUNCTUATION.contains(&byte))
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
///
/// `S` is the level's sort reference and `D` its declaration identity: an
/// authored item at the Semantic level and a generated symbol at the
/// Definition level.
#[cfg_attr(
    target_pointer_width = "64",
    expect(
        clippy::large_enum_variant,
        reason = "Public production attribute payloads retain their unboxed construction API; the size imbalance is specific to 64-bit targets."
    )
)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(tag = "attribute_kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum ProductionAttribute<S, D> {
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
        /// K's `alias-rec`: an expansion may apply again to its own output.
        #[serde(default, skip_serializing_if = "is_false")]
        recursive: bool,
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
    /// Usable in rules but not program syntax. Semantic IR only: lowering
    /// consumes it when it places the production in the semantics module.
    Internal {
        /// Attribute provenance.
        origin: NodeOrigin,
    },
    /// Asserts that the production is program syntax. Semantic IR only:
    /// lowering consumes it and warns when the production cannot be placed in
    /// the program-syntax module.
    Program {
        /// Attribute provenance.
        origin: NodeOrigin,
    },
    /// K's `color(name)`: one colour for every printed terminal.
    Color {
        /// Attribute provenance.
        origin: NodeOrigin,
        /// Colour name, not checked against K's colour table.
        value: String,
    },
    /// K's `colors(a,b,..)`: one colour per printed terminal and per `%c`.
    Colors {
        /// Attribute provenance.
        origin: NodeOrigin,
        /// Colour names in printing order.
        values: Vec<String>,
    },
    /// K's typed `prefer` parser preference, the counterpart of `avoid`.
    Prefer {
        /// Attribute provenance.
        origin: NodeOrigin,
    },
    /// K's `overload(key)`: the production belongs to an overload family.
    ///
    /// At the Semantic level `target` is the authored target production; at
    /// the Definition level it is the family root, whose symbol is K's family
    /// key, and the root carries the attribute too.
    Overload {
        /// Attribute provenance.
        origin: NodeOrigin,
        /// The overloaded production.
        target: D,
    },
    /// K's `private`: the production is visible only to its own module.
    /// Definition IR only: lowering derives it for a production whose Rust
    /// item is not `pub`.
    Private {
        /// Attribute provenance.
        origin: NodeOrigin,
    },
    /// K's `memo`: a hint that a function's results may be memoized.
    Memo {
        /// Attribute provenance.
        origin: NodeOrigin,
    },
    /// The cons production of a `#[k::syntax_list]` sort, K's
    /// `List{Elem, "sep"}` or `NeList{..}` (KF-020). Its items are
    /// `[NonTerminal head, Terminal(sep) when sep is nonempty, NonTerminal tail]`.
    ListCons {
        /// Attribute provenance.
        origin: NodeOrigin,
        /// The separator terminal; empty for a list without separator.
        separator: String,
        /// Whether the list is K's `NeList`: programs cannot write it empty.
        non_empty: bool,
        /// The list's terminator production.
        terminator: D,
    },
    /// The terminator production of a `#[k::syntax_list]` sort, whose only
    /// item is the terminal `.Sort`; K generates it from the cons sentence.
    ListTerminator {
        /// Attribute provenance.
        origin: NodeOrigin,
        /// The list's cons production.
        cons: D,
    },
    /// A quoted hook, `hook = "NAMESPACE.name"`: K's exact hook name, which
    /// the pinned hook registry knows but the typed catalog does not cover.
    /// Its signature is unchecked; the package must allow raw K.
    RawHook {
        /// Attribute provenance.
        origin: NodeOrigin,
        /// Hook namespace before the first `.`, such as `KRYPTO`.
        namespace: String,
        /// Hook name after the first `.`, such as `keccak256`.
        name: String,
    },
    /// K's `freshGenerator`: the total function, of one Int argument, that
    /// produces the fresh values of its result sort (`#[k::fresh]`, KF-022).
    FreshGenerator {
        /// Attribute provenance.
        origin: NodeOrigin,
    },
    /// K's `smtlib(symbol)`: the SMT solver sees the function as the
    /// uninterpreted SMT-LIB symbol `symbol` (KF-044).
    Smtlib {
        /// Attribute provenance.
        origin: NodeOrigin,
        /// SMT-LIB simple symbol.
        symbol: String,
    },
    /// K's `smt-hook(template)`: the SMT solver sees the function as the
    /// SMT-LIB term `template` over its arguments (KF-044).
    SmtHook {
        /// Attribute provenance.
        origin: NodeOrigin,
        /// Checked template fragments in source order.
        template: Vec<SmtFragment>,
    },
    /// Declares a constructor production as a one-way static desugar, K's
    /// `macro` (`macro-rec` when `recursive`), expanded before anything runs
    /// and never printed backwards (KF-028).
    Desugar {
        /// Attribute provenance.
        origin: NodeOrigin,
        /// K's `macro-rec`: an expansion may apply again to its own output.
        #[serde(default, skip_serializing_if = "is_false")]
        recursive: bool,
    },
}

#[expect(
    clippy::trivially_copy_pass_by_ref,
    reason = "serde's skip_serializing_if passes the field by reference."
)]
const fn is_false(value: &bool) -> bool {
    !*value
}

impl<S, D> ProductionAttribute<S, D> {
    /// Returns mandatory attribute provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        match self {
            Self::Documentation { origin, .. }
            | Self::Function { origin }
            | Self::Total { origin }
            | Self::Hook { origin, .. }
            | Self::Alias { origin, .. }
            | Self::Desugar { origin, .. }
            | Self::Token { origin, .. }
            | Self::Group { origin, .. }
            | Self::Bracket { origin }
            | Self::Avoid { origin }
            | Self::Format { origin, .. }
            | Self::Strictness { origin, .. }
            | Self::Internal { origin }
            | Self::Program { origin }
            | Self::Color { origin, .. }
            | Self::Colors { origin, .. }
            | Self::Prefer { origin }
            | Self::Overload { origin, .. }
            | Self::Private { origin }
            | Self::Memo { origin }
            | Self::ListCons { origin, .. }
            | Self::ListTerminator { origin, .. }
            | Self::RawHook { origin, .. }
            | Self::FreshGenerator { origin }
            | Self::Smtlib { origin, .. }
            | Self::SmtHook { origin, .. } => origin,
        }
    }

    /// Returns the non-repeatable production attribute family.
    #[must_use]
    pub const fn unique_family(&self) -> Option<crate::ProductionAttributeFamily> {
        match self {
            Self::Documentation { .. } => None,
            Self::Function { .. } => Some(crate::ProductionAttributeFamily::Function),
            Self::Total { .. } => Some(crate::ProductionAttributeFamily::Total),
            Self::Hook { .. } | Self::RawHook { .. } => {
                Some(crate::ProductionAttributeFamily::Hook)
            }
            Self::Alias { .. } => Some(crate::ProductionAttributeFamily::Alias),
            Self::Token { .. } => Some(crate::ProductionAttributeFamily::Token),
            Self::Group { .. } => Some(crate::ProductionAttributeFamily::Group),
            Self::Bracket { .. } => Some(crate::ProductionAttributeFamily::Bracket),
            Self::Avoid { .. } => Some(crate::ProductionAttributeFamily::Avoid),
            Self::Format { .. } => Some(crate::ProductionAttributeFamily::Format),
            Self::Strictness { .. } => Some(crate::ProductionAttributeFamily::Strictness),
            Self::Internal { .. } => Some(crate::ProductionAttributeFamily::Internal),
            Self::Program { .. } => Some(crate::ProductionAttributeFamily::Program),
            Self::Color { .. } | Self::Colors { .. } => {
                Some(crate::ProductionAttributeFamily::Color)
            }
            Self::Prefer { .. } => Some(crate::ProductionAttributeFamily::Prefer),
            Self::Overload { .. } => Some(crate::ProductionAttributeFamily::Overload),
            Self::Private { .. } => Some(crate::ProductionAttributeFamily::Private),
            Self::Memo { .. } => Some(crate::ProductionAttributeFamily::Memo),
            Self::ListCons { .. } => Some(crate::ProductionAttributeFamily::ListCons),
            Self::ListTerminator { .. } => Some(crate::ProductionAttributeFamily::ListTerminator),
            Self::FreshGenerator { .. } => Some(crate::ProductionAttributeFamily::FreshGenerator),
            Self::Smtlib { .. } | Self::SmtHook { .. } => {
                Some(crate::ProductionAttributeFamily::Smt)
            }
            Self::Desugar { .. } => Some(crate::ProductionAttributeFamily::Desugar),
        }
    }
}

/// The K sentence keyword a `k::raw_k!` text starts with.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RawSentenceKind {
    /// `rule`.
    Rule,
    /// `claim`.
    Claim,
    /// `context`.
    Context,
}

impl RawSentenceKind {
    /// The K keyword.
    #[must_use]
    pub const fn keyword(self) -> &'static str {
        match self {
            Self::Rule => "rule",
            Self::Claim => "claim",
            Self::Context => "context",
        }
    }

    /// The kind whose keyword is `keyword`.
    #[must_use]
    pub fn from_keyword(keyword: &str) -> Option<Self> {
        match keyword {
            "rule" => Some(Self::Rule),
            "claim" => Some(Self::Claim),
            "context" => Some(Self::Context),
            _ => None,
        }
    }
}

/// One `k::raw_k!` sentence: K text that KRS does not parse, placed verbatim
/// in its package's semantics module and parsed by K with that module's
/// grammar. It is never a transition descriptor and joins no KRS sentence
/// provenance beyond its own origin.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RawSentence {
    /// The `raw_k!` text literal.
    pub origin: NodeOrigin,
    /// The sentence keyword the text starts with.
    pub kind: RawSentenceKind,
    /// The complete K sentence text, verbatim.
    pub text: String,
    /// One-based line of the `raw_k!` invocation in its source file.
    pub line: u32,
    /// One-based column of the `raw_k!` invocation.
    pub column: u32,
    /// Definition IR only: every builtin sort the package mentions. Raw text
    /// is opaque, so its module imports the full K module of each of them.
    #[serde(default, skip_serializing_if = "std::collections::BTreeSet::is_empty")]
    pub builtin_sorts: std::collections::BTreeSet<crate::BuiltinSort>,
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

/// One named regex fragment, K's `syntax lexical Name = r".."`.
///
/// A lexical adds no syntax; token, layout, and lexical regexes refer to it
/// as `{Name}`.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LexicalSentence {
    origin: NodeOrigin,
    name: String,
    regex: String,
}

impl LexicalSentence {
    /// Creates a named lexical.
    ///
    /// # Errors
    ///
    /// Returns [`GrammarShapeError`] for an empty name or regex.
    pub fn new(
        origin: NodeOrigin,
        name: impl Into<String>,
        regex: impl Into<String>,
    ) -> Result<Self, GrammarShapeError> {
        let name = name.into();
        let regex = regex.into();
        if name.is_empty() {
            return Err(GrammarShapeError::EmptyText(crate::IrField::LexicalName));
        }
        if regex.is_empty() {
            return Err(GrammarShapeError::EmptyText(
                crate::IrField::ProductionRegex,
            ));
        }
        Ok(Self {
            origin,
            name,
            regex,
        })
    }

    /// Returns sentence provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }

    /// Returns the lexical name, referenced as `{Name}`.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the unescaped regex text.
    #[must_use]
    pub fn regex(&self) -> &str {
        &self.regex
    }
}

/// One layout regex, K's `syntax #Layout ::= r".." [token]`.
///
/// Declaring any layout replaces K's default layout.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LayoutSentence {
    origin: NodeOrigin,
    regex: String,
}

impl LayoutSentence {
    /// Creates a layout regex sentence.
    ///
    /// # Errors
    ///
    /// Returns [`GrammarShapeError`] for an empty regex.
    pub fn new(origin: NodeOrigin, regex: impl Into<String>) -> Result<Self, GrammarShapeError> {
        let regex = regex.into();
        if regex.is_empty() {
            return Err(GrammarShapeError::EmptyText(
                crate::IrField::ProductionRegex,
            ));
        }
        Ok(Self { origin, regex })
    }

    /// Returns sentence provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }

    /// Returns the unescaped regex text.
    #[must_use]
    pub fn regex(&self) -> &str {
        &self.regex
    }
}

/// Invalid target-neutral grammar shape.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum GrammarShapeError {
    /// A textual field was empty.
    EmptyText(crate::IrField),
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
