use krs_ir::{AtLeastTwo, SortTestKind};
use proc_macro2::{Span, TokenStream};
use quote::ToTokens;
use syn::parse::Parser;
use syn::spanned::Spanned;
use syn::{
    Expr, ExprCall, ExprGroup, ExprLit, ExprMacro, ExprParen, ExprPath, ExprStruct, ExprUnary, Lit,
    LitBool, LitByteStr, LitInt, LitStr, Member, Pat, PatIdent, PatOr, PatStruct, PatTupleStruct,
    Path, Token, UnOp,
};

use crate::parse::{KeyAllocator, KrsSyntax};
use crate::path::{is_plain_path, path_text};
use crate::positions::{PatternRoot, RootConstruct};
use crate::{ProvenanceAnchor, ProvenanceRole, SyntaxError, SyntaxErrorKind, TokenRange};
use krs_ir::ProvenanceKey;

/// Syntactic shape at the root of an accepted term.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TermRootKind {
    /// Bare named path: a variable/reference or a unit constructor after resolution.
    Named,
    /// Tuple/unit-like named constructor application, `path(arguments...)`.
    Call,
    /// Record named constructor application, `path { fields... }`.
    Record,
    /// Integer or Boolean Rust literal.
    Literal,
    /// Anonymous wildcard admitted only by a structured rule pattern.
    Wildcard,
}

/// An unsuffixed Rust integer literal in any radix, optionally negative (`-1`,
/// `0xFF0F`, `-0x10`).
///
/// The sign belongs to the literal: a negative literal's token carries it, so
/// its decimal value ([`Self::base10_digits`]) is the signed K `Int` token,
/// and its source range runs from the `-` through the digits.
#[derive(Clone, Debug)]
pub struct IntegerLiteral {
    literal: LitInt,
    range: TokenRange,
}

impl IntegerLiteral {
    /// An unsigned literal, ranging over its own token.
    pub(crate) fn unsigned(literal: LitInt) -> Result<Self, SyntaxError> {
        let range = TokenRange::for_tokens(&literal)?;
        Ok(Self { literal, range })
    }

    /// A negative literal from its `-` and its digits' spans; `literal` holds the
    /// signed value.
    pub(crate) const fn negative(literal: LitInt, minus: Span, digits: Span) -> Self {
        Self {
            literal,
            range: TokenRange::new(minus, digits),
        }
    }

    /// Returns the literal token; a negative literal's token carries its sign.
    #[must_use]
    pub const fn literal(&self) -> &LitInt {
        &self.literal
    }

    /// Returns the base-10 value, signed, without separators or leading zeros.
    #[must_use]
    pub fn base10_digits(&self) -> &str {
        self.literal.base10_digits()
    }

    /// Returns the source range from the sign (if any) through the digits.
    #[must_use]
    pub const fn range(&self) -> TokenRange {
        self.range
    }

    /// Returns the span at which the literal begins.
    #[must_use]
    pub const fn span(&self) -> Span {
        self.range.first()
    }
}

/// A Rust float literal or `f32::`/`f64::` constant, as one K `Float` token.
///
/// The sign belongs to the literal, as for a negative integer: `-0.0` is the
/// token `-0.0`, and the source range runs from the `-` through the literal.
/// The token is the canonical spelling of [`krs_ir::float_token`]: the digits
/// without separators, `f32` as K's `f`, `f64` as `d`, and K's `pNxM` kept.
#[derive(Clone, Debug)]
pub struct FloatLiteral {
    digits: String,
    suffix: String,
    negative: bool,
    token: String,
    range: TokenRange,
}

impl FloatLiteral {
    /// Returns the canonical K Float token.
    #[must_use]
    pub fn token(&self) -> &str {
        &self.token
    }

    /// Returns the authored digits without separators, or the constant name
    /// (`NAN`, `INFINITY`, `NEG_INFINITY`) of a constant path.
    #[must_use]
    pub fn digits(&self) -> &str {
        &self.digits
    }

    /// Returns the authored Rust suffix (`f32`, `f64`, `pNxM`, or empty); a
    /// constant path's suffix is its type, `f32` or `f64`.
    #[must_use]
    pub fn suffix(&self) -> &str {
        &self.suffix
    }

    /// Whether the literal is negated by a leading `-`.
    #[must_use]
    pub const fn negative(&self) -> bool {
        self.negative
    }

    /// Returns the source range from the sign (if any) through the literal.
    #[must_use]
    pub const fn range(&self) -> TokenRange {
        self.range
    }

    /// Returns the span at which the literal begins.
    #[must_use]
    pub const fn span(&self) -> Span {
        self.range.first()
    }
}

/// Exact literal families admitted by the term grammar.
#[derive(Clone, Debug)]
pub enum TermLiteral {
    /// Unsuffixed Rust integer literal in any radix, optionally negative (`-1`).
    Integer(IntegerLiteral),
    /// Rust Boolean literal.
    Boolean(LitBool),
    /// Rust string literal, ordinary or raw, as a K `String` token. Its value
    /// holds code points in U+0000..=U+00FF only.
    String(LitStr),
    /// Rust float literal, optionally negative, or an `f32::`/`f64::` `NAN`,
    /// `INFINITY`, or `NEG_INFINITY` constant, as a K `Float` token.
    Float(FloatLiteral),
}

impl TermLiteral {
    /// Returns a canonical literal spelling suitable for target-neutral
    /// lowering. Integer separators are removed.
    #[must_use]
    pub fn spelling(&self) -> String {
        match self {
            Self::Integer(literal) => literal.base10_digits().replace('_', ""),
            Self::Boolean(literal) => literal.value.to_string(),
            Self::String(literal) => literal.value(),
            Self::Float(literal) => literal.token().to_owned(),
        }
    }

    /// The literal's authored tokens, a negative sign included.
    ///
    /// # Errors
    ///
    /// Returns [`SyntaxErrorKind::MissingTokenEndpoint`] for a literal
    /// without tokens, which a parsed literal never is.
    pub fn range(&self) -> Result<TokenRange, SyntaxError> {
        match self {
            Self::Integer(literal) => Ok(literal.range()),
            Self::Boolean(literal) => TokenRange::for_tokens(literal),
            Self::String(literal) => TokenRange::for_tokens(literal),
            Self::Float(literal) => Ok(literal.range()),
        }
    }
}

/// Typed semantic node retained in deterministic expression preorder.
#[derive(Clone, Debug)]
pub enum TermNode {
    /// Head path of a named call or record construction.
    ApplicationHead(Path),
    /// Bare path awaiting binder/constructor resolution.
    Reference(Path),
    /// Integer, Boolean, string, or float literal.
    Literal(TermLiteral),
    /// Compiler-owned concrete token of builtin sort `Id`.
    IdToken(LitStr),
    /// Compiler-owned concrete token of builtin sort `Bytes`.
    BytesToken(LitByteStr),
    /// One typed anonymous-variable occurrence.
    Anonymous {
        /// Explicit object-language sort.
        sort: Path,
        /// Exact display spelling.
        spelling: LitStr,
    },
    /// Compiler-owned associative object-Bool disjunction shell.
    OrBool(TokenRange),
    /// `k::lexeme!(Sort, "text")`: one token of a user token sort.
    Lexeme {
        /// Authored token-sort path.
        sort: Path,
        /// Token text literal.
        text: LitStr,
    },
    /// `k::is!(Sort, t)` or `k::project!(Sort, t)` macro shell.
    SortTest {
        /// Complete macro invocation range.
        range: TokenRange,
        /// Authored sort path.
        sort: Path,
    },
    /// `name @ pattern` (K's `#as`) shell in a pattern payload; it precedes
    /// the nodes of its subpattern.
    As {
        /// The alias identifier.
        binding: syn::Ident,
        /// Complete `name @ pattern` range.
        range: TokenRange,
    },
    /// `A | B | ..` (K's `#Or`) shell in a pattern payload; it precedes the
    /// nodes of its alternatives.
    Or(TokenRange),
    /// `k::matches!(subject, pattern)` (K's `:=K`) shell; it precedes the
    /// nodes of its subject, then of its pattern.
    Matches(TokenRange),
    /// One `_` of a `k::matches!` pattern; these follow the pattern's other
    /// nodes, in pattern preorder.
    MatchesWildcard(TokenRange),
    /// One `let pattern = value;` statement (K's `#let`) shell; it precedes
    /// the nodes of its pattern, then of its value, then of the rest of the
    /// block.
    Let {
        /// The `let` statement's range.
        range: TokenRange,
        /// The sort type of `let name: Sort = value;`.
        sort: Option<Path>,
    },
    /// One `_` of a `let` pattern; these follow the pattern's other nodes,
    /// in pattern preorder.
    LetWildcard(TokenRange),
    /// The closure `|binder: Sort| body` of an `ml::exists` (KF-039); it
    /// follows the `ml::exists` head and precedes the nodes of its body.
    Closure {
        /// The complete closure range.
        range: TokenRange,
        /// The quantified binder.
        binder: syn::Ident,
        /// The binder's authored sort path.
        sort: Path,
    },
    /// `k::rewrite!(from => to)` (K's local `=>`, KF-011) shell in a
    /// single-body rule's subject; it precedes the `from_nodes` nodes of its
    /// left side, then the `to_nodes` nodes of its right side.
    Rewrite {
        /// Complete macro invocation range.
        range: TokenRange,
        /// The left side's range.
        from: TokenRange,
        /// The right side's range (`()` for `.K`).
        to: TokenRange,
        /// How many nodes the left side has.
        from_nodes: usize,
        /// How many nodes the right side has.
        to_nodes: usize,
    },
}

impl TermNode {
    /// Returns the path for a named node and `None` for a literal.
    #[must_use]
    pub const fn path(&self) -> Option<&Path> {
        match self {
            Self::ApplicationHead(path) | Self::Reference(path) => Some(path),
            Self::Literal(_)
            | Self::IdToken(_)
            | Self::BytesToken(_)
            | Self::Anonymous { .. }
            | Self::OrBool(_)
            | Self::Lexeme { .. }
            | Self::SortTest { .. }
            | Self::As { .. }
            | Self::Or(_)
            | Self::Matches(_)
            | Self::MatchesWildcard(_)
            | Self::Let { .. }
            | Self::Closure { .. }
            | Self::LetWildcard(_)
            | Self::Rewrite { .. } => None,
        }
    }

    /// Returns the literal for a literal node.
    #[must_use]
    pub const fn literal(&self) -> Option<&TermLiteral> {
        match self {
            Self::Literal(literal) => Some(literal),
            Self::ApplicationHead(_)
            | Self::Reference(_)
            | Self::IdToken(_)
            | Self::BytesToken(_)
            | Self::Anonymous { .. }
            | Self::OrBool(_)
            | Self::Lexeme { .. }
            | Self::SortTest { .. }
            | Self::As { .. }
            | Self::Or(_)
            | Self::Matches(_)
            | Self::MatchesWildcard(_)
            | Self::Let { .. }
            | Self::Closure { .. }
            | Self::LetWildcard(_)
            | Self::Rewrite { .. } => None,
        }
    }

    /// The node's authored tokens, which its key's anchor covers: a path,
    /// a literal, a `k::anonymous!`'s spelling, a `k::lexeme!`'s text, or
    /// an island's whole range.
    ///
    /// # Errors
    ///
    /// Returns [`SyntaxErrorKind::MissingTokenEndpoint`] for a node without
    /// tokens, which a parsed node never is.
    pub fn range(&self) -> Result<TokenRange, SyntaxError> {
        match self {
            Self::ApplicationHead(path) | Self::Reference(path) => TokenRange::for_tokens(path),
            Self::Literal(literal) => literal.range(),
            Self::IdToken(literal) => TokenRange::for_tokens(literal),
            Self::BytesToken(literal) => TokenRange::for_tokens(literal),
            Self::Anonymous { spelling, .. } => TokenRange::for_tokens(spelling),
            Self::OrBool(range)
            | Self::SortTest { range, .. }
            | Self::As { range, .. }
            | Self::Or(range)
            | Self::Matches(range)
            | Self::MatchesWildcard(range)
            | Self::Let { range, .. }
            | Self::Closure { range, .. }
            | Self::LetWildcard(range)
            | Self::Rewrite { range, .. } => Ok(*range),
            Self::Lexeme { text, .. } => TokenRange::for_tokens(text),
        }
    }
}

/// Structured application arguments preserving Rust call-versus-record
/// semantics.
#[derive(Clone, Debug)]
pub enum TermArguments {
    /// Ordered positional arguments of `head(first, second)`.
    Positional(Vec<TermTree>),
    /// Authored named arguments of `head { second: y, first: x }`.
    Named(Vec<TermNamedArgument>),
}

impl TermArguments {
    /// Returns positional arguments, or `None` for a record application.
    #[must_use]
    pub fn positional(&self) -> Option<&[TermTree]> {
        match self {
            Self::Positional(arguments) => Some(arguments),
            Self::Named(_) => None,
        }
    }

    /// Returns named arguments, or `None` for a call application.
    #[must_use]
    pub fn named(&self) -> Option<&[TermNamedArgument]> {
        match self {
            Self::Named(arguments) => Some(arguments),
            Self::Positional(_) => None,
        }
    }
}

/// One named record argument with its exact authored Rust field identity.
#[derive(Clone, Debug)]
pub struct TermNamedArgument {
    pub(crate) name: syn::Ident,
    pub(crate) value: TermTree,
}

impl TermNamedArgument {
    /// Returns the exact record field identifier and its authored span.
    #[must_use]
    pub const fn name(&self) -> &syn::Ident {
        &self.name
    }

    /// Returns the field's structured term or pattern value.
    #[must_use]
    pub const fn value(&self) -> &TermTree {
        &self.value
    }
}

/// One named constructor or builtin application in the structured term tree.
#[derive(Clone, Debug)]
pub struct TermApplication {
    pub(crate) head: Path,
    pub(crate) arguments: TermArguments,
    pub(crate) instance: Vec<crate::TermSort>,
    pub(crate) notation: bool,
    /// The base `t` of a record update `Ctor { f: e, ..t }`, a reference.
    pub(crate) update: Option<Box<TermTree>>,
    /// Whether a record pattern ends in `..`, `Ctor { f: p, .. }`.
    pub(crate) open: bool,
}

/// One compiler-owned complete parent-cell term.
#[derive(Clone, Debug)]
pub struct CellTerm {
    pub(crate) range: TokenRange,
    pub(crate) owner: Path,
    pub(crate) fields: Vec<TermNamedArgument>,
    /// Whether a pattern ends in `..`, leaving the children it does not
    /// name unconstrained.
    pub(crate) open: bool,
    /// The base `t` of a group update `Group { f: e, ..t }`, a reference.
    pub(crate) update: Option<Box<TermTree>>,
}

impl CellTerm {
    /// Returns the complete `fragment!` invocation range.
    #[must_use]
    pub const fn range(&self) -> TokenRange {
        self.range
    }

    /// Returns the nominal `#[k::cell]` owner.
    #[must_use]
    pub const fn owner(&self) -> &Path {
        &self.owner
    }

    /// Returns authored child fields in source order.
    #[must_use]
    pub fn fields(&self) -> &[TermNamedArgument] {
        &self.fields
    }

    /// Whether the pattern ends in `..`: the children it does not name are
    /// unconstrained.
    #[must_use]
    pub const fn is_open(&self) -> bool {
        self.open
    }

    /// Returns the base `t` of a group update `Group { f: e, ..t }`.
    #[must_use]
    pub fn update(&self) -> Option<&TermTree> {
        self.update.as_deref()
    }
}

impl TermApplication {
    /// Returns the rustc-resolvable application-head path.
    #[must_use]
    pub const fn head(&self) -> &Path {
        &self.head
    }

    /// Returns positional call arguments or named record arguments.
    #[must_use]
    pub const fn arguments(&self) -> &TermArguments {
        &self.arguments
    }

    /// Returns the turbofish sort markers of a parametric production head
    /// (`Choose::<k::builtin::Int> { .. }`, KF-027), in parameter order;
    /// empty when the head has no turbofish. [`Self::head`] never carries them.
    #[must_use]
    pub fn instance(&self) -> &[crate::TermSort] {
        &self.instance
    }

    /// Whether the application is notation (`a && b`, `a || b`, or
    /// `recv.op::<D>(..)`) for a builtin call. Its [`Self::head`] is then the
    /// operation's path in the facade's `builtin` module (`bool::and_then`),
    /// which expansion qualifies with the facade; an authored head is never
    /// notation, whatever it spells.
    #[must_use]
    pub const fn is_notation(&self) -> bool {
        self.notation
    }

    /// Whether the application is a level of list notation (`[a, ..]`),
    /// which denotes a list's constructors, not an operation.
    #[must_use]
    pub fn is_list_notation(&self) -> bool {
        self.notation && crate::list_notation::is_level_head(&self.head)
    }

    /// Whether the application is notation that applies an operation, not
    /// notation for a collection's value: a level of list notation, and the
    /// empty collection and a set's singleton that a collection literal
    /// (`map![]`, `set![x]`) denotes, build values.
    #[must_use]
    pub fn applies_operation(&self) -> bool {
        self.notation
            && !crate::list_notation::is_level_head(&self.head)
            && !crate::collection_literal::is_value_head(&self.head)
    }

    /// Returns the base `t` of a record update `Ctor { f: e, ..t }`: the
    /// record is the matched record `t` with the listed fields replaced.
    #[must_use]
    pub fn update(&self) -> Option<&TermTree> {
        self.update.as_deref()
    }

    /// Whether the application is a record pattern ending in `..`,
    /// `Ctor { f: p, .. }`, whose unnamed fields are unconstrained; it may
    /// name no field, `Ctor { .. }`.
    #[must_use]
    pub const fn is_open(&self) -> bool {
        self.open
    }
}

/// Splits an application head into its rustc-resolvable path without generic
/// arguments and the sort markers of its turbofish (KF-027). Only the last
/// segment may carry generic arguments, and each must be a sort marker: a
/// plain path such as `k::builtin::Int` or a single-trait object such as
/// `dyn ExpSort`.
pub(crate) fn application_head(path: &Path) -> Result<(Path, Vec<crate::TermSort>), SyntaxError> {
    let invalid = |reason: &str, span: proc_macro2::Span| {
        SyntaxError::new(
            SyntaxErrorKind::InvalidTurbofish {
                reason: reason.to_owned(),
            },
            span,
        )
    };
    let Some(last) = path.segments.last() else {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedPath,
            path.span(),
        ));
    };
    for segment in path.segments.iter().take(path.segments.len() - 1) {
        if !matches!(segment.arguments, syn::PathArguments::None) {
            return Err(invalid(
                "a turbofish belongs on the last segment of a term head, the production: `Choose::<k::builtin::Int>`",
                segment.arguments.span(),
            ));
        }
    }
    let arguments = match &last.arguments {
        syn::PathArguments::None => return Ok((path.clone(), Vec::new())),
        syn::PathArguments::Parenthesized(arguments) => {
            return Err(invalid(
                "a term head's generic arguments are a turbofish of sort markers, such as `Choose::<k::builtin::Int>`",
                arguments.span(),
            ));
        }
        syn::PathArguments::AngleBracketed(arguments) => arguments,
    };
    if arguments.args.is_empty() {
        return Err(invalid(
            "an empty turbofish names no instance; write the sort marker, such as `Choose::<k::builtin::Int>`",
            arguments.span(),
        ));
    }
    let mut instance = Vec::with_capacity(arguments.args.len());
    for argument in &arguments.args {
        let sort = match argument {
            syn::GenericArgument::Type(ty) => crate::term_sort::parse_instance_sort(ty),
            _ => None,
        };
        let Some(sort) = sort else {
            return Err(invalid(
                "a turbofish on a term head lists sort markers only, the types that go inside `k::Term<..>`: `k::builtin::Int`, or a user sort's `dyn ExpSort`; lifetimes and consts are not sorts",
                argument.span(),
            ));
        };
        instance.push(sort);
    }
    let mut head = path.clone();
    if let Some(last) = head.segments.last_mut() {
        last.arguments = syn::PathArguments::None;
    }
    Ok((head, instance))
}

/// Whether `path` is a valid application head: a plain path, or a plain path
/// whose last segment carries a turbofish (KF-027).
fn is_head_path(path: &Path) -> bool {
    path.segments
        .iter()
        .take(path.segments.len().saturating_sub(1))
        .all(|segment| matches!(segment.arguments, syn::PathArguments::None))
        && !path.segments.is_empty()
}

/// Structured term/pattern shape used for deterministic argument lowering.
///
/// Parentheses and invisible `syn` groups are transparent. A wildcard occurs
/// only in a rule pattern, never in a result or standalone term expression.
#[derive(Clone, Debug)]
pub enum TermTree {
    /// Named application retaining positional-versus-record arguments.
    Application(TermApplication),
    /// Bare path awaiting binder or zero-argument constructor resolution.
    Reference(Path),
    /// Integer, Boolean, string, or float literal.
    Literal(TermLiteral),
    /// Native Rust pattern wildcard.
    Wildcard(TokenRange),
    /// `k::id!("$name")` concrete builtin token.
    IdToken {
        /// Exact validated token literal.
        literal: LitStr,
    },
    /// `k::bytes!(b"...")` concrete builtin token.
    BytesToken {
        /// Exact validated byte-string literal.
        literal: LitByteStr,
    },
    /// `k::anonymous!(Sort, "_Name")` anonymous occurrence.
    Anonymous {
        /// Explicit object-language sort path.
        sort: Path,
        /// Exact authored display spelling.
        spelling: LitStr,
    },
    /// `k::or_bool![...]` associative Boolean disjunction.
    OrBool {
        /// Complete macro invocation range.
        range: TokenRange,
        /// Ordered operands (at least two).
        arguments: AtLeastTwo<TermTree>,
    },
    /// `k::fragment![Parent { ... }]` complete nested-cell term.
    Cell(CellTerm),
    /// `k::lexeme!(Sort, "text")`: one token of a user token sort, which
    /// emits as `#token("text","Sort")`.
    Lexeme {
        /// Authored token-sort path.
        sort: Path,
        /// Token text literal.
        text: LitStr,
    },
    /// `k::is!(Sort, t)` (K's `isSort(T)`) or `k::project!(Sort, t)` (K's
    /// `{T}:>Sort`).
    SortTest {
        /// Complete macro invocation range.
        range: TokenRange,
        /// Predicate or projection.
        kind: SortTestKind,
        /// Authored sort path.
        sort: Path,
        /// The tested or projected term.
        operand: Box<TermTree>,
    },
    /// `name @ pattern`: K's `( PATTERN #as Name:Sort )`, only in patterns.
    As {
        /// The alias identifier.
        binding: syn::Ident,
        /// The aliased subpattern.
        pattern: Box<TermTree>,
    },
    /// `A | B | ..`: K's `( A #Or B #Or .. )`, only in patterns.
    Or {
        /// Complete or-pattern range.
        range: TokenRange,
        /// The alternatives, in source order.
        alternatives: AtLeastTwo<TermTree>,
    },
    /// `k::matches!(subject, pattern)`: K's `( PATTERN :=K SUBJECT )`, a Bool
    /// test, only in results and conditions.
    Matches {
        /// Complete macro invocation range.
        range: TokenRange,
        /// The tested term.
        subject: Box<TermTree>,
        /// The pattern (a Rust pattern, PAT-1).
        pattern: Box<TermTree>,
        /// The pattern's local binders (BIND-1), in first-occurrence order:
        /// every unqualified single-identifier reference below the pattern's
        /// root and every `name @ ..` alias.
        binders: Vec<syn::Ident>,
    },
    /// One `let pattern = value;` statement of a term block and the rest
    /// of the block: K's `( #let PATTERN = VALUE #in BODY )`, only in
    /// results and conditions. A block's statements nest to the right.
    Let {
        /// The `let` statement's range.
        range: TokenRange,
        /// The pattern (a Rust pattern, PAT-1).
        pattern: Box<TermTree>,
        /// The sort type of `let name: Sort = value;`.
        sort: Option<Path>,
        /// The matched term, outside the pattern's scope.
        value: Box<TermTree>,
        /// The rest of the block: the next `let`, or the result term.
        body: Box<TermTree>,
        /// The pattern's local binders (BIND-1), in first-occurrence order:
        /// every unqualified single-identifier reference, the root included.
        binders: Vec<syn::Ident>,
    },
    /// `|binder: Sort| body`, the one argument of `ml::exists` (KF-039): K's
    /// `#Exists BINDER:Sort . BODY`. The binder is a local binder (BIND-1)
    /// visible only in the body.
    Closure {
        /// The complete closure range.
        range: TokenRange,
        /// The quantified binder.
        binder: syn::Ident,
        /// The binder's authored sort path.
        sort: Path,
        /// The quantified predicate.
        body: Box<TermTree>,
    },
    /// `k::rewrite!(from => to)`: K's local `( FROM => TO )`, only in the
    /// subject of a single-body rule (KF-011). The left side is a pattern;
    /// the right side is a term over the subject's bindings.
    Rewrite {
        /// Complete macro invocation range.
        range: TokenRange,
        /// The left side's range.
        from_range: TokenRange,
        /// The right side's range.
        to_range: TokenRange,
        /// The left side, a pattern.
        from: Box<TermTree>,
        /// The right side; `None` is `()`, K's `.K`, which removes a whole
        /// K-sequence item.
        to: Option<Box<TermTree>>,
    },
}

impl TermTree {
    /// Returns an application node, if this is a call or record application.
    #[must_use]
    pub const fn application(&self) -> Option<&TermApplication> {
        match self {
            Self::Application(application) => Some(application),
            Self::Reference(_)
            | Self::Literal(_)
            | Self::Wildcard(_)
            | Self::IdToken { .. }
            | Self::BytesToken { .. }
            | Self::Anonymous { .. }
            | Self::OrBool { .. }
            | Self::Cell(_)
            | Self::Lexeme { .. }
            | Self::SortTest { .. }
            | Self::As { .. }
            | Self::Or { .. }
            | Self::Matches { .. }
            | Self::Let { .. }
            | Self::Closure { .. }
            | Self::Rewrite { .. } => None,
        }
    }

    /// Returns the bare reference path, if present.
    #[must_use]
    pub const fn reference(&self) -> Option<&Path> {
        match self {
            Self::Reference(path) => Some(path),
            Self::Application(_)
            | Self::Literal(_)
            | Self::Wildcard(_)
            | Self::IdToken { .. }
            | Self::BytesToken { .. }
            | Self::Anonymous { .. }
            | Self::OrBool { .. }
            | Self::Cell(_)
            | Self::Lexeme { .. }
            | Self::SortTest { .. }
            | Self::As { .. }
            | Self::Or { .. }
            | Self::Matches { .. }
            | Self::Let { .. }
            | Self::Closure { .. }
            | Self::Rewrite { .. } => None,
        }
    }

    /// Returns the literal, if present.
    #[must_use]
    pub const fn literal(&self) -> Option<&TermLiteral> {
        match self {
            Self::Literal(literal) => Some(literal),
            Self::Application(_)
            | Self::Reference(_)
            | Self::Wildcard(_)
            | Self::IdToken { .. }
            | Self::BytesToken { .. }
            | Self::Anonymous { .. }
            | Self::OrBool { .. }
            | Self::Cell(_)
            | Self::Lexeme { .. }
            | Self::SortTest { .. }
            | Self::As { .. }
            | Self::Or { .. }
            | Self::Matches { .. }
            | Self::Let { .. }
            | Self::Closure { .. }
            | Self::Rewrite { .. } => None,
        }
    }

    /// Returns the wildcard token range, if this is a native pattern `_`.
    #[must_use]
    pub const fn wildcard_range(&self) -> Option<TokenRange> {
        match self {
            Self::Wildcard(range) => Some(*range),
            Self::Application(_)
            | Self::Reference(_)
            | Self::Literal(_)
            | Self::IdToken { .. }
            | Self::BytesToken { .. }
            | Self::Anonymous { .. }
            | Self::OrBool { .. }
            | Self::Cell(_)
            | Self::Lexeme { .. }
            | Self::SortTest { .. }
            | Self::As { .. }
            | Self::Or { .. }
            | Self::Matches { .. }
            | Self::Let { .. }
            | Self::Closure { .. }
            | Self::Rewrite { .. } => None,
        }
    }

    /// Appends the record field names of the tree to `output`, in the
    /// preorder its sentence keys them in ([`TermKeys::record_field`]).
    pub fn record_field_names_preorder(&self, output: &mut Vec<syn::Ident>) {
        let arguments = match self {
            Self::Application(application) => &application.arguments,
            Self::Cell(cell) => {
                for argument in &cell.fields {
                    output.push(argument.name.clone());
                    argument.value.record_field_names_preorder(output);
                }
                return;
            }
            Self::SortTest { operand, .. } => {
                operand.record_field_names_preorder(output);
                return;
            }
            Self::As { pattern, .. } => {
                pattern.record_field_names_preorder(output);
                return;
            }
            Self::Or { alternatives, .. } => {
                for alternative in alternatives {
                    alternative.record_field_names_preorder(output);
                }
                return;
            }
            Self::Matches {
                subject, pattern, ..
            } => {
                subject.record_field_names_preorder(output);
                pattern.record_field_names_preorder(output);
                return;
            }
            Self::Let {
                pattern,
                value,
                body,
                ..
            } => {
                pattern.record_field_names_preorder(output);
                value.record_field_names_preorder(output);
                body.record_field_names_preorder(output);
                return;
            }
            Self::Closure { body, .. } => {
                body.record_field_names_preorder(output);
                return;
            }
            Self::Rewrite { from, to, .. } => {
                from.record_field_names_preorder(output);
                if let Some(to) = to {
                    to.record_field_names_preorder(output);
                }
                return;
            }
            _ => return,
        };
        match arguments {
            TermArguments::Positional(arguments) => {
                for argument in arguments {
                    argument.record_field_names_preorder(output);
                }
            }
            TermArguments::Named(arguments) => {
                for argument in arguments {
                    output.push(argument.name.clone());
                    argument.value.record_field_names_preorder(output);
                }
            }
        }
    }

    /// Appends the ranges of the tree's `_` to `output`, in the preorder its
    /// sentence keys them in ([`TermKeys::wildcard`]); a `k::matches!` or
    /// `let` pattern's wildcards are nodes of their own and are left out.
    pub fn wildcard_ranges_preorder(&self, output: &mut Vec<TokenRange>) {
        match self {
            Self::Application(application) => match &application.arguments {
                TermArguments::Positional(arguments) => {
                    for argument in arguments {
                        argument.wildcard_ranges_preorder(output);
                    }
                }
                TermArguments::Named(arguments) => {
                    for argument in arguments {
                        argument.value.wildcard_ranges_preorder(output);
                    }
                }
            },
            Self::Wildcard(range) => output.push(*range),
            Self::OrBool { arguments, .. } => {
                for argument in arguments {
                    argument.wildcard_ranges_preorder(output);
                }
            }
            Self::Cell(cell) => {
                for argument in &cell.fields {
                    argument.value.wildcard_ranges_preorder(output);
                }
            }
            Self::SortTest { operand, .. } => operand.wildcard_ranges_preorder(output),
            Self::As { pattern, .. } => pattern.wildcard_ranges_preorder(output),
            Self::Or { alternatives, .. } => {
                for alternative in alternatives {
                    alternative.wildcard_ranges_preorder(output);
                }
            }
            // A `k::matches!` pattern's wildcards are its own
            // (`TermNode::MatchesWildcard`); only its subject is searched.
            Self::Matches { subject, .. } => subject.wildcard_ranges_preorder(output),
            // Likewise a `let` pattern's (`TermNode::LetWildcard`).
            Self::Let { value, body, .. } => {
                value.wildcard_ranges_preorder(output);
                body.wildcard_ranges_preorder(output);
            }
            Self::Closure { body, .. } => body.wildcard_ranges_preorder(output),
            // The right side of a rewrite is a term and has no wildcard.
            Self::Rewrite { from, .. } => from.wildcard_ranges_preorder(output),
            Self::Reference(_)
            | Self::Literal(_)
            | Self::IdToken { .. }
            | Self::BytesToken { .. }
            | Self::Anonymous { .. }
            | Self::Lexeme { .. } => {}
        }
    }
}

/// Role of one path within a term expression.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TermSymbolKind {
    /// Head of a call or record constructor application.
    ApplicationHead,
    /// Bare path whose constructor/reference meaning awaits Rust/KRS resolution.
    Reference,
}

/// One named path retained in deterministic preorder.
#[derive(Clone, Debug)]
pub struct TermSymbol {
    path: Path,
    kind: TermSymbolKind,
}

impl TermSymbol {
    /// Returns the authored path with its original token spans.
    #[must_use]
    pub const fn path(&self) -> &Path {
        &self.path
    }

    /// Returns whether this path is an application head or a bare reference.
    #[must_use]
    pub const fn kind(&self) -> TermSymbolKind {
        self.kind
    }
}

/// A pass over a sentence's terms: each term's nodes with its keys.
pub(crate) type TermVisit<'a> =
    dyn FnMut(&[TermNode], &mut TermKeys) -> Result<(), SyntaxError> + 'a;

/// A pass that keys one kind of island in one term.
pub(crate) type IslandKeys =
    fn(&mut KeyAllocator, &[TermNode], &mut TermKeys) -> Result<(), SyntaxError>;

/// The keys one sentence's keying pass gave the nodes of a term, indexed as
/// the term's own lists.
///
/// A term is keyed by the sentence it stands in, with the roles of its
/// position there: a term parsed alone carries the standalone `term_*` keys,
/// and a sentence that embeds a term re-keys it, so the keys a caller sees are
/// those of the outermost sentence. A slot is empty exactly when that sentence
/// anchors no such node.
///
/// The pass clears a term's keys before it keys the term, and each
/// `allocate_*_keys` helper it calls writes the key it hands out into the slot
/// of the node the key names.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct TermKeys {
    payload: Option<ProvenanceKey>,
    term: Option<ProvenanceKey>,
    symbols: Vec<Option<ProvenanceKey>>,
    nodes: Vec<Vec<ProvenanceKey>>,
    record_fields: Vec<Option<ProvenanceKey>>,
    wildcards: Vec<Option<ProvenanceKey>>,
}

impl TermKeys {
    /// The key of the whole term: its payload, or the item, key, value, result
    /// or condition the enclosing sentence names it as.
    #[must_use]
    pub const fn payload(&self) -> Option<&ProvenanceKey> {
        self.payload.as_ref()
    }

    /// The key of the whole term under the role its sentence gives every term
    /// it holds, beside [`Self::payload`], which then names the term's place
    /// in a `k!` or `map!`: an initializer's `initializer_term`.
    #[must_use]
    pub const fn term(&self) -> Option<&ProvenanceKey> {
        self.term.as_ref()
    }

    /// The key of the path at `index` in [`TermExpression::symbols`] (for a
    /// native rule pattern, in its constructor and binding paths).
    #[must_use]
    pub fn symbol(&self, index: usize) -> Option<&ProvenanceKey> {
        self.symbols.get(index).and_then(Option::as_ref)
    }

    /// Every key the sentence gave the node at `index` in
    /// [`TermExpression::nodes`], in allocation order: an application head's
    /// own key before its turbofish instances', and an island's shell before
    /// its parts. [`Self::node_key`] reads one part by its role.
    #[must_use]
    pub fn node(&self, index: usize) -> &[ProvenanceKey] {
        self.nodes.get(index).map_or(&[], Vec::as_slice)
    }

    /// The key of `role` the sentence gave the node at `index`: which part
    /// of the node the key names (an application head or one of its
    /// turbofish instances, a `let` or its sort, an island's shell or one of
    /// its parts) is the role's to say, not the key's place among the
    /// node's keys.
    #[must_use]
    pub fn node_key(&self, index: usize, role: ProvenanceRole) -> Option<&ProvenanceKey> {
        self.node_keys(index, role).next()
    }

    /// Every key of `role` the sentence gave the node at `index`, in
    /// allocation order: an application head's turbofish instances.
    pub fn node_keys(
        &self,
        index: usize,
        role: ProvenanceRole,
    ) -> impl Iterator<Item = &ProvenanceKey> {
        self.node(index)
            .iter()
            .filter(move |key| key.role() == role)
    }

    /// The key of the record field name at `index` in the term tree's
    /// preorder of record field names.
    #[must_use]
    pub fn record_field(&self, index: usize) -> Option<&ProvenanceKey> {
        self.record_fields.get(index).and_then(Option::as_ref)
    }

    /// The key of the `_` at `index` in the term tree's preorder of
    /// wildcards.
    #[must_use]
    pub fn wildcard(&self, index: usize) -> Option<&ProvenanceKey> {
        self.wildcards.get(index).and_then(Option::as_ref)
    }

    /// Forgets every key, before a sentence's pass keys the term again.
    pub(crate) fn clear(&mut self) {
        *self = Self::default();
    }

    pub(crate) fn set_payload(&mut self, key: ProvenanceKey) {
        debug_assert!(self.payload.is_none(), "a pass keys a term once");
        self.payload = Some(key);
    }

    pub(crate) fn set_term(&mut self, key: ProvenanceKey) {
        debug_assert!(self.term.is_none(), "a pass keys a term once");
        self.term = Some(key);
    }

    pub(crate) fn set_symbol(&mut self, index: usize, key: ProvenanceKey) {
        set_slot(&mut self.symbols, index, key);
    }

    pub(crate) fn push_node(&mut self, index: usize, key: ProvenanceKey) {
        if self.nodes.len() <= index {
            self.nodes.resize_with(index + 1, Vec::new);
        }
        self.nodes[index].push(key);
    }

    pub(crate) fn set_record_field(&mut self, index: usize, key: ProvenanceKey) {
        set_slot(&mut self.record_fields, index, key);
    }

    pub(crate) fn set_wildcard(&mut self, index: usize, key: ProvenanceKey) {
        set_slot(&mut self.wildcards, index, key);
    }
}

fn set_slot(slots: &mut Vec<Option<ProvenanceKey>>, index: usize, key: ProvenanceKey) {
    if slots.len() <= index {
        slots.resize(index + 1, None);
    }
    debug_assert!(slots[index].is_none(), "a pass keys a node once");
    slots[index] = Some(key);
}

#[cfg(test)]
impl TermKeys {
    /// Records the keys of a term's nodes: each path's at the path, each
    /// node's at the part of the node its role names, and each record field
    /// name's and wildcard's at the name or `_` of `tree` in preorder. The
    /// whole term's keys are its sentence's to place.
    ///
    /// A slot past the last node it indexes is a key no node holds, and
    /// fails the walk.
    pub(crate) fn keyed_nodes(
        &self,
        nodes: &mut crate::keyed_nodes::KeyedNodes,
        paths: &[TokenRange],
        term_nodes: &[TermNode],
        tree: &TermTree,
    ) -> Result<(), SyntaxError> {
        assert!(
            self.symbols.len() <= paths.len(),
            "a path key past the paths"
        );
        for (key, range) in self.symbols.iter().zip(paths) {
            nodes.push(key.as_ref(), *range);
        }
        assert!(
            self.nodes.len() <= term_nodes.len(),
            "a node key past the nodes"
        );
        for (node, node_keys) in term_nodes.iter().zip(&self.nodes) {
            let mut instances = 0;
            for key in node_keys {
                let range = node.keyed_range(key.role(), &mut instances)?;
                nodes.push(Some(key), range);
            }
        }
        let mut fields = Vec::new();
        tree.record_field_names_preorder(&mut fields);
        let mut wildcards = Vec::new();
        tree.wildcard_ranges_preorder(&mut wildcards);
        assert!(
            self.record_fields.len() <= fields.len(),
            "a field key past the fields"
        );
        for (key, field) in self.record_fields.iter().zip(&fields) {
            nodes.push_tokens(key.as_ref(), field)?;
        }
        assert!(
            self.wildcards.len() <= wildcards.len(),
            "a wildcard key past the wildcards"
        );
        for (key, range) in self.wildcards.iter().zip(wildcards) {
            nodes.push(key.as_ref(), range);
        }
        Ok(())
    }
}

#[cfg(test)]
impl TermNode {
    /// The part of the node that a key of `role` names: an island's sort,
    /// binder, text, or rewrite side, the `instances`-th turbofish argument
    /// of an application head, or else the node itself.
    fn keyed_range(
        &self,
        role: ProvenanceRole,
        instances: &mut usize,
    ) -> Result<TokenRange, SyntaxError> {
        use ProvenanceRole as Role;
        match (self, role) {
            (
                Self::Let {
                    sort: Some(sort), ..
                },
                Role::LetSort,
            )
            | (Self::Closure { sort, .. }, Role::MlBinderSort)
            | (Self::Lexeme { sort, .. }, Role::LexemeSort)
            | (Self::SortTest { sort, .. }, Role::SortTestSort)
            | (Self::Anonymous { sort, .. }, Role::ClaimAnonymousSort) => {
                TokenRange::for_tokens(sort)
            }
            (Self::Closure { binder, .. }, Role::MlBinder)
            | (
                Self::As {
                    binding: binder, ..
                },
                Role::PatternAsBinding,
            ) => TokenRange::for_tokens(binder),
            (Self::Lexeme { text, .. }, Role::LexemeText) => TokenRange::for_tokens(text),
            (Self::Rewrite { from, .. }, Role::RuleLocalRewriteFrom) => Ok(*from),
            (Self::Rewrite { to, .. }, Role::RuleLocalRewriteTo) => Ok(*to),
            (Self::ApplicationHead(path), Role::ApplicationInstance) => {
                let Some(syn::PathArguments::AngleBracketed(arguments)) =
                    path.segments.last().map(|segment| &segment.arguments)
                else {
                    panic!("an application instance key on a head without a turbofish");
                };
                let argument = &arguments.args[*instances];
                *instances += 1;
                TokenRange::for_tokens(argument)
            }
            _ => self.range(),
        }
    }
}

#[cfg(test)]
impl TermExpression {
    /// The ranges of the term's symbol paths, which its path keys index.
    pub(crate) fn path_ranges(&self) -> Result<Vec<TokenRange>, SyntaxError> {
        self.symbols
            .iter()
            .map(|symbol| TokenRange::for_tokens(&symbol.path))
            .collect()
    }

    /// Records the term's keyed nodes: the whole term's keys at the term,
    /// then its nodes' ([`TermKeys::keyed_nodes`]).
    pub(crate) fn keyed_nodes(
        &self,
        nodes: &mut crate::keyed_nodes::KeyedNodes,
    ) -> Result<(), SyntaxError> {
        if self.keys.payload.is_some() || self.keys.term.is_some() {
            let range = TokenRange::for_tokens(&self.expression)?;
            nodes.push(self.keys.payload(), range);
            nodes.push(self.keys.term(), range);
        }
        self.keyed_parts(nodes)
    }

    /// Records the keys of the term's nodes, without the whole term's.
    pub(crate) fn keyed_parts(
        &self,
        nodes: &mut crate::keyed_nodes::KeyedNodes,
    ) -> Result<(), SyntaxError> {
        self.keys
            .keyed_nodes(nodes, &self.path_ranges()?, &self.nodes, &self.tree)
    }
}

/// A validated Rust-expression term in the deliberately small term grammar.
///
/// Accepted nodes are plain paths, named calls, named record construction,
/// parentheses/groups, and Rust literals below a named root, and the notation
/// forms `a && b`, `a || b`, and `recv.op::<D>(..)`, each of which is the
/// builtin call it denotes. No other operator, method, closure, control-flow,
/// assignment, macro, update-rest, or arbitrary block expression is silently
/// retained.
#[derive(Clone, Debug)]
pub struct TermExpression {
    expression: TermSource,
    root_kind: TermRootKind,
    symbols: Vec<TermSymbol>,
    nodes: Vec<TermNode>,
    tree: TermTree,
    keys: TermKeys,
    /// The anchors of the term's standalone keying, which both provenance
    /// views project.
    anchors: Vec<ProvenanceAnchor>,
}

impl TermExpression {
    /// Validates a previously parsed Rust expression as a term.
    ///
    /// # Errors
    ///
    /// Returns a structured error at the first expression outside the closed
    /// named-term subset.
    pub fn from_expression(expression: Expr) -> Result<Self, SyntaxError> {
        Self::from_expression_context(expression, TermExpressionContext::Expression)
    }

    pub(crate) fn from_pattern_expression(expression: Expr) -> Result<Self, SyntaxError> {
        Self::from_expression_context(expression, TermExpressionContext::Pattern)
    }

    fn from_expression_context(
        mut expression: Expr,
        context: TermExpressionContext,
    ) -> Result<Self, SyntaxError> {
        // Tokens [`parse_term_expression`] read as no expression hold
        // `name @ pattern`: they are read as the pattern they are.
        if let Expr::Verbatim(tokens) = expression {
            return Self::from_aliased_tokens(tokens);
        }
        // A `k::bits!(value, "..")` test is sugar for its `Bool` long form.
        if context == TermExpressionContext::Expression {
            crate::rule::expand_bit_tests(&mut expression)?;
        }
        let root = transparent_expression(&expression);
        let root_kind = match root {
            Expr::Path(path) if float_constant_path(&path.path).is_some() => TermRootKind::Literal,
            Expr::Path(_) => TermRootKind::Named,
            Expr::Call(_) => TermRootKind::Call,
            Expr::Struct(_) => TermRootKind::Record,
            Expr::Lit(literal) if is_supported_literal(literal) => TermRootKind::Literal,
            // `validate_expression` reports the suffix of an Int literal.
            Expr::Lit(literal)
                if matches!(literal.lit, Lit::Int(_)) && literal.attrs.is_empty() =>
            {
                TermRootKind::Literal
            }
            // `a && b`, `a + b`, `!a`, `-a`, and `recv.op::<D>(..)` denote
            // builtin calls.
            other if crate::notation::is_expression_notation(other) => TermRootKind::Call,
            // `[a, ..rest]` denotes one level of list notation, and a term
            // block (K's `#let`) applies a generated function.
            Expr::Array(_) | Expr::Block(_) => TermRootKind::Call,
            // The minus of a literal, which `validate_expression` checks.
            Expr::Unary(ExprUnary {
                op: UnOp::Neg(_), ..
            }) => TermRootKind::Literal,
            Expr::Infer(_) if context == TermExpressionContext::Pattern => TermRootKind::Wildcard,
            // A collection literal denotes the calls that build it.
            Expr::Macro(value)
                if crate::collection_literal::literal_collection(&value.mac.path).is_some() =>
            {
                TermRootKind::Call
            }
            Expr::Macro(value) => special_macro_kind(&value.mac.path)
                .ok_or_else(|| unsupported_root_macro(&value.mac.path, value.span()))?
                .root_kind(),
            other @ (Expr::Cast(_) | Expr::Range(_)) => {
                return Err(
                    rust_only_operator(other).expect("a cast and a range are Rust-only operators")
                );
            }
            other => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::UnsupportedTermExpression {
                        reason: "the root must be a named path/call/record or an Int/Bool literal",
                    },
                    other.span(),
                ));
            }
        };
        let mut symbols = Vec::new();
        let mut nodes = Vec::new();
        let tree = validate_expression(&expression, context, &mut symbols, &mut nodes)?;
        Self {
            expression: TermSource::Expression(expression),
            root_kind,
            symbols,
            nodes,
            tree,
            keys: TermKeys::default(),
            anchors: Vec::new(),
        }
        .keyed_standalone()
    }

    /// Parses and validates a pattern payload (PAT-1): the tokens are a Rust
    /// pattern (`syn::Pat::parse_multi`), which admits `name @ pattern`
    /// (K's `#as`) at any depth below the root. Every term form accepted in
    /// an expression payload has a pattern twin with the same tree, symbols,
    /// nodes, and provenance ranges.
    ///
    /// # Errors
    ///
    /// Returns a structured error at the first pattern outside the closed
    /// named-term subset.
    pub fn parse_pattern_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        Self::parse_pattern_tokens_at(tokens, PatternRoot::Value)
    }

    /// Parses and validates a pattern payload whose root is `root`
    /// ([`PatternRoot`]), as [`Self::parse_pattern_tokens`] does below a
    /// root: a `k::term!` subject's payload is read at the subject's root, as
    /// a native subject is, since the wrapper is optional around a subject
    /// and changes nothing the subject means.
    ///
    /// # Errors
    ///
    /// Returns a structured error at the first pattern outside the closed
    /// named-term subset, or at a construct the root does not admit.
    pub(crate) fn parse_pattern_tokens_at(
        tokens: TokenStream,
        root: PatternRoot,
    ) -> Result<Self, SyntaxError> {
        let signs = crate::rule::NegativeLiteralSpans::scan(tokens.clone());
        match Pat::parse_multi.parse2(tokens.clone()) {
            Ok(pattern) => Self::from_pattern_at(pattern, tokens, signs, root),
            // Tokens that are no Rust pattern but a term expression are the
            // term they denote, a `let` block or an `ml::exists` closure
            // among them, and the position table judges it where it stands.
            // `&&`, `||` and a method call, which no pattern holds, denote a
            // builtin call, and a pattern names its head instead.
            Err(error) => match syn::parse2::<Expr>(tokens) {
                Ok(expression) => {
                    if let Some(error) = crate::notation::notation_in_pattern(&expression) {
                        return Err(error);
                    }
                    Self::from_pattern_expression(expression)
                }
                Err(_) => Err(error.into()),
            },
        }
    }

    /// Parses and validates the key of a map a pattern reads: a pattern, or
    /// else a term expression, notation included. A key is what the map is
    /// looked up by, so a computed key is the value it computes, and
    /// notation there is the builtin call it denotes, as in a readable map
    /// read's key; the position table judges each construct by the reading
    /// the key's construct gives (`crate::positions`, "Keys").
    ///
    /// # Errors
    ///
    /// Returns a structured error at the first term outside the closed
    /// named-term subset.
    pub(crate) fn parse_key_pattern_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        let signs = crate::rule::NegativeLiteralSpans::scan(tokens.clone());
        match Pat::parse_multi.parse2(tokens.clone()) {
            Ok(pattern) => Self::from_pattern_at(pattern, tokens, signs, PatternRoot::Value),
            Err(error) => match syn::parse2::<Expr>(tokens) {
                Ok(expression) => Self::from_pattern_expression(expression),
                Err(_) => Err(error.into()),
            },
        }
    }

    /// Reads tokens that hold `name @ pattern` at a position that builds a
    /// term: no Rust expression holds the alias, so the tokens are read as
    /// the pattern they are, and the position table refuses the alias at its
    /// own tokens, as it refuses every construct its position cannot hold.
    fn from_aliased_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        let signs = crate::rule::NegativeLiteralSpans::scan(tokens.clone());
        let pattern = Pat::parse_multi.parse2(tokens.clone())?;
        Self::from_pattern(pattern, tokens, signs)
    }

    /// Validates a previously parsed Rust pattern as a term pattern; `signs`
    /// holds the `-` and digit spans of its negative literals in token order.
    ///
    /// # Errors
    ///
    /// Returns a structured error at the first pattern outside the closed
    /// named-term subset.
    pub(crate) fn from_pattern(
        pattern: Pat,
        tokens: TokenStream,
        signs: crate::rule::NegativeLiteralSpans,
    ) -> Result<Self, SyntaxError> {
        Self::from_pattern_at(pattern, tokens, signs, PatternRoot::Value)
    }

    /// [`Self::from_pattern`] with the pattern's root read as `root` says.
    fn from_pattern_at(
        pattern: Pat,
        tokens: TokenStream,
        mut signs: crate::rule::NegativeLiteralSpans,
        root: PatternRoot,
    ) -> Result<Self, SyntaxError> {
        // Tokens [`parse_term_pattern`] read as no pattern are a term
        // expression.
        if let Pat::Verbatim(tokens) = pattern {
            return Self::parse_pattern_tokens(tokens);
        }
        let root_kind = pattern_root_kind(&pattern)?;
        let mut symbols = Vec::new();
        let mut nodes = Vec::new();
        let tree = read_pattern(&pattern, root, &mut signs, &mut symbols, &mut nodes)?;
        Self {
            expression: TermSource::Pattern { pattern, tokens },
            root_kind,
            symbols,
            nodes,
            tree,
            keys: TermKeys::default(),
            anchors: Vec::new(),
        }
        .keyed_standalone()
    }

    /// Returns the original span-preserving Rust expression or pattern, as
    /// authored: notation (`&&`, `||`, `recv.op::<D>(..)`) stays notation.
    /// Ranges and spellings derive from it; code emitted for rustc must use
    /// [`Self::denoted_tokens`] instead, which rustc can resolve.
    #[must_use]
    pub const fn expression(&self) -> &TermSource {
        &self.expression
    }

    /// Returns the Rust tokens for code that rustc checks: the authored
    /// expression with each notation form replaced by the builtin call it
    /// denotes, whose head is qualified by `builtin`, the facade's `builtin`
    /// module. A pattern payload, which has no notation, keeps its tokens.
    #[must_use]
    pub fn denoted_tokens(&self, builtin: &Path) -> TokenStream {
        match &self.expression {
            TermSource::Expression(expression) => {
                let mut expression = expression.clone();
                crate::notation::denote_notation(&mut expression, builtin);
                expression.into_token_stream()
            }
            TermSource::Pattern { .. } => self.expression.to_token_stream(),
        }
    }

    /// Returns the syntactic root kind.
    #[must_use]
    pub const fn root_kind(&self) -> TermRootKind {
        self.root_kind
    }

    /// Returns all named paths in deterministic preorder.
    #[must_use]
    pub fn symbols(&self) -> &[TermSymbol] {
        &self.symbols
    }

    /// Returns application heads, references, and literals in deterministic
    /// expression preorder.
    #[must_use]
    pub fn nodes(&self) -> &[TermNode] {
        &self.nodes
    }

    /// Returns the structured argument-preserving term tree.
    #[must_use]
    pub const fn tree(&self) -> &TermTree {
        &self.tree
    }

    /// Returns the token spelling used by the deterministic reference surface.
    #[must_use]
    pub fn spelling(&self) -> String {
        self.expression.to_token_stream().to_string()
    }

    /// Returns the keys the term's sentence gave its nodes.
    #[must_use]
    pub const fn keys(&self) -> &TermKeys {
        &self.keys
    }

    /// The term's nodes with its keys, for a pass that keys them.
    pub(crate) fn keying(&mut self) -> (&[TermNode], &TermTree, &mut TermKeys) {
        (&self.nodes, &self.tree, &mut self.keys)
    }

    /// Forgets the term's keys and the anchors of its standalone keying,
    /// before an enclosing sentence's pass keys it with the roles of its
    /// position: the term then holds that sentence's keys, and its anchors
    /// are that sentence's.
    pub(crate) fn clear_keys(&mut self) {
        self.keys.clear();
        self.anchors.clear();
    }

    /// Keys the term as a sentence of its own: its payload, its paths, its
    /// application head, reference and literal nodes, then its record field
    /// names, under the standalone roles.
    fn keyed_standalone(mut self) -> Result<Self, SyntaxError> {
        let mut keys = KeyAllocator::default();
        self.allocate_keys(
            &mut keys,
            ProvenanceRole::TermPayload,
            ProvenanceRole::TermPath,
        )?;
        self.allocate_node_keys(
            &mut keys,
            ProvenanceRole::TermApplicationHead,
            ProvenanceRole::TermReference,
            ProvenanceRole::TermLiteral,
            ProvenanceRole::TermRecordFieldName,
        )?;
        self.anchors = keys.into_anchors();
        Ok(self)
    }

    /// The standalone anchors of the given roles, in allocation order.
    fn standalone_anchors(&self, roles: &[ProvenanceRole]) -> Vec<ProvenanceAnchor> {
        self.anchors
            .iter()
            .filter(|anchor| roles.contains(&anchor.role()))
            .cloned()
            .collect()
    }

    /// Returns standalone term-payload provenance anchors: the payload and
    /// the paths of the term's standalone keying.
    ///
    /// # Errors
    ///
    /// None: the term was keyed when it was parsed.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.standalone_anchors(&[ProvenanceRole::TermPayload, ProvenanceRole::TermPath]))
    }

    /// Returns payload plus typed application/reference/literal anchors for
    /// protocol-v6 lowering: the payload, nodes and record field names of the
    /// term's standalone keying. The compact path catalog remains available
    /// via [`Self::provenance`].
    ///
    /// # Errors
    ///
    /// None: the term was keyed when it was parsed.
    pub fn full_provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.standalone_anchors(&[
            ProvenanceRole::TermPayload,
            ProvenanceRole::TermApplicationHead,
            ProvenanceRole::TermReference,
            ProvenanceRole::TermLiteral,
            ProvenanceRole::TermRecordFieldName,
        ]))
    }

    /// Keys each application head, reference, and literal node in preorder,
    /// then each record field name.
    pub(crate) fn allocate_node_keys(
        &mut self,
        keys: &mut KeyAllocator,
        application_role: ProvenanceRole,
        reference_role: ProvenanceRole,
        literal_role: ProvenanceRole,
        record_field_role: ProvenanceRole,
    ) -> Result<(), SyntaxError> {
        for (index, node) in self.nodes.iter().enumerate() {
            let role = match node {
                TermNode::ApplicationHead(_) => application_role,
                TermNode::Reference(_) => reference_role,
                TermNode::Literal(_) => literal_role,
                TermNode::IdToken(_)
                | TermNode::BytesToken(_)
                | TermNode::Anonymous { .. }
                | TermNode::OrBool(_)
                | TermNode::Lexeme { .. }
                | TermNode::SortTest { .. }
                | TermNode::As { .. }
                | TermNode::Or(_)
                | TermNode::Matches(_)
                | TermNode::MatchesWildcard(_)
                | TermNode::Let { .. }
                | TermNode::Closure { .. }
                | TermNode::LetWildcard(_)
                | TermNode::Rewrite { .. } => {
                    continue;
                }
            };
            self.keys.push_node(index, keys.key(role, node.range()?)?);
        }
        allocate_record_field_keys(keys, &self.tree, &mut self.keys, record_field_role)
    }

    /// Keys the payload, then each symbol path in preorder.
    pub(crate) fn allocate_keys(
        &mut self,
        keys: &mut KeyAllocator,
        payload_role: ProvenanceRole,
        path_role: ProvenanceRole,
    ) -> Result<(), SyntaxError> {
        self.allocate_payload_key(keys, payload_role)?;
        self.allocate_symbol_keys(keys, path_role)
    }

    /// Keys the whole term as the next of `role`.
    pub(crate) fn allocate_payload_key(
        &mut self,
        keys: &mut KeyAllocator,
        role: ProvenanceRole,
    ) -> Result<(), SyntaxError> {
        self.keys
            .set_payload(keys.key(role, TokenRange::for_tokens(&self.expression)?)?);
        Ok(())
    }

    /// Keys each symbol path in preorder, as the next of `role`.
    pub(crate) fn allocate_symbol_keys(
        &mut self,
        keys: &mut KeyAllocator,
        role: ProvenanceRole,
    ) -> Result<(), SyntaxError> {
        for (index, symbol) in self.symbols.iter().enumerate() {
            self.keys.set_symbol(
                index,
                keys.key(role, TokenRange::for_tokens(&symbol.path)?)?,
            );
        }
        Ok(())
    }
}

/// The authored Rust syntax of a term payload: an expression in results and
/// conditions, a pattern in pattern payloads (PAT-1).
#[derive(Clone, Debug)]
pub enum TermSource {
    /// A result, condition, or initializer expression.
    Expression(Expr),
    /// A pattern payload, with its authored tokens: syn folds a negative
    /// literal pattern into one token, while ranges and spelling keep the
    /// authored `-` and digits.
    Pattern {
        /// The parsed pattern.
        pattern: Pat,
        /// The authored tokens.
        tokens: TokenStream,
    },
}

impl TermSource {
    /// Returns the expression, or `None` for a pattern payload.
    #[must_use]
    pub const fn as_expression(&self) -> Option<&Expr> {
        match self {
            Self::Expression(expression) => Some(expression),
            Self::Pattern { .. } => None,
        }
    }

    /// Returns the parsed pattern, or `None` for an expression.
    #[must_use]
    pub const fn as_pattern(&self) -> Option<&Pat> {
        match self {
            Self::Pattern { pattern, .. } => Some(pattern),
            Self::Expression(_) => None,
        }
    }
}

impl ToTokens for TermSource {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            Self::Expression(expression) => expression.to_tokens(tokens),
            Self::Pattern {
                tokens: authored, ..
            } => authored.to_tokens(tokens),
        }
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum TermExpressionContext {
    Pattern,
    Expression,
}

impl KrsSyntax for TermExpression {
    /// Parses a term at a position that builds one: an expression, or tokens
    /// that hold `name @ pattern` ([`parse_term_expression`]).
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        let expression = parse_term_expression.parse2(tokens)?;
        Self::from_expression(expression)
    }
}

/// Reads one term at a position that builds a term (a result, a condition, a
/// value): a Rust expression, or, when the tokens are no expression but a
/// pattern that holds `name @ pattern`, those tokens as [`Expr::Verbatim`],
/// which [`TermExpression::from_expression`] reads as the pattern they are.
/// A pattern alias is a construct like any other, so its position decides
/// it, not the expression grammar.
///
/// # Errors
///
/// The expression's parse error, when the tokens are neither.
pub(crate) fn parse_term_expression(input: syn::parse::ParseStream<'_>) -> syn::Result<Expr> {
    use syn::parse::discouraged::Speculative as _;
    let expression = input.fork();
    let error = match expression.parse::<Expr>() {
        // An expression stops before the `@` of an alias at its root.
        Ok(parsed) if !expression.peek(syn::Token![@]) => {
            input.advance_to(&expression);
            return Ok(parsed);
        }
        Ok(_) => expression.error("unexpected token"),
        Err(error) => error,
    };
    let pattern = input.fork();
    let start = pattern.cursor();
    if pattern.call(Pat::parse_multi).is_ok() {
        let tokens = tokens_between(start, pattern.cursor());
        if find_pattern_alias(&tokens).is_some() {
            input.advance_to(&pattern);
            return Ok(Expr::Verbatim(tokens));
        }
    }
    Err(error)
}

/// Reads one term at a position that matches terms (a subject): a Rust
/// pattern, or, when the tokens are no pattern but a term expression (a
/// `let` block, an `ml::exists` closure), those tokens as [`Pat::Verbatim`],
/// which the pattern readers read as the term they denote, so that the
/// position table judges the construct where it stands.
///
/// # Errors
///
/// The pattern's parse error, when the tokens are neither.
pub(crate) fn parse_term_pattern(input: syn::parse::ParseStream<'_>) -> syn::Result<Pat> {
    use syn::parse::discouraged::Speculative as _;
    let pattern = input.fork();
    let start = pattern.cursor();
    let error = match pattern.call(Pat::parse_multi) {
        // A pattern followed by `[` or `.` (but `..`) is the receiver of an
        // index or a method call, a term no pattern spells: the tokens are
        // read as the expression they continue into.
        Ok(_)
            if pattern.peek(syn::token::Bracket)
                || (pattern.peek(syn::Token![.]) && !pattern.peek(syn::Token![..])) =>
        {
            pattern.error("a pattern continues into an index or a method call")
        }
        // syn reports the tokens a pattern leaves inside a group (`..base` in
        // a record) only when the whole parse ends: the pattern's own tokens,
        // read alone, report them here, where the term reading is still open.
        Ok(parsed) => match Pat::parse_multi.parse2(tokens_between(start, pattern.cursor())) {
            Ok(_) => {
                input.advance_to(&pattern);
                return Ok(parsed);
            }
            Err(error) => error,
        },
        Err(error) => error,
    };
    let expression = input.fork();
    let start = expression.cursor();
    if expression.parse::<Expr>().is_ok() {
        let tokens = tokens_between(start, expression.cursor());
        input.advance_to(&expression);
        return Ok(Pat::Verbatim(tokens));
    }
    Err(error)
}

/// The tokens from `start` up to `end`.
pub(crate) fn tokens_between(
    start: syn::buffer::Cursor<'_>,
    end: syn::buffer::Cursor<'_>,
) -> TokenStream {
    let mut tokens = TokenStream::new();
    let mut cursor = start;
    while cursor != end {
        let Some((token, next)) = cursor.token_tree() else {
            break;
        };
        tokens.extend([token]);
        cursor = next;
    }
    tokens
}

/// Parses the `fn` item in `tokens`. A body that holds `name @ pattern`,
/// which no Rust block holds, is read as one term with the pattern grammar
/// ([`parse_term_expression`]), so that the position table refuses the alias
/// in the result, at its own tokens.
///
/// # Errors
///
/// Rust syntax errors.
pub fn parse_fn_item(tokens: TokenStream) -> Result<syn::ItemFn, SyntaxError> {
    let mut tokens = tokens.into_iter().collect::<Vec<_>>();
    let body = match tokens.last_mut() {
        Some(proc_macro2::TokenTree::Group(group))
            if group.delimiter() == proc_macro2::Delimiter::Brace
                && find_pattern_alias(&group.stream()).is_some() =>
        {
            let body = group.stream();
            let mut empty =
                proc_macro2::Group::new(proc_macro2::Delimiter::Brace, TokenStream::new());
            empty.set_span(group.span());
            *group = empty;
            Some(body)
        }
        _ => None,
    };
    let mut item = syn::parse2::<syn::ItemFn>(tokens.into_iter().collect())?;
    if let Some(body) = body {
        let result = parse_term_expression.parse2(body)?;
        item.block.stmts = vec![syn::Stmt::Expr(result, None)];
    }
    Ok(item)
}

pub(crate) fn find_pattern_alias(tokens: &TokenStream) -> Option<Span> {
    let tokens = tokens.clone().into_iter().collect::<Vec<_>>();
    // A `let` statement's pattern (KF-032) is checked by the term-block
    // validator, which explains why it cannot alias.
    let mut in_let_pattern = false;
    for (index, token) in tokens.iter().enumerate() {
        match token {
            proc_macro2::TokenTree::Ident(ident) if ident == "let" => in_let_pattern = true,
            proc_macro2::TokenTree::Punct(punct)
                if in_let_pattern
                    && (punct.as_char() == ';'
                        || (punct.as_char() == '='
                            && punct.spacing() == proc_macro2::Spacing::Alone)) =>
            {
                in_let_pattern = false;
            }
            _ if in_let_pattern => {}
            // `name @ ..` is a remainder, which its own parser reports.
            proc_macro2::TokenTree::Punct(punct)
                if punct.as_char() == '@'
                    && !matches!(
                        tokens.get(index + 1),
                        Some(proc_macro2::TokenTree::Punct(dot)) if dot.as_char() == '.'
                    ) =>
            {
                return Some(punct.span());
            }
            proc_macro2::TokenTree::Group(group) => {
                let after_macro = index > 0
                    && matches!(&tokens[index - 1], proc_macro2::TokenTree::Punct(bang) if bang.as_char() == '!');
                if !after_macro && let Some(span) = find_pattern_alias(&group.stream()) {
                    return Some(span);
                }
            }
            _ => {}
        }
    }
    None
}

fn pattern_root_kind(pattern: &Pat) -> Result<TermRootKind, SyntaxError> {
    Ok(match pattern {
        Pat::Paren(paren) => return pattern_root_kind(&paren.pat),
        Pat::Ident(PatIdent {
            subpat: Some((_, subpattern)),
            ..
        }) => return pattern_root_kind(subpattern),
        Pat::Path(path) if float_constant_path(&path.path).is_some() => TermRootKind::Literal,
        Pat::Path(_) | Pat::Ident(_) => TermRootKind::Named,
        Pat::TupleStruct(_) | Pat::Slice(_) => TermRootKind::Call,
        Pat::Struct(_) => TermRootKind::Record,
        Pat::Lit(_) => TermRootKind::Literal,
        Pat::Wild(_) => TermRootKind::Wildcard,
        Pat::Or(or) => match or.cases.first() {
            Some(first) => return pattern_root_kind(first),
            None => return Err(unsupported_pattern_form(pattern)),
        },
        Pat::Macro(value)
            if crate::collection_literal::literal_collection(&value.mac.path).is_some() =>
        {
            TermRootKind::Call
        }
        Pat::Macro(value) => special_macro_kind(&value.mac.path)
            .ok_or_else(|| unsupported_root_macro(&value.mac.path, value.span()))?
            .root_kind(),
        other => {
            return Err(unsupported_pattern_form(other));
        }
    })
}

fn unsupported_pattern_form(pattern: &Pat) -> SyntaxError {
    let reason = match pattern {
        Pat::Rest(_) => {
            "a `..` remainder binds only inside a sequence, collection or cells! pattern"
        }
        _ => {
            "expected paths, named calls/records, parentheses, `name @ pattern`, `A | B`, `_`, or literal arguments"
        }
    };
    SyntaxError::new(
        SyntaxErrorKind::UnsupportedTermExpression { reason },
        pattern.span(),
    )
}

fn pattern_as_error(reason: String, span: Span) -> SyntaxError {
    SyntaxError::new(SyntaxErrorKind::InvalidPatternAs { reason }, span)
}

/// Validates `name @ subpattern` (K's `#as`, KF-029): the alias is an
/// unadorned binder that does not occur inside its own subpattern, and the
/// subpattern is a term, not a `..` remainder. The alias node precedes the
/// subpattern's nodes, so it counts first in binder order.
pub(crate) fn validate_pattern_as(
    identifier: &PatIdent,
    subpattern: &Pat,
    nodes: &mut Vec<TermNode>,
    validate: impl FnOnce(&Pat, &mut Vec<TermNode>) -> Result<TermTree, SyntaxError>,
) -> Result<TermTree, SyntaxError> {
    let name = &identifier.ident;
    if let Some(by_ref) = &identifier.by_ref {
        return Err(pattern_as_error(
            format!("`ref {name} @ pattern`: K's #as binds the matched term itself; remove `ref`"),
            by_ref.span(),
        ));
    }
    if let Some(mutability) = &identifier.mutability {
        return Err(pattern_as_error(
            format!("`mut {name} @ pattern`: K binders are immutable; remove `mut`"),
            mutability.span(),
        ));
    }
    if !identifier.attrs.is_empty() {
        return Err(pattern_as_error(
            "pattern attributes are not supported on `name @ pattern`".to_owned(),
            identifier.span(),
        ));
    }
    if matches!(subpattern, Pat::Rest(_)) {
        return Err(pattern_as_error(
            format!(
                "`{name} @ ..`: a `..` remainder binds only inside a sequence, collection or cells! pattern"
            ),
            identifier.span(),
        ));
    }
    crate::parse::validate_authored_binder(&name.to_string(), name.span())?;
    let index = nodes.len();
    nodes.push(TermNode::As {
        binding: name.clone(),
        range: TokenRange::for_tokens(identifier)?,
    });
    let pattern = validate(subpattern, nodes)?;
    if let Some(last) = trailing_negative_literal_end(subpattern, &nodes[index + 1..])
        && let TermNode::As { range, .. } = &mut nodes[index]
    {
        *range = TokenRange::new(range.first(), last);
    }
    for node in &nodes[index + 1..] {
        let inner = match node {
            TermNode::Reference(path) => path.get_ident(),
            TermNode::As { binding, .. } => Some(binding),
            _ => None,
        };
        if let Some(inner) = inner
            && inner == name
        {
            return Err(pattern_as_error(
                format!(
                    "identifier `{name}` is bound more than once in the same pattern: an alias cannot occur inside its own subpattern (E0416)"
                ),
                inner.span(),
            ));
        }
    }
    Ok(TermTree::As {
        binding: name.clone(),
        pattern: Box::new(pattern),
    })
}

/// Where a pattern that ends with a negative literal ends: at the literal's
/// digits. syn joins `-1` into one token whose span, in a compiler host,
/// covers only the `-`, so the span of the pattern's last token ends early
/// there; the literal's validated range carries the scanned digit span.
fn trailing_negative_literal_end(pattern: &Pat, nodes: &[TermNode]) -> Option<Span> {
    fn ends_negative(pattern: &Pat) -> bool {
        match pattern {
            Pat::Lit(literal) => literal.lit.to_token_stream().to_string().starts_with('-'),
            Pat::Or(or) => or.cases.last().is_some_and(ends_negative),
            Pat::Ident(identifier) => identifier
                .subpat
                .as_ref()
                .is_some_and(|(_, subpattern)| ends_negative(subpattern)),
            _ => false,
        }
    }
    if !ends_negative(pattern) {
        return None;
    }
    nodes.iter().rev().find_map(|node| match node {
        TermNode::Literal(literal) => literal.range().ok().map(TokenRange::last),
        _ => None,
    })
}

fn pattern_or_error(reason: String, span: Span) -> SyntaxError {
    SyntaxError::new(SyntaxErrorKind::InvalidPatternOr { reason }, span)
}

/// The reason given for `|` next to a `..` remainder.
pub(crate) const PATTERN_OR_REMAINDER: &str = "or-patterns combine terms, not remainders";

/// Validates `A | B | ..` (K's `#Or`, KF-030): every alternative is a term,
/// not a `..` remainder, and every alternative binds the same names (rustc's
/// E0408). The shell node precedes the alternatives' nodes. `validate`
/// checks one alternative and returns its tree and the names it binds; the
/// result carries the names the whole pattern binds, in first-appearance
/// order.
///
/// # Errors
///
/// Returns [`SyntaxErrorKind::InvalidPatternOr`] for a remainder alternative
/// or a name not bound in every alternative, or the first error of an
/// alternative.
pub(crate) fn validate_pattern_or(
    or: &PatOr,
    nodes: &mut Vec<TermNode>,
    mut validate: impl FnMut(
        &Pat,
        &mut Vec<TermNode>,
    ) -> Result<(TermTree, Vec<syn::Ident>), SyntaxError>,
) -> Result<(TermTree, Vec<syn::Ident>), SyntaxError> {
    reject_attributes(&or.attrs, or.span())?;
    let range = TokenRange::for_tokens(or)?;
    let index = nodes.len();
    nodes.push(TermNode::Or(range));
    let mut trees = Vec::with_capacity(or.cases.len());
    let mut bound = Vec::with_capacity(or.cases.len());
    let mut names: Vec<syn::Ident> = Vec::new();
    for case in &or.cases {
        let remainder = match case {
            Pat::Rest(_) => true,
            Pat::Ident(PatIdent {
                subpat: Some((_, subpattern)),
                ..
            }) => matches!(subpattern.as_ref(), Pat::Rest(_)),
            _ => false,
        };
        if remainder {
            return Err(pattern_or_error(
                PATTERN_OR_REMAINDER.to_owned(),
                case.span(),
            ));
        }
        let (tree, case_names) = validate(case, nodes)?;
        trees.push(tree);
        let mut spellings = std::collections::BTreeSet::new();
        for name in case_names {
            let spelling = syn::ext::IdentExt::unraw(&name).to_string();
            if !names
                .iter()
                .any(|known| syn::ext::IdentExt::unraw(known) == spelling)
            {
                names.push(name);
            }
            spellings.insert(spelling);
        }
        bound.push(spellings);
    }
    if let Some(last) = or
        .cases
        .last()
        .and_then(|case| trailing_negative_literal_end(case, &nodes[index + 1..]))
    {
        nodes[index] = TermNode::Or(TokenRange::new(range.first(), last));
    }
    for name in &names {
        let spelling = syn::ext::IdentExt::unraw(name).to_string();
        if let Some((case, _)) = or
            .cases
            .iter()
            .zip(&bound)
            .find(|(_, spellings)| !spellings.contains(&spelling))
        {
            return Err(pattern_or_error(
                format!("variable `{spelling}` is not bound in all alternatives"),
                case.span(),
            ));
        }
    }
    let alternatives = AtLeastTwo::try_from(trees).map_err(|_| {
        pattern_or_error(
            "an or-pattern needs at least two alternatives".to_owned(),
            or.span(),
        )
    })?;
    Ok((
        TermTree::Or {
            range,
            alternatives,
        },
        names,
    ))
}

/// The pattern twin of [`validate_expression`] in pattern context, below a
/// subject's root.
fn validate_pattern(
    pattern: &Pat,
    signs: &mut crate::rule::NegativeLiteralSpans,
    symbols: &mut Vec<TermSymbol>,
    nodes: &mut Vec<TermNode>,
) -> Result<TermTree, SyntaxError> {
    read_pattern(pattern, PatternRoot::Value, signs, symbols, nodes)
}

/// Whether `pattern` at a `for Sort` clause's root stands for the whole term
/// rather than naming the constructor the clause matches: a bare name, `_`,
/// an alias or an island ([`PatternRoot::at`]), parenthesized or not, since
/// parentheses denote nothing.
pub(crate) fn holds_whole_term(pattern: &Pat) -> bool {
    match pattern {
        Pat::Paren(paren) => holds_whole_term(&paren.pat),
        _ => matches!(pattern, Pat::Ident(_) | Pat::Macro(_) | Pat::Wild(_)),
    }
}

/// Reads a pattern of the term grammar: the one pattern reader, for a
/// `k::term!` payload, a native rule subject, a readable value, and a
/// `k::matches!`, `let` or rewrite pattern. `root` is what the pattern's root
/// is ([`PatternRoot`]); everything below it reads at [`PatternRoot::Value`].
/// Every construct builds its node wherever it stands; the position table
/// judges where it may.
#[expect(
    clippy::too_many_lines,
    reason = "One match over syn's closed pattern variants."
)]
pub(crate) fn read_pattern(
    pattern: &Pat,
    root: PatternRoot,
    signs: &mut crate::rule::NegativeLiteralSpans,
    symbols: &mut Vec<TermSymbol>,
    nodes: &mut Vec<TermNode>,
) -> Result<TermTree, SyntaxError> {
    let root = root.at(holds_whole_term(pattern));
    match pattern {
        Pat::Ident(identifier) => {
            if let Some((_, subpattern)) = &identifier.subpat {
                if !root.admits(RootConstruct::As) {
                    let name = &identifier.ident;
                    return Err(pattern_as_error(
                        format!(
                            "`{name} @ pattern` cannot alias a whole rule subject: its root is the matched constructor or function; alias a subterm instead"
                        ),
                        name.span(),
                    )
                    .for_whole_subject());
                }
                return validate_pattern_as(identifier, subpattern, nodes, |subpattern, nodes| {
                    validate_pattern(subpattern, signs, symbols, nodes)
                });
            }
            let adorned = identifier.by_ref.is_some() || identifier.mutability.is_some();
            if root.names_constructor() && (adorned || !identifier.attrs.is_empty()) {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::UnsupportedRulePattern {
                        reason: "a unit constructor subject must be one unadorned Rust identifier",
                    },
                    identifier.span(),
                ));
            }
            reject_attributes(&identifier.attrs, identifier.span())?;
            if adorned {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::UnsupportedTermExpression {
                        reason: "`ref` and `mut` bindings are not term patterns",
                    },
                    identifier.span(),
                ));
            }
            let path = Path::from(identifier.ident.clone());
            symbols.push(TermSymbol {
                path: path.clone(),
                kind: TermSymbolKind::Reference,
            });
            nodes.push(TermNode::Reference(path.clone()));
            Ok(TermTree::Reference(path))
        }
        Pat::Path(path) => validate_path_expression(path, symbols, nodes),
        Pat::TupleStruct(tuple) => validate_tuple_struct_pattern(tuple, signs, symbols, nodes),
        Pat::Slice(slice) => {
            let (head, elements) = crate::list_notation::pattern_level(slice)?;
            symbols.push(TermSymbol {
                path: head.clone(),
                kind: TermSymbolKind::ApplicationHead,
            });
            nodes.push(TermNode::ApplicationHead(head.clone()));
            let mut arguments = Vec::with_capacity(elements.len());
            for element in &elements {
                arguments.push(validate_pattern(element, signs, symbols, nodes)?);
            }
            Ok(TermTree::Application(TermApplication {
                head,
                arguments: TermArguments::Positional(arguments),
                instance: Vec::new(),
                notation: true,
                update: None,
                open: false,
            }))
        }
        Pat::Struct(record) => validate_struct_pattern(record, signs, symbols, nodes),
        Pat::Paren(paren) => {
            reject_attributes(&paren.attrs, paren.span())?;
            read_pattern(&paren.pat, root, signs, symbols, nodes)
        }
        // At a subject's root, each alternative is a whole subject.
        Pat::Or(or) => {
            let (tree, _) = validate_pattern_or(or, nodes, |alternative, nodes| {
                let tree = read_pattern(alternative, root, signs, symbols, nodes)?;
                let names = pattern_tree_binders(&tree, root.names_constructor());
                Ok((tree, names))
            })?;
            Ok(tree)
        }
        Pat::Lit(literal) => {
            let literal = crate::rule::validate_pattern_literal(literal, nodes, signs)?;
            Ok(TermTree::Literal(literal))
        }
        Pat::Wild(wildcard) if root.admits(RootConstruct::Wildcard) => {
            reject_attributes(&wildcard.attrs, wildcard.span())?;
            Ok(TermTree::Wildcard(TokenRange::for_tokens(wildcard)?))
        }
        // A collection literal is the calls it denotes, a pattern holds it
        // as it holds them, and the root reads it as it reads them.
        Pat::Macro(value)
            if crate::collection_literal::literal_collection(&value.mac.path).is_some() =>
        {
            signs.skip(crate::rule::NegativeLiteralSpans::scan(value.mac.tokens.clone()).len());
            validate_expression(
                &Expr::Macro(value.clone()),
                TermExpressionContext::Pattern,
                symbols,
                nodes,
            )
        }
        Pat::Macro(value) if !root.admits(RootConstruct::Island) => {
            Err(subject_root_macro(&value.mac.path))
        }
        Pat::Macro(value)
            if matches!(
                special_macro_kind(&value.mac.path),
                Some(TermMacroKind::Fragment)
            ) =>
        {
            validate_cell_pattern(value, signs, symbols, nodes)
        }
        // Every other island parses its own tokens: their negative literals
        // leave the enclosing pattern's queue.
        Pat::Macro(value) => {
            signs.skip(crate::rule::NegativeLiteralSpans::scan(value.mac.tokens.clone()).len());
            if matches!(
                special_macro_kind(&value.mac.path),
                Some(TermMacroKind::Rewrite)
            ) {
                reject_attributes(&value.attrs, value.span())?;
                return validate_rewrite(value, symbols, nodes);
            }
            validate_special_macro(value, TermExpressionContext::Pattern, symbols, nodes)
        }
        // Tokens that are no Rust pattern but a term expression
        // ([`parse_term_pattern`]) build the tree they denote.
        Pat::Verbatim(tokens) => {
            signs.skip(crate::rule::NegativeLiteralSpans::scan(tokens.clone()).len());
            let term = TermExpression::parse_pattern_tokens(tokens.clone())?;
            symbols.extend(term.symbols);
            nodes.extend(term.nodes);
            Ok(term.tree)
        }
        Pat::Wild(_) => Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedRulePattern {
                reason: "a rule subject's root is the constructor or function the rule matches, so `_` stands only below it",
            },
            pattern.span(),
        )
        .for_whole_subject()),
        other => Err(unsupported_pattern_form(other)),
    }
}

/// The error for a macro at the root of a rule's subject. A compiler-owned
/// island stands below the root, which is the constructor or function the
/// rule matches; any other macro is not a pattern.
fn subject_root_macro(path: &Path) -> SyntaxError {
    if is_rewrite_macro(path) {
        SyntaxError::new(
            SyntaxErrorKind::UnsupportedRulePattern {
                reason: "a whole-subject `k::rewrite!(from => to)` is an ordinary rule: write `from` as the subject and `to` as the result, or mark the change below the subject's root",
            },
            path.span(),
        )
    } else if is_island_macro(path) {
        SyntaxError::new(
            SyntaxErrorKind::UnsupportedRulePattern {
                reason: "a rule subject's root is the constructor or function the rule matches, so a compiler-owned island stands below it, as in `F(k::fragment![Group { .. }])` or `F(k::bytes!(b\"..\"))`",
            },
            path.span(),
        )
        .for_whole_subject()
    } else {
        unexpected_macro(path)
    }
}

fn validate_tuple_struct_pattern(
    tuple: &PatTupleStruct,
    signs: &mut crate::rule::NegativeLiteralSpans,
    symbols: &mut Vec<TermSymbol>,
    nodes: &mut Vec<TermNode>,
) -> Result<TermTree, SyntaxError> {
    reject_attributes(&tuple.attrs, tuple.span())?;
    if tuple.qself.is_some() || !is_head_path(&tuple.path) {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedPath,
            tuple.path.span(),
        ));
    }
    let (head, instance) = application_head(&tuple.path)?;
    symbols.push(TermSymbol {
        path: tuple.path.clone(),
        kind: TermSymbolKind::ApplicationHead,
    });
    nodes.push(TermNode::ApplicationHead(tuple.path.clone()));
    let mut arguments = Vec::with_capacity(tuple.elems.len());
    for element in &tuple.elems {
        arguments.push(validate_pattern(element, signs, symbols, nodes)?);
    }
    Ok(TermTree::Application(TermApplication {
        head,
        arguments: TermArguments::Positional(arguments),
        instance,
        notation: false,
        update: None,
        open: false,
    }))
}

fn validate_struct_pattern(
    record: &PatStruct,
    signs: &mut crate::rule::NegativeLiteralSpans,
    symbols: &mut Vec<TermSymbol>,
    nodes: &mut Vec<TermNode>,
) -> Result<TermTree, SyntaxError> {
    reject_attributes(&record.attrs, record.span())?;
    if record.qself.is_some() || !is_head_path(&record.path) {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedPath,
            record.path.span(),
        ));
    }
    let (head, instance) = application_head(&record.path)?;
    if let Some(rest) = &record.rest {
        reject_attributes(&rest.attrs, rest.span())?;
    }
    let open = record.rest.is_some();
    symbols.push(TermSymbol {
        path: record.path.clone(),
        kind: TermSymbolKind::ApplicationHead,
    });
    nodes.push(TermNode::ApplicationHead(record.path.clone()));
    let arguments = validate_field_patterns(
        record,
        "record terms require unadorned named fields",
        signs,
        symbols,
        nodes,
    )?;
    Ok(TermTree::Application(TermApplication {
        head,
        arguments: TermArguments::Named(arguments),
        instance,
        notation: false,
        update: None,
        open,
    }))
}

fn validate_field_patterns(
    record: &PatStruct,
    reason: &'static str,
    signs: &mut crate::rule::NegativeLiteralSpans,
    symbols: &mut Vec<TermSymbol>,
    nodes: &mut Vec<TermNode>,
) -> Result<Vec<TermNamedArgument>, SyntaxError> {
    let mut arguments = Vec::with_capacity(record.fields.len());
    for field in &record.fields {
        let Member::Named(name) = &field.member else {
            return Err(SyntaxError::new(
                SyntaxErrorKind::UnsupportedTermExpression { reason },
                field.span(),
            ));
        };
        if !field.attrs.is_empty() {
            return Err(SyntaxError::new(
                SyntaxErrorKind::UnsupportedTermExpression { reason },
                field.span(),
            ));
        }
        arguments.push(TermNamedArgument {
            name: name.clone(),
            value: validate_pattern(&field.pat, signs, symbols, nodes)?,
        });
    }
    Ok(arguments)
}

/// The error for `as` and a range, Rust operators that no builtin operation
/// stands behind, or `None` for any other expression.
fn rust_only_operator(expression: &Expr) -> Option<SyntaxError> {
    let (reason, span) = match expression {
        Expr::Cast(cast) => (
            "`as` converts Rust values, and no term operator does; convert with a builtin call such as `float::from_int(..)` or `string::from_int(..)`",
            cast.as_token.span,
        ),
        Expr::Range(range) => (
            "a range is not a term; `..` belongs only in a pattern, after the items it matches",
            range.limits.span(),
        ),
        _ => return None,
    };
    Some(SyntaxError::new(
        SyntaxErrorKind::InvalidExpressionNotation {
            reason: reason.to_owned(),
        },
        span,
    ))
}

fn validate_expression(
    expression: &Expr,
    context: TermExpressionContext,
    symbols: &mut Vec<TermSymbol>,
    nodes: &mut Vec<TermNode>,
) -> Result<TermTree, SyntaxError> {
    // A notation form is the builtin application it denotes.
    if let Some(call) = crate::notation::denoted_call(expression)? {
        return validate_call(&call, true, context, symbols, nodes);
    }
    match expression {
        Expr::Path(path) => validate_path_expression(path, symbols, nodes),
        Expr::Call(call) => validate_call(call, false, context, symbols, nodes),
        Expr::Struct(record) => validate_record(record, context, symbols, nodes),
        Expr::Paren(ExprParen { attrs, expr, .. }) | Expr::Group(ExprGroup { attrs, expr, .. }) => {
            reject_attributes(attrs, expression.span())?;
            validate_expression(expr, context, symbols, nodes)
        }
        Expr::Lit(literal) => validate_literal(literal, nodes),
        Expr::Unary(unary) if matches!(unary.op, UnOp::Neg(_)) => {
            let literal = match negative_float(unary)? {
                Some(float) => TermLiteral::Float(float),
                None => TermLiteral::Integer(negative_integer(unary)?),
            };
            nodes.push(TermNode::Literal(literal.clone()));
            Ok(TermTree::Literal(literal))
        }
        Expr::Infer(infer) if context == TermExpressionContext::Pattern => {
            reject_attributes(&infer.attrs, infer.span())?;
            Ok(TermTree::Wildcard(TokenRange::for_tokens(infer)?))
        }
        Expr::Macro(value) => validate_special_macro(value, context, symbols, nodes),
        Expr::Block(block) => validate_let_block(block, symbols, nodes),
        // A closure is only the one argument of `ml::exists` (KF-039),
        // which `validate_call` admits.
        Expr::Closure(closure) => Err(ml_exists_error(
            CLOSURE_OUTSIDE_EXISTS.to_owned(),
            closure.span(),
        )),
        Expr::Cast(_) | Expr::Range(_) => {
            Err(rust_only_operator(expression).expect("a cast and a range are Rust-only operators"))
        }
        _ => Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedTermExpression {
                reason: "expected paths, named calls/records, parentheses, or literal arguments",
            },
            expression.span(),
        )),
    }
}

enum TermMacroKind {
    Id,
    Bytes,
    Anonymous,
    OrBool,
    Fragment,
    Lexeme,
    Is,
    Project,
    Matches,
    Rewrite,
}

impl TermMacroKind {
    const fn root_kind(self) -> TermRootKind {
        match self {
            Self::OrBool
            | Self::Fragment
            | Self::Is
            | Self::Project
            | Self::Matches
            | Self::Rewrite => TermRootKind::Call,
            Self::Id | Self::Bytes | Self::Anonymous | Self::Lexeme => TermRootKind::Literal,
        }
    }
}

/// The error for a macro at a term's root that is no compiler-owned term
/// island; a `k::bits!` template there is out of place.
fn unsupported_root_macro(path: &Path, span: Span) -> SyntaxError {
    if crate::rule::is_bits_macro(path) {
        return crate::rule::misplaced_bit_template(path.span());
    }
    SyntaxError::new(
        SyntaxErrorKind::UnsupportedTermExpression {
            reason: "the root must be a named path/call/record or an Int/Bool literal",
        },
        span,
    )
}

/// Whether `path` names a compiler-owned term island.
#[must_use]
pub fn is_island_macro(path: &Path) -> bool {
    special_macro_kind(path).is_some()
}

/// Whether `path` names an island that denotes one constant of its sort:
/// `k::bytes!`, `k::id!`, or `k::lexeme!`. Such a term has the same value in
/// every sentence and in an initializer.
#[must_use]
pub fn is_constant_island_macro(path: &Path) -> bool {
    matches!(
        special_macro_kind(path),
        Some(TermMacroKind::Bytes | TermMacroKind::Id | TermMacroKind::Lexeme)
    )
}

/// Whether `path` names `k::rewrite!`, K's local rewrite.
pub(crate) fn is_rewrite_macro(path: &Path) -> bool {
    matches!(special_macro_kind(path), Some(TermMacroKind::Rewrite))
}

fn special_macro_kind(path: &Path) -> Option<TermMacroKind> {
    let name = path.segments.last()?.ident.to_string();
    match name.as_str() {
        "id" => Some(TermMacroKind::Id),
        "bytes" => Some(TermMacroKind::Bytes),
        "anonymous" => Some(TermMacroKind::Anonymous),
        "or_bool" => Some(TermMacroKind::OrBool),
        "fragment" => Some(TermMacroKind::Fragment),
        "lexeme" => Some(TermMacroKind::Lexeme),
        "is" => Some(TermMacroKind::Is),
        "project" => Some(TermMacroKind::Project),
        "matches" => Some(TermMacroKind::Matches),
        "rewrite" => Some(TermMacroKind::Rewrite),
        _ => None,
    }
}

#[expect(
    clippy::too_many_lines,
    reason = "One match over the closed set of compiler-owned term islands."
)]
fn validate_special_macro(
    value: &ExprMacro,
    context: TermExpressionContext,
    symbols: &mut Vec<TermSymbol>,
    nodes: &mut Vec<TermNode>,
) -> Result<TermTree, SyntaxError> {
    reject_attributes(&value.attrs, value.span())?;
    if is_std_matches(&value.mac.path) {
        return Err(matches_error(STD_MATCHES.to_owned(), value.mac.path.span()));
    }
    match special_macro_kind(&value.mac.path) {
        Some(TermMacroKind::Id) => {
            let literal: LitStr =
                syn::parse2(crate::parse::strip_trailing_comma(value.mac.tokens.clone()))?;
            let text = literal.value();
            if !valid_extended_id(&text) {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::UnsupportedTermExpression {
                        reason: "invalid builtin `Id` token; expected `$` followed by ASCII letters, digits, or `_`",
                    },
                    literal.span(),
                ));
            }
            nodes.push(TermNode::IdToken(literal.clone()));
            Ok(TermTree::IdToken { literal })
        }
        Some(TermMacroKind::Bytes) => {
            let literal: LitByteStr =
                syn::parse2(crate::parse::strip_trailing_comma(value.mac.tokens.clone()))?;
            nodes.push(TermNode::BytesToken(literal.clone()));
            Ok(TermTree::BytesToken { literal })
        }
        Some(TermMacroKind::Anonymous) => {
            let parser = |input: syn::parse::ParseStream<'_>| -> syn::Result<(Path, LitStr)> {
                let sort: Path = input.parse()?;
                input.parse::<Token![,]>()?;
                let spelling: LitStr = input.parse()?;
                if !input.is_empty() {
                    return Err(input.error("anonymous! accepts exactly `Sort, \"_Name\"`"));
                }
                Ok((sort, spelling))
            };
            let (sort, spelling) =
                parser.parse2(crate::parse::strip_trailing_comma(value.mac.tokens.clone()))?;
            let text = spelling.value();
            crate::parse::validate_authored_binder(&text, spelling.span())?;
            if !text.starts_with('_')
                || text.len() < 2
                || !text[1..]
                    .chars()
                    .all(|ch| ch == '_' || ch.is_ascii_alphanumeric())
            {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::UnsupportedTermExpression {
                        reason: "anonymous spelling must begin with `_` and contain only ASCII letters, digits, or `_`",
                    },
                    spelling.span(),
                ));
            }
            nodes.push(TermNode::Anonymous {
                sort: sort.clone(),
                spelling: spelling.clone(),
            });
            Ok(TermTree::Anonymous { sort, spelling })
        }
        Some(TermMacroKind::OrBool) => {
            let expressions = syn::punctuated::Punctuated::<Expr, Token![,]>::parse_terminated
                .parse2(value.mac.tokens.clone())?;
            let expressions = AtLeastTwo::try_from(expressions.into_iter().collect::<Vec<_>>())
                .map_err(|_| {
                    SyntaxError::new(
                        SyntaxErrorKind::UnsupportedTermExpression {
                            reason: "or_bool! requires at least two object-Bool operands",
                        },
                        value.span(),
                    )
                })?;
            let range = TokenRange::for_tokens(value)?;
            nodes.push(TermNode::OrBool(range));
            let arguments = expressions.try_map_ref(|expression| {
                validate_expression(expression, context, symbols, nodes)
            })?;
            Ok(TermTree::OrBool { range, arguments })
        }
        Some(TermMacroKind::Fragment) => validate_cell_term(value, context, symbols, nodes),
        Some(TermMacroKind::Lexeme) => {
            let (sort, text) = parse_lexeme_arguments(value.mac.tokens.clone())?;
            nodes.push(TermNode::Lexeme {
                sort: sort.clone(),
                text: text.clone(),
            });
            Ok(TermTree::Lexeme { sort, text })
        }
        Some(TermMacroKind::Is) => {
            validate_sort_test(value, SortTestKind::Predicate, context, symbols, nodes)
        }
        Some(TermMacroKind::Project) => {
            validate_sort_test(value, SortTestKind::Projection, context, symbols, nodes)
        }
        Some(TermMacroKind::Matches) => validate_matches(value, symbols, nodes),
        Some(TermMacroKind::Rewrite) => validate_rewrite(value, symbols, nodes),
        None if crate::rule::is_bits_macro(&value.mac.path) => {
            Err(crate::rule::misplaced_bit_template(value.mac.path.span()))
        }
        None => Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedTermExpression {
                reason: "macros are not terms unless they are compiler-owned `fragment!`, `id!`, `bytes!`, `anonymous!`, `lexeme!`, `is!`, `project!`, `matches!`, `or_bool!`, or `rewrite!` islands",
            },
            value.span(),
        )),
    }
}

/// The reason given for std's bare `matches!` in a term.
pub(crate) const STD_MATCHES: &str =
    "did you mean `k::matches!`? std's matches! tests a host value";

/// The reason given for an `if` guard in `k::matches!`.
const MATCHES_GUARD: &str = "K's :=K has no guard; conjoin a separate condition with bool::and";

fn matches_error(reason: String, span: Span) -> SyntaxError {
    SyntaxError::new(SyntaxErrorKind::InvalidMatches { reason }, span)
}

/// Whether `path` names std's `matches!` rather than `k::matches!`: the bare
/// name, which the prelude resolves to std's macro, or a `std::`/`core::`
/// path.
pub(crate) fn is_std_matches(path: &Path) -> bool {
    let Some(last) = path.segments.last() else {
        return false;
    };
    last.ident == "matches"
        && (path.segments.len() == 1
            || path
                .segments
                .first()
                .is_some_and(|first| first.ident == "std" || first.ident == "core"))
}

/// Splits the arguments of `k::matches!(subject, pattern)` into the subject
/// expression and the pattern tokens.
///
/// # Errors
///
/// Rejects anything but one term expression, a comma, and a pattern without
/// an `if` guard.
pub fn parse_matches_arguments(tokens: TokenStream) -> Result<(Expr, TokenStream), SyntaxError> {
    let tokens = crate::parse::strip_trailing_comma(tokens);
    let shape =
        || "`k::matches!` expects `subject, pattern`: `k::matches!(t, Pair(_, _))`".to_owned();
    let parser = |input: syn::parse::ParseStream<'_>| -> syn::Result<(Expr, TokenStream)> {
        let subject: Expr = input.parse()?;
        input.parse::<Token![,]>()?;
        let pattern: TokenStream = input.parse()?;
        Ok((subject, pattern))
    };
    let span = tokens.span();
    let (subject, pattern) = parser
        .parse2(tokens)
        .map_err(|error| matches_error(shape(), error.span()))?;
    if pattern.is_empty() {
        return Err(matches_error(shape(), span));
    }
    if let Some(guard) = pattern.clone().into_iter().find_map(|token| match token {
        proc_macro2::TokenTree::Ident(ident) if ident == "if" => Some(ident.span()),
        _ => None,
    }) {
        return Err(matches_error(MATCHES_GUARD.to_owned(), guard));
    }
    Ok((subject, pattern))
}

/// The binders of a pattern (BIND-1), in first-occurrence order: every
/// `name @ ..` alias and every unqualified single-identifier reference, but a
/// bare path at the root when `root_is_constructor` (a rule subject's or a
/// `k::matches!` pattern's root is a unit constructor; a `let` pattern's bare
/// root binds, `let n = ..`). The names a `let`, an `ml::exists` closure or a
/// `k::matches!` pattern inside the pattern binds are local to that
/// construct, and the right side of a `k::rewrite!` binds nothing.
pub(crate) fn pattern_tree_binders(
    pattern: &TermTree,
    root_is_constructor: bool,
) -> Vec<syn::Ident> {
    fn walk(tree: &TermTree, root: bool, output: &mut Vec<syn::Ident>) {
        let mut push = |ident: &syn::Ident| {
            if !output.contains(ident) {
                output.push(ident.clone());
            }
        };
        match tree {
            TermTree::Reference(path) if !root => {
                if let Some(ident) = crate::path::pattern_binder(path) {
                    push(ident);
                }
            }
            TermTree::As { binding, pattern } => {
                push(binding);
                walk(pattern, false, output);
            }
            TermTree::Or { alternatives, .. } => {
                for alternative in alternatives {
                    walk(alternative, root, output);
                }
            }
            TermTree::Application(application) => match &application.arguments {
                TermArguments::Positional(arguments) => {
                    for argument in arguments {
                        walk(argument, false, output);
                    }
                }
                TermArguments::Named(arguments) => {
                    for argument in arguments {
                        walk(&argument.value, false, output);
                    }
                }
            },
            TermTree::Cell(cell) => {
                for field in &cell.fields {
                    walk(&field.value, false, output);
                }
            }
            TermTree::SortTest { operand, .. } => walk(operand, false, output),
            TermTree::OrBool { arguments, .. } => {
                for argument in arguments {
                    walk(argument, false, output);
                }
            }
            TermTree::Matches { subject, .. } => walk(subject, false, output),
            // A rewrite's left side stands where the rewrite does.
            TermTree::Rewrite { from, .. } => walk(from, root, output),
            TermTree::Let { .. }
            | TermTree::Closure { .. }
            | TermTree::Reference(_)
            | TermTree::Literal(_)
            | TermTree::Wildcard(_)
            | TermTree::IdToken { .. }
            | TermTree::BytesToken { .. }
            | TermTree::Anonymous { .. }
            | TermTree::Lexeme { .. } => {}
        }
    }
    let mut output = Vec::new();
    walk(pattern, root_is_constructor, &mut output);
    output
}

/// Validates `k::matches!(subject, pattern)` (K's `:=K`, KF-031): the shell
/// node precedes the subject's nodes, then the pattern's, then one
/// `MatchesWildcard` node per `_` of the pattern.
fn validate_matches(
    value: &ExprMacro,
    symbols: &mut Vec<TermSymbol>,
    nodes: &mut Vec<TermNode>,
) -> Result<TermTree, SyntaxError> {
    let (subject, pattern_tokens) = parse_matches_arguments(value.mac.tokens.clone())?;
    let range = TokenRange::for_tokens(value)?;
    nodes.push(TermNode::Matches(range));
    let subject = validate_expression(&subject, TermExpressionContext::Expression, symbols, nodes)?;
    let mut signs = crate::rule::NegativeLiteralSpans::scan(pattern_tokens.clone());
    let pattern = Pat::parse_multi.parse2(pattern_tokens)?;
    if let Pat::Rest(_) = pattern {
        return Err(unsupported_pattern_form(&pattern));
    }
    let pattern = validate_pattern(&pattern, &mut signs, symbols, nodes)?;
    let mut wildcards = Vec::new();
    pattern.wildcard_ranges_preorder(&mut wildcards);
    nodes.extend(wildcards.into_iter().map(TermNode::MatchesWildcard));
    let binders = pattern_tree_binders(&pattern, true);
    Ok(TermTree::Matches {
        range,
        subject: Box::new(subject),
        pattern: Box::new(pattern),
        binders,
    })
}

/// The expected `k::rewrite!` arguments.
const REWRITE_SHAPE: &str =
    "`k::rewrite!` expects `from => to`: `k::rewrite!(Assign(x, v) => ())`, where `()` is K's `.K`";

pub(crate) fn local_rewrite_error(reason: String, span: Span) -> SyntaxError {
    SyntaxError::new(SyntaxErrorKind::InvalidLocalRewrite { reason }, span)
}

/// Splits `k::rewrite!` arguments at the top-level `=>`.
fn split_rewrite_arguments(tokens: &TokenStream) -> Option<(TokenStream, TokenStream)> {
    let tokens = crate::parse::strip_trailing_comma(tokens.clone())
        .into_iter()
        .collect::<Vec<_>>();
    let arrow = tokens.windows(2).position(|pair| {
        matches!(&pair[0], proc_macro2::TokenTree::Punct(first)
            if first.as_char() == '=' && first.spacing() == proc_macro2::Spacing::Joint)
            && matches!(&pair[1], proc_macro2::TokenTree::Punct(second) if second.as_char() == '>')
    })?;
    let from = tokens[..arrow].iter().cloned().collect::<TokenStream>();
    let to = tokens[arrow + 2..].iter().cloned().collect::<TokenStream>();
    (!from.is_empty() && !to.is_empty()).then_some((from, to))
}

/// Whether `tokens` is exactly `()`, K's `.K` on the right of a rewrite.
fn is_unit_tokens(tokens: &TokenStream) -> bool {
    let mut tokens = tokens.clone().into_iter();
    matches!(
        (tokens.next(), tokens.next()),
        (Some(proc_macro2::TokenTree::Group(group)), None)
            if group.delimiter() == proc_macro2::Delimiter::Parenthesis && group.stream().is_empty()
    )
}

/// Validates `k::rewrite!(from => to)` (K's local `=>`, KF-011): the shell
/// node precedes the left side's nodes (a pattern), then the right side's
/// (a term; `()` is `.K` and has none).
fn validate_rewrite(
    value: &ExprMacro,
    symbols: &mut Vec<TermSymbol>,
    nodes: &mut Vec<TermNode>,
) -> Result<TermTree, SyntaxError> {
    let range = TokenRange::for_tokens(value)?;
    let (from_tokens, to_tokens) = split_rewrite_arguments(&value.mac.tokens)
        .ok_or_else(|| local_rewrite_error(REWRITE_SHAPE.to_owned(), value.span()))?;
    let from_range = TokenRange::for_tokens(&from_tokens)?;
    let to_range = TokenRange::for_tokens(&to_tokens)?;
    let shell = nodes.len();
    nodes.push(TermNode::Rewrite {
        range,
        from: from_range,
        to: to_range,
        from_nodes: 0,
        to_nodes: 0,
    });
    let mut signs = crate::rule::NegativeLiteralSpans::scan(from_tokens.clone());
    let pattern = Pat::parse_multi.parse2(from_tokens)?;
    if let Pat::Rest(_) = pattern {
        return Err(unsupported_pattern_form(&pattern));
    }
    let start = nodes.len();
    let from = validate_pattern(&pattern, &mut signs, symbols, nodes)?;
    let middle = nodes.len();
    let to = if is_unit_tokens(&to_tokens) {
        None
    } else {
        let expression = syn::parse2::<Expr>(to_tokens)?;
        Some(Box::new(validate_expression(
            &expression,
            TermExpressionContext::Expression,
            symbols,
            nodes,
        )?))
    };
    let end = nodes.len();
    nodes[shell] = TermNode::Rewrite {
        range,
        from: from_range,
        to: to_range,
        from_nodes: middle - start,
        to_nodes: end - middle,
    };
    Ok(TermTree::Rewrite {
        range,
        from_range,
        to_range,
        from: Box::new(from),
        to,
    })
}

/// Checks that every unqualified bare name on the right side of a
/// `k::rewrite!` in `tree` is one of `bindings`, the left image's term
/// bindings (KF-011), or a name the right side binds around it: the right
/// side is a term built over the subject's bindings, in which a `let` binds
/// its names in the rest of its block, an `ml::exists` closure its parameter
/// in its body, and a `k::matches!` pattern its names in itself, as they do in
/// a result.
///
/// # Errors
///
/// Returns [`SyntaxErrorKind::InvalidLocalRewrite`] at the first unbound name.
pub(crate) fn check_rewrite_right_bindings(
    tree: &TermTree,
    bindings: &[syn::Ident],
) -> Result<(), SyntaxError> {
    RewriteRightNames {
        bindings,
        scopes: Vec::new(),
    }
    .find_rewrites(tree)
}

/// The names in scope on the right side of a `k::rewrite!`.
struct RewriteRightNames<'a> {
    /// The left image's term bindings.
    bindings: &'a [syn::Ident],
    /// The names the enclosing `let` statements and closures of the right
    /// side bind, innermost last.
    scopes: Vec<&'a [syn::Ident]>,
}

impl<'a> RewriteRightNames<'a> {
    /// Checks the right side of every rewrite at or below `tree`, a part of
    /// the subject.
    fn find_rewrites(&mut self, tree: &'a TermTree) -> Result<(), SyntaxError> {
        match tree {
            TermTree::Rewrite { to, .. } => to.as_deref().map_or(Ok(()), |to| self.right(to)),
            other => subterms(other)
                .into_iter()
                .try_for_each(|subterm| self.find_rewrites(subterm)),
        }
    }

    /// Checks the names of `tree`, a part of a rewrite's right side.
    fn right(&mut self, tree: &'a TermTree) -> Result<(), SyntaxError> {
        match tree {
            TermTree::Reference(path) => self.name(path),
            // The value is read outside the pattern's scope, the rest of the
            // block inside it.
            TermTree::Let {
                value,
                body,
                binders,
                ..
            } => {
                self.right(value)?;
                self.scoped(binders, body)
            }
            TermTree::Closure { binder, body, .. } => {
                self.scoped(std::slice::from_ref(binder), body)
            }
            // The pattern's names are its own.
            TermTree::Matches { subject, .. } => self.right(subject),
            other => subterms(other)
                .into_iter()
                .try_for_each(|subterm| self.right(subterm)),
        }
    }

    fn scoped(&mut self, names: &'a [syn::Ident], body: &'a TermTree) -> Result<(), SyntaxError> {
        self.scopes.push(names);
        let checked = self.right(body);
        self.scopes.pop();
        checked
    }

    fn name(&self, path: &Path) -> Result<(), SyntaxError> {
        let Some(name) = crate::path::pattern_binder(path) else {
            return Ok(());
        };
        if self
            .bindings
            .iter()
            .chain(self.scopes.iter().copied().flatten())
            .any(|binding| binding == name)
        {
            return Ok(());
        }
        Err(local_rewrite_error(
            format!(
                "`{name}` on the right of `k::rewrite!` is not bound by the rule's left image (its subject with each rewrite replaced by its left side); bind it in the pattern, or qualify a unit constructor"
            ),
            name.span(),
        ))
    }
}

/// The terms directly below `tree`, in source order.
fn subterms(tree: &TermTree) -> Vec<&TermTree> {
    match tree {
        TermTree::Application(application) => {
            let mut subterms = match &application.arguments {
                TermArguments::Positional(arguments) => arguments.iter().collect::<Vec<_>>(),
                TermArguments::Named(arguments) => {
                    arguments.iter().map(|argument| &argument.value).collect()
                }
            };
            subterms.extend(application.update.as_deref());
            subterms
        }
        TermTree::Cell(cell) => cell
            .fields
            .iter()
            .map(|field| &field.value)
            .chain(cell.update.as_deref())
            .collect(),
        TermTree::SortTest { operand, .. } => vec![operand],
        TermTree::OrBool { arguments, .. } => arguments.iter().collect(),
        TermTree::As { pattern, .. } => vec![pattern],
        TermTree::Or { alternatives, .. } => alternatives.iter().collect(),
        TermTree::Matches {
            subject, pattern, ..
        } => vec![subject, pattern],
        TermTree::Let {
            pattern,
            value,
            body,
            ..
        } => vec![pattern, value, body],
        TermTree::Closure { body, .. } => vec![body],
        TermTree::Rewrite { from, to, .. } => std::iter::once(from.as_ref())
            .chain(to.as_deref())
            .collect(),
        TermTree::Reference(_)
        | TermTree::Literal(_)
        | TermTree::Wildcard(_)
        | TermTree::IdToken { .. }
        | TermTree::BytesToken { .. }
        | TermTree::Anonymous { .. }
        | TermTree::Lexeme { .. } => Vec::new(),
    }
}

/// Keys the `rule_local_rewrite`, `rule_local_rewrite_from`, and
/// `rule_local_rewrite_to` nodes of every `k::rewrite!` in `nodes`, each as
/// the next of its role (KF-011).
///
/// # Errors
///
/// Returns an occurrence-overflow error.
pub(crate) fn allocate_rewrite_keys(
    keys: &mut KeyAllocator,
    nodes: &[TermNode],
    term_keys: &mut TermKeys,
) -> Result<(), SyntaxError> {
    for (index, node) in nodes.iter().enumerate() {
        let TermNode::Rewrite {
            range, from, to, ..
        } = node
        else {
            continue;
        };
        term_keys.push_node(index, keys.key(ProvenanceRole::RuleLocalRewrite, *range)?);
        term_keys.push_node(
            index,
            keys.key(ProvenanceRole::RuleLocalRewriteFrom, *from)?,
        );
        term_keys.push_node(index, keys.key(ProvenanceRole::RuleLocalRewriteTo, *to)?);
    }
    Ok(())
}

/// The shape every term block takes (KF-032).
pub(crate) const LET_BLOCK_SHAPE: &str =
    "a term block is `let pattern = term;`* followed by one result term (K's #let)";

/// The reason given for an ascribed pattern that is not one name.
const LET_ASCRIPTION: &str =
    "a `let` sort ascription names one binder and a plain sort: `let x: Sort = term;`";

fn let_error(reason: String, span: Span) -> SyntaxError {
    SyntaxError::new(SyntaxErrorKind::InvalidLet { reason }, span)
}

/// Validates a term block `{ let pattern = term; .. result }` (K's `#let`,
/// KF-032).
fn validate_let_block(
    block: &syn::ExprBlock,
    symbols: &mut Vec<TermSymbol>,
    nodes: &mut Vec<TermNode>,
) -> Result<TermTree, SyntaxError> {
    if !block.attrs.is_empty() || block.label.is_some() {
        return Err(let_error(LET_BLOCK_SHAPE.to_owned(), block.span()));
    }
    validate_let_statements(&block.block.stmts, block.span(), symbols, nodes)
}

/// Validates the statements of a term block: zero or more
/// `let pattern = term;` statements and one result term without a
/// semicolon. The statements nest to the right, so each `let` scopes over
/// the rest of the block; the nodes follow source order.
pub(crate) fn validate_let_statements(
    statements: &[syn::Stmt],
    span: Span,
    symbols: &mut Vec<TermSymbol>,
    nodes: &mut Vec<TermNode>,
) -> Result<TermTree, SyntaxError> {
    let Some((tail, lets)) = statements.split_last() else {
        return Err(let_error(LET_BLOCK_SHAPE.to_owned(), span));
    };
    let mut statements = Vec::with_capacity(lets.len());
    for statement in lets {
        let syn::Stmt::Local(local) = statement else {
            return Err(let_error(LET_BLOCK_SHAPE.to_owned(), statement.span()));
        };
        statements.push(validate_let_statement(local, symbols, nodes)?);
    }
    let syn::Stmt::Expr(tail, None) = tail else {
        return Err(let_error(LET_BLOCK_SHAPE.to_owned(), tail.span()));
    };
    let mut tree = validate_expression(tail, TermExpressionContext::Expression, symbols, nodes)?;
    for statement in statements.into_iter().rev() {
        tree = TermTree::Let {
            range: statement.range,
            pattern: Box::new(statement.pattern),
            sort: statement.sort,
            value: Box::new(statement.value),
            body: Box::new(tree),
            binders: statement.binders,
        };
    }
    Ok(tree)
}

struct LetStatement {
    range: TokenRange,
    pattern: TermTree,
    sort: Option<Path>,
    value: TermTree,
    binders: Vec<syn::Ident>,
}

/// Validates one `let pattern = value;` statement: the shell node, then the
/// pattern's nodes and wildcards, then the value's nodes.
fn validate_let_statement(
    local: &syn::Local,
    symbols: &mut Vec<TermSymbol>,
    nodes: &mut Vec<TermNode>,
) -> Result<LetStatement, SyntaxError> {
    let shape = || let_error(LET_BLOCK_SHAPE.to_owned(), local.span());
    if !local.attrs.is_empty() {
        return Err(shape());
    }
    let Some(init) = &local.init else {
        return Err(shape());
    };
    if init.diverge.is_some() {
        return Err(shape());
    }
    let (pattern, sort) = match &local.pat {
        Pat::Type(typed) => {
            let Pat::Ident(identifier) = typed.pat.as_ref() else {
                return Err(let_error(LET_ASCRIPTION.to_owned(), typed.span()));
            };
            if identifier.subpat.is_some() || !identifier.attrs.is_empty() {
                return Err(let_error(LET_ASCRIPTION.to_owned(), typed.span()));
            }
            let syn::Type::Path(sort) = typed.ty.as_ref() else {
                return Err(let_error(LET_ASCRIPTION.to_owned(), typed.ty.span()));
            };
            if sort.qself.is_some() || !is_plain_path(&sort.path) {
                return Err(let_error(LET_ASCRIPTION.to_owned(), typed.ty.span()));
            }
            (typed.pat.as_ref(), Some(sort.path.clone()))
        }
        pattern => (pattern, None),
    };
    if let Pat::Ident(identifier) = pattern
        && (identifier.by_ref.is_some() || identifier.mutability.is_some())
    {
        return Err(shape());
    }
    if let Pat::Rest(_) = pattern {
        return Err(unsupported_pattern_form(pattern));
    }
    let range = TokenRange::for_tokens(local)?;
    nodes.push(TermNode::Let {
        range,
        sort: sort.clone(),
    });
    let mut signs = crate::rule::NegativeLiteralSpans::scan(pattern.to_token_stream());
    let pattern = validate_pattern(pattern, &mut signs, symbols, nodes)?;
    let mut wildcards = Vec::new();
    pattern.wildcard_ranges_preorder(&mut wildcards);
    nodes.extend(wildcards.into_iter().map(TermNode::LetWildcard));
    let value = validate_expression(
        &init.expr,
        TermExpressionContext::Expression,
        symbols,
        nodes,
    )?;
    let binders = pattern_tree_binders(&pattern, false);
    Ok(LetStatement {
        range,
        pattern,
        sort,
        value,
        binders,
    })
}

/// Keys every `let` statement, with its optional `let_sort` numbered as the
/// statement is, and every `_` in a `let` pattern as a `let_wildcard`. Like
/// `matches` roles, both are side-neutral.
///
/// # Errors
///
/// Returns an endpoint or occurrence-overflow error.
pub(crate) fn allocate_let_keys(
    keys: &mut KeyAllocator,
    nodes: &[TermNode],
    term_keys: &mut TermKeys,
) -> Result<(), SyntaxError> {
    for (index, node) in nodes.iter().enumerate() {
        match node {
            TermNode::Let { range, sort } => {
                // The sort precedes its statement.
                if let Some(sort) = sort {
                    let statement = keys.next_key(ProvenanceRole::Let);
                    let sort = keys.paired(
                        ProvenanceRole::LetSort,
                        &statement,
                        TokenRange::for_tokens(sort)?,
                    )?;
                    term_keys.push_node(index, sort);
                }
                term_keys.push_node(index, keys.key(ProvenanceRole::Let, *range)?);
            }
            TermNode::LetWildcard(range) => {
                term_keys.push_node(index, keys.key(ProvenanceRole::LetWildcard, *range)?);
            }
            _ => {}
        }
    }
    Ok(())
}

/// Keys the `ml_binder_sort`, `ml_binder`, and `ml_connective` nodes of every
/// `ml::exists` closure (KF-039), each as the next of its role. Like `let`
/// roles, they are side-neutral.
///
/// # Errors
///
/// Returns an endpoint or occurrence-overflow error.
pub(crate) fn allocate_ml_binder_keys(
    keys: &mut KeyAllocator,
    nodes: &[TermNode],
    term_keys: &mut TermKeys,
) -> Result<(), SyntaxError> {
    for (index, node) in nodes.iter().enumerate() {
        if let TermNode::Closure {
            range,
            binder,
            sort,
        } = node
        {
            let sort = keys.key(ProvenanceRole::MlBinderSort, TokenRange::for_tokens(sort)?)?;
            term_keys.push_node(index, sort);
            let binder = keys.key(ProvenanceRole::MlBinder, TokenRange::for_tokens(binder)?)?;
            term_keys.push_node(index, binder);
            term_keys.push_node(index, keys.key(ProvenanceRole::MlConnective, *range)?);
        }
    }
    Ok(())
}

/// Keys every `k::matches!` node and every `_` in a `k::matches!` pattern.
/// Like lexeme roles, both are side-neutral: a sentence numbers them once,
/// in the order it expands.
///
/// # Errors
///
/// Returns an occurrence-overflow error.
pub(crate) fn allocate_matches_keys(
    keys: &mut KeyAllocator,
    nodes: &[TermNode],
    term_keys: &mut TermKeys,
) -> Result<(), SyntaxError> {
    for (index, node) in nodes.iter().enumerate() {
        let (role, range) = match node {
            TermNode::Matches(range) => (ProvenanceRole::Matches, range),
            TermNode::MatchesWildcard(range) => (ProvenanceRole::MatchesWildcard, range),
            _ => continue,
        };
        term_keys.push_node(index, keys.key(role, *range)?);
    }
    Ok(())
}

/// Keys the `lexeme_sort` and `lexeme_text` nodes of every `k::lexeme!`
/// node in `nodes`.
///
/// Lexeme roles are side-neutral, so one sentence numbers its lexemes once,
/// across its subject, result, and conditions in that order.
///
/// # Errors
///
/// Returns an endpoint or occurrence-overflow error.
pub(crate) fn allocate_lexeme_keys(
    keys: &mut KeyAllocator,
    nodes: &[TermNode],
    term_keys: &mut TermKeys,
) -> Result<(), SyntaxError> {
    for (index, node) in nodes.iter().enumerate() {
        if let TermNode::Lexeme { sort, text } = node {
            let sort = keys.key(ProvenanceRole::LexemeSort, TokenRange::for_tokens(sort)?)?;
            term_keys.push_node(index, sort);
            let text = keys.key(ProvenanceRole::LexemeText, TokenRange::for_tokens(text)?)?;
            term_keys.push_node(index, text);
        }
    }
    Ok(())
}

/// Keys every literal node in `nodes` under `role`, over the literal's
/// tokens: an initializer's literals, which a pass numbers in preorder across
/// the initializer's terms.
///
/// # Errors
///
/// Returns an endpoint or occurrence-overflow error.
pub(crate) fn allocate_literal_keys(
    keys: &mut KeyAllocator,
    nodes: &[TermNode],
    term_keys: &mut TermKeys,
    role: ProvenanceRole,
) -> Result<(), SyntaxError> {
    for (index, node) in nodes.iter().enumerate() {
        if let TermNode::Literal(literal) = node {
            term_keys.push_node(index, keys.key(role, literal.range()?)?);
        }
    }
    Ok(())
}

/// Validates `k::is!(Sort, t)` or `k::project!(Sort, t)`; the macro shell
/// node precedes the operand's nodes.
fn validate_sort_test(
    value: &ExprMacro,
    kind: SortTestKind,
    context: TermExpressionContext,
    symbols: &mut Vec<TermSymbol>,
    nodes: &mut Vec<TermNode>,
) -> Result<TermTree, SyntaxError> {
    let (sort, operand) = parse_sort_test_arguments(kind, value.mac.tokens.clone())?;
    let range = TokenRange::for_tokens(value)?;
    nodes.push(TermNode::SortTest {
        range,
        sort: sort.clone(),
    });
    let operand = validate_expression(&operand, context, symbols, nodes)?;
    Ok(TermTree::SortTest {
        range,
        kind,
        sort,
        operand: Box::new(operand),
    })
}

/// Keys the `sort_test` and `sort_test_sort` nodes of every `k::is!` and
/// `k::project!` node in `nodes`.
///
/// Like lexeme roles, sort-test roles are side-neutral, so one sentence
/// numbers its sort tests once, across its subject, result, and conditions in
/// that order.
///
/// # Errors
///
/// Returns an endpoint or occurrence-overflow error.
pub(crate) fn allocate_sort_test_keys(
    keys: &mut KeyAllocator,
    nodes: &[TermNode],
    term_keys: &mut TermKeys,
) -> Result<(), SyntaxError> {
    for (index, node) in nodes.iter().enumerate() {
        if let TermNode::SortTest { range, sort } = node {
            term_keys.push_node(index, keys.key(ProvenanceRole::SortTest, *range)?);
            let sort = keys.key(ProvenanceRole::SortTestSort, TokenRange::for_tokens(sort)?)?;
            term_keys.push_node(index, sort);
        }
    }
    Ok(())
}

/// Keys every turbofish sort marker on an application head in `nodes`
/// (`Choose::<k::builtin::Int>`, KF-027). Like sort tests, instances are
/// numbered once across a sentence, in expansion order.
///
/// # Errors
///
/// Returns an endpoint or occurrence-overflow error.
pub(crate) fn allocate_application_instance_keys(
    keys: &mut KeyAllocator,
    nodes: &[TermNode],
    term_keys: &mut TermKeys,
) -> Result<(), SyntaxError> {
    for (index, node) in nodes.iter().enumerate() {
        let TermNode::ApplicationHead(path) = node else {
            continue;
        };
        let Some(syn::PathArguments::AngleBracketed(arguments)) =
            path.segments.last().map(|segment| &segment.arguments)
        else {
            continue;
        };
        for argument in &arguments.args {
            let instance = keys.key(
                ProvenanceRole::ApplicationInstance,
                TokenRange::for_tokens(argument)?,
            )?;
            term_keys.push_node(index, instance);
        }
    }
    Ok(())
}

/// Keys the `pattern_as` and `pattern_as_binding` nodes of every
/// `name @ pattern` node in `nodes`. A sentence numbers its aliases once,
/// in the order its left-hand side expands.
///
/// # Errors
///
/// Returns an endpoint or occurrence-overflow error.
pub(crate) fn allocate_pattern_as_keys(
    keys: &mut KeyAllocator,
    nodes: &[TermNode],
    term_keys: &mut TermKeys,
) -> Result<(), SyntaxError> {
    for (index, node) in nodes.iter().enumerate() {
        if let TermNode::As { binding, range } = node {
            term_keys.push_node(index, keys.key(ProvenanceRole::PatternAs, *range)?);
            let binding = keys.key(
                ProvenanceRole::PatternAsBinding,
                TokenRange::for_tokens(binding)?,
            )?;
            term_keys.push_node(index, binding);
        }
    }
    Ok(())
}

/// Keys every `A | B` node in `nodes`. A sentence numbers its or-patterns
/// once, in the order its left-hand side expands.
///
/// # Errors
///
/// Returns an occurrence-overflow error.
pub(crate) fn allocate_pattern_or_keys(
    keys: &mut KeyAllocator,
    nodes: &[TermNode],
    term_keys: &mut TermKeys,
) -> Result<(), SyntaxError> {
    for (index, node) in nodes.iter().enumerate() {
        if let TermNode::Or(range) = node {
            term_keys.push_node(index, keys.key(ProvenanceRole::PatternOr, *range)?);
        }
    }
    Ok(())
}

/// Parses the arguments of `k::is!(Sort, t)` or `k::project!(Sort, t)`.
///
/// # Errors
///
/// Rejects anything but a plain sort path, a comma, and one term expression.
pub fn parse_sort_test_arguments(
    kind: SortTestKind,
    tokens: TokenStream,
) -> Result<(Path, Expr), SyntaxError> {
    let tokens = crate::parse::strip_trailing_comma(tokens);
    let parser = |input: syn::parse::ParseStream<'_>| -> syn::Result<(Path, Expr)> {
        let sort: Path = input.parse()?;
        input.parse::<Token![,]>()?;
        let operand: Expr = input.parse()?;
        if !input.is_empty() {
            return Err(input.error("expected exactly `Sort, term`"));
        }
        Ok((sort, operand))
    };
    let reason = match kind {
        SortTestKind::Predicate => "`k::is!` expects `Sort, term`: `k::is!(Sort, t)`",
        SortTestKind::Projection => "`k::project!` expects `Sort, term`: `k::project!(Sort, t)`",
    };
    let (sort, operand) = parser.parse2(tokens).map_err(|error| {
        SyntaxError::new(
            SyntaxErrorKind::UnsupportedTermExpression { reason },
            error.span(),
        )
    })?;
    if !is_plain_path(&sort) {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedPath,
            sort.span(),
        ));
    }
    Ok((sort, operand))
}

/// Parses the arguments of `k::lexeme!(Sort, "text")`.
///
/// # Errors
///
/// Rejects anything but a plain sort path, a comma, and one nonempty string
/// literal.
pub fn parse_lexeme_arguments(tokens: TokenStream) -> Result<(Path, LitStr), SyntaxError> {
    let tokens = crate::parse::strip_trailing_comma(tokens);
    let parser = |input: syn::parse::ParseStream<'_>| -> syn::Result<(Path, LitStr)> {
        let sort: Path = input.parse()?;
        input.parse::<Token![,]>()?;
        let text: LitStr = input.parse()?;
        if !input.is_empty() {
            return Err(input.error("lexeme! accepts exactly `Sort, \"text\"`"));
        }
        Ok((sort, text))
    };
    let (sort, text) = parser.parse2(tokens).map_err(|error| {
        SyntaxError::new(
            SyntaxErrorKind::InvalidTokenAttribute {
                reason: "`k::lexeme!` takes exactly a token sort path and a string literal: `k::lexeme!(Sort, \"text\")`",
            },
            error.span(),
        )
    })?;
    if !is_plain_path(&sort) {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedPath,
            sort.span(),
        ));
    }
    if text.value().is_empty() {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidTokenAttribute {
                reason: "`k::lexeme!` text must not be empty",
            },
            text.span(),
        ));
    }
    Ok((sort, text))
}

fn validate_cell_term(
    value: &ExprMacro,
    context: TermExpressionContext,
    symbols: &mut Vec<TermSymbol>,
    nodes: &mut Vec<TermNode>,
) -> Result<TermTree, SyntaxError> {
    let record: ExprStruct =
        syn::parse2(crate::parse::strip_trailing_comma(value.mac.tokens.clone()))?;
    reject_attributes(&record.attrs, record.span())?;
    if record.qself.is_some() || !is_plain_path(&record.path) {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedPath,
            record.path.span(),
        ));
    }
    let base = record_update_base(&record)?;
    if base.is_some() {
        reject_repeated_fields(record.fields.iter().map(|field| &field.member))?;
    }
    symbols.push(TermSymbol {
        path: record.path.clone(),
        kind: TermSymbolKind::ApplicationHead,
    });
    nodes.push(TermNode::ApplicationHead(record.path.clone()));
    let mut fields = Vec::with_capacity(record.fields.len());
    for field in &record.fields {
        let Member::Named(name) = &field.member else {
            return Err(SyntaxError::new(
                SyntaxErrorKind::UnsupportedTermExpression {
                    reason: "complete cell terms require unadorned named fields",
                },
                field.span(),
            ));
        };
        if !field.attrs.is_empty() {
            return Err(SyntaxError::new(
                SyntaxErrorKind::UnsupportedTermExpression {
                    reason: "complete cell terms require unadorned named fields",
                },
                field.span(),
            ));
        }
        fields.push(TermNamedArgument {
            name: name.clone(),
            value: validate_expression(&field.expr, context, symbols, nodes)?,
        });
    }
    // An update takes the children it does not list from its base.
    let update = base
        .map(|base| validate_path_expression(base, symbols, nodes).map(Box::new))
        .transpose()?;
    if fields.is_empty() && update.is_none() {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedTermExpression {
                reason: "complete cell terms require at least one child field",
            },
            record.span(),
        ));
    }
    Ok(TermTree::Cell(CellTerm {
        range: TokenRange::for_tokens(value)?,
        owner: record.path,
        fields,
        open: false,
        update,
    }))
}

/// The pattern twin of [`validate_cell_term`]: `k::fragment![..]` in a
/// pattern payload, whose field values are patterns (PAT-1).
fn validate_cell_pattern(
    value: &ExprMacro,
    signs: &mut crate::rule::NegativeLiteralSpans,
    symbols: &mut Vec<TermSymbol>,
    nodes: &mut Vec<TermNode>,
) -> Result<TermTree, SyntaxError> {
    reject_attributes(&value.attrs, value.span())?;
    let Pat::Struct(record) =
        Pat::parse_multi.parse2(crate::parse::strip_trailing_comma(value.mac.tokens.clone()))?
    else {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedTermExpression {
                reason: "fragment! requires one nominal cell record",
            },
            value.mac.tokens.span(),
        ));
    };
    reject_attributes(&record.attrs, record.span())?;
    if record.qself.is_some() || !is_plain_path(&record.path) {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedPath,
            record.path.span(),
        ));
    }
    // `..` leaves the children the pattern does not name unconstrained.
    let open = match &record.rest {
        Some(rest) => {
            reject_attributes(&rest.attrs, rest.span())?;
            true
        }
        None => false,
    };
    symbols.push(TermSymbol {
        path: record.path.clone(),
        kind: TermSymbolKind::ApplicationHead,
    });
    nodes.push(TermNode::ApplicationHead(record.path.clone()));
    let fields = validate_field_patterns(
        &record,
        "complete cell terms require unadorned named fields",
        signs,
        symbols,
        nodes,
    )?;
    if fields.is_empty() && !open {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedTermExpression {
                reason: "complete cell terms require at least one child field",
            },
            record.span(),
        ));
    }
    Ok(TermTree::Cell(CellTerm {
        range: TokenRange::for_tokens(value)?,
        owner: record.path,
        fields,
        open,
        update: None,
    }))
}

fn valid_extended_id(value: &str) -> bool {
    value.strip_prefix('$').is_some_and(|tail| {
        !tail.is_empty()
            && tail
                .chars()
                .all(|ch| ch == '_' || ch.is_ascii_alphanumeric())
    })
}

fn validate_path_expression(
    expression: &ExprPath,
    symbols: &mut Vec<TermSymbol>,
    nodes: &mut Vec<TermNode>,
) -> Result<TermTree, SyntaxError> {
    reject_attributes(&expression.attrs, expression.span())?;
    if expression.qself.is_some() || !is_plain_path(&expression.path) {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedPath,
            expression.span(),
        ));
    }
    if expression.path.leading_colon.is_none()
        && let Some(constant) = float_constant_path(&expression.path)
    {
        let literal = TermLiteral::Float(float_constant(&expression.path, constant?, None)?);
        nodes.push(TermNode::Literal(literal.clone()));
        return Ok(TermTree::Literal(literal));
    }
    symbols.push(TermSymbol {
        path: expression.path.clone(),
        kind: TermSymbolKind::Reference,
    });
    nodes.push(TermNode::Reference(expression.path.clone()));
    Ok(TermTree::Reference(expression.path.clone()))
}

/// Validates a call; `notation` marks the call that a notation form denotes.
fn validate_call(
    call: &ExprCall,
    notation: bool,
    context: TermExpressionContext,
    symbols: &mut Vec<TermSymbol>,
    nodes: &mut Vec<TermNode>,
) -> Result<TermTree, SyntaxError> {
    reject_attributes(&call.attrs, call.span())?;
    let Expr::Path(head) = &*call.func else {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedTermExpression {
                reason: "a term call must have a plain named path as its head",
            },
            call.func.span(),
        ));
    };
    if head.qself.is_some() || !head.attrs.is_empty() || !is_head_path(&head.path) {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedPath,
            head.span(),
        ));
    }
    let (head_path, instance) = application_head(&head.path)?;
    symbols.push(TermSymbol {
        path: head.path.clone(),
        kind: TermSymbolKind::ApplicationHead,
    });
    nodes.push(TermNode::ApplicationHead(head.path.clone()));
    let mut arguments = Vec::with_capacity(call.args.len());
    for argument in &call.args {
        // `ml::exists(|x: S| p)` (KF-039): the closure is the call's one
        // argument. Semantic lowering checks that the head is `ml::exists`.
        if let Expr::Closure(closure) = argument
            && call.args.len() == 1
        {
            arguments.push(validate_closure(closure, symbols, nodes)?);
            continue;
        }
        arguments.push(validate_expression(argument, context, symbols, nodes)?);
    }
    Ok(TermTree::Application(TermApplication {
        head: head_path,
        arguments: TermArguments::Positional(arguments),
        instance,
        notation,
        update: None,
        open: false,
    }))
}

/// The reason given for a closure outside `ml::exists` (KF-039).
pub(crate) const CLOSURE_OUTSIDE_EXISTS: &str = "closures introduce quantified binders only inside ml::exists: write `ml::exists(|x: Sort| predicate)`; a closure is never a K function";

/// The shape every `ml::exists` closure takes (KF-039).
const ML_EXISTS_SHAPE: &str = "ml::exists takes exactly one closure with one typed parameter: `ml::exists(|x: Sort| predicate)`";

fn ml_exists_error(reason: String, span: Span) -> SyntaxError {
    SyntaxError::new(SyntaxErrorKind::InvalidMlExists { reason }, span)
}

/// Validates the closure `|binder: Sort| body` of an `ml::exists`
/// (KF-039): its shell node precedes the nodes of its body.
fn validate_closure(
    closure: &syn::ExprClosure,
    symbols: &mut Vec<TermSymbol>,
    nodes: &mut Vec<TermNode>,
) -> Result<TermTree, SyntaxError> {
    let shape = |span: Span| ml_exists_error(ML_EXISTS_SHAPE.to_owned(), span);
    if !closure.attrs.is_empty()
        || closure.lifetimes.is_some()
        || closure.constness.is_some()
        || closure.movability.is_some()
        || closure.asyncness.is_some()
        || closure.capture.is_some()
    {
        return Err(shape(closure.span()));
    }
    if let syn::ReturnType::Type(_, ty) = &closure.output {
        return Err(shape(ty.span()));
    }
    let mut inputs = closure.inputs.iter();
    let (Some(input), None) = (inputs.next(), inputs.next()) else {
        return Err(shape(closure.or1_token.span()));
    };
    let Pat::Type(typed) = input else {
        return Err(ml_exists_error(
            "the ml::exists binder needs a sort: write `|x: Sort| predicate`".to_owned(),
            input.span(),
        ));
    };
    let Pat::Ident(identifier) = typed.pat.as_ref() else {
        return Err(shape(typed.pat.span()));
    };
    if identifier.by_ref.is_some()
        || identifier.mutability.is_some()
        || identifier.subpat.is_some()
        || !identifier.attrs.is_empty()
        || !typed.attrs.is_empty()
    {
        return Err(shape(typed.span()));
    }
    let syn::Type::Path(sort) = typed.ty.as_ref() else {
        return Err(shape(typed.ty.span()));
    };
    if sort.qself.is_some() || !is_plain_path(&sort.path) {
        return Err(shape(typed.ty.span()));
    }
    nodes.push(TermNode::Closure {
        range: TokenRange::for_tokens(closure)?,
        binder: identifier.ident.clone(),
        sort: sort.path.clone(),
    });
    let body = validate_expression(
        &closure.body,
        TermExpressionContext::Expression,
        symbols,
        nodes,
    )?;
    Ok(TermTree::Closure {
        range: TokenRange::for_tokens(closure)?,
        binder: identifier.ident.clone(),
        sort: sort.path.clone(),
        body: Box::new(body),
    })
}

fn validate_record(
    record: &ExprStruct,
    context: TermExpressionContext,
    symbols: &mut Vec<TermSymbol>,
    nodes: &mut Vec<TermNode>,
) -> Result<TermTree, SyntaxError> {
    reject_attributes(&record.attrs, record.span())?;
    if record.qself.is_some() || !is_head_path(&record.path) {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedPath,
            record.path.span(),
        ));
    }
    let (head, instance) = application_head(&record.path)?;
    let base = record_update_base(record)?;
    if base.is_some() {
        reject_repeated_fields(record.fields.iter().map(|field| &field.member))?;
    }
    symbols.push(TermSymbol {
        path: record.path.clone(),
        kind: TermSymbolKind::ApplicationHead,
    });
    nodes.push(TermNode::ApplicationHead(record.path.clone()));
    let mut arguments = Vec::with_capacity(record.fields.len());
    for field in &record.fields {
        let Member::Named(name) = &field.member else {
            return Err(SyntaxError::new(
                SyntaxErrorKind::UnsupportedTermExpression {
                    reason: "record terms require unadorned named fields",
                },
                field.span(),
            ));
        };
        if !field.attrs.is_empty() {
            return Err(SyntaxError::new(
                SyntaxErrorKind::UnsupportedTermExpression {
                    reason: "record terms require unadorned named fields",
                },
                field.span(),
            ));
        }
        arguments.push(TermNamedArgument {
            name: name.clone(),
            value: validate_expression(&field.expr, context, symbols, nodes)?,
        });
    }
    // The base is read after the fields, where it is written.
    let update = base
        .map(|base| validate_path_expression(base, symbols, nodes).map(Box::new))
        .transpose()?;
    Ok(TermTree::Application(TermApplication {
        head,
        arguments: TermArguments::Named(arguments),
        instance,
        notation: false,
        update,
        // `..` with no base leaves the record's other fields open, as in a pattern.
        open: record.rest.is_none() && record.dot2_token.is_some(),
    }))
}

/// The base `t` of a record update `Ctor { f: e, ..t }` (F5): one binder.
/// Where an update may stand is the position table's to say.
fn record_update_base(record: &ExprStruct) -> Result<Option<&ExprPath>, SyntaxError> {
    let Some(rest) = &record.rest else {
        return Ok(None);
    };
    let invalid = |reason: &str, span| {
        SyntaxError::new(
            SyntaxErrorKind::InvalidRecordUpdate {
                reason: reason.to_owned(),
            },
            span,
        )
    };
    match rest.as_ref() {
        Expr::Path(path)
            if path.attrs.is_empty() && path.qself.is_none() && path.path.get_ident().is_some() =>
        {
            Ok(Some(path))
        }
        _ => Err(invalid(
            "the base of a record update is one name: in a sentence the alias `t` of a record matched as `t @ Ctor { .. }`, in an initializer a configuration variable, a name a `let` binds, or a constant",
            rest.span(),
        )),
    }
}

/// Rejects a record that names one field twice: a field has one value.
fn reject_repeated_fields<'a>(
    members: impl IntoIterator<Item = &'a Member>,
) -> Result<(), SyntaxError> {
    let mut seen = Vec::<&syn::Ident>::new();
    for member in members {
        if let Member::Named(name) = member {
            if seen.contains(&name) {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::InvalidRecordUpdate {
                        reason: format!("the record names the field `{name}` twice"),
                    },
                    name.span(),
                ));
            }
            seen.push(name);
        }
    }
    Ok(())
}

/// The reason given for a unary minus that is not part of an Int literal.
pub(crate) const UNARY_MINUS: &str = "this minus is a literal's sign, which only an unsuffixed integer literal (in any radix) or a float literal takes";

/// The reason given for `-0`, which is not a canonical K `Int` token.
pub(crate) const NEGATIVE_ZERO: &str = "`-0` is not an Int literal; write 0";

/// The reason given for an integer literal with a Rust width suffix.
pub(crate) const INT_SUFFIX: &str =
    "Int literals must be unsuffixed Rust integers (decimal, 0x hex, 0o octal, or 0b binary)";

/// Whether an integer literal is unsuffixed, in any radix (`255`, `0xFF`,
/// `0o377`, `0b1111_1111`). A radix is spelling: the literal denotes one
/// integer, which [`LitInt::base10_digits`] holds in decimal without passing
/// through a fixed-width Rust integer, so K receives that decimal value. A
/// suffix names a Rust width, which K's unbounded `Int` does not have.
pub(crate) fn is_unsuffixed_integer(integer: &LitInt) -> bool {
    integer.suffix().is_empty()
}

/// Whether an integer literal's value is zero.
pub(crate) fn is_zero(integer: &LitInt) -> bool {
    integer
        .base10_digits()
        .trim_start_matches('-')
        .bytes()
        .all(|digit| digit == b'0')
}

/// Accepts `-N`, a unary minus applied directly to an unsuffixed integer
/// literal in any radix, as one signed literal ranging from the `-` through the digits.
fn negative_integer(unary: &ExprUnary) -> Result<IntegerLiteral, SyntaxError> {
    reject_attributes(&unary.attrs, unary.span())?;
    let UnOp::Neg(minus) = unary.op else {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedTermExpression {
                reason: UNARY_MINUS,
            },
            unary.span(),
        ));
    };
    let Expr::Lit(literal) = &*unary.expr else {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedTermExpression {
                reason: UNARY_MINUS,
            },
            unary.span(),
        ));
    };
    reject_attributes(&literal.attrs, literal.span())?;
    let Lit::Int(integer) = &literal.lit else {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedTermExpression {
                reason: "only Int and Bool Rust literals are term values",
            },
            literal.span(),
        ));
    };
    if !is_unsuffixed_integer(integer) {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedTermExpression { reason: INT_SUFFIX },
            literal.span(),
        ));
    }
    if is_zero(integer) {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedTermExpression {
                reason: NEGATIVE_ZERO,
            },
            unary.span(),
        ));
    }
    Ok(IntegerLiteral::negative(
        LitInt::new(&format!("-{integer}"), minus.span),
        minus.span,
        integer.span(),
    ))
}

/// Whether `literal` is an integer literal that K reads as a Float: decimal
/// digits with a float suffix (`1f32`, `1f64`, or K's `1p24x8`).
pub(crate) fn is_float_suffixed_int(literal: &Lit) -> bool {
    let Lit::Int(integer) = literal else {
        return false;
    };
    let suffix = integer.suffix();
    (matches!(suffix, "f32" | "f64") || (suffix.starts_with('p') && suffix.contains('x')))
        && integer
            .to_string()
            .trim_start_matches('-')
            .strip_suffix(suffix)
            .is_some_and(|digits| {
                digits
                    .chars()
                    .all(|character| character.is_ascii_digit() || character == '_')
            })
}

fn float_error(error: krs_ir::float_token::FloatLiteralError, span: Span) -> SyntaxError {
    let reason = match error {
        krs_ir::float_token::FloatLiteralError::Suffix => FLOAT_SUFFIX,
        krs_ir::float_token::FloatLiteralError::PrecisionSuffix => FLOAT_PRECISION_SUFFIX,
        krs_ir::float_token::FloatLiteralError::NegatedNan => FLOAT_NEGATED_NAN,
        krs_ir::float_token::FloatLiteralError::NegatedInfinity => FLOAT_NEGATED_INFINITY,
        krs_ir::float_token::FloatLiteralError::NegatedNegInfinity => FLOAT_NEGATED_NEG_INFINITY,
        krs_ir::float_token::FloatLiteralError::Digits => FLOAT_DIGITS,
    };
    SyntaxError::new(SyntaxErrorKind::UnsupportedTermExpression { reason }, span)
}

/// The reason given for a float suffix K has no spelling for.
pub(crate) const FLOAT_SUFFIX: &str =
    "Float literal suffix must be f32, f64, or K's p<precision>x<exponent>";
/// The reason given for a `pNxM` suffix with a zero or a leading zero.
pub(crate) const FLOAT_PRECISION_SUFFIX: &str = "a p<precision>x<exponent> Float suffix takes two positive decimal numbers without leading zeros";
/// The reason given for `-f64::NAN`.
pub(crate) const FLOAT_NEGATED_NAN: &str =
    "NaN has no sign in K's token syntax; write f64::NAN or f32::NAN";
/// The reason given for `-f64::INFINITY`.
pub(crate) const FLOAT_NEGATED_INFINITY: &str =
    "a minus on INFINITY is not a Float literal; write f64::NEG_INFINITY (or f32::NEG_INFINITY)";
/// The reason given for `-f64::NEG_INFINITY`.
pub(crate) const FLOAT_NEGATED_NEG_INFINITY: &str =
    "a minus on NEG_INFINITY is not a Float literal; write f64::INFINITY (or f32::INFINITY)";
/// The reason given for an `f32::`/`f64::` path that is not one of K's constants.
pub(crate) const FLOAT_CONSTANT: &str = "the f32 and f64 constants with K Float tokens are NAN, INFINITY, and NEG_INFINITY; write other values as literals";
const FLOAT_DIGITS: &str = "Float literals must be decimal Rust float literals";

/// Reads a float literal (or a float-suffixed integer literal) as a Float token;
/// `minus` is the span of a `-` written before it. syn may already carry the
/// sign in the literal's digits (a negative literal pattern). Returns `None`
/// for a literal that is not a float.
pub(crate) fn float_literal(
    literal: &Lit,
    minus: Option<Span>,
) -> Result<Option<FloatLiteral>, SyntaxError> {
    float_literal_spanning(literal, minus, None)
}

/// [`float_literal`] with the source span of the digits when syn's literal is
/// a signed token it built itself (a negative literal pattern), whose own span
/// is not the authored one.
pub(crate) fn float_literal_spanning(
    literal: &Lit,
    minus: Option<Span>,
    digits_span: Option<Span>,
) -> Result<Option<FloatLiteral>, SyntaxError> {
    let (digits, suffix, span) = match literal {
        Lit::Float(float) => (float.base10_digits(), float.suffix(), float.span()),
        Lit::Int(integer) if is_float_suffixed_int(literal) => {
            (integer.base10_digits(), integer.suffix(), integer.span())
        }
        _ => return Ok(None),
    };
    let (signed, digits) = match digits.strip_prefix('-') {
        Some(digits) => (true, digits),
        None => (false, digits),
    };
    let negative = signed || minus.is_some();
    let span = digits_span.unwrap_or(span);
    let start = minus.unwrap_or(span);
    let token = krs_ir::float_token::from_literal(negative, digits, suffix)
        .map_err(|error| float_error(error, span))?;
    Ok(Some(FloatLiteral {
        digits: digits.replace('_', ""),
        suffix: suffix.to_owned(),
        negative,
        token,
        range: TokenRange::new(start, span),
    }))
}

/// Recognises `f32::NAME` and `f64::NAME`: `None` for any other path,
/// `Some(Err(..))` for an `f32`/`f64` name that is not one of K's constants.
pub(crate) fn float_constant_path(
    path: &Path,
) -> Option<Result<krs_ir::float_token::FloatConstant, SyntaxError>> {
    if path.segments.len() != 2 || !is_plain_path(path) {
        return None;
    }
    let width = path.segments.first()?.ident.to_string();
    krs_ir::float_token::FloatWidth::from_name(&width)?;
    let name = path.segments.last()?.ident.to_string();
    Some(
        krs_ir::float_token::FloatConstant::from_name(&name).ok_or_else(|| {
            SyntaxError::new(
                SyntaxErrorKind::UnsupportedTermExpression {
                    reason: FLOAT_CONSTANT,
                },
                path.span(),
            )
        }),
    )
}

/// The Float token of the constant `path` (`f32::NAN`, ...), negated when
/// `minus` holds the span of a `-` before it.
pub(crate) fn float_constant(
    path: &Path,
    constant: krs_ir::float_token::FloatConstant,
    minus: Option<Span>,
) -> Result<FloatLiteral, SyntaxError> {
    let width_name = path
        .segments
        .first()
        .map(|segment| segment.ident.to_string())
        .unwrap_or_default();
    let width = krs_ir::float_token::FloatWidth::from_name(&width_name)
        .expect("float_constant_path recognised the width");
    let path_range = TokenRange::for_tokens(path)?;
    let token = krs_ir::float_token::from_constant(width, constant, minus.is_some())
        .map_err(|error| float_error(error, minus.unwrap_or_else(|| path.span())))?;
    Ok(FloatLiteral {
        digits: constant.name().to_owned(),
        suffix: width.name().to_owned(),
        negative: minus.is_some(),
        token,
        range: minus.map_or(path_range, |minus| {
            TokenRange::new(minus, path_range.last())
        }),
    })
}

/// Accepts `-` applied directly to a float literal or an `f32::`/`f64::`
/// constant as one Float token; `None` when the operand is neither.
fn negative_float(unary: &ExprUnary) -> Result<Option<FloatLiteral>, SyntaxError> {
    let UnOp::Neg(minus) = unary.op else {
        return Ok(None);
    };
    match &*unary.expr {
        Expr::Lit(literal) => {
            if float_literal(&literal.lit, None).is_ok_and(|float| float.is_none()) {
                return Ok(None);
            }
            reject_attributes(&unary.attrs, unary.span())?;
            reject_attributes(&literal.attrs, literal.span())?;
            float_literal(&literal.lit, Some(minus.span))
        }
        Expr::Path(path) if path.qself.is_none() && path.path.leading_colon.is_none() => {
            let Some(constant) = float_constant_path(&path.path) else {
                return Ok(None);
            };
            reject_attributes(&unary.attrs, unary.span())?;
            reject_attributes(&path.attrs, path.span())?;
            float_constant(&path.path, constant?, Some(minus.span)).map(Some)
        }
        _ => Ok(None),
    }
}

/// The reason given for a string holding a code point above U+00FF.
pub(crate) const STRING_OUT_OF_RANGE: &str = "K 7.1.337 Strings are defined for U+0000..U+00FF only (domains.md, Strings); use Bytes for other data";

/// Accepts a string literal whose value a K `String` can hold.
pub(crate) fn string_literal(literal: &LitStr) -> Result<LitStr, SyntaxError> {
    if !literal.suffix().is_empty() {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedTermExpression {
                reason: "String literals take no suffix",
            },
            literal.span(),
        ));
    }
    if literal
        .value()
        .chars()
        .any(|character| character > krs_ir::string_token::MAX_CODE_POINT)
    {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedTermExpression {
                reason: STRING_OUT_OF_RANGE,
            },
            literal.span(),
        ));
    }
    Ok(literal.clone())
}

/// The diagnostic for a Rust literal that is not a K term value.
pub(crate) fn unsupported_literal(literal: &Lit) -> SyntaxError {
    let reason = match literal {
        Lit::Char(_) => "K has no Char sort; write \"a\"",
        Lit::ByteStr(_) | Lit::CStr(_) => "write k::bytes!(b\"..\") for a Bytes value",
        Lit::Byte(_) => "K has no byte literal; write an Int or k::bytes!(b\"..\")",
        _ => "only Int, Bool, String, and Float Rust literals are term values",
    };
    SyntaxError::new(
        SyntaxErrorKind::UnsupportedTermExpression { reason },
        literal.span(),
    )
}

fn validate_literal(literal: &ExprLit, nodes: &mut Vec<TermNode>) -> Result<TermTree, SyntaxError> {
    reject_attributes(&literal.attrs, literal.span())?;
    let literal = match &literal.lit {
        Lit::Int(integer) if is_unsuffixed_integer(integer) => {
            TermLiteral::Integer(IntegerLiteral::unsigned(integer.clone())?)
        }
        Lit::Bool(boolean) => TermLiteral::Boolean(boolean.clone()),
        Lit::Str(string) => TermLiteral::String(string_literal(string)?),
        Lit::Float(_) => {
            TermLiteral::Float(float_literal(&literal.lit, None)?.expect("a float literal"))
        }
        Lit::Int(_) if is_float_suffixed_int(&literal.lit) => {
            TermLiteral::Float(float_literal(&literal.lit, None)?.expect("a float-suffixed int"))
        }
        Lit::Int(_) => {
            return Err(SyntaxError::new(
                SyntaxErrorKind::UnsupportedTermExpression { reason: INT_SUFFIX },
                literal.span(),
            ));
        }
        other => return Err(unsupported_literal(other)),
    };
    nodes.push(TermNode::Literal(literal.clone()));
    Ok(TermTree::Literal(literal))
}

/// Keys each record field name of `tree` in preorder, into `term_keys`.
pub(crate) fn allocate_record_field_keys(
    keys: &mut KeyAllocator,
    tree: &TermTree,
    term_keys: &mut TermKeys,
    role: ProvenanceRole,
) -> Result<(), SyntaxError> {
    let mut fields = Vec::new();
    tree.record_field_names_preorder(&mut fields);
    for (index, field) in fields.iter().enumerate() {
        term_keys.set_record_field(index, keys.key(role, TokenRange::for_tokens(field)?)?);
    }
    Ok(())
}

fn is_supported_literal(literal: &ExprLit) -> bool {
    match &literal.lit {
        Lit::Bool(_) | Lit::Str(_) | Lit::Float(_) => literal.attrs.is_empty(),
        Lit::Int(_) if is_float_suffixed_int(&literal.lit) => literal.attrs.is_empty(),
        Lit::Int(integer) => literal.attrs.is_empty() && is_unsuffixed_integer(integer),
        _ => false,
    }
}

fn transparent_expression(mut expression: &Expr) -> &Expr {
    loop {
        expression = match expression {
            Expr::Paren(paren) => &paren.expr,
            Expr::Group(group) => &group.expr,
            _ => return expression,
        };
    }
}

pub(crate) fn reject_attributes(
    attributes: &[syn::Attribute],
    span: proc_macro2::Span,
) -> Result<(), SyntaxError> {
    if attributes.is_empty() {
        Ok(())
    } else {
        Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedTermExpression {
                reason: "expression attributes are not supported in term payloads",
            },
            span,
        ))
    }
}

pub(crate) fn is_term_macro(path: &Path) -> bool {
    is_plain_path(path)
        && path
            .segments
            .last()
            .is_some_and(|segment| segment.ident == "term")
}

pub(crate) fn unexpected_macro(path: &Path) -> SyntaxError {
    if crate::rule::is_bits_macro(path) {
        return crate::rule::misplaced_bit_template(path.span());
    }
    SyntaxError::new(
        SyntaxErrorKind::UnexpectedMacro {
            path: path_text(path),
        },
        path.span(),
    )
}

#[cfg(test)]
mod bytes_token_tests {
    use super::{TermExpression, TermNode, TermTree};
    use crate::{KrsSyntax, SyntaxErrorKind};
    use krs_test_support::assert_rejects;

    #[test]
    fn byte_string_macro_parses_as_one_intrinsic_token() {
        let expression = TermExpression::parse_source(r#"k::bytes!(b"\x00A\xff")"#).unwrap();
        let TermTree::BytesToken { literal } = expression.tree() else {
            panic!("bytes! must retain its intrinsic token node");
        };
        assert_eq!(literal.value(), b"\x00A\xff");
        assert!(matches!(expression.nodes(), [TermNode::BytesToken(_)]));
        assert_eq!(expression.spelling(), r#"k :: bytes ! (b"\x00A\xff")"#);
    }

    #[test]
    fn byte_string_macro_rejects_non_byte_literals() {
        assert_rejects!(
            TermExpression::parse_source(r#"k::bytes!("not bytes")"#),
            error if matches!(
                error.kind(),
                SyntaxErrorKind::RustSyntax(message) if message == "expected byte string literal"
            )
        );
    }
}

#[cfg(test)]
mod negative_literal_tests {
    use super::{INT_SUFFIX, NEGATIVE_ZERO, TermExpression, TermLiteral, TermNode, TermRootKind};
    use crate::{KrsSyntax, ProvenanceRole, SyntaxErrorKind};

    fn literals(source: &str) -> Vec<String> {
        TermExpression::parse_source(source)
            .unwrap()
            .nodes()
            .iter()
            .filter_map(|node| match node {
                TermNode::Literal(literal @ TermLiteral::Integer(_)) => Some(literal.spelling()),
                _ => None,
            })
            .collect()
    }

    #[test]
    fn a_minus_on_an_integer_literal_is_one_signed_literal() {
        assert_eq!(literals("Sgn(-1)"), ["-1"]);
        assert_eq!(literals("int::div(7, -3)"), ["7", "-3"]);
        assert_eq!(literals("Div { lhs, rhs: -1_000 }"), ["-1000"]);
        let root = TermExpression::parse_source("-42").unwrap();
        assert_eq!(root.root_kind(), TermRootKind::Literal);
        assert_eq!(literals("-42"), ["-42"]);
    }

    #[test]
    fn a_radix_is_spelling_and_the_value_is_decimal() {
        assert_eq!(
            literals("Sgn(0xFF0F, 0o17, 0b1010, 1_000, 0x_ff)"),
            ["65295", "15", "10", "1000", "255"]
        );
        assert_eq!(literals("int::add(-0x10, -0b1)"), ["-16", "-1"]);
        assert_eq!(literals("0xFF0F"), ["65295"]);
        assert_eq!(
            literals("0x1_0000_0000_0000_0000_0000_0000_0000_0000"),
            ["340282366920938463463374607431768211456"]
        );
    }

    #[test]
    fn a_suffixed_literal_is_rejected_in_every_radix() {
        for source in ["Sgn(0xFFu8)", "Sgn(0b1i64)", "Sgn(0o7usize)", "Sgn(1u32)"] {
            let error = TermExpression::parse_source(source).unwrap_err();
            assert!(
                matches!(
                    error.kind(),
                    SyntaxErrorKind::UnsupportedTermExpression { reason } if *reason == INT_SUFFIX
                ),
                "{source}: {error:?}"
            );
        }
    }

    #[test]
    fn the_literal_anchor_spans_the_sign_through_the_digits() {
        let expression = TermExpression::parse_source("Sgn(-12)").unwrap();
        let anchor = expression
            .full_provenance()
            .unwrap()
            .into_iter()
            .find(|anchor| anchor.role() == ProvenanceRole::TermLiteral)
            .unwrap();
        assert_eq!(anchor.range().start().column, 4);
        assert_eq!(anchor.range().end().column, 7);
    }

    #[test]
    fn a_minus_on_anything_but_a_literal_is_the_negation_operator() {
        for source in ["-x", "Sgn(-x)", "Sgn(-(1))", "Sgn(--1)", "Sgn(-Zero())"] {
            let term = TermExpression::parse_source(source).unwrap();
            let negations = term
                .nodes()
                .iter()
                .filter(|node| {
                    matches!(node, TermNode::ApplicationHead(path)
                        if crate::path::path_text(path) == "__operator::neg")
                })
                .count();
            assert_eq!(negations, 1, "{source}");
        }
        assert_eq!(
            TermExpression::parse_source("-x").unwrap().root_kind(),
            TermRootKind::Call
        );
        // `--1` negates the literal `-1`.
        assert_eq!(literals("Sgn(--1)"), ["-1"]);
    }

    #[test]
    fn a_malformed_signed_literal_is_rejected() {
        for (source, expected) in [
            ("Sgn(-0)", NEGATIVE_ZERO),
            ("Sgn(-0_0)", NEGATIVE_ZERO),
            ("Sgn(-1i32)", INT_SUFFIX),
            ("Sgn(-0xFFu8)", INT_SUFFIX),
            ("Sgn(-0x0)", NEGATIVE_ZERO),
        ] {
            let error = TermExpression::parse_source(source).unwrap_err();
            assert!(
                matches!(
                    error.kind(),
                    SyntaxErrorKind::UnsupportedTermExpression { reason } if *reason == expected
                ),
                "{source}: {error:?}"
            );
        }
    }
}

#[cfg(test)]
mod string_literal_tests {
    use super::{STRING_OUT_OF_RANGE, TermExpression, TermLiteral, TermNode};
    use crate::{KrsSyntax, SyntaxErrorKind};

    fn strings(source: &str) -> Vec<String> {
        TermExpression::parse_source(source)
            .unwrap()
            .nodes()
            .iter()
            .filter_map(|node| match node {
                TermNode::Literal(literal @ TermLiteral::String(_)) => Some(literal.spelling()),
                _ => None,
            })
            .collect()
    }

    #[test]
    fn string_and_raw_string_literals_are_string_tokens() {
        assert_eq!(strings(r#"Greet("world")"#), ["world"]);
        assert_eq!(
            strings(r#"string::concat("say \"hi\"", "\n\u{c1}")"#),
            ["say \"hi\"", "\n\u{c1}"]
        );
    }

    #[test]
    fn non_latin_1_char_and_byte_literals_are_rejected() {
        for (source, expected) in [
            (r#"Greet("\u{100}")"#, STRING_OUT_OF_RANGE),
            ("Greet('a')", "K has no Char sort; write \"a\""),
            (
                r#"Greet(b"ab")"#,
                "write k::bytes!(b\"..\") for a Bytes value",
            ),
        ] {
            let error = TermExpression::parse_source(source).unwrap_err();
            assert!(
                matches!(
                    error.kind(),
                    SyntaxErrorKind::UnsupportedTermExpression { reason } if *reason == expected
                ),
                "{source}: {error:?}"
            );
        }
    }
}

#[cfg(test)]
mod float_literal_tests {
    use super::{
        FLOAT_CONSTANT, FLOAT_NEGATED_INFINITY, FLOAT_NEGATED_NAN, FLOAT_NEGATED_NEG_INFINITY,
        FLOAT_PRECISION_SUFFIX, FLOAT_SUFFIX, TermExpression, TermLiteral, TermNode, TermRootKind,
    };
    use crate::{KrsSyntax, ProvenanceRole, SyntaxErrorKind};

    fn floats(source: &str) -> Vec<String> {
        TermExpression::parse_source(source)
            .unwrap()
            .nodes()
            .iter()
            .filter_map(|node| match node {
                TermNode::Literal(literal @ TermLiteral::Float(_)) => Some(literal.spelling()),
                _ => None,
            })
            .collect()
    }

    #[test]
    fn float_literals_map_to_k_tokens() {
        assert_eq!(
            floats("Floats(1.5, 1.5f64, 0.1f32, 1f32, 1.0p113x15, -0.0, -2.5e-3, 1_000.25, 2f64)"),
            [
                "1.5",
                "1.5d",
                "0.1f",
                "1f",
                "1.0p113x15",
                "-0.0",
                "-2.5e-3",
                "1000.25",
                "2d"
            ]
        );
        let root = TermExpression::parse_source("-0.5").unwrap();
        assert_eq!(root.root_kind(), TermRootKind::Literal);
        assert_eq!(floats("-0.5"), ["-0.5"]);
    }

    #[test]
    fn float_constant_paths_are_tokens() {
        assert_eq!(
            floats(
                "float::add(f64::NAN, f32::NAN, f64::INFINITY, f32::INFINITY, f64::NEG_INFINITY, f32::NEG_INFINITY)"
            ),
            [
                "NaN",
                "NaNf",
                "Infinity",
                "Infinityf",
                "-Infinity",
                "-Infinityf"
            ]
        );
        let root = TermExpression::parse_source("f64::NAN").unwrap();
        assert_eq!(root.root_kind(), TermRootKind::Literal);
        assert!(root.symbols().is_empty());
    }

    #[test]
    fn the_float_anchor_spans_the_sign_through_the_literal() {
        let expression = TermExpression::parse_source("Neg(-1.25f32)").unwrap();
        let anchor = expression
            .full_provenance()
            .unwrap()
            .into_iter()
            .find(|anchor| anchor.role() == ProvenanceRole::TermLiteral)
            .unwrap();
        assert_eq!(anchor.range().start().column, 4);
        assert_eq!(anchor.range().end().column, 12);
    }

    #[test]
    fn unsupported_floats_are_rejected() {
        for (source, expected) in [
            ("F(1.0f16)", FLOAT_SUFFIX),
            ("F(1.0u8)", FLOAT_SUFFIX),
            ("F(1.0P24X8)", FLOAT_SUFFIX),
            ("F(1.0p0x8)", FLOAT_PRECISION_SUFFIX),
            ("F(1.0p24x08)", FLOAT_PRECISION_SUFFIX),
            ("F(-f64::NAN)", FLOAT_NEGATED_NAN),
            ("F(-f32::NAN)", FLOAT_NEGATED_NAN),
            ("F(-f64::INFINITY)", FLOAT_NEGATED_INFINITY),
            ("F(-f64::NEG_INFINITY)", FLOAT_NEGATED_NEG_INFINITY),
            ("F(f64::MAX)", FLOAT_CONSTANT),
            ("F(f32::EPSILON)", FLOAT_CONSTANT),
        ] {
            let error = TermExpression::parse_source(source).unwrap_err();
            assert!(
                matches!(
                    error.kind(),
                    SyntaxErrorKind::UnsupportedTermExpression { reason } if *reason == expected
                ),
                "{source}: {error:?}"
            );
        }
    }
}
