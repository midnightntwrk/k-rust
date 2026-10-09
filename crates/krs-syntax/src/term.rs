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

use crate::parse::{KrsSyntax, checked_ordinal};
use crate::path::{is_plain_path, path_text};
use crate::{ProvenanceAnchor, ProvenanceRole, SyntaxError, SyntaxErrorKind, TokenRange};

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

/// An unsuffixed decimal Rust integer literal, optionally negative (`-1`).
///
/// The sign belongs to the literal: a negative literal's token carries it, so
/// its spelling is the signed K `Int` token, and its source range runs from the
/// `-` through the digits.
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
    /// Unsuffixed decimal Rust integer literal, optionally negative (`-1`).
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

    fn range(&self) -> Result<TokenRange, SyntaxError> {
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
    /// Integer or Boolean literal.
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
            | Self::MatchesWildcard(_) => None,
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
            | Self::MatchesWildcard(_) => None,
        }
    }

    pub(crate) fn range(&self) -> Result<TokenRange, SyntaxError> {
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
            | Self::MatchesWildcard(range) => Ok(*range),
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
}

/// One compiler-owned complete parent-cell term.
#[derive(Clone, Debug)]
pub struct CellTerm {
    pub(crate) range: TokenRange,
    pub(crate) owner: Path,
    pub(crate) fields: Vec<TermNamedArgument>,
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
    /// Integer or Boolean literal.
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
            | Self::Matches { .. } => None,
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
            | Self::Matches { .. } => None,
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
            | Self::Matches { .. } => None,
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
            | Self::Matches { .. } => None,
        }
    }

    pub(crate) fn record_field_names_preorder(&self, output: &mut Vec<syn::Ident>) {
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

    pub(crate) fn wildcard_ranges_preorder(&self, output: &mut Vec<TokenRange>) {
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

/// A validated Rust-expression term in the deliberately small term grammar.
///
/// Accepted nodes are plain paths, named calls, named record construction,
/// parentheses/groups, and Rust literals below a named root. No operator,
/// method, closure, control-flow, assignment, macro, update-rest, or arbitrary
/// block expression is silently retained.
#[derive(Clone, Debug)]
pub struct TermExpression {
    expression: TermSource,
    root_kind: TermRootKind,
    symbols: Vec<TermSymbol>,
    nodes: Vec<TermNode>,
    tree: TermTree,
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
        expression: Expr,
        context: TermExpressionContext,
    ) -> Result<Self, SyntaxError> {
        let root = transparent_expression(&expression);
        let root_kind = match root {
            Expr::Path(path) if float_constant_path(&path.path).is_some() => {
                TermRootKind::Literal
            }
            Expr::Path(_) => TermRootKind::Named,
            Expr::Call(_) => TermRootKind::Call,
            Expr::Struct(_) => TermRootKind::Record,
            Expr::Lit(literal) if is_supported_literal(literal) => TermRootKind::Literal,
            // `validate_expression` reports a minus on anything but a numeric literal.
            Expr::Unary(ExprUnary {
                op: UnOp::Neg(_), ..
            }) => TermRootKind::Literal,
            Expr::Infer(_) if context == TermExpressionContext::Pattern => TermRootKind::Wildcard,
            Expr::Binary(binary) if matches!(binary.op, syn::BinOp::BitOr(_)) => {
                return Err(pattern_or_error(
                    PATTERN_OR_OUTSIDE_LHS.to_owned(),
                    binary.op.span(),
                ));
            }
            Expr::Macro(value) => special_macro_kind(&value.mac.path)
                .ok_or_else(|| {
                    SyntaxError::new(
                        SyntaxErrorKind::UnsupportedTermExpression {
                            reason: "the root must be a named path/call/record or an Int/Bool literal",
                        },
                        value.span(),
                    )
                })?
                .root_kind(),
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
        Ok(Self {
            expression: TermSource::Expression(expression),
            root_kind,
            symbols,
            nodes,
            tree,
        })
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
        let signs = crate::rule::NegativeLiteralSpans::scan(tokens.clone());
        let source = tokens.clone();
        let pattern = match Pat::parse_multi.parse2(tokens.clone()) {
            Ok(pattern) => pattern,
            // A form that is no Rust pattern but a term expression the
            // grammar rejects (such as `-f64::INFINITY`) keeps the
            // expression grammar's specific reason.
            Err(error) => {
                if let Ok(expression) = syn::parse2::<Expr>(tokens)
                    && let Err(specific) = Self::from_expression(expression)
                {
                    return Err(specific);
                }
                return Err(error.into());
            }
        };
        Self::from_pattern(pattern, source, signs)
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
        mut signs: crate::rule::NegativeLiteralSpans,
    ) -> Result<Self, SyntaxError> {
        let root_kind = pattern_root_kind(&pattern)?;
        let mut symbols = Vec::new();
        let mut nodes = Vec::new();
        let tree = validate_pattern(&pattern, &mut signs, &mut symbols, &mut nodes)?;
        Ok(Self {
            expression: TermSource::Pattern { pattern, tokens },
            root_kind,
            symbols,
            nodes,
            tree,
        })
    }

    /// Returns the original span-preserving Rust expression or pattern.
    #[must_use]
    pub const fn expression(&self) -> &TermSource {
        &self.expression
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

    /// Returns standalone term-payload provenance anchors.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only if a parsed Rust node emits no leaves.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        self.provenance_with_roles(ProvenanceRole::TermPayload, ProvenanceRole::TermPath)
    }

    /// Returns payload plus typed application/reference/literal anchors for
    /// protocol-v6 lowering. The compact path catalog remains available via
    /// [`Self::provenance`].
    ///
    /// # Errors
    ///
    /// Returns an endpoint or occurrence-overflow error.
    pub fn full_provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        self.full_provenance_with_roles(
            ProvenanceRole::TermPayload,
            ProvenanceRole::TermApplicationHead,
            ProvenanceRole::TermReference,
            ProvenanceRole::TermLiteral,
            ProvenanceRole::TermRecordFieldName,
        )
    }

    pub(crate) fn full_provenance_with_roles(
        &self,
        payload_role: ProvenanceRole,
        application_role: ProvenanceRole,
        reference_role: ProvenanceRole,
        literal_role: ProvenanceRole,
        record_field_role: ProvenanceRole,
    ) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = vec![ProvenanceAnchor::new(
            payload_role,
            0,
            TokenRange::for_tokens(&self.expression)?,
        )];
        let mut application_ordinal = 0_usize;
        let mut reference_ordinal = 0_usize;
        let mut literal_ordinal = 0_usize;
        for node in &self.nodes {
            let (role, ordinal) = match node {
                TermNode::ApplicationHead(_) => {
                    let ordinal = application_ordinal;
                    application_ordinal += 1;
                    (application_role, ordinal)
                }
                TermNode::Reference(_) => {
                    let ordinal = reference_ordinal;
                    reference_ordinal += 1;
                    (reference_role, ordinal)
                }
                TermNode::Literal(_) => {
                    let ordinal = literal_ordinal;
                    literal_ordinal += 1;
                    (literal_role, ordinal)
                }
                TermNode::IdToken(_)
                | TermNode::BytesToken(_)
                | TermNode::Anonymous { .. }
                | TermNode::OrBool(_)
                | TermNode::Lexeme { .. }
                | TermNode::SortTest { .. }
                | TermNode::As { .. }
                | TermNode::Or(_)
                | TermNode::Matches(_)
                | TermNode::MatchesWildcard(_) => {
                    continue;
                }
            };
            let range = node.range()?;
            anchors.push(ProvenanceAnchor::new(
                role,
                checked_ordinal(ordinal, role, range.first())?,
                range,
            ));
        }
        push_record_field_anchors(&mut anchors, &self.tree, record_field_role)?;
        Ok(anchors)
    }

    pub(crate) fn provenance_with_roles(
        &self,
        payload_role: ProvenanceRole,
        path_role: ProvenanceRole,
    ) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = Vec::with_capacity(self.symbols.len() + 1);
        anchors.push(ProvenanceAnchor::new(
            payload_role,
            0,
            TokenRange::for_tokens(&self.expression)?,
        ));
        for (ordinal, symbol) in self.symbols.iter().enumerate() {
            let ordinal = checked_ordinal(ordinal, path_role, symbol.path.span())?;
            anchors.push(ProvenanceAnchor::new(
                path_role,
                ordinal,
                TokenRange::for_tokens(&symbol.path)?,
            ));
        }
        Ok(anchors)
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
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        reject_pattern_alias(&tokens)?;
        let expression = syn::parse2::<Expr>(tokens)?;
        Self::from_expression(expression)
    }
}

/// The reason given for `name @ pattern` outside a left-hand side.
pub(crate) const PATTERN_AS_OUTSIDE_LHS: &str = "`name @ pattern` binds only on a left-hand side (K's #as is LHS-only); refer to the name without `@` here";

/// Rejects `name @ pattern` in tokens that are parsed as an expression (a
/// result, condition, or initializer), which syn would otherwise report as
/// an unexpected token. Tokens inside nested macro invocations are skipped:
/// a nested `term!` or `cells!` checks its own payload.
///
/// # Errors
///
/// Returns [`SyntaxErrorKind::InvalidPatternAs`] at the first `@`.
pub(crate) fn reject_pattern_alias(tokens: &TokenStream) -> Result<(), SyntaxError> {
    match find_pattern_alias(tokens) {
        Some(span) => Err(SyntaxError::new(
            SyntaxErrorKind::InvalidPatternAs {
                reason: PATTERN_AS_OUTSIDE_LHS.to_owned(),
            },
            span,
        )),
        None => Ok(()),
    }
}

/// Rejects `name @ pattern` in the body (the result) of the `fn` item in
/// `tokens`, before syn reports it as an unexpected token.
///
/// # Errors
///
/// Returns [`SyntaxErrorKind::InvalidPatternAs`] at the first `@`.
pub(crate) fn reject_pattern_alias_in_fn_body(tokens: &TokenStream) -> Result<(), SyntaxError> {
    let body = tokens.clone().into_iter().last();
    match body {
        Some(proc_macro2::TokenTree::Group(group))
            if group.delimiter() == proc_macro2::Delimiter::Brace =>
        {
            reject_pattern_alias(&group.stream())
        }
        _ => Ok(()),
    }
}

fn find_pattern_alias(tokens: &TokenStream) -> Option<Span> {
    let tokens = tokens.clone().into_iter().collect::<Vec<_>>();
    for (index, token) in tokens.iter().enumerate() {
        match token {
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
        Pat::TupleStruct(_) => TermRootKind::Call,
        Pat::Struct(_) => TermRootKind::Record,
        Pat::Lit(_) => TermRootKind::Literal,
        Pat::Wild(_) => TermRootKind::Wildcard,
        Pat::Or(or) => match or.cases.first() {
            Some(first) => return pattern_root_kind(first),
            None => return Err(unsupported_pattern_form(pattern)),
        },
        Pat::Macro(value) => special_macro_kind(&value.mac.path)
            .ok_or_else(|| {
                SyntaxError::new(
                    SyntaxErrorKind::UnsupportedTermExpression {
                        reason: "the root must be a named path/call/record or an Int/Bool literal",
                    },
                    value.span(),
                )
            })?
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

fn pattern_or_error(reason: String, span: Span) -> SyntaxError {
    SyntaxError::new(SyntaxErrorKind::InvalidPatternOr { reason }, span)
}

/// The reason given for `|` in a result or condition.
pub(crate) const PATTERN_OR_OUTSIDE_LHS: &str =
    "`|` is a pattern alternative; for Bool disjunction use bool::or or k::or_bool!";

/// The reason given for `|` next to a `..` remainder.
pub(crate) const PATTERN_OR_REMAINDER: &str = "or-patterns combine terms, not remainders";

/// The variables a term pattern's nodes bind: every bare single-identifier
/// reference and every `name @ pattern` alias, in preorder.
fn pattern_binders(nodes: &[TermNode]) -> Vec<syn::Ident> {
    nodes
        .iter()
        .filter_map(|node| match node {
            TermNode::Reference(path) if path.leading_colon.is_none() => path.get_ident().cloned(),
            TermNode::As { binding, .. } => Some(binding.clone()),
            _ => None,
        })
        .collect()
}

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

/// The pattern twin of [`validate_expression`] in pattern context.
fn validate_pattern(
    pattern: &Pat,
    signs: &mut crate::rule::NegativeLiteralSpans,
    symbols: &mut Vec<TermSymbol>,
    nodes: &mut Vec<TermNode>,
) -> Result<TermTree, SyntaxError> {
    match pattern {
        Pat::Ident(identifier) => {
            if let Some((_, subpattern)) = &identifier.subpat {
                return validate_pattern_as(identifier, subpattern, nodes, |subpattern, nodes| {
                    validate_pattern(subpattern, signs, symbols, nodes)
                });
            }
            reject_attributes(&identifier.attrs, identifier.span())?;
            if identifier.by_ref.is_some() || identifier.mutability.is_some() {
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
        Pat::Struct(record) => validate_struct_pattern(record, signs, symbols, nodes),
        Pat::Paren(paren) => {
            reject_attributes(&paren.attrs, paren.span())?;
            validate_pattern(&paren.pat, signs, symbols, nodes)
        }
        Pat::Or(or) => {
            let (tree, _) = validate_pattern_or(or, nodes, |alternative, nodes| {
                let start = nodes.len();
                let tree = validate_pattern(alternative, signs, symbols, nodes)?;
                Ok((tree, pattern_binders(&nodes[start..])))
            })?;
            Ok(tree)
        }
        Pat::Lit(literal) => {
            let literal = crate::rule::validate_pattern_literal(literal, nodes, signs)?;
            Ok(TermTree::Literal(literal))
        }
        Pat::Wild(wildcard) => {
            reject_attributes(&wildcard.attrs, wildcard.span())?;
            Ok(TermTree::Wildcard(TokenRange::for_tokens(wildcard)?))
        }
        Pat::Macro(value)
            if matches!(
                special_macro_kind(&value.mac.path),
                Some(TermMacroKind::Fragment)
            ) =>
        {
            validate_cell_pattern(value, signs, symbols, nodes)
        }
        Pat::Macro(value) => {
            validate_special_macro(value, TermExpressionContext::Pattern, symbols, nodes)
        }
        other => Err(unsupported_pattern_form(other)),
    }
}

fn validate_tuple_struct_pattern(
    tuple: &PatTupleStruct,
    signs: &mut crate::rule::NegativeLiteralSpans,
    symbols: &mut Vec<TermSymbol>,
    nodes: &mut Vec<TermNode>,
) -> Result<TermTree, SyntaxError> {
    reject_attributes(&tuple.attrs, tuple.span())?;
    if tuple.qself.is_some() || !is_plain_path(&tuple.path) {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedPath,
            tuple.path.span(),
        ));
    }
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
        head: tuple.path.clone(),
        arguments: TermArguments::Positional(arguments),
    }))
}

fn validate_struct_pattern(
    record: &PatStruct,
    signs: &mut crate::rule::NegativeLiteralSpans,
    symbols: &mut Vec<TermSymbol>,
    nodes: &mut Vec<TermNode>,
) -> Result<TermTree, SyntaxError> {
    reject_attributes(&record.attrs, record.span())?;
    if record.qself.is_some() || !is_plain_path(&record.path) {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedPath,
            record.path.span(),
        ));
    }
    if let Some(rest) = &record.rest {
        reject_attributes(&rest.attrs, rest.span())?;
    }
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
        head: record.path.clone(),
        arguments: TermArguments::Named(arguments),
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

fn validate_expression(
    expression: &Expr,
    context: TermExpressionContext,
    symbols: &mut Vec<TermSymbol>,
    nodes: &mut Vec<TermNode>,
) -> Result<TermTree, SyntaxError> {
    match expression {
        Expr::Path(path) => validate_path_expression(path, symbols, nodes),
        Expr::Call(call) => validate_call(call, context, symbols, nodes),
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
        // `A | B` is K's #Or only in a pattern; a result or condition has no
        // alternatives (KF-030).
        Expr::Binary(binary) if matches!(binary.op, syn::BinOp::BitOr(_)) => Err(pattern_or_error(
            PATTERN_OR_OUTSIDE_LHS.to_owned(),
            binary.op.span(),
        )),
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
}

impl TermMacroKind {
    const fn root_kind(self) -> TermRootKind {
        match self {
            Self::OrBool | Self::Fragment | Self::Is | Self::Project | Self::Matches => {
                TermRootKind::Call
            }
            Self::Id | Self::Bytes | Self::Anonymous | Self::Lexeme => TermRootKind::Literal,
        }
    }
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
            let literal: LitStr = syn::parse2(value.mac.tokens.clone())?;
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
            let literal: LitByteStr = syn::parse2(value.mac.tokens.clone())?;
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
            let (sort, spelling) = parser.parse2(value.mac.tokens.clone())?;
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
        Some(TermMacroKind::Matches) => {
            if context == TermExpressionContext::Pattern {
                return Err(matches_error(
                    MATCHES_IN_PATTERN.to_owned(),
                    value.mac.path.span(),
                ));
            }
            validate_matches(value, symbols, nodes)
        }
        None => Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedTermExpression {
                reason: "macros are not terms unless they are compiler-owned `id!`, `anonymous!`, `lexeme!`, `is!`, `project!`, `matches!`, or `or_bool!` islands",
            },
            value.span(),
        )),
    }
}

/// The reason given for std's bare `matches!` in a term.
pub(crate) const STD_MATCHES: &str =
    "did you mean `k::matches!`? std's matches! tests a host value";

/// The reason given for `k::matches!` in a pattern.
pub(crate) const MATCHES_IN_PATTERN: &str = "`k::matches!` is a Bool test (K's :=K); it cannot appear on a left-hand side or inside a pattern";

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

/// Whether `path` names `k::matches!`.
pub(crate) fn is_matches_macro(path: &Path) -> bool {
    is_plain_path(path)
        && path.segments.len() > 1
        && path
            .segments
            .last()
            .is_some_and(|segment| segment.ident == "matches")
}

/// The error for `k::matches!` (or std's `matches!`) in a pattern position,
/// at the macro's name.
pub(crate) fn matched_matches(path: &Path) -> SyntaxError {
    let reason = if is_std_matches(path) {
        STD_MATCHES
    } else {
        MATCHES_IN_PATTERN
    };
    matches_error(reason.to_owned(), path.span())
}

/// Splits the arguments of `k::matches!(subject, pattern)` into the subject
/// expression and the pattern tokens.
///
/// # Errors
///
/// Rejects anything but one term expression, a comma, and a pattern without
/// an `if` guard.
pub fn parse_matches_arguments(tokens: TokenStream) -> Result<(Expr, TokenStream), SyntaxError> {
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

/// The local binders of a `k::matches!` pattern (BIND-1), in first-occurrence
/// order: every `name @ ..` alias and every unqualified single-identifier
/// reference below the root (a bare root path is a unit constructor, as in a
/// rule subject).
fn matches_binders(pattern: &TermTree) -> Vec<syn::Ident> {
    fn walk(tree: &TermTree, root: bool, output: &mut Vec<syn::Ident>) {
        let mut push = |ident: &syn::Ident| {
            if !output.contains(ident) {
                output.push(ident.clone());
            }
        };
        match tree {
            TermTree::Reference(path) if !root && path.leading_colon.is_none() => {
                if let Some(ident) = path.get_ident() {
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
            TermTree::Reference(_)
            | TermTree::Literal(_)
            | TermTree::Wildcard(_)
            | TermTree::IdToken { .. }
            | TermTree::BytesToken { .. }
            | TermTree::Anonymous { .. }
            | TermTree::Lexeme { .. } => {}
        }
    }
    let mut output = Vec::new();
    walk(pattern, true, &mut output);
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
    let binders = matches_binders(&pattern);
    Ok(TermTree::Matches {
        range,
        subject: Box::new(subject),
        pattern: Box::new(pattern),
        binders,
    })
}

/// Appends the `matches` anchor of every `k::matches!` node and the
/// `matches_wildcard` anchor of every `_` in a `k::matches!` pattern,
/// numbering each role from its ordinal. Like lexeme roles, both are
/// side-neutral: a sentence numbers them once, in the order it expands.
///
/// # Errors
///
/// Returns an occurrence-overflow error.
pub(crate) fn push_matches_anchors(
    anchors: &mut Vec<ProvenanceAnchor>,
    nodes: &[TermNode],
    matches: &mut usize,
    wildcards: &mut usize,
) -> Result<(), SyntaxError> {
    for node in nodes {
        let (role, ordinal, range) = match node {
            TermNode::Matches(range) => (ProvenanceRole::Matches, &mut *matches, range),
            TermNode::MatchesWildcard(range) => {
                (ProvenanceRole::MatchesWildcard, &mut *wildcards, range)
            }
            _ => continue,
        };
        let current = checked_ordinal(*ordinal, role, range.first())?;
        anchors.push(ProvenanceAnchor::new(role, current, *range));
        *ordinal += 1;
    }
    Ok(())
}

/// Appends the `lexeme_sort` and `lexeme_text` anchors of every
/// `k::lexeme!` node in `nodes`, numbering them from `*ordinal`.
///
/// Lexeme roles are side-neutral, so one sentence numbers its lexemes once,
/// across its subject, result, and conditions in that order.
///
/// # Errors
///
/// Returns an endpoint or occurrence-overflow error.
pub(crate) fn push_lexeme_anchors(
    anchors: &mut Vec<ProvenanceAnchor>,
    nodes: &[TermNode],
    ordinal: &mut usize,
) -> Result<(), SyntaxError> {
    for node in nodes {
        if let TermNode::Lexeme { sort, text } = node {
            let current = checked_ordinal(*ordinal, ProvenanceRole::LexemeText, text.span())?;
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::LexemeSort,
                current,
                TokenRange::for_tokens(sort)?,
            ));
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::LexemeText,
                current,
                TokenRange::for_tokens(text)?,
            ));
            *ordinal += 1;
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

/// Appends the `sort_test` and `sort_test_sort` anchors of every `k::is!`
/// and `k::project!` node in `nodes`, numbering them from `*ordinal`.
///
/// Like lexeme roles, sort-test roles are side-neutral, so one sentence
/// numbers its sort tests once, across its subject, result, and conditions in
/// that order.
///
/// # Errors
///
/// Returns an endpoint or occurrence-overflow error.
pub(crate) fn push_sort_test_anchors(
    anchors: &mut Vec<ProvenanceAnchor>,
    nodes: &[TermNode],
    ordinal: &mut usize,
) -> Result<(), SyntaxError> {
    for node in nodes {
        if let TermNode::SortTest { range, sort } = node {
            let current = checked_ordinal(*ordinal, ProvenanceRole::SortTest, range.first())?;
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::SortTest,
                current,
                *range,
            ));
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::SortTestSort,
                current,
                TokenRange::for_tokens(sort)?,
            ));
            *ordinal += 1;
        }
    }
    Ok(())
}

/// Appends the `pattern_as` and `pattern_as_binding` anchors of every
/// `name @ pattern` node in `nodes`, numbering them from `*ordinal`. A
/// sentence numbers its aliases once, in the order its left-hand side
/// expands.
///
/// # Errors
///
/// Returns an endpoint or occurrence-overflow error.
pub(crate) fn push_pattern_as_anchors(
    anchors: &mut Vec<ProvenanceAnchor>,
    nodes: &[TermNode],
    ordinal: &mut usize,
) -> Result<(), SyntaxError> {
    for node in nodes {
        if let TermNode::As { binding, range } = node {
            let current = checked_ordinal(*ordinal, ProvenanceRole::PatternAs, range.first())?;
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::PatternAs,
                current,
                *range,
            ));
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::PatternAsBinding,
                current,
                TokenRange::for_tokens(binding)?,
            ));
            *ordinal += 1;
        }
    }
    Ok(())
}

/// Appends the `pattern_or` anchor of every `A | B` node in `nodes`,
/// numbering them from `*ordinal`. A sentence numbers its or-patterns once,
/// in the order its left-hand side expands.
///
/// # Errors
///
/// Returns an occurrence-overflow error.
pub(crate) fn push_pattern_or_anchors(
    anchors: &mut Vec<ProvenanceAnchor>,
    nodes: &[TermNode],
    ordinal: &mut usize,
) -> Result<(), SyntaxError> {
    for node in nodes {
        if let TermNode::Or(range) = node {
            let current = checked_ordinal(*ordinal, ProvenanceRole::PatternOr, range.first())?;
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::PatternOr,
                current,
                *range,
            ));
            *ordinal += 1;
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
    let record: ExprStruct = syn::parse2(value.mac.tokens.clone())?;
    reject_attributes(&record.attrs, record.span())?;
    if record.qself.is_some() || !is_plain_path(&record.path) {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedPath,
            record.path.span(),
        ));
    }
    if let Some(rest) = &record.rest {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedTermExpression {
                reason: "complete cell terms do not admit record update/rest syntax",
            },
            rest.span(),
        ));
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
    if fields.is_empty() {
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
    let Pat::Struct(record) = Pat::parse_multi.parse2(value.mac.tokens.clone())? else {
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
    if let Some(rest) = &record.rest {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedTermExpression {
                reason: "complete cell terms do not admit record update/rest syntax",
            },
            rest.span(),
        ));
    }
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
    if fields.is_empty() {
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

fn validate_call(
    call: &ExprCall,
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
    if head.qself.is_some() || !head.attrs.is_empty() || !is_plain_path(&head.path) {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedPath,
            head.span(),
        ));
    }
    symbols.push(TermSymbol {
        path: head.path.clone(),
        kind: TermSymbolKind::ApplicationHead,
    });
    nodes.push(TermNode::ApplicationHead(head.path.clone()));
    let mut arguments = Vec::with_capacity(call.args.len());
    for argument in &call.args {
        arguments.push(validate_expression(argument, context, symbols, nodes)?);
    }
    Ok(TermTree::Application(TermApplication {
        head: head.path.clone(),
        arguments: TermArguments::Positional(arguments),
    }))
}

fn validate_record(
    record: &ExprStruct,
    context: TermExpressionContext,
    symbols: &mut Vec<TermSymbol>,
    nodes: &mut Vec<TermNode>,
) -> Result<TermTree, SyntaxError> {
    reject_attributes(&record.attrs, record.span())?;
    if record.qself.is_some() || !is_plain_path(&record.path) {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedPath,
            record.path.span(),
        ));
    }
    if let Some(rest) = &record.rest {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedTermExpression {
                reason: "record update/rest syntax is not supported in term construction",
            },
            rest.span(),
        ));
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
    Ok(TermTree::Application(TermApplication {
        head: record.path.clone(),
        arguments: TermArguments::Named(arguments),
    }))
}

/// The reason given for a unary minus that is not part of an Int literal.
pub(crate) const UNARY_MINUS: &str =
    "unary minus is part of a literal only; K has no unary minus on Int, write int::sub(0, x)";

/// The reason given for `-0`, which is not a canonical K `Int` token.
pub(crate) const NEGATIVE_ZERO: &str = "`-0` is not an Int literal; write 0";

/// Whether an integer literal is unsuffixed and written in decimal digits and `_`.
pub(crate) fn is_unsuffixed_decimal(integer: &LitInt) -> bool {
    integer.suffix().is_empty()
        && integer
            .to_string()
            .trim_start_matches('-')
            .chars()
            .all(|character| character.is_ascii_digit() || character == '_')
}

/// Whether an integer literal's value is zero.
pub(crate) fn is_zero(integer: &LitInt) -> bool {
    integer
        .base10_digits()
        .trim_start_matches('-')
        .bytes()
        .all(|digit| digit == b'0')
}

/// Accepts `-N`, a unary minus applied directly to an unsuffixed decimal integer
/// literal, as one signed literal ranging from the `-` through the digits.
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
    if !is_unsuffixed_decimal(integer) {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedTermExpression {
                reason: "Int literals must be unsuffixed decimal Rust integers",
            },
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
        Lit::Int(integer) if is_unsuffixed_decimal(integer) => {
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
                SyntaxErrorKind::UnsupportedTermExpression {
                    reason: "Int literals must be unsuffixed decimal Rust integers",
                },
                literal.span(),
            ));
        }
        other => return Err(unsupported_literal(other)),
    };
    nodes.push(TermNode::Literal(literal.clone()));
    Ok(TermTree::Literal(literal))
}

pub(crate) fn push_record_field_anchors(
    anchors: &mut Vec<ProvenanceAnchor>,
    tree: &TermTree,
    role: ProvenanceRole,
) -> Result<(), SyntaxError> {
    let mut fields = Vec::new();
    tree.record_field_names_preorder(&mut fields);
    for (ordinal, field) in fields.iter().enumerate() {
        anchors.push(ProvenanceAnchor::new(
            role,
            checked_ordinal(ordinal, role, field.span())?,
            TokenRange::for_tokens(field)?,
        ));
    }
    Ok(())
}

fn is_supported_literal(literal: &ExprLit) -> bool {
    match &literal.lit {
        Lit::Bool(_) | Lit::Str(_) | Lit::Float(_) => literal.attrs.is_empty(),
        Lit::Int(_) if is_float_suffixed_int(&literal.lit) => literal.attrs.is_empty(),
        Lit::Int(integer) => literal.attrs.is_empty() && is_unsuffixed_decimal(integer),
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

fn reject_attributes(
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

/// Whether `path` names `k::is!` or `k::project!`, which may be a whole
/// result term but are never matched.
pub(crate) fn is_sort_test_macro(path: &Path) -> bool {
    is_plain_path(path)
        && path
            .segments
            .last()
            .is_some_and(|segment| segment.ident == "is" || segment.ident == "project")
}

/// The error for `k::is!` or `k::project!` in a pattern position, at the
/// macro's name.
pub(crate) fn matched_sort_test(path: &Path) -> SyntaxError {
    let span = path
        .segments
        .last()
        .map_or_else(|| path.span(), |segment| segment.ident.span());
    SyntaxError::new(
        SyntaxErrorKind::UnsupportedTermExpression {
            reason: "`k::is!` and `k::project!` are function calls and cannot be matched; restrict the binder with a typed parameter or `where x: S`",
        },
        span,
    )
}

pub(crate) fn unexpected_macro(path: &Path) -> SyntaxError {
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
    use super::{NEGATIVE_ZERO, TermExpression, TermLiteral, TermNode, TermRootKind, UNARY_MINUS};
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
    fn a_minus_on_anything_else_is_rejected() {
        for (source, expected) in [
            ("-x", UNARY_MINUS),
            ("Sgn(-x)", UNARY_MINUS),
            ("Sgn(-(1))", UNARY_MINUS),
            ("Sgn(--1)", UNARY_MINUS),
            ("Sgn(-Zero())", UNARY_MINUS),
            ("Sgn(-0)", NEGATIVE_ZERO),
            ("Sgn(-0_0)", NEGATIVE_ZERO),
            (
                "Sgn(-1i32)",
                "Int literals must be unsuffixed decimal Rust integers",
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
