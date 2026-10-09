use std::error::Error;
use std::fmt;

use krs_diagnostic::{Code, Diagnostic, Location, ToDiagnostic, codes};
use proc_macro2::Span;

use crate::SourceRange;

/// Machine-readable category for a rejected syntax shape.
#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum SyntaxErrorKind {
    /// An authored binder contained the generated-identity marker.
    ReservedBinder,
    /// Rust token parsing failed before KRS shape validation could finish.
    RustSyntax(String),
    /// An attribute which takes no arguments received a payload.
    UnexpectedAttributePayload {
        /// Attribute whose payload must be empty.
        attribute: &'static str,
    },
    /// A keyed attribute argument is not part of the attribute grammar.
    UnknownArgument {
        /// Rejected argument name.
        name: String,
    },
    /// A keyed attribute argument occurred more than once.
    DuplicateArgument {
        /// Repeated argument name.
        name: &'static str,
    },
    /// A required keyed attribute argument was absent.
    MissingArgument {
        /// Missing argument name.
        name: &'static str,
    },
    /// A keyed argument had the wrong Rust AST shape.
    InvalidArgumentValue {
        /// Argument whose value was invalid.
        name: &'static str,
        /// Expected source shape.
        expected: &'static str,
    },
    /// A Rust path uses generics or another form outside the plain-path subset.
    UnsupportedPath,
    /// A `sort` trait was not a non-generic, safe, empty marker trait.
    UnsupportedSortDeclaration {
        /// Specific marker-trait restriction.
        reason: &'static str,
    },
    /// A constructor item was not a nongeneric unit or named-field struct.
    UnsupportedConstructorDeclaration {
        /// Specific constructor-shape restriction.
        reason: &'static str,
    },
    /// A closed enum constructor family was outside the supported Rust enum shape.
    UnsupportedEnumConstructorDeclaration {
        /// Specific closed-enum restriction.
        reason: &'static str,
    },
    /// A token newtype was outside the closed token declaration shape.
    UnsupportedTokenDeclaration {
        /// Specific token-newtype restriction.
        reason: &'static str,
    },
    /// A subsort implementation was outside the explicit subsort impl shape.
    UnsupportedSubsortDeclaration {
        /// Specific impl restriction.
        reason: &'static str,
    },
    /// A checked syntax or bracket template was malformed.
    InvalidSyntaxTemplate {
        /// Specific template restriction.
        reason: &'static str,
    },
    /// A checked syntax template named an unknown constructor field.
    UnknownTemplateField {
        /// Unknown placeholder spelling.
        name: String,
    },
    /// A checked syntax template omitted or repeated a constructor field.
    InvalidTemplateFieldOccurrence {
        /// Responsible field spelling.
        name: String,
        /// Required occurrence count.
        expected: u32,
        /// Actual occurrence count.
        actual: u32,
    },
    /// Token regular-expression text was malformed.
    InvalidTokenRegex {
        /// Stable reason for rejection.
        reason: &'static str,
    },
    /// Structured unparse format text was malformed for its production.
    InvalidFormat {
        /// Stable reason for rejection.
        reason: &'static str,
    },
    /// Production colour metadata was malformed or does not match the printed terminals.
    InvalidColor {
        /// Stable reason for rejection.
        reason: &'static str,
    },
    /// Strictness metadata was empty, repeated a field, or named an unknown field.
    InvalidStrictness {
        /// Stable reason for rejection.
        reason: &'static str,
    },
    /// A precedence or associativity macro payload was malformed.
    InvalidGrammarMacro {
        /// Stable reason for rejection.
        reason: &'static str,
    },
    /// An enum-level readable-family precedence chain was invalid.
    InvalidEnumPrecedence {
        /// Specific exhaustive-chain failure.
        reason: String,
    },
    /// A configuration item was not a fixed cell-tree shape.
    UnsupportedConfigurationDeclaration {
        /// Specific declaration restriction.
        reason: &'static str,
    },
    /// A configuration field was outside the fixed cell shape.
    UnsupportedConfigurationField {
        /// Specific field restriction.
        reason: &'static str,
    },
    /// An initializer function used an unsupported signature feature.
    UnsupportedInitializerSignature {
        /// Specific signature restriction.
        reason: &'static str,
    },
    /// A configuration-variable parameter was outside the fixed-state subset.
    UnsupportedConfigurationVariable {
        /// Specific parameter restriction.
        reason: &'static str,
    },
    /// More than one initializer parameter claimed the main configuration input.
    AmbiguousMainConfigurationVariable,
    /// An initializer body was outside the closed declarative grammar.
    UnsupportedInitializerBody {
        /// Specific body restriction.
        reason: &'static str,
    },
    /// The one required initializer field was absent.
    MissingConfigurationField {
        /// Required Rust field name.
        name: &'static str,
    },
    /// An initializer field occurred more than once.
    DuplicateConfigurationField {
        /// Repeated Rust field name.
        name: &'static str,
    },
    /// A `#[k::cell(...)]` payload was malformed.
    InvalidCellAttribute {
        /// Stable reason for rejection.
        reason: &'static str,
    },
    /// A compiler-owned configuration/state macro payload was malformed.
    InvalidStateMacro {
        /// Reserved macro whose payload was rejected.
        macro_name: &'static str,
        /// Stable reason for rejection.
        reason: &'static str,
    },
    /// Source trivia could not be classified against the token byte ranges.
    InvalidTrivia {
        /// Stable reason for the coverage or lexical failure.
        reason: &'static str,
    },
    /// A non-documentation block comment occurred in a line-comment-only DSL body.
    UnsupportedDslBlockComment {
        /// DSL macro whose source body contained the comment.
        macro_name: &'static str,
    },
    /// A rule function used a signature feature outside the one-clause rule ABI.
    UnsupportedRuleSignature {
        /// Specific signature restriction.
        reason: &'static str,
    },
    /// A rule fn's typed binder list broke the binder-list contract (KF-009, X5).
    InvalidBinderList {
        /// Specific binder or list restriction.
        reason: String,
    },
    /// A rule subject was not a supported named-constructor pattern.
    UnsupportedRulePattern {
        /// Specific pattern restriction.
        reason: &'static str,
    },
    /// A symbolic constructor field or rule type was not a supported `Term` sort.
    InvalidTermType,
    /// A rule body was not exactly one unterminated term expression.
    UnsupportedRuleBody {
        /// Specific body restriction.
        reason: &'static str,
    },
    /// A macro in a rule subject or result was not the reserved `term!` form.
    UnexpectedMacro {
        /// Macro path as written.
        path: String,
    },
    /// A Rust expression is outside the closed named-term grammar.
    UnsupportedTermExpression {
        /// Specific expression restriction.
        reason: &'static str,
    },
    /// A token-bearing semantic node unexpectedly emitted no token leaves.
    MissingTokenEndpoint,
    /// A single invocation contained more same-role nodes than `u32` can key.
    TooManyProvenanceOccurrences {
        /// Stable parser-owned role spelling.
        role: &'static str,
    },
    /// A sentence attribute combined keys that K does not accept together.
    InvalidRuleKey {
        /// Complete stable explanation, naming the fix.
        reason: &'static str,
    },
    /// A retired attribute was used.
    RetiredAttribute {
        /// Retired attribute as written, such as `#[k::priority(..)]`.
        attribute: &'static str,
        /// Replacement spelling, with the authored values filled in.
        replacement: String,
    },
    /// A `#[k::token]` attribute, a stack of them, or a `k::lexeme!` term was malformed.
    InvalidTokenAttribute {
        /// Complete stable explanation, naming the fix.
        reason: &'static str,
    },
    /// A `k::lexical!` or `k::layout!` block was malformed.
    InvalidLexicalMacro {
        /// Complete stable explanation, naming the fix.
        reason: &'static str,
    },
    /// A `#[k::syntax_list]` attribute or enum was malformed (KF-020).
    InvalidSyntaxList {
        /// Complete stable explanation, naming the fix.
        reason: &'static str,
    },
    /// A `k::raw_k!` text is not exactly one rule, claim, or context sentence.
    RawKShape {
        /// Complete explanation.
        reason: String,
    },
    /// A `#[k::fresh]` binder occurs where the step has not created it yet
    /// (the pattern or `requires`), shadows another binding, or is unused.
    FreshBinderPosition {
        /// Specific placement restriction.
        reason: &'static str,
    },
    /// A function's `smtlib` or `smt_hook` metadata was malformed (KF-044).
    InvalidSmtMetadata {
        /// Complete explanation, naming the fix.
        reason: String,
    },
    /// A `concrete`, `symbolic`, or `smt_lemma` key was malformed (KF-043).
    InvalidMatchRestriction {
        /// Complete explanation, naming the fix.
        reason: String,
    },
    /// An `unbound_variables = [..]` key of a desugar clause was malformed or
    /// misplaced (KF-046).
    InvalidUnboundVariables {
        /// Complete explanation, naming the fix.
        reason: String,
    },
}

impl SyntaxErrorKind {
    /// Returns the registered code for this syntax category.
    #[must_use]
    pub const fn code(&self) -> Code {
        match self {
            Self::ReservedBinder => codes::syntax::RESERVED_BINDER,
            Self::RustSyntax(_) => codes::syntax::RUST_SYNTAX,
            Self::UnexpectedAttributePayload { .. } => codes::syntax::UNEXPECTED_ATTRIBUTE_PAYLOAD,
            Self::UnknownArgument { .. } => codes::syntax::UNKNOWN_ARGUMENT,
            Self::DuplicateArgument { .. } => codes::syntax::DUPLICATE_ARGUMENT,
            Self::MissingArgument { .. } => codes::syntax::MISSING_ARGUMENT,
            Self::InvalidArgumentValue { .. } => codes::syntax::INVALID_ARGUMENT_VALUE,
            Self::UnsupportedPath => codes::syntax::UNSUPPORTED_PATH,
            Self::UnsupportedSortDeclaration { .. } => codes::syntax::UNSUPPORTED_SORT_DECLARATION,
            Self::UnsupportedConstructorDeclaration { .. } => {
                codes::syntax::UNSUPPORTED_CONSTRUCTOR_DECLARATION
            }
            Self::UnsupportedEnumConstructorDeclaration { .. } => {
                codes::syntax::UNSUPPORTED_ENUM_CONSTRUCTOR_DECLARATION
            }
            Self::UnsupportedTokenDeclaration { .. } => {
                codes::syntax::UNSUPPORTED_TOKEN_DECLARATION
            }
            Self::UnsupportedSubsortDeclaration { .. } => {
                codes::syntax::UNSUPPORTED_SUBSORT_DECLARATION
            }
            Self::InvalidSyntaxTemplate { .. } => codes::syntax::INVALID_SYNTAX_TEMPLATE,
            Self::UnknownTemplateField { .. } => codes::syntax::UNKNOWN_TEMPLATE_FIELD,
            Self::InvalidTemplateFieldOccurrence { .. } => {
                codes::syntax::INVALID_TEMPLATE_FIELD_OCCURRENCE
            }
            Self::InvalidTokenRegex { .. } => codes::syntax::INVALID_TOKEN_REGEX,
            Self::InvalidFormat { .. } => codes::syntax::INVALID_FORMAT,
            Self::InvalidColor { .. } => codes::syntax::INVALID_COLOR,
            Self::InvalidStrictness { .. } => codes::syntax::INVALID_STRICTNESS,
            Self::InvalidGrammarMacro { .. } => codes::syntax::INVALID_GRAMMAR_MACRO,
            Self::InvalidEnumPrecedence { .. } => codes::syntax::INVALID_ENUM_PRECEDENCE,
            Self::UnsupportedConfigurationDeclaration { .. } => {
                codes::syntax::UNSUPPORTED_CONFIGURATION_DECLARATION
            }
            Self::UnsupportedConfigurationField { .. } => {
                codes::syntax::UNSUPPORTED_CONFIGURATION_FIELD
            }
            Self::UnsupportedInitializerSignature { .. } => {
                codes::syntax::UNSUPPORTED_INITIALIZER_SIGNATURE
            }
            Self::UnsupportedConfigurationVariable { .. } => {
                codes::syntax::UNSUPPORTED_CONFIGURATION_VARIABLE
            }
            Self::AmbiguousMainConfigurationVariable => {
                codes::syntax::AMBIGUOUS_MAIN_CONFIGURATION_VARIABLE
            }
            Self::UnsupportedInitializerBody { .. } => codes::syntax::UNSUPPORTED_INITIALIZER_BODY,
            Self::MissingConfigurationField { .. } => codes::syntax::MISSING_CONFIGURATION_FIELD,
            Self::DuplicateConfigurationField { .. } => {
                codes::syntax::DUPLICATE_CONFIGURATION_FIELD
            }
            Self::InvalidCellAttribute { .. } => codes::syntax::INVALID_CELL_ATTRIBUTE,
            Self::InvalidStateMacro { .. } => codes::syntax::INVALID_STATE_MACRO,
            Self::InvalidTrivia { .. } => codes::syntax::INVALID_TRIVIA,
            Self::UnsupportedDslBlockComment { .. } => codes::syntax::UNSUPPORTED_DSL_BLOCK_COMMENT,
            Self::UnsupportedRuleSignature { .. } | Self::InvalidBinderList { .. } => {
                codes::syntax::UNSUPPORTED_RULE_SIGNATURE
            }
            Self::UnsupportedRulePattern { .. } => codes::syntax::UNSUPPORTED_RULE_PATTERN,
            Self::InvalidTermType => codes::syntax::INVALID_TERM_TYPE,
            Self::UnsupportedRuleBody { .. } => codes::syntax::UNSUPPORTED_RULE_BODY,
            Self::UnexpectedMacro { .. } => codes::syntax::UNEXPECTED_MACRO,
            Self::UnsupportedTermExpression { .. } => codes::syntax::UNSUPPORTED_TERM_EXPRESSION,
            Self::MissingTokenEndpoint => codes::syntax::MISSING_TOKEN_ENDPOINT,
            Self::TooManyProvenanceOccurrences { .. } => {
                codes::syntax::TOO_MANY_PROVENANCE_OCCURRENCES
            }
            Self::InvalidRuleKey { .. } => codes::syntax::INVALID_RULE_KEY,
            Self::RetiredAttribute { .. } => codes::syntax::RETIRED_ATTRIBUTE,
            Self::InvalidTokenAttribute { .. } => codes::syntax::INVALID_TOKEN_ATTRIBUTE,
            Self::InvalidLexicalMacro { .. } => codes::syntax::INVALID_LEXICAL_MACRO,
            Self::InvalidSyntaxList { .. } => codes::syntax::INVALID_SYNTAX_LIST_ATTRIBUTE,
            Self::RawKShape { .. } => codes::syntax::RAW_K_SHAPE,
            Self::FreshBinderPosition { .. } => codes::analysis::FRESH_BINDER_POSITION,
            Self::InvalidSmtMetadata { .. } => codes::syntax::INVALID_SMT_METADATA,
            Self::InvalidMatchRestriction { .. } => codes::syntax::INVALID_MATCH_RESTRICTION_KEY,
            Self::InvalidUnboundVariables { .. } => codes::syntax::INVALID_UNBOUND_VARIABLES,
        }
    }
}

/// A structured parser error carrying the most specific available source span.
#[derive(Clone, Debug)]
pub struct SyntaxError {
    kind: SyntaxErrorKind,
    span: Span,
    source_range: Option<SourceRange>,
}

impl SyntaxError {
    /// Creates an error at the token which caused it.
    #[must_use]
    pub const fn new(kind: SyntaxErrorKind, span: Span) -> Self {
        Self {
            kind,
            span,
            source_range: None,
        }
    }

    /// Adds a byte-exact range in the source string passed to a `_source` API.
    ///
    /// Comments have no `proc_macro2::Span`, so source-reparse diagnostics use this range while retaining [`Self::span`] for compatibility with callers that consume `syn::Error`.
    #[must_use]
    pub const fn with_source_range(mut self, source_range: SourceRange) -> Self {
        self.source_range = Some(source_range);
        self
    }

    /// Returns the machine-readable error category.
    #[must_use]
    pub const fn kind(&self) -> &SyntaxErrorKind {
        &self.kind
    }

    /// Returns the primary diagnostic span.
    #[must_use]
    pub const fn span(&self) -> Span {
        self.span
    }

    /// Returns the byte-exact source range when the error arose in trivia.
    #[must_use]
    pub const fn source_range(&self) -> Option<SourceRange> {
        self.source_range
    }
}

impl ToDiagnostic for SyntaxError {
    fn to_diagnostic(&self) -> Diagnostic {
        let location = self
            .source_range
            .map_or_else(|| Location::Span(self.span), Location::Range);
        Diagnostic::error(self.kind.code(), self.to_string(), location)
    }
}

impl From<SyntaxError> for syn::Error {
    fn from(error: SyntaxError) -> Self {
        Self::new(error.span(), error.to_string())
    }
}

impl fmt::Display for SyntaxError {
    #[expect(
        clippy::too_many_lines,
        reason = "Exhaustive formatting keeps each syntax error message with its variant."
    )]
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            SyntaxErrorKind::ReservedBinder => write!(
                formatter,
                "marker `{}` is reserved for generated identifiers",
                krs_ir::ir::RESERVED_MARKER
            ),
            SyntaxErrorKind::RustSyntax(message) => formatter.write_str(message),
            SyntaxErrorKind::UnexpectedAttributePayload { attribute } => {
                write!(formatter, "`{attribute}` takes no arguments")
            }
            SyntaxErrorKind::UnknownArgument { name } => {
                write!(formatter, "unknown argument `{name}`")
            }
            SyntaxErrorKind::DuplicateArgument { name } => {
                write!(formatter, "duplicate argument `{name}`")
            }
            SyntaxErrorKind::MissingArgument { name } => {
                write!(formatter, "missing required argument `{name} = ...`")
            }
            SyntaxErrorKind::InvalidArgumentValue { name, expected } => {
                write!(formatter, "`{name}` must be {expected}")
            }
            SyntaxErrorKind::UnsupportedPath => {
                formatter.write_str("Rust references must be plain paths without generic arguments")
            }
            SyntaxErrorKind::UnsupportedSortDeclaration { reason } => {
                write!(formatter, "unsupported sort declaration: {reason}")
            }
            SyntaxErrorKind::UnsupportedConstructorDeclaration { reason } => {
                write!(formatter, "unsupported constructor declaration: {reason}")
            }
            SyntaxErrorKind::UnsupportedEnumConstructorDeclaration { reason } => {
                write!(
                    formatter,
                    "unsupported enum constructor declaration: {reason}"
                )
            }
            SyntaxErrorKind::UnsupportedTokenDeclaration { reason } => {
                write!(formatter, "unsupported token declaration: {reason}")
            }
            SyntaxErrorKind::UnsupportedSubsortDeclaration { reason } => {
                write!(formatter, "unsupported subsort declaration: {reason}")
            }
            SyntaxErrorKind::InvalidSyntaxTemplate { reason } => {
                write!(formatter, "invalid KRS syntax template: {reason}")
            }
            SyntaxErrorKind::UnknownTemplateField { name } => {
                write!(formatter, "syntax template names unknown field `{name}`")
            }
            SyntaxErrorKind::InvalidTemplateFieldOccurrence {
                name,
                expected,
                actual,
            } => write!(
                formatter,
                "syntax template must name field `{name}` {expected} time(s), found {actual}"
            ),
            SyntaxErrorKind::InvalidTokenRegex { reason } => {
                write!(formatter, "invalid token regular expression: {reason}")
            }
            SyntaxErrorKind::InvalidFormat { reason } => {
                write!(formatter, "invalid production format: {reason}")
            }
            SyntaxErrorKind::InvalidColor { reason } => {
                write!(formatter, "invalid production colours: {reason}")
            }
            SyntaxErrorKind::InvalidStrictness { reason } => {
                write!(formatter, "invalid strictness metadata: {reason}")
            }
            SyntaxErrorKind::InvalidGrammarMacro { reason } => {
                write!(formatter, "invalid grammar macro: {reason}")
            }
            SyntaxErrorKind::InvalidEnumPrecedence { reason } => {
                write!(formatter, "invalid enum precedence chain: {reason}")
            }
            SyntaxErrorKind::UnsupportedConfigurationDeclaration { reason } => {
                write!(
                    formatter,
                    "unsupported fixed configuration declaration: {reason}"
                )
            }
            SyntaxErrorKind::UnsupportedConfigurationField { reason } => {
                write!(formatter, "unsupported fixed configuration field: {reason}")
            }
            SyntaxErrorKind::UnsupportedInitializerSignature { reason } => {
                write!(formatter, "unsupported initializer signature: {reason}")
            }
            SyntaxErrorKind::UnsupportedConfigurationVariable { reason } => {
                write!(formatter, "unsupported configuration variable: {reason}")
            }
            SyntaxErrorKind::AmbiguousMainConfigurationVariable => {
                formatter.write_str("at most one configuration variable may be marked `main`")
            }
            SyntaxErrorKind::UnsupportedInitializerBody { reason } => {
                write!(
                    formatter,
                    "unsupported declarative initializer body: {reason}"
                )
            }
            SyntaxErrorKind::MissingConfigurationField { name } => {
                write!(formatter, "initializer is missing required field `{name}`")
            }
            SyntaxErrorKind::DuplicateConfigurationField { name } => {
                write!(formatter, "initializer repeats field `{name}`")
            }
            SyntaxErrorKind::InvalidCellAttribute { reason } => {
                write!(formatter, "invalid `cell` attribute: {reason}")
            }
            SyntaxErrorKind::InvalidStateMacro { macro_name, reason } => {
                write!(formatter, "invalid `{macro_name}!` payload: {reason}")
            }
            SyntaxErrorKind::InvalidTrivia { reason } => {
                write!(formatter, "invalid source trivia: {reason}")
            }
            SyntaxErrorKind::UnsupportedDslBlockComment { macro_name } => write!(
                formatter,
                "non-documentation block comments are not allowed inside `{macro_name}!` bodies; use `//`"
            ),
            SyntaxErrorKind::UnsupportedRuleSignature { reason } => {
                write!(formatter, "unsupported rule signature: {reason}")
            }
            SyntaxErrorKind::InvalidBinderList { reason } => {
                write!(formatter, "unsupported rule signature: {reason}")
            }
            SyntaxErrorKind::UnsupportedRulePattern { reason } => {
                write!(formatter, "unsupported rule pattern: {reason}")
            }
            SyntaxErrorKind::InvalidTermType => {
                formatter.write_str("expected `Term<SortPath>` or `Term<dyn SortPath>`")
            }
            SyntaxErrorKind::UnsupportedRuleBody { reason } => {
                write!(formatter, "unsupported rule body: {reason}")
            }
            SyntaxErrorKind::UnexpectedMacro { path } => {
                write!(
                    formatter,
                    "expected the reserved `term!` macro, found `{path}!`"
                )
            }
            SyntaxErrorKind::UnsupportedTermExpression { reason } => {
                write!(formatter, "unsupported term expression: {reason}")
            }
            SyntaxErrorKind::MissingTokenEndpoint => {
                formatter.write_str("semantic node had no token endpoints")
            }
            SyntaxErrorKind::TooManyProvenanceOccurrences { role } => {
                write!(
                    formatter,
                    "too many `{role}` nodes to assign provenance ordinals"
                )
            }
            SyntaxErrorKind::InvalidRuleKey { reason }
            | SyntaxErrorKind::InvalidTokenAttribute { reason }
            | SyntaxErrorKind::InvalidLexicalMacro { reason }
            | SyntaxErrorKind::InvalidSyntaxList { reason }
            | SyntaxErrorKind::FreshBinderPosition { reason } => formatter.write_str(reason),
            SyntaxErrorKind::RetiredAttribute {
                attribute,
                replacement,
            } => write!(formatter, "`{attribute}` is retired; write `{replacement}`"),
            SyntaxErrorKind::RawKShape { reason }
            | SyntaxErrorKind::InvalidSmtMetadata { reason }
            | SyntaxErrorKind::InvalidMatchRestriction { reason }
            | SyntaxErrorKind::InvalidUnboundVariables { reason } => formatter.write_str(reason),
        }
    }
}

impl Error for SyntaxError {}

impl From<syn::Error> for SyntaxError {
    fn from(error: syn::Error) -> Self {
        Self::new(SyntaxErrorKind::RustSyntax(error.to_string()), error.span())
    }
}

#[cfg(test)]
mod tests;
