//! Shared parsing, provenance ordinal, and reference-candidate plumbing.

use std::cell::RefCell;
use std::collections::BTreeMap;

use krs_ir::ProvenanceKey;
use proc_macro2::{Span, TokenStream};
use syn::parse::{ParseStream, Parser};
use syn::{Attribute, Path};

use crate::surface::path_text;
use crate::{ProvenanceRole, SyntaxError, SyntaxErrorKind};

/// An error from a parser that accepts both Rust and structured syntax failures.
pub enum ParseError {
    /// A validated syntax failure whose kind and span must survive syn parsing.
    Structured(SyntaxError),
    /// A plain syn parser failure.
    Syn(syn::Error),
}

impl From<SyntaxError> for ParseError {
    fn from(error: SyntaxError) -> Self {
        Self::Structured(error)
    }
}

impl From<syn::Error> for ParseError {
    fn from(error: syn::Error) -> Self {
        Self::Syn(error)
    }
}

impl From<ParseError> for syn::Error {
    fn from(error: ParseError) -> Self {
        match error {
            ParseError::Structured(error) => error.into(),
            ParseError::Syn(error) => error,
        }
    }
}

fn bridge<T, E: Into<ParseError>>(
    parser: impl Fn(ParseStream<'_>) -> Result<T, E>,
    run: impl FnOnce(&dyn for<'a> Fn(ParseStream<'a>) -> syn::Result<T>) -> syn::Result<T>,
    syn_error: impl FnOnce(syn::Error) -> SyntaxError,
) -> Result<T, SyntaxError> {
    let structured = RefCell::new(None);
    let parser = |input: ParseStream<'_>| match parser(input).map_err(Into::into) {
        Ok(value) => Ok(value),
        Err(ParseError::Structured(error)) => {
            let diagnostic = syn::Error::new(error.span(), error.to_string());
            structured.replace(Some(error));
            Err(diagnostic)
        }
        Err(ParseError::Syn(error)) => Err(error),
    };
    run(&parser).map_err(|error| {
        structured
            .borrow_mut()
            .take()
            .unwrap_or_else(|| syn_error(error))
    })
}

/// Parses all tokens while preserving a structured error through syn's parser.
///
/// # Errors
///
/// Returns the parser failure or a syn failure converted to `SyntaxError`.
pub fn structured<T, E: Into<ParseError>>(
    tokens: TokenStream,
    parser: impl Fn(ParseStream<'_>) -> Result<T, E>,
) -> Result<T, SyntaxError> {
    structured_with(tokens, parser, SyntaxError::from)
}

/// Parses all tokens with a caller-specific translation for plain syn errors.
///
/// # Errors
///
/// Returns the parser failure or the caller's translation of a syn failure.
pub fn structured_with<T, E: Into<ParseError>>(
    tokens: TokenStream,
    parser: impl Fn(ParseStream<'_>) -> Result<T, E>,
    syn_error: impl FnOnce(syn::Error) -> SyntaxError,
) -> Result<T, SyntaxError> {
    bridge(parser, |parser| parser.parse2(tokens), syn_error)
}

/// Parses an attribute payload using syn's attribute-specific stream handling.
///
/// # Errors
///
/// Returns the parser failure or a syn failure converted to `SyntaxError`.
pub fn structured_args<T, E: Into<ParseError>>(
    attribute: &Attribute,
    parser: impl Fn(ParseStream<'_>) -> Result<T, E>,
) -> Result<T, SyntaxError> {
    bridge(
        parser,
        |parser| attribute.parse_args_with(parser),
        SyntaxError::from,
    )
}

/// Tokenizes source with the call-site span used for lexing failures.
///
/// # Errors
///
/// Returns a Rust syntax error when source tokenization fails.
pub fn tokens_from_source(source: &str) -> Result<TokenStream, SyntaxError> {
    source.parse().map_err(|error: proc_macro2::LexError| {
        SyntaxError::new(
            SyntaxErrorKind::RustSyntax(error.to_string()),
            Span::call_site(),
        )
    })
}

/// Parses a syntax value from tokens or source text.
pub trait KrsSyntax: Sized {
    /// Parses a complete token stream.
    ///
    /// # Errors
    ///
    /// Returns a syntax error when the tokens do not form this value.
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError>;

    /// Parses source text after tokenization.
    ///
    /// # Errors
    ///
    /// Returns a syntax error when tokenization or parsing fails.
    fn parse_source(source: &str) -> Result<Self, SyntaxError> {
        Self::parse_tokens(tokens_from_source(source)?)
    }
}

/// Converts an existing index to a provenance ordinal without renumbering gaps.
///
/// # Errors
///
/// Returns an occurrence overflow error at `span` when `index` exceeds `u32`.
pub fn checked_ordinal(index: usize, role: ProvenanceRole, span: Span) -> Result<u32, SyntaxError> {
    u32::try_from(index).map_err(|_| occurrence_overflow(role, span))
}

fn occurrence_overflow(role: ProvenanceRole, span: Span) -> SyntaxError {
    SyntaxError::new(
        SyntaxErrorKind::TooManyProvenanceOccurrences {
            role: role.as_str(),
        },
        span,
    )
}

/// Assigns zero-based ordinals independently for each provenance role.
#[derive(Default)]
pub struct ProvenanceAnchors(BTreeMap<ProvenanceRole, u32>);

impl ProvenanceAnchors {
    /// Returns the next ordinal for a role, reporting overflow at its node.
    ///
    /// # Errors
    ///
    /// Returns an occurrence overflow error at `span` after the last `u32` ordinal.
    pub fn next(&mut self, role: ProvenanceRole, span: Span) -> Result<u32, SyntaxError> {
        let value = self.0.entry(role).or_default();
        let current = *value;
        *value = value
            .checked_add(1)
            .ok_or_else(|| occurrence_overflow(role, span))?;
        Ok(current)
    }
}

/// One parser-keyed Rust path with an optional semantic kind.
#[derive(Clone, Debug)]
pub struct ReferenceCandidate<K = ()> {
    pub(crate) key: ProvenanceKey,
    pub(crate) path: Path,
    pub(crate) kind: K,
}

impl<K> ReferenceCandidate<K> {
    /// Returns the parser-owned provenance key.
    #[must_use]
    pub const fn key(&self) -> &ProvenanceKey {
        &self.key
    }

    /// Returns the authored Rust path.
    #[must_use]
    pub const fn path(&self) -> &Path {
        &self.path
    }

    /// Returns the authored path as [`path_text`] spells it.
    #[must_use]
    pub fn path_spelling(&self) -> String {
        path_text(&self.path)
    }

    /// Returns the parser-owned semantic kind.
    #[must_use]
    pub const fn kind(&self) -> K
    where
        K: Copy,
    {
        self.kind
    }
}

pub(crate) fn duplicate(name: &'static str, span: Span) -> ParseError {
    SyntaxError::new(SyntaxErrorKind::DuplicateArgument { name }, span).into()
}

pub(crate) fn missing(name: &'static str, span: Span) -> ParseError {
    SyntaxError::new(SyntaxErrorKind::MissingArgument { name }, span).into()
}

pub(crate) fn unknown(name: String, span: Span) -> ParseError {
    SyntaxError::new(SyntaxErrorKind::UnknownArgument { name }, span).into()
}

pub(crate) fn invalid_argument(
    name: &'static str,
    expected: &'static str,
    span: Span,
) -> ParseError {
    SyntaxError::new(
        SyntaxErrorKind::InvalidArgumentValue { name, expected },
        span,
    )
    .into()
}

pub(crate) fn unsupported_rule_signature(reason: &'static str, span: Span) -> SyntaxError {
    SyntaxError::new(SyntaxErrorKind::UnsupportedRuleSignature { reason }, span)
}

pub(crate) fn unsupported_rule_pattern(reason: &'static str, span: Span) -> SyntaxError {
    SyntaxError::new(SyntaxErrorKind::UnsupportedRulePattern { reason }, span)
}

pub(crate) fn unsupported_initializer_signature(reason: &'static str, span: Span) -> SyntaxError {
    SyntaxError::new(
        SyntaxErrorKind::UnsupportedInitializerSignature { reason },
        span,
    )
}

pub(crate) fn unsupported_configuration_variable(reason: &'static str, span: Span) -> SyntaxError {
    SyntaxError::new(
        SyntaxErrorKind::UnsupportedConfigurationVariable { reason },
        span,
    )
}

pub(crate) fn unsupported_initializer_body(reason: &'static str, span: Span) -> SyntaxError {
    SyntaxError::new(SyntaxErrorKind::UnsupportedInitializerBody { reason }, span)
}
