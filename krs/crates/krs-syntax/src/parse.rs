//! Shared parsing, provenance ordinal, and reference-candidate plumbing.

use std::cell::RefCell;
use std::collections::BTreeMap;

use krs_ir::ProvenanceKey;
use proc_macro2::{Span, TokenStream};
use syn::parse::{ParseStream, Parser};
use syn::{Attribute, Path};

use crate::path::path_text;
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

/// Removes one trailing top-level comma that follows at least one token.
///
/// A trailing comma adds no element to a list, so every macro or attribute
/// argument list accepts one; the parser then sees the list without it. A lone
/// comma, or a second comma, is left for the parser to reject.
#[must_use]
pub fn strip_trailing_comma(tokens: TokenStream) -> TokenStream {
    let mut tokens: Vec<_> = tokens.into_iter().collect();
    let trailing = tokens.len() >= 2
        && is_comma(&tokens[tokens.len() - 1])
        && !is_comma(&tokens[tokens.len() - 2]);
    if trailing {
        tokens.pop();
        // The new last token ends the stream, so it joins nothing.
        if let Some(proc_macro2::TokenTree::Punct(last)) = tokens.last_mut() {
            let mut alone = proc_macro2::Punct::new(last.as_char(), proc_macro2::Spacing::Alone);
            alone.set_span(last.span());
            *last = alone;
        }
    }
    tokens.into_iter().collect()
}

fn is_comma(token: &proc_macro2::TokenTree) -> bool {
    matches!(token, proc_macro2::TokenTree::Punct(punct) if punct.as_char() == ',')
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

pub(crate) fn validate_authored_binder(spelling: &str, span: Span) -> Result<(), SyntaxError> {
    if spelling.contains(krs_ir::ir::RESERVED_MARKER) && !crate::rule::is_generated_binder(spelling)
    {
        return Err(SyntaxError::new(SyntaxErrorKind::ReservedBinder, span));
    }
    Ok(())
}

fn occurrence_overflow(role: ProvenanceRole, span: Span) -> SyntaxError {
    SyntaxError::new(
        SyntaxErrorKind::TooManyProvenanceOccurrences {
            role: role.as_str(),
        },
        span,
    )
}

/// Allocates the provenance keys of one sentence and records each key's anchor.
///
/// A key is `(role, ordinal)`, where the ordinal counts the sentence's earlier
/// nodes of that role in the order the sentence's keying pass visits them. The
/// allocator hands out the next ordinal of a role and records the anchor of the
/// node that receives it, so the sentence's anchors are exactly the keys it
/// handed out, in allocation order, and no key is handed out twice.
#[derive(Clone, Debug, Default)]
pub struct KeyAllocator {
    next: BTreeMap<ProvenanceRole, u32>,
    anchors: Vec<crate::ProvenanceAnchor>,
}

impl KeyAllocator {
    /// An allocator that continues after `anchors`, which it records first:
    /// each role's next ordinal follows the last one `anchors` hold.
    #[must_use]
    pub fn continuing(anchors: Vec<crate::ProvenanceAnchor>) -> Self {
        Self {
            next: BTreeMap::new(),
            anchors,
        }
    }

    /// Hands out the next key of `role` to the node at `range` and records its
    /// anchor.
    ///
    /// # Errors
    ///
    /// Returns an occurrence overflow error at the node after the last `u32`
    /// ordinal of `role`.
    pub fn key(
        &mut self,
        role: ProvenanceRole,
        range: crate::TokenRange,
    ) -> Result<ProvenanceKey, SyntaxError> {
        let ordinal = self.next_ordinal(role);
        self.next.insert(
            role,
            ordinal
                .checked_add(1)
                .ok_or_else(|| occurrence_overflow(role, range.first()))?,
        );
        self.anchors
            .push(crate::ProvenanceAnchor::new(role, ordinal, range));
        Ok(role.key(ordinal))
    }

    /// The key the next [`Self::key`] of `role` hands out, without handing it
    /// out, for a node [`Self::paired`] with an owner that is keyed after it.
    #[must_use]
    pub fn next_key(&self, role: ProvenanceRole) -> ProvenanceKey {
        role.key(self.next_ordinal(role))
    }

    /// The next ordinal of `role`. Before the first [`Self::key`] of `role`,
    /// it follows the last ordinal of `role` among the anchors recorded so
    /// far, which are those the allocator continues after and any
    /// [`Self::paired`] keys.
    fn next_ordinal(&self, role: ProvenanceRole) -> u32 {
        self.next.get(&role).copied().unwrap_or_else(|| {
            self.anchors
                .iter()
                .filter(|anchor| anchor.role() == role)
                .map(|anchor| anchor.ordinal().saturating_add(1))
                .max()
                .unwrap_or(0)
        })
    }

    /// Hands out the key of `role` that shares the ordinal of `owner` to the
    /// node at `range`, and records its anchor. A node that exists only as an
    /// optional part of another, such as a token regex's lexical precedence,
    /// is numbered as its owner is, so its key names the owner's.
    ///
    /// A role keyed this way is never keyed by [`Self::key`] in the same
    /// sentence, so its keys are distinct when the owners' are.
    pub fn paired(
        &mut self,
        role: ProvenanceRole,
        owner: &ProvenanceKey,
        range: crate::TokenRange,
    ) -> ProvenanceKey {
        debug_assert!(
            !self.next.contains_key(&role),
            "a paired role is never numbered on its own"
        );
        let ordinal = owner.ordinal();
        self.anchors
            .push(crate::ProvenanceAnchor::new(role, ordinal, range));
        role.key(ordinal)
    }

    /// The anchors recorded so far, in allocation order.
    #[must_use]
    pub fn anchors(&self) -> &[crate::ProvenanceAnchor] {
        &self.anchors
    }

    /// The anchors of every key handed out, in allocation order.
    #[must_use]
    pub fn into_anchors(self) -> Vec<crate::ProvenanceAnchor> {
        self.anchors
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

/// The first attribute that is not documentation. Doc comments (`///`,
/// `#[doc = ".."]`, `#[doc(..)]`) document the Rust item and carry no K
/// meaning, so positions that take no attribute still accept them.
pub(crate) fn first_non_doc_attribute(attributes: &[Attribute]) -> Option<&Attribute> {
    attributes
        .iter()
        .find(|attribute| !attribute.path().is_ident("doc"))
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
