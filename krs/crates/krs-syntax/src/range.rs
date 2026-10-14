use proc_macro2::{LineColumn, Span, TokenStream, TokenTree};
use quote::ToTokens;

use crate::{SyntaxError, SyntaxErrorKind};

/// First-leaf start and last-leaf end spans for one parsed semantic node.
///
/// Keeping both endpoints avoids relying on unstable span joining. A proc macro
/// can unwrap each endpoint to stable `proc_macro::Span` and capture its start
/// or end. The source reparser uses the same parsed node and key catalog.
#[derive(Clone, Copy, Debug)]
pub struct TokenRange {
    first: Span,
    last: Span,
}

impl TokenRange {
    /// Selects delimiter-aware first and last leaves from a token-emitting AST.
    ///
    /// # Errors
    ///
    /// Returns [`SyntaxErrorKind::MissingTokenEndpoint`] for an empty node.
    pub fn for_tokens(tokens: &impl ToTokens) -> Result<Self, SyntaxError> {
        let stream = tokens.to_token_stream();
        let mut spans = Vec::new();
        collect_leaf_spans(stream, &mut spans);
        match (spans.first(), spans.last()) {
            (Some(first), Some(last)) => Ok(Self {
                first: *first,
                last: *last,
            }),
            _ => Err(SyntaxError::new(
                SyntaxErrorKind::MissingTokenEndpoint,
                Span::call_site(),
            )),
        }
    }

    /// Creates a range from already-selected leaf endpoints.
    #[must_use]
    pub const fn new(first: Span, last: Span) -> Self {
        Self { first, last }
    }

    /// Returns the first authored leaf span.
    #[must_use]
    pub const fn first(self) -> Span {
        self.first
    }

    /// Returns the last authored leaf span.
    #[must_use]
    pub const fn last(self) -> Span {
        self.last
    }

    /// Returns the first leaf's start location when span locations are present.
    #[must_use]
    pub fn start(self) -> LineColumn {
        self.first.start()
    }

    /// Returns the last leaf's exclusive end location when spans are present.
    #[must_use]
    pub fn end(self) -> LineColumn {
        self.last.end()
    }
}

fn collect_leaf_spans(stream: TokenStream, output: &mut Vec<Span>) {
    for tree in stream {
        match tree {
            TokenTree::Group(group) => {
                output.push(group.span_open());
                collect_leaf_spans(group.stream(), output);
                output.push(group.span_close());
            }
            other => output.push(other.span()),
        }
    }
}
