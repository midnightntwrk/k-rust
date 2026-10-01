//! Renderer failures with their producer-owned diagnostics.

use std::fmt;

use krs_diagnostic::{Code, Diagnostic, Location, ToDiagnostic, codes};
use krs_syntax::SyntaxError;
use proc_macro2::{Ident, Span, TokenStream, TokenTree};
use quote::ToTokens;

/// A renderer failure containing one or more diagnostics in reporting order.
#[derive(Debug)]
pub struct ExpandError {
    failures: Vec<Failure>,
}

#[derive(Debug)]
struct Failure {
    diagnostic: Diagnostic,
    // Stable rustc cannot always join spans, so retain syn's rendering endpoints.
    rustc_spans: Option<(Span, Span)>,
}

/// The result of rendering one KRS invocation.
pub type Result<T> = std::result::Result<T, ExpandError>;

impl ExpandError {
    /// Creates a renderer error at one span.
    #[must_use]
    pub fn new(code: Code, span: Span, message: impl fmt::Display) -> Self {
        Self::from_diagnostic(Diagnostic::error(
            code,
            message.to_string(),
            Location::Span(span),
        ))
    }

    /// Creates a renderer error covering the supplied tokens.
    /// The rustc renderer must retain both endpoints when stable rustc cannot join them.
    #[must_use]
    pub fn new_spanned(code: Code, tokens: impl ToTokens, message: impl fmt::Display) -> Self {
        let mut error = Self::from(syn::Error::new_spanned(tokens, message));
        error.failures[0].diagnostic.code = code;
        error
    }

    /// Creates a renderer failure from a shared diagnostic.
    #[must_use]
    pub fn from_diagnostic(diagnostic: Diagnostic) -> Self {
        Self {
            failures: vec![Failure {
                diagnostic,
                rustc_spans: None,
            }],
        }
    }

    /// Appends another failure's diagnostics without changing their order.
    pub fn combine(&mut self, another: Self) {
        self.failures.extend(another.failures);
    }

    /// Returns the diagnostics in reporting order.
    pub fn diagnostics(&self) -> impl Iterator<Item = &Diagnostic> {
        self.failures.iter().map(|failure| &failure.diagnostic)
    }

    /// Consumes the failure and returns its diagnostics in reporting order.
    pub fn into_diagnostics(self) -> impl Iterator<Item = Diagnostic> {
        self.failures.into_iter().map(|failure| failure.diagnostic)
    }

    /// Renders one rustc sub-error per diagnostic, retaining available span endpoints.
    /// Diagnostics without a macro span use the invocation's `call_site`.
    ///
    /// # Panics
    ///
    /// Panics if an internal constructor violates the nonempty diagnostic invariant.
    #[must_use]
    pub fn into_syn_error(self, call_site: Span) -> syn::Error {
        let mut errors = self.failures.into_iter().map(|failure| {
            if let Some((start, end)) = failure.rustc_spans {
                let tokens = TokenStream::from_iter([
                    TokenTree::Ident(Ident::new("start", start)),
                    TokenTree::Ident(Ident::new("end", end)),
                ]);
                syn::Error::new_spanned(tokens, failure.diagnostic.message)
            } else {
                let span = match failure.diagnostic.primary.location {
                    Location::Span(span) => span,
                    _ => call_site,
                };
                syn::Error::new(span, failure.diagnostic.message)
            }
        });
        let mut error = errors
            .next()
            .expect("a renderer failure has at least one diagnostic");
        for next in errors {
            error.combine(next);
        }
        error
    }
}

impl From<SyntaxError> for ExpandError {
    fn from(error: SyntaxError) -> Self {
        Self::from_diagnostic(error.to_diagnostic())
    }
}

impl From<syn::Error> for ExpandError {
    fn from(error: syn::Error) -> Self {
        Self {
            failures: error
                .into_iter()
                .map(|error| {
                    let diagnostic = Diagnostic::error(
                        codes::syntax::RUST_SYNTAX,
                        error.to_string(),
                        Location::Span(error.span()),
                    );
                    let tokens = error.to_compile_error().into_iter().collect::<Vec<_>>();
                    let rustc_spans = Some((
                        tokens
                            .first()
                            .expect("syn emits compile_error tokens")
                            .span(),
                        tokens
                            .last()
                            .expect("syn emits a compile_error group")
                            .span(),
                    ));
                    Failure {
                        diagnostic,
                        rustc_spans,
                    }
                })
                .collect(),
        }
    }
}

impl fmt::Display for ExpandError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.failures[0].diagnostic.message)
    }
}

impl std::error::Error for ExpandError {}

#[cfg(test)]
mod tests {
    use super::*;

    fn rendering_spans(
        error: &syn::Error,
    ) -> Vec<(std::ops::Range<usize>, std::ops::Range<usize>)> {
        error
            .clone()
            .into_iter()
            .map(|error| {
                let tokens: Vec<_> = error.to_compile_error().into_iter().collect();
                (tokens[0].span().byte_range(), tokens[2].span().byte_range())
            })
            .collect()
    }

    #[test]
    fn combined_rust_syntax_errors_preserve_messages_and_rendering_endpoints() {
        let tokens: TokenStream = "first middle last".parse().unwrap();
        let mut original = syn::Error::new_spanned(tokens.clone(), "first failure");
        original.combine(syn::Error::new(
            tokens.into_iter().next().unwrap().span(),
            "second failure",
        ));
        let expected = rendering_spans(&original);
        let error = ExpandError::from(original);
        let diagnostics: Vec<_> = error.diagnostics().collect();
        assert_eq!(diagnostics.len(), 2);
        assert!(
            diagnostics
                .iter()
                .all(|diagnostic| diagnostic.code == codes::syntax::RUST_SYNTAX)
        );
        assert_eq!(diagnostics[0].message, "first failure");
        assert_eq!(diagnostics[1].message, "second failure");
        let rendered = error.into_syn_error(Span::call_site());
        assert_eq!(rendering_spans(&rendered), expected);
        assert_eq!(
            rendered
                .into_iter()
                .map(|error| error.to_string())
                .collect::<Vec<_>>(),
            ["first failure", "second failure"]
        );
    }

    #[test]
    fn structured_syntax_errors_keep_their_code_and_nonspan_errors_use_the_call_site() {
        let tokens: TokenStream = "invocation".parse().unwrap();
        let call_site = tokens.into_iter().next().unwrap().span();
        let syntax = SyntaxError::new(
            krs_syntax::SyntaxErrorKind::UnexpectedAttributePayload { attribute: "sort" },
            call_site,
        );
        let error = ExpandError::from(syntax);
        assert_eq!(
            error.diagnostics().next().unwrap().code,
            codes::syntax::UNEXPECTED_ATTRIBUTE_PAYLOAD
        );
        for location in [
            Location::None,
            Location::Range(krs_ir::ByteRange::new(0, 1).unwrap()),
        ] {
            let error = ExpandError::from_diagnostic(Diagnostic::error(
                codes::expand::ORPHAN_HELPER,
                "failure",
                location,
            ));
            let rendered = error.into_syn_error(call_site);
            assert_eq!(rendered.span().byte_range(), call_site.byte_range());
        }
    }
}
