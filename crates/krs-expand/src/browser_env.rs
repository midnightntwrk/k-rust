//! The [`MacroEnvironment`] of an expansion host outside rustc.
//!
//! [`BrowserEnvironment`] answers every environment query from request data
//! and from the `proc_macro2` fallback spans of one authored file, and returns
//! what `krs-macros` reads from rustc when Cargo compiles the same file:
//!
//! | Query | rustc (`krs-macros`) | [`BrowserEnvironment`] |
//! |---|---|---|
//! | display file | `Span::file()` | the authored file's display file |
//! | positions | 1-based line and column of the span | fallback line, fallback column + 1 |
//! | synthesized spans | located at the invocation's call site | located at the configured call site |
//! | call site | `Span::call_site()` | the configured call site |
//! | facade path | `proc_macro_crate` lookup of `krs` | the configured facade path |

use std::cell::Cell;

use proc_macro2::{LineColumn, Span};
use syn::Path;

use crate::sink::AuthoredFile;
use crate::{MacroEnvironment, SourcePosition};

/// Environment values for invocations in one authored file.
///
/// A span lies in the authored file when it came from the tokens
/// [`AuthoredFile::lex`] returned. Every other span (a `Span::call_site()`
/// or `Span::mixed_site()` token, or a token re-parsed from a string) is
/// located at the current invocation's call site, as rustc locates it.
pub struct BrowserEnvironment<'a> {
    authored: &'a AuthoredFile,
    facade: Path,
    call_site: Cell<Option<Span>>,
}

impl<'a> BrowserEnvironment<'a> {
    /// An environment for `authored` whose generated code names the facade
    /// through `facade`.
    #[must_use]
    pub fn new(authored: &'a AuthoredFile, facade: Path) -> Self {
        Self {
            authored,
            facade,
            call_site: Cell::new(None),
        }
    }

    /// Sets the call site of the next invocation: the invoking `#[...]`
    /// attribute, or a function-like macro's path through its closing
    /// delimiter.
    pub fn set_call_site(&self, span: Span) {
        self.call_site.set(Some(span));
    }

    fn resolve(&self, span: Span) -> Span {
        if self.authored.contains(span) {
            span
        } else {
            self.call_site.get().unwrap_or(span)
        }
    }

    fn position(location: LineColumn) -> Option<SourcePosition> {
        Some(SourcePosition {
            line: u32::try_from(location.line).ok()?,
            column: u32::try_from(location.column).ok()?.checked_add(1)?,
        })
    }
}

impl MacroEnvironment for BrowserEnvironment<'_> {
    fn span_file(&self, _span: Span) -> String {
        self.authored.display_file().to_owned()
    }

    fn span_start(&self, span: Span) -> Option<SourcePosition> {
        Self::position(self.resolve(span).start())
    }

    fn span_end(&self, span: Span) -> Option<SourcePosition> {
        Self::position(self.resolve(span).end())
    }

    fn call_site(&self) -> Option<Span> {
        self.call_site.get()
    }

    fn facade_path(&self) -> syn::Result<Path> {
        Ok(self.facade.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::BrowserEnvironment;
    use crate::sink::AuthoredFile;
    use crate::{MacroEnvironment, SourcePosition};
    use proc_macro2::{Span, TokenTree};

    #[test]
    fn synthesized_spans_resolve_to_the_call_site() {
        let (authored, tokens) = AuthoredFile::lex("src/lib.rs", "\n  k::k![x]").unwrap();
        let env = BrowserEnvironment::new(&authored, syn::parse_str("::k").unwrap());
        let first = tokens.into_iter().next().map(|tree| tree.span()).unwrap();
        assert_eq!(env.span_file(first), "src/lib.rs");
        assert_eq!(
            env.span_start(first),
            Some(SourcePosition { line: 2, column: 3 })
        );
        env.set_call_site(first);
        let synthesized = Span::call_site();
        assert_eq!(env.span_end(synthesized), env.span_end(first));
        let reparsed = "y".parse::<proc_macro2::TokenStream>().unwrap();
        let Some(TokenTree::Ident(ident)) = reparsed.into_iter().next() else {
            panic!("an identifier");
        };
        assert_eq!(env.span_start(ident.span()), env.span_start(first));
        assert_eq!(
            quote::ToTokens::to_token_stream(&env.facade_path().unwrap()).to_string(),
            ":: k"
        );
    }
}
