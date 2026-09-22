//! Host facilities that exist only inside a running procedural macro.
//!
//! Expansion code reaches invocation source locations and `krs` facade
//! discovery only through [`MacroEnvironment`]. [`ProcMacroEnvironment`] is the
//! native host and the only code in this crate that calls `Span::unwrap()` or
//! `proc_macro_crate`.

use proc_macro_crate::{FoundCrate, crate_name};
use proc_macro2::Span;
use syn::{Ident, Path, parse_quote};

/// One source position as a proc macro observes it: 1-based line and column.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct SourcePosition {
    pub(crate) line: u32,
    pub(crate) column: u32,
}

pub(crate) trait MacroEnvironment {
    /// The display file of `span` (`proc_macro::Span::file`).
    fn span_file(&self, span: Span) -> String;
    /// Start of `span`, or `None` when the host has no representable location.
    fn span_start(&self, span: Span) -> Option<SourcePosition>;
    /// End of `span`, or `None` when the host has no representable location.
    fn span_end(&self, span: Span) -> Option<SourcePosition>;
    /// The invocation's call-site span, if the host exposes one.
    fn call_site(&self) -> Option<Span>;
    /// The path through which generated code names the `krs` facade.
    fn facade_path(&self) -> syn::Result<Path>;
}

/// The environment of a macro invocation expanded by rustc.
pub(crate) struct ProcMacroEnvironment;

impl ProcMacroEnvironment {
    fn position(location: proc_macro::Span) -> Option<SourcePosition> {
        Some(SourcePosition {
            line: u32::try_from(location.line()).ok()?,
            column: u32::try_from(location.column()).ok()?,
        })
    }
}

impl MacroEnvironment for ProcMacroEnvironment {
    fn span_file(&self, span: Span) -> String {
        span.unwrap().file()
    }

    fn span_start(&self, span: Span) -> Option<SourcePosition> {
        Self::position(span.unwrap().start())
    }

    fn span_end(&self, span: Span) -> Option<SourcePosition> {
        Self::position(span.unwrap().end())
    }

    fn call_site(&self) -> Option<Span> {
        Some(Span::call_site())
    }

    fn facade_path(&self) -> syn::Result<Path> {
        match crate_name("krs") {
            Ok(FoundCrate::Itself) => Ok(parse_quote!(crate)),
            Ok(FoundCrate::Name(name)) => {
                let ident = Ident::new(&name, Span::call_site());
                Ok(parse_quote!(::#ident))
            }
            Err(error) => Err(syn::Error::new(
                Span::call_site(),
                format!(
                    "KRS macros require a direct dependency on the `krs` facade (dependency renames are supported): {error}"
                ),
            )),
        }
    }
}

/// A host-independent environment for unit tests: a configured display file
/// and facade path, positions from `proc_macro2` span locations, and no call
/// site.
#[cfg(test)]
pub(crate) struct FixedEnvironment {
    pub(crate) file: String,
    pub(crate) facade: Path,
}

#[cfg(test)]
impl FixedEnvironment {
    pub(crate) fn new(file: &str, facade: &str) -> Self {
        Self {
            file: file.to_owned(),
            facade: syn::parse_str(facade).expect("a test facade is a Rust path"),
        }
    }

    fn position(location: proc_macro2::LineColumn) -> Option<SourcePosition> {
        Some(SourcePosition {
            line: u32::try_from(location.line).ok()?,
            column: u32::try_from(location.column).ok()?.checked_add(1)?,
        })
    }
}

#[cfg(test)]
impl MacroEnvironment for FixedEnvironment {
    fn span_file(&self, _span: Span) -> String {
        self.file.clone()
    }

    fn span_start(&self, span: Span) -> Option<SourcePosition> {
        Self::position(span.start())
    }

    fn span_end(&self, span: Span) -> Option<SourcePosition> {
        Self::position(span.end())
    }

    fn call_site(&self) -> Option<Span> {
        None
    }

    fn facade_path(&self) -> syn::Result<Path> {
        Ok(self.facade.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::FixedEnvironment;
    use proc_macro2::TokenStream;

    #[test]
    fn sorts_expand_outside_a_proc_macro() {
        let environment = FixedEnvironment::new("src/lib.rs", "::k");
        let input: TokenStream = "Exp;\nVal;".parse().unwrap();
        let output = crate::expand::sorts(&environment, input)
            .unwrap()
            .to_string();
        assert!(output.contains(":: k :: HostSourceAnchor :: new"));
        assert!(output.contains("\"src/lib.rs\""));
    }

    #[test]
    fn host_provenance_without_call_site_uses_first_token_range() {
        let environment = FixedEnvironment::new("src/lib.rs", "::k");
        let facade = syn::parse_str("::k").unwrap();
        let tokens: TokenStream = "alpha beta".parse().unwrap();
        let fallback = krs_syntax::TokenRange::for_tokens(&tokens).unwrap();
        let output = crate::provenance::host_provenance(&environment, &facade, fallback, &[])
            .unwrap()
            .to_string();
        assert!(output.contains("\"src/lib.rs\" . to_owned ()"));
        assert!(output.contains("HostSourcePosition :: new (1u32 , 1u32)"));
        assert!(output.contains("HostSourcePosition :: new (1u32 , 11u32)"));
        assert!(output.contains("AnchorPrecision :: InvocationFallback"));
    }
}
