//! The rustc host of [`MacroEnvironment`].
//!
//! [`ProcMacroEnvironment`] is the only code in the KRS workspace that calls
//! `Span::unwrap()` or `proc_macro_crate`; `krs-expand` reaches invocation
//! source locations and `krs` facade discovery only through it.

use krs_expand::{MacroEnvironment, SourcePosition};
use krs_ir::Position;
use proc_macro_crate::{FoundCrate, crate_name};
use proc_macro2::Span;
use syn::{Ident, Path, parse_quote};

/// The environment of a macro invocation expanded by rustc.
pub(crate) struct ProcMacroEnvironment;

impl ProcMacroEnvironment {
    fn position(location: proc_macro::Span) -> Option<SourcePosition> {
        Position::from_proc_macro_values(location.line(), location.column())
            .ok()
            .map(Into::into)
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
