//! Equation tables: `k::equations!`.

use krs_syntax::{KrsSyntax, TokenRange};
use proc_macro2::TokenStream;
use quote::{format_ident, quote, quote_spanned};
use syn::spanned::Spanned;

use super::nonce::expansion_nonce;
use crate::environment::MacroEnvironment;

/// Expands a table into one ordinary equation per row, a check that the
/// header names a non-parametric function, and the rustc checks of the
/// table's `use` items.
pub(crate) fn equations(
    env: &dyn MacroEnvironment,
    input: TokenStream,
) -> crate::Result<TokenStream> {
    let table = krs_syntax::EquationTable::parse_tokens(input)?;
    let facade = env.facade_path()?;
    let authored = table.function();
    // The header path names the function every row defines. It reaches
    // rustc once, at its authored tokens, as this alias's definition; the
    // header check and every row name the alias, so a path that resolves to
    // nothing is one error, at the path.
    let name = &authored
        .segments
        .last()
        .expect("an equation table's header path has a segment")
        .ident;
    let nonce = expansion_nonce(
        env,
        "equation_table_function",
        name,
        TokenRange::for_tokens(authored)?,
    );
    let function = format_ident!("__KrsTableFunction_{nonce:016x}", span = authored.span());
    let header = quote_spanned! {authored.span()=>
        #[doc(hidden)]
        #[allow(dead_code, non_camel_case_types)]
        type #function = #authored;
        const _: () = {
            fn __krs_equation_table_function<F: #facade::__KrsFunction + ?Sized>() {}
            let _ = __krs_equation_table_function::<#function>;
        };
    };
    let imports = table.imports().iter().map(|item| {
        quote! {
            const _: () = {
                #[allow(unused_imports, clippy::enum_glob_use)]
                #item
            };
        }
    });
    let rows = table
        .rows()
        .iter()
        .map(|row| {
            super::rules::equation_row(
                env,
                row,
                super::rules::TableRow {
                    imports: table.imports(),
                    function: &function,
                },
            )
        })
        .collect::<crate::Result<Vec<_>>>()?;
    Ok(quote! {
        #header
        #(#imports)*
        #(#rows)*
    })
}
