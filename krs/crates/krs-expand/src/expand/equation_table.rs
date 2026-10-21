//! Equation tables: `k::equations!`.

use krs_syntax::KrsSyntax;
use proc_macro2::TokenStream;
use quote::{quote, quote_spanned};
use syn::spanned::Spanned;

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
    let function = table.function();
    let header = quote_spanned! {function.span()=>
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
        .map(|row| super::rules::equation_row(env, row, table.imports(), function))
        .collect::<crate::Result<Vec<_>>>()?;
    Ok(quote! {
        #header
        #(#imports)*
        #(#rows)*
    })
}
