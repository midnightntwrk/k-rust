//! Compiler-owned builtin token islands.
//!
//! These macros have no runtime value; the collector reads their authored
//! tokens. Expansion only checks the literal form and emits a panicking
//! placeholder expression.

use proc_macro2::TokenStream;
use quote::quote;

/// Compiler-owned concrete builtin Id token island.
pub(crate) fn id(input: TokenStream) -> syn::Result<TokenStream> {
    let literal: syn::LitStr = syn::parse2(input)?;
    let value = literal.value();
    if !value.strip_prefix('$').is_some_and(|tail| {
        !tail.is_empty()
            && tail
                .chars()
                .all(|ch| ch == '_' || ch.is_ascii_alphanumeric())
    }) {
        return Err(syn::Error::new(
            literal.span(),
            "invalid builtin `Id` token",
        ));
    }
    Ok(quote!(::core::panic!("id! has no runtime value")))
}

/// Compiler-owned concrete builtin Bytes token island.
pub(crate) fn bytes(input: TokenStream) -> syn::Result<TokenStream> {
    let _literal: syn::LitByteStr = syn::parse2(input)?;
    Ok(quote!(::core::panic!("bytes! has no runtime value")))
}

/// Compiler-owned fresh anonymous object-language occurrence.
pub(crate) fn anonymous() -> TokenStream {
    quote!(::core::panic!("anonymous! has no runtime value"))
}

/// Compiler-owned associative object-Bool disjunction.
pub(crate) fn or_bool() -> TokenStream {
    quote!(::core::panic!("or_bool! has no runtime value"))
}
