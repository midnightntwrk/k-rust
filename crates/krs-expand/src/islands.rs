//! Compiler-owned builtin token islands.
//!
//! These macros have no runtime value; the collector reads their authored
//! tokens. Expansion only checks the literal form and emits a panicking
//! placeholder expression.

use crate::ExpandError;
use krs_diagnostic::codes::expand;
use proc_macro2::TokenStream;
use quote::quote;

/// Compiler-owned concrete builtin Id token island.
pub(crate) fn id(input: TokenStream) -> crate::Result<TokenStream> {
    let literal: syn::LitStr = syn::parse2(input)?;
    let value = literal.value();
    if !value.strip_prefix('$').is_some_and(|tail| {
        !tail.is_empty()
            && tail
                .chars()
                .all(|ch| ch == '_' || ch.is_ascii_alphanumeric())
    }) {
        return Err(ExpandError::new(
            expand::INVALID_ID_TOKEN,
            literal.span(),
            "invalid builtin `Id` token",
        ));
    }
    Ok(quote!(::core::panic!("id! has no runtime value")))
}

/// Compiler-owned concrete builtin Bytes token island.
pub(crate) fn bytes(input: TokenStream) -> crate::Result<TokenStream> {
    let _literal: syn::LitByteStr = syn::parse2(input)?;
    Ok(quote!(::core::panic!("bytes! has no runtime value")))
}

/// Compiler-owned anonymous object-language variable occurrence.
pub(crate) fn anonymous() -> TokenStream {
    quote!(::core::panic!("anonymous! has no runtime value"))
}

/// Compiler-owned token of a user token sort. The sort path is checked by
/// rustc; the text is never re-lexed, so it is checked only for form.
pub(crate) fn lexeme(input: TokenStream) -> crate::Result<TokenStream> {
    let (sort, _text) = krs_syntax::parse_lexeme_arguments(input)?;
    Ok(quote! {{
        let _krs_typecheck_lexeme_sort = || ::core::any::TypeId::of::<#sort>();
        ::core::panic!("lexeme! has no runtime value")
    }})
}

/// Compiler-owned sort predicate (`k::is!`) or projection (`k::project!`).
/// The sort path is checked by rustc; the operand is a KRS term whose
/// binders are not Rust values, so only its form is checked.
pub(crate) fn sort_test(
    kind: krs_ir::SortTestKind,
    input: TokenStream,
) -> crate::Result<TokenStream> {
    let (sort, _operand) = krs_syntax::parse_sort_test_arguments(kind, input)?;
    let message = match kind {
        krs_ir::SortTestKind::Predicate => "is! has no runtime value",
        krs_ir::SortTestKind::Projection => "project! has no runtime value",
    };
    Ok(quote! {{
        let _krs_typecheck_sort_test_sort = || ::core::any::TypeId::of::<#sort>();
        ::core::panic!(#message)
    }})
}

/// Compiler-owned associative object-Bool disjunction.
pub(crate) fn or_bool() -> TokenStream {
    quote!(::core::panic!("or_bool! has no runtime value"))
}
