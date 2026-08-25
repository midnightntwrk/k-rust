//! Stable procedural-macro side of the builtin registration spike.

use proc_macro::TokenStream;
use proc_macro_crate::{FoundCrate, crate_name};
use proc_macro2::Span;
use quote::{ToTokens, format_ident, quote};
use syn::{Expr, ExprCall, ExprPath, ItemFn, Path, Stmt, parse_macro_input, spanned::Spanned};

/// Registers the final tuple-marker application in an ordinary Rust function.
///
/// The authored function is preserved. Consequently rustc checks its operands
/// and result exactly as ordinary Rust, while collection calls only generated
/// descriptor factories and never executes the function.
#[proc_macro_attribute]
pub fn builtin_application(arguments: TokenStream, item: TokenStream) -> TokenStream {
    if !arguments.is_empty() {
        return syn::Error::new(Span::call_site(), "`builtin_application` takes no arguments")
            .into_compile_error()
            .into();
    }
    let function = parse_macro_input!(item as ItemFn);
    expand(&function)
        .unwrap_or_else(syn::Error::into_compile_error)
        .into()
}

fn expand(function: &ItemFn) -> syn::Result<proc_macro2::TokenStream> {
    if !function.sig.generics.params.is_empty() || function.sig.generics.where_clause.is_some() {
        return Err(syn::Error::new_spanned(
            &function.sig.generics,
            "builtin application carriers must be concrete functions",
        ));
    }
    let Some(last) = function.block.stmts.last() else {
        return Err(syn::Error::new_spanned(
            &function.block,
            "builtin application carrier must end in a tuple-marker call",
        ));
    };
    let expression = match last {
        Stmt::Expr(expression, None) => expression,
        statement => {
            return Err(syn::Error::new_spanned(
                statement,
                "builtin application carrier must have an unterminated final call",
            ));
        }
    };
    let Expr::Call(ExprCall { func, args, .. }) = expression else {
        return Err(syn::Error::new_spanned(
            expression,
            "builtin application carrier must end in a tuple-marker call",
        ));
    };
    let Expr::Path(ExprPath { qself: None, path, .. }) = &**func else {
        return Err(syn::Error::new(
            func.span(),
            "builtin operation must be an ordinary Rust path",
        ));
    };
    let facade = facade_path()?;
    let function_name = &function.sig.ident;
    let key = format_ident!("__krs_builtin_key_{}", function_name, span = Span::call_site());
    let factory = format_ident!(
        "__krs_builtin_application_{}",
        function_name,
        span = Span::call_site()
    );
    let spelling = path_spelling(path);
    let arity = args.len();
    let identity_name = function_name.to_string();

    Ok(quote! {
        #function

        #[doc(hidden)]
        fn #key() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#path>()
        }

        #[doc(hidden)]
        fn #factory() -> #facade::HostBuiltinApplication {
            #facade::HostBuiltinApplication {
                identity: concat!(
                    env!("CARGO_PKG_NAME"),
                    "::",
                    module_path!(),
                    "::",
                    #identity_name,
                ),
                authored_path: #spelling,
                arity: #arity,
                type_key: #key,
            }
        }

        #facade::__submit_builtin_application!(#factory);
    })
}

fn path_spelling(path: &Path) -> String {
    path.to_token_stream()
        .to_string()
        .split_whitespace()
        .collect()
}

fn facade_path() -> syn::Result<Path> {
    match crate_name("m3-builtin-facade") {
        Ok(FoundCrate::Itself) => syn::parse_str("crate"),
        Ok(FoundCrate::Name(name)) => syn::parse_str(&format!("::{name}")),
        Err(error) => Err(syn::Error::new(
            Span::call_site(),
            format!("the spike macro requires the builtin facade dependency: {error}"),
        )),
    }
}

