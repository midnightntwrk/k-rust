use proc_macro::TokenStream;
use quote::{ToTokens, quote};
use syn::{
    Expr, ExprLit, FnArg, ItemFn, ItemStruct, ItemTrait, Lit, Meta, Pat, ReturnType, Token,
    parse::Parser, parse_macro_input, punctuated::Punctuated,
};

fn rust_expression(input: TokenStream, macro_name: &str) -> TokenStream {
    let expression = match syn::parse::<Expr>(input) {
        Ok(expression) => expression,
        Err(error) => return error.to_compile_error().into(),
    };
    let name = syn::LitStr::new(macro_name, proc_macro2::Span::call_site());
    quote! {{
        // This prototype deliberately keeps the payload as a real Rust
        // expression. A future K-specific payload needs KRS-aware editor help.
        let _krs_typecheck_payload = || { #expression };
        concat!(#name, ": ", stringify!(#expression))
    }}
    .into()
}

#[proc_macro]
pub fn term(input: TokenStream) -> TokenStream {
    rust_expression(input, "term")
}

#[proc_macro]
pub fn cells(input: TokenStream) -> TokenStream {
    rust_expression(input, "cells")
}

#[proc_macro]
pub fn ml(input: TokenStream) -> TokenStream {
    rust_expression(input, "ml")
}

fn origin(item: &syn::Ident) -> proc_macro2::TokenStream {
    quote! {
        ::krs::Origin {
            package: env!("CARGO_PKG_NAME"),
            module: module_path!(),
            item: stringify!(#item),
            file: file!(),
            line: line!(),
            column: column!(),
        }
    }
}

#[proc_macro_attribute]
pub fn sort(attributes: TokenStream, input: TokenStream) -> TokenStream {
    if !attributes.is_empty() {
        return syn::Error::new(proc_macro2::Span::call_site(), "`sort` takes no arguments")
            .to_compile_error()
            .into();
    }
    let item = parse_macro_input!(input as ItemTrait);
    let name = &item.ident;
    let origin = origin(name);
    let parents: Vec<_> = item.supertraits.iter().map(ToTokens::to_token_stream).collect();
    quote! {
        #item
        ::krs::inventory::submit! {
            ::krs::Registration {
                origin: #origin,
                descriptor: ::krs::Descriptor::Sort(::krs::SortDescriptor {
                    name: stringify!(#name),
                    parents: &[#(stringify!(#parents)),*],
                }),
            }
        }
    }
    .into()
}

fn name_value(arguments: &Punctuated<Meta, Token![,]>, key: &str) -> syn::Result<String> {
    let value = arguments.iter().find_map(|meta| match meta {
        Meta::NameValue(value) if value.path.is_ident(key) => Some(&value.value),
        _ => None,
    });
    match value {
        Some(Expr::Path(path)) => Ok(path.path.to_token_stream().to_string()),
        Some(Expr::Lit(ExprLit { lit: Lit::Str(value), .. })) => Ok(value.value()),
        Some(other) => Err(syn::Error::new_spanned(other, format!("`{key}` has the wrong value type"))),
        None => Err(syn::Error::new(proc_macro2::Span::call_site(), format!("missing `{key} = ...`"))),
    }
}

fn path_value(
    arguments: &Punctuated<Meta, Token![,]>,
    key: &str,
) -> syn::Result<syn::Path> {
    let value = arguments.iter().find_map(|meta| match meta {
        Meta::NameValue(value) if value.path.is_ident(key) => Some(&value.value),
        _ => None,
    });
    match value {
        Some(Expr::Path(path)) => Ok(path.path.clone()),
        Some(other) => Err(syn::Error::new_spanned(
            other,
            format!("`{key}` must be a Rust trait path"),
        )),
        None => Err(syn::Error::new(
            proc_macro2::Span::call_site(),
            format!("missing `{key} = ...`"),
        )),
    }
}

#[proc_macro_attribute]
pub fn constructor(attributes: TokenStream, input: TokenStream) -> TokenStream {
    let parser = Punctuated::<Meta, Token![,]>::parse_terminated;
    let arguments = match parser.parse(attributes) {
        Ok(arguments) => arguments,
        Err(error) => return error.to_compile_error().into(),
    };
    let sort = match path_value(&arguments, "sort") {
        Ok(sort) => sort,
        Err(error) => return error.to_compile_error().into(),
    };
    let syntax = match name_value(&arguments, "syntax") {
        Ok(syntax) => syntax,
        Err(error) => return error.to_compile_error().into(),
    };
    let item = parse_macro_input!(input as ItemStruct);
    let name = &item.ident;
    let origin = origin(name);
    quote! {
        #item
        const _: ::core::marker::PhantomData<fn() -> dyn #sort> =
            ::core::marker::PhantomData;
        ::krs::inventory::submit! {
            ::krs::Registration {
                origin: #origin,
                descriptor: ::krs::Descriptor::Constructor(::krs::ConstructorDescriptor {
                    name: stringify!(#name),
                    sort: stringify!(#sort),
                    syntax: #syntax,
                }),
            }
        }
    }
    .into()
}

#[proc_macro_attribute]
pub fn rule(attributes: TokenStream, input: TokenStream) -> TokenStream {
    if !attributes.is_empty() {
        return syn::Error::new(proc_macro2::Span::call_site(), "`rule` takes no arguments")
            .to_compile_error()
            .into();
    }
    let item = parse_macro_input!(input as ItemFn);
    let name = &item.sig.ident;
    let origin = origin(name);

    if item.sig.inputs.len() != 1 {
        return syn::Error::new_spanned(
            &item.sig.inputs,
            "a prototype rule must have exactly one pattern parameter",
        )
        .to_compile_error()
        .into();
    }
    let (pattern, parameter_type) = match item.sig.inputs.first().expect("checked length") {
        FnArg::Typed(argument) => (&argument.pat, &argument.ty),
        receiver => {
            return syn::Error::new_spanned(receiver, "rules cannot have a `self` receiver")
                .to_compile_error()
                .into();
        }
    };
    if matches!(&**pattern, Pat::Wild(_)) {
        return syn::Error::new_spanned(pattern, "a rule needs a meaningful left-hand pattern")
            .to_compile_error()
            .into();
    }
    let result_type = match &item.sig.output {
        ReturnType::Type(_, ty) => ty.to_token_stream(),
        ReturnType::Default => {
            return syn::Error::new_spanned(&item.sig, "a rule must declare its result sort")
                .to_compile_error()
                .into();
        }
    };
    let body = &item.block;
    if body.stmts.len() != 1 {
        return syn::Error::new_spanned(body, "a prototype rule body must contain one term")
            .to_compile_error()
            .into();
    }
    let body_term = &body.stmts[0];
    let visibility = &item.vis;
    let attributes = &item.attrs;

    // Keep an ordinary Rust item with the authored name for symbols/navigation,
    // but consume the relational signature before Rust's irrefutable-pattern and
    // body type checks. The descriptor remains the semantic source of truth.
    quote! {
        #(#attributes)*
        #[doc(hidden)]
        #visibility fn #name() {}

        const _: ::core::marker::PhantomData<#parameter_type> =
            ::core::marker::PhantomData;
        const _: ::core::marker::PhantomData<#result_type> =
            ::core::marker::PhantomData;

        ::krs::inventory::submit! {
            ::krs::Registration {
                origin: #origin,
                descriptor: ::krs::Descriptor::Rule(::krs::RuleDescriptor {
                    name: stringify!(#name),
                    parameter_pattern: stringify!(#pattern),
                    parameter_type: stringify!(#parameter_type),
                    result_type: stringify!(#result_type),
                    body: stringify!(#body_term),
                }),
            }
        }
    }
    .into()
}
