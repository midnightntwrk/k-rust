//! Actual stable procedural macros used by the M2 initializer registration spike.

use proc_macro::TokenStream;
use proc_macro2::Span;
use proc_macro_crate::{FoundCrate, crate_name};
use quote::{format_ident, quote};
use syn::parse::{Parse, ParseStream};
use syn::{Ident, ImplItemFn, ItemStruct, Path, ReturnType, Token, Type, parse_macro_input};

#[proc_macro_attribute]
pub fn init(arguments: TokenStream, item: TokenStream) -> TokenStream {
    let arguments = parse_macro_input!(arguments as InitArguments);
    let method = parse_macro_input!(item as ImplItemFn);
    expand_init(arguments, method)
        .unwrap_or_else(syn::Error::into_compile_error)
        .into()
}

#[proc_macro_attribute]
pub fn configuration(arguments: TokenStream, item: TokenStream) -> TokenStream {
    if !arguments.is_empty() {
        return syn::Error::new(Span::call_site(), "`configuration` takes no arguments")
            .into_compile_error()
            .into();
    }
    let item = parse_macro_input!(item as ItemStruct);
    expand_configuration(item)
        .unwrap_or_else(syn::Error::into_compile_error)
        .into()
}

enum InitArguments {
    Paired,
    Explicit(Path),
    AttemptSelf,
}

impl Parse for InitArguments {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        if input.is_empty() {
            return Ok(Self::Paired);
        }
        let key: Ident = input.parse()?;
        if key == "attempt_self" && input.is_empty() {
            return Ok(Self::AttemptSelf);
        }
        if key != "config" {
            return Err(syn::Error::new(
                key.span(),
                "expected no arguments, `config = Type`, or spike-only `attempt_self`",
            ));
        }
        input.parse::<Token![=]>()?;
        let path = input.parse()?;
        if !input.is_empty() {
            return Err(input.error("unexpected initializer argument"));
        }
        Ok(Self::Explicit(path))
    }
}

fn expand_init(arguments: InitArguments, method: ImplItemFn) -> syn::Result<proc_macro2::TokenStream> {
    validate_method(&method)?;
    let facade = facade_path()?;
    let visibility = &method.vis;
    let payload = quote! {
        #[doc(hidden)]
        #visibility fn __krs_initializer_payload() -> #facade::InitPayload {
            #facade::InitPayload { method: "init" }
        }
    };

    match arguments {
        InitArguments::Paired => Ok(quote! {
            #method
            #payload
        }),
        InitArguments::Explicit(authored_config) => {
            let generated_config: Path = syn::parse_str(&quote!(#authored_config).to_string())?;
            let config_name = quote!(#authored_config).to_string();
            Ok(quote! {
                #method
                #payload

                // Exactly one source-spanned use supports attribute navigation.
                const __KRS_EXPLICIT_TYPE_CHECK: ::core::marker::PhantomData<#authored_config> =
                    ::core::marker::PhantomData;

                #[doc(hidden)]
                fn __krs_explicit_type_key() -> ::core::any::TypeId {
                    ::core::any::TypeId::of::<Self>()
                }

                #[doc(hidden)]
                fn __krs_explicit_type_name() -> &'static str {
                    ::core::any::type_name::<Self>()
                }

                #[doc(hidden)]
                fn __krs_explicit_descriptor() -> #facade::Descriptor {
                    #facade::Descriptor {
                        identity: concat!(
                            env!("CARGO_PKG_NAME"),
                            "::",
                            module_path!(),
                            "::",
                            #config_name,
                            "::init",
                        ),
                        type_key: Self::__krs_explicit_type_key,
                        type_name: Self::__krs_explicit_type_name,
                        payload: Self::__krs_initializer_payload,
                    }
                }

                // `inventory::submit!` itself emits `const _: ()`, which is not
                // an allowed associated item. Nest it in a named associated
                // const so its retained statics are block items instead.
                const __KRS_EXPLICIT_REGISTRATION: () = {
                    #facade::__submit!(#generated_config::__krs_explicit_descriptor);
                };
            })
        }
        InitArguments::AttemptSelf => Ok(quote! {
            #method
            #payload

            #[doc(hidden)]
            fn __krs_self_descriptor() -> #facade::Descriptor {
                #facade::Descriptor {
                    identity: concat!(env!("CARGO_PKG_NAME"), "::", module_path!(), "::Self::init"),
                    type_key: Self::__krs_self_type_key,
                    type_name: Self::__krs_self_type_name,
                    payload: Self::__krs_initializer_payload,
                }
            }

            #[doc(hidden)]
            fn __krs_self_type_key() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<Self>()
            }

            #[doc(hidden)]
            fn __krs_self_type_name() -> &'static str {
                ::core::any::type_name::<Self>()
            }

            // This is the exact attractive-but-invalid bare-method expansion.
            const __KRS_SELF_REGISTRATION: () = {
                #facade::__submit!(Self::__krs_self_descriptor);
            };
        }),
    }
}

fn expand_configuration(item: ItemStruct) -> syn::Result<proc_macro2::TokenStream> {
    if !item.generics.params.is_empty() || item.generics.where_clause.is_some() {
        return Err(syn::Error::new_spanned(
            &item.generics,
            "this spike accepts only concrete configuration types",
        ));
    }
    let facade = facade_path()?;
    let authored_ident = &item.ident;
    let generated_ident = Ident::new(&authored_ident.to_string(), Span::call_site());
    let suffix = authored_ident.to_string().to_lowercase();
    let type_key = format_ident!("__krs_configuration_type_key_{suffix}");
    let type_name = format_ident!("__krs_configuration_type_name_{suffix}");
    let factory = format_ident!("__krs_configuration_descriptor_{suffix}");
    let config_name = authored_ident.to_string();

    Ok(quote! {
        #item

        #[doc(hidden)]
        fn #type_key() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#generated_ident>()
        }

        #[doc(hidden)]
        fn #type_name() -> &'static str {
            ::core::any::type_name::<#generated_ident>()
        }

        #[doc(hidden)]
        fn #factory() -> #facade::Descriptor {
            #facade::Descriptor {
                identity: concat!(
                    env!("CARGO_PKG_NAME"),
                    "::",
                    module_path!(),
                    "::",
                    #config_name,
                    "::init",
                ),
                type_key: #type_key,
                type_name: #type_name,
                payload: #generated_ident::__krs_initializer_payload,
            }
        }

        #facade::__submit!(#factory);
    })
}

fn validate_method(method: &ImplItemFn) -> syn::Result<()> {
    if method.sig.ident != "init" {
        return Err(syn::Error::new_spanned(
            &method.sig.ident,
            "initializer must be named `init`",
        ));
    }
    if method.sig.receiver().is_some() {
        return Err(syn::Error::new_spanned(
            &method.sig.inputs,
            "initializer must be an associated function without a receiver",
        ));
    }
    let ReturnType::Type(_, result) = &method.sig.output else {
        return Err(syn::Error::new_spanned(
            &method.sig,
            "initializer must return `Self`",
        ));
    };
    let Type::Path(result) = &**result else {
        return Err(syn::Error::new_spanned(result, "initializer must return `Self`"));
    };
    if result.qself.is_some()
        || result.path.leading_colon.is_some()
        || result.path.segments.len() != 1
        || result.path.segments[0].ident != "Self"
    {
        return Err(syn::Error::new_spanned(result, "initializer must return `Self`"));
    }
    Ok(())
}

fn facade_path() -> syn::Result<Path> {
    match crate_name("m2-init-facade") {
        Ok(FoundCrate::Itself) => syn::parse_str("crate"),
        Ok(FoundCrate::Name(name)) => syn::parse_str(&format!("::{name}")),
        Err(error) => Err(syn::Error::new(
            Span::call_site(),
            format!("the spike macros require the facade dependency: {error}"),
        )),
    }
}
