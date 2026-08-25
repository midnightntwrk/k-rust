use std::hash::{Hash, Hasher};

use krs_syntax::{
    RulePattern, parse_constructor_attribute, parse_constructor_declaration,
    parse_rule_attribute, parse_rule_item, parse_sort_attribute, parse_sort_declaration,
    parse_term_expression,
};
use proc_macro2::{Span, TokenStream};
use proc_macro_crate::{FoundCrate, crate_name};
use quote::{ToTokens, format_ident, quote};
use syn::parse::Parser;
use syn::spanned::Spanned;
use syn::{Attribute, Ident, Path, parse_quote};

use crate::provenance::host_provenance;

pub(crate) fn sort(attributes: TokenStream, item: TokenStream) -> syn::Result<TokenStream> {
    parse_sort_attribute(attributes).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let declaration =
        parse_sort_declaration(item).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let facade = facade_path()?;
    let anchors = declaration
        .provenance()
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let fallback = krs_syntax::TokenRange::for_tokens(declaration.item())
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let provenance = host_provenance(&facade, fallback, &anchors)?;
    let nonce = expansion_nonce("sort", &declaration.item().ident, fallback);
    let factory = format_ident!("__krs_sort_descriptor_{nonce:016x}", span = Span::call_site());
    let declared_key = format_ident!("__krs_sort_type_{nonce:016x}", span = Span::call_site());
    let item = declaration.item();
    let name = declaration.item().ident.to_string();
    let declared = call_site_ident(&declaration.item().ident)?;
    let cfg = call_site_cfg_attributes(&item.attrs)?;

    let mut key_functions = Vec::new();
    let mut parents = Vec::new();
    for (index, parent) in declaration.parents().iter().enumerate() {
        let key = format_ident!(
            "__krs_sort_parent_{nonce:016x}_{index}",
            span = Span::call_site()
        );
        let generated = call_site_path(parent)?;
        let spelling = spelling(parent);
        key_functions.push(quote! {
            #(#cfg)*
            #[doc(hidden)]
            fn #key() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<dyn #generated>()
            }
        });
        parents.push(type_reference(&facade, &key, &spelling));
    }

    Ok(quote! {
        #item

        #(#cfg)*
        #[doc(hidden)]
        fn #declared_key() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<dyn #declared>()
        }

        #(#key_functions)*

        #(#cfg)*
        #[doc(hidden)]
        fn #factory() -> #facade::HostDescriptor {
            #facade::HostDescriptor {
                protocol_version: #facade::ProtocolVersion::CURRENT,
                id: #facade::HostItemId::from_macro_context(
                    env!("CARGO_PKG_NAME"),
                    env!("CARGO_PKG_VERSION"),
                    env!("CARGO_MANIFEST_DIR"),
                    module_path!(),
                    #name,
                    #facade::ItemKind::Sort,
                    "",
                )
                .expect("Cargo and Rust macro context form a valid host identity"),
                declared_type: ::core::option::Option::Some(#facade::HostTypeKey(#declared_key)),
                payload: #facade::HostDescriptorPayload::Sort(#facade::HostSortDescriptor {
                    parents: ::std::vec![#(#parents),*],
                }),
                cfg: ::core::default::Default::default(),
                provenance: #provenance,
            }
        }

        #(#cfg)*
        #facade::__register_host_descriptor!(#factory);
    })
}

pub(crate) fn constructor(
    attributes: TokenStream,
    item: TokenStream,
) -> syn::Result<TokenStream> {
    let attribute = parse_constructor_attribute(attributes)
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let declaration =
        parse_constructor_declaration(item).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let facade = facade_path()?;
    let mut anchors = attribute
        .provenance()
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    anchors.extend(
        declaration
            .provenance()
            .map_err(krs_syntax::SyntaxError::into_syn_error)?,
    );
    let fallback = krs_syntax::TokenRange::for_tokens(declaration.item())
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let provenance = host_provenance(&facade, fallback, &anchors)?;
    let nonce = expansion_nonce("constructor", declaration.name(), fallback);
    let factory = format_ident!(
        "__krs_constructor_descriptor_{nonce:016x}",
        span = Span::call_site()
    );
    let declared_key = format_ident!(
        "__krs_constructor_type_{nonce:016x}",
        span = Span::call_site()
    );
    let sort_key = format_ident!(
        "__krs_constructor_sort_{nonce:016x}",
        span = Span::call_site()
    );
    let item = declaration.item();
    let cfg = call_site_cfg_attributes(&item.attrs)?;
    let name = declaration.name().to_string();
    let declared = call_site_ident(declaration.name())?;
    let authored_sort = &attribute.sort;
    let generated_sort = call_site_path(&attribute.sort)?;
    let sort_spelling = spelling(&attribute.sort);
    let sort_reference = type_reference(&facade, &sort_key, &sort_spelling);
    let syntax = option_owned_string(attribute.syntax.as_ref().map(syn::LitStr::value));

    let mut field_key_functions = Vec::new();
    let mut fields = Vec::new();
    for (index, field) in declaration.fields().iter().enumerate() {
        let key = format_ident!(
            "__krs_constructor_field_{nonce:016x}_{index}",
            span = Span::call_site()
        );
        let generated = call_site_path(field.term_sort().sort())?;
        let spelling = field.term_sort().sort_spelling();
        let field_name = field.name().to_string();
        field_key_functions.push(quote! {
            #(#cfg)*
            #[doc(hidden)]
            fn #key() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<dyn #generated>()
            }
        });
        let reference = type_reference(&facade, &key, &spelling);
        fields.push(quote! {
            #facade::HostConstructorFieldDescriptor {
                name: #field_name.to_owned(),
                sort: #reference,
            }
        });
    }

    Ok(quote! {
        #item

        const _: ::core::marker::PhantomData<dyn #authored_sort> =
            ::core::marker::PhantomData;

        #(#cfg)*
        #[doc(hidden)]
        fn #declared_key() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#declared>()
        }

        #(#cfg)*
        #[doc(hidden)]
        fn #sort_key() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<dyn #generated_sort>()
        }

        #(#field_key_functions)*

        #(#cfg)*
        #[doc(hidden)]
        fn #factory() -> #facade::HostDescriptor {
            #facade::HostDescriptor {
                protocol_version: #facade::ProtocolVersion::CURRENT,
                id: #facade::HostItemId::from_macro_context(
                    env!("CARGO_PKG_NAME"),
                    env!("CARGO_PKG_VERSION"),
                    env!("CARGO_MANIFEST_DIR"),
                    module_path!(),
                    #name,
                    #facade::ItemKind::Constructor,
                    "",
                )
                .expect("Cargo and Rust macro context form a valid host identity"),
                declared_type: ::core::option::Option::Some(#facade::HostTypeKey(#declared_key)),
                payload: #facade::HostDescriptorPayload::Constructor(
                    #facade::HostConstructorDescriptor {
                        sort: #sort_reference,
                        syntax: #syntax,
                        fields: ::std::vec![#(#fields),*],
                    },
                ),
                cfg: ::core::default::Default::default(),
                provenance: #provenance,
            }
        }

        #(#cfg)*
        #facade::__register_host_descriptor!(#factory);
    })
}

pub(crate) fn rule(attributes: TokenStream, item: TokenStream) -> syn::Result<TokenStream> {
    parse_rule_attribute(attributes).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let rule = parse_rule_item(item).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let facade = facade_path()?;
    let anchors = rule
        .provenance()
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let fallback = krs_syntax::TokenRange::for_tokens(rule.item())
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let provenance = host_provenance(&facade, fallback, &anchors)?;
    let nonce = expansion_nonce("rule", &rule.item().sig.ident, fallback);
    let factory = format_ident!("__krs_rule_descriptor_{nonce:016x}", span = Span::call_site());
    let candidates = rule
        .reference_candidates()
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let cfg = call_site_cfg_attributes(&rule.item().attrs)?;

    let mut key_functions = Vec::new();
    let mut references = Vec::new();
    let mut parameter_key = None;
    let mut result_key = None;
    for (index, candidate) in candidates.iter().enumerate() {
        let key_fn = format_ident!(
            "__krs_rule_reference_{nonce:016x}_{index}",
            span = Span::call_site()
        );
        let path = call_site_path(candidate.path())?;
        let role = candidate.key().role();
        let ty = match role {
            "rule_type" | "rule_result_type" => quote!(dyn #path),
            "rule_left_path" | "rule_right_path" => quote!(#path),
            _ => {
                return Err(syn::Error::new(
                    candidate.path().span(),
                    format!("unsupported protocol-v3 rule reference role `{role}`"),
                ));
            }
        };
        key_functions.push(quote! {
            #(#cfg)*
            #[doc(hidden)]
            fn #key_fn() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<#ty>()
            }
        });
        if role == "rule_type" {
            parameter_key = Some(key_fn.clone());
        } else if role == "rule_result_type" {
            result_key = Some(key_fn.clone());
        }
        let role = candidate.key().role();
        let ordinal = candidate.key().ordinal();
        let spelling = candidate.path_spelling();
        let target = type_reference(&facade, &key_fn, &spelling);
        references.push(quote! {
            #facade::HostDescriptorReference::new(
                #facade::ProvenanceKey::new(#role, #ordinal)
                    .expect("KRS parser roles are nonempty"),
                #target,
            )
        });
    }
    let parameter_key = parameter_key
        .ok_or_else(|| syn::Error::new(rule.item().sig.span(), "missing rule parameter key"))?;
    let result_key = result_key
        .ok_or_else(|| syn::Error::new(rule.item().sig.span(), "missing rule result key"))?;

    let original = rule.item();
    let attrs = &original.attrs;
    let visibility = &original.vis;
    let fn_token = original.sig.fn_token;
    let name_ident = &original.sig.ident;
    let parameter_type = rule.parameter().term_sort.ty();
    let result_type = rule.result_sort().ty();
    let surface_pattern = match &rule.parameter().pattern {
        RulePattern::Native { pattern, .. } => quote!(#pattern),
        RulePattern::TermMacro { term, .. } => {
            let expression = term.expression();
            quote!(#expression)
        }
    };
    let result_expression = rule.result().expression();
    let name = name_ident.to_string();
    let lhs = rule.parameter().pattern.spelling();
    let rhs = rule.result().spelling();
    let parameter_sort_spelling = rule.parameter().term_sort.sort_spelling();
    let result_sort_spelling = rule.result_sort().sort_spelling();
    let bindings = rule
        .parameter()
        .pattern
        .bindings()
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>();
    let parameter_reference = type_reference(&facade, &parameter_key, &parameter_sort_spelling);
    let result_reference = type_reference(&facade, &result_key, &result_sort_spelling);

    Ok(quote! {
        #(#attrs)*
        #visibility #fn_token #name_ident(
            __krs_symbolic_subject: #parameter_type,
        ) -> #result_type {
            let _krs_surface_check = |__krs_constructor_subject| {
                match __krs_constructor_subject {
                    #surface_pattern => {
                        let _ = #result_expression;
                    }
                    _ => {}
                }
            };
            let _ = __krs_symbolic_subject;
            ::core::panic!("KRS rule declarations have no runtime implementation")
        }

        #(#key_functions)*

        #(#cfg)*
        #[doc(hidden)]
        fn #factory() -> #facade::HostDescriptor {
            let rule = #facade::HostRuleDescriptor {
                sentence_kind: #facade::SentenceKind::Transition,
                parameters: ::std::vec![#facade::HostRuleParameterDescriptor {
                    bindings: ::std::vec![#(#bindings.to_owned()),*],
                    sort: #parameter_reference,
                    pattern: #lhs.to_owned(),
                }],
                result_sort: #result_reference,
                references: ::std::vec![#(#references),*],
                lhs: #lhs.to_owned(),
                rhs: #rhs.to_owned(),
            };
            rule.validate_reference_keys()
                .expect("KRS shared parsers emit unique rule reference keys");
            rule.validate_bindings()
                .expect("KRS shared parsers emit unique, nonempty rule bindings");
            #facade::HostDescriptor {
                protocol_version: #facade::ProtocolVersion::CURRENT,
                id: #facade::HostItemId::from_macro_context(
                    env!("CARGO_PKG_NAME"),
                    env!("CARGO_PKG_VERSION"),
                    env!("CARGO_MANIFEST_DIR"),
                    module_path!(),
                    #name,
                    #facade::ItemKind::Rule,
                    "",
                )
                .expect("Cargo and Rust macro context form a valid host identity"),
                declared_type: ::core::option::Option::None,
                payload: #facade::HostDescriptorPayload::Rule(rule),
                cfg: ::core::default::Default::default(),
                provenance: #provenance,
            }
        }

        #(#cfg)*
        #facade::__register_host_descriptor!(#factory);
    })
}

pub(crate) fn term(input: TokenStream) -> syn::Result<TokenStream> {
    let term = parse_term_expression(input).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let expression = term.expression();
    Ok(quote! {{
        let _krs_typecheck_named_term = || {
            let _ = #expression;
        };
        ::core::panic!("`term!` has no runtime value in KRS M1")
    }})
}

fn facade_path() -> syn::Result<Path> {
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

fn type_reference(
    facade: &Path,
    key_function: &Ident,
    authored_path: &str,
) -> TokenStream {
    quote! {
        #facade::HostTypeReference {
            key: #facade::HostTypeKey(#key_function),
            authored_path: #authored_path.to_owned(),
        }
    }
}

fn option_owned_string(value: Option<String>) -> TokenStream {
    match value {
        Some(value) => quote!(::core::option::Option::Some(#value.to_owned())),
        None => quote!(::core::option::Option::None),
    }
}

fn spelling(tokens: &impl ToTokens) -> String {
    tokens.to_token_stream().to_string()
}

fn call_site_path(path: &Path) -> syn::Result<Path> {
    syn::parse_str(&path.to_token_stream().to_string())
}

fn call_site_ident(ident: &Ident) -> syn::Result<Ident> {
    syn::parse_str(&ident.to_string())
}

fn call_site_cfg_attributes(attributes: &[Attribute]) -> syn::Result<Vec<Attribute>> {
    let mut parsed = Vec::new();
    for attribute in attributes
        .iter()
        .filter(|attribute| attribute.path().is_ident("cfg"))
    {
        let mut attributes = Attribute::parse_outer
            .parse_str(&attribute.to_token_stream().to_string())?;
        if attributes.len() != 1 {
            return Err(syn::Error::new(
                attribute.span(),
                "KRS could not reproduce this cfg attribute",
            ));
        }
        parsed.push(attributes.remove(0));
    }
    Ok(parsed)
}

fn expansion_nonce(kind: &str, ident: &Ident, range: krs_syntax::TokenRange) -> u64 {
    let mut hasher = StableHasher::default();
    kind.hash(&mut hasher);
    ident.to_string().hash(&mut hasher);
    let start = range.start();
    let end = range.end();
    start.line.hash(&mut hasher);
    start.column.hash(&mut hasher);
    end.line.hash(&mut hasher);
    end.column.hash(&mut hasher);
    hasher.finish()
}

struct StableHasher(u64);

impl Default for StableHasher {
    fn default() -> Self {
        Self(0xcbf2_9ce4_8422_2325)
    }
}

impl Hasher for StableHasher {
    fn finish(&self) -> u64 {
        self.0
    }

    fn write(&mut self, bytes: &[u8]) {
        for byte in bytes {
            self.0 ^= u64::from(*byte);
            self.0 = self.0.wrapping_mul(0x0000_0100_0000_01b3);
        }
    }
}
