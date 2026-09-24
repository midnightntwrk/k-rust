//! Single productions: `#[k::symbol]`, `#[k::constructor]`, `#[k::function]`, `#[k::token]`, and the orphan strictness helpers.

use krs_syntax::surface::{AttributeMacro, helper_entry, last_segment_entry};
use krs_syntax::{
    ProvenanceAnchor, ProvenanceRole, StrictnessAttribute, SyntaxTemplateItem, TokenRange,
    parse_alias_attribute, parse_constructor_attribute, parse_constructor_declaration,
    parse_function_attribute, parse_seqstrict_attribute, parse_strict_attribute,
    parse_symbol_attribute, parse_token_attribute, parse_token_declaration,
};
use proc_macro2::{Span, TokenStream};
use quote::{ToTokens, format_ident, quote};
use syn::spanned::Spanned;
use syn::{Attribute, Ident, Item, ItemStruct, Meta, Path, parse_quote};

use super::nonce::expansion_nonce;
use super::productions::{
    constructor_metadata_tokens, production_documentation_tokens, strictness_tokens,
};
use super::tokens::{
    call_site_cfg_attributes, call_site_ident, call_site_path, helper_tokens, host_sort_reference,
    option_owned_string, provenance_key, sort_type_tokens, spelling, type_reference,
};
use crate::environment::MacroEnvironment;
use crate::provenance::host_provenance;

pub(crate) fn symbol(attributes: TokenStream, item: TokenStream) -> syn::Result<TokenStream> {
    let symbol =
        parse_symbol_attribute(attributes).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let mut item: Item = syn::parse2(item)?;
    let (attrs, span) = match &mut item {
        Item::Trait(item) => (&mut item.attrs, item.ident.span()),
        Item::Struct(item) => (&mut item.attrs, item.ident.span()),
        _ => {
            return Err(syn::Error::new(
                item.span(),
                "#[k::symbol] currently supports sort traits and constructor structs",
            ));
        }
    };
    if attrs
        .iter()
        .any(|attribute| last_segment_entry(attribute.path()) == Some(AttributeMacro::Symbol))
    {
        return Err(syn::Error::new(span, "duplicate #[k::symbol] attribute"));
    }
    let targets = attrs
        .iter()
        .enumerate()
        .filter(|(_, attribute)| {
            matches!(
                last_segment_entry(attribute.path()),
                Some(AttributeMacro::Sort | AttributeMacro::Constructor)
            )
        })
        .map(|(index, _)| index)
        .collect::<Vec<_>>();
    let [target] = targets.as_slice() else {
        return Err(syn::Error::new(
            span,
            "#[k::symbol] must immediately precede exactly one #[k::sort] or #[k::constructor] declaration",
        ));
    };
    let literal = symbol.literal();
    attrs.insert(
        *target + 1,
        parse_quote!(#[__krs_explicit_symbol(#literal)]),
    );
    Ok(item.into_token_stream())
}

#[allow(clippy::too_many_lines)]
pub(crate) fn constructor(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> syn::Result<TokenStream> {
    let attribute =
        parse_constructor_attribute(attributes).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    constructor_like(env, attribute, item, None, None)
}

pub(crate) fn function(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> syn::Result<TokenStream> {
    let function =
        parse_function_attribute(attributes).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let totality_anchor = function
        .provenance()
        .map_err(krs_syntax::SyntaxError::into_syn_error)?
        .into_iter()
        .find(|anchor| {
            matches!(
                anchor.role(),
                ProvenanceRole::FunctionTotal | ProvenanceRole::FunctionPartial
            )
        })
        .expect("a parsed function retains its totality marker");
    let hook = function
        .hook()
        .map(|path| -> syn::Result<(ProvenanceAnchor, TokenStream)> {
            let segments = path
                .segments
                .iter()
                .map(|segment| segment.ident.to_string())
                .collect::<Vec<_>>();
            let operation = match segments.as_slice() {
                [module, name] if module == "krypto" && name == "keccak256_raw" => {
                    let facade = env.facade_path()?;
                    quote!(#facade::HookOperation::KryptoKeccak256Raw)
                }
                [module, name] if module == "krypto" && name == "sha256_raw" => {
                    let facade = env.facade_path()?;
                    quote!(#facade::HookOperation::KryptoSha256Raw)
                }
                [module, name] if module == "krypto" && name == "ripemd160_raw" => {
                    let facade = env.facade_path()?;
                    quote!(#facade::HookOperation::KryptoRipemd160Raw)
                }
                [module, name] if module == "krypto" && name == "ecdsa_recover" => {
                    let facade = env.facade_path()?;
                    quote!(#facade::HookOperation::KryptoEcdsaRecover)
                }
                [module, name] if module == "krypto" && name == "bn128_valid" => {
                    let facade = env.facade_path()?;
                    quote!(#facade::HookOperation::KryptoBn128Valid)
                }
                [module, name] if module == "krypto" && name == "bn128_add" => {
                    let facade = env.facade_path()?;
                    quote!(#facade::HookOperation::KryptoBn128Add)
                }
                [module, name] if module == "krypto" && name == "bn128_mul" => {
                    let facade = env.facade_path()?;
                    quote!(#facade::HookOperation::KryptoBn128Mul)
                }
                [module, name] if module == "krypto" && name == "bn128_g2_valid" => {
                    let facade = env.facade_path()?;
                    quote!(#facade::HookOperation::KryptoBn128G2Valid)
                }
                [module, name] if module == "krypto" && name == "bn128_ate" => {
                    let facade = env.facade_path()?;
                    quote!(#facade::HookOperation::KryptoBn128Ate)
                }
                _ => {
                    return Err(syn::Error::new(
                        path.span(),
                        "unknown KRS hook; expected `krypto::keccak256_raw`, `krypto::sha256_raw`, `krypto::ripemd160_raw`, `krypto::ecdsa_recover`, `krypto::bn128_valid`, `krypto::bn128_add`, `krypto::bn128_mul`, `krypto::bn128_g2_valid`, or `krypto::bn128_ate`",
                    ));
                }
            };
            Ok((
                ProvenanceAnchor::new(
                    ProvenanceRole::FunctionHook,
                    0,
                    TokenRange::for_tokens(path)
                        .map_err(krs_syntax::SyntaxError::into_syn_error)?,
                ),
                operation,
            ))
        })
        .transpose()?;
    constructor_like(
        env,
        function.production().clone(),
        item,
        Some((totality_anchor, function.is_total())),
        hook,
    )
}

#[allow(clippy::needless_pass_by_value, clippy::too_many_lines)]
fn constructor_like(
    env: &dyn MacroEnvironment,
    attribute: krs_syntax::ConstructorAttribute,
    item: TokenStream,
    totality: Option<(ProvenanceAnchor, bool)>,
    hook: Option<(ProvenanceAnchor, TokenStream)>,
) -> syn::Result<TokenStream> {
    let functional = totality.is_some();
    let total = totality.as_ref().is_some_and(|(_, total)| *total);
    let mut raw_item: ItemStruct = syn::parse2(item)?;
    reject_unexpanded_symbol(&raw_item.attrs)?;
    let explicit_symbol = take_explicit_symbol_helper(&mut raw_item.attrs)?;
    let strictness = take_strictness_helpers(&mut raw_item.attrs)?;
    let alias = take_alias_helper(&mut raw_item.attrs)?;
    if functional && alias.is_some() {
        return Err(syn::Error::new(
            raw_item.ident.span(),
            "a function production cannot also be a static alias",
        ));
    }
    let declaration = parse_constructor_declaration(raw_item.to_token_stream())
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    attribute
        .validate_declaration(&declaration)
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    if let Some(strictness) = &strictness {
        strictness
            .validate_fields(
                declaration
                    .fields()
                    .iter()
                    .map(krs_syntax::ConstructorField::name),
            )
            .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    }
    let facade = env.facade_path()?;
    let mut declaration_anchors = attribute
        .provenance()
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    declaration_anchors.extend(
        declaration
            .provenance()
            .map_err(krs_syntax::SyntaxError::into_syn_error)?,
    );
    if let Some(symbol) = &explicit_symbol {
        declaration_anchors.extend(
            symbol
                .provenance()
                .map_err(krs_syntax::SyntaxError::into_syn_error)?,
        );
    }
    let fallback = krs_syntax::TokenRange::for_tokens(declaration.item())
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let provenance = host_provenance(env, &facade, fallback, &declaration_anchors)?;
    let mut grammar_anchors = attribute
        .full_provenance()
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    if !attribute.avoid
        && grammar_anchors
            .iter()
            .any(|anchor| anchor.role() == ProvenanceRole::ConstructorAvoid)
    {
        return Err(syn::Error::new(
            declaration.name().span(),
            "`avoid = false` is not metadata; omit the argument instead",
        ));
    }
    grammar_anchors.extend(
        declaration
            .full_provenance()
            .map_err(krs_syntax::SyntaxError::into_syn_error)?,
    );
    if let Some(symbol) = &explicit_symbol {
        grammar_anchors.extend(
            symbol
                .provenance()
                .map_err(krs_syntax::SyntaxError::into_syn_error)?,
        );
    }
    if let Some(alias) = &alias {
        grammar_anchors.push(alias.clone());
    }
    if functional {
        if total {
            grammar_anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::FunctionDeclaration,
                0,
                TokenRange::for_tokens(declaration.name())
                    .map_err(krs_syntax::SyntaxError::into_syn_error)?,
            ));
        }
        grammar_anchors.push(
            totality
                .as_ref()
                .expect("functional constructors retain totality provenance")
                .0
                .clone(),
        );
    }
    if let Some((anchor, _)) = &hook {
        grammar_anchors.push(anchor.clone());
    }
    if let Some(strictness) = &strictness {
        grammar_anchors.extend(
            strictness
                .provenance()
                .map_err(krs_syntax::SyntaxError::into_syn_error)?,
        );
    }
    let grammar_provenance = host_provenance(env, &facade, fallback, &grammar_anchors)?;
    let nonce = expansion_nonce(env, "constructor", declaration.name(), fallback);
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
    let authored_sort_type = if functional {
        quote!(#authored_sort)
    } else {
        quote!(dyn #authored_sort)
    };
    let generated_sort_type = if functional {
        quote!(#generated_sort)
    } else {
        quote!(dyn #generated_sort)
    };
    let sort_spelling = spelling(&attribute.sort);
    let sort_reference = host_sort_reference(
        &facade,
        ProvenanceRole::ConstructorSort,
        0,
        &sort_key,
        &sort_spelling,
    );
    let syntax = option_owned_string(attribute.syntax.as_ref().map(syn::LitStr::value));

    let mut field_key_functions = Vec::new();
    let mut fields = Vec::new();
    for (index, field) in declaration.fields().iter().enumerate() {
        let key = format_ident!(
            "__krs_constructor_field_{nonce:016x}_{index}",
            span = Span::call_site()
        );
        let generated = call_site_path(field.term_sort().sort())?;
        let generated = sort_type_tokens(&generated, field.term_sort().is_dynamic());
        let spelling = field.term_sort().sort_spelling();
        let field_name = field.name().to_string();
        field_key_functions.push(quote! {
            #(#cfg)*
            #[doc(hidden)]
            fn #key() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<#generated>()
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

    let owner_target = quote!(#facade::HostApplicationTarget::Nominal(#facade::HostTypeReference {
        key: #facade::HostTypeKey(#declared_key),
        authored_path: #name.to_owned(),
    }));
    let rule_application = quote! {
        #(#cfg)*
        impl<const __KRS_SELECTOR: u64> #facade::__KrsRuleApplication<__KRS_SELECTOR>
            for #declared
        {
            fn __krs_rule_application(authored_path: &str) -> #facade::HostApplicationTarget {
                #facade::HostApplicationTarget::Nominal(#facade::HostTypeReference {
                    key: #facade::HostTypeKey(#declared_key),
                    authored_path: authored_path.to_owned(),
                })
            }
        }
    };
    let grammar = constructor_grammar(
        &facade,
        &attribute,
        &declaration,
        strictness.as_ref(),
        &declared_key,
        &sort_key,
        nonce,
        &cfg,
        &grammar_provenance,
        &owner_target,
        "",
        functional,
        total,
        hook.as_ref().map(|(_, operation)| operation),
        alias.is_some(),
    )?;

    Ok(quote! {
        #item

        #(#cfg)*
        const _: ::core::marker::PhantomData<#authored_sort_type> =
            ::core::marker::PhantomData;

        #(#cfg)*
        #[doc(hidden)]
        fn #declared_key() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#declared>()
        }

        #(#cfg)*
        #[doc(hidden)]
        fn #sort_key() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#generated_sort_type>()
        }

        #(#field_key_functions)*

        #rule_application

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
                declared_type: ::core::option::Option::Some(
                    #facade::HostDeclarationIdentity::Nominal(
                        #facade::HostTypeKey(#declared_key),
                    ),
                ),
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

        #grammar
    })
}

pub(super) fn reject_unexpanded_symbol(attributes: &[Attribute]) -> syn::Result<()> {
    if let Some(attribute) = attributes
        .iter()
        .find(|attribute| last_segment_entry(attribute.path()) == Some(AttributeMacro::Symbol))
    {
        return Err(syn::Error::new(
            attribute.span(),
            "#[k::symbol] must appear before the symbol-bearing KRS declaration attribute",
        ));
    }
    Ok(())
}

pub(super) fn take_explicit_symbol_helper(
    attributes: &mut Vec<Attribute>,
) -> syn::Result<Option<krs_syntax::SymbolAttribute>> {
    let mut symbol = None;
    let mut retained = Vec::with_capacity(attributes.len());
    for attribute in std::mem::take(attributes) {
        if attribute.path().is_ident("__krs_explicit_symbol") {
            let parsed =
                parse_symbol_attribute(helper_tokens(&attribute, "__krs_explicit_symbol")?)
                    .map_err(krs_syntax::SyntaxError::into_syn_error)?;
            if symbol.replace(parsed).is_some() {
                return Err(syn::Error::new(
                    attribute.span(),
                    "duplicate explicit stable-symbol helper",
                ));
            }
        } else {
            retained.push(attribute);
        }
    }
    *attributes = retained;
    Ok(symbol)
}

fn take_strictness_helpers(
    attributes: &mut Vec<Attribute>,
) -> syn::Result<Option<StrictnessAttribute>> {
    let mut strictness = None;
    let mut retained = Vec::with_capacity(attributes.len());
    for attribute in std::mem::take(attributes) {
        let parsed = match helper_entry(attribute.path()) {
            Some(entry @ AttributeMacro::Strict) => Some(
                parse_strict_attribute(helper_tokens(&attribute, entry.name())?)
                    .map_err(krs_syntax::SyntaxError::into_syn_error)?,
            ),
            Some(entry @ AttributeMacro::Seqstrict) => Some(
                parse_seqstrict_attribute(helper_tokens(&attribute, entry.name())?)
                    .map_err(krs_syntax::SyntaxError::into_syn_error)?,
            ),
            _ => None,
        };
        if let Some(parsed) = parsed {
            if strictness.is_some() {
                return Err(syn::Error::new(
                    attribute.span(),
                    "a constructor may declare only one `strict` or `seqstrict` strategy",
                ));
            }
            strictness = Some(parsed);
        } else {
            retained.push(attribute);
        }
    }
    *attributes = retained;
    Ok(strictness)
}

fn take_alias_helper(attributes: &mut Vec<Attribute>) -> syn::Result<Option<ProvenanceAnchor>> {
    let mut alias = None;
    let mut retained = Vec::with_capacity(attributes.len());
    for attribute in std::mem::take(attributes) {
        if helper_entry(attribute.path()) == Some(AttributeMacro::Alias) {
            let tokens = match &attribute.meta {
                Meta::Path(_) => TokenStream::new(),
                Meta::List(list) => list.tokens.clone(),
                Meta::NameValue(_) => {
                    return Err(syn::Error::new(
                        attribute.span(),
                        "`alias` must use marker syntax",
                    ));
                }
            };
            parse_alias_attribute(tokens).map_err(krs_syntax::SyntaxError::into_syn_error)?;
            if alias.is_some() {
                return Err(syn::Error::new(
                    attribute.span(),
                    "a constructor may declare `alias` only once",
                ));
            }
            let marker = attribute
                .path()
                .segments
                .last()
                .expect("helper attributes have a final path segment");
            alias = Some(ProvenanceAnchor::new(
                ProvenanceRole::AliasProduction,
                0,
                TokenRange::for_tokens(&marker.ident)
                    .map_err(krs_syntax::SyntaxError::into_syn_error)?,
            ));
        } else {
            retained.push(attribute);
        }
    }
    *attributes = retained;
    Ok(alias)
}

pub(crate) fn orphan_strictness(
    entry: AttributeMacro,
    attributes: TokenStream,
    _item: TokenStream,
) -> syn::Result<TokenStream> {
    let name = entry.name();
    match entry {
        AttributeMacro::Strict => {
            parse_strict_attribute(attributes).map_err(krs_syntax::SyntaxError::into_syn_error)?;
        }
        AttributeMacro::Seqstrict => {
            parse_seqstrict_attribute(attributes)
                .map_err(krs_syntax::SyntaxError::into_syn_error)?;
        }
        _ => unreachable!(),
    }
    Err(syn::Error::new(
        Span::call_site(),
        format!("`#[k::{name}]` is a constructor helper; place `#[k::constructor(...)]` before it"),
    ))
}

#[allow(clippy::too_many_lines)]
pub(crate) fn token(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> syn::Result<TokenStream> {
    let token_lexical_precedence_role = ProvenanceRole::TokenLexicalPrecedence;
    let token_declaration_role = ProvenanceRole::TokenDeclaration;
    let token_regex_role = ProvenanceRole::TokenRegex;
    let attribute =
        parse_token_attribute(attributes).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let declaration =
        parse_token_declaration(item).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let facade = env.facade_path()?;
    let fallback = TokenRange::for_tokens(declaration.item())
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let nonce = expansion_nonce(env, "token", declaration.name(), fallback);
    let key_fn = format_ident!("__krs_token_type_{nonce:016x}");
    let sort_factory = format_ident!("__krs_token_sort_descriptor_{nonce:016x}");
    let grammar_factory = format_ident!("__krs_token_grammar_descriptor_{nonce:016x}");
    let cfg = call_site_cfg_attributes(&declaration.item().attrs)?;
    let item = declaration.item();
    let name = declaration.name().to_string();
    let declared = call_site_ident(declaration.name())?;

    let sort_anchor = ProvenanceAnchor::new(
        ProvenanceRole::SortDeclaration,
        0,
        TokenRange::for_tokens(declaration.name())
            .map_err(krs_syntax::SyntaxError::into_syn_error)?,
    );
    let sort_provenance = host_provenance(env, &facade, fallback, &[sort_anchor])?;
    let mut grammar_anchors = attribute
        .provenance()
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    grammar_anchors.extend(
        declaration
            .provenance()
            .map_err(krs_syntax::SyntaxError::into_syn_error)?,
    );
    let grammar_provenance = host_provenance(env, &facade, fallback, &grammar_anchors)?;
    let regex = attribute.regex().value();
    let lexical_precedence = if let Some(value) = attribute.lexical_precedence() {
        quote!(::core::option::Option::Some(#facade::DescriptorLexicalPrecedence {
            key: #facade::ProvenanceKey::new(#token_lexical_precedence_role, 0)
                .expect("KRS parser roles are nonempty"),
            value: #value,
        }))
    } else {
        quote!(::core::option::Option::None)
    };
    let grammar_name = format!("__krs_grammar_token_{name}");
    let token_reference =
        host_sort_reference(&facade, ProvenanceRole::TokenDeclaration, 0, &key_fn, &name);

    Ok(quote! {
        #item

        #(#cfg)*
        #[doc(hidden)]
        fn #key_fn() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#declared>()
        }

        #(#cfg)*
        #[doc(hidden)]
        fn #sort_factory() -> #facade::HostDescriptor {
            #facade::HostDescriptor {
                protocol_version: #facade::ProtocolVersion::CURRENT,
                id: #facade::HostItemId::from_macro_context(
                    env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"),
                    env!("CARGO_MANIFEST_DIR"), module_path!(), #name,
                    #facade::ItemKind::Sort, "",
                ).expect("Cargo and Rust macro context form a valid token-sort identity"),
                declared_type: ::core::option::Option::Some(
                    #facade::HostDeclarationIdentity::Nominal(#facade::HostTypeKey(#key_fn)),
                ),
                payload: #facade::HostDescriptorPayload::Sort(
                    #facade::HostSortDescriptor { parents: ::std::vec![] },
                ),
                cfg: ::core::default::Default::default(),
                provenance: #sort_provenance,
            }
        }

        #(#cfg)*
        #facade::__register_host_descriptor!(#sort_factory);

        #(#cfg)*
        #[doc(hidden)]
        fn #grammar_factory() -> #facade::HostDescriptor {
            #facade::HostDescriptor {
                protocol_version: #facade::ProtocolVersion::CURRENT,
                id: #facade::HostItemId::from_macro_context(
                    env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"),
                    env!("CARGO_MANIFEST_DIR"), module_path!(), #grammar_name,
                    #facade::ItemKind::Grammar, "token",
                ).expect("Cargo and Rust macro context form a valid token-grammar identity"),
                declared_type: ::core::option::Option::None,
                payload: #facade::HostDescriptorPayload::Grammar(::std::boxed::Box::new(
                    #facade::HostGrammarDescriptor::Production(#facade::HostProduction {
                        key: #facade::ProvenanceKey::new(#token_declaration_role, 0)
                            .expect("KRS parser roles are nonempty"),
                        template_key: ::core::option::Option::None,
                        owner: #facade::HostProductionOwner::TokenSort {
                            sort: #token_reference,
                        },
                        result_sort: #facade::HostSortReference {
                            key: #facade::ProvenanceKey::new(#token_declaration_role, 0)
                                .expect("KRS parser roles are nonempty"),
                            target: #facade::HostTypeReference {
                                key: #facade::HostTypeKey(#key_fn),
                                authored_path: #name.to_owned(),
                            },
                        },
                        items: ::std::vec![#facade::HostProductionItem::RegexTerminal {
                            key: #facade::ProvenanceKey::new(#token_regex_role, 0)
                                .expect("KRS parser roles are nonempty"),
                            precede_regex: ::core::option::Option::None,
                            regex: #regex.to_owned(),
                            follow_regex: ::core::option::Option::None,
                        }],
                        attributes: ::std::vec![#facade::HostProductionAttribute::Token {
                            key: #facade::ProvenanceKey::new(#token_regex_role, 0)
                                .expect("KRS parser roles are nonempty"),
                            lexical_precedence: #lexical_precedence,
                        }],
                    }),
                )),
                cfg: ::core::default::Default::default(),
                provenance: #grammar_provenance,
            }
        }

        #(#cfg)*
        #facade::__register_host_descriptor!(#grammar_factory);
    })
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn constructor_grammar(
    facade: &Path,
    attribute: &krs_syntax::ConstructorAttribute,
    declaration: &krs_syntax::ConstructorDeclaration,
    strictness: Option<&StrictnessAttribute>,
    _declared_key: &Ident,
    sort_key: &Ident,
    nonce: u64,
    cfg: &[Attribute],
    provenance: &TokenStream,
    owner_target: &TokenStream,
    disambiguator: &str,
    functional: bool,
    total: bool,
    hook: Option<&TokenStream>,
    alias: bool,
) -> syn::Result<TokenStream> {
    let function_total_role = ProvenanceRole::FunctionTotal;
    let function_hook_role = ProvenanceRole::FunctionHook;
    let alias_production_role = ProvenanceRole::AliasProduction;
    let constructor_declaration_role = ProvenanceRole::ConstructorDeclaration;
    let name = declaration.name().to_string();
    let grammar_name = format!("__krs_grammar_{name}");
    let factory = format_ident!("__krs_constructor_grammar_{nonce:016x}");
    let result_sort_spelling = spelling(&attribute.sort);
    let result_sort = host_sort_reference(
        facade,
        ProvenanceRole::ConstructorSort,
        0,
        sort_key,
        &result_sort_spelling,
    );
    let template_key = attribute
        .syntax_template()
        .map(|_| provenance_key(facade, ProvenanceRole::ConstructorSyntax, 0));
    let template_key = if let Some(key) = template_key {
        quote!(::core::option::Option::Some(#key))
    } else {
        quote!(::core::option::Option::None)
    };
    let items = constructor_production_items(
        facade,
        attribute.syntax_template(),
        declaration.name(),
        declaration.fields(),
        nonce,
    )?;
    let (strict_key_function, strict_attribute) = strictness_tokens(
        facade,
        strictness,
        declaration
            .fields()
            .iter()
            .map(krs_syntax::ConstructorField::name),
        nonce,
        cfg,
    )?;
    let mut attributes = constructor_metadata_tokens(
        facade,
        attribute.group.as_ref().map(syn::LitStr::value),
        attribute.avoid,
        attribute.structured_format(),
    )?;
    attributes.splice(
        0..0,
        production_documentation_tokens(facade, declaration.documentation())?,
    );
    if functional {
        let function_key = if total {
            ProvenanceRole::FunctionDeclaration
        } else {
            ProvenanceRole::FunctionPartial
        };
        attributes.insert(
            0,
            quote! {
                #facade::HostProductionAttribute::Function {
                    key: #facade::ProvenanceKey::new(#function_key, 0)
                        .expect("KRS parser roles are nonempty"),
                }
            },
        );
        if total {
            attributes.insert(
                1,
                quote! {
                    #facade::HostProductionAttribute::Total {
                        key: #facade::ProvenanceKey::new(#function_total_role, 0)
                            .expect("KRS parser roles are nonempty"),
                    }
                },
            );
        }
    }
    if let Some(operation) = hook {
        let position = if total { 2 } else { 1 };
        attributes.insert(
            position,
            quote! {
                #facade::HostProductionAttribute::Hook {
                    key: #facade::ProvenanceKey::new(#function_hook_role, 0)
                        .expect("KRS parser roles are nonempty"),
                    operation: #operation,
                }
            },
        );
    }
    if alias {
        attributes.insert(
            0,
            quote! {
                #facade::HostProductionAttribute::Alias {
                    key: #facade::ProvenanceKey::new(#alias_production_role, 0)
                        .expect("KRS parser roles are nonempty"),
                }
            },
        );
    }
    if let Some(strict_attribute) = strict_attribute {
        attributes.push(strict_attribute);
    }
    let primary = provenance_key(facade, ProvenanceRole::ConstructorDeclaration, 0);

    Ok(quote! {
        #strict_key_function

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
                    #grammar_name,
                    #facade::ItemKind::Grammar,
                    #disambiguator,
                )
                .expect("Cargo and Rust macro context form a valid grammar identity"),
                declared_type: ::core::option::Option::None,
                payload: #facade::HostDescriptorPayload::Grammar(::std::boxed::Box::new(
                    #facade::HostGrammarDescriptor::Production(#facade::HostProduction {
                        key: #primary,
                        template_key: #template_key,
                        owner: #facade::HostProductionOwner::Constructor {
                            constructor: #facade::HostApplicationReference {
                                key: #facade::ProvenanceKey::new(#constructor_declaration_role, 0)
                                    .expect("KRS parser roles are nonempty"),
                                target: #owner_target,
                            },
                        },
                        result_sort: #result_sort,
                        items: ::std::vec![#(#items),*],
                        attributes: ::std::vec![#(#attributes),*],
                    }),
                )),
                cfg: ::core::default::Default::default(),
                provenance: #provenance,
            }
        }

        #(#cfg)*
        #facade::__register_host_descriptor!(#factory);
    })
}

fn constructor_production_items(
    facade: &Path,
    template: Option<&krs_syntax::SyntaxTemplate>,
    name: &Ident,
    fields: &[krs_syntax::ConstructorField],
    nonce: u64,
) -> syn::Result<Vec<TokenStream>> {
    let mut items = Vec::new();
    if let Some(template) = template {
        let mut field_ordinal = 0_u32;
        for (item_index, item) in template.items().iter().enumerate() {
            let item_ordinal = u32::try_from(item_index)
                .map_err(|_| syn::Error::new(name.span(), "too many production items"))?;
            let item_key =
                provenance_key(facade, ProvenanceRole::ConstructorSyntaxItem, item_ordinal);
            match item {
                SyntaxTemplateItem::Terminal(text) => items.push(quote! {
                    #facade::HostProductionItem::Terminal {
                        key: #item_key,
                        text: #text.to_owned(),
                    }
                }),
                SyntaxTemplateItem::Field(field_name) => {
                    let declaration_index = fields
                        .iter()
                        .position(|field| field.name() == field_name)
                        .ok_or_else(|| {
                            syn::Error::new(name.span(), "checked template field disappeared")
                        })?;
                    let declaration_ordinal = u32::try_from(declaration_index)
                        .map_err(|_| syn::Error::new(name.span(), "too many constructor fields"))?;
                    let sort_key =
                        format_ident!("__krs_constructor_field_{nonce:016x}_{declaration_index}");
                    let field = &fields[declaration_index];
                    let sort_spelling = field.term_sort().sort_spelling();
                    let sort = host_sort_reference(
                        facade,
                        ProvenanceRole::ConstructorFieldSort,
                        declaration_ordinal,
                        &sort_key,
                        &sort_spelling,
                    );
                    let field_key = provenance_key(
                        facade,
                        ProvenanceRole::ConstructorSyntaxFieldReference,
                        field_ordinal,
                    );
                    let declaration_key = provenance_key(
                        facade,
                        ProvenanceRole::ConstructorFieldDeclaration,
                        declaration_ordinal,
                    );
                    items.push(quote! {
                        #facade::HostProductionItem::NonTerminal {
                            key: #item_key,
                            field_key: #field_key,
                            declaration_key: ::core::option::Option::Some(#declaration_key),
                            field: #facade::ProductionFieldId::new(#field_name)
                                .expect("Rust field identifiers are valid production fields"),
                            sort: ::std::boxed::Box::new(#sort),
                        }
                    });
                    field_ordinal = field_ordinal
                        .checked_add(1)
                        .ok_or_else(|| syn::Error::new(name.span(), "too many fields"))?;
                }
            }
        }
    } else {
        let declaration_key = provenance_key(facade, ProvenanceRole::ConstructorDeclaration, 0);
        let terminal = name.to_string();
        items.push(quote! {
            #facade::HostProductionItem::Terminal {
                key: #declaration_key,
                text: #terminal.to_owned(),
            }
        });
        for (index, field) in fields.iter().enumerate() {
            let ordinal = u32::try_from(index)
                .map_err(|_| syn::Error::new(name.span(), "too many constructor fields"))?;
            let key = provenance_key(facade, ProvenanceRole::ConstructorFieldDeclaration, ordinal);
            let sort_key = format_ident!("__krs_constructor_field_{nonce:016x}_{index}");
            let sort_spelling = field.term_sort().sort_spelling();
            let sort = host_sort_reference(
                facade,
                ProvenanceRole::ConstructorFieldSort,
                ordinal,
                &sort_key,
                &sort_spelling,
            );
            let field_name = field.name().to_string();
            items.push(quote! {
                #facade::HostProductionItem::NonTerminal {
                    key: #key,
                    field_key: #key,
                    declaration_key: ::core::option::Option::Some(#key),
                    field: #facade::ProductionFieldId::new(#field_name)
                        .expect("Rust field identifiers are valid production fields"),
                    sort: ::std::boxed::Box::new(#sort),
                }
            });
        }
    }
    Ok(items)
}
