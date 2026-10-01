//! Single productions: `#[k::symbol]`, `#[k::constructor]`, `#[k::function]`, `#[k::token]`, and the orphan strictness helpers.

use krs_ir::wire::{
    WireConstructorDescriptor, WireConstructorFieldDescriptor, WireGrammarDescriptor, WirePayload,
    WireProduction, WireProductionAttribute, WireProductionItem, WireProductionOwner,
    WireSortReference, WireTypeReference,
};
use krs_syntax::KrsSyntax;
use krs_syntax::surface::{AttributeMacro, helper_entry, last_segment_entry};
use krs_syntax::{
    ProvenanceAnchor, ProvenanceRole, StrictnessAttribute, SyntaxTemplateItem, TokenRange,
    parse_seqstrict_attribute, parse_strict_attribute,
};
use proc_macro2::{Span, TokenStream};
use quote::{ToTokens, format_ident, quote};
use syn::spanned::Spanned;
use syn::{Attribute, Ident, Item, ItemStruct, Meta, Path, parse_quote};

use super::factory::{DescriptorFactory, IdentityCheck};
use super::nonce::expansion_nonce;
use super::productions::strictness_tokens;
use super::terms::{WireSlots, wire_key, wire_sort_reference};
use super::tokens::{
    call_site_cfg_attributes, call_site_ident, call_site_path, helper_tokens, sort_type_tokens,
    spelling,
};
use crate::environment::MacroEnvironment;
use crate::provenance::host_provenance;

pub(crate) fn symbol(attributes: TokenStream, item: TokenStream) -> syn::Result<TokenStream> {
    let symbol = krs_syntax::SymbolAttribute::parse_tokens(attributes)?;
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

pub(crate) fn constructor(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> syn::Result<TokenStream> {
    let attribute = krs_syntax::ConstructorAttribute::parse_tokens(attributes)?;
    constructor_like(env, attribute, item, None, None)
}

pub(crate) fn function(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> syn::Result<TokenStream> {
    let function = krs_syntax::FunctionAttribute::parse_tokens(attributes)?;
    let totality_anchor = function
        .provenance()?
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
        .map(|path| -> syn::Result<(ProvenanceAnchor, krs_ir::HookOperation)> {
            let segments = path
                .segments
                .iter()
                .map(|segment| segment.ident.to_string())
                .collect::<Vec<_>>();
            let operation = match segments.as_slice() {
                [module, name] if module == "krypto" && name == "keccak256_raw" => {
                    krs_ir::HookOperation::KryptoKeccak256Raw
                }
                [module, name] if module == "krypto" && name == "sha256_raw" => {
                    krs_ir::HookOperation::KryptoSha256Raw
                }
                [module, name] if module == "krypto" && name == "ripemd160_raw" => {
                    krs_ir::HookOperation::KryptoRipemd160Raw
                }
                [module, name] if module == "krypto" && name == "ecdsa_recover" => {
                    krs_ir::HookOperation::KryptoEcdsaRecover
                }
                [module, name] if module == "krypto" && name == "bn128_valid" => {
                    krs_ir::HookOperation::KryptoBn128Valid
                }
                [module, name] if module == "krypto" && name == "bn128_add" => {
                    krs_ir::HookOperation::KryptoBn128Add
                }
                [module, name] if module == "krypto" && name == "bn128_mul" => {
                    krs_ir::HookOperation::KryptoBn128Mul
                }
                [module, name] if module == "krypto" && name == "bn128_g2_valid" => {
                    krs_ir::HookOperation::KryptoBn128G2Valid
                }
                [module, name] if module == "krypto" && name == "bn128_ate" => {
                    krs_ir::HookOperation::KryptoBn128Ate
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
                        ?,
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
    hook: Option<(ProvenanceAnchor, krs_ir::HookOperation)>,
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
    let declaration = krs_syntax::ConstructorDeclaration::parse_tokens(raw_item.to_token_stream())?;
    attribute.validate_declaration(&declaration)?;
    if let Some(strictness) = &strictness {
        strictness.validate_fields(
            declaration
                .fields()
                .iter()
                .map(krs_syntax::ConstructorField::name),
        )?;
    }
    let facade = env.facade_path()?;
    let mut declaration_anchors = attribute.provenance()?;
    declaration_anchors.extend(declaration.provenance()?);
    if let Some(symbol) = &explicit_symbol {
        declaration_anchors.extend(symbol.provenance()?);
    }
    let fallback = krs_syntax::TokenRange::for_tokens(declaration.item())?;
    let provenance = host_provenance(env, &facade, fallback, &declaration_anchors);
    let mut grammar_anchors = attribute.full_provenance()?;
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
    grammar_anchors.extend(declaration.full_provenance()?);
    if let Some(symbol) = &explicit_symbol {
        grammar_anchors.extend(symbol.provenance()?);
    }
    if let Some(alias) = &alias {
        grammar_anchors.push(alias.clone());
    }
    if functional {
        if total {
            grammar_anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::FunctionDeclaration,
                0,
                TokenRange::for_tokens(declaration.name())?,
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
        grammar_anchors.extend(strictness.provenance()?);
    }
    let grammar_provenance = host_provenance(env, &facade, fallback, &grammar_anchors);
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
    let mut slots = WireSlots::new(&facade);
    let sort_reference = WireSortReference {
        key: wire_key(ProvenanceRole::ConstructorSort, 0),
        target: WireTypeReference {
            slot: slots.type_slot(quote!(#facade::HostTypeKey(#sort_key))),
            authored_path: sort_spelling,
        },
    };
    let mut field_key_functions = Vec::new();
    let mut fields = Vec::new();
    for (index, field) in declaration.fields().iter().enumerate() {
        let key = format_ident!(
            "__krs_constructor_field_{nonce:016x}_{index}",
            span = Span::call_site()
        );
        let generated = call_site_path(field.term_sort().sort())?;
        let generated = sort_type_tokens(&generated, field.term_sort().is_dynamic());
        let spelling = field.term_sort().sort_token_text();
        let field_name = field.name().to_string();
        field_key_functions.push(quote! {
            #(#cfg)*
            #[doc(hidden)]
            fn #key() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<#generated>()
            }
        });
        fields.push(WireConstructorFieldDescriptor {
            name: field_name,
            sort: WireTypeReference {
                slot: slots.type_slot(quote!(#facade::HostTypeKey(#key))),
                authored_path: spelling,
            },
        });
    }
    let wire = WirePayload::Constructor(WireConstructorDescriptor {
        sort: sort_reference,
        fields,
    });
    let wire = serde_json::to_string(&wire).expect("constructor wire is serializable");
    let slot_tokens = slots.tokens();

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
        "",
        functional,
        total,
        hook.as_ref().map(|(_, operation)| operation),
        alias.is_some(),
    )?;

    let factory_tokens = DescriptorFactory {
        facade: &facade,
        factory: &factory,
        name: quote!(#name),
        item_kind: quote!(#facade::ItemKind::Constructor),
        disambiguator: quote!(""),
        identity_check: IdentityCheck::Expect(
            "Cargo and Rust macro context form a valid host identity",
        ),
        declared_type: quote! {
            ::core::option::Option::Some(
                #facade::HostDeclarationIdentity::Nominal(
                    #facade::HostTypeKey(#declared_key),
                ),
            )
        },
        payload: quote!(#facade::__krs_host_payload(#wire, #slot_tokens)),
        cfg: quote!(::core::default::Default::default()),
        attributes: quote!(#(#cfg)*),
        provenance: quote!(#provenance),
        prelude: TokenStream::new(),
    }
    .render();

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

        #factory_tokens

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
            let parsed = krs_syntax::SymbolAttribute::parse_tokens(helper_tokens(
                &attribute,
                "__krs_explicit_symbol",
            )?)?;
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
            Some(entry @ AttributeMacro::Strict) => Some(parse_strict_attribute(helper_tokens(
                &attribute,
                entry.name(),
            )?)?),
            Some(entry @ AttributeMacro::Seqstrict) => Some(parse_seqstrict_attribute(
                helper_tokens(&attribute, entry.name())?,
            )?),
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
            krs_syntax::AliasAttribute::parse_tokens(tokens)?;
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
                TokenRange::for_tokens(&marker.ident)?,
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
            parse_strict_attribute(attributes)?;
        }
        AttributeMacro::Seqstrict => {
            parse_seqstrict_attribute(attributes)?;
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
    let attribute = krs_syntax::TokenAttribute::parse_tokens(attributes)?;
    let declaration = krs_syntax::TokenDeclaration::parse_tokens(item)?;
    let facade = env.facade_path()?;
    let fallback = TokenRange::for_tokens(declaration.item())?;
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
        TokenRange::for_tokens(declaration.name())?,
    );
    let sort_provenance = host_provenance(env, &facade, fallback, &[sort_anchor]);
    let mut grammar_anchors = attribute.provenance()?;
    grammar_anchors.extend(declaration.provenance()?);
    let grammar_provenance = host_provenance(env, &facade, fallback, &grammar_anchors);
    let regex = attribute.regex().value();
    let lexical_precedence =
        attribute
            .lexical_precedence()
            .map(|value| krs_ir::DescriptorLexicalPrecedence {
                key: wire_key(token_lexical_precedence_role, 0),
                value,
            });
    let grammar_name = format!("__krs_grammar_token_{name}");
    let mut slots = WireSlots::new(&facade);
    let token_reference = wire_sort_reference(
        &mut slots,
        &facade,
        ProvenanceRole::TokenDeclaration,
        0,
        &key_fn,
        &name,
    );
    let wire = WirePayload::Grammar(Box::new(WireGrammarDescriptor::Production(
        WireProduction {
            key: wire_key(token_declaration_role, 0),
            template_key: None,
            owner: WireProductionOwner::TokenSort {
                sort: token_reference.clone(),
            },
            result_sort: token_reference,
            items: vec![WireProductionItem::RegexTerminal {
                key: wire_key(token_regex_role, 0),
                precede_regex: None,
                regex: regex.clone(),
                follow_regex: None,
            }],
            attributes: vec![WireProductionAttribute::Token {
                key: wire_key(token_regex_role, 0),
                lexical_precedence,
            }],
        },
    )));
    let wire = serde_json::to_string(&wire).expect("KRS wire values serialize");
    let slot_tokens = slots.tokens();

    let sort_factory_tokens = DescriptorFactory {
        facade: &facade,
        factory: &sort_factory,
        name: quote!(#name),
        item_kind: quote!(#facade::ItemKind::Sort),
        disambiguator: quote!(""),
        identity_check: IdentityCheck::Expect(
            "Cargo and Rust macro context form a valid token-sort identity",
        ),
        declared_type: quote! {
            ::core::option::Option::Some(
                #facade::HostDeclarationIdentity::Nominal(#facade::HostTypeKey(#key_fn)),
            )
        },
        payload: quote! {
            #facade::HostDescriptorPayload::Sort(
                #facade::HostSortDescriptor { parents: ::std::vec![] },
            )
        },
        cfg: quote!(::core::default::Default::default()),
        attributes: quote!(#(#cfg)*),
        provenance: quote!(#sort_provenance),
        prelude: TokenStream::new(),
    }
    .render();
    let grammar_factory_tokens = DescriptorFactory {
        facade: &facade,
        factory: &grammar_factory,
        name: quote!(#grammar_name),
        item_kind: quote!(#facade::ItemKind::Grammar),
        disambiguator: quote!("token"),
        identity_check: IdentityCheck::Expect(
            "Cargo and Rust macro context form a valid token-grammar identity",
        ),
        declared_type: quote!(::core::option::Option::None),
        payload: quote!(#facade::__krs_host_payload(#wire, #slot_tokens)),
        cfg: quote!(::core::default::Default::default()),
        attributes: quote!(#(#cfg)*),
        provenance: quote!(#grammar_provenance),
        prelude: TokenStream::new(),
    }
    .render();

    Ok(quote! {
        #item

        #(#cfg)*
        #[doc(hidden)]
        fn #key_fn() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#declared>()
        }

        #sort_factory_tokens

        #grammar_factory_tokens
    })
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn constructor_grammar(
    facade: &Path,
    attribute: &krs_syntax::ConstructorAttribute,
    declaration: &krs_syntax::ConstructorDeclaration,
    strictness: Option<&StrictnessAttribute>,
    declared_key: &Ident,
    sort_key: &Ident,
    nonce: u64,
    cfg: &[Attribute],
    provenance: &TokenStream,
    disambiguator: &str,
    functional: bool,
    total: bool,
    hook: Option<&krs_ir::HookOperation>,
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
    let mut slots = WireSlots::new(facade);
    let result_sort = wire_sort_reference(
        &mut slots,
        facade,
        ProvenanceRole::ConstructorSort,
        0,
        sort_key,
        &result_sort_spelling,
    );
    let template_key = attribute
        .syntax_template()
        .map(|_| wire_key(ProvenanceRole::ConstructorSyntax, 0));
    let items = constructor_production_wire_items(
        facade,
        attribute.syntax_template(),
        declaration.name(),
        declaration.fields(),
        nonce,
        &mut slots,
    )?;
    let (strict_key_function, _) = strictness_tokens(
        facade,
        strictness,
        declaration
            .fields()
            .iter()
            .map(krs_syntax::ConstructorField::name),
        nonce,
        cfg,
    )?;
    let mut attributes = super::productions::constructor_metadata_wire(
        attribute.group.as_ref().map(syn::LitStr::value),
        attribute.avoid,
        attribute.structured_format(),
    )?;
    attributes.splice(
        0..0,
        super::productions::production_documentation_wire(declaration.documentation())?,
    );
    if functional {
        let function_key = if total {
            ProvenanceRole::FunctionDeclaration
        } else {
            ProvenanceRole::FunctionPartial
        };
        attributes.insert(
            0,
            WireProductionAttribute::Function {
                key: wire_key(function_key, 0),
            },
        );
        if total {
            attributes.insert(
                1,
                WireProductionAttribute::Total {
                    key: wire_key(function_total_role, 0),
                },
            );
        }
    }
    if let Some(operation) = hook {
        attributes.insert(
            if total { 2 } else { 1 },
            WireProductionAttribute::Hook {
                key: wire_key(function_hook_role, 0),
                operation: *operation,
            },
        );
    }
    if alias {
        attributes.insert(
            0,
            WireProductionAttribute::Alias {
                key: wire_key(alias_production_role, 0),
            },
        );
    }
    if let Some(strict_attribute) =
        super::productions::strictness_wire(facade, strictness, nonce, &mut slots)
    {
        attributes.push(strict_attribute);
    }
    let owner_slot = slots.nominal_target_slot(&quote!(#facade::HostTypeKey(#declared_key)));
    let wire = WirePayload::Grammar(Box::new(WireGrammarDescriptor::Production(
        WireProduction {
            key: wire_key(ProvenanceRole::ConstructorDeclaration, 0),
            template_key,
            owner: WireProductionOwner::Constructor {
                constructor: krs_ir::wire::WireApplicationReference {
                    key: wire_key(constructor_declaration_role, 0),
                    target: owner_slot,
                    authored_path: name,
                },
            },
            result_sort,
            items,
            attributes,
        },
    )));
    let wire = serde_json::to_string(&wire).expect("KRS wire values serialize");
    let slot_tokens = slots.tokens();

    let factory_tokens = DescriptorFactory {
        facade,
        factory: &factory,
        name: quote!(#grammar_name),
        item_kind: quote!(#facade::ItemKind::Grammar),
        disambiguator: quote!(#disambiguator),
        identity_check: IdentityCheck::Expect(
            "Cargo and Rust macro context form a valid grammar identity",
        ),
        declared_type: quote!(::core::option::Option::None),
        payload: quote!(#facade::__krs_host_payload(#wire, #slot_tokens)),
        cfg: quote!(::core::default::Default::default()),
        attributes: quote!(#(#cfg)*),
        provenance: quote!(#provenance),
        prelude: TokenStream::new(),
    }
    .render();

    Ok(quote! {
        #strict_key_function

        #factory_tokens
    })
}

fn constructor_production_wire_items(
    facade: &Path,
    template: Option<&krs_syntax::SyntaxTemplate>,
    name: &Ident,
    fields: &[krs_syntax::ConstructorField],
    nonce: u64,
    slots: &mut WireSlots,
) -> syn::Result<Vec<WireProductionItem>> {
    let mut items = Vec::new();
    if let Some(template) = template {
        let mut field_ordinal = 0_u32;
        for (item_index, item) in template.items().iter().enumerate() {
            let item_ordinal = u32::try_from(item_index)
                .map_err(|_| syn::Error::new(name.span(), "too many production items"))?;
            let key = wire_key(ProvenanceRole::ConstructorSyntaxItem, item_ordinal);
            match item {
                SyntaxTemplateItem::Terminal(text) => items.push(WireProductionItem::Terminal {
                    key,
                    text: text.to_owned(),
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
                    let sort_spelling = fields[declaration_index].term_sort().sort_token_text();
                    let sort = wire_sort_reference(
                        slots,
                        facade,
                        ProvenanceRole::ConstructorFieldSort,
                        declaration_ordinal,
                        &sort_key,
                        &sort_spelling,
                    );
                    items.push(WireProductionItem::NonTerminal {
                        key,
                        field_key: wire_key(
                            ProvenanceRole::ConstructorSyntaxFieldReference,
                            field_ordinal,
                        ),
                        declaration_key: Some(wire_key(
                            ProvenanceRole::ConstructorFieldDeclaration,
                            declaration_ordinal,
                        )),
                        field: krs_ir::ProductionFieldId::new(field_name.clone())
                            .expect("Rust field identifiers are valid production fields"),
                        sort: Box::new(sort),
                    });
                    field_ordinal = field_ordinal
                        .checked_add(1)
                        .ok_or_else(|| syn::Error::new(name.span(), "too many fields"))?;
                }
            }
        }
    } else {
        let key = wire_key(ProvenanceRole::ConstructorDeclaration, 0);
        items.push(WireProductionItem::Terminal {
            key,
            text: name.to_string(),
        });
        for (index, field) in fields.iter().enumerate() {
            let ordinal = u32::try_from(index)
                .map_err(|_| syn::Error::new(name.span(), "too many constructor fields"))?;
            let key = wire_key(ProvenanceRole::ConstructorFieldDeclaration, ordinal);
            let sort_key = format_ident!("__krs_constructor_field_{nonce:016x}_{index}");
            let sort_spelling = field.term_sort().sort_token_text();
            items.push(WireProductionItem::NonTerminal {
                key: key.clone(),
                field_key: key.clone(),
                declaration_key: Some(key),
                field: krs_ir::ProductionFieldId::new(field.name().to_string())
                    .expect("Rust field identifiers are valid production fields"),
                sort: Box::new(wire_sort_reference(
                    slots,
                    facade,
                    ProvenanceRole::ConstructorFieldSort,
                    ordinal,
                    &sort_key,
                    &sort_spelling,
                )),
            });
        }
    }
    Ok(items)
}
