//! Single productions: `#[k::symbol]`, `#[k::constructor]`, `#[k::function]`, `#[k::token]`, and the orphan strictness helpers.

use crate::ExpandError;
use krs_diagnostic::codes::expand;
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

use super::factory::{DescriptorFactory, FactoryPayload};
use super::nonce::expansion_nonce;
use super::productions::strictness_key_function;
use super::terms::{WireSlots, wire_key, wire_sort_reference};
use super::tokens::{
    call_site_cfg_attributes, call_site_ident, call_site_path, helper_tokens, sort_type_tokens,
    spelling,
};
use crate::environment::MacroEnvironment;
use crate::provenance::host_provenance;

pub(crate) fn symbol(attributes: TokenStream, item: TokenStream) -> crate::Result<TokenStream> {
    let symbol = krs_syntax::SymbolAttribute::parse_tokens(attributes)?;
    let mut item: Item = syn::parse2(item)?;
    let (attrs, span) = match &mut item {
        Item::Trait(item) => (&mut item.attrs, item.ident.span()),
        Item::Struct(item) => (&mut item.attrs, item.ident.span()),
        _ => {
            return Err(ExpandError::new(
                expand::UNSUPPORTED_SYMBOL_ITEM,
                item.span(),
                "#[k::symbol] currently supports sort traits and constructor structs",
            ));
        }
    };
    if attrs
        .iter()
        .any(|attribute| last_segment_entry(attribute.path()) == Some(AttributeMacro::Symbol))
    {
        return Err(ExpandError::new(
            expand::DUPLICATE_SYMBOL,
            span,
            "duplicate #[k::symbol] attribute",
        ));
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
        return Err(ExpandError::new(
            expand::SYMBOL_ATTRIBUTE_ORDER,
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
) -> crate::Result<TokenStream> {
    let attribute = krs_syntax::ConstructorAttribute::parse_tokens(attributes)?;
    constructor_like(env, attribute, item, None, [None, None], None, None)
}

pub(crate) fn function(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> crate::Result<TokenStream> {
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
        .map(|hook| -> crate::Result<(ProvenanceAnchor, ExpandedHook)> {
            let expanded = match hook {
                krs_syntax::FunctionHook::Catalog(path) => {
                    ExpandedHook::Catalog(catalog_hook(path)?)
                }
                krs_syntax::FunctionHook::Quoted(literal) => quoted_hook(literal, &item)?,
            };
            Ok((
                ProvenanceAnchor::new(ProvenanceRole::FunctionHook, 0, hook.range()?),
                expanded,
            ))
        })
        .transpose()?;
    let memo = function
        .memo()
        .map(|flag| -> crate::Result<ProvenanceAnchor> {
            Ok(ProvenanceAnchor::new(
                ProvenanceRole::FunctionMemo,
                0,
                TokenRange::for_tokens(flag)?,
            ))
        })
        .transpose()?;
    let fresh_generator = function
        .fresh_generator()
        .map(|flag| -> crate::Result<ProvenanceAnchor> {
            Ok(ProvenanceAnchor::new(
                ProvenanceRole::FunctionFreshGenerator,
                0,
                TokenRange::for_tokens(flag)?,
            ))
        })
        .transpose()?;
    let smt = expanded_smt(&function, &item)?;
    constructor_like(
        env,
        function.production().clone(),
        item,
        Some((totality_anchor, function.is_total())),
        [memo, fresh_generator],
        hook,
        smt,
    )
}

/// The `smtlib` or `smt_hook` of a function production, with its provenance
/// anchors and its wire attribute (KF-044).
pub(super) struct ExpandedSmt {
    anchors: Vec<ProvenanceAnchor>,
    attribute: WireProductionAttribute,
}

/// Checks `smt_hook` placeholders against the struct's fields and lowers the
/// function's SMT key to its wire attribute.
fn expanded_smt(
    function: &krs_syntax::FunctionAttribute,
    item: &TokenStream,
) -> crate::Result<Option<ExpandedSmt>> {
    let Some(smt) = function.smt() else {
        return Ok(None);
    };
    let anchors = function
        .provenance()?
        .into_iter()
        .filter(|anchor| {
            matches!(
                anchor.role(),
                ProvenanceRole::FunctionSmtlib
                    | ProvenanceRole::FunctionSmtHook
                    | ProvenanceRole::SmtHookPlaceholder
            )
        })
        .collect();
    let attribute = match smt {
        krs_syntax::FunctionSmt::Smtlib(literal) => WireProductionAttribute::Smtlib {
            key: wire_key(ProvenanceRole::FunctionSmtlib, 0),
            symbol: literal.value(),
        },
        krs_syntax::FunctionSmt::Hook(template) => {
            let fields = syn::parse2::<ItemStruct>(item.clone())
                .map(|item| {
                    item.fields
                        .into_iter()
                        .filter_map(|field| field.ident)
                        .collect::<Vec<_>>()
                })
                .unwrap_or_default();
            function.validate_smt_fields(&fields)?;
            let mut placeholder = 0_u32;
            let fragments = template
                .fragments()
                .iter()
                .map(|fragment| match fragment {
                    krs_syntax::SmtTemplateFragment::Text(text) => krs_ir::DescriptorSmtFragment {
                        key: None,
                        fragment: krs_ir::SmtFragment::Text(text.clone()),
                    },
                    krs_syntax::SmtTemplateFragment::Field(name) => {
                        let key = wire_key(ProvenanceRole::SmtHookPlaceholder, placeholder);
                        placeholder += 1;
                        krs_ir::DescriptorSmtFragment {
                            key: Some(key),
                            fragment: krs_ir::SmtFragment::Field(
                                krs_ir::ProductionFieldId::new(name.clone())
                                    .expect("a checked placeholder is a Rust identifier"),
                            ),
                        }
                    }
                })
                .collect();
            WireProductionAttribute::SmtHook {
                key: wire_key(ProvenanceRole::FunctionSmtHook, 0),
                template: fragments,
            }
        }
    };
    Ok(Some(ExpandedSmt { anchors, attribute }))
}

/// The resolved `hook` value of a function production.
#[derive(Clone, Debug)]
pub(super) enum ExpandedHook {
    /// A typed catalog path.
    Catalog(krs_ir::HookOperation),
    /// A quoted K hook name from the pinned registry.
    Raw { namespace: String, name: String },
}

fn catalog_hook(path: &Path) -> crate::Result<krs_ir::HookOperation> {
    let segments = path
        .segments
        .iter()
        .map(|segment| segment.ident.to_string())
        .collect::<Vec<_>>();
    krs_ir::HookOperation::ALL
        .into_iter()
        .find(|operation| {
            let spec = operation.spec();
            matches!(segments.as_slice(), [module, name] if module == spec.rust_module && name == spec.rust_name)
        })
        .ok_or_else(|| {
            let expected = krs_ir::HookOperation::ALL.map(|operation| {
                let spec = operation.spec();
                format!("`{}::{}`", spec.rust_module, spec.rust_name)
            });
            let (last, preceding) = expected
                .split_last()
                .expect("the hook catalog contains operations");
            ExpandError::new(
                expand::UNKNOWN_HOOK,
                path.span(),
                format!(
                    "unknown KRS hook; expected {}, or {last}",
                    preceding.join(", ")
                ),
            )
        })
}

/// Splits a quoted hook into `NAMESPACE` and `name`: an uppercase namespace
/// (`[A-Z][A-Z0-9_]*`), one `.`, and a name of ASCII letters, digits and `_`.
pub(crate) fn split_quoted_hook(value: &str) -> Option<(&str, &str)> {
    let (namespace, name) = value.split_once('.')?;
    let namespace_ok = namespace.starts_with(|ch: char| ch.is_ascii_uppercase())
        && namespace
            .bytes()
            .all(|byte| byte.is_ascii_uppercase() || byte.is_ascii_digit() || byte == b'_');
    let name_ok = !name.is_empty()
        && name
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_');
    (namespace_ok && name_ok).then_some((namespace, name))
}

/// Checks a quoted hook against the pinned registry. Whether the package may
/// use it (`allow-raw-k`, `profile`) is decided after collection, where the
/// package metadata and `krs --profile` are known.
fn quoted_hook(literal: &syn::LitStr, item: &TokenStream) -> crate::Result<ExpandedHook> {
    let value = literal.value();
    let Some((namespace, name)) = split_quoted_hook(&value) else {
        return Err(ExpandError::new(
            expand::INVALID_HOOK_STRING,
            literal.span(),
            format!(
                "invalid hook string `{value}`; expected NAMESPACE.name, such as \"KRYPTO.keccak256\""
            ),
        ));
    };
    if let Some(operation) = krs_ir::hook_registry::catalogued_hook(&value) {
        let spec = operation.spec();
        return Err(ExpandError::new(
            expand::CATALOGUED_RAW_HOOK,
            literal.span(),
            format!(
                "`{value}` is in the typed hook catalog; use hook = {}::{}",
                spec.rust_module, spec.rust_name
            ),
        ));
    }
    let Some(registered) = krs_ir::hook_registry::registered_hook(&value) else {
        return Err(ExpandError::new(
            expand::UNKNOWN_HOOK_NAME,
            literal.span(),
            format!("`{value}` is not a hook of the pinned K and k-rust; check its spelling"),
        ));
    };
    if let Some(arity) = registered.crypto_arity {
        let fields = syn::parse2::<ItemStruct>(item.clone())
            .map(|item| item.fields.len())
            .unwrap_or_default();
        if fields != usize::from(arity) {
            return Err(ExpandError::new(
                expand::RAW_HOOK_ARITY,
                literal.span(),
                format!(
                    "`{value}` takes {arity} argument{}, but the production has {fields} field{}",
                    if arity == 1 { "" } else { "s" },
                    if fields == 1 { "" } else { "s" },
                ),
            ));
        }
    }
    Ok(ExpandedHook::Raw {
        namespace: namespace.to_owned(),
        name: name.to_owned(),
    })
}

#[expect(
    clippy::needless_pass_by_value,
    clippy::too_many_lines,
    reason = "Constructor metadata and fields are expanded in one pass; the entry point owns the parsed attribute."
)]
fn constructor_like(
    env: &dyn MacroEnvironment,
    attribute: krs_syntax::ConstructorAttribute,
    item: TokenStream,
    totality: Option<(ProvenanceAnchor, bool)>,
    [memo, fresh_generator]: [Option<ProvenanceAnchor>; 2],
    hook: Option<(ProvenanceAnchor, ExpandedHook)>,
    smt: Option<ExpandedSmt>,
) -> crate::Result<TokenStream> {
    let functional = totality.is_some();
    let total = totality.as_ref().is_some_and(|(_, total)| *total);
    let mut raw_item: ItemStruct = syn::parse2(item)?;
    reject_unexpanded_symbol(&raw_item.attrs)?;
    let explicit_symbol = take_explicit_symbol_helper(&mut raw_item.attrs)?;
    let strictness = take_strictness_helpers(&mut raw_item.attrs)?;
    let static_marker = take_static_helper(&mut raw_item.attrs)?;
    if functional && let Some((marker, _)) = &static_marker {
        return Err(ExpandError::new(
            expand::FUNCTION_ALIAS_CONFLICT,
            raw_item.ident.span(),
            match marker.mode() {
                krs_syntax::StaticMode::Alias => {
                    "a function production cannot also be a static alias"
                }
                krs_syntax::StaticMode::Desugar => {
                    "a function production cannot also be a desugar: K expands a desugar before anything runs, while a function is evaluated as rules run"
                }
            },
        ));
    }
    let declaration = krs_syntax::ConstructorDeclaration::parse_tokens(raw_item.to_token_stream())?;
    attribute.validate_declaration(&declaration)?;
    super::productions::check_placement_visibility(
        attribute.placement().zip(attribute.placement_key()),
        &raw_item.vis,
    )?;
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
        return Err(ExpandError::new(
            expand::INVALID_AVOID_METADATA,
            declaration.name().span(),
            "`avoid = false` is not metadata; omit the argument instead",
        ));
    }
    grammar_anchors.extend(declaration.full_provenance()?);
    if let Some(symbol) = &explicit_symbol {
        grammar_anchors.extend(symbol.provenance()?);
    }
    if let Some((marker, anchor)) = &static_marker {
        grammar_anchors.push(anchor.clone());
        grammar_anchors.extend(marker.provenance());
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
    if let Some(anchor) = &memo {
        grammar_anchors.push(anchor.clone());
    }
    if let Some(anchor) = &fresh_generator {
        grammar_anchors.push(anchor.clone());
    }
    if let Some((anchor, _)) = &hook {
        grammar_anchors.push(anchor.clone());
    }
    if let Some(smt) = &smt {
        grammar_anchors.extend(smt.anchors.iter().cloned());
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
    let item = &parametric_item(declaration.item());
    let cfg = call_site_cfg_attributes(&item.attrs)?;
    let name = declaration.name().to_string();
    let declared = call_site_ident(declaration.name())?;
    let authored_sort = &attribute.sort;
    let generated_sort = call_site_path(&attribute.sort)?;
    // A K sort parameter (KF-027) has no `TypeId` in a free function, so each
    // one is a generated marker type whose key the collector joins back to
    // the parameter's name.
    let parameter_markers = declaration
        .sort_parameters()
        .iter()
        .enumerate()
        .map(|(index, _)| {
            (
                format_ident!(
                    "__KrsSortParameter_{nonce:016x}_{index}",
                    span = Span::call_site()
                ),
                format_ident!(
                    "__krs_sort_parameter_{nonce:016x}_{index}",
                    span = Span::call_site()
                ),
            )
        })
        .collect::<Vec<_>>();
    let result_parameter = declaration
        .sort_parameter_index(&attribute.sort)
        .map(|index| parameter_markers[index].0.clone());
    let authored_sort_type = quote!(#authored_sort);
    let generated_sort_type = quote!(#generated_sort);
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
        let generated = if let Some(parameter) = field.parameter() {
            let marker = &parameter_markers[parameter].0;
            quote!(#marker)
        } else {
            let generated = call_site_path(field.term_sort().sort())?;
            sort_type_tokens(&facade, &generated, field.term_sort().is_dynamic())
        };
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
    let parameters = parameter_wire_references(
        &facade,
        declaration.sort_parameters(),
        &parameter_markers,
        &mut slots,
    );
    let wire = WirePayload::Constructor(WireConstructorDescriptor {
        sort: sort_reference,
        fields,
        parameters,
    });
    let wire = serde_json::to_string(&wire).expect("constructor wire is serializable");
    let slot_tokens = slots.tokens();

    let generic_parameters = declaration.sort_parameters();
    let rule_application = quote! {
        #(#cfg)*
        impl<#(#generic_parameters: ?Sized + 'static,)* const __KRS_SELECTOR: u64>
            #facade::__KrsRuleApplication<__KRS_SELECTOR>
            for #declared<#(#generic_parameters),*>
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
        &parameter_markers,
        nonce,
        &cfg,
        &grammar_provenance,
        "",
        functional,
        total,
        [memo.is_some(), fresh_generator.is_some()],
        hook.as_ref().map(|(_, operation)| operation),
        smt.map(|smt| smt.attribute),
        static_marker.as_ref().map(|(marker, _)| *marker),
    )?;

    let factory_tokens = DescriptorFactory {
        facade: &facade,
        factory: &factory,
        name: quote!(#name),
        item_kind: quote!(#facade::ItemKind::Constructor),
        disambiguator: quote!(""),
        identity_label: "Cargo and Rust macro context form a valid host identity",
        declared_type: quote! {
            ::core::option::Option::Some(
                #facade::HostDeclarationIdentity::Nominal(
                    #facade::HostTypeKey(#declared_key),
                ),
            )
        },
        payload: FactoryPayload::wire(wire, slot_tokens),
        cfg: quote!(::core::default::Default::default()),
        attributes: quote!(#(#cfg)*),
        provenance: quote!(#provenance),
        prelude: TokenStream::new(),
    }
    .render();

    let sort_check = if result_parameter.is_some() {
        TokenStream::new()
    } else {
        quote! {
            #(#cfg)*
            const _: ::core::marker::PhantomData<#authored_sort_type> =
                ::core::marker::PhantomData;
        }
    };
    let generated_sort_type =
        result_parameter.map_or(generated_sort_type, |marker| quote!(#marker));
    let parameter_items = parameter_markers.iter().map(|(marker, key)| {
        quote! {
            #(#cfg)*
            #[doc(hidden)]
            #[allow(non_camel_case_types)]
            enum #marker {}

            #(#cfg)*
            #[doc(hidden)]
            fn #key() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<#marker>()
            }
        }
    });

    Ok(quote! {
        #item

        #sort_check

        #(#parameter_items)*

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

/// The declared struct as rustc sees it. Each K sort parameter gets the
/// default `dyn ::core::any::Any`, so `TypeId::of::<Choose>()` names the one
/// canonical instantiation that keys the declaration and every application,
/// with or without a turbofish (KF-027). Authors cannot write a default.
fn parametric_item(item: &ItemStruct) -> ItemStruct {
    let mut item = item.clone();
    for parameter in &mut item.generics.params {
        if let syn::GenericParam::Type(parameter) = parameter {
            parameter.eq_token = Some(syn::Token![=](Span::call_site()));
            parameter.default = Some(syn::parse_quote!(dyn ::core::any::Any));
        }
    }
    item
}

/// One sort reference per K sort parameter, keyed `sort_parameter` in
/// declaration order, whose slot is the parameter's marker type (KF-027).
fn parameter_wire_references(
    facade: &Path,
    parameters: &[Ident],
    markers: &[(Ident, Ident)],
    slots: &mut WireSlots,
) -> Vec<WireSortReference> {
    parameters
        .iter()
        .zip(markers)
        .enumerate()
        .map(|(ordinal, (parameter, (_, key)))| {
            wire_sort_reference(
                slots,
                facade,
                ProvenanceRole::SortParameter,
                u32::try_from(ordinal).expect("sort parameters are few"),
                key,
                &parameter.to_string(),
            )
        })
        .collect()
}

pub(super) fn reject_unexpanded_symbol(attributes: &[Attribute]) -> crate::Result<()> {
    if let Some(attribute) = attributes
        .iter()
        .find(|attribute| last_segment_entry(attribute.path()) == Some(AttributeMacro::Symbol))
    {
        return Err(ExpandError::new(
            expand::SYMBOL_ATTRIBUTE_ORDER,
            attribute.span(),
            "#[k::symbol] must appear before the symbol-bearing KRS declaration attribute",
        ));
    }
    Ok(())
}

pub(super) fn take_explicit_symbol_helper(
    attributes: &mut Vec<Attribute>,
) -> crate::Result<Option<krs_syntax::SymbolAttribute>> {
    let mut symbol = None;
    let mut retained = Vec::with_capacity(attributes.len());
    for attribute in std::mem::take(attributes) {
        if attribute.path().is_ident("__krs_explicit_symbol") {
            let parsed = krs_syntax::SymbolAttribute::parse_tokens(helper_tokens(
                &attribute,
                "__krs_explicit_symbol",
            )?)?;
            if symbol.replace(parsed).is_some() {
                return Err(ExpandError::new(
                    expand::DUPLICATE_SYMBOL,
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
) -> crate::Result<Option<StrictnessAttribute>> {
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
                return Err(ExpandError::new(
                    expand::DUPLICATE_STRICTNESS,
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

/// Takes the struct's `#[k::alias]` or `#[k::desugar]` production marker
/// (KF-028), with the anchor of its name.
fn take_static_helper(
    attributes: &mut Vec<Attribute>,
) -> crate::Result<Option<(krs_syntax::StaticProductionAttribute, ProvenanceAnchor)>> {
    let mut found: Option<(krs_syntax::StaticProductionAttribute, ProvenanceAnchor)> = None;
    let mut retained = Vec::with_capacity(attributes.len());
    for attribute in std::mem::take(attributes) {
        let mode = match helper_entry(attribute.path()) {
            Some(AttributeMacro::Alias) => krs_syntax::StaticMode::Alias,
            Some(AttributeMacro::Desugar) => krs_syntax::StaticMode::Desugar,
            _ => {
                retained.push(attribute);
                continue;
            }
        };
        let tokens = match &attribute.meta {
            Meta::Path(_) => TokenStream::new(),
            Meta::List(list) => list.tokens.clone(),
            Meta::NameValue(_) => {
                return Err(ExpandError::new(
                    expand::ALIAS_MARKER_FORM,
                    attribute.span(),
                    format!("`{}` must use marker syntax", mode.name()),
                ));
            }
        };
        let marker = krs_syntax::StaticProductionAttribute::parse_marker(mode, tokens)?;
        let name = attribute
            .path()
            .segments
            .last()
            .expect("helper attributes have a final path segment");
        if let Some((previous, _)) = &found {
            return Err(ExpandError::new(
                expand::DUPLICATE_ALIAS,
                name.ident.span(),
                if previous.mode() == mode {
                    format!("a constructor may declare `{}` only once", mode.name())
                } else {
                    "a production is an alias or a desugar, not both: `alias` also prints backwards, `desugar` only expands".to_owned()
                },
            ));
        }
        let anchor = ProvenanceAnchor::new(
            mode.production_role(),
            0,
            TokenRange::for_tokens(&name.ident)?,
        );
        found = Some((marker, anchor));
    }
    *attributes = retained;
    Ok(found)
}

pub(crate) fn orphan_strictness(
    entry: AttributeMacro,
    attributes: TokenStream,
    _item: TokenStream,
) -> crate::Result<TokenStream> {
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
    Err(ExpandError::new(
        expand::ORPHAN_HELPER,
        Span::call_site(),
        format!("`#[k::{name}]` is a constructor helper; place `#[k::constructor(...)]` before it"),
    ))
}

/// Removes the `#[k::token]` attributes stacked below the expanding one and
/// returns them in source order; rustc would otherwise expand each again.
fn take_stacked_token_attributes(
    attributes: &mut Vec<Attribute>,
) -> crate::Result<Vec<krs_syntax::TokenAttribute>> {
    let mut stacked = Vec::new();
    let mut retained = Vec::with_capacity(attributes.len());
    for attribute in std::mem::take(attributes) {
        if helper_entry(attribute.path()) == Some(AttributeMacro::Token) {
            stacked.push(krs_syntax::TokenAttribute::parse_tokens(helper_tokens(
                &attribute, "token",
            )?)?);
        } else {
            retained.push(attribute);
        }
    }
    *attributes = retained;
    Ok(stacked)
}

/// Rejects a token-struct field that names anything but std's `String`, such
/// as the K marker `k::builtin::string::String`, with the lint's own message.
fn token_field_check(item: &ItemStruct, cfg: &[Attribute]) -> TokenStream {
    let syn::Fields::Unnamed(fields) = &item.fields else {
        return TokenStream::new();
    };
    let Some(field) = fields.unnamed.first() else {
        return TokenStream::new();
    };
    let ty = &field.ty;
    quote! {
        #(#cfg)*
        const _: () = {
            #[diagnostic::on_unimplemented(
                message = "this field resolves to the K String marker; token carriers use std's String: import `k::builtin::string` as a module, not `string::String`",
                label = "a token struct's field is std's `String`, which stores nothing at runtime"
            )]
            trait KrsTokenCarrierField {}
            impl KrsTokenCarrierField for ::std::string::String {}
            const fn krs_token_carrier_field<T: KrsTokenCarrierField + ?Sized>() {}
            krs_token_carrier_field::<#ty>();
        };
    }
}

#[expect(
    clippy::too_many_lines,
    reason = "Token metadata and carrier items are emitted together."
)]
pub(crate) fn token(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> crate::Result<TokenStream> {
    let first = krs_syntax::TokenAttribute::parse_tokens(attributes)?;
    let mut item: Item = syn::parse2(item)?;
    let stacked = match &mut item {
        Item::Struct(item) => take_stacked_token_attributes(&mut item.attrs)?,
        Item::Type(item) => take_stacked_token_attributes(&mut item.attrs)?,
        _ => Vec::new(),
    };
    let declaration = krs_syntax::TokenDeclaration::parse_tokens(item.to_token_stream())?;
    let mut all = vec![first];
    all.extend(stacked);
    let stack = krs_syntax::TokenStack::new(all)?;
    let facade = env.facade_path()?;
    let fallback = TokenRange::for_tokens(&item)?;
    let nonce = expansion_nonce(env, "token", declaration.name(), fallback);
    let key_fn = format_ident!("__krs_token_type_{nonce:016x}");
    let sort_factory = format_ident!("__krs_token_sort_descriptor_{nonce:016x}");
    let grammar_factory = format_ident!("__krs_token_grammar_descriptor_{nonce:016x}");
    let cfg = call_site_cfg_attributes(declaration.attributes())?;
    let name = declaration.name().to_string();
    let declared = call_site_ident(declaration.name())?;

    let mut grammar_anchors = stack.provenance()?;
    grammar_anchors.extend(declaration.provenance()?);
    let grammar_provenance = host_provenance(env, &facade, fallback, &grammar_anchors);
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
    let productions = stack
        .ordinals()
        .into_iter()
        .map(|(ordinal, attribute)| {
            let role = attribute.content().role();
            let item = match attribute.content() {
                krs_syntax::TokenContent::Regex(literal) => WireProductionItem::RegexTerminal {
                    key: wire_key(role, ordinal),
                    precede_regex: None,
                    regex: literal.value(),
                    follow_regex: None,
                },
                krs_syntax::TokenContent::Terminal(literal) => WireProductionItem::Terminal {
                    key: wire_key(role, ordinal),
                    text: literal.value(),
                },
            };
            WireProduction {
                parameters: Vec::new(),
                key: wire_key(role, ordinal),
                template_key: None,
                owner: WireProductionOwner::TokenSort {
                    sort: token_reference.clone(),
                },
                result_sort: token_reference.clone(),
                items: vec![item],
                attributes: vec![WireProductionAttribute::Token {
                    key: wire_key(role, ordinal),
                    lexical_precedence: attribute.lexical_precedence().map(|value| {
                        krs_ir::DescriptorLexicalPrecedence {
                            key: wire_key(ProvenanceRole::TokenLexicalPrecedence, ordinal),
                            value,
                        }
                    }),
                }],
            }
        })
        .collect();
    let wire = WirePayload::Grammar(Box::new(WireGrammarDescriptor::Tokens { productions }));
    let wire = serde_json::to_string(&wire).expect("KRS wire values serialize");
    let slot_tokens = slots.tokens();

    let grammar_factory_tokens = DescriptorFactory {
        facade: &facade,
        factory: &grammar_factory,
        name: quote!(#grammar_name),
        item_kind: quote!(#facade::ItemKind::Grammar),
        disambiguator: quote!("token"),
        identity_label: "Cargo and Rust macro context form a valid token-grammar identity",
        declared_type: quote!(::core::option::Option::None),
        payload: FactoryPayload::wire(wire, slot_tokens),
        cfg: quote!(::core::default::Default::default()),
        attributes: quote!(#(#cfg)*),
        provenance: quote!(#grammar_provenance),
        prelude: TokenStream::new(),
    }
    .render();

    // A struct declares a new closed token sort; a type alias adds token
    // productions to the sort it names and declares nothing else.
    let (sort_factory_tokens, field_check) = match declaration.carrier() {
        krs_syntax::TokenCarrier::Struct(item_struct) => {
            let sort_anchor = ProvenanceAnchor::new(
                ProvenanceRole::SortDeclaration,
                0,
                TokenRange::for_tokens(declaration.name())?,
            );
            let sort_provenance = host_provenance(env, &facade, fallback, &[sort_anchor]);
            let sort_wire =
                serde_json::to_string(&WirePayload::Sort(krs_ir::wire::WireSortDescriptor {
                    parents: Vec::new(),
                }))
                .expect("KRS wire values serialize");
            let factory = DescriptorFactory {
                facade: &facade,
                factory: &sort_factory,
                name: quote!(#name),
                item_kind: quote!(#facade::ItemKind::Sort),
                disambiguator: quote!(""),
                identity_label: "Cargo and Rust macro context form a valid token-sort identity",
                declared_type: quote! {
                    ::core::option::Option::Some(
                        #facade::HostDeclarationIdentity::Nominal(#facade::HostTypeKey(#key_fn)),
                    )
                },
                payload: FactoryPayload::wire(sort_wire, quote!(#facade::__KrsSlots::default())),
                cfg: quote!(::core::default::Default::default()),
                attributes: quote!(#(#cfg)*),
                provenance: quote!(#sort_provenance),
                prelude: TokenStream::new(),
            }
            .render();
            (factory, token_field_check(item_struct, &cfg))
        }
        krs_syntax::TokenCarrier::Alias(_) => (TokenStream::new(), TokenStream::new()),
    };

    Ok(quote! {
        #item

        #(#cfg)*
        #[doc(hidden)]
        fn #key_fn() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#declared>()
        }

        #field_check

        #sort_factory_tokens

        #grammar_factory_tokens
    })
}

#[expect(
    clippy::too_many_arguments,
    clippy::too_many_lines,
    reason = "Grammar lowering retains all declaration context in one expansion."
)]
fn constructor_grammar(
    facade: &Path,
    attribute: &krs_syntax::ConstructorAttribute,
    declaration: &krs_syntax::ConstructorDeclaration,
    strictness: Option<&StrictnessAttribute>,
    declared_key: &Ident,
    sort_key: &Ident,
    parameter_markers: &[(Ident, Ident)],
    nonce: u64,
    cfg: &[Attribute],
    provenance: &TokenStream,
    disambiguator: &str,
    functional: bool,
    total: bool,
    [memo, fresh_generator]: [bool; 2],
    hook: Option<&ExpandedHook>,
    smt: Option<WireProductionAttribute>,
    static_marker: Option<krs_syntax::StaticProductionAttribute>,
) -> crate::Result<TokenStream> {
    let function_total_role = ProvenanceRole::FunctionTotal;
    let function_hook_role = ProvenanceRole::FunctionHook;
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
    let strict_key_function = strictness_key_function(
        strictness,
        declaration
            .fields()
            .iter()
            .map(krs_syntax::ConstructorField::name),
        nonce,
        cfg,
    )?;
    let overload = attribute.overload().map(|target| {
        super::productions::overload_wire(
            facade,
            target,
            &format_ident!("__krs_overload_target_{nonce:016x}"),
            cfg,
            &mut slots,
        )
    });
    let overload_tokens = overload
        .as_ref()
        .map(|overload| overload.tokens.clone())
        .unwrap_or_default();
    let mut attributes = super::productions::constructor_metadata_wire(
        attribute.group.as_ref().map(syn::LitStr::value),
        attribute.avoid,
        attribute.prefer(),
        attribute.placement(),
        overload.map(|overload| overload.attribute),
        &super::productions::ColorMetadata {
            color: attribute.color(),
            colors: attribute.colors(),
        },
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
    if let Some(hook) = hook {
        let key = wire_key(function_hook_role, 0);
        attributes.insert(
            if total { 2 } else { 1 },
            match hook {
                ExpandedHook::Catalog(operation) => WireProductionAttribute::Hook {
                    key,
                    operation: *operation,
                },
                ExpandedHook::Raw { namespace, name } => WireProductionAttribute::RawHook {
                    key,
                    namespace: namespace.clone(),
                    name: name.clone(),
                },
            },
        );
    }
    // K's memo hint follows the function and totality markers.
    if memo {
        attributes.insert(
            if total { 2 } else { 1 },
            WireProductionAttribute::Memo {
                key: wire_key(ProvenanceRole::FunctionMemo, 0),
            },
        );
    }
    // `freshGenerator` follows them and the memo hint (KF-022).
    if fresh_generator {
        attributes.insert(
            1 + usize::from(total) + usize::from(memo),
            WireProductionAttribute::FreshGenerator {
                key: wire_key(ProvenanceRole::FunctionFreshGenerator, 0),
            },
        );
    }
    // `smtlib` or `smt-hook` follows them and the hook (KF-044), as in KEVM's
    // `[function, total, hook(..), smtlib(..)]`.
    if let Some(smt) = smt {
        attributes.insert(
            1 + usize::from(total)
                + usize::from(memo)
                + usize::from(fresh_generator)
                + usize::from(hook.is_some()),
            smt,
        );
    }
    if let Some(marker) = &static_marker {
        attributes.insert(0, super::productions::static_mode_wire(marker));
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
            parameters: parameter_wire_references(
                facade,
                declaration.sort_parameters(),
                parameter_markers,
                &mut slots,
            ),
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
        identity_label: "Cargo and Rust macro context form a valid grammar identity",
        declared_type: quote!(::core::option::Option::None),
        payload: FactoryPayload::wire(wire, slot_tokens),
        cfg: quote!(::core::default::Default::default()),
        attributes: quote!(#(#cfg)*),
        provenance: quote!(#provenance),
        prelude: TokenStream::new(),
    }
    .render();

    Ok(quote! {
        #strict_key_function
        #overload_tokens

        #factory_tokens
    })
}

#[expect(
    clippy::too_many_lines,
    reason = "Template fields and production slots are lowered in one ordered pass."
)]
fn constructor_production_wire_items(
    facade: &Path,
    template: Option<&krs_syntax::SyntaxTemplate>,
    name: &Ident,
    fields: &[krs_syntax::ConstructorField],
    nonce: u64,
    slots: &mut WireSlots,
) -> crate::Result<Vec<WireProductionItem>> {
    let mut items = Vec::new();
    if let Some(template) = template {
        let mut field_ordinal = 0_u32;
        for (item_index, item) in template.items().iter().enumerate() {
            let item_ordinal = u32::try_from(item_index).map_err(|_| {
                ExpandError::new(
                    expand::DESCRIPTOR_CAPACITY,
                    name.span(),
                    "too many production items",
                )
            })?;
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
                            ExpandError::new(
                                expand::MISSING_CHECKED_FIELD,
                                name.span(),
                                "checked template field disappeared",
                            )
                        })?;
                    let declaration_ordinal = u32::try_from(declaration_index).map_err(|_| {
                        ExpandError::new(
                            expand::DESCRIPTOR_CAPACITY,
                            name.span(),
                            "too many constructor fields",
                        )
                    })?;
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
                    field_ordinal = field_ordinal.checked_add(1).ok_or_else(|| {
                        ExpandError::new(
                            expand::DESCRIPTOR_CAPACITY,
                            name.span(),
                            "too many fields",
                        )
                    })?;
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
            let ordinal = u32::try_from(index).map_err(|_| {
                ExpandError::new(
                    expand::DESCRIPTOR_CAPACITY,
                    name.span(),
                    "too many constructor fields",
                )
            })?;
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
