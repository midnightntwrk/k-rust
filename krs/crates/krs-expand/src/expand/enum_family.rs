//! Enum production families: `#[k::constructors]`.

use crate::ExpandError;
use krs_diagnostic::codes::expand;
use krs_syntax::KrsSyntax;
use std::collections::BTreeMap;

use krs_ir::wire::{
    WireApplicationReference, WireConstructorDescriptor, WireConstructorFieldDescriptor,
    WireGrammarDescriptor, WirePayload, WireProduction, WireProductionAttribute,
    WireProductionOwner, WireSortReference, WireTypeReference,
};
use krs_ir::{
    DescriptorAssociativitySentence, DescriptorGroupReference, DescriptorPrecedenceChain,
    ENUM_VARIANT_DISAMBIGUATOR_PREFIX, GroupAssociativity, ProductionGroupId,
};
use krs_syntax::{
    GroupAssociativity as SyntaxGroupAssociativity, ProvenanceRole, SyntaxTemplateItem, TokenRange,
};
use proc_macro2::TokenStream;
use quote::{ToTokens, format_ident, quote};
use syn::{Attribute, Ident, ItemEnum, Path};

use super::factory::{DescriptorFactory, FactoryPayload};
use super::grammar::grammar_macro_descriptor;
use super::nonce::{expansion_nonce, rule_application_selector};
use super::productions::strictness_key_function;
use super::terms::{WireSlots, read_key, wire_key, wire_sort_reference};
use super::tokens::{
    call_site_cfg_attributes, call_site_ident, call_site_path, sort_type_tokens, spelling,
    variant_marker_function,
};
use crate::environment::MacroEnvironment;
use crate::provenance::host_provenance;

pub(crate) fn constructors(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> crate::Result<TokenStream> {
    let stand_in = enum_stand_in(env, &item, false);
    constructors_inner(env, attributes, item).map_err(|error| error.with_stand_in(stand_in))
}

/// The items a failed `#[k::constructors]` or `#[k::syntax_list]` enum leaves
/// in place of its expansion, so that the names it declares still resolve and
/// rustc reports nothing beyond the KRS diagnostics: a `use Enum::*;` or
/// `use Enum::Variant;` whose first segment names nothing is an error rustc
/// does not silence after a `compile_error!`.
///
/// The stand-in declares only what the authored item states independently of
/// the failed KRS judgement: the enum's name, visibility, documentation, and
/// `#[cfg]`, and each variant's name, kind, documentation, and `#[cfg]`. The
/// variants have no fields, since generated code names a variant only by the
/// pattern `Variant { .. }` and a field type can depend on what failed (a
/// readable list's tail is rewritten on success). Beside it stands the
/// generated interface other expansions name: one marker function and one
/// `__KrsRuleApplication` impl per variant, and for a syntactic list its sort marker trait and `KItemSort` impl. Nothing in it
/// runs: the diagnostics' `compile_error!` stops every build that contains it.
/// It is empty when the item is not an enum, the facade cannot be resolved,
/// or a `#[cfg]` cannot be reproduced.
pub(super) fn enum_stand_in(
    env: &dyn MacroEnvironment,
    item: &TokenStream,
    syntax_list: bool,
) -> TokenStream {
    let Ok(facade) = env.facade_path() else {
        return TokenStream::new();
    };
    let Ok(item) = syn::parse2::<ItemEnum>(item.clone()) else {
        return TokenStream::new();
    };
    let (Ok(cfg), Ok(enum_ident)) = (
        call_site_cfg_attributes(&item.attrs),
        call_site_ident(&item.ident),
    ) else {
        return TokenStream::new();
    };
    let attributes = item
        .attrs
        .iter()
        .filter(|attribute| attribute.path().is_ident("doc") || attribute.path().is_ident("cfg"));
    let visibility = &item.vis;
    let name = &item.ident;
    let dead_code =
        (!matches!(item.vis, syn::Visibility::Public(_))).then(|| quote!(#[allow(dead_code)]));
    let mut variants = Vec::new();
    let mut markers = Vec::new();
    let mut rule_applications = Vec::new();
    let mut selectors = std::collections::BTreeSet::new();
    for variant in &item.variants {
        // Variants that collide in rule resolution are a KRS error
        // (`enum-variant-collision`); the stand-in keeps the first, so it
        // declares no conflicting item of its own.
        let selector = rule_application_selector(&variant.ident);
        if !selectors.insert(selector) {
            continue;
        }
        let Ok(variant_cfg) = call_site_cfg_attributes(&variant.attrs) else {
            return TokenStream::new();
        };
        let attributes = variant.attrs.iter().filter(|attribute| {
            attribute.path().is_ident("doc") || attribute.path().is_ident("cfg")
        });
        let ident = &variant.ident;
        let fields = match &variant.fields {
            syn::Fields::Named(_) => quote!({}),
            syn::Fields::Unnamed(_) => quote!(()),
            syn::Fields::Unit => TokenStream::new(),
        };
        variants.push(quote!(#(#attributes)* #ident #fields));
        let marker = variant_marker_function(ident);
        markers.push(quote! {
            #(#variant_cfg)*
            #[doc(hidden)]
            #[allow(non_snake_case)]
            pub fn #marker() -> ::core::any::TypeId {
                ::core::unreachable!("a failed KRS enum has no variant markers")
            }
        });
        rule_applications.push(quote! {
            #(#cfg)*
            #(#variant_cfg)*
            impl #facade::__KrsRuleApplication<#selector> for #enum_ident {
                fn __krs_rule_application(
                    _authored_path: &str,
                ) -> #facade::HostApplicationTarget {
                    ::core::unreachable!("a failed KRS enum has no rule applications")
                }
            }
        });
    }
    let list_sort = syntax_list.then(|| {
        let marker = format_ident!("{}Sort", item.ident, span = proc_macro2::Span::call_site());
        quote! {
            #(#cfg)*
            #[doc(hidden)]
            pub trait #marker: #facade::KItemSort {}

            #(#cfg)*
            impl #facade::KItemSort for #enum_ident {}
        }
    });
    quote! {
        #(#attributes)*
        #dead_code
        #visibility enum #name {
            #(#variants,)*
        }

        #(#cfg)*
        #[allow(dead_code)]
        impl #enum_ident {
            #(#markers)*
        }

        #(#rule_applications)*

        #list_sort
    }
}

#[expect(
    clippy::too_many_lines,
    reason = "The enum family and its variants share one descriptor expansion."
)]
fn constructors_inner(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> crate::Result<TokenStream> {
    let attribute = krs_syntax::ConstructorsAttribute::parse_tokens(attributes)?;
    let item: ItemEnum = syn::parse2(item)?;
    let declaration = krs_syntax::EnumConstructorDeclaration::from_parts(&attribute, item)?;
    if let Some(internal) = attribute.internal() {
        super::productions::check_placement_visibility(
            Some((krs_syntax::PlacementFlag::Internal, internal)),
            &declaration.item().vis,
        )?;
    }
    for variant in declaration.variants() {
        if let Some(syntax) = variant.syntax() {
            super::productions::check_placement_visibility(
                syntax.placement().zip(syntax.placement_key()),
                &declaration.item().vis,
            )?;
        }
    }
    let facade = env.facade_path()?;
    let fallback = TokenRange::for_tokens(declaration.item())?;
    let nonce = expansion_nonce(env, "constructors", declaration.enum_name(), fallback);
    let cfg = call_site_cfg_attributes(&declaration.item().attrs)?;
    let enum_ident = call_site_ident(declaration.enum_name())?;
    let enum_name = declaration.enum_name().to_string();
    let enum_key = format_ident!("__krs_enum_type_{nonce:016x}");
    // Keep the family's authored sort attached to the
    // `constructors(sort = ...)` token. This witness is the semantic bridge
    // rust-analyzer needs for definition and rename through the consumed
    // procedural-attribute argument.
    let outer_path = declaration.sort();
    let family_sort_key = format_ident!("__krs_enum_family_sort_{nonce:016x}");
    let item = declaration.item();

    let mut marker_types = Vec::new();
    let mut associated_keys = Vec::new();
    let mut rule_applications = Vec::new();
    let mut variant_expansions = Vec::new();
    let mut rule_application_selectors = BTreeMap::new();
    for (index, variant) in declaration.variants().iter().enumerate() {
        let marker = format_ident!("__KrsEnumVariant_{nonce:016x}_{index}");
        let variant_key = format_ident!("__krs_enum_variant_{nonce:016x}_{index}");
        let associated = variant_marker_function(variant.name());
        marker_types.push(quote! {
            #(#cfg)*
            #[doc(hidden)]
            struct #marker;

            #(#cfg)*
            #[doc(hidden)]
            fn #variant_key() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<#marker>()
            }
        });
        associated_keys.push(quote! {
            #[doc(hidden)]
            #[allow(non_snake_case)]
            pub fn #associated() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<#marker>()
            }
        });
        let selector = rule_application_selector(variant.name());
        if let Some(previous) = rule_application_selectors.insert(selector, variant.name()) {
            return Err(ExpandError::new(
                expand::ENUM_VARIANT_COLLISION,
                variant.name().span(),
                format!(
                    "enum variants `{previous}` and `{}` collide in readable rule resolution",
                    variant.name()
                ),
            ));
        }
        let variant_name = variant.name().to_string();
        let application_path = format!("{enum_name}::{variant_name}");
        rule_applications.push(quote! {
            #(#cfg)*
            impl #facade::__KrsRuleApplication<#selector> for #enum_ident {
                fn __krs_rule_application(
                    _authored_path: &str,
                ) -> #facade::HostApplicationTarget {
                    #facade::HostApplicationTarget::EnumVariant(
                        #facade::HostEnumVariantReference::new(
                            #facade::HostTypeReference {
                                key: #facade::HostTypeKey(#enum_key),
                                authored_path: #enum_name.to_owned(),
                            },
                            #facade::HostTypeKey(#variant_key),
                            #application_path,
                        )
                        .expect("generated enum variants retain their owning enum path"),
                    )
                }
            }
        });
        variant_expansions.push(expand_enum_variant(
            env,
            &facade,
            &declaration,
            variant,
            &enum_key,
            &family_sort_key,
            &variant_key,
            nonce,
            index,
            &cfg,
        )?);
    }

    let open_sort_key = quote! {
        #(#cfg)*
        #[doc(hidden)]
        fn #family_sort_key() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#outer_path>()
        }
    };
    let family_grammar = expand_enum_family_grammar(
        env,
        &facade,
        &declaration,
        nonce,
        &enum_name,
        &cfg,
        fallback,
    )?;

    // Only K rules construct the variants of a family that is not `pub`, so
    // rustc would report them as never constructed.
    let dead_code =
        (!matches!(item.vis, syn::Visibility::Public(_))).then(|| quote!(#[allow(dead_code)]));

    Ok(quote! {
        #dead_code
        #item

        #(#cfg)*
        #[doc(hidden)]
        fn #enum_key() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#enum_ident>()
        }

        #open_sort_key

        #(#marker_types)*

        #(#cfg)*
        impl #enum_ident {
            #(#associated_keys)*
        }

        #(#rule_applications)*

        #(#variant_expansions)*
        #family_grammar
    })
}

fn enum_precedence_group_name(
    declaration: &krs_syntax::EnumConstructorDeclaration,
    ordinal: usize,
) -> String {
    declaration
        .precedence_groups()
        .nth(ordinal)
        .expect("enum precedence ordinal identifies a parsed group")
        .emitted_name(declaration.enum_name(), ordinal)
}

#[expect(
    clippy::too_many_lines,
    reason = "The family's precedence and associativity descriptors are lowered together."
)]
fn expand_enum_family_grammar(
    env: &dyn MacroEnvironment,
    facade: &Path,
    declaration: &krs_syntax::EnumConstructorDeclaration,
    nonce: u64,
    enum_name: &str,
    cfg: &[Attribute],
    fallback: TokenRange,
) -> crate::Result<TokenStream> {
    let precedence_group_reference_role = ProvenanceRole::PrecedenceGroupReference;
    let precedence_declaration_role = ProvenanceRole::PrecedenceDeclaration;
    let precedence_chain_role = ProvenanceRole::PrecedenceChain;
    let associativity_sentence_role = ProvenanceRole::AssociativitySentence;
    let associativity_group_reference_role = ProvenanceRole::AssociativityGroupReference;
    let associativity_declaration_role = ProvenanceRole::AssociativityDeclaration;
    let mut output = Vec::new();
    if let Some(precedence) = declaration.precedence_descriptor()? {
        let provenance = host_provenance(env, facade, fallback, &precedence.provenance);
        let factory = format_ident!("__krs_enum_precedence_{nonce:016x}");
        let name = format!("__krs_grammar_{enum_name}_precedence");
        let mut group_ordinal = 0_usize;
        let groups = precedence.groups.try_map_ref(|group| -> crate::Result<_> {
            let ordinal = group_ordinal;
            group_ordinal += 1;
            let name = group.emitted_name(declaration.enum_name(), ordinal);
            let ordinal = u32::try_from(ordinal).map_err(|_| {
                ExpandError::new(
                    expand::DESCRIPTOR_CAPACITY,
                    declaration.enum_name().span(),
                    "too many groups",
                )
            })?;
            Ok(DescriptorGroupReference {
                key: read_key(
                    group.precedence_key(),
                    wire_key(precedence_group_reference_role, ordinal),
                ),
                group: ProductionGroupId::new(name)
                    .expect("generated enum groups are valid identities"),
            })
        })?;
        let grammar = WireGrammarDescriptor::Precedence {
            key: read_key(
                declaration.precedence_declaration_key(),
                wire_key(precedence_declaration_role, 0),
            ),
            chains: vec![DescriptorPrecedenceChain {
                key: read_key(
                    declaration.precedence_chain_key(),
                    wire_key(precedence_chain_role, 0),
                ),
                groups,
            }],
        };
        let descriptor = grammar_macro_descriptor(
            facade,
            &factory,
            &name,
            &format!("enum-precedence:{enum_name}"),
            &grammar,
            &provenance,
            None,
        );
        output.push(quote!(#(#cfg)* #descriptor));
    }
    if let Some(anchors) = declaration.associativity_provenance()? {
        let provenance = host_provenance(env, facade, fallback, &anchors);
        let factory = format_ident!("__krs_enum_associativity_{nonce:016x}");
        let name = format!("__krs_grammar_{enum_name}_associativity");
        let mut sentences = Vec::new();
        for (sentence_ordinal, (group_ordinal, group)) in declaration
            .precedence_groups()
            .enumerate()
            .filter(|(_, group)| group.associativity().is_some())
            .enumerate()
        {
            let group_name = enum_precedence_group_name(declaration, group_ordinal);
            let associativity = match group
                .associativity()
                .expect("filtered enum groups have explicit associativity")
            {
                SyntaxGroupAssociativity::Left => GroupAssociativity::Left,
                SyntaxGroupAssociativity::Right => GroupAssociativity::Right,
                SyntaxGroupAssociativity::NonAssociative => GroupAssociativity::NonAssociative,
            };
            let ordinal = u32::try_from(sentence_ordinal).map_err(|_| {
                ExpandError::new(
                    expand::DESCRIPTOR_CAPACITY,
                    group.range().first(),
                    "too many groups",
                )
            })?;
            // The tier's sentence, then its reference.
            let keys = group.associativity_keys();
            sentences.push(DescriptorAssociativitySentence {
                key: read_key(keys.first(), wire_key(associativity_sentence_role, ordinal)),
                associativity,
                groups: vec![DescriptorGroupReference {
                    key: read_key(
                        keys.get(1),
                        wire_key(associativity_group_reference_role, ordinal),
                    ),
                    group: ProductionGroupId::new(group_name)
                        .expect("generated enum groups are valid identities"),
                }],
            });
        }
        let grammar = WireGrammarDescriptor::Associativity {
            key: read_key(
                declaration.associativity_declaration_key(),
                wire_key(associativity_declaration_role, 0),
            ),
            sentences,
        };
        let descriptor = grammar_macro_descriptor(
            facade,
            &factory,
            &name,
            &format!("enum-associativity:{enum_name}"),
            &grammar,
            &provenance,
            None,
        );
        output.push(quote!(#(#cfg)* #descriptor));
    }
    Ok(quote!(#(#output)*))
}

#[expect(
    clippy::too_many_arguments,
    clippy::too_many_lines,
    reason = "Variant lowering keeps the complete family context and metadata together."
)]
fn expand_enum_variant(
    env: &dyn MacroEnvironment,
    facade: &Path,
    declaration: &krs_syntax::EnumConstructorDeclaration,
    variant: &krs_syntax::EnumConstructorVariant,
    enum_key: &Ident,
    result_key: &Ident,
    variant_key: &Ident,
    nonce: u64,
    index: usize,
    cfg: &[Attribute],
) -> crate::Result<TokenStream> {
    let constructor_syntax_role = ProvenanceRole::ConstructorSyntax;
    let constructor_declaration_role = ProvenanceRole::ConstructorDeclaration;
    let enum_name = declaration.enum_name().to_string();
    let variant_name = variant.name().to_string();
    let descriptor_factory = format_ident!("__krs_enum_constructor_{nonce:016x}_{index}");
    let grammar_factory = format_ident!("__krs_enum_grammar_{nonce:016x}_{index}");
    let disambiguator = format!("{ENUM_VARIANT_DISAMBIGUATOR_PREFIX}{enum_name}");
    let grammar_name = format!("__krs_grammar_{enum_name}_{variant_name}");
    let anchors = declaration.variant_provenance(variant)?;
    if variant.syntax().is_some_and(|syntax| !syntax.avoid())
        && anchors
            .iter()
            .any(|anchor| anchor.role() == ProvenanceRole::ConstructorAvoid)
    {
        return Err(ExpandError::new(
            expand::INVALID_AVOID_METADATA,
            variant.name().span(),
            "`avoid = false` is not metadata; omit the argument instead",
        ));
    }
    let fallback = TokenRange::for_tokens(variant.variant())?;
    // Element types reach only the constructor descriptor, not the grammar.
    let constructor_anchors = variant.constructor_provenance()?;
    let provenance = host_provenance(env, facade, fallback, &constructor_anchors);
    let grammar_provenance = host_provenance(env, facade, fallback, &anchors);

    let mut slots = WireSlots::new(facade);
    let result_slot = slots.type_slot(quote!(#facade::HostTypeKey(#result_key)));
    let mut field_key_functions = Vec::new();
    let mut fields = Vec::new();
    for (field_index, field) in variant.fields().iter().enumerate() {
        let key = format_ident!("__krs_enum_field_{nonce:016x}_{index}_{field_index}");
        let ty = if declaration.is_reference_family() && field.term_sort().is_dynamic() {
            field.term_sort().ty().to_token_stream()
        } else {
            let path = call_site_path(field.term_sort().sort())?;
            sort_type_tokens(facade, &path, field.term_sort().is_dynamic())
        };
        let spelling = field.term_sort().sort_token_text();
        let field_name = field.name().to_string();
        field_key_functions.push(quote! {
            #(#cfg)*
            #[doc(hidden)]
            fn #key() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<#ty>()
            }
        });
        fields.push(WireConstructorFieldDescriptor {
            name: field_name,
            sort: WireTypeReference {
                slot: slots.type_slot(quote!(#facade::HostTypeKey(#key))),
                authored_path: spelling,
            },
            arguments: Vec::new(),
        });
    }
    // Each field's element types, numbered in preorder across the fields.
    let mut sink = super::terms::SortArgumentSink {
        facade,
        prefix: format!("__krs_enum_field_argument_{nonce:016x}_{index}"),
        cfg,
        helpers: &mut field_key_functions,
        slots: &mut slots,
        ordinal: 0,
    };
    for (wire, field) in fields.iter_mut().zip(variant.fields()) {
        wire.arguments = super::terms::production_sort_arguments(
            field.term_sort().arguments(),
            ProvenanceRole::ConstructorFieldSortArgument,
            &mut sink,
        )?;
    }

    let grammar_nonce = expansion_nonce(env, "enum_strictness", variant.name(), fallback);
    let strictness_key = strictness_key_function(
        variant.strictness(),
        variant
            .fields()
            .iter()
            .map(krs_syntax::ConstructorField::name),
        grammar_nonce,
        cfg,
    )?;
    let mut grammar_slots = WireSlots::new(facade);
    let items =
        enum_variant_production_wire_items(facade, variant, nonce, index, &mut grammar_slots)?;
    let group = variant
        .precedence_group()
        .map(|ordinal| enum_precedence_group_name(declaration, ordinal));
    let overload = variant
        .syntax()
        .and_then(krs_syntax::VariantSyntaxAttribute::overload)
        .map(|target| {
            super::productions::overload_wire(
                facade,
                target,
                variant.syntax().and_then(|syntax| syntax.keys().overload()),
                &format_ident!("__krs_overload_target_{nonce:016x}_{index}"),
                cfg,
                &mut grammar_slots,
            )
        });
    let overload_tokens = overload
        .as_ref()
        .map(|overload| overload.tokens.clone())
        .unwrap_or_default();
    let mut attributes = if let Some(syntax) = variant.syntax() {
        // A tier's membership names its group; else the syntax's `group`.
        let group_key = if group.is_some() {
            variant.group_key()
        } else {
            syntax.keys().group()
        };
        super::productions::constructor_metadata_wire(
            syntax.keys(),
            (
                group.or_else(|| syntax.group().map(syn::LitStr::value)),
                group_key,
            ),
            syntax.avoid(),
            syntax.prefer(),
            syntax.placement(),
            overload.map(|overload| overload.attribute),
            &super::productions::ColorMetadata {
                color: syntax.color(),
                colors: syntax.colors(),
            },
            syntax.structured_format(),
        )?
    } else {
        Vec::new()
    };
    attributes.splice(
        0..0,
        super::productions::production_documentation_wire(variant.documentation())?,
    );
    if let Some(marker) = variant.static_attribute() {
        attributes.insert(
            0,
            super::productions::static_mode_wire(marker, variant.static_key()),
        );
    }
    if let Some(strictness) = super::productions::strictness_wire(
        facade,
        variant.strictness(),
        grammar_nonce,
        &mut grammar_slots,
    ) {
        attributes.push(strictness);
    }
    // The cons of a `#[k::cons_list]` enum names its empty sibling (F6).
    if let Some((cons, empty)) = declaration.cons_list()
        && cons == index
    {
        let empty_key = format_ident!("__krs_enum_variant_{nonce:016x}_{empty}");
        // The marker, which also names the empty sibling.
        attributes.push(WireProductionAttribute::ConsList {
            key: read_key(
                variant.cons_list_key(),
                wire_key(ProvenanceRole::ConsListDeclaration, 0),
            ),
            empty: WireApplicationReference {
                key: read_key(
                    variant.cons_list_key(),
                    wire_key(ProvenanceRole::ConsListDeclaration, 0),
                ),
                target: grammar_slots.variant_slot_for_grammar(
                    &quote!(#facade::HostTypeKey(#enum_key)),
                    &quote!(#facade::HostTypeKey(#empty_key)),
                ),
                authored_path: format!("{enum_name}::{}", declaration.variants()[empty].name()),
            },
        });
    }
    let template_key = variant
        .syntax()
        .map(|syntax| read_key(syntax.keys().syntax(), wire_key(constructor_syntax_role, 0)));
    let application_path = format!("{enum_name}::{variant_name}");
    let result_spelling = spelling(variant.constructor_sort());
    let result_sort = wire_sort_reference(
        &mut grammar_slots,
        facade,
        (variant.sort_key(), ProvenanceRole::ConstructorSort, 0),
        result_key,
        &result_spelling,
    );
    let variant_slot = grammar_slots.variant_slot_for_grammar(
        &quote!(#facade::HostTypeKey(#enum_key)),
        &quote!(#facade::HostTypeKey(#variant_key)),
    );
    let grammar_wire = WirePayload::Grammar(Box::new(WireGrammarDescriptor::Production(
        WireProduction {
            parameters: Vec::new(),
            key: read_key(
                variant.key(),
                wire_key(ProvenanceRole::ConstructorDeclaration, 0),
            ),
            template_key,
            // The production's owner is its own variant.
            owner: WireProductionOwner::Constructor {
                constructor: WireApplicationReference {
                    key: read_key(variant.key(), wire_key(constructor_declaration_role, 0)),
                    target: variant_slot,
                    authored_path: application_path,
                },
            },
            result_sort,
            items,
            attributes,
        },
    )));
    let grammar_wire = serde_json::to_string(&grammar_wire).expect("KRS wire values serialize");
    let grammar_slot_tokens = grammar_slots.tokens();
    let constructor_wire = WirePayload::Constructor(WireConstructorDescriptor {
        parameters: Vec::new(),
        sort: WireSortReference {
            key: read_key(
                variant.sort_key(),
                wire_key(ProvenanceRole::ConstructorSort, 0),
            ),
            target: WireTypeReference {
                slot: result_slot,
                authored_path: result_spelling,
            },
        },
        fields,
        arguments: Vec::new(),
    });
    let constructor_wire =
        serde_json::to_string(&constructor_wire).expect("enum-constructor wire is serializable");
    let slot_tokens = slots.tokens();

    let descriptor_factory_tokens = DescriptorFactory {
        facade,
        factory: &descriptor_factory,
        name: quote!(#variant_name),
        item_kind: quote!(#facade::ItemKind::Constructor),
        disambiguator: quote!(#disambiguator),
        identity_label: "Cargo and Rust macro context form a valid enum-variant identity",
        declared_type: quote! {
            ::core::option::Option::Some(
                #facade::HostDeclarationIdentity::EnumVariant(
                    #facade::HostEnumVariantKey::new(
                        #facade::HostTypeKey(#enum_key),
                        #facade::HostTypeKey(#variant_key),
                    ),
                ),
            )
        },
        payload: FactoryPayload::wire(constructor_wire, slot_tokens),
        cfg: quote!(::core::default::Default::default()),
        attributes: quote!(#(#cfg)*),
        provenance: quote!(#provenance),
        prelude: TokenStream::new(),
    }
    .render();
    let grammar_factory_tokens = DescriptorFactory {
        facade,
        factory: &grammar_factory,
        name: quote!(#grammar_name),
        item_kind: quote!(#facade::ItemKind::Grammar),
        disambiguator: quote!(#disambiguator),
        identity_label: "Cargo and Rust macro context form a valid variant-grammar identity",
        declared_type: quote!(::core::option::Option::None),
        payload: FactoryPayload::wire(grammar_wire, grammar_slot_tokens),
        cfg: quote!(::core::default::Default::default()),
        attributes: quote!(#(#cfg)*),
        provenance: quote!(#grammar_provenance),
        prelude: TokenStream::new(),
    }
    .render();

    Ok(quote! {
        #(#field_key_functions)*
        #strictness_key
        #overload_tokens

        #descriptor_factory_tokens

        #grammar_factory_tokens
    })
}

#[expect(
    clippy::too_many_lines,
    reason = "Template fields and production slots are lowered in one ordered pass."
)]
fn enum_variant_production_wire_items(
    facade: &Path,
    variant: &krs_syntax::EnumConstructorVariant,
    nonce: u64,
    variant_index: usize,
    slots: &mut WireSlots,
) -> crate::Result<Vec<krs_ir::wire::WireProductionItem>> {
    use krs_ir::wire::WireProductionItem as Item;
    let mut items = Vec::new();
    if let Some(syntax) = variant.syntax() {
        let mut field_ordinal = 0_u32;
        for (item_index, item) in syntax.syntax_template().items().iter().enumerate() {
            let ordinal = u32::try_from(item_index).map_err(|_| {
                ExpandError::new(
                    expand::DESCRIPTOR_CAPACITY,
                    variant.name().span(),
                    "too many production items",
                )
            })?;
            let item_keys = syntax.syntax_template().item_keys(item_index);
            let key = read_key(
                item_keys.first(),
                wire_key(ProvenanceRole::ConstructorSyntaxItem, ordinal),
            );
            match item {
                SyntaxTemplateItem::Terminal(text) => items.push(Item::Terminal {
                    key,
                    text: text.to_owned(),
                }),
                SyntaxTemplateItem::Field(name) => {
                    let declaration_index = variant
                        .fields()
                        .iter()
                        .position(|field| field.name() == name)
                        .ok_or_else(|| {
                            ExpandError::new(
                                expand::MISSING_CHECKED_FIELD,
                                variant.name().span(),
                                "checked field disappeared",
                            )
                        })?;
                    let declaration_ordinal = u32::try_from(declaration_index).map_err(|_| {
                        ExpandError::new(
                            expand::DESCRIPTOR_CAPACITY,
                            variant.name().span(),
                            "too many fields",
                        )
                    })?;
                    let sort_key = format_ident!(
                        "__krs_enum_field_{nonce:016x}_{variant_index}_{declaration_index}"
                    );
                    let field = &variant.fields()[declaration_index];
                    items.push(Item::NonTerminal {
                        key,
                        field_key: read_key(
                            item_keys.get(1),
                            wire_key(
                                ProvenanceRole::ConstructorSyntaxFieldReference,
                                field_ordinal,
                            ),
                        ),
                        // The field's declaration, which the template names.
                        declaration_key: Some(read_key(
                            field.name_key(),
                            wire_key(
                                ProvenanceRole::ConstructorFieldDeclaration,
                                declaration_ordinal,
                            ),
                        )),
                        field: krs_ir::ProductionFieldId::new(name.clone())
                            .expect("Rust fields are valid production fields"),
                        sort: Box::new(wire_sort_reference(
                            slots,
                            facade,
                            (
                                field.sort_key(),
                                ProvenanceRole::ConstructorFieldSort,
                                declaration_ordinal,
                            ),
                            &sort_key,
                            &field.term_sort().sort_token_text(),
                        )),
                    });
                    field_ordinal = field_ordinal.checked_add(1).ok_or_else(|| {
                        ExpandError::new(
                            expand::DESCRIPTOR_CAPACITY,
                            variant.name().span(),
                            "too many fields",
                        )
                    })?;
                }
            }
        }
    } else {
        // Without a template the production reads as the variant's name,
        // which declares it.
        items.push(Item::Terminal {
            key: read_key(
                variant.key(),
                wire_key(ProvenanceRole::ConstructorDeclaration, 0),
            ),
            text: variant.name().to_string(),
        });
        for (field_index, field) in variant.fields().iter().enumerate() {
            let ordinal = u32::try_from(field_index).map_err(|_| {
                ExpandError::new(
                    expand::DESCRIPTOR_CAPACITY,
                    variant.name().span(),
                    "too many fields",
                )
            })?;
            // The field's name keys its item, its field and its declaration.
            let key = read_key(
                field.name_key(),
                wire_key(ProvenanceRole::ConstructorFieldDeclaration, ordinal),
            );
            let sort_key =
                format_ident!("__krs_enum_field_{nonce:016x}_{variant_index}_{field_index}");
            items.push(Item::NonTerminal {
                key: key.clone(),
                field_key: key.clone(),
                declaration_key: Some(key),
                field: krs_ir::ProductionFieldId::new(field.name().to_string())
                    .expect("Rust fields are valid production fields"),
                sort: Box::new(wire_sort_reference(
                    slots,
                    facade,
                    (
                        field.sort_key(),
                        ProvenanceRole::ConstructorFieldSort,
                        ordinal,
                    ),
                    &sort_key,
                    &field.term_sort().sort_token_text(),
                )),
            });
        }
    }
    Ok(items)
}
