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
use super::terms::{WireSlots, wire_key, wire_sort_reference};
use super::tokens::{
    call_site_cfg_attributes, call_site_ident, call_site_path, sort_type_tokens, spelling,
    variant_marker_function,
};
use crate::environment::MacroEnvironment;
use crate::provenance::host_provenance;

#[expect(
    clippy::too_many_lines,
    reason = "The enum family and its variants share one descriptor expansion."
)]
pub(crate) fn constructors(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> crate::Result<TokenStream> {
    let subsort_declaration_role = ProvenanceRole::SubsortDeclaration;
    let attribute = krs_syntax::ConstructorsAttribute::parse_tokens(attributes)?;
    let item: ItemEnum = syn::parse2(item)?;
    let declaration = krs_syntax::EnumConstructorDeclaration::from_parts(&attribute, item)?;
    let facade = env.facade_path()?;
    let fallback = TokenRange::for_tokens(declaration.item())?;
    let nonce = expansion_nonce(env, "constructors", declaration.sort_name(), fallback);
    let cfg = call_site_cfg_attributes(&declaration.item().attrs)?;
    let enum_ident = call_site_ident(declaration.sort_name())?;
    let enum_name = declaration.sort_name().to_string();
    let enum_key = format_ident!("__krs_enum_type_{nonce:016x}");
    let sort_factory = format_ident!("__krs_enum_sort_descriptor_{nonce:016x}");
    let membership_factory = format_ident!("__krs_enum_membership_descriptor_{nonce:016x}");
    let membership_key = format_ident!("__krs_enum_membership_super_{nonce:016x}");
    // Keep the enum family's authored membership sort attached to the
    // `constructors(sort = ...)` token. This witness is the semantic bridge
    // rust-analyzer needs for definition and rename through the consumed
    // procedural-attribute argument.
    let outer_path = declaration.membership_sort();
    let outer_spelling = spelling(declaration.membership_sort());
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
            if declaration.is_open_family() {
                &family_sort_key
            } else {
                &enum_key
            },
            &variant_key,
            nonce,
            index,
            &cfg,
        )?);
    }

    let membership_name = format!("__krs_grammar_membership_{enum_name}");
    let mut membership_slots = WireSlots::new(&facade);
    let membership_subsort = wire_sort_reference(
        &mut membership_slots,
        &facade,
        ProvenanceRole::SubsortSubSort,
        0,
        &enum_key,
        &enum_name,
    );
    let membership_supersort = wire_sort_reference(
        &mut membership_slots,
        &facade,
        ProvenanceRole::SubsortSuperSort,
        0,
        &membership_key,
        &outer_spelling,
    );
    let membership_wire = WirePayload::Grammar(Box::new(WireGrammarDescriptor::Subsort {
        key: wire_key(subsort_declaration_role, 0),
        subsort: membership_subsort,
        supersort: membership_supersort,
    }));
    let membership_wire =
        serde_json::to_string(&membership_wire).expect("KRS wire values serialize");
    let membership_slot_tokens = membership_slots.tokens();

    let closed_sort = if declaration.is_open_family() {
        TokenStream::new()
    } else {
        let sort_anchors = declaration.sort_provenance()?;
        let sort_provenance = host_provenance(env, &facade, fallback, &sort_anchors);
        let membership_anchors = declaration.membership_provenance()?;
        let membership_provenance = host_provenance(env, &facade, fallback, &membership_anchors);
        let sort_wire =
            serde_json::to_string(&WirePayload::Sort(krs_ir::wire::WireSortDescriptor {
                parents: Vec::new(),
            }))
            .expect("KRS wire values serialize");
        let sort_factory_tokens = DescriptorFactory {
            facade: &facade,
            factory: &sort_factory,
            name: quote!(#enum_name),
            item_kind: quote!(#facade::ItemKind::Sort),
            disambiguator: quote!(""),
            identity_label: "Cargo and Rust macro context form a valid enum-sort identity",
            declared_type: quote! {
                ::core::option::Option::Some(
                    #facade::HostDeclarationIdentity::Nominal(#facade::HostTypeKey(#enum_key)),
                )
            },
            payload: FactoryPayload::wire(sort_wire, quote!(#facade::__KrsSlots::default())),
            cfg: quote!(::core::default::Default::default()),
            attributes: quote!(#(#cfg)*),
            provenance: quote!(#sort_provenance),
            prelude: TokenStream::new(),
        }
        .render();
        let membership_factory_tokens = DescriptorFactory {
            facade: &facade,
            factory: &membership_factory,
            name: quote!(#membership_name),
            item_kind: quote!(#facade::ItemKind::Grammar),
            disambiguator: quote!("enum-membership"),
            identity_label: "Cargo and Rust macro context form a valid enum-membership identity",
            declared_type: quote!(::core::option::Option::None),
            payload: FactoryPayload::wire(membership_wire, membership_slot_tokens),
            cfg: quote!(::core::default::Default::default()),
            attributes: quote!(#(#cfg)*),
            provenance: quote!(#membership_provenance),
            prelude: TokenStream::new(),
        }
        .render();

        quote! {
            #(#cfg)*
            #[doc(hidden)]
            fn #membership_key() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<dyn #outer_path>()
            }

            #sort_factory_tokens

            #membership_factory_tokens
        }
    };
    let open_sort_key = declaration.is_open_family().then(|| {
        quote! {
            #(#cfg)*
            #[doc(hidden)]
            fn #family_sort_key() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<#outer_path>()
            }
        }
    });
    let family_grammar = expand_enum_family_grammar(
        env,
        &facade,
        &declaration,
        nonce,
        &enum_name,
        &cfg,
        fallback,
    )?;

    Ok(quote! {
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

        #closed_sort

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
        .emitted_name(declaration.sort_name(), ordinal)
}

#[expect(
    clippy::too_many_lines,
    reason = "Family productions and their provenance are emitted together."
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
    if !declaration.is_open_family() {
        return Ok(TokenStream::new());
    }
    let mut output = Vec::new();
    if let Some(precedence) = declaration.precedence_descriptor()? {
        let provenance = host_provenance(env, facade, fallback, &precedence.provenance);
        let factory = format_ident!("__krs_enum_precedence_{nonce:016x}");
        let name = format!("__krs_grammar_{enum_name}_precedence");
        let mut group_ordinal = 0_usize;
        let groups = precedence.groups.try_map_ref(|group| -> crate::Result<_> {
            let ordinal = group_ordinal;
            group_ordinal += 1;
            let name = group.emitted_name(declaration.sort_name(), ordinal);
            let ordinal = u32::try_from(ordinal).map_err(|_| {
                ExpandError::new(
                    expand::DESCRIPTOR_CAPACITY,
                    declaration.sort_name().span(),
                    "too many groups",
                )
            })?;
            Ok(DescriptorGroupReference {
                key: wire_key(precedence_group_reference_role, ordinal),
                group: ProductionGroupId::new(name)
                    .expect("generated enum groups are valid identities"),
            })
        })?;
        let grammar = WireGrammarDescriptor::Precedence {
            key: wire_key(precedence_declaration_role, 0),
            chains: vec![DescriptorPrecedenceChain {
                key: wire_key(precedence_chain_role, 0),
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
            sentences.push(DescriptorAssociativitySentence {
                key: wire_key(associativity_sentence_role, ordinal),
                associativity,
                groups: vec![DescriptorGroupReference {
                    key: wire_key(associativity_group_reference_role, ordinal),
                    group: ProductionGroupId::new(group_name)
                        .expect("generated enum groups are valid identities"),
                }],
            });
        }
        let grammar = WireGrammarDescriptor::Associativity {
            key: wire_key(associativity_declaration_role, 0),
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
    let alias_production_role = ProvenanceRole::AliasProduction;
    let constructor_syntax_role = ProvenanceRole::ConstructorSyntax;
    let constructor_declaration_role = ProvenanceRole::ConstructorDeclaration;
    let enum_name = declaration.sort_name().to_string();
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
    let provenance = host_provenance(env, facade, fallback, &anchors);
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
            sort_type_tokens(&path, field.term_sort().is_dynamic())
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
        });
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
    let mut attributes = if let Some(syntax) = variant.syntax() {
        super::productions::constructor_metadata_wire(
            group.or_else(|| syntax.group().map(syn::LitStr::value)),
            syntax.avoid(),
            syntax.structured_format(),
        )?
    } else {
        Vec::new()
    };
    attributes.splice(
        0..0,
        super::productions::production_documentation_wire(variant.documentation())?,
    );
    if variant.is_alias() {
        attributes.insert(
            0,
            WireProductionAttribute::Alias {
                key: wire_key(alias_production_role, 0),
            },
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
    let template_key = variant
        .syntax()
        .map(|_| wire_key(constructor_syntax_role, 0));
    let application_path = format!("{enum_name}::{variant_name}");
    let result_spelling = spelling(variant.constructor_sort());
    let result_sort = wire_sort_reference(
        &mut grammar_slots,
        facade,
        ProvenanceRole::ConstructorSort,
        0,
        result_key,
        &result_spelling,
    );
    let variant_slot = grammar_slots.variant_slot_for_grammar(
        &quote!(#facade::HostTypeKey(#enum_key)),
        &quote!(#facade::HostTypeKey(#variant_key)),
    );
    let grammar_wire = WirePayload::Grammar(Box::new(WireGrammarDescriptor::Production(
        WireProduction {
            key: wire_key(ProvenanceRole::ConstructorDeclaration, 0),
            template_key,
            owner: WireProductionOwner::Constructor {
                constructor: WireApplicationReference {
                    key: wire_key(constructor_declaration_role, 0),
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
        sort: WireSortReference {
            key: wire_key(ProvenanceRole::ConstructorSort, 0),
            target: WireTypeReference {
                slot: result_slot,
                authored_path: result_spelling,
            },
        },
        fields,
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
            let key = wire_key(ProvenanceRole::ConstructorSyntaxItem, ordinal);
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
                        field_key: wire_key(
                            ProvenanceRole::ConstructorSyntaxFieldReference,
                            field_ordinal,
                        ),
                        declaration_key: Some(wire_key(
                            ProvenanceRole::ConstructorFieldDeclaration,
                            declaration_ordinal,
                        )),
                        field: krs_ir::ProductionFieldId::new(name.clone())
                            .expect("Rust fields are valid production fields"),
                        sort: Box::new(wire_sort_reference(
                            slots,
                            facade,
                            ProvenanceRole::ConstructorFieldSort,
                            declaration_ordinal,
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
        items.push(Item::Terminal {
            key: wire_key(ProvenanceRole::ConstructorDeclaration, 0),
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
            let key = wire_key(ProvenanceRole::ConstructorFieldDeclaration, ordinal);
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
                    ProvenanceRole::ConstructorFieldSort,
                    ordinal,
                    &sort_key,
                    &field.term_sort().sort_token_text(),
                )),
            });
        }
    }
    Ok(items)
}
