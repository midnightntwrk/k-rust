//! Enum production families: `#[k::constructors]`.

use std::collections::BTreeMap;

use krs_syntax::{
    GroupAssociativity as SyntaxGroupAssociativity, ProvenanceRole, SyntaxTemplateItem, TokenRange,
    parse_constructors_attribute,
};
use proc_macro2::TokenStream;
use quote::{ToTokens, format_ident, quote};
use syn::{Attribute, Ident, ItemEnum, Path};

use super::grammar::grammar_macro_descriptor;
use super::nonce::{expansion_nonce, rule_application_selector};
use super::productions::{
    constructor_metadata_tokens, production_documentation_tokens, strictness_tokens,
};
use super::tokens::{
    call_site_cfg_attributes, call_site_ident, call_site_path, host_sort_reference,
    option_owned_string, provenance_key, sort_type_tokens, spelling, type_reference,
    variant_marker_function,
};
use crate::environment::MacroEnvironment;
use crate::provenance::host_provenance;

#[allow(clippy::too_many_lines)]
pub(crate) fn constructors(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> syn::Result<TokenStream> {
    let subsort_declaration_role = ProvenanceRole::SubsortDeclaration;
    let attribute = parse_constructors_attribute(attributes)
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let item: ItemEnum = syn::parse2(item)?;
    let declaration = krs_syntax::EnumConstructorDeclaration::from_parts(&attribute, item)
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let facade = env.facade_path()?;
    let fallback = TokenRange::for_tokens(declaration.item())
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
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
            return Err(syn::Error::new(
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
    let membership_subsort = host_sort_reference(
        &facade,
        ProvenanceRole::SubsortSubSort,
        0,
        &enum_key,
        &enum_name,
    );
    let membership_supersort = host_sort_reference(
        &facade,
        ProvenanceRole::SubsortSuperSort,
        0,
        &membership_key,
        &outer_spelling,
    );

    let closed_sort = if declaration.is_open_family() {
        TokenStream::new()
    } else {
        let sort_anchors = declaration
            .sort_provenance()
            .map_err(krs_syntax::SyntaxError::into_syn_error)?;
        let sort_provenance = host_provenance(env, &facade, fallback, &sort_anchors)?;
        let membership_anchors = declaration
            .membership_provenance()
            .map_err(krs_syntax::SyntaxError::into_syn_error)?;
        let membership_provenance = host_provenance(env, &facade, fallback, &membership_anchors)?;
        quote! {
            #(#cfg)*
            #[doc(hidden)]
            fn #membership_key() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<dyn #outer_path>()
            }

            #(#cfg)*
            #[doc(hidden)]
            fn #sort_factory() -> #facade::HostDescriptor {
                #facade::HostDescriptor {
                    protocol_version: #facade::SchemaVersion::CURRENT,
                    id: #facade::HostItemId::from_macro_context(
                        env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"),
                        env!("CARGO_MANIFEST_DIR"), module_path!(), #enum_name,
                        #facade::ItemKind::Sort, "",
                    ).expect("Cargo and Rust macro context form a valid enum-sort identity"),
                    declared_type: ::core::option::Option::Some(
                        #facade::HostDeclarationIdentity::Nominal(#facade::HostTypeKey(#enum_key)),
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
            fn #membership_factory() -> #facade::HostDescriptor {
                #facade::HostDescriptor {
                    protocol_version: #facade::SchemaVersion::CURRENT,
                    id: #facade::HostItemId::from_macro_context(
                        env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"),
                        env!("CARGO_MANIFEST_DIR"), module_path!(), #membership_name,
                        #facade::ItemKind::Grammar, "enum-membership",
                    ).expect("Cargo and Rust macro context form a valid enum-membership identity"),
                    declared_type: ::core::option::Option::None,
                    payload: #facade::HostDescriptorPayload::Grammar(::std::boxed::Box::new(
                        #facade::HostGrammarDescriptor::Subsort {
                            key: #facade::ProvenanceKey::new(#subsort_declaration_role, 0)
                                .expect("KRS parser roles are nonempty"),
                            subsort: #membership_subsort,
                            supersort: #membership_supersort,
                        },
                    )),
                    cfg: ::core::default::Default::default(),
                    provenance: #membership_provenance,
                }
            }

            #(#cfg)*
            #facade::__register_host_descriptor!(#membership_factory);
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
    declaration.precedence_groups()[ordinal].emitted_name(declaration.sort_name(), ordinal)
}

#[allow(clippy::too_many_lines)]
fn expand_enum_family_grammar(
    env: &dyn MacroEnvironment,
    facade: &Path,
    declaration: &krs_syntax::EnumConstructorDeclaration,
    nonce: u64,
    enum_name: &str,
    cfg: &[Attribute],
    fallback: TokenRange,
) -> syn::Result<TokenStream> {
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
    if let Some(anchors) = declaration
        .precedence_provenance()
        .map_err(krs_syntax::SyntaxError::into_syn_error)?
    {
        let provenance = host_provenance(env, facade, fallback, &anchors)?;
        let factory = format_ident!("__krs_enum_precedence_{nonce:016x}");
        let name = format!("__krs_grammar_{enum_name}_precedence");
        let mut groups = Vec::new();
        for (ordinal, _) in declaration.precedence_groups().iter().enumerate() {
            let group = enum_precedence_group_name(declaration, ordinal);
            let ordinal = u32::try_from(ordinal)
                .map_err(|_| syn::Error::new(declaration.sort_name().span(), "too many groups"))?;
            groups.push(quote! {
                #facade::DescriptorGroupReference {
                    key: #facade::ProvenanceKey::new(#precedence_group_reference_role, #ordinal)
                        .expect("KRS parser roles are nonempty"),
                    group: #facade::ProductionGroupId::new(#group)
                        .expect("generated enum groups are valid identities"),
                }
            });
        }
        let grammar = quote! {
            #facade::HostGrammarDescriptor::Precedence {
                key: #facade::ProvenanceKey::new(#precedence_declaration_role, 0)
                    .expect("KRS parser roles are nonempty"),
                chains: ::std::vec![#facade::DescriptorPrecedenceChain {
                    key: #facade::ProvenanceKey::new(#precedence_chain_role, 0)
                        .expect("KRS parser roles are nonempty"),
                    groups: ::std::vec![#(#groups),*],
                }],
            }
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
    if let Some(anchors) = declaration
        .associativity_provenance()
        .map_err(krs_syntax::SyntaxError::into_syn_error)?
    {
        let provenance = host_provenance(env, facade, fallback, &anchors)?;
        let factory = format_ident!("__krs_enum_associativity_{nonce:016x}");
        let name = format!("__krs_grammar_{enum_name}_associativity");
        let mut sentences = Vec::new();
        for (sentence_ordinal, (group_ordinal, group)) in declaration
            .precedence_groups()
            .iter()
            .enumerate()
            .filter(|(_, group)| group.associativity().is_some())
            .enumerate()
        {
            let group_name = enum_precedence_group_name(declaration, group_ordinal);
            let associativity = match group
                .associativity()
                .expect("filtered enum groups have explicit associativity")
            {
                SyntaxGroupAssociativity::Left => quote!(#facade::GroupAssociativity::Left),
                SyntaxGroupAssociativity::Right => quote!(#facade::GroupAssociativity::Right),
                SyntaxGroupAssociativity::NonAssociative => {
                    quote!(#facade::GroupAssociativity::NonAssociative)
                }
            };
            let ordinal = u32::try_from(sentence_ordinal)
                .map_err(|_| syn::Error::new(group.range().first(), "too many groups"))?;
            sentences.push(quote! {
                #facade::DescriptorAssociativitySentence {
                    key: #facade::ProvenanceKey::new(#associativity_sentence_role, #ordinal)
                        .expect("KRS parser roles are nonempty"),
                    associativity: #associativity,
                    groups: ::std::vec![#facade::DescriptorGroupReference {
                        key: #facade::ProvenanceKey::new(
                            #associativity_group_reference_role,
                            #ordinal,
                        ).expect("KRS parser roles are nonempty"),
                        group: #facade::ProductionGroupId::new(#group_name)
                            .expect("generated enum groups are valid identities"),
                    }],
                }
            });
        }
        let grammar = quote! {
            #facade::HostGrammarDescriptor::Associativity {
                key: #facade::ProvenanceKey::new(#associativity_declaration_role, 0)
                    .expect("KRS parser roles are nonempty"),
                sentences: ::std::vec![#(#sentences),*],
            }
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

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
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
) -> syn::Result<TokenStream> {
    let alias_production_role = ProvenanceRole::AliasProduction;
    let constructor_syntax_role = ProvenanceRole::ConstructorSyntax;
    let constructor_declaration_role = ProvenanceRole::ConstructorDeclaration;
    let enum_name = declaration.sort_name().to_string();
    let variant_name = variant.name().to_string();
    let descriptor_factory = format_ident!("__krs_enum_constructor_{nonce:016x}_{index}");
    let grammar_factory = format_ident!("__krs_enum_grammar_{nonce:016x}_{index}");
    let disambiguator = format!("enum:{enum_name}");
    let grammar_name = format!("__krs_grammar_{enum_name}_{variant_name}");
    let anchors = declaration
        .variant_provenance(variant)
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    if variant.syntax().is_some_and(|syntax| !syntax.avoid())
        && anchors
            .iter()
            .any(|anchor| anchor.role() == ProvenanceRole::ConstructorAvoid)
    {
        return Err(syn::Error::new(
            variant.name().span(),
            "`avoid = false` is not metadata; omit the argument instead",
        ));
    }
    let fallback = TokenRange::for_tokens(variant.variant())
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let provenance = host_provenance(env, facade, fallback, &anchors)?;
    let grammar_provenance = host_provenance(env, facade, fallback, &anchors)?;
    let syntax = option_owned_string(variant.syntax().map(|syntax| syntax.syntax().value()));

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
        let spelling = field.term_sort().sort_spelling();
        let field_name = field.name().to_string();
        field_key_functions.push(quote! {
            #(#cfg)*
            #[doc(hidden)]
            fn #key() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<#ty>()
            }
        });
        let reference = type_reference(facade, &key, &spelling);
        fields.push(quote! {
            #facade::HostConstructorFieldDescriptor {
                name: #field_name.to_owned(),
                sort: #reference,
            }
        });
    }

    let items = enum_variant_production_items(facade, variant, nonce, index)?;
    let group = variant
        .precedence_group()
        .map(|ordinal| enum_precedence_group_name(declaration, ordinal));
    let mut attributes = if let Some(syntax) = variant.syntax() {
        constructor_metadata_tokens(
            facade,
            group.or_else(|| syntax.group().map(syn::LitStr::value)),
            syntax.avoid(),
            syntax.structured_format(),
        )?
    } else {
        Vec::new()
    };
    attributes.splice(
        0..0,
        production_documentation_tokens(facade, variant.documentation())?,
    );
    if variant.is_alias() {
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
    let (strictness_key, strictness) = strictness_tokens(
        facade,
        variant.strictness(),
        variant
            .fields()
            .iter()
            .map(krs_syntax::ConstructorField::name),
        expansion_nonce(env, "enum_strictness", variant.name(), fallback),
        cfg,
    )?;
    if let Some(strictness) = strictness {
        attributes.push(strictness);
    }
    let template_key = if variant.syntax().is_some() {
        quote!(::core::option::Option::Some(
            #facade::ProvenanceKey::new(#constructor_syntax_role, 0)
                .expect("KRS parser roles are nonempty")
        ))
    } else {
        quote!(::core::option::Option::None)
    };
    let owner_path = enum_name.clone();
    let application_path = format!("{enum_name}::{variant_name}");
    let result_spelling = spelling(variant.constructor_sort());
    let result_sort = host_sort_reference(
        facade,
        ProvenanceRole::ConstructorSort,
        0,
        result_key,
        &result_spelling,
    );
    let primary = provenance_key(facade, ProvenanceRole::ConstructorDeclaration, 0);

    Ok(quote! {
        #(#field_key_functions)*
        #strictness_key

        #(#cfg)*
        #[doc(hidden)]
        fn #descriptor_factory() -> #facade::HostDescriptor {
            #facade::HostDescriptor {
                protocol_version: #facade::SchemaVersion::CURRENT,
                id: #facade::HostItemId::from_macro_context(
                    env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"),
                    env!("CARGO_MANIFEST_DIR"), module_path!(), #variant_name,
                    #facade::ItemKind::Constructor, #disambiguator,
                ).expect("Cargo and Rust macro context form a valid enum-variant identity"),
                declared_type: ::core::option::Option::Some(
                    #facade::HostDeclarationIdentity::EnumVariant(
                        #facade::HostEnumVariantKey::new(
                            #facade::HostTypeKey(#enum_key),
                            #facade::HostTypeKey(#variant_key),
                        ),
                    ),
                ),
                payload: #facade::HostDescriptorPayload::Constructor(
                    #facade::HostConstructorDescriptor {
                        sort: #result_sort,
                        syntax: #syntax,
                        fields: ::std::vec![#(#fields),*],
                    },
                ),
                cfg: ::core::default::Default::default(),
                provenance: #provenance,
            }
        }

        #(#cfg)*
        #facade::__register_host_descriptor!(#descriptor_factory);

        #(#cfg)*
        #[doc(hidden)]
        fn #grammar_factory() -> #facade::HostDescriptor {
            #facade::HostDescriptor {
                protocol_version: #facade::SchemaVersion::CURRENT,
                id: #facade::HostItemId::from_macro_context(
                    env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"),
                    env!("CARGO_MANIFEST_DIR"), module_path!(), #grammar_name,
                    #facade::ItemKind::Grammar, #disambiguator,
                ).expect("Cargo and Rust macro context form a valid variant-grammar identity"),
                declared_type: ::core::option::Option::None,
                payload: #facade::HostDescriptorPayload::Grammar(::std::boxed::Box::new(
                    #facade::HostGrammarDescriptor::Production(#facade::HostProduction {
                        key: #primary,
                        template_key: #template_key,
                        owner: #facade::HostProductionOwner::Constructor {
                            constructor: #facade::HostApplicationReference {
                                key: #facade::ProvenanceKey::new(#constructor_declaration_role, 0)
                                    .expect("KRS parser roles are nonempty"),
                                target: #facade::HostApplicationTarget::EnumVariant(
                                    #facade::HostEnumVariantReference::new(
                                        #facade::HostTypeReference {
                                            key: #facade::HostTypeKey(#enum_key),
                                            authored_path: #owner_path.to_owned(),
                                        },
                                        #facade::HostTypeKey(#variant_key),
                                        #application_path,
                                    ).expect("generated variant paths retain their enum owner"),
                                ),
                            },
                        },
                        result_sort: #result_sort,
                        items: ::std::vec![#(#items),*],
                        attributes: ::std::vec![#(#attributes),*],
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

fn enum_variant_production_items(
    facade: &Path,
    variant: &krs_syntax::EnumConstructorVariant,
    nonce: u64,
    variant_index: usize,
) -> syn::Result<Vec<TokenStream>> {
    let constructor_field_declaration_role = ProvenanceRole::ConstructorFieldDeclaration;
    let mut items = Vec::new();
    if let Some(syntax) = variant.syntax() {
        let mut field_ordinal = 0_u32;
        for (item_index, item) in syntax.syntax_template().items().iter().enumerate() {
            let item_ordinal = u32::try_from(item_index)
                .map_err(|_| syn::Error::new(variant.name().span(), "too many production items"))?;
            let item_key =
                provenance_key(facade, ProvenanceRole::ConstructorSyntaxItem, item_ordinal);
            match item {
                SyntaxTemplateItem::Terminal(text) => items.push(quote! {
                    #facade::HostProductionItem::Terminal { key: #item_key, text: #text.to_owned() }
                }),
                SyntaxTemplateItem::Field(name) => {
                    let declaration_index = variant
                        .fields()
                        .iter()
                        .position(|field| field.name() == name)
                        .ok_or_else(|| {
                            syn::Error::new(variant.name().span(), "checked field disappeared")
                        })?;
                    let declaration_ordinal = u32::try_from(declaration_index)
                        .map_err(|_| syn::Error::new(variant.name().span(), "too many fields"))?;
                    let sort_key = format_ident!(
                        "__krs_enum_field_{nonce:016x}_{variant_index}_{declaration_index}"
                    );
                    let field = &variant.fields()[declaration_index];
                    let sort = host_sort_reference(
                        facade,
                        ProvenanceRole::ConstructorFieldSort,
                        declaration_ordinal,
                        &sort_key,
                        &field.term_sort().sort_spelling(),
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
                            field: #facade::ProductionFieldId::new(#name)
                                .expect("Rust fields are valid production fields"),
                            sort: ::std::boxed::Box::new(#sort),
                        }
                    });
                    field_ordinal = field_ordinal
                        .checked_add(1)
                        .ok_or_else(|| syn::Error::new(variant.name().span(), "too many fields"))?;
                }
            }
        }
    } else {
        let key = provenance_key(facade, ProvenanceRole::ConstructorDeclaration, 0);
        let terminal = variant.name().to_string();
        items.push(quote! {
            #facade::HostProductionItem::Terminal { key: #key, text: #terminal.to_owned() }
        });
        for (field_index, field) in variant.fields().iter().enumerate() {
            let ordinal = u32::try_from(field_index)
                .map_err(|_| syn::Error::new(variant.name().span(), "too many fields"))?;
            let field_key =
                provenance_key(facade, ProvenanceRole::ConstructorFieldDeclaration, ordinal);
            let sort_key =
                format_ident!("__krs_enum_field_{nonce:016x}_{variant_index}_{field_index}");
            let sort = host_sort_reference(
                facade,
                ProvenanceRole::ConstructorFieldSort,
                ordinal,
                &sort_key,
                &field.term_sort().sort_spelling(),
            );
            let name = field.name().to_string();
            items.push(quote! {
                #facade::HostProductionItem::NonTerminal {
                    key: #field_key,
                    field_key: #facade::ProvenanceKey::new(
                        #constructor_field_declaration_role, #ordinal,
                    ).expect("KRS parser roles are nonempty"),
                    declaration_key: ::core::option::Option::Some(
                        #facade::ProvenanceKey::new(#constructor_field_declaration_role, #ordinal)
                            .expect("KRS parser roles are nonempty"),
                    ),
                    field: #facade::ProductionFieldId::new(#name)
                        .expect("Rust fields are valid production fields"),
                    sort: ::std::boxed::Box::new(#sort),
                }
            });
        }
    }
    Ok(items)
}
