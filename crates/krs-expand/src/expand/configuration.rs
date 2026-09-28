//! Configuration declarations: `#[k::configuration]` and `#[k::cell]`.

use krs_syntax::KrsSyntax;
use krs_syntax::{ConfigurationCellContent, ProvenanceRole, TokenRange, role_tokens};
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use syn::spanned::Spanned;
use syn::{Ident, ItemStruct, Path, parse_quote};

use super::nonce::expansion_nonce;
use super::tokens::{call_site_cfg_attributes, call_site_ident, call_site_path, spelling};
use crate::environment::MacroEnvironment;
use crate::provenance::host_provenance;

#[allow(clippy::too_many_lines)]
pub(crate) fn configuration(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> syn::Result<TokenStream> {
    let configuration_declaration_role = ProvenanceRole::ConfigurationDeclaration;
    let attribute = krs_syntax::ConfigurationAttribute::parse_tokens(attributes)?;
    let declaration = krs_syntax::ConfigurationDeclaration::parse_tokens(item)?;
    let facade = env.facade_path()?;
    let configuration_declaration_role = role_tokens(configuration_declaration_role, &facade);
    let mut anchors = declaration.provenance()?;
    anchors.extend(attribute.provenance()?);
    let fallback = krs_syntax::TokenRange::for_tokens(declaration.item())?;
    let provenance = host_provenance(env, &facade, fallback, &anchors);
    let nonce = expansion_nonce(env, "configuration", declaration.name(), fallback);
    let declared_key = format_ident!(
        "__krs_configuration_type_{nonce:016x}",
        span = Span::call_site()
    );
    let factory = format_ident!(
        "__krs_configuration_descriptor_{nonce:016x}",
        span = Span::call_site()
    );
    let mut item = declaration.item().clone();
    inject_inferred_cell_wrappers(&mut item, &declaration, &facade)?;
    strip_cell_helpers(&mut item);
    let cfg = call_site_cfg_attributes(&item.attrs)?;
    let name = declaration.name().to_string();
    let declared = call_site_ident(declaration.name())?;
    let root = configuration_root(&facade, &attribute);
    let (field_helpers, fields) =
        configuration_fields(&facade, &declaration, &declared, &declared_key)?;

    Ok(quote! {
        #item

        #(#cfg)*
        impl #declared {
            #[doc(hidden)]
            pub fn __krs_configuration_type_key() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<Self>()
            }
            #(#field_helpers)*
        }

        #(#cfg)*
        #[doc(hidden)]
        fn #declared_key() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#declared>()
        }

        #(#cfg)*
        #[doc(hidden)]
        fn #factory() -> #facade::HostDescriptor {
            let (initializer, initializer_provenance) = #declared::__krs_initializer_payload();
            #facade::HostDescriptor {
                protocol_version: #facade::SchemaVersion::CURRENT,
                id: #facade::HostItemId::from_macro_context(
                    env!("CARGO_PKG_NAME"),
                    env!("CARGO_PKG_VERSION"),
                    env!("CARGO_MANIFEST_DIR"),
                    module_path!(),
                    #name,
                    #facade::ItemKind::Configuration,
                    "",
                )
                .expect("Cargo and Rust macro context form a valid host identity"),
                declared_type: ::core::option::Option::Some(
                    #facade::HostDeclarationIdentity::Nominal(
                        #facade::HostTypeKey(#declared_key),
                    ),
                ),
                payload: #facade::HostDescriptorPayload::FixedConfiguration(
                    ::std::boxed::Box::new(#facade::HostFixedConfiguration {
                        root: #root,
                        declaration: #facade::HostConfigurationDeclaration {
                            key: #facade::ProvenanceKey::new(#configuration_declaration_role, 0),
                            fields: ::std::vec![#(#fields),*],
                        },
                        initializer,
                    }),
                ),
                cfg: ::core::default::Default::default(),
                provenance: #provenance
                    .merge(initializer_provenance)
                    .expect("configuration and initializer provenance keys are disjoint"),
            }
        }

        #(#cfg)*
        #facade::__register_host_descriptor!(#factory);
    })
}

pub(crate) fn cell(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> syn::Result<TokenStream> {
    let configuration_declaration_role = ProvenanceRole::ConfigurationDeclaration;
    krs_syntax::CellAttributePayload::parse_tokens(attributes)?;
    let declaration = krs_syntax::ConfigurationDeclaration::parse_tokens(item)?;
    let facade = env.facade_path()?;
    let configuration_declaration_role = role_tokens(configuration_declaration_role, &facade);
    let anchors = declaration.provenance()?;
    let fallback = TokenRange::for_tokens(declaration.item())?;
    let provenance = host_provenance(env, &facade, fallback, &anchors);
    let nonce = expansion_nonce(env, "cell", declaration.name(), fallback);
    let declared_key = format_ident!("__krs_cell_type_{nonce:016x}");
    let factory = format_ident!("__krs_cell_descriptor_{nonce:016x}");
    let mut item = declaration.item().clone();
    inject_inferred_cell_wrappers(&mut item, &declaration, &facade)?;
    strip_cell_helpers(&mut item);
    let cfg = call_site_cfg_attributes(&item.attrs)?;
    let declared = call_site_ident(declaration.name())?;
    let name = declaration.name().to_string();
    let (field_helpers, fields) =
        configuration_fields(&facade, &declaration, &declared, &declared_key)?;

    Ok(quote! {
        #item

        #(#cfg)*
        impl #declared {
            #[doc(hidden)]
            pub fn __krs_configuration_type_key() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<Self>()
            }
            #(#field_helpers)*
        }

        #(#cfg)*
        #[doc(hidden)]
        fn #declared_key() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#declared>()
        }

        #(#cfg)*
        #[doc(hidden)]
        fn #factory() -> #facade::HostDescriptor {
            #facade::HostDescriptor {
                protocol_version: #facade::SchemaVersion::CURRENT,
                id: #facade::HostItemId::from_macro_context(
                    env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"),
                    env!("CARGO_MANIFEST_DIR"), module_path!(), #name,
                    #facade::ItemKind::Cell, "",
                ).expect("Cargo and Rust macro context form a valid host identity"),
                declared_type: ::core::option::Option::Some(
                    #facade::HostDeclarationIdentity::Nominal(#facade::HostTypeKey(#declared_key)),
                ),
                payload: #facade::HostDescriptorPayload::Cell(::std::boxed::Box::new(
                    #facade::HostCellDeclaration {
                        key: #facade::ProvenanceKey::new(#configuration_declaration_role, 0),
                        fields: ::std::vec![#(#fields),*],
                    }
                )),
                cfg: ::core::default::Default::default(),
                provenance: #provenance,
            }
        }

        #(#cfg)*
        #facade::__register_host_descriptor!(#factory);
    })
}

fn strip_cell_helpers(item: &mut ItemStruct) {
    if let syn::Fields::Named(fields) = &mut item.fields {
        for field in &mut fields.named {
            field.attrs.retain(|attribute| {
                attribute
                    .path()
                    .segments
                    .last()
                    .is_none_or(|segment| segment.ident != "cell")
            });
        }
    }
}

fn inject_inferred_cell_wrappers(
    item: &mut ItemStruct,
    declaration: &krs_syntax::ConfigurationDeclaration,
    facade: &Path,
) -> syn::Result<()> {
    let syn::Fields::Named(fields) = &mut item.fields else {
        return Err(syn::Error::new(
            item.fields.span(),
            "a fixed configuration must be a named-field struct",
        ));
    };
    for field in &mut fields.named {
        let Some(name) = &field.ident else {
            continue;
        };
        let Some(cell) = declaration.cells().iter().find(|cell| cell.name() == name) else {
            return Err(syn::Error::new(
                name.span(),
                "configuration field disappeared during wrapper injection",
            ));
        };
        if !cell.has_inferred_wrapper() {
            continue;
        }
        let content = field.ty.clone();
        field.ty = if cell.is_computation_cell() {
            parse_quote!(#facade::configuration::KCell<#content>)
        } else {
            parse_quote!(#facade::configuration::Cell<#content>)
        };
    }
    Ok(())
}

pub(super) fn cell_marker_function(field: &Ident) -> Ident {
    format_ident!("__krs_cell_field_type_id_{}", field)
}

fn configuration_root(
    facade: &Path,
    attribute: &krs_syntax::ConfigurationAttribute,
) -> TokenStream {
    let configuration_root_role = role_tokens(ProvenanceRole::ConfigurationRoot, facade);
    if let Some(root) = attribute.optional_root() {
        let value = root.value();
        quote! {
            #facade::DescriptorConfigurationRoot::Named {
                key: #facade::ProvenanceKey::new(#configuration_root_role, 0),
                name: #value.to_owned(),
            }
        }
    } else {
        quote!(#facade::DescriptorConfigurationRoot::GeneratedTop)
    }
}

#[allow(clippy::too_many_lines)]
fn configuration_fields(
    facade: &Path,
    declaration: &krs_syntax::ConfigurationDeclaration,
    owner: &Ident,
    owner_key: &Ident,
) -> syn::Result<(Vec<TokenStream>, Vec<TokenStream>)> {
    let configuration_cell_name_role = role_tokens(ProvenanceRole::ConfigurationCellName, facade);
    let configuration_cell_color_role = role_tokens(ProvenanceRole::ConfigurationCellColor, facade);
    let configuration_cell_multiplicity_role =
        role_tokens(ProvenanceRole::ConfigurationCellMultiplicity, facade);
    let configuration_cell_type_role = role_tokens(ProvenanceRole::ConfigurationCellType, facade);
    let configuration_cell_content_argument_role =
        role_tokens(ProvenanceRole::ConfigurationCellContentArgument, facade);
    let configuration_cell_wrapper_role =
        role_tokens(ProvenanceRole::ConfigurationCellWrapper, facade);
    let configuration_cell_content_role =
        role_tokens(ProvenanceRole::ConfigurationCellContent, facade);
    let configuration_field_role = role_tokens(ProvenanceRole::ConfigurationField, facade);
    let mut helpers = Vec::new();
    let mut fields = Vec::new();
    let mut argument_ordinal = 0_u32;
    for (index, field) in declaration.cells().iter().enumerate() {
        let ordinal = u32::try_from(index)
            .map_err(|_| syn::Error::new(field.name().span(), "too many fixed cells"))?;
        let marker = cell_marker_function(field.name());
        helpers.push(quote! {
            #[doc(hidden)]
            pub fn #marker() -> ::core::any::TypeId {
                struct __KrsCellFieldMarker;
                ::core::any::TypeId::of::<__KrsCellFieldMarker>()
            }
        });
        let rust_field = field.name().to_string();
        let emitted_name = field.attribute().name().map_or_else(
            || quote!(::core::option::Option::None),
            |name| {
                let value = name.value();
                quote! {
                    ::core::option::Option::Some(#facade::DescriptorCellName {
                        key: #facade::ProvenanceKey::new(#configuration_cell_name_role, #ordinal),
                        value: #value.to_owned(),
                    })
                }
            },
        );
        let color = field.attribute().color().map_or_else(
            || quote!(::core::option::Option::None),
            |color| {
                let value = color.value();
                quote! {
                    ::core::option::Option::Some(#facade::DescriptorCellColor {
                        key: #facade::ProvenanceKey::new(#configuration_cell_color_role, #ordinal),
                        value: #value.to_owned(),
                    })
                }
            },
        );
        let multiplicity = field.attribute().multiplicity().map_or_else(
            || quote!(::core::option::Option::None),
            |multiplicity| {
                let value = multiplicity.value();
                quote! {
                    ::core::option::Option::Some(#facade::DescriptorCellMultiplicity {
                        key: #facade::ProvenanceKey::new(
                            #configuration_cell_multiplicity_role, #ordinal,
                        ),
                        value: #value.to_owned(),
                    })
                }
            },
        );
        let cell_type = field.attribute().cell_type().map_or_else(
            || quote!(::core::option::Option::None),
            |cell_type| {
                let value = cell_type.value();
                quote! {
                    ::core::option::Option::Some(#facade::DescriptorCellType {
                        key: #facade::ProvenanceKey::new(
                            #configuration_cell_type_role, #ordinal,
                        ),
                        value: #value.to_owned(),
                    })
                }
            },
        );
        let content = match field.cell_content() {
            ConfigurationCellContent::Leaf {
                sort,
                arguments,
                computation,
                ..
            } => {
                let sort = call_site_path(sort)?;
                let authored = spelling(&sort);
                let sort_key = format_ident!("__krs_configuration_sort_{}_{}", owner_key, index);
                helpers.push(quote! {
                    #[doc(hidden)]
                    pub fn #sort_key() -> ::core::any::TypeId {
                        ::core::any::TypeId::of::<#sort>()
                    }
                });
                let wrapper = if *computation {
                    quote!(#facade::CellWrapper::KCell)
                } else {
                    quote!(#facade::CellWrapper::Cell)
                };
                let mut argument_references = Vec::new();
                for argument in arguments {
                    let generated = call_site_path(argument)?;
                    let authored = spelling(argument);
                    let key = format_ident!(
                        "__krs_configuration_sort_argument_{}_{}",
                        owner_key,
                        argument_ordinal
                    );
                    helpers.push(quote! {
                        #[doc(hidden)]
                        pub fn #key() -> ::core::any::TypeId {
                            ::core::any::TypeId::of::<#generated>()
                        }
                    });
                    let ordinal = argument_ordinal;
                    argument_ordinal = argument_ordinal.checked_add(1).ok_or_else(|| {
                        syn::Error::new(argument.span(), "too many configuration sort arguments")
                    })?;
                    argument_references.push(quote! {
                        #facade::HostSortReference {
                            key: #facade::ProvenanceKey::new(
                                #configuration_cell_content_argument_role, #ordinal,
                            ),
                            target: #facade::HostTypeReference {
                                key: #facade::HostTypeKey(#owner::#key),
                                authored_path: #authored.to_owned(),
                            },
                        }
                    });
                }
                quote! {
                    #facade::ProtocolCellContent::Leaf {
                        wrapper_key: #facade::ProvenanceKey::new(
                            #configuration_cell_wrapper_role, #ordinal,
                        ),
                        wrapper: #wrapper,
                        sort: #facade::HostSortReference {
                            key: #facade::ProvenanceKey::new(
                                #configuration_cell_content_role, #ordinal,
                            ),
                            target: #facade::HostTypeReference {
                                key: #facade::HostTypeKey(#owner::#sort_key),
                                authored_path: #authored.to_owned(),
                            },
                        },
                        arguments: ::std::vec![#(#argument_references),*],
                    }
                }
            }
            ConfigurationCellContent::Nested { declaration } => {
                let generated = call_site_path(declaration)?;
                let authored = spelling(declaration);
                let nested_key =
                    format_ident!("__krs_configuration_nested_{}_{}", owner_key, index);
                helpers.push(quote! {
                    #[doc(hidden)]
                    pub fn #nested_key() -> ::core::any::TypeId {
                        ::core::any::TypeId::of::<#generated>()
                    }
                });
                quote! {
                    #facade::ProtocolCellContent::Nested {
                        declaration: #facade::HostCellDeclarationReference {
                            key: #facade::ProvenanceKey::new(
                                #configuration_cell_content_role, #ordinal,
                            ),
                            declaration: #facade::HostTypeReference {
                                key: #facade::HostTypeKey(#owner::#nested_key),
                                authored_path: #authored.to_owned(),
                            },
                        },
                    }
                }
            }
        };
        fields.push(quote! {
            #facade::HostCellField {
                reference: #facade::HostCellReference {
                    key: #facade::ProvenanceKey::new(#configuration_field_role, #ordinal),
                    cell: #facade::HostCellIdentity {
                        owner: #facade::HostTypeKey(#owner_key),
                        field: #facade::HostTypeKey(#owner::#marker),
                    },
                },
                rust_field: #rust_field.to_owned(),
                emitted_name: #emitted_name,
                color: #color,
                multiplicity: #multiplicity,
                cell_type: #cell_type,
                content: #content,
            }
        });
    }
    Ok((helpers, fields))
}
