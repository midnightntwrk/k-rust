//! Configuration declarations: `#[k::configuration]` and `#[k::cell]`.

use crate::ExpandError;
use krs_diagnostic::codes::expand;
use krs_ir::wire::{
    WireCellDeclaration, WireCellDeclarationReference, WireCellField, WireCellIdentity,
    WireCellReference, WirePayload, WireSortReference, WireTypeReference,
};
use krs_ir::{
    CellWrapper, DescriptorCellColor, DescriptorCellMultiplicity, DescriptorCellName,
    DescriptorCellType, DescriptorConfigurationRoot, ProtocolCellContent,
};
use krs_syntax::KrsSyntax;
use krs_syntax::{ConfigurationCellContent, ProvenanceRole, TokenRange};
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use syn::spanned::Spanned;
use syn::{Ident, ItemStruct, Path, parse_quote};

use super::factory::{DescriptorFactory, FactoryPayload};
use super::nonce::expansion_nonce;
use super::terms::{WireSlots, wire_key};
use super::tokens::{call_site_cfg_attributes, call_site_ident, call_site_path, spelling};
use crate::environment::MacroEnvironment;
use crate::provenance::host_provenance;

pub(crate) fn configuration(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> crate::Result<TokenStream> {
    let configuration_declaration_role = ProvenanceRole::ConfigurationDeclaration;
    let attribute = krs_syntax::ConfigurationAttribute::parse_tokens(attributes)?;
    let declaration = krs_syntax::ConfigurationDeclaration::parse_tokens(item)?;
    let facade = env.facade_path()?;
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
    let root = configuration_root(&attribute);
    let mut slots = WireSlots::new(&facade);
    let (field_helpers, fields) =
        configuration_fields(&facade, &declaration, &declared, &declared_key, &mut slots)?;

    let wire = serde_json::to_string(&(
        root,
        WireCellDeclaration {
            key: wire_key(configuration_declaration_role, 0),
            fields,
        },
    ))
    .expect("KRS wire values serialize");
    let slot_tokens = slots.tokens();

    let factory_tokens = DescriptorFactory {
        facade: &facade,
        factory: &factory,
        name: quote!(#name),
        item_kind: quote!(#facade::ItemKind::Configuration),
        disambiguator: quote!(""),
        identity_label: "Cargo and Rust macro context form a valid host identity",
        declared_type: quote! {
            ::core::option::Option::Some(
                #facade::HostDeclarationIdentity::Nominal(
                    #facade::HostTypeKey(#declared_key),
                ),
            )
        },
        payload: FactoryPayload::fixed_configuration(wire, slot_tokens),
        cfg: quote!(::core::default::Default::default()),
        attributes: quote!(#(#cfg)*),
        provenance: quote! {
            #provenance
            .merge(initializer_provenance)
            .expect("configuration and initializer provenance keys are disjoint")
        },
        prelude: quote!(let (initializer, initializer_slots, initializer_provenance) = #declared::__krs_initializer_payload()?;),
    }
    .render();

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

        #factory_tokens
    })
}

pub(crate) fn cell(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> crate::Result<TokenStream> {
    let configuration_declaration_role = ProvenanceRole::ConfigurationDeclaration;
    krs_syntax::CellAttributePayload::parse_tokens(attributes)?;
    let declaration = krs_syntax::ConfigurationDeclaration::parse_tokens(item)?;
    let facade = env.facade_path()?;
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
    let mut slots = WireSlots::new(&facade);
    let (field_helpers, fields) =
        configuration_fields(&facade, &declaration, &declared, &declared_key, &mut slots)?;

    let wire = serde_json::to_string(&WirePayload::Cell(Box::new(WireCellDeclaration {
        key: wire_key(configuration_declaration_role, 0),
        fields,
    })))
    .expect("KRS wire values serialize");
    let slot_tokens = slots.tokens();

    let factory_tokens = DescriptorFactory {
        facade: &facade,
        factory: &factory,
        name: quote!(#name),
        item_kind: quote!(#facade::ItemKind::Cell),
        disambiguator: quote!(""),
        identity_label: "Cargo and Rust macro context form a valid host identity",
        declared_type: quote! {
            ::core::option::Option::Some(
                #facade::HostDeclarationIdentity::Nominal(#facade::HostTypeKey(#declared_key)),
            )
        },
        payload: FactoryPayload::wire(wire, slot_tokens),
        cfg: quote!(::core::default::Default::default()),
        attributes: quote!(#(#cfg)*),
        provenance: quote!(#provenance),
        prelude: TokenStream::new(),
    }
    .render();

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

        #factory_tokens
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
) -> crate::Result<()> {
    let syn::Fields::Named(fields) = &mut item.fields else {
        return Err(ExpandError::new(
            expand::CONFIGURATION_SHAPE,
            item.fields.span(),
            "a fixed configuration must be a named-field struct",
        ));
    };
    for field in &mut fields.named {
        let Some(name) = &field.ident else {
            continue;
        };
        let Some(cell) = declaration.cells().iter().find(|cell| cell.name() == name) else {
            return Err(ExpandError::new(
                expand::MISSING_CHECKED_FIELD,
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
    attribute: &krs_syntax::ConfigurationAttribute,
) -> DescriptorConfigurationRoot {
    attribute
        .optional_root()
        .map_or(DescriptorConfigurationRoot::GeneratedTop, |root| {
            DescriptorConfigurationRoot::Named {
                key: wire_key(ProvenanceRole::ConfigurationRoot, 0),
                name: root.value(),
            }
        })
}

fn configuration_fields(
    facade: &Path,
    declaration: &krs_syntax::ConfigurationDeclaration,
    owner: &Ident,
    owner_key: &Ident,
    slots: &mut WireSlots,
) -> crate::Result<(Vec<TokenStream>, Vec<WireCellField>)> {
    let mut helpers = Vec::new();
    let mut fields = Vec::new();
    let mut argument_ordinal = 0_u32;
    for (index, field) in declaration.cells().iter().enumerate() {
        let ordinal = u32::try_from(index).map_err(|_| {
            ExpandError::new(
                expand::DESCRIPTOR_CAPACITY,
                field.name().span(),
                "too many fixed cells",
            )
        })?;
        let marker = cell_marker_function(field.name());
        helpers.push(quote! {
            #[doc(hidden)]
            pub fn #marker() -> ::core::any::TypeId {
                struct __KrsCellFieldMarker;
                ::core::any::TypeId::of::<__KrsCellFieldMarker>()
            }
        });
        let emitted_name = field.attribute().name().map(|name| DescriptorCellName {
            key: wire_key(ProvenanceRole::ConfigurationCellName, ordinal),
            value: name.value(),
        });
        let color = field.attribute().color().map(|color| DescriptorCellColor {
            key: wire_key(ProvenanceRole::ConfigurationCellColor, ordinal),
            value: color.value(),
        });
        let multiplicity =
            field
                .attribute()
                .multiplicity()
                .map(|value| DescriptorCellMultiplicity {
                    key: wire_key(ProvenanceRole::ConfigurationCellMultiplicity, ordinal),
                    value: value.value(),
                });
        let cell_type = field
            .attribute()
            .cell_type()
            .map(|value| {
                Ok::<_, ExpandError>(DescriptorCellType {
                    key: wire_key(ProvenanceRole::ConfigurationCellType, ordinal),
                    value: value.value().try_into().map_err(|error| {
                        ExpandError::new(expand::CONFIGURATION_SHAPE, value.span(), error)
                    })?,
                })
            })
            .transpose()?;
        let content = configuration_content(
            field.cell_content(),
            index,
            ordinal,
            &mut argument_ordinal,
            &mut ConfigurationFieldContext {
                facade,
                owner,
                owner_key,
                helpers: &mut helpers,
                slots,
            },
        )?;
        fields.push(WireCellField {
            reference: WireCellReference {
                key: wire_key(ProvenanceRole::ConfigurationField, ordinal),
                cell: WireCellIdentity {
                    owner: slots.type_slot(quote!(#facade::HostTypeKey(#owner_key))),
                    field: slots.type_slot(quote!(#facade::HostTypeKey(#owner::#marker))),
                },
            },
            rust_field: field.name().to_string(),
            emitted_name,
            color,
            multiplicity,
            cell_type,
            content,
        });
    }
    Ok((helpers, fields))
}

struct ConfigurationFieldContext<'a> {
    facade: &'a Path,
    owner: &'a Ident,
    owner_key: &'a Ident,
    helpers: &'a mut Vec<TokenStream>,
    slots: &'a mut WireSlots,
}

fn configuration_content(
    content: &ConfigurationCellContent,
    index: usize,
    ordinal: u32,
    argument_ordinal: &mut u32,
    assembly: &mut ConfigurationFieldContext<'_>,
) -> crate::Result<krs_ir::wire::WireCellContent> {
    let ConfigurationFieldContext {
        facade,
        owner,
        owner_key,
        helpers,
        slots,
    } = assembly;
    let content = match content {
        ConfigurationCellContent::Leaf {
            sort,
            arguments,
            computation,
            ..
        } => {
            let sort = call_site_path(sort)?;
            let authored_path = spelling(&sort);
            let sort_key = format_ident!("__krs_configuration_sort_{}_{}", owner_key, index);
            helpers.push(quote! {
                #[doc(hidden)]
                pub fn #sort_key() -> ::core::any::TypeId {
                    ::core::any::TypeId::of::<#sort>()
                }
            });
            let mut argument_references = Vec::new();
            for argument in arguments {
                let generated = call_site_path(argument)?;
                let authored_path = spelling(argument);
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
                let ordinal = *argument_ordinal;
                *argument_ordinal = argument_ordinal.checked_add(1).ok_or_else(|| {
                    ExpandError::new(
                        expand::DESCRIPTOR_CAPACITY,
                        argument.span(),
                        "too many configuration sort arguments",
                    )
                })?;
                argument_references.push(WireSortReference {
                    key: wire_key(ProvenanceRole::ConfigurationCellContentArgument, ordinal),
                    target: WireTypeReference {
                        slot: slots.type_slot(quote!(#facade::HostTypeKey(#owner::#key))),
                        authored_path,
                    },
                });
            }
            ProtocolCellContent::Leaf {
                wrapper_key: wire_key(ProvenanceRole::ConfigurationCellWrapper, ordinal),
                wrapper: if *computation {
                    CellWrapper::KCell
                } else {
                    CellWrapper::Cell
                },
                sort: WireSortReference {
                    key: wire_key(ProvenanceRole::ConfigurationCellContent, ordinal),
                    target: WireTypeReference {
                        slot: slots.type_slot(quote!(#facade::HostTypeKey(#owner::#sort_key))),
                        authored_path,
                    },
                },
                arguments: argument_references,
            }
        }
        ConfigurationCellContent::Nested { declaration } => {
            let generated = call_site_path(declaration)?;
            let authored_path = spelling(declaration);
            let nested_key = format_ident!("__krs_configuration_nested_{}_{}", owner_key, index);
            helpers.push(quote! {
                #[doc(hidden)]
                pub fn #nested_key() -> ::core::any::TypeId {
                    ::core::any::TypeId::of::<#generated>()
                }
            });
            ProtocolCellContent::Nested {
                declaration: WireCellDeclarationReference {
                    key: wire_key(ProvenanceRole::ConfigurationCellContent, ordinal),
                    declaration: WireTypeReference {
                        slot: slots.type_slot(quote!(#facade::HostTypeKey(#owner::#nested_key))),
                        authored_path,
                    },
                },
            }
        }
    };
    Ok(content)
}
