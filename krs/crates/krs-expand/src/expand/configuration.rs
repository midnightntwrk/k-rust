//! Configuration declarations: `#[k::configuration]` and `#[k::cell]`.

use crate::ExpandError;
use krs_diagnostic::codes::expand;
use krs_ir::wire::{
    WireCellDeclaration, WireCellDeclarationReference, WireCellField, WireCellIdentity,
    WireCellReference, WirePayload, WireSortReference, WireTypeReference,
};
use krs_ir::{
    CellWrapper, DescriptorCellColor, DescriptorCellExit, DescriptorCellInitial,
    DescriptorCellMultiplicity, DescriptorCellName, DescriptorCellStream, DescriptorCellType,
    DescriptorConfigurationRoot, ProtocolCellContent,
};
use krs_syntax::KrsSyntax;
use krs_syntax::{ConfigurationCellContent, TokenRange};
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote, quote_spanned};
use syn::spanned::Spanned;
use syn::{Ident, ItemStruct, Path, parse_quote};

use super::factory::{DescriptorFactory, FactoryPayload};
use super::ledger::KeyLedger;
use super::nonce::expansion_nonce;
use super::terms::WireSlots;
use super::tokens::{call_site_cfg_attributes, call_site_ident, spelling};
use crate::environment::MacroEnvironment;
use crate::provenance::host_provenance;

pub(crate) fn configuration(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> crate::Result<TokenStream> {
    let attribute = krs_syntax::ConfigurationAttribute::parse_tokens(attributes)?;
    let declaration = krs_syntax::ConfigurationDeclaration::parse_tokens(item)?;
    let facade = env.facade_path()?;
    let anchors = declaration.descriptor_provenance(&attribute)?;
    let fallback = krs_syntax::TokenRange::for_tokens(declaration.item())?;
    let provenance = host_provenance(env, &facade, fallback, &anchors);
    let ledger = KeyLedger::new(&anchors, &[]);
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
    let root = configuration_root(&ledger, &attribute)?;
    let mut slots = WireSlots::new(&facade);
    let (field_helpers, fields) = configuration_fields(
        (&facade, &ledger),
        &declaration,
        &declared,
        &declared_key,
        &mut slots,
    )?;
    let declaration_wire = WireCellDeclaration {
        key: ledger.define(declaration.name_key())?,
        fields,
    };
    ledger.finish()?;

    let wire = serde_json::to_string(&(root, declaration_wire)).expect("KRS wire values serialize");
    let slot_tokens = slots.tokens();
    let payload = Ident::new("fixed_configuration", Span::call_site());

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
        payload: FactoryPayload::prepared(payload.clone()),
        cfg: quote!(::core::default::Default::default()),
        attributes: quote!(#(#cfg)*),
        provenance: quote! {
            #provenance
            .merge(initializer_provenance)
            .expect("configuration and initializer provenance keys are disjoint")
        },
        prelude: {
            // Spanned at the configuration's name, where rustc reports a
            // missing initializer through the fallback trait's bound.
            let span = declaration.name().span();
            let mut configuration = declared.clone();
            configuration.set_span(span);
            // The initializer's payload hands its wire and slot table to
            // this closure inside its own body: a slot that names a
            // declaration through the lexical witness is a value computed
            // there, so the table cannot outlive that body.
            let join = quote! {
                |initializer, initializer_slots| {
                    (#slot_tokens).__krs_fixed_configuration(#wire, initializer, initializer_slots)
                }
            };
            let call = quote_spanned!(span=> #configuration::__krs_initializer_payload(#join));
            quote! {
                #[allow(unused_imports)]
                use #facade::configuration::__KrsInitializerFallback as _;
                let (#payload, initializer_provenance) = #call?;
            }
        },
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
    krs_syntax::CellAttributePayload::parse_tokens(attributes)?;
    let declaration = krs_syntax::ConfigurationDeclaration::parse_tokens(item)?;
    let facade = env.facade_path()?;
    let anchors = declaration.provenance()?;
    let fallback = TokenRange::for_tokens(declaration.item())?;
    let provenance = host_provenance(env, &facade, fallback, &anchors);
    let ledger = KeyLedger::new(&anchors, &[]);
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
    let (field_helpers, fields) = configuration_fields(
        (&facade, &ledger),
        &declaration,
        &declared,
        &declared_key,
        &mut slots,
    )?;
    let declaration_wire = WireCellDeclaration {
        key: ledger.define(declaration.name_key())?,
        fields,
    };
    ledger.finish()?;

    let wire = serde_json::to_string(&WirePayload::Cell(Box::new(declaration_wire)))
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

        // A readable record in a cell position names this struct as rustc
        // resolves it (KF-016); the collector then reads the application as
        // a group term.
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
        // An optional cell's field is `Option<T>`; its wrapper goes inside
        // (KF-023, R7).
        let content = krs_syntax::option_content(&field.ty)
            .filter(|_| cell.is_optional())
            .unwrap_or(&field.ty)
            .clone();
        let wrapped: syn::Type = if cell.is_computation_cell() {
            parse_quote!(#facade::configuration::KCell<#content>)
        } else {
            parse_quote!(#facade::configuration::Cell<#content>)
        };
        field.ty = if cell.is_optional() {
            parse_quote!(::core::option::Option<#wrapped>)
        } else {
            wrapped
        };
    }
    Ok(())
}

pub(super) fn cell_marker_function(field: &Ident) -> Ident {
    format_ident!("__krs_cell_field_type_id_{}", field)
}

fn configuration_root(
    ledger: &KeyLedger<'_>,
    attribute: &krs_syntax::ConfigurationAttribute,
) -> crate::Result<DescriptorConfigurationRoot> {
    Ok(match attribute.optional_root() {
        Some(root) => DescriptorConfigurationRoot::Named {
            key: ledger.define(attribute.root_key())?,
            name: root.value(),
        },
        None => DescriptorConfigurationRoot::GeneratedTop,
    })
}

#[expect(
    clippy::too_many_lines,
    reason = "Each field kind (leaf, nested, optional, collection) maps its metadata to the wire in one place."
)]
fn configuration_fields(
    (facade, ledger): (&Path, &KeyLedger<'_>),
    declaration: &krs_syntax::ConfigurationDeclaration,
    owner: &Ident,
    owner_key: &Ident,
    slots: &mut WireSlots,
) -> crate::Result<(Vec<TokenStream>, Vec<WireCellField>)> {
    let mut helpers = Vec::new();
    let mut fields = Vec::new();
    let mut argument_ordinal = 0_u32;
    for (index, field) in declaration.cells().iter().enumerate() {
        let marker = cell_marker_function(field.name());
        helpers.push(quote! {
            #[doc(hidden)]
            pub fn #marker() -> ::core::any::TypeId {
                struct __KrsCellFieldMarker;
                ::core::any::TypeId::of::<__KrsCellFieldMarker>()
            }
        });
        let keys = field.attribute().keys();
        let emitted_name = field
            .attribute()
            .name()
            .map(|name| -> crate::Result<_> {
                Ok(DescriptorCellName {
                    key: ledger.define(keys.name())?,
                    value: name.value(),
                })
            })
            .transpose()?;
        let color = field
            .attribute()
            .color()
            .map(|color| -> crate::Result<_> {
                Ok(DescriptorCellColor {
                    key: ledger.define(keys.color())?,
                    value: color.value(),
                })
            })
            .transpose()?;
        let multiplicity = field
            .attribute()
            .multiplicity()
            .map(|value| -> crate::Result<_> {
                Ok(DescriptorCellMultiplicity {
                    key: ledger.define(keys.multiplicity())?,
                    value: value.value(),
                })
            })
            .transpose()?;
        let cell_type = field
            .attribute()
            .cell_type()
            .map(|value| {
                Ok::<_, ExpandError>(DescriptorCellType {
                    key: ledger.define(keys.cell_type())?,
                    value: value.value().try_into().map_err(|error| {
                        ExpandError::new(expand::CONFIGURATION_SHAPE, value.span(), error)
                    })?,
                })
            })
            .transpose()?;
        let stream = field
            .attribute()
            .stream()
            .map(|value| {
                let stream = krs_ir::CellStream::from_k(&value.value()).ok_or_else(|| {
                    ExpandError::new(
                        expand::CONFIGURATION_SHAPE,
                        value.span(),
                        "K supports stream=\"stdin\" and \"stdout\"",
                    )
                })?;
                Ok::<_, ExpandError>(DescriptorCellStream {
                    key: ledger.define(keys.stream())?,
                    value: stream,
                })
            })
            .transpose()?;
        let exit = field
            .attribute()
            .exit()
            .map(|_| {
                ledger
                    .define(keys.exit())
                    .map(|key| DescriptorCellExit { key })
            })
            .transpose()?;
        let initial = field
            .attribute()
            .initial()
            .map(|_| {
                ledger
                    .define(keys.initial())
                    .map(|key| DescriptorCellInitial { key })
            })
            .transpose()?;
        let content = configuration_content(
            field,
            index,
            &mut argument_ordinal,
            &mut ConfigurationFieldContext {
                facade,
                ledger,
                owner,
                owner_key,
                helpers: &mut helpers,
                slots,
            },
        )?;
        fields.push(WireCellField {
            reference: WireCellReference {
                key: ledger.define(field.key())?,
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
            stream,
            exit,
            initial,
            content,
        });
    }
    Ok((helpers, fields))
}

struct ConfigurationFieldContext<'a> {
    facade: &'a Path,
    ledger: &'a KeyLedger<'a>,
    owner: &'a Ident,
    owner_key: &'a Ident,
    helpers: &'a mut Vec<TokenStream>,
    slots: &'a mut WireSlots,
}

fn configuration_content(
    field: &krs_syntax::FixedCellField,
    index: usize,
    argument_ordinal: &mut u32,
    assembly: &mut ConfigurationFieldContext<'_>,
) -> crate::Result<krs_ir::wire::WireCellContent> {
    let ConfigurationFieldContext {
        facade,
        ledger,
        owner,
        owner_key,
        helpers,
        slots,
    } = assembly;
    let content = match field.cell_content() {
        ConfigurationCellContent::Leaf {
            sort,
            arguments,
            computation,
            ..
        } => {
            let authored_path = spelling(sort);
            let sort_key = format_ident!("__krs_configuration_sort_{}_{}", owner_key, index);
            helpers.push(quote! {
                #[doc(hidden)]
                pub fn #sort_key() -> ::core::any::TypeId {
                    ::core::any::TypeId::of::<#sort>()
                }
            });
            let argument_references = configuration_sort_arguments(
                arguments,
                &mut SortArgumentContext {
                    facade,
                    ledger,
                    owner,
                    owner_key,
                    cfg: &[],
                    helpers,
                    slots,
                    ordinal: argument_ordinal,
                },
            )?;
            ProtocolCellContent::Leaf {
                wrapper_key: ledger.define(field.wrapper_key())?,
                wrapper: if *computation {
                    CellWrapper::KCell
                } else {
                    CellWrapper::Cell
                },
                sort: WireSortReference {
                    key: ledger.define(field.content_key())?,
                    target: WireTypeReference {
                        slot: slots.type_slot(quote!(#facade::HostTypeKey(#owner::#sort_key))),
                        authored_path,
                    },
                },
                arguments: argument_references,
            }
        }
        ConfigurationCellContent::Nested { declaration } => {
            let generated = declaration;
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
                    key: ledger.define(field.content_key())?,
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

/// What [`configuration_sort_arguments`] needs to emit one argument's
/// `TypeId` helper and wire reference.
pub(super) struct SortArgumentContext<'a, 'b> {
    pub(super) facade: &'a Path,
    /// The ledger of the descriptor the arguments belong to.
    pub(super) ledger: &'a KeyLedger<'a>,
    /// The type whose associated helpers the keys are.
    pub(super) owner: &'a Ident,
    /// Distinguishes the helpers' names.
    pub(super) owner_key: &'a Ident,
    /// The `cfg` attributes the helpers carry.
    pub(super) cfg: &'a [syn::Attribute],
    pub(super) helpers: &'a mut Vec<TokenStream>,
    pub(super) slots: &'a mut WireSlots,
    /// The number of the next helper.
    pub(super) ordinal: &'b mut u32,
}

/// The wire tree of a cell's or a configuration variable's collection
/// arguments, each keyed by its path, with one `TypeId` helper per argument
/// numbered in preorder.
pub(super) fn configuration_sort_arguments(
    arguments: &[krs_syntax::SortArgument],
    context: &mut SortArgumentContext<'_, '_>,
) -> crate::Result<Vec<krs_ir::ProtocolSortArgument<WireSortReference>>> {
    let mut output = Vec::with_capacity(arguments.len());
    for argument in arguments {
        let facade = context.facade;
        let owner = context.owner;
        let generated = &argument.path;
        let ty = super::tokens::sort_type_tokens(facade, generated, argument.dynamic);
        let authored_path = spelling(&argument.path);
        let key = format_ident!(
            "__krs_configuration_sort_argument_{}_{}",
            context.owner_key,
            *context.ordinal
        );
        let cfg = context.cfg;
        context.helpers.push(quote! {
            #(#cfg)*
            #[doc(hidden)]
            pub fn #key() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<#ty>()
            }
        });
        *context.ordinal = context.ordinal.checked_add(1).ok_or_else(|| {
            ExpandError::new(
                expand::DESCRIPTOR_CAPACITY,
                argument.path.span(),
                "too many configuration sort arguments",
            )
        })?;
        let sort = WireSortReference {
            key: context.ledger.define(argument.key())?,
            target: WireTypeReference {
                slot: context
                    .slots
                    .type_slot(quote!(#facade::HostTypeKey(#owner::#key))),
                authored_path,
            },
        };
        output.push(krs_ir::ProtocolSortArgument {
            sort,
            arguments: configuration_sort_arguments(&argument.arguments, context)?,
        });
    }
    Ok(output)
}
