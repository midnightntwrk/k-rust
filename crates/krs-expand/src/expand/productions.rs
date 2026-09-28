//! Production metadata, documentation, and strictness tokens shared by single productions and enum families.

use krs_syntax::{
    ProvenanceRole, StrictnessAttribute, StrictnessKind as SyntaxStrictnessKind,
    StructuredFormatFragment, role_tokens,
};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::spanned::Spanned;
use syn::{Attribute, Ident, Path};

use super::tokens::{call_site_path, host_sort_reference, spelling};

pub(super) fn strictness_tokens<'a>(
    facade: &Path,
    strictness: Option<&StrictnessAttribute>,
    fields: impl IntoIterator<Item = &'a Ident>,
    nonce: u64,
    cfg: &[Attribute],
) -> syn::Result<(TokenStream, Option<TokenStream>)> {
    let strictness_context_alias_reference_role =
        role_tokens(ProvenanceRole::StrictnessContextAliasReference, facade);
    let strictness_field_reference_role =
        role_tokens(ProvenanceRole::StrictnessFieldReference, facade);
    let strictness_declaration_role = role_tokens(ProvenanceRole::StrictnessDeclaration, facade);
    let Some(strictness) = strictness else {
        return Ok((TokenStream::new(), None));
    };
    let available = fields
        .into_iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>();
    let key_fn = format_ident!("__krs_strictness_result_{nonce:016x}");
    let path = call_site_path(strictness.result_sort())?;
    let spelling = spelling(strictness.result_sort());
    let result_sort = host_sort_reference(
        facade,
        ProvenanceRole::StrictnessResultSort,
        0,
        &key_fn,
        &spelling,
    );
    let result_type = if strictness.has_readable_result() {
        quote!(#path)
    } else {
        quote!(dyn #path)
    };
    let key_function = quote! {
        #(#cfg)*
        #[doc(hidden)]
        fn #key_fn() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#result_type>()
        }
    };
    let kind = match strictness.kind() {
        SyntaxStrictnessKind::Strict => quote!(#facade::StrictnessKind::Strict),
        SyntaxStrictnessKind::SeqStrict => quote!(#facade::StrictnessKind::SeqStrict),
    };
    let using = strictness.using().map_or_else(
        || Ok(quote!(::core::option::Option::None)),
        |alias| -> syn::Result<TokenStream> {
            if strictness.result_sort().segments.last().is_none_or(|segment| segment.ident != "KResult") {
                return Err(syn::Error::new(
                    strictness.result_sort().span(),
                    "a named context alias currently requires the unambiguous `KResult` result sort",
                ));
            }
            let name = alias.to_string();
            Ok(quote!(::core::option::Option::Some(#facade::HostContextAliasReference {
                key: #facade::ProvenanceKey::new(#strictness_context_alias_reference_role, 0),
                alias: #facade::HostItemId::from_macro_context(
                    env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"), env!("CARGO_MANIFEST_DIR"),
                    module_path!(), #name, #facade::ItemKind::ContextAlias, "",
                ).expect("a strictness context alias forms a valid host identity"),
            })))
        },
    )?;
    let mut selected = Vec::new();
    for (index, field) in strictness.fields().iter().enumerate() {
        let name = field.to_string();
        if !available.iter().any(|available| available == &name) {
            return Err(syn::Error::new(
                field.span(),
                "strictness field is not declared",
            ));
        }
        let ordinal = u32::try_from(index)
            .map_err(|_| syn::Error::new(field.span(), "too many strictness fields"))?;
        selected.push(quote! {
            #facade::DescriptorFieldReference {
                key: #facade::ProvenanceKey::new(#strictness_field_reference_role, #ordinal),
                field: #facade::ProductionFieldId::new(#name)
                    .expect("Rust field identifiers are valid production fields"),
            }
        });
    }
    let attribute = quote! {
        #facade::HostProductionAttribute::Strictness {
            key: #facade::ProvenanceKey::new(#strictness_declaration_role, 0),
            kind: #kind,
            using: #using,
            fields: ::std::vec![#(#selected),*],
            result_sort: ::std::boxed::Box::new(#result_sort),
        }
    };
    Ok((key_function, Some(attribute)))
}

pub(super) fn constructor_metadata_wire(
    group: Option<String>,
    avoid: bool,
    format: Option<&krs_syntax::StructuredFormat>,
) -> syn::Result<Vec<krs_ir::wire::WireProductionAttribute>> {
    use super::terms::wire_key;
    use krs_ir::wire::WireProductionAttribute as Attribute;
    use krs_ir::{
        DescriptorFormatFragment, DescriptorGroupReference, FormatFragment, ProductionGroupId,
    };
    let mut attributes = Vec::new();
    if let Some(group) = group {
        attributes.push(Attribute::Group {
            reference: DescriptorGroupReference {
                key: wire_key(ProvenanceRole::ConstructorGroup, 0),
                group: ProductionGroupId::new(group)
                    .expect("checked production groups are valid identities"),
            },
        });
    }
    if avoid {
        attributes.push(Attribute::Avoid {
            key: wire_key(ProvenanceRole::ConstructorAvoid, 0),
        });
    }
    if let Some(format) = format {
        let mut fragments = Vec::new();
        for (index, fragment) in format.fragments().iter().enumerate() {
            let ordinal = u32::try_from(index).map_err(|_| {
                syn::Error::new(format.literal().span(), "too many format fragments")
            })?;
            let fragment = match fragment {
                StructuredFormatFragment::Literal(text) => FormatFragment::Literal(text.to_owned()),
                StructuredFormatFragment::Item(position) => FormatFragment::Item(*position),
                StructuredFormatFragment::Newline => FormatFragment::Newline,
                StructuredFormatFragment::Indent => FormatFragment::Indent,
                StructuredFormatFragment::Dedent => FormatFragment::Dedent,
            };
            fragments.push(DescriptorFormatFragment {
                key: wire_key(ProvenanceRole::ConstructorFormatFragment, ordinal),
                fragment,
            });
        }
        attributes.push(Attribute::Format {
            key: wire_key(ProvenanceRole::ConstructorFormat, 0),
            fragments,
        });
    }
    Ok(attributes)
}

pub(super) fn production_documentation_wire(
    documentation: &[krs_syntax::ProductionDocumentation],
) -> syn::Result<Vec<krs_ir::wire::WireProductionAttribute>> {
    use super::terms::wire_key;
    documentation
        .iter()
        .enumerate()
        .map(|(ordinal, documentation)| {
            let ordinal = u32::try_from(ordinal).map_err(|_| {
                syn::Error::new(documentation.literal().span(), "too many rustdoc lines")
            })?;
            Ok(krs_ir::wire::WireProductionAttribute::Documentation {
                key: wire_key(ProvenanceRole::ConstructorDocumentation, ordinal),
                text: documentation.text().to_owned(),
            })
        })
        .collect()
}

pub(super) fn strictness_wire(
    facade: &Path,
    strictness: Option<&StrictnessAttribute>,
    nonce: u64,
    slots: &mut super::terms::WireSlots,
) -> Option<krs_ir::wire::WireProductionAttribute> {
    use super::terms::wire_key;
    use krs_ir::wire::{
        WireContextAliasReference, WireProductionAttribute, WireSortReference, WireTypeReference,
    };
    use krs_ir::{DescriptorFieldReference, ProductionFieldId, StrictnessKind};
    let strictness = strictness?;
    let key_fn = format_ident!("__krs_strictness_result_{nonce:016x}");
    let spelling = spelling(strictness.result_sort());
    let using = strictness.using().map(|alias| {
        let name = alias.to_string();
        let expression = quote!(#facade::HostItemId::from_macro_context(
            env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"), env!("CARGO_MANIFEST_DIR"),
            module_path!(), #name, #facade::ItemKind::ContextAlias, "",
        ).expect("a strictness context alias forms a valid host identity"));
        WireContextAliasReference {
            key: wire_key(ProvenanceRole::StrictnessContextAliasReference, 0),
            slot: slots.item_slot(&expression),
        }
    });
    let fields = strictness
        .fields()
        .iter()
        .enumerate()
        .map(|(index, field)| DescriptorFieldReference {
            key: wire_key(
                ProvenanceRole::StrictnessFieldReference,
                u32::try_from(index).expect("checked strictness field count"),
            ),
            field: ProductionFieldId::new(field.to_string())
                .expect("Rust field identifiers are valid production fields"),
        })
        .collect();
    let kind = match strictness.kind() {
        SyntaxStrictnessKind::Strict => StrictnessKind::Strict,
        SyntaxStrictnessKind::SeqStrict => StrictnessKind::SeqStrict,
    };
    Some(WireProductionAttribute::Strictness {
        key: wire_key(ProvenanceRole::StrictnessDeclaration, 0),
        kind,
        using,
        fields,
        result_sort: Box::new(WireSortReference {
            key: wire_key(ProvenanceRole::StrictnessResultSort, 0),
            target: WireTypeReference {
                slot: slots.type_slot(quote!(#facade::HostTypeKey(#key_fn))),
                authored_path: spelling,
            },
        }),
    })
}
