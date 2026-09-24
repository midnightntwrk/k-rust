//! Production metadata, documentation, and strictness tokens shared by single productions and enum families.

use krs_syntax::{
    ProvenanceRole, StrictnessAttribute, StrictnessKind as SyntaxStrictnessKind,
    StructuredFormatFragment,
};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::spanned::Spanned;
use syn::{Attribute, Ident, Path};

use super::tokens::{call_site_path, host_sort_reference, spelling};

pub(super) fn constructor_metadata_tokens(
    facade: &Path,
    group: Option<String>,
    avoid: bool,
    format: Option<&krs_syntax::StructuredFormat>,
) -> syn::Result<Vec<TokenStream>> {
    let constructor_group_role = ProvenanceRole::ConstructorGroup;
    let constructor_avoid_role = ProvenanceRole::ConstructorAvoid;
    let constructor_format_fragment_role = ProvenanceRole::ConstructorFormatFragment;
    let constructor_format_role = ProvenanceRole::ConstructorFormat;
    let mut attributes = Vec::new();
    if let Some(group) = group {
        attributes.push(quote! {
            #facade::HostProductionAttribute::Group {
                reference: #facade::DescriptorGroupReference {
                    key: #facade::ProvenanceKey::new(#constructor_group_role, 0)
                        .expect("KRS parser roles are nonempty"),
                    group: #facade::ProductionGroupId::new(#group)
                        .expect("checked production groups are valid identities"),
                },
            }
        });
    }
    if avoid {
        attributes.push(quote! {
            #facade::HostProductionAttribute::Avoid {
                key: #facade::ProvenanceKey::new(#constructor_avoid_role, 0)
                    .expect("KRS parser roles are nonempty"),
            }
        });
    }
    if let Some(format) = format {
        let mut fragments = Vec::new();
        for (index, fragment) in format.fragments().iter().enumerate() {
            let ordinal = u32::try_from(index).map_err(|_| {
                syn::Error::new(format.literal().span(), "too many format fragments")
            })?;
            let fragment = match fragment {
                StructuredFormatFragment::Literal(text) => {
                    quote!(#facade::FormatFragment::Literal(#text.to_owned()))
                }
                StructuredFormatFragment::Item(position) => {
                    quote!(#facade::FormatFragment::Item(#position))
                }
                StructuredFormatFragment::Newline => {
                    quote!(#facade::FormatFragment::Newline)
                }
                StructuredFormatFragment::Indent => {
                    quote!(#facade::FormatFragment::Indent)
                }
                StructuredFormatFragment::Dedent => {
                    quote!(#facade::FormatFragment::Dedent)
                }
            };
            fragments.push(quote! {
                #facade::DescriptorFormatFragment {
                    key: #facade::ProvenanceKey::new(
                        #constructor_format_fragment_role,
                        #ordinal,
                    )
                    .expect("KRS parser roles are nonempty"),
                    fragment: #fragment,
                }
            });
        }
        attributes.push(quote! {
            #facade::HostProductionAttribute::Format {
                key: #facade::ProvenanceKey::new(#constructor_format_role, 0)
                    .expect("KRS parser roles are nonempty"),
                fragments: ::std::vec![#(#fragments),*],
            }
        });
    }
    Ok(attributes)
}

pub(super) fn production_documentation_tokens(
    facade: &Path,
    documentation: &[krs_syntax::ProductionDocumentation],
) -> syn::Result<Vec<TokenStream>> {
    let constructor_documentation_role = ProvenanceRole::ConstructorDocumentation;
    documentation
        .iter()
        .enumerate()
        .map(|(ordinal, documentation)| {
            let ordinal = u32::try_from(ordinal).map_err(|_| {
                syn::Error::new(documentation.literal().span(), "too many rustdoc lines")
            })?;
            let text = documentation.text();
            Ok(quote! {
                #facade::HostProductionAttribute::Documentation {
                    key: #facade::ProvenanceKey::new(#constructor_documentation_role, #ordinal)
                        .expect("KRS parser roles are nonempty"),
                    text: #text.to_owned(),
                }
            })
        })
        .collect()
}

pub(super) fn strictness_tokens<'a>(
    facade: &Path,
    strictness: Option<&StrictnessAttribute>,
    fields: impl IntoIterator<Item = &'a Ident>,
    nonce: u64,
    cfg: &[Attribute],
) -> syn::Result<(TokenStream, Option<TokenStream>)> {
    let strictness_context_alias_reference_role = ProvenanceRole::StrictnessContextAliasReference;
    let strictness_field_reference_role = ProvenanceRole::StrictnessFieldReference;
    let strictness_declaration_role = ProvenanceRole::StrictnessDeclaration;
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
                key: #facade::ProvenanceKey::new(#strictness_context_alias_reference_role, 0)
                    .expect("KRS parser roles are nonempty"),
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
                key: #facade::ProvenanceKey::new(#strictness_field_reference_role, #ordinal)
                    .expect("KRS parser roles are nonempty"),
                field: #facade::ProductionFieldId::new(#name)
                    .expect("Rust field identifiers are valid production fields"),
            }
        });
    }
    let attribute = quote! {
        #facade::HostProductionAttribute::Strictness {
            key: #facade::ProvenanceKey::new(#strictness_declaration_role, 0)
                .expect("KRS parser roles are nonempty"),
            kind: #kind,
            using: #using,
            fields: ::std::vec![#(#selected),*],
            result_sort: ::std::boxed::Box::new(#result_sort),
        }
    };
    Ok((key_function, Some(attribute)))
}
