//! Production metadata, documentation, and strictness tokens shared by single productions and enum families.

use crate::ExpandError;
use krs_diagnostic::codes::expand;
use krs_syntax::{
    StrictnessAttribute, StrictnessKind as SyntaxStrictnessKind, StructuredFormatFragment,
};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::spanned::Spanned;
use syn::{Attribute, Ident, Path};

use super::ledger::KeyLedger;
use super::tokens::{call_site_path, enum_variant_parts, spelling, variant_marker_function};
use krs_ir::ProvenanceKey;
/// The production roles a constructor's descriptor repeats from its grammar descriptor.
pub(super) use krs_ir::transport::grammar::REPEATED_PRODUCTION_ROLES;

pub(super) fn strictness_key_function<'a>(
    strictness: Option<&StrictnessAttribute>,
    fields: impl IntoIterator<Item = &'a Ident>,
    nonce: u64,
    cfg: &[Attribute],
) -> crate::Result<TokenStream> {
    let Some(strictness) = strictness else {
        return Ok(TokenStream::new());
    };
    let available = fields
        .into_iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>();
    let key_fn = format_ident!("__krs_strictness_result_{nonce:016x}");
    let path = call_site_path(strictness.result_sort())?;
    let result_type = quote!(#path);
    if strictness.using().is_some()
        && strictness
            .result_sort()
            .segments
            .last()
            .is_none_or(|segment| segment.ident != "KResult")
    {
        return Err(ExpandError::new(
            expand::CONTEXT_ALIAS_RESULT_SORT,
            strictness.result_sort().span(),
            "a named context alias currently requires the unambiguous `KResult` result sort",
        ));
    }
    for (index, field) in strictness.fields().iter().enumerate() {
        let name = field.to_string();
        if !available.iter().any(|available| available == &name) {
            return Err(ExpandError::new(
                expand::UNDECLARED_STRICTNESS_FIELD,
                field.span(),
                "strictness field is not declared",
            ));
        }
        u32::try_from(index).map_err(|_| {
            ExpandError::new(
                expand::DESCRIPTOR_CAPACITY,
                field.span(),
                "too many strictness fields",
            )
        })?;
    }
    Ok(quote! {
        #(#cfg)*
        #[doc(hidden)]
        fn #key_fn() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#result_type>()
        }
    })
}

/// Rejects an `internal` or `program` flag on a production whose Rust item is
/// not `pub`: a non-pub production is already private to the package's rules.
pub(super) fn check_placement_visibility(
    placement: Option<(krs_syntax::PlacementFlag, &Ident)>,
    visibility: &syn::Visibility,
) -> crate::Result<()> {
    if let Some((flag, key)) = placement
        && !matches!(visibility, syn::Visibility::Public(_))
    {
        return Err(ExpandError::new(
            expand::INVALID_PLACEMENT_FLAG,
            key.span(),
            format!(
                "`{}` applies only to a `pub` production; non-pub productions are already private",
                flag.as_str()
            ),
        ));
    }
    Ok(())
}

/// The expansion of one `overload = Path` key.
pub(super) struct OverloadWire {
    /// The target's type-key function and a rustc-checked pattern use of the
    /// target, so rustc reports an unknown or private target (E0433, E0603)
    /// at the authored path and rust-analyzer navigates from it.
    pub(super) tokens: TokenStream,
    /// The `overload` production attribute.
    pub(super) attribute: krs_ir::wire::WireProductionAttribute,
}

/// Expands the target of `overload = Path`: an enum variant `Enum::Variant`
/// or a constructor struct.
pub(super) fn overload_wire(
    (facade, ledger): (&Path, &KeyLedger<'_>),
    target: &Path,
    read: Option<&ProvenanceKey>,
    key_fn: &Ident,
    cfg: &[Attribute],
    slots: &mut super::terms::WireSlots,
) -> crate::Result<OverloadWire> {
    // The owner keeps the authored spans, so rustc reports an unknown or
    // private target at the path the author wrote.
    let (owner, variant) = enum_variant_parts(target).map_or_else(
        || (target.clone(), None),
        |(owner, variant)| (owner, Some(variant)),
    );
    let owner_key = quote!(#facade::HostTypeKey(#key_fn));
    let slot = if let Some(variant) = &variant {
        let marker = variant_marker_function(variant);
        slots.variant_slot_for_grammar(&owner_key, &quote!(#facade::HostTypeKey(#owner::#marker)))
    } else {
        slots.nominal_target_slot(&owner_key)
    };
    let tokens = quote! {
        #(#cfg)*
        #[doc(hidden)]
        fn #key_fn() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#owner>()
        }

        #(#cfg)*
        #[doc(hidden)]
        #[allow(irrefutable_let_patterns)]
        const _: () = {
            let _ = |value| if let #target { .. } = value {};
        };
    };
    Ok(OverloadWire {
        tokens,
        attribute: krs_ir::wire::WireProductionAttribute::Overload {
            target: krs_ir::wire::WireApplicationReference {
                key: ledger.define(read)?,
                target: slot,
                authored_path: spelling(target),
            },
        },
    })
}

/// A production's `color` literal or `colors` literals.
pub(super) struct ColorMetadata<'a> {
    pub(super) color: Option<&'a syn::LitStr>,
    pub(super) colors: Option<&'a [syn::LitStr]>,
}

#[expect(
    clippy::too_many_arguments,
    reason = "A production's metadata values and their keys come from its attribute or its family."
)]
pub(super) fn constructor_metadata_wire(
    ledger: &KeyLedger<'_>,
    keys: &krs_syntax::ProductionKeys,
    (group, group_key): (Option<String>, Option<&ProvenanceKey>),
    avoid: bool,
    prefer: bool,
    placement: Option<krs_syntax::PlacementFlag>,
    overload: Option<krs_ir::wire::WireProductionAttribute>,
    colors: &ColorMetadata<'_>,
    format: Option<&krs_syntax::StructuredFormat>,
) -> crate::Result<Vec<krs_ir::wire::WireProductionAttribute>> {
    use krs_ir::wire::WireProductionAttribute as Attribute;
    use krs_ir::{
        DescriptorFormatFragment, DescriptorGroupReference, FormatFragment, ProductionGroupId,
    };
    let mut attributes = Vec::new();
    if let Some(group) = group {
        attributes.push(Attribute::Group {
            reference: DescriptorGroupReference {
                key: ledger.define(group_key)?,
                group: ProductionGroupId::new(group)
                    .expect("checked production groups are valid identities"),
            },
        });
    }
    if avoid {
        attributes.push(Attribute::Avoid {
            key: ledger.define(keys.avoid())?,
        });
    }
    if prefer {
        attributes.push(Attribute::Prefer {
            key: ledger.define(keys.prefer())?,
        });
    }
    match placement {
        Some(krs_syntax::PlacementFlag::Internal) => attributes.push(Attribute::Internal {
            key: ledger.define(keys.placement())?,
        }),
        Some(krs_syntax::PlacementFlag::Program) => attributes.push(Attribute::Program {
            key: ledger.define(keys.placement())?,
        }),
        None => {}
    }
    attributes.extend(overload);
    if let Some(color) = colors.color {
        attributes.push(Attribute::Color {
            key: ledger.define(keys.color())?,
            value: color.value(),
        });
    }
    if let Some(literals) = colors.colors {
        let mut values = Vec::with_capacity(literals.len());
        for (index, literal) in literals.iter().enumerate() {
            values.push(krs_ir::DescriptorColorEntry {
                key: ledger.define(keys.color_entries().get(index))?,
                value: literal.value(),
            });
        }
        attributes.push(Attribute::Colors {
            key: ledger.define(keys.color())?,
            values,
        });
    }
    if let Some(format) = format {
        let mut fragments = Vec::new();
        for (index, fragment) in format.fragments().iter().enumerate() {
            let fragment = match fragment {
                StructuredFormatFragment::Literal(text) => FormatFragment::Literal(text.to_owned()),
                StructuredFormatFragment::Item(position) => FormatFragment::Item(*position),
                StructuredFormatFragment::Newline => FormatFragment::Newline,
                StructuredFormatFragment::Indent => FormatFragment::Indent,
                StructuredFormatFragment::Dedent => FormatFragment::Dedent,
                StructuredFormatFragment::ColorNext => FormatFragment::ColorNext,
                StructuredFormatFragment::ColorReset => FormatFragment::ColorReset,
            };
            fragments.push(DescriptorFormatFragment {
                key: ledger.define(format.fragment_keys().get(index))?,
                fragment,
            });
        }
        attributes.push(Attribute::Format {
            key: ledger.define(keys.format())?,
            fragments,
        });
    }
    Ok(attributes)
}

pub(super) fn production_documentation_wire(
    ledger: &KeyLedger<'_>,
    documentation: &[krs_syntax::ProductionDocumentation],
) -> crate::Result<Vec<krs_ir::wire::WireProductionAttribute>> {
    documentation
        .iter()
        .map(|documentation| {
            Ok(krs_ir::wire::WireProductionAttribute::Documentation {
                key: ledger.define(documentation.key())?,
                text: documentation.text().to_owned(),
            })
        })
        .collect()
}

/// The production attribute of a `#[k::alias]` or `#[k::desugar]` marker
/// (KF-028), keyed `read`, the marker's name, with the `recursive`
/// keyword's key when written.
pub(super) fn static_mode_wire(
    ledger: &KeyLedger<'_>,
    marker: &krs_syntax::StaticProductionAttribute,
    read: Option<&ProvenanceKey>,
) -> crate::Result<krs_ir::wire::WireProductionAttribute> {
    let recursive = marker
        .is_recursive()
        .then(|| ledger.define(marker.recursive_key()))
        .transpose()?;
    Ok(match marker.mode() {
        krs_syntax::StaticMode::Alias => krs_ir::wire::WireProductionAttribute::Alias {
            key: ledger.define(read)?,
            recursive,
        },
        krs_syntax::StaticMode::Desugar => krs_ir::wire::WireProductionAttribute::Desugar {
            key: ledger.define(read)?,
            recursive,
        },
    })
}

pub(super) fn strictness_wire(
    (facade, ledger): (&Path, &KeyLedger<'_>),
    strictness: Option<&StrictnessAttribute>,
    nonce: u64,
    slots: &mut super::terms::WireSlots,
) -> crate::Result<Option<krs_ir::wire::WireProductionAttribute>> {
    use krs_ir::wire::{
        WireContextAliasReference, WireProductionAttribute, WireSortReference, WireTypeReference,
    };
    use krs_ir::{DescriptorFieldReference, ProductionFieldId, StrictnessKind};
    let Some(strictness) = strictness else {
        return Ok(None);
    };
    let key_fn = format_ident!("__krs_strictness_result_{nonce:016x}");
    let spelling = spelling(strictness.result_sort());
    let using = strictness
        .using()
        .map(|alias| -> crate::Result<_> {
            let name = alias.to_string();
            let expression = quote!(#facade::HostItemId::from_macro_context(
            env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"), env!("CARGO_MANIFEST_DIR"),
            module_path!(), #name, #facade::ItemKind::ContextAlias, "",
        ).expect("a strictness context alias forms a valid host identity"));
            Ok(WireContextAliasReference {
                key: ledger.define(strictness.using_key())?,
                slot: slots.item_slot(&expression),
            })
        })
        .transpose()?;
    let fields = strictness
        .fields()
        .iter()
        .enumerate()
        .map(|(index, field)| -> crate::Result<_> {
            Ok(DescriptorFieldReference {
                key: ledger.define(strictness.field_keys().get(index))?,
                field: ProductionFieldId::new(field.to_string())
                    .expect("Rust field identifiers are valid production fields"),
            })
        })
        .collect::<crate::Result<_>>()?;
    let kind = match strictness.kind() {
        SyntaxStrictnessKind::Strict => StrictnessKind::Strict,
        SyntaxStrictnessKind::SeqStrict => StrictnessKind::SeqStrict,
    };
    Ok(Some(WireProductionAttribute::Strictness {
        key: ledger.define(strictness.key())?,
        kind,
        using,
        fields,
        result_sort: Box::new(WireSortReference {
            key: ledger.define(strictness.result_sort_key())?,
            target: WireTypeReference {
                slot: slots.type_slot(quote!(#facade::HostTypeKey(#key_fn))),
                authored_path: spelling,
            },
        }),
    }))
}
