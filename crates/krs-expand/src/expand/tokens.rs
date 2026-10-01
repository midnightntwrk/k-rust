//! Token helpers shared by every entry point.

use crate::ExpandError;
use krs_diagnostic::codes::expand;
use krs_syntax::{KSequence, MapExpression, ProvenanceRole, TermLiteral};
use proc_macro2::{Span, TokenStream};
use quote::{ToTokens, format_ident, quote};
use syn::parse::Parser;
use syn::spanned::Spanned;
use syn::{Attribute, Ident, Meta, Path};

pub(super) fn sequence_has_role(sequence: &KSequence, role: ProvenanceRole) -> crate::Result<bool> {
    sequence
        .provenance()
        .map(|anchors| anchors.iter().any(|anchor| anchor.role() == role))
        .map_err(ExpandError::from)
}

pub(super) fn map_has_role(map: &MapExpression, role: ProvenanceRole) -> crate::Result<bool> {
    map.provenance()
        .map(|anchors| anchors.iter().any(|anchor| anchor.role() == role))
        .map_err(ExpandError::from)
}

pub(super) fn wire_literal(literal: &TermLiteral) -> krs_ir::DescriptorLiteral {
    match literal {
        TermLiteral::Integer(value) => {
            krs_ir::DescriptorLiteral::Int(value.base10_digits().replace('_', ""))
        }
        TermLiteral::Boolean(value) => krs_ir::DescriptorLiteral::Bool(value.value),
    }
}

pub(super) fn take_counter(counter: &mut u32) -> crate::Result<u32> {
    let value = *counter;
    *counter = counter.checked_add(1).ok_or_else(|| {
        ExpandError::new(
            expand::DESCRIPTOR_CAPACITY,
            Span::call_site(),
            "too many term nodes",
        )
    })?;
    Ok(value)
}

pub(super) fn sort_type_tokens(path: &Path, dynamic: bool) -> TokenStream {
    if dynamic {
        quote!(dyn #path)
    } else {
        quote!(#path)
    }
}

pub(super) fn is_bound_ident_path(path: &Path, bindings: &[Ident]) -> bool {
    path.leading_colon.is_none()
        && path.segments.len() == 1
        && path.segments.first().is_some_and(|segment| {
            bindings
                .iter()
                .any(|binding| binding == &segment.ident.to_string())
        })
}

pub(super) fn enum_variant_parts(path: &Path) -> Option<(Path, Ident)> {
    if path.segments.len() < 2 {
        return None;
    }
    let owner_segment = path.segments.iter().nth_back(1)?;
    if !owner_segment
        .ident
        .to_string()
        .chars()
        .next()
        .is_some_and(char::is_uppercase)
    {
        return None;
    }
    let variant = path.segments.last()?.ident.clone();
    let mut owner = path.clone();
    owner.segments.pop();
    if owner.segments.trailing_punct() {
        owner.segments.pop_punct();
    }
    Some((owner, variant))
}

pub(super) fn variant_marker_function(variant: &Ident) -> Ident {
    format_ident!("__krs_variant_type_id_{}", variant)
}

pub(super) fn helper_tokens(attribute: &Attribute, name: &str) -> crate::Result<TokenStream> {
    let Meta::List(list) = &attribute.meta else {
        return Err(ExpandError::new(
            expand::HELPER_PAYLOAD_FORM,
            attribute.span(),
            format!("`{name}` requires a parenthesized payload"),
        ));
    };
    Ok(list.tokens.clone())
}

pub(super) fn spelling(tokens: &impl ToTokens) -> String {
    tokens.to_token_stream().to_string()
}

pub(super) fn call_site_path(path: &Path) -> crate::Result<Path> {
    syn::parse_str(&path.to_token_stream().to_string()).map_err(ExpandError::from)
}

pub(super) fn call_site_ident(ident: &Ident) -> crate::Result<Ident> {
    syn::parse_str(&ident.to_string()).map_err(ExpandError::from)
}

pub(super) fn call_site_cfg_attributes(attributes: &[Attribute]) -> crate::Result<Vec<Attribute>> {
    let mut parsed = Vec::new();
    for attribute in attributes
        .iter()
        .filter(|attribute| attribute.path().is_ident("cfg"))
    {
        let mut attributes =
            Attribute::parse_outer.parse_str(&attribute.to_token_stream().to_string())?;
        if attributes.len() != 1 {
            return Err(ExpandError::new(
                expand::CFG_REPRODUCTION,
                attribute.span(),
                "KRS could not reproduce this cfg attribute",
            ));
        }
        parsed.push(attributes.remove(0));
    }
    Ok(parsed)
}
