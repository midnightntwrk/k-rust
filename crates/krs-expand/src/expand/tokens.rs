//! Token helpers shared by every entry point.

use krs_syntax::{KSequence, KSequenceNotation, MapExpression, ProvenanceRole, TermLiteral};
use proc_macro2::{Span, TokenStream};
use quote::{ToTokens, format_ident, quote};
use syn::parse::Parser;
use syn::spanned::Spanned;
use syn::{Attribute, Ident, Meta, Path};

pub(super) fn option_key(facade: &Path, role: ProvenanceRole, ordinal: u32) -> TokenStream {
    let key = provenance_key(facade, role, ordinal);
    quote!(::core::option::Option::Some(#key))
}

pub(super) fn sequence_has_role(sequence: &KSequence, role: ProvenanceRole) -> syn::Result<bool> {
    sequence
        .provenance()
        .map(|anchors| anchors.iter().any(|anchor| anchor.role() == role))
        .map_err(krs_syntax::SyntaxError::into_syn_error)
}

pub(super) fn map_has_role(map: &MapExpression, role: ProvenanceRole) -> syn::Result<bool> {
    map.provenance()
        .map(|anchors| anchors.iter().any(|anchor| anchor.role() == role))
        .map_err(krs_syntax::SyntaxError::into_syn_error)
}

pub(super) fn k_notation(facade: &Path, notation: KSequenceNotation) -> TokenStream {
    match notation {
        KSequenceNotation::Comma => quote!(#facade::DescriptorKSequenceNotation::Comma),
        KSequenceNotation::Operator => quote!(#facade::DescriptorKSequenceNotation::Operator),
        KSequenceNotation::DotK => quote!(#facade::DescriptorKSequenceNotation::DotK),
    }
}

pub(super) fn literal_tokens(facade: &Path, literal: &TermLiteral) -> TokenStream {
    match literal {
        TermLiteral::Integer(value) => {
            let value = value.base10_digits().replace('_', "");
            quote!(#facade::DescriptorLiteral::Int(#value.to_owned()))
        }
        TermLiteral::Boolean(value) => {
            let value = value.value;
            quote!(#facade::DescriptorLiteral::Bool(#value))
        }
    }
}

pub(super) fn bytes_token_value(literal: &syn::LitByteStr) -> String {
    use std::fmt::Write as _;

    let mut value = String::from("b\"");
    for byte in literal.value() {
        write!(&mut value, "\\x{byte:02x}").expect("writing to a String cannot fail");
    }
    value.push('"');
    value
}

pub(super) fn take_counter(counter: &mut u32) -> syn::Result<u32> {
    let value = *counter;
    *counter = counter
        .checked_add(1)
        .ok_or_else(|| syn::Error::new(Span::call_site(), "too many term nodes"))?;
    Ok(value)
}

pub(super) fn provenance_key(facade: &Path, role: ProvenanceRole, ordinal: u32) -> TokenStream {
    quote! {
        #facade::ProvenanceKey::new(#role, #ordinal)
            .expect("KRS parser roles are nonempty")
    }
}

pub(super) fn host_sort_reference(
    facade: &Path,
    role: ProvenanceRole,
    ordinal: u32,
    key_function: &Ident,
    authored_path: &str,
) -> TokenStream {
    let key = provenance_key(facade, role, ordinal);
    quote! {
        #facade::HostSortReference {
            key: #key,
            target: #facade::HostTypeReference {
                key: #facade::HostTypeKey(#key_function),
                authored_path: #authored_path.to_owned(),
            },
        }
    }
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

pub(super) fn helper_tokens(attribute: &Attribute, name: &str) -> syn::Result<TokenStream> {
    let Meta::List(list) = &attribute.meta else {
        return Err(syn::Error::new(
            attribute.span(),
            format!("`{name}` requires a parenthesized payload"),
        ));
    };
    Ok(list.tokens.clone())
}

pub(super) fn type_reference(
    facade: &Path,
    key_function: &Ident,
    authored_path: &str,
) -> TokenStream {
    quote! {
        #facade::HostTypeReference {
            key: #facade::HostTypeKey(#key_function),
            authored_path: #authored_path.to_owned(),
        }
    }
}

pub(super) fn option_owned_string(value: Option<String>) -> TokenStream {
    if let Some(value) = value {
        quote!(::core::option::Option::Some(#value.to_owned()))
    } else {
        quote!(::core::option::Option::None)
    }
}

pub(super) fn spelling(tokens: &impl ToTokens) -> String {
    tokens.to_token_stream().to_string()
}

pub(super) fn call_site_path(path: &Path) -> syn::Result<Path> {
    syn::parse_str(&path.to_token_stream().to_string())
}

pub(super) fn call_site_ident(ident: &Ident) -> syn::Result<Ident> {
    syn::parse_str(&ident.to_string())
}

pub(super) fn call_site_cfg_attributes(attributes: &[Attribute]) -> syn::Result<Vec<Attribute>> {
    let mut parsed = Vec::new();
    for attribute in attributes
        .iter()
        .filter(|attribute| attribute.path().is_ident("cfg"))
    {
        let mut attributes =
            Attribute::parse_outer.parse_str(&attribute.to_token_stream().to_string())?;
        if attributes.len() != 1 {
            return Err(syn::Error::new(
                attribute.span(),
                "KRS could not reproduce this cfg attribute",
            ));
        }
        parsed.push(attributes.remove(0));
    }
    Ok(parsed)
}

#[cfg(test)]
mod tests {
    use super::bytes_token_value;

    #[test]
    fn byte_string_transport_is_canonical_lower_hex() {
        let literal = syn::parse_str::<syn::LitByteStr>(r#"b"\x00A\xff""#).unwrap();
        assert_eq!(bytes_token_value(&literal), r#"b"\x00\x41\xff""#);
    }
}
