//! Host descriptor factories and their registration calls.

use proc_macro2::TokenStream;
use quote::quote;
use syn::{Ident, Path};

pub(super) struct DescriptorFactory<'a> {
    pub facade: &'a Path,
    pub factory: &'a Ident,
    pub name: TokenStream,
    pub item_kind: TokenStream,
    pub disambiguator: TokenStream,
    pub identity_label: &'static str,
    pub declared_type: TokenStream,
    pub payload: FactoryPayload,
    pub cfg: TokenStream,
    pub attributes: TokenStream,
    pub provenance: TokenStream,
    pub prelude: TokenStream,
}

impl DescriptorFactory<'_> {
    /// Renders the factory function followed by its registration.
    pub fn render(&self) -> TokenStream {
        let factory_tokens = self.render_unregistered();
        let Self {
            facade,
            factory,
            attributes,
            ..
        } = self;
        quote! {
            #factory_tokens

            #attributes
            #facade::__register_host_descriptor!(#factory);
        }
    }

    /// Renders only the factory function, for a caller that lists it in a table instead of registering it.
    pub fn render_unregistered(&self) -> TokenStream {
        let Self {
            facade,
            factory,
            name,
            item_kind,
            disambiguator,
            identity_label,
            declared_type,
            payload,
            cfg,
            attributes,
            provenance,
            prelude,
        } = self;
        let payload = payload.render(facade);
        quote! {
            #attributes
            #[doc(hidden)]
            fn #factory() -> ::core::result::Result<#facade::HostDescriptor, #facade::HostProvenanceError> {
                #prelude
                ::core::result::Result::Ok(#facade::HostDescriptor {
                    protocol_version: #facade::SchemaVersion::CURRENT,
                    id: #facade::HostItemId::from_macro_context(
                        env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"),
                        env!("CARGO_MANIFEST_DIR"), module_path!(), #name,
                        #item_kind, #disambiguator,
                    ).expect(#identity_label),
                    declared_type: #declared_type,
                    payload: #payload,
                    cfg: #cfg,
                    provenance: #provenance,
                })
            }
        }
    }
}

/// A factory emits static wire data with Rust-resolved references.
pub(super) enum FactoryPayload {
    Wire { json: String, slots: TokenStream },
    FixedConfiguration { json: String, slots: TokenStream },
}

impl FactoryPayload {
    pub(super) fn wire(json: String, slots: TokenStream) -> Self {
        Self::Wire { json, slots }
    }

    pub(super) fn fixed_configuration(json: String, slots: TokenStream) -> Self {
        Self::FixedConfiguration { json, slots }
    }

    fn render(&self, facade: &Path) -> TokenStream {
        match self {
            Self::Wire { json, slots } => quote!(#facade::__krs_host_payload(#json, #slots)),
            Self::FixedConfiguration { json, slots } => quote! {
                (#slots).__krs_fixed_configuration(#json, initializer, initializer_slots)
            },
        }
    }
}
