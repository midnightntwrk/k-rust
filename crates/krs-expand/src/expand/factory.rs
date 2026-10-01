//! Host descriptor factories and their registration calls.

use proc_macro2::TokenStream;
use quote::quote;
use syn::{Ident, Path};

pub(super) enum IdentityCheck {
    Expect(&'static str),
    Unwrap,
}

pub(super) struct DescriptorFactory<'a> {
    pub facade: &'a Path,
    pub factory: &'a Ident,
    pub name: TokenStream,
    pub item_kind: TokenStream,
    pub disambiguator: TokenStream,
    pub identity_check: IdentityCheck,
    pub declared_type: TokenStream,
    pub payload: TokenStream,
    pub cfg: TokenStream,
    pub attributes: TokenStream,
    pub provenance: TokenStream,
    pub prelude: TokenStream,
}

impl DescriptorFactory<'_> {
    pub fn render(&self) -> TokenStream {
        let Self {
            facade,
            factory,
            name,
            item_kind,
            disambiguator,
            identity_check,
            declared_type,
            payload,
            cfg,
            attributes,
            provenance,
            prelude,
        } = self;
        let (last_argument, check) = match identity_check {
            IdentityCheck::Expect(label) => (quote!(#disambiguator,), quote!(.expect(#label))),
            // The claim factory omits the trailing argument comma.
            IdentityCheck::Unwrap => (quote!(#disambiguator), quote!(.unwrap())),
        };
        quote! {
            #attributes
            #[doc(hidden)]
            fn #factory() -> #facade::HostDescriptor {
                #prelude
                #facade::HostDescriptor {
                    protocol_version: #facade::SchemaVersion::CURRENT,
                    id: #facade::HostItemId::from_macro_context(
                        env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"),
                        env!("CARGO_MANIFEST_DIR"), module_path!(), #name,
                        #item_kind, #last_argument
                    )#check,
                    declared_type: #declared_type,
                    payload: #payload,
                    cfg: #cfg,
                    provenance: #provenance,
                }
            }

            #attributes
            #facade::__register_host_descriptor!(#factory);
        }
    }
}
