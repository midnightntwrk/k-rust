use krs_ir::ProvenanceKey;
use proc_macro2::TokenStream;

use crate::TokenRange;

pub use krs_ir::{ProvenanceRole, RuleRole, RuleSide};

/// Emits a facade-qualified role variant for generated collector code.
#[must_use]
pub fn role_tokens(role: ProvenanceRole, facade: &syn::Path) -> TokenStream {
    let variant = syn::Ident::new(role.variant_ident(), proc_macro2::Span::call_site());
    quote::quote!(#facade::ProvenanceRole::#variant)
}

/// One canonical semantic key paired with its authored token endpoints.
#[derive(Clone, Debug)]
pub struct ProvenanceAnchor {
    role: ProvenanceRole,
    ordinal: u32,
    range: TokenRange,
}

impl ProvenanceAnchor {
    /// Creates an anchor from a parser-owned role, occurrence, and range.
    #[must_use]
    pub const fn new(role: ProvenanceRole, ordinal: u32, range: TokenRange) -> Self {
        Self {
            role,
            ordinal,
            range,
        }
    }

    /// Returns the parser-owned role.
    #[must_use]
    pub const fn role(&self) -> ProvenanceRole {
        self.role
    }

    /// Returns the zero-based role occurrence.
    #[must_use]
    pub const fn ordinal(&self) -> u32 {
        self.ordinal
    }

    /// Returns the exact token endpoints.
    #[must_use]
    pub const fn range(&self) -> TokenRange {
        self.range
    }

    /// Returns the IR key a producer and reparser must use for this node.
    #[must_use]
    pub const fn key(&self) -> ProvenanceKey {
        self.role.key(self.ordinal)
    }
}
