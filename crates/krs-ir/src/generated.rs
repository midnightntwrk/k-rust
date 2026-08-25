//! Stable identities for semantic declarations synthesized by the compiler.
//!
//! This module owns the derivation. Emitters and native adapters consume the
//! resulting [`StableItemId`] and must not independently name token or bracket
//! productions.

use std::error::Error;
use std::fmt;

use crate::{IdentityError, ItemKind, StableItemId};

/// The semantic-production domain synthesized from a grammar descriptor.
///
/// A kind is part of the identity, so a token and a bracket declared by the
/// same grammar item cannot collide.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum GeneratedProductionKind {
    /// A regex token production.
    Token,
    /// A syntax-only bracket production.
    Bracket,
}

impl GeneratedProductionKind {
    const fn domain_tag(self) -> &'static str {
        match self {
            Self::Token => "token",
            Self::Bracket => "bracket",
        }
    }
}

/// Failure to derive a compiler-owned semantic-production identity.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum GeneratedProductionIdError {
    /// The source was not a grammar descriptor identity.
    ExpectedGrammarDescriptor {
        /// Kind supplied by the caller.
        actual: ItemKind,
    },
    /// Construction violated a stable-identity invariant.
    InvalidDerivedIdentity(IdentityError),
}

impl fmt::Display for GeneratedProductionIdError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ExpectedGrammarDescriptor { actual } => write!(
                formatter,
                "generated production source must be a grammar descriptor, not {actual:?}"
            ),
            Self::InvalidDerivedIdentity(error) => {
                write!(formatter, "invalid generated production identity: {error}")
            }
        }
    }
}

impl Error for GeneratedProductionIdError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::ExpectedGrammarDescriptor { .. } => None,
            Self::InvalidDerivedIdentity(error) => Some(error),
        }
    }
}

/// Derives the sole stable identity for a compiler-owned token or bracket
/// production.
///
/// The derivation is injective over a validated grammar descriptor identity
/// and [`GeneratedProductionKind`]: it preserves the package and module,
/// places the result in the constructor namespace, and encodes the source item
/// name and disambiguator as hexadecimal UTF-8 under a versioned domain tag.
/// Lengths and punctuation in source components therefore cannot create an
/// ambiguous concatenation. The generated item name and disambiguator prefix
/// are reserved for this compiler-owned use.
///
/// This deliberately does not depend on descriptor contents, source paths,
/// collection order, or adapter choice. Changing this recipe is a stable-IR
/// compatibility change.
///
/// # Errors
///
/// Returns [`GeneratedProductionIdError::ExpectedGrammarDescriptor`] unless
/// `grammar_descriptor` belongs to [`ItemKind::Grammar`]. The derived
/// components are valid by construction; an invariant failure is returned as
/// [`GeneratedProductionIdError::InvalidDerivedIdentity`].
pub fn generated_production_id(
    grammar_descriptor: &StableItemId,
    kind: GeneratedProductionKind,
) -> Result<StableItemId, GeneratedProductionIdError> {
    if grammar_descriptor.item_kind() != ItemKind::Grammar {
        return Err(GeneratedProductionIdError::ExpectedGrammarDescriptor {
            actual: grammar_descriptor.item_kind(),
        });
    }

    let disambiguator = format!(
        "krs-generated-production-v1:{}:{}:{}",
        kind.domain_tag(),
        hex_encode(grammar_descriptor.item_name()),
        hex_encode(grammar_descriptor.disambiguator())
    );

    StableItemId::new(
        grammar_descriptor.package().clone(),
        grammar_descriptor.module_path().iter().cloned(),
        "__krs_generated_semantic_production",
        ItemKind::Constructor,
        disambiguator,
    )
    .map_err(GeneratedProductionIdError::InvalidDerivedIdentity)
}

fn hex_encode(value: &str) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut encoded = String::with_capacity(value.len() * 2);
    for byte in value.bytes() {
        encoded.push(char::from(HEX[usize::from(byte >> 4)]));
        encoded.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    encoded
}
