//! Stable identities for semantic declarations synthesized by the compiler.
//!
//! This module owns the derivation. Emitters and native adapters consume the
//! resulting [`StableItemId`] and must not independently name token or bracket
//! productions.

use std::error::Error;
use std::fmt;

use crate::{IdentityError, ItemKind, StableItemId, lower_hex};

/// The semantic-production domain synthesized from a grammar descriptor.
///
/// A kind is part of the identity, so a token and a bracket declared by the
/// same grammar item cannot collide.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum GeneratedProductionKind<'a> {
    /// One token production of a token carrier, keyed by its content so that
    /// reordering stacked `#[k::token]` attributes keeps every identity.
    Token {
        /// The production's regex or terminal text.
        content: TokenProductionContent<'a>,
    },
    /// A syntax-only bracket production.
    Bracket,
}

/// The content that identifies one generated token production.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum TokenProductionContent<'a> {
    /// `#[k::token(regex = r"..")]`.
    Regex(&'a str),
    /// `#[k::token(terminal = "..")]`.
    Terminal(&'a str),
}

impl GeneratedProductionKind<'_> {
    fn domain_tag(self) -> String {
        match self {
            Self::Token {
                content: TokenProductionContent::Regex(text),
            } => format!("token:regex:{}", lower_hex(text.as_bytes())),
            Self::Token {
                content: TokenProductionContent::Terminal(text),
            } => format!("token:terminal:{}", lower_hex(text.as_bytes())),
            Self::Bracket => "bracket".to_owned(),
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
                "generated production source must be a grammar descriptor, not {actual}"
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
/// Apart from a token production's own regex or terminal text, which keys
/// it among the productions of one carrier, this deliberately does not
/// depend on descriptor contents, source paths,
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
    kind: GeneratedProductionKind<'_>,
) -> Result<StableItemId, GeneratedProductionIdError> {
    if grammar_descriptor.item_kind() != ItemKind::Grammar {
        return Err(GeneratedProductionIdError::ExpectedGrammarDescriptor {
            actual: grammar_descriptor.item_kind(),
        });
    }

    let disambiguator = format!(
        "krs-generated-production-v1:{}:{}:{}",
        kind.domain_tag(),
        lower_hex(grammar_descriptor.item_name().as_bytes()),
        lower_hex(grammar_descriptor.disambiguator().as_bytes())
    );

    StableItemId::generated_production(
        grammar_descriptor.package().clone(),
        grammar_descriptor.module_path().iter().cloned(),
        disambiguator,
    )
    .map_err(GeneratedProductionIdError::InvalidDerivedIdentity)
}

/// The stable identities of the function KRS lifts out of one `let` block or `k::matches!` of a
/// sentence that holds it where no tool lowers it: the function's production and its equations.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LocalFunctionIds {
    /// The lifted function's production.
    pub production: StableItemId,
    /// The lifted function's equation: a `let` block's only one, a `k::matches!`'s `true` one.
    pub equation: StableItemId,
    /// A `k::matches!`'s `false` equation, which applies where the `true` one does not.
    pub otherwise: StableItemId,
}

/// Derives the identities of the `index`th local function lifted out of the sentence `host`.
///
/// The derivation is injective over the host's identity and the index: it keeps the package
/// and module, places the production in the constructor namespace and the equations in the
/// equation namespace, all under the reserved generated item name (the `otherwise` equation's
/// disambiguator suffixed `:otherwise`, which no index ends with), and encodes the host's
/// namespace, item name and disambiguator as hexadecimal UTF-8 under a versioned domain tag,
/// which no token or bracket production's disambiguator carries. It depends on nothing but the
/// host's identity and the index, so a host lifted again gets the same identities. Changing this
/// recipe is a stable-IR compatibility change.
///
/// # Errors
///
/// An invariant failure of the derived identities is returned as
/// [`GeneratedProductionIdError::InvalidDerivedIdentity`].
pub fn local_function_ids(
    host: &StableItemId,
    index: usize,
) -> Result<LocalFunctionIds, GeneratedProductionIdError> {
    let disambiguator = format!(
        "krs-local-function-v1:{}:{}:{}:{index}",
        lower_hex(host.item_kind().to_string().as_bytes()),
        lower_hex(host.item_name().as_bytes()),
        lower_hex(host.disambiguator().as_bytes())
    );
    let production = StableItemId::generated_production(
        host.package().clone(),
        host.module_path().iter().cloned(),
        disambiguator.clone(),
    )
    .map_err(GeneratedProductionIdError::InvalidDerivedIdentity)?;
    let equation = |disambiguator: String| {
        StableItemId::new(
            host.package().clone(),
            host.module_path().iter().cloned(),
            production.item_name(),
            ItemKind::Equation,
            disambiguator,
        )
        .map_err(GeneratedProductionIdError::InvalidDerivedIdentity)
    };
    Ok(LocalFunctionIds {
        equation: equation(disambiguator.clone())?,
        otherwise: equation(format!("{disambiguator}:otherwise"))?,
        production,
    })
}
