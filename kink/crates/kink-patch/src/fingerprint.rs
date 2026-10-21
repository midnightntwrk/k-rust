//! Metadata-insensitive sentence versions, distinct from sentence identity.

use crate::{Sha256Digest, payload_digest};
use k_rust::definition::{AttributeKey, Attributes, Definition, FlatModule, Sentence};
use std::{fmt, sync::Arc};

pub const FINGERPRINT_DOMAIN: &str = "kink/sentence-fingerprint/v1";

/// Position and provenance keys excluded from the version payload.
pub const POSITION_KEYS: [AttributeKey; 10] = [
    AttributeKey::Location,
    AttributeKey::Source,
    AttributeKey::SourceId,
    AttributeKey::SentenceStartOffset,
    AttributeKey::SentenceEndOffset,
    AttributeKey::ContentStartLine,
    AttributeKey::ContentStartColumn,
    AttributeKey::ContentStartOffset,
    AttributeKey::Origin,
    AttributeKey::InputAddresses,
];

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FingerprintError {
    ContextAlias,
    Encode(String),
}

impl fmt::Display for FingerprintError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ContextAlias => formatter.write_str("context aliases have no v1 fingerprint"),
            Self::Encode(detail) => write!(formatter, "sentence encoding failed: {detail}"),
        }
    }
}

impl std::error::Error for FingerprintError {}

/// Encodes the position-free sentence in an otherwise empty KAST definition.
///
/// # Errors
///
/// Refuses context aliases and propagates encoding errors.
pub fn fingerprint_payload(sentence: &Sentence) -> Result<String, FingerprintError> {
    if matches!(sentence, Sentence::ContextAlias { .. }) {
        return Err(FingerprintError::ContextAlias);
    }
    let mut sentence = sentence.clone();
    for key in POSITION_KEYS {
        sentence.attributes_mut().remove(key.as_str());
    }
    let definition = Definition {
        main_module: String::new(),
        modules: vec![FlatModule {
            name: String::new(),
            imports: Vec::new(),
            local_sentences: vec![Arc::new(sentence)],
            attributes: Attributes::default(),
        }],
        attributes: Attributes::default(),
    };
    k_rust::definition::json::to_string(&definition)
        .map_err(|error| FingerprintError::Encode(error.to_string()))
}

/// A sentence version; equal versions need not identify the same sentence.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SentenceFingerprint(Sha256Digest);

impl SentenceFingerprint {
    /// # Errors
    ///
    /// Refuses sentences without a v1 payload.
    pub fn of(sentence: &Sentence) -> Result<Self, FingerprintError> {
        Ok(Self(payload_digest(
            FINGERPRINT_DOMAIN,
            fingerprint_payload(sentence)?.as_bytes(),
        )))
    }

    #[must_use]
    pub fn parse(text: &str) -> Option<Self> {
        Sha256Digest::parse(text).map(Self)
    }
}

impl fmt::Display for SentenceFingerprint {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(formatter)
    }
}
