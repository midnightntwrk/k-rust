//! SHA-256 identities for exact bytes and domain-separated payloads.

use std::fmt;

/// An exact SHA-256 digest, displayed as lowercase hexadecimal.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Sha256Digest([u8; 32]);

impl Sha256Digest {
    /// Parses exactly 64 lowercase hexadecimal digits.
    #[must_use]
    pub fn parse(text: &str) -> Option<Self> {
        if text.len() != 64 {
            return None;
        }
        let mut bytes = [0; 32];
        for (out, pair) in bytes
            .iter_mut()
            .zip(text.as_bytes().as_chunks::<2>().0.iter())
        {
            let digit = |byte| match byte {
                b'0'..=b'9' => Some(byte - b'0'),
                b'a'..=b'f' => Some(byte - b'a' + 10),
                _ => None,
            };
            *out = digit(pair[0])? * 16 + digit(pair[1])?;
        }
        Some(Self(bytes))
    }

    #[must_use]
    pub const fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }
}

impl fmt::Display for Sha256Digest {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        for byte in self.0 {
            write!(formatter, "{byte:02x}")?;
        }
        Ok(())
    }
}

/// Hashes exact bytes through k-rust's public content-hash contract.
#[must_use]
pub fn sha256(bytes: &[u8]) -> Sha256Digest {
    Sha256Digest(k_rust::provenance::LogicalSourceId::new("", bytes).content_hash)
}

/// Hashes UTF-8 domain, one NUL byte, and the payload, in that order.
#[must_use]
pub fn payload_digest(domain: &str, payload: &[u8]) -> Sha256Digest {
    let mut bytes = Vec::with_capacity(domain.len() + 1 + payload.len());
    bytes.extend_from_slice(domain.as_bytes());
    bytes.push(0);
    bytes.extend_from_slice(payload);
    sha256(&bytes)
}

pub const CANONICAL_PATCH_DOMAIN: &str = "kink/canonical-patch/v1";
pub const COMPILED_KORE_DOMAIN: &str = "kink/compiled-kore/v1";
pub const TEST_MANIFEST_DOMAIN: &str = "kink/test-manifest/v1";
pub const OBSERVATION_DOMAIN: &str = "kink/observation/v1";
pub const CAMPAIGN_MANIFEST_DOMAIN: &str = "kink/campaign-manifest/v1";

/// Compact JSON with sorted object keys (serde_json without preserve_order).
pub fn canonical_json(value: &serde_json::Value) -> String {
    serde_json::to_string(value).expect("JSON values encode")
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum StructureError {
    ContextAlias,
    Encode(String),
}
impl std::fmt::Display for StructureError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::error::Error for StructureError {}

/// Hashes metadata-free KAST bytes; refuses context aliases omitted by KAST v4.
pub fn structure_sha256(
    definition: &k_rust::definition::Definition,
) -> Result<Sha256Digest, StructureError> {
    if definition
        .modules
        .iter()
        .flat_map(|m| &m.local_sentences)
        .any(|s| matches!(**s, k_rust::definition::Sentence::ContextAlias { .. }))
    {
        return Err(StructureError::ContextAlias);
    }
    let text = k_rust::definition::json::to_string(definition)
        .map_err(|e| StructureError::Encode(e.to_string()))?;
    Ok(sha256(text.as_bytes()))
}
