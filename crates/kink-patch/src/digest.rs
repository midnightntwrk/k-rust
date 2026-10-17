//! SHA-256 identities for exact bytes and domain-separated payloads.

use crate::stack::{OPTIMIZED, StackRefusal, with_stack};
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

/// The deepest JSON document kink reads, in nested arrays and objects as serde_json counts them:
/// 128,000 in an unoptimized build (kink's `dev` and test profile) and 600,000 in an optimized
/// one (re-pin L1-3-fix-2). [`parse_json`] refuses a deeper document with
/// [`JsonError::TooDeep`] before it parses any of it, and each writer of a document a kink reader
/// reads refuses to write one ([`check_json_depth`]: the patch codec, kink-campaign's report,
/// kink-corpus `Store::write_json`, through which kink-corpus and kink-flow write every stored
/// document), so each reader accepts what its writer writes.
///
/// The limit is set by the one recursion over a document that kink does not size: serde_json
/// drops a `Value`, and compares and copies one, by recursion on the caller's stack. Dropping a
/// document of nested objects, the costliest shape measured (L1-3-fix-2 probe), takes 943 bytes
/// per level unoptimized and 209 bytes optimized, so a document at the limit takes 115 MiB and
/// 120 MiB: under half of the 256 MiB that kink's commands run on (kink-corpus
/// `DEFINITION_STACK_BYTES`), which library callers that read or write documents this deep need
/// too. Parsing and serializing take more per level (up to 2.4 KiB unoptimized), but run on a
/// stack sized from the document's depth ([`crate::stack`]). KAST and KORE JSON nest two levels
/// per term level, so the limit holds terms about 64,000 levels deep unoptimized and 300,000
/// optimized. Every document within serde_json's former limit of 128 is read exactly as
/// `serde_json::from_str` read it.
pub const MAX_JSON_DEPTH: usize = if OPTIMIZED { 600_000 } else { 128_000 };

/// Upper bound on the native stack that serde_json's parse and serialization of a document
/// take per level of nesting. Measured by the pages they touched on a fresh segment, over
/// nested arrays, nested objects, objects of four members and KAST JSON 20,000 levels deep: at
/// most 2,411 bytes (parsing objects of four members) unoptimized and 628 bytes optimized. The
/// bound is about twice each.
const JSON_STACK_PER_LEVEL: usize = if OPTIMIZED { 1280 } else { 5 * 1024 };

/// A JSON document kink does not read.
#[derive(Debug)]
pub enum JsonError {
    /// The document nests `depth` levels deep, more than [`MAX_JSON_DEPTH`] (`limit`).
    TooDeep { depth: usize, limit: usize },
    /// The system refused the stack segment the document's depth needs.
    Stack(StackRefusal),
    /// The text is not one JSON document (serde_json's error).
    Syntax(serde_json::Error),
}

impl fmt::Display for JsonError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TooDeep { depth, limit } => write!(
                formatter,
                "the JSON nests {depth} levels deep, more than kink's limit of {limit} \
                 (kink-patch MAX_JSON_DEPTH)"
            ),
            Self::Stack(refusal) => write!(formatter, "{refusal}"),
            Self::Syntax(error) => write!(formatter, "{error}"),
        }
    }
}

impl std::error::Error for JsonError {}

/// The nesting depth of the JSON text `text`: the most arrays and objects open at once outside
/// strings, counted without recursion. For a JSON document it is the depth serde_json counts;
/// for other text it is at least the depth serde_json reaches before it stops at the first
/// error, so a refusal by this depth never lets a parse go deeper.
#[must_use]
pub fn json_depth(text: &str) -> usize {
    let (mut depth, mut deepest) = (0_usize, 0_usize);
    let (mut in_string, mut escaped) = (false, false);
    for byte in text.bytes() {
        if in_string {
            match (escaped, byte) {
                (true, _) => escaped = false,
                (false, b'\\') => escaped = true,
                (false, b'"') => in_string = false,
                (false, _) => {}
            }
            continue;
        }
        match byte {
            b'"' => in_string = true,
            b'[' | b'{' => {
                depth += 1;
                deepest = deepest.max(depth);
            }
            b']' | b'}' => depth = depth.saturating_sub(1),
            _ => {}
        }
    }
    deepest
}

/// The nesting depth of `value` (a scalar is 0, an empty array or object 1), counted without
/// recursion.
#[must_use]
pub fn value_depth(value: &serde_json::Value) -> usize {
    use serde_json::Value;
    let mut deepest = 0;
    let mut pending = vec![(value, 0)];
    while let Some((value, depth)) = pending.pop() {
        match value {
            Value::Array(items) => {
                deepest = deepest.max(depth + 1);
                pending.extend(items.iter().map(|item| (item, depth + 1)));
            }
            Value::Object(members) => {
                deepest = deepest.max(depth + 1);
                pending.extend(members.values().map(|member| (member, depth + 1)));
            }
            Value::Null | Value::Bool(_) | Value::Number(_) | Value::String(_) => {}
        }
    }
    deepest
}

/// Refuses a document deeper than [`MAX_JSON_DEPTH`], which no kink reader reads: every writer of
/// such a document checks it before writing, so a reader accepts what its writer writes.
///
/// # Errors
/// Returns [`JsonError::TooDeep`] with the document's depth.
pub fn check_json_depth(value: &serde_json::Value) -> Result<(), JsonError> {
    let depth = value_depth(value);
    if depth > MAX_JSON_DEPTH {
        return Err(JsonError::TooDeep {
            depth,
            limit: MAX_JSON_DEPTH,
        });
    }
    Ok(())
}

/// Compact JSON with sorted object keys (serde_json without preserve_order), serialized on a
/// stack sized from the value's depth ([`crate::stack`]), so a document of any depth kink reads
/// serializes on any thread. Beyond the largest stack segment kink maps, or when the system
/// refuses it, it serializes on the calling thread's stack, as before re-pin L1-3-fix-2.
pub fn canonical_json(value: &serde_json::Value) -> String {
    let serialize = || serde_json::to_string(value).expect("JSON values encode");
    with_stack(value_depth(value), JSON_STACK_PER_LEVEL, serialize).unwrap_or_else(|_| serialize())
}

/// Parses one JSON document, as `serde_json::from_str` does, but with kink's limit of
/// [`MAX_JSON_DEPTH`] nested arrays and objects in place of serde_json's limit of 128 (re-pin
/// L1-3-fix-1, L1-3-fix-2), on a stack sized from the document's depth.
///
/// kink's own JSON (a canonical patch, a campaign report, k-rust's KAST JSON of an edited term
/// or sentence, a KORE test input) nests as deep as the terms it holds: KAST and KORE JSON take
/// two levels per term level, so serde_json's limit refused every mutation of a rule more than
/// about 55 terms deep as invalid, a valid mutation hidden from the score by an implementation
/// limit (review L1-3-1). The depth is counted first, without recursion ([`json_depth`]); a
/// deeper document is refused before any of it is parsed, and the parse runs on the calling
/// thread when its remaining stack covers the depth and on a segment of that size otherwise, so
/// the outcome does not depend on the thread (review L1-3-2 D3). The returned value is dropped
/// on the caller's stack (see [`MAX_JSON_DEPTH`]). Every document within serde_json's limit
/// parses to the same value, so no encoding, digest or key changes.
///
/// Every reader of kink's own JSON goes through it: kink-patch's patch codec (encode and
/// decode) and operator specs; kink-campaign's report (the KAST JSON it embeds) and replay;
/// kink-corpus's store (`Store::read_json`: campaign reports, admission records, the index),
/// its corpus manifest and its KORE test inputs (admission and rebuild); kink-flow's run report,
/// outcome records, results records and hints. k-rust's own readers (KAST and KORE JSON,
/// semantic-input provenance JSON) are k-rust's, unbounded and stack-safe.
///
/// # Errors
/// Returns [`JsonError::TooDeep`] for a document deeper than [`MAX_JSON_DEPTH`],
/// [`JsonError::Stack`] when the system refuses the segment its depth needs, and serde_json's
/// error for text that is not one JSON document.
pub fn parse_json(text: &str) -> Result<serde_json::Value, JsonError> {
    let depth = json_depth(text);
    if depth > MAX_JSON_DEPTH {
        return Err(JsonError::TooDeep {
            depth,
            limit: MAX_JSON_DEPTH,
        });
    }
    let parse = || {
        let mut deserializer = serde_json::Deserializer::from_str(text);
        deserializer.disable_recursion_limit();
        let value = serde::Deserialize::deserialize(&mut deserializer)?;
        deserializer.end()?;
        Ok(value)
    };
    with_stack(depth, JSON_STACK_PER_LEVEL, parse)
        .map_err(JsonError::Stack)?
        .map_err(JsonError::Syntax)
}

/// Runs `work`, which parses, builds, serializes and drops documents at most `levels` deep, on a
/// stack that holds them all, drops included; for the patch codec, whose documents are its own to
/// drop.
pub(crate) fn with_document_stack<T>(
    levels: usize,
    work: impl FnOnce() -> T,
) -> Result<T, StackRefusal> {
    with_stack(levels, JSON_STACK_PER_LEVEL, work)
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
