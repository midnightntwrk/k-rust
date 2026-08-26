//! Contracts shared by the target-neutral semantic and Definition IRs.

use std::error::Error;
use std::fmt;

use serde::{Deserialize, Deserializer, Serialize};

use crate::OriginStack;

/// Version of the semantic and Definition IR schemas.
///
/// This is deliberately independent of [`crate::ProtocolVersion`]. Changing
/// collector transport does not change lowering meaning, and changing lowering
/// meaning does not require adding a descriptor protocol variant. Schema v1
/// was the M2-only model: declared-only production/variable sorts, unclassified
/// syntax strings, and declared-only applications. Schema v2 added typed
/// builtin sorts and applications plus classified M3 object grammar. Schema v3
/// adds structured fixed configurations, cell-framed rewrites, K-sequence
/// matching, and typed Map terms. No compatibility reader reinterprets older
/// data as newer meaning. Schema v4 adds typed rule conditions. Schema v5 adds
/// functional-production totality, explicit equation priorities, and
/// reversible static alias productions and clauses.
/// Schema v6 adds M3D context, simplification, and claims. Schema v7 extends
/// the closed builtin-operation catalog with object-language Boolean
/// conjunction. Schema v8 carries exact Rust declaration visibility and
/// explicit stable-symbol identity on semantic sorts and productions. Schema
/// v9 carries constructor-production documentation through Semantic and
/// Definition IR for canonical K source emission. Schema v10 adds K's builtin
/// `Bytes` sort and its selected operation identities. Schema v11 adds K's
/// builtin associative `List` sort and selected operations.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(transparent)]
pub struct IrSchemaVersion(pub u32);

impl IrSchemaVersion {
    /// Schema written by this release.
    /// Schema v11 adds the selected builtin associative `List` surface.
    pub const CURRENT: Self = Self(11);
}

impl Default for IrSchemaVersion {
    fn default() -> Self {
        Self::CURRENT
    }
}

/// Frontend-neutral identities for K sorts supplied by the K language rather
/// than declared as generated KRS symbols.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BuiltinSort {
    /// Sort of an ordered K computation sequence (`K` in source K).
    KSequence,
    /// Arbitrary-precision integer domain from pinned module `INT`.
    Int,
    /// Boolean domain from pinned module `BOOL`.
    Bool,
    /// Finite map collection from pinned module `MAP`.
    Map,
    /// Identifier token domain from pinned module `ID-SYNTAX`.
    Id,
    /// Byte-string domain from pinned module `BYTES`.
    Bytes,
    /// Associative finite sequence domain from pinned module `LIST`.
    List,
}

impl BuiltinSort {
    /// Complete IR catalog in stable semantic order.
    pub const ALL: [Self; 7] = [
        Self::KSequence,
        Self::Int,
        Self::Bool,
        Self::Map,
        Self::Id,
        Self::Bytes,
        Self::List,
    ];

    /// Sort catalog frozen into descriptor protocol v6.
    ///
    /// Map and Id enter IR schema v3 without changing the already-frozen
    /// collector transport.
    pub const PROTOCOL_V6: [Self; 3] = [Self::KSequence, Self::Int, Self::Bool];

    /// Complete sort catalog required by descriptor protocol v7.
    pub(crate) const PROTOCOL_V7: [Self; 7] = Self::ALL;
}

/// Stable, path-free key used by source-map sidecars.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(transparent)]
pub struct SourceMapKey(String);

impl SourceMapKey {
    /// Creates a nonempty source-map key.
    ///
    /// # Errors
    ///
    /// Returns [`IrIdentityError`] for blank or path-shaped input.
    pub fn new(value: impl Into<String>) -> Result<Self, IrIdentityError> {
        validated_id("source_map_key", value.into()).map(Self)
    }

    /// Returns the stable key.
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl<'de> Deserialize<'de> for SourceMapKey {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Self::new(String::deserialize(deserializer)?).map_err(serde::de::Error::custom)
    }
}

/// Stable target-neutral module identity.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(transparent)]
pub struct ModuleId(String);

impl ModuleId {
    /// Creates a nonempty path-free module identity.
    ///
    /// # Errors
    ///
    /// Returns [`IrIdentityError`] for blank or path-shaped input.
    pub fn new(value: impl Into<String>) -> Result<Self, IrIdentityError> {
        validated_id("module_id", value.into()).map(Self)
    }

    /// Returns the identity.
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl<'de> Deserialize<'de> for ModuleId {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Self::new(String::deserialize(deserializer)?).map_err(serde::de::Error::custom)
    }
}

/// Stable semantic-only identity for configuration objects and variables.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(transparent)]
pub struct SemanticId(String);

impl SemanticId {
    /// Creates a nonempty path-free semantic identity.
    ///
    /// # Errors
    ///
    /// Returns [`IrIdentityError`] for blank or path-shaped input.
    pub fn new(value: impl Into<String>) -> Result<Self, IrIdentityError> {
        validated_id("semantic_id", value.into()).map(Self)
    }

    /// Returns the identity.
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl<'de> Deserialize<'de> for SemanticId {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Self::new(String::deserialize(deserializer)?).map_err(serde::de::Error::custom)
    }
}

/// Provenance attached to every IR sentence and nested term.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NodeOrigin {
    key: SourceMapKey,
    origin: OriginStack,
}

impl NodeOrigin {
    /// Associates one stable source-map key with an honest origin stack.
    #[must_use]
    pub const fn new(key: SourceMapKey, origin: OriginStack) -> Self {
        Self { key, origin }
    }

    /// Returns the source-map key.
    #[must_use]
    pub const fn key(&self) -> &SourceMapKey {
        &self.key
    }

    /// Returns the authored-to-IR origin stack.
    #[must_use]
    pub const fn origin(&self) -> &OriginStack {
        &self.origin
    }
}

/// Invalid stable IR identity.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum IrIdentityError {
    /// An identity was empty or whitespace-only.
    Empty(&'static str),
    /// An identity contained a filesystem separator.
    PathLike(&'static str, String),
}

impl fmt::Display for IrIdentityError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Empty(kind) => write!(formatter, "{kind} must not be empty"),
            Self::PathLike(kind, value) => {
                write!(formatter, "{kind} must be path-free, found {value:?}")
            }
        }
    }
}

impl Error for IrIdentityError {}

pub(crate) fn validated_id(kind: &'static str, value: String) -> Result<String, IrIdentityError> {
    if value.trim().is_empty() {
        return Err(IrIdentityError::Empty(kind));
    }
    if value.contains(['/', '\\']) {
        return Err(IrIdentityError::PathLike(kind, value));
    }
    Ok(value)
}
