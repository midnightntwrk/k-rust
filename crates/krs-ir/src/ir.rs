//! Contracts shared by the target-neutral semantic and Definition IRs.

use std::error::Error;
use std::fmt;

use serde::{Deserialize, Deserializer, Serialize};

use crate::OriginStack;

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
        validated_id(crate::IrIdentityKind::SourceMapKey, value.into()).map(Self)
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
        validated_id(crate::IrIdentityKind::ModuleId, value.into()).map(Self)
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
        validated_id(crate::IrIdentityKind::SemanticId, value.into()).map(Self)
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
    Empty(crate::IrIdentityKind),
    /// An identity contained a filesystem separator.
    PathLike(crate::IrIdentityKind, String),
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

pub(crate) fn validated_id(
    kind: crate::IrIdentityKind,
    value: String,
) -> Result<String, IrIdentityError> {
    if value.trim().is_empty() {
        return Err(IrIdentityError::Empty(kind));
    }
    if value.contains(['/', '\\']) {
        return Err(IrIdentityError::PathLike(kind, value));
    }
    Ok(value)
}
