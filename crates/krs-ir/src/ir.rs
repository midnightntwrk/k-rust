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

macro_rules! reserved_encodings {
    ($marker:literal) => {
        /// Marker reserved for generated semantic identifiers.
        pub const RESERVED_MARKER: &str = $marker;
        const WILDCARD_PREFIX: &str = concat!($marker, "wildcard_");
        const ANONYMOUS_SEPARATOR: &str = RESERVED_MARKER;
    };
}

reserved_encodings!("__krs_");

/// The reserved encoding recognized in a semantic identity.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SemanticIdKind<'a> {
    /// An identity beginning with the reserved wildcard prefix.
    Wildcard,
    /// An underscore-prefixed name followed by a decimal occurrence ordinal.
    Anonymous {
        /// The name before the final reserved separator.
        name: &'a str,
    },
    /// An identity without a recognized reserved encoding.
    Named,
}

impl SemanticId {
    /// Creates a nonempty path-free semantic identity.
    ///
    /// # Errors
    ///
    /// Returns [`IrIdentityError`] for blank or path-shaped input.
    pub fn new(value: impl Into<String>) -> Result<Self, IrIdentityError> {
        validated_id(crate::IrIdentityKind::SemanticId, value.into()).map(Self)
    }

    /// Creates an authored semantic identity without generated encodings.
    ///
    /// # Errors
    ///
    /// Returns [`IrIdentityError`] for reserved-marker, blank, or path-shaped input.
    pub fn authored(value: impl Into<String>) -> Result<Self, IrIdentityError> {
        let value = value.into();
        if value.contains(RESERVED_MARKER) {
            return Err(IrIdentityError::ReservedMarker(value));
        }
        Self::new(value)
    }

    /// Creates a wildcard occurrence with the reserved spelling.
    #[must_use]
    pub fn wildcard(ordinal: usize) -> Self {
        Self(format!("{WILDCARD_PREFIX}{ordinal}"))
    }

    /// Appends the reserved occurrence suffix to an anonymous spelling.
    ///
    /// Recognition requires an underscore-prefixed spelling longer than one byte.
    ///
    /// # Errors
    ///
    /// Returns [`IrIdentityError`] when the resulting identity is path-shaped.
    pub fn anonymous(spelling: &str, ordinal: usize) -> Result<Self, IrIdentityError> {
        Self::new(format!("{spelling}{ANONYMOUS_SEPARATOR}{ordinal}"))
    }

    /// Classifies the reserved encoding.
    ///
    /// An identity that carries both encodings is a wildcard.
    #[must_use]
    pub fn kind(&self) -> SemanticIdKind<'_> {
        if self.0.starts_with(WILDCARD_PREFIX) {
            return SemanticIdKind::Wildcard;
        }
        self.0
            .rsplit_once(ANONYMOUS_SEPARATOR)
            .filter(|(name, ordinal)| {
                name.starts_with('_')
                    && name.len() > 1
                    && !ordinal.is_empty()
                    && ordinal.bytes().all(|byte| byte.is_ascii_digit())
            })
            .map_or(SemanticIdKind::Named, |(name, _)| {
                SemanticIdKind::Anonymous { name }
            })
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
    /// An authored semantic identity contained the generated-identity marker.
    ReservedMarker(String),
}

impl fmt::Display for IrIdentityError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Empty(kind) => write!(formatter, "{kind} must not be empty"),
            Self::PathLike(kind, value) => {
                write!(formatter, "{kind} must be path-free, found {value:?}")
            }
            Self::ReservedMarker(value) => write!(
                formatter,
                "marker `{RESERVED_MARKER}` is reserved for generated identifiers, found {value:?}"
            ),
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn authored_semantic_ids_reject_reserved_marker() {
        for spelling in ["__krs_wildcard_1", "_x__krs_3", "a__krs_b"] {
            assert_eq!(
                SemanticId::authored(spelling),
                Err(IrIdentityError::ReservedMarker(spelling.into()))
            );
        }
        for spelling in ["x", "_x", "__x"] {
            assert_eq!(SemanticId::authored(spelling), SemanticId::new(spelling));
        }
        for spelling in ["", " ", "a/b", "a\\b"] {
            assert_eq!(SemanticId::authored(spelling), SemanticId::new(spelling));
        }
    }

    #[test]
    fn reserved_semantic_constructors_round_trip() {
        let wildcard = SemanticId::wildcard(12);
        assert_eq!(wildcard.as_str(), "__krs_wildcard_12");
        assert_eq!(wildcard.kind(), SemanticIdKind::Wildcard);
        let anonymous = SemanticId::anonymous("_B", 34).unwrap();
        assert_eq!(anonymous.as_str(), "_B__krs_34");
        assert_eq!(anonymous.kind(), SemanticIdKind::Anonymous { name: "_B" });
        assert!(SemanticId::anonymous("_a/b", 0).is_err());
        assert!(SemanticId::anonymous("_a\\b", 0).is_err());
    }

    #[test]
    fn semantic_kind_preserves_reserved_predicate_edges() {
        for spelling in ["__krs_wildcard_", "__krs_wildcard_text", "__krs_wildcard_١"] {
            assert_eq!(
                SemanticId::new(spelling).unwrap().kind(),
                SemanticIdKind::Wildcard
            );
        }
        for (spelling, name) in [
            ("_B__krs_0", "_B"),
            ("_B__krs_000", "_B"),
            ("_é__krs_9", "_é"),
            ("_B__krs_1__krs_2", "_B__krs_1"),
        ] {
            let id = SemanticId::new(spelling).unwrap();
            assert_eq!(id.kind(), SemanticIdKind::Anonymous { name }, "{spelling}");
        }
        for spelling in [
            "B",
            "_B",
            "_",
            "B__krs_0",
            "__krs_0",
            "___krs_0",
            "_B__krs_",
            "_B__krs_-1",
            "_B__krs_1x",
            "_B__krs_١",
            "_B__krs_1__krs_",
            "__krs_wildcard",
        ] {
            assert_eq!(
                SemanticId::new(spelling).unwrap().kind(),
                SemanticIdKind::Named,
                "{spelling}"
            );
        }
        let overlap = SemanticId::new("__krs_wildcard_text__krs_0").unwrap();
        assert_eq!(overlap.kind(), SemanticIdKind::Wildcard);
    }
}
