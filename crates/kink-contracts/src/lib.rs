//! Closed shared values for the portable K-in-K contracts.
//!
//! Diagnostics carried by these values are supplemental. Decisions are made
//! from the closed classifications, never by matching diagnostic text.

use std::fmt;
use std::path::PathBuf;

/// Stable classification for bootstrap conformance failures.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ConformanceFailureKind {
    /// A required CLI value was omitted.
    MissingInput,
    /// An unrecognized command, option, or positional value was supplied.
    UnexpectedInput,
    /// The frozen package could not be found below the repository root.
    PackageNotFound,
    /// A required package input could not be found.
    InputNotFound,
    /// An input could not be read.
    InputRead,
    /// An input is not a supported frozen envelope.
    MalformedInput,
    /// A frozen expectation and the portable implementation disagree.
    ConformanceMismatch,
}

impl ConformanceFailureKind {
    /// Returns the stable external failure code.
    #[must_use]
    pub const fn code(self) -> &'static str {
        match self {
            Self::MissingInput => "E_MISSING_INPUT",
            Self::UnexpectedInput => "E_UNEXPECTED_INPUT",
            Self::PackageNotFound => "E_PACKAGE_NOT_FOUND",
            Self::InputNotFound => "E_INPUT_NOT_FOUND",
            Self::InputRead => "E_INPUT_READ",
            Self::MalformedInput => "E_MALFORMED_INPUT",
            Self::ConformanceMismatch => "E_CONFORMANCE_MISMATCH",
        }
    }

    /// Returns the stable process exit code for this classification.
    #[must_use]
    pub const fn exit_code(self) -> u8 {
        match self {
            Self::MissingInput | Self::UnexpectedInput => 2,
            Self::PackageNotFound | Self::InputNotFound => 3,
            Self::InputRead => 4,
            Self::MalformedInput => 5,
            Self::ConformanceMismatch => 6,
        }
    }
}

/// A typed conformance failure with supplemental diagnostics.
#[derive(Debug)]
pub struct ConformanceFailure {
    kind: ConformanceFailureKind,
    path: Option<PathBuf>,
    detail: String,
}

impl ConformanceFailure {
    /// Constructs a failure without a path.
    #[must_use]
    pub fn new(kind: ConformanceFailureKind, detail: impl Into<String>) -> Self {
        Self {
            kind,
            path: None,
            detail: detail.into(),
        }
    }

    /// Attaches the path that supplied diagnostic context.
    #[must_use]
    pub fn at_path(mut self, path: impl Into<PathBuf>) -> Self {
        self.path = Some(path.into());
        self
    }

    /// Returns the closed failure classification.
    #[must_use]
    pub const fn kind(&self) -> ConformanceFailureKind {
        self.kind
    }
}

impl fmt::Display for ConformanceFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}", self.kind.code())?;
        if let Some(path) = &self.path {
            write!(formatter, " [{}]", path.display())?;
        }
        write!(formatter, ": {}", self.detail)
    }
}

impl std::error::Error for ConformanceFailure {}

/// The authority class attached to one result.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EvidenceClass {
    /// Portable contract checking, without native execution authority.
    Portable,
    /// One bundled finite vector result.
    FiniteVector,
    /// A deterministic scripted backend result.
    Scripted,
    /// Explicitly incomplete evidence.
    Incomplete,
    /// Evidence whose semantic answer is unknown.
    Unknown,
    /// Native conformance has not been proven.
    NotProven,
    /// Native evidence with a conformant production receipt.
    NativeProven,
}

/// Native capability defaults fail closed until production evidence exists.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum NativeConformance {
    /// No conformant native production evidence is attached.
    #[default]
    NotProven,
    /// Conformant native production evidence is attached.
    NativeProven,
}

/// Completeness is independent from the result's authority class.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Completeness {
    /// The declared finite input was completely considered.
    CompleteFinite,
    /// The producer declares that some relevant input was not considered.
    Incomplete,
    /// Completeness is unknown.
    Unknown,
}

/// Frozen artifact content models.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ContentModel {
    /// Exact canonical JSON bytes.
    CanonicalJson,
    /// Uninterpreted bytes identified by an opaque envelope.
    OpaqueBytes,
}

impl ContentModel {
    /// Parses the frozen spelling.
    pub fn parse(value: &str) -> Result<Self, ArtifactFailure> {
        match value {
            "canonical-json" => Ok(Self::CanonicalJson),
            "opaque-bytes" => Ok(Self::OpaqueBytes),
            _ => Err(ArtifactFailure::new(
                ArtifactFailureKind::UnsupportedForm,
                format!("unsupported content model {value}"),
            )),
        }
    }
}

/// Frozen parameter-free media types.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MediaType {
    /// `application/json`.
    ApplicationJson,
    /// `application/octet-stream`.
    ApplicationOctetStream,
}

impl MediaType {
    /// Parses the frozen lowercase spelling.
    pub fn parse(value: &str) -> Result<Self, ArtifactFailure> {
        match value {
            "application/json" => Ok(Self::ApplicationJson),
            "application/octet-stream" => Ok(Self::ApplicationOctetStream),
            _ => Err(ArtifactFailure::new(
                ArtifactFailureKind::MediaTypeMismatch,
                format!("unsupported media type {value}"),
            )),
        }
    }

    /// Returns the frozen spelling.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ApplicationJson => "application/json",
            Self::ApplicationOctetStream => "application/octet-stream",
        }
    }
}

/// Frozen artifact availability classes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ArtifactAvailability {
    /// Bytes are bundled below the reviewed repository root.
    Bundled,
    /// Bytes require the future Rust artifact store.
    ExternalRequired,
}

/// Closed resolver registry.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ResolverId {
    /// Repository resolver for bundled bytes.
    RepoV1,
    /// Future Rust artifact-store resolver.
    RustArtifactStoreV1,
}

/// A validated locator with a normalized lexical tail.
///
/// Construction is sealed so every value has passed the same lexical,
/// resolver, and availability checks used to derive storage and lock identity.
///
/// ```compile_fail
/// use kink_contracts::ArtifactLocator;
///
/// let _alias = ArtifactLocator::Artifact("a/../b".to_owned());
/// ```
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ArtifactLocator {
    scheme: ArtifactLocatorScheme,
    tail: String,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum ArtifactLocatorScheme {
    Repo,
    Artifact,
}

impl ArtifactLocator {
    /// Validates the locator/resolver/availability triple.
    pub fn parse(
        locator: &str,
        resolver: ResolverId,
        availability: ArtifactAvailability,
    ) -> Result<Self, ArtifactFailure> {
        let (scheme, tail) = locator.split_once("://").ok_or_else(|| {
            ArtifactFailure::new(
                ArtifactFailureKind::InvalidLocator,
                "locator has no registered scheme",
            )
        })?;
        validate_locator_tail(tail)?;
        match (scheme, resolver, availability) {
            ("repo", ResolverId::RepoV1, ArtifactAvailability::Bundled) => Ok(Self {
                scheme: ArtifactLocatorScheme::Repo,
                tail: tail.to_owned(),
            }),
            (
                "artifact",
                ResolverId::RustArtifactStoreV1,
                ArtifactAvailability::ExternalRequired,
            ) => Ok(Self {
                scheme: ArtifactLocatorScheme::Artifact,
                tail: tail.to_owned(),
            }),
            ("repo" | "artifact", _, _) => Err(ArtifactFailure::new(
                ArtifactFailureKind::ResolverMismatch,
                "locator, resolver, and availability do not form a registered triple",
            )),
            _ => Err(ArtifactFailure::new(
                ArtifactFailureKind::InvalidLocator,
                format!("unsupported locator scheme {scheme}"),
            )),
        }
    }

    /// Returns the normalized locator tail.
    #[must_use]
    pub fn tail(&self) -> &str {
        &self.tail
    }

    /// Reports whether this is the repository resolver form.
    #[must_use]
    pub const fn is_repo(&self) -> bool {
        matches!(self.scheme, ArtifactLocatorScheme::Repo)
    }

    /// Reports whether this is the durable artifact-store resolver form.
    #[must_use]
    pub const fn is_artifact(&self) -> bool {
        matches!(self.scheme, ArtifactLocatorScheme::Artifact)
    }

    /// Returns the complete normalized locator.
    #[must_use]
    pub fn normalized(&self) -> String {
        match self.scheme {
            ArtifactLocatorScheme::Repo => format!("repo://{}", self.tail),
            ArtifactLocatorScheme::Artifact => format!("artifact://{}", self.tail),
        }
    }
}

fn validate_locator_tail(tail: &str) -> Result<(), ArtifactFailure> {
    if tail.is_empty()
        || tail.starts_with('/')
        || !tail.is_ascii()
        || tail.bytes().any(|byte| byte.is_ascii_control())
        || tail.contains('\\')
        || tail.contains('%')
    {
        return Err(ArtifactFailure::new(
            ArtifactFailureKind::InvalidLocator,
            "locator tail is empty, absolute, non-ASCII/control, escaped, or backslashed",
        ));
    }
    if tail
        .split('/')
        .any(|component| component.is_empty() || component == "." || component == "..")
    {
        return Err(ArtifactFailure::new(
            ArtifactFailureKind::InvalidLocator,
            "locator tail contains an empty or dot component",
        ));
    }
    Ok(())
}

/// Closed artifact-ingress failure classifications.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ArtifactFailureKind {
    /// The locator is outside the closed lexical profile.
    InvalidLocator,
    /// Locator, availability, and resolver disagree.
    ResolverMismatch,
    /// The requested locator is unavailable.
    MissingArtifact,
    /// Filesystem or store I/O failed.
    Io,
    /// The resolved path escapes the repository through a symlink.
    SymlinkEscape,
    /// The resolved object is not a regular file.
    NotRegularFile,
    /// Exact byte SHA-256 differs from catalog metadata.
    ContentHashMismatch,
    /// Catalog and role-registry content models disagree.
    ContentModelMismatch,
    /// Catalog and role-registry media types disagree.
    MediaTypeMismatch,
    /// JSON is malformed or outside the restricted semantic domain.
    MalformedJson,
    /// JSON bytes are not exactly canonical.
    NonCanonicalBytes,
    /// The role is absent from the frozen registry.
    UnknownRole,
    /// A role-specific projection or embedded ID is invalid.
    SemanticDigestMismatch,
    /// The input names a v1 form that this layer does not support.
    UnsupportedForm,
    /// Two values claim one immutable key.
    Conflict,
}

/// Typed artifact failure with supplemental diagnostics.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ArtifactFailure {
    kind: ArtifactFailureKind,
    detail: String,
}

impl ArtifactFailure {
    /// Creates a typed failure.
    #[must_use]
    pub fn new(kind: ArtifactFailureKind, detail: impl Into<String>) -> Self {
        Self {
            kind,
            detail: detail.into(),
        }
    }

    /// Returns the decision-bearing classification.
    #[must_use]
    pub const fn kind(&self) -> ArtifactFailureKind {
        self.kind
    }
}

impl fmt::Display for ArtifactFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{:?}: {}", self.kind, self.detail)
    }
}

impl std::error::Error for ArtifactFailure {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn native_conformance_fails_closed() {
        assert_eq!(NativeConformance::default(), NativeConformance::NotProven);
        assert_ne!(EvidenceClass::Portable, EvidenceClass::NativeProven);
        assert_ne!(EvidenceClass::FiniteVector, EvidenceClass::Scripted);
    }

    #[test]
    fn locator_registry_rejects_nonportable_tails() {
        let invalid = [
            "repo://",
            "repo:///absolute",
            "repo://a//b",
            "repo://a/./b",
            "repo://a/../b",
            "repo://a\\b",
            "repo://a%2fb",
            "repo://café",
        ];
        for locator in invalid {
            let failure =
                ArtifactLocator::parse(locator, ResolverId::RepoV1, ArtifactAvailability::Bundled)
                    .expect_err("nonportable repo locator must reject");
            assert_eq!(failure.kind(), ArtifactFailureKind::InvalidLocator);
        }
    }

    #[test]
    fn artifact_locator_registry_rejects_alias_tails() {
        let invalid = [
            "artifact://",
            "artifact:///absolute",
            "artifact://a//b",
            "artifact://a/./b",
            "artifact://a/../b",
            "artifact://a\\b",
            "artifact://a%2fb",
        ];
        for locator in invalid {
            let failure = ArtifactLocator::parse(
                locator,
                ResolverId::RustArtifactStoreV1,
                ArtifactAvailability::ExternalRequired,
            )
            .expect_err("aliasing artifact locator must reject");
            assert_eq!(failure.kind(), ArtifactFailureKind::InvalidLocator);
        }
    }

    #[test]
    fn locator_registry_binds_resolver_and_availability() {
        let locator = ArtifactLocator::parse(
            "repo://material/value.json",
            ResolverId::RepoV1,
            ArtifactAvailability::Bundled,
        )
        .expect("registered locator triple must pass");
        assert_eq!(locator.normalized(), "repo://material/value.json");
        assert_eq!(
            ArtifactLocator::parse(
                "repo://material/value.json",
                ResolverId::RustArtifactStoreV1,
                ArtifactAvailability::ExternalRequired,
            )
            .expect_err("mismatched resolver must reject")
            .kind(),
            ArtifactFailureKind::ResolverMismatch
        );
    }
}
