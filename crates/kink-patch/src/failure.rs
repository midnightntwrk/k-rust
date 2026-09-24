//! Patch failure classes.

use std::fmt;

/// Closed transaction failure classifications.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PatchFailureKind {
    /// A target, content, module, or attribute precondition is stale.
    StalePrecondition,
    /// An edit would leave its target unchanged.
    NoChange,
    /// A typed path does not resolve in the immutable baseline.
    MalformedPath,
    /// Two edits name the same target region or insertion slot.
    DuplicateTarget,
    /// Edits name ancestor/descendant or destructive anchor regions.
    OverlappingEdit,
    /// Sort, scope, signature, sentence, or output invariants fail.
    LocallyIllFormed,
}

impl PatchFailureKind {
    /// Returns the failure spelling.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::StalePrecondition => "stale-precondition",
            Self::NoChange => "no-change",
            Self::MalformedPath => "malformed-path",
            Self::DuplicateTarget => "duplicate-target",
            Self::OverlappingEdit => "overlapping-edit",
            Self::LocallyIllFormed => "locally-ill-formed",
        }
    }
}

/// Atomic patch failure. It deliberately carries no partial output or identity.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PatchFailure {
    kind: PatchFailureKind,
    detail: String,
}

impl PatchFailure {
    pub(crate) fn new(kind: PatchFailureKind, detail: impl Into<String>) -> Self {
        Self {
            kind,
            detail: detail.into(),
        }
    }

    /// Returns the decision-bearing classification.
    #[must_use]
    pub const fn kind(&self) -> PatchFailureKind {
        self.kind
    }

    /// Failed transactions always publish zero applied edits.
    #[must_use]
    pub const fn applied_edit_count(&self) -> usize {
        0
    }
}

impl fmt::Display for PatchFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}: {}", self.kind.as_str(), self.detail)
    }
}

impl std::error::Error for PatchFailure {}
