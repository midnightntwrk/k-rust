use std::error::Error;
use std::fmt;

/// Broad category of an open-sort analysis failure.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum AnalysisErrorKind {
    /// Two serialized declarations used the same stable identity.
    DuplicateItemId,
    /// A sort or constructor referenced an absent declaration.
    UnresolvedReference,
    /// A sort or constructor referenced the wrong declaration namespace.
    ReferenceKindMismatch,
    /// The direct subsort relation contained a cycle.
    SortCycle,
}

/// Typed semantic-analysis diagnostic.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AnalysisError {
    kind: AnalysisErrorKind,
    detail: String,
}

impl AnalysisError {
    pub(crate) fn new(kind: AnalysisErrorKind, detail: impl Into<String>) -> Self {
        Self {
            kind,
            detail: detail.into(),
        }
    }

    /// Returns the machine-comparable diagnostic category.
    #[must_use]
    pub const fn kind(&self) -> AnalysisErrorKind {
        self.kind
    }

    /// Returns the contextual diagnostic detail.
    #[must_use]
    pub fn detail(&self) -> &str {
        &self.detail
    }
}

impl fmt::Display for AnalysisError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.detail)
    }
}

impl Error for AnalysisError {}
