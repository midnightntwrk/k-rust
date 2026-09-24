use std::error::Error;
use std::fmt;

/// Broad category of a host-collection failure.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum CollectionErrorKind {
    /// Caller-supplied package metadata was invalid.
    InvalidPackageContext,
    /// A host path could not be canonicalized or read.
    HostIo,
    /// More than one context claimed the same host package lookup key.
    DuplicatePackageContext,
    /// More than one package claimed the same immutable K namespace.
    DuplicateKNamespace,
    /// A descriptor carried a schema version other than the current one.
    UnsupportedSchemaVersion,
    /// The compiler-provided builtin marker catalog was incomplete or ambiguous.
    InvalidBuiltinRegistry,
    /// No selected Cargo package matched a descriptor's host lookup key.
    PackageNotSelected,
    /// The first `module_path!()` segment did not match the selected target.
    CrateRootMismatch,
    /// A host item could not become a stable item identity.
    InvalidStableIdentity,
    /// Two declarations produced the same final stable identity.
    DuplicateItemId,
    /// A descriptor payload did not agree with its declared item kind.
    ItemKindMismatch,
    /// Two declarations exposed the same build-local Rust `TypeId`.
    DuplicateTypeDeclaration,
    /// A Rust identity was assigned to both an authored declaration and a builtin.
    DeclarationBuiltinCollision,
    /// A sort or constructor declaration exposed no build-local Rust `TypeId`.
    MissingTypeDeclaration,
    /// A Rust type reference had no declaration in the selected collection.
    UnresolvedTypeReference,
    /// A resolved declaration had the wrong semantic item kind.
    ReferenceKindMismatch,
    /// A fixed configuration, cell, or configuration rule descriptor was malformed.
    InvalidConfiguration,
    /// A display filename was not a normalized relative source hint.
    InvalidDisplayFile,
    /// A resolved source escaped its canonical package directory.
    SourceOutsidePackage,
    /// A display hint resolved to multiple distinct files in the package.
    AmbiguousSourcePath,
    /// A line or Unicode-scalar column was outside the exact source revision.
    SourcePositionOutOfBounds,
    /// A semantic node used an invocation-fallback rather than exact leaves.
    ImpreciseAuthoredAnchor,
    /// The exact source no longer parses under the shared KRS parser.
    SourceSyntax,
    /// An authored attribute is named like a KRS attribute entry point but
    /// does not invoke it under the package's facade alias.
    UnresolvedAttribute,
    /// A host anchor did not match the corresponding reparsed semantic node.
    StaleAnchor,
    /// More than one reparsed invocation matched a host descriptor.
    AmbiguousAnchor,
    /// The macro and shared parser disagreed about the complete anchor set.
    ProvenanceMismatch,
}

/// Typed host-collection diagnostic with a stable category and human detail.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CollectionError {
    kind: CollectionErrorKind,
    detail: String,
}

impl CollectionError {
    pub(crate) fn new(kind: CollectionErrorKind, detail: impl Into<String>) -> Self {
        Self {
            kind,
            detail: detail.into(),
        }
    }

    /// Returns the machine-comparable diagnostic category.
    #[must_use]
    pub const fn kind(&self) -> CollectionErrorKind {
        self.kind
    }

    /// Returns the contextual diagnostic detail.
    #[must_use]
    pub fn detail(&self) -> &str {
        &self.detail
    }
}

impl fmt::Display for CollectionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.detail)
    }
}

impl Error for CollectionError {}

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
