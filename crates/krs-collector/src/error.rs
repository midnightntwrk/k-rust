use std::error::Error;
use std::fmt;

use krs_diagnostic::{Diagnostic, Location, ToDiagnostic, codes};
use krs_ir::{ByteRange, ProvenanceKey, SourceFileId, SourceRange};

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
    /// A display or resolved source file escaped its Cargo package directory.
    SourceOutsidePackage,
    /// A display hint resolved to multiple distinct files in the package.
    AmbiguousSourcePath,
    /// A line or Unicode-scalar column was outside the exact source revision.
    SourcePositionOutOfBounds,
    /// A semantic node used an invocation-fallback rather than exact leaves.
    ImpreciseAuthoredAnchor,
    /// The exact source no longer parses under the shared KRS parser.
    SourceSyntax,
    /// An authored attribute or item macro names a KRS entry point but does
    /// not invoke it under the package's facade alias.
    UnresolvedAttribute,
    /// A facade attribute annotates a macro instead of the item it names.
    FacadeAttributeOnMacro,
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
    source_range: Option<Box<SourceRange>>,
    input_range: Option<ByteRange>,
    reference_key: Option<ProvenanceKey>,
}

impl CollectionError {
    pub(crate) fn new(kind: CollectionErrorKind, detail: impl Into<String>) -> Self {
        Self {
            kind,
            detail: detail.into(),
            source_range: None,
            input_range: None,
            reference_key: None,
        }
    }

    pub(crate) fn with_source_range(mut self, range: SourceRange) -> Self {
        self.source_range = Some(Box::new(range));
        self
    }

    pub(crate) fn with_span(self, span: proc_macro2::Span) -> Self {
        match krs_diagnostic::span_byte_range(span) {
            Some(range) => self.with_input_range(range),
            None => self,
        }
    }

    pub(crate) fn with_provenance(self, provenance: &krs_ir::DescriptorProvenance) -> Self {
        let range = self
            .reference_key
            .as_ref()
            .and_then(|key| provenance.origin_for(key))
            .unwrap_or_else(|| provenance.primary_origin())
            .exact_authored_range();
        match range {
            Some(range) => self.with_source_range(range),
            None => self,
        }
    }

    pub(crate) fn with_input_range(mut self, range: ByteRange) -> Self {
        self.input_range = Some(range);
        self
    }

    pub(crate) fn with_reference_key(mut self, key: ProvenanceKey) -> Self {
        self.reference_key = Some(key);
        self
    }

    pub(crate) fn with_source_file(mut self, file: &SourceFileId) -> Self {
        if let Some(range) = self.input_range {
            self.source_range = SourceRange::from_byte_range(file.clone(), range)
                .ok()
                .map(Box::new);
        }
        self
    }

    /// Returns the exact authored location when the producer has one.
    #[must_use]
    pub fn source_range(&self) -> Option<&SourceRange> {
        self.source_range.as_deref()
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

impl ToDiagnostic for CollectionError {
    fn to_diagnostic(&self) -> Diagnostic {
        let code = match self.kind {
            CollectionErrorKind::InvalidPackageContext => codes::collect::INVALID_PACKAGE_CONTEXT,
            CollectionErrorKind::HostIo => codes::collect::HOST_IO,
            CollectionErrorKind::DuplicatePackageContext => {
                codes::collect::DUPLICATE_PACKAGE_CONTEXT
            }
            CollectionErrorKind::DuplicateKNamespace => codes::collect::DUPLICATE_KNAMESPACE,
            CollectionErrorKind::UnsupportedSchemaVersion => {
                codes::collect::UNSUPPORTED_SCHEMA_VERSION
            }
            CollectionErrorKind::InvalidBuiltinRegistry => codes::collect::INVALID_BUILTIN_REGISTRY,
            CollectionErrorKind::PackageNotSelected => codes::collect::PACKAGE_NOT_SELECTED,
            CollectionErrorKind::CrateRootMismatch => codes::collect::CRATE_ROOT_MISMATCH,
            CollectionErrorKind::InvalidStableIdentity => codes::collect::INVALID_STABLE_IDENTITY,
            CollectionErrorKind::DuplicateItemId => codes::collect::DUPLICATE_ITEM_ID,
            CollectionErrorKind::ItemKindMismatch => codes::collect::ITEM_KIND_MISMATCH,
            CollectionErrorKind::DuplicateTypeDeclaration => {
                codes::collect::DUPLICATE_TYPE_DECLARATION
            }
            CollectionErrorKind::DeclarationBuiltinCollision => {
                codes::collect::DECLARATION_BUILTIN_COLLISION
            }
            CollectionErrorKind::MissingTypeDeclaration => codes::collect::MISSING_TYPE_DECLARATION,
            CollectionErrorKind::UnresolvedTypeReference => {
                codes::collect::UNRESOLVED_TYPE_REFERENCE
            }
            CollectionErrorKind::ReferenceKindMismatch => codes::collect::REFERENCE_KIND_MISMATCH,
            CollectionErrorKind::InvalidConfiguration => codes::collect::INVALID_CONFIGURATION,
            CollectionErrorKind::InvalidDisplayFile => codes::collect::INVALID_DISPLAY_FILE,
            CollectionErrorKind::SourceOutsidePackage => codes::collect::SOURCE_OUTSIDE_PACKAGE,
            CollectionErrorKind::AmbiguousSourcePath => codes::collect::AMBIGUOUS_SOURCE_PATH,
            CollectionErrorKind::SourcePositionOutOfBounds => {
                codes::collect::SOURCE_POSITION_OUT_OF_BOUNDS
            }
            CollectionErrorKind::ImpreciseAuthoredAnchor => {
                codes::collect::IMPRECISE_AUTHORED_ANCHOR
            }
            CollectionErrorKind::SourceSyntax => codes::collect::SOURCE_SYNTAX,
            CollectionErrorKind::UnresolvedAttribute => codes::collect::UNRESOLVED_ATTRIBUTE,
            CollectionErrorKind::FacadeAttributeOnMacro => {
                codes::collect::FACADE_ATTRIBUTE_ON_MACRO
            }
            CollectionErrorKind::StaleAnchor => codes::collect::STALE_ANCHOR,
            CollectionErrorKind::AmbiguousAnchor => codes::collect::AMBIGUOUS_ANCHOR,
            CollectionErrorKind::ProvenanceMismatch => codes::collect::PROVENANCE_MISMATCH,
        };
        Diagnostic::error(
            code,
            self.detail.clone(),
            self.source_range
                .clone()
                .map_or(Location::None, |range| Location::Source(*range)),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use krs_ir::{PackageId, Sha256Digest};

    #[test]
    fn call_site_span_does_not_establish_a_location() {
        let error = CollectionError::new(CollectionErrorKind::SourceSyntax, "syntax")
            .with_span(proc_macro2::Span::call_site());
        assert_eq!(error.input_range, None);
        assert!(matches!(
            error.to_diagnostic().primary.location,
            Location::None
        ));
    }

    #[test]
    #[expect(
        clippy::too_many_lines,
        reason = "Covers every registered collection category."
    )]
    fn located_and_unlocated_errors_preserve_detail_and_registered_codes() {
        let file = SourceFileId::new(
            PackageId::new("TEST", "test", "0.1.0", "workspace").unwrap(),
            "src/lib.rs",
            Sha256Digest::new("11".repeat(32)).unwrap(),
        )
        .unwrap();
        let range = SourceRange::new(file, 7, 16).unwrap();
        for (kind, code) in [
            (
                CollectionErrorKind::InvalidPackageContext,
                codes::collect::INVALID_PACKAGE_CONTEXT,
            ),
            (CollectionErrorKind::HostIo, codes::collect::HOST_IO),
            (
                CollectionErrorKind::DuplicatePackageContext,
                codes::collect::DUPLICATE_PACKAGE_CONTEXT,
            ),
            (
                CollectionErrorKind::DuplicateKNamespace,
                codes::collect::DUPLICATE_KNAMESPACE,
            ),
            (
                CollectionErrorKind::UnsupportedSchemaVersion,
                codes::collect::UNSUPPORTED_SCHEMA_VERSION,
            ),
            (
                CollectionErrorKind::InvalidBuiltinRegistry,
                codes::collect::INVALID_BUILTIN_REGISTRY,
            ),
            (
                CollectionErrorKind::PackageNotSelected,
                codes::collect::PACKAGE_NOT_SELECTED,
            ),
            (
                CollectionErrorKind::CrateRootMismatch,
                codes::collect::CRATE_ROOT_MISMATCH,
            ),
            (
                CollectionErrorKind::InvalidStableIdentity,
                codes::collect::INVALID_STABLE_IDENTITY,
            ),
            (
                CollectionErrorKind::DuplicateItemId,
                codes::collect::DUPLICATE_ITEM_ID,
            ),
            (
                CollectionErrorKind::ItemKindMismatch,
                codes::collect::ITEM_KIND_MISMATCH,
            ),
            (
                CollectionErrorKind::DuplicateTypeDeclaration,
                codes::collect::DUPLICATE_TYPE_DECLARATION,
            ),
            (
                CollectionErrorKind::DeclarationBuiltinCollision,
                codes::collect::DECLARATION_BUILTIN_COLLISION,
            ),
            (
                CollectionErrorKind::MissingTypeDeclaration,
                codes::collect::MISSING_TYPE_DECLARATION,
            ),
            (
                CollectionErrorKind::UnresolvedTypeReference,
                codes::collect::UNRESOLVED_TYPE_REFERENCE,
            ),
            (
                CollectionErrorKind::ReferenceKindMismatch,
                codes::collect::REFERENCE_KIND_MISMATCH,
            ),
            (
                CollectionErrorKind::InvalidConfiguration,
                codes::collect::INVALID_CONFIGURATION,
            ),
            (
                CollectionErrorKind::InvalidDisplayFile,
                codes::collect::INVALID_DISPLAY_FILE,
            ),
            (
                CollectionErrorKind::SourceOutsidePackage,
                codes::collect::SOURCE_OUTSIDE_PACKAGE,
            ),
            (
                CollectionErrorKind::AmbiguousSourcePath,
                codes::collect::AMBIGUOUS_SOURCE_PATH,
            ),
            (
                CollectionErrorKind::SourcePositionOutOfBounds,
                codes::collect::SOURCE_POSITION_OUT_OF_BOUNDS,
            ),
            (
                CollectionErrorKind::ImpreciseAuthoredAnchor,
                codes::collect::IMPRECISE_AUTHORED_ANCHOR,
            ),
            (
                CollectionErrorKind::SourceSyntax,
                codes::collect::SOURCE_SYNTAX,
            ),
            (
                CollectionErrorKind::UnresolvedAttribute,
                codes::collect::UNRESOLVED_ATTRIBUTE,
            ),
            (
                CollectionErrorKind::FacadeAttributeOnMacro,
                codes::collect::FACADE_ATTRIBUTE_ON_MACRO,
            ),
            (
                CollectionErrorKind::StaleAnchor,
                codes::collect::STALE_ANCHOR,
            ),
            (
                CollectionErrorKind::AmbiguousAnchor,
                codes::collect::AMBIGUOUS_ANCHOR,
            ),
            (
                CollectionErrorKind::ProvenanceMismatch,
                codes::collect::PROVENANCE_MISMATCH,
            ),
        ] {
            let error = CollectionError::new(kind, "detail");
            assert_eq!(error.to_string(), "detail");
            let diagnostic = error.to_diagnostic();
            assert_eq!(diagnostic.code, code);
            assert!(matches!(diagnostic.primary.location, Location::None));
            let diagnostic = error.with_source_range(range.clone()).to_diagnostic();
            assert_eq!(diagnostic.message, "detail");
            let Location::Source(actual) = diagnostic.primary.location else {
                panic!("lost location")
            };
            assert_eq!(actual, range);
        }
    }
}
