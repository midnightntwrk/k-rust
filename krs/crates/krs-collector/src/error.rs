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
    /// More than one package's library has the same crate name.
    DuplicateCrateName,
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
    /// A rule at the head of the computation needs exactly one configuration, and the definition
    /// has none or several.
    ConfigurationCount,
    /// A sentence typed by a cell group whose group sits below an optional or a collection cell, so
    /// its cells have no one position.
    GroupSubjectPosition,
    /// A sentence typed by a cell group that no cell of the configuration holds.
    GroupNotInConfiguration,
    /// A sentence typed by a cell group names a cell outside the group.
    CellOutsideSubject,
    /// A claim typed by a cell group.
    GroupClaim,
    /// A `k::patterns!` block typed by a cell group, which is not supported yet (FB-49).
    GroupPattern,
    /// A rule at the head of the computation needs a computation cell in its configuration, and
    /// the configuration has no `KSequence` cell, or the record names a cell that is not one.
    ComputationCell,
    /// A configuration with several `KSequence` cells, none or more than one of which reads the
    /// program, which a rule at the head of the computation needs: the configuration's refusal.
    MainCell,
    /// Two configuration variables are read by the computation an initializer gives by
    /// brackets, which the declared kinds decide: the rule `k!` follows, at the second.
    AmbiguousMainConfigurationVariable,
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
    /// A `let` block in a field of an application whose path reads as a set's singleton and
    /// resolves to a constructor, whose field the pattern matches.
    LetInMatchedField,
    /// A `k::matches!` there.
    MatchesInMatchedField,
    /// A record update there.
    RecordUpdateInMatchedField,
    /// The collector's host declaration of a cell and its collected declaration give the cell
    /// different kinds: a collector fault.
    CellKindDisagreement,
    /// A `cells!` entry the entry-admission table refuses, with its class (design S5, §2.3).
    CellEntry(krs_syntax::cell_entries::Refusal),
    /// A constructor's record that a `cells!` value writes with `..` or `..base`
    /// (`record-remainder-in-cells-term`), told from a group record once its head resolves.
    RecordRemainderInCellsTerm,
    /// A refusal the shared parser left until the sentence's entries are admitted (a readable
    /// cell whose result is refused by its own notation or pairs with no subject entry, an item
    /// after a computation's rest), with the parser's registered code, by its place in
    /// [`codes::REGISTRY`] (which keeps the kind small and `Copy`): the fault is the parser's,
    /// and only its order waits for the cells' kinds.
    DeferredSyntax(u16),
    /// A `cells!` result remainder that names no subject frame of its own kind
    /// ([`krs_syntax::StateRuleItem::reuse_refusal`]), asked once the sentence's entries are
    /// admitted, or at once for a sentence whose entries the table does not judge.
    ResultRemainderReuse,
    /// A readable result entry over a collection the subject does not match: Q1's overwrite of
    /// every instance, which the table admits and no lowering expresses yet.
    CollectionOverwrite,
    /// A `?` cell's `Some(..)`, a collection's instance list or a group cell's entry in a
    /// context alias or an equation's function context, which the table admits and those
    /// sentences' lowerings, which read fixed leaf cells only, do not express yet
    /// ([`krs_syntax::cell_entries::fixed_cells_only_reason`]).
    FixedCellsOnly,
    /// A `?` cell's `Some(..)` or `None` naming a child of a collection's instance record, which
    /// the table admits and no lowering writes yet
    /// ([`krs_syntax::cell_entries::instance_child_presence`]).
    InstanceChildMultiplicity,
    /// An entry value the table admits by its marks whose sort is not below its cell's: in an
    /// initializer, a term on a group cell, a group record on a leaf, a record of another group;
    /// in a sentence, a group record on a leaf whose sort holds no cell term, and `k::k![..]`, a
    /// term of sort `K`, on a leaf of another sort or a group.
    ContentSort,
    /// `k::k![..]` on a leaf of sort `KSequence`: a term of the leaf's own sort, written by its
    /// items, which a sentence's leaf entry does not lower yet.
    LeafItems,
    /// `Some(..)` or `None` as a field of a constructor record at a configuration position,
    /// which the macro reads as a group record's `?` child presence: a constructor's field is a
    /// term, and no KRS term is an `Option`.
    NotADeclaration,
}

/// Typed host-collection diagnostic with a stable category and human detail.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CollectionError {
    kind: CollectionErrorKind,
    detail: String,
    source_range: Option<Box<SourceRange>>,
    input_range: Option<ByteRange>,
    reference_key: Option<ProvenanceKey>,
    item: Option<String>,
}

impl CollectionError {
    pub(crate) fn new(kind: CollectionErrorKind, detail: impl Into<String>) -> Self {
        Self {
            kind,
            detail: detail.into(),
            source_range: None,
            input_range: None,
            reference_key: None,
            item: None,
        }
    }

    /// Names the item the error is about, which a diagnostic without a range reports instead.
    pub(crate) fn with_item(mut self, item: &krs_ir::StableItemId) -> Self {
        self.item = Some(item.to_string());
        self
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
        // The referenced node when the author's text locates it, the item otherwise.
        let range = self
            .reference_key
            .as_ref()
            .and_then(|key| provenance.origin_for(key))
            .and_then(krs_ir::OriginStack::exact_authored_range)
            .or_else(|| provenance.primary_origin().exact_authored_range());
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
            CollectionErrorKind::DuplicateCrateName => codes::collect::DUPLICATE_CRATE_NAME,
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
            CollectionErrorKind::ConfigurationCount => codes::analysis::CONFIGURATION_COUNT,
            CollectionErrorKind::GroupSubjectPosition => codes::analysis::GROUP_SUBJECT_POSITION,
            CollectionErrorKind::GroupNotInConfiguration => {
                codes::analysis::GROUP_NOT_IN_CONFIGURATION
            }
            CollectionErrorKind::CellOutsideSubject => codes::analysis::CELL_OUTSIDE_SUBJECT,
            CollectionErrorKind::GroupClaim => codes::analysis::GROUP_CLAIM,
            CollectionErrorKind::GroupPattern => codes::syntax::INVALID_PATTERN,
            CollectionErrorKind::ComputationCell => codes::analysis::COMPUTATION_CELL,
            CollectionErrorKind::MainCell => codes::analysis::MAIN_CELL,
            CollectionErrorKind::AmbiguousMainConfigurationVariable => {
                codes::syntax::AMBIGUOUS_MAIN_CONFIGURATION_VARIABLE
            }
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
            CollectionErrorKind::LetInMatchedField => codes::expand::LET_OUTSIDE_TERM,
            CollectionErrorKind::MatchesInMatchedField => codes::expand::MATCHES_OUTSIDE_CONDITION,
            CollectionErrorKind::RecordUpdateInMatchedField => codes::syntax::INVALID_RECORD_UPDATE,
            CollectionErrorKind::CellKindDisagreement => codes::collect::CELL_KIND_DISAGREEMENT,
            CollectionErrorKind::CellEntry(refusal) => refusal.code(),
            CollectionErrorKind::RecordRemainderInCellsTerm => {
                krs_syntax::positions::Class::RecordRemainderInCellsTerm.code()
            }
            CollectionErrorKind::DeferredSyntax(place) => codes::REGISTRY
                .get(usize::from(place))
                .map_or(codes::collect::SOURCE_SYNTAX, |info| info.code.clone()),
            CollectionErrorKind::ResultRemainderReuse => codes::syntax::UNSUPPORTED_RULE_BODY,
            CollectionErrorKind::CollectionOverwrite
            | CollectionErrorKind::InstanceChildMultiplicity => codes::analysis::COLLECTION_ENTRY,
            CollectionErrorKind::FixedCellsOnly => codes::expand::CELL_COLLECTION_PLACEMENT,
            CollectionErrorKind::ContentSort | CollectionErrorKind::LeafItems => {
                codes::analysis::INVALID_TERM
            }
            CollectionErrorKind::NotADeclaration => codes::expand::NOT_A_DECLARATION,
        };
        let diagnostic = Diagnostic::error(
            code,
            self.detail.clone(),
            self.source_range
                .clone()
                .map_or(Location::None, |range| Location::Source(*range)),
        );
        match (&self.source_range, &self.item) {
            (None, Some(item)) => diagnostic.with_item(item.clone()),
            _ => diagnostic,
        }
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
                CollectionErrorKind::DuplicateCrateName,
                codes::collect::DUPLICATE_CRATE_NAME,
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
                CollectionErrorKind::ConfigurationCount,
                codes::analysis::CONFIGURATION_COUNT,
            ),
            (
                CollectionErrorKind::ComputationCell,
                codes::analysis::COMPUTATION_CELL,
            ),
            (CollectionErrorKind::MainCell, codes::analysis::MAIN_CELL),
            (
                CollectionErrorKind::GroupSubjectPosition,
                codes::analysis::GROUP_SUBJECT_POSITION,
            ),
            (
                CollectionErrorKind::GroupNotInConfiguration,
                codes::analysis::GROUP_NOT_IN_CONFIGURATION,
            ),
            (
                CollectionErrorKind::CellOutsideSubject,
                codes::analysis::CELL_OUTSIDE_SUBJECT,
            ),
            (
                CollectionErrorKind::GroupClaim,
                codes::analysis::GROUP_CLAIM,
            ),
            (
                CollectionErrorKind::GroupPattern,
                codes::syntax::INVALID_PATTERN,
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
            (
                CollectionErrorKind::LetInMatchedField,
                codes::expand::LET_OUTSIDE_TERM,
            ),
            (
                CollectionErrorKind::MatchesInMatchedField,
                codes::expand::MATCHES_OUTSIDE_CONDITION,
            ),
            (
                CollectionErrorKind::RecordUpdateInMatchedField,
                codes::syntax::INVALID_RECORD_UPDATE,
            ),
            (
                CollectionErrorKind::RecordRemainderInCellsTerm,
                codes::analysis::INVALID_RECORD_UPDATE,
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
