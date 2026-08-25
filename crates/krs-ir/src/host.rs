//! Host-process descriptors emitted by author-facing macros.

use std::any::TypeId;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::error::Error;
use std::fmt;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

use crate::{
    BuiltinSort, ConfigurationCellDescriptor, HostApplicationIdentity, HostCellDeclaration,
    HostConfigurationRule, HostContextAlias, HostDeclarationIdentity, HostFixedConfiguration,
    HostGrammarDescriptor, HostHeadRule, HostStructuredRuleDescriptor, ItemKind,
    ProtocolV6ShapeError, ProtocolV7ShapeError, ProtocolVersion, SentenceKind,
};

/// A function returning rustc's build-local identity for a referenced type.
///
/// This value is meaningful only within one collector process. It deliberately
/// has no serialization implementation.
#[derive(Clone, Copy)]
pub struct HostTypeKey(pub fn() -> TypeId);

impl HostTypeKey {
    /// Resolves the key in the current collector process.
    #[must_use]
    pub fn resolve(self) -> TypeId {
        (self.0)()
    }
}

impl fmt::Debug for HostTypeKey {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Do not expose or accidentally snapshot the function address.
        formatter.write_str("HostTypeKey(<build-local>)")
    }
}

/// Host-only lookup key for joining a macro expansion to Cargo metadata.
///
/// Unlike [`crate::PackageId`], this is not a semantic or reproducible
/// identity. The absolute manifest directory comes from the target crate's
/// `env!("CARGO_MANIFEST_DIR")` and exists only to disambiguate Cargo packages
/// during host collection. The collector must discard it when producing a
/// [`crate::DescriptorBundle`]; this type intentionally cannot serialize.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct HostPackageKey {
    cargo_name: String,
    cargo_version: String,
    manifest_dir: PathBuf,
}

impl HostPackageKey {
    /// Creates a host lookup key from target-crate Cargo environment values.
    ///
    /// # Errors
    ///
    /// Returns [`HostIdentityError`] if the Cargo name or version is blank, or
    /// if the manifest directory is not an absolute host path.
    pub fn new(
        cargo_name: impl Into<String>,
        cargo_version: impl Into<String>,
        manifest_dir: impl Into<PathBuf>,
    ) -> Result<Self, HostIdentityError> {
        let cargo_name = cargo_name.into();
        if cargo_name.trim().is_empty() {
            return Err(HostIdentityError::EmptyCargoName);
        }
        let cargo_version = cargo_version.into();
        if cargo_version.trim().is_empty() {
            return Err(HostIdentityError::EmptyCargoVersion);
        }
        let manifest_dir = manifest_dir.into();
        if !manifest_dir.is_absolute() {
            return Err(HostIdentityError::ManifestDirNotAbsolute(manifest_dir));
        }
        Ok(Self {
            cargo_name,
            cargo_version,
            manifest_dir,
        })
    }

    /// Returns the Cargo package name captured in the target crate.
    #[must_use]
    pub fn cargo_name(&self) -> &str {
        &self.cargo_name
    }

    /// Returns the Cargo package version captured in the target crate.
    #[must_use]
    pub fn cargo_version(&self) -> &str {
        &self.cargo_version
    }

    /// Returns the host-only absolute package lookup hint.
    #[must_use]
    pub fn manifest_dir(&self) -> &Path {
        &self.manifest_dir
    }
}

/// Macro-constructible item lookup identity used before Cargo materialization.
///
/// The Rust module path includes the crate-root segment emitted by
/// `module_path!()`. The collector joins the package key to Cargo metadata,
/// validates that root segment against the selected Cargo target, and only
/// then constructs the final namespace-bearing [`crate::StableItemId`].
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct HostItemId {
    package: HostPackageKey,
    rust_module_path: Vec<String>,
    item_name: String,
    item_kind: ItemKind,
    disambiguator: String,
}

impl HostItemId {
    /// Creates an item key from already split `module_path!()` segments.
    ///
    /// # Errors
    ///
    /// Returns [`HostIdentityError`] when a module path is empty or contains
    /// an invalid segment, the item name is blank, or the disambiguator
    /// contains a filesystem separator.
    pub fn new(
        package: HostPackageKey,
        rust_module_path: impl IntoIterator<Item = impl Into<String>>,
        item_name: impl Into<String>,
        item_kind: ItemKind,
        disambiguator: impl Into<String>,
    ) -> Result<Self, HostIdentityError> {
        let rust_module_path = rust_module_path
            .into_iter()
            .map(Into::into)
            .collect::<Vec<_>>();
        if rust_module_path.is_empty() {
            return Err(HostIdentityError::EmptyModulePath);
        }
        for segment in &rust_module_path {
            if segment.is_empty() || segment.contains("::") || segment.contains(['/', '\\']) {
                return Err(HostIdentityError::InvalidModuleSegment(segment.clone()));
            }
        }
        let item_name = item_name.into();
        if item_name.trim().is_empty()
            || item_name.contains("::")
            || item_name.contains(['/', '\\'])
        {
            return Err(HostIdentityError::InvalidItemName(item_name));
        }
        let disambiguator = disambiguator.into();
        if disambiguator.contains(['/', '\\']) {
            return Err(HostIdentityError::InvalidDisambiguator(disambiguator));
        }
        Ok(Self {
            package,
            rust_module_path,
            item_name,
            item_kind,
            disambiguator,
        })
    }

    /// Factory for values emitted directly by a procedural macro.
    ///
    /// Callers pass `env!("CARGO_PKG_NAME")`, `env!("CARGO_PKG_VERSION")`,
    /// `env!("CARGO_MANIFEST_DIR")`, and `module_path!()` from the target crate.
    ///
    /// # Errors
    ///
    /// Returns [`HostIdentityError`] when any package or item component is not
    /// a valid host lookup identity.
    pub fn from_macro_context(
        cargo_name: impl Into<String>,
        cargo_version: impl Into<String>,
        manifest_dir: impl Into<PathBuf>,
        module_path: &str,
        item_name: impl Into<String>,
        item_kind: ItemKind,
        disambiguator: impl Into<String>,
    ) -> Result<Self, HostIdentityError> {
        let package = HostPackageKey::new(cargo_name, cargo_version, manifest_dir)?;
        Self::new(
            package,
            module_path.split("::"),
            item_name,
            item_kind,
            disambiguator,
        )
    }

    /// Returns the Cargo metadata lookup key.
    #[must_use]
    pub const fn package(&self) -> &HostPackageKey {
        &self.package
    }

    /// Returns the full `module_path!()` segments, including crate root.
    #[must_use]
    pub fn rust_module_path(&self) -> &[String] {
        &self.rust_module_path
    }

    /// Returns the authored or deterministic generated item name.
    #[must_use]
    pub fn item_name(&self) -> &str {
        &self.item_name
    }

    /// Returns the declaration namespace.
    #[must_use]
    pub const fn item_kind(&self) -> ItemKind {
        self.item_kind
    }

    /// Returns the stable same-scope disambiguator.
    #[must_use]
    pub fn disambiguator(&self) -> &str {
        &self.disambiguator
    }
}

/// Invalid host-only Cargo/item lookup data.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum HostIdentityError {
    /// Target crate reported no Cargo package name.
    EmptyCargoName,
    /// Target crate reported no Cargo package version.
    EmptyCargoVersion,
    /// `CARGO_MANIFEST_DIR` was not an absolute host lookup path.
    ManifestDirNotAbsolute(PathBuf),
    /// `module_path!()` produced no segments.
    EmptyModulePath,
    /// A module path component contained a separator or was empty.
    InvalidModuleSegment(String),
    /// An item name was empty or not a single Rust path segment.
    InvalidItemName(String),
    /// A disambiguator contained a filesystem separator.
    InvalidDisambiguator(String),
}

impl fmt::Display for HostIdentityError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyCargoName => {
                formatter.write_str("host Cargo package name must not be empty")
            }
            Self::EmptyCargoVersion => {
                formatter.write_str("host Cargo package version must not be empty")
            }
            Self::ManifestDirNotAbsolute(path) => write!(
                formatter,
                "host manifest directory `{}` must be absolute",
                path.display()
            ),
            Self::EmptyModulePath => formatter.write_str("host Rust module path must not be empty"),
            Self::InvalidModuleSegment(segment) => {
                write!(formatter, "invalid host module segment `{segment}`")
            }
            Self::InvalidItemName(name) => write!(formatter, "invalid host item name `{name}`"),
            Self::InvalidDisambiguator(value) => {
                write!(formatter, "invalid host item disambiguator `{value}`")
            }
        }
    }
}

impl Error for HostIdentityError {}

/// One-based source position captured from stable `proc_macro::Span` APIs.
///
/// Columns count Unicode scalar values, not UTF-8 bytes or UTF-16 code units.
/// These positions are validation anchors only; the collector reparses the
/// exact source revision to produce final byte-based [`crate::SourceRange`]s.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct HostSourcePosition {
    line: u32,
    scalar_column: u32,
}

impl HostSourcePosition {
    /// Creates a one-based stable-span position.
    ///
    /// # Errors
    ///
    /// Returns [`HostProvenanceError`] if either coordinate is zero.
    pub const fn new(line: u32, scalar_column: u32) -> Result<Self, HostProvenanceError> {
        if line == 0 {
            return Err(HostProvenanceError::ZeroLine);
        }
        if scalar_column == 0 {
            return Err(HostProvenanceError::ZeroColumn);
        }
        Ok(Self {
            line,
            scalar_column,
        })
    }

    /// Returns the one-based source line.
    #[must_use]
    pub const fn line(self) -> u32 {
        self.line
    }

    /// Returns the one-based Unicode-scalar column.
    #[must_use]
    pub const fn scalar_column(self) -> u32 {
        self.scalar_column
    }
}

/// Precision available for one expansion-time source anchor.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum AnchorPrecision {
    /// The selected first and last authored leaves were directly recoverable.
    Exact,
    /// The node could only inherit the containing macro invocation location.
    InvocationFallback,
}

/// A non-serializable, expansion-time line/column anchor.
///
/// It intentionally contains no local path, raw span, byte offset, or source
/// text. `display_file` is only a remapped/display hint; Cargo package identity
/// remains authoritative when the collector locates source.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct HostSourceAnchor {
    display_file: String,
    start: HostSourcePosition,
    end: HostSourcePosition,
    precision: AnchorPrecision,
}

impl HostSourceAnchor {
    /// Creates a validated half-open display position range.
    ///
    /// # Errors
    ///
    /// Returns [`HostProvenanceError`] if the display filename is empty or
    /// absolute, or if `end` does not follow `start`.
    pub fn new(
        display_file: impl Into<String>,
        start: HostSourcePosition,
        end: HostSourcePosition,
        precision: AnchorPrecision,
    ) -> Result<Self, HostProvenanceError> {
        let display_file = display_file.into();
        if display_file.trim().is_empty() {
            return Err(HostProvenanceError::EmptyDisplayFile);
        }
        if is_absolute_display_file(&display_file) {
            return Err(HostProvenanceError::AbsoluteDisplayFile(display_file));
        }
        if end == start {
            return Err(HostProvenanceError::EmptyEndpointRange);
        }
        if end < start {
            return Err(HostProvenanceError::ReversedEndpoints { start, end });
        }
        Ok(Self {
            display_file,
            start,
            end,
            precision,
        })
    }

    /// Returns rustc's display/remapped filename hint.
    #[must_use]
    pub fn display_file(&self) -> &str {
        &self.display_file
    }

    /// Returns the inclusive start anchor.
    #[must_use]
    pub const fn start(&self) -> HostSourcePosition {
        self.start
    }

    /// Returns the exclusive end anchor.
    #[must_use]
    pub const fn end(&self) -> HostSourcePosition {
        self.end
    }

    /// Returns whether this anchor is exact or inherited from its invocation.
    #[must_use]
    pub const fn precision(&self) -> AnchorPrecision {
        self.precision
    }
}

/// Stable key used to match a semantic node during provenance reparsing.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(try_from = "ProvenanceKeyWire")]
pub struct ProvenanceKey {
    role: String,
    ordinal: u32,
}

#[derive(Deserialize)]
struct ProvenanceKeyWire {
    role: String,
    ordinal: u32,
}

impl TryFrom<ProvenanceKeyWire> for ProvenanceKey {
    type Error = HostProvenanceError;

    fn try_from(wire: ProvenanceKeyWire) -> Result<Self, Self::Error> {
        Self::new(wire.role, wire.ordinal)
    }
}

impl ProvenanceKey {
    /// Creates a semantic role and same-role invocation ordinal.
    ///
    /// # Errors
    ///
    /// Returns [`HostProvenanceError::EmptyRole`] when `role` is blank.
    pub fn new(role: impl Into<String>, ordinal: u32) -> Result<Self, HostProvenanceError> {
        let role = role.into();
        if role.trim().is_empty() {
            return Err(HostProvenanceError::EmptyRole);
        }
        Ok(Self { role, ordinal })
    }

    /// Returns the parser-defined semantic role.
    #[must_use]
    pub fn role(&self) -> &str {
        &self.role
    }

    /// Returns the zero-based occurrence within this invocation and role.
    #[must_use]
    pub const fn ordinal(&self) -> u32 {
        self.ordinal
    }
}

/// One semantic-node anchor captured by a procedural macro.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct HostAuthoredAnchor {
    key: ProvenanceKey,
    anchor: HostSourceAnchor,
}

impl HostAuthoredAnchor {
    /// Associates a validated semantic key with a source anchor.
    #[must_use]
    pub const fn new(key: ProvenanceKey, anchor: HostSourceAnchor) -> Self {
        Self { key, anchor }
    }

    /// Returns the parser matching key.
    #[must_use]
    pub const fn key(&self) -> &ProvenanceKey {
        &self.key
    }

    /// Returns the expansion-time position anchor.
    #[must_use]
    pub const fn anchor(&self) -> &HostSourceAnchor {
        &self.anchor
    }
}

/// Pre-materialization provenance retained in a host descriptor.
///
/// The collector resolves these hints against Cargo-owned package source and
/// emits content-addressed byte ranges into [`crate::OriginStack`]. This host
/// value is intentionally not serializable.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HostProvenance {
    invocation: HostSourceAnchor,
    authored: Vec<HostAuthoredAnchor>,
}

impl HostProvenance {
    /// Creates nonempty provenance with unique `(role, ordinal)` keys.
    ///
    /// # Errors
    ///
    /// Returns [`HostProvenanceError::MissingAuthoredAnchor`] when no semantic
    /// anchor is supplied, or [`HostProvenanceError::DuplicateKey`] when two
    /// anchors would compete for the same shared-parser match. A synthesized
    /// node uses an [`AnchorPrecision::InvocationFallback`] authored anchor
    /// rather than leaving this collection empty.
    pub fn new(
        invocation: HostSourceAnchor,
        authored: Vec<HostAuthoredAnchor>,
    ) -> Result<Self, HostProvenanceError> {
        if authored.is_empty() {
            return Err(HostProvenanceError::MissingAuthoredAnchor);
        }
        let mut keys = HashSet::with_capacity(authored.len());
        for authored_anchor in &authored {
            if !keys.insert(authored_anchor.key.clone()) {
                return Err(HostProvenanceError::DuplicateKey(
                    authored_anchor.key.clone(),
                ));
            }
        }
        Ok(Self {
            invocation,
            authored,
        })
    }

    /// Returns the containing attribute or function-like invocation anchor.
    #[must_use]
    pub const fn invocation(&self) -> &HostSourceAnchor {
        &self.invocation
    }

    /// Returns semantic-node anchors in parser-defined order.
    #[must_use]
    pub fn authored(&self) -> &[HostAuthoredAnchor] {
        &self.authored
    }

    /// Merges two descriptor fragments without changing either fragment's
    /// authored anchors. The left-hand invocation remains the containing
    /// invocation for the combined descriptor.
    ///
    /// # Errors
    ///
    /// Returns [`HostProvenanceError::DuplicateKey`] when both fragments claim
    /// the same parser-owned key.
    pub fn merge(self, other: Self) -> Result<Self, HostProvenanceError> {
        let mut authored = self.authored;
        authored.extend(other.authored);
        Self::new(self.invocation, authored)
    }
}

/// Invalid pre-materialization provenance data.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum HostProvenanceError {
    /// Stable span line was zero instead of one-based.
    ZeroLine,
    /// Stable span Unicode-scalar column was zero instead of one-based.
    ZeroColumn,
    /// Rustc supplied no usable display filename.
    EmptyDisplayFile,
    /// A local absolute path was presented as a display filename.
    AbsoluteDisplayFile(String),
    /// Start and end referred to the same position.
    EmptyEndpointRange,
    /// The endpoint preceded the start point.
    ReversedEndpoints {
        /// Inclusive start anchor.
        start: HostSourcePosition,
        /// Exclusive end anchor.
        end: HostSourcePosition,
    },
    /// A shared-parser semantic role was empty.
    EmptyRole,
    /// No authored semantic anchor was supplied for the descriptor.
    MissingAuthoredAnchor,
    /// Two authored anchors used the same semantic key.
    DuplicateKey(ProvenanceKey),
}

impl fmt::Display for HostProvenanceError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ZeroLine => formatter.write_str("host source line must be one-based"),
            Self::ZeroColumn => formatter.write_str("host source column must be one-based"),
            Self::EmptyDisplayFile => formatter.write_str("display filename must not be empty"),
            Self::AbsoluteDisplayFile(file) => {
                write!(
                    formatter,
                    "display filename `{file}` must not be an absolute path"
                )
            }
            Self::EmptyEndpointRange => formatter.write_str("host source anchor must not be empty"),
            Self::ReversedEndpoints { start, end } => {
                write!(
                    formatter,
                    "host source endpoint {end:?} precedes start {start:?}"
                )
            }
            Self::EmptyRole => formatter.write_str("provenance role must not be empty"),
            Self::MissingAuthoredAnchor => {
                formatter.write_str("host provenance requires at least one authored anchor")
            }
            Self::DuplicateKey(key) => write!(
                formatter,
                "duplicate provenance key `{}#{}`",
                key.role, key.ordinal
            ),
        }
    }
}

impl Error for HostProvenanceError {}

/// Duplicate parser-owned key in one rule's explicit target references.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DuplicateReferenceKey {
    /// Key claimed by more than one target.
    pub key: ProvenanceKey,
}

impl fmt::Display for DuplicateReferenceKey {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "duplicate explicit reference key `{}#{}`",
            self.key.role, self.key.ordinal
        )
    }
}

impl Error for DuplicateReferenceKey {}

pub(crate) fn validate_unique_reference_keys<'a>(
    keys: impl IntoIterator<Item = &'a ProvenanceKey>,
) -> Result<(), DuplicateReferenceKey> {
    let mut unique = HashSet::new();
    for key in keys {
        if !unique.insert(key) {
            return Err(DuplicateReferenceKey { key: key.clone() });
        }
    }
    Ok(())
}

pub(crate) const CONFIGURATION_VARIABLE_TYPE_ROLE: &str = "configuration_variable_type";
pub(crate) const INITIALIZER_TERM_PATH_ROLE: &str = "initializer_term_path";

/// Invalid fixed M2 configuration descriptor data.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ConfigurationDescriptorError {
    /// The authored root-cell name was blank.
    EmptyRoot,
    /// The fixed computation-cell name was not exactly `k`.
    InvalidCellName(String),
    /// The fixed computation-cell sort was not builtin `KSequence`.
    InvalidCellSort(BuiltinSort),
    /// The optional main variable used a blank Rust binding.
    EmptyVariableBinding,
    /// The optional main variable used a blank external K name.
    EmptyVariableName,
    /// The main-variable sort did not use its parser-owned role/ordinal.
    InvalidVariableSortKey(ProvenanceKey),
    /// The paired initializer name was not exactly `init`.
    InvalidInitializerName(String),
    /// The shared-parser term spelling was blank.
    EmptyInitializerTerm,
    /// An initializer semantic reference used a non-term parser role.
    InvalidInitializerReferenceKey(ProvenanceKey),
    /// A semantic reference had no matching parser-owned initializer anchor.
    MissingInitializerReferenceOrigin(ProvenanceKey),
    /// Two semantic references claimed one parser node.
    DuplicateReferenceKey(DuplicateReferenceKey),
    /// The combined descriptor did not expose its concrete configuration type.
    MissingConfigurationTypeKey,
    /// The combined payload was attached to a non-configuration item ID.
    ConfigurationItemKindMismatch(ItemKind),
    /// The associated initializer helper reported a different concrete `Self`.
    InitializerOwnerTypeMismatch,
    /// A resolved reference has the wrong declaration kind.
    ReferenceKindMismatch {
        /// Parser node whose target has the wrong kind.
        key: ProvenanceKey,
        /// Kind required by the configuration contract.
        expected: ItemKind,
        /// Kind present in the resolved stable item ID.
        actual: ItemKind,
    },
}

impl fmt::Display for ConfigurationDescriptorError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyRoot => formatter.write_str("configuration root name must not be blank"),
            Self::InvalidCellName(name) => write!(
                formatter,
                "M2 configuration cell must be named `k`, not `{name}`"
            ),
            Self::InvalidCellSort(sort) => write!(
                formatter,
                "M2 configuration cell must use builtin KSequence, not {sort:?}"
            ),
            Self::EmptyVariableBinding => {
                formatter.write_str("configuration-variable binding must not be blank")
            }
            Self::EmptyVariableName => {
                formatter.write_str("configuration-variable external name must not be blank")
            }
            Self::InvalidVariableSortKey(key) => write!(
                formatter,
                "configuration-variable sort uses invalid parser key `{}#{}`",
                key.role, key.ordinal
            ),
            Self::InvalidInitializerName(name) => write!(
                formatter,
                "M2 paired initializer must be named `init`, not `{name}`"
            ),
            Self::EmptyInitializerTerm => {
                formatter.write_str("initializer term spelling must not be blank")
            }
            Self::InvalidInitializerReferenceKey(key) => write!(
                formatter,
                "initializer semantic reference uses invalid parser key `{}#{}`",
                key.role, key.ordinal
            ),
            Self::MissingInitializerReferenceOrigin(key) => write!(
                formatter,
                "configuration semantic reference `{}#{}` has no initializer provenance node",
                key.role, key.ordinal
            ),
            Self::DuplicateReferenceKey(error) => error.fmt(formatter),
            Self::MissingConfigurationTypeKey => {
                formatter.write_str("configuration descriptor has no declared concrete type key")
            }
            Self::ConfigurationItemKindMismatch(actual) => write!(
                formatter,
                "configuration payload is attached to {actual:?}, not Configuration"
            ),
            Self::InitializerOwnerTypeMismatch => formatter.write_str(
                "paired initializer helper belongs to a different concrete configuration type",
            ),
            Self::ReferenceKindMismatch {
                key,
                expected,
                actual,
            } => write!(
                formatter,
                "configuration reference `{}#{}` resolves to {actual:?}, but {expected:?} is required",
                key.role, key.ordinal
            ),
        }
    }
}

impl Error for ConfigurationDescriptorError {}

pub(crate) fn validate_configuration_shape<'a>(
    root: &str,
    cell: &ConfigurationCellDescriptor,
    variable: Option<(&str, &str, &'a ProvenanceKey)>,
    initializer_name: &str,
    initializer_term: &str,
    initializer_references: impl IntoIterator<Item = &'a ProvenanceKey>,
) -> Result<(), ConfigurationDescriptorError> {
    if root.trim().is_empty() {
        return Err(ConfigurationDescriptorError::EmptyRoot);
    }
    if cell.name != "k" {
        return Err(ConfigurationDescriptorError::InvalidCellName(
            cell.name.clone(),
        ));
    }
    if cell.content_sort != BuiltinSort::KSequence {
        return Err(ConfigurationDescriptorError::InvalidCellSort(
            cell.content_sort,
        ));
    }
    let variable_key = if let Some((binding, external_name, key)) = variable {
        if binding.trim().is_empty() {
            return Err(ConfigurationDescriptorError::EmptyVariableBinding);
        }
        if external_name.trim().is_empty() {
            return Err(ConfigurationDescriptorError::EmptyVariableName);
        }
        if key.role() != CONFIGURATION_VARIABLE_TYPE_ROLE || key.ordinal() != 0 {
            return Err(ConfigurationDescriptorError::InvalidVariableSortKey(
                key.clone(),
            ));
        }
        Some(key)
    } else {
        None
    };
    if initializer_name != "init" {
        return Err(ConfigurationDescriptorError::InvalidInitializerName(
            initializer_name.to_owned(),
        ));
    }
    if initializer_term.trim().is_empty() {
        return Err(ConfigurationDescriptorError::EmptyInitializerTerm);
    }
    let initializer_references = initializer_references.into_iter().collect::<Vec<_>>();
    for key in &initializer_references {
        if key.role() != INITIALIZER_TERM_PATH_ROLE {
            return Err(
                ConfigurationDescriptorError::InvalidInitializerReferenceKey((*key).clone()),
            );
        }
    }
    validate_unique_reference_keys(variable_key.into_iter().chain(initializer_references))
        .map_err(ConfigurationDescriptorError::DuplicateReferenceKey)
}

/// Invalid binding list in one rule payload.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RuleBindingError {
    /// A binding name was empty or whitespace-only.
    Blank {
        /// Parameter position in authored order.
        parameter_index: usize,
        /// Binding position within that parameter's pattern preorder.
        binding_index: usize,
    },
    /// One rule introduced the same binding name more than once.
    Duplicate {
        /// Repeated authored binding name.
        binding: String,
        /// First parameter containing the name.
        first_parameter_index: usize,
        /// First preorder position within that parameter.
        first_binding_index: usize,
        /// Parameter containing the duplicate.
        duplicate_parameter_index: usize,
        /// Duplicate preorder position within that parameter.
        duplicate_binding_index: usize,
    },
}

impl fmt::Display for RuleBindingError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Blank {
                parameter_index,
                binding_index,
            } => write!(
                formatter,
                "blank rule binding at parameter {parameter_index}, binding {binding_index}"
            ),
            Self::Duplicate {
                binding,
                first_parameter_index,
                first_binding_index,
                duplicate_parameter_index,
                duplicate_binding_index,
            } => write!(
                formatter,
                "duplicate rule binding `{binding}` at parameter {duplicate_parameter_index}, binding {duplicate_binding_index}; first declared at parameter {first_parameter_index}, binding {first_binding_index}"
            ),
        }
    }
}

impl Error for RuleBindingError {}

pub(crate) fn validate_rule_bindings<'a>(
    parameters: impl IntoIterator<Item = &'a [String]>,
) -> Result<(), RuleBindingError> {
    let mut seen = HashMap::<&str, (usize, usize)>::new();
    for (parameter_index, bindings) in parameters.into_iter().enumerate() {
        for (binding_index, binding) in bindings.iter().enumerate() {
            if binding.trim().is_empty() {
                return Err(RuleBindingError::Blank {
                    parameter_index,
                    binding_index,
                });
            }
            if let Some(&(first_parameter_index, first_binding_index)) = seen.get(binding.as_str())
            {
                return Err(RuleBindingError::Duplicate {
                    binding: binding.clone(),
                    first_parameter_index,
                    first_binding_index,
                    duplicate_parameter_index: parameter_index,
                    duplicate_binding_index: binding_index,
                });
            }
            seen.insert(binding, (parameter_index, binding_index));
        }
    }
    Ok(())
}

fn is_absolute_display_file(display_file: &str) -> bool {
    let bytes = display_file.as_bytes();
    Path::new(display_file).is_absolute()
        || display_file.starts_with("file://")
        || display_file.starts_with("\\\\")
        || (bytes.len() >= 3
            && bytes[0].is_ascii_alphabetic()
            && bytes[1] == b':'
            && matches!(bytes[2], b'/' | b'\\'))
}

/// A rustc-resolved type reference awaiting collector resolution.
#[derive(Clone, Debug)]
pub struct HostTypeReference {
    /// Build-local type key.
    pub key: HostTypeKey,
    /// Authored Rust path, retained only for diagnostics.
    pub authored_path: String,
}

/// Registration data produced by one procedural macro expansion.
///
/// This type cannot be serialized because it may contain function pointers
/// and `TypeId` producers. Only a collector may resolve it into bundle data.
#[derive(Clone, Debug)]
pub struct HostDescriptor {
    /// Protocol expected by the producing macro.
    pub protocol_version: ProtocolVersion,
    /// Host-only lookup identity awaiting Cargo/K namespace materialization.
    pub id: HostItemId,
    /// Exact build-local identity, if this item declares a Rust-backed item.
    ///
    /// Ordinary types use a nominal `TypeId`. Enum constructor descriptors use
    /// an owner-enum/per-variant-marker pair because a Rust variant is not a
    /// type. Only the collector may resolve this host-only value.
    pub declared_type: Option<HostDeclarationIdentity>,
    /// Macro-local payload containing unresolved Rust references.
    pub payload: HostDescriptorPayload,
    /// Enabled cfg keys and their optional values.
    pub cfg: BTreeMap<String, Option<String>>,
    /// Expansion-time anchors awaiting collector materialization.
    pub provenance: HostProvenance,
}

impl HostDescriptor {
    /// Validates the host-only pairing proof for a configuration payload.
    ///
    /// The nested initializer helper returns its concrete associated `Self`
    /// key. Equality with the outer configuration declaration key detects a
    /// missing or accidentally cross-wired helper without executing the
    /// authored initializer.
    ///
    /// # Errors
    ///
    /// Returns [`ConfigurationDescriptorError`] for an invalid payload,
    /// missing declared key, or owner-key mismatch. Non-configuration
    /// descriptors require no pairing proof and return `Ok(())`.
    pub fn validate_configuration_pairing(&self) -> Result<(), ConfigurationDescriptorError> {
        let HostDescriptorPayload::Configuration(configuration) = &self.payload else {
            return Ok(());
        };
        if self.id.item_kind() != ItemKind::Configuration {
            return Err(ConfigurationDescriptorError::ConfigurationItemKindMismatch(
                self.id.item_kind(),
            ));
        }
        configuration.validate()?;
        let declared = self
            .declared_type
            .ok_or(ConfigurationDescriptorError::MissingConfigurationTypeKey)?;
        if declared.resolve()
            != HostApplicationIdentity::Nominal(configuration.initializer.owner_type.resolve())
        {
            return Err(ConfigurationDescriptorError::InitializerOwnerTypeMismatch);
        }
        Ok(())
    }

    /// Checks protocol-v6 outer ownership before stable collection.
    ///
    /// # Errors
    ///
    /// Returns [`ProtocolV6ShapeError`] when a grammar or structured rule is
    /// registered under the wrong stable namespace.
    pub fn validate_v6_ownership(&self) -> Result<(), ProtocolV6ShapeError> {
        let expected = match &self.payload {
            HostDescriptorPayload::Grammar(_) => Some(ItemKind::Grammar),
            HostDescriptorPayload::StructuredRule(rule) => Some(match rule.sentence_kind {
                SentenceKind::Transition => ItemKind::Rule,
                SentenceKind::Equation => ItemKind::Equation,
                SentenceKind::Simplification => ItemKind::Simplification,
                SentenceKind::Alias => ItemKind::Alias,
                SentenceKind::Claim => ItemKind::Claim,
            }),
            HostDescriptorPayload::Sort(_)
            | HostDescriptorPayload::Constructor(_)
            | HostDescriptorPayload::Configuration(_)
            | HostDescriptorPayload::Rule(_)
            | HostDescriptorPayload::FixedConfiguration(_)
            | HostDescriptorPayload::Cell(_)
            | HostDescriptorPayload::ConfigurationRule(_)
            | HostDescriptorPayload::HeadRule(_)
            | HostDescriptorPayload::ContextAlias(_) => None,
        };
        if let Some(expected) = expected.filter(|expected| self.id.item_kind() != *expected) {
            return Err(ProtocolV6ShapeError::DescriptorItemKind {
                expected,
                actual: self.id.item_kind(),
            });
        }
        Ok(())
    }

    /// Validates protocol-v7 configuration/cell/rule ownership and host joins.
    ///
    /// # Errors
    ///
    /// Returns [`ProtocolV7ShapeError`] when a staged v7 payload is registered
    /// under the wrong item kind, lacks its nominal declaration key, or has an
    /// invalid configuration/cell/rule shape.
    pub fn validate_v7_ownership(&self) -> Result<(), ProtocolV7ShapeError> {
        match &self.payload {
            HostDescriptorPayload::FixedConfiguration(configuration) => {
                if self.id.item_kind() != ItemKind::Configuration {
                    return Err(ProtocolV7ShapeError::ItemKind {
                        field: "fixed configuration descriptor",
                        expected: "Configuration",
                        actual: self.id.item_kind(),
                    });
                }
                let Some(HostDeclarationIdentity::Nominal(owner)) = self.declared_type else {
                    return Err(ProtocolV7ShapeError::InvalidCellContent(
                        "fixed configuration lacks a nominal host owner",
                    ));
                };
                configuration.validate(owner)
            }
            HostDescriptorPayload::Cell(declaration) => {
                if self.id.item_kind() != ItemKind::Cell {
                    return Err(ProtocolV7ShapeError::ItemKind {
                        field: "nested cell descriptor",
                        expected: "Cell",
                        actual: self.id.item_kind(),
                    });
                }
                let Some(HostDeclarationIdentity::Nominal(owner)) = self.declared_type else {
                    return Err(ProtocolV7ShapeError::InvalidCellContent(
                        "nested cell declaration lacks a nominal host owner",
                    ));
                };
                declaration.validate_host(owner)
            }
            HostDescriptorPayload::ConfigurationRule(rule) => rule.validate(self.id.item_kind()),
            HostDescriptorPayload::HeadRule(rule) => rule.validate(self.id.item_kind()),
            HostDescriptorPayload::ContextAlias(alias) => alias.validate(self.id.item_kind()),
            HostDescriptorPayload::Sort(_)
            | HostDescriptorPayload::Constructor(_)
            | HostDescriptorPayload::Configuration(_)
            | HostDescriptorPayload::Rule(_)
            | HostDescriptorPayload::Grammar(_)
            | HostDescriptorPayload::StructuredRule(_) => Ok(()),
        }
    }
}

/// Minimal host-side descriptor variants.
#[derive(Clone, Debug)]
pub enum HostDescriptorPayload {
    /// Open-sort declaration.
    Sort(HostSortDescriptor),
    /// Constructor declaration.
    Constructor(HostConstructorDescriptor),
    /// Fixed configuration plus its paired associated initializer.
    Configuration(HostConfigurationDescriptor),
    /// Relational sentence declaration.
    Rule(HostRuleDescriptor),
    /// Typed after-the-fact grammar registration.
    Grammar(Box<HostGrammarDescriptor>),
    /// Fully structured relational sentence.
    StructuredRule(Box<HostStructuredRuleDescriptor>),
    /// Protocol-v7 complete fixed configuration and initializer.
    FixedConfiguration(Box<HostFixedConfiguration>),
    /// Protocol-v7 nominal nested fixed-cell declaration.
    Cell(Box<HostCellDeclaration>),
    /// Protocol-v7 simultaneous whole-configuration rule.
    ConfigurationRule(Box<HostConfigurationRule>),
    /// Bare-sort rule completed into a fixed computation cell by the collector.
    HeadRule(Box<HostHeadRule>),
    /// One-sided reusable fixed-configuration context template.
    ContextAlias(Box<HostContextAlias>),
}

/// Host-side sort payload.
#[derive(Clone, Debug, Default)]
pub struct HostSortDescriptor {
    /// Rust-resolved direct super-sort references.
    pub parents: Vec<HostTypeReference>,
}

/// Host-side constructor payload.
#[derive(Clone, Debug)]
pub struct HostConstructorDescriptor {
    /// Rust-resolved result sort.
    pub sort: crate::HostSortReference,
    /// Checked authored syntax template.
    pub syntax: Option<String>,
    /// Ordered record fields and their rustc-resolved sorts.
    pub fields: Vec<HostConstructorFieldDescriptor>,
}

/// One host-side constructor record field.
#[derive(Clone, Debug)]
pub struct HostConstructorFieldDescriptor {
    /// Rust field name.
    pub name: String,
    /// Rust-resolved field sort.
    pub sort: HostTypeReference,
}

/// Host-side fixed configuration payload.
///
/// The mandatory nested initializer is produced by the paired-expansion
/// architecture: `#[configuration]` owns the registration, while `#[init]`
/// supplies the declarative payload helper. There is no separate initializer
/// registration or stable initializer item identity.
#[derive(Clone, Debug)]
pub struct HostConfigurationDescriptor {
    /// Authored root-cell name from `#[k::configuration(root = "...")]`.
    pub root: String,
    /// The sole fixed authored computation cell.
    pub cell: ConfigurationCellDescriptor,
    /// Zero or one explicitly main configuration variable.
    pub main_variable: Option<HostConfigurationVariableDescriptor>,
    /// Exactly one initializer payload paired by the configuration expansion.
    pub initializer: HostConfigurationInitializerDescriptor,
}

impl HostConfigurationDescriptor {
    /// Validates the fixed shape and parser-owned semantic reference roles.
    ///
    /// The collector must additionally compare `initializer.owner_type` with
    /// the outer [`HostDescriptor::declared_type`] to prove that the associated
    /// helper belongs to the registered concrete configuration type.
    ///
    /// # Errors
    ///
    /// Returns [`ConfigurationDescriptorError`] for an invalid fixed cell,
    /// blank syntax data, duplicate keys, or a non-semantic parser role.
    pub fn validate(&self) -> Result<(), ConfigurationDescriptorError> {
        validate_configuration_shape(
            &self.root,
            &self.cell,
            self.main_variable.as_ref().map(|variable| {
                (
                    variable.binding.as_str(),
                    variable.external_name.as_str(),
                    &variable.sort.key,
                )
            }),
            &self.initializer.name,
            &self.initializer.term,
            self.initializer
                .references
                .iter()
                .map(|reference| &reference.key),
        )?;
        let provenance_keys = self
            .initializer
            .provenance
            .authored()
            .iter()
            .map(HostAuthoredAnchor::key)
            .collect::<HashSet<_>>();
        let references = self
            .main_variable
            .iter()
            .map(|variable| &variable.sort)
            .chain(self.initializer.references.iter());
        for reference in references {
            if !provenance_keys.contains(&reference.key) {
                return Err(
                    ConfigurationDescriptorError::MissingInitializerReferenceOrigin(
                        reference.key.clone(),
                    ),
                );
            }
        }
        Ok(())
    }
}

/// Host-side optional main configuration variable.
#[derive(Clone, Debug)]
pub struct HostConfigurationVariableDescriptor {
    /// Authored Rust parameter binding.
    pub binding: String,
    /// External K configuration-variable name.
    pub external_name: String,
    /// Parser-keyed build-local reference to the declared variable sort.
    pub sort: HostDescriptorReference,
}

/// Host-only paired initializer data.
#[derive(Clone, Debug)]
pub struct HostConfigurationInitializerDescriptor {
    /// Fixed authored associated-method name (`init`).
    pub name: String,
    /// Concrete `Self` type key produced by the associated payload helper.
    ///
    /// This is compared with the configuration declaration's key during
    /// collection and is never serialized.
    pub owner_type: HostTypeKey,
    /// The initializer macro invocation, which may be in another source file
    /// from the configuration declaration.
    pub provenance: HostProvenance,
    /// Deterministic spelling reparsed by the existing shared term parser.
    pub term: String,
    /// Named term constructors only; wrapper paths, `Self`, and bound
    /// configuration variables are deliberately absent.
    pub references: Vec<HostDescriptorReference>,
}

/// One explicit rustc-resolved rule target keyed to the shared parser AST.
#[derive(Clone, Debug)]
pub struct HostDescriptorReference {
    /// Parser-owned semantic role and AST-order ordinal.
    pub key: ProvenanceKey,
    /// Build-local type target resolved by rustc.
    pub target: HostTypeReference,
}

impl HostDescriptorReference {
    /// Associates a parser-owned key with one rustc-resolved target.
    #[must_use]
    pub const fn new(key: ProvenanceKey, target: HostTypeReference) -> Self {
        Self { key, target }
    }
}

/// Host-side relational sentence payload.
#[derive(Clone, Debug)]
pub struct HostRuleDescriptor {
    /// Explicit semantic sentence kind.
    pub sentence_kind: SentenceKind,
    /// Parameters in authored order.
    pub parameters: Vec<HostRuleParameterDescriptor>,
    /// Rust-resolved result sort.
    pub result_sort: HostTypeReference,
    /// Explicit type and constructor targets keyed to parser provenance.
    ///
    /// This includes resolvable `rule_type`, `rule_result_type`,
    /// `rule_left_path`, and `rule_right_path` occurrences. Bare bound-variable
    /// paths do not receive a type target merely because they have an anchor.
    pub references: Vec<HostDescriptorReference>,
    /// Deterministic reference-surface pattern payload.
    pub lhs: String,
    /// Deterministic reference-surface result payload.
    pub rhs: String,
}

impl HostRuleDescriptor {
    /// Checks that one parser node does not resolve to multiple Rust targets.
    ///
    /// The collector invokes the corresponding bundle validation after it
    /// replaces every build-local target with a stable item ID.
    ///
    /// # Errors
    ///
    /// Returns [`DuplicateReferenceKey`] for the first repeated key.
    pub fn validate_reference_keys(&self) -> Result<(), DuplicateReferenceKey> {
        validate_unique_reference_keys(self.references.iter().map(|reference| &reference.key))
    }

    /// Validates binding names without changing their authored preorder.
    ///
    /// # Errors
    ///
    /// Returns [`RuleBindingError`] for a blank or repeated binding.
    pub fn validate_bindings(&self) -> Result<(), RuleBindingError> {
        validate_rule_bindings(
            self.parameters
                .iter()
                .map(|parameter| parameter.bindings.as_slice()),
        )
    }
}

/// One host-side rule parameter.
#[derive(Clone, Debug)]
pub struct HostRuleParameterDescriptor {
    /// Binder names in deterministic authored pattern preorder; may be empty.
    pub bindings: Vec<String>,
    /// Rust-resolved parameter sort.
    pub sort: HostTypeReference,
    /// Deterministic reference-surface pattern payload.
    pub pattern: String,
}

impl HostRuleParameterDescriptor {
    /// Validates this parameter's bindings without sorting them.
    ///
    /// # Errors
    ///
    /// Returns [`RuleBindingError`] for a blank or repeated binding.
    pub fn validate_bindings(&self) -> Result<(), RuleBindingError> {
        validate_rule_bindings(std::iter::once(self.bindings.as_slice()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_type_id() -> TypeId {
        TypeId::of::<u8>()
    }

    fn other_type_id() -> TypeId {
        TypeId::of::<u16>()
    }

    fn type_reference(path: &str) -> HostTypeReference {
        HostTypeReference {
            key: HostTypeKey(test_type_id),
            authored_path: path.into(),
        }
    }

    fn manifest_dir(name: &str) -> PathBuf {
        std::env::current_dir().unwrap().join(name)
    }

    fn position(line: u32, column: u32) -> HostSourcePosition {
        HostSourcePosition::new(line, column).unwrap()
    }

    #[test]
    fn host_packages_with_same_name_and_version_use_manifest_lookup_hint() {
        let package_a =
            HostPackageKey::new("semantics", "0.1.0", manifest_dir("package-a")).unwrap();
        let package_b =
            HostPackageKey::new("semantics", "0.1.0", manifest_dir("package-b")).unwrap();
        assert_ne!(package_a, package_b);

        let item_a = HostItemId::new(
            package_a,
            ["semantics", "expr"],
            "Value",
            ItemKind::Sort,
            "",
        )
        .unwrap();
        let item_b = HostItemId::new(
            package_b,
            ["semantics", "expr"],
            "Value",
            ItemKind::Sort,
            "",
        )
        .unwrap();
        assert_ne!(item_a, item_b);
    }

    #[test]
    fn macro_context_factory_preserves_full_rust_module_path() {
        let item = HostItemId::from_macro_context(
            "semantics",
            "0.1.0",
            manifest_dir("semantics"),
            "semantics::nested::expr",
            "Value",
            ItemKind::Sort,
            "",
        )
        .unwrap();
        assert_eq!(item.rust_module_path(), &["semantics", "nested", "expr"]);
        assert!(item.package().manifest_dir().is_absolute());
    }

    #[test]
    fn host_package_requires_absolute_manifest_lookup_hint() {
        assert_eq!(
            HostPackageKey::new("semantics", "0.1.0", "relative/package"),
            Err(HostIdentityError::ManifestDirNotAbsolute(PathBuf::from(
                "relative/package"
            )))
        );
        assert_eq!(
            HostPackageKey::new("", "0.1.0", manifest_dir("semantics")),
            Err(HostIdentityError::EmptyCargoName)
        );
    }

    #[test]
    fn host_item_rejects_invalid_macro_components() {
        let package = HostPackageKey::new("semantics", "0.1.0", manifest_dir("semantics")).unwrap();
        assert!(matches!(
            HostItemId::new(
                package.clone(),
                std::iter::empty::<String>(),
                "Value",
                ItemKind::Sort,
                ""
            ),
            Err(HostIdentityError::EmptyModulePath)
        ));
        assert!(matches!(
            HostItemId::new(package, ["semantics", ""], "Value", ItemKind::Sort, ""),
            Err(HostIdentityError::InvalidModuleSegment(_))
        ));
    }

    #[test]
    fn constructor_fields_retain_names_and_resolved_sorts() {
        let constructor = HostConstructorDescriptor {
            sort: crate::HostSortReference {
                key: ProvenanceKey::new("constructor_sort", 0).unwrap(),
                target: type_reference("model::Expr"),
            },
            syntax: Some("{value}".into()),
            fields: vec![HostConstructorFieldDescriptor {
                name: "value".into(),
                sort: type_reference("model::Value"),
            }],
        };
        assert_eq!(constructor.fields[0].name, "value");
        assert_eq!(constructor.fields[0].sort.key.resolve(), TypeId::of::<u8>());
    }

    #[test]
    fn host_rule_reference_keys_must_be_unique() {
        let key = ProvenanceKey::new("rule_left_path", 0).unwrap();
        let rule = HostRuleDescriptor {
            sentence_kind: SentenceKind::Transition,
            parameters: Vec::new(),
            result_sort: type_reference("model::Expr"),
            references: vec![
                HostDescriptorReference::new(key.clone(), type_reference("model::Foo")),
                HostDescriptorReference::new(key.clone(), type_reference("other::Foo")),
            ],
            lhs: "Foo".into(),
            rhs: "Bar".into(),
        };
        assert_eq!(
            rule.validate_reference_keys(),
            Err(DuplicateReferenceKey { key })
        );
    }

    #[test]
    fn host_rule_bindings_preserve_zero_or_many_authored_names() {
        let zero = HostRuleParameterDescriptor {
            bindings: Vec::new(),
            sort: type_reference("model::Expr"),
            pattern: "True".into(),
        };
        assert!(zero.validate_bindings().is_ok());

        let many = HostRuleParameterDescriptor {
            bindings: vec!["numerator".into(), "denominator".into()],
            sort: type_reference("model::Expr"),
            pattern: "Div(numerator, denominator)".into(),
        };
        assert!(many.validate_bindings().is_ok());
        assert_eq!(many.bindings, ["numerator", "denominator"]);
    }

    #[test]
    fn host_rule_bindings_reject_blank_and_duplicate_names() {
        let blank = HostRuleParameterDescriptor {
            bindings: vec!["numerator".into(), String::new()],
            sort: type_reference("model::Expr"),
            pattern: "Div(numerator, _)".into(),
        };
        assert!(matches!(
            blank.validate_bindings(),
            Err(RuleBindingError::Blank {
                binding_index: 1,
                ..
            })
        ));

        let duplicate = HostRuleParameterDescriptor {
            bindings: vec!["value".into(), "value".into()],
            sort: type_reference("model::Expr"),
            pattern: "Pair(value, value)".into(),
        };
        assert!(matches!(
            duplicate.validate_bindings(),
            Err(RuleBindingError::Duplicate {
                duplicate_binding_index: 1,
                ..
            })
        ));
    }

    #[test]
    fn host_configuration_retains_paired_owner_and_initializer_provenance() {
        let initializer_provenance = HostProvenance::new(
            HostSourceAnchor::new(
                "src/init.rs",
                position(2, 1),
                position(2, 10),
                AnchorPrecision::Exact,
            )
            .unwrap(),
            vec![
                HostAuthoredAnchor::new(
                    ProvenanceKey::new("initializer_declaration", 0).unwrap(),
                    HostSourceAnchor::new(
                        "src/init.rs",
                        position(3, 8),
                        position(3, 12),
                        AnchorPrecision::Exact,
                    )
                    .unwrap(),
                ),
                HostAuthoredAnchor::new(
                    ProvenanceKey::new("initializer_term_path", 0).unwrap(),
                    HostSourceAnchor::new(
                        "src/init.rs",
                        position(4, 9),
                        position(4, 19),
                        AnchorPrecision::Exact,
                    )
                    .unwrap(),
                ),
            ],
        )
        .unwrap();
        let configuration = HostConfigurationDescriptor {
            root: "machine".into(),
            cell: ConfigurationCellDescriptor {
                name: "k".into(),
                content_sort: BuiltinSort::KSequence,
            },
            main_variable: None,
            initializer: HostConfigurationInitializerDescriptor {
                name: "init".into(),
                owner_type: HostTypeKey(test_type_id),
                provenance: initializer_provenance,
                term: "model :: Foo".into(),
                references: vec![HostDescriptorReference::new(
                    ProvenanceKey::new("initializer_term_path", 0).unwrap(),
                    type_reference("model::Foo"),
                )],
            },
        };
        assert!(configuration.validate().is_ok());
        assert_eq!(
            configuration.initializer.owner_type.resolve(),
            TypeId::of::<u8>()
        );
        assert_eq!(
            configuration
                .initializer
                .provenance
                .invocation()
                .display_file(),
            "src/init.rs"
        );

        let package = HostPackageKey::new("semantics", "0.1.0", manifest_dir("semantics")).unwrap();
        let id = HostItemId::new(
            package,
            ["semantics", "machine"],
            "Machine",
            ItemKind::Configuration,
            "",
        )
        .unwrap();
        let outer_provenance = HostProvenance::new(
            anchor(AnchorPrecision::Exact),
            vec![HostAuthoredAnchor::new(
                ProvenanceKey::new("configuration_declaration", 0).unwrap(),
                anchor(AnchorPrecision::Exact),
            )],
        )
        .unwrap();
        let mut descriptor = HostDescriptor {
            protocol_version: ProtocolVersion::CURRENT,
            id,
            declared_type: Some(HostDeclarationIdentity::Nominal(HostTypeKey(test_type_id))),
            payload: HostDescriptorPayload::Configuration(configuration),
            cfg: BTreeMap::new(),
            provenance: outer_provenance,
        };
        assert!(descriptor.validate_configuration_pairing().is_ok());
        descriptor.declared_type = None;
        assert_eq!(
            descriptor.validate_configuration_pairing(),
            Err(ConfigurationDescriptorError::MissingConfigurationTypeKey)
        );
        descriptor.declared_type =
            Some(HostDeclarationIdentity::Nominal(HostTypeKey(other_type_id)));
        assert_eq!(
            descriptor.validate_configuration_pairing(),
            Err(ConfigurationDescriptorError::InitializerOwnerTypeMismatch)
        );
    }

    #[test]
    fn host_configuration_rejects_nonsemantic_and_duplicate_term_keys() {
        let invalid_key = ProvenanceKey::new("initializer_cell_constructor", 0).unwrap();
        let initializer_provenance = HostProvenance::new(
            anchor(AnchorPrecision::Exact),
            vec![HostAuthoredAnchor::new(
                ProvenanceKey::new("initializer_declaration", 0).unwrap(),
                anchor(AnchorPrecision::Exact),
            )],
        )
        .unwrap();
        let mut configuration = HostConfigurationDescriptor {
            root: "machine".into(),
            cell: ConfigurationCellDescriptor {
                name: "k".into(),
                content_sort: BuiltinSort::KSequence,
            },
            main_variable: None,
            initializer: HostConfigurationInitializerDescriptor {
                name: "init".into(),
                owner_type: HostTypeKey(test_type_id),
                provenance: initializer_provenance,
                term: "model :: Foo".into(),
                references: vec![HostDescriptorReference::new(
                    invalid_key.clone(),
                    type_reference("KCell::new"),
                )],
            },
        };
        assert_eq!(
            configuration.validate(),
            Err(ConfigurationDescriptorError::InvalidInitializerReferenceKey(invalid_key))
        );

        let key = ProvenanceKey::new("initializer_term_path", 0).unwrap();
        configuration.initializer.references = vec![
            HostDescriptorReference::new(key.clone(), type_reference("model::Foo")),
            HostDescriptorReference::new(key.clone(), type_reference("model::Bar")),
        ];
        assert_eq!(
            configuration.validate(),
            Err(ConfigurationDescriptorError::DuplicateReferenceKey(
                DuplicateReferenceKey { key }
            ))
        );
    }

    fn anchor(precision: AnchorPrecision) -> HostSourceAnchor {
        HostSourceAnchor::new("src/lib.rs", position(3, 2), position(3, 8), precision).unwrap()
    }

    #[test]
    fn positions_are_one_based() {
        assert_eq!(
            HostSourcePosition::new(0, 1),
            Err(HostProvenanceError::ZeroLine)
        );
        assert_eq!(
            HostSourcePosition::new(1, 0),
            Err(HostProvenanceError::ZeroColumn)
        );
    }

    #[test]
    fn anchors_reject_empty_reversed_and_absolute_locations() {
        let start = position(3, 8);
        let end = position(3, 2);
        assert_eq!(
            HostSourceAnchor::new("src/lib.rs", start, start, AnchorPrecision::Exact),
            Err(HostProvenanceError::EmptyEndpointRange)
        );
        assert!(matches!(
            HostSourceAnchor::new("src/lib.rs", start, end, AnchorPrecision::Exact),
            Err(HostProvenanceError::ReversedEndpoints { .. })
        ));
        for filename in ["", "/tmp/lib.rs", r"C:\checkout\lib.rs", r"\\server\lib.rs"] {
            assert!(
                HostSourceAnchor::new(
                    filename,
                    position(1, 1),
                    position(1, 2),
                    AnchorPrecision::Exact
                )
                .is_err()
            );
        }
    }

    #[test]
    fn provenance_keys_are_unique_within_authored_anchors() {
        let key = ProvenanceKey::new("rule_pattern", 0).unwrap();
        let authored = vec![
            HostAuthoredAnchor::new(key.clone(), anchor(AnchorPrecision::Exact)),
            HostAuthoredAnchor::new(key.clone(), anchor(AnchorPrecision::InvocationFallback)),
        ];
        assert_eq!(
            HostProvenance::new(anchor(AnchorPrecision::Exact), authored),
            Err(HostProvenanceError::DuplicateKey(key))
        );
    }

    #[test]
    fn provenance_requires_an_authored_anchor() {
        assert_eq!(
            HostProvenance::new(anchor(AnchorPrecision::Exact), Vec::new()),
            Err(HostProvenanceError::MissingAuthoredAnchor)
        );
    }

    #[test]
    fn provenance_merge_retains_disjoint_authored_anchors() {
        let left_key = ProvenanceKey::new("configuration_declaration", 0).unwrap();
        let right_key = ProvenanceKey::new("initializer_declaration", 0).unwrap();
        let left = HostProvenance::new(
            anchor(AnchorPrecision::Exact),
            vec![HostAuthoredAnchor::new(
                left_key.clone(),
                anchor(AnchorPrecision::Exact),
            )],
        )
        .unwrap();
        let right_anchor = HostSourceAnchor::new(
            "src/init.rs",
            position(4, 2),
            position(4, 8),
            AnchorPrecision::Exact,
        )
        .unwrap();
        let right = HostProvenance::new(
            right_anchor.clone(),
            vec![HostAuthoredAnchor::new(right_key.clone(), right_anchor)],
        )
        .unwrap();

        let merged = left.merge(right).unwrap();
        assert_eq!(
            merged
                .authored()
                .iter()
                .map(HostAuthoredAnchor::key)
                .collect::<Vec<_>>(),
            [&left_key, &right_key]
        );
        assert_eq!(merged.authored()[1].anchor().display_file(), "src/init.rs");
    }

    #[test]
    fn provenance_merge_keeps_left_invocation() {
        let left_invocation = anchor(AnchorPrecision::Exact);
        let right_invocation = HostSourceAnchor::new(
            "src/init.rs",
            position(4, 2),
            position(4, 8),
            AnchorPrecision::Exact,
        )
        .unwrap();
        let left = HostProvenance::new(
            left_invocation.clone(),
            vec![HostAuthoredAnchor::new(
                ProvenanceKey::new("configuration_declaration", 0).unwrap(),
                left_invocation.clone(),
            )],
        )
        .unwrap();
        let right = HostProvenance::new(
            right_invocation.clone(),
            vec![HostAuthoredAnchor::new(
                ProvenanceKey::new("initializer_declaration", 0).unwrap(),
                right_invocation,
            )],
        )
        .unwrap();

        assert_eq!(left.merge(right).unwrap().invocation(), &left_invocation);
    }

    #[test]
    fn provenance_merge_rejects_duplicate_keys() {
        let duplicate = ProvenanceKey::new("configuration_declaration", 0).unwrap();
        let fragment = || {
            HostProvenance::new(
                anchor(AnchorPrecision::Exact),
                vec![HostAuthoredAnchor::new(
                    duplicate.clone(),
                    anchor(AnchorPrecision::Exact),
                )],
            )
            .unwrap()
        };

        assert_eq!(
            fragment().merge(fragment()),
            Err(HostProvenanceError::DuplicateKey(duplicate))
        );
    }

    #[test]
    fn distinct_roles_and_ordinals_are_retained() {
        let authored = vec![
            HostAuthoredAnchor::new(
                ProvenanceKey::new("rule_pattern", 0).unwrap(),
                anchor(AnchorPrecision::Exact),
            ),
            HostAuthoredAnchor::new(
                ProvenanceKey::new("rule_pattern", 1).unwrap(),
                anchor(AnchorPrecision::InvocationFallback),
            ),
            HostAuthoredAnchor::new(
                ProvenanceKey::new("rule_type", 0).unwrap(),
                anchor(AnchorPrecision::Exact),
            ),
        ];
        let provenance = HostProvenance::new(anchor(AnchorPrecision::Exact), authored).unwrap();
        assert_eq!(provenance.authored().len(), 3);
        assert_eq!(provenance.authored()[1].key().ordinal(), 1);
        assert_eq!(
            provenance.authored()[1].anchor().precision(),
            AnchorPrecision::InvocationFallback
        );
    }
}
