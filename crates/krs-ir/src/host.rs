//! Host-process descriptors emitted by author-facing macros.

use std::any::TypeId;
use std::cmp::Ordering;
use std::collections::{BTreeMap, HashSet};
use std::error::Error;
use std::fmt;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

use crate::{
    DisplayPath, HostCellDeclaration, HostConfigurationRule, HostContextAlias,
    HostDeclarationIdentity, HostFixedConfiguration, HostGrammarDescriptor, HostHeadRule,
    HostStructuredRuleDescriptor, ItemKind, ProvenanceRole, SchemaVersion, StateTransportError,
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
    position: crate::Position,
}

impl HostSourcePosition {
    /// Creates a one-based stable-span position.
    ///
    /// # Errors
    ///
    /// Returns [`HostProvenanceError`] if either coordinate is zero.
    pub const fn new(line: u32, scalar_column: u32) -> Result<Self, HostProvenanceError> {
        match crate::Position::new(line, scalar_column) {
            Ok(position) => Ok(Self { position }),
            Err(crate::CoordinateError::ZeroLine) => Err(HostProvenanceError::ZeroLine),
            Err(crate::CoordinateError::ZeroColumn) => Err(HostProvenanceError::ZeroColumn),
            Err(_) => unreachable!(),
        }
    }

    /// Returns the one-based source line.
    #[must_use]
    pub const fn line(self) -> u32 {
        self.position.line()
    }

    /// Returns the one-based Unicode-scalar column.
    #[must_use]
    pub const fn scalar_column(self) -> u32 {
        self.position.scalar_column()
    }
}

impl fmt::Display for HostSourcePosition {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}:{}", self.line(), self.scalar_column())
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
        if DisplayPath::is_absolute_spelling(&display_file) {
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
#[derive(Clone, Debug, Eq, Hash, PartialEq, Serialize, Deserialize)]
#[serde(try_from = "ProvenanceKeyWire")]
pub struct ProvenanceKey {
    role: ProvenanceRole,
    ordinal: u32,
}

#[derive(Deserialize)]
struct ProvenanceKeyWire {
    role: String,
    ordinal: u32,
}

impl TryFrom<ProvenanceKeyWire> for ProvenanceKey {
    type Error = String;

    fn try_from(wire: ProvenanceKeyWire) -> Result<Self, Self::Error> {
        let role = ProvenanceRole::from_spelling(&wire.role)
            .ok_or_else(|| format!("unknown provenance role `{}`", wire.role))?;
        Ok(Self::new(role, wire.ordinal))
    }
}

impl ProvenanceKey {
    /// Creates a semantic role and same-role invocation ordinal.
    #[must_use]
    pub const fn new(role: ProvenanceRole, ordinal: u32) -> Self {
        Self { role, ordinal }
    }

    /// Returns the parser-defined semantic role.
    #[must_use]
    pub const fn role(&self) -> ProvenanceRole {
        self.role
    }

    /// Returns the zero-based occurrence within this invocation and role.
    #[must_use]
    pub const fn ordinal(&self) -> u32 {
        self.ordinal
    }
}

impl Ord for ProvenanceKey {
    fn cmp(&self, other: &Self) -> Ordering {
        (self.role.as_str(), self.ordinal).cmp(&(other.role.as_str(), other.ordinal))
    }
}

impl PartialOrd for ProvenanceKey {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
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
                    "host source endpoint {end} precedes start {start}"
                )
            }
            Self::MissingAuthoredAnchor => {
                formatter.write_str("host provenance requires at least one authored anchor")
            }
            Self::DuplicateKey(key) => write!(
                formatter,
                "duplicate provenance key `{}#{}`",
                key.role.as_str(),
                key.ordinal
            ),
        }
    }
}

impl Error for HostProvenanceError {}

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
    pub protocol_version: SchemaVersion,
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
    /// Validates configuration/cell/rule ownership and host joins.
    ///
    /// # Errors
    ///
    /// Returns [`StateTransportError`] when a configuration payload is registered
    /// under the wrong item kind, lacks its nominal declaration key, or has an
    /// invalid configuration/cell/rule shape.
    pub fn validate_state_ownership(&self) -> Result<(), StateTransportError> {
        match &self.payload {
            HostDescriptorPayload::FixedConfiguration(configuration) => {
                if self.id.item_kind() != ItemKind::Configuration {
                    return Err(StateTransportError::ItemKind {
                        field: "fixed configuration descriptor",
                        expected: "Configuration",
                        actual: self.id.item_kind(),
                    });
                }
                let Some(HostDeclarationIdentity::Nominal(owner)) = self.declared_type else {
                    return Err(StateTransportError::InvalidCellContent(
                        "fixed configuration lacks a nominal host owner",
                    ));
                };
                configuration.validate(owner)
            }
            HostDescriptorPayload::Cell(declaration) => {
                if self.id.item_kind() != ItemKind::Cell {
                    return Err(StateTransportError::ItemKind {
                        field: "nested cell descriptor",
                        expected: "Cell",
                        actual: self.id.item_kind(),
                    });
                }
                let Some(HostDeclarationIdentity::Nominal(owner)) = self.declared_type else {
                    return Err(StateTransportError::InvalidCellContent(
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
    /// Typed after-the-fact grammar registration.
    Grammar(Box<HostGrammarDescriptor>),
    /// Fully structured relational sentence.
    StructuredRule(Box<HostStructuredRuleDescriptor>),
    /// Complete fixed configuration and initializer.
    FixedConfiguration(Box<HostFixedConfiguration>),
    /// Nominal nested fixed-cell declaration.
    Cell(Box<HostCellDeclaration>),
    /// Simultaneous whole-configuration rule.
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

#[cfg(test)]
mod tests {
    use super::*;

    fn test_type_id() -> TypeId {
        TypeId::of::<u8>()
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
                key: ProvenanceKey::new(ProvenanceRole::ConstructorSort, 0),
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
        for (filename, expected_kind) in [
            ("", HostProvenanceError::EmptyDisplayFile),
            (
                "/tmp/lib.rs",
                HostProvenanceError::AbsoluteDisplayFile("/tmp/lib.rs".to_owned()),
            ),
            (
                r"C:\checkout\lib.rs",
                HostProvenanceError::AbsoluteDisplayFile(r"C:\checkout\lib.rs".to_owned()),
            ),
            (
                r"\\server\lib.rs",
                HostProvenanceError::AbsoluteDisplayFile(r"\\server\lib.rs".to_owned()),
            ),
            (
                r"\lib.rs",
                HostProvenanceError::AbsoluteDisplayFile(r"\lib.rs".to_owned()),
            ),
            (
                "file:relative.rs",
                HostProvenanceError::AbsoluteDisplayFile("file:relative.rs".to_owned()),
            ),
            (
                "file:/lib.rs",
                HostProvenanceError::AbsoluteDisplayFile("file:/lib.rs".to_owned()),
            ),
            (
                "file:",
                HostProvenanceError::AbsoluteDisplayFile("file:".to_owned()),
            ),
        ] {
            let error = HostSourceAnchor::new(
                filename,
                position(1, 1),
                position(1, 2),
                AnchorPrecision::Exact,
            )
            .unwrap_err();
            assert_eq!(error, expected_kind, "{filename}");
        }
        assert!(
            HostSourceAnchor::new(
                "../lib.rs",
                position(1, 1),
                position(1, 2),
                AnchorPrecision::Exact
            )
            .is_ok()
        );
    }

    #[test]
    fn provenance_keys_are_unique_within_authored_anchors() {
        let key = ProvenanceKey::new(ProvenanceRole::RulePattern, 0);
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
        let left_key = ProvenanceKey::new(ProvenanceRole::ConfigurationDeclaration, 0);
        let right_key = ProvenanceKey::new(ProvenanceRole::InitializerDeclaration, 0);
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
                ProvenanceKey::new(ProvenanceRole::ConfigurationDeclaration, 0),
                left_invocation.clone(),
            )],
        )
        .unwrap();
        let right = HostProvenance::new(
            right_invocation.clone(),
            vec![HostAuthoredAnchor::new(
                ProvenanceKey::new(ProvenanceRole::InitializerDeclaration, 0),
                right_invocation,
            )],
        )
        .unwrap();

        assert_eq!(left.merge(right).unwrap().invocation(), &left_invocation);
    }

    #[test]
    fn provenance_merge_rejects_duplicate_keys() {
        let duplicate = ProvenanceKey::new(ProvenanceRole::ConfigurationDeclaration, 0);
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
                ProvenanceKey::new(ProvenanceRole::RulePattern, 0),
                anchor(AnchorPrecision::Exact),
            ),
            HostAuthoredAnchor::new(
                ProvenanceKey::new(ProvenanceRole::RulePattern, 1),
                anchor(AnchorPrecision::InvocationFallback),
            ),
            HostAuthoredAnchor::new(
                ProvenanceKey::new(ProvenanceRole::RuleType, 0),
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

    #[test]
    fn provenance_key_uses_spelling_order_and_rejects_unknown_roles() {
        let payload = ProvenanceKey::new(ProvenanceRole::RuleLeftCellsPayload, 0);
        let field = ProvenanceKey::new(ProvenanceRole::RuleLeftCellsField, 0);
        assert!(field < payload);
        assert_eq!(
            serde_json::to_string(&field).unwrap(),
            r#"{"role":"rule_left_cells_field","ordinal":0}"#
        );
        let error = serde_json::from_str::<ProvenanceKey>(r#"{"role":"unknown_role","ordinal":0}"#)
            .unwrap_err();
        assert!(
            error
                .to_string()
                .contains("unknown provenance role `unknown_role`")
        );
    }
}
