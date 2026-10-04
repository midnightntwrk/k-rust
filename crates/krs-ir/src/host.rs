//! Host-process descriptors emitted by author-facing macros.

use std::any::TypeId;
use std::cmp::Ordering;
use std::collections::{BTreeMap, HashSet};
use std::error::Error;
use std::fmt;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

use crate::transport::detail::{StateCellContentReason, TransportField, TransportItemKind};
use crate::{
    DisplayPath, DisplayPathError, HostDeclarationIdentity, HostHeadRule, ItemKind, ProvenanceRole,
    SchemaVersion, StateTransportError,
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
    /// Returns [`HostProvenanceShapeError`] if either coordinate is zero.
    pub const fn new(line: u32, scalar_column: u32) -> Result<Self, HostProvenanceShapeError> {
        match crate::Position::new(line, scalar_column) {
            Ok(position) => Ok(Self { position }),
            Err(crate::CoordinateError::ZeroLine) => Err(HostProvenanceShapeError::ZeroLine),
            Err(crate::CoordinateError::ZeroColumn) => Err(HostProvenanceShapeError::ZeroColumn),
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
    /// Returns [`HostProvenanceShapeError`] if the display filename is empty or
    /// absolute, or if `end` does not follow `start`.
    pub fn new(
        display_file: impl Into<String>,
        start: HostSourcePosition,
        end: HostSourcePosition,
        precision: AnchorPrecision,
    ) -> Result<Self, HostProvenanceShapeError> {
        let display_file = display_file.into();
        if display_file.trim().is_empty() {
            return Err(HostProvenanceShapeError::EmptyDisplayFile);
        }
        if DisplayPath::is_absolute_spelling(&display_file) {
            return Err(HostProvenanceShapeError::AbsoluteDisplayFile(display_file));
        }
        if end == start {
            return Err(HostProvenanceShapeError::EmptyEndpointRange);
        }
        if end < start {
            return Err(HostProvenanceShapeError::ReversedEndpoints { start, end });
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
    /// Returns [`HostProvenanceShapeError::MissingAuthoredAnchor`] when no semantic
    /// anchor is supplied, or [`HostProvenanceShapeError::DuplicateKey`] when two
    /// anchors would compete for the same shared-parser match. A synthesized
    /// node uses an [`AnchorPrecision::InvocationFallback`] authored anchor
    /// rather than leaving this collection empty.
    pub fn new(
        invocation: HostSourceAnchor,
        authored: Vec<HostAuthoredAnchor>,
    ) -> Result<Self, HostProvenanceShapeError> {
        if authored.is_empty() {
            return Err(HostProvenanceShapeError::MissingAuthoredAnchor);
        }
        let mut keys = HashSet::with_capacity(authored.len());
        for authored_anchor in &authored {
            if !keys.insert(authored_anchor.key.clone()) {
                return Err(HostProvenanceShapeError::DuplicateKey(
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
    /// Returns [`HostProvenanceShapeError::DuplicateKey`] when both fragments claim
    /// the same parser-owned key.
    pub fn merge(self, other: Self) -> Result<Self, HostProvenanceShapeError> {
        let mut authored = self.authored;
        authored.extend(other.authored);
        Self::new(self.invocation, authored)
    }
}

/// One literal source anchor emitted by KRS macros: an index into the
/// provenance file table and one-based, ordered stable-span endpoints.
///
/// Generated descriptor factories construct it inside a `const` block, so an
/// anchor with a zero coordinate, or one that does not end after it starts,
/// is a compile error rather than a runtime failure.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct HostRawAnchor {
    file: usize,
    absolute: bool,
    start: HostSourcePosition,
    end: HostSourcePosition,
    precision: AnchorPrecision,
}

impl HostRawAnchor {
    /// Creates an anchor into entry `file` of its provenance file table.
    ///
    /// `absolute` marks a display filename that is resolved against the Cargo
    /// manifest directory when the provenance is decoded; `exact` is false for
    /// an anchor inherited from its containing invocation.
    ///
    /// # Panics
    ///
    /// Panics if a coordinate is zero or `end` does not follow `start`. In the
    /// `const` block of a generated factory that panic is a compile error.
    #[must_use]
    pub const fn new(
        file: usize,
        absolute: bool,
        start: (u32, u32),
        end: (u32, u32),
        exact: bool,
    ) -> Self {
        let (Ok(start_position), Ok(end_position)) = (
            crate::Position::new(start.0, start.1),
            crate::Position::new(end.0, end.1),
        ) else {
            panic!("KRS source positions are one-based");
        };
        assert!(
            end.0 > start.0 || (end.0 == start.0 && end.1 > start.1),
            "a KRS source anchor must end after it starts"
        );
        Self {
            file,
            absolute,
            start: HostSourcePosition {
                position: start_position,
            },
            end: HostSourcePosition {
                position: end_position,
            },
            precision: if exact {
                AnchorPrecision::Exact
            } else {
                AnchorPrecision::InvocationFallback
            },
        }
    }
}

/// The literal provenance of one generated descriptor factory: its display
/// file table, its invocation anchor, and its authored anchors.
///
/// Generated factories construct it inside a `const` block, so every fact that
/// does not depend on the build machine is checked at compile time.
/// [`Self::decode`] can fail only when an absolute display filename lies outside
/// the factory's Cargo package.
///
/// ```
/// use krs_ir::{HostRawAnchor, HostRawProvenance, ProvenanceRole};
///
/// const ANCHOR: HostRawAnchor = HostRawAnchor::new(0, false, (1, 1), (1, 2), true);
/// let provenance = const {
///     &HostRawProvenance::new(&["src/lib.rs"], ANCHOR, &[(ProvenanceRole::SortDeclaration, 0, ANCHOR)])
/// };
/// assert_eq!(provenance.decode("").unwrap().authored().len(), 1);
/// ```
///
/// Provenance without an authored anchor does not compile:
///
/// ```compile_fail
/// use krs_ir::{HostRawAnchor, HostRawProvenance};
///
/// const ANCHOR: HostRawAnchor = HostRawAnchor::new(0, false, (1, 1), (1, 2), true);
/// const _: HostRawProvenance = HostRawProvenance::new(&["src/lib.rs"], ANCHOR, &[]);
/// ```
#[derive(Clone, Copy, Debug)]
pub struct HostRawProvenance {
    files: &'static [&'static str],
    invocation: HostRawAnchor,
    authored: &'static [(ProvenanceRole, u32, HostRawAnchor)],
}

impl HostRawProvenance {
    /// Checks the literal provenance of one descriptor factory.
    ///
    /// # Panics
    ///
    /// Panics if an anchor names a missing file table entry, a display
    /// filename used by a relative anchor is not
    /// [accepted](Self::accepts_relative_display_file), `authored` is empty, or
    /// two authored anchors share a role and ordinal. In the `const` block of a
    /// generated factory that panic is a compile error.
    #[must_use]
    pub const fn new(
        files: &'static [&'static str],
        invocation: HostRawAnchor,
        authored: &'static [(ProvenanceRole, u32, HostRawAnchor)],
    ) -> Self {
        check_raw_anchor_file(files, invocation);
        assert!(
            !authored.is_empty(),
            "host provenance requires at least one authored anchor"
        );
        let mut index = 0;
        while index < authored.len() {
            let (role, ordinal, anchor) = authored[index];
            check_raw_anchor_file(files, anchor);
            let mut earlier = 0;
            while earlier < index {
                let (earlier_role, earlier_ordinal, _) = authored[earlier];
                assert!(
                    earlier_role as usize != role as usize || earlier_ordinal != ordinal,
                    "two authored anchors share a provenance key"
                );
                earlier += 1;
            }
            index += 1;
        }
        Self {
            files,
            invocation,
            authored,
        }
    }

    /// Reports whether a relative display filename can be stored in a
    /// [`HostSourceAnchor`]: it is not an absolute spelling and contains an
    /// ASCII character that is not white space, so it is not blank.
    #[must_use]
    pub const fn accepts_relative_display_file(spelling: &str) -> bool {
        if DisplayPath::is_absolute_spelling(spelling) {
            return false;
        }
        let bytes = spelling.as_bytes();
        let mut index = 0;
        while index < bytes.len() {
            if bytes[index].is_ascii()
                && !matches!(
                    bytes[index],
                    b'\t' | b'\n' | b'\x0B' | b'\x0C' | b'\r' | b' '
                )
            {
                return true;
            }
            index += 1;
        }
        false
    }

    /// Resolves the display filenames against `manifest_dir` and returns the
    /// validated provenance.
    ///
    /// # Errors
    ///
    /// Returns [`HostProvenanceError`] when an absolute display filename is not
    /// a normalized path inside `manifest_dir`.
    pub fn decode(&self, manifest_dir: &str) -> Result<HostProvenance, HostProvenanceError> {
        let mut resolved = vec![None; self.files.len()];
        let invocation = self.anchor(self.invocation, manifest_dir, &mut resolved)?;
        let mut authored = Vec::with_capacity(self.authored.len());
        for &(role, ordinal, raw) in self.authored {
            authored.push(HostAuthoredAnchor::new(
                ProvenanceKey::new(role, ordinal),
                self.anchor(raw, manifest_dir, &mut resolved)?,
            ));
        }
        // `new` checked that the authored anchors are nonempty and uniquely keyed.
        Ok(HostProvenance {
            invocation,
            authored,
        })
    }

    fn anchor(
        &self,
        raw: HostRawAnchor,
        manifest_dir: &str,
        resolved: &mut [Option<String>],
    ) -> Result<HostSourceAnchor, HostProvenanceError> {
        let display_file = if raw.absolute {
            if let Some(file) = &resolved[raw.file] {
                file.clone()
            } else {
                let file = self.package_relative(self.files[raw.file], manifest_dir)?;
                resolved[raw.file] = Some(file.clone());
                file
            }
        } else {
            self.files[raw.file].to_owned()
        };
        // `HostRawAnchor::new` checked the positions and their order, `new`
        // checked every relative display filename, and `package_relative`
        // checks every resolved one.
        Ok(HostSourceAnchor {
            display_file,
            start: raw.start,
            end: raw.end,
            precision: raw.precision,
        })
    }

    fn package_relative(
        &self,
        display_file: &str,
        manifest_dir: &str,
    ) -> Result<String, HostProvenanceError> {
        let outside_package = |path_error| HostProvenanceError {
            invocation_file: self.files[self.invocation.file].to_owned(),
            invocation_start: self.invocation.start,
            display_file: display_file.to_owned(),
            manifest_dir: manifest_dir.to_owned(),
            path_error,
        };
        let relative = Path::new(display_file)
            .strip_prefix(manifest_dir)
            .map_err(|_| outside_package(None))?
            .to_string_lossy();
        let path = DisplayPath::new(relative.as_ref())
            .map_err(|error| outside_package(Some(Box::new(error))))?;
        // A normalized path can still be blank, such as a single space.
        if path.as_str().trim().is_empty() {
            return Err(outside_package(Some(Box::new(DisplayPathError::Empty(
                relative.into_owned(),
            )))));
        }
        Ok(path.as_str().to_owned())
    }
}

const fn check_raw_anchor_file(files: &[&str], anchor: HostRawAnchor) {
    assert!(
        anchor.file < files.len(),
        "a KRS source anchor names a missing display file"
    );
    assert!(
        anchor.absolute || HostRawProvenance::accepts_relative_display_file(files[anchor.file]),
        "a relative KRS display filename is blank or absolute"
    );
}

/// A descriptor factory's display filename could not be validated within its Cargo package.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct HostProvenanceError {
    /// Display filename of the containing macro invocation.
    pub invocation_file: String,
    /// One-based start position of the containing macro invocation.
    pub invocation_start: HostSourcePosition,
    /// Display filename that could not be resolved within the package.
    pub display_file: String,
    /// Cargo manifest directory captured by the generated factory.
    pub manifest_dir: String,
    /// Validation failure after resolving the package-relative spelling.
    pub path_error: Option<Box<DisplayPathError>>,
}

impl fmt::Display for HostProvenanceError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            invocation_file,
            invocation_start,
            display_file,
            manifest_dir,
            path_error,
        } = self;
        let location = if path_error.is_some() {
            "not a normalized path inside"
        } else {
            "outside"
        };
        write!(
            formatter,
            "display file `{display_file}` is {location} Cargo package `{manifest_dir}` (invocation at {invocation_file}:{invocation_start})"
        )?;
        if let Some(error) = path_error {
            write!(formatter, ": {error}")?;
        }
        Ok(())
    }
}

impl Error for HostProvenanceError {}

/// Invalid pre-materialization provenance data.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum HostProvenanceShapeError {
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

impl fmt::Display for HostProvenanceShapeError {
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

impl Error for HostProvenanceShapeError {}

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
                        field: TransportField::FixedConfigurationDescriptor,
                        expected: TransportItemKind::Configuration,
                        actual: self.id.item_kind(),
                    });
                }
                let Some(HostDeclarationIdentity::Nominal(owner)) = self.declared_type else {
                    return Err(StateTransportError::InvalidCellContent(
                        StateCellContentReason::MissingConfigurationHostOwner,
                    ));
                };
                configuration.validate(owner)
            }
            HostDescriptorPayload::Cell(declaration) => {
                if self.id.item_kind() != ItemKind::Cell {
                    return Err(StateTransportError::ItemKind {
                        field: TransportField::NestedCellDescriptor,
                        expected: TransportItemKind::Cell,
                        actual: self.id.item_kind(),
                    });
                }
                let Some(HostDeclarationIdentity::Nominal(owner)) = self.declared_type else {
                    return Err(StateTransportError::InvalidCellContent(
                        StateCellContentReason::MissingNestedCellHostOwner,
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

/// Build-local payload with an authored head rule.
pub type HostDescriptorPayload = crate::bundle::Payload<crate::HostStage, HostHeadRule>;

/// Build-local host-stage form of [`crate::bundle::SortPayload`].
pub type HostSortDescriptor = crate::bundle::SortPayload<crate::HostStage>;

/// Build-local host-stage form of [`crate::bundle::Constructor`].
pub type HostConstructorDescriptor = crate::bundle::Constructor<crate::HostStage>;

/// Build-local host-stage form of [`crate::bundle::ConstructorField`].
pub type HostConstructorFieldDescriptor = crate::bundle::ConstructorField<crate::HostStage>;

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
            Err(HostProvenanceShapeError::ZeroLine)
        );
        assert_eq!(
            HostSourcePosition::new(1, 0),
            Err(HostProvenanceShapeError::ZeroColumn)
        );
    }

    #[test]
    fn anchors_reject_empty_reversed_and_absolute_locations() {
        let start = position(3, 8);
        let end = position(3, 2);
        assert_eq!(
            HostSourceAnchor::new("src/lib.rs", start, start, AnchorPrecision::Exact),
            Err(HostProvenanceShapeError::EmptyEndpointRange)
        );
        assert!(matches!(
            HostSourceAnchor::new("src/lib.rs", start, end, AnchorPrecision::Exact),
            Err(HostProvenanceShapeError::ReversedEndpoints { .. })
        ));
        for (filename, expected_kind) in [
            ("", HostProvenanceShapeError::EmptyDisplayFile),
            (
                "/tmp/lib.rs",
                HostProvenanceShapeError::AbsoluteDisplayFile("/tmp/lib.rs".to_owned()),
            ),
            (
                r"C:\checkout\lib.rs",
                HostProvenanceShapeError::AbsoluteDisplayFile(r"C:\checkout\lib.rs".to_owned()),
            ),
            (
                r"\\server\lib.rs",
                HostProvenanceShapeError::AbsoluteDisplayFile(r"\\server\lib.rs".to_owned()),
            ),
            (
                r"\lib.rs",
                HostProvenanceShapeError::AbsoluteDisplayFile(r"\lib.rs".to_owned()),
            ),
            (
                "file:relative.rs",
                HostProvenanceShapeError::AbsoluteDisplayFile("file:relative.rs".to_owned()),
            ),
            (
                "file:/lib.rs",
                HostProvenanceShapeError::AbsoluteDisplayFile("file:/lib.rs".to_owned()),
            ),
            (
                "file:",
                HostProvenanceShapeError::AbsoluteDisplayFile("file:".to_owned()),
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
            Err(HostProvenanceShapeError::DuplicateKey(key))
        );
    }

    #[test]
    fn provenance_requires_an_authored_anchor() {
        assert_eq!(
            HostProvenance::new(anchor(AnchorPrecision::Exact), Vec::new()),
            Err(HostProvenanceShapeError::MissingAuthoredAnchor)
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
            Err(HostProvenanceShapeError::DuplicateKey(duplicate))
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

    #[test]
    fn accepted_relative_display_files_form_valid_source_anchors() {
        for byte in 0..=0x7f_u8 {
            let character = char::from(byte);
            let spelling = character.to_string();
            let accepted = HostRawProvenance::accepts_relative_display_file(&spelling);
            assert_eq!(
                accepted,
                !character.is_whitespace() && byte != b'/' && byte != b'\\',
                "{byte:#04x}"
            );
            if accepted {
                assert!(
                    HostSourceAnchor::new(
                        spelling,
                        position(1, 1),
                        position(1, 2),
                        AnchorPrecision::Exact
                    )
                    .is_ok()
                );
            }
        }
        for spelling in [
            "",
            " \t",
            "\u{3000}",
            "/src/lib.rs",
            "C:\\lib.rs",
            "file:lib.rs",
        ] {
            assert!(
                !HostRawProvenance::accepts_relative_display_file(spelling),
                "{spelling:?}"
            );
        }
        assert!(HostRawProvenance::accepts_relative_display_file(
            "src/\u{65e5}\u{672c}.rs"
        ));
    }
}
