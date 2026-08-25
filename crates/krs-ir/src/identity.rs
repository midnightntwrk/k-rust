//! Machine-independent identities used by serialized descriptors.

use std::error::Error;
use std::fmt;

use serde::{Deserialize, Deserializer, Serialize};

/// Exact source-level visibility of one Rust declaration.
///
/// Restricted visibility retains whether the author wrote the explicit
/// `in` token, so `pub(crate)` and `pub(in crate)` do not collapse in the
/// collector protocol even though rustc gives them the same reachability.
#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "snake_case", tag = "visibility")]
pub enum RustVisibility {
    /// No `pub` token was authored.
    #[default]
    Inherited,
    /// Unrestricted `pub` visibility.
    Public,
    /// Restricted `pub(path)` or `pub(in path)` visibility.
    Restricted {
        /// Canonical Rust path spelling without whitespace.
        path: String,
        /// Whether the source contained the explicit `in` token.
        explicit_in: bool,
    },
}

#[derive(Deserialize)]
#[serde(rename_all = "snake_case", tag = "visibility", deny_unknown_fields)]
enum RustVisibilityWire {
    Inherited,
    Public,
    Restricted { path: String, explicit_in: bool },
}

impl<'de> Deserialize<'de> for RustVisibility {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        match RustVisibilityWire::deserialize(deserializer)? {
            RustVisibilityWire::Inherited => Ok(Self::Inherited),
            RustVisibilityWire::Public => Ok(Self::Public),
            RustVisibilityWire::Restricted { path, explicit_in } => {
                Self::restricted(path, explicit_in).map_err(serde::de::Error::custom)
            }
        }
    }
}

impl RustVisibility {
    /// Creates exact restricted visibility metadata.
    ///
    /// # Errors
    ///
    /// Rejects an empty path, an empty path segment, or filesystem separators.
    pub fn restricted(path: impl Into<String>, explicit_in: bool) -> Result<Self, IdentityError> {
        let path = path.into();
        if path.is_empty() || path.contains(['/', '\\']) || path.split("::").any(str::is_empty) {
            return Err(IdentityError::InvalidVisibilityPath(path));
        }
        Ok(Self::Restricted { path, explicit_in })
    }

    /// Whether this declaration authored unrestricted public visibility.
    #[must_use]
    pub const fn is_public(&self) -> bool {
        matches!(self, Self::Public)
    }

    /// Whether no `pub` token was authored.
    #[must_use]
    pub const fn is_inherited(&self) -> bool {
        matches!(self, Self::Inherited)
    }
}

/// An explicit stable public symbol identity supplied by `#[k::symbol]`.
///
/// This is a logical `::`-separated path, not an emitted backend spelling.
/// The package K namespace remains compiler-owned and is always prepended by
/// the naming pass.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(transparent)]
pub struct ExplicitSymbol(String);

impl ExplicitSymbol {
    /// Validates one author-facing stable symbol identity.
    ///
    /// # Errors
    ///
    /// Rejects empty identities, empty path components, filesystem
    /// separators, and components which are not K/Rust identifier shaped.
    pub fn new(value: impl Into<String>) -> Result<Self, IdentityError> {
        let value = value.into();
        let valid = !value.is_empty()
            && !value.contains(['/', '\\'])
            && value.split("::").all(|component| {
                let mut characters = component.chars();
                characters
                    .next()
                    .is_some_and(|character| character == '_' || character.is_ascii_alphabetic())
                    && characters.all(|character| {
                        character == '_' || character == '-' || character.is_ascii_alphanumeric()
                    })
            });
        if !valid {
            return Err(IdentityError::InvalidExplicitSymbol(value));
        }
        Ok(Self(value))
    }

    /// Returns the logical symbol identity exactly as authored.
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }

    /// Returns its final component, used for the readable emitted K symbol.
    #[must_use]
    pub fn final_component(&self) -> &str {
        self.0.rsplit("::").next().unwrap_or(self.as_str())
    }
}

impl<'de> Deserialize<'de> for ExplicitSymbol {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let value = String::deserialize(deserializer)?;
        Self::new(value).map_err(serde::de::Error::custom)
    }
}

/// A Cargo package in an immutable K semantic namespace.
///
/// `cargo_source` is a locked, logical source identity such as
/// `registry+https://github.com/rust-lang/crates.io-index`, a pinned Git URL,
/// or `workspace`. It must never be an absolute checkout path.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(try_from = "PackageIdWire")]
pub struct PackageId {
    /// Immutable namespace contributed to the final K definition.
    k_namespace: String,
    /// Cargo's package name.
    cargo_name: String,
    /// Locked Cargo package version.
    cargo_version: String,
    /// Stable Cargo source identity, or `workspace` for a workspace package.
    cargo_source: String,
}

impl PackageId {
    /// Creates a package identity after rejecting empty components and paths.
    ///
    /// # Errors
    ///
    /// Returns [`IdentityError`] when a component is empty or `cargo_source`
    /// is an absolute checkout path.
    pub fn new(
        k_namespace: impl Into<String>,
        cargo_name: impl Into<String>,
        cargo_version: impl Into<String>,
        cargo_source: impl Into<String>,
    ) -> Result<Self, IdentityError> {
        let package = Self {
            k_namespace: k_namespace.into(),
            cargo_name: cargo_name.into(),
            cargo_version: cargo_version.into(),
            cargo_source: cargo_source.into(),
        };
        validate_component("k_namespace", &package.k_namespace)?;
        validate_component("cargo_name", &package.cargo_name)?;
        validate_component("cargo_version", &package.cargo_version)?;
        validate_component("cargo_source", &package.cargo_source)?;
        if looks_like_absolute_path(&package.cargo_source) {
            return Err(IdentityError::AbsoluteCargoSource);
        }
        Ok(package)
    }

    /// Returns the immutable K namespace.
    #[must_use]
    pub fn k_namespace(&self) -> &str {
        &self.k_namespace
    }

    /// Returns the Cargo package name.
    #[must_use]
    pub fn cargo_name(&self) -> &str {
        &self.cargo_name
    }

    /// Returns the locked Cargo package version.
    #[must_use]
    pub fn cargo_version(&self) -> &str {
        &self.cargo_version
    }

    /// Returns the stable Cargo source identity.
    #[must_use]
    pub fn cargo_source(&self) -> &str {
        &self.cargo_source
    }
}

#[derive(Deserialize)]
struct PackageIdWire {
    k_namespace: String,
    cargo_name: String,
    cargo_version: String,
    cargo_source: String,
}

impl TryFrom<PackageIdWire> for PackageId {
    type Error = IdentityError;

    fn try_from(wire: PackageIdWire) -> Result<Self, Self::Error> {
        Self::new(
            wire.k_namespace,
            wire.cargo_name,
            wire.cargo_version,
            wire.cargo_source,
        )
    }
}

/// The namespace occupied by an authored or generated declaration.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ItemKind {
    /// An open K sort declaration.
    Sort,
    /// A constructor production.
    Constructor,
    /// An after-the-fact production, subsort, precedence, or associativity
    /// registration. It has no emitted K symbol of its own.
    Grammar,
    /// A complete configuration declaration and its paired initializer.
    Configuration,
    /// A nominal nested fixed-cell group declaration.
    Cell,
    /// A rewrite rule.
    Rule,
    /// An equation.
    Equation,
    /// A simplifier lemma.
    Simplification,
    /// A compile-time alias clause.
    Alias,
    /// A reusable source-level context template.
    ContextAlias,
    /// A reachability or logical claim.
    Claim,
}

/// A stable declaration identity, independent of linker and collection order.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(try_from = "StableItemIdWire")]
pub struct StableItemId {
    /// Package containing the declaration.
    package: PackageId,
    /// Rust module segments below the crate root.
    module_path: Vec<String>,
    /// Rust item name or deterministic generated name.
    item_name: String,
    /// Declaration namespace.
    item_kind: ItemKind,
    /// Stable same-scope disambiguator; empty for ordinary named items.
    disambiguator: String,
}

impl StableItemId {
    /// Creates and validates a declaration identity.
    ///
    /// # Errors
    ///
    /// Returns [`IdentityError`] when the item name is empty or a module or
    /// disambiguator contains a filesystem or module-path separator.
    pub fn new(
        package: PackageId,
        module_path: impl IntoIterator<Item = impl Into<String>>,
        item_name: impl Into<String>,
        item_kind: ItemKind,
        disambiguator: impl Into<String>,
    ) -> Result<Self, IdentityError> {
        let module_path = module_path.into_iter().map(Into::into).collect::<Vec<_>>();
        for component in &module_path {
            validate_component("module_path", component)?;
            if component.contains("::") || component.contains(['/', '\\']) {
                return Err(IdentityError::InvalidModuleComponent(component.clone()));
            }
        }
        let item_name = item_name.into();
        validate_component("item_name", &item_name)?;
        let disambiguator = disambiguator.into();
        if disambiguator.contains(['/', '\\']) {
            return Err(IdentityError::InvalidDisambiguator(disambiguator));
        }
        Ok(Self {
            package,
            module_path,
            item_name,
            item_kind,
            disambiguator,
        })
    }

    /// Returns the package containing this item.
    #[must_use]
    pub fn package(&self) -> &PackageId {
        &self.package
    }

    /// Returns module segments below the crate root.
    #[must_use]
    pub fn module_path(&self) -> &[String] {
        &self.module_path
    }

    /// Returns the Rust item or generated item name.
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

#[derive(Deserialize)]
struct StableItemIdWire {
    package: PackageId,
    module_path: Vec<String>,
    item_name: String,
    item_kind: ItemKind,
    disambiguator: String,
}

impl TryFrom<StableItemIdWire> for StableItemId {
    type Error = IdentityError;

    fn try_from(wire: StableItemIdWire) -> Result<Self, Self::Error> {
        Self::new(
            wire.package,
            wire.module_path,
            wire.item_name,
            wire.item_kind,
            wire.disambiguator,
        )
    }
}

/// A lowercase hexadecimal SHA-256 digest.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(transparent)]
pub struct Sha256Digest(String);

impl Sha256Digest {
    /// Parses exactly 64 lowercase hexadecimal characters.
    ///
    /// # Errors
    ///
    /// Returns [`IdentityError::InvalidSha256`] for any other representation.
    pub fn new(hex: impl Into<String>) -> Result<Self, IdentityError> {
        let hex = hex.into();
        if hex.len() != 64
            || !hex
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
        {
            return Err(IdentityError::InvalidSha256);
        }
        Ok(Self(hex))
    }

    /// Returns the lowercase hexadecimal digest.
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl TryFrom<String> for Sha256Digest {
    type Error = IdentityError;

    fn try_from(hex: String) -> Result<Self, Self::Error> {
        Self::new(hex)
    }
}

impl<'de> Deserialize<'de> for Sha256Digest {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let hex = String::deserialize(deserializer)?;
        Self::new(hex).map_err(serde::de::Error::custom)
    }
}

/// Stable identity of a source file, without a machine-specific prefix.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(try_from = "SourceFileIdWire")]
pub struct SourceFileId {
    /// Package owning the source file.
    package: PackageId,
    /// Normalized, slash-separated path relative to the package root.
    package_relative_path: String,
    /// Identity of the exact file contents.
    content_sha256: Sha256Digest,
}

impl SourceFileId {
    /// Creates a source identity and normalizes `\\` separators to `/`.
    ///
    /// # Errors
    ///
    /// Returns [`IdentityError::InvalidSourcePath`] when the path is empty,
    /// absolute, contains empty components, or can escape the package root.
    pub fn new(
        package: PackageId,
        package_relative_path: impl Into<String>,
        content_sha256: Sha256Digest,
    ) -> Result<Self, IdentityError> {
        let package_relative_path = package_relative_path.into().replace('\\', "/");
        if package_relative_path.is_empty()
            || package_relative_path.starts_with('/')
            || package_relative_path
                .split('/')
                .any(|part| part.is_empty() || part == "." || part == "..")
            || looks_like_windows_absolute_path(&package_relative_path)
        {
            return Err(IdentityError::InvalidSourcePath(package_relative_path));
        }
        Ok(Self {
            package,
            package_relative_path,
            content_sha256,
        })
    }

    /// Returns the package owning the file.
    #[must_use]
    pub fn package(&self) -> &PackageId {
        &self.package
    }

    /// Returns the normalized path relative to the package root.
    #[must_use]
    pub fn package_relative_path(&self) -> &str {
        &self.package_relative_path
    }

    /// Returns the identity of the exact file contents.
    #[must_use]
    pub fn content_sha256(&self) -> &Sha256Digest {
        &self.content_sha256
    }
}

#[derive(Deserialize)]
struct SourceFileIdWire {
    package: PackageId,
    package_relative_path: String,
    content_sha256: Sha256Digest,
}

impl TryFrom<SourceFileIdWire> for SourceFileId {
    type Error = IdentityError;

    fn try_from(wire: SourceFileIdWire) -> Result<Self, Self::Error> {
        Self::new(
            wire.package,
            wire.package_relative_path,
            wire.content_sha256,
        )
    }
}

/// A rejected stable-identity component.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum IdentityError {
    /// A required component was empty.
    EmptyComponent(&'static str),
    /// Cargo source identity looked like an absolute host path.
    AbsoluteCargoSource,
    /// A Rust module component contained a separator.
    InvalidModuleComponent(String),
    /// An item disambiguator contained a filesystem separator.
    InvalidDisambiguator(String),
    /// A source path was not normalized and package-relative.
    InvalidSourcePath(String),
    /// A restricted Rust visibility path was malformed.
    InvalidVisibilityPath(String),
    /// An explicit stable public symbol was malformed.
    InvalidExplicitSymbol(String),
    /// A content digest was not lowercase hexadecimal SHA-256.
    InvalidSha256,
}

impl fmt::Display for IdentityError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyComponent(component) => {
                write!(formatter, "identity component `{component}` is empty")
            }
            Self::AbsoluteCargoSource => {
                formatter.write_str("Cargo source identity must not be an absolute checkout path")
            }
            Self::InvalidModuleComponent(component) => {
                write!(formatter, "invalid module component `{component}`")
            }
            Self::InvalidDisambiguator(value) => {
                write!(formatter, "invalid item disambiguator `{value}`")
            }
            Self::InvalidSourcePath(path) => write!(
                formatter,
                "source path `{path}` is not normalized and package-relative"
            ),
            Self::InvalidVisibilityPath(path) => {
                write!(formatter, "invalid restricted visibility path `{path}`")
            }
            Self::InvalidExplicitSymbol(value) => {
                write!(formatter, "invalid explicit stable symbol `{value}`")
            }
            Self::InvalidSha256 => {
                formatter.write_str("SHA-256 digest must be 64 lowercase hexadecimal characters")
            }
        }
    }
}

impl Error for IdentityError {}

fn validate_component(name: &'static str, value: &str) -> Result<(), IdentityError> {
    if value.is_empty() {
        Err(IdentityError::EmptyComponent(name))
    } else {
        Ok(())
    }
}

fn looks_like_absolute_path(value: &str) -> bool {
    value.starts_with('/') || looks_like_windows_absolute_path(value)
}

fn looks_like_windows_absolute_path(value: &str) -> bool {
    let bytes = value.as_bytes();
    bytes.len() >= 3
        && bytes[0].is_ascii_alphabetic()
        && bytes[1] == b':'
        && matches!(bytes[2], b'/' | b'\\')
}

#[cfg(test)]
mod tests {
    use super::*;

    fn package(namespace: &str, name: &str) -> PackageId {
        PackageId::new(namespace, name, "1.0.0", "workspace").unwrap()
    }

    #[test]
    fn same_spelling_in_distinct_modules_and_packages_is_distinct() {
        let package_a = package("ORG-A", "semantics-a");
        let package_b = package("ORG-B", "semantics-b");
        let root =
            StableItemId::new(package_a.clone(), ["expr"], "Value", ItemKind::Sort, "").unwrap();
        let nested =
            StableItemId::new(package_a, ["nested", "expr"], "Value", ItemKind::Sort, "").unwrap();
        let dependency =
            StableItemId::new(package_b, ["expr"], "Value", ItemKind::Sort, "").unwrap();

        assert_ne!(root, nested);
        assert_ne!(root, dependency);
        assert_ne!(nested, dependency);
    }

    #[test]
    fn source_paths_are_normalized_and_cannot_escape_package() {
        let digest = Sha256Digest::new("a".repeat(64)).unwrap();
        let source =
            SourceFileId::new(package("ORG-A", "a"), "src\\nested\\mod.rs", digest.clone())
                .unwrap();
        assert_eq!(source.package_relative_path(), "src/nested/mod.rs");
        assert!(SourceFileId::new(package("ORG-A", "a"), "../outside.rs", digest).is_err());
    }

    #[test]
    fn absolute_checkout_path_is_not_a_package_identity() {
        assert_eq!(
            PackageId::new("ORG-A", "a", "1.0.0", "/tmp/checkout"),
            Err(IdentityError::AbsoluteCargoSource)
        );
    }

    #[test]
    fn deserialization_cannot_bypass_identity_validation() {
        let absolute_source = r#"{
            "k_namespace":"ORG-A",
            "cargo_name":"a",
            "cargo_version":"1.0.0",
            "cargo_source":"/tmp/checkout"
        }"#;
        assert!(serde_json::from_str::<PackageId>(absolute_source).is_err());
        assert!(serde_json::from_str::<Sha256Digest>(r#""NOT-A-DIGEST""#).is_err());
    }
}
