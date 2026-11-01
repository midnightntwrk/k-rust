use crate::CommandError;
use serde::Deserialize;
use serde_json::Value;
use std::error::Error;
use std::fmt;
use std::path::Path;

/// The stable subset of `cargo metadata --format-version 1` used by KRS.
#[derive(Clone, Debug, Deserialize)]
pub struct CargoMetadata {
    /// All packages in the resolved graph.
    pub packages: Vec<MetadataPackage>,
    /// Cargo's resolved dependency graph and activated features.
    pub resolve: Option<MetadataResolve>,
    /// Package IDs which are workspace members.
    #[serde(default)]
    pub workspace_members: Vec<String>,
    /// Cargo's workspace root directory, when supplied by Cargo itself.
    #[serde(default)]
    pub workspace_root: Option<String>,
    /// Cargo's resolved target directory, including configuration overrides.
    #[serde(default)]
    pub target_directory: Option<String>,
}

impl CargoMetadata {
    /// Deserialize a Cargo metadata JSON document.
    ///
    /// Unknown Cargo fields are intentionally ignored so this remains a
    /// consumer of format version 1 rather than a mirror of Cargo internals.
    ///
    /// # Errors
    ///
    /// Returns [`MetadataError`] when `bytes` is not a compatible JSON
    /// representation of Cargo metadata format version 1.
    pub fn from_json(bytes: &[u8]) -> Result<Self, MetadataError> {
        serde_json::from_slice(bytes).map_err(MetadataError)
    }
}

pub(crate) fn cargo_metadata(manifest: &Path) -> Result<CargoMetadata, CommandError> {
    cargo_metadata_in(manifest, None)
}

/// [`cargo_metadata`] with Cargo's target directory set to `target` when one is given.
pub(crate) fn cargo_metadata_in(
    manifest: &Path,
    target: Option<&Path>,
) -> Result<CargoMetadata, CommandError> {
    let output = crate::process::run(
        "Cargo metadata",
        crate::cargo::command_in(target)
            .args(["metadata", "--format-version", "1", "--manifest-path"])
            .arg(manifest),
    )?;
    CargoMetadata::from_json(&output.stdout).map_err(CommandError::Metadata)
}

/// One package from a Cargo metadata document.
#[derive(Clone, Debug, Deserialize)]
pub struct MetadataPackage {
    /// Cargo's opaque, build-local package ID.
    pub id: String,
    /// Cargo package name.
    pub name: String,
    /// Cargo package version.
    pub version: String,
    /// Registry or Git source identity. Path packages have no source.
    pub source: Option<String>,
    /// Absolute or metadata-relative path to the package manifest.
    pub manifest_path: String,
    /// Cargo package Rust edition.
    #[serde(default)]
    pub edition: Option<String>,
    /// Package metadata, including `package.metadata.krs`.
    #[serde(default)]
    pub metadata: Value,
    /// Cargo build targets declared by the package.
    #[serde(default)]
    pub targets: Vec<MetadataTarget>,
}

/// Cargo target metadata used for planning and source formatting.
#[derive(Clone, Debug, Deserialize)]
pub struct MetadataTarget {
    /// Cargo's actual target name and resulting Rust crate-root spelling.
    pub name: String,
    /// Rust edition selected for this target.
    #[serde(default)]
    pub edition: Option<String>,
    /// Source file serving as this target's crate root.
    #[serde(default)]
    pub src_path: Option<String>,
    /// Cargo target kinds, such as `lib`, `bin`, or `proc-macro`.
    #[serde(default)]
    pub kind: Vec<String>,
    /// rustc crate types emitted for this target.
    #[serde(default)]
    pub crate_types: Vec<String>,
}

/// Resolved Cargo graph.
#[derive(Clone, Debug, Deserialize)]
pub struct MetadataResolve {
    /// Resolved packages and their dependency edges.
    pub nodes: Vec<MetadataNode>,
}

/// One node in Cargo's resolved graph.
#[derive(Clone, Debug, Deserialize)]
pub struct MetadataNode {
    /// Package ID matching a package in [`CargoMetadata::packages`].
    pub id: String,
    /// Activated feature names for this package.
    #[serde(default)]
    pub features: Vec<String>,
    /// Direct resolved dependency package IDs.
    #[serde(default)]
    pub dependencies: Vec<String>,
    /// The direct dependencies with the crate names this package's sources give them.
    #[serde(default)]
    pub deps: Vec<MetadataNodeDependency>,
}

/// One direct dependency of a resolved node.
#[derive(Clone, Debug, Deserialize)]
pub struct MetadataNodeDependency {
    /// The crate name the dependent's sources use: the dependency's rename, or its library
    /// target's name.
    pub name: String,
    /// Its package ID.
    pub pkg: String,
    /// The kinds of dependency edge Cargo resolved under this name.
    #[serde(default)]
    pub dep_kinds: Vec<MetadataDependencyKind>,
}

impl MetadataNodeDependency {
    /// Whether the dependent's library and binaries, not only its tests, benches or build
    /// script, name the dependency by [`Self::name`]: one of its edges is a normal dependency
    /// (`kind` null). Cargo before 1.41 lists no kinds; a name is then taken as normal.
    #[must_use]
    pub fn is_normal(&self) -> bool {
        self.dep_kinds.is_empty() || self.dep_kinds.iter().any(|kind| kind.kind.is_none())
    }
}

/// One kind of a resolved dependency edge.
#[derive(Clone, Debug, Deserialize)]
pub struct MetadataDependencyKind {
    /// `null` for a normal dependency, `"dev"` or `"build"` otherwise.
    pub kind: Option<String>,
}

/// Invalid Cargo metadata JSON.
#[derive(Debug)]
pub struct MetadataError(serde_json::Error);

impl fmt::Display for MetadataError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "invalid Cargo metadata JSON: {}", self.0)
    }
}

impl Error for MetadataError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        Some(&self.0)
    }
}

#[cfg(test)]
mod tests {
    use super::MetadataNode;

    /// A crate name the library's sources use comes from a normal dependency edge: the same
    /// package renamed as a dev-dependency is named so only in tests.
    #[test]
    fn a_dependency_name_is_normal_only_on_a_normal_edge() {
        let node: MetadataNode = serde_json::from_value(serde_json::json!({
            "id": "root 0.1.0",
            "deps": [
                {"name": "base_in_tests", "pkg": "base 0.1.0", "dep_kinds": [{"kind": "dev", "target": null}]},
                {"name": "semantic_base", "pkg": "base 0.1.0", "dep_kinds": [{"kind": null, "target": null}]},
                {"name": "old_cargo", "pkg": "other 0.1.0"}
            ]
        }))
        .unwrap();
        let normal = node
            .deps
            .iter()
            .filter(|dependency| dependency.is_normal())
            .map(|dependency| dependency.name.as_str())
            .collect::<Vec<_>>();
        assert_eq!(normal, ["semantic_base", "old_cargo"]);
    }
}
