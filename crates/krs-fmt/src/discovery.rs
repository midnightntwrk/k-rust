use std::collections::{BTreeSet, HashSet};
use std::path::{Path, PathBuf};
use std::process::Command;

use serde::Deserialize;

use crate::{FormatError, FormatErrorKind};

#[derive(Deserialize)]
struct Metadata {
    packages: Vec<Package>,
    workspace_members: Vec<String>,
}

#[derive(Deserialize)]
struct Package {
    id: String,
    manifest_path: PathBuf,
}

/// Discovers every Rust source file owned by the selected Cargo workspace.
///
/// Discovery uses Cargo metadata for package membership, recursively walks
/// each member's package directory, excludes generated/build directories,
/// and returns a deterministic path order.
///
/// # Errors
///
/// Returns a discovery diagnostic when Cargo metadata fails, is malformed, or
/// a package directory cannot be read.
pub fn discover_rust_files(manifest_path: Option<&Path>) -> Result<Vec<PathBuf>, FormatError> {
    let mut command = Command::new("cargo");
    command.args(["metadata", "--format-version", "1", "--no-deps"]);
    if let Some(path) = manifest_path {
        command.arg("--manifest-path").arg(path);
    }
    let output = command.output().map_err(|error| {
        FormatError::new(
            FormatErrorKind::Discovery,
            format!("cannot start `cargo metadata`: {error}"),
        )
    })?;
    if !output.status.success() {
        return Err(FormatError::new(
            FormatErrorKind::Discovery,
            format!(
                "`cargo metadata` failed: {}",
                String::from_utf8_lossy(&output.stderr).trim()
            ),
        ));
    }
    let metadata: Metadata = serde_json::from_slice(&output.stdout).map_err(|error| {
        FormatError::new(
            FormatErrorKind::Discovery,
            format!("cannot decode `cargo metadata` output: {error}"),
        )
    })?;
    let members = metadata
        .workspace_members
        .into_iter()
        .collect::<HashSet<_>>();
    let roots = metadata
        .packages
        .into_iter()
        .filter(|package| members.contains(&package.id))
        .filter_map(|package| package.manifest_path.parent().map(Path::to_path_buf))
        .collect::<Vec<_>>();
    expand_paths(&roots)
}

/// Expands explicit Rust files and directories into deterministic file paths.
///
/// Directories named `target`, `build`, or `.git` are excluded at every
/// depth. Non-Rust files are ignored.
///
/// # Errors
///
/// Returns an I/O diagnostic for a missing path or unreadable directory.
pub fn expand_paths(paths: &[PathBuf]) -> Result<Vec<PathBuf>, FormatError> {
    let mut files = BTreeSet::new();
    for path in paths {
        collect_path(path, &mut files)?;
    }
    Ok(files.into_iter().collect())
}

fn collect_path(path: &Path, files: &mut BTreeSet<PathBuf>) -> Result<(), FormatError> {
    let metadata = std::fs::metadata(path).map_err(|error| {
        FormatError::new(
            FormatErrorKind::Io,
            format!("cannot inspect `{}`: {error}", path.display()),
        )
    })?;
    if metadata.is_file() {
        if path.extension().is_some_and(|extension| extension == "rs") {
            files.insert(path.to_path_buf());
        }
        return Ok(());
    }
    if !metadata.is_dir() || excluded(path) {
        return Ok(());
    }
    let mut entries = std::fs::read_dir(path)
        .map_err(|error| {
            FormatError::new(
                FormatErrorKind::Io,
                format!("cannot read directory `{}`: {error}", path.display()),
            )
        })?
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| {
            FormatError::new(
                FormatErrorKind::Io,
                format!("cannot enumerate directory `{}`: {error}", path.display()),
            )
        })?;
    entries.sort_by_key(std::fs::DirEntry::file_name);
    for entry in entries {
        collect_path(&entry.path(), files)?;
    }
    Ok(())
}

fn excluded(path: &Path) -> bool {
    path.file_name()
        .is_some_and(|name| matches!(name.to_str(), Some("target" | "build" | ".git")))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn excluded_directory_names_are_exact() {
        assert!(excluded(Path::new("crate/target")));
        assert!(excluded(Path::new("crate/build")));
        assert!(!excluded(Path::new("crate/src/builders")));
    }
}
