use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use krs_fmt::Edition;

use crate::metadata::{CargoMetadata, MetadataPackage};

/// One Rust file and its Cargo-selected edition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FormatInput {
    /// Rust source path:
    /// canonical for workspace discovery,
    /// and under the caller's spelling for explicit paths.
    pub path: PathBuf,
    /// Edition selected by the owning Cargo target or package.
    pub edition: Edition,
}

/// Discovers Rust files from workspace targets or explicit paths.
///
/// Without paths, every workspace member target contributes the `.rs` files
/// under the directory of its crate root.
/// Explicit files and directories are expanded the same way and must belong to a workspace member.
/// A walk never enters `.git`, Cargo's target directory, or a directory holding another package's `Cargo.toml`.
/// Each file takes the edition of the target whose source directory most specifically contains it.
///
/// # Errors
///
/// Returns a diagnostic for Cargo metadata, path traversal, or ownership failures.
pub fn discover_format_inputs(
    manifest_path: Option<&Path>,
    paths: &[PathBuf],
) -> Result<Vec<FormatInput>, String> {
    let metadata = load_metadata(manifest_path)?;
    let members = metadata.workspace_members.iter().collect::<BTreeSet<_>>();
    let packages = metadata
        .packages
        .iter()
        .filter(|package| members.contains(&package.id))
        .map(|package| {
            let root = Path::new(&package.manifest_path)
                .parent()
                .ok_or_else(|| format!("invalid manifest path `{}`", package.manifest_path))?;
            Ok((canonical(root)?, package))
        })
        .collect::<Result<BTreeMap<_, _>, String>>()?;
    let target_directory = metadata
        .target_directory
        .as_deref()
        .map(|path| canonical_or_normalized(Path::new(path)))
        .transpose()?;

    if paths.is_empty() {
        let mut selected = BTreeMap::new();
        for (package_root, package) in &packages {
            for target in &package.targets {
                let Some(source) = &target.src_path else {
                    continue;
                };
                let source = canonical(Path::new(source))?;
                let root = source.parent().ok_or_else(|| {
                    format!("target source has no parent: `{}`", source.display())
                })?;
                let edition = target_edition(package, target.edition.as_deref())?;
                let mut files = BTreeSet::new();
                walk(root, package_root, target_directory.as_deref(), &mut files)?;
                for file in files {
                    // A more specific target source directory selects the edition.
                    // Equal directories use Cargo's target order.
                    let specificity = root.components().count();
                    let entry = selected.entry(file).or_insert((0, edition));
                    if specificity > entry.0 {
                        *entry = (specificity, edition);
                    }
                }
            }
        }
        return Ok(selected
            .into_iter()
            .map(|(path, (_, edition))| FormatInput { path, edition })
            .collect());
    }

    // Ownership is resolved on canonical paths; files keep the caller's spelling.
    let mut files = BTreeMap::new();
    for path in paths {
        let root = canonical(path)?;
        let package_root = nearest_manifest_root(&root);
        let allowed_root = package_root.as_deref().unwrap_or(&root);
        let mut found = BTreeSet::new();
        walk(&root, allowed_root, target_directory.as_deref(), &mut found)?;
        for file in found {
            let spelled = match file.strip_prefix(&root) {
                Ok(relative) if !relative.as_os_str().is_empty() => path.join(relative),
                _ => path.clone(),
            };
            files.entry(file).or_insert(spelled);
        }
    }
    files
        .into_iter()
        .map(|(canonical_path, path)| {
            let root = nearest_manifest_root(&canonical_path);
            let package = root.as_ref().and_then(|root| packages.get(root));
            let Some(package) = package else {
                return Err(format!(
                    "`{}` is not owned by a workspace package; pass --manifest-path of the workspace that owns it",
                    path.display()
                ));
            };
            let mut edition = target_edition(package, None)?;
            let mut specificity = 0;
            for target in &package.targets {
                let Some(source) = &target.src_path else { continue };
                let source = canonical(Path::new(source))?;
                let Some(root) = source.parent() else { continue };
                if canonical_path.starts_with(root) && root.components().count() > specificity {
                    specificity = root.components().count();
                    edition = target_edition(package, target.edition.as_deref())?;
                }
            }
            Ok(FormatInput { path, edition })
        })
        .collect()
}

fn load_metadata(manifest_path: Option<&Path>) -> Result<CargoMetadata, String> {
    let mut command = crate::cargo::command();
    command.args(["metadata", "--format-version", "1", "--no-deps"]);
    if let Some(manifest) = manifest_path {
        let manifest = canonical(manifest)?;
        command.current_dir(
            manifest
                .parent()
                .ok_or("manifest has no parent directory")?,
        );
        command.arg("--manifest-path").arg(manifest);
    }
    let output = command
        .output()
        .map_err(|error| format!("cannot start `cargo metadata`: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "`cargo metadata` failed: {}",
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    CargoMetadata::from_json(&output.stdout)
        .map_err(|error| format!("cannot decode `cargo metadata` output: {error}"))
}

fn target_edition(package: &MetadataPackage, target: Option<&str>) -> Result<Edition, String> {
    target
        .or(package.edition.as_deref())
        // Cargo's edition for a manifest that names none.
        .unwrap_or("2015")
        .parse()
}

fn canonical(path: &Path) -> Result<PathBuf, String> {
    path.canonicalize()
        .map_err(|error| format!("cannot inspect `{}`: {error}", path.display()))
}

fn canonical_or_normalized(path: &Path) -> Result<PathBuf, String> {
    if path.exists() {
        return canonical(path);
    }
    let parent = path
        .parent()
        .ok_or_else(|| format!("invalid path `{}`", path.display()))?;
    let name = path
        .file_name()
        .ok_or_else(|| format!("invalid path `{}`", path.display()))?;
    Ok(canonical_or_normalized(parent)?.join(name))
}

fn nearest_manifest_root(path: &Path) -> Option<PathBuf> {
    let start = if path.is_dir() { path } else { path.parent()? };
    start
        .ancestors()
        .find(|dir| dir.join("Cargo.toml").is_file())
        .map(Path::to_path_buf)
}

fn walk(
    path: &Path,
    package_root: &Path,
    target_directory: Option<&Path>,
    files: &mut BTreeSet<PathBuf>,
) -> Result<(), String> {
    let metadata = std::fs::metadata(path)
        .map_err(|error| format!("cannot inspect `{}`: {error}", path.display()))?;
    if metadata.is_file() {
        if path.extension().is_some_and(|extension| extension == "rs") {
            files.insert(path.to_path_buf());
        }
        return Ok(());
    }
    if !metadata.is_dir()
        || path.file_name().is_some_and(|name| name == ".git")
        || target_directory.is_some_and(|target| path == target)
        || (path != package_root && path.join("Cargo.toml").is_file())
    {
        return Ok(());
    }
    let mut entries = std::fs::read_dir(path)
        .map_err(|error| format!("cannot read directory `{}`: {error}", path.display()))?
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| format!("cannot enumerate directory `{}`: {error}", path.display()))?;
    entries.sort_by_key(std::fs::DirEntry::file_name);
    for entry in entries {
        let child = entry.path();
        if entry.file_type().is_ok_and(|kind| kind.is_symlink()) {
            continue;
        }
        walk(&child, package_root, target_directory, files)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::fs;

    use krs_test_support::temp_dir;

    use super::*;

    #[test]
    fn target_walk_uses_editions_and_excludes_nested_crates() {
        let temporary = temp_dir();
        let root = temporary.path();
        fs::create_dir_all(root.join("src/build")).unwrap();
        fs::create_dir_all(root.join("tests/fixtures/nested/src")).unwrap();
        fs::write(
            root.join("Cargo.toml"),
            "[package]\nname = \"format-discovery\"\nversion = \"0.1.0\"\nedition = \"2021\"\n[workspace]\n",
        )
        .unwrap();
        fs::write(root.join("src/lib.rs"), "mod build;\n").unwrap();
        fs::write(root.join("src/build/mod.rs"), "pub fn build() {}\n").unwrap();
        fs::write(root.join("build.rs"), "fn main() {}\n").unwrap();
        fs::write(
            root.join("tests/fixtures/nested/Cargo.toml"),
            "[package]\nname = \"nested\"\nversion = \"0.1.0\"\nedition = \"2024\"\n[workspace]\n",
        )
        .unwrap();
        fs::write(
            root.join("tests/fixtures/nested/src/lib.rs"),
            "pub fn nested() {}\n",
        )
        .unwrap();

        let files = discover_format_inputs(Some(&root.join("Cargo.toml")), &[]).unwrap();
        let expected = [
            root.join("build.rs"),
            root.join("src/build/mod.rs"),
            root.join("src/lib.rs"),
        ]
        .into_iter()
        .collect::<BTreeSet<_>>();
        assert_eq!(
            files
                .iter()
                .map(|file| file.path.clone())
                .collect::<BTreeSet<_>>(),
            expected
        );
        assert!(files.iter().all(|file| file.edition == Edition::E2021));

        let explicit = discover_format_inputs(
            Some(&root.join("Cargo.toml")),
            &[root.join("src/build/mod.rs")],
        )
        .unwrap();
        assert_eq!(explicit[0].path, root.join("src/build/mod.rs"));
        assert_eq!(explicit[0].edition, Edition::E2021);
        let error = discover_format_inputs(
            Some(&root.join("Cargo.toml")),
            &[root.join("tests/fixtures/nested/src/lib.rs")],
        )
        .unwrap_err();
        assert!(error.contains("nested/src/lib.rs"));
        assert!(error.contains("--manifest-path"));
    }
}
