use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use krs_fmt::Edition;
use syn::ext::IdentExt as _;

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
/// Without paths, every workspace member target contributes its crate root
/// and the files of its out-of-line modules, as `cargo fmt` selects them:
/// `mod name;` resolves to `name.rs` or `name/mod.rs` by Rust's module path rules,
/// including `#[path]` and inline module nesting.
/// Other files near a target, such as test fixtures, are not inputs,
/// and a file that does not parse is an input whose modules are not followed.
/// An explicit file must be a `.rs` file of a workspace member.
/// An explicit directory is walked through every workspace member it contains,
/// never entering another package's directory,
/// and contributes only the files owned by a workspace member;
/// a directory that contributes none is an error.
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
        for package in packages.values() {
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
                module_files(&source, &mut files)?;
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
        if root.is_file() {
            if root.extension().is_none_or(|extension| extension != "rs") {
                return Err(format!("`{}` is not a Rust source file", path.display()));
            }
            let Some(edition) = explicit_edition(&root, &packages)? else {
                return Err(format!(
                    "`{}` is not owned by a workspace package; pass --manifest-path of the workspace that owns it",
                    path.display()
                ));
            };
            files.entry(root).or_insert(FormatInput {
                path: path.clone(),
                edition,
            });
            continue;
        }
        let mut found = BTreeSet::new();
        let enter = |directory: &Path| directory == root || packages.contains_key(directory);
        walk(&root, &enter, target_directory.as_deref(), &mut found)?;
        let mut owned = 0_usize;
        for file in found {
            // Files of no workspace member, such as a virtual workspace root's fixtures, are not inputs.
            let Some(edition) = explicit_edition(&file, &packages)? else {
                continue;
            };
            owned += 1;
            let spelled = match file.strip_prefix(&root) {
                Ok(relative) => path.join(relative),
                Err(_) => file.clone(),
            };
            files.entry(file).or_insert(FormatInput {
                path: spelled,
                edition,
            });
        }
        if owned == 0 {
            return Err(format!(
                "`{}` holds no Rust file owned by a workspace package; pass --manifest-path of the workspace that owns it",
                path.display()
            ));
        }
    }
    Ok(files.into_values().collect())
}

/// Returns the edition of the workspace member owning `file`,
/// taken from the member target whose source directory most specifically contains it.
fn explicit_edition(
    file: &Path,
    packages: &BTreeMap<PathBuf, &MetadataPackage>,
) -> Result<Option<Edition>, String> {
    let Some(package) = nearest_manifest_root(file)
        .as_ref()
        .and_then(|root| packages.get(root))
    else {
        return Ok(None);
    };
    let mut edition = target_edition(package, None)?;
    let mut specificity = 0;
    for target in &package.targets {
        let Some(source) = &target.src_path else {
            continue;
        };
        let source = canonical(Path::new(source))?;
        let Some(root) = source.parent() else {
            continue;
        };
        if file.starts_with(root) && root.components().count() > specificity {
            specificity = root.components().count();
            edition = target_edition(package, target.edition.as_deref())?;
        }
    }
    Ok(Some(edition))
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

/// Collects `crate_root` and every file reachable from it through out-of-line module declarations.
fn module_files(crate_root: &Path, files: &mut BTreeSet<PathBuf>) -> Result<(), String> {
    let directory = crate_root
        .parent()
        .ok_or_else(|| format!("target source has no parent: `{}`", crate_root.display()))?;
    // A crate root owns its directory, like a `mod.rs` file.
    module_file(crate_root, &ModuleDirectory::owned(directory), files)
}

/// Where the out-of-line modules declared in one module scope live.
struct ModuleDirectory {
    path: PathBuf,
    /// The file stem of a non-`mod.rs` module file, whose child modules live under that stem.
    relative: Option<String>,
}

impl ModuleDirectory {
    fn owned(path: &Path) -> Self {
        Self {
            path: path.to_path_buf(),
            relative: None,
        }
    }

    /// The directory holding the scope's `mod name;` files when no `#[path]` applies.
    fn children(&self) -> PathBuf {
        match &self.relative {
            Some(relative) => self.path.join(relative),
            None => self.path.clone(),
        }
    }
}

fn module_file(
    file: &Path,
    directory: &ModuleDirectory,
    files: &mut BTreeSet<PathBuf>,
) -> Result<(), String> {
    let file = canonical(file)?;
    if !files.insert(file.clone()) {
        return Ok(());
    }
    let source = std::fs::read_to_string(&file)
        .map_err(|error| format!("cannot read `{}`: {error}", file.display()))?;
    // The formatter reports the parse error; there are no declarations to follow.
    let Ok(parsed) = syn::parse_file(&source) else {
        return Ok(());
    };
    module_items(&file, &parsed.items, directory, files)
}

fn module_items(
    file: &Path,
    items: &[syn::Item],
    directory: &ModuleDirectory,
    files: &mut BTreeSet<PathBuf>,
) -> Result<(), String> {
    for item in items {
        let syn::Item::Mod(module) = item else {
            continue;
        };
        let name = module.ident.unraw().to_string();
        let path_attribute = module_path_attribute(module);
        if let Some((_, items)) = &module.content {
            let nested = match path_attribute {
                Some(path) => ModuleDirectory::owned(&directory.path.join(path)),
                None => ModuleDirectory::owned(&directory.children().join(&name)),
            };
            module_items(file, items, &nested, files)?;
            continue;
        }
        if let Some(path) = path_attribute {
            let child = directory.path.join(path);
            let parent = child.parent().unwrap_or(&directory.path).to_path_buf();
            module_file(&child, &ModuleDirectory::owned(&parent), files)?;
            continue;
        }
        let base = directory.children();
        let flat = base.join(format!("{name}.rs"));
        let nested = base.join(&name).join("mod.rs");
        if flat.is_file() {
            let child = ModuleDirectory {
                path: base,
                relative: Some(name),
            };
            module_file(&flat, &child, files)?;
        } else if nested.is_file() {
            module_file(&nested, &ModuleDirectory::owned(&base.join(&name)), files)?;
        } else {
            return Err(format!(
                "cannot find `{}` or `{}` for `mod {name};` in `{}`",
                flat.display(),
                nested.display(),
                file.display()
            ));
        }
    }
    Ok(())
}

/// Returns the value of a module's `#[path = "..."]` attribute.
fn module_path_attribute(module: &syn::ItemMod) -> Option<String> {
    module.attrs.iter().find_map(|attribute| {
        let syn::Meta::NameValue(meta) = &attribute.meta else {
            return None;
        };
        if !meta.path.is_ident("path") {
            return None;
        }
        match &meta.value {
            syn::Expr::Lit(syn::ExprLit {
                lit: syn::Lit::Str(path),
                ..
            }) => Some(path.value()),
            _ => None,
        }
    })
}

fn nearest_manifest_root(path: &Path) -> Option<PathBuf> {
    let start = if path.is_dir() { path } else { path.parent()? };
    start
        .ancestors()
        .find(|dir| dir.join("Cargo.toml").is_file())
        .map(Path::to_path_buf)
}

/// Collects `.rs` files under `path`.
/// A directory holding a `Cargo.toml` is entered only when `enter_package` accepts it.
fn walk(
    path: &Path,
    enter_package: &dyn Fn(&Path) -> bool,
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
        || (path.join("Cargo.toml").is_file() && !enter_package(path))
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
        walk(&child, enter_package, target_directory, files)?;
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

    #[test]
    fn workspace_discovery_follows_module_declarations_only() {
        let temporary = temp_dir();
        let root = temporary.path();
        for directory in [
            "src/flat",
            "src/outer/deep",
            "src/moved",
            "shared",
            "tests/suite",
            "tests/fixtures/broken",
        ] {
            fs::create_dir_all(root.join(directory)).unwrap();
        }
        fs::write(
            root.join("Cargo.toml"),
            "[package]\nname = \"format-modules\"\nversion = \"0.1.0\"\nedition = \"2024\"\n[workspace]\n",
        )
        .unwrap();
        let sources = [
            (
                "src/lib.rs",
                "mod flat;\nmod r#async;\nmod outer { mod deep; }\n#[path = \"moved/renamed.rs\"]\nmod moved;\n#[path = \"../shared/common.rs\"]\nmod common;\n",
            ),
            // A non-`mod.rs` file owns the directory named by its stem.
            ("src/flat.rs", "mod inner;\n"),
            ("src/flat/inner.rs", "\n"),
            ("src/async.rs", "\n"),
            ("src/outer/deep.rs", "\n"),
            // A `#[path]` file owns its own directory, like `mod.rs`.
            ("src/moved/renamed.rs", "mod sibling;\n"),
            ("src/moved/sibling.rs", "\n"),
            ("shared/common.rs", "\n"),
            // A file that does not parse is still an input; its declarations are not followed.
            ("tests/suite.rs", "mod helper;\nfn broken( {\n"),
            ("tests/suite/helper.rs", "\n"),
            ("tests/fixtures/broken/source.rs", "fn broken( {\n"),
            ("src/unused.rs", "\n"),
        ];
        for (file, source) in sources {
            fs::write(root.join(file), source).unwrap();
        }
        let root = root.canonicalize().unwrap();
        let manifest = root.join("Cargo.toml");
        let selected = discover_format_inputs(Some(&manifest), &[])
            .unwrap()
            .into_iter()
            .map(|input| input.path)
            .collect::<BTreeSet<_>>();
        let expected = [
            "shared/common.rs",
            "src/async.rs",
            "src/flat.rs",
            "src/flat/inner.rs",
            "src/lib.rs",
            "src/moved/renamed.rs",
            "src/moved/sibling.rs",
            "src/outer/deep.rs",
            "tests/suite.rs",
        ]
        .into_iter()
        .map(|file| root.join(file))
        .collect::<BTreeSet<_>>();
        assert_eq!(selected, expected);

        fs::write(root.join("src/flat.rs"), "mod missing;\n").unwrap();
        let error = discover_format_inputs(Some(&manifest), &[]).unwrap_err();
        assert!(error.contains("mod missing;"), "{error}");
        assert!(error.contains("src/flat/missing.rs"), "{error}");
    }

    #[test]
    fn explicit_directories_span_members_and_skip_unowned_files() {
        let temporary = temp_dir();
        let root = temporary.path();
        for directory in [
            "crates/first/src",
            "crates/second/src",
            "crates/first/tests/fixtures/nested/src",
            "fixtures",
        ] {
            fs::create_dir_all(root.join(directory)).unwrap();
        }
        fs::write(
            root.join("Cargo.toml"),
            "[workspace]\nmembers = [\"crates/first\", \"crates/second\"]\nresolver = \"3\"\n",
        )
        .unwrap();
        for (name, edition) in [("first", "2021"), ("second", "2024")] {
            fs::write(
                root.join(format!("crates/{name}/Cargo.toml")),
                format!(
                    "[package]\nname = \"{name}\"\nversion = \"0.1.0\"\nedition = \"{edition}\"\n"
                ),
            )
            .unwrap();
            fs::write(root.join(format!("crates/{name}/src/lib.rs")), "\n").unwrap();
        }
        fs::write(
            root.join("crates/first/tests/fixtures/nested/Cargo.toml"),
            "[package]\nname = \"nested\"\nversion = \"0.1.0\"\nedition = \"2024\"\n[workspace]\n",
        )
        .unwrap();
        fs::write(
            root.join("crates/first/tests/fixtures/nested/src/lib.rs"),
            "\n",
        )
        .unwrap();
        fs::write(root.join("fixtures/unowned.rs"), "\n").unwrap();
        let manifest = root.join("Cargo.toml");
        let root = root.canonicalize().unwrap();
        let expected = vec![
            FormatInput {
                path: root.join("crates/first/src/lib.rs"),
                edition: Edition::E2021,
            },
            FormatInput {
                path: root.join("crates/second/src/lib.rs"),
                edition: Edition::E2024,
            },
        ];

        for directory in [root.join("crates"), root.clone()] {
            assert_eq!(
                discover_format_inputs(Some(&manifest), &[directory]).unwrap(),
                expected
            );
        }
        for unowned in [
            root.join("fixtures"),
            root.join("fixtures/unowned.rs"),
            root.join("crates/first/tests/fixtures/nested"),
        ] {
            let error = discover_format_inputs(Some(&manifest), &[unowned]).unwrap_err();
            assert!(error.contains("--manifest-path"), "{error}");
        }
        let error =
            discover_format_inputs(Some(&manifest), &[root.join("crates/first/Cargo.toml")])
                .unwrap_err();
        assert!(error.contains("not a Rust source file"), "{error}");
    }
}
