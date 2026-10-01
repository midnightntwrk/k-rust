use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use krs_fmt::Edition;
use syn::ext::IdentExt as _;

use crate::metadata::{CargoMetadata, MetadataPackage};

/// One Rust file and its Cargo-selected edition and facade aliases.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FormatInput {
    /// Rust source path:
    /// canonical for workspace discovery,
    /// and under the caller's spelling for explicit paths.
    pub path: PathBuf,
    /// Edition selected by the owning Cargo target or package.
    pub edition: Edition,
    /// Names under which the owning Cargo package can invoke the `krs` facade.
    /// A package with no facade dependency has no aliases, unless it is the facade itself.
    pub facade_aliases: BTreeSet<String>,
}

/// Discovers Rust files from workspace targets or explicit paths.
///
/// Without paths, every workspace member target contributes its crate root
/// and the files of its out-of-line modules, as `cargo fmt --all` selects them:
/// `mod name;` resolves to `name.rs` or `name/mod.rs` by Rust's module path rules,
/// including `#[path]` and inline module nesting,
/// and finding both files is an error, as in rustc.
/// Without `#[path]`, every existing file named by a `#[cfg_attr(..., path = "...")]`
/// of the declaration is an input too, as in rustfmt,
/// and the default file may then be absent.
/// Modules declared inside macro invocations, such as `cfg_if!`, are not followed.
/// Other files near a target, such as test fixtures, are not inputs,
/// and a file that does not parse is an input whose modules are not followed.
/// An explicit file must be a `.rs` file of a workspace member.
/// An explicit directory is walked through every workspace member it contains,
/// never entering another package's directory,
/// and contributes only the files owned by a workspace member;
/// a directory that contributes none is an error.
/// Each file takes the edition of the target whose source directory most specifically contains it.
/// Without paths, only the targets that reach a file count,
/// so a file reached through `#[path]` from outside the source directory of every such target
/// takes the edition of the first target, in Cargo's order, that reached it.
/// Each file takes its facade aliases from its owning package's Cargo metadata dependencies.
/// Dependency kinds and target predicates do not restrict the alias set.
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
        return workspace_inputs(&packages);
    }

    // Ownership is resolved on canonical paths; files keep the caller's spelling.
    let mut files = BTreeMap::new();
    for path in paths {
        let root = canonical(path)?;
        if root.is_file() {
            if root.extension().is_none_or(|extension| extension != "rs") {
                return Err(format!("`{}` is not a Rust source file", path.display()));
            }
            let Some((edition, facade_aliases)) = explicit_settings(&root, &packages)? else {
                return Err(format!(
                    "`{}` is not owned by a workspace package; pass --manifest-path of the workspace that owns it",
                    path.display()
                ));
            };
            files.entry(root).or_insert(FormatInput {
                path: path.clone(),
                edition,
                facade_aliases,
            });
            continue;
        }
        let mut found = BTreeSet::new();
        let enter = |directory: &Path| directory == root || packages.contains_key(directory);
        walk(&root, &enter, target_directory.as_deref(), &mut found)?;
        let mut owned = 0_usize;
        for file in found {
            // Files of no workspace member, such as a virtual workspace root's fixtures, are not inputs.
            let Some((edition, facade_aliases)) = explicit_settings(&file, &packages)? else {
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
                facade_aliases,
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

fn workspace_inputs(
    packages: &BTreeMap<PathBuf, &MetadataPackage>,
) -> Result<Vec<FormatInput>, String> {
    let mut selected = BTreeMap::new();
    for package in packages.values() {
        for target in &package.targets {
            let Some(source) = &target.src_path else {
                continue;
            };
            let source = canonical(Path::new(source))?;
            let root = source
                .parent()
                .ok_or_else(|| format!("target source has no parent: `{}`", source.display()))?;
            let edition = target_edition(package, target.edition.as_deref())?;
            let mut files = BTreeSet::new();
            module_files(&source, &mut files)?;
            for file in files {
                // A more specific containing target source directory selects the edition.
                // Equal or no containing directories use Cargo's target order.
                let specificity = if file.starts_with(root) {
                    root.components().count()
                } else {
                    0
                };
                let facade_aliases =
                    facade_aliases(owning_package(&file, packages).unwrap_or(package))?;
                let entry =
                    selected
                        .entry(file)
                        .or_insert((specificity, edition, facade_aliases.clone()));
                if specificity > entry.0 {
                    *entry = (specificity, edition, facade_aliases);
                }
            }
        }
    }
    Ok(selected
        .into_iter()
        .map(|(path, (_, edition, facade_aliases))| FormatInput {
            path,
            edition,
            facade_aliases,
        })
        .collect())
}

/// Returns the facade aliases and the most specific target's edition of the owning workspace member.
fn explicit_settings(
    file: &Path,
    packages: &BTreeMap<PathBuf, &MetadataPackage>,
) -> Result<Option<(Edition, BTreeSet<String>)>, String> {
    let Some(package) = owning_package(file, packages) else {
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
    Ok(Some((edition, facade_aliases(package)?)))
}

/// The facade aliases of `package` under the collector's manifest rule.
fn facade_aliases(package: &MetadataPackage) -> Result<BTreeSet<String>, String> {
    krs_collector::package_facade_aliases(Path::new(&package.manifest_path))
        .map_err(|error| error.to_string())
}

fn owning_package<'a>(
    file: &Path,
    packages: &BTreeMap<PathBuf, &'a MetadataPackage>,
) -> Option<&'a MetadataPackage> {
    nearest_manifest_root(file)
        .as_ref()
        .and_then(|root| packages.get(root).copied())
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
        let conditional = module_cfg_attr_paths(module)
            .into_iter()
            .map(|path| directory.path.join(path))
            .filter(|path| path.is_file())
            .collect::<Vec<_>>();
        match (flat.is_file(), nested.is_file()) {
            (true, true) => {
                return Err(format!(
                    "file for `mod {name};` in `{}` found at both `{}` and `{}`; delete or rename one of them",
                    file.display(),
                    flat.display(),
                    nested.display()
                ));
            }
            (true, false) => {
                let child = ModuleDirectory {
                    path: base,
                    relative: Some(name),
                };
                module_file(&flat, &child, files)?;
            }
            (false, true) => {
                module_file(&nested, &ModuleDirectory::owned(&base.join(&name)), files)?;
            }
            (false, false) if conditional.is_empty() => {
                return Err(format!(
                    "cannot find `{}` or `{}` for `mod {name};` in `{}`",
                    flat.display(),
                    nested.display(),
                    file.display()
                ));
            }
            (false, false) => {}
        }
        for child in conditional {
            let parent = child.parent().unwrap_or(&directory.path).to_path_buf();
            module_file(&child, &ModuleDirectory::owned(&parent), files)?;
        }
    }
    Ok(())
}

/// Returns the value of a module's `#[path = "..."]` attribute.
fn module_path_attribute(module: &syn::ItemMod) -> Option<String> {
    module
        .attrs
        .iter()
        .find_map(|attribute| path_value(&attribute.meta))
}

/// Returns every `path` value that a module's `#[cfg_attr]` attributes may apply,
/// including through nested `cfg_attr`.
fn module_cfg_attr_paths(module: &syn::ItemMod) -> Vec<String> {
    let mut paths = Vec::new();
    for attribute in &module.attrs {
        cfg_attr_paths(&attribute.meta, &mut paths);
    }
    paths
}

fn cfg_attr_paths(meta: &syn::Meta, paths: &mut Vec<String>) {
    let syn::Meta::List(list) = meta else {
        return;
    };
    if !list.path.is_ident("cfg_attr") {
        return;
    }
    // rustc reports a malformed `cfg_attr`; it applies no path here.
    let Ok(arguments) = list.parse_args_with(
        syn::punctuated::Punctuated::<syn::Meta, syn::Token![,]>::parse_terminated,
    ) else {
        return;
    };
    // The first argument is the configuration predicate.
    for argument in arguments.iter().skip(1) {
        if let Some(path) = path_value(argument) {
            paths.push(path);
        } else {
            cfg_attr_paths(argument, paths);
        }
    }
}

/// Returns the string of a `path = "..."` meta item.
fn path_value(meta: &syn::Meta) -> Option<String> {
    let syn::Meta::NameValue(meta) = meta else {
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
    fn discovered_and_explicit_files_use_workspace_inherited_facade_aliases() {
        let temporary = temp_dir();
        let root = temporary.path();
        fs::write(
            root.join("Cargo.toml"),
            concat!(
                "[workspace]\nmembers = [\"facade\", \"definition\"]\nresolver = \"3\"\n",
                "[workspace.dependencies]\nlang = { package = \"krs\", path = \"facade\" }\n",
            ),
        )
        .unwrap();
        for (directory, name, dependency) in [
            ("facade", "krs", ""),
            (
                "definition",
                "definition",
                "[dependencies]\nlang.workspace = true\n",
            ),
        ] {
            fs::create_dir_all(root.join(directory).join("src")).unwrap();
            fs::write(
                root.join(directory).join("Cargo.toml"),
                format!(
                    "[package]\nname = \"{name}\"\nversion = \"0.1.0\"\nedition = \"2024\"\n{dependency}"
                ),
            )
            .unwrap();
            fs::write(root.join(directory).join("src/lib.rs"), "\n").unwrap();
        }
        let manifest = root.join("Cargo.toml");
        let inputs = discover_format_inputs(Some(&manifest), &[]).unwrap();
        for (directory, alias) in [("facade", "crate"), ("definition", "lang")] {
            let path = root.join(directory).join("src/lib.rs");
            let selected = inputs.iter().find(|input| input.path == path).unwrap();
            assert_eq!(selected.facade_aliases, BTreeSet::from([alias.to_owned()]));
            assert_eq!(
                discover_format_inputs(Some(&manifest), &[path]).unwrap(),
                vec![selected.clone()]
            );
        }
    }

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
        assert!(files.iter().all(|file| file.facade_aliases.is_empty()));

        let explicit = discover_format_inputs(
            Some(&root.join("Cargo.toml")),
            &[root.join("src/build/mod.rs")],
        )
        .unwrap();
        assert_eq!(explicit[0].path, root.join("src/build/mod.rs"));
        assert_eq!(explicit[0].edition, Edition::E2021);
        assert!(explicit[0].facade_aliases.is_empty());
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
        fs::write(
            root.join("Cargo.toml"),
            "[package]\nname = \"format-modules\"\nversion = \"0.1.0\"\nedition = \"2024\"\n[workspace]\n\n[[bin]]\nname = \"tool\"\npath = \"src/bin/tool/main.rs\"\nedition = \"2021\"\n",
        )
        .unwrap();
        let sources = [
            (
                "src/lib.rs",
                concat!(
                    "mod flat;\nmod r#async;\nmod outer { mod deep; }\nmod tree;\n",
                    "#[path = \"moved/renamed.rs\"]\nmod moved;\n",
                    "#[path = \"../shared/common.rs\"]\nmod common;\n",
                    "#[path = \"elsewhere\"]\nmod inline { mod leaf; }\n",
                    "#[cfg_attr(unix, path = \"platform/unix.rs\")]\n",
                    "#[cfg_attr(unix, cfg_attr(target_os = \"linux\", path = \"platform/linux.rs\"))]\n",
                    "#[cfg_attr(windows, path = \"platform/absent.rs\")]\nmod platform;\n",
                    "#[cfg_attr(test, path = \"alternate.rs\")]\nmod defaulted;\n",
                ),
            ),
            // A non-`mod.rs` file owns the directory named by its stem,
            // and its inline modules nest below it.
            ("src/flat.rs", "mod inner;\nmod nest { mod item; }\n"),
            ("src/flat/inner.rs", "\n"),
            ("src/flat/nest/item.rs", "\n"),
            ("src/async.rs", "\n"),
            ("src/outer/deep.rs", "\n"),
            ("src/tree/mod.rs", "mod branch;\n"),
            ("src/tree/branch.rs", "\n"),
            // A `#[path]` file owns its own directory, like `mod.rs`.
            ("src/moved/renamed.rs", "mod sibling;\n"),
            ("src/moved/sibling.rs", "\n"),
            ("src/elsewhere/leaf.rs", "\n"),
            ("shared/common.rs", "\n"),
            // Every existing `cfg_attr` path is an input, and the default file may be absent.
            ("src/platform/unix.rs", "\n"),
            ("src/platform/linux.rs", "\n"),
            ("src/defaulted.rs", "\n"),
            ("src/alternate.rs", "\n"),
            // The binary reaches a file inside the library's source directory.
            (
                "src/bin/tool/main.rs",
                "#[path = \"../../outer/deep.rs\"]\nmod deep;\nfn main() {}\n",
            ),
            // A file that does not parse is still an input; its declarations are not followed.
            ("tests/suite.rs", "mod helper;\nfn broken( {\n"),
            ("tests/suite/helper.rs", "\n"),
            ("tests/fixtures/broken/source.rs", "fn broken( {\n"),
            ("src/unused.rs", "\n"),
        ];
        for (file, source) in sources {
            let file = root.join(file);
            fs::create_dir_all(file.parent().unwrap()).unwrap();
            fs::write(file, source).unwrap();
        }
        let root = root.canonicalize().unwrap();
        let manifest = root.join("Cargo.toml");
        let inputs = discover_format_inputs(Some(&manifest), &[]).unwrap();
        let selected = inputs
            .iter()
            .map(|input| input.path.clone())
            .collect::<BTreeSet<_>>();
        let expected = [
            "shared/common.rs",
            "src/alternate.rs",
            "src/async.rs",
            "src/bin/tool/main.rs",
            "src/defaulted.rs",
            "src/elsewhere/leaf.rs",
            "src/flat.rs",
            "src/flat/inner.rs",
            "src/flat/nest/item.rs",
            "src/lib.rs",
            "src/moved/renamed.rs",
            "src/moved/sibling.rs",
            "src/outer/deep.rs",
            "src/platform/linux.rs",
            "src/platform/unix.rs",
            "src/tree/branch.rs",
            "src/tree/mod.rs",
            "tests/suite.rs",
        ]
        .into_iter()
        .map(|file| root.join(file))
        .collect::<BTreeSet<_>>();
        assert_eq!(selected, expected);
        let edition = |file: &str| {
            inputs
                .iter()
                .find(|input| input.path == root.join(file))
                .unwrap()
                .edition
        };
        assert_eq!(edition("src/bin/tool/main.rs"), Edition::E2021);
        // The library's directory contains the file; the deeper binary directory does not.
        assert_eq!(edition("src/outer/deep.rs"), Edition::E2024);
    }

    #[test]
    fn workspace_discovery_rejects_missing_and_ambiguous_module_files() {
        let temporary = temp_dir();
        let root = temporary.path();
        fs::create_dir_all(root.join("src/tree")).unwrap();
        fs::write(
            root.join("Cargo.toml"),
            "[package]\nname = \"format-module-errors\"\nversion = \"0.1.0\"\nedition = \"2024\"\n[workspace]\n",
        )
        .unwrap();
        fs::write(root.join("src/lib.rs"), "mod tree;\n").unwrap();
        fs::write(root.join("src/tree.rs"), "\n").unwrap();
        fs::write(root.join("src/tree/mod.rs"), "\n").unwrap();
        let manifest = root.join("Cargo.toml");
        let error = discover_format_inputs(Some(&manifest), &[]).unwrap_err();
        assert!(error.contains("mod tree;"), "{error}");
        assert!(error.contains("found at both"), "{error}");
        assert!(error.contains("src/tree.rs"), "{error}");
        assert!(error.contains("src/tree/mod.rs"), "{error}");

        fs::remove_file(root.join("src/tree/mod.rs")).unwrap();
        fs::write(root.join("src/tree.rs"), "mod missing;\n").unwrap();
        let error = discover_format_inputs(Some(&manifest), &[]).unwrap_err();
        assert!(error.contains("mod missing;"), "{error}");
        assert!(error.contains("src/tree/missing.rs"), "{error}");
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
                facade_aliases: BTreeSet::new(),
            },
            FormatInput {
                path: root.join("crates/second/src/lib.rs"),
                edition: Edition::E2024,
                facade_aliases: BTreeSet::new(),
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
