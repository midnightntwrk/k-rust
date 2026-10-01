//! The names under which a selected package's authored sources invoke the
//! `krs` facade, and the resolution of authored attributes under them.
//!
//! KRS macros locate the facade through the invoking package's Cargo manifest
//! (`proc_macro_crate`). The collector reads the same manifest, so it
//! resolves an authored attribute exactly when the package can name the
//! facade that way: the package itself when it is `krs` (`crate`), and every
//! dependency or dev-dependency, target-specific or not, whose package is
//! `krs`, under its dependency name with `-` spelled `_`. A dependency
//! inherited with `workspace = true` takes its package from the
//! `[workspace.dependencies]` table of the workspace root manifest.
//! Within a source file, `use <facade> as <alias>;` and
//! `extern crate <facade> as <alias>;` add a module-scoped alias
//! ([`AttributeResolver::scoped`]).
//!
//! Resolution and module bindings are delegated to [`krs_syntax::surface::FacadeScope`].

use krs_ir::Position;
use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

use krs_syntax::surface::{self, AttributeMacro, Entry, FacadeScope, FunctionMacro, Resolve};
use syn::Attribute;
use syn::ext::IdentExt;
use syn::spanned::Spanned;
use syn::visit::Visit;
use toml_edit::{Document, Item, TableLike};

use crate::collect::{record_file, record_probe};
use crate::{CollectionError, CollectionErrorKind};

/// The Cargo package name of the KRS facade.
const FACADE_PACKAGE: &str = "krs";

/// The names under which one package's authored sources name the facade.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct FacadeAliases {
    aliases: BTreeSet<String>,
}

impl FacadeAliases {
    /// Reads the facade aliases of the package whose manifest is `manifest`.
    ///
    /// # Errors
    ///
    /// Returns a collection error if a required manifest cannot be read or parsed.
    pub fn from_manifest(manifest: &Path) -> Result<Self, CollectionError> {
        let document = read_manifest(manifest)?;
        let table = document.as_table();
        let package = table
            .get("package")
            .and_then(|package| package.get("name"))
            .and_then(Item::as_str);
        let mut aliases = BTreeSet::new();
        if package == Some(FACADE_PACKAGE) {
            aliases.insert("crate".to_owned());
        }
        let mut workspace = None;
        for dependencies in dependency_tables(table) {
            for (name, dependency) in dependencies.iter() {
                let mut package_name = dependency
                    .get("package")
                    .and_then(Item::as_str)
                    .unwrap_or(name)
                    .to_owned();
                if dependency.get("workspace").and_then(Item::as_bool) == Some(true) {
                    if workspace.is_none() {
                        workspace = Some(workspace_dependencies(manifest, table)?);
                    }
                    if let Some(inherited) = workspace
                        .as_ref()
                        .and_then(|workspace| workspace.iter().find(|(key, _)| key == name))
                    {
                        package_name.clone_from(&inherited.1);
                    }
                }
                if package_name == FACADE_PACKAGE && package != Some(FACADE_PACKAGE) {
                    aliases.insert(name.replace('-', "_"));
                }
            }
        }
        Ok(Self { aliases })
    }

    /// The package's facade scope before file and inline-module bindings.
    #[must_use]
    pub fn scope(&self) -> FacadeScope {
        FacadeScope::new(self.aliases.clone())
    }
}

/// Resolves the attributes of one module of an authored source file.
#[derive(Clone, Debug)]
pub(crate) struct AttributeResolver<'a> {
    facade: FacadeScope,
    display_file: &'a str,
}

impl<'a> AttributeResolver<'a> {
    pub(crate) fn new(facade: &FacadeAliases, display_file: &'a str) -> Self {
        Self {
            facade: facade.scope(),
            display_file,
        }
    }

    /// The resolver for a file or inline module whose items are `items`.
    pub(crate) fn scoped(&self, items: &[syn::Item]) -> Self {
        Self {
            facade: self.facade.scoped(items),
            display_file: self.display_file,
        }
    }

    /// The replacement spelling for an unresolved entry under each facade
    /// name in scope.
    fn suggest(&self, entry: &str, macro_invocation: bool) -> String {
        let (open, close) = if macro_invocation {
            ("", "!")
        } else {
            ("#[", "]")
        };
        if self.facade.aliases().is_empty() {
            return format!(
                "no name binds the `krs` facade here; add a dependency on the `krs` package (for example `k = {{ package = \"krs\", ... }}`) and write `{open}k::{entry}{close}`"
            );
        }
        let spellings = self
            .facade
            .aliases()
            .iter()
            .map(|alias| format!("`{open}{alias}::{entry}{close}`"))
            .collect::<Vec<_>>()
            .join(" or ");
        format!("write {spellings} instead")
    }

    /// Whether `attribute` invokes the attribute entry point `entry`.
    pub(crate) fn invokes(&self, attribute: &Attribute, entry: AttributeMacro) -> bool {
        self.facade.resolve(attribute.path()) == Some(Entry::Attribute(entry))
    }

    /// Checks every authored attribute and item-level macro in a module,
    /// including members, variants, fields, and nested inline modules.
    pub(crate) fn check_items(&self, items: &[syn::Item]) -> Result<(), CollectionError> {
        let scoped = self.scoped(items);
        for item in items {
            if let syn::Item::Mod(module) = item {
                scoped.check(&module.attrs)?;
                if let Some((_, nested)) = &module.content {
                    scoped.check_items(nested)?;
                }
                continue;
            }
            let mut visitor = EntryVisitor {
                resolver: &scoped,
                error: None,
            };
            visitor.visit_item(item);
            if let Some(error) = visitor.error {
                return Err(error);
            }
        }
        Ok(())
    }

    /// Rejects an attribute whose last path segment names an attribute entry
    /// point but whose path does not resolve to a KRS entry point, such as
    /// `#[other::rule]` or an imported `#[rule]`.
    pub(crate) fn check(&self, attributes: &[Attribute]) -> Result<(), CollectionError> {
        for attribute in attributes {
            let Some(entry) = named_attribute_entry(attribute.path()) else {
                continue;
            };
            if self.resolves_attribute(attribute.path(), &entry) {
                continue;
            }
            let start = Position::from_proc_macro2(attribute.pound_token.span.start()).map_err(
                |error| {
                    CollectionError::new(
                        CollectionErrorKind::SourcePositionOutOfBounds,
                        error.to_string(),
                    )
                },
            )?;
            return Err(CollectionError::new(
                CollectionErrorKind::UnresolvedAttribute,
                format!(
                    "attribute `{}` at `{}`:{}:{} is named like the KRS entry point `{}` but does not invoke it; KRS attributes are written only under a name that binds the `krs` facade, so {}",
                    surface::path_text(attribute.path()),
                    self.display_file,
                    start.line(),
                    start.scalar_column(),
                    entry,
                    self.suggest(&entry, false),
                ),
            )
            .with_span(attribute.span()));
        }
        Ok(())
    }

    fn resolves_attribute(&self, path: &syn::Path, name: &str) -> bool {
        self.facade.facade_member(path).as_deref() == Some(name)
            && (self.facade.resolve(path).is_some() || is_helper(name))
    }

    fn check_macro(&self, invocation: &syn::Macro) -> Result<(), CollectionError> {
        let Some(segment) = invocation.path.segments.last() else {
            return Ok(());
        };
        let name = segment.ident.unraw().to_string();
        let Some(entry) = FunctionMacro::from_name(&name) else {
            return Ok(());
        };
        if entry.name().starts_with("__")
            || self.facade.resolve(&invocation.path) == Some(Entry::Function(entry))
        {
            return Ok(());
        }
        let start =
            Position::from_proc_macro2(invocation.path.span().start()).map_err(|error| {
                CollectionError::new(
                    CollectionErrorKind::SourcePositionOutOfBounds,
                    error.to_string(),
                )
            })?;
        Err(CollectionError::new(
            CollectionErrorKind::UnresolvedAttribute,
            format!(
                "macro `{}` at `{}`:{}:{} is named like the KRS entry point `{}` but does not invoke it; KRS macros are written only under a name that binds the `krs` facade, so {}",
                surface::path_text(&invocation.path),
                self.display_file,
                start.line(),
                start.scalar_column(),
                name,
                self.suggest(&name, true),
            ),
        )
        .with_span(invocation.path.span()))
    }
}

fn is_helper(name: &str) -> bool {
    [
        surface::ENUM_HELPERS,
        surface::VARIANT_HELPERS,
        surface::FIELD_HELPERS,
        surface::PARAMETER_HELPERS,
    ]
    .into_iter()
    .flatten()
    .any(|helper| *helper == name)
}

fn named_attribute_entry(path: &syn::Path) -> Option<String> {
    let name = path.segments.last()?.ident.unraw().to_string();
    (AttributeMacro::from_name(&name).is_some() || is_helper(&name)).then_some(name)
}

struct EntryVisitor<'resolver, 'file> {
    resolver: &'resolver AttributeResolver<'file>,
    error: Option<CollectionError>,
}

impl<'ast> Visit<'ast> for EntryVisitor<'_, '_> {
    fn visit_attribute(&mut self, attribute: &'ast Attribute) {
        if self.error.is_none() {
            self.error = self.resolver.check(std::slice::from_ref(attribute)).err();
        }
    }

    fn visit_item_macro(&mut self, item: &'ast syn::ItemMacro) {
        if self.error.is_none() {
            self.error = self.resolver.check_macro(&item.mac).err();
        }
        syn::visit::visit_item_macro(self, item);
    }
}

fn read_manifest(manifest: &Path) -> Result<Document<String>, CollectionError> {
    let text = fs::read_to_string(manifest).map_err(|error| {
        CollectionError::new(
            CollectionErrorKind::HostIo,
            format!(
                "cannot read Cargo manifest `{}`: {error}",
                manifest.display()
            ),
        )
    })?;
    record_probe(manifest);
    record_file(manifest, text.as_bytes());
    text.parse().map_err(|error| {
        CollectionError::new(
            CollectionErrorKind::InvalidPackageContext,
            format!(
                "cannot parse Cargo manifest `{}`: {error}",
                manifest.display()
            ),
        )
    })
}

/// The dependency and dev-dependency tables of a manifest, including the
/// target-specific ones.
fn dependency_tables(manifest: &toml_edit::Table) -> Vec<&dyn TableLike> {
    let mut output = own_dependency_tables(manifest);
    if let Some(targets) = manifest.get("target").and_then(Item::as_table_like) {
        for (_, target) in targets.iter() {
            if let Some(target) = target.as_table_like() {
                output.extend(own_dependency_tables(target));
            }
        }
    }
    output
}

fn own_dependency_tables(table: &dyn TableLike) -> Vec<&dyn TableLike> {
    ["dependencies", "dev-dependencies"]
        .into_iter()
        .filter_map(|key| table.get(key).and_then(Item::as_table_like))
        .collect()
}

/// The `(dependency name, package name)` pairs of the workspace that the
/// package of `manifest` belongs to.
fn workspace_dependencies(
    manifest: &Path,
    table: &toml_edit::Table,
) -> Result<Vec<(String, String)>, CollectionError> {
    let root = workspace_root(manifest, table)?;
    let document;
    let workspace = match &root {
        None => return Ok(Vec::new()),
        Some(root) if root == manifest => table,
        Some(root) => {
            document = read_manifest(root)?;
            document.as_table()
        }
    };
    Ok(workspace
        .get("workspace")
        .and_then(|workspace| workspace.get("dependencies"))
        .and_then(Item::as_table_like)
        .map(|dependencies| {
            dependencies
                .iter()
                .map(|(name, dependency)| {
                    let package = dependency
                        .get("package")
                        .and_then(Item::as_str)
                        .unwrap_or(name);
                    (name.to_owned(), package.to_owned())
                })
                .collect()
        })
        .unwrap_or_default())
}

/// The workspace root manifest of the package of `manifest`: the path that
/// `package.workspace` names, the manifest itself when it has a `[workspace]`
/// table, or else the nearest ancestor with a `[workspace]` table that does
/// not exclude the package, as Cargo discovers it.
fn workspace_root(
    manifest: &Path,
    table: &toml_edit::Table,
) -> Result<Option<PathBuf>, CollectionError> {
    let package_dir = manifest.parent().unwrap_or(Path::new(""));
    if let Some(explicit) = table
        .get("package")
        .and_then(|package| package.get("workspace"))
        .and_then(Item::as_str)
    {
        return Ok(Some(package_dir.join(explicit).join("Cargo.toml")));
    }
    if table.contains_key("workspace") {
        return Ok(Some(manifest.to_owned()));
    }
    for directory in package_dir.ancestors().skip(1) {
        let candidate = directory.join("Cargo.toml");
        record_probe(&candidate);
        if !candidate.is_file() {
            continue;
        }
        let document = read_manifest(&candidate)?;
        if let Some(workspace) = document.get("workspace").and_then(Item::as_table_like)
            && !workspace_excludes(workspace, directory, manifest)
        {
            return Ok(Some(candidate));
        }
    }
    Ok(None)
}

/// Whether the workspace rooted at `root` excludes the package of `manifest`.
///
/// Like Cargo, this compares `exclude` and `members` entries as literal path
/// prefixes without expanding globs, and an explicit member overrides an
/// exclusion.
fn workspace_excludes(workspace: &dyn TableLike, root: &Path, manifest: &Path) -> bool {
    let lists_package = |key: &str| {
        workspace
            .get(key)
            .and_then(Item::as_array)
            .is_some_and(|entries| {
                entries
                    .iter()
                    .filter_map(toml_edit::Value::as_str)
                    .any(|entry| manifest.starts_with(root.join(entry)))
            })
    };
    lists_package("exclude") && !lists_package("members")
}

#[cfg(test)]
mod tests {
    use super::*;
    use proc_macro_crate::{FoundCrate, crate_name};
    use std::process::Command;

    fn aliases(manifest: &str) -> BTreeSet<String> {
        static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
        let directory = std::env::temp_dir().join(format!(
            "krs-collector-facade-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
        ));
        fs::create_dir_all(&directory).unwrap();
        let path = directory.join("Cargo.toml");
        fs::write(&path, manifest).unwrap();
        let aliases = FacadeAliases::from_manifest(&path).unwrap().aliases;
        fs::remove_dir_all(&directory).unwrap();
        aliases
    }

    #[test]
    fn manifest_names_the_facade_by_dependency_name() {
        assert_eq!(
            aliases(
                "[package]\nname = \"p\"\n[workspace]\n[dependencies]\nk = { package = \"krs\", path = \"x\" }\nserde = \"1\"\n"
            ),
            BTreeSet::from(["k".to_owned()])
        );
        assert_eq!(
            aliases(
                "[package]\nname = \"p\"\n[workspace]\n[target.'cfg(unix)'.dev-dependencies]\nrenamed-krs = { package = \"krs\" }\n[dependencies]\nkrs = \"0.1\"\n"
            ),
            BTreeSet::from(["krs".to_owned(), "renamed_krs".to_owned()])
        );
        assert_eq!(
            aliases(
                "[package]\nname = \"krs\"\n[workspace]\n[dependencies]\nkrs-macros = \"0.1\"\n"
            ),
            BTreeSet::from(["crate".to_owned()])
        );
        assert_eq!(
            aliases(
                "[package]\nname = \"p\"\n[workspace.dependencies]\nlanguage-host = { package = \"krs\", path = \"x\" }\n[dependencies]\nlanguage-host = { workspace = true }\n"
            ),
            BTreeSet::from(["language_host".to_owned()])
        );
        assert!(aliases("[package]\nname = \"p\"\n[workspace]\n").is_empty());
    }

    #[test]
    #[ignore = "run by manifest_aliases_match_proc_macro_crate in a child process"]
    fn proc_macro_crate_child() {
        let result = match crate_name(FACADE_PACKAGE) {
            Ok(FoundCrate::Itself) => "itself".to_owned(),
            Ok(FoundCrate::Name(name)) => format!("name:{name}"),
            Err(error) => {
                eprintln!("KRS_FACADE_PARITY_ERROR={error}");
                "error".to_owned()
            }
        };
        println!("KRS_FACADE_PARITY={result}");
    }

    fn assert_proc_macro_crate_parity(
        case: &str,
        package_manifest: &str,
        workspace_manifest: Option<&str>,
        expected: &str,
    ) {
        let temporary = tempfile::tempdir().unwrap();
        let package_dir = if let Some(workspace_manifest) = workspace_manifest {
            fs::write(temporary.path().join("Cargo.toml"), workspace_manifest).unwrap();
            fs::create_dir(temporary.path().join("src")).unwrap();
            fs::write(temporary.path().join("src/lib.rs"), "").unwrap();
            let package_dir = temporary.path().join("member");
            fs::create_dir(&package_dir).unwrap();
            package_dir
        } else {
            temporary.path().to_owned()
        };
        let manifest = package_dir.join("Cargo.toml");
        fs::write(&manifest, package_manifest).unwrap();
        fs::create_dir(package_dir.join("src")).unwrap();
        fs::write(package_dir.join("src/lib.rs"), "").unwrap();

        let aliases = FacadeAliases::from_manifest(&manifest).unwrap().aliases;
        let child = Command::new(std::env::current_exe().unwrap())
            .arg("facade::tests::proc_macro_crate_child")
            .arg("--exact")
            .arg("--ignored")
            .arg("--nocapture")
            .env("CARGO_MANIFEST_DIR", &package_dir)
            .env(
                "CARGO",
                std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into()),
            )
            .output()
            .unwrap();
        assert!(
            child.status.success(),
            "{case}: child test failed: {}",
            String::from_utf8_lossy(&child.stderr)
        );
        let stdout = String::from_utf8(child.stdout).unwrap();
        let found = stdout
            .lines()
            .find_map(|line| {
                line.split_once("KRS_FACADE_PARITY=")
                    .map(|(_, value)| value)
            })
            .unwrap_or_else(|| panic!("{case}: child result missing from {stdout:?}"));
        assert_eq!(
            found,
            expected,
            "{case}: unexpected proc-macro-crate result: {}",
            String::from_utf8_lossy(&child.stderr)
        );
        assert_eq!(
            found == "itself",
            aliases.contains("crate"),
            "{case}: Itself must agree with the `crate` alias"
        );
        if let Some(name) = found.strip_prefix("name:") {
            assert!(
                aliases.contains(name),
                "{case}: alias {name:?} is missing from {aliases:?}"
            );
        } else if found == "error" {
            assert!(aliases.is_empty(), "{case}: aliases must be empty on error");
        }
    }

    #[test]
    fn manifest_aliases_match_proc_macro_crate() {
        assert_proc_macro_crate_parity(
            "renamed dependency",
            "[package]\nname = \"fixture\"\nversion = \"0.1.0\"\n[workspace]\n[dependencies]\nrenamed-krs = { package = \"krs\", version = \"0.1.0\" }\n",
            None,
            "name:renamed_krs",
        );
        assert_proc_macro_crate_parity(
            "dev-dependency",
            "[package]\nname = \"fixture\"\nversion = \"0.1.0\"\n[workspace]\n[dev-dependencies]\nkrs = \"0.1.0\"\n",
            None,
            "name:krs",
        );
        assert_proc_macro_crate_parity(
            "target-specific dependency",
            "[package]\nname = \"fixture\"\nversion = \"0.1.0\"\n[workspace]\n[target.'cfg(unix)'.dependencies]\ntarget-krs = { package = \"krs\", version = \"0.1.0\" }\n",
            None,
            "name:target_krs",
        );
        assert_proc_macro_crate_parity(
            "the facade package itself",
            "[package]\nname = \"krs\"\nversion = \"0.1.0\"\n[workspace]\n",
            None,
            "itself",
        );
        assert_proc_macro_crate_parity(
            "workspace-inherited dependency",
            "[package]\nname = \"fixture\"\nversion = \"0.1.0\"\n[dependencies]\nworkspace-krs = { workspace = true }\n",
            Some(
                "[workspace]\nmembers = [\"m*\"]\n[workspace.dependencies]\nworkspace-krs = { package = \"krs\", version = \"0.1.0\" }\n",
            ),
            "name:workspace_krs",
        );
        assert_proc_macro_crate_parity(
            "no facade dependency",
            "[package]\nname = \"fixture\"\nversion = \"0.1.0\"\n[workspace]\n",
            None,
            "error",
        );
        assert_proc_macro_crate_parity(
            "excluded workspace package",
            "[package]\nname = \"fixture\"\nversion = \"0.1.0\"\n[dependencies]\nworkspace-krs = { workspace = true }\n",
            Some(
                "[workspace]\nmembers = [\"m*\"]\nexclude = [\"member\"]\n[workspace.dependencies]\nworkspace-krs = { package = \"krs\", version = \"0.1.0\" }\n",
            ),
            "error",
        );
        assert_proc_macro_crate_parity(
            "explicit member that is also excluded",
            "[package]\nname = \"fixture\"\nversion = \"0.1.0\"\n[dependencies]\nworkspace-krs = { workspace = true }\n",
            Some(
                "[workspace]\nmembers = [\"member\"]\nexclude = [\"member\"]\n[workspace.dependencies]\nworkspace-krs = { package = \"krs\", version = \"0.1.0\" }\n",
            ),
            "name:workspace_krs",
        );
        assert_proc_macro_crate_parity(
            "glob exclude entries are literal prefixes",
            "[package]\nname = \"fixture\"\nversion = \"0.1.0\"\n[dependencies]\nworkspace-krs = { workspace = true }\n",
            Some(
                "[workspace]\nmembers = [\"m*\"]\nexclude = [\"m*\"]\n[workspace.dependencies]\nworkspace-krs = { package = \"krs\", version = \"0.1.0\" }\n",
            ),
            "name:workspace_krs",
        );
        assert_proc_macro_crate_parity(
            "path-dependency member of a root package",
            "[package]\nname = \"fixture\"\nversion = \"0.1.0\"\n[dependencies]\nworkspace-krs = { workspace = true }\n",
            Some(
                "[package]\nname = \"root\"\nversion = \"0.1.0\"\n[workspace]\n[dependencies]\nfixture = { path = \"member\" }\n[workspace.dependencies]\nworkspace-krs = { package = \"krs\", version = \"0.1.0\" }\n",
            ),
            "name:workspace_krs",
        );
    }

    #[test]
    fn attributes_resolve_exactly_under_the_facade() {
        let facade = FacadeAliases {
            aliases: BTreeSet::from(["k".to_owned()]),
        };
        let resolver = AttributeResolver::new(&facade, "src/lib.rs");
        let item: syn::ItemFn = syn::parse_quote! {
            #[k::rule]
            #[doc = "x"]
            #[k::syntax]
            fn f() {}
        };
        assert!(resolver.invokes(&item.attrs[0], AttributeMacro::Rule));
        assert!(!resolver.invokes(&item.attrs[0], AttributeMacro::Claim));
        resolver.check(&item.attrs).unwrap();
        for foreign in [
            quote::quote!(#[other::rule]),
            quote::quote!(#[rule]),
            quote::quote!(#[::k::rule]),
        ] {
            let item: syn::ItemFn = syn::parse_quote!(#foreign fn f() {});
            assert!(!resolver.invokes(&item.attrs[0], AttributeMacro::Rule));
            let error = resolver.check(&item.attrs).unwrap_err();
            assert_eq!(error.kind(), CollectionErrorKind::UnresolvedAttribute);
            assert!(
                error.detail().ends_with("write `#[k::rule]` instead"),
                "{}",
                error.detail()
            );
        }
    }
}
