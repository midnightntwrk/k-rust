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
//! Resolution is exact and delegated to [`krs_syntax::surface::resolve`].

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

use krs_syntax::surface::{self, AttributeMacro, Entry};
use syn::ext::IdentExt;
use syn::{Attribute, UseTree};
use toml_edit::{Document, Item, TableLike};

use crate::{CollectionError, CollectionErrorKind};

/// The Cargo package name of the KRS facade.
const FACADE_PACKAGE: &str = "krs";

/// The names under which one package's authored sources name the facade.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct FacadeAliases {
    aliases: BTreeSet<String>,
}

impl FacadeAliases {
    /// Reads the facade aliases of the package whose manifest is `manifest`.
    pub(crate) fn from_manifest(manifest: &Path) -> Result<Self, CollectionError> {
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

    fn contains(&self, name: &str) -> bool {
        self.aliases.contains(name)
    }

    /// The entry point that authored `path` invokes under any facade alias.
    fn resolve(&self, path: &syn::Path) -> Option<Entry> {
        self.aliases
            .iter()
            .find_map(|alias| surface::resolve(path, alias))
    }

    /// The replacement spelling for an attribute that names `entry` without
    /// resolving: `#[<alias>::<entry>]` under each facade name in scope.
    fn suggest(&self, entry: AttributeMacro) -> String {
        let entry = entry.name();
        if self.aliases.is_empty() {
            return format!(
                "no name binds the `krs` facade here; add a dependency on the `krs` package (for example `k = {{ package = \"krs\", ... }}`) and write `#[k::{entry}]`"
            );
        }
        let spellings = self
            .aliases
            .iter()
            .map(|alias| format!("`#[{alias}::{entry}]`"))
            .collect::<Vec<_>>()
            .join(" or ");
        format!("write {spellings} instead")
    }
}

/// Resolves the attributes of one module of an authored source file.
#[derive(Clone, Debug)]
pub(crate) struct AttributeResolver<'a> {
    facade: FacadeAliases,
    display_file: &'a str,
}

impl<'a> AttributeResolver<'a> {
    pub(crate) fn new(facade: &FacadeAliases, display_file: &'a str) -> Self {
        Self {
            facade: facade.clone(),
            display_file,
        }
    }

    /// The resolver for a module whose items are `items`, nested in the
    /// module this resolver covers (or the file root).
    ///
    /// A `use <facade> as <alias>;` or `extern crate <facade> as <alias>;`
    /// item adds `<alias>`, and any other item that binds a facade name in
    /// the type namespace (`use`, `extern crate`, or `mod`) removes it.
    /// Names are inherited into nested inline modules, where rustc accepts
    /// them only through an import of the outer binding.
    pub(crate) fn scoped(&self, items: &[syn::Item]) -> Self {
        let mut added = BTreeSet::new();
        let mut shadowed = BTreeSet::new();
        for item in items {
            match item {
                syn::Item::Use(item_use) => {
                    self.use_bindings(&item_use.tree, &mut added, &mut shadowed);
                }
                syn::Item::ExternCrate(extern_crate) => {
                    let binding = extern_crate
                        .rename
                        .as_ref()
                        .map_or(&extern_crate.ident, |(_, rename)| rename)
                        .unraw()
                        .to_string();
                    if self
                        .facade
                        .contains(&extern_crate.ident.unraw().to_string())
                    {
                        added.insert(binding);
                    } else {
                        shadowed.insert(binding);
                    }
                }
                syn::Item::Mod(module) => {
                    shadowed.insert(module.ident.unraw().to_string());
                }
                _ => {}
            }
        }
        let mut facade = self.facade.clone();
        facade.aliases.retain(|alias| !shadowed.contains(alias));
        facade.aliases.extend(added);
        Self {
            facade,
            display_file: self.display_file,
        }
    }

    /// Records the type-namespace bindings of a top-level `use` tree: a
    /// rename of a facade name adds its alias, and any other binding shadows
    /// the name it binds.
    fn use_bindings(
        &self,
        tree: &UseTree,
        added: &mut BTreeSet<String>,
        shadowed: &mut BTreeSet<String>,
    ) {
        match tree {
            UseTree::Rename(rename) => {
                let binding = rename.rename.unraw().to_string();
                if self.facade.contains(&rename.ident.unraw().to_string()) {
                    added.insert(binding);
                } else {
                    shadowed.insert(binding);
                }
            }
            UseTree::Name(name) => {
                let binding = name.ident.unraw().to_string();
                if !self.facade.contains(&binding) {
                    shadowed.insert(binding);
                }
            }
            UseTree::Group(group) => {
                for tree in &group.items {
                    self.use_bindings(tree, added, shadowed);
                }
            }
            UseTree::Path(path) => {
                // `use super::k;` re-imports an outer binding, which may be a
                // facade alias; any other path binds a non-facade item.
                let relative = ["self", "super", "crate"]
                    .iter()
                    .any(|keyword| path.ident == keyword);
                let mut bound = BTreeSet::new();
                nested_bindings(&path.tree, &mut bound);
                shadowed.extend(
                    bound
                        .into_iter()
                        .filter(|name| !(relative && self.facade.contains(name))),
                );
            }
            UseTree::Glob(_) => {}
        }
    }

    /// Whether `attribute` invokes the attribute entry point `entry`.
    pub(crate) fn invokes(&self, attribute: &Attribute, entry: AttributeMacro) -> bool {
        self.facade.resolve(attribute.path()) == Some(Entry::Attribute(entry))
    }

    /// Rejects an attribute whose last path segment names an attribute entry
    /// point but whose path does not resolve to a KRS entry point, such as
    /// `#[other::rule]` or an imported `#[rule]`.
    pub(crate) fn check(&self, attributes: &[Attribute]) -> Result<(), CollectionError> {
        for attribute in attributes {
            let Some(entry) = surface::last_segment_entry(attribute.path()) else {
                continue;
            };
            if self.facade.resolve(attribute.path()).is_some() {
                continue;
            }
            let start = attribute.pound_token.span.start();
            return Err(CollectionError::new(
                CollectionErrorKind::UnresolvedAttribute,
                format!(
                    "attribute `{}` at `{}`:{}:{} is named like the KRS entry point `{}` but does not invoke it; KRS attributes are written only under a name that binds the `krs` facade, so {}",
                    attribute_spelling(attribute.path()),
                    self.display_file,
                    start.line,
                    start.column + 1,
                    entry.name(),
                    self.facade.suggest(entry),
                ),
            ));
        }
        Ok(())
    }
}

/// Records the names that a `use` subtree below a path prefix binds; none
/// of them names the facade.
fn nested_bindings(tree: &UseTree, shadowed: &mut BTreeSet<String>) {
    match tree {
        UseTree::Rename(rename) => {
            shadowed.insert(rename.rename.unraw().to_string());
        }
        UseTree::Name(name) if name.ident != "self" => {
            shadowed.insert(name.ident.unraw().to_string());
        }
        UseTree::Name(_) | UseTree::Glob(_) => {}
        UseTree::Group(group) => {
            for tree in &group.items {
                nested_bindings(tree, shadowed);
            }
        }
        UseTree::Path(path) => nested_bindings(&path.tree, shadowed),
    }
}

fn attribute_spelling(path: &syn::Path) -> String {
    quote::ToTokens::to_token_stream(path)
        .to_string()
        .replace(' ', "")
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
/// table, or else the nearest ancestor manifest with one.
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
        if candidate.is_file()
            && read_manifest(&candidate)?
                .as_table()
                .contains_key("workspace")
        {
            return Ok(Some(candidate));
        }
    }
    Ok(None)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn aliases(manifest: &str) -> BTreeSet<String> {
        static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
        let directory = std::env::temp_dir().join(format!(
            "krs-compiler-facade-{}-{}",
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
    fn module_items_rename_and_shadow_the_facade() {
        let facade = FacadeAliases {
            aliases: BTreeSet::from(["language_host".to_owned()]),
        };
        let root = AttributeResolver::new(&facade, "src/lib.rs");
        let file: syn::File = syn::parse_quote! {
            use k::Term;
            use language_host as k;
            extern crate language_host as host;
        };
        let scoped = root.scoped(&file.items);
        assert_eq!(
            scoped.facade.aliases,
            BTreeSet::from([
                "host".to_owned(),
                "k".to_owned(),
                "language_host".to_owned()
            ])
        );
        let nested: syn::File = syn::parse_quote! {
            use super::k;
            use other as host;
            mod language_host {}
        };
        assert_eq!(
            scoped.scoped(&nested.items).facade.aliases,
            BTreeSet::from(["k".to_owned()])
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
