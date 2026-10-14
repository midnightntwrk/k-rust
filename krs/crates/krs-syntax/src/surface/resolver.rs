//! Resolution of KRS entry points under authored and generated facade names.

use std::collections::BTreeSet;

use syn::ext::IdentExt;
use syn::{Path, UseTree};

use super::{Entry, facade_member, resolve_under};

/// Resolves KRS entry points in a source scope.
/// Consumers must derive a resolver for the file root and each inline module from its items.
pub trait Resolve {
    /// The unraw member name when `path` names a member under a facade alias in scope.
    fn facade_member(&self, path: &Path) -> Option<String>;

    /// The entry point invoked by `path` in this scope.
    fn resolve(&self, path: &Path) -> Option<Entry> {
        Entry::from_name(&self.facade_member(path)?)
    }

    /// The resolver for a file or inline module whose items are `items`.
    fn scoped(&self, items: &[syn::Item]) -> Box<dyn Resolve>;
}

/// Resolves authored paths under one facade alias.
/// Imports do not change the alias.
#[derive(Clone, Debug)]
pub struct AuthoredResolver {
    alias: String,
}

impl AuthoredResolver {
    /// Creates a resolver for exactly `<alias>::<entry>`.
    #[must_use]
    pub fn new(alias: &str) -> Self {
        Self {
            alias: alias.to_owned(),
        }
    }
}

impl Resolve for AuthoredResolver {
    fn facade_member(&self, path: &Path) -> Option<String> {
        facade_member(path, &self.alias)
    }

    fn scoped(&self, _items: &[syn::Item]) -> Box<dyn Resolve> {
        Box::new(self.clone())
    }
}

/// Resolves authored paths and paths under the facade chosen by an expansion host.
#[derive(Clone, Debug)]
pub struct GeneratedResolver {
    authored: AuthoredResolver,
    facade: Path,
}

impl GeneratedResolver {
    /// Creates a resolver for `<alias>::<entry>` and `<facade>::<entry>`.
    #[must_use]
    pub fn new(alias: &str, facade: &Path) -> Self {
        Self {
            authored: AuthoredResolver::new(alias),
            facade: facade.clone(),
        }
    }
}

impl Resolve for GeneratedResolver {
    fn facade_member(&self, path: &Path) -> Option<String> {
        self.authored.facade_member(path)
    }

    fn resolve(&self, path: &Path) -> Option<Entry> {
        self.authored
            .resolve(path)
            .or_else(|| resolve_under(path, &self.facade))
    }

    fn scoped(&self, _items: &[syn::Item]) -> Box<dyn Resolve> {
        Box::new(self.clone())
    }
}

/// Resolves authored paths under the facade names available in one module.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct FacadeScope {
    aliases: BTreeSet<String>,
}

impl FacadeScope {
    /// Creates a module scope from the unraw facade names of a package.
    #[must_use]
    pub fn new(aliases: BTreeSet<String>) -> Self {
        Self { aliases }
    }

    /// The facade names available in this scope.
    #[must_use]
    pub fn aliases(&self) -> &BTreeSet<String> {
        &self.aliases
    }

    /// The resolver for a file or inline module whose items are `items`.
    ///
    /// A `use <facade> as <alias>;` or `extern crate <facade> as <alias>;` item adds `<alias>`.
    /// Other `use`, `extern crate`, and `mod` bindings shadow facade names in the type namespace.
    /// A relative import of an inherited facade name, such as `use super::k;`, preserves that name.
    #[must_use]
    pub fn scoped(&self, items: &[syn::Item]) -> Self {
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
                        .aliases
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
        let mut aliases = self.aliases.clone();
        aliases.retain(|alias| !shadowed.contains(alias));
        aliases.extend(added);
        Self { aliases }
    }

    /// Records facade aliases and shadowing type-namespace bindings in a top-level `use` tree.
    fn use_bindings(
        &self,
        tree: &UseTree,
        added: &mut BTreeSet<String>,
        shadowed: &mut BTreeSet<String>,
    ) {
        match tree {
            UseTree::Rename(rename) => {
                let binding = rename.rename.unraw().to_string();
                if self.aliases.contains(&rename.ident.unraw().to_string()) {
                    added.insert(binding);
                } else {
                    shadowed.insert(binding);
                }
            }
            UseTree::Name(name) => {
                let binding = name.ident.unraw().to_string();
                if !self.aliases.contains(&binding) {
                    shadowed.insert(binding);
                }
            }
            UseTree::Group(group) => {
                for tree in &group.items {
                    self.use_bindings(tree, added, shadowed);
                }
            }
            UseTree::Path(path) => {
                // Relative imports preserve inherited facade names.
                let relative = ["self", "super", "crate"]
                    .iter()
                    .any(|keyword| path.ident == keyword);
                let mut bound = BTreeSet::new();
                nested_bindings(&path.tree, &mut bound);
                shadowed.extend(
                    bound
                        .into_iter()
                        .filter(|name| !(relative && self.aliases.contains(name))),
                );
            }
            UseTree::Glob(_) => {}
        }
    }
}

impl Resolve for FacadeScope {
    fn facade_member(&self, path: &Path) -> Option<String> {
        self.aliases
            .iter()
            .find_map(|alias| facade_member(path, alias))
    }

    fn scoped(&self, items: &[syn::Item]) -> Box<dyn Resolve> {
        Box::new(Self::scoped(self, items))
    }
}

/// Records names bound by a `use` subtree below a path prefix.
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn module_items_rename_and_shadow_the_facade() {
        let root = FacadeScope::new(BTreeSet::from(["language_host".to_owned()]));
        let file: syn::File = syn::parse_quote! {
            use k::Term;
            use language_host as k;
            extern crate language_host as host;
        };
        let scoped = root.scoped(&file.items);
        assert_eq!(
            scoped.aliases,
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
            scoped.scoped(&nested.items).aliases,
            BTreeSet::from(["k".to_owned()])
        );
    }

    #[test]
    fn authored_and_generated_resolvers_are_object_safe() {
        let authored = AuthoredResolver::new("k");
        let resolver: &dyn Resolve = &authored;
        let items: syn::File = syn::parse_quote! {
            use k as renamed;
            mod k {}
        };
        let scoped = resolver.scoped(&items.items);
        assert_eq!(
            scoped.resolve(&syn::parse_quote!(k::rules)),
            Entry::from_name("rules")
        );
        assert_eq!(scoped.resolve(&syn::parse_quote!(renamed::rules)), None);
        assert_eq!(
            resolver
                .facade_member(&syn::parse_quote!(r#k::r#unknown))
                .as_deref(),
            Some("unknown")
        );

        let generated = GeneratedResolver::new("k", &syn::parse_quote!(::host::facade));
        let resolver: &dyn Resolve = &generated;
        assert_eq!(
            resolver.resolve(&syn::parse_quote!(::host::facade::rules)),
            Entry::from_name("rules")
        );
        assert_eq!(
            resolver.resolve(&syn::parse_quote!(k::rules)),
            Entry::from_name("rules")
        );
        assert_eq!(
            resolver.resolve(&syn::parse_quote!(host::facade::rules)),
            None
        );
        assert_eq!(
            resolver
                .scoped(&items.items)
                .resolve(&syn::parse_quote!(::host::facade::rules)),
            Entry::from_name("rules")
        );
    }

    #[test]
    fn grouped_and_raw_bindings_preserve_the_existing_scope_rules() {
        let root = FacadeScope::new(BTreeSet::from(["k".to_owned(), "host".to_owned()]));
        let file: syn::File = syn::parse_quote! {
            use {r#k as r#lang, other::{Type as host, Nested}};
            extern crate other as k;
        };
        let scoped = root.scoped(&file.items);
        assert_eq!(scoped.aliases(), &BTreeSet::from(["lang".to_owned()]));
        assert_eq!(
            scoped.resolve(&syn::parse_quote!(r#lang::r#rule)),
            Entry::from_name("rule")
        );
        assert_eq!(scoped.resolve(&syn::parse_quote!(k::rule)), None);
        assert_eq!(
            root.aliases(),
            &BTreeSet::from(["k".to_owned(), "host".to_owned()])
        );
    }

    #[test]
    fn scoped_resolution_through_the_trait_tracks_imports() {
        let scope = FacadeScope::new(BTreeSet::from(["host".to_owned()]));
        let resolver: &dyn Resolve = &scope;
        let file: syn::File = syn::parse_quote! { use host as k; };
        let scoped = resolver.scoped(&file.items);
        assert_eq!(
            scoped.resolve(&syn::parse_quote!(k::rules)),
            Entry::from_name("rules")
        );
        assert_eq!(resolver.resolve(&syn::parse_quote!(k::rules)), None);
    }
}
