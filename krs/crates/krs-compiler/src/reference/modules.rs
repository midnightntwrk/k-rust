//! The module files of a crate, read as rustc reads them: from the crate root, through each
//! out-of-line `mod name;` declaration, inline modules included.

use super::{ReferenceExpansionError, ReferenceSourceError};
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use syn::ext::IdentExt;

/// One module file of the crate.
pub(super) struct ModuleFile {
    /// The file on disk.
    pub(super) path: PathBuf,
    /// Its normalized `/`-separated path relative to the package root, as a descriptor's source
    /// file names it; `None` for a file outside the package directory.
    pub(super) relative: Option<String>,
    /// The module path of the file's own items, from the crate root.
    pub(super) module_path: Vec<String>,
    /// The file's text.
    pub(super) source: String,
    /// The file's exact bytes' digest.
    pub(super) digest: krs_ir::Sha256Digest,
    /// The file parsed.
    pub(super) parsed: syn::File,
}

/// The module files of a crate and, for each module it declares, the module its declaration is
/// visible in.
pub(super) struct ModuleTree {
    pub(super) files: Vec<ModuleFile>,
    visible_in: BTreeMap<Vec<String>, Vec<String>>,
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

impl std::fmt::Debug for ModuleTree {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("ModuleTree")
            .field(
                "files",
                &self.files.iter().map(|file| &file.path).collect::<Vec<_>>(),
            )
            .field("visible_in", &self.visible_in)
            .finish()
    }
}

impl ModuleTree {
    /// The module files rustc reads from `crate_root`, the library target's root file, in a
    /// package rooted at `package_root`.
    ///
    /// The files of a module under `#[cfg]` are kept only where `named` says a descriptor was
    /// collected from one of them: a module whose condition did not hold denotes nothing (its file
    /// may not even exist, or a module of the same name under the opposite condition may stand
    /// beside it), and one whose files hold no descriptor needs no printing. A module whose file a
    /// `cfg_attr` may choose is refused, since the source alone does not say which file rustc
    /// read.
    pub(super) fn read(
        crate_root: &Path,
        package_root: &Path,
        named: &dyn Fn(&str) -> bool,
    ) -> Result<Self, ReferenceExpansionError> {
        let package_root = package_root
            .canonicalize()
            .unwrap_or_else(|_| package_root.to_path_buf());
        let mut tree = Self {
            files: Vec::new(),
            visible_in: BTreeMap::new(),
        };
        let directory = crate_root.parent().unwrap_or(Path::new("."));
        // A crate root owns its directory, like a `mod.rs` file.
        let mut walk = Walk {
            package_root: &package_root,
            named,
            tree: &mut tree,
        };
        walk.file(crate_root, &ModuleDirectory::owned(directory), Vec::new())?;
        Ok(tree)
    }

    /// Whether `crate::m1::..::mk`, the path `module`, names its module from the module `from`:
    /// each module on it is declared visible where `from` stands.
    pub(super) fn reaches(&self, module: &[String], from: &[String]) -> bool {
        (1..=module.len()).all(|end| {
            self.visible_in
                .get(&module[..end])
                .is_some_and(|visible_in| from.starts_with(visible_in))
        })
    }
}

struct Walk<'a> {
    package_root: &'a Path,
    named: &'a dyn Fn(&str) -> bool,
    tree: &'a mut ModuleTree,
}

impl Walk<'_> {
    fn file(
        &mut self,
        path: &Path,
        directory: &ModuleDirectory,
        module_path: Vec<String>,
    ) -> Result<(), ReferenceExpansionError> {
        let source_error = ReferenceExpansionError::Source;
        let bytes = fs::read(path).map_err(|error| {
            source_error(ReferenceSourceError::Read {
                path: path.to_path_buf(),
                error,
            })
        })?;
        let digest =
            krs_ir::Sha256Digest::from_bytes(<sha2::Sha256 as sha2::Digest>::digest(&bytes).into());
        let source = String::from_utf8(bytes).map_err(|error| {
            source_error(ReferenceSourceError::Encoding {
                path: path.to_path_buf(),
                error: error.utf8_error(),
            })
        })?;
        let parsed = syn::parse_file(&source).map_err(ReferenceExpansionError::RustSyntax)?;
        let relative = path
            .canonicalize()
            .ok()
            .and_then(|canonical| {
                canonical
                    .strip_prefix(self.package_root)
                    .ok()
                    .map(Path::to_path_buf)
            })
            .and_then(|relative| {
                relative
                    .components()
                    .map(|component| component.as_os_str().to_str().map(str::to_owned))
                    .collect::<Option<Vec<_>>>()
            })
            .map(|segments| segments.join("/"));
        self.items(path, &parsed.items, directory, &module_path)?;
        self.tree.files.push(ModuleFile {
            path: path.to_path_buf(),
            relative,
            module_path,
            source,
            digest,
            parsed,
        });
        Ok(())
    }

    fn items(
        &mut self,
        file: &Path,
        items: &[syn::Item],
        directory: &ModuleDirectory,
        module_path: &[String],
    ) -> Result<(), ReferenceExpansionError> {
        for item in items {
            let syn::Item::Mod(module) = item else {
                continue;
            };
            let name = module.ident.unraw().to_string();
            let mut child_path = module_path.to_vec();
            child_path.push(name.clone());
            // Two declarations of one module (under exclusive `cfg`s) may differ in visibility:
            // the narrower, which is the longer path, is the one known to hold.
            let visible = visible_in(&module.vis, module_path);
            self.tree
                .visible_in
                .entry(child_path.clone())
                .and_modify(|known| {
                    if visible.len() > known.len() {
                        known.clone_from(&visible);
                    }
                })
                .or_insert(visible);
            let configured = module
                .attrs
                .iter()
                .any(|attribute| attribute.path().is_ident("cfg"));
            if !configured {
                self.module(file, module, directory, child_path)?;
                continue;
            }
            let kept = self.tree.files.len();
            let walked = self.module(file, module, directory, child_path);
            let collected = self.tree.files[kept..].iter().any(|walked| {
                walked
                    .relative
                    .as_deref()
                    .is_some_and(|relative| (self.named)(relative))
            });
            if walked.is_err() || !collected {
                self.tree.files.truncate(kept);
            }
        }
        Ok(())
    }

    /// Follows the module `module`, declared among the items of `file` in `directory`, whose path
    /// is `child_path`.
    fn module(
        &mut self,
        file: &Path,
        module: &syn::ItemMod,
        directory: &ModuleDirectory,
        child_path: Vec<String>,
    ) -> Result<(), ReferenceExpansionError> {
        let name = module.ident.unraw().to_string();
        let path_attribute = module_path_attribute(module);
        if let Some((_, items)) = &module.content {
            let nested = match path_attribute {
                Some(path) => ModuleDirectory::owned(&directory.path.join(path)),
                None => ModuleDirectory::owned(&directory.children().join(&name)),
            };
            return self.items(file, items, &nested, &child_path);
        }
        if module.attrs.iter().any(applies_path_conditionally) {
            return Err(ReferenceExpansionError::Source(
                ReferenceSourceError::ConditionalModulePath {
                    file: file.to_path_buf(),
                    module: child_path.join("::"),
                },
            ));
        }
        if let Some(path) = path_attribute {
            let child = directory.path.join(path);
            let parent = child.parent().unwrap_or(&directory.path).to_path_buf();
            return self.file(&child, &ModuleDirectory::owned(&parent), child_path);
        }
        let base = directory.children();
        let flat = base.join(format!("{name}.rs"));
        let nested = base.join(&name).join("mod.rs");
        if flat.is_file() {
            let child = ModuleDirectory {
                path: base,
                relative: Some(name),
            };
            self.file(&flat, &child, child_path)
        } else if nested.is_file() {
            self.file(
                &nested,
                &ModuleDirectory::owned(&base.join(&name)),
                child_path,
            )
        } else {
            // rustc reports a missing module file; reading it reports it here.
            self.file(&flat, &ModuleDirectory::owned(&base), child_path)
        }
    }
}

/// The module within which an item of the module `parent` with visibility `visibility` is
/// visible: the module itself for a private item (and its descendants, as Rust's privacy
/// reaches them), the crate root for `pub` and `pub(crate)`. A restriction this does not read
/// is taken as the narrowest, the module itself, which every visibility includes.
fn visible_in(visibility: &syn::Visibility, parent: &[String]) -> Vec<String> {
    match visibility {
        syn::Visibility::Public(_) => Vec::new(),
        syn::Visibility::Inherited => parent.to_vec(),
        syn::Visibility::Restricted(restricted) => {
            let mut segments = restricted
                .path
                .segments
                .iter()
                .map(|segment| segment.ident.unraw().to_string());
            match segments.next().as_deref() {
                Some("crate") if restricted.path.leading_colon.is_none() => segments.collect(),
                Some("super") if restricted.path.segments.len() == 1 && !parent.is_empty() => {
                    parent[..parent.len() - 1].to_vec()
                }
                _ => parent.to_vec(),
            }
        }
    }
}

/// The `#[path = ".."]` value of a module.
fn module_path_attribute(module: &syn::ItemMod) -> Option<String> {
    module
        .attrs
        .iter()
        .find_map(|attribute| path_value(&attribute.meta))
}

fn path_value(meta: &syn::Meta) -> Option<String> {
    let syn::Meta::NameValue(name_value) = meta else {
        return None;
    };
    if !name_value.path.is_ident("path") {
        return None;
    }
    match &name_value.value {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Str(path),
            ..
        }) => Some(path.value()),
        _ => None,
    }
}

/// Whether an attribute is a `cfg_attr` that may apply a `path`, directly or nested.
fn applies_path_conditionally(attribute: &syn::Attribute) -> bool {
    fn applies(meta: &syn::Meta) -> bool {
        let syn::Meta::List(list) = meta else {
            return false;
        };
        if !list.path.is_ident("cfg_attr") {
            return false;
        }
        list.parse_args_with(
            syn::punctuated::Punctuated::<syn::Meta, syn::Token![,]>::parse_terminated,
        )
        .is_ok_and(|arguments| {
            arguments
                .iter()
                .skip(1)
                .any(|argument| path_value(argument).is_some() || applies(argument))
        })
    }
    applies(&attribute.meta)
}

#[cfg(test)]
mod tests {
    use super::ModuleTree;
    use std::fs;

    #[test]
    fn the_tree_follows_mod_declarations_and_records_where_each_module_is_visible() {
        let root =
            std::env::temp_dir().join(format!("krs-reference-modules-{}", std::process::id()));
        let write = |path: &str, text: &str| {
            let path = root.join(path);
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(path, text).unwrap();
        };
        write(
            "src/lib.rs",
            "pub mod a;\nmod b;\n#[cfg(any())] mod gone;\n#[cfg(any())] mod held;\nmod c { pub(crate) mod d { mod e {} } pub(super) mod f {} }\n#[path = \"elsewhere/g.rs\"] mod g;\n#[cfg(all())] #[path = \"twin_a.rs\"] mod twin;\n#[cfg(any())] #[path = \"twin_b.rs\"] mod twin;\n",
        );
        write("src/a.rs", "mod inner;\n");
        write("src/a/inner.rs", "");
        write("src/b/mod.rs", "pub mod deep;\n");
        write("src/b/deep.rs", "");
        write("src/held.rs", "");
        write("src/elsewhere/g.rs", "");
        write("src/twin_a.rs", "");
        write("src/twin_b.rs", "");
        // The twin under the condition that held is the one a descriptor names.
        let named = |file: &str| matches!(file, "src/held.rs" | "src/twin_a.rs");
        let tree = ModuleTree::read(&root.join("src/lib.rs"), &root, &named).unwrap();
        let files = tree
            .files
            .iter()
            .map(|file| (file.relative.clone().unwrap(), file.module_path.join("::")))
            .collect::<Vec<_>>();
        let path = |segments: &[&str]| segments.iter().map(|s| (*s).to_owned()).collect::<Vec<_>>();
        fs::remove_dir_all(&root).unwrap();
        assert_eq!(
            files,
            [
                ("src/a/inner.rs", "a::inner"),
                ("src/a.rs", "a"),
                ("src/b/deep.rs", "b::deep"),
                ("src/b/mod.rs", "b"),
                ("src/held.rs", "held"),
                ("src/elsewhere/g.rs", "g"),
                ("src/twin_a.rs", "twin"),
                ("src/lib.rs", ""),
            ]
            .map(|(file, module)| (file.to_owned(), module.to_owned()))
        );
        // A child of the crate root is visible everywhere; a private module only inside its parent.
        assert!(tree.reaches(&path(&["b", "deep"]), &path(&["a"])));
        assert!(!tree.reaches(&path(&["a", "inner"]), &path(&["b"])));
        assert!(tree.reaches(&path(&["a", "inner"]), &path(&["a"])));
        assert!(tree.reaches(&path(&["a", "inner"]), &path(&["a", "inner"])));
        assert!(tree.reaches(&path(&["c", "d"]), &path(&["b"])));
        assert!(!tree.reaches(&path(&["c", "d", "e"]), &path(&["b"])));
        assert!(tree.reaches(&path(&["c", "d", "e"]), &path(&["c", "d"])));
        assert!(tree.reaches(&path(&["c", "f"]), &path(&[])));
    }

    #[test]
    fn a_module_whose_file_a_cfg_attr_may_choose_is_refused() {
        let root = std::env::temp_dir().join(format!(
            "krs-reference-modules-cfg-attr-{}",
            std::process::id()
        ));
        fs::create_dir_all(root.join("src")).unwrap();
        fs::write(
            root.join("src/lib.rs"),
            "#[cfg_attr(unix, path = \"unix.rs\")]\nmod platform;\n",
        )
        .unwrap();
        fs::write(root.join("src/platform.rs"), "").unwrap();
        let error = ModuleTree::read(&root.join("src/lib.rs"), &root, &|_: &str| false)
            .unwrap_err()
            .to_string();
        fs::remove_dir_all(&root).unwrap();
        assert!(
            error.contains("expand cannot tell which file the module `platform` declared in"),
            "{error}"
        );
    }
}
