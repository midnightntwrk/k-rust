//! Which imports a failed KRS item names, so that `krs check` can tell an
//! `unused_imports` error that follows from the failure from a real one.
//!
//! A KRS macro that rejects its item expands to `compile_error!` (and at most a
//! stand-in that names only facade paths), so the code that would have used
//! the item's imports does not exist when rustc runs its unused-import lint.
//! The lint's verdict about an import the failed item names is then a fact
//! about the withheld expansion, not about the authored program: the author
//! wrote a use of it, in an item that does not compile yet.

use proc_macro2::{Delimiter, Spacing, TokenStream, TokenTree};
use quote::ToTokens;
use std::collections::BTreeSet;
use syn::Item;
use syn::spanned::Spanned;

/// A source file parsed once, with byte offsets that match the file's.
pub(super) struct ParsedSource {
    file: syn::File,
}

impl ParsedSource {
    /// Parses `bytes`; `None` when they are not UTF-8 Rust that `syn` parses.
    pub(super) fn parse(bytes: &[u8]) -> Option<Self> {
        let mut text = std::str::from_utf8(bytes).ok()?.to_owned();
        // `syn::parse_file` drops a byte-order mark and a shebang line, which
        // would shift every offset; blank them instead.
        let start = if text.starts_with('\u{feff}') {
            text.replace_range(..'\u{feff}'.len_utf8(), "   ");
            '\u{feff}'.len_utf8()
        } else {
            0
        };
        if text[start..].starts_with("#!") && !text[start + 2..].trim_start().starts_with('[') {
            let end = text.find('\n').unwrap_or(text.len());
            text.replace_range(start..end, &" ".repeat(end - start));
        }
        syn::parse_str(&text).ok().map(|file| Self { file })
    }

    /// The innermost item that contains byte `offset`: an item with its
    /// attributes, a member of an `impl` (an `#[k::init]` method, not its
    /// whole `impl`), or a macro invocation such as `k::rules! { .. }`.
    pub(super) fn failed_item(&self, offset: usize) -> Option<FailedItem> {
        let mut modules = Vec::new();
        let tokens = innermost(&self.file.items, offset, &mut modules)?;
        let mut identifiers = BTreeSet::new();
        referencing_identifiers(tokens, &mut identifiers);
        Some(FailedItem {
            modules,
            identifiers,
        })
    }

    /// The inline modules enclosing the module-level `use` item that contains
    /// byte `offset`; `None` when no module-level `use` contains it (a `use`
    /// in a block is scoped to the block, not to its module).
    pub(super) fn use_module(&self, offset: usize) -> Option<Vec<String>> {
        let mut modules = Vec::new();
        let mut items = self.file.items.as_slice();
        loop {
            let item = items.iter().find(|item| contains(*item, offset))?;
            match item {
                Item::Use(_) => return Some(modules),
                Item::Mod(module) => {
                    let (_, content) = module.content.as_ref()?;
                    modules.push(module.ident.to_string());
                    items = content;
                }
                _ => return None,
            }
        }
    }
}

/// A KRS item that failed: the inline modules that enclose it in its file and
/// the identifiers it writes where they could name an imported item.
#[derive(Debug, PartialEq, Eq)]
pub(super) struct FailedItem {
    pub(super) modules: Vec<String>,
    pub(super) identifiers: BTreeSet<String>,
}

fn contains(node: &impl Spanned, offset: usize) -> bool {
    node.span().byte_range().contains(&offset)
}

fn innermost(items: &[Item], offset: usize, modules: &mut Vec<String>) -> Option<TokenStream> {
    let item = items.iter().find(|item| contains(*item, offset))?;
    match item {
        Item::Mod(module) => {
            if let Some((_, content)) = &module.content {
                modules.push(module.ident.to_string());
                if let Some(tokens) = innermost(content, offset, modules) {
                    return Some(tokens);
                }
                modules.pop();
            }
        }
        Item::Impl(implementation) => {
            if let Some(member) = implementation
                .items
                .iter()
                .find(|member| contains(*member, offset))
            {
                return Some(member.to_token_stream());
            }
        }
        _ => {}
    }
    Some(item.to_token_stream())
}

/// Collects the identifiers of `tokens`, nested groups included, that could
/// name an imported item: one whose first character after any underscores is
/// uppercase (a type, constructor, or constant), or one followed by `::`, `(`,
/// or a macro's `!` (a module, function, or macro). Any other snake-case
/// identifier is a binder or a cell or field label by KRS's spelling rule and
/// names no import, so a binder spelled like an import does not vouch for it.
fn referencing_identifiers(tokens: TokenStream, identifiers: &mut BTreeSet<String>) {
    let trees = tokens.into_iter().collect::<Vec<_>>();
    for (index, tree) in trees.iter().enumerate() {
        match tree {
            TokenTree::Group(group) => referencing_identifiers(group.stream(), identifiers),
            TokenTree::Ident(ident) => {
                let name = ident.to_string();
                let name = name.strip_prefix("r#").unwrap_or(&name);
                let capitalized = name
                    .trim_start_matches('_')
                    .chars()
                    .next()
                    .is_some_and(char::is_uppercase);
                let followed = match (trees.get(index + 1), trees.get(index + 2)) {
                    (Some(TokenTree::Punct(colon)), Some(TokenTree::Punct(second))) => {
                        colon.as_char() == ':'
                            && colon.spacing() == Spacing::Joint
                            && second.as_char() == ':'
                    }
                    _ => false,
                } || match trees.get(index + 1) {
                    Some(TokenTree::Group(group)) => group.delimiter() == Delimiter::Parenthesis,
                    Some(TokenTree::Punct(bang)) => {
                        bang.as_char() == '!' && bang.spacing() == Spacing::Alone
                    }
                    _ => false,
                };
                if capitalized || followed {
                    identifiers.insert(name.to_owned());
                }
            }
            TokenTree::Punct(_) | TokenTree::Literal(_) => {}
        }
    }
}

/// The name an import binds, from the text of its use-tree leaf (`bytes`,
/// `k::builtin::Map`, `k::builtin::set as s`); `None` for a glob, an
/// underscore import, a `self` leaf, or a group, whose bound names the text
/// alone does not give.
pub(super) fn imported_name(text: &str) -> Option<&str> {
    let text = text.trim();
    let name = match text.rsplit_once(" as ") {
        Some((_, alias)) => alias.trim(),
        None => text.rsplit("::").next()?.trim(),
    };
    let name = name.strip_prefix("r#").unwrap_or(name);
    let identifier = !name.is_empty()
        && name != "_"
        && name != "self"
        && name.chars().all(|c| c == '_' || c.is_alphanumeric());
    identifier.then_some(name)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn failed(source: &str, marker: &str) -> FailedItem {
        let parsed = ParsedSource::parse(source.as_bytes()).unwrap();
        parsed.failed_item(source.find(marker).unwrap()).unwrap()
    }

    fn names(item: &FailedItem) -> Vec<&str> {
        item.identifiers.iter().map(String::as_str).collect()
    }

    #[test]
    fn a_failed_item_is_the_innermost_item_and_names_only_referencing_identifiers() {
        let source = "\
use k::builtin::{list, set};

mod outer {
    k::rules! {
        for Machine;
        use Cmd::*;
        bump: { k: [Go(), ..], acc: set } => { acc: list::item(set) } where set: Int;
    }
}

impl Machine {
    pub fn other() {}
    #[k::init]
    pub fn init() -> Self { Self { k: k::k![], seen: set::empty() } }
}
";
        let rules = failed(source, "bump");
        assert_eq!(rules.modules, ["outer"]);
        // `set` is a binder and a cell content here, never followed by `::` or `(`.
        assert_eq!(
            names(&rules),
            ["Cmd", "Go", "Int", "Machine", "item", "k", "list", "rules"]
        );
        let init = failed(source, "#[k::init]");
        assert!(init.modules.is_empty());
        assert!(init.identifiers.contains("set"));
        assert!(!init.identifiers.contains("other"));
    }

    #[test]
    fn a_use_belongs_to_its_module_only_at_module_level() {
        let source = "\
use k::builtin::Map;
mod inner {
    use k::builtin::Set;
    fn f() { use k::builtin::List; }
}
";
        let parsed = ParsedSource::parse(source.as_bytes()).unwrap();
        let at = |marker: &str| parsed.use_module(source.find(marker).unwrap());
        assert_eq!(at("Map"), Some(Vec::new()));
        assert_eq!(at("Set"), Some(vec!["inner".to_owned()]));
        assert_eq!(at("List"), None);
    }

    #[test]
    fn offsets_survive_a_byte_order_mark_and_a_shebang() {
        let source = "\u{feff}#!/usr/bin/env run\nuse k::builtin::Map;\nk::rules! { Go() }\n";
        let parsed = ParsedSource::parse(source.as_bytes()).unwrap();
        assert_eq!(
            parsed.use_module(source.find("Map").unwrap()),
            Some(Vec::new())
        );
        let item = parsed.failed_item(source.find("Go").unwrap()).unwrap();
        assert!(item.identifiers.contains("Go"));
    }

    #[test]
    fn imported_names_are_the_alias_or_the_last_segment() {
        assert_eq!(imported_name("bytes"), Some("bytes"));
        assert_eq!(imported_name("k::builtin::Map"), Some("Map"));
        assert_eq!(imported_name("k::builtin::set as s"), Some("s"));
        assert_eq!(imported_name("r#type"), Some("type"));
        assert_eq!(imported_name("Cmd::*"), None);
        assert_eq!(imported_name("k::builtin::set as _"), None);
        assert_eq!(imported_name("self"), None);
        assert_eq!(imported_name("k::builtin::{Map, Set}"), None);
    }
}
