use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
};

use quote::ToTokens;
use serde::Deserialize;
use syn::{
    spanned::Spanned,
    visit::{self, Visit},
};

use crate::model::{Anchor, Cost};

#[derive(Clone, Debug, Deserialize)]
#[serde(untagged)]
pub(crate) enum Representation {
    Path(String),
    WithRole(RoleRepresentation),
}

/// A `{ type, role }` representation table; unknown keys are rejected.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct RoleRepresentation {
    #[serde(rename = "type")]
    type_path: String,
    role: String,
}

impl Representation {
    pub(crate) fn type_path(&self) -> &str {
        match self {
            Self::Path(path) => path,
            Self::WithRole(representation) => &representation.type_path,
        }
    }

    pub(crate) fn role(&self) -> Option<&str> {
        match self {
            Self::Path(_) => None,
            Self::WithRole(representation) => Some(&representation.role),
        }
    }

    pub(crate) fn id(&self) -> String {
        match self.role() {
            Some(role) => format!("{} [{role}]", self.type_path()),
            None => self.type_path().to_owned(),
        }
    }
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct Constraint {
    pub id: String,
    pub site: String,
    pub via: String,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct CardCost {
    pub mode: String,
    pub bound: String,
}

impl From<&CardCost> for Cost {
    fn from(value: &CardCost) -> Self {
        Self {
            mode: value.mode.clone(),
            bound: value.bound.clone(),
        }
    }
}

#[derive(Clone, Debug, Default, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct CardBody {
    pub id: String,
    #[serde(default)]
    pub name: Option<String>,
    #[serde(default)]
    pub sites: Vec<String>,
    #[serde(default)]
    pub role: Option<String>,
    #[serde(default)]
    pub variable: Option<String>,
    #[serde(default)]
    pub counters: Vec<String>,
    #[serde(default)]
    pub no_counter: Option<String>,
    #[serde(default)]
    pub invariant: Option<String>,
    #[serde(default)]
    pub consumes: Vec<Representation>,
    #[serde(default)]
    pub produces: Vec<Representation>,
    #[serde(default)]
    pub constrains: Vec<Constraint>,
    #[serde(default)]
    pub variant_of: Option<String>,
    #[serde(default)]
    pub falls_back_to: Vec<String>,
    #[serde(default)]
    pub span: Option<String>,
    #[serde(default)]
    pub tests: Vec<String>,
    #[serde(default)]
    pub cost: Vec<CardCost>,
    /// Lean theorems whose models mirror the card's sites; each must be a line of
    /// `lean/theorems.txt`.
    #[serde(default)]
    pub lean: Vec<String>,
    /// The workspace type a representation card describes.
    #[serde(default, rename = "type")]
    pub type_path: Option<String>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum CardKind {
    Primary,
    Site,
    Contract,
    /// An `algorithm-representation` fence: the invariants every value of one workspace type
    /// satisfies, anchored at the sites that establish them.
    Representation,
}

#[derive(Clone, Debug)]
pub(crate) struct Card {
    pub kind: CardKind,
    pub body: CardBody,
    pub crate_name: String,
    pub file: String,
    pub source: String,
}

impl Card {
    pub(crate) fn site_anchors(&self) -> Vec<Anchor> {
        self.body
            .sites
            .iter()
            .map(|symbol| Anchor {
                crate_name: self.crate_name.clone(),
                file: self.file.clone(),
                symbol: symbol.clone(),
            })
            .collect()
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct SourceIndex {
    pub symbols: BTreeMap<(String, String), BTreeMap<String, usize>>,
    pub types: BTreeMap<(String, String), Vec<Anchor>>,
    pub files: BTreeMap<String, SourceFacts>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct SourceFacts {
    pub algorithm_spans: BTreeSet<String>,
    pub raw_algo_spans: usize,
    pub has_invariant_loop: bool,
    /// Outcome patterns outside `#[cfg(test)]` modules; see [`OutcomePattern`].
    pub outcome_patterns: BTreeSet<OutcomePattern>,
    /// Names bound by the file's `use` declarations outside function bodies and `#[cfg(test)]`
    /// modules, mapped to the path segments as written: `use a::b::Name` binds `Name` to
    /// `[a, b, Name]`, `use a::b::X as Name` binds `Name` to `[a, b, X]`, and `use a::b::{self}`
    /// binds `b` to `[a, b]`.
    pub imports: BTreeMap<String, Vec<String>>,
    /// Path prefixes of the file's glob `use` declarations, as `[super]` for `use super::*`.
    pub glob_imports: BTreeSet<Vec<String>>,
    /// The counters the file's items bump, outside `#[cfg(test)]` code; see [`CounterBump`].
    pub counter_bumps: BTreeSet<CounterBump>,
}

/// The file that declares `Counter`; its `Counter::X` paths declare and name counters, they do
/// not count work.
pub(crate) const COUNTER_DECLARATION_FILE: &str = "crates/k-rust-kore/src/measure.rs";

/// A `Counter::X` path in an item: outside the file that declares `Counter`, the item that
/// writes it bumps the counter or passes it to a function that does, so the work it measures is
/// done there. A path inside a macro's tokens (`debug_assert!`) counts too.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct CounterBump {
    /// The site symbols that name the enclosing top-level item, most specific first: `function`,
    /// or `Type::method` then `impl Type`; empty where no site symbol names the item (a trait's
    /// default method, a constant's initializer, a method of an `impl` whose type is not a path).
    pub sites: Vec<String>,
    /// The counter's variant name, as `MatchingPairs` in `Counter::MatchingPairs`.
    pub counter: String,
}

/// Where a counter bump belongs among the algorithms whose cards claim the counter.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum CountedSite<'a> {
    /// No card claims the counter, or the bump is in the file that declares `Counter`.
    Unclaimed,
    /// The enclosing item is a named site (an anchor or a `sites` entry) of a claimant.
    Named,
    /// No claimant names the enclosing item, so it is a counted site of every claimant.
    Counted {
        symbol: &'a str,
        algorithms: &'a BTreeSet<String>,
    },
    /// Claimants exist, but no site symbol names the enclosing item.
    Unnameable { algorithms: &'a BTreeSet<String> },
}

/// The counters each algorithm's cards claim, and the items they name.
///
/// A counter listed in an algorithm card's `counters` measures that algorithm's work, so an item
/// that bumps it does some claimant's work. Each such item is a site of a claimant: one a card
/// names, or else a counted site of every claimant, derived here from the code instead of being
/// written on a card. "A claimant", not "every claimant": a caller may claim a callee
/// algorithm's counter, measured inside its spans, and the callee's card naming the item already
/// places the work.
#[derive(Debug, Default)]
pub(crate) struct CounterClaims {
    claimants: BTreeMap<String, BTreeSet<String>>,
    named: BTreeMap<String, BTreeSet<(String, String)>>,
}

impl CounterClaims {
    pub(crate) fn new(cards: &[Card]) -> Self {
        let mut claims = Self::default();
        for card in cards
            .iter()
            .filter(|card| matches!(card.kind, CardKind::Primary | CardKind::Site))
        {
            for counter in &card.body.counters {
                claims
                    .claimants
                    .entry(counter.clone())
                    .or_default()
                    .insert(card.body.id.clone());
            }
            claims
                .named
                .entry(card.body.id.clone())
                .or_default()
                .extend(
                    card.body
                        .sites
                        .iter()
                        .map(|symbol| (card.file.clone(), symbol.clone())),
                );
        }
        claims
    }

    /// Where a bump in `file` belongs.
    pub(crate) fn place<'a>(&'a self, file: &str, bump: &'a CounterBump) -> CountedSite<'a> {
        let Some(algorithms) = self.claimants.get(&bump.counter) else {
            return CountedSite::Unclaimed;
        };
        if file == COUNTER_DECLARATION_FILE {
            return CountedSite::Unclaimed;
        }
        let Some(symbol) = bump.sites.first() else {
            return CountedSite::Unnameable { algorithms };
        };
        let named = algorithms.iter().any(|algorithm| {
            self.named.get(algorithm).is_some_and(|named| {
                bump.sites
                    .iter()
                    .any(|site| named.contains(&(file.to_owned(), site.clone())))
            })
        });
        if named {
            CountedSite::Named
        } else {
            CountedSite::Counted { symbol, algorithms }
        }
    }
}

/// One identifier named by an outcome pattern.
///
/// An outcome pattern is a `match` arm, `let`, `let`-`else`, `if let`, or `while let` pattern, or
/// the pattern argument of `matches!`, whose scrutinee is a function call once references,
/// parentheses, and `?` are removed, or a local variable that `let name = function(..);` bound
/// earlier in the same top-level item. Every path segment inside the pattern is an identifier it
/// names, as `MatchResult` and `Failed` in `MatchResult::Failed(_)`; type ascriptions inside the
/// pattern name nothing.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct OutcomePattern {
    /// The enclosing top-level item in site form: `function` or `Type::method`; `None` outside a
    /// function body.
    pub item: Option<String>,
    /// The last path segment of the called function, as `match_terms` in
    /// `crate::matching::match_terms(..)`, directly or through the local binding.
    pub callee: String,
    pub identifier: String,
    /// The segments of the pattern path up to and including `identifier`, as written.
    pub path: Vec<String>,
}

impl SourceIndex {
    fn insert_file(
        &mut self,
        crate_name: &str,
        relative: &str,
        visitor: ItemVisitor,
        has_invariant_comment: bool,
    ) {
        self.symbols.insert(
            (crate_name.to_owned(), relative.to_owned()),
            visitor.symbols,
        );
        for type_name in visitor.types {
            self.types
                .entry((crate_name.to_owned(), type_name.clone()))
                .or_default()
                .push(Anchor {
                    crate_name: crate_name.to_owned(),
                    file: relative.to_owned(),
                    symbol: type_name,
                });
        }
        self.files.insert(
            relative.to_owned(),
            SourceFacts {
                algorithm_spans: visitor.algorithm_spans,
                raw_algo_spans: visitor.raw_algo_spans,
                has_invariant_loop: visitor.has_loop && has_invariant_comment,
                outcome_patterns: visitor.outcome_patterns,
                imports: visitor.imports,
                glob_imports: visitor.glob_imports,
                counter_bumps: visitor.counter_bumps,
            },
        );
    }

    pub(crate) fn symbol_count(&self, crate_name: &str, file: &str, symbol: &str) -> usize {
        self.symbols
            .get(&(crate_name.to_owned(), file.to_owned()))
            .and_then(|symbols| symbols.get(symbol))
            .copied()
            .unwrap_or(0)
    }

    /// Resolve a path written in `file` to an absolute path whose first segment is a crate name
    /// with underscores, as `k_rust_kore::kore::ast::Sentence`.
    ///
    /// The first segment is resolved in this order: `crate`, `self`, and `super` relative to the
    /// file's module; a name bound by an explicit `use` in the file; a type the file defines; a
    /// name bound by an explicit `use` in, or a type defined by, the workspace module file that a
    /// glob `use` of the file names (one level, not transitively). An explicit `use` of a path
    /// outside the workspace resolves to that path as written. A first segment that none of these
    /// bind is resolved only when it names a workspace crate. A resolved path that crosses a
    /// crate root's own `use` re-export, as `k_rust::kore` for `pub use k_rust_kore::kore`, is
    /// rewritten through that re-export. `None` means the path could not be resolved.
    pub(crate) fn resolve_path(&self, file: &str, path: &[String]) -> Option<Vec<String>> {
        let resolved = self.resolve_in_file(file, path, true, 0)?;
        Some(self.follow_root_reexports(resolved))
    }

    fn resolve_in_file(
        &self,
        file: &str,
        path: &[String],
        globs: bool,
        depth: usize,
    ) -> Option<Vec<String>> {
        // Bounds resolution through `use` declarations that name each other.
        if depth > 8 {
            return None;
        }
        let (first, rest) = path.split_first()?;
        let module = module_path(file)?;
        let absolute = |head: Vec<String>| -> Vec<String> {
            head.into_iter().chain(rest.iter().cloned()).collect()
        };
        match first.as_str() {
            "crate" => return Some(absolute(module[..1].to_vec())),
            "self" => return Some(absolute(module)),
            "super" => {
                let supers = path
                    .iter()
                    .take_while(|segment| *segment == "super")
                    .count();
                let mut parent = module;
                parent.truncate(parent.len().saturating_sub(supers).max(1));
                return Some(
                    parent
                        .into_iter()
                        .chain(path[supers..].iter().cloned())
                        .collect(),
                );
            }
            _ => {}
        }
        let facts = self.files.get(file)?;
        if let Some(imported) = facts.imports.get(first) {
            // `use name;` of an external crate binds the name to itself; resolving it again
            // would not terminate.
            let target = if imported.first() == Some(first) {
                imported.clone()
            } else {
                self.resolve_in_file(file, imported, false, depth + 1)
                    .unwrap_or_else(|| imported.clone())
            };
            return Some(target.into_iter().chain(rest.iter().cloned()).collect());
        }
        if self.defines_type(file, first) {
            let mut defined = module;
            defined.push(first.clone());
            return Some(absolute(defined));
        }
        if globs {
            for glob in &facts.glob_imports {
                let Some(target) = self.resolve_in_file(file, glob, false, depth + 1) else {
                    continue;
                };
                let Some(target_file) = self.module_file(&target) else {
                    continue;
                };
                if self.files.get(target_file)?.imports.contains_key(first)
                    || self.defines_type(target_file, first)
                {
                    return self.resolve_in_file(target_file, path, false, depth + 1);
                }
            }
        }
        self.is_workspace_crate(first).then(|| path.to_vec())
    }

    fn follow_root_reexports(&self, mut path: Vec<String>) -> Vec<String> {
        for _ in 0..4 {
            let Some(root) = path
                .first()
                .and_then(|crate_name| self.module_file(std::slice::from_ref(crate_name)))
            else {
                break;
            };
            let Some(reexport) = path
                .get(1)
                .and_then(|name| self.files.get(root)?.imports.get(name))
            else {
                break;
            };
            let Some(target) = self.resolve_in_file(root, reexport, false, 0) else {
                break;
            };
            if target[..] == path[..2] {
                break;
            }
            path = target.into_iter().chain(path.drain(2..)).collect();
        }
        path
    }

    fn defines_type(&self, file: &str, name: &str) -> bool {
        crate_directory(file).is_some_and(|crate_name| {
            self.resolve_type(crate_name, name)
                .iter()
                .any(|anchor| anchor.file == file)
        })
    }

    fn is_workspace_crate(&self, crate_ident: &str) -> bool {
        self.module_file(&[crate_ident.to_owned()]).is_some()
    }

    /// The workspace file of an absolute module path, as `crates/k-rust/src/kompile/module_to_kore.rs`
    /// for `k_rust::kompile::module_to_kore`.
    fn module_file(&self, module: &[String]) -> Option<&str> {
        let (crate_ident, modules) = module.split_first()?;
        let base = format!("crates/{}/src", crate_ident.replace('_', "-"));
        let candidates = if modules.is_empty() {
            vec![format!("{base}/lib.rs"), format!("{base}/main.rs")]
        } else {
            let joined = modules.join("/");
            vec![
                format!("{base}/{joined}.rs"),
                format!("{base}/{joined}/mod.rs"),
            ]
        };
        candidates
            .into_iter()
            .find_map(|candidate| self.files.get_key_value(&candidate))
            .map(|(file, _)| file.as_str())
    }

    pub(crate) fn resolve_type(&self, crate_name: &str, symbol: &str) -> &[Anchor] {
        self.types
            .get(&(crate_name.to_owned(), symbol.to_owned()))
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }
}

pub(crate) fn read_cards(
    root: &Path,
    report: &mut Vec<String>,
) -> std::io::Result<(Vec<Card>, SourceIndex)> {
    let mut files = Vec::new();
    let crates = root.join("crates");
    if crates.is_dir() {
        for entry in fs::read_dir(crates)? {
            let path = entry?.path();
            if path.is_dir() {
                collect_rust_files(&path.join("src"), &mut files)?;
            }
        }
    }
    files.sort();
    let mut sources = Vec::with_capacity(files.len());
    for path in files {
        sources.push((relative_path(root, &path), fs::read_to_string(&path)?));
    }
    Ok(index_sources(sources, report))
}

/// The cards and source index of the workspace source files `sources`, each a path relative to
/// the workspace root (`crates/<crate>/src/...`) with its text.
pub(crate) fn index_sources(
    sources: Vec<(String, String)>,
    report: &mut Vec<String>,
) -> (Vec<Card>, SourceIndex) {
    let mut cards = Vec::new();
    let mut index = SourceIndex::default();
    for (relative, source) in sources {
        let Some(crate_name) = crate_name(&relative) else {
            continue;
        };
        match syn::parse_file(&source) {
            Ok(file) => {
                let mut visitor = ItemVisitor::default();
                visitor.visit_file(&file);
                for (kind, source) in extract_fences(&visitor.docs) {
                    match toml::from_str::<CardBody>(&source) {
                        Ok(body) => cards.push(Card {
                            kind,
                            body,
                            crate_name: crate_name.clone(),
                            file: relative.clone(),
                            source,
                        }),
                        Err(error) => report.push(format!(
                            "unresolved card in {relative}: invalid TOML: {error}"
                        )),
                    }
                }
                let has_invariant_comment = source.contains("Invariant:");
                index.insert_file(&crate_name, &relative, visitor, has_invariant_comment);
            }
            Err(error) => report.push(format!(
                "unresolved source index for {relative}: Rust parse failed: {error}"
            )),
        }
    }
    (cards, index)
}

fn collect_rust_files(directory: &Path, files: &mut Vec<PathBuf>) -> std::io::Result<()> {
    if !directory.is_dir() {
        return Ok(());
    }
    for entry in fs::read_dir(directory)? {
        let path = entry?.path();
        if path.is_dir() {
            collect_rust_files(&path, files)?;
        } else if path.extension().is_some_and(|extension| extension == "rs") {
            files.push(path);
        }
    }
    Ok(())
}

fn relative_path(root: &Path, path: &Path) -> String {
    path.strip_prefix(root)
        .unwrap_or(path)
        .components()
        .map(|component| component.as_os_str().to_string_lossy())
        .collect::<Vec<_>>()
        .join("/")
}

fn crate_directory(relative: &str) -> Option<&str> {
    relative.split('/').nth(1)
}

/// The absolute module path of a workspace source file, as `[k_rust, kompile, module_to_kore]`
/// for `crates/k-rust/src/kompile/module_to_kore.rs`.
fn module_path(relative: &str) -> Option<Vec<String>> {
    let rest = relative.strip_prefix("crates/")?;
    let (crate_directory, rest) = rest.split_once("/src/")?;
    let mut module = vec![crate_directory.replace('-', "_")];
    let rest = rest.strip_suffix(".rs")?;
    if rest != "lib" && rest != "main" {
        let mut segments = rest.split('/').collect::<Vec<_>>();
        if segments.last() == Some(&"mod") {
            segments.pop();
        }
        module.extend(segments.into_iter().map(ToOwned::to_owned));
    }
    Some(module)
}

/// Whether a workspace-relative path is a source file the graph reads: a `.rs` file below a
/// crate's `src` directory (`crates/<crate>/src/...`), as [`read_cards`] collects them.
pub(crate) fn is_graph_source(relative: &str) -> bool {
    let parts = relative.split('/').collect::<Vec<_>>();
    parts.len() > 3 && parts[0] == "crates" && parts[2] == "src" && relative.ends_with(".rs")
}

pub(crate) fn crate_name(relative: &str) -> Option<String> {
    relative.split('/').nth(1).map(ToOwned::to_owned)
}

fn extract_fences(docs: &[LocatedDoc]) -> Vec<(CardKind, String)> {
    let mut fences = Vec::new();
    let mut current: Option<(CardKind, String)> = None;
    for doc in docs.iter().map(|doc| doc.value.as_str()) {
        if let Some((kind, body)) = &mut current {
            if doc.trim() == "```" {
                fences.push((*kind, std::mem::take(body)));
                current = None;
            } else {
                body.push_str(doc.strip_prefix(' ').unwrap_or(doc));
                body.push('\n');
            }
            continue;
        }
        current = match doc.trim() {
            "```toml algorithm" | "```algorithm" => Some((CardKind::Primary, String::new())),
            "```toml algorithm-site" | "```algorithm-site" => Some((CardKind::Site, String::new())),
            "```toml algorithm-contract" | "```algorithm-contract" => {
                Some((CardKind::Contract, String::new()))
            }
            "```toml algorithm-representation" | "```algorithm-representation" => {
                Some((CardKind::Representation, String::new()))
            }
            _ => None,
        };
    }
    fences
}

/// The source lines of one item that a site symbol names.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct ItemSpan {
    /// First line of the item, including its attributes and documentation, 1-based.
    pub start: usize,
    /// Last line of the item, inclusive.
    pub end: usize,
    /// The item holds code that can execute: a function, a method, or an `impl` block. A struct,
    /// enum, union, or type alias holds none.
    pub code: bool,
}

/// The lines of every item in `source` that a site symbol can name, keyed like the source
/// index's symbols: `function`, `Type::method`, `impl Type`, and `Type`.
pub(crate) fn item_spans(source: &str) -> syn::Result<BTreeMap<String, Vec<ItemSpan>>> {
    let file = syn::parse_file(source)?;
    let mut visitor = ItemVisitor::default();
    visitor.visit_file(&file);
    Ok(visitor.item_spans)
}

/// One doc attribute (a `///` or `//!` line) and the source lines it spans.
#[derive(Clone, Debug)]
pub(crate) struct LocatedDoc {
    pub value: String,
    pub start: usize,
    pub end: usize,
}

/// A source file as `algo-graph drift` compares it: its doc attributes in source order, and each
/// item a site symbol can name, under that symbol (named as [`item_spans`] names it), with the
/// item's tokens, and its counter bumps.
pub(crate) struct NamedSource {
    pub docs: Vec<LocatedDoc>,
    pub items: BTreeMap<String, Vec<(ItemSpan, proc_macro2::TokenStream)>>,
    pub counter_bumps: BTreeSet<CounterBump>,
}

pub(crate) fn named_source(source: &str) -> syn::Result<NamedSource> {
    let file = syn::parse_file(source)?;
    let mut visitor = ItemVisitor {
        item_tokens: Some(BTreeMap::new()),
        ..ItemVisitor::default()
    };
    visitor.visit_file(&file);
    let mut tokens = visitor.item_tokens.unwrap_or_default();
    let items = visitor
        .item_spans
        .into_iter()
        .map(|(symbol, spans)| {
            let tokens = tokens.remove(&symbol).unwrap_or_default();
            (symbol, spans.into_iter().zip(tokens).collect())
        })
        .collect();
    Ok(NamedSource {
        docs: visitor.docs,
        items,
        counter_bumps: visitor.counter_bumps,
    })
}

/// The one namer of the items a card's `sites` entries name: the graph's source index, the item
/// spans that coverage and profiles attribute lines by, and `algo-graph drift` all read a file
/// through it, so a symbol names the same item everywhere.
#[derive(Default)]
struct ItemVisitor {
    symbols: BTreeMap<String, usize>,
    /// The lines of each symbol's items; a symbol that resolves to several items has several.
    item_spans: BTreeMap<String, Vec<ItemSpan>>,
    /// The tokens of each symbol's items, in the order of `item_spans`; recorded only when
    /// `Some`, for `algo-graph drift`.
    item_tokens: Option<BTreeMap<String, Vec<proc_macro2::TokenStream>>>,
    types: BTreeSet<String>,
    docs: Vec<LocatedDoc>,
    algorithm_spans: BTreeSet<String>,
    raw_algo_spans: usize,
    has_loop: bool,
    function_depth: usize,
    outcome_patterns: BTreeSet<OutcomePattern>,
    imports: BTreeMap<String, Vec<String>>,
    glob_imports: BTreeSet<Vec<String>>,
    /// Callees of the enclosing scrutinized patterns; `None` inside a type ascription.
    outcome_callees: Vec<Option<String>>,
    impl_types: Vec<Option<String>>,
    current_item: Option<String>,
    /// The site symbols of the current top-level item; see [`CounterBump::sites`].
    current_sites: Vec<String>,
    /// How many enclosing items are `#[cfg(test)]`.
    cfg_test_depth: usize,
    counter_bumps: BTreeSet<CounterBump>,
    /// `let name = function(..);` bindings in the current top-level item, by name.
    call_bindings: BTreeMap<String, String>,
}

impl ItemVisitor {
    fn add_symbol(&mut self, symbol: String) {
        *self.symbols.entry(symbol).or_default() += 1;
    }

    fn add_type(&mut self, symbol: String, item: &impl ToTokens) {
        self.add_symbol(symbol.clone());
        self.add_span(symbol.clone(), item, false);
        self.types.insert(symbol);
    }

    fn add_span(&mut self, symbol: String, item: &impl ToTokens, code: bool) {
        let span = item.span();
        if let Some(tokens) = &mut self.item_tokens {
            tokens
                .entry(symbol.clone())
                .or_default()
                .push(item.to_token_stream());
        }
        self.item_spans.entry(symbol).or_default().push(ItemSpan {
            start: span.start().line,
            end: span.end().line,
            code,
        });
    }

    fn visit_scrutinized_pattern(&mut self, pattern: &syn::Pat, scrutinee: &syn::Expr) {
        self.outcome_callees
            .push(called_function(scrutinee, &self.call_bindings));
        self.visit_pat(pattern);
        self.outcome_callees.pop();
    }

    fn visit_top_level_function(
        &mut self,
        item: String,
        sites: Vec<String>,
        visit: impl FnOnce(&mut Self),
    ) {
        let top_level = self.function_depth == 0;
        let (enclosing, enclosing_sites) = if top_level {
            (
                self.current_item.replace(item),
                std::mem::replace(&mut self.current_sites, sites),
            )
        } else {
            (self.current_item.clone(), self.current_sites.clone())
        };
        self.function_depth += 1;
        visit(self);
        self.function_depth -= 1;
        self.current_item = enclosing;
        self.current_sites = enclosing_sites;
        if top_level {
            self.call_bindings.clear();
        }
    }
}

impl ItemVisitor {
    fn within_cfg(&mut self, attributes: &[syn::Attribute], visit: impl FnOnce(&mut Self)) {
        let test = attributes.iter().any(is_cfg_test);
        self.cfg_test_depth += usize::from(test);
        visit(self);
        self.cfg_test_depth -= usize::from(test);
    }

    fn add_counter_bump(&mut self, counter: String) {
        if self.cfg_test_depth == 0 {
            self.counter_bumps.insert(CounterBump {
                sites: self.current_sites.clone(),
                counter,
            });
        }
    }

    /// Every `Counter :: X` token sequence in a macro's tokens, which `syn` does not parse.
    fn add_counter_bumps_in(&mut self, tokens: proc_macro2::TokenStream) {
        use proc_macro2::TokenTree;
        let tokens = tokens.into_iter().collect::<Vec<_>>();
        for (index, token) in tokens.iter().enumerate() {
            match token {
                TokenTree::Group(group) => self.add_counter_bumps_in(group.stream()),
                TokenTree::Ident(ident) if ident == "Counter" => {
                    if let (
                        Some(TokenTree::Punct(first)),
                        Some(TokenTree::Punct(second)),
                        Some(TokenTree::Ident(variant)),
                    ) = (
                        tokens.get(index + 1),
                        tokens.get(index + 2),
                        tokens.get(index + 3),
                    ) && first.as_char() == ':'
                        && second.as_char() == ':'
                    {
                        self.add_counter_bump(variant.to_string());
                    }
                }
                _ => {}
            }
        }
    }
}

impl<'ast> Visit<'ast> for ItemVisitor {
    fn visit_item(&mut self, item: &'ast syn::Item) {
        let attributes: &[syn::Attribute] = match item {
            syn::Item::Const(item) => &item.attrs,
            syn::Item::Enum(item) => &item.attrs,
            syn::Item::Fn(item) => &item.attrs,
            syn::Item::Impl(item) => &item.attrs,
            syn::Item::Macro(item) => &item.attrs,
            syn::Item::Mod(item) => &item.attrs,
            syn::Item::Static(item) => &item.attrs,
            syn::Item::Struct(item) => &item.attrs,
            syn::Item::Trait(item) => &item.attrs,
            syn::Item::Type(item) => &item.attrs,
            syn::Item::Union(item) => &item.attrs,
            _ => &[],
        };
        self.within_cfg(attributes, |visitor| visit::visit_item(visitor, item));
    }

    fn visit_impl_item(&mut self, item: &'ast syn::ImplItem) {
        let attributes: &[syn::Attribute] = match item {
            syn::ImplItem::Const(item) => &item.attrs,
            syn::ImplItem::Fn(item) => &item.attrs,
            syn::ImplItem::Macro(item) => &item.attrs,
            syn::ImplItem::Type(item) => &item.attrs,
            _ => &[],
        };
        self.within_cfg(attributes, |visitor| visit::visit_impl_item(visitor, item));
    }

    fn visit_attribute(&mut self, attribute: &'ast syn::Attribute) {
        if attribute.path().is_ident("doc")
            && let syn::Meta::NameValue(name_value) = &attribute.meta
            && let syn::Expr::Lit(expression) = &name_value.value
            && let syn::Lit::Str(value) = &expression.lit
        {
            let span = attribute.span();
            self.docs.push(LocatedDoc {
                value: value.value(),
                start: span.start().line,
                end: span.end().line,
            });
        }
        visit::visit_attribute(self, attribute);
    }

    fn visit_item_fn(&mut self, item: &'ast syn::ItemFn) {
        if self.function_depth == 0 {
            self.add_symbol(item.sig.ident.to_string());
            self.add_span(item.sig.ident.to_string(), item, true);
        }
        let name = item.sig.ident.to_string();
        self.visit_top_level_function(name.clone(), vec![name], |visitor| {
            visit::visit_item_fn(visitor, item);
        });
    }

    fn visit_impl_item_fn(&mut self, item: &'ast syn::ImplItemFn) {
        let (symbol, sites) = match self.impl_types.last().cloned().flatten() {
            Some(type_name) => {
                let symbol = format!("{type_name}::{}", item.sig.ident);
                let sites = vec![symbol.clone(), format!("impl {type_name}")];
                (symbol, sites)
            }
            None => (item.sig.ident.to_string(), Vec::new()),
        };
        self.visit_top_level_function(symbol, sites, |visitor| {
            visit::visit_impl_item_fn(visitor, item);
        });
    }

    fn visit_item_mod(&mut self, item: &'ast syn::ItemMod) {
        if item.attrs.iter().any(is_cfg_test) {
            return;
        }
        visit::visit_item_mod(self, item);
    }

    fn visit_item_struct(&mut self, item: &'ast syn::ItemStruct) {
        self.add_type(item.ident.to_string(), item);
        visit::visit_item_struct(self, item);
    }

    fn visit_item_enum(&mut self, item: &'ast syn::ItemEnum) {
        self.add_type(item.ident.to_string(), item);
        visit::visit_item_enum(self, item);
    }

    fn visit_item_union(&mut self, item: &'ast syn::ItemUnion) {
        self.add_type(item.ident.to_string(), item);
        visit::visit_item_union(self, item);
    }

    fn visit_item_type(&mut self, item: &'ast syn::ItemType) {
        self.add_type(item.ident.to_string(), item);
        visit::visit_item_type(self, item);
    }

    fn visit_item_impl(&mut self, item: &'ast syn::ItemImpl) {
        if let Some(type_name) = impl_type_name(&item.self_ty) {
            self.add_symbol(format!("impl {type_name}"));
            self.add_span(format!("impl {type_name}"), item, true);
            for impl_item in &item.items {
                if let syn::ImplItem::Fn(function) = impl_item {
                    self.add_symbol(format!("{type_name}::{}", function.sig.ident));
                    self.add_span(
                        format!("{type_name}::{}", function.sig.ident),
                        function,
                        true,
                    );
                }
            }
        }
        self.impl_types.push(impl_type_name(&item.self_ty));
        visit::visit_item_impl(self, item);
        self.impl_types.pop();
    }

    fn visit_expr_call(&mut self, expression: &'ast syn::ExprCall) {
        if let syn::Expr::Path(function) = expression.func.as_ref()
            && function
                .path
                .segments
                .last()
                .is_some_and(|segment| segment.ident == "algorithm_span")
            && let Some(syn::Expr::Path(argument)) = expression.args.first()
        {
            let segments = argument.path.segments.iter().collect::<Vec<_>>();
            if segments.len() >= 2 && segments[segments.len() - 2].ident == "Algorithm" {
                self.algorithm_spans
                    .insert(segments[segments.len() - 1].ident.to_string());
            }
        }
        visit::visit_expr_call(self, expression);
    }

    fn visit_macro(&mut self, invocation: &'ast syn::Macro) {
        if invocation
            .path
            .segments
            .last()
            .is_some_and(|segment| segment.ident == "info_span")
            && invocation.tokens.to_string().starts_with("\"algo\"")
        {
            self.raw_algo_spans += 1;
        }
        if invocation
            .path
            .segments
            .last()
            .is_some_and(|segment| segment.ident == "matches")
            && let Ok(arguments) = invocation.parse_body::<MatchesArguments>()
        {
            self.visit_scrutinized_pattern(&arguments.pattern, &arguments.scrutinee);
        }
        self.add_counter_bumps_in(invocation.tokens.clone());
        visit::visit_macro(self, invocation);
    }

    fn visit_expr_match(&mut self, expression: &'ast syn::ExprMatch) {
        for attribute in &expression.attrs {
            self.visit_attribute(attribute);
        }
        self.visit_expr(&expression.expr);
        for arm in &expression.arms {
            for attribute in &arm.attrs {
                self.visit_attribute(attribute);
            }
            self.visit_scrutinized_pattern(&arm.pat, &expression.expr);
            if let Some((_, guard)) = &arm.guard {
                self.visit_expr(guard);
            }
            self.visit_expr(&arm.body);
        }
    }

    fn visit_expr_let(&mut self, expression: &'ast syn::ExprLet) {
        for attribute in &expression.attrs {
            self.visit_attribute(attribute);
        }
        self.visit_expr(&expression.expr);
        self.visit_scrutinized_pattern(&expression.pat, &expression.expr);
    }

    fn visit_local(&mut self, local: &'ast syn::Local) {
        for attribute in &local.attrs {
            self.visit_attribute(attribute);
        }
        let Some(init) = &local.init else {
            self.visit_pat(&local.pat);
            return;
        };
        self.visit_expr(&init.expr);
        if let Some((_, diverge)) = &init.diverge {
            self.visit_expr(diverge);
        }
        self.visit_scrutinized_pattern(&local.pat, &init.expr);
        if let syn::Pat::Ident(binding) = &local.pat {
            match called_function(&init.expr, &self.call_bindings) {
                Some(callee) => {
                    self.call_bindings.insert(binding.ident.to_string(), callee);
                }
                None => {
                    self.call_bindings.remove(&binding.ident.to_string());
                }
            }
        }
    }

    fn visit_pat_type(&mut self, pattern: &'ast syn::PatType) {
        self.visit_pat(&pattern.pat);
        self.outcome_callees.push(None);
        self.visit_type(&pattern.ty);
        self.outcome_callees.pop();
    }

    fn visit_path(&mut self, path: &'ast syn::Path) {
        if let [.., counter, variant] = path.segments.iter().collect::<Vec<_>>().as_slice()
            && counter.ident == "Counter"
        {
            self.add_counter_bump(variant.ident.to_string());
        }
        if let Some(Some(callee)) = self.outcome_callees.last() {
            let mut written = Vec::new();
            for segment in &path.segments {
                written.push(segment.ident.to_string());
                self.outcome_patterns.insert(OutcomePattern {
                    item: self.current_item.clone(),
                    callee: callee.clone(),
                    identifier: segment.ident.to_string(),
                    path: written.clone(),
                });
            }
        }
        visit::visit_path(self, path);
    }

    fn visit_item_use(&mut self, item: &'ast syn::ItemUse) {
        if self.function_depth == 0 {
            collect_use_tree(
                &item.tree,
                &mut Vec::new(),
                &mut self.imports,
                &mut self.glob_imports,
            );
        }
        visit::visit_item_use(self, item);
    }

    fn visit_expr_loop(&mut self, expression: &'ast syn::ExprLoop) {
        self.has_loop = true;
        visit::visit_expr_loop(self, expression);
    }

    fn visit_expr_while(&mut self, expression: &'ast syn::ExprWhile) {
        self.has_loop = true;
        visit::visit_expr_while(self, expression);
    }
}

/// The arguments of `matches!(scrutinee, pattern)` or `matches!(scrutinee, pattern if guard)`;
/// the guard is discarded.
struct MatchesArguments {
    scrutinee: syn::Expr,
    pattern: syn::Pat,
}

impl syn::parse::Parse for MatchesArguments {
    fn parse(input: syn::parse::ParseStream<'_>) -> syn::Result<Self> {
        let scrutinee = input.parse::<syn::Expr>()?;
        input.parse::<syn::Token![,]>()?;
        let pattern = syn::Pat::parse_multi_with_leading_vert(input)?;
        input.parse::<proc_macro2::TokenStream>()?;
        Ok(Self { scrutinee, pattern })
    }
}

/// The last path segment of the function an expression calls once references, parentheses,
/// invisible groups, and `?` are removed, or the callee recorded for a local variable bound by
/// `let name = function(..);` earlier in the same top-level item; `None` for a method call or any
/// other expression. Bindings are tracked by name without scopes, so a shadowing pattern binding
/// other than `let name = ..` is not seen.
fn called_function(expression: &syn::Expr, bindings: &BTreeMap<String, String>) -> Option<String> {
    match expression {
        syn::Expr::Call(call) => match call.func.as_ref() {
            syn::Expr::Path(function) => function
                .path
                .segments
                .last()
                .map(|segment| segment.ident.to_string()),
            _ => None,
        },
        syn::Expr::Path(variable) => variable
            .path
            .get_ident()
            .and_then(|name| bindings.get(&name.to_string()))
            .cloned(),
        syn::Expr::Reference(inner) => called_function(&inner.expr, bindings),
        syn::Expr::Paren(inner) => called_function(&inner.expr, bindings),
        syn::Expr::Group(inner) => called_function(&inner.expr, bindings),
        syn::Expr::Try(inner) => called_function(&inner.expr, bindings),
        _ => None,
    }
}

fn collect_use_tree(
    tree: &syn::UseTree,
    prefix: &mut Vec<String>,
    imports: &mut BTreeMap<String, Vec<String>>,
    globs: &mut BTreeSet<Vec<String>>,
) {
    match tree {
        syn::UseTree::Path(path) => {
            prefix.push(path.ident.to_string());
            collect_use_tree(&path.tree, prefix, imports, globs);
            prefix.pop();
        }
        syn::UseTree::Name(name) if name.ident == "self" => {
            if let Some(last) = prefix.last() {
                imports.insert(last.clone(), prefix.clone());
            }
        }
        syn::UseTree::Name(name) => {
            let mut path = prefix.clone();
            path.push(name.ident.to_string());
            imports.insert(name.ident.to_string(), path);
        }
        syn::UseTree::Rename(rename) => {
            if rename.rename == "_" {
                return;
            }
            let mut path = prefix.clone();
            if rename.ident != "self" {
                path.push(rename.ident.to_string());
            }
            imports.insert(rename.rename.to_string(), path);
        }
        syn::UseTree::Glob(_) => {
            globs.insert(prefix.clone());
        }
        syn::UseTree::Group(group) => {
            for tree in &group.items {
                collect_use_tree(tree, prefix, imports, globs);
            }
        }
    }
}

fn is_cfg_test(attribute: &syn::Attribute) -> bool {
    matches!(
        &attribute.meta,
        syn::Meta::List(list)
            if list.path.is_ident("cfg") && list.tokens.to_string() == "test"
    )
}

fn impl_type_name(ty: &syn::Type) -> Option<String> {
    let syn::Type::Path(path) = ty else {
        return None;
    };
    path.path
        .segments
        .last()
        .map(|segment| segment.ident.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn extracts_both_card_kinds() {
        let source = r#"
//! ```toml algorithm
//! id = "backend.example"
//! sites = ["run"]
//! ```
/// ```toml algorithm-site
/// id = "backend.example"
/// role = "part"
/// sites = ["helper"]
/// ```
fn run() {}
fn helper() {}
"#;
        let file = syn::parse_file(source).unwrap();
        let mut visitor = ItemVisitor::default();
        visitor.visit_file(&file);
        let fences = extract_fences(&visitor.docs);
        assert_eq!(fences.len(), 2);
        assert_eq!(fences[0].0, CardKind::Primary);
        assert_eq!(fences[1].0, CardKind::Site);
    }

    #[test]
    fn extracts_anchored_contract_cards() {
        let source = r#"
//! ```toml algorithm-contract
//! id = "contract.example.cache"
//! name = "one cache contract"
//! sites = ["run"]
//! constrains = [{ id = "backend.example", site = "run", via = "one OnceLock" }]
//! ```
fn run() {}
"#;
        let file = syn::parse_file(source).unwrap();
        let mut visitor = ItemVisitor::default();
        visitor.visit_file(&file);
        let fences = extract_fences(&visitor.docs);
        assert_eq!(fences.len(), 1);
        assert_eq!(fences[0].0, CardKind::Contract);
    }

    #[test]
    fn extracts_representation_cards_with_type_and_lean_keys() {
        let source = r#"
//! ```toml algorithm-representation
//! id = "representation.example.value"
//! name = "one value"
//! type = "k_rust::Value"
//! sites = ["Value::new"]
//! invariant = "fields are sorted"
//! lean = ["KRust.Example.sorted"]
//! ```
struct Value;
impl Value { fn new() -> Self { Value } }
"#;
        let file = syn::parse_file(source).unwrap();
        let mut visitor = ItemVisitor::default();
        visitor.visit_file(&file);
        let fences = extract_fences(&visitor.docs);
        assert_eq!(fences.len(), 1);
        assert_eq!(fences[0].0, CardKind::Representation);
        let body = toml::from_str::<CardBody>(&fences[0].1).unwrap();
        assert_eq!(body.type_path.as_deref(), Some("k_rust::Value"));
        assert_eq!(body.lean, ["KRust.Example.sorted"]);
    }

    #[test]
    fn rejects_a_stored_feeds_edge() {
        let error = toml::from_str::<CardBody>(
            r#"id = "backend.example"
feeds = ["backend.other"]
"#,
        )
        .unwrap_err();
        assert!(error.to_string().contains("unknown field `feeds`"));
    }

    #[test]
    fn rejects_unknown_keys_in_nested_tables() {
        for (nested, key) in [
            (
                "[[cost]]\nmode = \"m\"\nbound = \"O(p)\"\nvarible = \"p\"\n",
                "varible",
            ),
            (
                "constrains = [{ id = \"a.b\", site = \"run\", via = \"v\", sit = \"x\" }]\n",
                "sit",
            ),
        ] {
            let error = toml::from_str::<CardBody>(&format!("id = \"backend.example\"\n{nested}"))
                .unwrap_err();
            assert!(
                error
                    .to_string()
                    .contains(&format!("unknown field `{key}`")),
                "{error}"
            );
        }
        assert!(
            toml::from_str::<CardBody>(
                "id = \"backend.example\"\nconsumes = [{ type = \"k_rust::A\", role = \"r\", rol = \"x\" }]\n"
            )
            .is_err()
        );
        let accepted = toml::from_str::<CardBody>(
            "id = \"backend.example\"\nconsumes = [\"k_rust::A\", { type = \"k_rust::B\", role = \"r\" }]\n",
        )
        .unwrap();
        assert_eq!(accepted.consumes[1].id(), "k_rust::B [r]");
    }

    #[test]
    fn ignores_doc_comment_text_inside_a_string() {
        let file = syn::parse_file(
            r####"const EXAMPLE: &str = r#"
//! ```toml algorithm
//! id = "not.a.card"
//! ```
"#;"####,
        )
        .unwrap();
        let mut visitor = ItemVisitor::default();
        visitor.visit_file(&file);
        assert!(extract_fences(&visitor.docs).is_empty());
    }

    #[test]
    fn indexes_associated_items_but_not_function_local_items() {
        let file = syn::parse_file(
            "struct Thing; impl Thing { fn run() { fn nested() {} } } type Alias<'a> = &'a Thing;",
        )
        .unwrap();
        let mut visitor = ItemVisitor::default();
        visitor.visit_file(&file);
        assert_eq!(visitor.symbols["Thing::run"], 1);
        assert!(!visitor.symbols.contains_key("nested"));
        assert!(visitor.types.contains("Alias"));
    }

    #[test]
    fn outcome_patterns_record_call_scrutinees_only() {
        let file = syn::parse_file(
            r#"
use crate::matching::MatchResult;
fn direct() { match produce(1) { MatchResult::Success(_) => {} _ => {} } }
fn bound() { let found = produce(1); if let MatchResult::Failed(_) = found {} }
fn macro_call() -> bool { matches!(produce(1)?, Outcome::Done) }
fn held(value: Term) { match value { Term::Apply(_) => {} _ => {} } }
fn method(value: Term) { match value.kind() { Kind::Apply => {} _ => {} } }
fn ascribed() { let (left, _): (Annotated, u8) = produce(1); }
impl Engine { fn step() { let Ok(Stepped::Done) = produce(1) else { return }; } }
"#,
        )
        .unwrap();
        let mut visitor = ItemVisitor::default();
        visitor.visit_file(&file);
        let found = visitor
            .outcome_patterns
            .iter()
            .map(|pattern| {
                (
                    pattern.item.as_deref().unwrap_or(""),
                    pattern.callee.as_str(),
                    pattern.identifier.as_str(),
                )
            })
            .collect::<BTreeSet<_>>();
        for expected in [
            ("direct", "produce", "MatchResult"),
            ("bound", "produce", "MatchResult"),
            ("macro_call", "produce", "Outcome"),
            ("Engine::step", "produce", "Stepped"),
        ] {
            assert!(found.contains(&expected), "{expected:?} in {found:?}");
        }
        for absent in ["Term", "Kind", "Annotated"] {
            assert!(
                found.iter().all(|(_, _, identifier)| *identifier != absent),
                "{absent} in {found:?}"
            );
        }
    }

    fn index_of(files: &[(&str, &str)]) -> SourceIndex {
        let mut index = SourceIndex::default();
        for (relative, source) in files {
            let mut visitor = ItemVisitor::default();
            visitor.visit_file(&syn::parse_file(source).unwrap());
            index.insert_file(&crate_name(relative).unwrap(), relative, visitor, false);
        }
        index
    }

    fn resolved(index: &SourceIndex, file: &str, path: &[&str]) -> Option<String> {
        let path = path.iter().map(ToString::to_string).collect::<Vec<_>>();
        index
            .resolve_path(file, &path)
            .map(|resolved| resolved.join("::"))
    }

    const RESOLUTION_WORKSPACE: [(&str, &str); 6] = [
        ("crates/k-rust-kore/src/lib.rs", "pub mod kore;"),
        (
            "crates/k-rust-kore/src/kore/ast.rs",
            "pub enum Sentence { Axiom }",
        ),
        ("crates/k-rust/src/lib.rs", "pub use k_rust_kore::kore;"),
        (
            "crates/k-rust/src/definition.rs",
            "pub enum Sentence { Rule }",
        ),
        (
            "crates/k-rust/src/emit.rs",
            "use crate::definition::{Sentence}; use crate::kore::ast::{Sentence as KoreSentence};",
        ),
        (
            "crates/k-rust/src/emit/rules.rs",
            "use super::*; fn emit() {}",
        ),
    ];

    #[test]
    fn an_aliased_import_resolves_through_a_glob_and_a_crate_reexport() {
        let index = index_of(&RESOLUTION_WORKSPACE);
        for file in [
            "crates/k-rust/src/emit.rs",
            "crates/k-rust/src/emit/rules.rs",
        ] {
            assert_eq!(
                resolved(&index, file, &["KoreSentence", "Axiom"]).as_deref(),
                Some("k_rust_kore::kore::ast::Sentence::Axiom"),
                "{file}"
            );
        }
    }

    #[test]
    fn a_same_name_import_resolves_to_its_own_path() {
        let index = index_of(&RESOLUTION_WORKSPACE);
        for file in [
            "crates/k-rust/src/emit.rs",
            "crates/k-rust/src/emit/rules.rs",
        ] {
            assert_eq!(
                resolved(&index, file, &["Sentence"]).as_deref(),
                Some("k_rust::definition::Sentence"),
                "{file}"
            );
        }
        assert_eq!(
            resolved(&index, "crates/k-rust/src/emit/rules.rs", &["Unbound"]),
            None
        );
    }

    #[test]
    fn production_symbols_are_not_ambiguous_with_cfg_test_helpers() {
        let file = syn::parse_file("fn run() {} #[cfg(test)] mod tests { fn run() {} }").unwrap();
        let mut visitor = ItemVisitor::default();
        visitor.visit_file(&file);
        assert_eq!(visitor.symbols["run"], 1);
    }

    #[test]
    fn indexes_algorithm_span_calls_and_raw_literals() {
        let file = syn::parse_file(
            r#"fn run() {
                let _span = measure::algorithm_span(Algorithm::BackendExample);
                let _raw = tracing::info_span!("algo", id = "example");
                loop { // Invariant: example
                    break;
                }
            }"#,
        )
        .unwrap();
        let mut visitor = ItemVisitor::default();
        visitor.visit_file(&file);
        assert!(visitor.algorithm_spans.contains("BackendExample"));
        assert_eq!(visitor.raw_algo_spans, 1);
        assert!(visitor.has_loop);
    }

    fn bumps(source: &str) -> Vec<CounterBump> {
        let file = syn::parse_file(source).unwrap();
        let mut visitor = ItemVisitor::default();
        visitor.visit_file(&file);
        visitor.counter_bumps.into_iter().collect()
    }

    fn bump(sites: &[&str], counter: &str) -> CounterBump {
        CounterBump {
            sites: sites.iter().map(|site| (*site).to_owned()).collect(),
            counter: counter.to_owned(),
        }
    }

    #[test]
    fn records_counter_bumps_with_the_site_symbols_of_their_item() {
        let found = bumps(
            r#"
            fn run() { measure::bump(Counter::A); fn nested() { measure::add(Counter::B, 2); } }
            impl Engine { fn step(&self) { debug_assert!(touch(measure::Counter::C)); } }
            trait Walk { fn walk(&self) { measure::bump(Counter::D); } }
            #[cfg(test)] fn helper() { measure::bump(Counter::E); }
            #[cfg(test)] const CELL: Cell = Cell(Counter::F);
            impl Engine { #[cfg(test)] fn probe() { measure::bump(Counter::G); } }
            #[cfg(test)] mod tests { fn t() { measure::bump(Counter::H); } }
            fn other() { let _ = FreshCounter::mint(); }
            "#,
        );
        assert_eq!(
            found,
            [
                bump(&[], "D"),
                bump(&["Engine::step", "impl Engine"], "C"),
                bump(&["run"], "A"),
                bump(&["run"], "B"),
            ]
        );
    }

    fn site_card(kind: CardKind, id: &str, file: &str, sites: &[&str], counters: &[&str]) -> Card {
        Card {
            kind,
            body: CardBody {
                id: id.to_owned(),
                sites: sites.iter().map(|site| (*site).to_owned()).collect(),
                counters: counters
                    .iter()
                    .map(|counter| (*counter).to_owned())
                    .collect(),
                ..CardBody::default()
            },
            crate_name: "k-rust".to_owned(),
            file: file.to_owned(),
            source: String::new(),
        }
    }

    #[test]
    fn a_counter_bump_is_a_counted_site_of_every_claimant_unless_one_names_it() {
        let claims = CounterClaims::new(&[
            site_card(
                CardKind::Primary,
                "parser.recognize",
                "crates/k-rust/src/a.rs",
                &["recognize"],
                &["Attempts"],
            ),
            site_card(
                CardKind::Primary,
                "parser.bubbles",
                "crates/k-rust/src/b.rs",
                &["parse_bubble"],
                &["Attempts"],
            ),
            site_card(
                CardKind::Site,
                "parser.recognize",
                "crates/k-rust/src/c.rs",
                &["impl Chart"],
                &[],
            ),
            site_card(
                CardKind::Primary,
                "provenance.record",
                "crates/k-rust/src/d.rs",
                &["record"],
                &["Steps"],
            ),
        ]);
        let both = ["parser.bubbles", "parser.recognize"]
            .map(ToOwned::to_owned)
            .into_iter()
            .collect::<BTreeSet<_>>();

        // A callee's card names the item: the callers that claim its counter need not.
        assert_eq!(
            claims.place("crates/k-rust/src/a.rs", &bump(&["recognize"], "Attempts")),
            CountedSite::Named
        );
        // `impl Chart` on a site card names every method of it.
        assert_eq!(
            claims.place(
                "crates/k-rust/src/c.rs",
                &bump(&["Chart::complete", "impl Chart"], "Attempts")
            ),
            CountedSite::Named
        );
        // The same symbol in another file is another item.
        assert_eq!(
            claims.place("crates/k-rust/src/e.rs", &bump(&["recognize"], "Attempts")),
            CountedSite::Counted {
                symbol: "recognize",
                algorithms: &both
            }
        );
        // A card that does not claim the counter does not place its work.
        assert!(matches!(
            claims.place("crates/k-rust/src/d.rs", &bump(&["record"], "Attempts")),
            CountedSite::Counted {
                symbol: "record",
                ..
            }
        ));
        assert!(matches!(
            claims.place("crates/k-rust/src/e.rs", &bump(&[], "Steps")),
            CountedSite::Unnameable { .. }
        ));
        assert_eq!(
            claims.place("crates/k-rust/src/e.rs", &bump(&["run"], "Unclaimed")),
            CountedSite::Unclaimed
        );
        assert_eq!(
            claims.place(COUNTER_DECLARATION_FILE, &bump(&["Counter::name"], "Steps")),
            CountedSite::Unclaimed
        );
    }
}
