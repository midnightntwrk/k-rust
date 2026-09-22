use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
};

use serde::Deserialize;
use syn::visit::{self, Visit};

use crate::model::{Anchor, Cost};

#[derive(Clone, Debug, Deserialize)]
#[serde(untagged)]
pub(crate) enum Representation {
    Path(String),
    WithRole {
        #[serde(rename = "type")]
        type_path: String,
        role: String,
    },
}

impl Representation {
    pub(crate) fn type_path(&self) -> &str {
        match self {
            Self::Path(path) => path,
            Self::WithRole { type_path, .. } => type_path,
        }
    }

    pub(crate) fn role(&self) -> Option<&str> {
        match self {
            Self::Path(_) => None,
            Self::WithRole { role, .. } => Some(role),
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
pub(crate) struct Constraint {
    pub id: String,
    pub site: String,
    pub via: String,
}

#[derive(Clone, Debug, Deserialize)]
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
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum CardKind {
    Primary,
    Site,
    Contract,
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
}

impl SourceIndex {
    pub(crate) fn symbol_count(&self, crate_name: &str, file: &str, symbol: &str) -> usize {
        self.symbols
            .get(&(crate_name.to_owned(), file.to_owned()))
            .and_then(|symbols| symbols.get(symbol))
            .copied()
            .unwrap_or(0)
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

    let mut cards = Vec::new();
    let mut index = SourceIndex::default();
    for path in files {
        let relative = relative_path(root, &path);
        let Some(crate_name) = crate_name(&relative) else {
            continue;
        };
        let source = fs::read_to_string(&path)?;
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
                index
                    .symbols
                    .insert((crate_name.clone(), relative.clone()), visitor.symbols);
                for type_name in visitor.types {
                    index
                        .types
                        .entry((crate_name.clone(), type_name.clone()))
                        .or_default()
                        .push(Anchor {
                            crate_name: crate_name.clone(),
                            file: relative.clone(),
                            symbol: type_name,
                        });
                }
                index.files.insert(
                    relative,
                    SourceFacts {
                        algorithm_spans: visitor.algorithm_spans,
                        raw_algo_spans: visitor.raw_algo_spans,
                        has_invariant_loop: visitor.has_loop && source.contains("Invariant:"),
                    },
                );
            }
            Err(error) => report.push(format!(
                "unresolved source index for {relative}: Rust parse failed: {error}"
            )),
        }
    }
    Ok((cards, index))
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

fn crate_name(relative: &str) -> Option<String> {
    relative.split('/').nth(1).map(ToOwned::to_owned)
}

fn extract_fences(docs: &[String]) -> Vec<(CardKind, String)> {
    let mut fences = Vec::new();
    let mut current: Option<(CardKind, String)> = None;
    for doc in docs {
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
            _ => None,
        };
    }
    fences
}

#[derive(Default)]
struct ItemVisitor {
    symbols: BTreeMap<String, usize>,
    types: BTreeSet<String>,
    docs: Vec<String>,
    algorithm_spans: BTreeSet<String>,
    raw_algo_spans: usize,
    has_loop: bool,
    function_depth: usize,
}

impl ItemVisitor {
    fn add_symbol(&mut self, symbol: String) {
        *self.symbols.entry(symbol).or_default() += 1;
    }

    fn add_type(&mut self, symbol: String) {
        self.add_symbol(symbol.clone());
        self.types.insert(symbol);
    }
}

impl<'ast> Visit<'ast> for ItemVisitor {
    fn visit_attribute(&mut self, attribute: &'ast syn::Attribute) {
        if attribute.path().is_ident("doc")
            && let syn::Meta::NameValue(name_value) = &attribute.meta
            && let syn::Expr::Lit(expression) = &name_value.value
            && let syn::Lit::Str(value) = &expression.lit
        {
            self.docs.push(value.value());
        }
        visit::visit_attribute(self, attribute);
    }

    fn visit_item_fn(&mut self, item: &'ast syn::ItemFn) {
        if self.function_depth == 0 {
            self.add_symbol(item.sig.ident.to_string());
        }
        self.function_depth += 1;
        visit::visit_item_fn(self, item);
        self.function_depth -= 1;
    }

    fn visit_impl_item_fn(&mut self, item: &'ast syn::ImplItemFn) {
        self.function_depth += 1;
        visit::visit_impl_item_fn(self, item);
        self.function_depth -= 1;
    }

    fn visit_item_mod(&mut self, item: &'ast syn::ItemMod) {
        if item.attrs.iter().any(is_cfg_test) {
            return;
        }
        visit::visit_item_mod(self, item);
    }

    fn visit_item_struct(&mut self, item: &'ast syn::ItemStruct) {
        self.add_type(item.ident.to_string());
        visit::visit_item_struct(self, item);
    }

    fn visit_item_enum(&mut self, item: &'ast syn::ItemEnum) {
        self.add_type(item.ident.to_string());
        visit::visit_item_enum(self, item);
    }

    fn visit_item_union(&mut self, item: &'ast syn::ItemUnion) {
        self.add_type(item.ident.to_string());
        visit::visit_item_union(self, item);
    }

    fn visit_item_type(&mut self, item: &'ast syn::ItemType) {
        self.add_type(item.ident.to_string());
        visit::visit_item_type(self, item);
    }

    fn visit_item_impl(&mut self, item: &'ast syn::ItemImpl) {
        if let Some(type_name) = impl_type_name(&item.self_ty) {
            self.add_symbol(format!("impl {type_name}"));
            for impl_item in &item.items {
                if let syn::ImplItem::Fn(function) = impl_item {
                    self.add_symbol(format!("{type_name}::{}", function.sig.ident));
                }
            }
        }
        visit::visit_item_impl(self, item);
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
        visit::visit_macro(self, invocation);
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
}
