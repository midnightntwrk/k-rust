//! Counted work happens at a named site.
//!
//! A card's `counters` measure the work of that card's algorithm, so the item that bumps one of
//! them performs part of that algorithm. `algo-graph drift` reports a card only when a change
//! touches one of its named items (`docs/algorithm-cards.md`, "Reviewing card drift"), and the
//! atlas staleness check watches only the files of those items. So the top-level item that bumps
//! a counter must be a named site of some algorithm the counter measures (its anchor, a `sites`
//! entry of its primary card, or a `role = "part"` site card); otherwise a change to it never
//! marks the algorithm's cards or receipts stale.
//!
//! "Some", not "every": a counter is measured inside an algorithm's spans including nested spans,
//! so a caller may claim the counter of a callee algorithm that owns the work (the bubble parsers
//! claim `ParserParseAttempts`, which the Earley recognizer bumps). The callee being named is what
//! the invariant needs.
//!
//! The graph derives these sites from the code (`CounterClaims` in `src/cards.rs`): an item that
//! bumps a claimed counter and that no claimant's card names becomes a counted site of every
//! claimant. This test finds the bumps with its own scan of the sources, so it checks that
//! derivation, not only the cards. It is the precise form of the `worklist without card`
//! advisory, which guesses at uncarded work from a loop and an `// Invariant:` comment.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::Path,
};

use algo_graph::{build_graph, cfg_test_module_files, workspace_root};
use syn::visit::Visit;

/// The file that defines `Counter` and its registry; its references are declarations, not work.
const COUNTER_DEFINITION: &str = "crates/k-rust-kore/src/measure.rs";

fn is_cfg_test(attributes: &[syn::Attribute]) -> bool {
    attributes.iter().any(|attribute| {
        attribute.path().is_ident("cfg")
            && attribute.meta.require_list().is_ok_and(|list| {
                list.tokens
                    .to_string()
                    .split_whitespace()
                    .any(|t| t == "test")
            })
    })
}

/// Every `Counter::X` use outside `#[cfg(test)]` items, with the symbols `algo-graph drift` gives
/// the top-level item enclosing it: a free function's name, or `Type::method` and `impl Type` for
/// a method. The symbol list is empty outside every such item.
#[derive(Default)]
struct CounterUses {
    enclosing: Vec<Vec<String>>,
    self_type: Option<String>,
    uses: BTreeSet<(String, Vec<String>)>,
}

impl CounterUses {
    fn record(&mut self, variant: String) {
        let enclosing = self.enclosing.first().cloned().unwrap_or_default();
        self.uses.insert((variant, enclosing));
    }
}

impl<'ast> Visit<'ast> for CounterUses {
    fn visit_item(&mut self, item: &'ast syn::Item) {
        let attributes: &[syn::Attribute] = match item {
            syn::Item::Fn(item) => &item.attrs,
            syn::Item::Mod(item) => &item.attrs,
            syn::Item::Impl(item) => &item.attrs,
            syn::Item::Const(item) => &item.attrs,
            syn::Item::Static(item) => &item.attrs,
            _ => &[],
        };
        if !is_cfg_test(attributes) {
            syn::visit::visit_item(self, item);
        }
    }

    fn visit_item_fn(&mut self, item: &'ast syn::ItemFn) {
        self.enclosing.push(vec![item.sig.ident.to_string()]);
        syn::visit::visit_item_fn(self, item);
        self.enclosing.pop();
    }

    fn visit_item_impl(&mut self, item: &'ast syn::ItemImpl) {
        let self_type = match &*item.self_ty {
            syn::Type::Path(path) => path.path.segments.last().map(|s| s.ident.to_string()),
            _ => None,
        };
        let outer = std::mem::replace(&mut self.self_type, self_type);
        syn::visit::visit_item_impl(self, item);
        self.self_type = outer;
    }

    fn visit_impl_item(&mut self, item: &'ast syn::ImplItem) {
        let attributes: &[syn::Attribute] = match item {
            syn::ImplItem::Fn(item) => &item.attrs,
            syn::ImplItem::Const(item) => &item.attrs,
            _ => &[],
        };
        if !is_cfg_test(attributes) {
            syn::visit::visit_impl_item(self, item);
        }
    }

    fn visit_impl_item_fn(&mut self, item: &'ast syn::ImplItemFn) {
        let self_type = self.self_type.clone().unwrap_or_default();
        self.enclosing.push(vec![
            format!("{self_type}::{}", item.sig.ident),
            format!("impl {self_type}"),
        ]);
        syn::visit::visit_impl_item_fn(self, item);
        self.enclosing.pop();
    }

    fn visit_path(&mut self, path: &'ast syn::Path) {
        let segments = path.segments.iter().collect::<Vec<_>>();
        if let [.., counter, variant] = segments.as_slice()
            && counter.ident == "Counter"
        {
            self.record(variant.ident.to_string());
        }
        syn::visit::visit_path(self, path);
    }

    fn visit_macro(&mut self, mac: &'ast syn::Macro) {
        // `measure::add(Counter::X, n)` inside a macro body (e.g. `debug_assert!`) is still a use.
        let text = mac.tokens.to_string();
        let mut rest = text.as_str();
        while let Some(at) = rest.find("Counter :: ") {
            rest = &rest[at + "Counter :: ".len()..];
            let variant = rest
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                .collect::<String>();
            if !variant.is_empty() {
                self.record(variant);
            }
        }
    }
}

fn source_files(root: &Path, directory: &Path, files: &mut Vec<String>) {
    let entries = fs::read_dir(directory)
        .unwrap_or_else(|error| panic!("could not read {}: {error}", directory.display()));
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            if path.file_name().is_some_and(|name| name == "target") {
                continue;
            }
            source_files(root, &path, files);
        } else if path.extension().is_some_and(|extension| extension == "rs") {
            files.push(
                path.strip_prefix(root)
                    .unwrap()
                    .to_string_lossy()
                    .replace('\\', "/"),
            );
        }
    }
}

#[test]
fn every_item_that_bumps_a_counter_is_a_named_site_of_an_algorithm_the_counter_measures() {
    let root = workspace_root();
    let build = build_graph(&root).expect("the workspace graph should build");

    let mut measured_by = BTreeMap::<&str, BTreeSet<&str>>::new();
    for edge in build
        .graph
        .edges
        .iter()
        .filter(|edge| edge.kind == "measured-by")
    {
        measured_by
            .entry(edge.to.as_str())
            .or_default()
            .insert(edge.from.as_str());
    }
    let mut sites = BTreeMap::<&str, BTreeSet<(&str, &str)>>::new();
    for node in build
        .graph
        .nodes
        .iter()
        .filter(|node| node.kind == "algorithm")
    {
        let named = sites.entry(node.id.as_str()).or_default();
        named.insert((node.anchor.file.as_str(), node.anchor.symbol.as_str()));
        named.extend(
            node.sites
                .iter()
                .map(|site| (site.file.as_str(), site.symbol.as_str())),
        );
    }

    let mut files = Vec::new();
    for crate_directory in fs::read_dir(root.join("crates")).unwrap().flatten() {
        let source = crate_directory.path().join("src");
        if source.is_dir() {
            source_files(&root, &source, &mut files);
        }
    }

    // A file only `#[cfg(test)]` declarations load is test code, as an inline test module is.
    // Each file's counter uses are read as the files stream past, so one syntax tree is held at a
    // time, and the uses of the test files are discarded after.
    let mut uses_of = Vec::new();
    let test_files = cfg_test_module_files(files.iter().map(|file| {
        let text = fs::read_to_string(root.join(file)).unwrap();
        let syntax =
            syn::parse_file(&text).unwrap_or_else(|error| panic!("{file} does not parse: {error}"));
        if file != COUNTER_DEFINITION {
            let mut uses = CounterUses::default();
            uses.visit_file(&syntax);
            uses_of.push((file.as_str(), uses));
        }
        (file.as_str(), syntax)
    }));

    let mut violations = Vec::new();
    for (file, uses) in uses_of
        .iter()
        .filter(|(file, _)| !test_files.contains(*file))
    {
        for (counter, enclosing) in &uses.uses {
            let Some(algorithms) = measured_by.get(counter.as_str()) else {
                continue;
            };
            let named_here = |algorithm: &str, at_item: bool| {
                sites.get(algorithm).is_some_and(|named| {
                    named.iter().any(|(site_file, symbol)| {
                        *site_file == *file
                            && (!at_item || enclosing.iter().any(|candidate| candidate == symbol))
                    })
                })
            };
            if algorithms
                .iter()
                .any(|algorithm| named_here(algorithm, true))
            {
                continue;
            }
            let item = enclosing.first().map_or("(no item)", String::as_str);
            let file_named = algorithms
                .iter()
                .any(|algorithm| named_here(algorithm, false));
            violations.push(format!(
                "{file} {item}: bumps Counter::{counter}, which measures {}, but is not a named site of it{}",
                algorithms.iter().copied().collect::<Vec<_>>().join(" / "),
                if file_named { "" } else { " (no card of it in the file)" },
            ));
        }
    }
    assert!(
        violations.is_empty(),
        "{} counted-work items outside every named site of the counted algorithm:\n{}",
        violations.len(),
        violations.join("\n")
    );
}
