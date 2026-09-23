use std::{
    collections::BTreeMap,
    fmt::Write as _,
    fs, io,
    path::Path,
    process::{Command, Output},
};

use proc_macro2::{Delimiter, Group, LineColumn, TokenStream, TokenTree};
use quote::ToTokens;
use syn::{
    spanned::Spanned,
    visit::{self, Visit},
};

use crate::Error;

/// A card whose implementation site changed without its fence changing.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DriftFinding {
    pub card_id: String,
    pub file: String,
    pub item: String,
    pub hunks: Vec<String>,
    /// The card's `lean` theorems: their models mirror the changed site and must be re-checked.
    pub lean: Vec<String>,
}

/// The report produced for a Git revision range.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct DriftReport {
    pub findings: Vec<DriftFinding>,
}

/// Find card sites whose parsed Rust item changed while the card fence did not.
///
/// `until = None` compares `since` with the index and working tree. Findings are
/// advisory: their presence never turns this operation into an error.
pub fn drift(root: &Path, since: &str, until: Option<&str>) -> Result<DriftReport, Error> {
    let patch = git_diff(root, since, until)?;
    let files = parse_patch(&patch)?;
    let mut findings = Vec::new();

    for file_diff in files {
        let Some(after_source) = revision_source(root, until, &file_diff.file)? else {
            continue;
        };
        let before_source = revision_source(root, Some(since), &file_diff.file)?;
        findings.extend(drift_file(
            &file_diff,
            before_source.as_deref(),
            &after_source,
        )?);
    }

    findings.sort_by(|left, right| {
        (&left.file, &left.card_id, &left.item).cmp(&(&right.file, &right.card_id, &right.item))
    });
    Ok(DriftReport { findings })
}

/// Render a deterministic, human-readable drift report.
pub fn render_drift(report: &DriftReport) -> String {
    let mut output = String::new();
    for finding in &report.findings {
        let _ = writeln!(
            output,
            "card {} ({}): site {} changed while its card did not",
            finding.card_id, finding.file, finding.item
        );
        if !finding.lean.is_empty() {
            let _ = writeln!(
                output,
                "  re-check the Lean models of: {}",
                finding.lean.join(", ")
            );
        }
        for hunk in &finding.hunks {
            for line in hunk.lines() {
                let _ = writeln!(output, "  {line}");
            }
        }
    }
    output
}

fn git_diff(root: &Path, since: &str, until: Option<&str>) -> Result<String, Error> {
    let mut arguments = vec![
        "diff",
        "--no-ext-diff",
        "--no-color",
        "--no-renames",
        "--no-prefix",
        "--unified=0",
        since,
    ];
    if let Some(until) = until {
        arguments.push(until);
    }
    arguments.extend(["--", "*.rs"]);
    git_stdout(root, &arguments)
}

fn revision_source(
    root: &Path,
    revision: Option<&str>,
    file: &str,
) -> Result<Option<String>, Error> {
    let Some(revision) = revision else {
        return match fs::read_to_string(root.join(file)) {
            Ok(source) => Ok(Some(source)),
            Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(None),
            Err(error) => Err(error.into()),
        };
    };
    let object = format!("{revision}:{file}");
    let output = git_output(root, &["show", &object])?;
    if output.status.success() {
        String::from_utf8(output.stdout)
            .map(Some)
            .map_err(|error| Error::Invalid(format!("git show {object} was not UTF-8: {error}")))
    } else {
        Ok(None)
    }
}

fn git_stdout(root: &Path, arguments: &[&str]) -> Result<String, Error> {
    let output = git_output(root, arguments)?;
    if !output.status.success() {
        return Err(Error::Invalid(format!(
            "git {} failed: {}",
            arguments.join(" "),
            String::from_utf8_lossy(&output.stderr).trim()
        )));
    }
    String::from_utf8(output.stdout)
        .map_err(|error| Error::Invalid(format!("git output was not UTF-8: {error}")))
}

fn git_output(root: &Path, arguments: &[&str]) -> Result<Output, Error> {
    Command::new("git")
        .arg("-C")
        .arg(root)
        .args(arguments)
        .output()
        .map_err(Error::Io)
}

#[derive(Clone, Debug)]
struct FileDiff {
    file: String,
    hunks: Vec<Hunk>,
}

#[derive(Clone, Debug)]
struct Hunk {
    old: LineRange,
    new: LineRange,
    text: String,
}

#[derive(Clone, Copy, Debug)]
struct LineRange {
    start: usize,
    count: usize,
}

impl LineRange {
    fn intersects(self, item: ItemRange) -> bool {
        if self.count == 0 {
            return false;
        }
        let end = self.start + self.count - 1;
        self.start <= item.end && item.start <= end
    }
}

#[derive(Clone, Copy, Debug)]
struct ItemRange {
    start: usize,
    end: usize,
}

fn parse_patch(patch: &str) -> Result<Vec<FileDiff>, Error> {
    let mut files = Vec::<FileDiff>::new();
    let mut current_file: Option<FileDiff> = None;
    let mut current_hunk: Option<Hunk> = None;

    for line in patch.lines() {
        if line.starts_with("diff --git ") {
            finish_hunk(&mut current_file, &mut current_hunk);
            if let Some(file) = current_file.take() {
                files.push(file);
            }
            continue;
        }
        // `git diff --no-prefix` prints the new path without an `a/`, `b/`, or mnemonic
        // prefix, whatever diff.noprefix, diff.mnemonicPrefix, or diff.dstPrefix say.
        if let Some(path) = line.strip_prefix("+++ ") {
            current_file = (path != "/dev/null").then(|| FileDiff {
                file: path.to_owned(),
                hunks: Vec::new(),
            });
            continue;
        }
        if let Some(header) = line.strip_prefix("@@ ") {
            finish_hunk(&mut current_file, &mut current_hunk);
            let (old, new) = parse_hunk_header(header)?;
            current_hunk = Some(Hunk {
                old,
                new,
                text: format!("@@ {header}\n"),
            });
            continue;
        }
        if let Some(hunk) = &mut current_hunk {
            hunk.text.push_str(line);
            hunk.text.push('\n');
        }
    }
    finish_hunk(&mut current_file, &mut current_hunk);
    if let Some(file) = current_file {
        files.push(file);
    }
    Ok(files)
}

fn finish_hunk(file: &mut Option<FileDiff>, hunk: &mut Option<Hunk>) {
    if let (Some(file), Some(hunk)) = (file, hunk.take()) {
        file.hunks.push(hunk);
    }
}

fn parse_hunk_header(header: &str) -> Result<(LineRange, LineRange), Error> {
    let mut fields = header.split_whitespace();
    let old = fields
        .next()
        .and_then(|field| field.strip_prefix('-'))
        .and_then(parse_line_range);
    let new = fields
        .next()
        .and_then(|field| field.strip_prefix('+'))
        .and_then(parse_line_range);
    match (old, new) {
        (Some(old), Some(new)) => Ok((old, new)),
        _ => Err(Error::Invalid(format!(
            "could not parse Git hunk header @@ {header}"
        ))),
    }
}

fn parse_line_range(value: &str) -> Option<LineRange> {
    let (start, count) = value.split_once(',').unwrap_or((value, "1"));
    Some(LineRange {
        start: start.parse().ok()?,
        count: count.parse().ok()?,
    })
}

fn drift_file(
    diff: &FileDiff,
    before_source: Option<&str>,
    after_source: &str,
) -> Result<Vec<DriftFinding>, Error> {
    let before = before_source.map(parse_source).transpose()?;
    let after = parse_source(after_source)?;
    let mut findings = Vec::new();

    for (card_index, card) in after.cards.iter().enumerate() {
        let occurrence = after.cards[..card_index]
            .iter()
            .filter(|candidate| candidate.kind == card.kind && candidate.id == card.id)
            .count();
        let old_card = before.as_ref().and_then(|source| {
            source
                .cards
                .iter()
                .filter(|candidate| candidate.kind == card.kind && candidate.id == card.id)
                .nth(occurrence)
        });
        let card_changed = diff.hunks.iter().any(|hunk| {
            hunk.new.intersects(card.range)
                || old_card.is_some_and(|old| hunk.old.intersects(old.range))
        });
        if card_changed {
            continue;
        }

        for site in &card.sites {
            let old_item = before
                .as_ref()
                .and_then(|source| source.items.get(site))
                .and_then(|items| items.first());
            let new_item = after.items.get(site).and_then(|items| items.first());
            let relevant = diff
                .hunks
                .iter()
                .filter(|hunk| {
                    old_item.is_some_and(|item| hunk.old.intersects(item.range))
                        || new_item.is_some_and(|item| hunk.new.intersects(item.range))
                })
                .collect::<Vec<_>>();
            if relevant.is_empty()
                || old_item.map(|item| &item.tokens) == new_item.map(|item| &item.tokens)
            {
                continue;
            }
            findings.push(DriftFinding {
                card_id: card.id.clone(),
                file: diff.file.clone(),
                item: site.clone(),
                hunks: relevant.iter().map(|hunk| hunk.text.clone()).collect(),
                lean: card.lean.clone(),
            });
        }
    }
    Ok(findings)
}

#[derive(Clone, Debug, Default)]
struct ParsedSource {
    cards: Vec<LocatedCard>,
    items: BTreeMap<String, Vec<LocatedItem>>,
}

#[derive(Clone, Debug)]
struct LocatedCard {
    kind: CardKind,
    id: String,
    sites: Vec<String>,
    lean: Vec<String>,
    range: ItemRange,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CardKind {
    Primary,
    Site,
    Representation,
}

#[derive(Clone, Debug)]
struct LocatedItem {
    range: ItemRange,
    tokens: String,
}

#[derive(Clone, Debug)]
struct LocatedDoc {
    value: String,
    range: ItemRange,
}

fn parse_source(source: &str) -> Result<ParsedSource, Error> {
    let file = syn::parse_file(source)
        .map_err(|error| Error::Invalid(format!("could not parse changed Rust source: {error}")))?;
    let mut visitor = SourceVisitor::default();
    visitor.visit_file(&file);
    let cards = extract_cards(&visitor.docs)?;
    Ok(ParsedSource {
        cards,
        items: visitor.items,
    })
}

#[derive(Default)]
struct SourceVisitor {
    docs: Vec<LocatedDoc>,
    items: BTreeMap<String, Vec<LocatedItem>>,
    function_depth: usize,
}

impl SourceVisitor {
    fn add_item<T: ToTokens + Spanned>(&mut self, symbol: String, item: &T) {
        self.items.entry(symbol).or_default().push(LocatedItem {
            range: span_range(item.span()),
            tokens: strip_doc_attributes(item.to_token_stream()).to_string(),
        });
    }
}

impl<'ast> Visit<'ast> for SourceVisitor {
    fn visit_attribute(&mut self, attribute: &'ast syn::Attribute) {
        if attribute.path().is_ident("doc")
            && let syn::Meta::NameValue(name_value) = &attribute.meta
            && let syn::Expr::Lit(expression) = &name_value.value
            && let syn::Lit::Str(value) = &expression.lit
        {
            self.docs.push(LocatedDoc {
                value: value.value(),
                range: span_range(attribute.span()),
            });
        }
        visit::visit_attribute(self, attribute);
    }

    fn visit_item_fn(&mut self, item: &'ast syn::ItemFn) {
        if self.function_depth == 0 {
            self.add_item(item.sig.ident.to_string(), item);
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
        self.add_item(item.ident.to_string(), item);
        visit::visit_item_struct(self, item);
    }

    fn visit_item_enum(&mut self, item: &'ast syn::ItemEnum) {
        self.add_item(item.ident.to_string(), item);
        visit::visit_item_enum(self, item);
    }

    fn visit_item_union(&mut self, item: &'ast syn::ItemUnion) {
        self.add_item(item.ident.to_string(), item);
        visit::visit_item_union(self, item);
    }

    fn visit_item_type(&mut self, item: &'ast syn::ItemType) {
        self.add_item(item.ident.to_string(), item);
        visit::visit_item_type(self, item);
    }

    fn visit_item_impl(&mut self, item: &'ast syn::ItemImpl) {
        if let Some(type_name) = impl_type_name(&item.self_ty) {
            self.add_item(format!("impl {type_name}"), item);
            for impl_item in &item.items {
                if let syn::ImplItem::Fn(function) = impl_item {
                    self.add_item(format!("{type_name}::{}", function.sig.ident), function);
                }
            }
        }
        visit::visit_item_impl(self, item);
    }
}

/// Remove `#[doc = ..]` and `#![doc = ..]` attributes, so that a doc-comment edit compares equal.
fn strip_doc_attributes(tokens: TokenStream) -> TokenStream {
    let tokens = tokens.into_iter().collect::<Vec<_>>();
    let mut output = Vec::with_capacity(tokens.len());
    let mut index = 0;
    while index < tokens.len() {
        if let TokenTree::Punct(pound) = &tokens[index]
            && pound.as_char() == '#'
        {
            let bang = matches!(
                tokens.get(index + 1),
                Some(TokenTree::Punct(bang)) if bang.as_char() == '!'
            );
            let group_index = index + 1 + usize::from(bang);
            if let Some(TokenTree::Group(group)) = tokens.get(group_index)
                && group.delimiter() == Delimiter::Bracket
                && group
                    .stream()
                    .into_iter()
                    .next()
                    .is_some_and(|first| matches!(first, TokenTree::Ident(ident) if ident == "doc"))
            {
                index = group_index + 1;
                continue;
            }
        }
        output.push(match &tokens[index] {
            TokenTree::Group(group) => {
                let mut stripped =
                    Group::new(group.delimiter(), strip_doc_attributes(group.stream()));
                stripped.set_span(group.span());
                TokenTree::Group(stripped)
            }
            token => token.clone(),
        });
        index += 1;
    }
    output.into_iter().collect()
}

fn span_range(span: proc_macro2::Span) -> ItemRange {
    let LineColumn { line: start, .. } = span.start();
    let LineColumn { line: end, .. } = span.end();
    ItemRange { start, end }
}

fn extract_cards(docs: &[LocatedDoc]) -> Result<Vec<LocatedCard>, Error> {
    let mut cards = Vec::new();
    let mut current: Option<(CardKind, usize, usize, String)> = None;
    for doc in docs {
        if current
            .as_ref()
            .is_some_and(|(_, _, previous_end, _)| doc.range.start > *previous_end + 1)
        {
            current = None;
        }
        if let Some((kind, start, previous_end, body)) = &mut current {
            if doc.value.trim() == "```" {
                let body = toml::from_str::<DriftCardBody>(body).map_err(|error| {
                    Error::Invalid(format!(
                        "invalid algorithm card while checking drift: {error}"
                    ))
                })?;
                cards.push(LocatedCard {
                    kind: *kind,
                    id: body.id,
                    sites: body.sites,
                    lean: body.lean,
                    range: ItemRange {
                        start: *start,
                        end: doc.range.end,
                    },
                });
                current = None;
                continue;
            } else {
                body.push_str(doc.value.strip_prefix(' ').unwrap_or(&doc.value));
                body.push('\n');
                *previous_end = doc.range.end;
                continue;
            }
        }
        current = match doc.value.trim() {
            "```toml algorithm" | "```algorithm" => Some((
                CardKind::Primary,
                doc.range.start,
                doc.range.end,
                String::new(),
            )),
            "```toml algorithm-site" | "```algorithm-site" => Some((
                CardKind::Site,
                doc.range.start,
                doc.range.end,
                String::new(),
            )),
            "```toml algorithm-representation" | "```algorithm-representation" => Some((
                CardKind::Representation,
                doc.range.start,
                doc.range.end,
                String::new(),
            )),
            _ => None,
        };
    }
    Ok(cards)
}

#[derive(serde::Deserialize)]
struct DriftCardBody {
    id: String,
    sites: Vec<String>,
    #[serde(default)]
    lean: Vec<String>,
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
    use std::{
        fs,
        path::{Path, PathBuf},
        time::{SystemTime, UNIX_EPOCH},
    };

    use super::*;

    const ORIGINAL: &str = r#"//! ```toml algorithm
//! id = "backend.example"
//! name = "example"
//! sites = ["run"]
//! counters = []
//! no_counter = "example"
//! [[cost]]
//! mode = "one call"
//! bound = "O(1)"
//! ```

fn run() -> usize {
    1
}
"#;

    #[test]
    fn parses_paths_without_a_prefix() {
        let files = parse_patch(
            "diff --git crates/a/src/lib.rs crates/a/src/lib.rs\n--- crates/a/src/lib.rs\n+++ crates/a/src/lib.rs\n@@ -1 +1 @@\n-a\n+b\ndiff --git crates/a/src/gone.rs crates/a/src/gone.rs\n--- crates/a/src/gone.rs\n+++ /dev/null\n@@ -1 +0,0 @@\n-a\n",
        )
        .unwrap();
        assert_eq!(files.len(), 1);
        assert_eq!(files[0].file, "crates/a/src/lib.rs");
        assert_eq!(files[0].hunks.len(), 1);
    }

    #[test]
    fn doc_attributes_are_stripped_before_comparison() {
        let tokens = |source: &str| {
            let item = syn::parse_str::<syn::Item>(source).unwrap();
            strip_doc_attributes(item.to_token_stream()).to_string()
        };
        assert_eq!(
            tokens("/// Runs it.\nfn run() { //! inner\n 1 }"),
            tokens("/// Runs the thing.\n#[doc = \"more\"]\nfn run() { 1 }")
        );
        assert_ne!(tokens("#[inline] fn run() { 1 }"), tokens("fn run() { 1 }"));
    }

    #[test]
    fn ignores_a_doc_comment_only_change() {
        let Some(repository) = TestRepository::new() else {
            return;
        };
        let documented = ORIGINAL.replace("fn run()", "/// Runs it.\nfn run()");
        if !repository.commit_source(&documented) {
            return;
        }
        repository.write_source(&documented.replace("/// Runs it.", "/// Runs the thing."));

        let report = drift(&repository.path, "HEAD", None).unwrap();
        assert!(report.findings.is_empty(), "{report:?}");
    }

    #[test]
    fn reports_a_site_body_change() {
        let Some(repository) = TestRepository::new() else {
            return;
        };
        if !repository.commit_source(ORIGINAL) {
            return;
        }
        repository.write_source(&ORIGINAL.replace("    1", "    2"));

        let report = drift(&repository.path, "HEAD", None).unwrap();
        assert_eq!(report.findings.len(), 1);
        assert_eq!(report.findings[0].card_id, "backend.example");
        assert_eq!(report.findings[0].item, "run");
        assert!(report.findings[0].hunks[0].contains("-    1"));
        assert!(report.findings[0].hunks[0].contains("+    2"));
    }

    #[test]
    fn names_the_lean_theorems_of_a_representation_card_whose_site_changed() {
        let Some(repository) = TestRepository::new() else {
            return;
        };
        let original = r#"/// ```toml algorithm-representation
/// id = "representation.example.value"
/// name = "one value"
/// type = "example::Value"
/// sites = ["Value::new"]
/// invariant = "the field is positive"
/// lean = ["KRust.Example.positive"]
/// ```
pub struct Value(u32);

impl Value {
    fn new() -> Self {
        Value(1)
    }
}
"#;
        if !repository.commit_source(original) {
            return;
        }
        repository.write_source(&original.replace("Value(1)", "Value(0)"));

        let report = drift(&repository.path, "HEAD", None).unwrap();
        assert_eq!(report.findings.len(), 1, "{report:?}");
        assert_eq!(report.findings[0].card_id, "representation.example.value");
        assert_eq!(report.findings[0].item, "Value::new");
        assert_eq!(report.findings[0].lean, ["KRust.Example.positive"]);
        assert!(
            render_drift(&report).contains("re-check the Lean models of: KRust.Example.positive")
        );
    }

    #[test]
    fn ignores_comment_and_format_only_changes() {
        let Some(repository) = TestRepository::new() else {
            return;
        };
        if !repository.commit_source(ORIGINAL) {
            return;
        }
        repository.write_source(&ORIGINAL.replace(
            "fn run() -> usize {\n    1\n}",
            "fn run( ) -> usize\n{\n    // An explanatory comment.\n    1\n}",
        ));

        let report = drift(&repository.path, "HEAD", None).unwrap();
        assert!(report.findings.is_empty());
    }

    #[test]
    fn ignores_a_site_change_when_its_card_changes_too() {
        let Some(repository) = TestRepository::new() else {
            return;
        };
        if !repository.commit_source(ORIGINAL) {
            return;
        }
        let changed = ORIGINAL
            .replace("name = \"example\"", "name = \"revised example\"")
            .replace("    1", "    2");
        repository.write_source(&changed);

        let report = drift(&repository.path, "HEAD", None).unwrap();
        assert!(report.findings.is_empty());
    }

    struct TestRepository {
        path: PathBuf,
    }

    impl TestRepository {
        /// A fresh repository, or `None` (with a message) when `git` is absent or fails.
        fn new() -> Option<Self> {
            let nonce = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos();
            let path = std::env::temp_dir()
                .join(format!("algo-graph-drift-{}-{nonce}", std::process::id()));
            fs::create_dir_all(path.join("crates/example/src")).unwrap();
            let repository = Self { path };
            git(&repository.path, &["init", "--quiet"]).then_some(repository)
        }

        fn write_source(&self, source: &str) {
            fs::write(self.path.join("crates/example/src/lib.rs"), source).unwrap();
        }

        /// Commit `source`; `false` (with a message) when `git` refuses to commit.
        fn commit_source(&self, source: &str) -> bool {
            self.write_source(source);
            git(&self.path, &["add", "."])
                && git(
                    &self.path,
                    &[
                        "-c",
                        "user.name=Algorithm Graph Test",
                        "-c",
                        "user.email=algorithm-graph@example.invalid",
                        "-c",
                        "commit.gpgsign=false",
                        "commit",
                        "--quiet",
                        "--no-verify",
                        "-m",
                        "fixture",
                    ],
                )
        }
    }

    impl Drop for TestRepository {
        fn drop(&mut self) {
            fs::remove_dir_all(&self.path).unwrap();
        }
    }

    /// Run `git`; on a missing binary or a failure, print why the test is skipped.
    fn git(root: &Path, arguments: &[&str]) -> bool {
        match Command::new("git")
            .arg("-C")
            .arg(root)
            .args(arguments)
            .output()
        {
            Ok(output) if output.status.success() => true,
            Ok(output) => {
                eprintln!(
                    "skipping drift test: git {} failed: {}",
                    arguments.join(" "),
                    String::from_utf8_lossy(&output.stderr).trim()
                );
                false
            }
            Err(error) => {
                eprintln!("skipping drift test: git is not runnable: {error}");
                false
            }
        }
    }
}
