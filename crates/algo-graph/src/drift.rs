use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::Write as _,
    fs, io,
    io::{BufRead, BufReader, Read, Write as _},
    path::Path,
    process::{Output, Stdio},
};

use proc_macro2::{Delimiter, Group, TokenStream, TokenTree};

use crate::{
    Error,
    cards::{self, Card, CountedSite, CounterBump, CounterClaims, LocatedDoc, named_source},
    git_command,
};

/// A card whose implementation site changed without its fence changing.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DriftFinding {
    pub card_id: String,
    pub file: String,
    pub item: String,
    pub hunks: Vec<String>,
    /// The card's `lean` theorems: their models mirror the changed site and must be re-checked.
    pub lean: Vec<String>,
    /// For a counted site (`docs/algorithm-cards.md`), the counters the item bumps that the
    /// algorithm claims; empty for a site a card names.
    pub counters: Vec<String>,
}

/// The report produced for a Git revision range.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct DriftReport {
    pub findings: Vec<DriftFinding>,
}

/// Find card sites whose parsed Rust item changed while the card fence did not.
///
/// A site is a named one (a card's `sites` entry, in the card's file) or a counted one: an item
/// that bumps a counter which no claimant's card names (`docs/algorithm-cards.md`), reported for
/// each algorithm that claims the counter, read from the cards of the whole tree at `until`.
///
/// `until = None` compares `since` with the index and working tree. Findings are
/// advisory: their presence never turns this operation into an error.
pub fn drift(root: &Path, since: &str, until: Option<&str>) -> Result<DriftReport, Error> {
    let patch = git_diff(root, since, until)?;
    let mut changed = Vec::new();
    for diff in parse_patch(&patch)? {
        let Some(after_source) = revision_source(root, until, &diff.file)? else {
            continue;
        };
        let before_source = revision_source(root, Some(since), &diff.file)?;
        changed.push(ChangedFile {
            before: before_source.as_deref().map(parse_source).transpose()?,
            after: parse_source(&after_source)?,
            diff,
        });
    }

    let mut findings = changed.iter().flat_map(named_findings).collect::<Vec<_>>();
    if changed.iter().any(|file| {
        !file.after.counter_bumps.is_empty()
            || file
                .before
                .as_ref()
                .is_some_and(|before| !before.counter_bumps.is_empty())
    }) {
        let cards = cards_at(root, until)?;
        findings.extend(counted_findings(&changed, &cards));
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
        if finding.counters.is_empty() {
            let _ = writeln!(
                output,
                "card {} ({}): site {} changed while its card did not",
                finding.card_id, finding.file, finding.item
            );
        } else {
            let _ = writeln!(
                output,
                "card {} ({}): counted site {} changed while its card did not; it bumps {}",
                finding.card_id,
                finding.file,
                finding.item,
                finding
                    .counters
                    .iter()
                    .map(|counter| format!("Counter::{counter}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            );
        }
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
    git_command(root)
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

/// A changed file: its diff and its source parsed at both ends of the range.
struct ChangedFile {
    diff: FileDiff,
    before: Option<ParsedSource>,
    after: ParsedSource,
}

impl ChangedFile {
    /// Whether a hunk touches the fence of `self.after.cards[index]`, at either end.
    fn card_changed(&self, index: usize) -> bool {
        let card = &self.after.cards[index];
        let occurrence = self.after.cards[..index]
            .iter()
            .filter(|candidate| candidate.kind == card.kind && candidate.id == card.id)
            .count();
        let old_card = self.before.as_ref().and_then(|source| {
            source
                .cards
                .iter()
                .filter(|candidate| candidate.kind == card.kind && candidate.id == card.id)
                .nth(occurrence)
        });
        self.diff.hunks.iter().any(|hunk| {
            hunk.new.intersects(card.range)
                || old_card.is_some_and(|old| hunk.old.intersects(old.range))
        })
    }

    /// The hunks that change the item `symbol` names, or none when its tokens are unchanged.
    fn item_change(&self, symbol: &str) -> Vec<String> {
        let old_item = self
            .before
            .as_ref()
            .and_then(|source| source.items.get(symbol))
            .and_then(|items| items.first());
        let new_item = self.after.items.get(symbol).and_then(|items| items.first());
        if old_item.map(|item| &item.tokens) == new_item.map(|item| &item.tokens) {
            return Vec::new();
        }
        self.diff
            .hunks
            .iter()
            .filter(|hunk| {
                old_item.is_some_and(|item| hunk.old.intersects(item.range))
                    || new_item.is_some_and(|item| hunk.new.intersects(item.range))
            })
            .map(|hunk| hunk.text.clone())
            .collect()
    }
}

/// The changed sites that the file's own cards name.
fn named_findings(changed: &ChangedFile) -> Vec<DriftFinding> {
    let mut findings = Vec::new();
    for (card_index, card) in changed.after.cards.iter().enumerate() {
        if changed.card_changed(card_index) {
            continue;
        }
        for site in &card.sites {
            let hunks = changed.item_change(site);
            if hunks.is_empty() {
                continue;
            }
            findings.push(DriftFinding {
                card_id: card.id.clone(),
                file: changed.diff.file.clone(),
                item: site.clone(),
                hunks,
                lean: card.lean.clone(),
                counters: Vec::new(),
            });
        }
    }
    findings
}

/// The changed counted sites: an item of a graph source file (not a test target) that bumps a
/// counter at either end of the range, where
/// `cards`, the cards of the whole tree at the end of the range, place it as a counted site of
/// the counter's claimants. A claimant is not reported when a card of it that claims the counter
/// changed in the range.
fn counted_findings(changed: &[ChangedFile], cards: &[Card]) -> Vec<DriftFinding> {
    let claims = CounterClaims::new(cards);
    let mut findings = BTreeMap::<(String, String, String), DriftFinding>::new();
    for file in changed
        .iter()
        .filter(|file| cards::is_graph_source(&file.diff.file))
    {
        let bumps = file
            .before
            .iter()
            .flat_map(|before| &before.counter_bumps)
            .chain(&file.after.counter_bumps)
            .collect::<BTreeSet<_>>();
        for bump in bumps {
            let CountedSite::Counted { symbol, algorithms } = claims.place(&file.diff.file, bump)
            else {
                continue;
            };
            let hunks = file.item_change(symbol);
            if hunks.is_empty() {
                continue;
            }
            for algorithm in algorithms {
                let claiming = cards
                    .iter()
                    .filter(|card| {
                        &card.body.id == algorithm && card.body.counters.contains(&bump.counter)
                    })
                    .collect::<Vec<_>>();
                if claiming
                    .iter()
                    .any(|card| claim_changed(changed, card, &bump.counter))
                {
                    continue;
                }
                let finding = findings
                    .entry((file.diff.file.clone(), algorithm.clone(), symbol.to_owned()))
                    .or_insert_with(|| DriftFinding {
                        card_id: algorithm.clone(),
                        file: file.diff.file.clone(),
                        item: symbol.to_owned(),
                        hunks: hunks.clone(),
                        lean: Vec::new(),
                        counters: Vec::new(),
                    });
                for card in claiming {
                    for theorem in &card.body.lean {
                        if !finding.lean.contains(theorem) {
                            finding.lean.push(theorem.clone());
                        }
                    }
                }
                if !finding.counters.contains(&bump.counter) {
                    finding.counters.push(bump.counter.clone());
                }
            }
        }
    }
    findings.into_values().collect()
}

/// Whether the range changed the fence of `card`, a card of the tree at its end that claims
/// `counter`.
fn claim_changed(changed: &[ChangedFile], card: &Card, counter: &str) -> bool {
    changed
        .iter()
        .filter(|file| file.diff.file == card.file)
        .any(|file| {
            file.after.cards.iter().enumerate().any(|(index, located)| {
                located.id == card.body.id
                    && located.counters.iter().any(|claimed| claimed == counter)
                    && file.card_changed(index)
            })
        })
}

/// The cards of every workspace source file at `revision`, or in the working tree for `None`.
/// A file that does not parse contributes no card.
fn cards_at(root: &Path, revision: Option<&str>) -> Result<Vec<Card>, Error> {
    let mut ignored = Vec::new();
    let Some(revision) = revision else {
        return Ok(cards::read_cards(root, &mut ignored)?.0);
    };
    let listing = git_stdout(
        root,
        &[
            "ls-tree",
            "-r",
            "-z",
            "--name-only",
            revision,
            "--",
            "crates",
        ],
    )?;
    let files = listing
        .split('\0')
        .filter(|path| cards::is_graph_source(path))
        .map(ToOwned::to_owned)
        .collect::<Vec<_>>();
    let sources = revision_sources(root, revision, &files)?;
    Ok(cards::index_sources(sources, &mut ignored).0)
}

/// The text of each of `files` at `revision`, read by one `git cat-file --batch`.
fn revision_sources(
    root: &Path,
    revision: &str,
    files: &[String],
) -> Result<Vec<(String, String)>, Error> {
    let mut child = git_command(root)
        .args(["cat-file", "--batch"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .map_err(Error::Io)?;
    let mut stdin = child.stdin.take().expect("stdin is piped");
    let requests = files
        .iter()
        .map(|file| format!("{revision}:{file}\n"))
        .collect::<String>();
    // Written from another thread: git answers each request as it reads it, so writing every
    // request before reading could fill both pipes.
    let writer = std::thread::spawn(move || stdin.write_all(requests.as_bytes()));
    let mut output = BufReader::new(child.stdout.take().expect("stdout is piped"));
    let mut sources = Vec::with_capacity(files.len());
    for file in files {
        let mut header = String::new();
        output.read_line(&mut header).map_err(Error::Io)?;
        if header.trim_end().ends_with(" missing") {
            continue;
        }
        // `<object id> <type> <size>`, then the contents and a newline.
        let Some(size) = header
            .split_whitespace()
            .nth(2)
            .and_then(|size| size.parse::<usize>().ok())
        else {
            return Err(Error::Invalid(format!(
                "git cat-file --batch answered {file} with {header:?}"
            )));
        };
        let mut contents = vec![0; size + 1];
        output.read_exact(&mut contents).map_err(Error::Io)?;
        contents.pop();
        if let Ok(source) = String::from_utf8(contents) {
            sources.push((file.clone(), source));
        }
    }
    writer
        .join()
        .expect("the request writer does not panic")
        .map_err(Error::Io)?;
    child.wait().map_err(Error::Io)?;
    Ok(sources)
}

#[derive(Clone, Debug, Default)]
struct ParsedSource {
    cards: Vec<LocatedCard>,
    items: BTreeMap<String, Vec<LocatedItem>>,
    counter_bumps: BTreeSet<CounterBump>,
}

#[derive(Clone, Debug)]
struct LocatedCard {
    kind: CardKind,
    id: String,
    sites: Vec<String>,
    lean: Vec<String>,
    counters: Vec<String>,
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

fn parse_source(source: &str) -> Result<ParsedSource, Error> {
    let named = named_source(source)
        .map_err(|error| Error::Invalid(format!("could not parse changed Rust source: {error}")))?;
    let cards = extract_cards(&named.docs)?;
    let items = named
        .items
        .into_iter()
        .map(|(symbol, items)| {
            let items = items
                .into_iter()
                .map(|(span, tokens)| LocatedItem {
                    range: ItemRange {
                        start: span.start,
                        end: span.end,
                    },
                    tokens: strip_doc_attributes(tokens).to_string(),
                })
                .collect();
            (symbol, items)
        })
        .collect();
    Ok(ParsedSource {
        cards,
        items,
        counter_bumps: named.counter_bumps,
    })
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

fn extract_cards(docs: &[LocatedDoc]) -> Result<Vec<LocatedCard>, Error> {
    let mut cards = Vec::new();
    let mut current: Option<(CardKind, usize, usize, String)> = None;
    for doc in docs {
        if current
            .as_ref()
            .is_some_and(|(_, _, previous_end, _)| doc.start > *previous_end + 1)
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
                    counters: body.counters,
                    range: ItemRange {
                        start: *start,
                        end: doc.end,
                    },
                });
                current = None;
                continue;
            } else {
                body.push_str(doc.value.strip_prefix(' ').unwrap_or(&doc.value));
                body.push('\n');
                *previous_end = doc.end;
                continue;
            }
        }
        current = match doc.value.trim() {
            "```toml algorithm" | "```algorithm" => {
                Some((CardKind::Primary, doc.start, doc.end, String::new()))
            }
            "```toml algorithm-site" | "```algorithm-site" => {
                Some((CardKind::Site, doc.start, doc.end, String::new()))
            }
            "```toml algorithm-representation" | "```algorithm-representation" => {
                Some((CardKind::Representation, doc.start, doc.end, String::new()))
            }
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
    #[serde(default)]
    counters: Vec<String>,
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
            strip_doc_attributes(quote::ToTokens::to_token_stream(&item)).to_string()
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

    const CLAIMANT: &str = r#"//! ```toml algorithm
//! id = "backend.example"
//! name = "example"
//! sites = ["run"]
//! counters = ["ExampleSteps"]
//! [[cost]]
//! mode = "one call"
//! bound = "O(1)"
//! ```

fn run() -> usize {
    walk::walk()
}
"#;

    const WALK: &str = r#"pub fn walk() -> usize {
    measure::bump(Counter::ExampleSteps);
    1
}

pub fn unrelated() -> usize {
    1
}
"#;

    #[test]
    fn reports_a_counted_site_of_each_claimant_of_the_counter_it_bumps() {
        let Some(repository) = TestRepository::new() else {
            return;
        };
        repository.write_file("walk.rs", WALK);
        if !repository.commit_source(CLAIMANT) {
            return;
        }
        repository.write_file(
            "walk.rs",
            &WALK.replace("    1\n}\n\npub", "    2\n}\n\npub"),
        );

        let report = drift(&repository.path, "HEAD", None).unwrap();
        assert_eq!(report.findings.len(), 1, "{report:?}");
        let finding = &report.findings[0];
        assert_eq!(
            (
                finding.card_id.as_str(),
                finding.file.as_str(),
                finding.item.as_str()
            ),
            ("backend.example", "crates/example/src/walk.rs", "walk")
        );
        assert_eq!(finding.counters, ["ExampleSteps"]);
        assert!(render_drift(&report).contains(
            "counted site walk changed while its card did not; it bumps Counter::ExampleSteps"
        ));

        // The same range read from two commits, whose cards come from the later one.
        if !repository.commit() {
            return;
        }
        let committed = drift(&repository.path, "HEAD~1", Some("HEAD")).unwrap();
        assert_eq!(committed, report);

        // A change to the claiming card's fence in the same range is its review.
        repository.write_source(&CLAIMANT.replace("name = \"example\"", "name = \"walked\""));
        assert!(
            drift(&repository.path, "HEAD~1", None)
                .unwrap()
                .findings
                .is_empty()
        );
    }

    #[test]
    fn a_counted_item_named_by_a_claimant_is_reported_once_as_its_site() {
        let Some(repository) = TestRepository::new() else {
            return;
        };
        let named = CLAIMANT
            .replace("sites = [\"run\"]", "sites = [\"run\", \"walk\"]")
            .replace("    walk::walk()\n}\n", "    walk()\n}\n\nfn walk() -> usize {\n    measure::bump(Counter::ExampleSteps);\n    1\n}\n");
        if !repository.commit_source(&named) {
            return;
        }
        repository.write_source(&named.replace("ExampleSteps);\n    1", "ExampleSteps);\n    2"));

        let report = drift(&repository.path, "HEAD", None).unwrap();
        assert_eq!(report.findings.len(), 1, "{report:?}");
        assert_eq!(report.findings[0].item, "walk");
        assert!(report.findings[0].counters.is_empty());
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
            self.write_file("lib.rs", source);
        }

        fn write_file(&self, name: &str, source: &str) {
            fs::write(self.path.join("crates/example/src").join(name), source).unwrap();
        }

        /// Commit `source`; `false` (with a message) when `git` refuses to commit.
        fn commit_source(&self, source: &str) -> bool {
            self.write_source(source);
            self.commit()
        }

        /// Commit the working tree; `false` (with a message) when `git` refuses to commit.
        fn commit(&self) -> bool {
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
        match git_command(root).args(arguments).output() {
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
