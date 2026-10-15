//! The mutation list an LLM writes (`MUTATIONS.toml`, flow README section 5.5) and its
//! resolution into one pinned [`Patch`] per mutation.
//!
//! A mutation is one or more text edits, each addressed to one authored rule of the
//! specification: by its label, by a line inside it, or by the unique occurrence of its
//! `find` text in the file. Every text an edit addresses, searches or shows is in the file's
//! **K view** (flow README 6.1): the text k-rust parsed, which is the file itself for a `.k`
//! source and the extraction of the selected fences for a `.md` source (prose and fence lines
//! reduced to whitespace, so lines and columns are the file's). kink-flow never edits the
//! user's Markdown: [`View`]'s constructor is the only code that reads a Markdown file's text,
//! and the envelope builder ([`markdown_envelope`]) the only code that writes Markdown.
//! Resolution is all or nothing:
//!
//! 1. every source file the mutation touches gets its K view, checked against the baseline's
//!    source table (an extraction of that file with the recomputed offset map, else
//!    `source-view-mismatch`); every edit is addressed to exactly one rule sentence of the
//!    baseline, whose span in the view is its offset attributes
//!    (`SentenceStartOffset`/`SentenceEndOffset`), which must name the same bytes as its
//!    location (else `no-usable-span`);
//! 2. the edits are applied to the views, and the edited views are loaded with the
//!    specification's own load options (kink-corpus [`load_source_with_overlay`]): a `.k` file
//!    as its edited view, a `.md` file as a one-fence Markdown envelope of its edited view whose
//!    extraction must give the edited view back (else `markdown-envelope`). The edited load
//!    must have the baseline's modules and sentences in the same order with equal
//!    fingerprints, except that each replaced rule is exactly one rule sentence with the same
//!    label and each deleted rule is gone; and in every edited file every sentence must start
//!    (and, unless it is a replaced rule, end) where the edits move it (else `span-changed`);
//! 3. one [`Patch`] is built: a `ReplaceSentence` with the edited load's sentence (carrying the
//!    baseline sentence's position and provenance attributes, as kink-patch requires) at each
//!    replaced rule and a `DeleteSentence` at each deleted rule, pinned to the baseline
//!    fingerprints. Its [`CandidateGeneration`] ([`ResolvedMutation::generation`]) holds
//!    exactly that patch, so application, validation, compilation, digests and replay are
//!    the existing pipeline's. The mutation digest is [`Patch::digest`].
//!
//! Anything else is an [`InvalidMutation`] naming the edit and the reason, and no patch
//! exists for it. Resolution only loads; it never compiles (it has no validator).

use crate::{
    admit::corpus_source,
    manifest::{FlowManifest, ManifestError},
};
use k_rust::{
    definition::{AttributeKey, Attributes, Definition, Location, Sentence},
    outer::extract_fenced_k_code_with_map,
    provenance::{LogicalSourceId, SourceId},
};
use kink_corpus::{LoadedSource, resolver::load_source_with_overlay};
use kink_patch::{
    Baseline, Bindings, CandidateDisposition, CandidateGeneration, Discovery, DiscoveryTuple, Edit,
    POSITION_KEYS, Patch, SelectionPolicy, SentenceFingerprint, SentenceRef, Sha256Digest, Site,
    TermRef, select, sha256,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt, fs,
    ops::Range,
    path::{Component, Path, PathBuf},
    sync::Arc,
};
use toml::{Table, Value};

/// The operator name of every flow mutation's candidate generation.
pub const MUTATION_OPERATOR: &str = "kink-flow/mutation/v1";

/// A decoded `MUTATIONS.toml`.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct MutationList {
    pub mutations: Vec<Mutation>,
}

/// One `[[mutation]]`: its edits are applied together or not at all.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Mutation {
    pub id: String,
    /// Free text for the reader; it enters no digest.
    pub note: Option<String>,
    pub edits: Vec<EditSpec>,
}

/// One `[[mutation.edit]]`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EditSpec {
    /// The source file, relative to the manifest's directory; optional when the
    /// specification reads one file or when `rule` names the rule.
    pub file: Option<String>,
    /// A rule label, module-qualified (`CALC.add`) or bare (`add`) when that is unique.
    pub rule: Option<String>,
    /// A line (1-based) inside the rule.
    pub line: Option<u32>,
    pub action: EditAction,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum EditAction {
    /// Replace the unique occurrence of `find` in the addressed rule (or, with neither
    /// `rule` nor `line`, in the file, inside one rule).
    Replace { find: String, replace: String },
    /// Remove the addressed rule.
    Delete,
}

impl MutationList {
    /// Read and decode the mutation list at `path`.
    pub fn read(path: &Path) -> Result<Self, ManifestError> {
        let text = fs::read_to_string(path)
            .map_err(|e| ManifestError::new("", format!("cannot read the mutation list: {e}")))?;
        Self::decode(&text)
    }

    /// Decode a mutation list. Unknown keys, values of the wrong type, duplicate or empty
    /// ids, a mutation without edits and an edit that is not exactly one of find/replace or
    /// `delete = true` are errors naming the key.
    pub fn decode(text: &str) -> Result<Self, ManifestError> {
        let top: Table = toml::from_str(text)
            .map_err(|e| ManifestError::new("", format!("invalid TOML: {e}")))?;
        known_keys(&top, "", &["mutation"])?;
        let mutations = match top.get("mutation") {
            None => Vec::new(),
            Some(Value::Array(entries)) => entries
                .iter()
                .enumerate()
                .map(|(index, entry)| mutation(index, entry))
                .collect::<Result<Vec<_>, _>>()?,
            Some(_) => {
                return Err(ManifestError::new(
                    "mutation",
                    "expected [[mutation]] tables",
                ));
            }
        };
        let mut ids = BTreeSet::new();
        for mutation in &mutations {
            if !ids.insert(mutation.id.as_str()) {
                return Err(ManifestError::new(
                    mutation_key(&mutation.id),
                    "duplicate mutation id",
                ));
            }
        }
        Ok(Self { mutations })
    }
}

fn mutation_key(id: &str) -> String {
    format!("mutation {id:?}")
}

fn join(prefix: &str, key: &str) -> String {
    if prefix.is_empty() {
        key.to_owned()
    } else {
        format!("{prefix}.{key}")
    }
}

fn known_keys(table: &Table, prefix: &str, known: &[&str]) -> Result<(), ManifestError> {
    match table.keys().find(|key| !known.contains(&key.as_str())) {
        Some(key) => Err(ManifestError::new(join(prefix, key), "unknown key")),
        None => Ok(()),
    }
}

fn non_empty(value: &Value, key: &str) -> Result<String, ManifestError> {
    match value.as_str() {
        Some(text) if !text.is_empty() => Ok(text.to_owned()),
        Some(_) => Err(ManifestError::new(key, "must not be empty")),
        None => Err(ManifestError::new(key, "expected a string")),
    }
}

fn optional_non_empty(
    table: &Table,
    prefix: &str,
    name: &str,
) -> Result<Option<String>, ManifestError> {
    table
        .get(name)
        .map(|value| non_empty(value, &join(prefix, name)))
        .transpose()
}

fn mutation(index: usize, value: &Value) -> Result<Mutation, ManifestError> {
    let position = format!("mutation[{index}]");
    let entry = value
        .as_table()
        .ok_or_else(|| ManifestError::new(&position, "expected a table"))?;
    let id = non_empty(
        entry
            .get("id")
            .ok_or_else(|| ManifestError::new(join(&position, "id"), "missing required key"))?,
        &join(&position, "id"),
    )?;
    let key = mutation_key(&id);
    known_keys(entry, &key, &["id", "note", "edit"])?;
    let note = match entry.get("note") {
        None => None,
        Some(Value::String(note)) => Some(note.clone()),
        Some(_) => return Err(ManifestError::new(join(&key, "note"), "expected a string")),
    };
    let edits = match entry.get("edit") {
        Some(Value::Array(edits)) if !edits.is_empty() => edits
            .iter()
            .enumerate()
            .map(|(index, edit)| edit_spec(&format!("{key}.edit[{index}]"), edit))
            .collect::<Result<Vec<_>, _>>()?,
        Some(Value::Array(_)) | None => {
            return Err(ManifestError::new(
                key,
                "needs at least one [[mutation.edit]]",
            ));
        }
        Some(_) => {
            return Err(ManifestError::new(
                join(&key, "edit"),
                "expected [[mutation.edit]] tables",
            ));
        }
    };
    Ok(Mutation { id, note, edits })
}

fn edit_spec(key: &str, value: &Value) -> Result<EditSpec, ManifestError> {
    let entry = value
        .as_table()
        .ok_or_else(|| ManifestError::new(key, "expected a table"))?;
    known_keys(
        entry,
        key,
        &["file", "rule", "line", "find", "replace", "delete"],
    )?;
    let file = optional_non_empty(entry, key, "file")?;
    let rule = optional_non_empty(entry, key, "rule")?;
    let line = match entry.get("line") {
        None => None,
        Some(Value::Integer(line)) if *line > 0 => Some(
            u32::try_from(*line)
                .map_err(|_| ManifestError::new(join(key, "line"), "is too large"))?,
        ),
        Some(Value::Integer(_)) => {
            return Err(ManifestError::new(join(key, "line"), "must be positive"));
        }
        Some(_) => {
            return Err(ManifestError::new(join(key, "line"), "expected an integer"));
        }
    };
    let action = match (entry.get("find"), entry.get("replace"), entry.get("delete")) {
        (Some(find), Some(replace), None) => EditAction::Replace {
            find: non_empty(find, &join(key, "find"))?,
            replace: replace
                .as_str()
                .ok_or_else(|| ManifestError::new(join(key, "replace"), "expected a string"))?
                .to_owned(),
        },
        (None, None, Some(Value::Boolean(true))) => EditAction::Delete,
        (_, _, Some(Value::Boolean(false))) => {
            return Err(ManifestError::new(
                join(key, "delete"),
                "must be true; leave it out for a find/replace edit",
            ));
        }
        (_, _, Some(Value::Boolean(true))) => {
            return Err(ManifestError::new(
                key,
                "give find and replace, or delete = true, not both",
            ));
        }
        (_, _, Some(_)) => {
            return Err(ManifestError::new(
                join(key, "delete"),
                "expected a boolean",
            ));
        }
        (Some(_), None, None) => {
            return Err(ManifestError::new(
                join(key, "replace"),
                "missing: find needs replace",
            ));
        }
        (None, Some(_), None) => {
            return Err(ManifestError::new(
                join(key, "find"),
                "missing: replace needs find",
            ));
        }
        (None, None, None) => {
            return Err(ManifestError::new(
                key,
                "give find and replace, or delete = true",
            ));
        }
    };
    if action == EditAction::Delete && rule.is_none() && line.is_none() {
        return Err(ManifestError::new(
            key,
            "delete = true needs rule or line to address the rule",
        ));
    }
    Ok(EditSpec {
        file,
        rule,
        line,
        action,
    })
}

/// Why a mutation has no patch.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum InvalidReason {
    /// `file` is not a source file of the specification.
    UnknownFile,
    /// The specification reads several files and the edit names neither a file nor a rule.
    FileRequired,
    /// No authored sentence has the label.
    UnknownLabel,
    /// The bare label names several rules; qualify it with the module.
    AmbiguousLabel,
    /// No authored sentence covers the line.
    LineOutsideRules,
    /// Several rules cover the line.
    LineAmbiguous,
    /// `rule`, `line` and `file` do not all address the same rule.
    AddressMismatch,
    /// The addressed sentence is not a rule (only rules are editable).
    NonRuleSentence,
    /// The addressed rule has no usable source span.
    NoUsableSpan,
    /// `find` does not occur where the edit looks for it.
    FindNotFound,
    /// `find` occurs more than once where the edit looks for it.
    FindAmbiguous,
    /// `find` occurs in the file but not inside the addressed rule, or (with neither
    /// `rule` nor `line`) not inside any rule.
    EditOutsideRule,
    /// Two edits of one rule overlap, or a rule is deleted and edited.
    OverlappingEdits,
    /// A source file differs from the one the specification was loaded from.
    SourceChanged,
    /// The K view of a source file (its text, or for `.md` its extraction under the
    /// manifest's `md_selector`) is not an extraction the baseline's source table holds, or
    /// an addressed rule's spans do not index it: it is not what k-rust parsed.
    SourceViewMismatch,
    /// The Markdown envelope of an edited K view does not extract to that view, or an edit
    /// makes a line of the view a Markdown fence line.
    MarkdownEnvelope,
    /// The edited sources do not load.
    EditedLoadFailed,
    /// The edited load does not have the baseline's sentences outside the addressed rules,
    /// or an edited rule is no longer exactly one rule sentence.
    StructureChanged,
    /// The edit changes the rule's label.
    LabelChanged,
    /// In an edited file, a sentence of the edited load does not start where the edits move
    /// its baseline start, an unaddressed sentence does not end where they move its end, or a
    /// replaced rule ends later than that, or earlier by more than whitespace.
    SpanChanged,
    /// The edited rule is the baseline rule up to formatting.
    NoChange,
    /// kink-patch refused the patch (defensive: the checks above make it unreachable).
    PatchRejected,
}

impl InvalidReason {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::UnknownFile => "unknown-file",
            Self::FileRequired => "file-required",
            Self::UnknownLabel => "unknown-label",
            Self::AmbiguousLabel => "ambiguous-label",
            Self::LineOutsideRules => "line-outside-rules",
            Self::LineAmbiguous => "line-ambiguous",
            Self::AddressMismatch => "address-mismatch",
            Self::NonRuleSentence => "non-rule-sentence",
            Self::NoUsableSpan => "no-usable-span",
            Self::FindNotFound => "find-not-found",
            Self::FindAmbiguous => "find-ambiguous",
            Self::EditOutsideRule => "edit-outside-rule",
            Self::OverlappingEdits => "overlapping-edits",
            Self::SourceChanged => "source-changed",
            Self::SourceViewMismatch => "source-view-mismatch",
            Self::MarkdownEnvelope => "markdown-envelope",
            Self::EditedLoadFailed => "edited-load-failed",
            Self::StructureChanged => "structure-changed",
            Self::LabelChanged => "label-changed",
            Self::SpanChanged => "span-changed",
            Self::NoChange => "no-change",
            Self::PatchRejected => "patch-rejected",
        }
    }
}

/// A mutation that resolves to no patch (status `invalid-mutation`).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InvalidMutation {
    /// The index of the offending edit in the mutation (`edit[i]`), when one edit is at fault.
    pub edit: Option<usize>,
    pub reason: InvalidReason,
    pub detail: String,
}

impl fmt::Display for InvalidMutation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(edit) = self.edit {
            write!(f, "edit[{edit}]: ")?;
        }
        write!(f, "{}: {}", self.reason.as_str(), self.detail)
    }
}

impl std::error::Error for InvalidMutation {}

/// A mutation resolved into one pinned patch.
#[derive(Clone, Debug)]
pub struct ResolvedMutation {
    pub id: String,
    /// The pinned patch: a `ReplaceSentence` or `DeleteSentence` per addressed rule.
    pub patch: Patch,
    /// [`Patch::digest`]: the mutation's identity.
    pub digest: Sha256Digest,
    /// The addressed rules, in sentence order.
    pub rules: Vec<EditedRule>,
    /// The edited K view of every edited source file, by its logical name: for a `.k` file its
    /// edited text, for a `.md` file its edited K view (never Markdown).
    pub edited_views: BTreeMap<String, String>,
    /// F-04's name for [`Self::edited_views`], kept for its callers: the same K text.
    pub edited_sources: BTreeMap<String, String>,
    /// What the edited load read in place of each edited file (see [`Self::overlay`]).
    overlay: BTreeMap<String, String>,
}

/// One rule a mutation edits or deletes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EditedRule {
    pub at: SentenceRef,
    /// The indices of the mutation's edits addressed to this rule.
    pub edits: Vec<usize>,
    pub file: String,
    pub label: Option<String>,
    /// The baseline rule's lines (1-based, inclusive).
    pub start_line: u32,
    pub end_line: u32,
    /// The baseline rule's source text.
    pub before: String,
    /// The edited rule's source text; `None` for a deleted rule.
    pub after: Option<String>,
}

impl ResolvedMutation {
    /// The kink-corpus loader overlay the edited load read, by logical name: a `.k` file's
    /// edited view, or a `.md` file's Markdown envelope of its edited view (one fence around
    /// the view, which extracts to the view again; [`markdown_envelope`]). It exists so that a
    /// test can repeat the edited load; nothing shows it to a user, and the mutant is never
    /// built from it (the mutant is the patched baseline).
    pub fn overlay(&self) -> &BTreeMap<String, String> {
        &self.overlay
    }

    /// The candidate generation that runs this mutation: one candidate, this patch, with a
    /// site at the body of every addressed rule (a supplied, hence non-exhaustive and never
    /// scored, discovery; kink-patch `Discovery::supplied`). `baseline` must be the baseline
    /// of the validator that runs the campaign (`CandidateGeneration::derived_from`).
    pub fn generation<'b>(
        &self,
        baseline: &'b Baseline,
    ) -> Result<CandidateGeneration<'b>, InvalidMutation> {
        let rejected = |detail: String| InvalidMutation {
            edit: None,
            reason: InvalidReason::PatchRejected,
            detail,
        };
        let sites = self
            .patch
            .written_sentences()
            .into_iter()
            .enumerate()
            .map(|(index, at)| Site {
                role: format!("rule-{}", index + 1),
                at: TermRef::new(at, [0]),
            })
            .collect();
        let discovery = Discovery::supplied(
            baseline,
            vec![DiscoveryTuple {
                sites,
                bindings: Bindings::default(),
            }],
            true,
            false,
        )
        .map_err(|e| rejected(e.to_string()))?;
        let generation = select(&discovery, SelectionPolicy::TupleEach, 1)
            .map_err(|e| rejected(e.to_string()))?
            .fold(MUTATION_OPERATOR, |_| self.patch.clone())
            .map_err(|e| rejected(e.to_string()))?;
        match generation.dispositions() {
            [CandidateDisposition::Mutant(0)] => Ok(generation),
            [CandidateDisposition::Rejected(failure)] => Err(rejected(failure.to_string())),
            other => Err(rejected(format!("unexpected dispositions {other:?}"))),
        }
    }
}

/// One text edit addressed to one rule.
struct TextEdit {
    edit: usize,
    at: SentenceRef,
    file: String,
    range: Range<usize>,
    /// `None` deletes the rule.
    replacement: Option<String>,
}

/// An authored sentence with its source file.
struct Authored<'a> {
    at: SentenceRef,
    sentence: &'a Sentence,
    file: Option<&'a str>,
    location: Option<Location>,
}

impl Authored<'_> {
    fn is_rule(&self) -> bool {
        matches!(self.sentence, Sentence::Rule { .. })
    }

    fn label(&self) -> Option<&str> {
        self.sentence.attributes().string(AttributeKey::Label)
    }

    fn covers(&self, line: u32) -> bool {
        self.location
            .is_some_and(|l| l.start_line <= line && line <= l.end_line)
    }

    fn describe(&self) -> String {
        let place = match (self.file, self.location) {
            (Some(file), Some(l)) => format!("{file}:{}", l.start_line),
            _ => format!("{}#{}", self.at.module, self.at.index),
        };
        match self.label() {
            Some(label) => format!("{label} ({place})"),
            None => place,
        }
    }
}

/// The K view of one source file: the text k-rust parsed for it (flow README 6.1).
///
/// For a `.k` file (any name not ending in `.md`, as k-rust's loader decides) it is the
/// file's text. For a `.md` file it is `k_rust::outer::extract_fenced_k_code_with_map(raw,
/// md_selector).text`, the extraction the loader parses: every whitespace character of the
/// file and every character of a selected fence's content, so lines are the file's lines and
/// columns on code lines are the file's columns. The constructor ([`View::read`]) is the only
/// code of kink-flow that reads a Markdown file's text; the raw text is dropped once the view
/// is built.
pub struct View {
    /// The K text.
    pub text: String,
    /// Whether the file is Markdown (its view is an extraction).
    pub markdown: bool,
    /// The source-table ids of the baseline's extractions equal to this view (the same logical
    /// name, raw content hash and offset map); never empty.
    pub source_ids: BTreeSet<SourceId>,
}

impl View {
    /// The K view of the source file `name` of `loaded`, read from `directory` (the manifest's
    /// directory) and checked twice: its bytes against the digest the load recorded
    /// (`source-changed`), and its view against the baseline's source table: the table must
    /// hold an extraction of this file (its logical name and raw content hash) whose offset
    /// map equals the recomputed one (`.k`: none), else `source-view-mismatch`.
    pub fn read(
        directory: &Path,
        loaded: &LoadedSource,
        md_selector: &str,
        name: &str,
    ) -> Result<Self, (InvalidReason, String)> {
        let changed = |detail: String| (InvalidReason::SourceChanged, detail);
        let mismatch = |detail: String| (InvalidReason::SourceViewMismatch, detail);
        let file = loaded
            .files
            .iter()
            .find(|f| f.name == name)
            .ok_or_else(|| changed(format!("{name} is not a source of the specification")))?;
        let bytes = fs::read(directory.join(name))
            .map_err(|e| changed(format!("cannot read {name}: {e}")))?;
        if sha256(&bytes) != file.sha256 {
            return Err(changed(format!(
                "{name} changed since the specification was loaded"
            )));
        }
        let identity = LogicalSourceId::new(name, &bytes);
        let raw =
            String::from_utf8(bytes).map_err(|e| changed(format!("{name} is not UTF-8: {e}")))?;
        let markdown = name.ends_with(".md");
        let (text, offset_map) = if markdown {
            let extracted = extract_fenced_k_code_with_map(&raw, md_selector).map_err(|e| {
                mismatch(format!(
                    "{name} does not extract under md_selector {md_selector:?}: {e}"
                ))
            })?;
            (extracted.text, Some(extracted.offset_map))
        } else {
            (raw, None)
        };
        let table = loaded.baseline.loaded().source_table();
        let source_ids = table
            .iter()
            .enumerate()
            .map(|(index, source)| (SourceId(index), source))
            .filter(|(id, source)| {
                **source == identity && table.offset_map(*id) == offset_map.as_ref()
            })
            .map(|(id, _)| id)
            .collect::<BTreeSet<_>>();
        if source_ids.is_empty() {
            return Err(mismatch(if markdown {
                format!(
                    "the baseline's source table holds no extraction of {name} equal to its K view \
                     under md_selector {md_selector:?}: k-rust parsed other text"
                )
            } else {
                format!("the baseline's source table holds no unextracted entry for {name}")
            }));
        }
        Ok(Self {
            text,
            markdown,
            source_ids,
        })
    }
}

/// The K views of the specification's source files, built on first use.
struct Views<'a> {
    directory: PathBuf,
    md_selector: String,
    loaded: &'a LoadedSource,
    views: BTreeMap<String, View>,
}

impl Views<'_> {
    fn names(&self) -> impl Iterator<Item = &str> {
        self.loaded.files.iter().map(|f| f.name.as_str())
    }

    fn view(&mut self, name: &str) -> Result<&View, (InvalidReason, String)> {
        if !self.views.contains_key(name) {
            let view = View::read(&self.directory, self.loaded, &self.md_selector, name)?;
            self.views.insert(name.to_owned(), view);
        }
        Ok(&self.views[name])
    }
}

/// A file name normalised lexically as the resolver names sources (`a/./b/../c.k` is
/// `a/c.k`); `None` for a path that leaves the manifest's directory.
fn normalize(name: &str) -> Option<String> {
    let mut parts = Vec::new();
    for component in Path::new(name).components() {
        match component {
            Component::Normal(part) => parts.push(part.to_str()?),
            Component::CurDir => {}
            Component::ParentDir => {
                parts.pop()?;
            }
            _ => return None,
        }
    }
    Some(parts.join("/"))
}

/// The byte offset of a 1-based (line, column) position, columns counting characters.
fn offset_at(text: &str, line: u32, column: u32) -> Option<usize> {
    let mut start = 0;
    for _ in 1..line {
        start += text[start..].find('\n')? + 1;
    }
    let rest = &text[start..];
    let line_text = &rest[..rest.find('\n').unwrap_or(rest.len())];
    let column = usize::try_from(column.checked_sub(1)?).ok()?;
    match line_text.char_indices().nth(column) {
        Some((offset, _)) => Some(start + offset),
        None => (line_text.chars().count() == column).then_some(start + line_text.len()),
    }
}

/// The byte range a location names in `text` (the end column is exclusive).
pub fn location_span(location: Location, text: &str) -> Option<Range<usize>> {
    Some(
        offset_at(text, location.start_line, location.start_column)?
            ..offset_at(text, location.end_line, location.end_column)?,
    )
}

/// A sentence's offset attributes (`SentenceStartOffset`, `SentenceEndOffset`): byte offsets
/// into the text k-rust parsed for its source (the K view).
fn offsets(sentence: &Sentence) -> Option<Range<usize>> {
    let attributes = sentence.attributes();
    let offset = |key| {
        attributes
            .value(key)
            .and_then(serde_json::Value::as_u64)
            .and_then(|v| usize::try_from(v).ok())
    };
    Some(offset(AttributeKey::SentenceStartOffset)?..offset(AttributeKey::SentenceEndOffset)?)
}

/// A sentence's source span in `text`, which must be the K view of its source (the text
/// k-rust parsed; never raw Markdown): its offset attributes, else its location. `None` when
/// neither gives a non-empty range of `text` on character boundaries.
pub fn sentence_span(sentence: &Sentence, text: &str) -> Option<Range<usize>> {
    let range = match offsets(sentence) {
        Some(range) => range,
        None => location_span(sentence.attributes().location()?, text)?,
    };
    (range.start < range.end && text.get(range.clone()).is_some()).then_some(range)
}

/// The span of an addressed sentence in `view`, the K view its spans index: its offset
/// attributes, which must name the same bytes of `view` as its location (fail closed: on the
/// view k-rust parsed they agree by construction, so a disagreement means `view` is not that
/// text). `Err` holds the detail of a `no-usable-span` refusal.
fn view_span(sentence: &Sentence, view: &str, name: &str) -> Result<Range<usize>, String> {
    let attributes = sentence.attributes();
    let (Some(range), Some(location)) = (offsets(sentence), attributes.location()) else {
        return Err(format!("{name} has no offsets or no location"));
    };
    if range.start >= range.end || view.get(range.clone()).is_none() {
        return Err(format!("{name} has no usable source span"));
    }
    if location_span(location, view) != Some(range.clone()) {
        return Err(format!(
            "the offsets and the location of {name} name different text"
        ));
    }
    Ok(range)
}

/// The sentence's source id must name one of the view's extractions, so that its offsets
/// index the view (`Err`: the detail of a `source-view-mismatch` refusal).
fn indexes_view(sentence: &Sentence, view: &View, name: &str) -> Result<(), String> {
    match sentence.attributes().source_id() {
        Some(id) if view.source_ids.contains(&id) => Ok(()),
        Some(id) => Err(format!(
            "the spans of {name} index source-table entry {}, not its file's K view",
            id.0
        )),
        None => Err(format!("{name} names no source-table entry")),
    }
}

/// Every start offset of `needle` in `haystack`, overlapping occurrences included.
fn occurrences(haystack: &str, needle: &str) -> Vec<usize> {
    haystack
        .char_indices()
        .map(|(i, _)| i)
        .filter(|&i| haystack[i..].starts_with(needle))
        .collect()
}

/// One authored rule of the specification with its K text, for listings (flow F-13: the rules
/// no mutation targets).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RuleText {
    pub at: SentenceRef,
    /// The rule's source file (a source of the specification), when it has one.
    pub file: Option<String>,
    pub label: Option<String>,
    pub start_line: Option<u32>,
    pub end_line: Option<u32>,
    /// The rule's text in its file's K view, exactly as a mutation's `before` slices it; `None`
    /// when the file's view or the rule's span is not usable.
    pub text: Option<String>,
}

/// Every authored rule of the specification `loaded`, in sentence order, with its K text
/// (sliced from its file's K view by the same checked span resolution uses).
pub fn rule_texts(manifest: &FlowManifest, loaded: &LoadedSource) -> Vec<RuleText> {
    let mut views = Views {
        directory: manifest.directory.clone(),
        md_selector: manifest.spec.md_selector.clone(),
        loaded,
        views: BTreeMap::new(),
    };
    let file_names = loaded
        .files
        .iter()
        .map(|f| f.name.clone())
        .collect::<BTreeSet<_>>();
    loaded
        .baseline
        .authored_sentences()
        .filter(|(_, sentence)| matches!(sentence, Sentence::Rule { .. }))
        .map(|(at, sentence)| {
            let attributes = sentence.attributes();
            let file = attributes
                .source()
                .filter(|source| file_names.contains(*source))
                .map(str::to_owned);
            let location = attributes.location();
            let label = attributes.string(AttributeKey::Label).map(str::to_owned);
            let text = file.as_deref().and_then(|name| {
                let view = views.view(name).ok()?;
                indexes_view(sentence, view, name).ok()?;
                let span = view_span(sentence, &view.text, name).ok()?;
                Some(view.text[span].to_owned())
            });
            RuleText {
                at,
                file,
                label,
                start_line: location.map(|l| l.start_line),
                end_line: location.map(|l| l.end_line),
                text,
            }
        })
        .collect()
}

/// Resolve `mutation` against the specification `loaded` (kink-corpus `load_source` of the
/// manifest's specification): one pinned patch, or the reason there is none. Nothing is
/// compiled.
pub fn resolve(
    manifest: &FlowManifest,
    loaded: &LoadedSource,
    mutation: &Mutation,
) -> Result<ResolvedMutation, InvalidMutation> {
    let baseline = &loaded.baseline;
    let mut views = Views {
        directory: manifest.directory.clone(),
        md_selector: manifest.spec.md_selector.clone(),
        loaded,
        views: BTreeMap::new(),
    };
    let file_names = loaded
        .files
        .iter()
        .map(|f| f.name.as_str())
        .collect::<BTreeSet<_>>();
    let authored = baseline
        .authored_sentences()
        .map(|(at, sentence)| {
            let file = sentence
                .attributes()
                .source()
                .and_then(|source| file_names.get(source).copied());
            Authored {
                at,
                sentence,
                file,
                location: sentence.attributes().location(),
            }
        })
        .collect::<Vec<_>>();
    let from_view = |(reason, detail)| InvalidMutation {
        edit: None,
        reason,
        detail,
    };

    // Step 1: address every edit in the K views.
    let mut text_edits = Vec::new();
    for (index, edit) in mutation.edits.iter().enumerate() {
        text_edits.push(address(index, edit, &authored, &mut views)?);
    }

    // Edits of one rule must not overlap; a deleted rule takes no other edit.
    let mut groups = BTreeMap::<SentenceRef, Vec<&TextEdit>>::new();
    for edit in &text_edits {
        groups.entry(edit.at.clone()).or_default().push(edit);
    }
    for edits in groups.values_mut() {
        edits.sort_by_key(|e| (e.range.start, e.range.end));
        if edits.len() > 1
            && let Some(delete) = edits.iter().find(|e| e.replacement.is_none())
        {
            return Err(InvalidMutation {
                edit: Some(delete.edit),
                reason: InvalidReason::OverlappingEdits,
                detail: "a deleted rule takes no other edit".into(),
            });
        }
        for pair in edits.windows(2) {
            if pair[0].range.end > pair[1].range.start {
                return Err(InvalidMutation {
                    edit: Some(pair[0].edit.max(pair[1].edit)),
                    reason: InvalidReason::OverlappingEdits,
                    detail: format!(
                        "edit[{}] and edit[{}] overlap in the same rule",
                        pair[0].edit.min(pair[1].edit),
                        pair[0].edit.max(pair[1].edit)
                    ),
                });
            }
        }
    }

    // Step 2: apply the text edits to the K views and load the edited views (a `.md` file
    // through its Markdown envelope).
    let whole = || (mutation.edits.len() == 1).then_some(0);
    let mut by_file = BTreeMap::<&str, Vec<&TextEdit>>::new();
    for edit in &text_edits {
        by_file.entry(&edit.file).or_default().push(edit);
    }
    let mut edited_files = BTreeMap::<String, EditedFile>::new();
    let mut overlay = BTreeMap::<String, String>::new();
    for (file, mut edits) in by_file {
        let view = views.view(file).map_err(from_view)?;
        edits.sort_by_key(|e| (e.range.start, e.range.end));
        let mut edited_view = String::with_capacity(view.text.len());
        let mut shifts = Vec::new();
        let mut written = Vec::new();
        let mut cursor = 0;
        for edit in edits {
            // Rule spans are disjoint and the edits of one rule do not overlap (checked above).
            if edit.range.start < cursor {
                return Err(InvalidMutation {
                    edit: Some(edit.edit),
                    reason: InvalidReason::OverlappingEdits,
                    detail: format!("edit[{}] overlaps another edit of {file}", edit.edit),
                });
            }
            edited_view.push_str(&view.text[cursor..edit.range.start]);
            let start = edited_view.len();
            let replacement = edit.replacement.as_deref().unwrap_or("");
            edited_view.push_str(replacement);
            written.push((edit.edit, start..edited_view.len()));
            shifts.push((edit.range.clone(), length_change(&edit.range, replacement)));
            cursor = edit.range.end;
        }
        edited_view.push_str(&view.text[cursor..]);
        let (loaded_text, parsed, shift) = if view.markdown {
            for (edit, range) in &written {
                if let Some((line, text)) = fence_line_touching(&edited_view, range) {
                    return Err(InvalidMutation {
                        edit: Some(*edit),
                        reason: InvalidReason::MarkdownEnvelope,
                        detail: format!(
                            "the edit makes line {line} of the K view of {file} a Markdown fence \
                             line ({text:?}); an edit of a Markdown specification may not write \
                             or touch a fence line"
                        ),
                    });
                }
            }
            let envelope =
                markdown_envelope(&edited_view, &manifest.spec.md_selector).map_err(|detail| {
                    InvalidMutation {
                        edit: whole(),
                        reason: InvalidReason::MarkdownEnvelope,
                        detail: format!("{file}: {detail}"),
                    }
                })?;
            (envelope.text, envelope.extracted, envelope.shift)
        } else {
            (edited_view.clone(), edited_view.clone(), 0)
        };
        overlay.insert(file.to_owned(), loaded_text);
        edited_files.insert(
            file.to_owned(),
            EditedFile {
                shifts,
                edited_view,
                parsed,
                shift,
            },
        );
    }
    let edited = load_source_with_overlay(&corpus_source(manifest), &overlay).map_err(|error| {
        InvalidMutation {
            edit: whole(),
            reason: InvalidReason::EditedLoadFailed,
            detail: error.to_string(),
        }
    })?;

    // Step 2 (continued): the edited load has the baseline's structure, and every sentence of
    // an edited file is where the edits move it.
    let addressed = groups
        .iter()
        .map(|(at, edits)| {
            (
                at.clone(),
                Addressed {
                    edits: edits.iter().map(|e| e.edit).collect(),
                    deleted: edits.iter().any(|e| e.replacement.is_none()),
                },
            )
        })
        .collect::<BTreeMap<_, _>>();
    let edited_rules = compare(
        baseline.definition(),
        edited.baseline.definition(),
        &addressed,
        &authored,
    )?;
    check_span_shifts(
        baseline.definition(),
        edited.baseline.definition(),
        &addressed,
        &edited_files,
        &authored,
        whole(),
    )?;

    // Step 3: one pinned patch.
    let mut edits = Vec::new();
    let mut rules = Vec::new();
    for (at, group) in &addressed {
        let original = baseline
            .sentence(at)
            .expect("an addressed rule is a baseline sentence");
        let site = authored
            .iter()
            .find(|a| a.at == *at)
            .expect("an addressed rule is authored");
        let file = site.file.expect("an addressed rule has a file").to_owned();
        let location = site.location.expect("an addressed rule has a location");
        let no_span = |detail: String| InvalidMutation {
            edit: Some(group.edits[0]),
            reason: InvalidReason::NoUsableSpan,
            detail,
        };
        let view = views.view(&file).map_err(from_view)?;
        let before = view.text
            [view_span(original, &view.text, &site.describe()).map_err(no_span)?]
        .to_owned();
        let after = match edited_rules.get(at) {
            None => {
                edits.push(Edit::DeleteSentence { at: at.clone() });
                None
            }
            Some(edited_sentence) => {
                let replacement = with_baseline_positions(edited_sentence, original);
                if fingerprint_equal(&replacement, original) {
                    return Err(InvalidMutation {
                        edit: Some(group.edits[0]),
                        reason: InvalidReason::NoChange,
                        detail: format!("{} is unchanged up to formatting", site.describe()),
                    });
                }
                edits.push(Edit::ReplaceSentence {
                    at: at.clone(),
                    replacement,
                });
                let edited_file = &edited_files[&file];
                let span = view_span(edited_sentence, &edited_file.parsed, &site.describe())
                    .map_err(|detail| no_span(format!("after the edits, {detail}")))?;
                let span = edited_file.to_view(span).ok_or_else(|| {
                    no_span(format!(
                        "after the edits, the span of {} lies outside the edited K view",
                        site.describe()
                    ))
                })?;
                Some(edited_file.edited_view[span].to_owned())
            }
        };
        rules.push(EditedRule {
            at: at.clone(),
            edits: group.edits.clone(),
            file,
            label: site.label().map(str::to_owned),
            start_line: location.start_line,
            end_line: location.end_line,
            before,
            after,
        });
    }
    let rejected = |detail: String| InvalidMutation {
        edit: None,
        reason: InvalidReason::PatchRejected,
        detail,
    };
    let patch = Patch::new(edits)
        .map_err(|e| rejected(e.to_string()))?
        .pinned(baseline)
        .map_err(|e| rejected(e.to_string()))?;
    let digest = patch.digest().map_err(|e| rejected(e.to_string()))?;
    let edited_views = edited_files
        .into_iter()
        .map(|(name, file)| (name, file.edited_view))
        .collect::<BTreeMap<_, _>>();
    let resolved = ResolvedMutation {
        id: mutation.id.clone(),
        patch,
        digest,
        rules,
        edited_sources: edited_views.clone(),
        edited_views,
        overlay,
    };
    // kink-patch applies the patch (and nothing else) once more when it folds the generation.
    resolved.generation(baseline)?;
    Ok(resolved)
}

/// One edited source file: its edits in the K view and the text the edited load parsed.
struct EditedFile {
    /// Each edit's range in the baseline view and its length change, in view order.
    shifts: Vec<(Range<usize>, isize)>,
    /// The edited K view.
    edited_view: String,
    /// The text the edited load parsed (its offsets index it): the edited view for a `.k`
    /// file, the extraction of the Markdown envelope for a `.md` file.
    parsed: String,
    /// An offset into `parsed` minus the same position's offset into `edited_view`: the
    /// envelope's first-line length difference ([`Envelope::shift`]; always 0 for a
    /// `.k` file).
    shift: isize,
}

impl EditedFile {
    /// Where the edits move a baseline view offset: plus the length changes of the edits
    /// that end at or before it.
    fn moved(&self, offset: usize) -> Option<usize> {
        let change = self
            .shifts
            .iter()
            .filter(|(range, _)| range.end <= offset)
            .map(|(_, change)| change)
            .sum::<isize>();
        offset.checked_add_signed(change)
    }

    /// A range of `parsed` as the same text's range in the edited view.
    fn to_view(&self, parsed: Range<usize>) -> Option<Range<usize>> {
        let range = parsed.start.checked_add_signed(-self.shift)?
            ..parsed.end.checked_add_signed(-self.shift)?;
        self.edited_view.get(range.clone())?;
        Some(range)
    }
}

/// `replacement.len() - range.len()`.
fn length_change(range: &Range<usize>, replacement: &str) -> isize {
    let signed = |n: usize| isize::try_from(n).expect("a source text fits in isize");
    signed(replacement.len()) - signed(range.len())
}

/// The first line of `text` touching the written `range` that is a Markdown fence line
/// (after at most three spaces, three or more backticks or tildes), as (1-based line, text).
fn fence_line_touching(text: &str, range: &Range<usize>) -> Option<(usize, String)> {
    let first = text[..range.start].rfind('\n').map_or(0, |i| i + 1);
    // The start of the last written character (or of the empty range).
    let last = text[range.clone()]
        .char_indices()
        .next_back()
        .map_or(range.start, |(offset, _)| range.start + offset);
    let end = text[last..].find('\n').map_or(text.len(), |i| last + i);
    let line_number = text[..first].matches('\n').count() + 1;
    text[first..end]
        .split('\n')
        .enumerate()
        .find(|(_, line)| is_fence_line(line))
        .map(|(index, line)| (line_number + index, line.to_owned()))
}

fn is_fence_line(line: &str) -> bool {
    let line = line.strip_suffix('\r').unwrap_or(line);
    let indent = line.bytes().take_while(|b| *b == b' ').count();
    indent <= 3 && (line[indent..].starts_with("```") || line[indent..].starts_with("~~~"))
}

/// The length of the backtick run that starts `line` after at most three spaces.
fn leading_backticks(line: &str) -> Option<usize> {
    let indent = line.bytes().take_while(|b| *b == b' ').count();
    (indent <= 3).then(|| line[indent..].bytes().take_while(|b| *b == b'`').count())
}

/// A Markdown envelope of an edited K view (flow README 6.1, design 3).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Envelope {
    /// The envelope: one opening fence line, the view from its first line break on, a line
    /// break if the view does not end with one, and one closing fence line.
    pub text: String,
    /// `extract_fenced_k_code_with_map(text, md_selector).text`: the edited view, up to
    /// whitespace in the first line and a whitespace-only suffix (checked).
    pub extracted: String,
    /// The extraction's first-line length minus the view's: the offset shift between the
    /// edited load's spans and the edited view. The fence line carries the view's first line,
    /// so the shift is 0 when the info string is at most one tag; an info string of several
    /// tags adds the spaces between them (the extractor keeps whitespace). At the pin a
    /// selector that selects no single tag also rejects the builtin fences (tagged `k`), so
    /// such a specification cannot be admitted (it loads, but does not compile: F-10 review 1
    /// m2) and every shift of an admitted specification is 0.
    pub shift: isize,
}

/// The Markdown text that kink-flow loads in place of an edited `.md` file: one fence around
/// the edited K view `view`. The fence is `w` backticks, `w = max(3, 1 + the longest backtick
/// run that starts a line of the view after at most three spaces)`, so no line of the view
/// closes it; its info string is a tag set that `md_selector` selects ([`fence_info`]); the
/// fence line carries the whitespace of the view's first line, which holds no code. The round
/// trip is the proof that the edited load parses the edited view: the extractor applied to the
/// envelope must give the view back, up to whitespace in the first line and a whitespace-only
/// suffix; otherwise `Err` (the mutation is `markdown-envelope`). This is the only code of
/// kink-flow that writes Markdown.
pub fn markdown_envelope(view: &str, md_selector: &str) -> Result<Envelope, String> {
    let newline = view
        .find('\n')
        .ok_or_else(|| "the K view has no line break".to_owned())?;
    let first = &view[..newline];
    if !first.chars().all(char::is_whitespace) {
        return Err("the first line of the K view holds code".into());
    }
    let width = view
        .split('\n')
        .filter_map(leading_backticks)
        .max()
        .map_or(3, |run| (run + 1).max(3));
    let fence = "`".repeat(width);
    let info = fence_info(md_selector)?;
    let body = &view[newline + 1..];
    let mut text = format!("{fence}{info}{first}\n{body}");
    if !view.ends_with('\n') {
        text.push('\n');
    }
    text.push_str(&fence);
    let extracted = extract_fenced_k_code_with_map(&text, md_selector)
        .map_err(|e| format!("the Markdown envelope does not extract: {e}"))?
        .text;
    let round_trip = extracted
        .split_once('\n')
        .and_then(|(extracted_first, rest)| {
            let suffix = rest.strip_prefix(body)?;
            (extracted_first.chars().all(char::is_whitespace)
                && suffix.chars().all(char::is_whitespace))
            .then_some(extracted_first.len())
        });
    let Some(extracted_first) = round_trip else {
        return Err("extracting the Markdown envelope does not give the edited K view back".into());
    };
    let signed = |n: usize| isize::try_from(n).expect("a source text fits in isize");
    Ok(Envelope {
        text,
        extracted,
        shift: signed(extracted_first) - signed(first.len()),
    })
}

/// The tags a Markdown selector names (comments removed, a leading `.` dropped), in order.
fn selector_tags(selector: &str) -> Vec<String> {
    let mut text = String::new();
    let mut rest = selector;
    while let Some(start) = rest.find("/*") {
        text.push_str(&rest[..start]);
        text.push(' ');
        rest = rest[start + 2..]
            .find("*/")
            .map_or("", |end| &rest[start + 2 + end + 2..]);
    }
    text.push_str(rest);
    let mut tags = Vec::<String>::new();
    for token in text.split(|c: char| c.is_whitespace() || matches!(c, '!' | '&' | '|' | '(' | ')'))
    {
        let tag = token.strip_prefix('.').unwrap_or(token);
        if !tag.is_empty() && !tags.iter().any(|t| t == tag) {
            tags.push(tag.to_owned());
        }
    }
    tags
}

/// The most subsets of the selector's tags [`fence_info`] tries.
pub const FENCE_INFO_TRIES: usize = 256;

/// A fence info string that `md_selector` selects: the first subset of the tags the selector
/// names, in size order (the empty set first; within a size, in the selector's order), whose
/// one-line fence the extractor itself selects. At most [`FENCE_INFO_TRIES`] subsets are tried.
pub fn fence_info(md_selector: &str) -> Result<String, String> {
    let tags = selector_tags(md_selector);
    let info = |subset: &[usize]| match subset {
        [] => String::new(),
        [one] => tags[*one].clone(),
        several => format!(
            "{{{}}}",
            several
                .iter()
                .map(|i| tags[*i].as_str())
                .collect::<Vec<_>>()
                .join(" ")
        ),
    };
    let selected = |info: &str| {
        extract_fenced_k_code_with_map(&format!("```{info}\nx\n```\n"), md_selector)
            .is_ok_and(|extracted| extracted.text.contains('x'))
    };
    let mut tried = 0;
    for size in 0..=tags.len() {
        // Every subset of `size` indices, in lexicographic order.
        let mut subset = (0..size).collect::<Vec<_>>();
        loop {
            if tried == FENCE_INFO_TRIES {
                return Err(format!(
                    "no fence info string among the first {FENCE_INFO_TRIES} tag sets of \
                     md_selector {md_selector:?} is selected by it"
                ));
            }
            tried += 1;
            let candidate = info(&subset);
            if selected(&candidate) {
                return Ok(candidate);
            }
            // The next subset: raise the last index that can still rise.
            let Some(position) = (0..size).rev().find(|&p| subset[p] < tags.len() - size + p)
            else {
                break;
            };
            subset[position] += 1;
            for next in position + 1..size {
                subset[next] = subset[next - 1] + 1;
            }
        }
    }
    Err(format!(
        "no set of the tags of md_selector {md_selector:?} makes a fence it selects"
    ))
}

/// In every edited file, each sentence of the edited load must start at its baseline start
/// moved by the edits (plus the length changes of the edits that end at or before it); an
/// unaddressed sentence must also end at its moved end; a replaced rule may end at its moved
/// end or earlier, with only whitespace between. Offsets are compared in the K views (the
/// edited load's through [`EditedFile::to_view`]). With [`compare`]'s fingerprint check, this
/// makes a replaced rule's edited text exactly its baseline text with the edits applied, and
/// keeps every other sentence's text where and what it was (flow README 6.1, design 4).
fn check_span_shifts(
    baseline: &Definition,
    edited: &Definition,
    addressed: &BTreeMap<SentenceRef, Addressed>,
    files: &BTreeMap<String, EditedFile>,
    authored: &[Authored<'_>],
    single_edit: Option<usize>,
) -> Result<(), InvalidMutation> {
    let describe = |at: &SentenceRef| {
        authored
            .iter()
            .find(|a| a.at == *at)
            .map_or_else(|| format!("{}#{}", at.module, at.index), Authored::describe)
    };
    for (module, edited_module) in baseline.modules.iter().zip(&edited.modules) {
        let mut next = edited_module.local_sentences.iter();
        for (index, original) in module.local_sentences.iter().enumerate() {
            let at = SentenceRef::new(module.name.clone(), u32::try_from(index).expect("u32"));
            let group = addressed.get(&at);
            if group.is_some_and(|g| g.deleted) {
                continue;
            }
            let sentence = next.next().expect("compare counted the sentences");
            let source = original.attributes().source();
            let edited_source = sentence.attributes().source();
            let Some((name, file)) = [source, edited_source]
                .into_iter()
                .flatten()
                .find_map(|name| files.get_key_value(name))
            else {
                continue;
            };
            let changed = |detail: String| InvalidMutation {
                edit: group.map_or(single_edit, |g| Some(g.edits[0])),
                reason: InvalidReason::SpanChanged,
                detail,
            };
            if source != edited_source {
                return Err(changed(format!(
                    "{} moved to another source file",
                    describe(&at)
                )));
            }
            let (before, after) = match (offsets(original), offsets(sentence)) {
                (None, None) => continue,
                (Some(before), Some(after)) => (before, after),
                _ => {
                    return Err(changed(format!(
                        "{} has source offsets before or after the edits, not both",
                        describe(&at)
                    )));
                }
            };
            let after = file.to_view(after).ok_or_else(|| {
                changed(format!(
                    "{} lies outside the edited K view of {name}",
                    describe(&at)
                ))
            })?;
            let (start, end) = (file.moved(before.start), file.moved(before.end));
            if start != Some(after.start) {
                return Err(changed(format!(
                    "{} starts at byte {} of the edited K view of {name}, not at byte {} where \
                     the edits move its start: the edits changed text outside it",
                    describe(&at),
                    after.start,
                    start.map_or_else(|| "?".to_owned(), |s| s.to_string())
                )));
            }
            let end_holds = match (group, end) {
                (_, None) => false,
                (Some(_), Some(end)) => {
                    after.end <= end
                        && file
                            .edited_view
                            .get(after.end..end)
                            .is_some_and(|gap| gap.chars().all(char::is_whitespace))
                }
                (None, Some(end)) => after.end == end,
            };
            if !end_holds {
                return Err(changed(format!(
                    "{} ends at byte {} of the edited K view of {name}, not at byte {} where the \
                     edits move its end{}",
                    describe(&at),
                    after.end,
                    end.map_or_else(|| "?".to_owned(), |e| e.to_string()),
                    if group.is_some() {
                        " (or earlier by whitespace only): the edit's text continues past the rule"
                    } else {
                        ""
                    }
                )));
            }
        }
    }
    Ok(())
}

/// The edits addressed to one rule.
struct Addressed {
    edits: Vec<usize>,
    deleted: bool,
}

/// Address one edit to one authored rule and the byte range it rewrites.
fn address(
    index: usize,
    edit: &EditSpec,
    authored: &[Authored<'_>],
    views: &mut Views<'_>,
) -> Result<TextEdit, InvalidMutation> {
    let invalid = |reason, detail: String| InvalidMutation {
        edit: Some(index),
        reason,
        detail,
    };
    let from_views = |(reason, detail)| invalid(reason, detail);

    let file = match &edit.file {
        None => None,
        Some(name) => Some(
            normalize(name)
                .filter(|name| views.names().any(|known| known == name))
                .ok_or_else(|| {
                    invalid(
                        InvalidReason::UnknownFile,
                        format!(
                            "{name:?} is not a source file of the specification (files: {})",
                            views.names().collect::<Vec<_>>().join(", ")
                        ),
                    )
                })?,
        ),
    };

    let by_label = match &edit.rule {
        None => None,
        Some(label) => {
            // A label is stored as `MODULE.x` for `rule [x]:` and as the bare `x` for
            // `[label(x)]`; `x` and `MODULE.x` address both forms in module MODULE. The
            // `MODULE.x` arm matches only a stored bare label (no '.'), so `MODULE.MODULE.x`
            // does not address the rule stored as `MODULE.x` (F-10 review 1 m1).
            let matches = authored
                .iter()
                .filter(|a| {
                    a.label().is_some_and(|l| {
                        l == label
                            || l == format!("{}.{label}", a.at.module)
                            || (!l.contains('.')
                                && label.strip_prefix(&format!("{}.", a.at.module)) == Some(l))
                    })
                })
                .collect::<Vec<_>>();
            match matches.as_slice() {
                [] => {
                    return Err(invalid(
                        InvalidReason::UnknownLabel,
                        format!("no rule is labelled {label:?}"),
                    ));
                }
                [one] if !one.is_rule() => {
                    return Err(invalid(
                        InvalidReason::NonRuleSentence,
                        format!("{} is not a rule", one.describe()),
                    ));
                }
                [one] => Some(*one),
                several => {
                    return Err(invalid(
                        InvalidReason::AmbiguousLabel,
                        format!(
                            "{label:?} names {}; qualify it with the module",
                            several
                                .iter()
                                .map(|a| a.describe())
                                .collect::<Vec<_>>()
                                .join(", ")
                        ),
                    ));
                }
            }
        }
    };
    if let (Some(file), Some(rule)) = (&file, by_label)
        && rule.file != Some(file.as_str())
    {
        return Err(invalid(
            InvalidReason::AddressMismatch,
            format!("{} is not in {file}", rule.describe()),
        ));
    }
    let file = match (file, by_label) {
        (Some(file), _) => file,
        (None, Some(rule)) => rule
            .file
            .ok_or_else(|| {
                invalid(
                    InvalidReason::NoUsableSpan,
                    format!("{} has no source file", rule.describe()),
                )
            })?
            .to_owned(),
        (None, None) => {
            let names = views.names().collect::<Vec<_>>();
            match names.as_slice() {
                [only] => (*only).to_owned(),
                _ => {
                    return Err(invalid(
                        InvalidReason::FileRequired,
                        format!(
                            "the specification reads several files ({}); name one with file",
                            names.join(", ")
                        ),
                    ));
                }
            }
        }
    };
    let in_file = |a: &&Authored<'_>| a.file == Some(file.as_str());

    let by_line = match edit.line {
        None => None,
        Some(line) => {
            let covering = authored
                .iter()
                .filter(in_file)
                .filter(|a| a.covers(line))
                .collect::<Vec<_>>();
            let covering_rules = covering
                .iter()
                .copied()
                .filter(|a| a.is_rule())
                .collect::<Vec<_>>();
            match (covering_rules.as_slice(), covering.as_slice()) {
                ([one], _) => Some(*one),
                ([], []) => {
                    return Err(invalid(
                        InvalidReason::LineOutsideRules,
                        format!("no sentence of {file} covers line {line}"),
                    ));
                }
                ([], others) => {
                    return Err(invalid(
                        InvalidReason::NonRuleSentence,
                        format!(
                            "line {line} of {file} holds {}, not a rule",
                            others
                                .iter()
                                .map(|a| a.describe())
                                .collect::<Vec<_>>()
                                .join(", ")
                        ),
                    ));
                }
                (several, _) => {
                    return Err(invalid(
                        InvalidReason::LineAmbiguous,
                        format!(
                            "line {line} of {file} holds several rules: {}",
                            several
                                .iter()
                                .map(|a| a.describe())
                                .collect::<Vec<_>>()
                                .join(", ")
                        ),
                    ));
                }
            }
        }
    };
    if let (Some(rule), Some(line)) = (by_label, by_line)
        && rule.at != line.at
    {
        return Err(invalid(
            InvalidReason::AddressMismatch,
            format!(
                "rule {:?} is {}, but line {} is in {}",
                edit.rule.as_deref().unwrap_or_default(),
                rule.describe(),
                edit.line.unwrap_or_default(),
                line.describe()
            ),
        ));
    }

    // Everything below is in the file's K view: spans, occurrence counts and the rule prefix.
    let view = views.view(&file).map_err(from_views)?;
    let text = &view.text;
    let span_of = |a: &Authored<'_>| -> Result<Range<usize>, InvalidMutation> {
        let name = a.describe();
        indexes_view(a.sentence, view, &name)
            .map_err(|detail| invalid(InvalidReason::SourceViewMismatch, detail))?;
        let span = view_span(a.sentence, text, &name)
            .map_err(|detail| invalid(InvalidReason::NoUsableSpan, detail))?;
        if !text[span.clone()].starts_with("rule") {
            return Err(invalid(
                InvalidReason::NoUsableSpan,
                format!("the span of {name} does not start with `rule`"),
            ));
        }
        Ok(span)
    };

    let (rule, range) = match (by_label.or(by_line), &edit.action) {
        (Some(rule), EditAction::Delete) => (rule, span_of(rule)?),
        (Some(rule), EditAction::Replace { find, .. }) => {
            let span = span_of(rule)?;
            match occurrences(&text[span.clone()], find).as_slice() {
                [one] => (rule, span.start + one..span.start + one + find.len()),
                [] if text.contains(find.as_str()) => {
                    return Err(invalid(
                        InvalidReason::EditOutsideRule,
                        format!(
                            "{find:?} occurs in {file} but not inside {}",
                            rule.describe()
                        ),
                    ));
                }
                [] => {
                    return Err(invalid(
                        InvalidReason::FindNotFound,
                        format!("{find:?} does not occur in {}", rule.describe()),
                    ));
                }
                several => {
                    return Err(invalid(
                        InvalidReason::FindAmbiguous,
                        format!(
                            "{find:?} occurs {} times in {}",
                            several.len(),
                            rule.describe()
                        ),
                    ));
                }
            }
        }
        (None, EditAction::Delete) => unreachable!("decoding requires rule or line for delete"),
        (None, EditAction::Replace { find, .. }) => {
            let at = match occurrences(text, find).as_slice() {
                [one] => *one,
                [] => {
                    return Err(invalid(
                        InvalidReason::FindNotFound,
                        format!("{find:?} does not occur in {file}"),
                    ));
                }
                several => {
                    return Err(invalid(
                        InvalidReason::FindAmbiguous,
                        format!(
                            "{find:?} occurs {} times in {file}; address the rule with rule or line",
                            several.len()
                        ),
                    ));
                }
            };
            let range = at..at + find.len();
            let containing = authored
                .iter()
                .filter(in_file)
                .filter(|a| {
                    sentence_span(a.sentence, text)
                        .is_some_and(|s| s.start <= range.start && range.end <= s.end)
                })
                .collect::<Vec<_>>();
            let containing_rules = containing
                .iter()
                .copied()
                .filter(|a| a.is_rule())
                .collect::<Vec<_>>();
            match (containing_rules.as_slice(), containing.as_slice()) {
                ([one], _) => {
                    span_of(one)?;
                    (*one, range)
                }
                ([], []) => {
                    return Err(invalid(
                        InvalidReason::EditOutsideRule,
                        format!("the occurrence of {find:?} in {file} is inside no rule"),
                    ));
                }
                ([], others) => {
                    return Err(invalid(
                        InvalidReason::NonRuleSentence,
                        format!(
                            "the occurrence of {find:?} is inside {}, not a rule",
                            others[0].describe()
                        ),
                    ));
                }
                (several, _) => {
                    return Err(invalid(
                        InvalidReason::FindAmbiguous,
                        format!(
                            "the occurrence of {find:?} is inside several rules: {}",
                            several
                                .iter()
                                .map(|a| a.describe())
                                .collect::<Vec<_>>()
                                .join(", ")
                        ),
                    ));
                }
            }
        }
    };
    Ok(TextEdit {
        edit: index,
        at: rule.at.clone(),
        file,
        range,
        replacement: match &edit.action {
            EditAction::Replace { replace, .. } => Some(replace.clone()),
            EditAction::Delete => None,
        },
    })
}

/// `attributes` without the position and provenance keys (kink-patch `POSITION_KEYS`).
fn without_positions(attributes: &Attributes) -> BTreeMap<String, serde_json::Value> {
    let mut entries = attributes.entries();
    for key in POSITION_KEYS {
        entries.remove(key.as_str());
    }
    entries
}

fn fingerprint_equal(left: &Sentence, right: &Sentence) -> bool {
    match (
        SentenceFingerprint::of(left),
        SentenceFingerprint::of(right),
    ) {
        (Ok(left), Ok(right)) => left == right,
        // A context alias has no v1 fingerprint: compare it without positions.
        _ => {
            let strip = |sentence: &Sentence| {
                let mut sentence = sentence.clone();
                for key in POSITION_KEYS {
                    sentence.attributes_mut().remove(key.as_str());
                }
                sentence
            };
            strip(left) == strip(right)
        }
    }
}

/// The edited sentence with the baseline sentence's position and provenance attributes
/// (kink-patch `POSITION_KEYS`: location, source, offsets, origin, input addresses), as a
/// `ReplaceSentence` must keep them; every other attribute and the body are the edited
/// load's.
fn with_baseline_positions(edited: &Sentence, original: &Sentence) -> Sentence {
    let mut replacement = edited.clone();
    let attributes = replacement.attributes_mut();
    for key in POSITION_KEYS {
        attributes.remove(key.as_str());
        if let Some(value) = original.attributes().get(key.as_str()) {
            attributes.insert(key.as_str(), value.clone());
        }
    }
    replacement
}

/// Check that `edited` has `baseline`'s modules and sentences in the same order with equal
/// fingerprints, except at the addressed rules: a deleted rule is gone and a replaced rule is
/// exactly one rule sentence with the baseline's label and identity. Returns the edited
/// sentence of each replaced rule.
fn compare(
    baseline: &Definition,
    edited: &Definition,
    addressed: &BTreeMap<SentenceRef, Addressed>,
    authored: &[Authored<'_>],
) -> Result<BTreeMap<SentenceRef, Arc<Sentence>>, InvalidMutation> {
    let changed = |edit, detail: String| InvalidMutation {
        edit,
        reason: InvalidReason::StructureChanged,
        detail,
    };
    if baseline.main_module != edited.main_module
        || without_positions(&baseline.attributes) != without_positions(&edited.attributes)
        || baseline.modules.len() != edited.modules.len()
    {
        return Err(changed(
            None,
            "the edited definition's modules differ from the baseline's".into(),
        ));
    }
    let describe = |at: &SentenceRef| {
        authored
            .iter()
            .find(|a| a.at == *at)
            .map_or_else(|| format!("{}#{}", at.module, at.index), Authored::describe)
    };
    let mut replaced = BTreeMap::new();
    for (module, edited_module) in baseline.modules.iter().zip(&edited.modules) {
        let in_module = addressed
            .iter()
            .filter(|(at, _)| at.module == module.name)
            .flat_map(|(_, group)| group.edits.iter().copied())
            .collect::<BTreeSet<_>>();
        let module_edit = (in_module.len() == 1).then(|| *in_module.first().expect("one"));
        if module.name != edited_module.name
            || module.imports != edited_module.imports
            || without_positions(&module.attributes) != without_positions(&edited_module.attributes)
        {
            return Err(changed(
                module_edit,
                format!("module {} changed outside its rules", module.name),
            ));
        }
        let deleted = addressed
            .iter()
            .filter(|(at, group)| at.module == module.name && group.deleted)
            .count();
        let expected = module.local_sentences.len() - deleted;
        if edited_module.local_sentences.len() != expected {
            return Err(changed(
                module_edit,
                format!(
                    "module {} has {} sentences after the edits, not {expected}: an edit split, \
                     merged, added or removed a sentence",
                    module.name,
                    edited_module.local_sentences.len()
                ),
            ));
        }
        let mut next = edited_module.local_sentences.iter();
        for (index, original) in module.local_sentences.iter().enumerate() {
            let at = SentenceRef::new(module.name.clone(), u32::try_from(index).expect("u32"));
            match addressed.get(&at) {
                Some(group) if group.deleted => {}
                Some(group) => {
                    let sentence = next.next().expect("counted");
                    let edit = Some(group.edits[0]);
                    if !matches!(**sentence, Sentence::Rule { .. }) {
                        return Err(changed(
                            edit,
                            format!("{} is no longer a rule after the edit", describe(&at)),
                        ));
                    }
                    for key in [AttributeKey::Label, AttributeKey::UniqueId] {
                        if sentence.attributes().value(key) != original.attributes().value(key) {
                            return Err(InvalidMutation {
                                edit,
                                reason: if key == AttributeKey::Label {
                                    InvalidReason::LabelChanged
                                } else {
                                    InvalidReason::StructureChanged
                                },
                                detail: format!(
                                    "the edit changes the {} of {} to {}",
                                    key.as_str(),
                                    describe(&at),
                                    sentence
                                        .attributes()
                                        .value(key)
                                        .map_or_else(|| "none".to_owned(), ToString::to_string)
                                ),
                            });
                        }
                    }
                    replaced.insert(at, sentence.clone());
                }
                None => {
                    let sentence = next.next().expect("counted");
                    if !(**sentence == **original || fingerprint_equal(sentence, original)) {
                        return Err(changed(
                            module_edit,
                            format!("{} changed although no edit addresses it", describe(&at)),
                        ));
                    }
                }
            }
        }
    }
    Ok(replaced)
}
