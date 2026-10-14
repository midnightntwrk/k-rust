//! The mutation list an LLM writes (`MUTATIONS.toml`, flow README section 5.5) and its
//! resolution into one pinned [`Patch`] per mutation.
//!
//! A mutation is one or more text edits, each addressed to one authored rule of the
//! specification: by its label, by a line inside it, or by the unique occurrence of its
//! `find` text in the file. Resolution is all or nothing:
//!
//! 1. every edit is addressed to exactly one rule sentence of the baseline, whose source span
//!    comes from its offset attributes (`SentenceStartOffset`/`SentenceEndOffset`), or from
//!    its location when the offsets are absent;
//! 2. the edits are applied to in-memory copies of the source files and the edited sources are
//!    loaded with the specification's own load options (kink-corpus
//!    [`load_source_with_overlay`]); the edited load must have the baseline's modules and
//!    sentences in the same order with equal fingerprints, except that each replaced rule is
//!    exactly one rule sentence with the same label and each deleted rule is gone;
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
use k_rust::definition::{AttributeKey, Attributes, Definition, Location, Sentence};
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
    /// The edited sources do not load.
    EditedLoadFailed,
    /// The edited load does not have the baseline's sentences outside the addressed rules,
    /// or an edited rule is no longer exactly one rule sentence.
    StructureChanged,
    /// The edit changes the rule's label.
    LabelChanged,
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
            Self::EditedLoadFailed => "edited-load-failed",
            Self::StructureChanged => "structure-changed",
            Self::LabelChanged => "label-changed",
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
    /// The edited text of every edited source file, by its logical name.
    pub edited_sources: BTreeMap<String, String>,
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

/// The specification's source texts, read from the manifest's directory and checked
/// against the digests the load recorded.
struct Sources<'a> {
    directory: PathBuf,
    loaded: &'a LoadedSource,
    texts: BTreeMap<String, String>,
}

impl Sources<'_> {
    fn names(&self) -> impl Iterator<Item = &str> {
        self.loaded.files.iter().map(|f| f.name.as_str())
    }

    fn text(&mut self, name: &str) -> Result<&str, (InvalidReason, String)> {
        if !self.texts.contains_key(name) {
            let changed = |detail: String| (InvalidReason::SourceChanged, detail);
            let file = self
                .loaded
                .files
                .iter()
                .find(|f| f.name == name)
                .ok_or_else(|| changed(format!("{name} is not a source of the specification")))?;
            let bytes = fs::read(self.directory.join(name))
                .map_err(|e| changed(format!("cannot read {name}: {e}")))?;
            if sha256(&bytes) != file.sha256 {
                return Err(changed(format!(
                    "{name} changed since the specification was loaded"
                )));
            }
            let text = String::from_utf8(bytes)
                .map_err(|e| changed(format!("{name} is not UTF-8: {e}")))?;
            self.texts.insert(name.to_owned(), text);
        }
        Ok(&self.texts[name])
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

/// A sentence's source span in `text`: its offset attributes, else its location. `None`
/// when neither gives a non-empty range of `text` on character boundaries.
pub fn sentence_span(sentence: &Sentence, text: &str) -> Option<Range<usize>> {
    let attributes = sentence.attributes();
    let offset = |key| {
        attributes
            .value(key)
            .and_then(serde_json::Value::as_u64)
            .and_then(|v| usize::try_from(v).ok())
    };
    let range = match (
        offset(AttributeKey::SentenceStartOffset),
        offset(AttributeKey::SentenceEndOffset),
    ) {
        (Some(start), Some(end)) => start..end,
        _ => location_span(attributes.location()?, text)?,
    };
    (range.start < range.end && text.get(range.clone()).is_some()).then_some(range)
}

/// Every start offset of `needle` in `haystack`, overlapping occurrences included.
fn occurrences(haystack: &str, needle: &str) -> Vec<usize> {
    haystack
        .char_indices()
        .map(|(i, _)| i)
        .filter(|&i| haystack[i..].starts_with(needle))
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
    let mut sources = Sources {
        directory: manifest.directory.clone(),
        loaded,
        texts: BTreeMap::new(),
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

    // Step 1: address every edit.
    let mut text_edits = Vec::new();
    for (index, edit) in mutation.edits.iter().enumerate() {
        text_edits.push(address(index, edit, &authored, &mut sources)?);
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

    // Step 2: apply the text edits in memory and load the edited sources.
    let mut edited_sources = BTreeMap::<String, String>::new();
    let mut by_file = BTreeMap::<&str, Vec<&TextEdit>>::new();
    for edit in &text_edits {
        by_file.entry(&edit.file).or_default().push(edit);
    }
    for (file, mut edits) in by_file {
        let mut text = sources
            .text(file)
            .map_err(|(reason, detail)| InvalidMutation {
                edit: None,
                reason,
                detail,
            })?
            .to_owned();
        edits.sort_by_key(|e| std::cmp::Reverse(e.range.start));
        for edit in edits {
            text.replace_range(
                edit.range.clone(),
                edit.replacement.as_deref().unwrap_or(""),
            );
        }
        edited_sources.insert(file.to_owned(), text);
    }
    let whole = || (mutation.edits.len() == 1).then_some(0);
    let edited =
        load_source_with_overlay(&corpus_source(manifest), &edited_sources).map_err(|error| {
            InvalidMutation {
                edit: whole(),
                reason: InvalidReason::EditedLoadFailed,
                detail: error.to_string(),
            }
        })?;

    // Step 2 (continued): the edited load has the baseline's structure.
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
        let text = sources
            .text(&file)
            .map_err(|(reason, detail)| InvalidMutation {
                edit: None,
                reason,
                detail,
            })?;
        let before = text[sentence_span(original, text).expect("addressed by its span")].to_owned();
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
                let edited_text = &edited_sources[&file];
                Some(
                    sentence_span(edited_sentence, edited_text)
                        .map(|span| edited_text[span].to_owned())
                        .unwrap_or_default(),
                )
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
    let resolved = ResolvedMutation {
        id: mutation.id.clone(),
        patch,
        digest,
        rules,
        edited_sources,
    };
    // kink-patch applies the patch (and nothing else) once more when it folds the generation.
    resolved.generation(baseline)?;
    Ok(resolved)
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
    sources: &mut Sources<'_>,
) -> Result<TextEdit, InvalidMutation> {
    let invalid = |reason, detail: String| InvalidMutation {
        edit: Some(index),
        reason,
        detail,
    };
    let from_sources = |(reason, detail)| invalid(reason, detail);

    let file = match &edit.file {
        None => None,
        Some(name) => Some(
            normalize(name)
                .filter(|name| sources.names().any(|known| known == name))
                .ok_or_else(|| {
                    invalid(
                        InvalidReason::UnknownFile,
                        format!(
                            "{name:?} is not a source file of the specification (files: {})",
                            sources.names().collect::<Vec<_>>().join(", ")
                        ),
                    )
                })?,
        ),
    };

    let by_label = match &edit.rule {
        None => None,
        Some(label) => {
            let matches = authored
                .iter()
                .filter(|a| {
                    a.label()
                        .is_some_and(|l| l == label || l == format!("{}.{label}", a.at.module))
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
            let names = sources.names().collect::<Vec<_>>();
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

    let text = sources.text(&file).map_err(from_sources)?.to_owned();
    let span_of = |a: &Authored<'_>| -> Result<Range<usize>, InvalidMutation> {
        sentence_span(a.sentence, &text)
            .filter(|span| text[span.clone()].starts_with("rule"))
            .ok_or_else(|| {
                invalid(
                    InvalidReason::NoUsableSpan,
                    format!("{} has no usable source span", a.describe()),
                )
            })
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
            let at = match occurrences(&text, find).as_slice() {
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
                    sentence_span(a.sentence, &text)
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
