//! The mutation list an LLM writes (one `MUTATIONS.toml`, or a directory of `<topic>.toml` files;
//! kink-flow README, "`MUTATIONS.toml`") and its resolution into one pinned [`Patch`] per mutation.
//!
//! A mutation is one or more text edits, each addressed to one authored rule of the
//! specification: by its label (the whole label, or a unique suffix of its components), by a line
//! inside it, or by the unique occurrence of its `find` text in the file. Every text an edit addresses, searches or shows is in the file's
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
//!
//! # Grammar edits
//!
//! An edit may instead edit a grammar declaration (PJ-34): a `syntax` declaration of productions,
//! `syntax priority`, `syntax left|right|non-assoc` or `syntax lexical`, addressed by
//! `production = NAME` (a production's label: the `symbol` or `klabel` it declares, else the label
//! K derives from its text; for KRS the symbol it derives from the production's item), by a line
//! in it or by a `find` in it and in no rule. A declaration lowers to several sentences (one per
//! production, a priority sentence for `>`, an associativity sentence per `left:` group and per
//! `[left]`), and the parser reads priority and associativity only from those sentences, so the
//! edit is of the whole declaration: `find` occurs once in it, and `delete = true` deletes it (one
//! of several productions is refused). A mutation may edit rules beside grammar declarations
//! (PJ-35).
//!
//! A grammar mutant changes which program text parses to which term and keeps the terms of the
//! rules it does not edit (the patched baseline's unedited rules are the baseline's), so a grammar
//! edit is not read by an edited load, which would parse every rule again under the edited
//! grammar (a literal a rule uses would make it fail): every source file's K view, the edited
//! views in place of the edited files, is read by k-rust's outer parser and lowered as one source
//! set ([`k_rust::outer::lower`], which never parses a rule's body). Then, failing closed:
//!
//! 1. each edited file has the baseline's modules (names, attributes, imports, requires) and its
//!    declarations less the deleted ones, of the same kinds, each unedited one where the edits move
//!    it and each edited one starting where they move it and ending there or earlier by
//!    whitespace (`structure-changed`, `span-changed`);
//! 2. every declaration no edit edits lowers to the sentences it lowered to before, up to
//!    positions (a tag of a priority declaration elsewhere could resolve otherwise:
//!    `structure-changed`), and the loaded specification's sentences of each edited declaration
//!    are its outer lowering (`unread-declaration`: a sort synonym, which the load resolves after
//!    lowering, is one such case);
//! 3. the sentences of each edited declaration before and after are paired by kind (productions
//!    by label, the others by equality, then in order): a pair that differs is a
//!    `ReplaceSentence` with the baseline's position keys, an unpaired baseline sentence a
//!    `DeleteSentence`, an unpaired edited one an `InsertSentence` at its module's end (order
//!    within a module means nothing to the grammar). A production that declares no `symbol` or
//!    `klabel` keeps the baseline's label, and its declaration's priority and associativity tags
//!    name it so: the label K derives from the literals names the constructor the rules' terms
//!    use, and the edit changes its text, not the constructor (refused when another production
//!    already has the derived label); a declared label that changes is `label-changed`;
//! 4. the pinned patch applies (`edited-load-failed` for a definition that does not resolve) and
//!    its mutant gives a program parser for the syntax module (kink-patch
//!    `Mutant::program_parser`; `no-program-parser`);
//! 5. a rule edited beside the grammar edits is the declaration its bubble is in steps 1 and 2,
//!    and its text after the edits is parsed under the mutant's grammar (the baseline patched by
//!    step 4's patch), at its module, by k-rust's `parse_rule_content`, the parse the load makes
//!    of every rule bubble with its module's rule grammar (checked: its text before the edits,
//!    parsed so under the specification's grammar, is the loaded rule, else
//!    `unread-declaration`): a rule that does not parse there is `edited-load-failed`, one no
//!    longer one rule `structure-changed`, a changed label `label-changed`. Its replacement (or
//!    deletion) joins the patch, which is admitted again as in step 4.
//!
//! The rows show the declaration before and after ([`EditedKind::Grammar`]), and each edited
//! rule as a rule mutation's rows do. `run`'s first-kill search judges a grammar mutation after it
//! parses each case again under the mutant's grammar (`crate::reparse`,
//! [`ResolvedMutation::grammar_generation`]); every other command and mode refuses one
//! ([`ResolvedMutation::run_refusal`]).

use crate::{
    admit::corpus_source,
    manifest::{FlowManifest, ManifestError},
};
use k_rust::{
    definition::{AttributeKey, Attributes, Definition, Location, ResolvedDefinition, Sentence},
    inner::parse_rule_content,
    outer::{self, extract_fenced_k_code_with_map},
    provenance::{LogicalSourceId, SourceId},
};
use kink_corpus::{LoadedSource, resolver::load_source_with_overlay};
use kink_patch::{
    Baseline, Bindings, CandidateDisposition, CandidateGeneration, CodecError, Discovery,
    DiscoveryTuple, Edit, GrammarForm, InsertPosition, POSITION_KEYS, Patch, PatchFailureKind,
    SelectionPolicy, SentenceFingerprint, SentenceRef, Sha256Digest, Site, StackRefusal, TermRef,
    select, sha256,
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

/// A decoded mutation list: one `MUTATIONS.toml`, or every `<topic>.toml` of a mutations
/// directory ([`MutationList::read`]).
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct MutationList {
    pub mutations: Vec<Mutation>,
    /// The generated grammar sets the list names (`[[mutation]]` with `grammar`), in list order:
    /// each expands, once the specification is admitted, into one mutation per generated grammar
    /// patch ([`crate::grammar_set`]), which `run` judges and `check` shows after the written
    /// mutations. They are not among [`Self::mutations`], which holds the mutations written as
    /// edits: every reader of those is unchanged.
    pub grammar_sets: Vec<GrammarSet>,
}

/// One `[[mutation]]` that names a generated set of grammar mutations (`grammar = "default"` or
/// `grammar = { forms = [...] }`) instead of writing edits ([`crate::grammar_set`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GrammarSet {
    /// The id as written (qualified by the file's stem in a mutations directory): the prefix of
    /// every generated row's id, `<id>/<form>/<module>/<site>/<variant>`.
    pub id: String,
    /// The forms it generates, as written.
    pub set: GrammarSetName,
    /// The entry's `misunderstanding` (or `note`), when it gives one: it prefixes every row's
    /// note, which states the form's misunderstanding at its site.
    pub misunderstanding: Option<String>,
}

/// The grammar forms a [`GrammarSet`] names (PJ-35).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum GrammarSetName {
    /// `grammar = "default"`: kink-patch `GrammarForm::DEFAULT` (widening and token-level
    /// narrowing).
    Default,
    /// `grammar = { forms = [...] }`: the forms named, distinct and not empty, in
    /// `GrammarForm::ALL` order whatever order the list writes them in.
    Forms(Vec<GrammarForm>),
}

impl GrammarSetName {
    /// The forms the set generates, in `GrammarForm::ALL` order.
    #[must_use]
    pub fn forms(&self) -> Vec<GrammarForm> {
        match self {
            Self::Default => GrammarForm::DEFAULT.to_vec(),
            Self::Forms(forms) => forms.clone(),
        }
    }

    /// The value as the list writes it: `"default"`, or `{"forms": [...]}`.
    #[must_use]
    pub fn value(&self) -> serde_json::Value {
        match self {
            Self::Default => serde_json::Value::from("default"),
            Self::Forms(forms) => serde_json::json!({
                "forms": forms.iter().map(|form| form.name()).collect::<Vec<_>>(),
            }),
        }
    }
}

/// One `[[mutation]]`: its edits are applied together or not at all.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Mutation {
    /// The id as written in a single list; in a mutations directory, qualified by the file's
    /// stem (`add-carry/ge` for the mutation `ge` of `add-carry.toml`).
    pub id: String,
    /// The plausible misunderstanding of the specification the mutation writes, in prose (key
    /// `misunderstanding`, or its alias `note`): required, since a mutation is meant to be a
    /// mistake an author could make, and a reviewer judges it and a survivor's next program by
    /// what it says. It enters no digest and no key.
    pub misunderstanding: String,
    /// The verdict the author claims the corpus gives the mutation (key `expect`), when the list
    /// states one: [`Expect::Survive`] for a control, a mutation no program of the corpus should
    /// distinguish from the specification, [`Expect::Kill`] for a mistake the corpus must catch;
    /// either for the row's own status ([`Expected::Row`]) or per projection
    /// ([`Expected::Projections`]). `run` checks it against the row's status or its projections'
    /// ([`crate::report::mutation_expectation`]); it changes no verdict and enters no digest, key,
    /// memo or lock.
    pub expect: Option<Expected>,
    pub edits: Vec<EditSpec>,
}

/// What a mutation's `expect` claims ([`Mutation::expect`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Expected {
    /// `expect = "survive"` or `"kill"`: the row's own status, which is the status under the
    /// implicit `default` projection of a flow that declares no projection, and the status of the
    /// run's own search (over the union of the projections' observations) in a flow that declares
    /// some.
    Row(Expect),
    /// `expect = { NAME = "survive" | "kill", ... }`: the status under each named projection of
    /// the flow (projections PJ-11), in the table's key order; never a snapshot projection
    /// ([`MutationList::check_projections`]).
    Projections(Vec<(String, Expect)>),
}

impl Expected {
    /// The value as the run document's row writes it: the string, or `{NAME: verdict}`.
    #[must_use]
    pub fn value(&self) -> serde_json::Value {
        match self {
            Self::Row(expect) => serde_json::Value::from(expect.as_str()),
            Self::Projections(named) => serde_json::Value::Object(
                named
                    .iter()
                    .map(|(name, expect)| (name.clone(), expect.as_str().into()))
                    .collect(),
            ),
        }
    }

    /// The projections the claim names (none for [`Expected::Row`]).
    pub fn projection_names(&self) -> impl Iterator<Item = &str> {
        let named = match self {
            Self::Row(_) => &[][..],
            Self::Projections(named) => named.as_slice(),
        };
        named.iter().map(|(name, _)| name.as_str())
    }
}

/// The verdict a mutation states it expects ([`Mutation::expect`]).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Expect {
    /// `expect = "survive"`: no program of the corpus distinguishes the mutant from the
    /// specification.
    Survive,
    /// `expect = "kill"`: some program of the corpus distinguishes it.
    Kill,
}

impl Expect {
    /// The value as the list and the run document write it.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Survive => "survive",
            Self::Kill => "kill",
        }
    }

    /// The value the list writes as `text`, if it is one.
    #[must_use]
    pub fn parse(text: &str) -> Option<Self> {
        match text {
            "survive" => Some(Self::Survive),
            "kill" => Some(Self::Kill),
            _ => None,
        }
    }
}

/// One `[[mutation.edit]]`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EditSpec {
    /// The source file, relative to the manifest's directory; optional when the
    /// specification reads one file or when `rule` names the rule.
    pub file: Option<String>,
    /// A rule label: the stored label or its module-qualified form (`CALC.add`, or the bare
    /// `add`), or a suffix of its components (`plus_zero` for `nat--plus_zero`); it must name
    /// exactly one label in either way ([`label_match`]).
    pub rule: Option<String>,
    /// A production's name: its label, the `symbol` (or `klabel`) it declares, else the label K
    /// derives from its text; matched as `rule` matches a label ([`label_match`]). It addresses
    /// the grammar declaration that declares the production (PJ-34). `rule` and `production`
    /// exclude each other.
    pub production: Option<String>,
    /// A line (1-based) inside the rule, or inside the grammar declaration.
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
    /// Read and decode the mutation list at `path`: a file is one list whose ids are as written;
    /// a directory is a mutations directory ([`Self::read_directory`]).
    pub fn read(path: &Path) -> Result<Self, ManifestError> {
        if path.is_dir() {
            return Self::read_directory(path);
        }
        let text = fs::read_to_string(path)
            .map_err(|e| ManifestError::new("", format!("cannot read the mutation list: {e}")))?;
        Self::decode(&text)
    }

    /// Read a mutations directory: every regular file directly in it whose name ends in `.toml`
    /// and does not start with `.`, in byte order of the file names, each holding one or more
    /// `[[mutation]]`. A mutation's id is qualified by its file's stem (`add-carry/ge` for `ge` in
    /// `add-carry.toml`): a stem holds no `/`, so two files never give one id. Other entries
    /// (subdirectories, notes, editor files) are not read. An error names the file.
    pub fn read_directory(directory: &Path) -> Result<Self, ManifestError> {
        let unreadable = |e: std::io::Error| {
            ManifestError::new(
                "",
                format!(
                    "cannot read the mutations directory {}: {e}",
                    directory.display()
                ),
            )
        };
        let mut files = Vec::new();
        for entry in fs::read_dir(directory).map_err(unreadable)? {
            let entry = entry.map_err(unreadable)?;
            let Ok(name) = entry.file_name().into_string() else {
                continue;
            };
            let Some(stem) = name.strip_suffix(".toml") else {
                continue;
            };
            if stem.is_empty() || name.starts_with('.') || !entry.path().is_file() {
                continue;
            }
            files.push((name.clone(), stem.to_owned()));
        }
        files.sort();
        let mut mutations = Vec::new();
        let mut grammar_sets = Vec::new();
        for (name, stem) in files {
            let in_file = |error: ManifestError| {
                ManifestError::new(
                    if error.key.is_empty() {
                        name.clone()
                    } else {
                        format!("{name}: {}", error.key)
                    },
                    error.message,
                )
            };
            let text = fs::read_to_string(directory.join(&name))
                .map_err(|e| in_file(ManifestError::new("", format!("cannot read it: {e}"))))?;
            let list = Self::decode(&text).map_err(in_file)?;
            mutations.extend(list.mutations.into_iter().map(|mut mutation| {
                mutation.id = format!("{stem}/{}", mutation.id);
                mutation
            }));
            grammar_sets.extend(list.grammar_sets.into_iter().map(|mut set| {
                set.id = format!("{stem}/{}", set.id);
                set
            }));
        }
        Ok(Self {
            mutations,
            grammar_sets,
        })
    }

    /// Decode one mutation list. Unknown keys, values of the wrong type, duplicate or empty
    /// ids, a mutation without edits or without its misunderstanding, and an edit that is not
    /// exactly one of find/replace or `delete = true` are errors naming the key. A `[[mutation]]`
    /// with `grammar` is a generated set ([`GrammarSet`]): it writes no edit and no `expect`.
    pub fn decode(text: &str) -> Result<Self, ManifestError> {
        let top: Table = toml::from_str(text)
            .map_err(|e| ManifestError::new("", format!("invalid TOML: {e}")))?;
        known_keys(&top, "", &["mutation"])?;
        let mut mutations = Vec::new();
        let mut grammar_sets = Vec::new();
        match top.get("mutation") {
            None => {}
            Some(Value::Array(entries)) => {
                for (index, entry) in entries.iter().enumerate() {
                    if entry
                        .as_table()
                        .is_some_and(|table| table.contains_key("grammar"))
                    {
                        grammar_sets.push(grammar_set(index, entry)?);
                    } else {
                        mutations.push(mutation(index, entry)?);
                    }
                }
            }
            Some(_) => {
                return Err(ManifestError::new(
                    "mutation",
                    "expected [[mutation]] tables",
                ));
            }
        }
        let mut ids = BTreeSet::new();
        for id in mutations
            .iter()
            .map(|mutation| &mutation.id)
            .chain(grammar_sets.iter().map(|set| &set.id))
        {
            if !ids.insert(id.as_str()) {
                return Err(ManifestError::new(
                    mutation_key(id),
                    "duplicate mutation id",
                ));
            }
        }
        Ok(Self {
            mutations,
            grammar_sets,
        })
    }

    /// Whether `id` names a mutation `run --only` can select before the specification is
    /// admitted: a written mutation, a generated set (every row it expands into), or a row of a
    /// set (an id under `<set id>/`, which the expansion decides).
    #[must_use]
    pub fn names(&self, id: &str) -> bool {
        self.mutations.iter().any(|mutation| mutation.id == id)
            || self.grammar_sets.iter().any(|set| {
                set.id == id
                    || id
                        .strip_prefix(set.id.as_str())
                        .is_some_and(|rest| rest.starts_with('/'))
            })
    }

    /// Whether every projection a mutation's `expect` names ([`Expected::Projections`]) is one
    /// `manifest` declares ([`FlowManifest::projections`]: `default` alone for a flow that declares
    /// none) and no snapshot projection, which `run` never judges
    /// ([`FlowManifest::run_projections`]): the list decodes without its flow, so a command that
    /// reads both checks it, and either name is an error naming its key, since its claim could
    /// never be checked.
    pub fn check_projections(&self, manifest: &FlowManifest) -> Result<(), ManifestError> {
        let declared = manifest.projections();
        let names = declared
            .iter()
            .map(|projection| projection.name.as_str())
            .collect::<Vec<_>>();
        for mutation in &self.mutations {
            let Some(expect) = &mutation.expect else {
                continue;
            };
            for name in expect.projection_names() {
                let key = || join(&join(&mutation_key(&mutation.id), "expect"), name);
                match declared.iter().find(|projection| projection.name == name) {
                    None => {
                        return Err(ManifestError::new(
                            key(),
                            format!(
                                "names no projection of the flow (its projections: {})",
                                names.join(", ")
                            ),
                        ));
                    }
                    Some(projection) if projection.is_snapshot() => {
                        return Err(ManifestError::new(
                            key(),
                            format!(
                                "`{name}` is a snapshot projection (`relation = \"snapshot\"`): it \
                                 relates an implementation's answer to the value a user accepted, \
                                 which `compare` judges; `run` judges mutants of the definition \
                                 under none"
                            ),
                        ));
                    }
                    // A host-dependent metric (no relation: its value is reported only): `run`
                    // never judges a metric projection, so the claim could never be checked.
                    Some(projection) if projection.is_host_dependent() => {
                        return Err(ManifestError::new(
                            key(),
                            format!(
                                "`{name}` is a metric projection (`kind = \"metric\"`): it \
                                 measures an implementation's answer, which `compare` reports; \
                                 `run` judges mutants of the definition under none"
                            ),
                        ));
                    }
                    Some(_) => {}
                }
            }
        }
        Ok(())
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

/// A `[[mutation]]` with `grammar` at `index` ([`GrammarSet`]): `id`, `grammar = "default"` or
/// `grammar = { forms = [...] }` ([`grammar_forms`]) and an optional `misunderstanding` (or
/// `note`); `edit` and `expect` are errors, since a set writes no edit and one claim cannot hold
/// for every row it gives.
fn grammar_set(index: usize, value: &Value) -> Result<GrammarSet, ManifestError> {
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
    for (name, why) in [
        (
            "edit",
            "a mutation with `grammar` is a generated set: it writes no edit (write the edits in              a mutation of their own)",
        ),
        (
            "expect",
            "a generated set's rows are judged one by one: no one expectation holds for every              row",
        ),
    ] {
        if entry.contains_key(name) {
            return Err(ManifestError::new(join(&key, name), why));
        }
    }
    known_keys(entry, &key, &["id", "grammar", "misunderstanding", "note"])?;
    let set = grammar_forms(&entry["grammar"], &join(&key, "grammar"))?;
    let misunderstanding = match (entry.get("misunderstanding"), entry.get("note")) {
        (Some(text), None) => Some(non_empty(text, &join(&key, "misunderstanding"))?),
        (None, Some(text)) => Some(non_empty(text, &join(&key, "note"))?),
        (Some(_), Some(_)) => {
            return Err(ManifestError::new(
                join(&key, "note"),
                "`note` is an alias of `misunderstanding`; give one of them",
            ));
        }
        (None, None) => None,
    };
    Ok(GrammarSet {
        id,
        set,
        misunderstanding,
    })
}

/// A set's `grammar` value: `"default"`, or an inline table whose one key `forms` is a non-empty
/// array of distinct form names, any of kink-patch's forms (`GrammarForm::ALL`).
fn grammar_forms(value: &Value, position: &str) -> Result<GrammarSetName, ManifestError> {
    let names = GrammarForm::ALL
        .iter()
        .map(|form| format!("\"{}\"", form.name()))
        .collect::<Vec<_>>()
        .join(", ");
    let expected = || {
        ManifestError::new(
            position,
            format!(
                "expected \"default\" (the default grammar operator set: widening and \
                 token-level narrowing) or {{ forms = [...] }}, a non-empty list of distinct \
                 forms among {names}"
            ),
        )
    };
    if value.as_str() == Some("default") {
        return Ok(GrammarSetName::Default);
    }
    let table = value.as_table().ok_or_else(expected)?;
    known_keys(table, position, &["forms"])?;
    let written = table
        .get("forms")
        .and_then(Value::as_array)
        .filter(|forms| !forms.is_empty())
        .ok_or_else(expected)?;
    let mut forms = Vec::new();
    for item in written {
        let form = item
            .as_str()
            .and_then(|name| {
                GrammarForm::ALL
                    .into_iter()
                    .find(|form| form.name() == name)
            })
            .ok_or_else(|| {
                ManifestError::new(
                    join(position, "forms"),
                    format!("unknown grammar form {item}: the forms are {names}"),
                )
            })?;
        if forms.contains(&form) {
            return Err(ManifestError::new(
                join(position, "forms"),
                format!("the form \"{}\" is named twice", form.name()),
            ));
        }
        forms.push(form);
    }
    forms.sort();
    Ok(GrammarSetName::Forms(forms))
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
    known_keys(
        entry,
        &key,
        &["id", "misunderstanding", "note", "expect", "edit"],
    )?;
    let expect = match entry.get("expect") {
        None => None,
        Some(value) => Some(expected(&join(&key, "expect"), value)?),
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
    let misunderstanding = match (entry.get("misunderstanding"), entry.get("note")) {
        (Some(text), None) => non_empty(text, &join(&key, "misunderstanding"))?,
        (None, Some(text)) => non_empty(text, &join(&key, "note"))?,
        (Some(_), Some(_)) => {
            return Err(ManifestError::new(
                join(&key, "note"),
                "`note` is an alias of `misunderstanding`; give one of them",
            ));
        }
        (None, None) => {
            return Err(ManifestError::new(
                join(&key, "misunderstanding"),
                "missing required key: say in prose which plausible misunderstanding of the \
                 specification this mutation writes (`note` is accepted as its alias)",
            ));
        }
    };
    Ok(Mutation {
        id,
        misunderstanding,
        expect,
        edits,
    })
}

/// A mutation's `expect` at `key`: `"survive"` or `"kill"`, or a nonempty table of those per
/// projection name ([`Expected`]). Whether each name is a projection of the flow, and none a
/// snapshot projection, is checked where the list is read with its manifest
/// ([`MutationList::check_projections`]).
fn expected(key: &str, value: &Value) -> Result<Expected, ManifestError> {
    const VERDICT: &str =
        "expected \"survive\" or \"kill\": the verdict the corpus gives the mutation";
    if let Value::Table(table) = value {
        if table.is_empty() {
            return Err(ManifestError::new(
                key,
                "names no projection: give `\"survive\"`, `\"kill\"` or { NAME = \"survive\" | \"kill\" }",
            ));
        }
        return table
            .iter()
            .map(|(name, verdict)| {
                verdict
                    .as_str()
                    .and_then(Expect::parse)
                    .map(|verdict| (name.clone(), verdict))
                    .ok_or_else(|| ManifestError::new(join(key, name), VERDICT))
            })
            .collect::<Result<Vec<_>, _>>()
            .map(Expected::Projections);
    }
    value
        .as_str()
        .and_then(Expect::parse)
        .map(Expected::Row)
        .ok_or_else(|| {
            ManifestError::new(
                key,
                "expected \"survive\" or \"kill\" (or a table of them by projection name): \
                 the verdict the corpus gives the mutation",
            )
        })
}

fn edit_spec(key: &str, value: &Value) -> Result<EditSpec, ManifestError> {
    let entry = value
        .as_table()
        .ok_or_else(|| ManifestError::new(key, "expected a table"))?;
    known_keys(
        entry,
        key,
        &[
            "file",
            "rule",
            "production",
            "line",
            "find",
            "replace",
            "delete",
        ],
    )?;
    let file = optional_non_empty(entry, key, "file")?;
    let rule = optional_non_empty(entry, key, "rule")?;
    let production = optional_non_empty(entry, key, "production")?;
    if rule.is_some() && production.is_some() {
        return Err(ManifestError::new(
            key,
            "give rule or production, not both: a rule label and a production name are anchors \
             of different sentences",
        ));
    }
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
    if action == EditAction::Delete && rule.is_none() && production.is_none() && line.is_none() {
        return Err(ManifestError::new(
            key,
            "delete = true needs rule, production or line to address what it deletes",
        ));
    }
    Ok(EditSpec {
        file,
        rule,
        production,
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
    /// No authored sentence's label is the anchor or ends with it as whole components (for
    /// `production`, no production's name).
    UnknownLabel,
    /// The anchor names several labels (exactly or as a suffix of their components); the
    /// detail gives each one's module-qualified label, its fullest anchor.
    AmbiguousLabel,
    /// No authored sentence covers the line.
    LineOutsideRules,
    /// Several rules cover the line.
    LineAmbiguous,
    /// `rule` (or `production`), `line` and `file` do not all address the same rule (or grammar
    /// declaration).
    AddressMismatch,
    /// The addressed sentence is neither a rule nor in a grammar declaration (a production, a
    /// lexical, priority or associativity declaration): a sort declaration, a configuration or
    /// another sentence, none of which is editable.
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
    /// The edited rule loads to the baseline rule's sentence (layout, comments, a `requires true`).
    NoChange,
    /// kink-patch refused the patch for a reason other than typing (a stale pin, a patch that does
    /// not resolve, a selection error). Defensive: the checks above make it unreachable on rules
    /// k-rust loaded. No typing error refuses a mutation (re-pin L2-2-fix-1; findings C-02,
    /// C-03): a mutant is valid when it compiles, and kink-patch only records an edited rule's
    /// errors in compilation's typing view (the row's `typing_diagnostics`). k-rust documents
    /// those errors as errors compilation stops at, but its view refuses shapes compilation
    /// accepts (`CellCompletion`, and a least upper bound that a second common supersort in the
    /// main module makes non-unique; review L2-2-review-1, probes lub, lubbase and lubmain).
    PatchRejected,
    /// An edited rule is too deep for kink: its patch's document would nest deeper than
    /// kink-patch `MAX_JSON_DEPTH` (two JSON levels per term level: terms about 64,000 levels
    /// deep in an unoptimized build, 300,000 in an optimized one), so the mutation has no
    /// encoding and no identity. It is kink's limit, not a fault of the mutation (re-pin
    /// L1-3-fix-2; before, such a rule aborted the process in typing, review L1-3-2 D1). A patch
    /// holds the whole edited rule, so the detail gives the rule's depth as a whole, and says
    /// when the specification's rule alone is already past the limit, so that no mutation of it
    /// can be judged in this build (re-pin L1-3-tail, review L1-3-fix-2-1 D4).
    EditedRuleTooDeep,
    /// The host refused the native stack that encoding the mutation's patch needs (the system
    /// would not map a stack segment of the size the patch's depth needs: an address-space limit
    /// such as `ulimit -v`, or memory it will not commit). It is the host's limit, neither a fault
    /// of the mutation nor a verdict, so the row's status is `error`, not `invalid-mutation`
    /// ([`Self::status`]); the same mutation is judged where the host grants the stack (re-pin
    /// L1-3-tail, review L1-3-fix-2-1 D1).
    HostStackRefused,
    /// The edited grammar declarations give no program parser for the specification's syntax
    /// module (kink-patch `Mutant::program_parser`): the detail is k-rust's reason (an invalid
    /// regex, a token two productions rank differently, a priority cycle).
    NoProgramParser,
    /// kink-flow reads a grammar edit from the declaration's text with k-rust's outer parser and
    /// lowering, and the specification's loaded sentences of an edited declaration are not that
    /// reading (a sort synonym the load resolves after lowering, say), or the declarations do not
    /// lower apart from the rest of the load (a tag declared only in the prelude): kink-flow
    /// cannot tell what the edit changes.
    UnreadDeclaration,
    /// A command that does not judge a mutation that edits the grammar: only `run`'s first-kill
    /// search (in its default mode or under `--verify`) in a flow without `[[projection]]` parses
    /// each case again under the mutant's grammar (`crate::reparse`), and running the mutant on
    /// the baseline's parsed cases would judge another mutant. `run --full`, a flow with
    /// `[[projection]]`, prune's cells, coverage flips and a `fuzz` kill job give it. It is kink's
    /// limit, neither a fault of the mutation nor a verdict, so the row's status is `error`;
    /// `check` resolves the mutation.
    GrammarNotRun,
    /// A generated grammar set ([`GrammarSet`]) in a flow whose front end judges written
    /// production edits only (a KRS flow, whose productions are emitted from Rust items; a
    /// generated row has no text edit for it to judge): kink generates no row it would run
    /// unjudged, so the set gives no mutant (U34h).
    GrammarSetNotJudged,
    /// A row a generated grammar set expands into has the id of a written mutation, of another
    /// set or of another of its rows.
    GrammarSetIdCollision,
    /// A front end refused the mutation before kink-flow resolved it, by a check only the front
    /// end can make (the krs front end: an edit of a node KRS generated, a mutant KRS's own
    /// analysis refuses). `name` is the front end's kebab-case reason and `next` what the author
    /// does next. kink-flow never constructs it; [`Self::ALL`] and [`Self::parse`] list kink-flow's
    /// own reasons only.
    External {
        name: &'static str,
        next: &'static str,
    },
}

impl InvalidReason {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::External { name, .. } => name,
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
            Self::EditedRuleTooDeep => "edited-rule-too-deep",
            Self::HostStackRefused => "host-stack-refused",
            Self::NoProgramParser => "no-program-parser",
            Self::UnreadDeclaration => "unread-declaration",
            Self::GrammarNotRun => "grammar-not-run",
            Self::GrammarSetNotJudged => "grammar-set-not-judged",
            Self::GrammarSetIdCollision => "grammar-set-id-collision",
        }
    }

    /// Every reason kink-flow gives, in declaration order (not [`Self::External`], a front end's).
    pub const ALL: [Self; 29] = [
        Self::UnknownFile,
        Self::FileRequired,
        Self::UnknownLabel,
        Self::AmbiguousLabel,
        Self::LineOutsideRules,
        Self::LineAmbiguous,
        Self::AddressMismatch,
        Self::NonRuleSentence,
        Self::NoUsableSpan,
        Self::FindNotFound,
        Self::FindAmbiguous,
        Self::EditOutsideRule,
        Self::OverlappingEdits,
        Self::SourceChanged,
        Self::SourceViewMismatch,
        Self::MarkdownEnvelope,
        Self::EditedLoadFailed,
        Self::StructureChanged,
        Self::LabelChanged,
        Self::SpanChanged,
        Self::NoChange,
        Self::PatchRejected,
        Self::EditedRuleTooDeep,
        Self::HostStackRefused,
        Self::NoProgramParser,
        Self::UnreadDeclaration,
        Self::GrammarNotRun,
        Self::GrammarSetNotJudged,
        Self::GrammarSetIdCollision,
    ];

    /// The reason whose [`Self::as_str`] is `name`.
    pub fn parse(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|reason| reason.as_str() == name)
    }

    /// What the author of the mutation does next: one sentence, for `check` and every refusal.
    pub const fn next_step(self) -> &'static str {
        match self {
            Self::External { next, .. } => next,
            Self::UnknownFile => {
                "name a source file of the specification in `file` (the detail lists them), or \
                 leave `file` out and address the rule by `rule`"
            }
            Self::FileRequired => {
                "add `file`, or address the rule by `rule = <label>` (a production by \
                 `production = <name>`)"
            }
            Self::UnknownLabel => {
                "the rule was renamed or removed, or the anchor is misspelt: find the rule's \
                 current label in the K (the detail names the labels near the anchor, when there \
                 are any) and rewrite `rule`, or drop the mutation if the rule is gone"
            }
            Self::AmbiguousLabel => {
                "write more of the label so that it names one rule: more of its components, or \
                 the whole label qualified by its module (MODULE.label, given in the detail)"
            }
            Self::LineOutsideRules | Self::LineAmbiguous => {
                "address the rule by `rule = <label>` instead of `line`: a line moves whenever \
                 anything above it changes"
            }
            Self::AddressMismatch => {
                "make `rule` (or `production`), `line` and `file` name one rule (or grammar \
                 declaration), or keep `rule` (or `production`) alone"
            }
            Self::NonRuleSentence => {
                "address a rule or a grammar declaration (a production, a lexical, priority or \
                 associativity declaration): sort declarations, configurations and other \
                 sentences are not editable"
            }
            Self::FindNotFound => {
                "the rule's text changed or `find` is misspelt: copy `find` from the rule's \
                 current K text, or drop the mutation if what it changed is gone"
            }
            Self::FindAmbiguous => "make `find` longer, so that it occurs once in the rule",
            Self::EditOutsideRule => {
                "address the rule that holds the text by `rule`, or change `find` to text inside \
                 the addressed rule"
            }
            Self::OverlappingEdits => {
                "merge the overlapping edits into one edit or make their `find` texts disjoint; \
                 a deleted rule takes no other edit"
            }
            Self::SourceChanged => {
                "rerun the command: a source file changed after the specification was loaded"
            }
            Self::SourceViewMismatch => {
                "rerun with the md_selector the specification was loaded with; report it if it \
                 persists"
            }
            Self::MarkdownEnvelope => "do not write or touch a Markdown fence line in an edit",
            Self::EditedLoadFailed => {
                "fix the replacement so that the edited rule parses and sorts (the detail is \
                 k-rust's message)"
            }
            Self::StructureChanged => {
                "edit only the addressed rule (or grammar declaration): a replaced rule must stay \
                 one rule sentence, a grammar declaration one declaration, and nothing outside \
                 them may change (the detail says what did)"
            }
            Self::LabelChanged => {
                "keep the rule's label: a mutation changes what a rule does, not its name"
            }
            Self::SpanChanged => {
                "keep the replacement inside the rule: do not end it in a comment or write past \
                 the rule's end"
            }
            Self::NoChange => {
                "change what the rule says, or drop the edit: as written it changes nothing"
            }
            Self::NoUsableSpan | Self::PatchRejected => "report it: this is a defect of kink",
            Self::EditedRuleTooDeep => {
                "target another rule, or replace the deep part of the rule by a shallow one (the \
                 detail gives the depths)"
            }
            Self::HostStackRefused => {
                "rerun where the host grants more address space; the mutation is not at fault"
            }
            Self::NoProgramParser => {
                "fix the edit so that the edited grammar still gives a program parser (the detail \
                 is k-rust's reason)"
            }
            Self::UnreadDeclaration => {
                "edit another declaration, or report it: kink-flow cannot read this declaration's \
                 edit apart from the rest of the specification (the detail says why)"
            }
            Self::GrammarNotRun => {
                "judge the mutation with `run`'s first-kill search (with or without `--verify`) in \
                 a flow without `[[projection]]`: this command does not parse the cases again \
                 under a mutant's grammar, so it does not judge it"
            }
            Self::GrammarSetNotJudged => {
                "leave the generated grammar set out of this flow's list, and write each grammar \
                 mutation as a text edit: its front end judges written production edits only, so \
                 kink generates no grammar mutant for it"
            }
            Self::GrammarSetIdCollision => {
                "rename the set or the mutation whose id a generated row takes (the detail names \
                 both)"
            }
        }
    }

    /// The status of the row of a mutation refused for this reason: `error` for the host's
    /// refusal ([`Self::HostStackRefused`]) and for kink's not judging a grammar mutation yet
    /// ([`Self::GrammarNotRun`]), neither a fault of the mutation; `invalid-mutation` for every
    /// other reason, a front end's included.
    pub const fn status(self) -> &'static str {
        match self {
            Self::HostStackRefused | Self::GrammarNotRun => "error",
            _ => crate::search::INVALID_MUTATION,
        }
    }
}

/// A mutation that resolves to no patch (status `invalid-mutation`, or `error` for the host's
/// refusal: [`InvalidReason::status`]).
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
    /// Every edit as it was applied, in the mutation's edit order: what each edit rewrites,
    /// one by one, where [`Self::rules`] gives each rule's text with all of its edits applied.
    pub edits: Vec<ResolvedEdit>,
    /// The edited K view of every edited source file, by its logical name: for a `.k` file its
    /// edited text, for a `.md` file its edited K view (never Markdown).
    pub edited_views: BTreeMap<String, String>,
    /// F-04's name for [`Self::edited_views`], kept for its callers: the same K text.
    pub edited_sources: BTreeMap<String, String>,
    /// What the edited load read in place of each edited file (see [`Self::overlay`]).
    overlay: BTreeMap<String, String>,
}

/// One edit of a mutation as resolution applied it to the K view of its file.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedEdit {
    /// The index of the edit in the mutation (`edit[i]`).
    pub edit: usize,
    /// The baseline rule the edit is addressed to.
    pub at: SentenceRef,
    /// The rule's source file, by its logical name.
    pub file: String,
    /// The bytes of the file's baseline K view the edit rewrites: the occurrence of `find`, or
    /// the rule's whole span for a deletion.
    pub range: Range<usize>,
    /// The text written in place of [`Self::range`]; `None` for a deletion, which writes nothing.
    pub replacement: Option<String>,
    /// Where the replacement lies in the edited K view ([`ResolvedMutation::edited_views`]);
    /// empty, at the place of the removed rule, for a deletion.
    pub edited_range: Range<usize>,
}

/// What an [`EditedRule`] is: a rule, or a grammar declaration (PJ-34).
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum EditedKind {
    /// One rule sentence.
    #[default]
    Rule,
    /// One grammar declaration (a `syntax` declaration of productions, `syntax priority`,
    /// `syntax left|right|non-assoc`, `syntax lexical`) and every sentence it lowers to; `at` is
    /// the item the edits address (the production `production` names, or the one production the
    /// line or text lies in, else the declaration's first sentence), and the lines and texts are
    /// the declaration's.
    Grammar,
}

/// One rule a mutation edits or deletes, or one grammar declaration it edits ([`EditedKind`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EditedRule {
    pub at: SentenceRef,
    pub kind: EditedKind,
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
    /// The resolution of a row a generated grammar set expands into ([`crate::grammar_set`]):
    /// `patch`, kink-patch's generated patch (pinned, admitted by a program parser for the
    /// syntax module), with its digest and the one grammar entry of its site, `rule`. No text
    /// edit wrote it, so it has no edits, no edited views and no overlay.
    pub(crate) fn generated(
        id: String,
        patch: Patch,
        digest: Sha256Digest,
        rule: EditedRule,
    ) -> Self {
        Self {
            id,
            patch,
            digest,
            rules: vec![rule],
            edits: Vec::new(),
            edited_views: BTreeMap::new(),
            edited_sources: BTreeMap::new(),
            overlay: BTreeMap::new(),
        }
    }

    /// The kink-corpus loader overlay the edited load read, by logical name: a `.k` file's
    /// edited view, or a `.md` file's Markdown envelope of its edited view (one fence around
    /// the view, which extracts to the view again; [`markdown_envelope`]). It exists so that a
    /// test can repeat the edited load; nothing shows it to a user, and the mutant is never
    /// built from it (the mutant is the patched baseline). Empty for a grammar mutation, which no
    /// edited load reads (module documentation, "Grammar edits").
    pub fn overlay(&self) -> &BTreeMap<String, String> {
        &self.overlay
    }

    /// Whether the mutation edits grammar declarations (it may edit rules beside them). A mutation
    /// that does not is a rule mutation, whose grammar is the specification's.
    #[must_use]
    pub fn is_grammar(&self) -> bool {
        self.rules
            .iter()
            .any(|rule| rule.kind == EditedKind::Grammar)
    }

    /// The candidate generation of a grammar mutation, for `run`'s search alone, which parses
    /// every case again under the mutant's grammar before it runs any (`crate::reparse`): one
    /// candidate, this patch, admitted when its mutant gives a program parser for
    /// `syntax_module` (kink-patch `supplied_grammar`). [`Self::generation`] keeps refusing a
    /// grammar mutation, so no other caller runs a grammar mutant on the cases as the
    /// specification parses them. `baseline` must be the baseline of the validator that runs the
    /// campaign.
    ///
    /// # Errors
    ///
    /// `patch-rejected` for a rule mutation or a patch the fold refuses.
    pub fn grammar_generation<'b>(
        &self,
        baseline: &'b Baseline,
        syntax_module: &str,
    ) -> Result<CandidateGeneration<'b>, InvalidMutation> {
        let rejected = |detail: String| InvalidMutation {
            edit: None,
            reason: InvalidReason::PatchRejected,
            detail,
        };
        if !self.is_grammar() {
            return Err(rejected(
                "a rule mutation has no grammar generation".to_owned(),
            ));
        }
        let generation =
            kink_patch::supplied_grammar(baseline, MUTATION_OPERATOR, &self.patch, syntax_module)
                .map_err(|e| rejected(e.to_string()))?;
        match generation.dispositions() {
            [CandidateDisposition::Mutant(0)] => Ok(generation),
            [CandidateDisposition::Rejected(failure)] => Err(rejected(failure.to_string())),
            other => Err(rejected(format!("unexpected dispositions {other:?}"))),
        }
    }

    /// Why a command does not judge this mutation: `grammar-not-run` for a mutation that edits
    /// the grammar ([`InvalidReason::GrammarNotRun`]), `None` for a rule mutation. Only `run`'s
    /// first-kill search, in its default mode or under `--verify`, judges a grammar mutation
    /// (`crate::reparse`); a `fuzz` kill job, coverage flips, prune's cells, `run --full` and a
    /// flow that declares `[[projection]]` give this refusal.
    #[must_use]
    pub fn run_refusal(&self) -> Option<InvalidMutation> {
        self.is_grammar().then(|| InvalidMutation {
            edit: None,
            reason: InvalidReason::GrammarNotRun,
            detail: format!(
                "the mutation edits the grammar ({}); only `run`'s first-kill search (with or \
                 without `--verify`), in a flow that declares no `[[projection]]`, parses each \
                 case again under the mutant's grammar, and running the mutant on the cases as \
                 the specification parses them would judge another mutant",
                self.rules
                    .iter()
                    .map(|rule| match &rule.label {
                        Some(label) => format!("{label} at {}:{}", rule.file, rule.start_line),
                        None => format!("the declaration at {}:{}", rule.file, rule.start_line),
                    })
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        })
    }

    /// The candidate generation that runs this mutation: one candidate, this patch, with a
    /// site at the body of every addressed rule (a supplied, hence non-exhaustive and never
    /// scored, discovery; kink-patch `Discovery::supplied`). `baseline` must be the baseline
    /// of the validator that runs the campaign (`CandidateGeneration::derived_from`). A grammar
    /// mutation has none yet ([`Self::run_refusal`]).
    pub fn generation<'b>(
        &self,
        baseline: &'b Baseline,
    ) -> Result<CandidateGeneration<'b>, InvalidMutation> {
        if let Some(refusal) = self.run_refusal() {
            return Err(refusal);
        }
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
    /// `None` deletes the rule (or the grammar declaration).
    replacement: Option<String>,
    /// The grammar declaration the edit edits; `None` for a rule edit.
    declaration: Option<Declaration>,
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

    /// A production's name, its label ([`EditSpec::production`]).
    fn production_name(&self) -> Option<&str> {
        match self.sentence {
            Sentence::Production {
                label: Some(label), ..
            } => Some(label.name.as_str()),
            _ => None,
        }
    }

    /// The name a row gives the sentence: its label (a rule's), else a production's name.
    fn name(&self) -> Option<&str> {
        self.label().or_else(|| self.production_name())
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
        match self.name() {
            Some(label) => format!("{label} ({place})"),
            None => place,
        }
    }
}

/// The K view of one source file: the text k-rust parsed for it (flow README 6.1).
///
/// For a `.k` file (any name not ending in `.md`, as k-rust's loader decides) it is the
/// file's text. For a `.md` file it is `k_rust::outer::extract_fenced_k_code_with_map(raw,
/// md_selector).text`, the extraction the loader parses: at k-rust 501f18b9 every character of
/// a selected fence's content and every line break are kept, and every other character becomes
/// one space per byte, so the view has the file's byte length, lines and columns (its offset
/// map is the identity). The constructor ([`View::read`]) is the only
/// code of kink-flow that reads a Markdown file's text; the raw text is dropped once the view
/// is built.
pub struct View {
    /// The K text.
    pub text: String,
    /// Whether the file is Markdown (its view is an extraction).
    pub markdown: bool,
    /// The source-table ids of the baseline's extractions of this file (the same logical name,
    /// raw content hash and offset map); never empty.
    pub source_ids: BTreeSet<SourceId>,
}

impl View {
    /// The K view of the source file `name` of `loaded`, read from `directory` (the manifest's
    /// directory) and checked: its bytes against the digest the load recorded
    /// (`source-changed`); for a `.md` file, the view under `md_selector` against the text the
    /// loader parsed, which is the extraction of those same bytes under the selector the load
    /// used ([`LoadedSource::md_selector`]; a load that recorded none is refused); and the
    /// baseline's source table must hold an extraction of this file (its logical name and raw
    /// content hash) whose offset map equals the recomputed one (`.k`: none). A failure of
    /// either of the last two is `source-view-mismatch`.
    ///
    /// The text comparison is what binds the view to the load: at k-rust 501f18b9 the offset
    /// map of every extraction is the identity (re-pin finding E-09), so the source table no
    /// longer tells a view built under another selector (one that also selects a ghost fence,
    /// say) from the text k-rust parsed. A view whose text differs would let a mutant differ
    /// from the baseline by more than its declared edits.
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
            let parsed_under = loaded.md_selector().ok_or_else(|| {
                mismatch(format!(
                    "the load of {name} recorded no Markdown selector, so the text k-rust parsed \
                     is unknown"
                ))
            })?;
            let parsed = extract_fenced_k_code_with_map(&raw, parsed_under).map_err(|e| {
                mismatch(format!(
                    "{name} does not extract under the load's selector {parsed_under:?}: {e}"
                ))
            })?;
            if parsed.text != extracted.text {
                return Err(mismatch(format!(
                    "the K view of {name} under md_selector {md_selector:?} is not the text the \
                     load parsed under {parsed_under:?}: k-rust parsed other text"
                )));
            }
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
    /// Each view's outer syntax (k-rust's outer parser) and its declarations, built on first use.
    parsed: BTreeMap<String, (outer::SourceFile, Vec<Declaration>)>,
}

impl<'a> Views<'a> {
    fn new(manifest: &FlowManifest, loaded: &'a LoadedSource) -> Self {
        Views {
            directory: manifest.directory.clone(),
            md_selector: manifest.spec.md_selector.clone(),
            loaded,
            views: BTreeMap::new(),
            parsed: BTreeMap::new(),
        }
    }

    /// The outer syntax of the K view of `name` and its declarations.
    fn parsed(
        &mut self,
        name: &str,
    ) -> Result<&(outer::SourceFile, Vec<Declaration>), (InvalidReason, String)> {
        if !self.parsed.contains_key(name) {
            let view = self.view(name)?;
            let file = outer::parse(name, &view.text).map_err(|e| {
                (
                    InvalidReason::SourceViewMismatch,
                    format!("k-rust's outer parser does not read the K view of {name}: {e}"),
                )
            })?;
            let declarations = declarations_of(&file);
            self.parsed.insert(name.to_owned(), (file, declarations));
        }
        Ok(&self.parsed[name])
    }

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

/// One declaration of a K view, as k-rust's outer parser reads it: a `syntax` declaration, a
/// `syntax priority`, associativity or lexical declaration, or a bubble (a rule, claim, context
/// or configuration).
#[derive(Clone, Debug, Eq, PartialEq)]
struct Declaration {
    module: String,
    /// Its bytes in the view.
    span: Range<usize>,
    start_line: u32,
    end_line: u32,
    /// Whether it is a grammar declaration (PJ-34): a `syntax` declaration of productions, or a
    /// priority, associativity or lexical declaration. A sort declaration, a sort synonym and a
    /// bubble are not.
    grammar: bool,
    /// The productions it declares (alternatives of a `syntax` declaration).
    productions: usize,
    /// Its kind, so that an edit cannot turn one kind of declaration into another.
    kind: &'static str,
}

impl Declaration {
    fn contains(&self, range: &Range<usize>) -> bool {
        self.span.start <= range.start && range.end <= self.span.end
    }

    fn describe(&self, file: &str) -> String {
        format!(
            "the {} declaration at {file}:{}",
            self.kind, self.start_line
        )
    }
}

/// The declarations of `file`, module by module in text order.
fn declarations_of(file: &outer::SourceFile) -> Vec<Declaration> {
    let mut declarations = Vec::new();
    for module in &file.modules {
        for sentence in &module.sentences {
            let (span, kind, productions) = match sentence {
                outer::Sentence::Syntax(syntax) => match &syntax.body {
                    outer::SyntaxBody::Productions(blocks) => (
                        syntax.span,
                        "syntax",
                        blocks.iter().map(|block| block.productions.len()).sum(),
                    ),
                    outer::SyntaxBody::Sort(_) => (syntax.span, "sort", 0),
                    outer::SyntaxBody::Synonym { .. } => (syntax.span, "sort synonym", 0),
                },
                outer::Sentence::Priority(priority) => (priority.span, "priority", 0),
                outer::Sentence::Associativity(associativity) => {
                    (associativity.span, "associativity", 0)
                }
                outer::Sentence::Lexical(lexical) => (lexical.span, "lexical", 0),
                outer::Sentence::Bubble(bubble) => (bubble.span, "bubble", 0),
            };
            declarations.push(Declaration {
                module: module.name.clone(),
                span: span.start.offset..span.end.offset,
                start_line: span.start.line,
                end_line: span.end.line,
                grammar: matches!(kind, "syntax" | "priority" | "associativity" | "lexical"),
                productions,
                kind,
            });
        }
    }
    declarations
}

/// The authored sentences of the baseline of `loaded`, each with its source file.
fn authored_sentences(loaded: &LoadedSource) -> Vec<Authored<'_>> {
    let file_names = loaded
        .files
        .iter()
        .map(|f| f.name.as_str())
        .collect::<BTreeSet<_>>();
    loaded
        .baseline
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
        .collect()
}

/// The rule `edit` alone is addressed to, as resolution's first step addresses it, with its
/// label: `None` when the edit addresses no single rule. It lets `check` name the rule of an
/// edit whose mutation is refused for another reason.
pub fn addressed_rule(
    manifest: &FlowManifest,
    loaded: &LoadedSource,
    edit: &EditSpec,
) -> Option<(SentenceRef, Option<String>)> {
    addressed_item(manifest, loaded, edit).map(|(at, label, _)| (at, label))
}

/// [`addressed_rule`] with what the edit edits: a rule, whose label it gives, or a grammar
/// declaration, whose item's production name it gives ([`EditedKind`]).
#[must_use]
pub fn addressed_item(
    manifest: &FlowManifest,
    loaded: &LoadedSource,
    edit: &EditSpec,
) -> Option<(SentenceRef, Option<String>, EditedKind)> {
    let authored = authored_sentences(loaded);
    let mut views = Views::new(manifest, loaded);
    let addressed = address(0, edit, &authored, &mut views).ok()?;
    let item = authored.iter().find(|a| a.at == addressed.at);
    Some(match addressed.declaration {
        None => (
            addressed.at,
            item.and_then(Authored::label).map(str::to_owned),
            EditedKind::Rule,
        ),
        Some(_) => (
            addressed.at,
            item.and_then(Authored::production_name).map(str::to_owned),
            EditedKind::Grammar,
        ),
    })
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

/// Every start offset of `needle` in `haystack`, overlapping occurrences included: a `find` applies
/// when it occurs once in the text it is resolved against by this count.
#[must_use]
pub fn occurrences(haystack: &str, needle: &str) -> Vec<usize> {
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
    /// The byte offset of `text` in its file's K view, which the spans of the rule's terms
    /// index; `None` with `text`.
    pub start: Option<usize>,
}

/// Every authored rule of the specification `loaded`, in sentence order, with its K text
/// (sliced from its file's K view by the same checked span resolution uses).
pub fn rule_texts(manifest: &FlowManifest, loaded: &LoadedSource) -> Vec<RuleText> {
    let mut views = Views::new(manifest, loaded);
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
            let sliced = file.as_deref().and_then(|name| {
                let view = views.view(name).ok()?;
                indexes_view(sentence, view, name).ok()?;
                let span = view_span(sentence, &view.text, name).ok()?;
                Some((view.text[span.clone()].to_owned(), span.start))
            });
            let (text, start) = sliced.unzip();
            RuleText {
                at,
                file,
                label,
                start_line: location.map(|l| l.start_line),
                end_line: location.map(|l| l.end_line),
                text,
                start,
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
    let mut views = Views::new(manifest, loaded);
    let authored = authored_sentences(loaded);
    let from_view = |(reason, detail)| InvalidMutation {
        edit: None,
        reason,
        detail,
    };

    // Step 1: address every edit in the K views.
    let mut text_edits = Vec::new();
    for (index, edit) in mutation.edits.iter().enumerate() {
        let text_edit = address(index, edit, &authored, &mut views)?;
        if let EditAction::Replace { find, replace } = &edit.action
            && find == replace
        {
            let rule = authored
                .iter()
                .find(|a| a.at == text_edit.at)
                .expect("an addressed rule is authored");
            return Err(InvalidMutation {
                edit: Some(index),
                reason: InvalidReason::NoChange,
                detail: format!(
                    "the edit replaces {find:?} in {} by the same text, so it changes nothing",
                    rule.describe()
                ),
            });
        }
        text_edits.push(text_edit);
    }

    // A grammar edit edits a declaration, read without parsing any unedited rule (module
    // documentation, "Grammar edits"); a rule edited beside it is parsed under the mutant's
    // grammar.
    if text_edits.iter().any(|e| e.declaration.is_some()) {
        return resolve_grammar(loaded, mutation, text_edits, &mut views, &authored);
    }

    // Edits of one rule must not overlap; a deleted rule takes no other edit.
    let mut groups = BTreeMap::<SentenceRef, Vec<&TextEdit>>::new();
    for edit in &text_edits {
        groups.entry(edit.at.clone()).or_default().push(edit);
    }
    check_overlaps(&mut groups, "rule")?;

    // Step 2: apply the text edits to the K views and load the edited views (a `.md` file
    // through its Markdown envelope).
    let whole = || (mutation.edits.len() == 1).then_some(0);
    let mut by_file = BTreeMap::<&str, Vec<&TextEdit>>::new();
    for edit in &text_edits {
        by_file.entry(&edit.file).or_default().push(edit);
    }
    let mut edited_files = BTreeMap::<String, EditedFile>::new();
    let mut overlay = BTreeMap::<String, String>::new();
    let mut resolved_edits = Vec::with_capacity(text_edits.len());
    for (file, edits) in by_file {
        let view = views.view(file).map_err(from_view)?;
        let (edited_view, shifts, written) = splice(&view.text, file, edits, &mut resolved_edits)?;
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
                        detail: format!(
                            "{} loads to the same sentence as before the edits: layout, \
                             comments and a `requires true` or `ensures true` load as they do \
                             without them",
                            site.describe()
                        ),
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
            kind: EditedKind::Rule,
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
    let digest = patch_digest(baseline, &patch, &rules, whole())?;
    resolved_edits.sort_by_key(|e| e.edit);
    let edited_views = edited_files
        .into_iter()
        .map(|(name, file)| (name, file.edited_view))
        .collect::<BTreeMap<_, _>>();
    let resolved = ResolvedMutation {
        id: mutation.id.clone(),
        patch,
        digest,
        rules,
        edits: resolved_edits,
        edited_sources: edited_views.clone(),
        edited_views,
        overlay,
    };
    // kink-patch applies the patch (and nothing else) once more when it folds the generation.
    resolved.generation(baseline)?;
    Ok(resolved)
}

/// The digest of `patch`, the mutation's identity, or why it has none: kink's depth limit
/// (`edited-rule-too-deep`, at the edit `whole` when the mutation has one) or the host's stack
/// (`host-stack-refused`).
fn patch_digest(
    baseline: &Baseline,
    patch: &Patch,
    rules: &[EditedRule],
    whole: Option<usize>,
) -> Result<Sha256Digest, InvalidMutation> {
    let rejected = |detail: String| InvalidMutation {
        edit: None,
        reason: InvalidReason::PatchRejected,
        detail,
    };
    let whole = || whole;
    patch.digest().map_err(|e| match e {
        CodecError::TooDeep { depth, limit } => InvalidMutation {
            edit: whole(),
            reason: InvalidReason::EditedRuleTooDeep,
            detail: too_deep_detail(baseline, patch, rules, depth, limit),
        },
        CodecError::Stack(StackRefusal::Refused(refused)) => InvalidMutation {
            edit: None,
            reason: InvalidReason::HostStackRefused,
            detail: format!(
                "{refused}: encoding this mutation's patch, whose JSON nests {} levels, needs \
                 that native stack, and the host refused it (an address-space limit such as \
                 `ulimit -v`, or memory the system will not commit); this is the host's limit, \
                 not a fault of the mutation, and the mutation is judged where the host grants \
                 the stack",
                patch
                    .document_depth()
                    .map_or_else(|_| "an unknown number of".to_owned(), |d| d.to_string())
            ),
        },
        CodecError::Stack(refusal @ StackRefusal::TooDeep { .. }) => InvalidMutation {
            edit: whole(),
            reason: InvalidReason::EditedRuleTooDeep,
            detail: format!(
                "{refusal}: encoding this mutation's patch needs more native stack than kink \
                 maps; this is kink's limit, not a fault of the mutation"
            ),
        },
        other => rejected(other.to_string()),
    })
}

/// Edits of one rule (or grammar declaration, `unit`) must not overlap, and a deleted one takes
/// no other edit. Sorts each group by range.
fn check_overlaps<K: Ord>(
    groups: &mut BTreeMap<K, Vec<&TextEdit>>,
    unit: &str,
) -> Result<(), InvalidMutation> {
    for edits in groups.values_mut() {
        edits.sort_by_key(|e| (e.range.start, e.range.end));
        if edits.len() > 1
            && let Some(delete) = edits.iter().find(|e| e.replacement.is_none())
        {
            return Err(InvalidMutation {
                edit: Some(delete.edit),
                reason: InvalidReason::OverlappingEdits,
                detail: format!("a deleted {unit} takes no other edit"),
            });
        }
        for pair in edits.windows(2) {
            if pair[0].range.end > pair[1].range.start {
                return Err(InvalidMutation {
                    edit: Some(pair[0].edit.max(pair[1].edit)),
                    reason: InvalidReason::OverlappingEdits,
                    detail: format!(
                        "edit[{}] and edit[{}] overlap in the same {unit}",
                        pair[0].edit.min(pair[1].edit),
                        pair[0].edit.max(pair[1].edit)
                    ),
                });
            }
        }
    }
    Ok(())
}

/// The edited K view of `file` (baseline view `text`) with `edits` applied, the length change of
/// each edit (its range in `text` and the change, in view order) and where each replacement lies
/// in the edited view; each applied edit is pushed onto `resolved`.
#[allow(clippy::type_complexity)]
fn splice(
    text: &str,
    file: &str,
    mut edits: Vec<&TextEdit>,
    resolved: &mut Vec<ResolvedEdit>,
) -> Result<
    (
        String,
        Vec<(Range<usize>, isize)>,
        Vec<(usize, Range<usize>)>,
    ),
    InvalidMutation,
> {
    edits.sort_by_key(|e| (e.range.start, e.range.end));
    let mut edited_view = String::with_capacity(text.len());
    let mut shifts = Vec::new();
    let mut written = Vec::new();
    let mut cursor = 0;
    for edit in edits {
        // Rule spans (and declaration spans) are disjoint and the edits of one do not overlap
        // (`check_overlaps`).
        if edit.range.start < cursor {
            return Err(InvalidMutation {
                edit: Some(edit.edit),
                reason: InvalidReason::OverlappingEdits,
                detail: format!("edit[{}] overlaps another edit of {file}", edit.edit),
            });
        }
        edited_view.push_str(&text[cursor..edit.range.start]);
        let start = edited_view.len();
        let replacement = edit.replacement.as_deref().unwrap_or("");
        edited_view.push_str(replacement);
        written.push((edit.edit, start..edited_view.len()));
        resolved.push(ResolvedEdit {
            edit: edit.edit,
            at: edit.at.clone(),
            file: file.to_owned(),
            range: edit.range.clone(),
            replacement: edit.replacement.clone(),
            edited_range: start..edited_view.len(),
        });
        shifts.push((edit.range.clone(), length_change(&edit.range, replacement)));
        cursor = edit.range.end;
    }
    edited_view.push_str(&text[cursor..]);
    Ok((edited_view, shifts, written))
}

/// One declaration of a file before and after the edits: its baseline declaration, the edited
/// declaration (`None` for a deleted one) and whether an edit edits it.
struct DeclarationPair {
    file: String,
    before: Declaration,
    after: Option<Declaration>,
    edited: bool,
}

/// Steps 2 and 3 for a mutation with a grammar edit (PJ-34, PJ-35; module documentation,
/// "Grammar edits"): the edits are applied to the K views, every file's view is read with k-rust's
/// outer parser and lowered (no rule is parsed), every declaration no edit edits must lower as
/// before, and each edited declaration's sentences are compared with its baseline's to give the
/// grammar patch, which must apply and give a program parser for the syntax module; each rule
/// edited beside them is then parsed under that patch's grammar ([`rule_patch_edits`]), and the
/// whole patch is admitted again.
fn resolve_grammar(
    loaded: &LoadedSource,
    mutation: &Mutation,
    mut text_edits: Vec<TextEdit>,
    views: &mut Views<'_>,
    authored: &[Authored<'_>],
) -> Result<ResolvedMutation, InvalidMutation> {
    let baseline = &loaded.baseline;
    let whole = || (mutation.edits.len() == 1).then_some(0);
    let from_view = |(reason, detail)| InvalidMutation {
        edit: None,
        reason,
        detail,
    };

    // A rule edited beside a grammar edit is the declaration its bubble is, so that the pairing
    // and the span checks cover it as they cover an edited declaration.
    for edit in &mut text_edits {
        if edit.declaration.is_none() {
            edit.declaration = Some(rule_bubble(views, authored, edit)?);
        }
    }
    let text_edits = text_edits.as_slice();

    // Edits of one declaration must not overlap; a deleted declaration takes no other edit.
    let mut groups = BTreeMap::<(String, usize), Vec<&TextEdit>>::new();
    for edit in text_edits {
        let declaration = edit.declaration.as_ref().expect("a grammar edit");
        groups
            .entry((edit.file.clone(), declaration.span.start))
            .or_default()
            .push(edit);
    }
    check_overlaps(&mut groups, "declaration")?;

    // Apply the edits to the K views (no envelope: no edited load reads them).
    let mut by_file = BTreeMap::<&str, Vec<&TextEdit>>::new();
    for edit in text_edits {
        by_file.entry(&edit.file).or_default().push(edit);
    }
    let mut edited_files = BTreeMap::<String, EditedFile>::new();
    let mut resolved_edits = Vec::with_capacity(text_edits.len());
    for (file, edits) in by_file {
        let view = views.view(file).map_err(from_view)?;
        let (edited_view, shifts, _) = splice(&view.text, file, edits, &mut resolved_edits)?;
        edited_files.insert(
            file.to_owned(),
            EditedFile {
                shifts,
                parsed: edited_view.clone(),
                edited_view,
                shift: 0,
            },
        );
    }

    // Every file's outer syntax, the edited views in place of the edited files, and its
    // declarations paired before and after the edits.
    let (before_files, after_files, pairs) =
        read_files(loaded, views, &edited_files, &groups, whole())?;

    let (edits, bubbles) = grammar_patch_edits(
        baseline,
        authored,
        &before_files,
        &after_files,
        &pairs,
        &groups,
        whole(),
    )?;
    if edits.is_empty() {
        let first = text_edits
            .iter()
            .find(|e| e.declaration.as_ref().is_some_and(|d| d.grammar))
            .unwrap_or(&text_edits[0]);
        return Err(InvalidMutation {
            edit: Some(first.edit),
            reason: InvalidReason::NoChange,
            detail: "the edited grammar declarations lower to the same sentences as before the \
                     edits: layout and comments are no change"
                .into(),
        });
    }

    let mut rules = grammar_rows(views, authored, &groups, &pairs, &edited_files)?;
    let grammar_patch = admitted_patch(loaded, edits.clone(), whole())?;
    let patch = if bubbles.is_empty() {
        grammar_patch
    } else {
        // Each edited rule parsed under the mutant's grammar, then the whole patch admitted.
        let (rule_edits, rule_rows) = rule_patch_edits(
            baseline,
            &grammar_patch,
            &bubbles,
            &groups,
            views,
            authored,
            &edited_files,
        )?;
        rules.extend(rule_rows);
        rules.sort_by(|a, b| a.at.cmp(&b.at));
        let mut edits = edits;
        edits.extend(rule_edits);
        admitted_patch(loaded, edits, whole())?
    };
    let digest = patch_digest(baseline, &patch, &rules, whole())?;
    resolved_edits.sort_by_key(|e| e.edit);
    let edited_views = edited_files
        .into_iter()
        .map(|(name, file)| (name, file.edited_view))
        .collect::<BTreeMap<_, _>>();
    Ok(ResolvedMutation {
        id: mutation.id.clone(),
        patch,
        digest,
        rules,
        edits: resolved_edits,
        edited_sources: edited_views.clone(),
        edited_views,
        overlay: BTreeMap::new(),
    })
}

/// The rows' entries of a grammar mutation: one per edited declaration, its item, lines and text
/// before and after the edits ([`EditedKind::Grammar`]).
fn grammar_rows(
    views: &mut Views<'_>,
    authored: &[Authored<'_>],
    groups: &BTreeMap<(String, usize), Vec<&TextEdit>>,
    pairs: &[DeclarationPair],
    edited_files: &BTreeMap<String, EditedFile>,
) -> Result<Vec<EditedRule>, InvalidMutation> {
    let from_view = |(reason, detail)| InvalidMutation {
        edit: None,
        reason,
        detail,
    };
    let mut rules = Vec::new();
    for ((file, start), group) in groups {
        if group[0].declaration.as_ref().is_some_and(|d| !d.grammar) {
            // An edited rule's row is [`rule_patch_edits`]'s.
            continue;
        }
        let pair = pairs
            .iter()
            .find(|p| p.file == *file && p.before.span.start == *start)
            .expect("an edited declaration is paired");
        let item = authored
            .iter()
            .find(|a| a.at == group[0].at)
            .expect("a grammar item is authored");
        let view = views.view(file).map_err(from_view)?;
        let before = view.text[pair.before.span.clone()].to_owned();
        let after = pair
            .after
            .as_ref()
            .map(|d| edited_files[file].edited_view[d.span.clone()].to_owned());
        let mut indices = group.iter().map(|e| e.edit).collect::<Vec<_>>();
        indices.sort_unstable();
        rules.push(EditedRule {
            at: item.at.clone(),
            kind: EditedKind::Grammar,
            edits: indices,
            file: file.clone(),
            label: item.production_name().map(str::to_owned),
            start_line: pair.before.start_line,
            end_line: pair.before.end_line,
            before,
            after,
        });
    }
    Ok(rules)
}

/// The declaration of the rule a rule edit of a grammar mutation addresses: the bubble of its
/// file's K view that starts where the rule's sentence starts (the outer lowering sets a
/// bubble's `SentenceStartOffset` to its start, and the load keeps it). `no-usable-span` where
/// no bubble starts there.
fn rule_bubble(
    views: &mut Views<'_>,
    authored: &[Authored<'_>],
    edit: &TextEdit,
) -> Result<Declaration, InvalidMutation> {
    let site = authored
        .iter()
        .find(|a| a.at == edit.at)
        .expect("an addressed rule is authored");
    let no_span = |detail: String| InvalidMutation {
        edit: Some(edit.edit),
        reason: InvalidReason::NoUsableSpan,
        detail,
    };
    let start = offsets(site.sentence)
        .ok_or_else(|| no_span(format!("{} has no offset attributes", site.describe())))?
        .start;
    let (_, declarations) =
        views
            .parsed(&edit.file)
            .map_err(|(reason, detail)| InvalidMutation {
                edit: Some(edit.edit),
                reason,
                detail,
            })?;
    declarations
        .iter()
        .find(|d| d.kind == "bubble" && d.span.start == start)
        .cloned()
        .ok_or_else(|| {
            no_span(format!(
                "no rule of the K view of {} starts where {} starts (byte {start})",
                edit.file,
                site.describe()
            ))
        })
}

/// One rule a grammar mutation edits beside its grammar edits, as the outer lowering reads it:
/// its module, its declaration's file and start in the baseline view, its lowered sentences
/// before and after the edits (none after for a deleted rule).
struct EditedBubble {
    module: String,
    file: String,
    start: usize,
    before: Vec<Arc<Sentence>>,
    after: Option<(Declaration, Vec<Arc<Sentence>>)>,
}

/// The one rule bubble `sentences` lower to: its contents and attributes, the source id left out
/// (no source table holds the edited view, so the parsed terms carry no source provenance; the
/// replacement takes the baseline rule's position keys, [`with_baseline_positions`]) and its
/// source named `file`, which a parse error names.
fn rule_bubble_parts<'s>(
    sentences: &'s [Arc<Sentence>],
    file: &str,
) -> Option<(&'s str, Attributes)> {
    match sentences {
        [sentence] => match &**sentence {
            Sentence::Bubble {
                sentence_type,
                contents,
                attributes,
            } if sentence_type == "rule" => {
                let mut attributes = attributes.clone();
                attributes.remove(AttributeKey::SourceId.as_str());
                attributes.set(AttributeKey::Source, serde_json::json!(file));
                Some((contents.as_str(), attributes))
            }
            _ => None,
        },
        _ => None,
    }
}

/// The replacement of the rule `original` (authored as `site`) that `bubble` edits, its edited
/// text lowered to `sentences`: parsed under the mutant's grammar `grammar`, with the baseline
/// rule's label, identity and position keys, and not the baseline rule ([`rule_patch_edits`]).
/// `Err` holds the refusal's reason and detail.
fn edited_rule(
    grammar: &ResolvedDefinition,
    bubble: &EditedBubble,
    sentences: &[Arc<Sentence>],
    original: &Sentence,
    site: &Authored<'_>,
) -> Result<Sentence, (InvalidReason, String)> {
    let (contents, attributes) = rule_bubble_parts(sentences, &bubble.file).ok_or_else(|| {
        (
            InvalidReason::StructureChanged,
            format!("{} is no longer a rule after the edit", site.describe()),
        )
    })?;
    let parsed =
        parse_rule_content(grammar, &bubble.module, contents, attributes).map_err(|e| {
            (
                InvalidReason::EditedLoadFailed,
                format!(
                    "{} does not parse under the edited grammar: {e}",
                    site.describe()
                ),
            )
        })?;
    for key in [AttributeKey::Label, AttributeKey::UniqueId] {
        if parsed.attributes().value(key) != original.attributes().value(key) {
            return Err((
                if key == AttributeKey::Label {
                    InvalidReason::LabelChanged
                } else {
                    InvalidReason::StructureChanged
                },
                format!(
                    "the edit changes the {} of {} to {}",
                    key.as_str(),
                    site.describe(),
                    parsed
                        .attributes()
                        .value(key)
                        .map_or_else(|| "none".to_owned(), ToString::to_string)
                ),
            ));
        }
    }
    let replacement = with_baseline_positions(&parsed, original);
    if fingerprint_equal(&replacement, original) {
        return Err((
            InvalidReason::NoChange,
            format!(
                "{} parses under the edited grammar to the same sentence as before the edits",
                site.describe()
            ),
        ));
    }
    Ok(replacement)
}

/// The edits and rows of the rules a grammar mutation edits beside its grammar edits (module
/// documentation, "Grammar edits"). Each edited rule's text is parsed under the mutant's grammar,
/// the baseline patched by `grammar_patch`: k-rust's `parse_rule_content` at the rule's module,
/// the parse the load makes of every rule bubble with its module's rule grammar. That reading is
/// checked on the baseline first: the rule's text before the edits, parsed so under the
/// specification's grammar, must be the loaded rule up to positions (else `unread-declaration`).
/// An edited rule that does not parse under the mutant's grammar is `edited-load-failed`; one
/// that is no longer one rule is `structure-changed`; a changed label `label-changed`; a rule
/// equal to the baseline's up to positions `no-change`. A replacement carries the baseline
/// rule's position keys, a deleted rule is a `DeleteSentence`; every other rule keeps the
/// specification's terms.
fn rule_patch_edits(
    baseline: &Baseline,
    grammar_patch: &Patch,
    bubbles: &[EditedBubble],
    groups: &BTreeMap<(String, usize), Vec<&TextEdit>>,
    views: &mut Views<'_>,
    authored: &[Authored<'_>],
    edited_files: &BTreeMap<String, EditedFile>,
) -> Result<(Vec<Edit>, Vec<EditedRule>), InvalidMutation> {
    let rejected = |detail: String| InvalidMutation {
        edit: None,
        reason: InvalidReason::PatchRejected,
        detail,
    };
    let specification = ResolvedDefinition::resolve(baseline.definition())
        .map_err(|e| rejected(format!("the specification does not resolve: {e}")))?;
    let mutant = kink_patch::apply(baseline, grammar_patch).map_err(|e| rejected(e.to_string()))?;
    let grammar =
        ResolvedDefinition::resolve(mutant.definition()).map_err(|e| InvalidMutation {
            edit: None,
            reason: InvalidReason::EditedLoadFailed,
            detail: format!("the edited grammar does not resolve: {e}"),
        })?;
    let mut edits = Vec::new();
    let mut rows = Vec::new();
    for bubble in bubbles {
        let group = &groups[&(bubble.file.clone(), bubble.start)];
        let edit = group[0].edit;
        let at = &group[0].at;
        let site = authored
            .iter()
            .find(|a| a.at == *at)
            .expect("an addressed rule is authored");
        let original = baseline
            .sentence(at)
            .expect("an addressed rule is a baseline sentence");
        let fail = |reason, detail: String| InvalidMutation {
            edit: Some(edit),
            reason,
            detail,
        };
        let unread = || {
            fail(
                InvalidReason::UnreadDeclaration,
                format!(
                    "{}: k-rust's outer lowering of its text, parsed with its module's rule \
                     grammar, is not the loaded rule",
                    site.describe()
                ),
            )
        };
        let (contents, attributes) =
            rule_bubble_parts(&bubble.before, &bubble.file).ok_or_else(unread)?;
        let read = parse_rule_content(&specification, &bubble.module, contents, attributes)
            .map_err(|_| unread())?;
        if !fingerprint_equal(&with_baseline_positions(&read, original), original) {
            return Err(unread());
        }
        let view = views
            .view(&bubble.file)
            .map_err(|(reason, detail)| fail(reason, detail))?;
        let before = view.text[view_span(original, &view.text, &site.describe())
            .map_err(|detail| fail(InvalidReason::NoUsableSpan, detail))?]
        .to_owned();
        let after = match &bubble.after {
            None => {
                edits.push(Edit::DeleteSentence { at: at.clone() });
                None
            }
            Some((declaration, sentences)) => {
                let replacement = edited_rule(&grammar, bubble, sentences, original, site)
                    .map_err(|(reason, detail)| fail(reason, detail))?;
                edits.push(Edit::ReplaceSentence {
                    at: at.clone(),
                    replacement,
                });
                Some(edited_files[&bubble.file].edited_view[declaration.span.clone()].to_owned())
            }
        };
        let location = site.location.expect("an addressed rule has a location");
        let mut indices = group.iter().map(|e| e.edit).collect::<Vec<_>>();
        indices.sort_unstable();
        rows.push(EditedRule {
            at: at.clone(),
            kind: EditedKind::Rule,
            edits: indices,
            file: bubble.file.clone(),
            label: site.label().map(str::to_owned),
            start_line: location.start_line,
            end_line: location.end_line,
            before,
            after,
        });
    }
    Ok((edits, rows))
}

/// The pinned patch of a grammar mutation's `edits`, once it applies (`edited-load-failed` for a
/// definition that does not resolve) and its mutant gives a program parser for the syntax module
/// (`no-program-parser`).
fn admitted_patch(
    loaded: &LoadedSource,
    edits: Vec<Edit>,
    whole: Option<usize>,
) -> Result<Patch, InvalidMutation> {
    let baseline = &loaded.baseline;
    let fail = |reason, detail: String| InvalidMutation {
        edit: whole,
        reason,
        detail,
    };
    let rejected = |detail: String| InvalidMutation {
        edit: None,
        reason: InvalidReason::PatchRejected,
        detail,
    };
    let patch = Patch::new(edits)
        .map_err(|e| rejected(e.to_string()))?
        .pinned(baseline)
        .map_err(|e| rejected(e.to_string()))?;
    let mutant = kink_patch::apply(baseline, &patch).map_err(|failure| {
        if failure.kind() == PatchFailureKind::LocallyIllFormed {
            fail(InvalidReason::EditedLoadFailed, failure.to_string())
        } else {
            rejected(failure.to_string())
        }
    })?;
    mutant
        .program_parser(loaded.syntax_module())
        .map_err(|failure| {
            fail(
                InvalidReason::NoProgramParser,
                format!(
                    "the edited grammar gives no program parser for {}: {failure}",
                    loaded.syntax_module()
                ),
            )
        })?;
    Ok(patch)
}

/// Every source file's outer syntax before and after the edits (the edited views in place of the
/// edited files), in the load's file order, and every declaration paired before and after.
#[allow(clippy::type_complexity)]
fn read_files(
    loaded: &LoadedSource,
    views: &mut Views<'_>,
    edited_files: &BTreeMap<String, EditedFile>,
    groups: &BTreeMap<(String, usize), Vec<&TextEdit>>,
    whole: Option<usize>,
) -> Result<
    (
        Vec<outer::SourceFile>,
        Vec<outer::SourceFile>,
        Vec<DeclarationPair>,
    ),
    InvalidMutation,
> {
    let from_view = |(reason, detail)| InvalidMutation {
        edit: None,
        reason,
        detail,
    };
    let fail = |reason, detail: String| InvalidMutation {
        edit: whole,
        reason,
        detail,
    };
    let names = loaded
        .files
        .iter()
        .map(|f| f.name.clone())
        .collect::<Vec<_>>();
    let mut before_files = Vec::with_capacity(names.len());
    let mut after_files = Vec::with_capacity(names.len());
    let mut pairs = Vec::new();
    for name in &names {
        let (before, declarations) = views.parsed(name).map_err(from_view)?.clone();
        let Some(edited) = edited_files.get(name) else {
            pairs.extend(declarations.into_iter().map(|d| DeclarationPair {
                file: name.clone(),
                after: Some(d.clone()),
                before: d,
                edited: false,
            }));
            after_files.push(before.clone());
            before_files.push(before);
            continue;
        };
        let after = outer::parse(name.as_str(), &edited.edited_view).map_err(|e| {
            fail(
                InvalidReason::EditedLoadFailed,
                format!("{name}: k-rust's outer parser does not read the edited view: {e}"),
            )
        })?;
        pairs.extend(paired_declarations(
            name,
            &before,
            &declarations,
            &after,
            edited,
            groups,
            whole,
        )?);
        before_files.push(before);
        after_files.push(after);
    }
    Ok((before_files, after_files, pairs))
}

/// The edits of a grammar mutation (module documentation, "Grammar edits", 2 and 3): the files
/// before and after the edits are lowered as one source set each, every unedited declaration must
/// lower as before, and each edited declaration's baseline sentences, which must be its outer
/// lowering, are turned into its sentences after the edits ([`declaration_edits`]).
fn grammar_patch_edits(
    baseline: &Baseline,
    authored: &[Authored<'_>],
    before_files: &[outer::SourceFile],
    after_files: &[outer::SourceFile],
    pairs: &[DeclarationPair],
    groups: &BTreeMap<(String, usize), Vec<&TextEdit>>,
    whole: Option<usize>,
) -> Result<(Vec<Edit>, Vec<EditedBubble>), InvalidMutation> {
    let fail = |reason, detail: String| InvalidMutation {
        edit: whole,
        reason,
        detail,
    };
    // Lower every file as one source set, so that tags resolve across files.
    let main_module = &baseline.definition().main_module;
    let lowered_before = lower_all(before_files, main_module).map_err(|detail| {
        fail(
            InvalidReason::UnreadDeclaration,
            format!("the specification's declarations do not lower apart from its load: {detail}"),
        )
    })?;
    let lowered_after = lower_all(after_files, main_module).map_err(|detail| {
        fail(
            InvalidReason::EditedLoadFailed,
            format!("the edited declarations do not lower: {detail}"),
        )
    })?;
    let mut edits = Vec::new();
    let mut bubbles = Vec::new();
    let mut inserted = BTreeMap::<String, u32>::new();
    for module in &lowered_before.modules {
        let after_module = lowered_after
            .modules
            .iter()
            .find(|m| m.name == module.name)
            .ok_or_else(|| {
                fail(
                    InvalidReason::StructureChanged,
                    format!("module {} is gone after the edits", module.name),
                )
            })?;
        let in_module = pairs
            .iter()
            .filter(|pair| pair.before.module == module.name)
            .collect::<Vec<_>>();
        let before = by_declaration(&module.local_sentences, in_module.iter().map(|p| &p.before));
        let after = by_declaration(
            &after_module.local_sentences,
            in_module.iter().filter_map(|p| p.after.as_ref()),
        );
        let unchanged = |left: &[Arc<Sentence>], right: &[Arc<Sentence>]| {
            left.len() == right.len()
                && left.iter().zip(right).all(|(l, r)| fingerprint_equal(l, r))
        };
        if !unchanged(&before.loose, &after.loose) {
            return Err(fail(
                InvalidReason::StructureChanged,
                format!(
                    "module {} lowers to other sentences outside its declarations after the edits",
                    module.name
                ),
            ));
        }
        for pair in in_module {
            let old = before.of(&pair.before);
            let new = pair.after.as_ref().map(|d| after.of(d)).unwrap_or_default();
            if !pair.edited && pair.after.is_some() {
                if !unchanged(old, new) {
                    return Err(fail(
                        InvalidReason::StructureChanged,
                        format!(
                            "{} lowers to other sentences after the edits, although no edit \
                             addresses it",
                            pair.before.describe(&pair.file)
                        ),
                    ));
                }
                continue;
            }
            if !pair.before.grammar {
                // An edited rule: parsed under the mutant's grammar once the grammar's edits are
                // known ([`rule_patch_edits`]).
                bubbles.push(EditedBubble {
                    module: module.name.clone(),
                    file: pair.file.clone(),
                    start: pair.before.span.start,
                    before: old.to_vec(),
                    after: pair.after.clone().map(|d| (d, new.to_vec())),
                });
                continue;
            }
            let edit_of = groups
                .get(&(pair.file.clone(), pair.before.span.start))
                .and_then(|edits| edits.first())
                .map(|edit| edit.edit);
            let specification = read_as_loaded(authored, pair, old, edit_of)?;
            declaration_edits(
                baseline,
                &module.name,
                &specification,
                new,
                edit_of,
                &mut inserted,
                &mut edits,
            )?;
        }
    }
    Ok((edits, bubbles))
}

/// The loaded specification's sentences of the edited declaration of `pair`, which must be
/// `read`, its outer lowering (same count and order, equal fingerprints): else
/// `unread-declaration`.
fn read_as_loaded<'x>(
    authored: &'x [Authored<'x>],
    pair: &DeclarationPair,
    read: &[Arc<Sentence>],
    edit: Option<usize>,
) -> Result<Vec<&'x Authored<'x>>, InvalidMutation> {
    let specification = declared(authored, &pair.file, &pair.before);
    if specification.len() == read.len()
        && specification
            .iter()
            .zip(read)
            .all(|(a, r)| fingerprint_equal(a.sentence, r))
    {
        return Ok(specification);
    }
    Err(InvalidMutation {
        edit,
        reason: InvalidReason::UnreadDeclaration,
        detail: format!(
            "the loaded specification's sentences of {} are not what k-rust's outer lowering \
             reads from its text ({} loaded, {} read)",
            pair.before.describe(&pair.file),
            specification.len(),
            read.len()
        ),
    })
}

/// The declarations of one edited file paired before and after the edits: the edited file must
/// have the baseline's modules and the baseline's declarations less the deleted ones, of the same
/// kinds, each unedited one where the edits move it and each edited one starting where they move
/// its start and ending where they move its end, or earlier by whitespace only.
fn paired_declarations(
    name: &str,
    before: &outer::SourceFile,
    declarations: &[Declaration],
    after: &outer::SourceFile,
    edited: &EditedFile,
    groups: &BTreeMap<(String, usize), Vec<&TextEdit>>,
    whole: Option<usize>,
) -> Result<Vec<DeclarationPair>, InvalidMutation> {
    let changed = |reason, detail: String| InvalidMutation {
        edit: whole,
        reason,
        detail,
    };
    if !same_modules(before, after) {
        return Err(changed(
            InvalidReason::StructureChanged,
            format!("the modules, imports or requires of {name} changed outside its declarations"),
        ));
    }
    let edits_of = |d: &Declaration| groups.get(&(name.to_owned(), d.span.start));
    let deleted = |d: &Declaration| {
        edits_of(d).is_some_and(|edits| edits.iter().any(|e| e.replacement.is_none()))
    };
    let after_declarations = declarations_of(after);
    let kept = declarations.iter().filter(|d| !deleted(d)).count();
    if kept != after_declarations.len() {
        return Err(changed(
            InvalidReason::StructureChanged,
            format!(
                "{name} has {} declarations after the edits, not {kept}: an edit split, merged, \
                 added or removed a declaration",
                after_declarations.len()
            ),
        ));
    }
    let mut next = after_declarations.into_iter();
    let mut pairs = Vec::with_capacity(declarations.len());
    for declaration in declarations {
        let edits = edits_of(declaration);
        if deleted(declaration) {
            pairs.push(DeclarationPair {
                file: name.to_owned(),
                before: declaration.clone(),
                after: None,
                edited: true,
            });
            continue;
        }
        let new = next.next().expect("counted above");
        let what = declaration.describe(name);
        let edit = edits
            .and_then(|e| e.first())
            .map_or(whole, |e| Some(e.edit));
        if new.module != declaration.module || new.kind != declaration.kind {
            return Err(InvalidMutation {
                edit,
                reason: InvalidReason::StructureChanged,
                detail: format!(
                    "{what} is a {} declaration of module {} after the edits",
                    new.kind, new.module
                ),
            });
        }
        let start = edited.moved(declaration.span.start);
        let end = edited.moved(declaration.span.end);
        let end_holds = match (edits, end) {
            (_, None) => false,
            (Some(_), Some(end)) => {
                new.span.end <= end
                    && edited
                        .edited_view
                        .get(new.span.end..end)
                        .is_some_and(|gap| gap.chars().all(char::is_whitespace))
            }
            (None, Some(end)) => new.span.end == end,
        };
        if start != Some(new.span.start) || !end_holds {
            return Err(InvalidMutation {
                edit,
                reason: InvalidReason::SpanChanged,
                detail: format!(
                    "{what} spans bytes {}..{} of the edited K view of {name}, not where the edits \
                     move it ({}..{}): the edits changed text outside the declarations they edit",
                    new.span.start,
                    new.span.end,
                    start.map_or_else(|| "?".to_owned(), |s| s.to_string()),
                    end.map_or_else(|| "?".to_owned(), |e| e.to_string())
                ),
            });
        }
        pairs.push(DeclarationPair {
            file: name.to_owned(),
            before: declaration.clone(),
            after: Some(new),
            edited: edits.is_some(),
        });
    }
    Ok(pairs)
}

/// Whether two readings of a file have the same modules (names, attributes, imports) and requires.
fn same_modules(before: &outer::SourceFile, after: &outer::SourceFile) -> bool {
    let modules = |file: &outer::SourceFile| {
        file.modules
            .iter()
            .map(|m| {
                (
                    m.name.clone(),
                    m.attributes.clone(),
                    m.imports
                        .iter()
                        .map(|i| (i.module.clone(), i.public))
                        .collect::<Vec<_>>(),
                )
            })
            .collect::<Vec<_>>()
    };
    let requires = |file: &outer::SourceFile| {
        file.requires
            .iter()
            .map(|r| r.path.clone())
            .collect::<Vec<_>>()
    };
    modules(before) == modules(after) && requires(before) == requires(after)
}

/// k-rust's outer lowering of `files` as one source set: one tag index over all of them, as the
/// load builds it. Only each sentence's module and offsets are read from the result, so every
/// sentence naming one source is harmless. `Err` holds k-rust's diagnostics.
fn lower_all(files: &[outer::SourceFile], main_module: &str) -> Result<Definition, String> {
    let combined = outer::SourceFile {
        source: "kink-flow:grammar-edit".to_owned(),
        source_id: files.first().map_or(SourceId(0), |f| f.source_id),
        requires: Vec::new(),
        modules: files
            .iter()
            .flat_map(|f| f.modules.iter().cloned())
            .collect(),
    };
    outer::lower(&combined, main_module).map_err(|diagnostics| {
        diagnostics
            .iter()
            .map(|d| d.message.clone())
            .collect::<Vec<_>>()
            .join("; ")
    })
}

/// A module's lowered sentences by the declaration whose span holds their start offset, in
/// [`kind_rank`] order within a declaration; `loose` holds those with no offset.
#[derive(Default)]
struct Lowered {
    by_start: BTreeMap<usize, Vec<Arc<Sentence>>>,
    loose: Vec<Arc<Sentence>>,
}

impl Lowered {
    fn of(&self, declaration: &Declaration) -> &[Arc<Sentence>] {
        self.by_start
            .get(&declaration.span.start)
            .map_or(&[], Vec::as_slice)
    }
}

fn by_declaration<'d>(
    sentences: &[Arc<Sentence>],
    declarations: impl Iterator<Item = &'d Declaration>,
) -> Lowered {
    let declarations = declarations.collect::<Vec<_>>();
    let mut lowered = Lowered::default();
    for sentence in sentences {
        let holder = offsets(sentence).and_then(|span| {
            declarations
                .iter()
                .find(|d| d.span.start <= span.start && span.start < d.span.end)
        });
        match holder {
            Some(declaration) => lowered
                .by_start
                .entry(declaration.span.start)
                .or_default()
                .push(sentence.clone()),
            None => lowered.loose.push(sentence.clone()),
        }
    }
    for list in lowered.by_start.values_mut() {
        list.sort_by_key(|s| {
            let span = offsets(s).unwrap_or_default();
            (span.start, span.end, kind_rank(s))
        });
    }
    lowered
}

/// The labels of the paired productions `pairs` (baseline sentence, index into `edited`): a
/// declared label is the constructor's name and must not change (`label-changed`); a label K
/// derives from the literals is kept as the baseline's in `edited`, in the production and in the
/// declaration's priority and associativity tags (`structure-changed` when another production
/// already has the derived label).
fn keep_derived_labels(
    baseline: &Baseline,
    pairs: &[(&Authored<'_>, usize)],
    edited: &mut [Sentence],
    edit: Option<usize>,
) -> Result<(), InvalidMutation> {
    let invalid = |reason, detail: String| InvalidMutation {
        edit,
        reason,
        detail,
    };
    let mut renamed = BTreeMap::<String, String>::new();
    for (old, i) in pairs {
        let (
            Sentence::Production {
                label: old_label, ..
            },
            Sentence::Production {
                label: new_label, ..
            },
        ) = (old.sentence, &edited[*i])
        else {
            continue;
        };
        let (old_name, new_name) = (
            old_label.as_ref().map(|l| l.name.clone()),
            new_label.as_ref().map(|l| l.name.clone()),
        );
        if old_name == new_name {
            continue;
        }
        if declares_label(old.sentence) || declares_label(&edited[*i]) {
            return Err(invalid(
                InvalidReason::LabelChanged,
                format!(
                    "the edit changes the name of {} to {}: a grammar edit changes which text \
                     parses to a constructor, not the constructor's declared name",
                    old.describe(),
                    new_name.as_deref().unwrap_or("none")
                ),
            ));
        }
        if let (Some(old_name), Some(new_name)) = (old_name, new_name) {
            renamed.insert(new_name, old_name);
        }
    }
    let labels = baseline
        .definition()
        .modules
        .iter()
        .flat_map(|m| &m.local_sentences)
        .filter_map(|s| match s.as_ref() {
            Sentence::Production {
                label: Some(label), ..
            } => Some(label.name.clone()),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    for (new_name, old_name) in &renamed {
        let twice = edited
            .iter()
            .filter(
                |s| matches!(s, Sentence::Production { label: Some(l), .. } if l.name == *new_name),
            )
            .count();
        if labels.contains(new_name) || twice > 1 {
            return Err(invalid(
                InvalidReason::StructureChanged,
                format!(
                    "after the edit, the production K labels {old_name} derives the label \
                     {new_name}, which another production has"
                ),
            ));
        }
    }
    if !renamed.is_empty() {
        let rename = |tag: &mut String| {
            if let Some(old) = renamed.get(tag.as_str()) {
                tag.clone_from(old);
            }
        };
        for sentence in edited.iter_mut() {
            match sentence {
                Sentence::Production {
                    label: Some(label), ..
                } => rename(&mut label.name),
                Sentence::SyntaxPriority { priorities, .. } => {
                    priorities.iter_mut().flatten().for_each(rename);
                }
                Sentence::SyntaxAssociativity { tags, .. } => tags.iter_mut().for_each(rename),
                _ => {}
            }
        }
    }
    Ok(())
}

/// Pairs the baseline sentences of kind `rank` with the edited ones: first each with the first
/// unpaired edited sentence `same` holds for, then the rest in order; the unpaired ones of each
/// side are pushed to `extra_old` and `extra_new`.
fn pair_kind<'x>(
    specification: &[&'x Authored<'x>],
    edited: &[Sentence],
    rank: u8,
    same: impl Fn(&Sentence, &Sentence) -> bool,
    pairs: &mut Vec<(&'x Authored<'x>, usize)>,
    extra_old: &mut Vec<&'x Authored<'x>>,
    extra_new: &mut Vec<usize>,
) {
    let old = specification
        .iter()
        .copied()
        .filter(|a| kind_rank(a.sentence) == rank)
        .collect::<Vec<_>>();
    let mut free = (0..edited.len())
        .filter(|i| kind_rank(&edited[*i]) == rank)
        .collect::<Vec<_>>();
    let mut unpaired = Vec::new();
    for a in old {
        match free.iter().position(|i| same(a.sentence, &edited[*i])) {
            Some(k) => pairs.push((a, free.remove(k))),
            None => unpaired.push(a),
        }
    }
    let mut free = free.into_iter();
    for a in unpaired {
        match free.next() {
            Some(i) => pairs.push((a, i)),
            None => extra_old.push(a),
        }
    }
    extra_new.extend(free);
}

/// Whether a production declares its label (`symbol` or `klabel`), rather than K deriving it from
/// its text.
fn declares_label(sentence: &Sentence) -> bool {
    sentence.attributes().has(AttributeKey::Symbol)
        || sentence.attributes().has(AttributeKey::Klabel)
}

/// The edits that turn the baseline sentences `specification` of one declaration of `module`
/// into `edited`, its sentences after the edits: paired by kind in order, a pair that differs is
/// replaced, an unpaired baseline sentence deleted, an unpaired edited one inserted at the
/// module's end. A production whose label neither side declares keeps the baseline's, and the
/// declaration's priority and associativity tags name it by that label (module documentation).
fn declaration_edits(
    baseline: &Baseline,
    module: &str,
    specification: &[&Authored<'_>],
    edited: &[Arc<Sentence>],
    edit: Option<usize>,
    inserted: &mut BTreeMap<String, u32>,
    edits: &mut Vec<Edit>,
) -> Result<(), InvalidMutation> {
    let mut edited = edited.iter().map(|s| (**s).clone()).collect::<Vec<_>>();
    // Productions pair by label, then in order; the rest of a kind by equality (after the
    // labels below), then in order.
    let mut pairs = Vec::new();
    let mut extra_old = Vec::new();
    let mut extra_new = Vec::new();
    let label_of = |sentence: &Sentence| match sentence {
        Sentence::Production { label, .. } => label.as_ref().map(|l| l.name.clone()),
        _ => None,
    };
    pair_kind(
        specification,
        &edited,
        0,
        |old, new| label_of(old).is_some() && label_of(old) == label_of(new),
        &mut pairs,
        &mut extra_old,
        &mut extra_new,
    );
    keep_derived_labels(baseline, &pairs, &mut edited, edit)?;
    for rank in 1..=4 {
        pair_kind(
            specification,
            &edited,
            rank,
            |old, new| fingerprint_equal(new, old),
            &mut pairs,
            &mut extra_old,
            &mut extra_new,
        );
    }
    for (old, i) in pairs {
        if !fingerprint_equal(&edited[i], old.sentence) {
            edits.push(Edit::ReplaceSentence {
                at: old.at.clone(),
                replacement: with_baseline_positions(&edited[i], old.sentence),
            });
        }
    }
    for old in extra_old {
        edits.push(Edit::DeleteSentence { at: old.at.clone() });
    }
    for i in extra_new {
        let mut sentence = edited[i].clone();
        for key in POSITION_KEYS {
            sentence.attributes_mut().remove(key.as_str());
        }
        let ordinal = inserted.entry(module.to_owned()).or_default();
        edits.push(Edit::InsertSentence {
            position: InsertPosition::ModuleEnd(module.to_owned()),
            ordinal: *ordinal,
            sentence,
        });
        *ordinal += 1;
    }
    Ok(())
}

/// The detail of an `edited-rule-too-deep` refusal of `patch`, whose document nests `depth` levels,
/// past kink's limit `limit` (re-pin L1-3-tail, review L1-3-fix-2-1 D4). A patch holds each edited
/// rule whole, so the advice is about the rule as a whole: the deepest replaced rule's depth as
/// edited and in the specification, and, when the specification's rule alone already makes a
/// patch past the limit, that no mutation that keeps the rule's deep part can be judged in this
/// build (review L1-3-tail-1 D4: one that replaces the deep part by a shallow one has a shallow
/// patch).
fn too_deep_detail(
    baseline: &kink_patch::Baseline,
    patch: &Patch,
    rules: &[EditedRule],
    depth: usize,
    limit: usize,
) -> String {
    // The document depth of the one-edit patch that replaces `at` by `sentence`.
    let document_depth = |at: &SentenceRef, sentence: &Sentence| {
        Patch::new(vec![Edit::ReplaceSentence {
            at: at.clone(),
            replacement: sentence.clone(),
        }])
        .ok()
        .and_then(|patch| patch.document_depth().ok())
        .unwrap_or(0)
    };
    let deepest = patch
        .edits()
        .iter()
        .filter_map(|edit| match edit {
            Edit::ReplaceSentence { at, replacement } => {
                let original = baseline.sentence(at)?;
                Some((
                    at,
                    replacement,
                    original,
                    document_depth(at, replacement),
                    document_depth(at, original),
                ))
            }
            _ => None,
        })
        .max_by_key(|(_, _, _, edited, original)| (*original > limit, *edited));
    let limit_text = format!(
        "kink's limit of {limit} in this build (kink-patch MAX_JSON_DEPTH; a patch holds each \
         edited rule whole, about two JSON levels per term level)"
    );
    let Some((at, edited, original, _, original_depth)) = deepest else {
        return format!(
            "the patch's JSON nests {depth} levels, more than {limit_text}; this is kink's limit, \
             not a fault of the mutation"
        );
    };
    let name = rules
        .iter()
        .find(|rule| &rule.at == at)
        .and_then(|rule| rule.label.as_deref())
        .map_or_else(
            || format!("sentence {} of module {}", at.index, at.module),
            |label| format!("[{label}]"),
        );
    let (edited_levels, original_levels) = (
        kink_patch::sentence_depth(edited),
        kink_patch::sentence_depth(original),
    );
    if original_depth > limit {
        format!(
            "the rule {name} nests {original_levels} term levels in the specification, so the \
             patch of a mutation that keeps the rule's deep part nests at least {original_depth} \
             JSON levels, more than {limit_text}: no mutation that keeps the rule's deep part can \
             be judged in this build, whatever else it changes (only one that replaces that part \
             by a shallow one has a patch within the limit); this is kink's limit, not a fault of \
             the mutation or of the rule"
        )
    } else {
        format!(
            "the rule {name} as edited nests {edited_levels} term levels as a whole (the \
             specification's rule {original_levels}), so the patch's JSON nests {depth} levels, \
             more than {limit_text}; this is kink's limit, not a fault of the mutation: a \
             mutation that leaves the whole rule within about {} term levels is judged",
            limit / 2
        )
    }
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
    /// and at k-rust 501f18b9 the extractor writes every character of the fence line itself
    /// (backticks and info string) as one space (re-pin finding E-09), so the shift is the
    /// length of the fence and its info string (`` ```k ``: 4). Only the first line grows, so
    /// one constant shift maps every later offset.
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

/// How an anchor names a stored label ([`label_match`]).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LabelMatch {
    /// The anchor is the label: the stored label itself, or its module-qualified form.
    Exact,
    /// The anchor is a suffix of the label made of whole components.
    Suffix,
}

/// Whether the anchor `rule = anchor` names the label `stored` of a sentence of module `module`.
///
/// K stores `rule [x]:` as `MODULE.x` and `[label(x)]` as the bare `x`, and `x` and `MODULE.x`
/// name both forms in module `MODULE` (exact). Otherwise the anchor names the label when it is a
/// suffix of whole components of the label's module-qualified form, components being separated
/// by `.` (K's module qualification) or `--` (the separator of KRS's labels), so that `plus_zero`
/// names `nat--plus_zero` and `NAT.nat--plus_zero` but `zero` does not. The `MODULE.x` form
/// matches only a stored bare label (no `.`), so `MODULE.MODULE.x` does not name `MODULE.x`.
/// A resolution takes the exact and the suffix matches together and refuses anything but exactly
/// one, so no rule's label takes precedence over another's.
pub fn label_match(stored: &str, module: &str, anchor: &str) -> Option<LabelMatch> {
    if stored == anchor
        || stored == format!("{module}.{anchor}")
        || (!stored.contains('.') && anchor.strip_prefix(&format!("{module}.")) == Some(stored))
    {
        return Some(LabelMatch::Exact);
    }
    let qualified = qualified_label(stored, module);
    (!anchor.is_empty()
        && (qualified.ends_with(&format!("--{anchor}"))
            || qualified.ends_with(&format!(".{anchor}"))))
    .then_some(LabelMatch::Suffix)
}

/// The module-qualified form of the label `stored` of a sentence of module `module`: K's
/// `rule [x]:` label as stored (`MODULE.x`), a bare `[label(x)]` qualified (`MODULE.x`).
pub(crate) fn qualified_label(stored: &str, module: &str) -> String {
    if stored.contains('.') {
        stored.to_owned()
    } else {
        format!("{module}.{stored}")
    }
}

/// The labels an unknown anchor may have meant, for its refusal, compared by last component (the
/// text after the last `.` or `-`): a rule label is near when its last component is the anchor's
/// up to case and `_` (a respelling, `plusZero` to `plus_zero`), contains the anchor's, shares a
/// word of three or more characters with it (words are separated by `_`), or is within a third of
/// the anchor's length in edits of single characters (at least one). A moved item keeps its last
/// component (`nat--plus_zero` to `nat--arith--plus_zero`), a renamed item keeps most of its words
/// (`plus_succ` to `plus_step`), and a misspelt anchor is a few edits away. They are listed
/// respellings first, then containing, then by edit distance, then in byte order, at most five;
/// with none, the text says so, so that the refusal's next step can always point at the detail.
fn near_labels<'a>(labels: impl IntoIterator<Item = &'a str>, anchor: &str) -> String {
    let last_component = |text: &'_ str| -> String {
        text.rsplit(['.', '-'])
            .find(|part| !part.is_empty())
            .unwrap_or(text)
            .to_owned()
    };
    let last = last_component(anchor);
    let words = |text: &str| -> BTreeSet<String> {
        text.split('_')
            .filter(|word| word.chars().count() >= 3)
            .map(str::to_owned)
            .collect()
    };
    let folded = |text: &str| -> String {
        text.chars()
            .filter(|c| *c != '_')
            .flat_map(char::to_lowercase)
            .collect()
    };
    let anchor_words = words(&last);
    let anchor_folded = folded(&last);
    let limit = (last.chars().count() / 3).max(1);
    let mut near = labels
        .into_iter()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .filter_map(|label| {
            let component = last_component(label);
            let distance = edit_distance(&component, &last);
            let respelt = folded(&component) == anchor_folded;
            let contains = component.contains(last.as_str());
            let shares = !words(&component).is_disjoint(&anchor_words);
            (respelt || contains || shares || distance <= limit)
                .then_some((!respelt, !contains, distance, label))
        })
        .collect::<Vec<_>>();
    near.sort_unstable();
    if near.is_empty() {
        return format!(
            "; no label is {last:?} up to case and `_`, contains it, shares a word with it or is \
             within {limit} edit{} of it",
            if limit == 1 { "" } else { "s" }
        );
    }
    let shown = near
        .iter()
        .take(5)
        .map(|(_, _, _, label)| *label)
        .collect::<Vec<_>>()
        .join(", ");
    let more = near.len().saturating_sub(5);
    format!(
        "; near labels: {shown}{}",
        if more > 0 {
            format!(" and {more} more")
        } else {
            String::new()
        }
    )
}

/// The number of single-character insertions, deletions and substitutions that turn `left` into
/// `right` (Levenshtein distance), over characters.
fn edit_distance(left: &str, right: &str) -> usize {
    let right = right.chars().collect::<Vec<_>>();
    let mut previous = (0..=right.len()).collect::<Vec<_>>();
    for (i, a) in left.chars().enumerate() {
        let mut current = Vec::with_capacity(right.len() + 1);
        current.push(i + 1);
        for (j, b) in right.iter().enumerate() {
            let substitution = previous[j] + usize::from(a != *b);
            current.push(substitution.min(previous[j + 1] + 1).min(current[j] + 1));
        }
        previous = current;
    }
    previous[right.len()]
}

/// The most characters of a rule's text a `find-not-found` refusal quotes ([`excerpt`]).
pub(crate) const EXCERPT_CHARS: usize = 400;

/// The largest search for the text nearest a `find` ([`nearest_text`]), in cells of its table
/// (characters of `find` times characters searched): 16 million cells, well under a second,
/// cover a `find` of a hundred characters in a file of 160,000. A larger search is not made,
/// and the refusal says so, so that a refusal costs little whatever the sizes.
pub(crate) const NEAREST_TEXT_CELLS: usize = 16_000_000;

/// The text nearest a `find` that does not occur ([`nearest_text`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct NearestText {
    /// The byte range of the text in the searched string.
    pub(crate) range: Range<usize>,
    /// Its edit distance from `find`, in single-character insertions, deletions and
    /// substitutions.
    pub(crate) distance: usize,
}

/// The substring of `haystack` with the least edit distance from `needle` (single-character
/// insertions, deletions and substitutions, over characters), and that distance: the
/// approximate-substring form of [`edit_distance`], where the substring may start and end
/// anywhere at no cost. Of equally near substrings it is one whose length in characters is
/// nearest `needle`'s (`x + 2` rather than `x + ` for `x + 1`), and of those the one that ends
/// first; at each end the table keeps one start, reached by matching or substituting a character
/// before skipping one of `needle`, before skipping one of `haystack`. The answer is a function
/// of the two texts. `None` when either is empty or the search would take more than
/// [`NEAREST_TEXT_CELLS`] cells.
pub(crate) fn nearest_text(haystack: &str, needle: &str) -> Option<NearestText> {
    let needle = needle.chars().collect::<Vec<_>>();
    // The byte offset of each character of `haystack`, and its length.
    let offsets = haystack
        .char_indices()
        .map(|(offset, _)| offset)
        .chain([haystack.len()])
        .collect::<Vec<_>>();
    let cells = needle.len().checked_mul(offsets.len() - 1)?;
    if needle.is_empty() || haystack.is_empty() || cells > NEAREST_TEXT_CELLS {
        return None;
    }
    // `cost[i]` is the least distance of `needle[..i]` from a substring of `haystack` that ends
    // at the current character, and `start[i]` the index of that substring's first character.
    let mut cost = (0..=needle.len()).collect::<Vec<_>>();
    let mut start = vec![0; needle.len() + 1];
    let mut next_cost = Vec::with_capacity(needle.len() + 1);
    let mut next_start = Vec::with_capacity(needle.len() + 1);
    // The best substring's (distance, length gap) and character range.
    let mut best: Option<((usize, usize), Range<usize>)> = None;
    for (index, character) in haystack.chars().enumerate() {
        let end = index + 1;
        next_cost.clear();
        next_start.clear();
        next_cost.push(0);
        next_start.push(end);
        for (i, wanted) in needle.iter().enumerate() {
            let mut cell = (cost[i] + usize::from(*wanted != character), start[i]);
            if next_cost[i] + 1 < cell.0 {
                cell = (next_cost[i] + 1, next_start[i]);
            }
            if cost[i + 1] + 1 < cell.0 {
                cell = (cost[i + 1] + 1, start[i + 1]);
            }
            next_cost.push(cell.0);
            next_start.push(cell.1);
        }
        std::mem::swap(&mut cost, &mut next_cost);
        std::mem::swap(&mut start, &mut next_start);
        let from = start[needle.len()];
        let key = (cost[needle.len()], (end - from).abs_diff(needle.len()));
        if best.as_ref().is_none_or(|(best, _)| key < *best) {
            best = Some((key, from..end));
        }
    }
    best.map(|((distance, _), range)| NearestText {
        range: offsets[range.start]..offsets[range.end],
        distance,
    })
}

/// `text` as a refusal quotes it (`{:?}`, so a quoted text is one line, and a TOML basic string
/// holds it as printed when it has no control character but tab, carriage return and line feed): whole when it has at most [`EXCERPT_CHARS`] characters, else that many
/// characters from the start of the line holding the byte `focus`, marked `...` where cut.
pub(crate) fn excerpt(text: &str, focus: usize) -> String {
    if text.chars().count() <= EXCERPT_CHARS {
        return format!("{text:?}");
    }
    let from = text[..focus].rfind('\n').map_or(0, |newline| newline + 1);
    let to = text[from..]
        .char_indices()
        .nth(EXCERPT_CHARS)
        .map_or(text.len(), |(offset, _)| from + offset);
    format!(
        "{}{:?}{}",
        if from > 0 { "..." } else { "" },
        &text[from..to],
        if to < text.len() { "..." } else { "" }
    )
}

/// What a `find-not-found` refusal adds to its detail so that the edit is re-anchored in one
/// look: the text of `scope` (a byte range of the K view `text` of `file`) nearest `find`
/// ([`nearest_text`]) with its line, when its distance is within a third of `find`'s length in
/// characters (at least one) and below that length (some character of `find` is kept), the rule
/// that [`near_labels`] applies to labels; and, for the addressed rule's text (`rule`), that text
/// ([`excerpt`], from the nearest text's line when it is long). It suggests and changes nothing:
/// a respelled text need not be the text the mutation meant, so the author chooses.
fn find_hint(text: &str, scope: Range<usize>, find: &str, file: &str, rule: bool) -> String {
    let what = if rule { "the rule" } else { file };
    let searched = &text[scope.clone()];
    let length = find.chars().count();
    let limit = (length / 3).max(1);
    let plural = |n: usize| if n == 1 { "" } else { "s" };
    let nearest = nearest_text(searched, find);
    let searched_whole = nearest.is_some();
    let close = nearest.filter(|near| near.distance <= limit && near.distance < length);
    let mut hint = match (&close, searched_whole) {
        (Some(near), _) => {
            let line = |offset: usize| 1 + text[..scope.start + offset].matches('\n').count();
            let (first, last) = (line(near.range.start), line(near.range.end));
            format!(
                "; nearest text, {} edit{} from find, at {file}:{first}{}: {:?}",
                near.distance,
                plural(near.distance),
                if last > first {
                    format!("-{last}")
                } else {
                    String::new()
                },
                &searched[near.range.clone()]
            )
        }
        (None, true) => format!(
            "; no text of {what} is within {limit} edit{} of find",
            plural(limit)
        ),
        (None, false) => format!("; {what} is too long to search for the text nearest find"),
    };
    if rule {
        let focus = close.map_or(0, |near| near.range.start);
        hint.push_str(&format!(
            "; the rule's text now: {}",
            excerpt(searched, focus)
        ));
    }
    hint
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
            // Exact and suffix matches are one candidate set, and the anchor must name exactly
            // one rule. An exact match does not take precedence: a stored anchor is replayed
            // after every edit of the specification, and a precedence would move a suffix anchor
            // silently onto a rule that comes to have the anchor as its whole label, where this
            // refuses it. The module-qualified label is the fullest anchor of a rule.
            let matches = authored
                .iter()
                .filter(|a| {
                    a.label()
                        .is_some_and(|l| label_match(l, &a.at.module, label).is_some())
                })
                .collect::<Vec<_>>();
            match matches.as_slice() {
                [] => {
                    return Err(invalid(
                        InvalidReason::UnknownLabel,
                        format!(
                            "no rule is labelled {label:?}, and no label ends with it as a whole \
                             component{}",
                            near_labels(
                                authored
                                    .iter()
                                    .filter(|a| a.is_rule())
                                    .filter_map(Authored::label),
                                label
                            )
                        ),
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
                            "{label:?} names several labels, as the label itself or as a suffix \
                             of its components: {}; write more of the label, such as the \
                             module-qualified label given for each",
                            several
                                .iter()
                                .map(|a| format!(
                                    "{} as {:?}",
                                    a.describe(),
                                    qualified_label(a.label().unwrap_or_default(), &a.at.module)
                                ))
                                .collect::<Vec<_>>()
                                .join(", ")
                        ),
                    ));
                }
            }
        }
    };
    let by_production = match &edit.production {
        None => None,
        Some(name) => {
            // As for `rule`: exact and suffix matches are one candidate set.
            let productions = authored
                .iter()
                .filter(|a| a.production_name().is_some())
                .collect::<Vec<_>>();
            let matches = productions
                .iter()
                .copied()
                .filter(|a| {
                    a.production_name()
                        .is_some_and(|n| label_match(n, &a.at.module, name).is_some())
                })
                .collect::<Vec<_>>();
            match matches.as_slice() {
                [] => {
                    return Err(invalid(
                        InvalidReason::UnknownLabel,
                        format!(
                            "no production is named {name:?} (its `symbol`, `klabel` or the label \
                             K derives from its text), and no name ends with it as a whole \
                             component{}",
                            near_labels(
                                productions.iter().filter_map(|a| a.production_name()),
                                name
                            )
                        ),
                    ));
                }
                [one] => Some(*one),
                several => {
                    return Err(invalid(
                        InvalidReason::AmbiguousLabel,
                        format!(
                            "{name:?} names several productions, as the name itself or as a \
                             suffix of its components: {}; write more of the name, such as the \
                             module-qualified name given for each",
                            several
                                .iter()
                                .map(|a| format!(
                                    "{} as {:?}",
                                    a.describe(),
                                    qualified_label(
                                        a.production_name().unwrap_or_default(),
                                        &a.at.module
                                    )
                                ))
                                .collect::<Vec<_>>()
                                .join(", ")
                        ),
                    ));
                }
            }
        }
    };
    let anchor = by_label.or(by_production);
    if let (Some(file), Some(rule)) = (&file, anchor)
        && rule.file != Some(file.as_str())
    {
        return Err(invalid(
            InvalidReason::AddressMismatch,
            format!("{} is not in {file}", rule.describe()),
        ));
    }
    let file = match (file, anchor) {
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
            let mut grammar = || -> Result<Option<Declaration>, InvalidMutation> {
                Ok(views
                    .parsed(&file)
                    .map_err(from_views)?
                    .1
                    .iter()
                    .find(|d| d.grammar && d.start_line <= line && line <= d.end_line)
                    .cloned())
            };
            match (covering_rules.as_slice(), covering.as_slice()) {
                ([one], _) => Some(LineHit::Rule(one)),
                ([], _) if let Some(declaration) = grammar()? => {
                    Some(LineHit::Grammar(declaration))
                }
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
    // A grammar edit: the production `production` names, or the grammar declaration the line
    // lies in.
    let line_declaration = match &by_line {
        Some(LineHit::Grammar(declaration)) => Some(declaration.clone()),
        _ => None,
    };
    if let Some(production) = by_production {
        let declaration = declaration_of(views, &file, production).map_err(from_views)?;
        let declaration = declaration.ok_or_else(|| {
            invalid(
                InvalidReason::NonRuleSentence,
                format!(
                    "{} lies in no grammar declaration of {file}: a configuration or another \
                     sentence declares it",
                    production.describe()
                ),
            )
        })?;
        if let Some(line) = edit.line
            && line_declaration.as_ref() != Some(&declaration)
        {
            return Err(invalid(
                InvalidReason::AddressMismatch,
                format!(
                    "production {:?} is {}, declared by {}, but line {line} is not in that \
                     declaration",
                    edit.production.as_deref().unwrap_or_default(),
                    production.describe(),
                    declaration.describe(&file)
                ),
            ));
        }
        let text = &views.view(&file).map_err(from_views)?.text;
        return grammar_edit(index, edit, file.clone(), declaration, production, text);
    }
    if let Some(declaration) = line_declaration {
        if let Some(rule) = by_label {
            return Err(invalid(
                InvalidReason::AddressMismatch,
                format!(
                    "rule {:?} is {}, but line {} is in {}",
                    edit.rule.as_deref().unwrap_or_default(),
                    rule.describe(),
                    edit.line.unwrap_or_default(),
                    declaration.describe(&file)
                ),
            ));
        }
        let line = edit.line.unwrap_or_default();
        let item = grammar_item(authored, &file, &declaration, |a| a.covers(line))
            .ok_or_else(|| unread_item(index, &file, &declaration))?;
        let text = &views.view(&file).map_err(from_views)?.text;
        return grammar_edit(index, edit, file.clone(), declaration, item, text);
    }
    let by_line = match by_line {
        Some(LineHit::Rule(rule)) => Some(rule),
        _ => None,
    };
    // A `find` alone may lie in a grammar declaration (read below, after the view is borrowed).
    let declarations = if by_label.or(by_line).is_none() {
        Some(views.parsed(&file).map_err(from_views)?.1.clone())
    } else {
        None
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
                        format!(
                            "{find:?} does not occur in {}{}",
                            rule.describe(),
                            find_hint(text, span, find, &file, true)
                        ),
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
                        format!(
                            "{find:?} does not occur in {file}{}",
                            find_hint(text, 0..text.len(), find, &file, false)
                        ),
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
            let in_grammar = declarations
                .iter()
                .flatten()
                .find(|d| d.grammar && d.contains(&range));
            match (containing_rules.as_slice(), containing.as_slice()) {
                ([one], _) => {
                    span_of(one)?;
                    (*one, range)
                }
                ([], _) if let Some(declaration) = in_grammar => {
                    let item = grammar_item(authored, &file, declaration, |a| {
                        sentence_span(a.sentence, text)
                            .is_some_and(|s| s.start <= range.start && range.end <= s.end)
                    })
                    .ok_or_else(|| unread_item(index, &file, declaration))?;
                    return grammar_edit(
                        index,
                        edit,
                        file.clone(),
                        declaration.clone(),
                        item,
                        text,
                    );
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
        declaration: None,
    })
}

/// What a `line` names: the rule covering it, or the grammar declaration it lies in.
enum LineHit<'x> {
    Rule(&'x Authored<'x>),
    Grammar(Declaration),
}

/// The grammar declaration of `file` that holds the production `production` (by its offsets).
fn declaration_of(
    views: &mut Views<'_>,
    file: &str,
    production: &Authored<'_>,
) -> Result<Option<Declaration>, (InvalidReason, String)> {
    let Some(span) = offsets(production.sentence) else {
        return Ok(None);
    };
    Ok(views
        .parsed(file)?
        .1
        .iter()
        .find(|d| d.grammar && d.module == production.at.module && d.contains(&span))
        .cloned())
}

/// The baseline sentences `declaration` of `file` lowers to (by their offsets), in text order.
fn declared<'x>(
    authored: &'x [Authored<'x>],
    file: &str,
    declaration: &Declaration,
) -> Vec<&'x Authored<'x>> {
    let mut declared = authored
        .iter()
        .filter(|a| a.file == Some(file) && a.at.module == declaration.module)
        .filter(|a| offsets(a.sentence).is_some_and(|s| declaration.contains(&s)))
        .collect::<Vec<_>>();
    declared.sort_by_key(|a| {
        let span = offsets(a.sentence).unwrap_or_default();
        (span.start, span.end, kind_rank(a.sentence), a.at.index)
    });
    declared
}

/// The item a grammar edit names in `declaration`: the one production `holds` admits, else the
/// declaration's first sentence; `None` when the declaration lowers to no baseline sentence.
fn grammar_item<'x>(
    authored: &'x [Authored<'x>],
    file: &str,
    declaration: &Declaration,
    holds: impl Fn(&Authored<'_>) -> bool,
) -> Option<&'x Authored<'x>> {
    let declared = declared(authored, file, declaration);
    let holding = declared
        .iter()
        .copied()
        .filter(|a| a.production_name().is_some() && holds(a))
        .collect::<Vec<_>>();
    match holding.as_slice() {
        [one] => Some(one),
        _ => declared.first().copied(),
    }
}

fn unread_item(index: usize, file: &str, declaration: &Declaration) -> InvalidMutation {
    InvalidMutation {
        edit: Some(index),
        reason: InvalidReason::UnreadDeclaration,
        detail: format!(
            "{} lowers to no sentence of the loaded specification",
            declaration.describe(file)
        ),
    }
}

/// The text edit of one grammar edit (PJ-34): `find` occurs once in the declaration, and a
/// deletion removes the whole declaration (one that declares several productions is refused:
/// the alternative's removal is a find/replace of the declaration).
fn grammar_edit(
    index: usize,
    edit: &EditSpec,
    file: String,
    declaration: Declaration,
    item: &Authored<'_>,
    text: &str,
) -> Result<TextEdit, InvalidMutation> {
    let invalid = |reason, detail: String| InvalidMutation {
        edit: Some(index),
        reason,
        detail,
    };
    let what = declaration.describe(&file);
    let range = match &edit.action {
        EditAction::Delete if declaration.productions > 1 => {
            return Err(invalid(
                InvalidReason::StructureChanged,
                format!(
                    "delete = true deletes a whole declaration, and {what} declares {} \
                     productions: write the removal of one alternative as a find/replace of the \
                     declaration (its text and its `|` or `>`, replaced by nothing)",
                    declaration.productions
                ),
            ));
        }
        EditAction::Delete => declaration.span.clone(),
        EditAction::Replace { find, .. } => {
            let scope = declaration.span.clone();
            match occurrences(&text[scope.clone()], find).as_slice() {
                [one] => scope.start + one..scope.start + one + find.len(),
                [] if text.contains(find.as_str()) => {
                    return Err(invalid(
                        InvalidReason::EditOutsideRule,
                        format!("{find:?} occurs in {file} but not inside {what}"),
                    ));
                }
                [] => {
                    return Err(invalid(
                        InvalidReason::FindNotFound,
                        format!(
                            "{find:?} does not occur in {what}{}",
                            find_hint(text, scope, find, &file, false)
                        ),
                    ));
                }
                several => {
                    return Err(invalid(
                        InvalidReason::FindAmbiguous,
                        format!("{find:?} occurs {} times in {what}", several.len()),
                    ));
                }
            }
        }
    };
    Ok(TextEdit {
        edit: index,
        at: item.at.clone(),
        file,
        range,
        replacement: match &edit.action {
            EditAction::Replace { replace, .. } => Some(replace.clone()),
            EditAction::Delete => None,
        },
        declaration: Some(declaration),
    })
}

/// The order of sentence kinds within one declaration's sentences.
fn kind_rank(sentence: &Sentence) -> u8 {
    match sentence {
        Sentence::Production { .. } => 0,
        Sentence::SyntaxLexical { .. } => 1,
        Sentence::SyntaxPriority { .. } => 2,
        Sentence::SyntaxAssociativity { .. } => 3,
        _ => 4,
    }
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

#[cfg(test)]
mod tests {
    use super::*;

    /// The nearest text is the substring fewest edits away, as long as `find` where that ties,
    /// and its line is the view's.
    #[test]
    fn the_nearest_text_is_the_fewest_edits_away() {
        let rule = "rule [add]: I1:Int + I2:Int => I1 -Int I2";
        let near = nearest_text(rule, "I1 /Int I2").unwrap();
        assert_eq!(
            (&rule[near.range.clone()], near.distance),
            ("I1 -Int I2", 1)
        );
        // `x + ` is one deletion from `x + 1`, as `x + 2` is one substitution; the length
        // decides.
        let near = nearest_text("y => x + 2", "x + 1").unwrap();
        assert_eq!(&"y => x + 2"[near.range], "x + 2");
        // Equally near and as long: the first.
        let near = nearest_text("ab ab", "ac").unwrap();
        assert_eq!((near.range, near.distance), (0..2, 1));
        // Characters, not bytes: a multi-byte character is one edit.
        let near = nearest_text("f(é) => 1", "f(e)").unwrap();
        assert_eq!(
            ("f(é) => 1"[near.range.clone()].to_owned(), near.distance),
            ("f(é)".to_owned(), 1)
        );
        // A respelled call inside a longer line.
        let line = "rule plus_zero(N) => N [label(nat--plus_zero)]";
        let near = nearest_text(line, "plusZero(N)").unwrap();
        assert_eq!(
            (&line[near.range.clone()], near.distance),
            ("plus_zero(N)", 2)
        );
        assert_eq!(nearest_text("", "a"), None);
        assert_eq!(nearest_text("a", ""), None);
        let long = "a".repeat(NEAREST_TEXT_CELLS / 2 + 1);
        assert_eq!(nearest_text(&long, "ab"), None);
        assert!(nearest_text(&long[1..], "ab").is_some());
    }

    #[test]
    fn a_long_rule_is_quoted_from_the_line_of_the_nearest_text() {
        assert_eq!(excerpt("a \"b\"\nc", 0), "\"a \\\"b\\\"\\nc\"");
        let first = "x".repeat(EXCERPT_CHARS);
        let text = format!("{first}\nrule y\n{first}");
        // From the line of the focus, cut after EXCERPT_CHARS characters.
        let quoted = excerpt(&text, EXCERPT_CHARS + 3);
        assert!(quoted.starts_with("...\"rule y\\n"), "{quoted}");
        assert!(quoted.ends_with("\"..."), "{quoted}");
        assert_eq!(
            quoted.len(),
            "...\"\"...".len() + EXCERPT_CHARS + 1,
            "{quoted}"
        );
        // From the start without a focus.
        assert!(excerpt(&text, 0).starts_with("\"xxx"));
    }

    #[test]
    fn a_find_not_found_names_the_nearest_text_and_the_rule_now() {
        let text = "module M\n  rule [add]: I1:Int + I2:Int\n    => I1 -Int I2\nendmodule\n";
        let span = text.find("rule").unwrap()..text.find("\nendmodule").unwrap();
        assert_eq!(
            find_hint(text, span.clone(), "I1 +Int I2", "m.k", true),
            "; nearest text, 1 edit from find, at m.k:3: \"I1 -Int I2\"; the rule's text now: \
             \"rule [add]: I1:Int + I2:Int\\n    => I1 -Int I2\""
        );
        // Across lines, the lines are a range.
        assert_eq!(
            find_hint(text, span.clone(), "I1:Int + I2:Int => I1", "m.k", false),
            "; nearest text, 4 edits from find, at m.k:2-3: \"I1:Int + I2:Int\\n    => I1\""
        );
        // Farther than a third of find's length, nothing is named.
        assert_eq!(
            find_hint(text, span.clone(), "maxInt ( A , B )", "m.k", true),
            "; no text of the rule is within 5 edits of find; the rule's text now: \
             \"rule [add]: I1:Int + I2:Int\\n    => I1 -Int I2\""
        );
        assert_eq!(
            find_hint(text, 0..text.len(), "zzz", "m.k", false),
            "; no text of m.k is within 1 edit of find"
        );
    }

    #[test]
    fn near_labels_name_respellings_moves_and_misspellings() {
        let labels = [
            "nat--plus_zero",
            "nat--arith--plus_succ",
            "nat--times_zero",
            "nat--evalBinaryOpWithCarry",
        ];
        // A respelling: equal up to case and `_`; `plusZero` is one word, so `times_zero`
        // shares none with it.
        assert_eq!(
            near_labels(labels, "nat--plusZero"),
            "; near labels: nat--plus_zero"
        );
        assert_eq!(
            near_labels(labels, "eval_binary_op_with_carry"),
            "; near labels: nat--evalBinaryOpWithCarry"
        );
        // A moved item keeps its last component.
        assert_eq!(
            near_labels(labels, "nat--plus_succ"),
            "; near labels: nat--arith--plus_succ, nat--plus_zero"
        );
        assert_eq!(
            near_labels(labels, "unrelated"),
            "; no label is \"unrelated\" up to case and `_`, contains it, shares a word with it \
             or is within 3 edits of it"
        );
    }
}
