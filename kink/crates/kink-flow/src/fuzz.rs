//! `kink-flow fuzz`: a k-rust-fuzz campaign on kink's own sides (fz26 P7-KINKFLOW, tickets T3a
//! and T3b).
//!
//! The command takes a template, a program of the flow with some of its literals marked as holes
//! (`TEMPLATES.toml`, [`TemplateList`]), and one job ([`FuzzJob`]). T3a builds the kill job: look
//! for hole values that make the template kill one mutation of the flow's list, so that the
//! program can join the corpus and kink's own `run` proves the kill. T5 adds the reach job (a
//! program `results` would list in a rule's `reached_by` or `fired_by`: its all-paths run must
//! be comparable, since kink counts only comparable programs) and the pattern job (a program
//! whose run reaches a configuration matching a pattern of `PATTERNS.toml`, as a `query` hit:
//! matched at any state, with the facts a complete search could stop at refused). Both run on
//! the baseline alone.
//!
//! **Sides.** The baseline is the admitted specification's compile, converted with
//! `k_rust_fuzz::CompiledDefinition::from_artifacts` with the loaded definition's source table,
//! on the route kink runs (`BackendRoute::FromDefinition`); it keeps its claims, as every kink
//! baseline run does. The mutant is the mutation's patch ([`crate::mutation::resolve`]) made
//! into the claim-free, consistency-checked mutant every kink test of that mutant runs on
//! (kink-campaign `claim_free_mutant`, admitted with the campaign's module and the flow's
//! `[spec] assume_joined`), converted with the baseline's source table: a mutant shares the
//! baseline's sources, and its provenance indexes them. A mutation kink would refuse
//! (`invalid-mutation`, `equivalent`, an invalid or inconsistent mutant, unsupported claims) ends
//! the command with kink's status and reason, and nothing is fuzzed.
//!
//! **Comparability.** The campaign reads data ends strictly: a definition whose full critical-pair
//! check reports a finding no name assumes makes the campaign `not-comparable`, and the document
//! lists every finding with its side and verdict. Under such a finding the definition may
//! identify the two ends a kill compares, so a kill would hold in no model of it; kink's own run
//! refuses it as well (`baseline-findings`) unless the flow names the findings. A finding is read
//! as resolved only when the author names it: in the flow's `[spec] assume_joined`, which are
//! always passed, or with `--assume-joined NAME` for this command. Every assumed name is printed
//! beside the `[[program]]` fragment, genuine ones flagged, with the instruction to add each name
//! the flow lacks (kink counts no kill on the definition without it).
//!
//! **Guards** (T3b). kink's definition exclusions are read on both sides as kink's runner reads
//! them; one refuses the job with the status and reason kink's `run` gives the mutation
//! (`unknown` and the exclusion for the mutant's; `error`, `no-comparable-program` for the
//! baseline's, which excludes every program's baseline run). kink assembles every test's input
//! from the baseline's grammar for both sides, so a run of no case first compares each side's
//! initial configuration at the holes' anchors: a mutant that assembles the template otherwise
//! (a `[macro]` edit) is refused before any case, and so is a baseline that assembles it otherwise
//! than kink does. Each candidate's program is then assembled by kink exactly as a `[[program]]`
//! ([`check_assembly`]), and each side's initial configuration must be that configuration, or
//! the candidate is not offered (`assembly-mismatch`). The last `run` document, only read, gives
//! the template program's class and the mutation's `reaching` programs (suggested as
//! templates), and the document warns about an unusable template, a template outside the
//! reaching programs, and the scope of `--time-limit-ms`.
//!
//! **Witness filter** (fz26 FZ-COMPARABLE-B). Unless `--no-filter` is given
//! ([`FuzzOptions::filter`]), the campaign runs with kink's own rules as a k-rust-fuzz witness
//! filter ([`crate::fuzz_filter`]), built from the loads the definition exclusions were read
//! from: a candidate kink would refuse for a reason that depends on the input (a non-ASCII String
//! end) is refused inside the search, repaired when its String holes can be, and the search goes
//! on. A campaign whose every hit was refused stops `client-refused`, never `budget`. A template
//! whose own input kink excludes is refused before any case (`initial-state-excluded`). The
//! filter keeps each side's kink load for the whole campaign (about +90 MB of peak memory on
//! TRIAL3's SIMPLE job, not measurable on IMP); `--no-filter` drops them.
//!
//! **Budgets.** `--cases N` (default [`DEFAULT_CASES`]) or `--work W`, `--seed S` (default 0),
//! the library's default proposers. Every case runs with the flow's `max_depth`, a safety limit
//! of the flow's `time_ms` per execution, and `max_work` of `--max-work` (default
//! [`DEFAULT_MAX_WORK`], always set, since a depth bound alone would leave work unbounded). Kills
//! use all paths unless `--one-path`. `--time-limit-ms T` cancels the campaign's run (not its
//! setup) after `T` ms; a cancelled campaign is outside the determinism contract
//! (`stopped: time-limit`). The campaign runs on the caller's thread, which the command line
//! gives kink-corpus's definition stack allowance.
//!
//! **Output.** One document ([`FUZZ_SCHEMA`]): the fuzz report of the attempt, the candidate (the
//! shrunk witness case, else the first), and the `[[program]]` fragment, printed, never written.
//! **Confirmation** (T4). Unless `--no-confirm` is given ([`FuzzOptions::confirm`]), kink's own
//! code confirms the candidate on an overlay of the flow held in memory, with the fragment as its
//! only program and a scratch cache removed on every path (`confirm`): `run` for a kill,
//! `results` for a reach, `query` for a pattern. When kink refuses the shrunk case and the first
//! is another program, the first is confirmed too; there is no seed retry. A candidate kink
//! refuses is not offered (`stopped: unconfirmed`). Nothing under the flow's directory or the
//! cache is written.

use crate::fuzz_filter::{FilterJob, FilterSide, KinkJudgement};
use crate::{
    admit::{AdmittedSpec, ProgramInputs, admit_spec},
    digest::{program_digest, spec_digest},
    manifest::{FlowManifest, ManifestError, Program},
    mutation::{MutationList, RuleText, resolve, rule_texts},
    pattern::{INVALID_PATTERN, Lowering, PatternList, Searcher},
    report::claims_value,
    results::kebab,
    search::status_name,
    search::{ProgramOrder, RunMode, RunOptions},
};
use k_rust::kore::{
    ast::{Pattern as KorePattern, Sentence},
    parser::{parse_definition, parse_pattern},
};
use k_rust::names::KoreAttribute;
use k_rust_fuzz::{
    BackendRoute, Budget, CallerIdentity, Campaign, CampaignSpec, CancellationToken, CaseOptions,
    CompiledDefinition, Definitions, HoleDecl, HoleLocation, PathMode, ProgramInput,
    ProposerConfig, Target, TargetKind,
    error::CampaignError,
    exec::ComparableCondition,
    holes::HoleFile,
    report::{
        AbortKind, CampaignOutcome, DefinitionFinding, FindingVerdict, FuzzReport, WitnessCase,
        digest_hex,
    },
    spec::{DEFAULT_REJECTION_CAP, ProgramSource as FuzzProgram, ProgramText},
    target::{DifferentialTarget, PatternAt, PatternTarget, RuleMode, RuleRef, RuleTarget},
    values::GenerationBounds,
};
use kink_campaign::{MutantAdmission, claim_free_mutant};
use kink_corpus::{ProgramSource, cli::DEFINITION_STACK_BYTES};
use kink_native::{
    K_RUST_REVISION, ValidatedDefinition,
    coverage::{RuleAuthors, coverage_domain},
    exclusion::{DefinitionExclusions, Exclusion, ValidatedLoad},
    execution::SolverProfile,
};
use kink_patch::SentenceRef;
use serde_json::{Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Component, Path, PathBuf},
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
        mpsc,
    },
    thread,
    time::Duration,
};
use toml::{Table, Value as Toml};

/// The document's `schema`.
pub const FUZZ_SCHEMA: &str = "kink-flow-fuzz";
/// The document's `version`. Version 3 (fz26 FZ-COMPARABLE-B) adds `job.filter`, the `stopped`
/// value `client-refused`, the warning `client-refused` and the refusal `initial-state-excluded`,
/// and embeds fuzz reports that carry the witness filter's fields. Version 4 (fz26 round 4,
/// FZ-REPLAY-WHOLE) embeds k-rust-fuzz reports of version 10: their identity records the
/// k-rust-fuzz build and the parser's diagnostic work limit, their totals the first case outside
/// the determinism contract, and every source location they name is relative to the main
/// module's file; it also adds the `stopped` value `domain-exhausted` and the warning
/// `witness-not-terminating` (FZ-ENGINE-R4), and the embedded totals' `domain`, `diverging` and
/// `coverage-last-grew`. `tests/formats.rs` ties the version to the document's shape.
pub const FUZZ_VERSION: u32 = 4;
/// The cases of a campaign that names neither `--cases` nor `--work`.
pub const DEFAULT_CASES: u64 = 1000;
/// The `max_work` of every case when `--max-work` is not given.
pub const DEFAULT_MAX_WORK: u64 = 100_000;

// ---------------------------------------------------------------------------------------------
// TEMPLATES.toml
// ---------------------------------------------------------------------------------------------

/// A decoded `TEMPLATES.toml`. Paths are relative to [`TemplateList::directory`] and stay inside
/// it, by the rule `FLOW.toml`'s paths follow.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TemplateList {
    /// The directory holding the file.
    pub directory: PathBuf,
    pub templates: Vec<Template>,
}

/// One `[[template]]`: a program text and its holes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Template {
    pub id: String,
    pub source: TemplateSource,
    /// `start_sort`; absent: the corpus program's, else kink's default
    /// (`program_start_position` of `$PGM`'s sort).
    pub start_sort: Option<String>,
    /// Configuration variables, name (without `$`) to text, sorted by name.
    pub variables: Vec<(String, String)>,
    /// The holes, decoded with k-rust-fuzz's `[[hole]]` decoder; a span hole addresses the
    /// template's text, whose name in the campaign is the template's id.
    pub holes: Vec<HoleDecl>,
}

/// Where a template's text comes from.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TemplateSource {
    /// `program`: a `[[program]]` of the flow, with its text, start sort and variables.
    Program(String),
    /// `file`, relative to the templates' directory.
    File(String),
    /// `text`.
    Text(String),
}

impl TemplateList {
    /// Read and decode the file at `path`; its directory becomes the root of its paths.
    ///
    /// # Errors
    ///
    /// The file cannot be read, or does not decode ([`Self::decode`]).
    pub fn read(path: &Path) -> Result<Self, ManifestError> {
        let text = fs::read_to_string(path)
            .map_err(|e| ManifestError::new("", format!("cannot read the templates: {e}")))?;
        let directory = match path.parent() {
            Some(parent) if !parent.as_os_str().is_empty() => parent.to_path_buf(),
            _ => PathBuf::from("."),
        };
        Self::decode(&text, &directory)
    }

    /// Decode `text`, whose paths are relative to `directory`. Strict, as `FLOW.toml`: an unknown
    /// key, a value of the wrong type, a duplicate id, a template with not exactly one of
    /// `program`, `file` and `text`, or a path leaving the directory is an error naming the key.
    /// Each `[[template.hole]]` goes from its TOML value through k-rust-fuzz's serde decoder
    /// (`HoleFile`), whose messages are wrapped with the template and the hole's index; a TOML
    /// date or time anywhere in a hole is refused (it is no K value), and a hole's `program`
    /// may only name a binding (`"$NAME"`, a literal inside that variable's text): by default a
    /// hole addresses the template's text.
    ///
    /// # Errors
    ///
    /// The first problem found, naming its key.
    pub fn decode(text: &str, directory: &Path) -> Result<Self, ManifestError> {
        let top: Table = toml::from_str(text)
            .map_err(|e| ManifestError::new("", format!("invalid TOML: {e}")))?;
        if let Some(key) = top.keys().find(|key| key.as_str() != "template") {
            return Err(ManifestError::new(key.clone(), "unknown key"));
        }
        let templates = match top.get("template") {
            None => Vec::new(),
            Some(Toml::Array(entries)) => entries
                .iter()
                .enumerate()
                .map(|(index, entry)| template(index, entry))
                .collect::<Result<Vec<_>, _>>()?,
            Some(_) => {
                return Err(ManifestError::new(
                    "template",
                    "expected [[template]] tables",
                ));
            }
        };
        let mut ids = BTreeSet::new();
        for template in &templates {
            if !ids.insert(template.id.as_str()) {
                return Err(ManifestError::new(
                    template_key(&template.id),
                    "duplicate template id",
                ));
            }
        }
        Ok(Self {
            directory: directory.to_path_buf(),
            templates,
        })
    }

    /// The template with this id.
    #[must_use]
    pub fn get(&self, id: &str) -> Option<&Template> {
        self.templates.iter().find(|template| template.id == id)
    }
}

fn template_key(id: &str) -> String {
    format!("template {id:?}")
}

fn join(prefix: &str, key: &str) -> String {
    format!("{prefix}.{key}")
}

fn nonempty_string(value: &Toml, key: &str) -> Result<String, ManifestError> {
    match value.as_str() {
        Some(text) if !text.is_empty() => Ok(text.to_owned()),
        Some(_) => Err(ManifestError::new(key, "must not be empty")),
        None => Err(ManifestError::new(key, "expected a string")),
    }
}

/// A relative path that stays inside the templates' directory (`FLOW.toml`'s rule).
fn relative_path(value: &Toml, key: &str) -> Result<String, ManifestError> {
    let text = nonempty_string(value, key)?;
    let mut depth = 0usize;
    for component in Path::new(&text).components() {
        match component {
            Component::Normal(_) => depth += 1,
            Component::CurDir => {}
            Component::ParentDir if depth > 0 => depth -= 1,
            _ => {
                return Err(ManifestError::new(
                    key,
                    format!("path {text:?} leaves the templates' directory"),
                ));
            }
        }
    }
    Ok(text)
}

fn template(index: usize, value: &Toml) -> Result<Template, ManifestError> {
    let position = format!("template[{index}]");
    let entry = value
        .as_table()
        .ok_or_else(|| ManifestError::new(&position, "expected a table"))?;
    let id = nonempty_string(
        entry
            .get("id")
            .ok_or_else(|| ManifestError::new(join(&position, "id"), "missing required key"))?,
        &join(&position, "id"),
    )?;
    let key = template_key(&id);
    if let Some(unknown) = entry.keys().find(|name| {
        ![
            "id",
            "program",
            "file",
            "text",
            "start_sort",
            "variables",
            "hole",
        ]
        .contains(&name.as_str())
    }) {
        return Err(ManifestError::new(join(&key, unknown), "unknown key"));
    }
    let source = match (entry.get("program"), entry.get("file"), entry.get("text")) {
        (Some(program), None, None) => {
            TemplateSource::Program(nonempty_string(program, &join(&key, "program"))?)
        }
        (None, Some(file), None) => TemplateSource::File(relative_path(file, &join(&key, "file"))?),
        (None, None, Some(Toml::String(text))) => TemplateSource::Text(text.clone()),
        (None, None, Some(_)) => {
            return Err(ManifestError::new(join(&key, "text"), "expected a string"));
        }
        _ => {
            return Err(ManifestError::new(
                key,
                "give exactly one of program, file and text",
            ));
        }
    };
    let program_source = matches!(source, TemplateSource::Program(_));
    let start_sort = entry
        .get("start_sort")
        .map(|value| nonempty_string(value, &join(&key, "start_sort")))
        .transpose()?;
    let variables = match entry.get("variables") {
        None => Vec::new(),
        Some(Toml::Table(variables)) => variables
            .iter()
            .map(|(name, text)| {
                let variable_key = join(&join(&key, "variables"), name);
                if name.is_empty() {
                    return Err(ManifestError::new(variable_key, "empty variable name"));
                }
                match text {
                    Toml::String(text) => Ok((name.clone(), text.clone())),
                    _ => Err(ManifestError::new(variable_key, "expected a string")),
                }
            })
            .collect::<Result<BTreeMap<_, _>, _>>()?
            .into_iter()
            .collect(),
        Some(_) => {
            return Err(ManifestError::new(
                join(&key, "variables"),
                "expected a table of strings",
            ));
        }
    };
    if program_source && (start_sort.is_some() || !variables.is_empty()) {
        return Err(ManifestError::new(
            key,
            "a template of a corpus program takes that program's start_sort and variables; give \
             the text as file or text to set others",
        ));
    }
    let holes = match entry.get("hole") {
        None => Vec::new(),
        Some(Toml::Array(holes)) => holes
            .iter()
            .enumerate()
            .map(|(index, hole)| template_hole(&id, &key, index, hole))
            .collect::<Result<Vec<_>, _>>()?,
        Some(_) => {
            return Err(ManifestError::new(
                join(&key, "hole"),
                "expected [[template.hole]] tables",
            ));
        }
    };
    Ok(Template {
        id,
        source,
        start_sort,
        variables,
        holes,
    })
}

/// Whether a TOML value holds a date or time anywhere.
fn holds_datetime(value: &Toml) -> bool {
    match value {
        Toml::Datetime(_) => true,
        Toml::Array(values) => values.iter().any(holds_datetime),
        Toml::Table(table) => table.values().any(holds_datetime),
        _ => false,
    }
}

/// One `[[template.hole]]`: k-rust-fuzz's flat `[[hole]]` keys, decoded by its serde type.
fn template_hole(
    id: &str,
    key: &str,
    index: usize,
    value: &Toml,
) -> Result<HoleDecl, ManifestError> {
    let hole_key = format!("{key}.hole[{index}]");
    if !value.is_table() {
        return Err(ManifestError::new(hole_key, "expected a table"));
    }
    if holds_datetime(value) {
        // `toml::Value::try_into` would read a date as its text, a string choice `krust fuzz`
        // refuses: refuse it here, as no hole value is a date.
        return Err(ManifestError::new(
            hole_key,
            "a TOML date or time is not a hole value; write a string, an integer, a boolean or a \
             value table",
        ));
    }
    let file: HoleFile = value
        .clone()
        .try_into()
        .map_err(|error: toml::de::Error| ManifestError::new(&hole_key, error.message().trim()))?;
    if let Some(program) = file
        .program
        .as_deref()
        .filter(|program| !program.starts_with('$'))
    {
        return Err(ManifestError::new(
            join(&hole_key, "program"),
            format!(
                "{program:?}: a template's hole addresses the template's text (leave `program` \
                 out) or a binding's text (\"$NAME\")"
            ),
        ));
    }
    file.into_decl(Some(id))
        .map_err(|message| ManifestError::new(hole_key, message))
}

// ---------------------------------------------------------------------------------------------
// The kill job
// ---------------------------------------------------------------------------------------------

/// Options of `kink-flow fuzz` (module docs, "Budgets").
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FuzzOptions {
    /// `--cases N` or `--work W`.
    pub budget: Budget,
    /// `--seed S`.
    pub seed: u64,
    /// `--max-work N`; `None`: [`DEFAULT_MAX_WORK`].
    pub max_work: Option<u64>,
    /// `--time-limit-ms T`: the watchdog that cancels the campaign's run.
    pub time_limit_ms: Option<u64>,
    /// `--assume-joined NAME`, in the order given (the flow's `[spec] assume_joined` are added).
    pub assume_joined: Vec<String>,
    /// All paths, or one with `--one-path`.
    pub paths: PathMode,
    /// `--cache DIR`: where the last `run` document is read from (default `.kink-flow` beside
    /// `FLOW.toml`); only read, for the template's class and the mutation's reaching programs.
    pub cache: Option<PathBuf>,
    /// Confirm each candidate with kink's own code (KF-T4; the command line's default, off with
    /// `--no-confirm`). Off in [`FuzzOptions::default`], so a library caller asks for it.
    pub confirm: bool,
    /// Judge each candidate hit and shrink candidate inside the campaign by kink's own rules
    /// ([`crate::fuzz_filter`], fz26 FZ-COMPARABLE-B); on by default, off with `--no-filter`.
    pub filter: bool,
}

impl Default for FuzzOptions {
    fn default() -> Self {
        Self {
            budget: Budget::Cases(DEFAULT_CASES),
            seed: 0,
            max_work: None,
            time_limit_ms: None,
            assume_joined: Vec::new(),
            paths: PathMode::AllPaths,
            cache: None,
            confirm: false,
            filter: true,
        }
    }
}

/// Why the command fuzzed nothing.
struct Refusal {
    stage: &'static str,
    reason: String,
    detail: String,
}

impl Refusal {
    fn new(stage: &'static str, reason: impl Into<String>, detail: impl Into<String>) -> Self {
        Self {
            stage,
            reason: reason.into(),
            detail: detail.into(),
        }
    }

    fn value(&self) -> Value {
        json!({
            "outcome": "refused",
            "stage": self.stage,
            "reason": self.reason,
            "detail": self.detail,
        })
    }
}

/// The document's header and the parts every outcome fills.
fn document() -> Value {
    json!({
        "schema": FUZZ_SCHEMA,
        "version": FUZZ_VERSION,
        "k_rust_revision": K_RUST_REVISION,
        "profile": SolverProfile::BUILD.name(),
        "kink_build": kink_campaign::kink_build().map_or(Value::Null, |b| json!(b.to_string())),
        "kink": kink_campaign::kink_identity(),
        "spec": null,
        "template": null,
        "job": null,
        "sides": null,
        "assembly": null,
        "findings": [],
        "assumed": [],
        "attempts": [],
        "program": null,
        "stopped": null,
        "action": null,
        "warnings": [],
    })
}

/// The document of a `FLOW.toml`, `TEMPLATES.toml` or `MUTATIONS.toml` that does not decode.
#[must_use]
pub fn input_refused(file: &str, error: &dyn std::fmt::Display) -> Value {
    let mut document = document();
    document["spec"] = Refusal::new("input", format!("invalid-{file}"), error.to_string()).value();
    document["stopped"] = json!("refused");
    document["action"] = json!(format!("fix {file}: the detail names the key"));
    document
}

/// The baseline or a mutant as a k-rust-fuzz definition: `side`'s loaded definition and compiled
/// artifacts with the baseline's source table (a mutant shares the baseline's sources), on the
/// route kink runs (`Backend::from_definition`).
///
/// # Errors
///
/// k-rust-fuzz's conversion error.
pub fn compiled_side(
    manifest: &FlowManifest,
    spec: &AdmittedSpec,
    side: &ValidatedDefinition,
) -> Result<CompiledDefinition, CampaignError> {
    let mut compiled = CompiledDefinition::from_artifacts(
        &manifest.spec.main_module,
        spec.loaded.syntax_module(),
        side.definition().clone(),
        spec.loaded.baseline.loaded().source_table().clone(),
        side.artifacts().clone(),
    )?;
    compiled.route = BackendRoute::FromDefinition;
    Ok(compiled)
}

fn side_value(side: &ValidatedDefinition, compiled: &CompiledDefinition) -> Value {
    let digest = |result: Result<String, CampaignError>| match result {
        Ok(digest) => json!(digest),
        Err(error) => json!({"error": error.to_string()}),
    };
    json!({
        "kore_sha256": side.kore_sha256().to_string(),
        "frontend_digest": digest(compiled.frontend_digest()),
        "execution_definition_digest": digest(compiled.execution_definition_digest()),
    })
}

/// A template made concrete against the flow: its text, start sort, variables, and where a file
/// of the instantiated program could go.
struct Instance {
    text: String,
    start_sort: String,
    start_sort_source: &'static str,
    /// The start sort a `[[program]]` of the witness writes (the template's or its program's).
    written_start_sort: Option<String>,
    variables: Vec<(String, String)>,
    file: Option<String>,
}

fn read_inside(root: &Path, name: &str) -> Result<String, String> {
    let root = fs::canonicalize(root).map_err(|_| "the templates' directory is unavailable")?;
    let path = fs::canonicalize(root.join(name)).map_err(|e| format!("cannot read {name}: {e}"))?;
    if !path.starts_with(&root) {
        return Err(format!("{name} escapes the templates' directory"));
    }
    fs::read_to_string(&path).map_err(|e| format!("cannot read {name}: {e}"))
}

fn instance(
    template: &Template,
    templates: &TemplateList,
    manifest: &FlowManifest,
    inputs: &ProgramInputs,
    spec: &AdmittedSpec,
) -> Result<Instance, Refusal> {
    let refused = |detail: String| Refusal::new("template", "template-refused", detail);
    let (text, given_sort, variables, file) = match &template.source {
        TemplateSource::Program(id) => {
            let program = manifest
                .programs
                .iter()
                .find(|program| &program.id == id)
                .ok_or_else(|| refused(format!("program {id:?}: FLOW.toml has no such program")))?;
            let text = inputs
                .text(program)
                .map_err(|refusal| refused(format!("program {id:?}: {}", refusal.detail)))?;
            let file = match &program.source {
                ProgramSource::File(name) => Some(name.clone()),
                ProgramSource::Text(_) => None,
            };
            (
                text,
                program.start_sort.clone(),
                program.variables.clone(),
                file,
            )
        }
        TemplateSource::File(name) => (
            read_inside(&templates.directory, name).map_err(refused)?,
            template.start_sort.clone(),
            template.variables.clone(),
            Some(name.clone()),
        ),
        TemplateSource::Text(text) => (
            text.clone(),
            template.start_sort.clone(),
            template.variables.clone(),
            None,
        ),
    };
    let (start_sort, start_sort_source) = match &given_sort {
        Some(sort) => (
            sort.clone(),
            if matches!(template.source, TemplateSource::Program(_)) {
                "program"
            } else {
                "template"
            },
        ),
        None => {
            // kink's default (kink-corpus `assemble_input_with`): the program-start position of
            // `$PGM`'s declared sort.
            let variables = &spec.compiled.artifacts().configuration_variables;
            let pgm = variables
                .get("PGM")
                .cloned()
                .unwrap_or_else(|| k_rust::kast::Sort::new("KItem"));
            (
                k_rust::kompile::program_start_position(&pgm).to_string(),
                "default",
            )
        }
    };
    Ok(Instance {
        text,
        start_sort,
        start_sort_source,
        written_start_sort: given_sort,
        variables,
        file,
    })
}

/// The flow's names and the command line's, sorted and without repeats.
fn assumed_names(manifest: &FlowManifest, options: &FuzzOptions) -> Vec<String> {
    manifest
        .spec
        .assume_joined
        .iter()
        .chain(&options.assume_joined)
        .cloned()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn verdict_name(verdict: FindingVerdict) -> &'static str {
    match verdict {
        FindingVerdict::Genuine => "genuine",
        FindingVerdict::Undecided => "undecided",
        FindingVerdict::Decided => "decided",
    }
}

fn role_name(role: k_rust_fuzz::report::DefinitionRole) -> &'static str {
    match role {
        k_rust_fuzz::report::DefinitionRole::Baseline => "baseline",
        k_rust_fuzz::report::DefinitionRole::Mutant => "mutant",
    }
}

fn finding_value(finding: &DefinitionFinding) -> Value {
    json!({
        "side": role_name(finding.side),
        "name": finding.name,
        "verdict": verdict_name(finding.verdict),
        "assumed": finding.assumed,
        "reason": finding.reason,
    })
}

/// Whether the report's finding is the one `name` names: equal, or equal after a side prefix
/// that names its side. (A name may also shorten a file path; such a name matches nothing here,
/// and its entry lists no finding.)
fn names_finding(name: &str, finding: &DefinitionFinding) -> bool {
    let Some(own) = finding.name.as_deref() else {
        return false;
    };
    let side = role_name(finding.side);
    name == own
        || name
            .strip_prefix(side)
            .and_then(|rest| rest.strip_prefix(':'))
            .is_some_and(|rest| rest == own)
}

/// The assumed names, each with where it came from and the findings it assumed.
fn assumed_value(
    manifest: &FlowManifest,
    options: &FuzzOptions,
    report: Option<&FuzzReport>,
) -> Value {
    let findings = report.map_or(&[][..], |report| &report.definition_findings[..]);
    let names = assumed_names(manifest, options);
    Value::Array(
        names
            .iter()
            .map(|name| {
                let matched = findings
                    .iter()
                    .filter(|finding| finding.assumed && names_finding(name, finding))
                    .collect::<Vec<_>>();
                json!({
                    "name": name,
                    "in_flow": manifest.spec.assume_joined.contains(name),
                    "from_command_line": options.assume_joined.contains(name),
                    "genuine": matched.iter().any(|f| f.verdict == FindingVerdict::Genuine),
                    "findings": matched.iter().map(|f| json!({
                        "side": role_name(f.side),
                        "verdict": verdict_name(f.verdict),
                    })).collect::<Vec<_>>(),
                })
            })
            .collect(),
    )
}

/// Run `body` under a watchdog that cancels its token after `time` (when given); whether it
/// fired.
fn under_watchdog<T>(
    time: Option<Duration>,
    body: impl FnOnce(Option<CancellationToken>) -> T,
) -> (T, bool) {
    let Some(time) = time else {
        return (body(None), false);
    };
    let token = CancellationToken::new();
    let fired = Arc::new(AtomicBool::new(false));
    if time.is_zero() {
        fired.store(true, Ordering::Release);
        token.cancel();
    }
    let (done, finished) = mpsc::channel::<()>();
    let guard = {
        let token = token.clone();
        let fired = Arc::clone(&fired);
        thread::spawn(move || {
            if finished.recv_timeout(time) == Err(mpsc::RecvTimeoutError::Timeout) {
                fired.store(true, Ordering::Release);
                token.cancel();
            }
        })
    };
    let value = body(Some(token));
    drop(done);
    guard.join().expect("the watchdog thread does not panic");
    (value, fired.load(Ordering::Acquire))
}

/// The `[[program]]` a witness case re-enters the corpus as, and its printed fragment.
struct Fragment {
    /// The fragment, as TOML text.
    toml: String,
    /// Where a file of the program's text could go, beside the template's file.
    file: Option<String>,
    id: String,
    /// The program as kink's manifest decodes the fragment (its text inline).
    program: Program,
    /// The instantiated program text.
    text: String,
}

/// The fragment of a witness case: the instantiated program text (the template's when the case
/// has none), the written start sort, and the template's variables with the case's instantiated
/// bindings over them (a span hole inside a binding, or a configuration-variable hole's whole
/// value).
fn fragment(template: &Template, instance: &Instance, case: &WitnessCase) -> Fragment {
    let text = case
        .program
        .clone()
        .unwrap_or_else(|| instance.text.clone());
    let mut variables = instance
        .variables
        .iter()
        .cloned()
        .collect::<BTreeMap<_, _>>();
    for (name, text) in &case.config_vars {
        let name = name.strip_prefix('$').unwrap_or(name);
        if !variables.contains_key(name) && KINK_STREAM_DEFAULTS.contains(&(name, text.as_str())) {
            // `campaign_variables`' binding, which kink's default gives the program anyway.
            continue;
        }
        variables.insert(name.to_owned(), text.clone());
    }
    for hole in &case.holes {
        if let (HoleLocation::ConfigVar { name }, Some(k_text)) = (&hole.location, &hole.k_text) {
            variables.insert(name.clone(), k_text.clone());
        }
    }
    let variables = variables.into_iter().collect::<Vec<_>>();
    let mut program = Program {
        id: String::new(),
        source: ProgramSource::Text(text.clone()),
        start_sort: instance.written_start_sort.clone(),
        variables: variables.clone(),
    };
    let digest = program_digest(&program, &text).to_string();
    let id = format!("{}-fz-{}", template.id, &digest[..8]);
    program.id.clone_from(&id);
    let file = instance.file.as_ref().map(|file| {
        let path = Path::new(file);
        let name = match path.extension().and_then(|e| e.to_str()) {
            Some(extension) => format!("{id}.{extension}"),
            None => id.clone(),
        };
        path.with_file_name(name).to_string_lossy().into_owned()
    });
    let mut table = Table::new();
    table.insert("id".into(), Toml::String(id.clone()));
    table.insert("text".into(), Toml::String(text.clone()));
    if let Some(sort) = &instance.written_start_sort {
        table.insert("start_sort".into(), Toml::String(sort.clone()));
    }
    if !variables.is_empty() {
        table.insert(
            "variables".into(),
            Toml::Table(
                variables
                    .into_iter()
                    .map(|(name, text)| (name, Toml::String(text)))
                    .collect(),
            ),
        );
    }
    let mut top = Table::new();
    top.insert("program".into(), Toml::Array(vec![Toml::Table(table)]));
    let toml = toml::to_string(&top).expect("a table of strings encodes");
    Fragment {
        toml,
        file,
        id,
        program,
        text,
    }
}

/// The premises of a witness, as the fragment prints them: each assumed name, genuine ones
/// flagged, and whether the flow already names it.
fn premises(manifest: &FlowManifest, options: &FuzzOptions, report: &FuzzReport) -> Vec<Value> {
    let assumed = assumed_value(manifest, options, Some(report));
    assumed
        .as_array()
        .into_iter()
        .flatten()
        .map(|entry| {
            let name = entry["name"].as_str().unwrap_or_default();
            let genuine = entry["genuine"].as_bool().unwrap_or(false);
            let in_flow = entry["in_flow"].as_bool().unwrap_or(false);
            let mut note = String::new();
            if genuine {
                note.push_str(
                    "GENUINE: the check exhibits two normal forms for one input, so this \
                     premise is known to be false and every kill under it is vacuous; ",
                );
            }
            note.push_str(if in_flow {
                "already in FLOW.toml's [spec] assume_joined"
            } else {
                "add it to FLOW.toml's [spec] assume_joined, or kink counts no kill on this \
                 definition (baseline-findings)"
            });
            json!({"name": name, "genuine": genuine, "in_flow": in_flow, "note": note})
        })
        .collect()
}

// ---------------------------------------------------------------------------------------------
// Guards: definition exclusions, assembly, the last run's facts
// ---------------------------------------------------------------------------------------------

/// What makes `exclusion` hold on a definition with these facts, naming the sentences.
fn exclusion_detail(facts: &DefinitionExclusions, exclusion: Exclusion) -> String {
    fn listed(items: impl IntoIterator<Item = String>) -> String {
        let items = items.into_iter().collect::<Vec<_>>();
        let shown = items.iter().take(8).cloned().collect::<Vec<_>>().join("; ");
        if items.len() > 8 {
            format!("{shown}; and {} more", items.len() - 8)
        } else {
            shown
        }
    }
    match exclusion {
        Exclusion::LoadStackStop => format!(
            "its load counted {} stop(s) for lack of native stack, so the theory a run executes \
             is not a function of the definition",
            facts.load_stack_stops
        ),
        Exclusion::ImplementationChosenHook => format!(
            "it references a hook whose value the definition leaves open and k-rust chooses: {}",
            listed(facts.implementation_chosen.iter().map(|reference| format!(
                "{} {} applies {} ({})",
                reference.module, reference.sentence, reference.symbol, reference.hook
            )))
        ),
        Exclusion::ShortCircuitReading => format!(
            "a rule's condition or result depends on whether andBool, orBool or #if skip an \
             operand that may be undefined: {}",
            listed(
                facts
                    .short_circuit_conditions
                    .iter()
                    .chain(&facts.short_circuit_results)
                    .cloned()
                    .collect::<BTreeSet<_>>()
            )
        ),
        Exclusion::EqualsCondition => format!(
            "a rule or equation has a condition equating two terms, a gap of k-rust's answers: {}",
            listed(facts.equals_conditions.iter().cloned())
        ),
        other => other.name().to_owned(),
    }
}

/// The definition exclusion of one side, if any, as kink-campaign's runner reads it for every
/// run on that side: from the side's compiled KORE loaded for `module` on this thread, with the
/// load, which the witness filter keeps ([`crate::fuzz_filter`]).
fn side_exclusion(
    side: &ValidatedDefinition,
    module: &str,
) -> Result<(ValidatedLoad, Option<(Exclusion, String)>), String> {
    let load = DefinitionExclusions::load_validated(side, module)?;
    let excluded = load
        .exclusions
        .definition_exclusion()
        .map(|exclusion| (exclusion, exclusion_detail(&load.exclusions, exclusion)));
    Ok((load, excluded))
}

/// What kink's own assembly makes of a witness's input, against each side's initial
/// configuration in the witness (design 3.2.5).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AssemblyCheck {
    /// Each side's initial configuration is kink's assembly of the program.
    Match,
    /// These sides' initial configurations (`baseline`, `mutant`) are not kink's assembly of the
    /// program, or do not parse as KORE.
    Mismatch { sides: Vec<String>, detail: String },
    /// kink refuses the program's input: its admission stage's reason and detail.
    Refused { reason: String, detail: String },
}

impl AssemblyCheck {
    /// `{status, ...}` for the document.
    #[must_use]
    pub fn value(&self) -> Value {
        match self {
            Self::Match => json!({"status": "match"}),
            Self::Mismatch { sides, detail } => {
                json!({"status": "mismatch", "sides": sides, "detail": detail})
            }
            Self::Refused { reason, detail } => {
                json!({"status": "refused", "reason": reason, "detail": detail})
            }
        }
    }
}

/// The per-candidate assembly check (design 3.2.5): kink assembles `program` (with `text`, its
/// instantiated text) exactly as it assembles a `[[program]]` of the corpus, from the
/// baseline's grammar for both sides of every test, with the program's start sort (kink's
/// default when it has none) and variables, then its concrete-state check and input gate; each
/// side's `initial_configuration` in `case`, parsed as KORE, must equal that configuration.
/// A difference means the campaign judged another input than the one kink would run, so the
/// case is no witness for kink (`assembly-mismatch`). The hole values are covered, since the
/// check reads the instantiated program.
pub fn check_assembly(
    spec: &AdmittedSpec,
    inputs: &mut ProgramInputs,
    program: &Program,
    text: &str,
    case: &WitnessCase,
) -> AssemblyCheck {
    let kink = match inputs.test_case(spec, program, text.to_owned()) {
        Ok(test) => test.initial_state,
        Err(refusal) => {
            return AssemblyCheck::Refused {
                reason: refusal.reason,
                detail: format!("{}: {}", refusal.stage, refusal.detail),
            };
        }
    };
    let kink_digest = digest_hex(kink.to_string().as_bytes());
    let mut sides = Vec::new();
    let mut details = Vec::new();
    for side in &case.sides {
        let role = role_name(side.role);
        match parse_pattern(&side.initial_configuration) {
            Ok(pattern) if pattern == kink => {}
            Ok(_) => {
                sides.push(role.to_owned());
                details.push(format!(
                    "the {role}'s initial configuration (sha256 {}) is not kink's assembly of \
                     the program (sha256 {kink_digest})",
                    digest_hex(side.initial_configuration.as_bytes())
                ));
            }
            Err(error) => {
                sides.push(role.to_owned());
                details.push(format!(
                    "the {role}'s initial configuration does not parse as KORE: {error}"
                ));
            }
        }
    }
    if sides.is_empty() {
        AssemblyCheck::Match
    } else {
        AssemblyCheck::Mismatch {
            sides,
            detail: details.join("; "),
        }
    }
}

/// The stream defaults kink assembles a program with (kink-corpus `assemble_input_with`): `$IO`
/// off and `$STDIN` empty, each as K text.
const KINK_STREAM_DEFAULTS: [(&str, &str); 2] = [("IO", "\"off\""), ("STDIN", "\"\"")];

/// The configuration variables the campaign assembles the template with, in kink's binding
/// order: the template's, then kink's stream defaults for each stream variable the definition
/// declares and the template does not bind. k-rust-fuzz's own default binds `$STDIN` to krun's
/// buffered empty input (`"\n"`) where kink binds `""`, so without these bindings every template
/// on a definition with stream cells assembled differently from kink's program and the job was
/// refused (`template-assembly-differs`; INT9 review K2). The order matters as much as the
/// values: the initial configuration lists the bindings in the order they are made.
fn campaign_variables(spec: &AdmittedSpec, instance: &Instance) -> Vec<(String, String)> {
    let declared = &spec.compiled.artifacts().configuration_variables;
    let mut variables = instance.variables.clone();
    for (name, text) in KINK_STREAM_DEFAULTS {
        let bound = variables
            .iter()
            .any(|(bound, _)| bound.strip_prefix('$').unwrap_or(bound) == name);
        if declared.contains_key(name) && !bound {
            variables.push((name.to_owned(), text.to_owned()));
        }
    }
    variables
}

/// The template as a `[[program]]` of the flow (its text inline): what kink would assemble and
/// digest for it.
fn template_program(template: &Template, instance: &Instance) -> Program {
    Program {
        id: template.id.clone(),
        source: ProgramSource::Text(instance.text.clone()),
        start_sort: instance.written_start_sort.clone(),
        variables: instance.variables.clone(),
    }
}

fn warning(kind: &str, detail: impl Into<String>) -> Value {
    json!({"kind": kind, "detail": detail.into()})
}

fn push_warning(document: &mut Value, warning: Value) {
    if let Some(warnings) = document["warnings"].as_array_mut() {
        warnings.push(warning);
    }
}

/// What the last `run` document (`report.json` in the cache directory, read as `report` reads
/// it: this build's, this kink identity's, and of the current specification) says about the
/// template and the mutation: the template program's class (found by its program digest), the
/// mutation's status and its `reaching` programs, each suggested as a template; and the
/// warnings these facts give. Nothing is run or written.
fn last_run(
    manifest: &FlowManifest,
    spec: &AdmittedSpec,
    options: &FuzzOptions,
    template: &Template,
    instance: &Instance,
    mutation: &str,
    warnings: &mut Vec<Value>,
) -> Value {
    let (document, found) = crate::report::report(
        manifest,
        &crate::report::ReportOptions {
            cache: options.cache.clone(),
        },
    );
    if !found {
        return json!({
            "found": false,
            "detail": document["detail"],
        });
    }
    let current = spec_digest(manifest, &spec.loaded.files).to_string();
    if document["spec"]["digest"] != json!(current) {
        warnings.push(warning(
            "stale-run-document",
            "the last run document is of another specification (its digest differs): run \
             `kink-flow run` again for the template's class and the mutation's reaching programs",
        ));
        return json!({"found": true, "current": false});
    }
    let program = template_program(template, instance);
    let digest = program_digest(&program, &instance.text).to_string();
    let rows = document["programs"].as_array().cloned().unwrap_or_default();
    let row = rows.iter().find(|row| row["digest"] == json!(digest));
    let template_row = row.map(|row| {
        json!({
            "program": row["id"],
            "class": row["class"],
            "cause": row["cause"],
        })
    });
    if let Some(row) = row
        && row["class"] != "comparable"
    {
        warnings.push(warning(
            "unusable-template",
            format!(
                "the template's own program ({}) is {} in the last run{}: kink compares only \
                 programs that end on a comparable value, so a witness from this template may \
                 be refused for the same reason; prefer a template whose program is comparable",
                row["id"].as_str().unwrap_or("?"),
                row["class"].as_str().unwrap_or("?"),
                row["cause"]
                    .as_str()
                    .map(|cause| format!(" ({cause})"))
                    .unwrap_or_default(),
            ),
        ));
    }
    let mutations = document["mutations"]
        .as_array()
        .cloned()
        .unwrap_or_default();
    let Some(entry) = mutations.iter().find(|entry| entry["id"] == mutation) else {
        return json!({
            "found": true,
            "current": true,
            "template": template_row,
            "mutation": null,
        });
    };
    let reaching = entry["reaching"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(Value::as_str)
        .map(str::to_owned)
        .collect::<Vec<_>>();
    let template_id = row.and_then(|row| row["id"].as_str());
    let status = entry["status"].as_str().unwrap_or_default();
    if status == "killed" {
        warnings.push(warning(
            "already-killed",
            format!(
                "the last run already killed this mutation (killer {})",
                entry["killer"].as_str().unwrap_or("?")
            ),
        ));
    } else if reaching.is_empty() {
        if crate::report::SURVIVOR_STATUSES.contains(&status) {
            warnings.push(warning(
                "no-reaching-program",
                "in the last run no comparable program reaches the edited rule: a template \
                 whose run reaches it is needed, or holes that make the run reach it",
            ));
        }
    } else if template_id.is_none_or(|id| !reaching.iter().any(|r| r == id)) {
        warnings.push(warning(
            "template-not-reaching",
            format!(
                "the template's program is not among the programs whose coverage reaches the \
                 edited rule in the last run ({}); a template built on one of them is suggested",
                reaching.join(", ")
            ),
        ));
    }
    let suggested = reaching
        .iter()
        .map(|id| {
            json!({
                "program": id,
                "template": format!(
                    "[[template]]\nid = \"{id}-holes\"\nprogram = \"{id}\"\n# mark literals \
                     with [[template.hole]] tables\n"
                ),
            })
        })
        .collect::<Vec<_>>();
    json!({
        "found": true,
        "current": true,
        "template": template_row,
        "mutation": {
            "status": entry["status"],
            "reason": entry["reason"],
            "reaching": reaching,
        },
        "suggested_templates": suggested,
    })
}

// ---------------------------------------------------------------------------------------------
// Jobs: kill, reach, pattern
// ---------------------------------------------------------------------------------------------

/// The job of one `kink-flow fuzz` command.
#[derive(Clone, Copy, Debug)]
pub enum FuzzJob<'a> {
    /// `--kill MUTATION --mutations MUTATIONS.toml`: hole values whose program kills the mutation.
    Kill {
        list: &'a MutationList,
        mutation: &'a str,
    },
    /// `--reach RULE [--fired]`: hole values whose program's all-paths baseline run is comparable
    /// and reaches the rule's condition (kink's `reached_by`), or with `fired` takes the rule's
    /// step on some path (`fired_by`, k-rust `committed`).
    Reach { rule: &'a str, fired: bool },
    /// `--pattern ID --patterns PATTERNS.toml`: hole values whose program reaches a configuration
    /// matching the pattern (a `hit` of kink's `query`).
    Pattern { list: &'a PatternList, id: &'a str },
}

impl FuzzJob<'_> {
    const fn kind(&self) -> &'static str {
        match self {
            Self::Kill { .. } => "kill",
            Self::Reach { .. } => "reach",
            Self::Pattern { .. } => "pattern",
        }
    }
}

/// `kink-flow fuzz FLOW.toml TEMPLATES.toml --template ID --kill MUTATION --mutations
/// MUTATIONS.toml`: the document and whether the job was done (a witness, or none within the
/// budget or the time limit); `false` when an input, the template or the mutation is refused, the
/// campaign is `not-comparable`, or a run failed.
pub fn kill(
    manifest: &FlowManifest,
    templates: &TemplateList,
    template: &str,
    list: &MutationList,
    mutation: &str,
    options: &FuzzOptions,
) -> (Value, bool) {
    fuzz_job(
        manifest,
        templates,
        template,
        FuzzJob::Kill { list, mutation },
        options,
    )
}

/// The document of one job ([`kill`] for the kill job) and whether the job was done.
#[allow(clippy::too_many_lines)]
pub fn fuzz_job(
    manifest: &FlowManifest,
    templates: &TemplateList,
    template: &str,
    job: FuzzJob<'_>,
    options: &FuzzOptions,
) -> (Value, bool) {
    let mut document = document();
    document["job"] = json!({
        "kind": job.kind(),
        "outcome": "pending",
        "path_mode": match options.paths {
            PathMode::AllPaths => "all-paths",
            PathMode::OnePath => "one-path",
        },
    });
    if let FuzzJob::Kill { mutation, .. } = job {
        document["job"]["mutation"] = json!(mutation);
    }
    // A pattern target reads no data end, so the campaign takes no assumed name (k-rust-fuzz
    // refuses names on such a target), not even the flow's.
    let reads_data = !matches!(job, FuzzJob::Pattern { .. });
    document["assumed"] = if reads_data {
        assumed_value(manifest, options, None)
    } else {
        json!([])
    };
    let refuse = |mut document: Value, refusal: Refusal, action: &str| {
        document["job"]["outcome"] = json!("refused");
        document["job"]["refusal"] = refusal.value();
        document["stopped"] = json!("refused");
        document["action"] = json!(action);
        (document, false)
    };
    let Some(template) = templates.get(template) else {
        let refusal = Refusal::new(
            "template",
            "unknown-template",
            format!("no template {template:?}"),
        );
        return refuse(document, refusal, "name a template of TEMPLATES.toml");
    };
    let mutation_entry = match job {
        FuzzJob::Kill { list, mutation } => {
            let Some(entry) = list.mutations.iter().find(|m| m.id == mutation) else {
                let refusal = Refusal::new(
                    "mutation",
                    "unknown-mutation",
                    format!("no mutation {mutation:?}"),
                );
                return refuse(document, refusal, "name a mutation of MUTATIONS.toml");
            };
            Some(entry)
        }
        FuzzJob::Reach { .. } | FuzzJob::Pattern { .. } => None,
    };
    let pattern_entry = match job {
        FuzzJob::Pattern { list, id } => {
            let Some(entry) = list.patterns.iter().find(|p| p.id == id) else {
                let refusal =
                    Refusal::new("pattern", "unknown-pattern", format!("no pattern {id:?}"));
                return refuse(document, refusal, "name a pattern of PATTERNS.toml");
            };
            Some(entry)
        }
        FuzzJob::Kill { .. } | FuzzJob::Reach { .. } => None,
    };
    let (record, admitted) = admit_spec(manifest);
    let Some((spec, mut inputs)) = admitted else {
        let refusal = record.refusal.as_ref().map_or_else(
            || Refusal::new("spec", "refused", ""),
            |r| Refusal {
                stage: "spec",
                reason: r.reason.clone(),
                detail: format!("{}: {}", r.stage, r.detail),
            },
        );
        document["spec"] = refusal.value();
        document["stopped"] = json!("refused");
        document["action"] =
            json!("fix the specification: `kink-flow check` gives the same refusal");
        return (document, false);
    };
    document["spec"] = json!({
        "outcome": "admitted",
        "assume_joined": manifest.spec.assume_joined,
        "has_data": spec.data.has_data(),
        "unnamed_findings": spec.data.unnamed().iter().map(|f| f.value()).collect::<Vec<_>>(),
    });
    let instance = match instance(template, templates, manifest, &inputs, &spec) {
        Ok(instance) => instance,
        Err(refusal) => return refuse(document, refusal, "fix the template"),
    };
    document["template"] = json!({
        "id": template.id,
        "source": match &template.source {
            TemplateSource::Program(id) => json!({"program": id}),
            TemplateSource::File(file) => json!({"file": file}),
            TemplateSource::Text(_) => json!({"text": true}),
        },
        "start_sort": instance.start_sort,
        "start_sort_source": instance.start_sort_source,
        "variables": instance
            .variables
            .iter()
            .map(|(name, text)| json!({"name": name, "text": text}))
            .collect::<Vec<_>>(),
        "holes": serde_json::to_value(&template.holes).expect("hole declarations encode"),
        "last_run": null,
    });
    let mut warnings = Vec::new();
    if options.time_limit_ms.is_some() {
        warnings.push(warning(
            "time-limit-scope",
            "--time-limit-ms bounds the campaign's run only: kink's admission, the mutant's \
             preparation, the definition exclusions and the campaign's setup (k-rust-fuzz \
             Campaign::new: both grammars and backends, and both definitions' full critical-pair \
             checks) run before the watchdog starts, and the confirmation by kink's own code runs \
             after it (kink's `time_ms` bounds each of its runs); no time limit bounds them",
        ));
    }
    if let FuzzJob::Kill { mutation, .. } = job {
        document["template"]["last_run"] = last_run(
            manifest,
            &spec,
            options,
            template,
            &instance,
            mutation,
            &mut warnings,
        );
    }
    document["warnings"] = json!(warnings);

    // The job's own target, resolved against the baseline before any campaign; a reach's
    // authored rule is the one whose `results` entry its confirmation reads.
    let mut reach_at = None;
    let kind = match job {
        FuzzJob::Kill { .. } => None,
        FuzzJob::Reach { rule, fired } => match resolve_reach(manifest, &spec, rule, fired) {
            Ok(reach) => {
                document["job"]["rule"] = reach.value();
                reach_at = Some(reach.at.at.clone());
                Some(TargetKind::Rule(RuleTarget {
                    rule: RuleRef::UniqueId(reach.id),
                    mode: if fired {
                        RuleMode::Covered
                    } else {
                        RuleMode::ConditionReached
                    },
                }))
            }
            Err(refusal) => {
                return refuse(
                    document,
                    refusal,
                    "name one authored rewrite rule of the specification: FILE:LINE (a line of the \
                     rule), its label (MODULE.x when the bare label is ambiguous), or its 64-hex \
                     id (the refusal's detail lists the rules nearest the reference, with their \
                     ids, when it finds any)",
                );
            }
        },
        FuzzJob::Pattern { .. } => {
            let entry = pattern_entry.expect("a pattern job has its entry");
            match lower_pattern(manifest, &spec, &entry.pattern) {
                Ok(kore) => {
                    document["job"]["pattern"] =
                        json!({"id": entry.id, "text": entry.pattern, "kore": kore});
                    Some(TargetKind::Pattern(PatternTarget {
                        pattern: entry.pattern.clone(),
                        at: PatternAt::AnyState,
                    }))
                }
                Err(refusal) => {
                    document["job"]["pattern"] = json!({"id": entry.id, "text": entry.pattern});
                    return refuse(
                        document,
                        refusal,
                        "fix the pattern: kink's `query` refuses it the same way (invalid-pattern)",
                    );
                }
            }
        }
    };

    // The mutant, exactly as kink's runner prepares it for every test of the mutation.
    let mutant = match mutation_entry {
        None => None,
        Some(mutation_entry) => {
            let resolved = match resolve(manifest, &spec.loaded, mutation_entry) {
                Ok(resolved) => resolved,
                Err(invalid) => {
                    document["job"]["status"] = json!(invalid.reason.status());
                    document["job"]["reason"] = json!(invalid.reason.as_str());
                    document["job"]["detail"] = json!(invalid.to_string());
                    let refusal =
                        Refusal::new("mutation", invalid.reason.as_str(), invalid.to_string());
                    return refuse(
                        document,
                        refusal,
                        "fix the mutation: it does not resolve (kink-flow run gives the same \
                         status)",
                    );
                }
            };
            let baseline = spec.validator.baseline();
            let admission = MutantAdmission::new(
                baseline,
                &spec.compiled,
                &k_rust::kast::identifier::encode(&manifest.spec.main_module),
                &manifest.spec.assume_joined,
            );
            match claim_free_mutant(
                &spec.validator,
                &spec.compiled,
                &resolved.patch,
                &admission,
                &mut |_| {},
            ) {
                Ok(mutant) => {
                    document["job"]["claims"] = claims_value(baseline, &mutant.claims);
                    document["job"]["mutant_unnamed_findings"] =
                        Value::Array(mutant.data.unnamed().iter().map(|f| f.value()).collect());
                    Some(mutant)
                }
                Err(refusal) => {
                    let status = status_name(refusal.failure.status());
                    let reason = kebab(&format!("{:?}", refusal.failure));
                    document["job"]["status"] = json!(status);
                    document["job"]["reason"] = json!(reason);
                    document["job"]["claims"] = claims_value(baseline, &refusal.claims);
                    document["job"]["inconsistent_pairs"] = Value::Array(
                        refusal
                            .inconsistent_pairs
                            .iter()
                            .map(kink_native::consistency::UnjoinedEquations::value)
                            .collect(),
                    );
                    let detail = format!("kink's mutant preparation: {status} ({reason})");
                    return refuse(
                        document,
                        Refusal::new("mutant", reason, detail),
                        "no mutant to fuzz: kink refuses this mutation the same way in \
                         `kink-flow run`",
                    );
                }
            }
        }
    };

    // kink's definition exclusions (design 3.2.4): one on the mutant makes every test of the
    // mutation unknown in kink's run; one on the baseline makes every program's baseline result
    // unknown (excluded), so no program is comparable and nothing can kill, reach or hit. Either
    // way no witness could be confirmed. A reach or pattern job has the baseline alone.
    let module = k_rust::kast::identifier::encode(&manifest.spec.main_module);
    let mut exclusions = serde_json::Map::new();
    let mut sides_to_check = vec![("baseline", &spec.compiled)];
    if let Some(mutant) = &mutant {
        sides_to_check.push(("mutant", &mutant.side));
    }
    // Each side's load, in side order, kept for the witness filter.
    let mut loads = Vec::new();
    for (role, side) in sides_to_check {
        match side_exclusion(side, &module) {
            Ok((load, None)) => {
                exclusions.insert(role.into(), Value::Null);
                if options.filter {
                    loads.push(load);
                }
            }
            Ok((_, Some((exclusion, detail)))) => {
                exclusions.insert(
                    role.into(),
                    json!({"exclusion": exclusion.name(), "detail": detail}),
                );
                document["job"]["exclusions"] = Value::Object(exclusions);
                if mutant.is_some() {
                    // The status and reason kink's `run` gives the mutation.
                    let (status, reason) = if role == "baseline" {
                        ("error", "no-comparable-program")
                    } else {
                        ("unknown", exclusion.name())
                    };
                    document["job"]["status"] = json!(status);
                    document["job"]["reason"] = json!(reason);
                }
                let detail = format!(
                    "the {role}'s definition has kink's definition exclusion {}: {detail}",
                    exclusion.name()
                );
                let action = if role == "baseline" {
                    "kink excludes every run on this specification, so every program's result is \
                     unknown and no witness could be confirmed (`kink-flow run` gives each \
                     mutation status error, no-comparable-program, and each program the exclusion \
                     as its cause): fix the specification"
                } else {
                    "kink reports this mutation unknown with this reason (every test of the \
                     mutant is excluded), so no program can kill it: choose another mutation \
                     (`kink-flow run` gives the same reason)"
                };
                return refuse(
                    document,
                    Refusal::new("exclusions", exclusion.name(), detail),
                    action,
                );
            }
            Err(error) => {
                return refuse(
                    document,
                    Refusal::new(
                        "exclusions",
                        "exclusions-unavailable",
                        format!("the {role}'s definition exclusions: {error}"),
                    ),
                    "report this: kink's exclusions of the side could not be read",
                );
            }
        }
    }
    document["job"]["exclusions"] = Value::Object(exclusions);

    let sides = compiled_side(manifest, &spec, &spec.compiled).and_then(|baseline_side| {
        mutant
            .as_ref()
            .map(|mutant| compiled_side(manifest, &spec, &mutant.side))
            .transpose()
            .map(|mutant_side| (baseline_side, mutant_side))
    });
    let (baseline_side, mutant_side) = match sides {
        Ok(sides) => sides,
        Err(error) => {
            return refuse(
                document,
                Refusal::new("sides", "conversion-failed", error.to_string()),
                "report this: kink's sides do not convert into k-rust-fuzz definitions",
            );
        }
    };
    document["sides"] = json!({
        "baseline": side_value(&spec.compiled, &baseline_side),
    });
    if let (Some(mutant), Some(mutant_side)) = (&mutant, &mutant_side) {
        document["sides"]["mutant"] = side_value(&mutant.side, mutant_side);
    }

    let target = match kind {
        // Kill: the mutant's clean end outside the baseline's complete set of ends.
        None => Target {
            kind: TargetKind::Differential(DifferentialTarget::default()),
            run_to_completion: false,
            negated_property: false,
            data_end: true,
            // Both options judge rule and pattern hits only; a differential target ignores them.
            comparable: false,
            query_confirmable: false,
        },
        // Reach: kink counts a program in `reached_by` (`fired_by`) only when its all-paths
        // baseline run is comparable, so the hit's run of every path must be (`comparable`),
        // which also needs data ends.
        Some(kind @ TargetKind::Rule(_)) => Target {
            kind,
            run_to_completion: true,
            negated_property: false,
            data_end: true,
            comparable: true,
            query_confirmable: false,
        },
        // Pattern: a query `hit` needs some reached configuration that matches, so the pattern
        // is matched at every configuration (`any-state`), with the facts a complete search
        // could stop at refused (`query-confirmable`).
        Some(kind) => Target {
            kind,
            run_to_completion: false,
            negated_property: false,
            data_end: false,
            comparable: false,
            query_confirmable: true,
        },
    };
    let budget = manifest.budget;
    let campaign_spec = CampaignSpec {
        definitions: Definitions {
            baseline: Arc::new(baseline_side),
            mutant: mutant_side.map(Arc::new),
        },
        program: ProgramInput::Source(FuzzProgram {
            program: Some(ProgramText {
                name: template.id.clone(),
                text: instance.text.clone(),
                start_sort: instance.start_sort.clone(),
            }),
            config_vars: campaign_variables(&spec, &instance),
        }),
        holes: template.holes.clone(),
        target,
        options: CaseOptions {
            paths: options.paths,
            max_depth: Some(budget.max_depth),
            max_work: Some(options.max_work.unwrap_or(DEFAULT_MAX_WORK)),
            safety_limit_ms: Some(budget.time_ms),
            assume_joined: if reads_data {
                assumed_names(manifest, options)
            } else {
                Vec::new()
            },
            ..CaseOptions::default()
        },
        proposers: ProposerConfig::default(),
        bounds: GenerationBounds::default(),
        rejection_cap: DEFAULT_REJECTION_CAP,
        seed: options.seed,
        identity: CallerIdentity {
            k_rust_revision: k_rust::build_identity().to_owned(),
            thread_stack_size: Some(DEFINITION_STACK_BYTES as u64),
        },
    };
    let mut campaign = match Campaign::new(campaign_spec) {
        Ok(campaign) => campaign,
        Err(error) => {
            return refuse(
                document,
                Refusal::new("campaign", "campaign-refused", error.to_string()),
                "fix the template's holes or the assumed names: the detail says which",
            );
        }
    };

    // The up-front assembly check (design 3.2.5): a run of no case gives each side's initial
    // configuration at the holes' anchors (the identity's digests). kink assembles both sides'
    // inputs from the baseline, so a mutant that assembles the template otherwise (an edit of a
    // `[macro]` rule) would judge an input kink never runs; and a baseline that assembles it
    // otherwise than kink would make every candidate an assembly mismatch.
    let zero = campaign.run(Budget::Cases(0), None);
    let anchor = |role| {
        zero.identity
            .definitions
            .iter()
            .find(|definition| definition.role == role)
            .and_then(|definition| definition.initial_configuration_digest.clone())
    };
    let (baseline_anchor, mutant_anchor) = (
        anchor(k_rust_fuzz::report::DefinitionRole::Baseline),
        anchor(k_rust_fuzz::report::DefinitionRole::Mutant),
    );
    let template_input = template_program(template, &instance);
    let kink_template = inputs.test_case(&spec, &template_input, instance.text.clone());
    let kink_digest = kink_template
        .as_ref()
        .ok()
        .map(|test| digest_hex(test.initial_state.to_string().as_bytes()));
    document["assembly"] = json!({
        "kink_template": match &kink_template {
            Ok(_) => json!({"sha256": kink_digest}),
            Err(refusal) => json!({
                "refused": {"stage": refusal.stage, "reason": refusal.reason, "detail": refusal.detail},
            }),
        },
        "baseline_anchor": baseline_anchor,
        "mutant_anchor": mutant_anchor,
    });
    if let Err(refusal) = &kink_template {
        push_warning(
            &mut document,
            warning(
                "unusable-template",
                format!(
                    "kink refuses the template's own input ({}: {}): a program from this \
                     template may be refused the same way",
                    refusal.reason, refusal.detail
                ),
            ),
        );
    }
    if let (Some(baseline), Some(mutant)) = (&baseline_anchor, &mutant_anchor)
        && baseline != mutant
    {
        return refuse(
            document,
            Refusal::new(
                "assembly",
                "mutant-assembly-differs",
                format!(
                    "the mutant parses the template differently from kink's input: at the \
                     holes' anchors its initial configuration (sha256 {mutant}) is not the \
                     baseline's (sha256 {baseline}), while kink assembles every test's input \
                     from the baseline (an edit of a [macro] rule, or of what the program's \
                     parse reads)"
                ),
            ),
            "no witness of this campaign could be kink's: the fuzz would run the mutant on \
             another input than kink does. Choose another mutation, or kill this one with a \
             program whose text does not reach the edited parse",
        );
    }
    if let (Some(baseline), Some(kink)) = (&baseline_anchor, &kink_digest)
        && baseline != kink
    {
        return refuse(
            document,
            Refusal::new(
                "assembly",
                "template-assembly-differs",
                format!(
                    "the campaign's baseline assembles the template at the holes' anchors \
                     (sha256 {baseline}) differently from kink's assembly of the template \
                     (sha256 {kink})"
                ),
            ),
            "report this: k-rust-fuzz and kink assemble the template into different initial \
             configurations (grammar, bindings or stream defaults), so every candidate would \
             be an assembly mismatch",
        );
    }

    // The witness filter (fz26 FZ-COMPARABLE-B): kink's rules judge each candidate inside the
    // campaign, on the loads the exclusions were read from, with the data facts of the names
    // kink's confirmation judges under (the flow's and the command line's).
    let mut filter = None;
    if options.filter {
        let mut loads = loads.into_iter();
        let job_kind = match job {
            FuzzJob::Kill { .. } => FilterJob::Kill,
            FuzzJob::Reach { .. } => FilterJob::Reach,
            FuzzJob::Pattern { .. } => FilterJob::Pattern,
        };
        let baseline = loads
            .next()
            .map(|load| FilterSide::new(load, spec.data.clone()));
        let mutant_side = mutant
            .as_ref()
            .and_then(|mutant| Some(FilterSide::new(loads.next()?, mutant.data.clone())));
        if let Some(mut baseline) = baseline {
            let mut mutant_side = mutant_side;
            let added = options
                .assume_joined
                .iter()
                .any(|name| !manifest.spec.assume_joined.contains(name));
            if reads_data && added {
                let names = assumed_names(manifest, options);
                for side in std::iter::once(&mut baseline).chain(mutant_side.as_mut()) {
                    if let Err(error) = side.recompute_data(&names) {
                        return refuse(
                            document,
                            Refusal::new("filter", "filter-unavailable", error),
                            "report this: kink's data facts of a side could not be read for the \
                             witness filter (--no-filter runs without it)",
                        );
                    }
                }
            }
            let mut judgement =
                KinkJudgement::new(job_kind, baseline, mutant_side, manifest.budget.work());
            // Hole values add no hooked or function application to the template, so a state
            // exclusion of the anchors' input is one of every candidate's: no witness could be
            // confirmed.
            if let Ok(test) = &kink_template
                && let Some((role, exclusion)) = judgement.initial_exclusion(&test.initial_state)
            {
                document["job"]["filter"] = json!({"on": true, "id": null});
                return refuse(
                    document,
                    Refusal::new(
                        "filter",
                        "initial-state-excluded",
                        format!(
                            "kink's input of the template has the exclusion {exclusion} on the \
                             {role}'s definition, so kink takes no evidence from any program of \
                             this template"
                        ),
                    ),
                    "choose a template whose input applies no implementation-chosen hook and no \
                     function whose value depends on the short-circuit reading (kink-flow run gives \
                     such a program the exclusion as its cause)",
                );
            }
            filter = Some(judgement);
        }
    }
    let (report, fired) = under_watchdog(
        options.time_limit_ms.map(Duration::from_millis),
        |token| match filter.as_mut() {
            Some(filter) => campaign.run_filtered(options.budget, token, filter),
            None => campaign.run(options.budget, token),
        },
    );
    drop(filter);
    document["job"]["outcome"] = json!("fuzzed");
    document["job"]["filter"] = json!({"on": options.filter, "id": report.identity.filter});
    let refused = &report.totals.filter.refused;
    if !refused.is_empty() {
        let causes = refused
            .iter()
            .map(|(cause, count)| format!("{count} {cause}"))
            .collect::<Vec<_>>()
            .join(", ");
        push_warning(
            &mut document,
            warning(
                "client-refused",
                format!(
                    "kink's rules, as the witness filter reads them, refused candidate hits inside \
                     the campaign ({causes}), each judged before its confirmation (the filter is \
                     stricter than kink's own run only where the README says); the fuzz report's \
                     client-refusals give each cause's first case and kink's reason"
                ),
            ),
        );
    }
    document["findings"] = Value::Array(
        report
            .definition_findings
            .iter()
            .map(finding_value)
            .collect(),
    );
    if reads_data {
        document["assumed"] = assumed_value(manifest, options, Some(&report));
    }
    // A crash is no kill and moves no verdict: one warning per crash, for its report
    // (FZ-CRASH).
    for line in report.crashes.lines() {
        push_warning(&mut document, warning("crash", line));
    }
    let fuzz =
        serde_json::from_str::<Value>(&report.to_canonical_json()).expect("a fuzz report is JSON");
    let mut attempt = json!({
        "seed": options.seed.to_string(),
        "fuzz": fuzz,
        "candidate": null,
        "confirmation": null,
    });
    // What the job looks for, for the actions below.
    let sought = match job {
        FuzzJob::Kill { .. } => {
            "choose a template whose run reaches the edited rule and ends on both sides"
        }
        FuzzJob::Reach { .. } => {
            "choose a template whose run comes near the rule, and ends on every path with values"
        }
        FuzzJob::Pattern { .. } => "choose a template whose run comes near the pattern",
    };
    let ok = match &report.outcome {
        CampaignOutcome::WitnessFound { witness } => {
            // The candidates, in order: the shrunk case (else the first), then the first when
            // kink refuses the shrunk one and the first is another program (KF-T4).
            let mut cases = vec![
                witness
                    .shrunk
                    .as_ref()
                    .map_or((&witness.first, "first"), |shrunk| (shrunk, "shrunk")),
            ];
            if witness.shrunk.is_some() && options.confirm {
                cases.push((&witness.first, "first"));
            }
            let premises = if reads_data {
                premises(manifest, options, &report)
            } else {
                Vec::new()
            };
            let mut refused = Vec::new();
            let mut offered = None;
            let mut offered_case = None;
            for (case, which) in cases {
                let fragment = fragment(template, &instance, case);
                if refused
                    .iter()
                    .any(|(id, _): &(String, Value)| id == &fragment.id)
                {
                    continue;
                }
                let mut candidate = serde_json::to_value(case).expect("a witness case encodes");
                candidate["case"] = json!(which);
                let assembly =
                    check_assembly(&spec, &mut inputs, &fragment.program, &fragment.text, case);
                candidate["assembly"] = assembly.value();
                if assembly != AssemblyCheck::Match {
                    if offered.is_none() && refused.is_empty() {
                        attempt["candidate"] = candidate;
                        document["stopped"] = json!("assembly-mismatch");
                        document["action"] = json!(format!(
                            "the witness is no kink witness: kink's assembly of its program does \
                             not give the input the campaign judged ({}); nothing is offered. \
                             Report it, or try another seed or template",
                            match &assembly {
                                AssemblyCheck::Mismatch { detail, .. } => detail.clone(),
                                AssemblyCheck::Refused { reason, detail } => {
                                    format!("kink refuses the program's input, {reason}: {detail}")
                                }
                                AssemblyCheck::Match => unreachable!(),
                            }
                        ));
                        document["attempts"] = json!([attempt]);
                        return (document, true);
                    }
                    continue;
                }
                if !options.confirm {
                    attempt["candidate"] = candidate;
                    offered = Some((fragment, false));
                    offered_case = Some(case);
                    break;
                }
                let mut confirmation =
                    confirm(manifest, options, job, reach_at.as_ref(), &fragment.program);
                confirmation["case"] = json!(which);
                let confirmed = confirmation["confirmed"] == true;
                attempt["candidate"] = candidate;
                attempt["confirmation"] = confirmation.clone();
                if confirmed {
                    offered = Some((fragment, true));
                    offered_case = Some(case);
                    break;
                }
                refused.push((fragment.id.clone(), confirmation));
            }
            if refused.len() > 1 {
                attempt["refused_confirmations"] =
                    Value::Array(refused.iter().map(|(_, c)| c.clone()).collect());
            } else if let (Some(_), [(_, earlier)]) = (&offered, refused.as_slice()) {
                attempt["refused_confirmations"] = json!([earlier]);
            }
            let Some((fragment, confirmed)) = offered else {
                // Every candidate kink was asked about was refused.
                let (_, last) = refused.last().expect("a refused candidate");
                document["stopped"] = json!("unconfirmed");
                document["action"] = json!(format!(
                    "kink's own {} does not confirm the witness ({}: {}); nothing is offered. \
                     Try another template, seed or hole range",
                    match job {
                        FuzzJob::Kill { .. } => "run",
                        FuzzJob::Reach { .. } => "results",
                        FuzzJob::Pattern { .. } => "query",
                    },
                    last["status"].as_str().unwrap_or("refused"),
                    last["cause"]
                        .as_str()
                        .map_or_else(|| last["reason"].to_string(), str::to_owned),
                ));
                document["attempts"] = json!([attempt]);
                return (document, true);
            };
            // A witness whose run of every path a bound or a clock cut may not terminate: as a
            // corpus program it runs to the budget in every `run` and `results`, and is never
            // comparable (final review ux S8). Only a pattern witness can be one: a reach
            // witness's run is comparable, and a kill's two runs end.
            if let Some(comparable) = offered_case.and_then(|case| case.comparable.as_ref()) {
                let cuts = comparable
                    .reasons
                    .iter()
                    .filter(|reason| {
                        matches!(
                            reason,
                            ComparableCondition::WorkBound
                                | ComparableCondition::DepthBound
                                | ComparableCondition::Clock
                        )
                    })
                    .map(|reason| reason.name())
                    .collect::<Vec<_>>();
                if !cuts.is_empty() {
                    push_warning(
                        &mut document,
                        warning(
                            "witness-not-terminating",
                            format!(
                                "the witness program's run of every path did not end within \
                                 the bounds ({}): it reaches the target, but as a test it may \
                                 not terminate, so every `run` and `results` would run it to \
                                 the budget and kink would never count it comparable; prefer \
                                 hole values or a template whose run ends",
                                cuts.join(", ")
                            ),
                        ),
                    );
                }
            }
            let (id, file) = (fragment.id.clone(), fragment.file.clone());
            document["program"] = json!({
                "id": id,
                "fragment": fragment.toml,
                "file": file,
                "premises": premises,
                "confirmed": confirmed,
            });
            let missing = premises
                .iter()
                .filter(|p| p["in_flow"] == false)
                .filter_map(|p| p["name"].as_str())
                .collect::<Vec<_>>();
            let append = format!(
                "append the [[program]] fragment to FLOW.toml (as text, or write the text to {} \
                 and give it as file)",
                file.as_deref().unwrap_or("a file")
            );
            let mut action = if confirmed {
                format!(
                    "{append}: kink's own {} confirmed it on the flow with this program alone",
                    match job {
                        FuzzJob::Kill { .. } => "run (killed, with the fragment as killer)",
                        FuzzJob::Reach { .. } => "results (comparable, and listed for the rule)",
                        FuzzJob::Pattern { .. } => "query (the claim is confirmed)",
                    }
                )
            } else {
                let mut action = match job {
                    FuzzJob::Kill { mutation, .. } => format!(
                        "{append}, then run `kink-flow run FLOW.toml MUTATIONS.toml --only \
                         {mutation}`: kink's own run proves the kill and writes the hint"
                    ),
                    FuzzJob::Reach { fired, .. } => format!(
                        "{append}, then run `kink-flow results FLOW.toml`: the rule's {} lists \
                         the program once kink's own run of it is comparable",
                        if fired { "fired_by" } else { "reached_by" }
                    ),
                    FuzzJob::Pattern { id: pattern, .. } => format!(
                        "{append}, add {id:?} to the `programs` of pattern {pattern:?} in \
                         PATTERNS.toml, then run `kink-flow query FLOW.toml PATTERNS.toml --only \
                         {pattern}`: kink's own search confirms the claim"
                    ),
                };
                action.push_str(". This command did not confirm it (--no-confirm)");
                action
            };
            if !missing.is_empty() {
                action.push_str(&format!(
                    "; first add to [spec] assume_joined the premises FLOW.toml lacks: {}",
                    missing.join(", ")
                ));
            }
            document["action"] = json!(action);
            true
        }
        CampaignOutcome::NoWitnessFound { no_witness }
            if !report.totals.filter.refused.is_empty() && report.totals.unconfirmed == 0 =>
        {
            // Every hit was one kink's rules refuse (none the filter accepted was lost to its
            // confirmation): no witness kink accepts, which is no sign of survival
            // (FZ-COMPARABLE-B review M5).
            document["stopped"] = json!("client-refused");
            document["action"] = json!(format!(
                "no witness kink accepts: {} Mark other literals as holes, narrow the holes to \
                 values kink compares, or {sought}",
                no_witness.statement
            ));
            true
        }
        CampaignOutcome::NoWitnessFound { no_witness }
            if report.totals.domain.is_some_and(|domain| domain.exhausted) =>
        {
            // Every assignment of the holes ran: no budget was spent, and more cases would only
            // repeat them (final review ux S6).
            document["stopped"] = json!("domain-exhausted");
            document["action"] = json!(format!(
                "no witness: {} Every assignment of the holes ran, so this campaign has no other \
                 case to run: mark more literals as holes, widen their ranges, or {sought}",
                no_witness.statement
            ));
            true
        }
        CampaignOutcome::NoWitnessFound { no_witness } => {
            document["stopped"] = json!("budget");
            // More cases help only a campaign whose cases still found something new: not one
            // whose coverage stopped growing long ago (the statement says so), nor one where the
            // mutant ran out of work where the baseline ended, which no bound decides (the mutant
            // may not terminate on this program, so more cases of it repeat that). Advising more
            // cases there contradicts the statement it follows (final review ux S5).
            let hint = if report.totals.coverage_stalled_since().is_some()
                || report.totals.diverging.is_some()
            {
                "Rather than raising --cases or --work, mark other literals as holes"
            } else {
                "Raise --cases or --work, mark more literals as holes"
            };
            document["action"] = json!(format!(
                "no witness: {} {hint}, or {sought}",
                no_witness.statement
            ));
            true
        }
        CampaignOutcome::RejectedOut { no_witness } => {
            document["stopped"] = json!("rejected-out");
            document["action"] = json!(format!(
                "no witness: {} Most generated values were rejected: narrow the holes' ranges or \
                 choices",
                no_witness.statement
            ));
            true
        }
        CampaignOutcome::Cancelled { no_witness } => {
            document["stopped"] = json!(if fired { "time-limit" } else { "cancelled" });
            document["action"] = json!(format!(
                "no witness before the time limit (outside the determinism contract): {} Raise \
                 --time-limit-ms or lower the budget",
                no_witness.statement
            ));
            true
        }
        CampaignOutcome::Equivalent => {
            document["stopped"] = json!("equivalent");
            document["action"] = json!(
                "the two definitions execute alike (equal execution digests): no input can kill \
                 this mutation"
            );
            true
        }
        CampaignOutcome::NotComparable { .. } => {
            document["stopped"] = json!("not-comparable");
            let names = report
                .definition_findings
                .iter()
                .filter(|f| !f.assumed)
                .map(|f| {
                    format!(
                        "{} ({}, {})",
                        f.name.as_deref().unwrap_or("unnamed"),
                        role_name(f.side),
                        verdict_name(f.verdict)
                    )
                })
                .collect::<Vec<_>>();
            document["action"] = json!(format!(
                "not comparable (the fuzz report's outcome explains the verdicts); findings no \
                 name assumes: {}. Under such a finding the definition may identify the ends a \
                 test compares, so a kill would hold in no model and a reaching program would be \
                 no comparable test; kink refuses kills too (baseline-findings) unless FLOW.toml's \
                 [spec] assume_joined names them. Fix the definition, or name each finding you \
                 accept as a premise with --assume-joined NAME and in [spec] assume_joined (a \
                 decided finding cannot be named; a genuine one is known false)",
                names.join("; ")
            ));
            false
        }
        CampaignOutcome::Aborted { kind, reason, .. } => {
            document["stopped"] = json!("aborted");
            let what = match kind {
                AbortKind::SolverPreludeInconsistent | AbortKind::SolverPreludeMalformed => {
                    "the solver's prelude failed (the definition's SMT text, a user prelude, or \
                     k-rust's SMT translation of them): check the definition's smtlib and \
                     smt-hook attributes, or report it"
                }
                AbortKind::SolverPreludeUnknown => {
                    "the solver could not decide the prelude: try again, or report it"
                }
                AbortKind::SolverInit => {
                    "the solver did not start for this definition (its SMT declarations, \
                     k-rust's translation of them, or the host): report it"
                }
                AbortKind::ClientPanic => {
                    "the campaign's observer panicked (a defect of its client): report it"
                }
                AbortKind::RebuildFailed => {
                    "the campaign's backends did not rebuild after a crash: report it with the \
                     fuzz report's crashes"
                }
                AbortKind::ClientDefect => {
                    "kink-flow's witness filter broke its contract (a defect of kink-flow): \
                     report it, and run with --no-filter meanwhile"
                }
            };
            document["action"] = json!(format!("the campaign aborted: {what}. {reason}"));
            false
        }
    };
    document["attempts"] = json!([attempt]);
    (document, ok)
}

/// One reach job's rule, resolved on the baseline.
struct ReachRule {
    /// The targeted rewrite id.
    id: String,
    /// The authored rule the id belongs to: `results` lists programs under authored rules only.
    at: RuleText,
    /// Equation ids of the same sentence, which the target does not read.
    untargeted: Vec<String>,
    fired: bool,
}

impl ReachRule {
    fn value(&self) -> Value {
        json!({
            "module": self.at.at.module,
            "index": self.at.at.index,
            "file": self.at.file,
            "start_line": self.at.start_line,
            "label": self.at.label,
            "id": self.id,
            "mode": if self.fired { "covered" } else { "condition-reached" },
            "untargeted_ids": self.untargeted,
        })
    }
}

/// The most rules a reach refusal lists as the ones the reference may have meant.
const NEAREST_RULES: usize = 5;

/// Whether `text` is a compiled rule id (64 lowercase hex digits).
fn is_rule_id(text: &str) -> bool {
    text.len() == 64
        && text
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

/// The ids of the baseline's rewrite axioms: a rewrite axiom is a `\rewrites` (k-rust
/// classifies every other `UNIQUE_ID` axiom as an equation of some kind).
fn rewrite_ids(validated: &ValidatedDefinition) -> BTreeSet<String> {
    let Ok(definition) = parse_definition(&validated.artifacts().definition_kore) else {
        return BTreeSet::new();
    };
    definition
        .modules
        .iter()
        .flat_map(|module| &module.sentences)
        .filter_map(|sentence| match sentence {
            Sentence::Axiom {
                pattern,
                attributes,
                ..
            } if matches!(**pattern, KorePattern::Rewrites { .. }) => {
                attributes.0.iter().find_map(|attribute| match attribute {
                    KorePattern::Application { symbol, arguments }
                        if symbol.name == KoreAttribute::UniqueId.as_str() =>
                    {
                        match arguments.as_slice() {
                            [KorePattern::String(id)] => id.as_utf8().ok().map(str::to_owned),
                            _ => None,
                        }
                    }
                    _ => None,
                })
            }
            _ => None,
        })
        .collect()
}

/// Resolve `--reach RULE` on the baseline: `FILE:LINE` (a line inside an authored rule of
/// `FILE`), a label (bare or `MODULE.x`, as a mutation edit's), or a compiled id. The rule's ids
/// with a coverage signal (kink's coverage domain) must hold exactly one rewrite id, which is
/// targeted; the sentence's equation ids are listed as untargeted.
fn resolve_reach(
    manifest: &FlowManifest,
    spec: &AdmittedSpec,
    rule: &str,
    fired: bool,
) -> Result<ReachRule, Refusal> {
    let refused = |reason: &str, detail: String| Refusal::new("reach", reason, detail);
    let authors = RuleAuthors::of(&spec.compiled);
    let domain = coverage_domain(&spec.compiled);
    let rewrites = rewrite_ids(&spec.compiled);
    let texts = rule_texts(manifest, &spec.loaded);
    let (at, ids): (RuleText, Vec<String>) = if is_rule_id(rule) {
        if authors.get(rule).is_none() {
            return Err(refused(
                "unknown-rule-id",
                format!("no axiom of the baseline has the id {rule}"),
            ));
        }
        let Some(at) = texts
            .iter()
            .find(|text| authors.ids_of(&text.at).any(|id| id == rule))
            .cloned()
        else {
            // `results` lists programs under the specification's authored rules only, so no
            // program is ever listed for this id and no reach of it can be confirmed.
            return Err(refused(
                "no-authored-rule",
                format!(
                    "the axiom {rule} was written by no authored rule of the specification (a \
                     prelude rule, or a sentence that is not a rule), and kink's `results` lists \
                     programs under authored rules only"
                ),
            ));
        };
        (at, vec![rule.to_owned()])
    } else {
        let by_line = rule
            .rsplit_once(':')
            .and_then(|(file, line)| Some((file, line.parse::<u32>().ok()?)));
        let matches = match by_line {
            Some((file, line)) => texts
                .iter()
                .filter(|text| {
                    text.file
                        .as_deref()
                        .is_some_and(|name| name == file || name.ends_with(&format!("/{file}")))
                        && text.start_line.is_some_and(|start| start <= line)
                        && text.end_line.is_some_and(|end| line <= end)
                })
                .collect::<Vec<_>>(),
            None => texts
                .iter()
                .filter(|text| {
                    text.label.as_deref().is_some_and(|label| {
                        label == rule
                            || label == format!("{}.{rule}", text.at.module)
                            || (!label.contains('.')
                                && rule.strip_prefix(&format!("{}.", text.at.module))
                                    == Some(label))
                    })
                })
                .collect(),
        };
        // A rule as a refusal lists it: its position, its label, and the ids a reach of it can
        // target (its rewrite ids with a coverage signal), so the author can name it by any of
        // them (final review ux S9: the refusal said "listed" ids and listed none).
        let describe = |text: &RuleText| {
            let ids = authors
                .ids_of(&text.at)
                .filter(|id| rewrites.contains(*id) && domain.contains(*id))
                .collect::<Vec<_>>();
            format!(
                "{}:{} ({}#{}{}) {}",
                text.file.as_deref().unwrap_or("?"),
                text.start_line
                    .map_or_else(|| "?".to_owned(), |l| l.to_string()),
                text.at.module,
                text.at.index,
                text.label
                    .as_deref()
                    .map_or_else(String::new, |label| format!(", label {label}")),
                if ids.is_empty() {
                    "no rewrite id a reach can target".to_owned()
                } else {
                    format!("id {}", ids.join(", "))
                }
            )
        };
        let listing = |texts: &[&RuleText]| {
            texts
                .iter()
                .map(|text| format!("\n  {}", describe(text)))
                .collect::<String>()
        };
        let one = match matches.as_slice() {
            [] => {
                return Err(match by_line {
                    Some((file, line)) => {
                        let in_file = |text: &&RuleText| {
                            text.file.as_deref().is_some_and(|name| {
                                name == file || name.ends_with(&format!("/{file}"))
                            })
                        };
                        let mut nearest = texts.iter().filter(in_file).collect::<Vec<_>>();
                        let detail = if nearest.is_empty() {
                            let files = texts
                                .iter()
                                .filter_map(|text| text.file.as_deref())
                                .collect::<BTreeSet<_>>();
                            format!(
                                "no authored rule of the specification is written in {file:?}; \
                                 the rules are written in: {}",
                                files.into_iter().collect::<Vec<_>>().join(", ")
                            )
                        } else {
                            nearest.sort_by_key(|text| {
                                let start = text.start_line.unwrap_or(u32::MAX);
                                let end = text.end_line.unwrap_or(start);
                                (start.abs_diff(line).min(end.abs_diff(line)), start)
                            });
                            nearest.truncate(NEAREST_RULES);
                            format!(
                                "no authored rule of the specification spans {rule}; the \
                                 nearest are:{}",
                                listing(&nearest)
                            )
                        };
                        refused("no-rule-at-line", detail)
                    }
                    None => {
                        let wanted = rule.to_lowercase();
                        let near = texts
                            .iter()
                            .filter(|text| {
                                text.label.as_deref().is_some_and(|label| {
                                    let label = label.to_lowercase();
                                    label.contains(&wanted) || wanted.contains(&label)
                                })
                            })
                            .take(NEAREST_RULES)
                            .collect::<Vec<_>>();
                        refused(
                            "unknown-label",
                            if near.is_empty() {
                                format!(
                                    "no rule is labelled {rule:?}, and no label contains it; \
                                     name the rule by FILE:LINE instead"
                                )
                            } else {
                                format!(
                                    "no rule is labelled {rule:?}; the labels that contain it, or \
                                     that it contains, are:{}",
                                    listing(&near)
                                )
                            },
                        )
                    }
                });
            }
            [one] => (*one).clone(),
            several => {
                return Err(refused(
                    if by_line.is_some() {
                        "ambiguous-rule-position"
                    } else {
                        "ambiguous-label"
                    },
                    format!(
                        "{rule:?} names several rules:{}\n{}",
                        listing(several),
                        if by_line.is_some() {
                            "give a longer path"
                        } else {
                            "qualify it with the module"
                        }
                    ),
                ));
            }
        };
        let ids = authors.ids_of(&one.at).map(str::to_owned).collect();
        (one, ids)
    };
    let signalled = ids
        .into_iter()
        .filter(|id| domain.contains(id))
        .collect::<Vec<_>>();
    if signalled.is_empty() {
        return Err(refused(
            "no-coverage-signal",
            format!(
                "{rule:?} compiles to no axiom k-rust's run coverage can name (a macro, a claim, \
                 an smt-lemma or non-executable axiom, or nothing), so kink lists it in no \
                 reached_by"
            ),
        ));
    }
    let (targets, untargeted): (Vec<String>, Vec<String>) =
        signalled.into_iter().partition(|id| rewrites.contains(id));
    match targets.as_slice() {
        [] => Err(refused(
            "equation-target",
            format!(
                "{rule:?} compiles to equations only ({}): a reach job targets a rewrite rule, \
                 whose condition a run reaches",
                untargeted.join(", ")
            ),
        )),
        [id] => Ok(ReachRule {
            id: id.clone(),
            at,
            untargeted,
            fired,
        }),
        several => Err(refused(
            "several-rewrite-ids",
            format!(
                "{rule:?} compiles to several rewrite axioms: {}; give one of them with --reach ID",
                several.join(", ")
            ),
        )),
    }
}

/// Lower a pattern's text exactly as kink's `query` does (its rule grammar and execution
/// definition, checked against the baseline search definition): the target's KORE, or the
/// refusal `invalid-pattern` with k-rust's message.
fn lower_pattern(
    manifest: &FlowManifest,
    spec: &AdmittedSpec,
    text: &str,
) -> Result<String, Refusal> {
    let searcher = Searcher::new(spec, &manifest.spec.main_module, manifest.budget)
        .map_err(|detail| Refusal::new("pattern", "search-backend", detail))?;
    let lowering = Lowering::new(spec, &manifest.spec.main_module)
        .map_err(|detail| Refusal::new("pattern", "search-backend", detail))?;
    lowering
        .lower(text, searcher.definition())
        .map(|lowered| lowered.kore())
        .map_err(|detail| Refusal::new("pattern", INVALID_PATTERN, detail))
}

/// A scratch directory, removed when dropped.
struct Scratch(PathBuf);

impl Scratch {
    fn new() -> std::io::Result<Self> {
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_or(0, |d| d.as_nanos());
        let path = std::env::temp_dir().join(format!(
            "kink-flow-fuzz-confirm-{}-{nanos}",
            std::process::id()
        ));
        fs::create_dir_all(&path)?;
        Ok(Self(path))
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

/// kink's own verdict on `program` for `job`, as the fuzz confirms a candidate ([`confirm`]):
/// the seam for checking a program written by hand, or one the fuzz did not find. A reach job's
/// rule is resolved on the admitted baseline as the fuzz resolves it; a specification kink does
/// not admit, or a rule that does not resolve, gives `{confirmed: false, status: "refused",
/// reason, cause}`.
pub fn confirm_program(
    manifest: &FlowManifest,
    options: &FuzzOptions,
    job: FuzzJob<'_>,
    program: &Program,
) -> Value {
    let refused = |reason: &str, cause: String| json!({"confirmed": false, "status": "refused", "reason": reason, "cause": cause});
    let reach_at = match job {
        FuzzJob::Reach { rule, fired } => {
            let (record, admitted) = admit_spec(manifest);
            let Some((spec, _)) = admitted else {
                return record.refusal.as_ref().map_or_else(
                    || refused("refused", String::new()),
                    |r| refused(&r.reason, format!("{}: {}", r.stage, r.detail)),
                );
            };
            match resolve_reach(manifest, &spec, rule, fired) {
                Ok(reach) => Some(reach.at.at),
                Err(refusal) => return refused(&refusal.reason, refusal.detail),
            }
        }
        FuzzJob::Kill { .. } | FuzzJob::Pattern { .. } => None,
    };
    confirm(manifest, options, job, reach_at.as_ref(), program)
}

/// kink's own verdict on a candidate (KF-T4), by kink's code on an overlay of the flow: its
/// `[spec]` with the flow's names and the command line's assumed (sorted, without repeats), its
/// `[budget]`, and `program` (the candidate's fragment) as the only `[[program]]`, with a fresh
/// scratch cache removed on every path, so nothing under the flow's directory or `--cache`
/// changes. A kill is confirmed when `run` kills the mutation with the program as killer; a reach
/// when `results` gives the program class `comparable` and lists it in the `reached_by`
/// (`fired_by`) of the targeted rule, `reach_at`, the authored rule the job resolved (final
/// review S1: a listing under any other rule confirms nothing about the target); a pattern when
/// `query`, asked with `programs = [program]`, confirms the claim. The value is `{confirmed,
/// status, reason, cause}` and the job's `killer`, `class` or `answer`.
fn confirm(
    manifest: &FlowManifest,
    options: &FuzzOptions,
    job: FuzzJob<'_>,
    reach_at: Option<&SentenceRef>,
    program: &Program,
) -> Value {
    let scratch = match Scratch::new() {
        Ok(scratch) => scratch,
        Err(error) => {
            return json!({
                "confirmed": false,
                "status": "error",
                "reason": "scratch-directory",
                "cause": format!("no scratch cache for the confirmation: {error}"),
            });
        }
    };
    let mut overlay = manifest.clone();
    overlay.programs = vec![program.clone()];
    let mut names = manifest.spec.assume_joined.clone();
    names.extend(options.assume_joined.iter().cloned());
    names.sort();
    names.dedup();
    overlay.spec.assume_joined = names;
    let cache = Some(scratch.0.clone());
    let id = program.id.as_str();
    match job {
        FuzzJob::Kill { list, mutation } => {
            let list = MutationList {
                mutations: list
                    .mutations
                    .iter()
                    .filter(|m| m.id == mutation)
                    .cloned()
                    .collect(),
            };
            let (run, _) = crate::search::run_with(
                &overlay,
                &list,
                &RunOptions {
                    only: vec![mutation.to_owned()],
                    cache,
                    order: ProgramOrder::Corpus,
                    compile_workers: Some(1),
                    ..RunOptions::default()
                },
                RunMode::Search,
            );
            let row = run["mutations"]
                .as_array()
                .and_then(|rows| rows.iter().find(|row| row["id"] == mutation))
                .cloned()
                .unwrap_or(Value::Null);
            let program = run["programs"]
                .as_array()
                .and_then(|rows| rows.iter().find(|row| row["id"] == id))
                .cloned()
                .unwrap_or(Value::Null);
            let killed = row["status"] == "killed" && row["killer"] == id;
            let cause = if killed {
                Value::Null
            } else if program["cause"].is_null() {
                run["spec"]["detail"].clone()
            } else {
                program["cause"].clone()
            };
            json!({
                "confirmed": killed,
                "status": row["status"],
                "reason": row["reason"],
                "killer": row["killer"],
                "class": program["class"],
                "cause": cause,
            })
        }
        FuzzJob::Reach { fired, .. } => {
            let (document, _) = crate::results::results(
                &overlay,
                &crate::results::ResultsOptions {
                    cache,
                    ..crate::results::ResultsOptions::default()
                },
            );
            let program = document["programs"]
                .as_array()
                .and_then(|rows| rows.iter().find(|row| row["id"] == id))
                .cloned()
                .unwrap_or(Value::Null);
            let key = if fired { "fired_by" } else { "reached_by" };
            // The targeted rule's own entry: `results` lists each authored rule once, by its
            // `(module, index)`. Without the resolved rule nothing is listed for the target.
            let listed = reach_at.is_some_and(|at| {
                document["rules"].as_array().is_some_and(|rules| {
                    rules.iter().any(|rule| {
                        rule["module"] == at.module.as_str()
                            && rule["index"] == u64::from(at.index)
                            && rule[key]
                                .as_array()
                                .is_some_and(|programs| programs.iter().any(|p| p == id))
                    })
                })
            });
            let comparable = program["class"] == "comparable";
            json!({
                "confirmed": comparable && listed,
                "status": if comparable && listed { "reached" } else { "unreached" },
                "reason": if !comparable {
                    "not-comparable"
                } else if listed {
                    "listed"
                } else {
                    "not-listed"
                },
                "class": program["class"],
                "cause": if program["cause"].is_null() {
                    document["spec"]["detail"].clone()
                } else {
                    program["cause"].clone()
                },
            })
        }
        FuzzJob::Pattern { list, id: pattern } => {
            let claimed = PatternList {
                patterns: list
                    .patterns
                    .iter()
                    .filter(|p| p.id == pattern)
                    .map(|p| crate::pattern::PatternEntry {
                        programs: Some(vec![id.to_owned()]),
                        ..p.clone()
                    })
                    .collect(),
            };
            let (document, _) = crate::query::query(
                &overlay,
                &claimed,
                &crate::query::QueryOptions {
                    only: vec![pattern.to_owned()],
                    cache,
                    verify: false,
                },
            );
            let row = document["rows"]
                .as_array()
                .and_then(|rows| rows.iter().find(|row| row["program"] == id))
                .cloned()
                .unwrap_or(Value::Null);
            json!({
                "confirmed": row["claim"] == "confirmed",
                "status": row["claim"],
                "reason": row["answer"],
                "answer": row["answer"],
                "cause": if row.is_null() {
                    document["spec"]["detail"].clone()
                } else {
                    row["cause"].clone()
                },
            })
        }
    }
}
