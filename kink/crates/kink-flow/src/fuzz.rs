//! `kink-flow fuzz`: a k-rust-fuzz campaign on kink's own sides (fz26 P7-KINKFLOW, tickets T3a
//! and T3b).
//!
//! The command takes a template, a program of the flow with some of its literals marked as holes
//! (`TEMPLATES.toml`, [`TemplateList`]), and one job. T3a builds the kill job: look for hole
//! values that make the template kill one mutation of the flow's list, so that the program can
//! join the corpus and kink's own `run` proves the kill.
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
//! T3a has no confirmation (`--no-confirm` is the only mode): kink's `run` proves the program once
//! it is in the corpus. Nothing is cached and nothing under the flow's directory is written.

use crate::{
    admit::{AdmittedSpec, ProgramInputs, admit_spec},
    digest::{program_digest, spec_digest},
    manifest::{FlowManifest, ManifestError, Program},
    mutation::{MutationList, resolve},
    report::claims_value,
    results::kebab,
    search::status_name,
};
use k_rust::kore::parser::parse_pattern;
use k_rust_fuzz::{
    BackendRoute, Budget, CallerIdentity, Campaign, CampaignSpec, CancellationToken, CaseOptions,
    CompiledDefinition, Definitions, HoleDecl, HoleLocation, PathMode, ProgramInput,
    ProposerConfig, Target, TargetKind,
    error::CampaignError,
    holes::HoleFile,
    report::{
        CampaignOutcome, DefinitionFinding, FindingVerdict, FuzzReport, WitnessCase, digest_hex,
    },
    spec::{DEFAULT_REJECTION_CAP, ProgramSource as FuzzProgram, ProgramText},
    target::DifferentialTarget,
    values::GenerationBounds,
};
use kink_campaign::{MutantAdmission, claim_free_mutant};
use kink_corpus::{ProgramSource, cli::DEFINITION_STACK_BYTES};
use kink_native::{
    K_RUST_REVISION, ValidatedDefinition,
    exclusion::{DefinitionExclusions, Exclusion},
    execution::SolverProfile,
};
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
/// The document's `version`.
pub const FUZZ_VERSION: u32 = 1;
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
/// run on that side: from the side's compiled KORE loaded for `module` on this thread.
fn side_exclusion(
    side: &ValidatedDefinition,
    module: &str,
) -> Result<Option<(Exclusion, String)>, String> {
    let facts = DefinitionExclusions::of_validated(side, module)?;
    Ok(facts
        .definition_exclusion()
        .map(|exclusion| (exclusion, exclusion_detail(&facts, exclusion))))
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
    let mut document = document();
    document["job"] = json!({
        "kind": "kill",
        "mutation": mutation,
        "outcome": "pending",
        "path_mode": match options.paths {
            PathMode::AllPaths => "all-paths",
            PathMode::OnePath => "one-path",
        },
    });
    document["assumed"] = assumed_value(manifest, options, None);
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
    let Some(mutation_entry) = list.mutations.iter().find(|m| m.id == mutation) else {
        let refusal = Refusal::new(
            "mutation",
            "unknown-mutation",
            format!("no mutation {mutation:?}"),
        );
        return refuse(document, refusal, "name a mutation of MUTATIONS.toml");
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
             checks) run before the watchdog starts, and no time limit bounds them",
        ));
    }
    document["template"]["last_run"] = last_run(
        manifest,
        &spec,
        options,
        template,
        &instance,
        mutation,
        &mut warnings,
    );
    document["warnings"] = json!(warnings);

    // The mutant, exactly as kink's runner prepares it for every test of the mutation.
    let resolved = match resolve(manifest, &spec.loaded, mutation_entry) {
        Ok(resolved) => resolved,
        Err(invalid) => {
            document["job"]["status"] = json!(invalid.reason.status());
            document["job"]["reason"] = json!(invalid.reason.as_str());
            document["job"]["detail"] = json!(invalid.to_string());
            let refusal = Refusal::new("mutation", invalid.reason.as_str(), invalid.to_string());
            return refuse(
                document,
                refusal,
                "fix the mutation: it does not resolve (kink-flow run gives the same status)",
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
    let mutant = match claim_free_mutant(
        &spec.validator,
        &spec.compiled,
        &resolved.patch,
        &admission,
        &mut |_| {},
    ) {
        Ok(mutant) => mutant,
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
                "no mutant to fuzz: kink refuses this mutation the same way in `kink-flow run`",
            );
        }
    };
    document["job"]["claims"] = claims_value(baseline, &mutant.claims);
    document["job"]["mutant_unnamed_findings"] =
        Value::Array(mutant.data.unnamed().iter().map(|f| f.value()).collect());

    // kink's definition exclusions (design 3.2.4): one on the mutant makes every test of the
    // mutation unknown in kink's run; one on the baseline makes every program's baseline result
    // unknown (excluded), so no program is comparable and nothing can kill. Either way no witness
    // could be confirmed.
    let module = k_rust::kast::identifier::encode(&manifest.spec.main_module);
    let mut exclusions = serde_json::Map::new();
    for (role, side) in [("baseline", &spec.compiled), ("mutant", &mutant.side)] {
        match side_exclusion(side, &module) {
            Ok(None) => {
                exclusions.insert(role.into(), Value::Null);
            }
            Ok(Some((exclusion, detail))) => {
                exclusions.insert(
                    role.into(),
                    json!({"exclusion": exclusion.name(), "detail": detail}),
                );
                document["job"]["exclusions"] = Value::Object(exclusions);
                // The status and reason kink's `run` gives the mutation.
                let (status, reason) = if role == "baseline" {
                    ("error", "no-comparable-program")
                } else {
                    ("unknown", exclusion.name())
                };
                document["job"]["status"] = json!(status);
                document["job"]["reason"] = json!(reason);
                let detail = format!(
                    "the {role}'s definition has kink's definition exclusion {}: {detail}",
                    exclusion.name()
                );
                let action = if role == "baseline" {
                    "kink excludes every run on this specification, so every program's result is \
                     unknown and no mutation can be killed (`kink-flow run` gives each mutation \
                     status error, no-comparable-program, and each program the exclusion as its \
                     cause): fix the specification"
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
        compiled_side(manifest, &spec, &mutant.side).map(|mutant_side| (baseline_side, mutant_side))
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
        "mutant": side_value(&mutant.side, &mutant_side),
    });

    let budget = manifest.budget;
    let campaign_spec = CampaignSpec {
        definitions: Definitions {
            baseline: Arc::new(baseline_side),
            mutant: Some(Arc::new(mutant_side)),
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
        target: Target {
            kind: TargetKind::Differential(DifferentialTarget::default()),
            run_to_completion: false,
            negated_property: false,
            data_end: true,
            // Both options judge rule and pattern hits only; a differential target ignores them.
            comparable: false,
            query_confirmable: false,
        },
        options: CaseOptions {
            paths: options.paths,
            max_depth: Some(budget.max_depth),
            max_work: Some(options.max_work.unwrap_or(DEFAULT_MAX_WORK)),
            safety_limit_ms: Some(budget.time_ms),
            assume_joined: assumed_names(manifest, options),
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

    let (report, fired) =
        under_watchdog(options.time_limit_ms.map(Duration::from_millis), |token| {
            campaign.run(options.budget, token)
        });
    document["job"]["outcome"] = json!("fuzzed");
    document["findings"] = Value::Array(
        report
            .definition_findings
            .iter()
            .map(finding_value)
            .collect(),
    );
    document["assumed"] = assumed_value(manifest, options, Some(&report));
    let fuzz =
        serde_json::from_str::<Value>(&report.to_canonical_json()).expect("a fuzz report is JSON");
    let mut attempt = json!({
        "seed": options.seed.to_string(),
        "fuzz": fuzz,
        "candidate": null,
        "confirmation": null,
    });
    let ok = match &report.outcome {
        CampaignOutcome::WitnessFound { witness } => {
            let (case, which) = witness
                .shrunk
                .as_ref()
                .map_or((&witness.first, "first"), |shrunk| (shrunk, "shrunk"));
            let mut candidate = serde_json::to_value(case).expect("a witness case encodes");
            candidate["case"] = json!(which);
            let fragment = fragment(template, &instance, case);
            let assembly =
                check_assembly(&spec, &mut inputs, &fragment.program, &fragment.text, case);
            candidate["assembly"] = assembly.value();
            attempt["candidate"] = candidate;
            if assembly != AssemblyCheck::Match {
                document["stopped"] = json!("assembly-mismatch");
                document["action"] = json!(format!(
                    "the witness is no kink witness: kink's assembly of its program does not \
                     give the input the campaign judged ({}); nothing is offered. Report it, or \
                     try another seed or template",
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
            let (id, file) = (fragment.id.clone(), fragment.file.clone());
            let premises = premises(manifest, options, &report);
            document["program"] = json!({
                "id": id,
                "fragment": fragment.toml,
                "file": file,
                "premises": premises,
                "confirmed": false,
            });
            let missing = premises
                .iter()
                .filter(|p| p["in_flow"] == false)
                .filter_map(|p| p["name"].as_str())
                .collect::<Vec<_>>();
            let mut action = format!(
                "append the [[program]] fragment to FLOW.toml (as text, or write the text to {} \
                 and give it as file), then run `kink-flow run FLOW.toml MUTATIONS.toml --only \
                 {mutation}`: kink's own run proves the kill and writes the hint. This command did \
                 not confirm it (--no-confirm)",
                file.as_deref().unwrap_or("a file")
            );
            if !missing.is_empty() {
                action.push_str(&format!(
                    "; first add to [spec] assume_joined the premises FLOW.toml lacks: {}",
                    missing.join(", ")
                ));
            }
            document["action"] = json!(action);
            true
        }
        CampaignOutcome::NoWitnessFound { no_witness } => {
            document["stopped"] = json!("budget");
            document["action"] = json!(format!(
                "no witness: {} Raise --cases or --work, mark more literals as holes, or choose \
                 a template whose run reaches the edited rule and ends on both sides",
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
                 kill compares, so a kill would hold in no model; kink refuses it too \
                 (baseline-findings) unless FLOW.toml's [spec] assume_joined names them. Fix \
                 the definition, or name each finding you accept as a premise with \
                 --assume-joined NAME and in [spec] assume_joined (a decided finding cannot be \
                 named; a genuine one is known false)",
                names.join("; ")
            ));
            false
        }
        CampaignOutcome::Aborted { reason, .. } => {
            document["stopped"] = json!("aborted");
            document["action"] = json!(format!("the campaign aborted: {reason}"));
            false
        }
    };
    document["attempts"] = json!([attempt]);
    (document, ok)
}
