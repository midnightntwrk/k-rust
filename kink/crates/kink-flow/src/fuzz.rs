//! `kink-flow fuzz`: a k-rust-fuzz campaign on kink's own sides (fz26 P7-KINKFLOW, ticket T3a).
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
    digest::program_digest,
    manifest::{FlowManifest, ManifestError, Program},
    mutation::{MutationList, resolve},
    report::claims_value,
    results::kebab,
    search::status_name,
};
use k_rust_fuzz::{
    BackendRoute, Budget, CallerIdentity, Campaign, CampaignSpec, CancellationToken, CaseOptions,
    CompiledDefinition, Definitions, HoleDecl, HoleLocation, PathMode, ProgramInput,
    ProposerConfig, Target, TargetKind,
    error::CampaignError,
    holes::HoleFile,
    report::{CampaignOutcome, DefinitionFinding, FindingVerdict, FuzzReport, WitnessCase},
    spec::{DEFAULT_REJECTION_CAP, ProgramSource as FuzzProgram, ProgramText},
    target::DifferentialTarget,
    values::GenerationBounds,
};
use kink_campaign::{MutantAdmission, claim_free_mutant};
use kink_corpus::{ProgramSource, cli::DEFINITION_STACK_BYTES};
use kink_native::{K_RUST_REVISION, ValidatedDefinition, execution::SolverProfile};
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
    /// may only name a binding (`"$NAME"`): by default a hole addresses the template's text.
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
    if file.program.is_some() {
        // The fragment would need the binding's instantiated text, which the fuzz report does
        // not carry (it has the program's): refused until the report or the library gives it.
        return Err(ManifestError::new(
            join(&hole_key, "program"),
            "a hole in a binding's text is not supported by kink-flow fuzz yet; make the whole \
             binding a hole with `config-var`",
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
        "findings": [],
        "assumed": [],
        "attempts": [],
        "program": null,
        "stopped": null,
        "action": null,
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

/// The `[[program]]` fragment of a witness case, as TOML text, and its id.
fn fragment(
    template: &Template,
    instance: &Instance,
    case: &WitnessCase,
) -> (String, Option<String>, String) {
    let text = case
        .program
        .clone()
        .unwrap_or_else(|| instance.text.clone());
    let mut variables = instance
        .variables
        .iter()
        .cloned()
        .collect::<BTreeMap<_, _>>();
    for hole in &case.holes {
        if let (HoleLocation::ConfigVar { name }, Some(k_text)) = (&hole.location, &hole.k_text) {
            variables.insert(name.clone(), k_text.clone());
        }
    }
    let variables = variables.into_iter().collect::<Vec<_>>();
    let digest_program = Program {
        id: String::new(),
        source: ProgramSource::Text(text.clone()),
        start_sort: instance.written_start_sort.clone(),
        variables: variables.clone(),
    };
    let digest = program_digest(&digest_program, &text).to_string();
    let id = format!("{}-fz-{}", template.id, &digest[..8]);
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
    table.insert("text".into(), Toml::String(text));
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
    (toml, file, id)
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
    let Some((spec, inputs)) = admitted else {
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
    });

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
            config_vars: instance.variables.clone(),
        }),
        holes: template.holes.clone(),
        target: Target {
            kind: TargetKind::Differential(DifferentialTarget::default()),
            run_to_completion: false,
            negated_property: false,
            data_end: true,
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
            attempt["candidate"] = candidate;
            let (fragment, file, id) = fragment(template, &instance, case);
            let premises = premises(manifest, options, &report);
            document["program"] = json!({
                "id": id,
                "fragment": fragment,
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
