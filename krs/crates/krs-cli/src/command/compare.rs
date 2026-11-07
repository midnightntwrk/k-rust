//! `krs compare`: two ends of the definition compared, or an end checked against a case's
//! expectation, printed as `krs run --case` prints an expectation's verdict.
//!
//! Each side is a file: an end document (`halt`, `rule`, `cells`; krs-exec's `ends` module, "End
//! documents"), or a case document, whose case is run as `krs run --case` runs it (its inputs and
//! its `run` table) and whose run's end is the side. A document of named cases names its case as
//! `FILE#NAME`, the case's id in `krs cases`. The keys of the two kinds are disjoint, so a
//! document is read as one kind, and one that holds keys of both is refused.
//!
//! Two sides are compared as two sets of ends ([`Semantics::compare_ends`]): an end document
//! states the one end of what produced it, and a run's end is its case's only end exactly when
//! the run chose nowhere: no state of its path had several successors and it read no value the
//! definition leaves open ([`Semantics::other_ends`]); otherwise the run side's set is
//! incomplete. A verdict rests on a side's completeness only where it says that side has no
//! other end: equal rests on both sides, and an end of one side outside the other rests on the
//! other. So a run side is followed again for its completeness only when the verdict rests on
//! it, and the sides are compared again when it is incomplete; each side at most once.
//!
//! With `--expect CASE`, the case's `expect` table is the expected end, with the cells it is
//! compared on, its views and its observer, and the one side given is checked against it as
//! `krs run --case` checks a run's end ([`Semantics::check_expectation`]): `--compare`, `--view`
//! and `--observer` do not apply, since the expectation states them.
//!
//! The case of a case side is run, never checked: its own `expect` table is not part of the
//! comparison.
//!
//! With `--pairs FILE`, the document FILE lists comparisons, each one `krs compare` question:
//! `LEFT RIGHT` with its own `compare`, `views` and `observer`, or `--expect CASE ACTUAL`. A case
//! side's end and whether it is the case's only end depend on the case and the definition alone,
//! never on the comparison it is used in, so a case that several pairs name is run once for the
//! whole batch and followed again at most once, and each pair's verdict is the one `krs compare`
//! gives for it alone. As in `krs cases`, the definition is loaded once per worker and each
//! observer prepared once and loaded once per worker that uses it.

use std::collections::{BTreeMap, HashMap};
use std::fmt::{self, Write as _};
use std::num::NonZeroUsize;
use std::panic::AssertUnwindSafe;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, OnceLock, PoisonError, mpsc};

use krs_exec::{
    BackendOptions, CaseDocument, CellViews, Compared, Comparison, CompiledStage, Difference,
    EndError, Ends, ExecError, RunOptions, RunReport, Semantics, Side, SourceText, State,
    StopCriterion, json_document, toml_text_document,
};
use krs_ir::measure::{Measurement, Span, Timings};
use krs_ir_levels::DefinitionIr;
use serde_json::{Value as Json, json};

use super::cases::{PrepareObserver, write_stdout};
use super::exec::{
    self, CaseFiles, Checked, Failure, Inputs, ObserverDefinition, SelectedCase, StageReuse,
    WORKER_STACK,
};
use super::{CommandError, CommandOutcome, PreparedDefinition, compared_status, exit_status};
use crate::DiagnosticSources;

/// The schema `krs compare --output json` names.
pub const COMPARE_SCHEMA: &str = "krs-compare/1";

/// How `krs compare` prints its verdict.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum CompareOutput {
    /// The verdict's lines.
    #[default]
    Human,
    /// One [`COMPARE_SCHEMA`] JSON document; with `--pairs`, one per pair and a summary, each
    /// on its own line.
    Json,
}

/// A side's file: an end document or a case document, and the named case it selects.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SideFile {
    /// The document, `.toml` or `.json`.
    pub path: PathBuf,
    /// The case of that name, in a document of named cases.
    pub name: Option<String>,
}

impl SideFile {
    /// The side `spelling` names: `FILE` or `FILE#NAME`, a case's id in `krs cases`, where
    /// `FILE` ends in `.toml` or `.json` (its extension selects how it is read). The name
    /// follows the first `#` that a document's extension precedes, so a name may hold `#`.
    ///
    /// # Errors
    ///
    /// Returns the reason as text: a file of another extension, and a `#` that no name follows.
    pub fn parse(spelling: &str) -> Result<Self, String> {
        let split = spelling
            .match_indices('#')
            .map(|(index, _)| index)
            .find(|index| has_document_extension(&spelling[..*index]));
        let (path, name) = match split {
            Some(index) => (&spelling[..index], Some(&spelling[index + 1..])),
            None => (spelling, None),
        };
        if name == Some("") {
            return Err(format!("`{spelling}`: no case name follows `#`"));
        }
        if !has_document_extension(path) {
            return Err(format!(
                "the document `{path}` is not a `.toml` or `.json` file, which its extension says"
            ));
        }
        Ok(Self {
            path: PathBuf::from(path),
            name: name.map(str::to_owned),
        })
    }
}

impl fmt::Display for SideFile {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.name {
            Some(name) => write!(formatter, "{}#{name}", self.path.display()),
            None => write!(formatter, "{}", self.path.display()),
        }
    }
}

fn has_document_extension(path: &str) -> bool {
    Path::new(path)
        .extension()
        .and_then(|extension| extension.to_str())
        .is_some_and(|extension| matches!(extension, "toml" | "json"))
}

/// What `krs compare` compares.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CompareSides {
    /// `LEFT RIGHT`: two sets of ends.
    Ends {
        /// The left side.
        left: SideFile,
        /// The right side.
        right: SideFile,
    },
    /// `--expect CASE ACTUAL`: an end against the expectation of a case.
    Expectation {
        /// The case whose `expect` table is the expected end.
        case: SideFile,
        /// The side checked against it.
        actual: SideFile,
    },
    /// `--pairs FILE`: the comparisons the document `file` lists, each of these two kinds.
    Pairs {
        /// The pairs document, `.toml` or `.json`.
        file: PathBuf,
        /// `--jobs`: the worker threads, each with the definition loaded once; the available
        /// parallelism by default.
        jobs: Option<NonZeroUsize>,
    },
}

/// `krs compare` inputs.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompareRequest {
    /// The sides.
    pub sides: CompareSides,
    /// `--compare`: the compared cells by declared path; `None` compares every leaf cell that is
    /// not unobservable.
    pub compare: Option<Vec<String>>,
    /// `--view CELL=FUNCTION`: the view of each viewed cell, by declared path.
    pub views: BTreeMap<String, String>,
    /// `--observer PACKAGE:DEFINITION`: the definition the views are resolved and evaluated in;
    /// `None` for the compared definition.
    pub observer: Option<String>,
    /// `--output`.
    pub output: CompareOutput,
    /// `--smt-resource-limit`, `--smt-clock-ms` and `--smt-retries`.
    pub solver: BackendOptions,
    /// `--view-budget`: the polls each evaluation of a view may take.
    pub view_budget: u64,
}

/// A side's document, read before the definition is loaded.
pub(super) enum SideDocument {
    /// An end document, decoded once the definition is loaded; `base` is its directory, which
    /// its file paths are relative to.
    End {
        file: SideFile,
        document: Json,
        base: PathBuf,
    },
    /// A case, run once the definition is loaded.
    Case(SelectedCase),
}

/// The two sides' documents: `LEFT` and `RIGHT`, or `CASE` and `ACTUAL`.
pub(super) struct ReadSides {
    first: SideDocument,
    second: SideDocument,
}

/// The keys of an end document.
const END_KEYS: [&str; 3] = ["halt", "rule", "cells"];

/// The keys of a case document: one case's, and a document of named cases'.
const CASE_KEYS: [&str; 4] = ["inputs", "run", "expect", "case"];

/// Read the sides' documents of `request`, before the definition is loaded.
///
/// # Errors
///
/// Fails for a document that cannot be read, holds keys of both kinds, or is no case document,
/// a `#NAME` its document does not select, and, with `--expect`, an end document or a case
/// that states no expectation.
pub(super) fn read(request: &CompareRequest) -> Result<ReadSides, Failure> {
    let (first, second) = match &request.sides {
        CompareSides::Ends { left, right } => (left, right),
        CompareSides::Expectation { case, actual } => (case, actual),
        CompareSides::Pairs { .. } => unreachable!("a batch reads each of its pairs' sides"),
    };
    let first = read_side(first)?;
    if let CompareSides::Expectation { case, .. } = &request.sides {
        match &first {
            SideDocument::End { .. } => {
                return Err(Failure::Usage(format!(
                    "--expect `{case}` names an end document; --expect names a case document whose `expect` table states the expected end"
                )));
            }
            SideDocument::Case(selected) if selected.case.expect.is_none() => {
                return Err(Failure::Usage(format!(
                    "--expect `{case}`: the case states no expectation (`expect`)"
                )));
            }
            SideDocument::Case(_) => {}
        }
    }
    let second = read_side(second)?;
    Ok(ReadSides { first, second })
}

/// The observer the views are evaluated in, where it is not the compared definition: the one
/// `--observer` names, or with `--expect` the one the expectation names beside a view.
pub(super) fn observer_name<'a>(
    request: &'a CompareRequest,
    read: &'a ReadSides,
) -> Option<&'a str> {
    match (&request.sides, &read.first) {
        (CompareSides::Expectation { .. }, SideDocument::Case(case)) => {
            exec::named_observer(&case.case)
        }
        _ => request.observer.as_deref(),
    }
}

/// A refusal of the side `file`'s document.
fn refuse(file: &SideFile, message: &str) -> Failure {
    Failure::Exec(ExecError::Case(format!("`{file}`: {message}")))
}

/// The document `file` names, read as an end document or a case document by its keys.
fn read_side(file: &SideFile) -> Result<SideDocument, Failure> {
    let path = &file.path;
    let text = std::fs::read_to_string(path)
        .map_err(|error| Failure::Read(format!("could not read `{}`: {error}", path.display())))?;
    let base = path.parent().map_or_else(PathBuf::new, Path::to_path_buf);
    let json = path
        .extension()
        .is_some_and(|extension| extension == "json");
    let document = if json {
        json_document(&text)
    } else {
        toml_text_document(&text)
    }
    .map_err(|error| refuse(file, &error.to_string()))?;
    let end_key = |key: &String| END_KEYS.contains(&key.as_str());
    if let Json::Object(table) = &document
        && table.keys().any(end_key)
    {
        if let Some(key) = table.keys().find(|key| CASE_KEYS.contains(&key.as_str())) {
            return Err(refuse(
                file,
                &format!(
                    "`{key}`: a document is an end document (`halt`, `rule`, `cells`) or a case document (`inputs`, `run`, `expect`, or `case` for named cases), not both"
                ),
            ));
        }
        if let Some(name) = &file.name {
            return Err(Failure::Usage(format!(
                "`{file}`: `{}` is an end document, which states one end and no named case; name it without `#{name}`",
                path.display()
            )));
        }
        return Ok(SideDocument::End {
            file: file.clone(),
            document,
            base,
        });
    }
    // The document's own file, named as `files` names every file it reads, so that a file it
    // includes that includes it back is a cycle.
    let top = path
        .canonicalize()
        .ok()
        .and_then(|resolved| resolved.to_str().map(str::to_owned));
    let mut files = CaseFiles { base: base.clone() };
    let document = CaseDocument::from_document(document, top.as_deref(), &mut files)
        .map_err(|error| refuse(file, &error.to_string()))?;
    let case = match (document, file.name.as_deref()) {
        (CaseDocument::One(case), None) => case,
        (CaseDocument::One(_), Some(name)) => {
            return Err(Failure::Usage(format!(
                "`{file}`: the case document `{}` holds one case, which has no name; name it without `#{name}`",
                path.display()
            )));
        }
        (document @ CaseDocument::Named(_), None) => {
            return Err(Failure::Usage(format!(
                "the case document `{}` holds named cases; name one as `{}#NAME`: {}",
                path.display(),
                path.display(),
                exec::listed_names(document.names())
            )));
        }
        (document @ CaseDocument::Named(_), Some(name)) => {
            let Some(case) = document.named(name).cloned() else {
                return Err(Failure::Usage(format!(
                    "`{file}`: the case document `{}` holds no case of that name; its cases are {}",
                    path.display(),
                    exec::listed_names(document.names())
                )));
            };
            case
        }
    };
    Ok(SideDocument::Case(SelectedCase {
        case,
        path: path.clone(),
        base,
    }))
}

/// Compare the sides of `request` on the prepared definition, its stage restored or compiled
/// once, the views evaluated in `observer` when it is given.
#[expect(
    clippy::too_many_arguments,
    reason = "The comparison takes exec_command's prepared definition, request and observers' inputs."
)]
pub(super) fn execute(
    prepared: &PreparedDefinition,
    request: &CompareRequest,
    sources: &DiagnosticSources,
    reuse: StageReuse<'_>,
    read: ReadSides,
    observer: Option<ObserverDefinition>,
    conditions: NamedConditions<ObserverDefinition>,
    measurement: &mut Measurement,
) -> Result<CommandOutcome, CommandError> {
    let sources = sources.clone();
    let conditions_named = conditions;
    let timings = &mut measurement.timings;
    let definition = prepared.lowered.definition();
    let mut reused = false;
    let reused_flag = &mut reused;
    let result = std::thread::scope(|scope| {
        std::thread::Builder::new()
            .name("krs-compare".into())
            .stack_size(WORKER_STACK)
            .spawn_scoped(scope, move || {
                let provider: SourceText = Box::new(move |file| sources.source_text(file));
                let (stage, restored) =
                    exec::compiled_stage(definition, reuse, timings).map_err(Failure::Exec)?;
                *reused_flag = restored;
                // The compared definition's stage, kept for a case side's stop condition.
                let own = stage.clone();
                let mut semantics = Semantics::from_stage_with_solver(
                    definition,
                    stage,
                    Some(provider),
                    request.solver,
                    timings,
                )
                .map_err(Failure::Exec)?;
                let mut conditions = Conditions::new(
                    request.view_budget,
                    definition,
                    &own,
                    request.solver,
                    reuse.restore,
                );
                for (name, observer) in conditions_named {
                    conditions.name(
                        name,
                        observer.map(|observer| {
                            observer.map(|observer| ConditionObserver::Prepared(Box::new(observer)))
                        }),
                    );
                }
                let mut observer = observer
                    .map(|observer| {
                        exec::load_observer(&observer, reuse.restore, request.solver, timings)
                    })
                    .transpose()
                    .map_err(Failure::Exec)?;
                let runs = CaseRuns::default();
                let verdict = compare(
                    &mut semantics,
                    observer.as_mut(),
                    &mut conditions,
                    request,
                    read,
                    &runs,
                    timings,
                )?;
                let stdout = match request.output {
                    CompareOutput::Human => {
                        let mut text = String::new();
                        verdict.write(&mut text, "krs compare");
                        text
                    }
                    CompareOutput::Json => format!("{}\n", verdict.document()),
                };
                let stderr = runs.passed_notes("krs compare");
                Ok(exec::outcome(stdout, stderr, verdict.exit_code()))
            })
            .map_err(|error| {
                CommandError::InvalidRequest(format!("could not start the compare worker: {error}"))
            })?
            .join()
            .map_err(|_| CommandError::InvalidRequest("the compare worker panicked".into()))
    })?;
    measurement.counters.set("stage.reused", u64::from(reused));
    result.map_err(|failure: Failure| failure.into_command_error(prepared))
}

/// The verdict of two sets of ends, with the views it applied.
struct EndsVerdict {
    verdict: Compared,
    views: BTreeMap<String, String>,
    observer: Option<String>,
}

impl EndsVerdict {
    /// The exit status the verdict gives ([`exit_status`]): equal, differs (a finding), or
    /// inconclusive (no answer).
    const fn exit_code(&self) -> i32 {
        compared_status(&self.verdict)
    }

    const fn word(&self) -> &'static str {
        match self.verdict {
            Compared::Equal => "equal",
            Compared::Differs(_) => "differs",
            Compared::Inconclusive(_) => "inconclusive",
        }
    }

    fn document(&self) -> Json {
        let mut document = json!({"schema": COMPARE_SCHEMA, "verdict": self.word()});
        match &self.verdict {
            Compared::Equal => {}
            Compared::Differs(difference) => document["difference"] = json!(difference),
            Compared::Inconclusive(reason) => document["reason"] = json!(reason),
        }
        if !self.views.is_empty() {
            document["views"] = json!(self.views);
            if let Some(observer) = &self.observer {
                document["observer"] = json!(observer);
            }
        }
        document
    }

    /// The verdict's lines, headed by `label`.
    fn write(&self, output: &mut String, label: &str) {
        match &self.verdict {
            Compared::Equal => {
                let _ = writeln!(output, "{label}: equal");
            }
            Compared::Inconclusive(reason) => {
                let _ = writeln!(output, "{label}: inconclusive: {reason}");
            }
            Compared::Differs(difference) => {
                exec::write_difference(output, &format!("{label}: differs"), difference);
                write_pair_note(output, difference);
            }
        }
        let observer = self.observer.as_deref().filter(|_| !self.views.is_empty());
        exec::write_views(output, &self.views, observer);
    }
}

/// One comparison's verdict: two sets of ends compared, or a side checked against a case's
/// expectation.
enum Verdict {
    Ends(EndsVerdict),
    Expectation(Checked),
}

impl Verdict {
    /// The exit status the verdict gives ([`exit_status`]).
    const fn exit_code(&self) -> i32 {
        match self {
            Self::Ends(verdict) => verdict.exit_code(),
            Self::Expectation(checked) => checked.exit_code(),
        }
    }

    /// The [`COMPARE_SCHEMA`] document.
    fn document(&self) -> Json {
        match self {
            Self::Ends(verdict) => verdict.document(),
            Self::Expectation(checked) => {
                let mut document = json!({"schema": COMPARE_SCHEMA});
                if let (Json::Object(target), Json::Object(members)) =
                    (&mut document, checked.document())
                {
                    target.extend(members);
                }
                document
            }
        }
    }

    /// The verdict's lines, headed by `label`.
    fn write(&self, output: &mut String, label: &str) {
        match self {
            Self::Ends(verdict) => verdict.write(output, label),
            Self::Expectation(checked) => checked.write(output, label),
        }
    }
}

/// Where a side has several ends, which end of each the difference shows: one the other side
/// does not have, and the nearest end of the other side.
fn write_pair_note(output: &mut String, difference: &Difference) {
    let (outside, other) = if difference.outside == difference.left.name {
        (&difference.left, &difference.right)
    } else {
        (&difference.right, &difference.left)
    };
    if outside.ends <= 1 && other.ends <= 1 {
        return;
    }
    let of = |ends: usize| {
        if ends > 1 {
            format!(", one of {ends}")
        } else {
            String::new()
        }
    };
    let _ = writeln!(
        output,
        "  (the {} end shown{} is not an end of the {} side; the {} end shown is the nearest{})",
        outside.name,
        of(outside.ends),
        other.name,
        other.name,
        if other.ends > 1 {
            format!(" of {}", other.ends)
        } else {
            String::new()
        }
    );
}

/// A failure recorded for every comparison that uses what failed, beyond the first, which gets
/// the failure itself.
#[derive(Clone)]
enum Recorded {
    /// A run that reached several states under conditions it cannot decide.
    Undecided(String),
    /// Any other failure, as its reason.
    Refused(String),
}

impl Recorded {
    fn of(failure: &Failure) -> Self {
        match failure {
            Failure::Exec(ExecError::Undecided(message)) => Self::Undecided(message.clone()),
            failure => Self::Refused(failure.reason()),
        }
    }

    fn failure(self) -> Failure {
        match self {
            Self::Undecided(message) => Failure::Exec(ExecError::Undecided(message)),
            Self::Refused(reason) => Failure::Read(reason),
        }
    }
}

/// The value `slot` holds, computed by `compute` when it holds none; a failure of `compute` is
/// returned to its caller as it is and recorded for every later one.
fn once<T>(
    slot: &OnceLock<Result<T, Recorded>>,
    compute: impl FnOnce() -> Result<T, Failure>,
) -> Result<&T, Failure> {
    let mut original = None;
    let stored = slot.get_or_init(|| {
        compute().map_err(|failure| {
            let recorded = Recorded::of(&failure);
            original = Some(failure);
            recorded
        })
    });
    match original {
        Some(failure) => Err(failure),
        None => stored
            .as_ref()
            .map_err(|recorded| recorded.clone().failure()),
    }
}

/// The run of each case a comparison's sides name, by its document and name: a case's end, and
/// whether it is the case's only end, are facts of the case and the definition, which no
/// comparison changes, so a batch runs each case once whichever pairs and workers use it.
#[derive(Default)]
struct CaseRuns {
    #[expect(
        clippy::type_complexity,
        reason = "A slot per case, each computed once by whichever worker needs it first."
    )]
    slots: Mutex<HashMap<(PathBuf, Option<String>), Arc<OnceLock<Result<Arc<CaseRun>, Recorded>>>>>,
}

impl CaseRuns {
    /// The notes of the runs taken that went on past a stop rule ([`CaseRun::passed`]), each
    /// headed by `label`.
    fn passed_notes(&self, label: &str) -> String {
        let slots = self.slots.lock().unwrap_or_else(PoisonError::into_inner);
        let mut notes = slots
            .values()
            .filter_map(|slot| match slot.get() {
                Some(Ok(run)) => run.passed.clone(),
                _ => None,
            })
            .collect::<Vec<_>>();
        notes.sort();
        notes.into_iter().fold(String::new(), |mut text, note| {
            let _ = std::fmt::Write::write_fmt(&mut text, format_args!("{label}: {note}\n"));
            text
        })
    }

    /// The run of `case`, run on `semantics` the first time a side names it.
    fn get(
        &self,
        semantics: &mut Semantics,
        conditions: &mut Conditions<'_>,
        case: &SelectedCase,
        timings: &mut Timings,
    ) -> Result<Arc<CaseRun>, Failure> {
        let document = case
            .path
            .canonicalize()
            .unwrap_or_else(|_| case.path.clone());
        let slot = Arc::clone(
            self.slots
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .entry((document, case.case.name.clone()))
                .or_default(),
        );
        once(&slot, || {
            timings.span("compare.run", |_| {
                CaseRun::run(semantics, conditions, case).map(Arc::new)
            })
        })
        .map(Arc::clone)
    }
}

/// The observers the stop conditions of a comparison's case sides name, each prepared before any
/// run asks: by name, `None` for one that names the compared definition itself, or why it could
/// not be prepared.
pub(super) type NamedConditions<O> = Vec<(String, Result<Option<O>, String>)>;

/// The observers the stop conditions of `read`'s case sides name, each once, in the order of
/// the sides: each is prepared before the sides are run, as a views' observer is, so that the
/// dependency facets it composes are known before the comparison.
pub(super) fn condition_observers(read: &ReadSides) -> Vec<String> {
    let mut names = Vec::new();
    for side in [&read.first, &read.second] {
        let SideDocument::Case(case) = side else {
            continue;
        };
        // A case whose stops cannot be read is refused when it is run.
        let Ok(stop) = case.stop(&StopCriterion::None, None) else {
            continue;
        };
        if let Some(name) = stop.when().and_then(|when| when.observer.clone())
            && !names.contains(&name)
        {
            names.push(name);
        }
    }
    names
}

/// An observer a case side's stop condition names, prepared: its Definition IR, compiled when a
/// run first asks (a single comparison), or compiled already (a batch, which compiles each
/// observer once).
enum ConditionObserver {
    Prepared(Box<ObserverDefinition>),
    Compiled(Arc<Observer>),
}

/// The definitions the stop conditions of case sides' runs are evaluated in, each loaded the
/// first time a run asks one: another semantics of the compared definition, or an observer it
/// names, prepared beforehand ([`Self::name`]). They are loaded apart from the views' observer,
/// which a comparison reads at the same time.
pub(super) struct Conditions<'a> {
    /// The polls each evaluation of a condition may spend (`--view-budget`), as `krs run --case`
    /// spends them.
    budget: u64,
    definition: &'a DefinitionIr,
    /// The compared definition's stage, for its own conditions.
    stage: &'a CompiledStage,
    solver: BackendOptions,
    restore: bool,
    /// The observers conditions name, prepared, by name ([`NamedConditions`]).
    named: HashMap<String, Result<Option<ConditionObserver>, String>>,
    /// By observer name, `None` for the compared definition's own.
    loaded: Vec<(Option<String>, Result<Semantics, String>)>,
}

impl<'a> Conditions<'a> {
    fn new(
        budget: u64,
        definition: &'a DefinitionIr,
        stage: &'a CompiledStage,
        solver: BackendOptions,
        restore: bool,
    ) -> Self {
        Self {
            budget,
            definition,
            stage,
            solver,
            restore,
            named: HashMap::new(),
            loaded: Vec::new(),
        }
    }

    /// Record the observer `name`, prepared, unless it is recorded already.
    fn name(&mut self, name: String, observer: Result<Option<ConditionObserver>, String>) {
        self.named.entry(name).or_insert(observer);
    }

    /// The definition the condition of `criterion` is evaluated in; `None` without one.
    fn of(&mut self, criterion: &StopCriterion) -> Result<Option<&mut Semantics>, Failure> {
        let Some(when) = criterion.when() else {
            return Ok(None);
        };
        let key = when.observer.clone();
        let position = if let Some(position) =
            self.loaded.iter().position(|(loaded, _)| *loaded == key)
        {
            position
        } else {
            let timings = &mut Timings::disabled();
            let own = |timings: &mut Timings| {
                exec::load_condition(self.definition, self.stage, None, self.solver, timings)
                    .map_err(|error| error.to_string())
            };
            let loaded = match &key {
                None => own(timings),
                Some(name) => match self.named.get(name) {
                    None => Err(format!("the observer `{name}` was not prepared")),
                    Some(Err(reason)) => Err(reason.clone()),
                    Some(Ok(None)) => own(timings),
                    Some(Ok(Some(ConditionObserver::Prepared(observer)))) => {
                        exec::load_observer(observer, self.restore, self.solver, timings)
                            .map_err(|error| error.to_string())
                    }
                    Some(Ok(Some(ConditionObserver::Compiled(observer)))) => exec::load_condition(
                        self.definition,
                        self.stage,
                        Some((&observer.definition, &observer.stage)),
                        self.solver,
                        timings,
                    )
                    .map_err(|error| error.to_string()),
                },
            }
            .map_err(|error| format!("krs cannot load the stop condition's definition: {error}"));
            self.loaded.push((key, loaded));
            self.loaded.len() - 1
        };
        self.loaded[position]
            .1
            .as_mut()
            .map(Some)
            .map_err(|reason| Failure::Exec(ExecError::StopWhen(reason.clone())))
    }
}

/// A case's run: its ends, the run they are of, and once the run is followed again, whether
/// its end is the case's only one.
struct CaseRun {
    ends: Ends,
    /// The note of the stop rules the run went on past ([`krs_exec::RunReport::passed_stops`]),
    /// naming the case; `None` when it passed none.
    passed: Option<String>,
    /// The run, when it has an end whose completeness following it again could change.
    run: Option<RunOf>,
    /// Once followed again: the ends with why they are incomplete, or `None` when they are
    /// complete.
    followed: OnceLock<Result<Option<Ends>, Recorded>>,
}

/// A case's run: the state it ran from, its options and its report.
struct RunOf {
    state: State,
    options: RunOptions,
    report: RunReport,
}

impl CaseRun {
    /// The end of `case`'s run, as `krs run --case` runs it: its inputs bound, its `run` table's
    /// depth and stops.
    fn run(
        semantics: &mut Semantics,
        conditions: &mut Conditions<'_>,
        case: &SelectedCase,
    ) -> Result<Self, Failure> {
        let stop = case.stop(&StopCriterion::None, None)?;
        let depth = case.depth(None)?;
        let state = exec::configure(semantics, Inputs::of_case(case), false)?;
        let options = RunOptions {
            depth,
            stop,
            condition_budget: Some(conditions.budget),
            ..RunOptions::default()
        };
        let condition = conditions.of(&options.stop)?;
        let report = match semantics.run_observed(&state, options.clone(), condition) {
            Ok(report) => report,
            // A run that cannot decide which of several states it reaches has no one end.
            Err(error @ ExecError::Undecided { .. }) => {
                return Ok(Self {
                    ends: Ends::none(format!("the run has no one end: {error}")),
                    passed: None,
                    run: None,
                    followed: OnceLock::new(),
                });
            }
            Err(error) => return Err(error.into()),
        };
        let ends = semantics
            .end_of(&report)
            .map_err(|error| exec::end_failure(&error))?;
        let passed = exec::passed_list(semantics, &report).map(|passed| {
            format!(
                "the run of the case `{}` went on past {passed}, at a step its state had another \
                 successor beside, so no arrival",
                case.id()
            )
        });
        // A run with no end has nothing a completeness could change.
        let run = (!ends.ends.is_empty()).then_some(RunOf {
            state,
            options,
            report,
        });
        Ok(Self {
            ends,
            passed,
            run,
            followed: OnceLock::new(),
        })
    }

    /// Follow the run again, once, for whether its end is its case's only one: the ends with
    /// why they are incomplete when it is not.
    fn follow(
        &self,
        semantics: &mut Semantics,
        conditions: &mut Conditions<'_>,
    ) -> Result<Option<&Ends>, Failure> {
        let Some(run) = &self.run else {
            return Ok(None);
        };
        let followed = once(&self.followed, || {
            let condition = conditions.of(&run.options.stop)?;
            Ok(semantics
                .other_ends_observed(&run.state, &run.options, &run.report, condition)?
                .map(|reason| Ends {
                    incomplete: Some(reason),
                    ..self.ends.clone()
                }))
        })?;
        Ok(followed.as_ref())
    }
}

/// A side's ends: an end document's one end, or a case's run, until its completeness is known.
struct Produced {
    name: &'static str,
    source: Source,
}

enum Source {
    End(Ends),
    /// A case's run, and whether this comparison followed it again ([`Produced::settle`]).
    Run {
        run: Arc<CaseRun>,
        followed: bool,
    },
}

impl Produced {
    fn ends(&self) -> &Ends {
        match &self.source {
            Source::End(ends) => ends,
            Source::Run { run, followed } => (*followed)
                .then(|| run.followed.get())
                .flatten()
                .and_then(|followed| followed.as_ref().ok().and_then(Option::as_ref))
                .unwrap_or(&run.ends),
        }
    }

    fn side(&self) -> Side<'_> {
        Side {
            name: self.name,
            ends: self.ends(),
        }
    }

    /// The end `document` of the side `file` states, refused unless it states every cell
    /// `comparison` compares.
    fn end(
        semantics: &Semantics,
        name: &'static str,
        (file, document, base): (&SideFile, &Json, PathBuf),
        comparison: &Comparison,
    ) -> Result<Self, Failure> {
        let mut files = CaseFiles { base };
        let end = semantics
            .read_end_in(document, None, &mut files)
            .map_err(|error| refuse(file, &error.to_string()))?;
        semantics
            .check_stated(comparison, &end, name)
            .map_err(|error| refuse(file, &error.to_string()))?;
        Ok(Self {
            name,
            source: Source::End(Ends::one(end)),
        })
    }

    /// The end of `case`'s run, run once for every comparison of `runs`.
    fn run(
        runs: &CaseRuns,
        semantics: &mut Semantics,
        conditions: &mut Conditions<'_>,
        name: &'static str,
        case: &SelectedCase,
        timings: &mut Timings,
    ) -> Result<Self, Failure> {
        // A stop condition refused on this side's run names the side and its case, which the
        // run's own refusal cannot.
        let run =
            runs.get(semantics, conditions, case, timings)
                .map_err(|failure| match failure {
                    Failure::Exec(
                        error @ (ExecError::StopWhen(_) | ExecError::StopCondition { .. }),
                    ) => Failure::Exec(ExecError::StopWhen(format!(
                        "the {name} side, the case `{}`: {error}",
                        case.id()
                    ))),
                    other => other,
                })?;
        Ok(Self {
            name,
            source: Source::Run {
                run,
                followed: false,
            },
        })
    }

    /// Follow the side's run again for whether its end is its case's only one; true when it is
    /// not, which makes the side's set incomplete. Each comparison follows a run at most once,
    /// and a batch follows each case's run at most once.
    fn settle(
        &mut self,
        semantics: &mut Semantics,
        conditions: &mut Conditions<'_>,
    ) -> Result<bool, Failure> {
        let Source::Run { run, followed } = &mut self.source else {
            return Ok(false);
        };
        if *followed {
            return Ok(false);
        }
        *followed = true;
        Ok(run.follow(semantics, conditions)?.is_some())
    }
}

/// Compare the sides `read` of `request`, the views evaluated in `observer` (the compared
/// definition when `None`), each case side's run taken from `runs`.
fn compare(
    semantics: &mut Semantics,
    observer: Option<&mut Semantics>,
    conditions: &mut Conditions<'_>,
    request: &CompareRequest,
    read: ReadSides,
    runs: &CaseRuns,
    timings: &mut Timings,
) -> Result<Verdict, Failure> {
    match &request.sides {
        CompareSides::Ends { .. } => compare_ends(
            semantics, observer, conditions, request, read, runs, timings,
        )
        .map(Verdict::Ends),
        CompareSides::Expectation { .. } => check_expectation(
            semantics, observer, conditions, request, read, runs, timings,
        )
        .map(Verdict::Expectation),
        CompareSides::Pairs { .. } => unreachable!("a batch compares each of its pairs"),
    }
}

/// A refusal of the comparison itself: its compared cells or its views.
fn refuse_comparison(error: &EndError) -> Failure {
    Failure::Exec(ExecError::Case(format!("the comparison: {error}")))
}

/// Compare two sets of ends: every end document read and checked first, so that a partial one
/// is refused before a case is run; then each case side run; then the views evaluated; then the
/// sets compared, a run side followed again where the verdict rests on its completeness.
fn compare_ends(
    semantics: &mut Semantics,
    observer: Option<&mut Semantics>,
    conditions: &mut Conditions<'_>,
    request: &CompareRequest,
    read: ReadSides,
    runs: &CaseRuns,
    timings: &mut Timings,
) -> Result<EndsVerdict, Failure> {
    let mut comparison = Comparison {
        compare: request.compare.clone(),
        views: CellViews::default(),
    };
    if !request.views.is_empty() {
        let resolver = observer.as_deref().unwrap_or(&*semantics);
        comparison.views = semantics
            .cell_views(resolver, &request.views)
            .map_err(|error| refuse_comparison(&error))?;
    }
    semantics
        .check_comparison(&comparison)
        .map_err(|error| refuse_comparison(&error))?;
    let verdict = |verdict| EndsVerdict {
        verdict,
        views: request.views.clone(),
        observer: request.observer.clone(),
    };
    let ReadSides { first, second } = read;
    let read_end = |name, document: &SideDocument| match document {
        SideDocument::End {
            file,
            document,
            base,
        } => Produced::end(semantics, name, (file, document, base.clone()), &comparison).map(Some),
        SideDocument::Case(_) => Ok(None),
    };
    let left = read_end("left", &first)?;
    let right = read_end("right", &second)?;
    let mut produce = |name, end: Option<Produced>, document: &SideDocument| match (end, document) {
        (Some(end), _) => Ok(end),
        (None, SideDocument::Case(case)) => {
            Produced::run(runs, semantics, conditions, name, case, timings)
        }
        (None, SideDocument::End { .. }) => unreachable!("an end document is read before"),
    };
    let mut left = produce("left", left, &first)?;
    let mut right = produce("right", right, &second)?;
    if !comparison.views.is_empty() {
        let (observer, subject) = match observer {
            Some(observer) => (observer, Some(&*semantics)),
            None => (&mut *semantics, None),
        };
        match comparison.views.evaluate_within(
            observer,
            subject,
            &[left.side(), right.side()],
            Some(request.view_budget),
        ) {
            Ok(()) => {}
            Err(error @ EndError::ViewStopped { .. }) => {
                return Ok(verdict(Compared::Inconclusive(error.to_string())));
            }
            Err(error) => return Err(refuse_comparison(&error)),
        }
    }
    loop {
        let compared = semantics
            .compare_ends(&comparison, left.side(), right.side())
            .map_err(|error| refuse_comparison(&error))?;
        // The sides whose completeness the verdict rests on.
        let (on_left, on_right) = match &compared {
            Compared::Equal => (true, true),
            Compared::Differs(difference) if difference.outside == right.name => (true, false),
            Compared::Differs(_) => (false, true),
            Compared::Inconclusive(_) => (false, false),
        };
        let mut changed = false;
        if on_left {
            changed |= left.settle(semantics, conditions)?;
        }
        if on_right {
            changed |= right.settle(semantics, conditions)?;
        }
        if !changed {
            return Ok(verdict(compared));
        }
    }
}

/// Check the actual side against the expectation of the case `--expect` names, as
/// `krs run --case` checks a run's end: an end document read and checked against the cells the
/// expectation compares, or a case side run; met only where the actual side has no other end.
fn check_expectation(
    semantics: &mut Semantics,
    mut observer: Option<&mut Semantics>,
    conditions: &mut Conditions<'_>,
    request: &CompareRequest,
    read: ReadSides,
    runs: &CaseRuns,
    timings: &mut Timings,
) -> Result<Checked, Failure> {
    let ReadSides { first, second } = read;
    let SideDocument::Case(case) = first else {
        unreachable!("`read` refuses an end document named by --expect")
    };
    let Some(mut expectation) = SelectedCase::expectation_of(Some(&case), semantics)? else {
        unreachable!("`read` refuses a case that states no expectation")
    };
    exec::resolve_views(semantics, observer.as_deref(), &case, &mut expectation)?;
    let mut actual = match &second {
        SideDocument::End {
            file,
            document,
            base,
        } => Produced::end(
            semantics,
            "actual",
            (file, document, base.clone()),
            &expectation.comparison,
        )?,
        SideDocument::Case(actual) => {
            Produced::run(runs, semantics, conditions, "actual", actual, timings)?
        }
    };
    let budget = request.view_budget;
    let checked = exec::check(
        semantics,
        observer.as_deref_mut(),
        &case,
        &mut expectation,
        actual.ends(),
        budget,
    )?;
    // One end that differs is unmet; one that agrees meets the expectation only where it is the
    // actual side's only end.
    if matches!(checked.verdict, Compared::Equal) && actual.settle(semantics, conditions)? {
        return exec::check(
            semantics,
            observer,
            &case,
            &mut expectation,
            actual.ends(),
            budget,
        );
    }
    Ok(checked)
}

/// The keys a pair holds: `LEFT RIGHT` with its comparison's options, or `--expect CASE ACTUAL`.
const PAIR_KEYS: [&str; 7] = [
    "left", "right", "compare", "views", "observer", "expect", "actual",
];

/// One pair of a pairs document: its record's `pair` member, the label its human lines carry,
/// and its comparison, or why it is none.
struct Pair {
    member: Json,
    label: String,
    request: Result<CompareRequest, String>,
}

/// The pairs the document `file` lists under `pair`, as a case document of named cases lists
/// its cases under `case`: a TOML array of tables or a JSON array of objects, read by the file's
/// extension. A pair's side paths are relative to the document's directory, as every path a
/// document names is.
///
/// # Errors
///
/// Fails for a document that cannot be read, holds another key than `pair`, or lists no pair; a
/// pair that is no comparison is refused in its own record ([`Pair::request`]).
fn read_pairs(file: &Path, template: &CompareRequest) -> Result<Vec<Pair>, Failure> {
    let shown = file.display();
    let text = std::fs::read_to_string(file)
        .map_err(|error| Failure::Read(format!("could not read `{shown}`: {error}")))?;
    let json = file
        .extension()
        .is_some_and(|extension| extension == "json");
    let document = if json {
        json_document(&text)
    } else {
        toml_text_document(&text)
    }
    .map_err(|error| Failure::Usage(format!("the pairs document `{shown}`: {error}")))?;
    let Json::Object(mut table) = document else {
        return Err(Failure::Usage(format!(
            "the pairs document `{shown}` is no table of `pair`"
        )));
    };
    if let Some(key) = table.keys().find(|key| *key != "pair") {
        return Err(Failure::Usage(format!(
            "the pairs document `{shown}` holds `{key}`; it lists its pairs under `pair` and holds nothing else"
        )));
    }
    let records = match table.remove("pair") {
        Some(Json::Array(records)) if !records.is_empty() => records,
        Some(Json::Array(_)) | None => {
            return Err(Failure::Usage(format!(
                "the pairs document `{shown}` lists no pair under `pair`"
            )));
        }
        Some(_) => {
            return Err(Failure::Usage(format!(
                "the pairs document `{shown}`: `pair` is an array of pairs"
            )));
        }
    };
    let base = file.parent().map_or_else(PathBuf::new, Path::to_path_buf);
    Ok(records
        .iter()
        .enumerate()
        .map(|(index, record)| Pair::read(index + 1, record, &base, template))
        .collect())
}

impl Pair {
    /// The pair `record`, the `number`th of its document (counting from 1), its side paths
    /// relative to `base`, with the output, solver and view budget of `template`.
    fn read(number: usize, record: &Json, base: &Path, template: &CompareRequest) -> Self {
        let mut member = json!({"number": number});
        let spelled = |key: &str| record.get(key).and_then(Json::as_str);
        for key in ["left", "right", "expect", "actual"] {
            if let Some(side) = spelled(key) {
                member[key] = json!(side);
            }
        }
        let label = match (
            spelled("left"),
            spelled("right"),
            spelled("expect"),
            spelled("actual"),
        ) {
            (Some(left), Some(right), _, _) => {
                format!(
                    "pair {number} ({left}, {right}{})",
                    pair_question_flags(record)
                )
            }
            (_, _, Some(case), Some(actual)) => {
                format!("pair {number} (--expect {case}, {actual})")
            }
            _ => format!("pair {number}"),
        };
        Self {
            member,
            label,
            request: Self::request(record, base, template),
        }
    }

    /// The comparison `record` states, as `krs compare` reads the same question from its
    /// arguments.
    fn request(
        record: &Json,
        base: &Path,
        template: &CompareRequest,
    ) -> Result<CompareRequest, String> {
        let Json::Object(table) = record else {
            return Err(
                "a pair is a table of `left` and `right`, or of `expect` and `actual`".to_owned(),
            );
        };
        if let Some(key) = table.keys().find(|key| !PAIR_KEYS.contains(&key.as_str())) {
            return Err(format!(
                "`{key}`: a pair holds `left`, `right`, `compare`, `views` and `observer`, or `expect` and `actual`"
            ));
        }
        let side = |key: &str| match table.get(key) {
            None => Ok(None),
            Some(Json::String(spelling)) => {
                let mut side =
                    SideFile::parse(spelling).map_err(|error| format!("`{key}`: {error}"))?;
                side.path = base.join(&side.path);
                Ok(Some(side))
            }
            Some(_) => Err(format!(
                "`{key}` is a side, a string naming a document as `FILE` or `FILE#NAME`"
            )),
        };
        let sides = match (
            side("left")?,
            side("right")?,
            side("expect")?,
            side("actual")?,
        ) {
            (Some(left), Some(right), None, None) => CompareSides::Ends { left, right },
            (None, None, Some(case), Some(actual)) => {
                if let Some(key) = ["compare", "views", "observer"]
                    .into_iter()
                    .find(|key| table.contains_key(*key))
                {
                    return Err(format!(
                        "`{key}` does not apply with `expect`: the case's `expect` table states the compared cells, the views and the observer"
                    ));
                }
                CompareSides::Expectation { case, actual }
            }
            _ => {
                return Err("a pair states `left` and `right`, or `expect` and `actual`".to_owned());
            }
        };
        let compare = pair_compare(table.get("compare"))?;
        let views = pair_views(table.get("views"))?;
        let observer = match table.get("observer") {
            None => None,
            Some(Json::String(observer)) if !observer.is_empty() => Some(observer.clone()),
            Some(_) => {
                return Err("`observer` names a definition, `PACKAGE:DEFINITION`".to_owned());
            }
        };
        if observer.is_some() && views.is_empty() {
            return Err(
                "`observer` names the definition the views are evaluated in, and `views` names no view"
                    .to_owned(),
            );
        }
        Ok(CompareRequest {
            sides,
            compare,
            views,
            observer,
            output: template.output,
            solver: template.solver,
            view_budget: template.view_budget,
        })
    }
}

/// What a pair of `left` and `right` asks besides its sides, as its header shows it: its
/// `compare` as `--compare CELL,...`, each view as `--view CELL=FUNCTION` and its `observer` as
/// `--observer PACKAGE:DEFINITION` would give them, each after a comma. Each changes the
/// question, so two pairs over the same sides that ask different questions have different
/// headers. A key whose value is not of its shape shows nothing; the pair's refusal says why.
fn pair_question_flags(record: &Json) -> String {
    let mut text = String::new();
    if let Some(Json::Array(cells)) = record.get("compare") {
        let cells = cells.iter().filter_map(Json::as_str).collect::<Vec<_>>();
        if !cells.is_empty() {
            let _ = write!(text, ", --compare {}", cells.join(","));
        }
    }
    if let Some(Json::Object(views)) = record.get("views") {
        for (cell, function) in views
            .iter()
            .filter_map(|(cell, function)| Some((cell, function.as_str()?)))
        {
            let _ = write!(text, ", --view {cell}={function}");
        }
    }
    if let Some(Json::String(observer)) = record.get("observer") {
        let _ = write!(text, ", --observer {observer}");
    }
    text
}

/// A pair's `compare`: the compared cells, a non-empty array of cell paths.
fn pair_compare(compare: Option<&Json>) -> Result<Option<Vec<String>>, String> {
    match compare {
        None => Ok(None),
        Some(Json::Array(cells)) if !cells.is_empty() => cells
            .iter()
            .map(|cell| match cell {
                Json::String(cell) if !cell.is_empty() => Ok(cell.clone()),
                _ => Err(format!("`compare` holds `{cell}`, which is no cell path")),
            })
            .collect::<Result<Vec<_>, _>>()
            .map(Some),
        Some(_) => Err(
            "`compare` is a non-empty array of cell paths; leave it out to compare every leaf cell that is not unobservable"
                .to_owned(),
        ),
    }
}

/// A pair's `views`: a table of a function by cell.
fn pair_views(views: Option<&Json>) -> Result<BTreeMap<String, String>, String> {
    let named = match views {
        None => return Ok(BTreeMap::new()),
        Some(Json::Object(named)) => named,
        Some(_) => return Err("`views` is a table of a function by cell".to_owned()),
    };
    named
        .iter()
        .map(|(cell, function)| match function {
            Json::String(function) if !cell.is_empty() && !function.is_empty() => {
                Ok((cell.clone(), function.clone()))
            }
            _ => Err(format!(
                "`views`: `{cell}` = `{function}` is no view; a view names a cell and a function"
            )),
        })
        .collect()
}

/// What a pair came to: a verdict, or no verdict and why.
enum Outcome {
    Verdict(Verdict),
    /// The question could not be asked: a pair that is no comparison, a side or an observer
    /// that is refused, a run that fails.
    Refused(String),
    /// No answer: a side's run reached several states under conditions it cannot decide.
    Unanswered(String),
}

impl Outcome {
    fn of(failure: &Failure) -> Self {
        match failure {
            Failure::Exec(ExecError::Undecided(_)) => Self::Unanswered(failure.reason()),
            failure => Self::Refused(failure.reason()),
        }
    }
}

/// One pair's record.
struct PairRecord {
    member: Json,
    label: String,
    outcome: Outcome,
}

impl PairRecord {
    /// The record's exit status ([`exit_status`]): its verdict's, the question not asked for a
    /// refused pair, and no answer for one whose run has no one end.
    const fn status(&self) -> i32 {
        match &self.outcome {
            Outcome::Verdict(verdict) => verdict.exit_code(),
            Outcome::Refused(_) => exit_status::UNASKED,
            Outcome::Unanswered(_) => exit_status::UNANSWERED,
        }
    }

    /// The pair's [`COMPARE_SCHEMA`] document, the one `krs compare` prints for it alone, with
    /// its `pair`.
    fn json(&self) -> Json {
        let mut document = match &self.outcome {
            Outcome::Verdict(verdict) => verdict.document(),
            Outcome::Refused(reason) => {
                json!({"schema": COMPARE_SCHEMA, "verdict": "refused", "reason": reason})
            }
            Outcome::Unanswered(reason) => {
                json!({"schema": COMPARE_SCHEMA, "verdict": "inconclusive", "reason": reason})
            }
        };
        document["pair"] = self.member.clone();
        document
    }

    fn human(&self) -> String {
        let mut text = String::new();
        match &self.outcome {
            Outcome::Verdict(verdict) => verdict.write(&mut text, &self.label),
            Outcome::Refused(reason) => {
                let _ = writeln!(text, "{}: refused: {reason}", self.label);
            }
            Outcome::Unanswered(reason) => {
                let _ = writeln!(text, "{}: inconclusive: {reason}", self.label);
            }
        }
        text
    }
}

/// The verdicts counted, for the summary and the exit status.
#[derive(Default)]
struct Tally {
    equal: usize,
    differs: usize,
    met: usize,
    unmet: usize,
    inconclusive: usize,
    refused: usize,
    /// The [`exit_status::join`] of the records' statuses.
    status: i32,
}

impl Tally {
    fn count(&mut self, record: &PairRecord) {
        let counter = match &record.outcome {
            Outcome::Verdict(Verdict::Ends(verdict)) => match verdict.verdict {
                Compared::Equal => &mut self.equal,
                Compared::Differs(_) => &mut self.differs,
                Compared::Inconclusive(_) => &mut self.inconclusive,
            },
            Outcome::Verdict(Verdict::Expectation(checked)) => match checked.verdict {
                Compared::Equal => &mut self.met,
                Compared::Differs(_) => &mut self.unmet,
                Compared::Inconclusive(_) => &mut self.inconclusive,
            },
            Outcome::Refused(_) => &mut self.refused,
            Outcome::Unanswered(_) => &mut self.inconclusive,
        };
        *counter += 1;
        self.status = exit_status::join(self.status, record.status());
    }

    const fn pairs(&self) -> usize {
        self.equal + self.differs + self.met + self.unmet + self.inconclusive + self.refused
    }

    fn json(&self) -> Json {
        json!({
            "schema": COMPARE_SCHEMA,
            "summary": {
                "pairs": self.pairs(),
                "equal": self.equal,
                "differs": self.differs,
                "met": self.met,
                "unmet": self.unmet,
                "inconclusive": self.inconclusive,
                "refused": self.refused,
            },
            "status": self.status,
        })
    }

    fn human(&self) -> String {
        let pairs = self.pairs();
        format!(
            "krs compare: {pairs} pair{}: {} equal, {} differs, {} met, {} unmet, {} inconclusive, {} refused\n",
            if pairs == 1 { "" } else { "s" },
            self.equal,
            self.differs,
            self.met,
            self.unmet,
            self.inconclusive,
            self.refused
        )
    }
}

/// Prints records in the pairs' order as they arrive in any.
struct Printer {
    next: usize,
    pending: BTreeMap<usize, PairRecord>,
    output: CompareOutput,
    tally: Tally,
}

impl Printer {
    fn put(&mut self, index: usize, record: PairRecord) -> Result<(), Failure> {
        self.pending.insert(index, record);
        while let Some(record) = self.pending.remove(&self.next) {
            self.tally.count(&record);
            let text = match self.output {
                CompareOutput::Json => format!("{}\n", record.json()),
                CompareOutput::Human => record.human(),
            };
            write_stdout(&text)?;
            self.next += 1;
        }
        Ok(())
    }
}

/// How many pairs may be compared ahead of the first one not yet printed, per worker: the bound
/// on the records held back for printing in the pairs' order.
const AHEAD_PER_WORKER: usize = 4;

/// An observer definition, prepared and compiled once, which each worker loads on first use.
struct Observer {
    definition: DefinitionIr,
    stage: CompiledStage,
}

/// One pair to compare: its place, its record's member and label, its comparison, its sides'
/// documents, and its observer when it names one other than the compared definition.
struct Job {
    index: usize,
    member: Json,
    label: String,
    request: CompareRequest,
    read: ReadSides,
    observer: Option<Arc<Observer>>,
    /// The observers its case sides' stop conditions name, prepared and compiled once a batch.
    conditions: NamedConditions<Arc<Observer>>,
}

/// Compare the pairs of the document `request` names (`--pairs`) on the prepared definition, its
/// stage restored or compiled once, each observer prepared by `observers` the first time a pair
/// names it.
pub(super) fn execute_pairs(
    prepared: &PreparedDefinition,
    request: &CompareRequest,
    sources: &DiagnosticSources,
    reuse: StageReuse<'_>,
    observers: &PrepareObserver<'_>,
    measurement: &mut Measurement,
) -> Result<CommandOutcome, CommandError> {
    let CompareSides::Pairs { file, jobs } = &request.sides else {
        unreachable!("execute_pairs is called for --pairs")
    };
    // The document is read before the definition is loaded, as a single comparison's sides are.
    let pairs =
        read_pairs(file, request).map_err(|failure| failure.into_command_error(prepared))?;
    let definition = prepared.lowered.definition();
    let timings = &mut measurement.timings;
    let mut reused = false;
    let reused_flag = &mut reused;
    let result = std::thread::scope(|scope| {
        std::thread::Builder::new()
            .name("krs-compare".into())
            .stack_size(WORKER_STACK)
            .spawn_scoped(scope, move || {
                let (stage, restored) =
                    exec::compiled_stage(definition, reuse, timings).map_err(Failure::Exec)?;
                *reused_flag = restored;
                let batch = Batch {
                    view_budget: request.view_budget,
                    definition,
                    stage: &stage,
                    sources,
                    output: request.output,
                    solver: request.solver,
                    restore: reuse.restore,
                    runs: CaseRuns::default(),
                };
                let workers = jobs
                    .or_else(|| std::thread::available_parallelism().ok())
                    .map_or(1, NonZeroUsize::get)
                    .min(pairs.len());
                timings.span("compare.batch", |timings| {
                    batch.run(pairs, workers, observers, timings)
                })
            })
            .map_err(|error| {
                CommandError::InvalidRequest(format!("could not start the compare worker: {error}"))
            })?
            .join()
            .map_err(|_| CommandError::InvalidRequest("the compare worker panicked".into()))
    })?;
    measurement.counters.set("stage.reused", u64::from(reused));
    result.map_err(|failure| failure.into_command_error(prepared))
}

/// The batch: the definition and its compiled stage, which every worker loads once, and the
/// case runs every worker shares.
struct Batch<'a> {
    /// The polls each evaluation of a case side's stop condition may spend; every pair's
    /// request carries the same (`--view-budget`).
    view_budget: u64,
    definition: &'a DefinitionIr,
    stage: &'a CompiledStage,
    sources: &'a DiagnosticSources,
    output: CompareOutput,
    solver: BackendOptions,
    restore: bool,
    runs: CaseRuns,
}

impl Batch<'_> {
    fn run(
        &self,
        pairs: Vec<Pair>,
        workers: usize,
        observers: &PrepareObserver<'_>,
        timings: &mut Timings,
    ) -> Result<CommandOutcome, Failure> {
        let (job_sender, job_receiver) = mpsc::channel::<Job>();
        let job_receiver = Mutex::new(job_receiver);
        let (record_sender, record_receiver) = mpsc::channel::<(usize, PairRecord)>();
        let mut printer = Printer {
            next: 0,
            pending: BTreeMap::new(),
            output: self.output,
            tally: Tally::default(),
        };
        let measured = timings.is_enabled();
        let spans = std::thread::scope(|scope| {
            let mut handles = Vec::new();
            for worker in 0..workers {
                let records = record_sender.clone();
                let job_receiver = &job_receiver;
                let handle = std::thread::Builder::new()
                    .name(format!("krs-compare-{worker}"))
                    .stack_size(WORKER_STACK)
                    .spawn_scoped(scope, move || {
                        let mut state = Worker::new(self, measured);
                        loop {
                            let job = job_receiver
                                .lock()
                                .unwrap_or_else(PoisonError::into_inner)
                                .recv();
                            let Ok(job) = job else { break };
                            let index = job.index;
                            if records.send((index, state.record(job))).is_err() {
                                break;
                            }
                        }
                        state.timings.take_spans()
                    })
                    .map_err(|error| {
                        Failure::Read(format!("could not start a compare worker: {error}"))
                    })?;
                handles.push(handle);
            }
            drop(record_sender);
            let mut feed = Feed {
                batch: self,
                observers,
                prepared: BTreeMap::new(),
                timings: &mut *timings,
                dispatched: 0,
                ahead: workers.saturating_mul(AHEAD_PER_WORKER),
                jobs: job_sender,
                records: &record_receiver,
                printer: &mut printer,
            };
            let handed = feed.pairs(pairs);
            let dispatched = feed.dispatched;
            // Every worker ends once the jobs are taken and the channel closes.
            drop(feed);
            handed?;
            while printer.next < dispatched {
                let (index, record) = record_receiver.recv().map_err(|_| {
                    Failure::Read(
                        "a compare worker ended before its pairs were compared".to_owned(),
                    )
                })?;
                printer.put(index, record)?;
            }
            Ok::<_, Failure>(
                handles
                    .into_iter()
                    .filter_map(|handle| handle.join().ok())
                    .collect::<Vec<Vec<Span>>>(),
            )
        })?;
        // The workers' spans, which ran in parallel with each other and with the pairs' feed.
        for worker in spans {
            timings.import(worker);
        }
        let summary = match self.output {
            CompareOutput::Json => format!("{}\n", printer.tally.json()),
            CompareOutput::Human => printer.tally.human(),
        };
        write_stdout(&summary)?;
        Ok(exec::outcome(
            String::new(),
            String::new(),
            printer.tally.status,
        ))
    }
}

/// The coordinator's side of the batch: reads each pair's sides, prepares observers, hands out
/// the pairs, and prints the records as they come back.
struct Feed<'f, 'b> {
    batch: &'f Batch<'b>,
    observers: &'f PrepareObserver<'f>,
    /// Each observer named so far, prepared and compiled, or why it is not.
    prepared: BTreeMap<String, Result<Option<Arc<Observer>>, String>>,
    timings: &'f mut Timings,
    dispatched: usize,
    ahead: usize,
    jobs: mpsc::Sender<Job>,
    records: &'f mpsc::Receiver<(usize, PairRecord)>,
    printer: &'f mut Printer,
}

impl Feed<'_, '_> {
    fn pairs(&mut self, pairs: Vec<Pair>) -> Result<(), Failure> {
        for pair in pairs {
            let Pair {
                member,
                label,
                request,
            } = pair;
            let refused = |reason| PairRecord {
                member: member.clone(),
                label: label.clone(),
                outcome: Outcome::Refused(reason),
            };
            let request = match request {
                Ok(request) => request,
                Err(reason) => {
                    self.settle(refused(reason))?;
                    continue;
                }
            };
            let read = match read(&request) {
                Ok(read) => read,
                Err(failure) => {
                    self.settle(PairRecord {
                        outcome: Outcome::of(&failure),
                        ..refused(String::new())
                    })?;
                    continue;
                }
            };
            let observer = match observer_name(&request, &read).map(str::to_owned) {
                Some(name) => match self.observer(&name) {
                    Ok(observer) => observer,
                    Err(reason) => {
                        self.settle(refused(reason))?;
                        continue;
                    }
                },
                None => None,
            };
            let conditions = condition_observers(&read)
                .into_iter()
                .map(|name| {
                    let observer = self.observer(&name);
                    (name, observer)
                })
                .collect();
            self.wait_for_room()?;
            let job = Job {
                index: self.dispatched,
                member,
                label,
                request,
                read,
                observer,
                conditions,
            };
            self.jobs.send(job).map_err(|_| {
                Failure::Read(
                    "every compare worker ended before the pairs were compared".to_owned(),
                )
            })?;
            self.dispatched += 1;
        }
        Ok(())
    }

    /// Print `record` at the next place, after the pairs handed out before it.
    fn settle(&mut self, record: PairRecord) -> Result<(), Failure> {
        self.wait_for_room()?;
        let index = self.dispatched;
        self.dispatched += 1;
        self.printer.put(index, record)
    }

    /// Wait until fewer than [`Self::ahead`] pairs are compared ahead of the first one not
    /// printed.
    fn wait_for_room(&mut self) -> Result<(), Failure> {
        while self.dispatched - self.printer.next >= self.ahead {
            let (index, record) = self.records.recv().map_err(|_| {
                Failure::Read(
                    "every compare worker ended before the pairs were compared".to_owned(),
                )
            })?;
            self.printer.put(index, record)?;
        }
        Ok(())
    }

    /// The observer `name`, prepared and compiled the first time a pair names it.
    fn observer(&mut self, name: &str) -> Result<Option<Arc<Observer>>, String> {
        if let Some(prepared) = self.prepared.get(name) {
            return prepared.clone();
        }
        let restore = self.batch.restore;
        let observers = self.observers;
        let prepared = self.timings.span("compare.observer", |timings| {
            observers(name).and_then(|observer| {
                observer
                    .map(|observer| {
                        let reuse = StageReuse {
                            cache: observer.cache.as_ref(),
                            restore,
                        };
                        let (stage, _) = exec::compiled_stage(&observer.definition, reuse, timings)
                            .map_err(|error| {
                                format!("the observer `{name}` cannot be compiled: {error}")
                            })?;
                        Ok(Arc::new(Observer {
                            definition: observer.definition,
                            stage,
                        }))
                    })
                    .transpose()
            })
        });
        self.prepared.insert(name.to_owned(), prepared.clone());
        prepared
    }
}

/// A worker's definitions, each loaded on its first pair, and the spans it records.
struct Worker<'a> {
    batch: &'a Batch<'a>,
    subject: Option<Result<Semantics, String>>,
    /// The observers loaded, by the prepared observer they were loaded from.
    observers: Vec<(Arc<Observer>, Result<Semantics, String>)>,
    /// The definitions case sides' stop conditions are evaluated in.
    conditions: Conditions<'a>,
    timings: Timings,
}

impl<'a> Worker<'a> {
    fn new(batch: &'a Batch<'a>, measured: bool) -> Self {
        Self {
            batch,
            subject: None,
            observers: Vec::new(),
            conditions: Conditions::new(
                batch.view_budget,
                batch.definition,
                batch.stage,
                batch.solver,
                batch.restore,
            ),
            timings: if measured {
                Timings::enabled()
            } else {
                Timings::disabled()
            },
        }
    }

    /// The record of `job`; a panic while comparing refuses the pair and reloads the
    /// definitions for the next one, since their state is then unknown.
    fn record(&mut self, job: Job) -> PairRecord {
        let member = job.member.clone();
        let label = job.label.clone();
        let outcome = match std::panic::catch_unwind(AssertUnwindSafe(|| self.compare(job))) {
            Ok(Ok(verdict)) => Outcome::Verdict(verdict),
            Ok(Err(outcome)) => outcome,
            Err(_) => {
                self.subject = None;
                self.observers.clear();
                self.conditions.loaded.clear();
                Outcome::Refused("krs panicked while comparing the pair".to_owned())
            }
        };
        PairRecord {
            member,
            label,
            outcome,
        }
    }

    fn compare(&mut self, job: Job) -> Result<Verdict, Outcome> {
        let Self {
            batch,
            subject,
            observers,
            conditions,
            timings,
        } = self;
        let subject = subject
            .get_or_insert_with(|| {
                let sources = batch.sources.clone();
                let provider: SourceText = Box::new(move |file| sources.source_text(file));
                timings
                    .span("compare.load", |timings| {
                        Semantics::from_stage_with_solver(
                            batch.definition,
                            batch.stage.clone(),
                            Some(provider),
                            batch.solver,
                            timings,
                        )
                    })
                    .map_err(|error| format!("krs cannot load the definition: {error}"))
            })
            .as_mut()
            .map_err(|reason| Outcome::Refused(reason.clone()))?;
        let observer = match &job.observer {
            None => None,
            Some(observer) => {
                let position = if let Some(position) = observers
                    .iter()
                    .position(|(loaded, _)| Arc::ptr_eq(loaded, observer))
                {
                    position
                } else {
                    let semantics = timings
                        .span("compare.observer_load", |timings| {
                            Semantics::from_stage_with_solver(
                                &observer.definition,
                                observer.stage.clone(),
                                None,
                                batch.solver,
                                timings,
                            )
                        })
                        .map_err(|error| format!("krs cannot load the observer: {error}"));
                    observers.push((Arc::clone(observer), semantics));
                    observers.len() - 1
                };
                Some(
                    observers[position]
                        .1
                        .as_mut()
                        .map_err(|reason| Outcome::Refused(reason.clone()))?,
                )
            }
        };
        for (name, observer) in job.conditions {
            conditions.name(
                name,
                observer.map(|observer| observer.map(ConditionObserver::Compiled)),
            );
        }
        compare(
            subject,
            observer,
            conditions,
            &job.request,
            job.read,
            &batch.runs,
            timings,
        )
        .map_err(|failure| Outcome::of(&failure))
    }
}

#[cfg(test)]
mod tests {
    use super::SideFile;
    use std::path::PathBuf;

    #[test]
    fn a_side_is_a_document_and_the_case_its_name_selects() {
        let side = |path: &str, name: Option<&str>| SideFile {
            path: PathBuf::from(path),
            name: name.map(str::to_owned),
        };
        assert_eq!(SideFile::parse("a.json"), Ok(side("a.json", None)));
        assert_eq!(
            SideFile::parse("cases/a.toml#ld-a"),
            Ok(side("cases/a.toml", Some("ld-a")))
        );
        assert_eq!(
            SideFile::parse("a.toml#x#y"),
            Ok(side("a.toml", Some("x#y")))
        );
        assert_eq!(
            SideFile::parse("dir#1/a.json"),
            Ok(side("dir#1/a.json", None))
        );
        assert_eq!(
            SideFile::parse("a.toml#ld-a").unwrap().to_string(),
            "a.toml#ld-a"
        );
        assert_eq!(
            SideFile::parse("a.toml#"),
            Err("`a.toml#`: no case name follows `#`".to_owned())
        );
        assert_eq!(
            SideFile::parse("a.txt"),
            Err(
                "the document `a.txt` is not a `.toml` or `.json` file, which its extension says"
                    .to_owned()
            )
        );
    }
}
