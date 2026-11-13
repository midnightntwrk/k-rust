//! `krs compare`: two ends of the definition compared, or an end checked against a case's
//! expectation, printed as `krs run --case` prints an expectation's verdict.
//!
//! Each side is a file: an end document (`halt`, `rule`, `cells`; krs-exec's `ends` module, "End
//! documents"), an observation document (`schema`, `channels`: the `krs-observations/1` document
//! `krs run --output observations` prints, krs-exec's `observations` module), or a case document,
//! whose case is run as `krs run --case` runs it (its inputs, its `run` table and its `observe`)
//! and whose run's end, and the observations its `observe` declares, are the side. A document of
//! named cases names its case as `FILE#NAME`, the case's id in `krs cases`. The keys of the three
//! kinds are disjoint, so a document is read as one kind, and one that holds keys of two is
//! refused.
//!
//! A side states ends (an end document, a case), observations (an observation document, a case
//! whose `observe` declares a channel), or both (such a case). Two sides are compared on what both
//! state: their ends where both state ends, their observations where both state observations, and
//! two sides that state nothing in common are refused. Observations are compared under one
//! declaration: two cases must declare the same `observe`, and an observation document must have
//! the channels the other side has, by name and kind, in order (that its elements correspond to
//! the other side's is its producer's claim). Where only one side states observations, the
//! verdict says they are not compared.
//!
//! Two records of observations are compared by krs-exec's one comparison of records
//! (`compare_records`): the first decided difference (a channel, an index, both sides' elements or
//! closures there, and the path inside two values), which is a finding (exit 1); or how far each
//! channel agrees. An element is a function of a finite prefix of its path, and a record knows
//! each channel up to where it is closed or open, so a difference read there holds of every
//! longer run, and a bound only ends what is known. The agreement is:
//!
//! - equal (exit 0), to both sides' closure, or up to a horizon where a side is open at a bound
//!   (its case's depth, a split of its path): the verdict says so and names each channel's
//!   horizon. The bound is part of the side's question, as `krs run --output observations`
//!   answers a depth-bounded run's observations with yes, and as two runs that a depth bound
//!   ended compare equal on their ends: nothing past the horizon is claimed;
//! - inconclusive (exit 3) where an element before any difference is unknown, or a side is open
//!   as undecided (an evaluation's budget spent, the solver undecided, an inconclusive halt)
//!   where the other side still knows the index: another run, with more budget, may differ there;
//! - inconclusive where the record does not hold of the definition: a case run that has no one
//!   path has no record, and where both sides' runs read a value the definition leaves open a
//!   difference may be one implementation's choice (where one side's run read none, that side's
//!   path is the definition's only one up to its record's open points, so a difference from it
//!   holds), and an agreement holds only where neither side's run read one.
//!
//! The observations are compared first: their first difference is reached before either path's
//! end, so the ends are compared only where the observations do not differ, and the verdict is
//! the join of the two, a difference before no answer before equal.
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
//! In a definition that declares ends, two sides are compared on what both state of the declared
//! class of their ends (`class`, `end`, `reason`), each part where every end of both states it
//! ([`Semantics::compare_ends`]): an end document that states only its halt is compared with a
//! run's end of any class on its halt and cells.
//!
//! With `--expect CASE`, the case's `expect` table is the expected end, with the cells it is
//! compared on, its views and its observer, and the one side given is checked against it as
//! `krs run --case` checks a run's end ([`Semantics::check_expectation`]): `--compare`, `--view`
//! and `--observer` do not apply, since the expectation states them. An end document is refused
//! where it does not state a compared cell, or, ending `stuck`, a part of the declared class the
//! expectation states ([`Semantics::check_stated_class`]).
//!
//! The case of a case side is run, never checked: its own `expect` table is not part of the
//! comparison.
//!
//! A case side's observations are recorded as `krs run --case` and `krs cases` record them, so a
//! case whose observation sequence does not exist (an element with no value) is refused here as
//! there, whatever the comparison reads of it.
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
    BackendOptions, CaseDocument, CellViews, ChannelAgreement, ChannelKind, Compared, Comparison,
    CompiledStage, Difference, EndError, Ends, ExecError, ObservationDifference, ObservationSpec,
    Observations, Observed, Observers, Reach, RecordComparison, RunOptions, RunReport, Semantics,
    Side, SourceText, State, StopCriterion, compare_records, json_document, open_values,
    toml_text_document,
};
use krs_ir::measure::{Measurement, Span, Timings};
use krs_ir_levels::DefinitionIr;
use serde_json::{Value as Json, json};

use super::cases::{PrepareObserver, write_stdout};
use super::definition_cache::RunDefinition;
use super::exec::{
    self, CaseFiles, Checked, Failure, Inputs, ObserverDefinition, SelectedCase, StageReuse,
    WORKER_STACK,
};
use super::{CommandError, CommandOutcome, compared_status, exit_status};
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
    /// An observation document, read as the record it states.
    Observations { record: Observations },
}

impl SideDocument {
    /// What the side is, as a refusal names it.
    const fn kind(&self) -> &'static str {
        match self {
            Self::End { .. } => "an end document",
            Self::Case(_) => "a case",
            Self::Observations { .. } => "an observation document",
        }
    }

    /// Whether the side states ends: an end document's one end, a case run's.
    const fn states_ends(&self) -> bool {
        matches!(self, Self::End { .. } | Self::Case(_))
    }

    /// The observations a case side declares, where it declares a channel.
    fn declared(&self) -> Option<&ObservationSpec> {
        match self {
            Self::Case(case) => case.case.observe.as_deref().filter(|spec| !spec.is_empty()),
            _ => None,
        }
    }

    /// Whether the side states observations: an observation document's, a case run's whose case
    /// declares a channel.
    fn states_observations(&self) -> bool {
        matches!(self, Self::Observations { .. }) || self.declared().is_some()
    }

    /// The side's channels by name and kind, in order, where it states observations: an
    /// observation document's, or those a case's declaration gives a record, its classes then its
    /// logs.
    fn channels(&self) -> Option<Vec<(&str, ChannelKind)>> {
        match self {
            Self::Observations { record, .. } => Some(
                record
                    .channels
                    .iter()
                    .map(|channel| (channel.name.as_str(), channel.kind))
                    .collect(),
            ),
            _ => self.declared().map(|spec| {
                spec.points
                    .iter()
                    .map(|point| (point.name.as_str(), ChannelKind::Point))
                    .chain(
                        spec.logs
                            .iter()
                            .map(|log| (log.name.as_str(), ChannelKind::Log)),
                    )
                    .collect()
            }),
        }
    }
}

/// The two sides' documents: `LEFT` and `RIGHT`, or `CASE` and `ACTUAL`.
pub(super) struct ReadSides {
    first: SideDocument,
    second: SideDocument,
}

/// The keys of an end document.
const END_KEYS: [&str; 3] = ["halt", "rule", "cells"];

/// The keys of a case document: one case's, and a document of named cases'.
const CASE_KEYS: [&str; 5] = ["inputs", "run", "observe", "expect", "case"];

/// The keys of an observation document.
const OBSERVATION_KEYS: [&str; 2] = ["schema", "channels"];

/// Read the sides' documents of `request`, before the definition is loaded.
///
/// # Errors
///
/// Fails for a document that cannot be read, holds keys of two kinds, or is no case document,
/// a `#NAME` its document does not select, and, with `--expect`, an end document or an
/// observation document named as the case, a case that states no expectation, and an observation
/// document named as the actual side.
pub(super) fn read(request: &CompareRequest) -> Result<ReadSides, Failure> {
    let (first, second) = match &request.sides {
        CompareSides::Ends { left, right } => (left, right),
        CompareSides::Expectation { case, actual } => (case, actual),
        CompareSides::Pairs { .. } => unreachable!("a batch reads each of its pairs' sides"),
    };
    let first = read_side(first)?;
    if let CompareSides::Expectation { case, .. } = &request.sides {
        match &first {
            SideDocument::End { .. } | SideDocument::Observations { .. } => {
                return Err(Failure::Usage(format!(
                    "--expect `{case}` names {}; --expect names a case document whose `expect` table states the expected end",
                    first.kind()
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
    if let (CompareSides::Expectation { actual, .. }, SideDocument::Observations { .. }) =
        (&request.sides, &second)
    {
        return Err(Failure::Usage(format!(
            "--expect checks an end against the case's expectation, and `{actual}` is an observation document, which states no end"
        )));
    }
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
    let kinds = [&END_KEYS[..], &OBSERVATION_KEYS[..], &CASE_KEYS[..]];
    let kind_of = |key: &String| kinds.iter().position(|keys| keys.contains(&key.as_str()));
    let kind = match &document {
        Json::Object(table) => {
            let first = table.keys().find_map(kind_of);
            if let Some(key) = table
                .keys()
                .find(|key| kind_of(key).is_some_and(|kind| Some(kind) != first))
            {
                return Err(refuse(
                    file,
                    &format!(
                        "`{key}`: a document is an end document (`halt`, `rule`, `cells`), an observation document (`schema`, `channels`) or a case document (`inputs`, `run`, `observe`, `expect`, or `case` for named cases), one of the three"
                    ),
                ));
            }
            first
        }
        _ => None,
    };
    if kind == Some(1) {
        if let Some(name) = &file.name {
            return Err(Failure::Usage(format!(
                "`{file}`: `{}` is an observation document, which states one record and no named case; name it without `#{name}`",
                path.display()
            )));
        }
        let record = Observations::from_document(&document).map_err(|error| {
            Failure::Exec(ExecError::Observe(format!(
                "`{file}`: the observation document {error}"
            )))
        })?;
        return Ok(SideDocument::Observations { record });
    }
    if kind == Some(0) {
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
    prepared: &RunDefinition,
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
    let definition = prepared.definition();
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
    result.map_err(|failure: Failure| failure.into_command_error(prepared.source_map()))
}

/// The observations part of a comparison ([module documentation](self)).
enum ObservationsPart {
    /// Only one side states observations: why the other states none.
    Unstated(String),
    /// The first decided difference.
    Differs(Box<ObservationDifference>),
    /// No difference: how far each channel agrees, and why that answers nothing where it does
    /// not.
    Agree {
        channels: Vec<ChannelAgreement>,
        inconclusive: Option<String>,
    },
}

impl ObservationsPart {
    /// The part's exit status ([`exit_status`]): a difference is a finding, an agreement that
    /// answers nothing has no answer, and an agreement to both sides' closure or up to a horizon
    /// is yes, as is a part that compares nothing.
    const fn status(&self) -> i32 {
        match self {
            Self::Differs(_) => exit_status::NO,
            Self::Agree {
                inconclusive: Some(_),
                ..
            } => exit_status::UNANSWERED,
            Self::Unstated(_) | Self::Agree { .. } => exit_status::YES,
        }
    }

    /// Whether some channel agrees up to a horizon rather than to both sides' closure.
    fn bounded(&self) -> bool {
        matches!(self, Self::Agree { channels, .. } if channels.iter().any(ChannelAgreement::bounded))
    }

    /// The part's document: `{"not_compared": REASON}`; `{"difference": {"channel", "index",
    /// "left", "right", "path"}}`, each side an element's document or `"end"` or `"undefined"`;
    /// or `{"agree": [{"channel", "through", "left", "right", "uncompared"?}], "reason"?}`, each
    /// side `"end"` or `"undefined"` where it closed there, `{"open": {"index", "reason",
    /// "undecided"?}}` where it is open there, or `"known"`.
    fn document(&self) -> Json {
        match self {
            Self::Unstated(reason) => json!({"not_compared": reason}),
            Self::Differs(difference) => json!({"difference": {
                "channel": difference.channel,
                "index": difference.index,
                "left": difference.left.document(difference.index),
                "right": difference.right.document(difference.index),
                "path": difference.path,
            }}),
            Self::Agree {
                channels,
                inconclusive,
            } => {
                let reach = |reach: &Reach| match reach {
                    Reach::Closed(closure) => json!(closure),
                    Reach::Open(open) => json!({"open": open}),
                    Reach::Known => json!("known"),
                };
                let channels = channels
                    .iter()
                    .map(|agreement| {
                        let mut document = json!({
                            "channel": agreement.channel,
                            "through": agreement.through,
                            "left": reach(&agreement.left),
                            "right": reach(&agreement.right),
                        });
                        if let Some(uncompared) = &agreement.uncompared {
                            document["uncompared"] = json!({
                                "index": uncompared.index,
                                "side": uncompared.side,
                                "reason": uncompared.reason,
                            });
                        }
                        document
                    })
                    .collect::<Vec<_>>();
                let mut document = json!({"agree": channels});
                if let Some(reason) = inconclusive {
                    document["reason"] = json!(reason);
                }
                document
            }
        }
    }

    /// The part's lines below a verdict's head: a line per agreeing channel, or why the
    /// observations are not compared; nothing for a difference, which the head shows.
    fn write(&self, output: &mut String) {
        match self {
            Self::Differs(_) => {}
            Self::Unstated(reason) => {
                let _ = writeln!(output, "  observations not compared: {reason}");
            }
            Self::Agree { channels, .. } => {
                for agreement in channels {
                    let through = agreement.through;
                    let elements = format!(
                        "{through} element{} agree{}",
                        if through == 1 { "" } else { "s" },
                        if through == 1 { "s" } else { "" }
                    );
                    let open = |reach: &Reach| match reach {
                        Reach::Open(open) => Some(open.reason.clone()),
                        _ => None,
                    };
                    let then = match (&agreement.left, &agreement.right) {
                        (Reach::Closed(krs_exec::Closure::End), _) => {
                            "then both paths end".to_owned()
                        }
                        (Reach::Closed(krs_exec::Closure::Undefined), _) => {
                            "then both paths take an undefined step".to_owned()
                        }
                        (left, right) => match (open(left), open(right)) {
                            (Some(left), Some(right)) => format!(
                                "then both sides are open: the left side: {left}; the right side: {right}"
                            ),
                            (Some(reason), None) => format!("then the left side is open: {reason}"),
                            (None, Some(reason)) => {
                                format!("then the right side is open: {reason}")
                            }
                            (None, None) => String::new(),
                        },
                    };
                    let _ = writeln!(
                        output,
                        "  observation `{}`: {elements}, {then}",
                        agreement.channel
                    );
                    if let Some(uncompared) = &agreement.uncompared {
                        let _ = writeln!(
                            output,
                            "    element {} is not compared{}: {}",
                            uncompared.index,
                            uncompared.side.map_or_else(String::new, |side| format!(
                                ", unknown on the {} side",
                                side.as_str()
                            )),
                            uncompared.reason
                        );
                    }
                }
            }
        }
    }
}

/// The lines of an observation difference, headed by `head`: where, then each side's element or
/// closure there.
fn write_observation_difference(
    output: &mut String,
    head: &str,
    difference: &ObservationDifference,
) {
    let at = difference
        .path
        .as_ref()
        .map_or_else(String::new, |path| format!(" at `{path}`"));
    let _ = writeln!(
        output,
        "{head} at the observation `{}` element {}{at}",
        difference.channel, difference.index
    );
    let shown = |observed: &Observed| match observed {
        Observed::End => "the end of the path".to_owned(),
        Observed::Undefined => "an undefined step, which ends the path".to_owned(),
        Observed::Element(element) => {
            let value = match (&element.undecided, &element.value) {
                (Some(reason), _) => format!("unknown ({reason})"),
                (None, Some(value)) => value.to_string(),
                (None, None) => "an element".to_owned(),
            };
            let steps = format!(
                "after {} step{}",
                element.depth,
                if element.depth == 1 { "" } else { "s" }
            );
            let point = match (&element.rule, element.side) {
                (Some(rule), Some(side)) => format!(
                    "{} `{rule}`, {steps}",
                    match side {
                        krs_exec::StopAt::Before => "before",
                        krs_exec::StopAt::After => "after",
                    }
                ),
                (Some(rule), None) => format!("at `{rule}`, {steps}"),
                (None, _) => format!("read at the path's end, {steps}"),
            };
            format!("{value} ({point})")
        }
    };
    for (name, observed) in [("left:", &difference.left), ("right:", &difference.right)] {
        let _ = writeln!(output, "  {name:<6} {}", shown(observed));
    }
}

/// The verdict of two sides: their ends' where both state ends and the observations do not
/// differ, their observations' where either states observations, with the views it applied.
struct SidesVerdict {
    ends: Option<Compared>,
    observations: Option<ObservationsPart>,
    views: BTreeMap<String, String>,
    observer: Option<String>,
}

impl SidesVerdict {
    /// The exit status the verdict gives ([`exit_status`]): the join of its parts', a difference
    /// (a finding) before no answer before equal.
    const fn exit_code(&self) -> i32 {
        let ends = match &self.ends {
            Some(ends) => compared_status(ends),
            None => exit_status::YES,
        };
        let observations = match &self.observations {
            Some(observations) => observations.status(),
            None => exit_status::YES,
        };
        exit_status::join(ends, observations)
    }

    const fn word(&self) -> &'static str {
        match self.exit_code() {
            exit_status::YES => "equal",
            exit_status::NO => "differs",
            _ => "inconclusive",
        }
    }

    /// Why the verdict is inconclusive: the ends' reason, else the observations'.
    fn reason(&self) -> Option<&str> {
        match (&self.ends, &self.observations) {
            (Some(Compared::Inconclusive(reason)), _)
            | (
                _,
                Some(ObservationsPart::Agree {
                    inconclusive: Some(reason),
                    ..
                }),
            ) => Some(reason),
            _ => None,
        }
    }

    fn document(&self) -> Json {
        let mut document = json!({"schema": COMPARE_SCHEMA, "verdict": self.word()});
        if let Some(Compared::Differs(difference)) = &self.ends {
            document["difference"] = json!(difference);
        }
        if self.exit_code() == exit_status::UNANSWERED
            && let Some(reason) = self.reason()
        {
            document["reason"] = json!(reason);
        }
        if let Some(observations) = &self.observations {
            document["observations"] = observations.document();
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
        match (&self.observations, &self.ends) {
            (Some(ObservationsPart::Differs(difference)), _) => {
                write_observation_difference(output, &format!("{label}: differs"), difference);
            }
            (_, Some(Compared::Differs(difference))) => {
                exec::write_difference(output, &format!("{label}: differs"), difference);
                write_pair_note(output, difference);
            }
            _ => match self
                .reason()
                .filter(|_| self.exit_code() == exit_status::UNANSWERED)
            {
                Some(reason) => {
                    let _ = writeln!(output, "{label}: inconclusive: {reason}");
                }
                None if self
                    .observations
                    .as_ref()
                    .is_some_and(ObservationsPart::bounded) =>
                {
                    let _ = writeln!(output, "{label}: equal up to a horizon");
                }
                None => {
                    let _ = writeln!(output, "{label}: equal");
                }
            },
        }
        if let Some(observations) = &self.observations {
            observations.write(output);
        }
        let observer = self.observer.as_deref().filter(|_| !self.views.is_empty());
        exec::write_views(output, &self.views, observer);
    }
}

/// One comparison's verdict: two sets of ends compared, or a side checked against a case's
/// expectation.
enum Verdict {
    Sides(SidesVerdict),
    Expectation(Checked),
}

impl Verdict {
    /// The exit status the verdict gives ([`exit_status`]).
    const fn exit_code(&self) -> i32 {
        match self {
            Self::Sides(verdict) => verdict.exit_code(),
            Self::Expectation(checked) => checked.exit_code(),
        }
    }

    /// The [`COMPARE_SCHEMA`] document.
    fn document(&self) -> Json {
        match self {
            Self::Sides(verdict) => verdict.document(),
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
            Self::Sides(verdict) => verdict.write(output, label),
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

/// The observers the stop conditions and the observations of a comparison's case sides name,
/// each prepared before any run asks: by name, `None` for one that names the compared definition
/// itself, or why it could not be prepared.
pub(super) type NamedConditions<O> = Vec<(String, Result<Option<O>, String>)>;

/// The observers the stop conditions and the observations of `read`'s case sides name, each
/// once, in the order of the sides: each is prepared before the sides are run, as a views'
/// observer is, so that the dependency facets it composes are known before the comparison.
pub(super) fn run_observers(read: &ReadSides) -> Vec<String> {
    let mut names = Vec::new();
    for side in [&read.first, &read.second] {
        let SideDocument::Case(case) = side else {
            continue;
        };
        // A case whose stops cannot be read is refused when it is run.
        let condition = case
            .stop(&StopCriterion::None, None)
            .ok()
            .and_then(|stop| stop.when().and_then(|when| when.observer.clone()));
        let observations = side
            .declared()
            .filter(|spec| spec.declares_function())
            .and_then(|spec| spec.observer.clone());
        for name in [condition, observations].into_iter().flatten() {
            if !names.contains(&name) {
                names.push(name);
            }
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

/// The definitions the stop conditions and the observations of case sides' runs are evaluated
/// in, each loaded the first time a run asks one: another semantics of the compared definition,
/// or an observer it names, prepared beforehand ([`Self::name`]). They are loaded apart from the
/// views' observer, which a comparison reads at the same time, and a run's observations apart
/// from its stop condition, since the run asks both at once.
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
    /// The stop conditions' definitions by observer name, `None` for the compared definition's
    /// own.
    loaded: Vec<(Option<String>, Result<Semantics, String>)>,
    /// The observations' definitions, by observer name as [`Self::loaded`].
    observations: Vec<(Option<String>, Result<Semantics, String>)>,
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
            observations: Vec::new(),
        }
    }

    /// Record the observer `name`, prepared, unless it is recorded already.
    fn name(&mut self, name: String, observer: Result<Option<ConditionObserver>, String>) {
        self.named.entry(name).or_insert(observer);
    }

    /// The definition the condition of `criterion` is evaluated in; `None` without one.
    fn of(&mut self, criterion: &StopCriterion) -> Result<Option<&mut Semantics>, Failure> {
        Ok(self.for_run(criterion, None)?.condition)
    }

    /// The definitions a run under `criterion` and the observations `observe` is evaluated in:
    /// its condition's, and its observations' where they evaluate a function.
    fn for_run(
        &mut self,
        criterion: &StopCriterion,
        observe: Option<&ObservationSpec>,
    ) -> Result<Observers<'_>, Failure> {
        let condition = criterion
            .when()
            .map(|when| self.position(false, when.observer.clone()));
        let observations = observe
            .filter(|spec| spec.declares_function())
            .map(|spec| self.position(true, spec.observer.clone()));
        let condition = match condition {
            None => None,
            Some(position) => Some(
                self.loaded[position]
                    .1
                    .as_mut()
                    .map_err(|reason| Failure::Exec(ExecError::StopWhen(reason.clone())))?,
            ),
        };
        let observations = match observations {
            None => None,
            Some(position) => Some(
                self.observations[position]
                    .1
                    .as_mut()
                    .map_err(|reason| Failure::Exec(ExecError::Observe(reason.clone())))?,
            ),
        };
        Ok(Observers {
            condition,
            observations,
        })
    }

    /// The place of the definition the observer `key` names (`None` for the compared
    /// definition's own) among the loaded observations' definitions (`observations`) or the stop
    /// conditions', loaded there the first time it is asked.
    fn position(&mut self, observations: bool, key: Option<String>) -> usize {
        let loaded = if observations {
            &self.observations
        } else {
            &self.loaded
        };
        if let Some(position) = loaded.iter().position(|(loaded, _)| *loaded == key) {
            return position;
        }
        let timings = &mut Timings::disabled();
        let own = |timings: &mut Timings| {
            exec::load_condition(self.definition, self.stage, None, self.solver, timings)
                .map_err(|error| error.to_string())
        };
        let semantics = match &key {
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
        .map_err(|error| {
            if observations {
                format!("krs cannot load the observations' definition: {error}")
            } else {
                format!("krs cannot load the stop condition's definition: {error}")
            }
        });
        let loaded = if observations {
            &mut self.observations
        } else {
            &mut self.loaded
        };
        loaded.push((key, semantics));
        loaded.len() - 1
    }
}

/// A case's run: its ends, the run they are of, and once the run is followed again, whether
/// its end is the case's only one.
struct CaseRun {
    ends: Ends,
    /// The record of the observations its case declares: `None` where it declares none, the
    /// reason where the run has no record.
    observations: Option<Result<Observations, String>>,
    /// Why the run's path may not be the definition's only one up to its record's open points:
    /// it read values the definition leaves open ([`open_values`]); `None` where it read none.
    chosen: Option<String>,
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
    /// depth and stops, and the observations its `observe` declares recorded as `krs run --case`
    /// records them, so that one whose element has no value refuses the run.
    fn run(
        semantics: &mut Semantics,
        conditions: &mut Conditions<'_>,
        case: &SelectedCase,
    ) -> Result<Self, Failure> {
        let stop = case.stop(&StopCriterion::None, None)?;
        let depth = case.depth(None)?;
        let state = exec::configure(semantics, Inputs::of_case(case), false)?;
        let observe = case
            .case
            .observe
            .as_deref()
            .filter(|spec| !spec.is_empty())
            .cloned();
        let declared = observe.is_some();
        let options = RunOptions {
            depth,
            stop,
            condition_budget: Some(conditions.budget),
            observe,
            ..RunOptions::default()
        };
        let observers = conditions.for_run(&options.stop, options.observe.as_ref())?;
        let report = match semantics.run_with(&state, options.clone(), observers) {
            Ok(report) => report,
            // A run that cannot decide which of several states it reaches has no one end, and
            // no one path to record observations along.
            Err(error @ ExecError::Undecided { .. }) => {
                return Ok(Self {
                    ends: Ends::none(format!("the run has no one end: {error}")),
                    observations: declared
                        .then(|| Err(format!("the run has no one path: {error}"))),
                    chosen: None,
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
        let observations = declared.then(|| Ok(report.observations.clone().unwrap_or_default()));
        let chosen = open_values(&report.implementation_chosen_values);
        // A run with no end has nothing a completeness could change; following it again reads
        // no observation.
        let run = (!ends.ends.is_empty()).then_some(RunOf {
            state,
            options: RunOptions {
                observe: None,
                ..options
            },
            report,
        });
        Ok(Self {
            ends,
            observations,
            chosen,
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

/// A side: an end document's one end, an observation document's record, or a case's run, its
/// ends until their completeness is known.
struct Produced {
    name: &'static str,
    source: Source,
}

enum Source {
    End(Ends),
    /// An observation document's record.
    Record(Observations),
    /// A case's run, and whether this comparison followed it again ([`Produced::settle`]).
    Run {
        run: Arc<CaseRun>,
        followed: bool,
    },
}

impl Produced {
    /// The side's ends; a comparison reads them only of a side that states ends
    /// ([`SideDocument::states_ends`]).
    fn ends(&self) -> &Ends {
        match &self.source {
            Source::End(ends) => ends,
            Source::Record(_) => {
                unreachable!("ends are compared only where both sides state them")
            }
            Source::Run { run, followed } => (*followed)
                .then(|| run.followed.get())
                .flatten()
                .and_then(|followed| followed.as_ref().ok().and_then(Option::as_ref))
                .unwrap_or(&run.ends),
        }
    }

    /// The side's record of observations, or why its run has none; `None` for a side that
    /// states no observations.
    fn record(&self) -> Option<Result<&Observations, &str>> {
        match &self.source {
            Source::End(_) => None,
            Source::Record(record) => Some(Ok(record)),
            Source::Run { run, .. } => run
                .observations
                .as_ref()
                .map(|record| record.as_ref().map_err(String::as_str)),
        }
    }

    /// Why the side's path may not be the definition's only one ([`CaseRun::chosen`]).
    fn chosen(&self) -> Option<&str> {
        match &self.source {
            Source::Run { run, .. } => run.chosen.as_deref(),
            Source::End(_) | Source::Record(_) => None,
        }
    }

    fn side(&self) -> Side<'_> {
        Side {
            name: self.name,
            ends: self.ends(),
        }
    }

    /// The end `document` of the side `file` states, refused unless it states every cell
    /// `comparison` compares and, checked against the expectation `expected`, each part of its
    /// declared class the expectation states.
    fn end(
        semantics: &Semantics,
        name: &'static str,
        (file, document, base): (&SideFile, &Json, PathBuf),
        comparison: &Comparison,
        expected: Option<&krs_exec::End>,
    ) -> Result<Self, Failure> {
        let mut files = CaseFiles { base };
        let end = semantics
            .read_end_in(document, None, &mut files)
            .map_err(|error| refuse(file, &error.to_string()))?;
        semantics
            .check_stated(comparison, &end, name)
            .map_err(|error| refuse(file, &error.to_string()))?;
        if let Some(expected) = expected {
            semantics
                .check_stated_class(expected, &end, name)
                .map_err(|error| refuse(file, &error.to_string()))?;
        }
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
        // A stop condition or observations refused on this side's run name the side and its
        // case, which the run's own refusal cannot.
        let run =
            runs.get(semantics, conditions, case, timings)
                .map_err(|failure| match failure {
                    Failure::Exec(
                        error @ (ExecError::StopWhen(_) | ExecError::StopCondition { .. }),
                    ) => Failure::Exec(ExecError::StopWhen(format!(
                        "the {name} side, the case `{}`: {error}",
                        case.id()
                    ))),
                    Failure::Exec(
                        error @ (ExecError::Observe(_) | ExecError::Observation { .. }),
                    ) => Failure::Exec(ExecError::Observe(format!(
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
        CompareSides::Ends { .. } => compare_sides(
            semantics, observer, conditions, request, read, runs, timings,
        )
        .map(Verdict::Sides),
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

/// Refuse sides that `read` and `request` cannot compare, before anything is run: sides that state
/// nothing in common, observations of two declarations, and compared cells or views where no
/// ends are compared.
fn check_sides(request: &CompareRequest, read: &ReadSides) -> Result<(), Failure> {
    let ReadSides { first, second } = read;
    let ends = first.states_ends() && second.states_ends();
    let observations = first.states_observations() && second.states_observations();
    let states = |document: &SideDocument| match document {
        SideDocument::End { .. } => "states an end and no observations",
        SideDocument::Observations { .. } => "states observations and no end",
        SideDocument::Case(_) if document.states_observations() => "states an end and observations",
        SideDocument::Case(_) => {
            "states an end and no observations (its case declares no `observe`)"
        }
    };
    if !ends && !observations {
        return Err(Failure::Usage(format!(
            "the left side, {}, {}, and the right side, {}, {}: the two sides state nothing both can be compared on",
            first.kind(),
            states(first),
            second.kind(),
            states(second)
        )));
    }
    if !ends && (request.compare.is_some() || !request.views.is_empty()) {
        let side = if first.states_ends() { second } else { first };
        return Err(Failure::Usage(format!(
            "--compare and --view apply to the ends a comparison compares, and the {} side, {}, states no end",
            if first.states_ends() { "right" } else { "left" },
            side.kind()
        )));
    }
    if observations {
        let refuse = |reason: String| {
            Failure::Exec(ExecError::Observe(format!(
                "the comparison: {reason}; observations are compared under one declaration"
            )))
        };
        if let (SideDocument::Case(left), SideDocument::Case(right)) = (first, second)
            && first.declared() != second.declared()
        {
            return Err(refuse(format!(
                "the cases `{}` and `{}` declare different observations (`observe`)",
                left.id(),
                right.id()
            )));
        }
        let (left, right) = (first.channels(), second.channels());
        if left != right {
            let listed = |channels: Option<Vec<(&str, ChannelKind)>>| {
                let channels = channels.unwrap_or_default();
                if channels.is_empty() {
                    return "none".to_owned();
                }
                channels
                    .iter()
                    .map(|(name, kind)| {
                        format!(
                            "`{name}` ({})",
                            match kind {
                                ChannelKind::Point => "point",
                                ChannelKind::Log => "log",
                            }
                        )
                    })
                    .collect::<Vec<_>>()
                    .join(", ")
            };
            return Err(refuse(format!(
                "the left side's channels are {} and the right side's are {}",
                listed(left),
                listed(right)
            )));
        }
    }
    Ok(())
}

/// Compare two sides on what both state ([module documentation](self)): every end document read
/// and checked first, so that a partial one is refused before a case is run; then each case side
/// run; then the observations compared, where both sides state them; then, unless they differ,
/// the views evaluated and the sets of ends compared, where both sides state ends, a run side
/// followed again where the verdict rests on its completeness.
fn compare_sides(
    semantics: &mut Semantics,
    observer: Option<&mut Semantics>,
    conditions: &mut Conditions<'_>,
    request: &CompareRequest,
    read: ReadSides,
    runs: &CaseRuns,
    timings: &mut Timings,
) -> Result<SidesVerdict, Failure> {
    check_sides(request, &read)?;
    let compares_ends = read.first.states_ends() && read.second.states_ends();
    let mut comparison = Comparison {
        compare: request.compare.clone(),
        views: CellViews::default(),
    };
    if compares_ends {
        if !request.views.is_empty() {
            let resolver = observer.as_deref().unwrap_or(&*semantics);
            comparison.views = semantics
                .cell_views(resolver, &request.views)
                .map_err(|error| refuse_comparison(&error))?;
        }
        semantics
            .check_comparison(&comparison)
            .map_err(|error| refuse_comparison(&error))?;
    }
    let mut verdict = SidesVerdict {
        ends: None,
        observations: None,
        views: request.views.clone(),
        observer: request.observer.clone(),
    };
    let ReadSides { first, second } = read;
    let read_end = |name, document: &SideDocument| match document {
        SideDocument::End {
            file,
            document,
            base,
        } => Produced::end(
            semantics,
            name,
            (file, document, base.clone()),
            &comparison,
            None,
        )
        .map(Some),
        SideDocument::Case(_) | SideDocument::Observations { .. } => Ok(None),
    };
    let left = read_end("left", &first)?;
    let right = read_end("right", &second)?;
    let mut produce = |name, end: Option<Produced>, document: SideDocument| match (end, document) {
        (Some(end), _) => Ok(end),
        (None, SideDocument::Case(case)) => {
            Produced::run(runs, semantics, conditions, name, &case, timings)
        }
        (None, SideDocument::Observations { record, .. }) => Ok(Produced {
            name,
            source: Source::Record(record),
        }),
        (None, SideDocument::End { .. }) => unreachable!("an end document is read before"),
    };
    let mut left = produce("left", left, first)?;
    let mut right = produce("right", right, second)?;
    verdict.observations = observations_part(&left, &right);
    if !compares_ends || matches!(verdict.observations, Some(ObservationsPart::Differs(_))) {
        return Ok(verdict);
    }
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
                verdict.ends = Some(Compared::Inconclusive(error.to_string()));
                return Ok(verdict);
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
            verdict.ends = Some(compared);
            return Ok(verdict);
        }
    }
}

/// The observations part of a comparison of `left` and `right` ([module documentation](self)):
/// `None` where neither side states observations.
fn observations_part(left: &Produced, right: &Produced) -> Option<ObservationsPart> {
    let unstated = |side: &Produced| {
        format!(
            "the {} side, {}, states no observations",
            side.name,
            match side.source {
                Source::End(_) => "an end document",
                Source::Record(_) | Source::Run { .. } => "a case that declares none (`observe`)",
            }
        )
    };
    let (left_record, right_record) = match (left.record(), right.record()) {
        (None, None) => return None,
        (Some(_), None) => return Some(ObservationsPart::Unstated(unstated(right))),
        (None, Some(_)) => return Some(ObservationsPart::Unstated(unstated(left))),
        (Some(left_record), Some(right_record)) => (left_record, right_record),
    };
    let inconclusive = |reason: String| ObservationsPart::Agree {
        channels: Vec::new(),
        inconclusive: Some(reason),
    };
    let (left_record, right_record) = match (left_record, right_record) {
        (Err(reason), _) => {
            return Some(inconclusive(format!(
                "the left side has no record of its observations: {reason}"
            )));
        }
        (_, Err(reason)) => {
            return Some(inconclusive(format!(
                "the right side has no record of its observations: {reason}"
            )));
        }
        (Ok(left_record), Ok(right_record)) => (left_record, right_record),
    };
    let chosen = |side: &Produced| {
        side.chosen()
            .map(|reason| format!("the {} side's run {reason}", side.name))
    };
    Some(match compare_records(left_record, right_record) {
        RecordComparison::Differs(difference) => match (chosen(left), chosen(right)) {
            // A difference from a side whose path is the definition's only one holds.
            (Some(left_chosen), Some(right_chosen)) => inconclusive(format!(
                "the observations differ at `{}` element {}, but {left_chosen}, and {right_chosen}, so the difference may be one implementation's choice",
                difference.channel, difference.index
            )),
            _ => ObservationsPart::Differs(difference),
        },
        RecordComparison::Agree(channels) => {
            let undecided = channels.iter().find_map(|agreement| {
                let (side, index, reason) = agreement.undecided()?;
                let channel = &agreement.channel;
                Some(match side {
                    None => format!("the observation `{channel}` element {index} is not compared: {reason}"),
                    Some(side) if index < agreement.through => format!(
                        "the observation `{channel}` element {index} is unknown on the {} side: {reason}",
                        side.as_str()
                    ),
                    Some(side) => format!(
                        "the observation `{channel}` is open on the {} side at element {index}, which another run may decide: {reason}",
                        side.as_str()
                    ),
                })
            });
            let inconclusive = undecided.or_else(|| {
                chosen(left).or_else(|| chosen(right)).map(|reason| {
                    format!("the observations agree as far as both are known, but {reason}")
                })
            });
            ObservationsPart::Agree {
                channels,
                inconclusive,
            }
        }
    })
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
            Some(&expectation.end),
        )?,
        SideDocument::Case(actual) => {
            Produced::run(runs, semantics, conditions, "actual", actual, timings)?
        }
        SideDocument::Observations { .. } => {
            unreachable!("`read` refuses an observation document as the actual side")
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
            Outcome::Verdict(Verdict::Sides(verdict)) => match verdict.exit_code() {
                exit_status::YES => &mut self.equal,
                exit_status::NO => &mut self.differs,
                _ => &mut self.inconclusive,
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
    prepared: &RunDefinition,
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
    let pairs = read_pairs(file, request)
        .map_err(|failure| failure.into_command_error(prepared.source_map()))?;
    let definition = prepared.definition();
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
    result.map_err(|failure| failure.into_command_error(prepared.source_map()))
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
            let conditions = run_observers(&read)
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
                self.conditions.observations.clear();
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
    use super::{CaseRun, ObservationsPart, Produced, SideFile, Source, observations_part};
    use krs_exec::{Channel, ChannelKind, Closure, Element, Ends, Observations};
    use serde_json::json;
    use std::path::PathBuf;
    use std::sync::{Arc, OnceLock};

    /// A case run's side whose record holds one element `value`, its run having read a value
    /// the definition leaves open where `chosen` says so.
    fn side(name: &'static str, value: i64, chosen: bool) -> Produced {
        let record = Observations {
            channels: vec![Channel {
                name: "c".to_owned(),
                kind: ChannelKind::Point,
                elements: vec![Element {
                    depth: 0,
                    rule: None,
                    side: None,
                    digest: None,
                    value: Some(json!(value)),
                    undecided: None,
                }],
                closed: Some(Closure::End),
                open: None,
            }],
            conversions: 0,
        };
        Produced {
            name,
            source: Source::Run {
                run: Arc::new(CaseRun {
                    ends: Ends::none("no end"),
                    observations: Some(Ok(record)),
                    chosen: chosen.then(|| "read values the definition leaves open".to_owned()),
                    passed: None,
                    run: None,
                    followed: OnceLock::new(),
                }),
                followed: false,
            },
        }
    }

    /// A difference holds where one side's path is the definition's only one, and is no answer
    /// where both sides' runs read a value the definition leaves open; an agreement holds only
    /// where neither did.
    #[test]
    fn open_values_bound_what_a_record_shows() {
        let part = |left, right| observations_part(&left, &right).unwrap();
        assert!(matches!(
            part(side("left", 0, false), side("right", 1, true)),
            ObservationsPart::Differs(_)
        ));
        assert!(matches!(
            part(side("left", 0, true), side("right", 1, true)),
            ObservationsPart::Agree {
                inconclusive: Some(_),
                ..
            }
        ));
        assert!(matches!(
            part(side("left", 0, false), side("right", 0, false)),
            ObservationsPart::Agree {
                inconclusive: None,
                ..
            }
        ));
        let ObservationsPart::Agree {
            inconclusive: Some(reason),
            ..
        } = part(side("left", 0, false), side("right", 0, true))
        else {
            panic!("an agreement with a path that read an open value is an answer");
        };
        assert!(
            reason.contains("the right side's run read values"),
            "{reason}"
        );
    }

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
