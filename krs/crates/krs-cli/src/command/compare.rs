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

use std::collections::BTreeMap;
use std::fmt::{self, Write as _};
use std::path::{Path, PathBuf};

use krs_exec::{
    BackendOptions, CaseDocument, CellViews, Compared, Comparison, Difference, EndError, Ends,
    ExecError, RunOptions, RunReport, Semantics, Side, SourceText, State, StopCriterion,
    json_document, toml_text_document,
};
use krs_ir::measure::Measurement;
use serde_json::{Value as Json, json};

use super::exec::{
    self, CaseFiles, Checked, Failure, Inputs, ObserverDefinition, SelectedCase, StageReuse,
    WORKER_STACK,
};
use super::{CommandError, CommandOutcome, PreparedDefinition};
use crate::DiagnosticSources;

/// The schema `krs compare --output json` names.
pub const COMPARE_SCHEMA: &str = "krs-compare/1";

/// How `krs compare` prints its verdict.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum CompareOutput {
    /// The verdict's lines.
    #[default]
    Human,
    /// One [`COMPARE_SCHEMA`] JSON document.
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
pub(super) fn execute(
    prepared: &PreparedDefinition,
    request: &CompareRequest,
    sources: &DiagnosticSources,
    reuse: StageReuse<'_>,
    read: ReadSides,
    observer: Option<ObserverDefinition>,
    measurement: &mut Measurement,
) -> Result<CommandOutcome, CommandError> {
    let sources = sources.clone();
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
                let mut semantics = Semantics::from_stage_with_solver(
                    definition,
                    stage,
                    Some(provider),
                    request.solver,
                    timings,
                )
                .map_err(Failure::Exec)?;
                let mut observer = observer
                    .map(|observer| {
                        exec::load_observer(&observer, reuse.restore, request.solver, timings)
                    })
                    .transpose()
                    .map_err(Failure::Exec)?;
                compare(&mut semantics, observer.as_mut(), request, read)
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

/// The verdict of two sets of ends, with the views it applied.
struct EndsVerdict {
    verdict: Compared,
    views: BTreeMap<String, String>,
    observer: Option<String>,
}

impl EndsVerdict {
    /// 0 equal, 1 differs, 3 inconclusive (no end to compare, which calls for another action
    /// than ends that differ).
    const fn exit_code(&self) -> i32 {
        match self.verdict {
            Compared::Equal => 0,
            Compared::Differs(_) => 1,
            Compared::Inconclusive(_) => 3,
        }
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

    fn write(&self, output: &mut String) {
        match &self.verdict {
            Compared::Equal => output.push_str("krs compare: equal\n"),
            Compared::Inconclusive(reason) => {
                let _ = writeln!(output, "krs compare: inconclusive: {reason}");
            }
            Compared::Differs(difference) => {
                exec::write_difference(output, "krs compare: differs", difference);
                write_pair_note(output, difference);
            }
        }
        let observer = self.observer.as_deref().filter(|_| !self.views.is_empty());
        exec::write_views(output, &self.views, observer);
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

/// A side's ends, and the run they are of until its completeness is known.
struct Produced {
    name: &'static str,
    ends: Ends,
    /// The run of a case side whose end may not be its case's only one, until
    /// [`Self::settle`] follows it again.
    unsettled: Option<RunOf>,
}

/// A case's run: the state it ran from, its options and its report.
struct RunOf {
    state: State,
    options: RunOptions,
    report: RunReport,
}

impl Produced {
    fn side(&self) -> Side<'_> {
        Side {
            name: self.name,
            ends: &self.ends,
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
            ends: Ends::one(end),
            unsettled: None,
        })
    }

    /// The end of `case`'s run, as `krs run --case` runs it: its inputs bound, its `run` table's
    /// depth and stops.
    fn run(
        semantics: &mut Semantics,
        name: &'static str,
        case: &SelectedCase,
    ) -> Result<Self, Failure> {
        let stop = case.stop(&StopCriterion::None)?;
        let depth = case.depth(None)?;
        let state = exec::configure(semantics, Inputs::of_case(case), false)?;
        let options = RunOptions {
            depth,
            stop,
            ..RunOptions::default()
        };
        let report = match semantics.run(&state, options.clone()) {
            Ok(report) => report,
            // A run that cannot decide which of several states it reaches has no one end.
            Err(error @ ExecError::Undecided { .. }) => {
                return Ok(Self {
                    name,
                    ends: Ends::none(format!("the run has no one end: {error}")),
                    unsettled: None,
                });
            }
            Err(error) => return Err(error.into()),
        };
        let ends = semantics
            .end_of(&report)
            .map_err(|error| exec::end_failure(&error))?;
        // A run with no end has nothing a completeness could change.
        let unsettled = (!ends.ends.is_empty()).then_some(RunOf {
            state,
            options,
            report,
        });
        Ok(Self {
            name,
            ends,
            unsettled,
        })
    }

    /// Follow the side's run again for whether its end is its case's only one; true when it is
    /// not, which makes the side's set incomplete. Each run is followed again once.
    fn settle(&mut self, semantics: &mut Semantics) -> Result<bool, Failure> {
        let Some(run) = self.unsettled.take() else {
            return Ok(false);
        };
        match semantics.other_ends(&run.state, &run.options, &run.report)? {
            Some(reason) => {
                self.ends.incomplete = Some(reason);
                Ok(true)
            }
            None => Ok(false),
        }
    }
}

/// Compare the sides `read` of `request`, the views evaluated in `observer` (the compared
/// definition when `None`), and print the verdict.
fn compare(
    semantics: &mut Semantics,
    observer: Option<&mut Semantics>,
    request: &CompareRequest,
    read: ReadSides,
) -> Result<CommandOutcome, Failure> {
    let (text, document, exit_code) = match &request.sides {
        CompareSides::Ends { .. } => {
            let verdict = compare_ends(semantics, observer, request, read)?;
            let mut text = String::new();
            verdict.write(&mut text);
            (text, verdict.document(), verdict.exit_code())
        }
        CompareSides::Expectation { .. } => {
            let checked = check_expectation(semantics, observer, request, read)?;
            let mut text = String::new();
            checked.write(&mut text, "krs compare");
            let mut document = json!({"schema": COMPARE_SCHEMA});
            if let (Json::Object(target), Json::Object(members)) =
                (&mut document, checked.document())
            {
                target.extend(members);
            }
            (text, document, checked.exit_code())
        }
    };
    let stdout = match request.output {
        CompareOutput::Human => text,
        CompareOutput::Json => format!("{document}\n"),
    };
    Ok(exec::outcome(stdout, String::new(), exit_code))
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
    request: &CompareRequest,
    read: ReadSides,
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
        (None, SideDocument::Case(case)) => Produced::run(semantics, name, case),
        (None, SideDocument::End { .. }) => unreachable!("an end document is read before"),
    };
    let mut left = produce("left", left, &first)?;
    let mut right = produce("right", right, &second)?;
    if !comparison.views.is_empty() {
        let observer = match observer {
            Some(observer) => observer,
            None => &mut *semantics,
        };
        match comparison.views.evaluate_within(
            observer,
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
            changed |= left.settle(semantics)?;
        }
        if on_right {
            changed |= right.settle(semantics)?;
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
    request: &CompareRequest,
    read: ReadSides,
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
        SideDocument::Case(actual) => Produced::run(semantics, "actual", actual)?,
    };
    let budget = request.view_budget;
    let checked = exec::check(
        semantics,
        observer.as_deref_mut(),
        &case,
        &mut expectation,
        &actual.ends,
        budget,
    )?;
    // One end that differs is unmet; one that agrees meets the expectation only where it is the
    // actual side's only end.
    if matches!(checked.verdict, Compared::Equal) && actual.settle(semantics)? {
        return exec::check(
            semantics,
            observer,
            &case,
            &mut expectation,
            &actual.ends,
            budget,
        );
    }
    Ok(checked)
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
