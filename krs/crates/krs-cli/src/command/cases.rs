//! `krs cases`: a batch of named cases, each run and checked against its expectation, with one
//! verdict record per case in document order and a summary.
//!
//! `krs run --case` runs one case and pays, for that case, a process, the definition's load into
//! the backend and its compiled stage's restore; a corpus of many cases pays them for every case.
//! `krs cases` loads the definition once per worker thread and runs every case it is given on
//! it, so the per-case cost is the case's own run and check, and the memory a batch takes grows
//! with the workers: each holds its own copy of the definition and of each observer it uses.
//!
//! A case's run does not depend on the cases a worker ran before it (each starts from its own
//! configured state), and a view's budget counts polls of the evaluation's own work, not time, so
//! the records are the same whichever worker runs a case, and `--jobs N` prints what `--jobs 1`
//! prints, but for a verdict a resource stop decides, which may depend on what runs beside the
//! case or before it on its worker: the simplifier's stack budget, which the process's threads
//! share; the solver's limits, under which a query a worker's solver answered before is answered
//! from its record of decided answers, and one it did not may be undecided; and a view's budget
//! that only such reuse of decided answers lets the evaluation meet.
//!
//! The documents are read one at a time, in the order given, each with its includes, and their
//! cases are run in parallel and printed in document order as each one's predecessors are
//! printed: a slow case holds back the printing of the cases after it, never their runs, up to a
//! bounded number of cases ahead of it.
//!
//! A case's views are evaluated in its observer: the definition the case runs on, or the
//! definition its expectation names (`observer`), which is prepared once, the first time a case
//! names it, and loaded once per worker that runs such a case.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::io::Write as _;
use std::num::NonZeroUsize;
use std::panic::AssertUnwindSafe;
use std::path::PathBuf;
use std::sync::{Arc, Mutex, mpsc};

use krs_exec::{
    BackendOptions, Case, CaseDocument, Compared, CompiledStage, ExecError, Halt, RunOptions,
    Semantics, SourceText, StopCriterion,
};
use krs_ir::measure::{Measurement, Timings};
use krs_ir_levels::DefinitionIr;
use serde_json::json;

use super::definition_cache::RunDefinition;
use super::exec::{
    self, Checked, ConditionSource, Failure, Inputs, ObserverDefinition, Run, SelectedCase,
    StageReuse, WORKER_STACK,
};
use super::{CommandError, CommandOutcome, exit_status};
use crate::DiagnosticSources;

/// The schema every record of `krs cases --output json` names. Version 2 records a case with
/// no expectation whose run has no one path as `ran` with a `reason` and no `halt` (version 1
/// refused it), and its summary's `status` is the exit status of the four actions
/// ([`exit_status`]), under which a refused case is 2, no longer 1. Version 3 records the halt
/// `stop-undecided` of a run whose stop condition was left undecided, a halt word a version 2
/// reader does not know. Version 4 records the stops of a run with stop rules as `krs run
/// --output json` reports them (`stop`, `stops`, `arrivals`, `undecided`, `passed_stops`), so a
/// version 3 reader would read a record without them as a run that passed no stop.
pub const CASES_SCHEMA: &str = "krs-cases/4";

/// The schema every record of `krs cases --output json` names for a definition that declares
/// ends ([`krs_exec::declares_ends`], [`cases_schema`]).
///
/// A case of such a definition whose run ends where no rule applies records the declared class of
/// its end (`end`), or the declared end left undecided (`end_undecided`, with the halt
/// `end-undecided`), as `krs run --output json` reports them, and a case that states no
/// expectation and ends in no declared end (a gap, or `undefined`) is a finding, which the
/// summary counts as `undeclared`.
/// A version 4 reader knows `ran` with the halt `stuck` as a case that ran to an end, and would
/// take a gap for one, so every record of a declaring definition is a format of its own version,
/// as its run documents are (`krs-exec/8`).
/// A definition that declares no end keeps [`CASES_SCHEMA`], and its records their bytes.
pub const CASES_SCHEMA_DECLARED_ENDS: &str = "krs-cases/5";

/// The schema of the records of a definition that declares ends (`declares_ends`) or none:
/// [`CASES_SCHEMA_DECLARED_ENDS`] or [`CASES_SCHEMA`].
#[must_use]
pub const fn cases_schema(declares_ends: bool) -> &'static str {
    if declares_ends {
        CASES_SCHEMA_DECLARED_ENDS
    } else {
        CASES_SCHEMA
    }
}

/// How `krs cases` prints its records.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum CasesOutput {
    /// A line per verdict, with an unmet expectation's difference below it.
    #[default]
    Human,
    /// One [`CASES_SCHEMA`] JSON document per line ([`CASES_SCHEMA_DECLARED_ENDS`] for a
    /// definition that declares ends).
    Json,
}

/// `krs cases` inputs.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CasesRequest {
    /// The case documents, in the order their cases are run and reported.
    pub documents: Vec<PathBuf>,
    /// `--jobs`: the worker threads, each with the definition loaded once; the available
    /// parallelism by default.
    pub jobs: Option<NonZeroUsize>,
    /// `--name`: only the named cases whose name the pattern matches (`*` any text, `?` any
    /// character).
    pub name: Option<String>,
    /// `--output`.
    pub output: CasesOutput,
    /// `--smt-resource-limit`, `--smt-clock-ms` and `--smt-retries`.
    pub solver: BackendOptions,
    /// `--view-budget`: the polls each evaluation of a view may take.
    pub view_budget: u64,
}

/// Prepares the observer a case names: `None` when it is the definition the cases run on.
pub(super) type PrepareObserver<'a> =
    dyn Fn(&str) -> Result<Option<ObserverDefinition>, String> + Sync + 'a;

/// How many cases may be run ahead of the first one not yet printed, per worker: the bound on
/// the records held back for printing in document order.
const AHEAD_PER_WORKER: usize = 4;

/// Run the cases of `request` on the prepared definition, its stage restored or compiled once.
pub(super) fn execute(
    prepared: &RunDefinition,
    request: &CasesRequest,
    sources: &DiagnosticSources,
    reuse: StageReuse<'_>,
    observers: &PrepareObserver<'_>,
    measurement: &mut Measurement,
) -> Result<CommandOutcome, CommandError> {
    let definition = prepared.definition();
    let timings = &mut measurement.timings;
    let mut reused = false;
    let reused_flag = &mut reused;
    let result = std::thread::scope(|scope| {
        std::thread::Builder::new()
            .name("krs-cases".into())
            .stack_size(WORKER_STACK)
            .spawn_scoped(scope, move || {
                let (stage, restored) =
                    exec::compiled_stage(definition, reuse, timings).map_err(Failure::Exec)?;
                *reused_flag = restored;
                let batch = Batch {
                    definition,
                    stage: &stage,
                    sources,
                    request,
                    restore: reuse.restore,
                };
                batch.run(observers, timings)
            })
            .map_err(|error| {
                CommandError::InvalidRequest(format!("could not start the cases worker: {error}"))
            })?
            .join()
            .map_err(|_| CommandError::InvalidRequest("the cases worker panicked".into()))
    })?;
    measurement.counters.set("stage.reused", u64::from(reused));
    result.map_err(|failure| failure.into_command_error(prepared.source_map()))
}

/// An observer definition, prepared and compiled once, which each worker loads on first use.
struct Observer {
    definition: DefinitionIr,
    stage: CompiledStage,
}

/// One case to run: its place in the output, its id, the case, and its observer when it names
/// one other than the definition it runs on.
struct Job {
    index: usize,
    id: String,
    case: SelectedCase,
    observer: Option<Arc<Observer>>,
    /// The definition its run's stop condition is evaluated in: `None` without a condition.
    condition: Option<ConditionSource<Arc<Observer>>>,
    /// The definition its run's observations are evaluated in: `None` without observations or
    /// with none that declares a function.
    observations: Option<ConditionSource<Arc<Observer>>>,
}

/// A case's verdict.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Verdict {
    Met,
    Unmet,
    Inconclusive,
    /// The case, its document or its observer is no case the definition can run, or a view has
    /// no value at an end.
    Refused,
    /// The case states no expectation, and ran: to a state, or, when it reaches several under
    /// conditions it cannot decide, to no one end.
    Ran,
}

impl Verdict {
    const fn as_str(self) -> &'static str {
        match self {
            Self::Met => "met",
            Self::Unmet => "unmet",
            Self::Inconclusive => "inconclusive",
            Self::Refused => "refused",
            Self::Ran => "ran",
        }
    }
}

/// One case's record.
struct Record {
    id: String,
    verdict: Verdict,
    /// The run's halt and steps, when it ran to a state.
    run: Option<(Halt, u64)>,
    /// The expectation's verdict, when the case states one and its run was checked.
    checked: Option<Checked>,
    /// Why the case was refused, or why a case that ran has no end.
    reason: Option<String>,
    /// The views and the observer the expectation names, as it writes them, for a record with no
    /// checked verdict to name them.
    written: (BTreeMap<String, String>, Option<String>),
    /// The run's stops, when it has stop rules: the status line's clause `krs run` prints
    /// ([`exec::stops_passed`]) and the members `krs run --output json` reports.
    stops: Option<(String, serde_json::Map<String, serde_json::Value>)>,
    /// In a definition that declares ends, the declared class of the run's end where it ended
    /// where no rule applies ([`krs_exec::RunReport::end`]).
    end: Option<krs_exec::RunEnd>,
    /// In a definition that declares ends, the declared end left undecided where the run halted
    /// `end-undecided` ([`krs_exec::RunReport::end_undecided`]).
    end_undecided: Option<krs_exec::EndUndecided>,
    /// Whether the run ended in no declared end of a definition that declares ends: at a state
    /// where no rule applies and no declared end holds, or `undefined`, at no state
    /// ([`exec::DeclaredOutcome::Undeclared`]).
    undeclared: bool,
}

impl Record {
    /// The record of `verdict`, with nothing else known.
    const fn of(id: String, verdict: Verdict) -> Self {
        Self {
            id,
            verdict,
            run: None,
            checked: None,
            reason: None,
            written: (BTreeMap::new(), None),
            stops: None,
            end: None,
            end_undecided: None,
            undeclared: false,
        }
    }

    fn refused(id: String, reason: String) -> Self {
        Self {
            reason: Some(reason),
            ..Self::of(id, Verdict::Refused)
        }
    }

    /// The record, naming the views and the observer `case`'s expectation writes.
    fn naming(mut self, case: &Case) -> Self {
        self.written = exec::written_views(case);
        self
    }

    /// Whether the record counts as inconclusive in the status: an inconclusive verdict, or a
    /// case without an expectation whose run has no end (an inconclusive halt, or no one path).
    fn inconclusive(&self) -> bool {
        match self.verdict {
            Verdict::Inconclusive => true,
            Verdict::Ran => self.run.is_none_or(|(halt, _)| !halt.is_complete()),
            Verdict::Met | Verdict::Unmet | Verdict::Refused => false,
        }
    }

    /// Whether the record is a case that states no expectation and ran to no declared end of a
    /// definition that declares ends, which counts as a finding in the status.
    const fn undeclared(&self) -> bool {
        matches!(self.verdict, Verdict::Ran) && self.undeclared
    }

    /// The record's exit status ([`exit_status`]): yes for a met case or one that ran to an end,
    /// a finding for an unmet one, no answer for an inconclusive one or one that ran to no end,
    /// and the question not asked for a refused one.
    ///
    /// In a definition that declares ends, a case that states no expectation is answered as
    /// `krs run` answers its run: an end of either declared class is an end, an end in no
    /// declared class (a state where no rule applies and no declared end holds, or `undefined`)
    /// is a finding, since the definition does not account for it, and an end left undecided is
    /// no answer. An expectation's verdict replaces all of these, as it does for `krs run`.
    fn status(&self) -> i32 {
        match self.verdict {
            Verdict::Ran if self.undeclared() => exit_status::NO,
            Verdict::Unmet => exit_status::NO,
            Verdict::Refused => exit_status::UNASKED,
            Verdict::Inconclusive | Verdict::Ran if self.inconclusive() => exit_status::UNANSWERED,
            Verdict::Met | Verdict::Inconclusive | Verdict::Ran => exit_status::YES,
        }
    }

    fn json(&self, schema: &str) -> serde_json::Value {
        let mut document = json!({
            "schema": schema,
            "case": self.id,
            "verdict": self.verdict.as_str(),
        });
        if let Some((halt, steps)) = self.run {
            document["halt"] = json!(halt.as_str());
            document["steps"] = json!(steps);
        }
        if let Some(end) = &self.end {
            document["end"] = json!(end);
        }
        if let Some(undecided) = &self.end_undecided {
            document["end_undecided"] = json!(undecided);
        }
        if let Some(reason) = &self.reason {
            document["reason"] = json!(reason);
        }
        if let Some((_, members)) = &self.stops {
            for (key, value) in members {
                document[key] = value.clone();
            }
        }
        if let Some(checked) = &self.checked {
            checked.extend(&mut document);
        } else {
            let (views, observer) = &self.written;
            if !views.is_empty() {
                document["views"] = json!(views);
            }
            if let Some(observer) = observer {
                document["observer"] = json!(observer);
            }
        }
        document
    }

    /// For a case refused for an expectation of a `depth-bound` end, its reason without the
    /// refusal's guidance ([`krs_exec::DEPTH_BOUND_GUIDANCE`]).
    fn depth_bound_refusal(&self) -> Option<&str> {
        if self.verdict != Verdict::Refused {
            return None;
        }
        self.reason
            .as_deref()?
            .strip_suffix(krs_exec::DEPTH_BOUND_GUIDANCE)
            .filter(|refusal| refusal.ends_with(krs_exec::DEPTH_BOUND_REFUSAL))
    }

    fn human(&self) -> String {
        let mut text = String::new();
        match (&self.checked, self.run, &self.reason) {
            (Some(checked), _, _) => checked.write(&mut text, &self.id),
            (None, None, Some(reason)) if self.verdict == Verdict::Ran => {
                let _ = writeln!(text, "{}: ran: {reason}", self.id);
            }
            (None, _, Some(reason)) => {
                let _ = writeln!(text, "{}: refused: {reason}", self.id);
            }
            (None, Some((halt, steps)), None) => {
                // The words of `krs run`'s status line, the declared end's included.
                let (word, class) =
                    exec::declared_end_clause(halt, self.end.as_ref(), self.end_undecided.as_ref());
                let _ = writeln!(
                    text,
                    "{}: ran, {word} after {steps} step{}{}{class}",
                    self.id,
                    if steps == 1 { "" } else { "s" },
                    self.stops
                        .as_ref()
                        .map_or("", |(clause, _)| clause.as_str()),
                );
            }
            (None, None, None) => {
                let _ = writeln!(text, "{}: {}", self.id, self.verdict.as_str());
            }
        }
        text
    }
}

/// The verdicts counted, for the summary and the exit status.
#[derive(Default)]
struct Tally {
    met: usize,
    unmet: usize,
    inconclusive: usize,
    refused: usize,
    ran: usize,
    /// The `ran` cases that ended in no declared end ([`Record::undeclared`]).
    undeclared: usize,
    /// The [`exit_status::join`] of the records' statuses ([`Record::status`]).
    status: i32,
    /// Whether the definition declares ends, which adds `undeclared` to the summary.
    declares_ends: bool,
}

impl Tally {
    fn count(&mut self, record: &Record) {
        match record.verdict {
            Verdict::Met => self.met += 1,
            Verdict::Unmet => self.unmet += 1,
            Verdict::Inconclusive => self.inconclusive += 1,
            Verdict::Refused => self.refused += 1,
            Verdict::Ran => self.ran += 1,
        }
        if record.undeclared() {
            self.undeclared += 1;
        }
        self.status = exit_status::join(self.status, record.status());
    }

    const fn cases(&self) -> usize {
        self.met + self.unmet + self.inconclusive + self.refused + self.ran
    }

    /// The batch's exit status: the [`exit_status::join`] of its records', so a refused case
    /// gives the question not asked, since the batch's answer is then incomplete.
    const fn status(&self) -> i32 {
        self.status
    }

    fn json(&self) -> serde_json::Value {
        let mut document = json!({
            "schema": cases_schema(self.declares_ends),
            "summary": {
                "cases": self.cases(),
                "met": self.met,
                "unmet": self.unmet,
                "inconclusive": self.inconclusive,
                "refused": self.refused,
                "ran": self.ran,
            },
            "status": self.status(),
        });
        if self.declares_ends {
            document["summary"]["undeclared"] = json!(self.undeclared);
        }
        document
    }

    fn human(&self) -> String {
        let cases = self.cases();
        format!(
            "krs cases: {cases} case{}: {} met, {} unmet, {} inconclusive, {} refused, {} ran{}\n",
            if cases == 1 { "" } else { "s" },
            self.met,
            self.unmet,
            self.inconclusive,
            self.refused,
            self.ran,
            if self.declares_ends {
                format!(" ({} at no declared end)", self.undeclared)
            } else {
                String::new()
            }
        )
    }
}

/// Prints records in document order as they arrive in any.
struct Printer {
    next: usize,
    pending: BTreeMap<usize, Record>,
    output: CasesOutput,
    tally: Tally,
    /// Under human output, the cases refused for an expectation of a `depth-bound` end, whose
    /// records state the refusal alone and whose guidance [`Self::guidance`] states once.
    depth_bound: Vec<String>,
}

impl Printer {
    fn put(&mut self, index: usize, record: Record) -> Result<(), Failure> {
        self.pending.insert(index, record);
        while let Some(record) = self.pending.remove(&self.next) {
            self.tally.count(&record);
            let text = match self.output {
                CasesOutput::Json => {
                    format!("{}\n", record.json(cases_schema(self.tally.declares_ends)))
                }
                CasesOutput::Human => match record.depth_bound_refusal() {
                    Some(refusal) => {
                        self.depth_bound.push(record.id.clone());
                        format!(
                            "{}: refused: {refusal} (why, and what to expect instead: below)\n",
                            record.id
                        )
                    }
                    None => record.human(),
                },
            };
            write_stdout(&text)?;
            self.next += 1;
        }
        Ok(())
    }

    /// The guidance of the `depth-bound` refusal, once for every case refused for it, before the
    /// count: the guidance is the same text for every case, so a batch of cases written the same
    /// way, as a corpus migrated from depth bounds is, states it once rather than once a case. A
    /// JSON record keeps its whole reason, since each is read alone.
    fn guidance(&self) -> String {
        if self.depth_bound.is_empty() {
            return String::new();
        }
        format!(
            "krs cases: {}: {}{}\n",
            self.depth_bound.join(", "),
            krs_exec::DEPTH_BOUND_REFUSAL,
            krs_exec::DEPTH_BOUND_GUIDANCE
        )
    }
}

/// Write `text` to standard output now, so that each record reaches a reader as it is decided.
pub(super) fn write_stdout(text: &str) -> Result<(), Failure> {
    let mut stdout = std::io::stdout().lock();
    stdout
        .write_all(text.as_bytes())
        .and_then(|()| stdout.flush())
        .map_err(|error| Failure::Read(format!("could not write standard output: {error}")))
}

/// The batch: the definition and its compiled stage, which every worker loads once.
struct Batch<'a> {
    definition: &'a DefinitionIr,
    stage: &'a CompiledStage,
    sources: &'a DiagnosticSources,
    request: &'a CasesRequest,
    restore: bool,
}

impl Batch<'_> {
    fn run(
        &self,
        observers: &PrepareObserver<'_>,
        timings: &mut Timings,
    ) -> Result<CommandOutcome, Failure> {
        let jobs = self
            .request
            .jobs
            .or_else(|| std::thread::available_parallelism().ok())
            .map_or(1, NonZeroUsize::get);
        let ahead = jobs.saturating_mul(AHEAD_PER_WORKER);
        let (job_sender, job_receiver) = mpsc::channel::<Job>();
        let job_receiver = Mutex::new(job_receiver);
        let (record_sender, record_receiver) = mpsc::channel::<(usize, Record)>();
        let mut printer = Printer {
            next: 0,
            pending: BTreeMap::new(),
            output: self.request.output,
            tally: Tally {
                declares_ends: krs_exec::declares_ends(self.definition),
                ..Tally::default()
            },
            depth_bound: Vec::new(),
        };
        std::thread::scope(|scope| {
            for worker in 0..jobs {
                let records = record_sender.clone();
                let job_receiver = &job_receiver;
                std::thread::Builder::new()
                    .name(format!("krs-cases-{worker}"))
                    .stack_size(WORKER_STACK)
                    .spawn_scoped(scope, move || {
                        let mut state = Worker::new(self);
                        loop {
                            let job = job_receiver
                                .lock()
                                .unwrap_or_else(std::sync::PoisonError::into_inner)
                                .recv();
                            let Ok(job) = job else { break };
                            let index = job.index;
                            if records.send((index, state.record(&job))).is_err() {
                                break;
                            }
                        }
                    })
                    .map_err(|error| {
                        Failure::Read(format!("could not start a cases worker: {error}"))
                    })?;
            }
            drop(record_sender);
            let mut feed = Feed {
                batch: self,
                observers,
                prepared: BTreeMap::new(),
                timings,
                dispatched: 0,
                ahead,
                jobs: job_sender,
                records: &record_receiver,
                printer: &mut printer,
            };
            let read = feed.documents();
            let dispatched = feed.dispatched;
            // Every worker ends once the jobs are taken and the channel closes.
            drop(feed);
            read?;
            while printer.next < dispatched {
                let (index, record) = record_receiver.recv().map_err(|_| {
                    Failure::Read("a cases worker ended before its cases were run".to_owned())
                })?;
                printer.put(index, record)?;
            }
            if dispatched == 0 {
                return Err(Failure::Usage(match &self.request.name {
                    Some(pattern) => {
                        format!("--name `{pattern}` selects no named case of the documents given")
                    }
                    None => "the documents given hold no case".to_owned(),
                }));
            }
            Ok(())
        })?;
        let summary = match self.request.output {
            CasesOutput::Json => format!("{}\n", printer.tally.json()),
            CasesOutput::Human => format!("{}{}", printer.guidance(), printer.tally.human()),
        };
        write_stdout(&summary)?;
        Ok(exec::outcome(
            String::new(),
            String::new(),
            printer.tally.status(),
        ))
    }
}

/// The coordinator's side of the batch: reads the documents, prepares observers, hands out the
/// cases, and prints the records as they come back.
struct Feed<'f, 'b> {
    batch: &'f Batch<'b>,
    observers: &'f PrepareObserver<'f>,
    /// Each observer named so far, prepared and compiled, or why it is not.
    prepared: BTreeMap<String, Result<Option<Arc<Observer>>, String>>,
    timings: &'f mut Timings,
    dispatched: usize,
    ahead: usize,
    jobs: mpsc::Sender<Job>,
    records: &'f mpsc::Receiver<(usize, Record)>,
    printer: &'f mut Printer,
}

impl Feed<'_, '_> {
    fn documents(&mut self) -> Result<(), Failure> {
        for path in &self.batch.request.documents {
            let document = exec::read_case_document(path);
            let shown = path.display().to_string();
            let (document, base) = match document {
                Ok(read) => read,
                Err(failure) => {
                    self.settle(Record::refused(shown, failure.reason()))?;
                    continue;
                }
            };
            let cases = match document {
                CaseDocument::One(case) => vec![(shown.clone(), case)],
                CaseDocument::Named(cases) => cases
                    .into_iter()
                    .map(|case| {
                        let id = format!("{shown}#{}", case.name.as_deref().unwrap_or_default());
                        (id, case)
                    })
                    .collect(),
            };
            for (id, case) in cases {
                if let Some(pattern) = &self.batch.request.name
                    && !case
                        .name
                        .as_deref()
                        .is_some_and(|name| glob_matches(pattern, name))
                {
                    continue;
                }
                let named = exec::named_observer(&case).map(str::to_owned);
                let observer = match named.map(|name| self.observer(&name)) {
                    Some(Err(reason)) => {
                        self.settle(Record::refused(id, reason).naming(&case))?;
                        continue;
                    }
                    Some(Ok(observer)) => observer,
                    None => None,
                };
                let condition = exec::run_condition(&krs_exec::StopCriterion::None, Some(&case))
                    .map(|when| when.observer.clone());
                let observations = case
                    .observe
                    .as_ref()
                    .filter(|spec| spec.declares_function())
                    .map(|spec| spec.observer.clone());
                let condition = self.source(condition.is_some(), condition.flatten().as_deref());
                let observations =
                    self.source(observations.is_some(), observations.flatten().as_deref());
                let (condition, observations) = match (condition, observations) {
                    (Ok(condition), Ok(observations)) => (condition, observations),
                    (Err(reason), _) | (_, Err(reason)) => {
                        self.settle(Record::refused(id, reason).naming(&case))?;
                        continue;
                    }
                };
                let case = SelectedCase {
                    case,
                    path: path.clone(),
                    base: base.clone(),
                };
                self.wait_for_room()?;
                let job = Job {
                    index: self.dispatched,
                    id,
                    case,
                    observer,
                    condition,
                    observations,
                };
                self.jobs.send(job).map_err(|_| {
                    Failure::Read("every cases worker ended before the cases were run".to_owned())
                })?;
                self.dispatched += 1;
            }
        }
        Ok(())
    }

    /// Print `record` at the next place, after the cases handed out before it.
    fn settle(&mut self, record: Record) -> Result<(), Failure> {
        self.wait_for_room()?;
        let index = self.dispatched;
        self.dispatched += 1;
        self.printer.put(index, record)
    }

    /// Wait until fewer than [`Self::ahead`] cases are run ahead of the first one not printed.
    fn wait_for_room(&mut self) -> Result<(), Failure> {
        while self.dispatched - self.printer.next >= self.ahead {
            let (index, record) = self.records.recv().map_err(|_| {
                Failure::Read("every cases worker ended before the cases were run".to_owned())
            })?;
            self.printer.put(index, record)?;
        }
        Ok(())
    }

    /// Where a stop condition or observations are evaluated, when the case has them
    /// (`declared`): in the observer `named`, or in the case's own definition where they name
    /// none or name it; `None` where the case has none.
    fn source(
        &mut self,
        declared: bool,
        named: Option<&str>,
    ) -> Result<Option<ConditionSource<Arc<Observer>>>, String> {
        if !declared {
            return Ok(None);
        }
        Ok(Some(
            match named.map(|name| self.observer(name)).transpose()?.flatten() {
                Some(observer) => ConditionSource::Named(observer),
                None => ConditionSource::Own,
            },
        ))
    }

    /// The observer `name`, prepared and compiled the first time a case names it.
    fn observer(&mut self, name: &str) -> Result<Option<Arc<Observer>>, String> {
        if let Some(prepared) = self.prepared.get(name) {
            return prepared.clone();
        }
        let prepared = (self.observers)(name).and_then(|observer| {
            observer
                .map(|observer| {
                    let reuse = StageReuse {
                        cache: observer.cache.as_ref(),
                        restore: self.batch.restore,
                    };
                    let (stage, _) =
                        exec::compiled_stage(&observer.definition, reuse, self.timings).map_err(
                            |error| format!("the observer `{name}` cannot be compiled: {error}"),
                        )?;
                    Ok(Arc::new(Observer {
                        definition: observer.definition,
                        stage,
                    }))
                })
                .transpose()
        });
        self.prepared.insert(name.to_owned(), prepared.clone());
        prepared
    }
}

/// A definition a stop condition or observations are evaluated in, loaded: by the prepared
/// observer, `None` for the case's own definition.
type LoadedCondition = (Option<Arc<Observer>>, Result<Semantics, String>);

/// The definition `source` names, from `loaded` where it was loaded before, else loaded into it
/// from `definition`'s `stage` or the observer's; `what` names its use in a refusal.
fn loaded<'l>(
    loaded: &'l mut Vec<LoadedCondition>,
    source: &ConditionSource<Arc<Observer>>,
    (definition, stage): (&DefinitionIr, &CompiledStage),
    solver: BackendOptions,
    what: &str,
) -> Result<&'l mut Semantics, String> {
    let observer = match source {
        ConditionSource::Own => None,
        ConditionSource::Named(observer) => Some(observer),
    };
    let found = loaded
        .iter()
        .position(|(loaded, _)| match (loaded, observer) {
            (None, None) => true,
            (Some(loaded), Some(observer)) => Arc::ptr_eq(loaded, observer),
            _ => false,
        });
    let position = found.unwrap_or_else(|| {
        let semantics = exec::load_condition(
            definition,
            stage,
            observer.map(|observer| (&observer.definition, &observer.stage)),
            solver,
            &mut Timings::disabled(),
        )
        .map_err(|error| format!("krs cannot load the {what}'s definition: {error}"));
        loaded.push((observer.cloned(), semantics));
        loaded.len() - 1
    });
    loaded[position].1.as_mut().map_err(|reason| reason.clone())
}

/// A worker's definitions, each loaded on its first case.
struct Worker<'a> {
    definition: &'a DefinitionIr,
    stage: &'a CompiledStage,
    sources: &'a DiagnosticSources,
    solver: BackendOptions,
    budget: u64,
    subject: Option<Result<Semantics, String>>,
    /// The observers loaded, by the prepared observer they were loaded from.
    observers: Vec<(Arc<Observer>, Result<Semantics, String>)>,
    /// The definitions stop conditions are evaluated in, loaded apart from the views' observers
    /// (a comparison reads both at once): by the prepared observer, `None` for another
    /// semantics of the case's own definition.
    conditions: Vec<LoadedCondition>,
    /// The definitions observations are evaluated in, loaded apart from the stop conditions'
    /// (a run asks both at once), as those are.
    observations: Vec<LoadedCondition>,
}

impl<'a> Worker<'a> {
    fn new(batch: &Batch<'a>) -> Self {
        Self {
            definition: batch.definition,
            stage: batch.stage,
            sources: batch.sources,
            solver: batch.request.solver,
            budget: batch.request.view_budget,
            subject: None,
            observers: Vec::new(),
            conditions: Vec::new(),
            observations: Vec::new(),
        }
    }

    /// The record of `job`; a panic while running it refuses the case and reloads the
    /// definitions for the next one, since their state is then unknown.
    fn record(&mut self, job: &Job) -> Record {
        let id = job.id.clone();
        match std::panic::catch_unwind(AssertUnwindSafe(|| self.run(job))) {
            Ok(Ok(record)) => record,
            Ok(Err(reason)) => Record::refused(id, reason).naming(&job.case.case),
            Err(_) => {
                self.subject = None;
                self.observers.clear();
                self.conditions.clear();
                self.observations.clear();
                Record::refused(id, "krs panicked while running the case".to_owned())
                    .naming(&job.case.case)
            }
        }
    }

    fn run(&mut self, job: &Job) -> Result<Record, String> {
        let Self {
            definition,
            stage,
            sources,
            solver,
            budget,
            subject,
            observers,
            conditions,
            observations,
        } = self;
        let own = (*definition, *stage);
        let condition = job
            .condition
            .as_ref()
            .map(|source| loaded(conditions, source, own, *solver, "stop condition"))
            .transpose()?;
        let observations = job
            .observations
            .as_ref()
            .map(|source| loaded(observations, source, own, *solver, "observations"))
            .transpose()?;
        let subject = subject
            .get_or_insert_with(|| {
                let sources = (*sources).clone();
                let provider: SourceText = Box::new(move |file| sources.source_text(file));
                Semantics::from_stage_with_solver(
                    definition,
                    (*stage).clone(),
                    Some(provider),
                    *solver,
                    &mut Timings::disabled(),
                )
                .map_err(|error| format!("krs cannot load the definition: {error}"))
            })
            .as_mut()
            .map_err(|reason| reason.clone())?;
        let observer = match &job.observer {
            None => None,
            Some(observer) => {
                let position = if let Some(position) = observers
                    .iter()
                    .position(|(loaded, _)| Arc::ptr_eq(loaded, observer))
                {
                    position
                } else {
                    let semantics = Semantics::from_stage_with_solver(
                        &observer.definition,
                        observer.stage.clone(),
                        None,
                        *solver,
                        &mut Timings::disabled(),
                    )
                    .map_err(|error| format!("krs cannot load the observer: {error}"));
                    observers.push((Arc::clone(observer), semantics));
                    observers.len() - 1
                };
                Some(
                    observers[position]
                        .1
                        .as_mut()
                        .map_err(|reason| reason.clone())?,
                )
            }
        };
        let observers = krs_exec::Observers {
            condition,
            observations,
        };
        run_case(subject, observer, observers, job, *budget).map_err(|failure| failure.reason())
    }
}

/// Run `job`'s case on `semantics`, as `krs run --case` runs it, its stop condition and its
/// observations evaluated in `observers`, and check its end against its expectation, the views
/// evaluated in `observer` (`semantics` when `None`) within `budget`.
///
/// The observations a case declares are recorded as `krs run --case` records them, so that a
/// case whose observation sequence does not exist (an element with no value) is refused here as
/// there; the record states no verdict on them, since an expectation states none.
fn run_case(
    semantics: &mut Semantics,
    observer: Option<&mut Semantics>,
    observers: krs_exec::Observers<'_>,
    job: &Job,
    budget: u64,
) -> Result<Record, Failure> {
    let krs_exec::Observers {
        mut condition,
        observations,
    } = observers;
    let case = &job.case;
    let stop = case.stop(&StopCriterion::None, None)?;
    let depth = case.depth(None)?;
    let state = exec::configure(semantics, Inputs::of_case(case), false)?;
    let mut expectation = SelectedCase::expectation_of(Some(case), semantics)?;
    if let Some(expectation) = &mut expectation {
        exec::resolve_views(semantics, observer.as_deref(), case, expectation)?;
    }
    let options = RunOptions {
        depth,
        stop,
        condition_budget: Some(budget),
        observe: case.case.observe.as_deref().cloned(),
        ..RunOptions::default()
    };
    let report = match (
        semantics.run_with(
            &state,
            options.clone(),
            krs_exec::Observers {
                condition: condition.as_deref_mut(),
                observations,
            },
        ),
        &expectation,
    ) {
        (Ok(report), _) => report,
        // A run that cannot decide which of several states it reaches has no one end.
        (Err(error @ ExecError::Undecided { .. }), Some(expectation)) => {
            let checked = Checked::undecided(case, expectation, &error);
            return Ok(Record {
                checked: Some(checked),
                ..Record::of(job.id.clone(), Verdict::Inconclusive)
            });
        }
        // Without an expectation, the case ran to no one end: no answer, as an inconclusive halt.
        (Err(error @ ExecError::Undecided { .. }), None) => {
            return Ok(Record {
                reason: Some(format!("the run has no one end: {error}")),
                ..Record::of(job.id.clone(), Verdict::Ran)
            });
        }
        (Err(error), _) => return Err(error.into()),
    };
    let run = Some((report.halt, report.steps));
    let stops = stops_of(semantics, &report, &options.stop);
    let undeclared =
        exec::DeclaredOutcome::of(semantics, &report) == exec::DeclaredOutcome::Undeclared;
    let Some(mut expectation) = expectation else {
        return Ok(Record {
            run,
            stops,
            end: report.end,
            end_undecided: report.end_undecided,
            undeclared,
            ..Record::of(job.id.clone(), Verdict::Ran)
        });
    };
    let checked = exec::check_run(
        semantics,
        observer,
        condition,
        Run {
            case,
            state: &state,
            options: &options,
            report: &report,
        },
        &mut expectation,
        budget,
    )?;
    let verdict = match checked.verdict {
        Compared::Equal => Verdict::Met,
        Compared::Differs(_) => Verdict::Unmet,
        Compared::Inconclusive(_) => Verdict::Inconclusive,
    };
    Ok(Record {
        run,
        checked: Some(checked),
        stops,
        end: report.end,
        end_undecided: report.end_undecided,
        undeclared,
        ..Record::of(job.id.clone(), verdict)
    })
}

/// A record's stops ([`Record::stops`]): `None` for a run without stop rules.
fn stops_of(
    semantics: &Semantics,
    report: &krs_exec::RunReport,
    criterion: &StopCriterion,
) -> Option<(String, serde_json::Map<String, serde_json::Value>)> {
    let stops = report.reported_stops()?;
    let mut members = serde_json::Map::new();
    let mut put = |key: &str, value: serde_json::Result<serde_json::Value>| {
        if let Ok(value) = value
            && !value.is_null()
            && value != json!([])
        {
            members.insert(key.to_owned(), value);
        }
    };
    put("stop", serde_json::to_value(&report.stop));
    put("stops", Ok(json!(stops)));
    put("arrivals", serde_json::to_value(report.arrivals));
    put("undecided", serde_json::to_value(&report.undecided));
    put("passed_stops", serde_json::to_value(&report.passed_stops));
    Some((exec::stops_passed(semantics, report, criterion), members))
}

/// Whether `name` matches `pattern`, where `*` matches any text and `?` any one character.
fn glob_matches(pattern: &str, name: &str) -> bool {
    let pattern = pattern.chars().collect::<Vec<_>>();
    let name = name.chars().collect::<Vec<_>>();
    // The furthest `*` seen, and the name position its match currently ends at.
    let (mut p, mut n) = (0, 0);
    let mut star: Option<(usize, usize)> = None;
    while n < name.len() {
        match pattern.get(p) {
            Some('*') => {
                star = Some((p, n));
                p += 1;
            }
            Some('?') => {
                p += 1;
                n += 1;
            }
            Some(&character) if character == name[n] => {
                p += 1;
                n += 1;
            }
            _ => match star {
                Some((star_p, star_n)) => {
                    p = star_p + 1;
                    n = star_n + 1;
                    star = Some((star_p, star_n + 1));
                }
                None => return false,
            },
        }
    }
    pattern[p..].iter().all(|character| *character == '*')
}

#[cfg(test)]
mod tests {
    use super::{Record, Tally, Verdict, glob_matches};
    use krs_exec::Halt;
    use std::collections::BTreeMap;

    /// A case without an expectation whose run has no end is inconclusive in the status, and
    /// one whose run ends is not; an unmet case comes before an inconclusive one, and a refused
    /// case before an unmet one.
    #[test]
    fn a_ran_case_without_an_end_makes_the_status_inconclusive() {
        let ran = |halt| Record {
            id: "a.toml#ran".to_owned(),
            verdict: Verdict::Ran,
            run: Some((halt, 3)),
            checked: None,
            reason: None,
            written: (BTreeMap::new(), None),
            stops: None,
            end: None,
            end_undecided: None,
            undeclared: false,
        };
        let mut tally = Tally::default();
        tally.count(&ran(Halt::Stuck));
        tally.count(&ran(Halt::DepthBound));
        assert_eq!(tally.status(), 0);
        // A run with no one path has no end either.
        let mut no_path = Tally::default();
        no_path.count(&ran(Halt::Stuck));
        no_path.count(&Record {
            run: None,
            reason: Some("the run has no one end".to_owned()),
            ..ran(Halt::Stuck)
        });
        assert_eq!(no_path.status(), 3);
        assert_eq!(no_path.json()["summary"]["ran"], 2);
        tally.count(&ran(Halt::Interrupted));
        assert_eq!(tally.status(), 3);
        assert_eq!(tally.json()["summary"]["ran"], 3);
        tally.count(&Record {
            verdict: Verdict::Unmet,
            run: None,
            ..ran(Halt::Stuck)
        });
        assert_eq!(tally.status(), 1);
        tally.count(&Record::refused("b.toml".to_owned(), "no".to_owned()));
        assert_eq!(tally.status(), 2);
        assert_eq!(tally.json()["status"], 2);
    }

    /// In a definition that declares ends, a case that states no expectation and ends in no
    /// declared end is a finding, which the summary counts; an expectation's verdict replaces
    /// it; and a definition that declares none keeps its version and its summary.
    #[test]
    fn a_ran_case_at_no_declared_end_is_a_finding() {
        let ran = |verdict, undeclared| Record {
            id: "a.toml#gap".to_owned(),
            verdict,
            run: Some((Halt::Stuck, 0)),
            checked: None,
            reason: None,
            written: (BTreeMap::new(), None),
            stops: None,
            end: None,
            end_undecided: None,
            undeclared,
        };
        let mut tally = Tally {
            declares_ends: true,
            ..Tally::default()
        };
        tally.count(&ran(Verdict::Ran, false));
        assert_eq!(tally.status(), 0);
        assert_eq!(tally.json()["summary"]["undeclared"], 0);
        tally.count(&ran(Verdict::Met, true));
        assert_eq!(tally.status(), 0);
        tally.count(&ran(Verdict::Ran, true));
        assert_eq!(tally.status(), 1);
        let summary = tally.json();
        assert_eq!(summary["schema"], "krs-cases/5");
        assert_eq!(summary["summary"]["undeclared"], 1);
        assert_eq!(summary["summary"]["ran"], 2);
        assert!(tally.human().ends_with(", 2 ran (1 at no declared end)\n"));
        let plain = Tally::default();
        assert_eq!(plain.json()["schema"], "krs-cases/4");
        assert_eq!(plain.json()["summary"].get("undeclared"), None);
        assert!(plain.human().ends_with(", 0 ran\n"));
    }

    #[test]
    fn name_patterns_match_any_text_and_any_character() {
        assert!(glob_matches("ld-a", "ld-a"));
        assert!(!glob_matches("ld-a", "ld-ab"));
        assert!(glob_matches("ld-*", "ld-a"));
        assert!(glob_matches("ld-*", "ld-"));
        assert!(glob_matches("*-a", "ld-a"));
        assert!(glob_matches("l?-?", "ld-a"));
        assert!(!glob_matches("l?-?", "ld-ab"));
        assert!(glob_matches("*a*b*", "xxaxxbxx"));
        assert!(!glob_matches("*a*b", "xxaxxbxx"));
        assert!(glob_matches("*", ""));
        assert!(!glob_matches("?", ""));
    }
}
