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

use super::exec::{
    self, Checked, Failure, Inputs, ObserverDefinition, Run, SelectedCase, StageReuse, WORKER_STACK,
};
use super::{CommandError, CommandOutcome, PreparedDefinition, exit_status};
use crate::DiagnosticSources;

/// The schema every record of `krs cases --output json` names. Version 2 records a case with
/// no expectation whose run has no one path as `ran` with a `reason` and no `halt` (version 1
/// refused it), and its summary's `status` is the exit status of the four actions
/// ([`exit_status`]), under which a refused case is 2, no longer 1.
pub const CASES_SCHEMA: &str = "krs-cases/2";

/// How `krs cases` prints its records.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum CasesOutput {
    /// A line per verdict, with an unmet expectation's difference below it.
    #[default]
    Human,
    /// One [`CASES_SCHEMA`] JSON document per line.
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
    prepared: &PreparedDefinition,
    request: &CasesRequest,
    sources: &DiagnosticSources,
    reuse: StageReuse<'_>,
    observers: &PrepareObserver<'_>,
    measurement: &mut Measurement,
) -> Result<CommandOutcome, CommandError> {
    let definition = prepared.lowered.definition();
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
    result.map_err(|failure| failure.into_command_error(prepared))
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
}

impl Record {
    fn refused(id: String, reason: String) -> Self {
        Self {
            id,
            verdict: Verdict::Refused,
            run: None,
            checked: None,
            reason: Some(reason),
            written: (BTreeMap::new(), None),
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

    /// The record's exit status ([`exit_status`]): yes for a met case or one that ran to an end,
    /// a finding for an unmet one, no answer for an inconclusive one or one that ran to no end,
    /// and the question not asked for a refused one.
    fn status(&self) -> i32 {
        match self.verdict {
            Verdict::Unmet => exit_status::NO,
            Verdict::Refused => exit_status::UNASKED,
            Verdict::Inconclusive | Verdict::Ran if self.inconclusive() => exit_status::UNANSWERED,
            Verdict::Met | Verdict::Inconclusive | Verdict::Ran => exit_status::YES,
        }
    }

    fn json(&self) -> serde_json::Value {
        let mut document = json!({
            "schema": CASES_SCHEMA,
            "case": self.id,
            "verdict": self.verdict.as_str(),
        });
        if let Some((halt, steps)) = self.run {
            document["halt"] = json!(halt.as_str());
            document["steps"] = json!(steps);
        }
        if let Some(reason) = &self.reason {
            document["reason"] = json!(reason);
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
                let _ = writeln!(
                    text,
                    "{}: ran, {} after {steps} step{}",
                    self.id,
                    halt.as_str(),
                    if steps == 1 { "" } else { "s" }
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
    /// The [`exit_status::join`] of the records' statuses ([`Record::status`]).
    status: i32,
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
        json!({
            "schema": CASES_SCHEMA,
            "summary": {
                "cases": self.cases(),
                "met": self.met,
                "unmet": self.unmet,
                "inconclusive": self.inconclusive,
                "refused": self.refused,
                "ran": self.ran,
            },
            "status": self.status(),
        })
    }

    fn human(&self) -> String {
        let cases = self.cases();
        format!(
            "krs cases: {cases} case{}: {} met, {} unmet, {} inconclusive, {} refused, {} ran\n",
            if cases == 1 { "" } else { "s" },
            self.met,
            self.unmet,
            self.inconclusive,
            self.refused,
            self.ran
        )
    }
}

/// Prints records in document order as they arrive in any.
struct Printer {
    next: usize,
    pending: BTreeMap<usize, Record>,
    output: CasesOutput,
    tally: Tally,
}

impl Printer {
    fn put(&mut self, index: usize, record: Record) -> Result<(), Failure> {
        self.pending.insert(index, record);
        while let Some(record) = self.pending.remove(&self.next) {
            self.tally.count(&record);
            let text = match self.output {
                CasesOutput::Json => format!("{}\n", record.json()),
                CasesOutput::Human => record.human(),
            };
            write_stdout(&text)?;
            self.next += 1;
        }
        Ok(())
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
            tally: Tally::default(),
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
            CasesOutput::Human => printer.tally.human(),
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
        } = self;
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
        run_case(subject, observer, job, *budget).map_err(|failure| failure.reason())
    }
}

/// Run `job`'s case on `semantics`, as `krs run --case` runs it, and check its end against its
/// expectation, the views evaluated in `observer` (`semantics` when `None`) within `budget`.
fn run_case(
    semantics: &mut Semantics,
    observer: Option<&mut Semantics>,
    job: &Job,
    budget: u64,
) -> Result<Record, Failure> {
    let case = &job.case;
    let stop = case.stop(&StopCriterion::None)?;
    let depth = case.depth(None)?;
    let state = exec::configure(semantics, Inputs::of_case(case), false)?;
    let mut expectation = SelectedCase::expectation_of(Some(case), semantics)?;
    if let Some(expectation) = &mut expectation {
        exec::resolve_views(semantics, observer.as_deref(), case, expectation)?;
    }
    let options = RunOptions {
        depth,
        stop,
        ..RunOptions::default()
    };
    let report = match (semantics.run(&state, options.clone()), &expectation) {
        (Ok(report), _) => report,
        // A run that cannot decide which of several states it reaches has no one end.
        (Err(error @ ExecError::Undecided { .. }), Some(expectation)) => {
            let checked = Checked::undecided(case, expectation, &error);
            return Ok(Record {
                id: job.id.clone(),
                verdict: Verdict::Inconclusive,
                run: None,
                checked: Some(checked),
                reason: None,
                written: (BTreeMap::new(), None),
            });
        }
        // Without an expectation, the case ran to no one end: no answer, as an inconclusive halt.
        (Err(error @ ExecError::Undecided { .. }), None) => {
            return Ok(Record {
                id: job.id.clone(),
                verdict: Verdict::Ran,
                run: None,
                checked: None,
                reason: Some(format!("the run has no one end: {error}")),
                written: (BTreeMap::new(), None),
            });
        }
        (Err(error), _) => return Err(error.into()),
    };
    let run = Some((report.halt, report.steps));
    let Some(mut expectation) = expectation else {
        return Ok(Record {
            id: job.id.clone(),
            verdict: Verdict::Ran,
            run,
            checked: None,
            reason: None,
            written: (BTreeMap::new(), None),
        });
    };
    let checked = exec::check_run(
        semantics,
        observer,
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
        id: job.id.clone(),
        verdict,
        run,
        checked: Some(checked),
        reason: None,
        written: (BTreeMap::new(), None),
    })
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
