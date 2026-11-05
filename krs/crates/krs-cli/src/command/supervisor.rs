//! `krs prove` as a supervisor: the claims are proved in a child process, so a process that ends
//! abnormally costs the claim it was proving and no other.
//!
//! A solver runs in the proof process, and some of its failures end that process
//! (Z3 exits with status 114 on an internal error; an abort or the kernel's out-of-memory killer
//! ends it by a signal); no code in the process can recover from that.
//! So `krs prove` runs the krs executable again as a worker (`--worker-protocol`, hidden), which
//! proves the claims and writes one event per line on its stdout; its stderr is passed through.
//!
//! The events are JSON objects whose `event` names them:
//! - `selected`: the claims the request selects, in order (`claims`, each as `krs-exec` serializes
//!   a claim), resolved once, before any is proved;
//! - `started`: the claim the worker proves next (`claim`, its label);
//! - `finished`: that claim's label (`claim`) and `verdict`, its `report` (a `krs-exec/2` proof
//!   report) when the output is JSON, the `text` the text outputs print for it and the `warnings`
//!   its prints raised;
//! - `end`: every selected claim finished and the worker's checks passed.
//!
//! A report's leaves are KAST JSON, which nests about two levels per term level, so a report can
//! be deeper than any fixed nesting limit: the supervisor keeps it as the worker's text
//! ([`RawValue`]), which it reads without recursion and prints unchanged.
//! A line that begins as an event and does not parse as one is an error of the batch; any other
//! line is something in the worker that wrote to its stdout, and is passed to stderr.
//!
//! A worker that ends with a status krs returns (0 to 3, [`exit_status`]) ended normally: after
//! `end` the batch is complete; without it, the worker reported an error on stderr, and that error
//! is the batch's. A worker returns 0 when it sends `end` and [`exit_status::UNASKED`] for an
//! error; the claims' verdicts, not the worker's status, give the batch's answer.
//! Any other end (a signal, or another exit status) is a crash; a worker that panics ends with
//! [`krs_exec::PANIC_EXIT_STATUS`], so a panic is a crash too. The claim that started and did not
//! finish is recorded as `crashed`, with how the worker ended ([`Crash`]), and the claims that did
//! not start are proved by a fresh worker, given them exactly (`--worker-claim`, hidden).
//! A worker colours its leaves as `--worker-color` (hidden) says, which the supervisor resolves
//! from `--color` against its own stdout.
//! Each worker after the first is started only when the previous one proved or crashed on at
//! least one claim, so a batch starts at most one worker per claim. A crash before `selected`, or a
//! crash outside any claim of a worker that finished none, is an error of the batch. A crash after
//! the last claim leaves every verdict but not the batch's own checks and output, so the batch's
//! status is the question not asked, joined with the verdicts'.

use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsString;
use std::fmt::Write as _;
use std::io::{BufRead as _, BufReader, Write};
use std::process::{Command, ExitStatus, Stdio};

use krs_exec::{ClaimInfo, Crash, PROVE_REPORT_SCHEMA, ProofReport, SolverReport, Verdict};
use serde::{Deserialize, Serialize};
use serde_json::json;
use serde_json::value::RawValue;

use super::exec::{ProveRequest, TermOutput};
use super::exit_status;

/// What `krs prove` prints of a batch, claim by claim, whether the claims are proved in this
/// process or by workers: stderr names each claim as it starts; the text outputs and
/// `--output jsonl` print each claim on stdout as it ends; `--output json` prints the one
/// document at the end; stderr ends with the count of proven claims.
pub(super) struct ProveOutput<'a> {
    output: TermOutput,
    /// The solver the claims are proved with, which the JSON outputs name.
    solver: SolverReport,
    stdout: &'a mut dyn Write,
    stderr: &'a mut dyn Write,
    /// The reports `--output json` prints at the end.
    reports: Vec<Box<RawValue>>,
    /// The number of claims of each verdict.
    verdicts: BTreeMap<&'static str, usize>,
    claims: usize,
    /// The [`exit_status::join`] of the finished claims' statuses ([`verdict_status`]).
    status: i32,
}

impl<'a> ProveOutput<'a> {
    pub(super) fn new(
        output: TermOutput,
        solver: SolverReport,
        stdout: &'a mut dyn Write,
        stderr: &'a mut dyn Write,
    ) -> Self {
        Self {
            output,
            solver,
            stdout,
            stderr,
            reports: Vec::new(),
            verdicts: BTreeMap::new(),
            claims: 0,
            status: exit_status::YES,
        }
    }

    /// The claim `label` is proved next.
    pub(super) fn started(&mut self, label: &str) -> std::io::Result<()> {
        line(self.stderr, &format!("proving {label}"))
    }

    /// Whether [`Self::finished`] needs a claim's serialized report.
    pub(super) const fn wants_report(&self) -> bool {
        wants_report(self.output)
    }

    /// A claim's proof ended with `verdict`: `report` is its serialized report (needed only when
    /// [`Self::wants_report`]), `text` what the text outputs print for it, `warnings` what its
    /// prints raised.
    pub(super) fn finished(
        &mut self,
        report: Option<Box<RawValue>>,
        verdict: Verdict,
        text: &str,
        warnings: &str,
    ) -> std::io::Result<()> {
        self.claims += 1;
        *self.verdicts.entry(verdict.as_str()).or_default() += 1;
        self.status = exit_status::join(self.status, verdict_status(verdict));
        let report =
            || report.ok_or_else(|| std::io::Error::other("a JSON output's claim has no report"));
        match self.output {
            TermOutput::Json => self.reports.push(report()?),
            TermOutput::JsonLines => {
                // The keys in the order a `serde_json::Value` object keeps them, as every krs
                // JSON document has them.
                #[derive(Serialize)]
                struct Line<'a> {
                    proof: &'a RawValue,
                    schema: &'static str,
                }
                let report = report()?;
                let line = Line {
                    proof: &report,
                    schema: PROVE_REPORT_SCHEMA,
                };
                serde_json::to_writer(&mut *self.stdout, &line)?;
                writeln!(self.stdout)?;
            }
            _ => self.stdout.write_all(text.as_bytes())?,
        }
        self.stdout.flush()?;
        self.stderr.write_all(warnings.as_bytes())?;
        self.stderr.flush()
    }

    /// The process proving `report`'s claim ended as its [`Crash`] says.
    fn crashed(&mut self, report: &ProofReport) -> std::io::Result<()> {
        let crash = report
            .crash
            .as_ref()
            .expect("a crashed report records its crash");
        line(
            self.stderr,
            &format!("krs prove: {} crashed: {crash}", report.claim),
        )?;
        let text = format!("{}: crashed\n  {crash}\n", report.claim);
        let value = self
            .wants_report()
            .then(|| serialize_report(report))
            .transpose()?;
        self.finished(value, Verdict::Crashed, &text, "")
    }

    /// Print what follows the last claim, and return the batch's exit status, the
    /// [`exit_status::join`] of its claims' ([`verdict_status`]). The JSON outputs name the solver
    /// the claims were proved with: the document's `solver` member, and the summary line's.
    pub(super) fn close(self) -> std::io::Result<i32> {
        let count = |verdict: Verdict| self.verdicts.get(verdict.as_str()).copied().unwrap_or(0);
        let (proven, trusted, crashed, timeout) = (
            count(Verdict::Proven),
            count(Verdict::Trusted),
            count(Verdict::Crashed),
            count(Verdict::Timeout),
        );
        match self.output {
            TermOutput::Json => {
                // The keys in the order a `serde_json::Value` object keeps them.
                #[derive(Serialize)]
                struct Document<'a> {
                    prove: &'a [Box<RawValue>],
                    schema: &'static str,
                    solver: &'a SolverReport,
                }
                let document = Document {
                    prove: &self.reports,
                    schema: PROVE_REPORT_SCHEMA,
                    solver: &self.solver,
                };
                serde_json::to_writer(&mut *self.stdout, &document)?;
                writeln!(self.stdout)?;
            }
            TermOutput::JsonLines => {
                let summary = json!({
                    "schema": PROVE_REPORT_SCHEMA,
                    "solver": self.solver,
                    "summary": {"claims": self.claims, "verdicts": self.verdicts},
                });
                writeln!(self.stdout, "{summary}")?;
            }
            _ => {}
        }
        self.stdout.flush()?;
        let mut also = String::new();
        if trusted != 0 {
            let _ = write!(also, ", {trusted} trusted");
        }
        if crashed != 0 {
            let _ = write!(also, ", {crashed} crashed");
        }
        if timeout != 0 {
            let _ = write!(also, ", {timeout} timed out");
        }
        line(
            self.stderr,
            &format!(
                "krs prove: {proven} of {} claim{} proven{also}",
                self.claims,
                if self.claims == 1 { "" } else { "s" },
            ),
        )?;
        Ok(self.status)
    }
}

/// The exit status a claim's verdict gives ([`exit_status`]): yes for a proven or a trusted claim
/// (a trusted claim is assumed, never proven, and does not fail the batch); a finding for a
/// disproved or a failed one; no answer for one the proof could not decide within its bounds
/// (indeterminate, depth or breadth bound, timeout); the question not asked for a claim whose
/// process crashed, which gave no answer and reported no error of its own.
const fn verdict_status(verdict: Verdict) -> i32 {
    match verdict {
        Verdict::Proven | Verdict::Trusted => exit_status::YES,
        Verdict::Disproved | Verdict::Failed => exit_status::NO,
        Verdict::Indeterminate | Verdict::DepthBound | Verdict::BreadthBound | Verdict::Timeout => {
            exit_status::UNANSWERED
        }
        Verdict::Crashed => exit_status::UNASKED,
    }
}

/// Whether a claim's serialized report is printed under `output`: only the JSON outputs print it.
pub(super) const fn wants_report(output: TermOutput) -> bool {
    matches!(output, TermOutput::Json | TermOutput::JsonLines)
}

/// `report` as the JSON outputs print it: serialized through a `serde_json::Value`, so its
/// objects' keys are in the order every krs JSON document has them.
/// A report's leaves can nest deeply: the caller runs on a thread with a large stack.
pub(super) fn serialize_report(report: &ProofReport) -> std::io::Result<Box<RawValue>> {
    let value = serde_json::to_value(report)?;
    Ok(serde_json::value::to_raw_value(&value)?)
}

/// Write the `selected` event: `selection`, and the Z3 library this worker links.
pub(super) fn send_selected(
    events: &mut impl Write,
    selection: &[ClaimInfo],
) -> std::io::Result<()> {
    send(
        events,
        &Event {
            claims: Some(selection.to_vec()),
            z3: krs_exec::z3_version().map(str::to_owned),
            ..Event::new("selected")
        },
    )
}

/// Write the `started` event of the claim `label`.
pub(super) fn send_started(events: &mut impl Write, label: &str) -> std::io::Result<()> {
    send(
        events,
        &Event {
            claim: Some(label.to_owned()),
            ..Event::new("started")
        },
    )
}

/// Write the `finished` event of `report`; its serialized form goes with it only when `output`
/// prints it ([`wants_report`]).
pub(super) fn send_finished(
    events: &mut impl Write,
    output: TermOutput,
    report: &ProofReport,
    text: &str,
    warnings: &str,
) -> std::io::Result<()> {
    let serialized = wants_report(output)
        .then(|| serialize_report(report))
        .transpose()?;
    send(
        events,
        &Event {
            claim: Some(report.claim.clone()),
            verdict: Some(report.verdict),
            report: serialized,
            text: Some(text.to_owned()),
            warnings: Some(warnings.to_owned()),
            ..Event::new("finished")
        },
    )
}

/// The `end` event, which the worker prints as its command's stdout.
pub(super) fn end_event() -> String {
    let mut line = serde_json::to_string(&Event::new("end")).expect("an end event serializes");
    line.push('\n');
    line
}

fn send(events: &mut impl Write, event: &Event) -> std::io::Result<()> {
    serde_json::to_writer(&mut *events, event)?;
    writeln!(events)?;
    events.flush()
}

/// Write `text` and a newline to `out` in one write, then flush. A worker shares the batch's
/// stderr and writes to it while the supervisor does (a panic message, a warning), and a line
/// written in pieces could be split by the worker's output; one write to a pipe of at most
/// `PIPE_BUF` bytes is never interleaved with another's.
fn line(out: &mut dyn Write, text: &str) -> std::io::Result<()> {
    let mut bytes = String::with_capacity(text.len() + 1);
    bytes.push_str(text);
    bytes.push('\n');
    out.write_all(bytes.as_bytes())?;
    out.flush()
}

/// The test hook of a worker: `KRS_TEST_CRASH_AT` lists, separated by commas, the points at which
/// the worker ends as a crash does. A point is a claim's label (when the worker starts that
/// claim), `before-selection`, `before-claims` (after the selection, before the first claim) or
/// `after-claims` (after the last claim, before `end`); a label always has a `.`, so no label is
/// one of the words. The worker ends by `KRS_TEST_CRASH_EXIT`'s exit status when that is a
/// number, by a panic when it is `panic`, and by an abort otherwise. Only a debug build has it.
#[cfg(debug_assertions)]
pub(super) fn test_crash(point: &str) {
    let Ok(points) = std::env::var("KRS_TEST_CRASH_AT") else {
        return;
    };
    if !points.split(',').any(|listed| listed == point) {
        return;
    }
    let _ = std::io::stderr().flush();
    let how = std::env::var("KRS_TEST_CRASH_EXIT").unwrap_or_default();
    // Formatted first, so the panic hook writes the message in one piece.
    let message = format!("the test hook panics at {point}");
    assert!(how != "panic", "{message}");
    match how.parse::<i32>() {
        Ok(status) => std::process::exit(status),
        Err(_) => std::process::abort(),
    }
}

/// In a worker, end the process once its supervisor has ended: nothing reads its events then,
/// and a supervisor that is killed (by a run's time budget, for one) gets no chance to stop it.
/// A thread checks the parent process every second, since a process can see that its parent
/// ended (it is adopted by another process) but is not told.
pub fn watch_supervisor() {
    #[cfg(unix)]
    {
        let supervisor = std::os::unix::process::parent_id();
        let watch = move || {
            loop {
                std::thread::sleep(std::time::Duration::from_secs(1));
                if std::os::unix::process::parent_id() != supervisor {
                    std::process::exit(1);
                }
            }
        };
        // Without the thread the worker still ends at its next event, which fails to write.
        let _ = std::thread::Builder::new()
            .name("krs-supervisor-watch".into())
            .spawn(watch);
    }
}

/// How one worker ended.
struct Ended {
    /// The `selected` event's claims and Z3 library, when the worker sent one.
    selected: Option<(Vec<ClaimInfo>, Option<String>)>,
    /// The claim that started and did not finish.
    running: Option<String>,
    /// The claims the worker finished.
    finished: usize,
    /// Whether the worker sent `end`.
    end: bool,
    status: ExitStatus,
}

/// Run `krs prove` with `arguments` (its command line, without the executable) as a supervisor of
/// workers, as the module documentation describes, and return its exit status.
#[must_use]
pub fn supervise_prove(arguments: &[OsString], request: &ProveRequest) -> i32 {
    let mut stdout = std::io::stdout().lock();
    let mut stderr = std::io::stderr();
    let mut printed = ProveOutput::new(
        request.output,
        SolverReport::of(request.solver),
        &mut stdout,
        &mut stderr,
    );
    // `--color auto` colours when this process's stdout is a terminal; a worker's stdout is the
    // events pipe, so the choice is made here and given to each worker.
    let color = if request.color.enabled() {
        "always"
    } else {
        "never"
    };
    let worker_status = supervise(arguments, color, &mut printed);
    let closed = worker_status.and_then(|status| {
        Ok(exit_status::join(
            printed.close().map_err(|error| output_error(&error))?,
            status,
        ))
    });
    match closed {
        Ok(status) => status,
        Err(Stop::Reported) => exit_status::UNASKED,
        Err(Stop::Error(message)) => {
            let _ = line(&mut std::io::stderr(), &format!("krs prove: {message}"));
            exit_status::UNASKED
        }
    }
}

/// Why a batch stops without its summary.
enum Stop {
    /// A worker reported an error on stderr and ended with a status krs returns.
    Reported,
    /// The supervisor's own error.
    Error(String),
}

fn output_error(error: &std::io::Error) -> Stop {
    Stop::Error(format!("could not write the proof output: {error}"))
}

/// Prove the batch in workers; the status is [`exit_status::UNASKED`] when the last worker failed
/// or crashed after it finished every claim, since the batch's own checks and output did not
/// complete, 0 otherwise.
fn supervise(
    arguments: &[OsString],
    color: &str,
    printed: &mut ProveOutput<'_>,
) -> Result<i32, Stop> {
    let executable = std::env::current_exe()
        .map_err(|error| Stop::Error(format!("could not find the krs executable: {error}")))?;
    // The selection and the Z3 library, from the first worker's `selected` event.
    let mut selection: Option<(Vec<ClaimInfo>, Option<String>)> = None;
    let mut done = BTreeSet::new();
    loop {
        let remaining = selection.as_ref().map(|(claims, _)| {
            claims
                .iter()
                .filter(|claim| !done.contains(&claim.label))
                .collect::<Vec<_>>()
        });
        let mut command = Command::new(&executable);
        command
            .args(arguments)
            .args(["--worker-protocol", "--worker-color", color]);
        for claim in remaining.iter().flatten() {
            command.arg("--worker-claim").arg(&claim.label);
        }
        let ended = run_worker(&mut command, printed, &mut done)?;
        if selection.is_none() {
            selection = ended.selected;
        }
        let code = ended.status.code();
        if ended.end && matches!(code, Some(0..=3)) {
            return Ok(if code == Some(0) {
                exit_status::YES
            } else {
                exit_status::UNASKED
            });
        }
        match code {
            Some(0) => {
                return Err(Stop::Error(
                    "the proof process ended without finishing its claims".into(),
                ));
            }
            // A status krs returns: the worker reported its error on stderr.
            Some(1..=3) => return Err(Stop::Reported),
            _ => {}
        }
        let crash = |z3: &Option<String>| Crash {
            exit_status: code,
            signal: signal(ended.status),
            z3: z3.clone(),
        };
        let Some((claims, z3)) = &selection else {
            return Err(Stop::Error(format!(
                "{} before it selected the claims",
                crash(&None)
            )));
        };
        let crash = crash(z3);
        if let Some(label) = &ended.running {
            let claim = claims
                .iter()
                .find(|claim| &claim.label == label)
                .ok_or_else(|| {
                    Stop::Error(format!(
                        "a proof process started the unselected claim `{label}`"
                    ))
                })?;
            printed
                .crashed(&ProofReport::crashed(claim, crash.clone()))
                .map_err(|error| output_error(&error))?;
            done.insert(label.clone());
        } else if ended.finished == 0 {
            return Err(Stop::Error(format!("{crash} outside any claim")));
        }
        let left = claims
            .iter()
            .filter(|claim| !done.contains(&claim.label))
            .count();
        if left == 0 {
            if ended.running.is_none() {
                let _ = line(
                    &mut std::io::stderr(),
                    &format!("krs prove: {crash} after its last claim"),
                );
            }
            // The worker did not complete the batch's checks and output after its last claim.
            return Ok(exit_status::UNASKED);
        }
        let _ = line(
            &mut std::io::stderr(),
            &format!(
                "krs prove: proving the {left} remaining claim{} in a new process",
                if left == 1 { "" } else { "s" }
            ),
        );
    }
}

/// Start one worker, print each claim it finishes, and wait for it.
fn run_worker(
    command: &mut Command,
    printed: &mut ProveOutput<'_>,
    done: &mut BTreeSet<String>,
) -> Result<Ended, Stop> {
    let mut child = command
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit())
        .spawn()
        .map_err(|error| Stop::Error(format!("could not start the proof process: {error}")))?;
    let events = BufReader::new(child.stdout.take().expect("the worker's stdout is piped"));
    let mut ended = Ended {
        selected: None,
        running: None,
        finished: 0,
        end: false,
        status: ExitStatus::default(),
    };
    let mut failure = None;
    for line in events.lines() {
        let line = match line {
            Ok(line) => line,
            Err(error) => {
                failure = Some(Stop::Error(format!(
                    "could not read the proof process's output: {error}"
                )));
                break;
            }
        };
        if let Err(stop) = event(&line, printed, done, &mut ended) {
            failure = Some(stop);
            break;
        }
    }
    if failure.is_some() {
        // The worker can no longer be followed; it is this supervisor's child, so stop it.
        let _ = child.kill();
    }
    ended.status = child
        .wait()
        .map_err(|error| Stop::Error(format!("could not wait for the proof process: {error}")))?;
    failure.map_or(Ok(ended), Err)
}

/// One event, as a worker writes it and its supervisor reads it: `event` names it, and each kind
/// has the fields the module documentation lists. The report stays text ([`RawValue`]): reading it
/// as a raw value has no nesting limit and does not recurse.
#[derive(Deserialize, Serialize)]
struct Event {
    #[serde(rename = "event")]
    kind: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    claim: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    verdict: Option<Verdict>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    report: Option<Box<RawValue>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    text: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    warnings: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    claims: Option<Vec<ClaimInfo>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    z3: Option<String>,
}

impl Event {
    fn new(event: &str) -> Self {
        Self {
            kind: event.to_owned(),
            claim: None,
            verdict: None,
            report: None,
            text: None,
            warnings: None,
            claims: None,
            z3: None,
        }
    }
}

/// The beginning of every event line: `serde_json` writes an [`Event`]'s fields in order.
const EVENT_PREFIX: &str = "{\"event\"";

/// Act on one line of a worker's stdout.
fn event(
    line: &str,
    printed: &mut ProveOutput<'_>,
    done: &mut BTreeSet<String>,
    ended: &mut Ended,
) -> Result<(), Stop> {
    let malformed = |what: &str| {
        let shown: String = line.chars().take(200).collect();
        let more = if shown.len() < line.len() { "..." } else { "" };
        Stop::Error(format!("the proof process sent {what}: {shown}{more}"))
    };
    let event = match serde_json::from_str::<Event>(line) {
        Ok(event) => event,
        Err(error) if line.starts_with(EVENT_PREFIX) => {
            return Err(malformed(&format!(
                "an event that does not parse ({error})"
            )));
        }
        Err(_) => {
            // Not an event: something in the worker wrote to its stdout; keep it, on stderr.
            let _ = self::line(&mut std::io::stderr(), line);
            return Ok(());
        }
    };
    match event.kind.as_str() {
        "selected" => {
            let claims = event
                .claims
                .ok_or_else(|| malformed("a selection without claims"))?;
            ended.selected = Some((claims, event.z3));
        }
        "started" => {
            let label = event
                .claim
                .ok_or_else(|| malformed("a start without a claim"))?;
            if let Some(running) = &ended.running {
                return Err(malformed(&format!(
                    "a start while `{running}` had not finished"
                )));
            }
            printed
                .started(&label)
                .map_err(|error| output_error(&error))?;
            ended.running = Some(label);
        }
        "finished" => {
            let (Some(label), Some(verdict)) = (event.claim, event.verdict) else {
                return Err(malformed("a finish without its claim and verdict"));
            };
            if ended.running.as_ref() != Some(&label) {
                return Err(malformed("a finish of a claim that had not started"));
            }
            if printed.wants_report() && event.report.is_none() {
                return Err(malformed("a finish without its report"));
            }
            printed
                .finished(
                    event.report,
                    verdict,
                    event.text.as_deref().unwrap_or_default(),
                    event.warnings.as_deref().unwrap_or_default(),
                )
                .map_err(|error| output_error(&error))?;
            ended.running = None;
            ended.finished += 1;
            done.insert(label);
        }
        "end" => ended.end = true,
        other => return Err(malformed(&format!("an unknown event `{other}`"))),
    }
    Ok(())
}

/// The signal that killed a process.
#[cfg(unix)]
fn signal(status: ExitStatus) -> Option<i32> {
    std::os::unix::process::ExitStatusExt::signal(&status)
}

#[cfg(not(unix))]
fn signal(_: ExitStatus) -> Option<i32> {
    None
}

#[cfg(test)]
mod tests {
    /// A proven or trusted claim is yes, a disproved or failed one a finding, a claim the proof
    /// could not decide within its bounds no answer, and a crashed one the question not asked.
    #[test]
    fn a_claim_s_verdict_gives_its_status() {
        use super::{Verdict, exit_status, verdict_status};
        for (verdict, status) in [
            (Verdict::Proven, exit_status::YES),
            (Verdict::Trusted, exit_status::YES),
            (Verdict::Disproved, exit_status::NO),
            (Verdict::Failed, exit_status::NO),
            (Verdict::Indeterminate, exit_status::UNANSWERED),
            (Verdict::DepthBound, exit_status::UNANSWERED),
            (Verdict::BreadthBound, exit_status::UNANSWERED),
            (Verdict::Timeout, exit_status::UNANSWERED),
            (Verdict::Crashed, exit_status::UNASKED),
        ] {
            assert_eq!(verdict_status(verdict), status, "{verdict:?}");
        }
    }

    use super::{Ended, ProveOutput, Stop, event};
    use crate::command::exec::TermOutput;
    use std::collections::BTreeSet;
    use std::process::ExitStatus;

    fn ended() -> Ended {
        Ended {
            selected: None,
            running: Some("SPEC.deep".to_owned()),
            finished: 0,
            end: false,
            status: ExitStatus::default(),
        }
    }

    /// A report nested far deeper than `serde_json`'s default limit of 128 (a deep leaf's KAST
    /// JSON) is read, recorded, and printed byte for byte.
    #[test]
    fn a_deep_report_is_printed_unchanged() {
        let depth = 10_000;
        let report = format!(
            r#"{{"claim":"SPEC.deep","leaves":[{}{}],"verdict":"disproved"}}"#,
            "[".repeat(depth),
            "]".repeat(depth)
        );
        let line = format!(
            r#"{{"event":"finished","claim":"SPEC.deep","verdict":"disproved","report":{report},"text":"","warnings":""}}"#
        );
        let (mut stdout, mut stderr) = (Vec::new(), Vec::new());
        let mut printed = ProveOutput::new(
            TermOutput::JsonLines,
            krs_exec::SolverReport::of(krs_exec::BackendOptions::RESOURCE_BOUNDED),
            &mut stdout,
            &mut stderr,
        );
        let (mut done, mut ended) = (BTreeSet::new(), ended());
        assert!(event(&line, &mut printed, &mut done, &mut ended).is_ok());
        assert_eq!(ended.finished, 1);
        assert!(done.contains("SPEC.deep"));
        drop(printed);
        assert_eq!(
            String::from_utf8(stdout).unwrap(),
            format!("{{\"proof\":{report},\"schema\":\"krs-exec/2\"}}\n")
        );
    }

    /// A line that begins as an event and does not parse fails the batch instead of being taken
    /// for stray output, and a finish needs the claim that started.
    #[test]
    fn a_malformed_event_is_an_error() {
        let (mut stdout, mut stderr) = (Vec::new(), Vec::new());
        let mut printed = ProveOutput::new(
            TermOutput::Json,
            krs_exec::SolverReport::of(krs_exec::BackendOptions::RESOURCE_BOUNDED),
            &mut stdout,
            &mut stderr,
        );
        let mut done = BTreeSet::new();
        for line in [
            r#"{"event":"finished","claim":"SPEC.deep","verdict":"disproved","report":[}"#,
            r#"{"event":"finished","claim":"SPEC.other","verdict":"proven","report":{}}"#,
            r#"{"event":"finished","claim":"SPEC.deep","verdict":"proven"}"#,
            r#"{"event":"started","claim":"SPEC.other"}"#,
            r#"{"event":"unknown"}"#,
        ] {
            let outcome = event(line, &mut printed, &mut done, &mut ended());
            assert!(matches!(outcome, Err(Stop::Error(_))), "{line}");
        }
        assert!(done.is_empty());
        // Anything else is something in the worker that wrote to its stdout.
        assert!(event("not an event", &mut printed, &mut done, &mut ended()).is_ok());
    }
}
