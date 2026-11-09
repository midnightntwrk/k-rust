//! The SMT trace: a record of the in-process solver's work, written while the process runs, for
//! diagnosing a solver crash, measuring the resource units queries consume, and reading what a
//! query's preparation and an implication check decided.
//!
//! `K_RUST_SMT_TRACE=<directory>` turns the trace on for the whole process; the variable is read
//! once, at the first attempt or record. Unset or empty, nothing is recorded, and an attempt reads
//! one process-wide value more than it would without the trace.
//!
//! - Before Z3 reads an attempt's script, the script is written, with a header that states the
//!   attempt, to `<directory>/<pid>-<thread>-inflight.smt2` and synced to disk; the file is
//!   removed once Z3 is done with the attempt: after its check, and for a model query after its
//!   model is read. Z3 ends the process from inside a call on an internal error (its
//!   `UNREACHABLE` calls `exit`), and no code after that call runs then: the in-flight files left
//!   behind are exactly the attempts Z3 was working on when the process ended. One whose log line
//!   is present ended after its check answered, while its model was read. A completed write
//!   alone outlives the process; the sync also keeps the file across a crash of the machine,
//!   which a run that exhausts the host's memory can cause.
//! - `<directory>/<pid>.jsonl` receives one JSON object per line: one per attempt (`"kind":
//!   "check"`: its script's SHA-256, its index, its budget's mode (`"budget"`: `units` or
//!   `clock`) and limits, its answer and Z3's reason for an
//!   unknown, the resource units it consumed and its wall time), one per query preparation of
//!   finite summaries (`"kind": "summary_preparation"`: whether the query has a congruence policy
//!   and how many calls it offers), one per call it offers (`"kind": "summary_admission"`: its
//!   eligibility and the catalog's verdict), and one per implication check (`"kind":
//!   "implication"`: what it established, and over how many destinations). Every record carries
//!   a process-wide sequence number, the thread's index and the label of the scope it was made in
//!   (`with_label`, `label`).
//! - `K_RUST_SMT_TRACE_SCRIPTS=all` also keeps every distinct script as
//!   `<directory>/<sha256>.smt2`, to build replay corpora. Its header states the attempt ladder
//!   of the first query that sent it; the log's lines state every attempt's limits. A kept script
//!   is written under a temporary name and renamed into place, so a kept script is complete
//!   whenever it exists.
//!
//! The trace is a diagnostic. It adds no assertion and no term to any Z3 context: it reads the
//! context's statistics once before a check, after the script is loaded, and once after it, and
//! the reason of an unknown answer after it. Reading statistics copies counters out of the
//! solver; it neither asserts nor simplifies, so it changes nothing the check or a later attempt
//! searches. So it changes no answer, and it enters no cache key and no output of the
//! backend. A failure to write the trace is reported once on standard error and changes
//! nothing else.
//!
//! [`replay`] runs a traced script's attempt ladder again on the linked Z3, and
//! `examples/smt_replay.rs` does so from the command line.

use std::{
    cell::Cell,
    ffi::OsString,
    fmt::Write as _,
    fs::{self, File, OpenOptions},
    io::{self, Write as _},
    num::NonZeroU32,
    path::{Path, PathBuf},
    sync::{
        Arc, Mutex, OnceLock,
        atomic::{AtomicBool, AtomicU64, Ordering},
    },
    time::Duration,
};

use serde_json::{Map, Value, json};
use sha2::{Digest, Sha256};
use z3::{SatResult, Solver};

use super::{
    AttemptLimit, Checked, Ladder, RejectedScript, SmtBudget, Z3Options, on_own_context,
    run_attempt,
};
use crate::{
    smt::summary::Rejected,
    term::{Term, TermKind},
};

/// The variable naming the trace's directory.
pub(crate) const DIRECTORY_VARIABLE: &str = "K_RUST_SMT_TRACE";
/// The variable that keeps every distinct script when it is `all`.
pub(crate) const SCRIPTS_VARIABLE: &str = "K_RUST_SMT_TRACE_SCRIPTS";

/// The first line of a traced script's header.
const HEADER_MAGIC: &str = "; k-rust-smt-trace 1";
/// The last line of a traced script's header; the script follows it.
const HEADER_END: &str = "; end of header";

/// Where the trace goes, once it is on.
#[derive(Debug)]
pub(crate) struct Sink {
    directory: PathBuf,
    keep_scripts: bool,
    log: Mutex<File>,
    sequence: AtomicU64,
    reported: AtomicBool,
}

impl Sink {
    fn open(directory: PathBuf, keep_scripts: bool) -> io::Result<Self> {
        fs::create_dir_all(&directory)?;
        let log = OpenOptions::new()
            .create(true)
            .append(true)
            .open(directory.join(format!("{}.jsonl", std::process::id())))?;
        Ok(Self {
            directory,
            keep_scripts,
            log: Mutex::new(log),
            sequence: AtomicU64::new(0),
            reported: AtomicBool::new(false),
        })
    }

    fn next(&self) -> u64 {
        self.sequence.fetch_add(1, Ordering::Relaxed)
    }

    /// Report the trace's first write failure; the process's work goes on untraced in part.
    fn failed(&self, what: &str, error: &io::Error) {
        if !self.reported.swap(true, Ordering::Relaxed) {
            eprintln!(
                "k-rust: the SMT trace in {} could not {what}: {error}; later failures are not reported",
                self.directory.display()
            );
        }
    }

    /// Append one record as a line of the log: one write of the whole line, under the lock, so
    /// that lines of concurrent threads never interleave.
    fn append(&self, sequence: u64, kind: &str, mut fields: Map<String, Value>) {
        fields.insert("seq".into(), json!(sequence));
        fields.insert("kind".into(), json!(kind));
        fields.insert("thread".into(), json!(thread_index()));
        fields.insert("label".into(), json!(LABEL.with(Cell::get)));
        let mut line = Value::Object(fields).to_string();
        line.push('\n');
        let mut log = self
            .log
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        if let Err(error) = log.write_all(line.as_bytes()) {
            self.failed("append to its log", &error);
        }
    }

    fn inflight_path(&self) -> PathBuf {
        self.directory.join(format!(
            "{}-{}-inflight.smt2",
            std::process::id(),
            thread_index()
        ))
    }
}

/// The trace's directory and whether every script is kept, read from `variable`: `None` when
/// the directory variable is unset or empty.
fn configured(variable: impl Fn(&str) -> Option<OsString>) -> Option<(PathBuf, bool)> {
    let directory = variable(DIRECTORY_VARIABLE).filter(|directory| !directory.is_empty())?;
    let keep_scripts = match variable(SCRIPTS_VARIABLE) {
        None => false,
        Some(value) if value.is_empty() => false,
        Some(value) if value == "all" => true,
        Some(value) => {
            eprintln!(
                "k-rust: {SCRIPTS_VARIABLE}={} is not `all`; only in-flight scripts are kept",
                value.to_string_lossy()
            );
            false
        }
    };
    Some((PathBuf::from(directory), keep_scripts))
}

fn from_environment() -> Option<Arc<Sink>> {
    let (directory, keep_scripts) = configured(|name| std::env::var_os(name))?;
    match Sink::open(directory.clone(), keep_scripts) {
        Ok(sink) => Some(Arc::new(sink)),
        Err(error) => {
            eprintln!(
                "k-rust: the SMT trace in {} could not be opened: {error}; the process runs untraced",
                directory.display()
            );
            None
        }
    }
}

static PROCESS: OnceLock<Option<Arc<Sink>>> = OnceLock::new();

#[cfg(test)]
thread_local! {
    /// A test's own sink for the thread, in place of the process's.
    static OVERRIDE: std::cell::RefCell<Option<Option<Arc<Sink>>>> =
        const { std::cell::RefCell::new(None) };
}

/// The trace's sink, when the trace is on.
fn active() -> Option<Arc<Sink>> {
    #[cfg(test)]
    if let Some(sink) = OVERRIDE.with(|cell| cell.borrow().clone()) {
        return sink;
    }
    PROCESS.get_or_init(from_environment).clone()
}

/// Run `body` with the thread's trace going to `directory` (`None`: off) whatever the
/// environment says.
#[cfg(test)]
pub(crate) fn with_directory<R>(
    directory: Option<&Path>,
    keep_scripts: bool,
    body: impl FnOnce() -> R,
) -> R {
    let sink = directory.map(|directory| {
        Arc::new(Sink::open(directory.to_owned(), keep_scripts).expect("trace directory"))
    });
    /// Puts the thread's previous override back, also when `body` panics.
    struct Restore(Option<Option<Arc<Sink>>>);
    impl Drop for Restore {
        fn drop(&mut self) {
            let previous = self.0.take();
            OVERRIDE.with(|cell| cell.replace(previous));
        }
    }
    let _restore = Restore(OVERRIDE.with(|cell| cell.replace(Some(sink))));
    body()
}

static NEXT_THREAD: AtomicU64 = AtomicU64::new(0);

thread_local! {
    static THREAD: u64 = NEXT_THREAD.fetch_add(1, Ordering::Relaxed);
    static LABEL: Cell<Option<&'static str>> = const { Cell::new(None) };
}

/// The thread's index in the trace: threads are numbered from 0 in the order they first record.
fn thread_index() -> u64 {
    THREAD.with(|index| *index)
}

/// A label's scope: until it is dropped, every record the thread makes carries the label; then
/// the thread's label is the one it had before.
#[must_use = "the label applies only while its scope is held"]
pub(crate) struct LabelScope(Option<Option<&'static str>>);

impl LabelScope {
    /// End the label's scope here rather than where the scope is dropped.
    pub(crate) fn end(self) {}
}

impl Drop for LabelScope {
    fn drop(&mut self) {
        if let Some(previous) = self.0.take() {
            LABEL.with(|cell| cell.set(previous));
        }
    }
}

/// Put `label` on every record the thread makes while the returned scope is held. With the trace
/// off this does nothing.
pub(crate) fn label(label: &'static str) -> LabelScope {
    if active().is_none() {
        return LabelScope(None);
    }
    LabelScope(Some(LABEL.with(|cell| cell.replace(Some(label)))))
}

/// Run `body` with `label` on every record the thread makes meanwhile, and restore the label it
/// had before, also when `body` panics. With the trace off this only runs `body`.
pub(crate) fn with_label<R>(label: &'static str, body: impl FnOnce() -> R) -> R {
    let _scope = self::label(label);
    body()
}

fn sha256(script: &str) -> String {
    let digest = Sha256::digest(script.as_bytes());
    let mut text = String::with_capacity(64);
    for byte in digest {
        let _ = write!(text, "{byte:02x}");
    }
    text
}

/// A budget as a header states it: `units N` or `clock N` (milliseconds).
fn budget_text(budget: SmtBudget) -> String {
    match budget {
        SmtBudget::Units(units) => format!("units {units}"),
        SmtBudget::Clock(clock) => format!("clock {}", clock.timeout_ms()),
    }
}

/// The budget a header's `budget` line states ([`budget_text`]).
#[expect(
    clippy::disallowed_methods,
    reason = "a replay runs the ladder the trace recorded, a clock when the traced query had one"
)]
fn parse_budget(value: &str) -> Result<SmtBudget, String> {
    let number = |text: &str| {
        text.parse::<u32>()
            .map_err(|error| format!("header `budget`: {error}"))
    };
    match value.split_once(' ') {
        Some(("units", units)) => Ok(SmtBudget::Units(
            NonZeroU32::new(number(units)?).ok_or("header `budget`: 0 units")?,
        )),
        Some(("clock", ms)) => Ok(SmtBudget::clock(number(ms)?)),
        _ => Err(format!(
            "header `budget`: `{value}` is neither `units N` nor `clock N`"
        )),
    }
}

/// The header of a traced script: the Z3 library, the ladder and, for an attempt, which one.
fn header(
    ladder: &Ladder,
    sha: &str,
    attempt: Option<(u64, u32, AttemptLimit)>,
    label: Option<&str>,
) -> String {
    let mut text = String::new();
    let _ = writeln!(text, "{HEADER_MAGIC}");
    let _ = writeln!(text, "; z3 = {}", super::z3_version());
    let _ = writeln!(text, "; script_sha256 = {sha}");
    let _ = writeln!(text, "; budget = {}", budget_text(ladder.options.budget));
    let _ = writeln!(text, "; retry_limit = {}", ladder.options.retry_limit);
    let _ = writeln!(
        text,
        "; clock = {}",
        if ladder.clocked { "on" } else { "off" }
    );
    if let Some((sequence, attempt, (timeout, rlimit))) = attempt {
        let _ = writeln!(text, "; seq = {sequence}");
        let _ = writeln!(text, "; attempt = {attempt}");
        let _ = writeln!(text, "; attempt_rlimit = {rlimit}");
        let _ = writeln!(
            text,
            "; attempt_timeout_ms = {}",
            timeout.map_or_else(|| "none".into(), |timeout| timeout.to_string())
        );
    }
    let _ = writeln!(text, "; label = {}", label.unwrap_or("none"));
    let _ = writeln!(text, "{HEADER_END}");
    text
}

/// Write `contents` to `path` and sync it to disk.
fn write_synced(path: &Path, contents: &[&[u8]]) -> io::Result<()> {
    let mut file = File::create(path)?;
    for part in contents {
        file.write_all(part)?;
    }
    file.sync_all()
}

/// Write `contents` to a temporary file beside `path`, sync it, and rename it to `path`: `path`
/// either does not exist or holds all of `contents`, also when the process ends mid-write or
/// another thread writes the same file meanwhile.
fn write_complete(path: &Path, contents: &[&[u8]]) -> io::Result<()> {
    let mut temporary = path.as_os_str().to_owned();
    temporary.push(format!(".{}-{}.tmp", std::process::id(), thread_index()));
    let temporary = PathBuf::from(temporary);
    write_synced(&temporary, contents)?;
    fs::rename(&temporary, path).inspect_err(|_| {
        let _ = fs::remove_file(&temporary);
    })
}

fn answer_text(result: SatResult) -> &'static str {
    match result {
        SatResult::Sat => "sat",
        SatResult::Unsat => "unsat",
        SatResult::Unknown => "unknown",
    }
}

/// One attempt being traced: its script is on disk until [`Attempt::rejected`] records that Z3
/// did not load it, or until the [`Answered`] that [`Attempt::finish`] returns is dropped. An
/// attempt dropped unanswered leaves its script, as one Z3 ended the process in does.
pub(super) struct Attempt {
    sink: Arc<Sink>,
    sequence: u64,
    inflight: Option<PathBuf>,
    fields: Map<String, Value>,
}

impl Attempt {
    /// Start tracing attempt `attempt` of `script` under `ladder` with `limit`: write the
    /// script before Z3 reads it. `None` when the trace is off.
    pub(super) fn begin(
        script: &str,
        ladder: &Ladder,
        attempt: u32,
        limit: AttemptLimit,
    ) -> Option<Self> {
        let sink = active()?;
        let sequence = sink.next();
        let sha = sha256(script);
        let label = LABEL.with(Cell::get);
        let path = sink.inflight_path();
        let inflight = match write_synced(
            &path,
            &[
                header(ladder, &sha, Some((sequence, attempt, limit)), label).as_bytes(),
                script.as_bytes(),
            ],
        ) {
            Ok(()) => Some(path),
            Err(error) => {
                sink.failed("write an in-flight script", &error);
                None
            }
        };
        if sink.keep_scripts {
            let kept = sink.directory.join(format!("{sha}.smt2"));
            if !kept.exists()
                && let Err(error) = write_complete(
                    &kept,
                    &[
                        header(ladder, &sha, None, label).as_bytes(),
                        script.as_bytes(),
                    ],
                )
            {
                sink.failed("keep a script", &error);
            }
        }
        let (timeout, rlimit) = limit;
        let mut fields = Map::new();
        fields.insert("script_sha256".into(), json!(sha));
        fields.insert("script_bytes".into(), json!(script.len()));
        fields.insert("attempt".into(), json!(attempt));
        fields.insert("retry_limit".into(), json!(ladder.options.retry_limit));
        fields.insert(
            "budget".into(),
            json!(match ladder.options.budget {
                SmtBudget::Units(_) => "units",
                SmtBudget::Clock(_) => "clock",
            }),
        );
        fields.insert("rlimit_param".into(), json!(rlimit));
        fields.insert("timeout_param".into(), json!(timeout));
        Some(Self {
            sink,
            sequence,
            inflight,
            fields,
        })
    }

    /// Append the attempt's line, and hand over its in-flight script.
    fn end(mut self, result: &str, reason: Option<String>, checked: Option<&Checked>) -> Answered {
        self.fields.insert("result".into(), json!(result));
        self.fields.insert("reason".into(), json!(reason));
        self.fields.insert(
            "rlimit_used".into(),
            json!(checked.and_then(|checked| checked.rlimit_used)),
        );
        self.fields.insert(
            "wall_us".into(),
            json!(
                checked
                    .and_then(|checked| checked.wall)
                    .map(|wall| u64::try_from(wall.as_micros()).unwrap_or(u64::MAX))
            ),
        );
        self.sink.append(self.sequence, "check", self.fields);
        Answered {
            sink: self.sink,
            inflight: self.inflight,
        }
    }

    /// Record the answer of the attempt's check by `solver`. The in-flight script stays until
    /// the returned value is dropped: hold it while Z3 still works on the attempt's context.
    pub(super) fn finish(self, solver: &Solver, checked: &Checked) -> Answered {
        let reason =
            matches!(checked.result, SatResult::Unknown).then(|| super::reason_unknown(solver));
        self.end(answer_text(checked.result), reason, Some(checked))
    }

    /// Record that Z3 did not load the attempt's script, and remove the script.
    pub(super) fn rejected(self, rejected: &RejectedScript) {
        drop(self.end("rejected", Some(rejected.message.clone()), None));
    }
}

/// A traced attempt whose check has answered: its in-flight script is removed when this is
/// dropped, once Z3 is done with the attempt.
pub(super) struct Answered {
    sink: Arc<Sink>,
    inflight: Option<PathBuf>,
}

impl Drop for Answered {
    fn drop(&mut self) {
        if let Some(path) = self.inflight.take()
            && let Err(error) = fs::remove_file(&path)
        {
            self.sink.failed("remove an in-flight script", &error);
        }
    }
}

/// Record a query's preparation of finite summaries: whether the query has a congruence policy,
/// without which it prepares none, and how many calls it offers to the catalog (`None`: none
/// collected, for want of a policy or because collecting them exceeded its work bound).
pub(in crate::smt) fn summary_preparation(congruence: bool, calls: Option<usize>) {
    let Some(sink) = active() else {
        return;
    };
    let mut fields = Map::new();
    fields.insert("congruence".into(), json!(congruence));
    fields.insert("calls".into(), json!(calls));
    sink.append(sink.next(), "summary_preparation", fields);
}

/// Record a function call that a query's preparation considered for a finite summary: whether it
/// was an eligible operand (`None`: not eligible, so not offered), and the catalog's admission
/// verdict.
pub(in crate::smt) fn summary_admission(call: &Term, verdict: Option<Result<(), Rejected>>) {
    let Some(sink) = active() else {
        return;
    };
    // Preparation offers only applications of unhooked functions.
    let head = if let TermKind::Application { symbol, .. } = call.kind() {
        symbol.name.to_string()
    } else {
        "(not an application)".to_owned()
    };
    let mut fields = Map::new();
    fields.insert("head".into(), json!(head));
    fields.insert("eligible".into(), json!(verdict.is_some()));
    fields.insert(
        "verdict".into(),
        json!(verdict.map(|verdict| match verdict {
            Ok(()) => "accepted".to_owned(),
            Err(rejected) => format!("{rejected:?}"),
        })),
    );
    sink.append(sink.next(), "summary_admission", fields);
}

/// What an implication check established, as the trace records it.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Established {
    /// The variant's name (`Holds`, `Undecided`, `Unprepared`, ...).
    pub(crate) variant: &'static str,
    /// Whether the obligations came from the consequent's condition or a match remainder.
    pub(crate) origin: Option<&'static str>,
    /// Which procedure refuted the obligations.
    pub(crate) refuter: Option<&'static str>,
    /// How many obligations the variant carries.
    pub(crate) obligations: Option<usize>,
}

/// Record what an implication check over `destinations` consequents established; `describe` runs
/// only with the trace on.
pub(crate) fn implication(destinations: usize, describe: impl FnOnce() -> Established) {
    let Some(sink) = active() else {
        return;
    };
    let established = describe();
    let mut fields = Map::new();
    fields.insert("destinations".into(), json!(destinations));
    fields.insert("established".into(), json!(established.variant));
    fields.insert("origin".into(), json!(established.origin));
    fields.insert("refuter".into(), json!(established.refuter));
    fields.insert("obligations".into(), json!(established.obligations));
    sink.append(sink.next(), "implication", fields);
}

/// A script read back from a trace: the script and the ladder its header states.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TracedScript {
    /// The script, exactly as Z3 read it.
    pub script: String,
    /// The query's attempt ladder; the default ladder ([`Z3Options::DEFAULT`]) for a script
    /// without a header, or whose header states no budget.
    pub options: Z3Options,
    /// Whether the clock bounded the attempts.
    pub clocked: bool,
    /// The in-flight attempt the file was written for, if it is an in-flight file.
    pub attempt: Option<u32>,
    /// The Z3 library the script was traced on.
    pub z3: Option<String>,
    /// The label of the scope the script was traced in.
    pub label: Option<String>,
}

impl TracedScript {
    /// Read a traced script, or a plain script without a header (one a minimizer wrote, say).
    ///
    /// A header states its budget on one `budget` line ([`budget_text`]). A header written
    /// before that line existed states it as `resource_limit` (`none`, or the units) and
    /// `timeout_ms` (the clock, used only under `resource_limit = none`), and reads as it did.
    ///
    /// # Errors
    ///
    /// A malformed header, a header that states its budget twice (two `budget` lines, or a
    /// `budget` line with the older keys), or a script whose SHA-256 differs from the one its
    /// header states.
    pub fn parse(text: &str) -> Result<Self, String> {
        let Some(rest) = text
            .strip_prefix(HEADER_MAGIC)
            .and_then(|rest| rest.strip_prefix('\n'))
        else {
            return Ok(Self {
                script: text.to_owned(),
                options: Z3Options::default(),
                clocked: true,
                attempt: None,
                z3: None,
                label: None,
            });
        };
        let mut traced = Self {
            script: String::new(),
            options: Z3Options::default(),
            clocked: true,
            attempt: None,
            z3: None,
            label: None,
        };
        let mut sha = None;
        let mut budget = None;
        let mut legacy_timeout = None;
        let mut legacy_units = None;
        let mut rest = rest;
        loop {
            let Some((line, after)) = rest.split_once('\n') else {
                return Err(format!("the header has no `{HEADER_END}` line"));
            };
            rest = after;
            if line == HEADER_END {
                break;
            }
            let Some((key, value)) = line
                .strip_prefix("; ")
                .and_then(|line| line.split_once(" = "))
            else {
                return Err(format!("malformed header line `{line}`"));
            };
            let number = |value: &str| {
                value
                    .parse::<u32>()
                    .map_err(|error| format!("header `{key}`: {error}"))
            };
            match key {
                "z3" => traced.z3 = Some(value.to_owned()),
                "script_sha256" => sha = Some(value.to_owned()),
                "budget" => {
                    if budget.replace(parse_budget(value)?).is_some() {
                        return Err("the header states `budget` twice".into());
                    }
                }
                "timeout_ms" => legacy_timeout = Some(number(value)?),
                "retry_limit" => traced.options.retry_limit = number(value)?,
                "resource_limit" => {
                    legacy_units = Some(if value == "none" {
                        None
                    } else {
                        Some(NonZeroU32::new(number(value)?).ok_or("header `resource_limit`: 0")?)
                    });
                }
                "clock" => traced.clocked = value != "off",
                "attempt" => traced.attempt = Some(number(value)?),
                "label" => traced.label = (value != "none").then(|| value.to_owned()),
                // Recorded for the reader; the ladder determines them.
                _ => {}
            }
        }
        traced.options.budget = match (budget, legacy_units, legacy_timeout) {
            (Some(_), Some(_), _) | (Some(_), _, Some(_)) => {
                return Err("the header states its budget by `budget` and by older keys".into());
            }
            (Some(budget), None, None) => budget,
            (None, Some(Some(units)), _) => SmtBudget::Units(units),
            (None, Some(None) | None, timeout) => legacy_budget(timeout),
        };
        traced.script = rest.to_owned();
        if let Some(sha) = sha
            && sha != sha256(&traced.script)
        {
            return Err(format!(
                "the script's SHA-256 is {}, not the header's {sha}",
                sha256(&traced.script)
            ));
        }
        Ok(traced)
    }
}

/// The budget of a header written before the `budget` line: the clock of its `timeout_ms` when
/// it has one, and otherwise the default.
#[expect(
    clippy::disallowed_methods,
    reason = "a replay runs the ladder the trace recorded, and a header without `resource_limit` \
              units recorded a clock"
)]
fn legacy_budget(timeout_ms: Option<u32>) -> SmtBudget {
    match timeout_ms {
        Some(timeout_ms) => SmtBudget::clock(timeout_ms),
        None => SmtBudget::DEFAULT,
    }
}

/// One attempt of a replay.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReplayedAttempt {
    /// The attempt's index, 0 first.
    pub attempt: u32,
    /// The attempt's wall-clock timeout; `None` without a clock.
    pub timeout_ms: Option<u32>,
    /// The attempt's resource limit (0: none).
    pub rlimit: u32,
    /// `sat`, `unsat` or `unknown`.
    pub result: &'static str,
    /// Z3's reason for an unknown answer.
    pub reason: Option<String>,
    /// The resource units the check consumed.
    pub rlimit_used: u64,
    /// The check's wall time.
    pub wall: Duration,
}

/// Run `script`'s attempt ladder under `options` on one fresh Z3 context, as the solver runs an
/// uncached query: the attempts share the context, each on a fresh solver, until one decides the
/// script, one meets an internal error of Z3 (its reason is the error's text, as the solver
/// stops there), or the retries are spent. A crash of Z3 can depend on the attempts before it,
/// so a replay runs them all.
///
/// # Errors
///
/// Z3's message when it does not load the script.
pub fn replay(
    script: &str,
    options: Z3Options,
    clocked: bool,
) -> Result<Vec<ReplayedAttempt>, String> {
    let ladder = Ladder { options, clocked };
    on_own_context(|| {
        let mut loaded = None;
        let mut attempts = Vec::new();
        for attempt in 0..=options.retry_limit {
            let limit = ladder.limit(attempt);
            let attempted = run_attempt(script, &mut loaded, &ladder, attempt, limit, true)
                .map_err(|rejected| rejected.message)?;
            let checked = &attempted.checked;
            let reason = matches!(checked.result, SatResult::Unknown)
                .then(|| super::reason_unknown(&attempted.solver));
            let decided_or_faulted = reason.as_deref().is_none_or(super::internal_error);
            attempts.push(ReplayedAttempt {
                attempt,
                timeout_ms: limit.0,
                rlimit: limit.1,
                result: answer_text(checked.result),
                reason,
                rlimit_used: checked.rlimit_used.unwrap_or(0),
                wall: checked.wall.unwrap_or_default(),
            });
            if decided_or_faulted {
                break;
            }
        }
        Ok(attempts)
    })
}

#[cfg(test)]
pub(crate) mod tests;
