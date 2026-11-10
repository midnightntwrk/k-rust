//! `compare`: other implementations of the corpus's system, each run on every program of the
//! corpus and compared with the definition under each view it declares (README, "Comparing
//! implementations: `kink-flow compare`").
//!
//! An `[[implementation]]` ([`ImplementationSection`]) is a command kink runs once per program,
//! one JSON request on its stdin ([`PROTOCOL`]: the program's id, its inputs as typed values,
//! the corpus's stop count, and the definition's start when `given = "start"`), and whose
//! answer is one JSON document on its stdout: how its run ended, `stopped` (it reached the
//! corpus's `[stop]`), `final` (it ended on its own) or `could-not-apply` (with a `reason`), and
//! for the first two its end's cells in the definition's cell vocabulary. The definition's side
//! is the program's baseline run as every command observes it (`[stop]`, `[budget]`, `[result]`,
//! the result cache), its ends named by the same words: an end some path reached at its last
//! stop is `stopped`, one every path reached on its own is `final`. Neither side names a rule or
//! the computation: the words are the corpus's observation, which both sides share.
//!
//! The comparison of cells is the front end's ([`Vocabulary`]): only a front end that reads the
//! definition's values has a cell vocabulary an implementation can write (krs: cells by Rust
//! field path, values as documents of the typed encoding) and views, functions of those values.
//! kink-flow's own front end reads K terms and has neither, so it refuses the command (stage
//! `implementation`, reason `unsupported-front-end`).
//!
//! Each (implementation, program, view) has one verdict: `equal`, `different` (with the first
//! difference), `could-not-apply` (the implementation's own answer, with its reason) or
//! `not-compared` (with the reason: a compared cell the implementation omits, a definition run
//! with no end or several, a view that could not be evaluated). A run of the implementation
//! that exits non-zero, writes no answer the protocol reads, cannot be started, or that the clock
//! cancels is a failure of the implementation, not a verdict: its row has `failure` and no
//! verdicts. The clock (`time_ms`) only cancels a run, which then has no answer; it never
//! decides a verdict.
//!
//! Only a required view decides the exit status ([`compare_status`]); every other verdict is
//! reported. The document's rows are what a later lock section records per (implementation,
//! program, view), keyed by the request's digest and the implementation's identity.

use crate::admit::{InputFiles, ManifestFiles, admit_spec};
use crate::cli::{EXIT_NO, EXIT_UNANSWERED, EXIT_UNASKED, EXIT_YES, exit_join};
use crate::manifest::{FlowManifest, Given, ImplementationSection, Program, ViewSection};
use crate::results::{
    BaselineRunner, ProgramRow, ResultClass, cache_directory, current_record,
    record_final_configuration, runner_refusal, update_results,
};
use k_rust::kore::{ast::Pattern, parser::parse_pattern};
use kink_corpus::admission::{AdmissionRecord, AdmissionRefusal};
use kink_native::execution::SolverProfile;
use kink_patch::{canonical_json, sha256};
use serde_json::{Map, Value, json};
use std::{
    collections::BTreeSet,
    io::{Read, Write},
    path::{Path, PathBuf},
    process::{Command, Stdio},
    sync::mpsc,
    time::{Duration, Instant},
};

/// The schema of the `compare` document.
pub const COMPARE_SCHEMA: &str = "kink-flow-compare";
/// The version of the `compare` document.
pub const COMPARE_VERSION: u64 = 1;
/// The protocol every request names (`protocol`), and every answer is read by.
pub const PROTOCOL: &str = "kink-implementation/1";
/// The most bytes of an implementation's stderr a failure quotes, its end.
const STDERR_QUOTED: usize = 2000;

/// `compare`'s options.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct CompareOptions {
    /// `--only NAME`: compare only these implementations; empty: every one.
    pub only: Vec<String>,
    /// `--cache DIR`: the result cache of the definition's baseline runs.
    pub cache: Option<PathBuf>,
}

/// How a run of an implementation ended, by its own answer.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EndWord {
    /// It reached the corpus's `[stop]`.
    Stopped,
    /// It ended on its own.
    Final,
}

impl EndWord {
    /// The word as the protocol writes it.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Stopped => "stopped",
            Self::Final => "final",
        }
    }
}

/// Why a view of a program is not compared, which says what to do next.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum NotCompared {
    /// The view compares a cell the implementation omits (`omits`): fix the declaration (2).
    Omitted(Vec<String>),
    /// The view compares a cell the corpus's ends leave out (`[result]`, unobservable cells),
    /// which the definition's side does not state: fix the declaration or the corpus (2).
    LeftOut(String),
    /// The definition's run has several ends under the view (or ends both at the stop and on
    /// its own): one answer against several ends is a question of inclusion, which `compare`
    /// does not decide (3).
    SeveralEnds(String),
    /// A view's evaluation stopped before it ended, or the comparison cannot conclude (3).
    Undecided(String),
    /// The definition's side cannot be stated in the front end's vocabulary (an end or a start
    /// with no document) (2).
    Unreadable(String),
}

impl NotCompared {
    /// The reason's name in documents.
    #[must_use]
    pub const fn reason(&self) -> &'static str {
        match self {
            Self::Omitted(_) => "omitted",
            Self::LeftOut(_) => "left-out",
            Self::SeveralEnds(_) => "several-ends",
            Self::Undecided(_) => "undecided",
            Self::Unreadable(_) => "unreadable",
        }
    }

    /// What the reason says.
    #[must_use]
    pub fn detail(&self) -> String {
        match self {
            Self::Omitted(cells) => format!(
                "the view compares {} the implementation omits (`omits`): its answer does not \
                 state {}",
                cells
                    .iter()
                    .map(|cell| format!("`{cell}`"))
                    .collect::<Vec<_>>()
                    .join(", "),
                if cells.len() == 1 { "it" } else { "them" }
            ),
            Self::LeftOut(detail)
            | Self::SeveralEnds(detail)
            | Self::Undecided(detail)
            | Self::Unreadable(detail) => detail.clone(),
        }
    }

    /// The status of a required view not compared for this reason: [`EXIT_UNANSWERED`] where
    /// another approach may answer (a view that did not end, several ends), [`EXIT_UNASKED`]
    /// where the declaration or the corpus must change.
    #[must_use]
    pub const fn status(&self) -> u8 {
        match self {
            Self::SeveralEnds(_) | Self::Undecided(_) => EXIT_UNANSWERED,
            Self::Omitted(_) | Self::LeftOut(_) | Self::Unreadable(_) => EXIT_UNASKED,
        }
    }
}

/// The front end's comparison of one view: equal, different with the first difference (the
/// front end's document), or not compared.
#[derive(Clone, Debug, PartialEq)]
pub enum Judged {
    /// Every end of the definition agrees with the answer on the view's cells; `omitted` lists
    /// the cells the comparison left out because the implementation omits them.
    Equal { omitted: Vec<String> },
    /// They differ, first here.
    Different {
        difference: Value,
        omitted: Vec<String>,
    },
    /// The view is not compared.
    NotCompared(NotCompared),
}

/// One question to the front end: the answer's cells against the definition's ends, under one
/// view of one implementation.
pub struct Question<'a> {
    pub implementation: &'a ImplementationSection,
    pub view: &'a ViewSection,
    /// The answer's `cells`, as the implementation wrote them; [`Vocabulary::read_answer`]
    /// accepted them.
    pub cells: &'a Value,
    /// The definition's ends for the program, final configurations of the K kink judges as its
    /// result slot compares them: each cell of `not_compared` replaced by `\top` of its sort.
    pub ends: &'a BTreeSet<Pattern>,
    /// The cells the corpus's ends leave out, by K cell name.
    pub not_compared: &'a [String],
}

/// What a front end that reads the definition's values adds for `compare`: its cell
/// vocabulary, in which the implementation is given the start and writes its end, and the
/// comparison of an end under a view. kink-flow's own front end has none.
pub trait Vocabulary {
    /// Check `implementation`'s declaration against the definition before any run: each cell
    /// of `omits` is a cell of the definition, and each view's front-end keys (`compare`,
    /// `views`, `observer`) resolve. `Err` is the refusal's detail, naming the key.
    ///
    /// # Errors
    ///
    /// Why the declaration does not hold of the definition.
    fn check(&self, implementation: &ImplementationSection) -> Result<(), String>;

    /// The document of the definition's start `state` (a configuration of the K kink judges,
    /// every cell stated) in the vocabulary an implementation reads: the request's `start`.
    ///
    /// # Errors
    ///
    /// Why the state has no document.
    fn start(&self, state: &Pattern) -> Result<Value, String>;

    /// `program`'s inputs as typed values, by input name: the request's `inputs`. `files`
    /// reads the files they name, relative to the file the case is written in.
    ///
    /// # Errors
    ///
    /// Why an input has no document.
    fn inputs(&self, program: &Program, files: &mut dyn InputFiles) -> Result<Value, String>;

    /// Check an answer's `cells` before any view compares them: each names a cell of the
    /// definition and holds a value of its type, and every cell a view of `implementation`
    /// compares that it does not omit is stated. `Err` makes the answer malformed, naming the
    /// cell.
    ///
    /// # Errors
    ///
    /// Why the cells are no end of the definition the implementation's views can compare.
    fn read_answer(
        &self,
        implementation: &ImplementationSection,
        cells: &Value,
    ) -> Result<(), String>;

    /// Compare one view ([`Question`]).
    ///
    /// # Errors
    ///
    /// A failure of the comparison itself (a definition that does not load), which fails the
    /// command.
    fn compare(&self, question: &Question<'_>) -> Result<Judged, String>;
}

/// A failure of an implementation's run: no answer to compare.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Failure {
    /// `spawn` (the command cannot be started), `exit` (it exited other than with status 0, or
    /// was killed by a signal), `malformed` (its stdout is no answer the protocol reads), or
    /// `timeout` (the clock cancelled it).
    pub kind: &'static str,
    pub detail: String,
    /// The exit status, when it exited with one.
    pub exit_code: Option<i32>,
    /// The end of its stderr, when it wrote some.
    pub stderr: Option<String>,
}

impl Failure {
    fn new(kind: &'static str, detail: impl Into<String>) -> Self {
        Self {
            kind,
            detail: detail.into(),
            exit_code: None,
            stderr: None,
        }
    }

    /// The failure's member of its row.
    #[must_use]
    pub fn value(&self) -> Value {
        json!({
            "kind": self.kind,
            "detail": self.detail,
            "exit_code": self.exit_code,
            "stderr": self.stderr,
        })
    }

    /// The status of an implementation with a required view whose run failed so: the clock's
    /// cancellation is no answer ([`EXIT_UNANSWERED`]), any other failure leaves the question
    /// unasked ([`EXIT_UNASKED`]: fix the implementation or its declaration).
    #[must_use]
    pub fn status(&self) -> u8 {
        if self.kind == "timeout" {
            EXIT_UNANSWERED
        } else {
            EXIT_UNASKED
        }
    }
}

/// An implementation's answer for one program, read ([`read_answer`]).
#[derive(Clone, Debug, PartialEq)]
pub enum Answer {
    /// It ended, so: its word and its end's cells.
    Ended { end: EndWord, cells: Value },
    /// It could not apply the program as given, for this reason.
    CouldNotApply { reason: String },
}

impl Answer {
    /// The answer's member of its row: `{end, reason}` (its cells are compared, not shown).
    fn value(&self) -> Value {
        match self {
            Self::Ended { end, .. } => json!({"end": end.as_str(), "reason": null}),
            Self::CouldNotApply { reason } => {
                json!({"end": "could-not-apply", "reason": reason})
            }
        }
    }
}

/// Read an answer document ([`PROTOCOL`]): a JSON object of `end`, `cells` (for `stopped` and
/// `final`) and `reason` (for `could-not-apply`, a nonempty string), and no other key.
///
/// # Errors
///
/// Why the bytes are no answer.
pub fn read_answer(bytes: &[u8]) -> Result<Answer, String> {
    let document: Value = serde_json::from_slice(bytes)
        .map_err(|error| format!("stdout is not one JSON document: {error}"))?;
    let Value::Object(object) = document else {
        return Err("the answer is not a JSON object".to_owned());
    };
    if let Some(key) = object
        .keys()
        .find(|key| !matches!(key.as_str(), "end" | "cells" | "reason"))
    {
        return Err(format!(
            "the answer has the key `{key}`; an answer holds `end`, `cells` and `reason` only \
             ({PROTOCOL})"
        ));
    }
    let end = object
        .get("end")
        .and_then(Value::as_str)
        .ok_or("the answer has no `end` string (`stopped`, `final` or `could-not-apply`)")?;
    let word = match end {
        "stopped" => EndWord::Stopped,
        "final" => EndWord::Final,
        "could-not-apply" => {
            if object.contains_key("cells") {
                return Err("a `could-not-apply` answer states no `cells`".to_owned());
            }
            let reason = object
                .get("reason")
                .and_then(Value::as_str)
                .filter(|reason| !reason.trim().is_empty())
                .ok_or("a `could-not-apply` answer gives its `reason`, a nonempty string")?;
            return Ok(Answer::CouldNotApply {
                reason: reason.to_owned(),
            });
        }
        other => {
            return Err(format!(
                "`end` is `{other}`, not `stopped`, `final` or `could-not-apply`"
            ));
        }
    };
    if object.contains_key("reason") {
        return Err(format!("a `{end}` answer gives no `reason`"));
    }
    match object.get("cells") {
        Some(cells @ Value::Object(_)) => Ok(Answer::Ended {
            end: word,
            cells: cells.clone(),
        }),
        Some(_) => Err("`cells` is not a JSON object".to_owned()),
        None => Err(format!("a `{end}` answer states its end's `cells`")),
    }
}

/// What a run of an implementation printed, once it exited with status 0.
struct Ran {
    stdout: Vec<u8>,
    wall_ms: u64,
}

/// Run `command` (its first word resolved by [`executable`]) in `directory` with `request` on
/// its stdin, cancelled after `limit`: its stdout once it exited 0, else the failure. The answer
/// is complete when the process has closed its stdout and stderr, and kink then waits for it to
/// exit; the clock cancels it (and kills it) only when it has not closed them by `limit`, so the
/// clock never decides an answer, only that there is none.
fn run_process(
    command: &[String],
    directory: &Path,
    request: Vec<u8>,
    limit: Duration,
) -> Result<Ran, Failure> {
    enum Stream {
        Out(std::io::Result<Vec<u8>>),
        Err(std::io::Result<Vec<u8>>),
    }
    let started = Instant::now();
    let (program, arguments) = command.split_first().expect("a command has a first word");
    let mut child = Command::new(executable(program, directory))
        .args(arguments)
        .current_dir(directory)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|error| Failure::new("spawn", format!("cannot start `{program}`: {error}")))?;
    let mut stdin = child.stdin.take().expect("stdin is piped");
    let mut stdout = child.stdout.take().expect("stdout is piped");
    let mut stderr = child.stderr.take().expect("stderr is piped");
    // An implementation may answer without reading its request (or exit first): the write then
    // fails, which is no failure of the run.
    let writer = std::thread::spawn(move || {
        let _ = stdin.write_all(&request);
    });
    let (sender, receiver) = mpsc::channel();
    let out = sender.clone();
    std::thread::spawn(move || {
        let mut bytes = Vec::new();
        let read = stdout.read_to_end(&mut bytes).map(|_| bytes);
        let _ = out.send(Stream::Out(read));
    });
    std::thread::spawn(move || {
        let mut bytes = Vec::new();
        let read = stderr.read_to_end(&mut bytes).map(|_| bytes);
        let _ = sender.send(Stream::Err(read));
    });
    let deadline = started + limit;
    let (mut out, mut err) = (None, None);
    while out.is_none() || err.is_none() {
        match receiver.recv_timeout(deadline.saturating_duration_since(Instant::now())) {
            Ok(Stream::Out(read)) => out = Some(read),
            Ok(Stream::Err(read)) => err = Some(read),
            Err(_) => {
                // The readers are left to end with the pipes: a process the implementation
                // started may hold them open past its own end.
                let _ = child.kill();
                let _ = child.wait();
                return Err(Failure::new(
                    "timeout",
                    format!(
                        "the clock cancelled the run after {} ms (time_ms) before it closed its \
                         output: it has no answer on this host",
                        limit.as_millis()
                    ),
                ));
            }
        }
    }
    let status = child
        .wait()
        .map_err(|error| Failure::new("exit", format!("cannot wait for the run: {error}")))?;
    let _ = writer.join();
    let wall_ms = u64::try_from(started.elapsed().as_millis()).unwrap_or(u64::MAX);
    let stderr = match err {
        Some(Ok(bytes)) if !bytes.is_empty() => Some(quoted_end(&bytes)),
        _ => None,
    };
    let stdout = match out {
        Some(Ok(bytes)) => bytes,
        _ => {
            return Err(Failure {
                stderr,
                ..Failure::new("malformed", "its stdout cannot be read")
            });
        }
    };
    if !status.success() {
        return Err(Failure {
            exit_code: status.code(),
            stderr,
            ..Failure::new(
                "exit",
                match status.code() {
                    Some(code) => format!("it exited with status {code}"),
                    None => "it was killed by a signal".to_owned(),
                },
            )
        });
    }
    Ok(Ran { stdout, wall_ms })
}

/// The last [`STDERR_QUOTED`] bytes of `bytes`, as text.
fn quoted_end(bytes: &[u8]) -> String {
    let start = bytes.len().saturating_sub(STDERR_QUOTED);
    String::from_utf8_lossy(&bytes[start..]).into_owned()
}

/// The executable a command's first word names: a path with a `/` relative to `directory`, the
/// manifest's directory; a bare name as the system looks it up on `PATH`.
fn executable(word: &str, directory: &Path) -> PathBuf {
    if word.contains('/') {
        directory.join(word)
    } else {
        PathBuf::from(word)
    }
}

/// The digest of a request or a file, as documents name it.
fn digest(bytes: &[u8]) -> String {
    sha256(bytes).to_string()
}

/// The definition's side of one program: its ends and their words, or why it has none.
enum Definition {
    Ends {
        ends: BTreeSet<Pattern>,
        /// The words of the ends, each once.
        words: BTreeSet<&'static str>,
    },
    /// The program's baseline has no end to compare: its class, its cause.
    None {
        class: String,
        cause: Option<String>,
    },
}

/// The definition's side of `row`, the program's baseline row, with the ends of its record:
/// this command's live run (`runner`, which ran it once), else the stored record.
fn definition_side(
    manifest: &FlowManifest,
    runner: &BaselineRunner<'_>,
    execution: crate::digest::ExecutionDigest,
    program: &Program,
    row: &ProgramRow,
    cache: &Path,
) -> Definition {
    let class = row.row["class"].as_str().unwrap_or("error").to_owned();
    let none = |cause: Option<String>| Definition::None {
        class: class.clone(),
        cause,
    };
    if class != ResultClass::Comparable.as_str() {
        return none(row.row["cause"].as_str().map(str::to_owned));
    }
    let texts: Option<Vec<String>> = match (&row.test, &row.inputs) {
        (Some(test), _) => runner
            .run(test.clone())
            .final_terms()
            .map(|terms| terms.into_iter().map(str::to_owned).collect()),
        (None, Some(inputs)) => current_record(manifest, execution, program, inputs, cache)
            .and_then(|record| {
                record_final_configuration(&record)
                    .map(|terms| terms.into_iter().map(str::to_owned).collect())
            }),
        (None, None) => None,
    };
    let Some(texts) = texts else {
        return none(Some(
            "the baseline's record holds no ends this command can read".to_owned(),
        ));
    };
    let mut ends = BTreeSet::new();
    for text in &texts {
        match parse_pattern(text) {
            Ok(end) => {
                ends.insert(end);
            }
            Err(error) => return none(Some(format!("an end does not parse: {error}"))),
        }
    }
    // Each end's halt, in the order of the record's ends: under `[stop]`, `stop` where some path
    // reached the end at its last stop; without it every end is the run's own.
    let words = if manifest.stop.is_none() {
        BTreeSet::from([EndWord::Final.as_str()])
    } else {
        row.row["ends"]
            .as_array()
            .map(|summaries| {
                summaries
                    .iter()
                    .map(|summary| match summary["halt"].as_str() {
                        Some("stop") => EndWord::Stopped.as_str(),
                        _ => EndWord::Final.as_str(),
                    })
                    .collect()
            })
            .unwrap_or_default()
    };
    Definition::Ends { ends, words }
}

/// The verdicts of one (implementation, program): the views' rows.
fn view_rows(
    vocabulary: &dyn Vocabulary,
    implementation: &ImplementationSection,
    answer: &Answer,
    definition: (&BTreeSet<Pattern>, &BTreeSet<&'static str>),
    not_compared: &[String],
) -> Result<Vec<Value>, String> {
    let (ends, words) = definition;
    let mut rows = Vec::new();
    for view in &implementation.views {
        let mut row = view_row(view);
        match answer {
            Answer::CouldNotApply { reason } => {
                row["verdict"] = json!("could-not-apply");
                row["detail"] = json!(reason);
            }
            Answer::Ended { end, cells } => {
                if words.is_empty() {
                    not_compared_row(
                        &mut row,
                        &NotCompared::Unreadable(
                            "the baseline's record names no end's halt, so its end's word is not \
                             known"
                                .to_owned(),
                        ),
                    );
                } else if words.len() > 1 {
                    not_compared_row(
                        &mut row,
                        &NotCompared::SeveralEnds(
                            "the definition's run ends both at the stop and on its own: one \
                             answer against several ends is a question of inclusion, which \
                             compare does not decide"
                                .to_owned(),
                        ),
                    );
                } else if let Some(word) = words.first().filter(|word| **word != end.as_str()) {
                    row["verdict"] = json!("different");
                    row["difference"] = json!({
                        "format": "kink-end/1",
                        "at": "end",
                        "definition": word,
                        "implementation": end.as_str(),
                    });
                } else {
                    let judged = vocabulary.compare(&Question {
                        implementation,
                        view,
                        cells,
                        ends,
                        not_compared,
                    })?;
                    match judged {
                        Judged::Equal { omitted } => {
                            row["verdict"] = json!("equal");
                            row["omitted"] = json!(omitted);
                        }
                        Judged::Different {
                            difference,
                            omitted,
                        } => {
                            row["verdict"] = json!("different");
                            row["difference"] = difference;
                            row["omitted"] = json!(omitted);
                        }
                        Judged::NotCompared(reason) => not_compared_row(&mut row, &reason),
                    }
                }
            }
        }
        rows.push(row);
    }
    Ok(rows)
}

/// A view's row before its verdict.
fn view_row(view: &ViewSection) -> Value {
    json!({
        "view": view.name,
        "required": view.required,
        "verdict": null,
        "difference": null,
        "reason": null,
        "detail": null,
        "omitted": [],
        "status": null,
    })
}

fn not_compared_row(row: &mut Value, reason: &NotCompared) {
    row["verdict"] = json!("not-compared");
    row["reason"] = json!(reason.reason());
    row["detail"] = json!(reason.detail());
    row["status"] = json!(reason.status());
}

/// The rows of every view of `implementation` not compared because the definition's side of
/// the program has no end (`class`, `cause`).
fn definition_rows(
    implementation: &ImplementationSection,
    class: &str,
    cause: Option<&str>,
) -> Vec<Value> {
    let status = match class {
        "timeout" | "unknown" | "comparable-prefix" => EXIT_UNANSWERED,
        _ => EXIT_UNASKED,
    };
    implementation
        .views
        .iter()
        .map(|view| {
            let mut row = view_row(view);
            row["verdict"] = json!("not-compared");
            row["reason"] = json!("definition");
            row["detail"] = json!(match cause {
                Some(cause) => format!(
                    "the definition's run of the program is `{class}` ({cause}): it has no end \
                     to compare"
                ),
                None => {
                    format!(
                        "the definition's run of the program is `{class}`: it has no end to compare"
                    )
                }
            });
            row["status"] = json!(status);
            row
        })
        .collect()
}

/// The status of one (implementation, program) row: the join of its required views' verdicts
/// (`equal` and `could-not-apply` [`EXIT_YES`], `different` [`EXIT_NO`], `not-compared` its
/// reason's status), and of its failure where some view is required. A view that is not
/// required decides nothing.
#[must_use]
pub fn row_status(row: &Value) -> u8 {
    let required = row["views"]
        .as_array()
        .into_iter()
        .flatten()
        .filter(|view| view["required"] == true);
    let mut status = EXIT_YES;
    for view in required {
        status = exit_join(
            status,
            match view["verdict"].as_str() {
                Some("equal" | "could-not-apply") => EXIT_YES,
                Some("different") => EXIT_NO,
                Some("not-compared") => view["status"]
                    .as_u64()
                    .and_then(|status| u8::try_from(status).ok())
                    .unwrap_or(EXIT_UNASKED),
                _ => EXIT_UNASKED,
            },
        );
    }
    if row["failure"].is_object() && row["required"] == true {
        status = exit_join(
            status,
            if row["failure"]["kind"] == "timeout" {
                EXIT_UNANSWERED
            } else {
                EXIT_UNASKED
            },
        );
    }
    status
}

/// The status of a `compare` document: [`EXIT_UNASKED`] for a refused one, else the join of its
/// rows' statuses ([`row_status`]).
#[must_use]
pub fn compare_status(document: &Value) -> u8 {
    if document["refusal"].is_object()
        || document["spec"]["outcome"] == "refused"
        || document["cache_error"] == true
    {
        return EXIT_UNASKED;
    }
    document["rows"]
        .as_array()
        .into_iter()
        .flatten()
        .map(row_status)
        .fold(EXIT_YES, exit_join)
}

/// The document's head: its schema, the builds and the specification's admission.
fn head(record: &AdmissionRecord, digest: Option<String>) -> Value {
    let refusal = record.refusal.as_ref();
    crate::with_z3_build(json!({
        "schema": COMPARE_SCHEMA,
        "version": COMPARE_VERSION,
        "protocol": PROTOCOL,
        "k_rust_revision": crate::k_rust_revision(),
        "profile": SolverProfile::BUILD.name(),
        "kink_build": kink_campaign::kink_build().map_or(Value::Null, |b| json!(b.to_string())),
        "spec": {
            "outcome": if refusal.is_some() { "refused" } else { "admitted" },
            "stage": refusal.map(|r| &r.stage),
            "reason": refusal.map(|r| &r.reason),
            "detail": refusal.map(|r| &r.detail),
            "digest": digest,
        },
        "refusal": null,
        "implementations": [],
        "programs": [],
        "rows": [],
        "summary": null,
    }))
}

/// A document refusing the comparison before any run: stage `implementation`.
fn refused(manifest: &FlowManifest, reason: &str, detail: String) -> Value {
    let mut document = head(&AdmissionRecord::new(&manifest.spec.entry), None);
    // Refused before the specification is admitted: it was not asked.
    document["spec"] = Value::Null;
    document["refusal"] = json!({"stage": "implementation", "reason": reason, "detail": detail});
    document
}

/// The refusal of a front end with no [`Vocabulary`] (kink-flow's own).
pub const UNSUPPORTED_FRONT_END: &str = "an implementation states its end in the definition's \
     cell vocabulary, values a front end that reads the definition's values reads (the krs front \
     end, `krs kink compare`); kink-flow's own front end reads K terms and has no such \
     vocabulary";

/// `compare` on `manifest` with the front end's `vocabulary` (module documentation): the
/// document, whose status is [`compare_status`]. A result record that could not be written sets
/// its `cache_error`, which fails the command as it fails `coverage`.
pub fn command(
    manifest: &FlowManifest,
    options: &CompareOptions,
    vocabulary: Option<&dyn Vocabulary>,
) -> Value {
    let Some(vocabulary) = vocabulary else {
        return refused(
            manifest,
            "unsupported-front-end",
            UNSUPPORTED_FRONT_END.to_owned(),
        );
    };
    if manifest.implementations.is_empty() {
        return refused(
            manifest,
            "no-implementation",
            "the manifest declares no [[implementation]]: nothing to compare".to_owned(),
        );
    }
    if let Some(name) = options
        .only
        .iter()
        .find(|name| !manifest.implementations.iter().any(|i| &i.name == *name))
    {
        return refused(
            manifest,
            "unknown-implementation",
            format!(
                "--only {name}: the manifest declares no implementation of this name (it \
                 declares {})",
                manifest
                    .implementations
                    .iter()
                    .map(|i| format!("`{}`", i.name))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        );
    }
    let selected = manifest
        .implementations
        .iter()
        .filter(|i| options.only.is_empty() || options.only.contains(&i.name))
        .collect::<Vec<_>>();
    let Ok(root) = std::fs::canonicalize(&manifest.directory) else {
        return refused(
            manifest,
            "manifest-directory",
            "the manifest's directory is unavailable".to_owned(),
        );
    };
    let mut declared = Vec::new();
    for implementation in &selected {
        if let Err(detail) = vocabulary.check(implementation) {
            return refused(
                manifest,
                "declaration",
                format!("implementation `{}`: {detail}", implementation.name),
            );
        }
        let mut value = implementation.value();
        if let Some(identity) = &implementation.identity {
            match std::fs::read(root.join(&identity.file)) {
                Ok(bytes) => value["identity"]["sha256"] = json!(digest(&bytes)),
                Err(error) => {
                    return refused(
                        manifest,
                        "identity",
                        format!(
                            "implementation `{}`: identity.file `{}` cannot be read: {error}",
                            implementation.name, identity.file
                        ),
                    );
                }
            }
        }
        declared.push(value);
    }
    let (mut record, admitted) = admit_spec(manifest);
    let Some((spec, mut inputs)) = admitted else {
        return head(&record, None);
    };
    let mut inputs = inputs.session(&spec);
    let cache = cache_directory(manifest, options.cache.as_deref());
    let runner = match BaselineRunner::new(&spec, manifest) {
        Ok(runner) => runner,
        Err(error) => {
            record.refusal = Some(runner_refusal(error));
            return head(&record, None);
        }
    };
    let update = update_results(&spec, manifest, &mut inputs, &runner, &cache, false, None);
    let not_compared = spec.result.not_compared.clone();
    let mut document = head(&record, Some(update.spec_digest.to_string()));
    let mut rows = Vec::new();
    let mut programs = Vec::new();
    for (program, row) in manifest.programs.iter().zip(&update.rows) {
        programs.push(json!({
            "id": program.id,
            "class": row.row["class"],
            "cause": row.row["cause"],
            "cached": row.row["cached"],
            "cache_error": row.row.get("cache_error"),
        }));
        let definition = definition_side(manifest, &runner, update.execution, program, row, &cache);
        // The request's parts every implementation shares: its inputs and the start, each
        // read once.
        let mut shared: Option<RequestParts> = None;
        for implementation in &selected {
            let mut out = json!({
                "implementation": implementation.name,
                "program": program.id,
                "required": implementation.has_required_view(),
                "request_sha256": null,
                "answer": null,
                "failure": null,
                "wall_ms": null,
                "views": [],
            });
            let (ends, words) = match &definition {
                Definition::None { class, cause } => {
                    out["views"] = json!(definition_rows(implementation, class, cause.as_deref()));
                    rows.push(out);
                    continue;
                }
                Definition::Ends { ends, words } => (ends, words),
            };
            let parts = shared.get_or_insert_with(|| {
                request_parts(
                    vocabulary,
                    &mut inputs,
                    &root,
                    program,
                    row,
                    selected.iter().any(|i| i.given == Given::Start),
                )
            });
            let request = match parts {
                Err(detail) => Err(NotCompared::Unreadable(detail.clone())),
                Ok((typed, start)) => {
                    request(manifest, program, implementation, typed, start.as_ref())
                }
            };
            let request = match request {
                Ok(request) => request,
                Err(reason) => {
                    out["views"] = json!(
                        implementation
                            .views
                            .iter()
                            .map(|view| {
                                let mut row = view_row(view);
                                not_compared_row(&mut row, &reason);
                                row
                            })
                            .collect::<Vec<_>>()
                    );
                    rows.push(out);
                    continue;
                }
            };
            let bytes = canonical_json(&request).into_bytes();
            out["request_sha256"] = json!(digest(&bytes));
            let limit =
                Duration::from_millis(implementation.time_ms.unwrap_or(manifest.budget.time_ms));
            let answer =
                run_process(&implementation.command, &root, bytes, limit).and_then(|ran| {
                    out["wall_ms"] = json!(ran.wall_ms);
                    let answer = read_answer(&ran.stdout)
                        .map_err(|detail| Failure::new("malformed", detail))?;
                    if let Answer::Ended { cells, .. } = &answer {
                        vocabulary
                            .read_answer(implementation, cells)
                            .map_err(|detail| {
                                Failure::new("malformed", format!("`cells`: {detail}"))
                            })?;
                    }
                    Ok(answer)
                });
            match answer {
                Err(failure) => out["failure"] = failure.value(),
                Ok(answer) => {
                    out["answer"] = answer.value();
                    match view_rows(
                        vocabulary,
                        implementation,
                        &answer,
                        (ends, words),
                        &not_compared,
                    ) {
                        Ok(views) => out["views"] = json!(views),
                        Err(detail) => {
                            document["refusal"] = json!({
                                "stage": "compare",
                                "reason": "front-end",
                                "detail": format!("implementation `{}`, program `{}`: {detail}", implementation.name, program.id),
                            });
                        }
                    }
                }
            }
            rows.push(out);
        }
    }
    document["implementations"] = json!(declared);
    document["programs"] = json!(programs);
    if let Some(stop) = manifest.stop_value() {
        document["stop"] = stop;
    }
    document["result"] = json!({"not_compared": not_compared});
    document["summary"] = summary(&rows);
    document["rows"] = json!(rows);
    if programs_failed(&update) && document["refusal"].is_null() {
        document["cache_error"] = json!(true);
    }
    document
}

/// Whether a program's record could not be written (its row's `cache_error`), which fails the
/// command as it fails `coverage`.
fn programs_failed(update: &crate::results::ResultsUpdate) -> bool {
    update.rows.iter().any(|row| {
        row.row["cache_error"]
            .as_str()
            .is_some_and(|error| error != crate::results::RESULT_CACHE_NO_BUILD)
    })
}

/// A program's typed inputs and, where some implementation is given it, its start or why it has
/// none ([`request_parts`]); `Err` when its inputs have no document.
type RequestParts = Result<(Value, Option<Result<Value, NotCompared>>), String>;

/// The request's typed inputs and, where some selected implementation is given it, the start
/// (or why it has none), for `program`; `Err` when its inputs have no document.
fn request_parts(
    vocabulary: &dyn Vocabulary,
    inputs: &mut crate::admit::InputSession<'_>,
    root: &Path,
    program: &Program,
    row: &ProgramRow,
    start: bool,
) -> RequestParts {
    let mut files = ManifestFiles {
        root,
        document: program.case_file.as_deref().or(program.case.as_deref()),
    };
    let typed = vocabulary
        .inputs(program, &mut files)
        .map_err(|detail| format!("the program's inputs have no document: {detail}"))?;
    if !start {
        return Ok((typed, None));
    }
    let test = match (&row.test, &row.inputs) {
        (Some(test), _) => Ok(test.clone()),
        (None, Some(case)) => inputs
            .test_case(program, case)
            .map_err(|refusal: AdmissionRefusal| refusal.detail),
        (None, None) => Err("the program's inputs cannot be read".to_owned()),
    };
    let unreadable = |detail| {
        NotCompared::Unreadable(format!("the definition's start has no document: {detail}"))
    };
    let start = match test.and_then(|test| inputs.start(&test)) {
        Ok(Some(state)) => vocabulary.start(&state).map_err(unreadable),
        // The clock only cancels: a start it stopped is no answer on this host.
        Ok(None) => Err(NotCompared::Undecided(
            "the clock (budget.time_ms) stopped the definition's depth-0 run: its start is not \
             known on this host"
                .to_owned(),
        )),
        Err(detail) => Err(unreadable(detail)),
    };
    Ok((typed, Some(start)))
}

/// The request to `implementation` for `program` ([`PROTOCOL`]): `{protocol, program, inputs,
/// stop, start}`, `stop` the corpus's count for the program where it has a `[stop]`, `start`
/// where the implementation is given it.
fn request(
    manifest: &FlowManifest,
    program: &Program,
    implementation: &ImplementationSection,
    typed: &Value,
    start: Option<&Result<Value, NotCompared>>,
) -> Result<Value, NotCompared> {
    let mut request = Map::new();
    request.insert("protocol".into(), json!(PROTOCOL));
    request.insert("program".into(), json!(program.id));
    request.insert("inputs".into(), typed.clone());
    if let Some(stop) = &manifest.stop {
        request.insert(
            "stop".into(),
            json!({"count": program.stop_count.unwrap_or(stop.count).get()}),
        );
    }
    if implementation.given == Given::Start {
        match start {
            Some(Ok(start)) => {
                request.insert("start".into(), start.clone());
            }
            Some(Err(reason)) => return Err(reason.clone()),
            None => {
                return Err(NotCompared::Unreadable(
                    "the definition's start was not read".to_owned(),
                ));
            }
        }
    }
    Ok(Value::Object(request))
}

/// The counts of the document's verdicts and failures: `{verdicts: {equal, different,
/// could-not-apply, not-compared}, required: {..the same, of required views}, failures}`.
fn summary(rows: &[Value]) -> Value {
    let mut verdicts = Map::new();
    let mut required = Map::new();
    for verdict in ["equal", "different", "could-not-apply", "not-compared"] {
        let count = |only_required: bool| {
            rows.iter()
                .flat_map(|row| row["views"].as_array().into_iter().flatten())
                .filter(|view| view["verdict"] == verdict)
                .filter(|view| !only_required || view["required"] == true)
                .count()
        };
        verdicts.insert(verdict.into(), json!(count(false)));
        required.insert(verdict.into(), json!(count(true)));
    }
    json!({
        "verdicts": verdicts,
        "required": required,
        "failures": rows.iter().filter(|row| row["failure"].is_object()).count(),
    })
}

/// The `--output text` rendering of a `compare` document: one line per (implementation,
/// program, view) verdict and per failure, then the summary.
///
/// # Errors
///
/// When `document` is no compare document.
pub fn text(document: &Value) -> Result<String, String> {
    if document["schema"] != COMPARE_SCHEMA {
        return Err("--output text renders a compare document only".to_owned());
    }
    let mut text = String::new();
    if let Some(refusal) = document["refusal"].as_object() {
        text.push_str(&format!(
            "refused at {} ({}): {}\n",
            refusal["stage"].as_str().unwrap_or("?"),
            refusal["reason"].as_str().unwrap_or("?"),
            refusal["detail"].as_str().unwrap_or("")
        ));
    }
    if document["spec"]["outcome"] == "refused" {
        text.push_str(&format!(
            "specification refused at {} ({}): {}\n",
            document["spec"]["stage"].as_str().unwrap_or("?"),
            document["spec"]["reason"].as_str().unwrap_or("?"),
            document["spec"]["detail"].as_str().unwrap_or("")
        ));
    }
    for row in document["rows"].as_array().into_iter().flatten() {
        let name = format!(
            "{} {}",
            row["implementation"].as_str().unwrap_or("?"),
            row["program"].as_str().unwrap_or("?")
        );
        if let Some(failure) = row["failure"].as_object() {
            text.push_str(&format!(
                "{name}: failed ({}): {}\n",
                failure["kind"].as_str().unwrap_or("?"),
                failure["detail"].as_str().unwrap_or("")
            ));
            continue;
        }
        for view in row["views"].as_array().into_iter().flatten() {
            let required = if view["required"] == true {
                "required"
            } else {
                "reported"
            };
            let verdict = view["verdict"].as_str().unwrap_or("?");
            let detail = match verdict {
                "different" => view["difference"]["at"]
                    .as_str()
                    .or_else(|| view["difference"]["path"].as_str())
                    .map(|at| format!(" at {at}"))
                    .unwrap_or_default(),
                "could-not-apply" | "not-compared" => view["detail"]
                    .as_str()
                    .map(|detail| format!(": {detail}"))
                    .unwrap_or_default(),
                _ => String::new(),
            };
            text.push_str(&format!(
                "{name} {} ({required}): {verdict}{detail}\n",
                view["view"].as_str().unwrap_or("?")
            ));
        }
    }
    let summary = &document["summary"];
    if summary.is_object() {
        let counts = |member: &str| {
            ["equal", "different", "could-not-apply", "not-compared"]
                .iter()
                .map(|verdict| format!("{} {verdict}", summary[member][*verdict]))
                .collect::<Vec<_>>()
                .join(", ")
        };
        text.push_str(&format!(
            "verdicts: {}; required views: {}; failed runs: {}\n",
            counts("verdicts"),
            counts("required"),
            summary["failures"]
        ));
    }
    Ok(text)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::manifest::ManifestFile;

    const HEAD: &str = "[spec]\nentry = \"calc.k\"\nmain_module = \"CALC\"\n\n";

    fn decoded(implementations: &str) -> Result<FlowManifest, crate::ManifestError> {
        FlowManifest::decode(&format!("{HEAD}{implementations}"), Path::new("."))
    }

    fn error(implementations: &str) -> String {
        decoded(implementations).unwrap_err().to_string()
    }

    const ONE: &str = "[[implementation]]\nname = \"cpu\"\ncommand = [\"bin/cpu\", \
                       \"--kink\"]\ngiven = \"start\"\nomits = [\"k\"]\nidentity = { file = \
                       \"bin/cpu\" }\ntime_ms = 5\nviews = [{ name = \"writes\", views = { bus = \
                       \"WritesView\" }, observer = \"p:views\", required = true }, { name = \
                       \"all\" }]\n";

    #[test]
    fn an_implementation_decodes_with_its_views() {
        let manifest = decoded(ONE).unwrap();
        let [implementation] = manifest.implementations.as_slice() else {
            panic!("{:?}", manifest.implementations);
        };
        assert_eq!(implementation.name, "cpu");
        assert_eq!(implementation.command, ["bin/cpu", "--kink"]);
        assert_eq!(implementation.given, Given::Start);
        assert_eq!(implementation.omits, ["k"]);
        assert_eq!(implementation.identity.as_ref().unwrap().file, "bin/cpu");
        assert_eq!(implementation.time_ms, Some(5));
        assert!(implementation.has_required_view());
        assert_eq!(
            implementation.views[0].value(),
            json!({"name": "writes", "required": true, "views": {"bus": "WritesView"}, "observer": "p:views"})
        );
        assert_eq!(
            implementation.views[1].value(),
            json!({"name": "all", "required": false})
        );
        // An implementation is no input of a run: a manifest without one decodes as before.
        assert!(
            ManifestFile::decode(HEAD, Path::new("."))
                .unwrap()
                .implementations
                .is_empty()
        );
    }

    #[test]
    fn a_declaration_is_refused_naming_its_key() {
        let base = "[[implementation]]\nname = \"x\"\ncommand = [\"x\"]\ngiven = \"inputs\"\n";
        for (text, expected) in [
            (
                format!("{base}views = []\n"),
                "implementation[0].views: names no view",
            ),
            (
                "[[implementation]]\nname = \"x\"\ngiven = \"inputs\"\nviews = [{ name = \"a\" }]\n"
                    .to_owned(),
                "implementation[0].command: missing required key",
            ),
            (
                "[[implementation]]\nname = \"x\"\ncommand = []\ngiven = \"inputs\"\nviews = [{ \
                 name = \"a\" }]\n"
                    .to_owned(),
                "implementation[0].command: expected a nonempty array",
            ),
            (
                "[[implementation]]\nname = \"x\"\ncommand = [\"x\"]\ngiven = \"both\"\nviews = [{ \
                 name = \"a\" }]\n"
                    .to_owned(),
                "implementation[0].given: `both` is no given",
            ),
            (
                format!("{base}views = [{{ name = \"a\" }}, {{ name = \"a\" }}]\n"),
                "implementation[0].views[1].name: `a` is declared twice",
            ),
            (
                format!("{base}views = [{{ name = \"a\", required = \"yes\" }}]\n"),
                "implementation[0].views[0].required: expected a boolean",
            ),
            (
                format!("{base}views = [{{ name = \"a\", compare = [] }}]\n"),
                "implementation[0].views[0].compare: names no cell",
            ),
            (
                format!("{base}views = [{{ name = \"a\", bus = \"WritesView\" }}]\n"),
                "implementation[0].views[0].bus: unknown key",
            ),
            (
                format!("{base}views = [{{ name = \"a\" }}]\nfiles = 1\n"),
                "implementation[0].files: unknown key",
            ),
            (
                format!("{base}views = [{{ name = \"a\" }}]\n\n{base}views = [{{ name = \"a\" }}]\n"),
                "implementation[1].name: `x` is declared twice",
            ),
        ] {
            let error = error(&text);
            assert!(error.starts_with(expected), "{text}\n{error}");
        }
    }

    #[test]
    fn kink_flow_refuses_compare_without_a_vocabulary() {
        let manifest = decoded(ONE).unwrap();
        let document = command(&manifest, &CompareOptions::default(), None);
        assert_eq!(document["schema"], COMPARE_SCHEMA);
        assert_eq!(document["refusal"]["reason"], "unsupported-front-end");
        assert_eq!(compare_status(&document), EXIT_UNASKED);
    }

    #[test]
    fn an_answer_is_read_by_the_protocol() {
        assert_eq!(
            read_answer(br#"{"end": "stopped", "cells": {"pc": 1}}"#),
            Ok(Answer::Ended {
                end: EndWord::Stopped,
                cells: json!({"pc": 1})
            })
        );
        assert_eq!(
            read_answer(b" {\"end\": \"final\", \"cells\": {}}\n"),
            Ok(Answer::Ended {
                end: EndWord::Final,
                cells: json!({})
            })
        );
        assert_eq!(
            read_answer(br#"{"end": "could-not-apply", "reason": "late request"}"#),
            Ok(Answer::CouldNotApply {
                reason: "late request".into()
            })
        );
        for (bytes, expected) in [
            (&b"not json"[..], "stdout is not one JSON document"),
            (b"[]", "the answer is not a JSON object"),
            (
                b"{\"end\": \"final\"}",
                "a `final` answer states its end's `cells`",
            ),
            (
                b"{\"end\": \"final\", \"cells\": {}, \"rule\": \"x\"}",
                "the answer has the key `rule`",
            ),
            (
                b"{\"end\": \"stopped\", \"cells\": {}, \"reason\": \"x\"}",
                "a `stopped` answer gives no `reason`",
            ),
            (
                b"{\"end\": \"could-not-apply\"}",
                "a `could-not-apply` answer gives its",
            ),
            (
                b"{\"end\": \"could-not-apply\", \"reason\": \"x\", \"cells\": {}}",
                "a `could-not-apply` answer states no `cells`",
            ),
            (b"{\"end\": \"stuck\", \"cells\": {}}", "`end` is `stuck`"),
            (
                b"{\"end\": \"final\", \"cells\": 1}",
                "`cells` is not a JSON object",
            ),
        ] {
            let error = read_answer(bytes).unwrap_err();
            assert!(error.starts_with(expected), "{error}");
        }
    }

    #[test]
    fn only_a_required_view_decides_the_status() {
        let view = |required: bool, verdict: &str, status: Value| json!({"required": required, "verdict": verdict, "status": status});
        let row = |views: Vec<Value>, failure: Value, required: bool| json!({"views": views, "failure": failure, "required": required});
        for (row, status) in [
            (
                row(vec![view(true, "equal", Value::Null)], Value::Null, true),
                EXIT_YES,
            ),
            (
                row(
                    vec![
                        view(true, "equal", Value::Null),
                        view(false, "different", Value::Null),
                    ],
                    Value::Null,
                    true,
                ),
                EXIT_YES,
            ),
            (
                row(
                    vec![view(true, "different", Value::Null)],
                    Value::Null,
                    true,
                ),
                EXIT_NO,
            ),
            (
                row(
                    vec![view(true, "could-not-apply", Value::Null)],
                    Value::Null,
                    true,
                ),
                EXIT_YES,
            ),
            (
                row(
                    vec![view(true, "not-compared", json!(3))],
                    Value::Null,
                    true,
                ),
                EXIT_UNANSWERED,
            ),
            (
                row(
                    vec![view(true, "not-compared", json!(2))],
                    Value::Null,
                    true,
                ),
                EXIT_UNASKED,
            ),
            (
                row(
                    vec![view(false, "not-compared", json!(2))],
                    Value::Null,
                    false,
                ),
                EXIT_YES,
            ),
            (row(vec![], json!({"kind": "exit"}), true), EXIT_UNASKED),
            (
                row(vec![], json!({"kind": "timeout"}), true),
                EXIT_UNANSWERED,
            ),
            (row(vec![], json!({"kind": "exit"}), false), EXIT_YES),
        ] {
            assert_eq!(row_status(&row), status, "{row}");
        }
    }

    fn sh(script: &str, limit: Duration) -> Result<Ran, Failure> {
        run_process(
            &["sh".into(), "-c".into(), script.into()],
            Path::new("."),
            b"{\"program\":\"p\"}".to_vec(),
            limit,
        )
    }

    #[test]
    fn a_run_is_its_output_or_a_failure_of_the_implementation() {
        let echoed = sh("cat", Duration::from_secs(60)).unwrap();
        assert_eq!(echoed.stdout, b"{\"program\":\"p\"}");
        // An implementation may answer without reading its request.
        let unread = sh("echo answered", Duration::from_secs(60)).unwrap();
        assert_eq!(unread.stdout, b"answered\n");
        let exited = sh("echo oops >&2; exit 4", Duration::from_secs(60))
            .err()
            .unwrap();
        assert_eq!(
            (exited.kind, exited.exit_code, exited.stderr.as_deref()),
            ("exit", Some(4), Some("oops\n"))
        );
        let cancelled = sh("exec sleep 30", Duration::from_millis(200))
            .err()
            .unwrap();
        assert_eq!(cancelled.kind, "timeout");
        assert_eq!(cancelled.status(), EXIT_UNANSWERED);
        let missing = run_process(
            &["./no-such-implementation".into()],
            Path::new("."),
            Vec::new(),
            Duration::from_secs(60),
        )
        .err()
        .unwrap();
        assert_eq!(missing.kind, "spawn");
    }
}
