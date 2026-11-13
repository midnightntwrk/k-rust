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
//! reported.
//!
//! An implementation of `kink-implementation/2` ([`Protocol::V2`]) may also declare *trace
//! views*, each over channels of the flow's `[observe]`. Its request then has `observe`: each
//! channel a trace view names, with its shape in the front end's vocabulary
//! ([`Vocabulary::observe_request`]) and `positions`, the number of indices from 0 the answer is
//! asked to state: the definition's channel has N elements, and `positions` is N where it is open
//! after them and N + 1 where it is closed after them (its closure is a position, at which an
//! implementation that goes on shows its element). Its answer has `observations`, the elements
//! it states for those channels, and may end in `horizon`: it stated the positions asked and
//! has not ended ([`read_answer_2`]). The definition's side is the values of the baseline run's
//! channels (`BaselineRunner::observed_values`, one more run of the baseline, shown to be the
//! recorded one), so a program whose baseline its bounds cut (`comparable-prefix`) is compared
//! by its trace views, and its end views are `not-compared` (`no-end`).
//! Those values are a function of the baseline's request and the channels asked, so a completed
//! value run's are kept in the cache directory (`definition-traces/`, [`TraceKey`]) under the
//! program's result key and the channels, and read by a later command only for the same
//! observation record; no document says which of the two a command did.
//!
//! A trace view compares elements at equal indices, which is the front end's
//! ([`Vocabulary::judge_trace`]); the verdict is kink-flow's ([`judged_row`]): `equal` only where
//! both sides close every channel after the same elements; `agree-up-to` where nothing differs
//! and some channel was compared only up to a horizon, the row's `horizon` naming per channel
//! how many elements agree and which side states nothing further (`limited_by`: the
//! `definition`, whose run was cut, or the `implementation`, whose answer stops before the
//! positions asked, which leaves a required view unanswered); `different` with the first
//! difference (`kink-trace/1`); `not-compared` where no element was compared
//! (`observed-nothing`), the baseline has several paths (`several-paths`) or an element is not
//! decided (`undecided`).
//!
//! Every verdict is a test of one build on the corpus's programs. A trace verdict also rests on
//! a claim kink cannot check, that the implementation's element k is its state at the
//! definition's point k: its row says so (`correspondence: "implementation-claim"`), as does the
//! document of a flow with an implementation of `/2` (`evidence: "testing"`). No verdict says
//! anything of other programs, of a longer run, or of how two definitions stand to each other.
//!
//! With `--lock FILE` the verdicts are the record's `[compare]` section ([`crate::lock`]), one
//! `[[compare.verdict]]` per (implementation, program, view) in the declarations' order
//! ([`verdict_rows`]), each with the digest of the request and of the implementation's
//! `identity`. A run without `--locked` rewrites it, as `run` and `coverage` rewrite theirs, and
//! `--locked` compares the section the run would write with the file's. A row whose verdict rests
//! on a run that gave no answer (the implementation's run failed or the clock cancelled it, or
//! the clock stopped the definition's baseline or depth-0 run) keeps its recorded value
//! ([`keep`]): no verdict was decided, so none can contradict the record.
//!
//! An implementation that declares `identity` has its answers cached
//! ([`IMPLEMENTATION_ANSWER_VERSION`]): the protocol answer of a run that exited 0 is stored in
//! the result cache (`--cache DIR`) under the protocol, the identity's digest, the command and
//! the request's digest, and a later run with the same four reads it instead of starting the
//! implementation. What the cache trusts
//! is that the same binary, given the same request, gives the same answer. The verdict is
//! computed again from the answer on every run, against the definition's ends and the views as
//! they are then, so an edit of the definition, the corpus or a view is never answered from the
//! cache. Without `identity` nothing says which build answered, and the implementation always
//! runs.

use crate::admit::{InputFiles, admit_spec, case_root};
use crate::cli::{EXIT_NO, EXIT_UNANSWERED, EXIT_UNASKED, EXIT_YES, exit_join};
use crate::clock::Kept;
use crate::lock::{Lock, LockKind, Settle, compare_row_id};
use crate::manifest::{
    FlowManifest, Given, ImplementationSection, ObserveSection, Program, Protocol, ViewSection,
};
use crate::results::{
    BaselineRunner, ProgramRow, ResultClass, cache_directory, current_record,
    record_final_configuration, result_key, result_store, runner_refusal, update_results,
};
use k_rust::kore::{ast::Pattern, parser::parse_pattern};
use kink_campaign::{
    ChannelEnd, ChannelValues, Closure, Element, Opened, Opening, StopSide, ValueElement,
    ValuesEnd, ValuesRefusal,
};
use kink_corpus::Store;
use kink_corpus::admission::{AdmissionRecord, AdmissionRefusal};
use kink_native::execution::SolverProfile;
use kink_patch::{canonical_json, sha256};
use serde_json::{Map, Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    io::{Read, Write},
    path::{Path, PathBuf},
    process::{Command, Stdio},
    sync::{Arc, mpsc},
    time::{Duration, Instant},
};

/// The schema of the `compare` document.
pub const COMPARE_SCHEMA: &str = "kink-flow-compare";
/// The version of the `compare` document: 1, the first; 2 since it has `lock` (`--lock FILE`), a
/// row's `cached` and `clock_stopped`, and a program's `not_cached`; 3 since an implementation
/// may be of a second protocol and declare trace views: the document of a flow with one names
/// `protocols` in place of `protocol` and its `evidence`, a trace view's row has `horizon` and
/// `correspondence` and may have the verdict `agree-up-to`, which its summary then counts, a
/// view may be `not-compared` for `no-end`, `several-paths` or `observed-nothing`, an answer's
/// `end` may be `horizon`, and a lock's changed and kept rows name a `horizon`. The document of
/// a flow of the first protocol's implementations differs from version 2's in `version` only.
/// 4 since an end view of a program the definition ends at a declared `refused` end has the
/// verdict `definition-refused`, whatever the implementation answered, which the summary then
/// counts; the document of a definition that declares no end differs in `version` only.
pub const COMPARE_VERSION: u64 = 4;
/// The protocol a request names (`protocol`) and its answer is read by, unless the
/// implementation declares another ([`Protocol`]).
pub const PROTOCOL: &str = "kink-implementation/1";
/// The format of a trace view's first difference ([`TraceDifference`]).
pub const TRACE_DIFFERENCE_FORMAT: &str = "kink-trace/1";
/// What a trace row's `correspondence` says: that the implementation's element k is its state
/// at the definition's point k is the implementation's claim, which kink does not check.
pub const CORRESPONDENCE: &str = "implementation-claim";
/// What `evidence` says of a compare document: its verdicts are tests of one build on these
/// programs, up to the horizons named.
pub const EVIDENCE: &str = "testing";
/// The format of a cached answer of an implementation (module documentation): a record
/// `{version, protocol, identity_sha256, command, request_sha256, answer}` whose name is the
/// digest of all but `answer`, the implementation's stdout. Every build reads `answer` again by
/// the protocol, so the record holds nothing kink's build decides.
pub const IMPLEMENTATION_ANSWER_VERSION: &str = "kink-flow/implementation-answer/v1";
/// The directory of the result cache that holds the cached answers.
const ANSWERS_DIRECTORY: &str = "implementation-answers";
/// The directory of the definition trace cache in the cache directory: the values of the
/// channels of a program's baseline run ([`TraceKey`]).
const DEFINITION_TRACES_DIRECTORY: &str = "definition-traces";
/// The format and meaning of a definition trace entry (its key's `version` and its digest's
/// domain).
const DEFINITION_TRACE_VERSION: &str = "kink-flow/definition-trace/v1";
/// The most bytes of an implementation's stderr a failure quotes, its end.
const STDERR_QUOTED: usize = 2000;

/// `compare`'s options.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct CompareOptions {
    /// `--only NAME`: compare only these implementations; empty: every one.
    pub only: Vec<String>,
    /// `--cache DIR`: the result cache of the definition's baseline runs, which also holds the
    /// cached answers of the implementations that declare `identity`.
    pub cache: Option<PathBuf>,
    /// `--lock FILE`: the corpus record whose `[compare]` section the command reads and writes.
    pub lock: Option<PathBuf>,
    /// `--locked`: compare the section the run would write with the file's, and write nothing.
    pub locked: bool,
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
    /// The clock (`budget.time_ms`) stopped the definition's depth-0 run, which gives the start:
    /// reason `undecided`, but its row rests on a run the clock stopped (3).
    ClockStopped(String),
    /// The definition's side cannot be stated in the front end's vocabulary (an end or a start
    /// with no document) (2).
    Unreadable(String),
    /// A trace view of a program whose baseline has several paths: its record holds prefix sets
    /// over the paths, and no one sequence of elements to compare an answer's with (3).
    SeveralPaths(String),
    /// A trace view none of whose channels was compared at any index: both sides agree through
    /// no element and state nothing further. A comparison of nothing is no agreement (3).
    ObservedNothing(String),
    /// An end view of a program whose baseline its bounds cut before it ended: the definition
    /// has no end there. `carried`: the same implementation declares a required trace view,
    /// which then carries the program's requirement (0); otherwise the question is open (3).
    NoEnd { detail: String, carried: bool },
}

impl NotCompared {
    /// The reason's name in documents.
    #[must_use]
    pub const fn reason(&self) -> &'static str {
        match self {
            Self::Omitted(_) => "omitted",
            Self::LeftOut(_) => "left-out",
            Self::SeveralEnds(_) => "several-ends",
            Self::Undecided(_) | Self::ClockStopped(_) => "undecided",
            Self::Unreadable(_) => "unreadable",
            Self::SeveralPaths(_) => "several-paths",
            Self::ObservedNothing(_) => "observed-nothing",
            Self::NoEnd { .. } => "no-end",
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
            | Self::ClockStopped(detail)
            | Self::Unreadable(detail)
            | Self::SeveralPaths(detail)
            | Self::ObservedNothing(detail)
            | Self::NoEnd { detail, .. } => detail.clone(),
        }
    }

    /// The status of a required view not compared for this reason: [`EXIT_UNANSWERED`] where
    /// another approach may answer (a view that did not end, several ends), [`EXIT_UNASKED`]
    /// where the declaration or the corpus must change. An end view of a program with no end
    /// ([`Self::NoEnd`]) is [`EXIT_YES`] where a required trace view carries the requirement.
    #[must_use]
    pub const fn status(&self) -> u8 {
        match self {
            Self::SeveralEnds(_)
            | Self::Undecided(_)
            | Self::ClockStopped(_)
            | Self::SeveralPaths(_)
            | Self::ObservedNothing(_)
            | Self::NoEnd { carried: false, .. } => EXIT_UNANSWERED,
            Self::Omitted(_) | Self::LeftOut(_) | Self::Unreadable(_) => EXIT_UNASKED,
            Self::NoEnd { carried: true, .. } => EXIT_YES,
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

    /// What a request asks of another producer for each channel of `channels` (channels of the
    /// flow's `[observe]`, in its order, those the trace views of one implementation name): one
    /// JSON object per channel, in their order, each with `name`, the channel's name, and the
    /// channel's shape in the vocabulary an implementation writes its elements in (its kind, its
    /// components or element with the types their values are documents at, its stuttering mode,
    /// its points as written), and no `positions`, which kink-flow adds per program. The objects
    /// are a function of the definition and the declaration, so a changed declaration is another
    /// request. Asked once per implementation that declares a trace view, before any run.
    ///
    /// # Errors
    ///
    /// Why a channel cannot be asked of an implementation (a component whose values have no
    /// document, a front end that compares no trace): the command is refused, stage
    /// `implementation`, reason `declaration`.
    fn observe_request(&self, channels: &[String]) -> Result<Vec<Value>, String>;

    /// Compare an answer's `observations` with the definition's values under each trace view of
    /// the implementation ([`TraceQuestion`]): [`TraceAnswer::Malformed`] where the answer's
    /// record is no record of the channels asked (the run then failed, `malformed`), else one
    /// [`TraceJudged`] per trace view, in the declaration's order.
    ///
    /// # Errors
    ///
    /// A failure of the comparison itself, which fails the command.
    fn judge_trace(&self, question: &TraceQuestion<'_>) -> Result<TraceAnswer, String>;
}

/// One channel a request asks for (`observe.channels[i]`).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AskedChannel {
    /// The channel's name in `[observe]`.
    pub name: String,
    /// The number of indices from 0 the answer is asked to state: the number of elements the
    /// definition's channel holds where it is open after them, one more where it is closed.
    pub positions: u64,
}

/// One question to the front end: an answer's `observations` against the definition's values,
/// under every trace view of one implementation.
pub struct TraceQuestion<'a> {
    pub implementation: &'a ImplementationSection,
    /// The channels the request asked for, in its order: every channel a trace view of the
    /// implementation names.
    pub channels: &'a [AskedChannel],
    /// The answer's `observations`, as the implementation wrote it. kink-flow has checked only
    /// that it is an object whose `channels` are objects named, once each, exactly as the
    /// request's are; everything else of the record is the front end's to read.
    pub observations: &'a Value,
    /// The definition's side: the values of the baseline run's channels, found by name. It
    /// holds every channel of `channels`, and may hold others. An element is the K the run
    /// read (`Element::Content`), the front end's own document of it (`Element::Evaluated`) or
    /// undecided; a channel ends closed or open ([`ChannelValues::ending`]).
    pub definition: &'a [ChannelValues],
}

/// The front end's reading of an answer's `observations` ([`Vocabulary::judge_trace`]).
#[derive(Clone, Debug, PartialEq)]
pub enum TraceAnswer {
    /// The record is no record of the channels asked: why, naming the place in the document.
    Malformed(String),
    /// One comparison per trace view of the implementation, in the declaration's order.
    Judged(Vec<TraceJudged>),
}

/// The front end's comparison of one trace view: what the two sides' elements at equal indices
/// show. The verdict, its status and its words are kink-flow's ([`judged_row`]).
#[derive(Clone, Debug, PartialEq)]
pub enum TraceJudged {
    /// No decided difference: for each channel of the view, in the view's order, how far the two
    /// sides agree.
    Agree(Vec<ChannelAgreed>),
    /// They differ, first here.
    Different(TraceDifference),
    /// Before any difference an element of one side is not decided: the detail names the
    /// channel, the index and the side.
    Undecided(String),
}

/// How far the two sides of one channel agree ([`TraceJudged::Agree`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ChannelAgreed {
    pub channel: String,
    /// The number of elements compared and equal, from index 0; a closure is not counted.
    pub elements: u64,
    pub reach: TraceReach,
}

/// Where the comparison of one channel ended without a difference.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TraceReach {
    /// Both sides close the channel after the same elements, by the same closure.
    Closed,
    /// After the elements that agree, some side states nothing further (its channel is open
    /// there). `implementation` is the answer's own reason where its channel is open there;
    /// `None` where it states more, or closes there. Whether the definition's channel is open
    /// there is kink-flow's to read, from the values it gave.
    Bounded { implementation: Option<String> },
}

/// The first difference of a trace view. Its document is `{format: "kink-trace/1", channel,
/// kind, index, path, definition, implementation, correspondence}`.
#[derive(Clone, Debug, PartialEq)]
pub struct TraceDifference {
    /// The channel that differs first.
    pub channel: String,
    /// What differs, in the front end's word (a value, a closure).
    pub kind: String,
    /// The index of the differing position.
    pub index: u64,
    /// Where in the element's value, for a difference of values.
    pub path: Option<String>,
    /// The definition's side there: `{element, rule, side, steps}`, or `{closed, ..}` where its
    /// channel closes there; `rule` and `side` are null for an element read at no point.
    pub definition: Value,
    /// The implementation's side there: `{element, count}`, `count` its own `depth`, or
    /// `{closed}` where its channel closes there.
    pub implementation: Value,
}

impl TraceDifference {
    /// The difference's document.
    #[must_use]
    pub fn value(&self) -> Value {
        json!({
            "format": TRACE_DIFFERENCE_FORMAT,
            "channel": self.channel,
            "kind": self.kind,
            "index": self.index,
            "path": self.path,
            "definition": self.definition,
            "implementation": self.implementation,
            "correspondence": CORRESPONDENCE,
        })
    }
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

/// How an answer of either protocol says the run ended.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum StatedEnd {
    /// `stopped` or `final`.
    Ended(EndWord),
    /// `horizon` ([`Protocol::V2`]): it stated the positions asked and has not ended.
    Horizon,
    /// `could-not-apply`, with its reason.
    CouldNotApply(String),
}

/// An answer of either protocol, read ([`read_answer`], [`read_answer_2`]).
#[derive(Clone, Debug, PartialEq)]
pub struct Stated {
    pub end: StatedEnd,
    /// Its end's cells, where it states them.
    pub cells: Option<Value>,
    /// Its `observations` ([`Protocol::V2`]), where the request asked for them.
    pub observations: Option<Value>,
}

impl From<Answer> for Stated {
    fn from(answer: Answer) -> Self {
        match answer {
            Answer::Ended { end, cells } => Self {
                end: StatedEnd::Ended(end),
                cells: Some(cells),
                observations: None,
            },
            Answer::CouldNotApply { reason } => Self {
                end: StatedEnd::CouldNotApply(reason),
                cells: None,
                observations: None,
            },
        }
    }
}

impl Stated {
    /// The answer's `end`, as the protocol writes it.
    #[must_use]
    pub const fn word(&self) -> &'static str {
        match &self.end {
            StatedEnd::Ended(end) => end.as_str(),
            StatedEnd::Horizon => "horizon",
            StatedEnd::CouldNotApply(_) => "could-not-apply",
        }
    }

    /// The answer's member of its row: `{end, reason}` (its cells and its observations are
    /// compared, not shown).
    fn value(&self) -> Value {
        match &self.end {
            StatedEnd::CouldNotApply(reason) => json!({"end": self.word(), "reason": reason}),
            _ => json!({"end": self.word(), "reason": null}),
        }
    }
}

/// What a request asked that decides which members its answer holds ([`read_answer_2`]).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Asked {
    /// The request has `observe`.
    pub observe: bool,
    /// The implementation declares an end view, which compares its end's `cells`.
    pub end_view: bool,
}

/// Read an answer document of [`Protocol::V2`]: a JSON object of `end`, `cells`, `reason` and
/// `observations`, and no other key. `end` is `stopped`, `final`, `horizon` (only to a request
/// with `observe`, and with no `cells`: it has no end) or `could-not-apply` (with a `reason`, a
/// nonempty string, and neither `cells` nor `observations`). A `stopped` or `final` answer
/// states its end's `cells` where the implementation declares an end view, and may state them
/// otherwise. `observations`, an object, is there exactly when the request has `observe` and
/// the answer is not `could-not-apply`: an answer that leaves a requested trace out is no answer
/// to the request, and one that states a trace nobody asked for is of another request.
///
/// # Errors
///
/// Why the bytes are no answer.
pub fn read_answer_2(bytes: &[u8], asked: Asked) -> Result<Stated, String> {
    let protocol = Protocol::V2.as_str();
    let document: Value = serde_json::from_slice(bytes)
        .map_err(|error| format!("stdout is not one JSON document: {error}"))?;
    let Value::Object(mut object) = document else {
        return Err("the answer is not a JSON object".to_owned());
    };
    if let Some(key) = object
        .keys()
        .find(|key| !matches!(key.as_str(), "end" | "cells" | "reason" | "observations"))
    {
        return Err(format!(
            "the answer has the key `{key}`; an answer holds `end`, `cells`, `reason` and \
             `observations` only ({protocol})"
        ));
    }
    let end = object.get("end").and_then(Value::as_str).ok_or(
        "the answer has no `end` string (`stopped`, `final`, `horizon` or `could-not-apply`)",
    )?;
    let end = match end {
        "stopped" => StatedEnd::Ended(EndWord::Stopped),
        "final" => StatedEnd::Ended(EndWord::Final),
        "horizon" => StatedEnd::Horizon,
        "could-not-apply" => {
            for key in ["cells", "observations"] {
                if object.contains_key(key) {
                    return Err(format!("a `could-not-apply` answer states no `{key}`"));
                }
            }
            let reason = object
                .get("reason")
                .and_then(Value::as_str)
                .filter(|reason| !reason.trim().is_empty())
                .ok_or("a `could-not-apply` answer gives its `reason`, a nonempty string")?;
            return Ok(Stated {
                end: StatedEnd::CouldNotApply(reason.to_owned()),
                cells: None,
                observations: None,
            });
        }
        other => {
            return Err(format!(
                "`end` is `{other}`, not `stopped`, `final`, `horizon` or `could-not-apply`"
            ));
        }
    };
    let word = match &end {
        StatedEnd::Ended(end) => end.as_str(),
        _ => "horizon",
    };
    if object.contains_key("reason") {
        return Err(format!("a `{word}` answer gives no `reason`"));
    }
    let cells = match (object.remove("cells"), &end) {
        (Some(_), StatedEnd::Horizon) => {
            return Err(
                "a `horizon` answer states no `cells`: the run has not ended, so it has no end"
                    .to_owned(),
            );
        }
        (Some(cells @ Value::Object(_)), _) => Some(cells),
        (Some(_), _) => return Err("`cells` is not a JSON object".to_owned()),
        (None, StatedEnd::Ended(_)) if asked.end_view => {
            return Err(format!("a `{word}` answer states its end's `cells`"));
        }
        (None, _) => None,
    };
    let observations = match (object.remove("observations"), asked.observe) {
        (Some(observations @ Value::Object(_)), true) => Some(observations),
        (Some(_), true) => return Err("`observations` is not a JSON object".to_owned()),
        (Some(_), false) => {
            return Err(
                "the answer states `observations`, and the request has no `observe`".to_owned(),
            );
        }
        (None, true) => {
            return Err(format!(
                "a `{word}` answer to a request with `observe` states its `observations`"
            ));
        }
        (None, false) => None,
    };
    if end == StatedEnd::Horizon && !asked.observe {
        return Err(
            "`end` is `horizon`, and the request has no `observe`: it asked for no positions"
                .to_owned(),
        );
    }
    Ok(Stated {
        end,
        cells,
        observations,
    })
}

/// Check that an answer's `observations` names the channels the request asked for: an object
/// whose `channels` is an array of objects, each with a `name`, the names being exactly the
/// request's, once each. What each channel holds is the front end's to read
/// ([`Vocabulary::judge_trace`]).
///
/// # Errors
///
/// Why it does not, naming the channel: a requested channel the answer leaves out is no answer
/// about that channel, so the answer is malformed, never a comparison of fewer channels.
pub fn stated_channels(observations: &Value, asked: &[AskedChannel]) -> Result<(), String> {
    let channels = observations["channels"]
        .as_array()
        .ok_or("`channels` is not an array")?;
    let mut names = Vec::new();
    for (index, channel) in channels.iter().enumerate() {
        let name = channel
            .as_object()
            .and_then(|channel| channel.get("name"))
            .and_then(Value::as_str)
            .ok_or_else(|| format!("`channels[{index}]` is no object with a `name` string"))?;
        if !asked.iter().any(|asked| asked.name == name) {
            return Err(format!(
                "`channels[{index}]` is `{name}`, a channel the request did not ask for"
            ));
        }
        if names.contains(&name) {
            return Err(format!("`channels[{index}]`: `{name}` is stated twice"));
        }
        names.push(name);
    }
    match asked
        .iter()
        .find(|asked| !names.contains(&asked.name.as_str()))
    {
        Some(missing) => Err(format!(
            "no channel `{}`, which the request asked for",
            missing.name
        )),
        None => Ok(()),
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
        /// Where an end is of a declared `refused` class (its summary's `declared`,
        /// `crate::evidence`, "Declared ends"), the first such end's item and reason, as a
        /// `definition-refused` verdict's detail states them.
        refused: Option<String>,
    },
    /// The program's baseline was cut by its bounds before it ended (`comparable-prefix`): it
    /// has no end, and its channels' elements up to their horizons, which a trace view compares.
    Prefix { cause: Option<String> },
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
    if class == ResultClass::ComparablePrefix.as_str() {
        return Definition::Prefix {
            cause: row.row["cause"].as_str().map(str::to_owned),
        };
    }
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
    // The first end the definition declares refused, in the order of the record's ends.
    let refused = row.row["ends"]
        .as_array()
        .into_iter()
        .flatten()
        .find(|summary| summary["declared"] == "refused")
        .map(|summary| {
            format!(
                "the definition refuses the program, at its declared end `{}`: `{}`",
                summary["declared_by"].as_str().unwrap_or_default(),
                summary["reason_text"].as_str().unwrap_or_default()
            )
        });
    Definition::Ends {
        ends,
        words,
        refused,
    }
}

/// `views`, the rows of `implementation`'s views on a program whose definition ends at a declared
/// `refused` end (`refused`, the detail), with each end view's verdict `definition-refused`
/// whatever the implementation answered: the definition states no end of the program to compare
/// an answer with, only that it refuses the program, for its reason, which the detail gives.
/// This mirrors `could-not-apply`, the implementation's own refusal, and is an answer as that
/// is. A trace view is kept: the elements before the end are behaviour the definition states.
fn definition_refused(views: &mut [Value], implementation: &ImplementationSection, refused: &str) {
    for (row, view) in views.iter_mut().zip(&implementation.views) {
        if view.is_trace() {
            continue;
        }
        let mut replaced = view_row(view);
        replaced["verdict"] = json!(DEFINITION_REFUSED);
        replaced["detail"] = json!(refused);
        *row = replaced;
    }
}

/// The verdict of an end view on a program the definition refuses ([`definition_refused`]).
pub const DEFINITION_REFUSED: &str = "definition-refused";

/// The definition's observation record of one program, which its trace views are compared
/// against: the `observations` of its baseline row.
enum Observed {
    Record(Value),
    /// The record is of a run with several paths.
    SeveralPaths,
    /// The baseline's record holds none this command can read: why.
    Unreadable(String),
}

/// The observation record of `row`'s baseline: this command's live run, else the stored record,
/// as [`definition_side`] reads the ends.
fn observed_record(
    manifest: &FlowManifest,
    runner: &BaselineRunner<'_>,
    execution: crate::digest::ExecutionDigest,
    program: &Program,
    row: &ProgramRow,
    cache: &Path,
) -> Observed {
    let record = match (&row.test, &row.inputs) {
        (Some(test), _) => runner
            .run(test.clone())
            .baseline
            .and_then(|baseline| baseline.get("observations").cloned()),
        (None, Some(inputs)) => current_record(manifest, execution, program, inputs, cache)
            .and_then(|record| record.get("baseline")?.get("observations").cloned()),
        (None, None) => None,
    };
    match record.filter(Value::is_object) {
        None => Observed::Unreadable(
            "the baseline's record holds no observation record this command can read".to_owned(),
        ),
        Some(record) if record.get("paths").is_some_and(Value::is_object) => Observed::SeveralPaths,
        Some(record) => Observed::Record(record),
    }
}

/// The channels a request asks for, each with its `positions`, from the baseline's observation
/// `record` (kink-campaign `BaselineRecord::value`): a channel that holds N elements is asked
/// for N positions where it is open after them, the definition stating nothing at N, and for
/// N + 1 where it is closed after them by its end or by an undefined state, since the closure is
/// a position: an implementation that goes on shows its element there. A channel closed by a
/// cycle is read as open after its elements (kink-campaign `ChannelValues::ending`), so it is
/// asked for N.
///
/// # Errors
///
/// The record holds no channel of a name asked.
pub fn asked_channels(record: &Value, channels: &[String]) -> Result<Vec<AskedChannel>, String> {
    channels
        .iter()
        .map(|name| {
            let channel = record["channels"]
                .as_array()
                .into_iter()
                .flatten()
                .find(|channel| channel["name"] == name.as_str())
                .ok_or_else(|| {
                    format!("the baseline's observation record holds no channel `{name}`")
                })?;
            let held = channel["elements"].as_array().map_or(0, Vec::len);
            let held = u64::try_from(held).unwrap_or(u64::MAX);
            let positions = match channel["closed"].as_str() {
                Some("end" | "undefined") => held.saturating_add(1),
                _ => held,
            };
            Ok(AskedChannel {
                name: name.clone(),
                positions,
            })
        })
        .collect()
}

/// The channels the trace views of `implementation` name, each once, in `[observe]`'s order.
fn traced_channels(
    implementation: &ImplementationSection,
    observe: Option<&ObserveSection>,
) -> Vec<String> {
    let named = |name: &str| {
        implementation.trace_views().any(|view| {
            view.channels
                .iter()
                .flatten()
                .any(|channel| channel == name)
        })
    };
    observe
        .into_iter()
        .flat_map(ObserveSection::channel_names)
        .filter(|name| named(name))
        .map(str::to_owned)
        .collect()
}

/// The front end's shapes of `channels` ([`Vocabulary::observe_request`]), checked: one object
/// per channel, named as it is, without `positions`.
fn channel_shapes(vocabulary: &dyn Vocabulary, channels: &[String]) -> Result<Vec<Value>, String> {
    let shapes = vocabulary.observe_request(channels)?;
    let named = shapes.len() == channels.len()
        && shapes.iter().zip(channels).all(|(shape, channel)| {
            shape.is_object()
                && shape["name"] == channel.as_str()
                && shape.get("positions").is_none()
        });
    if named {
        Ok(shapes)
    } else {
        Err(format!(
            "the front end gave no shape for each of the channels {}",
            channels
                .iter()
                .map(|channel| format!("`{channel}`"))
                .collect::<Vec<_>>()
                .join(", ")
        ))
    }
}

/// A request's `observe`: `{channels}`, each channel its shape with the `positions` asked.
fn observe_value(shapes: &[Value], asked: &[AskedChannel]) -> Value {
    let channels = shapes
        .iter()
        .zip(asked)
        .map(|(shape, asked)| {
            let mut channel = shape.clone();
            channel["positions"] = json!(asked.positions);
            channel
        })
        .collect::<Vec<_>>();
    json!({"channels": channels})
}

/// The verdict of one end view of one (implementation, program) whose definition has ends.
fn end_view_row(
    vocabulary: &dyn Vocabulary,
    implementation: &ImplementationSection,
    view: &ViewSection,
    stated: &Stated,
    definition: (&BTreeSet<Pattern>, &BTreeSet<&'static str>),
    not_compared: &[String],
) -> Result<Value, String> {
    let (ends, words) = definition;
    let mut row = view_row(view);
    if words.is_empty() {
        not_compared_row(
            &mut row,
            &NotCompared::Unreadable(
                "the baseline's record names no end's halt, so its end's word is not known"
                    .to_owned(),
            ),
        );
    } else if words.len() > 1 {
        not_compared_row(
            &mut row,
            &NotCompared::SeveralEnds(
                "the definition's run ends both at the stop and on its own: one answer against \
                 several ends is a question of inclusion, which compare does not decide"
                    .to_owned(),
            ),
        );
    } else if let Some(word) = words.first().filter(|word| **word != stated.word()) {
        row["verdict"] = json!("different");
        row["difference"] = json!({
            "format": "kink-end/1",
            "at": "end",
            "definition": word,
            "implementation": stated.word(),
        });
    } else {
        let cells = stated
            .cells
            .as_ref()
            .ok_or("an answer an end view compares states no `cells`")?;
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
    Ok(row)
}

/// Why an end view of `implementation` is not compared on a program whose baseline its bounds
/// cut ([`NotCompared::NoEnd`]).
fn no_end(implementation: &ImplementationSection) -> NotCompared {
    let carried = implementation.trace_views().any(|view| view.required);
    NotCompared::NoEnd {
        detail: format!(
            "the definition's run of the program is cut by its bounds before it ends \
             (`comparable-prefix`): it has no end to compare{}",
            if carried {
                "; the implementation's required trace view carries the program"
            } else {
                ""
            }
        ),
        carried,
    }
}

/// The trace side of one (implementation, program) with an answer.
enum TraceSide<'a> {
    /// The implementation's trace views are not compared on the program: why.
    Not(&'a NotCompared),
    /// The front end's comparison of each trace view, in the declaration's order, with the
    /// channels asked and the definition's values.
    Judged {
        judged: Vec<TraceJudged>,
        asked: &'a [AskedChannel],
        definition: &'a [ChannelValues],
    },
}

/// The front end's comparison of each trace view of the question's implementation
/// ([`Vocabulary::judge_trace`]), one per trace view: `Ok(Err)` where the answer's
/// `observations` is malformed.
fn judge_trace(
    vocabulary: &dyn Vocabulary,
    question: &TraceQuestion<'_>,
) -> Result<Result<Vec<TraceJudged>, String>, String> {
    match vocabulary.judge_trace(question)? {
        TraceAnswer::Malformed(detail) => Ok(Err(detail)),
        TraceAnswer::Judged(judged) => {
            let views = question.implementation.trace_views().count();
            if judged.len() == views {
                Ok(Ok(judged))
            } else {
                Err(format!(
                    "the front end compared {} trace views of the {views} the implementation \
                     declares",
                    judged.len()
                ))
            }
        }
    }
}

/// The verdicts of one (implementation, program) with the answer `stated`: the views' rows, in
/// the declaration's order. `ends` is the definition's ends and their words, `None` for a
/// program whose baseline has none (`comparable-prefix`), whose end views are then not compared
/// ([`no_end`]); `trace` is the trace views' side, `None` for an implementation without one.
fn answered_rows(
    vocabulary: &dyn Vocabulary,
    implementation: &ImplementationSection,
    stated: &Stated,
    ends: Option<(&BTreeSet<Pattern>, &BTreeSet<&'static str>)>,
    not_compared: &[String],
    trace: Option<TraceSide<'_>>,
) -> Result<Vec<Value>, String> {
    let (mut judged, not, asked, definition) = match trace {
        Some(TraceSide::Judged {
            judged,
            asked,
            definition,
        }) => (judged.into_iter(), None, asked, definition),
        Some(TraceSide::Not(reason)) => (Vec::new().into_iter(), Some(reason), &[][..], &[][..]),
        None => (Vec::new().into_iter(), None, &[][..], &[][..]),
    };
    let mut rows = Vec::new();
    for view in &implementation.views {
        if let StatedEnd::CouldNotApply(reason) = &stated.end {
            let mut row = view_row(view);
            row["verdict"] = json!("could-not-apply");
            row["detail"] = json!(reason);
            rows.push(row);
            continue;
        }
        rows.push(if view.is_trace() {
            match (not, judged.next()) {
                (Some(reason), _) => {
                    let mut row = view_row(view);
                    not_compared_row(&mut row, reason);
                    row
                }
                (None, Some(judged)) => judged_row(view, judged, asked, definition)?,
                (None, None) => {
                    return Err(format!("the trace view `{}` was not compared", view.name));
                }
            }
        } else if let Some(ends) = ends {
            end_view_row(vocabulary, implementation, view, stated, ends, not_compared)?
        } else {
            let mut row = view_row(view);
            not_compared_row(&mut row, &no_end(implementation));
            row
        });
    }
    Ok(rows)
}

/// `count` elements, as a line says it.
fn elements_agree(count: u64) -> String {
    if count == 1 {
        "1 element agrees".to_owned()
    } else {
        format!("{count} elements agree")
    }
}

/// The row of one trace view from the front end's comparison of it (`judged`), `asked` being the
/// channels the request asked for and `definition` the definition's values (both found by name).
///
/// The verdict is decided here, from how far each channel of the view agrees:
///
/// - `equal`: every channel is compared to both sides' closure. The definition's channel must
///   be closed after exactly the elements that agree; a front end that says so of a channel the
///   definition leaves open is refused, so agreement up to a horizon is never spelled `equal`.
/// - `agree-up-to`: nothing differs and some channel is bounded: after the elements that agree,
///   a side states nothing further. `horizon` names each bounded channel: `{elements,
///   limited_by, definition, implementation}`. It is `limited_by` the `definition` where the
///   definition's channel is open there (`definition`: its opening's name): the answer agrees
///   with everything the definition states. Otherwise the definition states a position the
///   answer does not (`limited_by: "implementation"`, `implementation`: its reason): the
///   question is left open, and the row's status is [`EXIT_UNANSWERED`], so an answer of fewer
///   positions than asked never passes a required view.
/// - `not-compared` (`observed-nothing`): every channel is bounded with no element compared. No
///   position was compared, so nothing agrees.
/// - `different`: the first difference ([`TraceDifference::value`]).
/// - `not-compared` (`undecided`): an element before any difference is not decided.
///
/// # Errors
///
/// The front end's comparison is none of this view against these values: it names another
/// channel, more elements than the definition holds, a closure the definition's channel does not
/// have, or a bound neither side has.
pub fn judged_row(
    view: &ViewSection,
    judged: TraceJudged,
    asked: &[AskedChannel],
    definition: &[ChannelValues],
) -> Result<Value, String> {
    let mut row = view_row(view);
    let names = view.channels.as_deref().unwrap_or_default();
    let agreed = match judged {
        TraceJudged::Undecided(detail) => {
            not_compared_row(&mut row, &NotCompared::Undecided(detail));
            return Ok(row);
        }
        TraceJudged::Different(difference) => {
            if !names.contains(&difference.channel) {
                return Err(format!(
                    "the front end's difference is at `{}`, no channel of the view `{}`",
                    difference.channel, view.name
                ));
            }
            row["verdict"] = json!("different");
            row["difference"] = difference.value();
            return Ok(row);
        }
        TraceJudged::Agree(agreed) => agreed,
    };
    if agreed.len() != names.len()
        || agreed
            .iter()
            .zip(names)
            .any(|(agreed, name)| agreed.channel != *name)
    {
        return Err(format!(
            "the front end's agreement is not one per channel of the view `{}`, in its order",
            view.name
        ));
    }
    let mut horizon = Map::new();
    let mut bounds = Vec::new();
    let mut short = false;
    // Whether some position was compared: an element, or a closure of both sides.
    let mut compared = false;
    for ChannelAgreed {
        channel,
        elements,
        reach,
    } in agreed
    {
        let missing = || format!("the channel `{channel}` was not asked for");
        let values = definition
            .iter()
            .find(|values| values.name == channel)
            .ok_or_else(missing)?;
        let positions = asked
            .iter()
            .find(|asked| asked.name == channel)
            .ok_or_else(missing)?
            .positions;
        let held = u64::try_from(values.elements.len()).unwrap_or(u64::MAX);
        let ending = values.ending();
        match reach {
            TraceReach::Closed => {
                if !matches!(ending, ValuesEnd::End | ValuesEnd::Undefined) || elements != held {
                    return Err(format!(
                        "the front end says `{channel}` agrees to both sides' closure after \
                         {elements} elements, and the definition's channel is not closed there \
                         (it holds {held})"
                    ));
                }
                compared = true;
            }
            TraceReach::Bounded { implementation } => {
                if elements > held {
                    return Err(format!(
                        "the front end says {elements} elements of `{channel}` agree, and the \
                         definition's channel holds {held}"
                    ));
                }
                let opening = match &ending {
                    ValuesEnd::Open { index, opening, .. }
                        if u64::try_from(*index).ok() == Some(elements) =>
                    {
                        Some(opening.name())
                    }
                    _ => None,
                };
                let limited_by = match (opening, &implementation) {
                    (Some(_), _) => "definition",
                    (None, Some(_)) => "implementation",
                    (None, None) => {
                        return Err(format!(
                            "the front end says `{channel}` is bounded after {elements} \
                             elements, where neither side's channel is open"
                        ));
                    }
                };
                compared |= elements > 0;
                short |= limited_by == "implementation";
                bounds.push(match (opening, &implementation) {
                    (Some("bound"), _) => format!(
                        "`{channel}` {}, then the definition's run is cut (bound)",
                        elements_agree(elements)
                    ),
                    (Some(opening), _) => format!(
                        "`{channel}` {}, then the definition's channel is open ({opening})",
                        elements_agree(elements)
                    ),
                    (None, reason) => format!(
                        "`{channel}` {}, then the implementation's channel is open ({}) before \
                         the {positions} positions asked",
                        elements_agree(elements),
                        reason.as_deref().unwrap_or_default()
                    ),
                });
                horizon.insert(
                    channel,
                    json!({
                        "elements": elements,
                        "limited_by": limited_by,
                        "definition": opening,
                        "implementation": implementation,
                    }),
                );
            }
        }
    }
    if horizon.is_empty() {
        row["verdict"] = json!("equal");
    } else if !compared {
        not_compared_row(
            &mut row,
            &NotCompared::ObservedNothing(format!(
                "no element of {} was compared: {}",
                names
                    .iter()
                    .map(|name| format!("`{name}`"))
                    .collect::<Vec<_>>()
                    .join(", "),
                bounds.join("; ")
            )),
        );
    } else {
        row["verdict"] = json!("agree-up-to");
        row["horizon"] = Value::Object(horizon);
        row["detail"] = json!(format!(
            "{}; nothing past it is compared",
            bounds.join("; ")
        ));
        row["status"] = json!(if short { EXIT_UNANSWERED } else { EXIT_YES });
    }
    Ok(row)
}

/// A view's row before its verdict. A trace view's also has `horizon` and says what its verdict
/// rests on ([`CORRESPONDENCE`]); an end view's row has neither key.
fn view_row(view: &ViewSection) -> Value {
    let mut row = json!({
        "view": view.name,
        "required": view.required,
        "verdict": null,
        "difference": null,
        "reason": null,
        "detail": null,
        "omitted": [],
        "status": null,
    });
    if view.is_trace() {
        row["horizon"] = Value::Null;
        row["correspondence"] = json!(CORRESPONDENCE);
    }
    row
}

/// Every view of `implementation` not compared for `reason`.
fn not_compared_rows(implementation: &ImplementationSection, reason: &NotCompared) -> Vec<Value> {
    implementation
        .views
        .iter()
        .map(|view| {
            let mut row = view_row(view);
            not_compared_row(&mut row, reason);
            row
        })
        .collect()
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
/// (`equal`, `could-not-apply` and `definition-refused` [`EXIT_YES`], `different` [`EXIT_NO`], `not-compared` its
/// reason's status, `agree-up-to` its own: [`EXIT_YES`] where the definition limits every
/// horizon, [`EXIT_UNANSWERED`] where the implementation's answer limits one), and of its failure
/// where some view is required. A view that is not
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
                Some("equal" | "could-not-apply" | DEFINITION_REFUSED) => EXIT_YES,
                Some("different") => EXIT_NO,
                Some("not-compared" | "agree-up-to") => view["status"]
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

/// The status of a `compare` document: [`EXIT_UNASKED`] for a refused one (its lock included),
/// else the join of its rows' statuses ([`row_status`]) and its lock's (`stale` [`EXIT_NO`],
/// `undecided` [`EXIT_UNANSWERED`], a failed write [`EXIT_UNASKED`]), as `run`'s and
/// `coverage`'s join theirs.
#[must_use]
pub fn compare_status(document: &Value) -> u8 {
    if document["refusal"].is_object()
        || document["spec"]["outcome"] == "refused"
        || document["cache_error"] == true
        || document["lock"]["outcome"] == "refused"
    {
        return EXIT_UNASKED;
    }
    document["rows"]
        .as_array()
        .into_iter()
        .flatten()
        .map(row_status)
        .fold(crate::cli::lock_status(document), exit_join)
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
/// its `cache_error`, which fails the command as it fails `coverage`. With `options.lock` the
/// record's `[compare]` section is read before anything runs (a record that does not decode, or
/// under `--locked` one of another version, refuses the command; `verb` is the front end's
/// spelling of the command, which the refusal names) and settled after ([`Lock::settle`]): the
/// document's `lock`.
pub fn command(
    manifest: &FlowManifest,
    options: &CompareOptions,
    vocabulary: Option<&dyn Vocabulary>,
    verb: &str,
) -> Value {
    let lock = match options.lock.as_deref() {
        None => None,
        Some(path) => match Lock::read_for(
            path,
            LockKind::Compare,
            None,
            options.locked,
            verb,
            manifest.definition.as_deref(),
        ) {
            Ok(lock) => Some(lock.with_assumed_totals(&manifest.assumed_totals)),
            Err(detail) => return lock_refused(manifest, path, &detail),
        },
    };
    let mut document = compared(manifest, options, vocabulary);
    if let Some(lock) = &lock {
        document["lock"] = if document["refusal"].is_object() || document["spec"].is_null() {
            lock.not_written("refused")
        } else {
            let store = Store::new(cache_directory(manifest, options.cache.as_deref()));
            let settle = Settle {
                locked: options.locked,
                verify: false,
                only: &options.only,
                stopped: false,
            };
            lock.settle(&store, &document, settle).0
        };
    }
    document
}

/// The document of a command whose lock at `path` does not decode: it names the refused lock
/// (`lock: {path, outcome: "refused", detail}`), and has no specification and no row, since the
/// lock is read before anything runs.
fn lock_refused(manifest: &FlowManifest, path: &Path, detail: &str) -> Value {
    let mut document = head(&AdmissionRecord::new(&manifest.spec.entry), None);
    document["spec"] = Value::Null;
    document["lock"] = crate::lock::refused_value(path, detail);
    document
}

/// [`command`] without its lock. The document of a flow some selected implementation of which
/// declares another protocol than [`PROTOCOL`] names the protocols of the selected
/// implementations (`protocols`, in place of `protocol`) and says what its verdicts are
/// (`evidence`, [`EVIDENCE`]); every other document is as it was before a second protocol
/// existed.
fn compared(
    manifest: &FlowManifest,
    options: &CompareOptions,
    vocabulary: Option<&dyn Vocabulary>,
) -> Value {
    let mut document = compared_selected(manifest, options, vocabulary);
    let protocols = manifest
        .implementations
        .iter()
        .filter(|i| options.only.is_empty() || options.only.contains(&i.name))
        .map(|implementation| implementation.protocol.as_str())
        .collect::<BTreeSet<_>>();
    if protocols.iter().any(|protocol| *protocol != PROTOCOL)
        && let Some(members) = document.as_object_mut()
    {
        members.remove("protocol");
        members.insert("protocols".into(), json!(protocols));
        members.insert("evidence".into(), json!(EVIDENCE));
    }
    document
}

/// Why a trace view of a program whose baseline has several paths is not compared.
const SEVERAL_PATHS: &str = "the definition's run of the program has several paths: its record \
     holds the paths' prefix sets and no one sequence of elements, and one answer against several \
     paths is a question of inclusion, which compare does not decide";

/// The values of the channels `channels` of `program`'s baseline run
/// (`BaselineRunner::observed_values`), whose observation record is `observed`: the entry the
/// definition trace cache holds under `key` for that record ([`TraceKey`]), else a value run,
/// whose values are then stored under it.
#[allow(clippy::too_many_arguments)]
fn value_run(
    runner: &BaselineRunner<'_>,
    inputs: &mut crate::admit::InputSession<'_>,
    program: &Program,
    row: &ProgramRow,
    observed: Option<&Observed>,
    channels: &[String],
    key: Option<&TraceKey>,
    store: &Store,
) -> Result<Vec<ChannelValues>, ValuesRefusal> {
    let Some(Observed::Record(record)) = observed else {
        return Err(ValuesRefusal::Capture(
            "the baseline's observation record was not read".to_owned(),
        ));
    };
    cached_values(key, store, record, || {
        let test = match (&row.test, &row.inputs) {
            (Some(test), _) => test.clone(),
            (None, Some(case)) => inputs
                .test_case(program, case)
                .map_err(|refusal| ValuesRefusal::Capture(refusal.detail))?,
            (None, None) => {
                return Err(ValuesRefusal::Capture(
                    "the program's inputs cannot be read".to_owned(),
                ));
            }
        };
        runner.observed_values(test, record, channels)
    })
}

/// The values of the channels of a baseline run whose observation record is `recorded`: the
/// entry stored under `key` for that record, else what `run`, the value run, gives, which is
/// then stored under `key`. Only values are stored: a value run that gave none (it was refused,
/// stopped, or is not the recorded run) leaves no entry, and is made again by the next command.
/// Without a key every call runs.
fn cached_values(
    key: Option<&TraceKey>,
    store: &Store,
    recorded: &Value,
    run: impl FnOnce() -> Result<Vec<ChannelValues>, ValuesRefusal>,
) -> Result<Vec<ChannelValues>, ValuesRefusal> {
    if let Some(values) = key.and_then(|key| key.read(recorded)) {
        return Ok(values);
    }
    let values = run()?;
    if let Some(key) = key {
        key.write(store, recorded, &values);
    }
    Ok(values)
}

/// What stops the trace views of an answer from being compared.
enum Trouble {
    /// The answer's `observations` is malformed: the run failed.
    Malformed(String),
    /// The command fails: the refusal's reason and detail.
    Command(&'static str, String),
}

/// [`compared`]'s document before its protocols are named.
fn compared_selected(
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
    // An implementation's command and identity are a function of one build, beside the flow;
    // the cases its requests state are read from the case root.
    let cases = match case_root(manifest) {
        Ok(cases) => cases,
        Err(refusal) => return refused(manifest, "manifest-directory", refusal.detail),
    };
    let mut declared = Vec::new();
    // Per selected implementation with a trace view: the channels its requests ask for and
    // their shapes, which no program changes.
    let mut traced = Vec::new();
    for implementation in &selected {
        // What of the declaration depends on the flow, before what depends on the definition.
        if let Err(detail) = implementation.declaration(manifest.observe.as_ref()) {
            return refused(
                manifest,
                "declaration",
                format!("implementation `{}`: {detail}", implementation.name),
            );
        }
        if let Err(detail) = vocabulary.check(implementation) {
            return refused(
                manifest,
                "declaration",
                format!("implementation `{}`: {detail}", implementation.name),
            );
        }
        let channels = traced_channels(implementation, manifest.observe.as_ref());
        traced.push(if channels.is_empty() {
            None
        } else {
            match channel_shapes(vocabulary, &channels) {
                Ok(shapes) => Some((channels, shapes)),
                Err(detail) => {
                    return refused(
                        manifest,
                        "declaration",
                        format!("implementation `{}`: {detail}", implementation.name),
                    );
                }
            }
        });
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
    let answers = Store::new(&cache);
    // kink's build where a baseline's result is a function of its key: the definition trace
    // cache is on exactly where the result cache is.
    let build = result_store(manifest.budget.backend_options()).ok();
    // Every channel some selected implementation's trace view names, in `[observe]`'s order: a
    // program's one value run reads them all.
    let observed_channels = manifest
        .observe
        .iter()
        .flat_map(ObserveSection::channel_names)
        .filter(|name| {
            traced
                .iter()
                .flatten()
                .any(|(channels, _)| channels.iter().any(|channel| channel == name))
        })
        .map(str::to_owned)
        .collect::<Vec<_>>();
    let several_paths = NotCompared::SeveralPaths(SEVERAL_PATHS.to_owned());
    let second_protocol = selected
        .iter()
        .any(|implementation| implementation.protocol != PROTOCOL);
    let mut document = head(&record, Some(update.spec_digest.to_string()));
    let mut rows = Vec::new();
    let mut programs = Vec::new();
    for (program, row) in manifest.programs.iter().zip(&update.rows) {
        programs.push(json!({
            "id": program.id,
            "class": row.row["class"],
            "cause": row.row["cause"],
            "cached": row.row["cached"],
            "not_cached": row.row.get("not_cached"),
            "cache_error": row.row.get("cache_error"),
        }));
        // The clock stopped the program's baseline run: it has no end on this host.
        let baseline_stopped = crate::clock::baseline_stopped(&row.row);
        let definition = definition_side(manifest, &runner, update.execution, program, row, &cache);
        // The request's parts every implementation shares: its inputs and the start, each
        // read once.
        let mut shared: Option<RequestParts> = None;
        // The definition's observation record and the values of its channels, each read once,
        // and only where an implementation with a trace view needs it.
        let mut observed: Option<Observed> = None;
        let mut values: Option<Result<Vec<ChannelValues>, ValuesRefusal>> = None;
        for ((implementation, declaration), shapes) in selected.iter().zip(&declared).zip(&traced) {
            let mut out = json!({
                "implementation": implementation.name,
                "program": program.id,
                "required": implementation.has_required_view(),
                "request_sha256": null,
                "answer": null,
                "cached": false,
                "failure": null,
                "wall_ms": null,
                "clock_stopped": null,
                "views": [],
            });
            let ends = match &definition {
                Definition::None { class, cause } => {
                    out["views"] = json!(definition_rows(implementation, class, cause.as_deref()));
                    if baseline_stopped {
                        out["clock_stopped"] = json!("baseline");
                    }
                    rows.push(out);
                    continue;
                }
                // No trace view: nothing of the program is compared, and nothing is asked. An
                // implementation of the first protocol is told so as it was before the second
                // existed.
                Definition::Prefix { cause } if shapes.is_none() => {
                    out["views"] = if implementation.protocol() == Some(Protocol::V2) {
                        json!(not_compared_rows(implementation, &no_end(implementation)))
                    } else {
                        json!(definition_rows(
                            implementation,
                            ResultClass::ComparablePrefix.as_str(),
                            cause.as_deref()
                        ))
                    };
                    if baseline_stopped {
                        out["clock_stopped"] = json!("baseline");
                    }
                    rows.push(out);
                    continue;
                }
                Definition::Prefix { .. } => None,
                Definition::Ends { ends, words, .. } => Some((ends, words)),
            };
            // The channels to ask for with their positions, or why the trace views are not
            // compared on this program; `None` for an implementation without a trace view.
            let trace = shapes.as_ref().map(|(channels, _)| {
                let observed = observed.get_or_insert_with(|| {
                    observed_record(manifest, &runner, update.execution, program, row, &cache)
                });
                match observed {
                    Observed::Record(record) => {
                        asked_channels(record, channels).map_err(NotCompared::Unreadable)
                    }
                    Observed::SeveralPaths => Err(several_paths.clone()),
                    Observed::Unreadable(detail) => Err(NotCompared::Unreadable(detail.clone())),
                }
            });
            let asked = trace.as_ref().and_then(|trace| trace.as_ref().ok());
            let unasked = trace.as_ref().and_then(|trace| trace.as_ref().err());
            let end_views = implementation.views.iter().any(|view| !view.is_trace());
            if let Some(reason) = unasked
                && (ends.is_none() || !end_views)
            {
                // No view can be compared, so nothing is asked: the trace views for their
                // reason, an end view because the definition has no end.
                let views = implementation.views.iter().map(|view| {
                    let mut row = view_row(view);
                    if view.is_trace() {
                        not_compared_row(&mut row, reason);
                    } else {
                        not_compared_row(&mut row, &no_end(implementation));
                    }
                    row
                });
                out["views"] = json!(views.collect::<Vec<_>>());
                rows.push(out);
                continue;
            }
            let parts = shared.get_or_insert_with(|| {
                request_parts(
                    vocabulary,
                    &mut inputs,
                    &cases,
                    program,
                    row,
                    selected.iter().any(|i| i.given == Given::Start),
                )
            });
            let observe = asked
                .zip(shapes.as_ref())
                .map(|(asked, (_, shapes))| observe_value(shapes, asked));
            let request = match parts {
                Err(detail) => Err(NotCompared::Unreadable(detail.clone())),
                Ok((typed, start)) => request(
                    manifest,
                    program,
                    implementation,
                    typed,
                    start.as_ref(),
                    observe,
                ),
            };
            let request = match request {
                Ok(request) => request,
                Err(reason) => {
                    if matches!(reason, NotCompared::ClockStopped(_)) {
                        out["clock_stopped"] = json!("start");
                    }
                    out["views"] = json!(not_compared_rows(implementation, &reason));
                    rows.push(out);
                    continue;
                }
            };
            let bytes = canonical_json(&request).into_bytes();
            let request_sha256 = digest(&bytes);
            out["request_sha256"] = json!(request_sha256);
            let limit =
                Duration::from_millis(implementation.time_ms.unwrap_or(manifest.budget.time_ms));
            // Where the implementation names its build, the answer of an earlier run of the same
            // build on the same request (module documentation).
            let key = declaration["identity"]["sha256"]
                .as_str()
                .map(|identity| AnswerKey::new(implementation, identity, &request_sha256));
            let cached = key.as_ref().and_then(|key| key.read(&answers));
            out["cached"] = json!(cached.is_some());
            let stdout = match cached {
                Some(stdout) => Ok(stdout),
                None => run_process(&implementation.command, &root, bytes, limit).map(|ran| {
                    out["wall_ms"] = json!(ran.wall_ms);
                    ran.stdout
                }),
            };
            let fresh = out["cached"] == false;
            let asks = Asked {
                observe: asked.is_some(),
                end_view: end_views,
            };
            let answer = stdout.and_then(|stdout| {
                // Each answer is read by its implementation's protocol, so an answer of the
                // second is never read as one of the first, nor the reverse.
                let stated = match implementation.protocol() {
                    Some(Protocol::V2) => read_answer_2(&stdout, asks),
                    _ => read_answer(&stdout).map(Stated::from),
                }
                .map_err(|detail| Failure::new("malformed", detail))?;
                if fresh && let Some(key) = &key {
                    // A cache that cannot be written costs the next run a start, nothing else.
                    key.write(&answers, &stdout);
                }
                if let Some(cells) = &stated.cells {
                    vocabulary
                        .read_answer(implementation, cells)
                        .map_err(|detail| {
                            Failure::new("malformed", format!("`cells`: {detail}"))
                        })?;
                }
                if let (Some(asked), Some(observations)) = (asked, &stated.observations) {
                    stated_channels(observations, asked).map_err(|detail| {
                        Failure::new("malformed", format!("`observations`: {detail}"))
                    })?;
                }
                Ok(stated)
            });
            match answer {
                Err(failure) => {
                    if failure.kind == "timeout" {
                        out["clock_stopped"] = json!("implementation");
                    }
                    out["failure"] = failure.value();
                }
                Ok(stated) => {
                    // The trace views' side: the front end's comparison of the answer's
                    // observations with the values of the definition's channels, which one
                    // more run of the program's baseline reads, once per program.
                    let side = match (unasked, asked, &stated.observations) {
                        (Some(reason), ..) => Ok(Some(TraceSide::Not(reason))),
                        (None, Some(asked), Some(observations)) => {
                            let definition = values.get_or_insert_with(|| {
                                let key = trace_key(
                                    manifest,
                                    build,
                                    update.execution,
                                    program,
                                    row,
                                    &cache,
                                    &observed_channels,
                                );
                                value_run(
                                    &runner,
                                    &mut inputs,
                                    program,
                                    row,
                                    observed.as_ref(),
                                    &observed_channels,
                                    key.as_ref(),
                                    &answers,
                                )
                            });
                            match definition {
                                Err(ValuesRefusal::SeveralPaths) => {
                                    Ok(Some(TraceSide::Not(&several_paths)))
                                }
                                Err(ValuesRefusal::Capture(why)) => Err(Trouble::Command(
                                    "trace-capture",
                                    format!("trace-capture:{}: {why}", program.id),
                                )),
                                Ok(definition) => {
                                    let question = TraceQuestion {
                                        implementation,
                                        channels: asked,
                                        observations,
                                        definition,
                                    };
                                    match judge_trace(vocabulary, &question) {
                                        Err(detail) => Err(Trouble::Command(
                                            "front-end",
                                            format!(
                                                "implementation `{}`, program `{}`: {detail}",
                                                implementation.name, program.id
                                            ),
                                        )),
                                        Ok(Err(detail)) => Err(Trouble::Malformed(detail)),
                                        Ok(Ok(judged)) => Ok(Some(TraceSide::Judged {
                                            judged,
                                            asked,
                                            definition,
                                        })),
                                    }
                                }
                            }
                        }
                        // An answer of `could-not-apply`, or an implementation with no trace
                        // view.
                        _ => Ok(None),
                    };
                    match side {
                        Err(Trouble::Malformed(detail)) => {
                            out["failure"] =
                                Failure::new("malformed", format!("`observations`: {detail}"))
                                    .value();
                        }
                        Err(Trouble::Command(reason, detail)) => {
                            out["answer"] = stated.value();
                            document["refusal"] = json!({
                                "stage": "compare",
                                "reason": reason,
                                "detail": detail,
                            });
                        }
                        Ok(side) => {
                            out["answer"] = stated.value();
                            match answered_rows(
                                vocabulary,
                                implementation,
                                &stated,
                                ends,
                                &not_compared,
                                side,
                            ) {
                                Ok(mut views) => {
                                    if let Definition::Ends {
                                        refused: Some(refused),
                                        ..
                                    } = &definition
                                    {
                                        definition_refused(&mut views, implementation, refused);
                                    }
                                    out["views"] = json!(views);
                                }
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
    document["summary"] = summary(&rows, second_protocol);
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
    cases: &crate::manifest::CaseRoot,
    program: &Program,
    row: &ProgramRow,
    start: bool,
) -> RequestParts {
    let mut files = cases.case_files(program);
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
        Ok(None) => Err(NotCompared::ClockStopped(
            "the clock (budget.time_ms) stopped the definition's depth-0 run: its start is not \
             known on this host"
                .to_owned(),
        )),
        Err(detail) => Err(unreadable(detail)),
    };
    Ok((typed, Some(start)))
}

/// The request to `implementation` for `program`: `{protocol, program, inputs, stop, start,
/// observe}`, `protocol` the implementation's, `stop` the corpus's count for the program where
/// it has a `[stop]`, `start` where the implementation is given it, and `observe`
/// ([`observe_value`]) where a trace is asked of it, which only a request of [`Protocol::V2`]
/// is. A request of [`PROTOCOL`] is what it was before a second protocol existed.
fn request(
    manifest: &FlowManifest,
    program: &Program,
    implementation: &ImplementationSection,
    typed: &Value,
    start: Option<&Result<Value, NotCompared>>,
    observe: Option<Value>,
) -> Result<Value, NotCompared> {
    let mut request = Map::new();
    request.insert("protocol".into(), json!(implementation.protocol));
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
    if let Some(observe) = observe {
        request.insert("observe".into(), observe);
    }
    Ok(Value::Object(request))
}

/// Where a cached answer of an implementation is, and what it is the answer to: its protocol,
/// the digest of the implementation's `identity` file, its command and the request's digest
/// (module documentation). A run with the same four reads the answer instead of starting the
/// implementation.
struct AnswerKey {
    record: Value,
    name: String,
}

impl AnswerKey {
    fn new(implementation: &ImplementationSection, identity: &str, request_sha256: &str) -> Self {
        let record = json!({
            "version": IMPLEMENTATION_ANSWER_VERSION,
            "protocol": implementation.protocol,
            "identity_sha256": identity,
            "command": implementation.command,
            "request_sha256": request_sha256,
        });
        let name = digest(canonical_json(&record).as_bytes());
        Self { record, name }
    }

    fn path(&self, store: &Store) -> PathBuf {
        store
            .root()
            .join(ANSWERS_DIRECTORY)
            .join(format!("{}.json", self.name))
    }

    /// The cached stdout, where a record of this key is stored and names the same four; `None`
    /// otherwise, so a record that does not read is answered by a run.
    fn read(&self, store: &Store) -> Option<Vec<u8>> {
        let mut record = store.read_json(&self.path(store)).ok()?;
        let answer = record.as_object_mut()?.remove("answer")?;
        (record == self.record).then(|| answer.as_str().map(|text| text.as_bytes().to_vec()))?
    }

    /// Store `stdout`, an answer the protocol reads (so UTF-8 text), under this key; a write that
    /// fails is left unreported, since it only costs the next run a start.
    fn write(&self, store: &Store, stdout: &[u8]) {
        let Ok(answer) = std::str::from_utf8(stdout) else {
            return;
        };
        let mut record = self.record.clone();
        record["answer"] = json!(answer);
        let path = self.path(store);
        if let Some(parent) = path.parent() {
            let _ = std::fs::create_dir_all(parent);
        }
        let _ = store.write_json(&path, &record);
    }
}

/// Where the definition trace cache keeps the values of a program's channels, and what they are
/// the values of: the program's result key (kink's build and identity, the execution digest,
/// the program, the budget, the program's stop, the syntax selection and the `[observe]`
/// declaration: what its baseline run is a function of) and the names of the channels asked, in
/// the order asked. A value run is that baseline run with a probe that also keeps the values of
/// those channels' elements, so its values are a function of the two.
struct TraceKey {
    key: Value,
    path: PathBuf,
}

impl TraceKey {
    /// The key of the channels `channels` of the run `result` (a result key) names, in the
    /// cache directory `cache`. The key decides what an entry may be used for; the path only
    /// finds it.
    fn new(cache: &Path, result: &Value, channels: &[String]) -> Self {
        let key = json!({
            "version": DEFINITION_TRACE_VERSION,
            "result": result,
            "channels": channels,
        });
        let path = cache
            .join(DEFINITION_TRACES_DIRECTORY)
            .join(format!("{}.json", digest(canonical_json(&key).as_bytes())));
        Self { key, path }
    }

    /// The values stored under this key for the run whose observation record is `recorded`;
    /// `None` where there is no entry, where the entry does not read (it is no record of this
    /// key, or does not carry its own digest: `crate::memo`'s record), and where it is not of
    /// `recorded` ([`stored_values`]). Such an entry is answered by a value run, whose values
    /// replace it.
    fn read(&self, recorded: &Value) -> Option<Vec<ChannelValues>> {
        let entry = crate::memo::read(&self.path, DEFINITION_TRACE_VERSION, &self.key)?;
        let channels = self.key["channels"].as_array()?;
        stored_values(&entry, recorded, channels)
    }

    /// Store `values`, the values of a value run whose record is `recorded`, under this key,
    /// where every element has a text form ([`values_entry`]); a write that fails is left
    /// unreported, since it only costs the next command a value run.
    fn write(&self, store: &Store, recorded: &Value, values: &[ChannelValues]) {
        if let Some(entry) = values_entry(recorded, values) {
            crate::memo::write(
                store,
                &self.path,
                DEFINITION_TRACE_VERSION,
                &self.key,
                &entry,
            );
        }
    }
}

/// The key of the definition trace cache for the channels `channels` of `program`'s baseline
/// run, whose row is `row`: `None` where the result cache is off (`build` is none,
/// `results::result_store`), where the program has no digest, and where its result is not kept
/// (its row's `not_cached`: the result is then not a function of its key, so neither is a value
/// run of it). The values are then read by a value run on every command.
fn trace_key(
    manifest: &FlowManifest,
    build: Option<kink_patch::Sha256Digest>,
    execution: crate::digest::ExecutionDigest,
    program: &Program,
    row: &ProgramRow,
    cache: &Path,
    channels: &[String],
) -> Option<TraceKey> {
    let kept = |name| row.row.get(name).is_none_or(Value::is_null);
    if !(kept("not_cached") && kept("cache_error")) {
        return None;
    }
    let result = result_key(
        execution,
        row.digest?,
        manifest.budget,
        Some(build?),
        manifest.program_stop(program),
        manifest
            .syntax
            .as_ref()
            .map(crate::manifest::SyntaxSelection::key_value),
        manifest.observe_value(),
    );
    Some(TraceKey::new(cache, &result, channels))
}

/// The digest of an observation record, as a definition trace entry names the run it is of.
fn recorded_digest(recorded: &Value) -> String {
    digest(canonical_json(recorded).as_bytes())
}

/// The entry of the definition trace cache for `values`, the values of a value run whose
/// observation record is `recorded`: `{recorded_sha256, channels: [{name, elements, closed,
/// open}]}`, `recorded_sha256` the digest of `recorded`, `closed` and `open` the channel's end as
/// the record writes it (kink-campaign `BaselineRecord::value`), and each element `{depth,
/// point, value}`: `point` `{rule, side}` or null, and `value` the front end's document of the
/// element, absent for an undecided element.
///
/// `None` where some element is of kink's own contents (`Element::Content`): KORE patterns,
/// which have no text form this record and its reader agree on, so such a run is not stored.
fn values_entry(recorded: &Value, values: &[ChannelValues]) -> Option<Value> {
    let channels = values
        .iter()
        .map(|channel| {
            let elements = channel
                .elements
                .iter()
                .map(|element| {
                    let mut out = Map::new();
                    out.insert("depth".into(), json!(element.depth));
                    out.insert(
                        "point".into(),
                        element.point.as_ref().map_or(
                            Value::Null,
                            |(rule, side)| json!({"rule": &**rule, "side": side_name(*side)}),
                        ),
                    );
                    match &element.element {
                        Element::Evaluated(value) => {
                            out.insert("value".into(), value.clone());
                        }
                        Element::Undecided => {}
                        // A closure is no element of a value run; a content has no text form.
                        Element::Content(_)
                        | Element::End
                        | Element::Undefined
                        | Element::Cycle => {
                            return None;
                        }
                    }
                    Some(Value::Object(out))
                })
                .collect::<Option<Vec<_>>>()?;
            let (closed, open) = match &channel.end {
                ChannelEnd::Closed(closure) => (json!(closure.name()), Value::Null),
                ChannelEnd::Open(Opened { opening, reason }) => (
                    Value::Null,
                    json!({
                        "index": elements.len(),
                        "opening": opening.name(),
                        "reason": reason,
                    }),
                ),
            };
            Some(json!({
                "name": channel.name,
                "elements": elements,
                "closed": closed,
                "open": open,
            }))
        })
        .collect::<Option<Vec<_>>>()?;
    Some(json!({"recorded_sha256": recorded_digest(recorded), "channels": channels}))
}

/// The record name of a point's side.
const fn side_name(side: StopSide) -> &'static str {
    match side {
        StopSide::Before => "before",
        StopSide::After => "after",
    }
}

/// The values `entry` ([`values_entry`]) holds of the channels named `names`, in their order,
/// where it is an entry of the run whose observation record is `recorded`: it names that
/// record's digest, and holds exactly the channels asked, each with the end the record gives it
/// (`closed` and `open`, as the record writes them), one element per element of the record, and
/// a value exactly where the record holds a digest. `None` otherwise: the entry is of another
/// run or is not what this build writes, and nothing of it is used.
fn stored_values(entry: &Value, recorded: &Value, names: &[Value]) -> Option<Vec<ChannelValues>> {
    if entry["recorded_sha256"].as_str()? != recorded_digest(recorded) {
        return None;
    }
    let stored = entry["channels"].as_array()?;
    if stored.len() != names.len() {
        return None;
    }
    stored
        .iter()
        .zip(names)
        .map(|(channel, name)| {
            let name = name.as_str()?;
            let record = recorded["channels"]
                .as_array()?
                .iter()
                .find(|record| record["name"] == name)?;
            if channel["name"] != name
                || channel["closed"] != record["closed"]
                || channel["open"] != record["open"]
            {
                return None;
            }
            let end = match (channel["closed"].as_str(), &channel["open"]) {
                (Some(closed), Value::Null) => ChannelEnd::Closed(
                    [Closure::End, Closure::Undefined, Closure::Cycle]
                        .into_iter()
                        .find(|closure| closure.name() == closed)?,
                ),
                (None, open) => ChannelEnd::Open(Opened {
                    opening: [
                        Opening::Bound,
                        Opening::UndecidedElement,
                        Opening::Branch,
                        Opening::UndecidedPath,
                        Opening::NotAppended,
                        Opening::Cycle,
                    ]
                    .into_iter()
                    .find(|opening| open["opening"] == opening.name())?,
                    reason: open["reason"].as_str()?.to_owned(),
                }),
                _ => return None,
            };
            let digests = record["elements"].as_array()?;
            let elements = channel["elements"].as_array()?;
            if elements.len() != digests.len() {
                return None;
            }
            let elements = elements
                .iter()
                .zip(digests)
                .map(|(element, digest)| {
                    let members = element.as_object()?;
                    let value = members.get("value");
                    // A value is the value of the element whose digest the record holds.
                    if value.is_some() == digest.is_null() {
                        return None;
                    }
                    let point = match members.get("point")? {
                        Value::Null => None,
                        point => Some((
                            Arc::from(point["rule"].as_str()?),
                            match point["side"].as_str()? {
                                "before" => StopSide::Before,
                                "after" => StopSide::After,
                                _ => return None,
                            },
                        )),
                    };
                    Some(ValueElement {
                        element: value.map_or(Element::Undecided, |value| {
                            Element::Evaluated(value.clone())
                        }),
                        depth: members.get("depth")?.as_u64()?,
                        point,
                    })
                })
                .collect::<Option<Vec<_>>>()?;
            Some(ChannelValues {
                name: name.to_owned(),
                elements,
                end,
            })
        })
        .collect()
}

/// The verdict rows a compare document's `[compare]` section holds, as it writes them: one per
/// (implementation, program, view) that has a verdict, implementation by implementation in the
/// manifest's order, each implementation's programs in the corpus's order and each program's
/// views in the declaration's: `{id, implementation, program, view, required, verdict, reason,
/// difference, request_sha256, identity_sha256}`. `reason` is a `not-compared` verdict's reason
/// and a `could-not-apply` verdict's own (the implementation's words); `difference` is a
/// `different` verdict's first difference as canonical JSON, a text that is a function of the
/// difference; `identity_sha256` is null for an implementation that declares no `identity`. An
/// `agree-up-to` verdict's row also has `horizon`, its horizon as canonical JSON; no other row
/// has the key. A row of a run that gave no answer has no verdict, so it has none here.
#[must_use]
pub fn verdict_rows(document: &Value) -> Vec<Value> {
    let rows = document["rows"].as_array().map_or(&[][..], Vec::as_slice);
    let mut verdicts = Vec::new();
    for implementation in document["implementations"].as_array().into_iter().flatten() {
        let name = implementation["name"].as_str().unwrap_or_default();
        let identity = &implementation["identity"]["sha256"];
        for row in rows.iter().filter(|row| row["implementation"] == name) {
            let program = row["program"].as_str().unwrap_or_default();
            for view in row["views"].as_array().into_iter().flatten() {
                let verdict = view["verdict"].as_str().unwrap_or_default();
                let reason = match verdict {
                    "not-compared" => view["reason"].clone(),
                    "could-not-apply" | DEFINITION_REFUSED => view["detail"].clone(),
                    _ => Value::Null,
                };
                let difference = if view["difference"].is_null() {
                    Value::Null
                } else {
                    json!(canonical_json(&view["difference"]))
                };
                let name_of_view = view["view"].as_str().unwrap_or_default();
                let mut verdict = json!({
                    "id": compare_row_id(name, program, name_of_view),
                    "implementation": name,
                    "program": program,
                    "view": name_of_view,
                    "required": view["required"] == true,
                    "verdict": verdict,
                    "reason": reason,
                    "difference": difference,
                    "request_sha256": row["request_sha256"],
                    "identity_sha256": identity,
                });
                if !view["horizon"].is_null() {
                    verdict["horizon"] = json!(canonical_json(&view["horizon"]));
                }
                verdicts.push(verdict);
            }
        }
    }
    verdicts
}

/// `document` with its `verdicts` ([`verdict_rows`]) as the `[compare]` section of `lock` is
/// compared with and written as, and what of it no run decided (the clock's rule, README "What
/// decides a verdict", applied to `compare`).
///
/// A row of (implementation, program) is decided on this host only when the runs it rests on
/// gave an answer: the implementation's run (a failure of it, the clock's cancellation included,
/// gives none) and the definition's baseline run and, for `given = "start"`, depth-0 run, which
/// the clock can stop. Where one gave none, the verdict of each view is what that run would have
/// given, which this host does not know, so the recorded rows of the pair are kept as they are
/// and the run's own rows are not written: `kept` names each recorded row a stopped definition
/// run gave another verdict on this host, `stopped` each run the clock stopped
/// (`{program, run: "baseline"}` once per program, `{implementation, program, run: "start" |
/// "implementation"}`), and `failed` each failed run of an implementation (`{implementation,
/// program, failure}`). A pair the lock records nothing for has its live rows, those of a run
/// that failed none. Under `--locked` a section that differs in nothing else is `undecided`.
#[must_use]
pub fn keep(lock: &Lock, document: &Value) -> Kept {
    let live = verdict_rows(document);
    // The recorded rows by (implementation, program), each with its id, in the file's order.
    let mut recorded: BTreeMap<(String, String), Vec<Value>> = BTreeMap::new();
    if let Some(table) = lock.recorded_table() {
        for row in table
            .get(LockKind::Compare.row())
            .and_then(toml::Value::as_array)
            .into_iter()
            .flatten()
        {
            let Ok(mut value) = serde_json::to_value(row) else {
                continue;
            };
            let field = |key: &str| value[key].as_str().unwrap_or_default().to_owned();
            let (implementation, program) = (field("implementation"), field("program"));
            value["id"] = json!(compare_row_id(&implementation, &program, &field("view")));
            recorded
                .entry((implementation, program))
                .or_default()
                .push(value);
        }
    }
    let mut stopped = Vec::new();
    let mut failed = Vec::new();
    let mut undecided = BTreeSet::new();
    for row in document["rows"].as_array().into_iter().flatten() {
        let (implementation, program) = (&row["implementation"], &row["program"]);
        let pair = (
            implementation.as_str().unwrap_or_default().to_owned(),
            program.as_str().unwrap_or_default().to_owned(),
        );
        match row["clock_stopped"].as_str() {
            Some("baseline") => {
                let entry = json!({"program": program, "run": "baseline"});
                if !stopped.contains(&entry) {
                    stopped.push(entry);
                }
            }
            Some(run) => stopped.push(json!({
                "implementation": implementation,
                "program": program,
                "run": run,
            })),
            None if row["failure"].is_object() => failed.push(json!({
                "implementation": implementation,
                "program": program,
                "failure": row["failure"]["kind"],
            })),
            None => continue,
        }
        undecided.insert(pair);
    }
    // What a lock compares of a row: a horizon only where the row has one, so a row without
    // one is compared, and reported, as it was before a verdict had a horizon.
    let compared = |row: &Value| {
        let mut compared = json!({"verdict": row["verdict"], "reason": row["reason"],
               "difference": row["difference"]});
        if let Some(horizon) = row.get("horizon").filter(|horizon| !horizon.is_null()) {
            compared["horizon"] = horizon.clone();
        }
        compared
    };
    let mut verdicts = Vec::new();
    let mut kept = Vec::new();
    let pairs = document["implementations"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|implementation| implementation["name"].as_str())
        .flat_map(|implementation| {
            document["programs"]
                .as_array()
                .into_iter()
                .flatten()
                .filter_map(|program| program["id"].as_str())
                .map(move |program| (implementation.to_owned(), program.to_owned()))
        });
    for pair in pairs {
        let own = live.iter().filter(|row| {
            row["implementation"] == pair.0.as_str() && row["program"] == pair.1.as_str()
        });
        match recorded.get(&pair).filter(|_| undecided.contains(&pair)) {
            Some(rows) => {
                for row in rows {
                    let now = own.clone().find(|live| live["id"] == row["id"]);
                    if let Some(now) = now.filter(|now| compared(now) != compared(row)) {
                        let mut entry =
                            LockKind::Compare.keyed(row["id"].as_str().unwrap_or_default());
                        entry.insert("recorded".into(), compared(row));
                        entry.insert("now".into(), compared(now));
                        kept.push(Value::Object(entry));
                    }
                    verdicts.push(row.clone());
                }
            }
            None => verdicts.extend(own.cloned()),
        }
    }
    let mut document = document.clone();
    document["verdicts"] = json!(verdicts);
    Kept {
        document,
        stopped,
        kept,
        failed,
    }
}

/// The lines `kink-flow` prints on stderr for a compare document's lock some row of which rests
/// on a run that gave no answer ([`keep`]): one per run the clock stopped and per failed run of
/// an implementation, then one per kept row (`lock.clock_stopped`, `lock.failed`, `lock.kept`).
#[must_use]
pub fn clock_lines(document: &Value) -> Vec<String> {
    let lock = &document["lock"];
    let path = lock["path"].as_str().unwrap_or(crate::lock::LOCK_FILE);
    let text = |value: &Value| value.as_str().unwrap_or("?").to_owned();
    let mut lines = Vec::new();
    for stop in lock["clock_stopped"].as_array().into_iter().flatten() {
        let program = text(&stop["program"]);
        let implementation = text(&stop["implementation"]);
        lines.push(match stop["run"].as_str() {
            Some("baseline") => format!(
                "{path}: the clock (budget.time_ms) stopped the baseline run of {program}: its \
                 compare rows are not decided on this host"
            ),
            Some("start") => format!(
                "{path}: {implementation} {program}: the clock (budget.time_ms) stopped the \
                 definition's depth-0 run, which gives the start: its rows are not decided on \
                 this host"
            ),
            _ => format!(
                "{path}: {implementation} {program}: the clock (time_ms) cancelled the \
                 implementation's run: its rows are not decided on this host"
            ),
        });
    }
    for failure in lock["failed"].as_array().into_iter().flatten() {
        lines.push(format!(
            "{path}: {} {}: the implementation's run failed ({}) and gave no answer: its rows \
             are not decided on this host",
            text(&failure["implementation"]),
            text(&failure["program"]),
            text(&failure["failure"])
        ));
    }
    let verdict = |side: &Value| match side["reason"].as_str() {
        Some(reason) => format!("{} ({reason})", text(&side["verdict"])),
        None => text(&side["verdict"]),
    };
    for entry in lock["kept"].as_array().into_iter().flatten() {
        lines.push(format!(
            "{path}: {}: kept {} unverified: this host gives {}",
            LockKind::Compare.named(entry),
            verdict(&entry["recorded"]),
            verdict(&entry["now"])
        ));
    }
    lines
}

/// The verdicts a summary counts, in the order its line gives them; `agree-up-to` only in the
/// document of a flow with an implementation of a second protocol (`second_protocol`), since
/// only a trace view has that verdict.
fn counted(second_protocol: bool) -> impl Iterator<Item = &'static str> {
    [
        "equal",
        "agree-up-to",
        "different",
        "could-not-apply",
        "not-compared",
    ]
    .into_iter()
    .filter(move |verdict| second_protocol || *verdict != "agree-up-to")
}

/// The counts of the document's verdicts and failures: `{verdicts: {equal, different,
/// could-not-apply, not-compared}, required: {..the same, of required views}, failures}`, each
/// with `agree-up-to` under `second_protocol` ([`counted`]) and with `definition-refused` where
/// some view has that verdict.
fn summary(rows: &[Value], second_protocol: bool) -> Value {
    let mut verdicts = Map::new();
    let mut required = Map::new();
    for verdict in counted(second_protocol) {
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
    // Only a definition that declares ends refuses a program, so the count is there where some
    // view is `definition-refused`, and a summary without one is the one it was.
    let refused = |only_required: bool| {
        rows.iter()
            .flat_map(|row| row["views"].as_array().into_iter().flatten())
            .filter(|view| view["verdict"] == DEFINITION_REFUSED)
            .filter(|view| !only_required || view["required"] == true)
            .count()
    };
    if refused(false) > 0 {
        verdicts.insert(DEFINITION_REFUSED.into(), json!(refused(false)));
        required.insert(DEFINITION_REFUSED.into(), json!(refused(true)));
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
        let implementation = row["implementation"].as_str().unwrap_or("?");
        let name = format!(
            "{implementation} {}",
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
                "different" if view["difference"]["format"] == TRACE_DIFFERENCE_FORMAT => {
                    format!(" at {}", trace_difference_text(&view["difference"]))
                }
                "different" => view["difference"]["at"]
                    .as_str()
                    .or_else(|| view["difference"]["path"].as_str())
                    .map(|at| format!(" at {at}"))
                    .unwrap_or_default(),
                "could-not-apply" | DEFINITION_REFUSED | "not-compared" | "agree-up-to" => {
                    view["detail"]
                        .as_str()
                        .map(|detail| format!(": {detail}"))
                        .unwrap_or_default()
                }
                _ => String::new(),
            };
            // A trace view's line ends with what its verdict rests on.
            let testing = if view["correspondence"] == CORRESPONDENCE {
                format!(
                    " (testing: that element k is the definition's point k is \
                     {implementation}'s claim)"
                )
            } else {
                String::new()
            };
            text.push_str(&format!(
                "{name} {} ({required}): {verdict}{detail}{testing}\n",
                view["view"].as_str().unwrap_or("?")
            ));
        }
    }
    let summary = &document["summary"];
    if summary.is_object() {
        let counts = |member: &str| {
            counted(summary[member].get("agree-up-to").is_some())
                .map(|verdict| format!("{} {verdict}", summary[member][verdict]))
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

/// A trace view's first difference ([`TraceDifference::value`]) as a line says it: the channel,
/// the index and the place in the value, then each side there: the definition's element with the
/// point it was read at and the steps its run took to it, or its closure; the implementation's
/// element with its own count, or its closure.
fn trace_difference_text(difference: &Value) -> String {
    let index = &difference["index"];
    let place = difference["path"]
        .as_str()
        .map(|path| format!(" at `{path}`"))
        .unwrap_or_default();
    let stated = |side: &Value| match side["closed"].as_str() {
        Some(closure) => format!("closed ({closure})"),
        None => canonical_json(&side["element"]),
    };
    let definition = &difference["definition"];
    let read = match (definition["rule"].as_str(), definition["steps"].as_u64()) {
        (Some(rule), Some(steps)) => format!(
            " ({} `{rule}`, after {steps} steps)",
            definition["side"].as_str().unwrap_or("at")
        ),
        (Some(rule), None) => format!(
            " ({} `{rule}`)",
            definition["side"].as_str().unwrap_or("at")
        ),
        (None, Some(steps)) => format!(" (after {steps} steps)"),
        (None, None) => String::new(),
    };
    let implementation = &difference["implementation"];
    let count = match implementation["count"].as_u64() {
        Some(count) if implementation["closed"].is_null() => {
            format!(" (its element {index}, its count {count})")
        }
        _ => format!(" (its position {index})"),
    };
    format!(
        "`{}` element {index}{place}: definition {}{read}; implementation {}{count}",
        difference["channel"].as_str().unwrap_or("?"),
        stated(definition),
        stated(implementation),
    )
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
        let document = command(
            &manifest,
            &CompareOptions::default(),
            None,
            "kink-flow compare",
        );
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

    // ---- `kink-implementation/2`: trace views ----

    const OBSERVE: &str = "[[observe.point]]\nname = \"ticks\"\nbefore = [\"CALC.tick\"]\nstutter \
                           = \"count\"\ncells = [\"n\"]\n\n[[observe.log]]\nname = \
                           \"writes\"\ncell = \"bus\"\nat = [\"ticks\"]\n\n";

    /// An implementation `fake` of the second protocol with the views `views`.
    fn second(views: &str) -> ImplementationSection {
        decoded(&format!(
            "{OBSERVE}[[implementation]]\nname = \"fake\"\nprotocol = \
             \"kink-implementation/2\"\ncommand = [\"fake\"]\ngiven = \"inputs\"\nviews = \
             [{views}]\n"
        ))
        .unwrap()
        .implementations
        .remove(0)
    }

    const TICKS: &str = "{ name = \"ticks\", channels = [\"ticks\"], required = true }";
    const BOTH: &str = "{ name = \"both\", channels = [\"writes\", \"ticks\"], required = true }";
    const END: &str = "{ name = \"end\", required = true }";

    /// A front end whose every answer is given: the shapes it asks, its comparison of an end
    /// view and its comparison of the trace views.
    struct Mock {
        shapes: Result<Vec<Value>, String>,
        end: Judged,
        trace: Result<TraceAnswer, String>,
    }

    impl Mock {
        fn judging(judged: Vec<TraceJudged>) -> Self {
            Self {
                shapes: Ok(Vec::new()),
                end: Judged::Equal {
                    omitted: Vec::new(),
                },
                trace: Ok(TraceAnswer::Judged(judged)),
            }
        }
    }

    impl Vocabulary for Mock {
        fn check(&self, _: &ImplementationSection) -> Result<(), String> {
            Ok(())
        }
        fn start(&self, _: &Pattern) -> Result<Value, String> {
            unreachable!("no start is asked")
        }
        fn inputs(
            &self,
            _: &Program,
            _: &mut dyn crate::admit::InputFiles,
        ) -> Result<Value, String> {
            unreachable!("no inputs are asked")
        }
        fn read_answer(&self, _: &ImplementationSection, _: &Value) -> Result<(), String> {
            Ok(())
        }
        fn compare(&self, _: &Question<'_>) -> Result<Judged, String> {
            Ok(self.end.clone())
        }
        fn observe_request(&self, _: &[String]) -> Result<Vec<Value>, String> {
            self.shapes.clone()
        }
        fn judge_trace(&self, _: &TraceQuestion<'_>) -> Result<TraceAnswer, String> {
            self.trace.clone()
        }
    }

    /// The definition's values of the channel `name`: `elements` elements, ended by `end`.
    fn channel(name: &str, elements: u64, end: ChannelEnd) -> ChannelValues {
        ChannelValues {
            name: name.to_owned(),
            elements: (0..elements)
                .map(|index| ValueElement {
                    element: Element::Evaluated(json!({"n": index})),
                    depth: index,
                    point: None,
                })
                .collect(),
            end,
        }
    }

    fn open(opening: Opening) -> ChannelEnd {
        ChannelEnd::Open(Opened {
            opening,
            reason: "the path was cut by a bound".to_owned(),
        })
    }

    const CLOSED: ChannelEnd = ChannelEnd::Closed(Closure::End);

    fn asked(channels: &[(&str, u64)]) -> Vec<AskedChannel> {
        channels
            .iter()
            .map(|(name, positions)| AskedChannel {
                name: (*name).to_owned(),
                positions: *positions,
            })
            .collect()
    }

    fn agreed(channel: &str, elements: u64, reach: TraceReach) -> ChannelAgreed {
        ChannelAgreed {
            channel: channel.to_owned(),
            elements,
            reach,
        }
    }

    fn bounded(implementation: Option<&str>) -> TraceReach {
        TraceReach::Bounded {
            implementation: implementation.map(str::to_owned),
        }
    }

    /// The row of the trace view `ticks` for the front end's `agreement` of its one channel,
    /// against a definition that holds `held` elements ended by `end`, and the status it gives
    /// its (implementation, program) row as a required view.
    fn ticks_row(
        held: u64,
        end: ChannelEnd,
        positions: u64,
        judged: TraceJudged,
    ) -> Result<(Value, u8), String> {
        let implementation = second(TICKS);
        let row = judged_row(
            &implementation.views[0],
            judged,
            &asked(&[("ticks", positions)]),
            &[channel("ticks", held, end)],
        )?;
        let status = row_status(&json!({"views": [row], "failure": null, "required": true}));
        Ok((row, status))
    }

    fn difference() -> TraceDifference {
        TraceDifference {
            channel: "ticks".to_owned(),
            kind: "value".to_owned(),
            index: 3,
            path: Some("acc".to_owned()),
            definition: json!({"element": {"n": -1, "acc": 3}, "rule": "crate::spin",
                               "side": "before", "steps": 3}),
            implementation: json!({"element": {"n": -1, "acc": 5}, "count": 3}),
        }
    }

    /// The status table of a trace view: which verdict the front end's comparison gives, and
    /// what a required view of it decides.
    #[test]
    fn a_trace_view_has_the_verdict_its_agreement_reaches() {
        // Both sides close after the same elements: `equal`.
        let (row, status) = ticks_row(
            6,
            CLOSED,
            7,
            TraceJudged::Agree(vec![agreed("ticks", 6, TraceReach::Closed)]),
        )
        .unwrap();
        assert_eq!((row["verdict"].as_str(), status), (Some("equal"), EXIT_YES));
        assert_eq!(row["horizon"], Value::Null);
        assert_eq!(row["correspondence"], "implementation-claim");
        // END against END with no element is a compared position: `equal`.
        let (row, status) = ticks_row(
            0,
            CLOSED,
            1,
            TraceJudged::Agree(vec![agreed("ticks", 0, TraceReach::Closed)]),
        )
        .unwrap();
        assert_eq!((row["verdict"].as_str(), status), (Some("equal"), EXIT_YES));

        // The definition's run is cut after 6 elements, and the answer agrees with all 6:
        // agreement up to the definition's horizon, which passes, and is not `equal`.
        for implementation in [Some("the requested positions"), None] {
            let (row, status) = ticks_row(
                6,
                open(Opening::Bound),
                6,
                TraceJudged::Agree(vec![agreed("ticks", 6, bounded(implementation))]),
            )
            .unwrap();
            assert_eq!(
                (row["verdict"].as_str(), status),
                (Some("agree-up-to"), EXIT_YES)
            );
            assert_eq!(
                row["horizon"],
                json!({"ticks": {"elements": 6, "limited_by": "definition",
                                 "definition": "bound", "implementation": implementation}})
            );
            assert_eq!(
                row["detail"],
                "`ticks` 6 elements agree, then the definition's run is cut (bound); nothing \
                 past it is compared"
            );
        }

        // The answer stops after 2 of the 6 positions asked: the question is left open, so a
        // required view is unanswered. An implementation that answers one element does not pass.
        let (row, status) = ticks_row(
            6,
            open(Opening::Bound),
            6,
            TraceJudged::Agree(vec![agreed("ticks", 2, bounded(Some("its own budget")))]),
        )
        .unwrap();
        assert_eq!(
            (row["verdict"].as_str(), status),
            (Some("agree-up-to"), EXIT_UNANSWERED)
        );
        assert_eq!(
            row["horizon"]["ticks"],
            json!({"elements": 2, "limited_by": "implementation", "definition": null,
                   "implementation": "its own budget"})
        );
        // The same of a definition that closes: the answer is open at the closure's position.
        let (row, status) = ticks_row(
            6,
            CLOSED,
            7,
            TraceJudged::Agree(vec![agreed("ticks", 6, bounded(Some("the positions")))]),
        )
        .unwrap();
        assert_eq!(
            (row["verdict"].as_str(), status),
            (Some("agree-up-to"), EXIT_UNANSWERED)
        );
        assert_eq!(row["horizon"]["ticks"]["limited_by"], "implementation");

        // No element compared and nothing closed: a comparison of nothing is no agreement.
        for (held, implementation) in [(0, None), (6, Some("it stated nothing"))] {
            let (row, status) = ticks_row(
                held,
                open(Opening::Bound),
                held,
                TraceJudged::Agree(vec![agreed("ticks", 0, bounded(implementation))]),
            )
            .unwrap();
            assert_eq!(
                (row["verdict"].as_str(), row["reason"].as_str(), status),
                (
                    Some("not-compared"),
                    Some("observed-nothing"),
                    EXIT_UNANSWERED
                )
            );
            assert_eq!(row["horizon"], Value::Null);
        }

        // A difference: `different`, with the `kink-trace/1` document.
        let (row, status) = ticks_row(
            6,
            open(Opening::Bound),
            6,
            TraceJudged::Different(difference()),
        )
        .unwrap();
        assert_eq!(
            (row["verdict"].as_str(), status),
            (Some("different"), EXIT_NO)
        );
        assert_eq!(
            row["difference"],
            json!({"format": "kink-trace/1", "channel": "ticks", "kind": "value", "index": 3,
                   "path": "acc",
                   "definition": {"element": {"n": -1, "acc": 3}, "rule": "crate::spin",
                                  "side": "before", "steps": 3},
                   "implementation": {"element": {"n": -1, "acc": 5}, "count": 3},
                   "correspondence": "implementation-claim"})
        );

        // An element that is not decided: `not-compared` (`undecided`).
        let (row, status) = ticks_row(
            6,
            open(Opening::Bound),
            6,
            TraceJudged::Undecided("`ticks` element 2 of the definition is undecided".to_owned()),
        )
        .unwrap();
        assert_eq!(
            (row["verdict"].as_str(), row["reason"].as_str(), status),
            (Some("not-compared"), Some("undecided"), EXIT_UNANSWERED)
        );
    }

    /// Agreement up to a horizon is never spelled `equal`, whatever the front end says: a
    /// closure the definition's channel does not have is refused, and so is every other
    /// comparison that is none of the view against the definition's values.
    #[test]
    fn a_front_end_cannot_close_what_the_definition_leaves_open() {
        for (held, end, judged, expected) in [
            (
                6,
                open(Opening::Bound),
                TraceJudged::Agree(vec![agreed("ticks", 6, TraceReach::Closed)]),
                "the definition's channel is not closed there",
            ),
            // Closed by a cycle is read as open: no `equal` either.
            (
                6,
                ChannelEnd::Closed(Closure::Cycle),
                TraceJudged::Agree(vec![agreed("ticks", 6, TraceReach::Closed)]),
                "the definition's channel is not closed there",
            ),
            (
                6,
                CLOSED,
                TraceJudged::Agree(vec![agreed("ticks", 5, TraceReach::Closed)]),
                "the definition's channel is not closed there",
            ),
            (
                6,
                CLOSED,
                TraceJudged::Agree(vec![agreed("ticks", 7, bounded(Some("x")))]),
                "the definition's channel holds 6",
            ),
            (
                6,
                CLOSED,
                TraceJudged::Agree(vec![agreed("ticks", 3, bounded(None))]),
                "neither side's channel is open",
            ),
            (
                6,
                CLOSED,
                TraceJudged::Agree(vec![agreed("writes", 6, TraceReach::Closed)]),
                "not one per channel of the view",
            ),
            (
                6,
                CLOSED,
                TraceJudged::Agree(Vec::new()),
                "not one per channel of the view",
            ),
            (
                6,
                CLOSED,
                TraceJudged::Different(TraceDifference {
                    channel: "writes".to_owned(),
                    ..difference()
                }),
                "no channel of the view",
            ),
        ] {
            let error = ticks_row(held, end, 7, judged).unwrap_err();
            assert!(error.contains(expected), "{error}");
        }
        // A channel closed by a cycle, compared through its elements, is a horizon of the
        // definition's.
        let (row, status) = ticks_row(
            6,
            ChannelEnd::Closed(Closure::Cycle),
            6,
            TraceJudged::Agree(vec![agreed("ticks", 6, bounded(None))]),
        )
        .unwrap();
        assert_eq!(
            (row["verdict"].as_str(), status),
            (Some("agree-up-to"), EXIT_YES)
        );
        assert_eq!(row["horizon"]["ticks"]["definition"], "cycle");
    }

    /// A view of several channels: `equal` only when each closes; one bounded channel makes it
    /// `agree-up-to`, naming that channel alone; and it is compared when some channel was.
    #[test]
    fn a_view_of_several_channels_names_each_bounded_one() {
        let implementation = second(BOTH);
        let definition = [
            channel("ticks", 6, open(Opening::Bound)),
            channel("writes", 2, CLOSED),
        ];
        let asked = asked(&[("ticks", 6), ("writes", 3)]);
        let row = |judged| judged_row(&implementation.views[0], judged, &asked, &definition);
        let mixed = row(TraceJudged::Agree(vec![
            agreed("writes", 2, TraceReach::Closed),
            agreed("ticks", 6, bounded(None)),
        ]))
        .unwrap();
        assert_eq!(mixed["verdict"], "agree-up-to");
        assert_eq!(
            mixed["horizon"]
                .as_object()
                .unwrap()
                .keys()
                .collect::<Vec<_>>(),
            ["ticks"]
        );
        assert_eq!(mixed["status"], EXIT_YES);
        // One channel short of its positions leaves the view unanswered, the other reaching the
        // definition's horizon.
        let short = row(TraceJudged::Agree(vec![
            agreed("writes", 1, bounded(Some("budget"))),
            agreed("ticks", 6, bounded(None)),
        ]))
        .unwrap();
        assert_eq!(
            (short["verdict"].as_str(), short["status"].as_u64()),
            (Some("agree-up-to"), Some(u64::from(EXIT_UNANSWERED)))
        );
        assert_eq!(
            short["detail"],
            "`writes` 1 element agrees, then the implementation's channel is open (budget) \
             before the 3 positions asked; `ticks` 6 elements agree, then the definition's run \
             is cut (bound); nothing past it is compared"
        );
        // The agreement is in the view's order of channels.
        assert!(
            row(TraceJudged::Agree(vec![
                agreed("ticks", 6, bounded(None)),
                agreed("writes", 2, TraceReach::Closed),
            ]))
            .is_err()
        );
    }

    #[test]
    fn positions_count_the_elements_and_a_closure() {
        let record = json!({"channels": [
            {"name": "ticks", "elements": ["00", "01", null], "closed": null,
             "open": {"index": 3, "opening": "bound", "reason": "cut"}},
            {"name": "writes", "elements": ["00", "01"], "closed": "end", "open": null},
            {"name": "halts", "elements": [], "closed": "undefined", "open": null},
            {"name": "loops", "elements": ["00"], "closed": "cycle", "open": null},
        ], "prefix": true, "crashed": false});
        let names = ["ticks", "writes", "halts", "loops"].map(str::to_owned);
        assert_eq!(
            asked_channels(&record, &names).unwrap(),
            asked(&[("ticks", 3), ("writes", 3), ("halts", 1), ("loops", 1)])
        );
        assert_eq!(
            asked_channels(&record, &["tocks".to_owned()]).unwrap_err(),
            "the baseline's observation record holds no channel `tocks`"
        );
    }

    /// A request's `observe` is the front end's shapes of the channels the implementation's
    /// trace views name, in `[observe]`'s order, each with its positions.
    #[test]
    fn a_request_asks_for_the_channels_of_the_trace_views() {
        let implementation = second(&format!("{END}, {BOTH}, {TICKS}"));
        let manifest = decoded(OBSERVE).unwrap();
        let channels = traced_channels(&implementation, manifest.observe.as_ref());
        assert_eq!(channels, ["ticks", "writes"]);
        assert!(traced_channels(&second(END), manifest.observe.as_ref()).is_empty());
        let shapes = vec![
            json!({"name": "ticks", "kind": "point", "stutter": "count", "filtered": false,
                   "components": [{"name": "n", "type": "Int"}],
                   "points": {"before": ["CALC.tick"], "after": []}}),
            json!({"name": "writes", "kind": "log", "element": {"type": "Int"}, "at": ["ticks"]}),
        ];
        let mock = |shapes| Mock {
            shapes,
            ..Mock::judging(Vec::new())
        };
        assert_eq!(
            channel_shapes(&mock(Ok(shapes.clone())), &channels).unwrap(),
            shapes
        );
        assert_eq!(
            observe_value(&shapes, &asked(&[("ticks", 6), ("writes", 3)])),
            json!({"channels": [
                {"name": "ticks", "kind": "point", "stutter": "count", "filtered": false,
                 "components": [{"name": "n", "type": "Int"}],
                 "points": {"before": ["CALC.tick"], "after": []}, "positions": 6},
                {"name": "writes", "kind": "log", "element": {"type": "Int"}, "at": ["ticks"],
                 "positions": 3},
            ]})
        );
        // The shapes are the channels asked, in order, and the positions are kink-flow's.
        for wrong in [
            Ok(vec![shapes[0].clone()]),
            Ok(vec![shapes[1].clone(), shapes[0].clone()]),
            Ok(vec![
                json!({"name": "ticks", "positions": 1}),
                shapes[1].clone(),
            ]),
            Err("no document form".to_owned()),
        ] {
            assert!(channel_shapes(&mock(wrong), &channels).is_err());
        }
    }

    const PROGRAM: &str = "[[program]]\nid = \"p\"\ntext = \"1 + 2\"\n\n";

    /// A request of the first protocol and its cached answer's record are what they were before
    /// a second protocol existed; a request of the second names it and holds `observe`, and its
    /// answers are cached apart.
    #[test]
    fn a_first_protocol_request_and_its_cache_record_are_unchanged() {
        let manifest = decoded(&format!("{PROGRAM}{ONE}")).unwrap();
        let (program, first) = (&manifest.programs[0], &manifest.implementations[0]);
        let start = Ok(json!({"pc": 0}));
        let typed = json!({"n": 3});
        let request = |implementation, observe| {
            request(
                &manifest,
                program,
                implementation,
                &typed,
                Some(&start),
                observe,
            )
            .map(|request| canonical_json(&request))
        };
        assert_eq!(
            request(first, None).unwrap(),
            r#"{"inputs":{"n":3},"program":"p","protocol":"kink-implementation/1","start":{"pc":0}}"#
        );
        let key = AnswerKey::new(first, "aa", "bb");
        assert_eq!(
            canonical_json(&key.record),
            r#"{"command":["bin/cpu","--kink"],"identity_sha256":"aa","protocol":"kink-implementation/1","request_sha256":"bb","version":"kink-flow/implementation-answer/v1"}"#
        );
        assert_eq!(key.name, digest(canonical_json(&key.record).as_bytes()));

        let second = ImplementationSection {
            protocol: Protocol::V2.as_str().to_owned(),
            ..first.clone()
        };
        assert_eq!(
            request(&second, Some(json!({"channels": []}))).unwrap(),
            r#"{"inputs":{"n":3},"observe":{"channels":[]},"program":"p","protocol":"kink-implementation/2","start":{"pc":0}}"#
        );
        let other = AnswerKey::new(&second, "aa", "bb");
        assert_eq!(other.record["protocol"], "kink-implementation/2");
        assert_ne!(other.name, key.name);
    }

    #[test]
    fn a_second_protocol_answer_is_read_by_what_its_request_asked() {
        let traced = Asked {
            observe: true,
            end_view: false,
        };
        let both = Asked {
            observe: true,
            end_view: true,
        };
        let ended = Asked {
            observe: false,
            end_view: true,
        };
        let observations = json!({"schema": "krs-observations/1", "channels": []});
        assert_eq!(
            read_answer_2(
                br#"{"end": "horizon", "observations": {"schema": "krs-observations/1", "channels": []}}"#,
                traced
            ),
            Ok(Stated {
                end: StatedEnd::Horizon,
                cells: None,
                observations: Some(observations.clone()),
            })
        );
        assert_eq!(
            read_answer_2(
                br#"{"end": "final", "cells": {"pc": 1}, "observations": {"schema": "krs-observations/1", "channels": []}}"#,
                both
            ),
            Ok(Stated {
                end: StatedEnd::Ended(EndWord::Final),
                cells: Some(json!({"pc": 1})),
                observations: Some(observations),
            })
        );
        // Without an end view the end's cells may be left out.
        assert!(
            read_answer_2(br#"{"end": "stopped", "observations": {}}"#, traced)
                .is_ok_and(|stated| stated.cells.is_none())
        );
        // A request without `observe` is answered as the first protocol's is.
        assert_eq!(
            read_answer_2(br#"{"end": "stopped", "cells": {}}"#, ended),
            Ok(Stated::from(
                read_answer(br#"{"end": "stopped", "cells": {}}"#).unwrap()
            ))
        );
        assert_eq!(
            read_answer_2(br#"{"end": "could-not-apply", "reason": "late"}"#, both),
            Ok(Stated {
                end: StatedEnd::CouldNotApply("late".to_owned()),
                cells: None,
                observations: None,
            })
        );
        for (bytes, asked, expected) in [
            (
                &br#"{"end": "final", "cells": {}}"#[..],
                both,
                "a `final` answer to a request with `observe` states its `observations`",
            ),
            (
                br#"{"end": "horizon"}"#,
                traced,
                "a `horizon` answer to a request with `observe` states its `observations`",
            ),
            (
                br#"{"end": "final", "observations": {}}"#,
                both,
                "a `final` answer states its end's `cells`",
            ),
            (
                br#"{"end": "horizon", "cells": {}, "observations": {}}"#,
                both,
                "a `horizon` answer states no `cells`",
            ),
            (
                br#"{"end": "final", "cells": {}, "observations": {}}"#,
                ended,
                "the answer states `observations`, and the request has no `observe`",
            ),
            (
                br#"{"end": "horizon"}"#,
                ended,
                "`end` is `horizon`, and the request has no `observe`",
            ),
            (
                br#"{"end": "final", "cells": {}, "observations": []}"#,
                both,
                "`observations` is not a JSON object",
            ),
            (
                br#"{"end": "could-not-apply", "reason": "x", "observations": {}}"#,
                both,
                "a `could-not-apply` answer states no `observations`",
            ),
            (
                br#"{"end": "final", "cells": {}, "observations": {}, "rule": 1}"#,
                both,
                "the answer has the key `rule`",
            ),
            (
                br#"{"end": "stuck", "observations": {}}"#,
                traced,
                "`end` is `stuck`",
            ),
        ] {
            let error = read_answer_2(bytes, asked).unwrap_err();
            assert!(error.starts_with(expected), "{error}");
        }
        // The first protocol's reader reads no answer of the second.
        for bytes in [
            &br#"{"end": "final", "cells": {}, "observations": {}}"#[..],
            br#"{"end": "horizon", "observations": {}}"#,
        ] {
            assert!(read_answer(bytes).is_err());
        }
    }

    /// An answer that leaves a requested channel out is malformed: it is never a comparison of
    /// the channels it does state.
    #[test]
    fn a_missing_requested_channel_is_malformed() {
        let asked = asked(&[("ticks", 6), ("writes", 3)]);
        let named = |names: &[&str]| json!({"channels": names.iter().map(|name| json!({"name": name})).collect::<Vec<_>>()});
        assert_eq!(
            stated_channels(&named(&["writes", "ticks"]), &asked),
            Ok(())
        );
        for (observations, expected) in [
            (
                named(&["ticks"]),
                "no channel `writes`, which the request asked for",
            ),
            (
                named(&[]),
                "no channel `ticks`, which the request asked for",
            ),
            (
                named(&["ticks", "writes", "tocks"]),
                "`channels[2]` is `tocks`, a channel the request did not ask for",
            ),
            (
                named(&["ticks", "ticks", "writes"]),
                "`channels[1]`: `ticks` is stated twice",
            ),
            (json!({}), "`channels` is not an array"),
            (
                json!({"channels": [{"kind": "point"}]}),
                "`channels[0]` is no object with a `name` string",
            ),
        ] {
            assert_eq!(
                stated_channels(&observations, &asked).unwrap_err(),
                expected
            );
        }
        // What the front end finds malformed in the record is the run's failure too, and a
        // front end that compares another number of views than declared fails the command.
        let implementation = second(TICKS);
        let definition = [channel("ticks", 6, CLOSED)];
        let observations = named(&["ticks"]);
        let question = TraceQuestion {
            implementation: &implementation,
            channels: &asked[..1],
            observations: &observations,
            definition: &definition,
        };
        let mock = |trace| Mock {
            trace,
            ..Mock::judging(Vec::new())
        };
        assert_eq!(
            judge_trace(
                &mock(Ok(TraceAnswer::Malformed(
                    "channels[0].elements[1].value.n: expected an Int".to_owned()
                ))),
                &question
            ),
            Ok(Err(
                "channels[0].elements[1].value.n: expected an Int".to_owned()
            ))
        );
        assert!(judge_trace(&mock(Ok(TraceAnswer::Judged(Vec::new()))), &question).is_err());
        assert!(judge_trace(&mock(Err("no definition".to_owned())), &question).is_err());
    }

    fn stated(end: StatedEnd, cells: bool, observations: bool) -> Stated {
        Stated {
            end,
            cells: cells.then(|| json!({"pc": 1})),
            observations: observations.then(|| json!({"channels": [{"name": "ticks"}]})),
        }
    }

    /// The rows of an answer of the second protocol, view by view: a trace view by the front
    /// end's comparison, an end view by the definition's ends, or `no-end` on a program whose
    /// baseline has none, where a required trace view carries the requirement (status 0) and
    /// nothing else does (status 3).
    #[test]
    fn an_answer_has_one_row_per_view_of_either_kind() {
        let mock = Mock::judging(Vec::new());
        let ends = BTreeSet::new();
        let words = BTreeSet::from(["final"]);
        let definition = [channel("ticks", 6, open(Opening::Bound))];
        let asked = asked(&[("ticks", 6)]);
        let side = || {
            Some(TraceSide::Judged {
                judged: vec![TraceJudged::Agree(vec![agreed("ticks", 6, bounded(None))])],
                asked: &asked,
                definition: &definition,
            })
        };
        let verdicts = |rows: &[Value]| {
            rows.iter()
                .map(|row| {
                    (
                        row["verdict"].as_str().unwrap().to_owned(),
                        row["reason"].as_str().map(str::to_owned),
                        row["status"].as_u64(),
                    )
                })
                .collect::<Vec<_>>()
        };
        let status =
            |rows: &[Value]| row_status(&json!({"views": rows, "failure": null, "required": true}));

        // A program that never ends: the end view has no end, the trace view carries it.
        let mixed = second(&format!("{END}, {TICKS}"));
        let rows = answered_rows(
            &mock,
            &mixed,
            &stated(StatedEnd::Horizon, false, true),
            None,
            &[],
            side(),
        )
        .unwrap();
        assert_eq!(
            verdicts(&rows),
            [
                (
                    "not-compared".to_owned(),
                    Some("no-end".to_owned()),
                    Some(0)
                ),
                ("agree-up-to".to_owned(), None, Some(0)),
            ]
        );
        assert_eq!(status(&rows), EXIT_YES);
        assert!(rows[0].get("correspondence").is_none() && rows[0].get("horizon").is_none());

        // The same where the trace view is only reported: nothing required carries the program.
        let reported = second(&format!(
            "{END}, {{ name = \"ticks\", channels = [\"ticks\"] }}"
        ));
        let rows = answered_rows(
            &mock,
            &reported,
            &stated(StatedEnd::Horizon, false, true),
            None,
            &[],
            side(),
        )
        .unwrap();
        assert_eq!(rows[0]["reason"], "no-end");
        assert_eq!(status(&rows), EXIT_UNANSWERED);
        assert_eq!(
            status(&not_compared_rows(&second(END), &no_end(&second(END)))),
            EXIT_UNANSWERED
        );

        // A program that ends, answered with `horizon`: the end view differs in its end's word.
        let rows = answered_rows(
            &mock,
            &mixed,
            &stated(StatedEnd::Horizon, false, true),
            Some((&ends, &words)),
            &[],
            side(),
        )
        .unwrap();
        assert_eq!(
            rows[0]["difference"],
            json!({"format": "kink-end/1", "at": "end", "definition": "final",
                   "implementation": "horizon"})
        );
        assert_eq!(status(&rows), EXIT_NO);

        // It ends as the definition does: the end view is the front end's, the trace view too.
        let rows = answered_rows(
            &mock,
            &mixed,
            &stated(StatedEnd::Ended(EndWord::Final), true, true),
            Some((&ends, &words)),
            &[],
            side(),
        )
        .unwrap();
        assert_eq!(
            verdicts(&rows),
            [
                ("equal".to_owned(), None, None),
                ("agree-up-to".to_owned(), None, Some(0)),
            ]
        );

        // The baseline has several paths: the trace view is not compared, the end view is.
        let several = NotCompared::SeveralPaths(SEVERAL_PATHS.to_owned());
        let rows = answered_rows(
            &mock,
            &mixed,
            &stated(StatedEnd::Ended(EndWord::Final), true, false),
            Some((&ends, &words)),
            &[],
            Some(TraceSide::Not(&several)),
        )
        .unwrap();
        assert_eq!(
            verdicts(&rows),
            [
                ("equal".to_owned(), None, None),
                (
                    "not-compared".to_owned(),
                    Some("several-paths".to_owned()),
                    Some(3)
                ),
            ]
        );
        assert_eq!(rows[1]["correspondence"], "implementation-claim");
        assert_eq!(status(&rows), EXIT_UNANSWERED);

        // It declined the program: every view says so, in its words.
        let rows = answered_rows(
            &mock,
            &mixed,
            &stated(StatedEnd::CouldNotApply("late".to_owned()), false, false),
            None,
            &[],
            None,
        )
        .unwrap();
        assert!(
            rows.iter()
                .all(|row| row["verdict"] == "could-not-apply" && row["detail"] == "late")
        );
        assert_eq!(status(&rows), EXIT_YES);

        // A trace view the front end did not compare fails the command.
        assert!(
            answered_rows(
                &mock,
                &mixed,
                &stated(StatedEnd::Horizon, false, true),
                None,
                &[],
                None
            )
            .is_err()
        );
    }

    /// The rows, the summary and the text of an implementation of the first protocol are what
    /// they were before a second existed: no key and no word of a trace.
    #[test]
    fn a_first_protocol_row_summary_and_text_are_unchanged() {
        let manifest = decoded(ONE).unwrap();
        let implementation = &manifest.implementations[0];
        let ends = BTreeSet::new();
        let words = BTreeSet::from(["stopped"]);
        let mock = Mock {
            end: Judged::Different {
                difference: json!({"format": "krs-difference/3", "path": "acc"}),
                omitted: vec!["k".to_owned()],
            },
            ..Mock::judging(Vec::new())
        };
        let answer = read_answer(br#"{"end": "stopped", "cells": {"pc": 1}}"#).unwrap();
        let rows = answered_rows(
            &mock,
            implementation,
            &Stated::from(answer.clone()),
            Some((&ends, &words)),
            &[],
            None,
        )
        .unwrap();
        assert_eq!(
            serde_json::to_string(&rows).unwrap(),
            r#"[{"detail":null,"difference":{"format":"krs-difference/3","path":"acc"},"omitted":["k"],"reason":null,"required":true,"status":null,"verdict":"different","view":"writes"},{"detail":null,"difference":{"format":"krs-difference/3","path":"acc"},"omitted":["k"],"reason":null,"required":false,"status":null,"verdict":"different","view":"all"}]"#
        );
        assert_eq!(
            Stated::from(answer).value().to_string(),
            r#"{"end":"stopped","reason":null}"#
        );
        // A program its bounds cut is told of as before, and nothing is asked.
        assert_eq!(
            serde_json::to_string(&definition_rows(implementation, "comparable-prefix", None))
                .unwrap(),
            r#"[{"detail":"the definition's run of the program is `comparable-prefix`: it has no end to compare","difference":null,"omitted":[],"reason":"definition","required":true,"status":3,"verdict":"not-compared","view":"writes"},{"detail":"the definition's run of the program is `comparable-prefix`: it has no end to compare","difference":null,"omitted":[],"reason":"definition","required":false,"status":3,"verdict":"not-compared","view":"all"}]"#
        );
        let rows = vec![
            json!({"implementation": "cpu", "program": "p", "required": true,
                               "failure": null, "views": rows}),
        ];
        let summary = summary(&rows, false);
        assert_eq!(
            summary.to_string(),
            r#"{"failures":0,"required":{"could-not-apply":0,"different":1,"equal":0,"not-compared":0},"verdicts":{"could-not-apply":0,"different":2,"equal":0,"not-compared":0}}"#
        );
        let document = json!({"schema": COMPARE_SCHEMA, "rows": rows, "summary": summary});
        assert_eq!(
            text(&document).unwrap(),
            "cpu p writes (required): different at acc\ncpu p all (reported): different at \
             acc\nverdicts: 0 equal, 2 different, 0 could-not-apply, 0 not-compared; required \
             views: 0 equal, 1 different, 0 could-not-apply, 0 not-compared; failed runs: 0\n"
        );
        assert!(
            verdict_rows(&json!({"implementations": [{"name": "cpu"}], "rows": document["rows"]}))
                .iter()
                .all(|row| row.get("horizon").is_none())
        );
        // The document names its one protocol as before, and nothing more.
        let refused = command(
            &manifest,
            &CompareOptions::default(),
            None,
            "kink-flow compare",
        );
        assert_eq!(refused["protocol"], "kink-implementation/1");
        assert!(refused.get("protocols").is_none() && refused.get("evidence").is_none());
    }

    /// The document of a flow with an implementation of the second protocol says what its
    /// verdicts are: tests. Each trace line ends with what its verdict rests on, the summary
    /// counts `agree-up-to` apart from `equal`, a lock row holds the horizon, and no key or line
    /// relates two definitions.
    #[test]
    fn a_trace_document_is_labelled_as_testing() {
        let implementation = second(&format!("{END}, {TICKS}"));
        let definition = [channel("ticks", 6, open(Opening::Bound))];
        let asked = asked(&[("ticks", 6)]);
        let view = &implementation.views[1];
        let row = |judged| judged_row(view, judged, &asked, &definition).unwrap();
        let mut none = view_row(view);
        not_compared_row(
            &mut none,
            &NotCompared::SeveralPaths(SEVERAL_PATHS.to_owned()),
        );
        let views = vec![
            row(TraceJudged::Agree(vec![agreed("ticks", 6, bounded(None))])),
            row(TraceJudged::Different(difference())),
            row(TraceJudged::Different(TraceDifference {
                kind: "closure".to_owned(),
                index: 6,
                path: None,
                definition: json!({"element": {"n": 0}, "rule": null, "side": null, "steps": 9}),
                implementation: json!({"closed": "end"}),
                ..difference()
            })),
            row(TraceJudged::Agree(vec![agreed(
                "ticks",
                0,
                bounded(Some("nothing")),
            )])),
            none,
        ];
        let rows = views
            .into_iter()
            .enumerate()
            .map(|(index, view)| {
                json!({"implementation": "fake", "program": format!("p{index}"),
                       "required": true, "request_sha256": "rr", "failure": null,
                       "views": [view]})
            })
            .collect::<Vec<_>>();
        let summary = summary(&rows, true);
        assert_eq!(
            summary["required"],
            json!({"equal": 0, "agree-up-to": 1, "different": 2, "could-not-apply": 0,
                   "not-compared": 2})
        );
        let document = json!({
            "schema": COMPARE_SCHEMA,
            "implementations": [{"name": "fake", "identity": null}],
            "rows": rows,
            "summary": summary,
        });
        let testing = " (testing: that element k is the definition's point k is fake's claim)";
        let text = text(&document).unwrap();
        let lines = text.lines().collect::<Vec<_>>();
        assert_eq!(
            lines,
            [
                format!(
                    "fake p0 ticks (required): agree-up-to: `ticks` 6 elements agree, then the \
                     definition's run is cut (bound); nothing past it is compared{testing}"
                ),
                format!(
                    "fake p1 ticks (required): different at `ticks` element 3 at `acc`: \
                     definition {{\"acc\":3,\"n\":-1}} (before `crate::spin`, after 3 steps); \
                     implementation {{\"acc\":5,\"n\":-1}} (its element 3, its count 3){testing}"
                ),
                format!(
                    "fake p2 ticks (required): different at `ticks` element 6: definition \
                     {{\"n\":0}} (after 9 steps); implementation closed (end) (its position \
                     6){testing}"
                ),
                format!(
                    "fake p3 ticks (required): not-compared: no element of `ticks` was \
                     compared: `ticks` 0 elements agree, then the implementation's channel is \
                     open (nothing) before the 6 positions asked{testing}"
                ),
                format!("fake p4 ticks (required): not-compared: {SEVERAL_PATHS}{testing}"),
                "verdicts: 0 equal, 1 agree-up-to, 2 different, 0 could-not-apply, 2 \
                 not-compared; required views: 0 equal, 1 agree-up-to, 2 different, 0 \
                 could-not-apply, 2 not-compared; failed runs: 0"
                    .to_owned(),
            ]
        );
        // A lock row of a horizon holds it, as canonical JSON; no other row has the key.
        let verdicts = verdict_rows(&document);
        assert_eq!(
            verdicts[0]["horizon"],
            r#"{"ticks":{"definition":"bound","elements":6,"implementation":null,"limited_by":"definition"}}"#
        );
        assert_eq!(verdicts[0]["verdict"], "agree-up-to");
        assert!(verdicts[1..].iter().all(|row| row.get("horizon").is_none()));

        // The document names the protocols of its implementations and its evidence.
        let manifest = decoded(&format!(
            "{OBSERVE}{ONE}\n[[implementation]]\nname = \"fake\"\nprotocol = \
             \"kink-implementation/2\"\ncommand = [\"fake\"]\ngiven = \"inputs\"\nviews = \
             [{TICKS}]\n"
        ))
        .unwrap();
        let refused = command(
            &manifest,
            &CompareOptions::default(),
            None,
            "kink-flow compare",
        );
        assert_eq!(
            refused["protocols"],
            json!(["kink-implementation/1", "kink-implementation/2"])
        );
        assert_eq!(refused["evidence"], "testing");
        assert!(refused.get("protocol").is_none());
        // Selecting the first protocol's implementation alone gives its document.
        let only = CompareOptions {
            only: vec!["cpu".to_owned()],
            ..CompareOptions::default()
        };
        let refused = command(&manifest, &only, None, "kink-flow compare");
        assert_eq!(refused["protocol"], "kink-implementation/1");
        assert!(refused.get("evidence").is_none());

        // Nothing relates two definitions: no key and no line names a standing, a relation or
        // a transfer.
        let all = format!(
            "{document}{verdicts:?}{text}{}",
            NotCompared::reason(&no_end(&implementation))
        );
        for word in ["standing", "relation", "transfer"] {
            assert!(!all.contains(word), "{word}");
        }
    }

    /// A front end that asks no trace refuses the declaration before any run, so a trace view
    /// is never run as an end view.
    #[test]
    fn a_front_end_without_traces_refuses_a_trace_view() {
        let manifest = decoded(&format!(
            "{OBSERVE}[[implementation]]\nname = \"fake\"\nprotocol = \
             \"kink-implementation/2\"\ncommand = [\"fake\"]\ngiven = \"inputs\"\nviews = \
             [{TICKS}]\n"
        ))
        .unwrap();
        let mock = Mock {
            shapes: Err("this front end compares no trace yet".to_owned()),
            ..Mock::judging(Vec::new())
        };
        let document = command(
            &manifest,
            &CompareOptions::default(),
            Some(&mock),
            "kink-flow compare",
        );
        assert_eq!(
            document["refusal"],
            json!({"stage": "implementation", "reason": "declaration",
                   "detail": "implementation `fake`: this front end compares no trace yet"})
        );
        assert_eq!(compare_status(&document), EXIT_UNASKED);
    }

    // ---- The definition trace cache ----

    /// The observation record of a run with two channels: `ticks`, two elements, the second
    /// undecided, closed by its end; `writes`, one element, open at a bound.
    fn recorded() -> Value {
        json!({
            "channels": [
                {"name": "ticks", "elements": ["0011223344556677", null], "closed": "end", "open": null},
                {
                    "name": "writes",
                    "elements": ["8899aabbccddeeff"],
                    "closed": null,
                    "open": {"index": 1, "opening": "bound", "reason": "the path was cut by a bound"},
                },
            ],
            "prefix": true,
            "crashed": false,
        })
    }

    /// The values of [`recorded`]'s channels named `names`, as a front end documents them.
    fn recorded_values(names: &[&str]) -> Vec<ChannelValues> {
        names
            .iter()
            .map(|name| match *name {
                "ticks" => ChannelValues {
                    name: "ticks".to_owned(),
                    elements: vec![
                        ValueElement {
                            element: Element::Evaluated(json!({"n": 2, "nothing": null})),
                            depth: 0,
                            point: Some((Arc::from("CALC.tick"), StopSide::Before)),
                        },
                        ValueElement {
                            element: Element::Undecided,
                            depth: 3,
                            point: Some((Arc::from("CALC.spin"), StopSide::After)),
                        },
                    ],
                    end: CLOSED,
                },
                _ => ChannelValues {
                    name: "writes".to_owned(),
                    elements: vec![ValueElement {
                        // A document that is JSON null is a value, not an undecided element.
                        element: Element::Evaluated(Value::Null),
                        depth: 4,
                        point: None,
                    }],
                    end: open(Opening::Bound),
                },
            })
            .collect()
    }

    /// The result key of a program under the execution digest of `definition`, with `stop` and
    /// `observe`.
    fn result_of(definition: &str, stop: Option<Value>, observe: Option<Value>) -> Value {
        result_key(
            crate::digest::ExecutionDigest {
                kind: "test",
                digest: sha256(definition.as_bytes()),
            },
            sha256(b"program"),
            crate::manifest::Budget::default(),
            Some(sha256(b"build")),
            stop,
            None,
            observe,
        )
    }

    /// A cache directory of its own for the test `name`, empty.
    fn trace_cache(name: &str) -> PathBuf {
        let directory =
            std::env::temp_dir().join(format!("kink-flow-traces-{name}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&directory);
        directory
    }

    /// A runner of value runs that counts the runs it makes: `values` of [`cached_values`]
    /// under `key` for the record `recorded`, each run giving `given`.
    struct Counting {
        store: Store,
        runs: std::cell::Cell<u32>,
    }

    impl Counting {
        fn new(cache: &Path) -> Self {
            Self {
                store: Store::new(cache),
                runs: std::cell::Cell::new(0),
            }
        }

        fn values(
            &self,
            key: Option<&TraceKey>,
            recorded: &Value,
            given: &Result<Vec<ChannelValues>, ValuesRefusal>,
        ) -> Result<Vec<ChannelValues>, ValuesRefusal> {
            cached_values(key, &self.store, recorded, || {
                self.runs.set(self.runs.get() + 1);
                given.clone()
            })
        }
    }

    #[test]
    fn a_second_read_of_a_definition_trace_makes_no_value_run() {
        let cache = trace_cache("warm");
        let runner = Counting::new(&cache);
        let (stop, observe) = (json!({"count": 3}), json!({"points": ["ticks"]}));
        let both = ["ticks".to_owned(), "writes".to_owned()];
        let key = TraceKey::new(
            &cache,
            &result_of("definition", Some(stop.clone()), Some(observe.clone())),
            &both,
        );
        let given = Ok(recorded_values(&["ticks", "writes"]));
        let cold = runner.values(Some(&key), &recorded(), &given);
        assert_eq!(runner.runs.get(), 1);
        // Warm: no run, and the values are the run's, element for element: a value, an
        // undecided element, a null document, each point, each end.
        let warm = runner.values(Some(&key), &recorded(), &given);
        assert_eq!(runner.runs.get(), 1);
        assert_eq!(warm, cold);
        assert_eq!(warm, given);
        assert!(key.path.starts_with(cache.join("definition-traces")));
        let stored = std::fs::read(&key.path).unwrap();

        // Another definition, `[observe]`, `[stop]` or channel set is another key: each misses
        // and runs, and none replaces the entry.
        let ticks = ["ticks".to_owned()];
        let others = [
            (
                result_of("edited", Some(stop.clone()), Some(observe.clone())),
                &both[..],
            ),
            (
                result_of(
                    "definition",
                    Some(stop.clone()),
                    Some(json!({"points": ["ticks", "more"]})),
                ),
                &both[..],
            ),
            (
                result_of(
                    "definition",
                    Some(json!({"count": 4})),
                    Some(observe.clone()),
                ),
                &both[..],
            ),
            (
                result_of("definition", None, Some(observe.clone())),
                &both[..],
            ),
            (
                result_of("definition", Some(stop.clone()), Some(observe.clone())),
                &ticks[..],
            ),
        ];
        for (at, (result, channels)) in others.iter().enumerate() {
            let other = TraceKey::new(&cache, result, channels);
            assert_ne!(other.path, key.path, "{at}");
            let names = channels.iter().map(String::as_str).collect::<Vec<_>>();
            let given = Ok(recorded_values(&names));
            let before = runner.runs.get();
            assert_eq!(runner.values(Some(&other), &recorded(), &given), given);
            assert_eq!(runner.runs.get(), before + 1, "{at}");
            // The entry of another key at this key's path is never read for it.
            std::fs::copy(&key.path, &other.path).unwrap();
            assert_eq!(runner.values(Some(&other), &recorded(), &given), given);
            assert_eq!(runner.runs.get(), before + 2, "{at}");
            assert_eq!(runner.values(Some(&other), &recorded(), &given), given);
            assert_eq!(runner.runs.get(), before + 2, "{at}");
        }
        assert_eq!(std::fs::read(&key.path).unwrap(), stored);

        // The same key for another record (another run): a miss, whose values replace the entry.
        let mut moved = recorded();
        moved["channels"][0]["elements"][0] = json!("ffffffffffffffff");
        let before = runner.runs.get();
        assert_eq!(runner.values(Some(&key), &moved, &given), given);
        assert_eq!(runner.runs.get(), before + 1);
        assert_ne!(std::fs::read(&key.path).unwrap(), stored);
        assert_eq!(runner.values(Some(&key), &recorded(), &given), given);
        assert_eq!(runner.runs.get(), before + 2);
        assert_eq!(std::fs::read(&key.path).unwrap(), stored);

        // Without a key every read runs.
        assert_eq!(runner.values(None, &recorded(), &given), given);
        assert_eq!(runner.runs.get(), before + 3);
        let _ = std::fs::remove_dir_all(&cache);
    }

    #[test]
    fn a_damaged_definition_trace_misses_and_is_rewritten() {
        let cache = trace_cache("damaged");
        let runner = Counting::new(&cache);
        let both = ["ticks".to_owned(), "writes".to_owned()];
        let key = TraceKey::new(&cache, &result_of("definition", None, None), &both);
        let given = Ok(recorded_values(&["ticks", "writes"]));
        runner.values(Some(&key), &recorded(), &given).unwrap();
        let stored = std::fs::read_to_string(&key.path).unwrap();
        let mut runs = 1;
        // Cut short; a value changed under the record's own digest; no JSON at all.
        let changed = stored.replace("\"n\":2", "\"n\":7");
        assert_ne!(changed, stored);
        for damaged in [&stored[..stored.len() / 2], &changed, ""] {
            std::fs::write(&key.path, damaged).unwrap();
            assert_eq!(runner.values(Some(&key), &recorded(), &given), given);
            runs += 1;
            assert_eq!(runner.runs.get(), runs);
            assert_eq!(std::fs::read_to_string(&key.path).unwrap(), stored);
            assert_eq!(runner.values(Some(&key), &recorded(), &given), given);
            assert_eq!(runner.runs.get(), runs);
        }

        // An entry that carries its own digest and is not of the record: each part of it that
        // the record decides (the end, the number of elements, which of them have a value, the
        // channels) makes it a miss.
        let entry = values_entry(&recorded(), given.as_ref().unwrap()).unwrap();
        let names = key.key["channels"].as_array().unwrap().clone();
        assert_eq!(
            stored_values(&entry, &recorded(), &names).as_ref(),
            given.as_ref().ok()
        );
        let edits: [fn(&mut Value); 8] = [
            |entry| entry["recorded_sha256"] = json!("0"),
            |entry| entry["channels"][0]["closed"] = json!("undefined"),
            |entry| entry["channels"][1]["open"]["opening"] = json!("branch"),
            |entry| {
                entry["channels"][0]["elements"]
                    .as_array_mut()
                    .unwrap()
                    .pop();
            },
            |entry| entry["channels"][0]["elements"][1]["value"] = json!(1),
            |entry| {
                entry["channels"][0]["elements"][0]
                    .as_object_mut()
                    .unwrap()
                    .remove("value");
            },
            |entry| entry["channels"][0]["elements"][0]["point"]["side"] = json!("beside"),
            |entry| entry["channels"].as_array_mut().unwrap().swap(0, 1),
        ];
        for (at, edit) in edits.iter().enumerate() {
            let mut edited = entry.clone();
            edit(&mut edited);
            assert_eq!(stored_values(&edited, &recorded(), &names), None, "{at}");
        }
        let _ = std::fs::remove_dir_all(&cache);
    }

    #[test]
    fn only_a_completed_value_run_with_a_text_form_is_stored() {
        let cache = trace_cache("unstored");
        let runner = Counting::new(&cache);
        let ticks = ["ticks".to_owned()];
        let key = TraceKey::new(&cache, &result_of("definition", None, None), &ticks);
        // A value run that gave no values: a refusal, or a run that is not the recorded one.
        for refusal in [
            ValuesRefusal::Capture("the value run's record is not the recorded one".to_owned()),
            ValuesRefusal::SeveralPaths,
        ] {
            let given = Err(refusal);
            assert_eq!(runner.values(Some(&key), &recorded(), &given), given);
            assert_eq!(runner.values(Some(&key), &recorded(), &given), given);
            assert!(!key.path.exists());
        }
        assert_eq!(runner.runs.get(), 4);
        // kink's own contents: KORE patterns, which the entry has no text form of.
        let mut contents = recorded_values(&["ticks"]);
        contents[0].elements[0].element = Element::Content(Vec::new());
        let given = Ok(contents);
        assert_eq!(runner.values(Some(&key), &recorded(), &given), given);
        assert_eq!(runner.values(Some(&key), &recorded(), &given), given);
        assert_eq!(runner.runs.get(), 6);
        assert!(!key.path.exists());
        assert!(!cache.join(DEFINITION_TRACES_DIRECTORY).exists());
        let _ = std::fs::remove_dir_all(&cache);
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
