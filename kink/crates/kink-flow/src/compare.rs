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
//! is the program's baseline run as every command observes it (`[stop]`, `[budget]`, the cells
//! the projections keep, the result cache), its ends named by the same words: an end some path
//! reached at its last stop is `stopped`, one every path reached on its own is `final`. Neither
//! side names a rule or the computation: the words are the corpus's observation, which both
//! sides share.
//!
//! The comparison of cells is the front end's ([`Vocabulary`]): only a front end that reads the
//! definition's values has a cell vocabulary an implementation can write (krs: cells by Rust
//! field path, values as documents of the typed encoding) and views, functions of those values.
//! kink-flow's own front end reads K terms and has neither, so it refuses the command (stage
//! `implementation`, reason `unsupported-front-end`).
//!
//! Each (implementation, program, view) has one verdict: `equal`, `different` (with the first
//! difference), `could-not-apply` (the implementation's own answer, a disagreement with a reason
//! that is reported and never locked) or `not-compared` (with the reason: a compared cell the
//! implementation omits, a definition run with no end or several, a view that could not be
//! evaluated, a program outside the domain of the projection the view names, for which nothing
//! is asked and nothing counted). An *acceptance view* (`kind = "accepts"`) compares whether
//! each side accepts the program ([`Acceptance`], [`acceptance_row`]): the definition accepts at
//! an end reached at the corpus's stop or of a declared `finished` class, and rejects at one of a
//! declared `refused` class or of none; an implementation accepts by `stopped` or `final` and
//! rejects by `rejected`
//! ([`Protocol::V3`], with its own `message` and the definition's refusal it names,
//! `refused`, compared by the front end where both sides state a part,
//! [`Vocabulary::judge_refusal`]). An end view of a program the definition refuses at every end
//! is judged so too, and so is one of a program the definition rejects before it runs (its entry
//! states `expect = { rejected = .. }` and admission rejected it there: [`Definition::Rejected`]),
//! which has no end, no run and no start; a view that needs one of these is `not-compared`
//! (`rejected-before-run`), and an implementation given `start` is not asked about it. A run of
//! the implementation that exits non-zero, writes no answer the protocol reads, cannot be
//! started, or that the clock cancels is a failure of the
//! implementation, not a verdict: its row has `failure` and no verdicts, but for a crash (a
//! failure of kind `exit`) on a program whose acceptance the definition states, which its
//! acceptance views judge `different`. The clock (`time_ms`) only cancels a run, which then has
//! no answer; it never decides a verdict.
//!
//! A view naming a projection whose `relation` is `snapshot` judges the implementation's value
//! against the one a user accepted for the program, a file beside the flow ([`crate::snapshot`]),
//! and reads no side of the definition ([`snapshot_rows`]): under an `accepts` projection the
//! implementation's whole answer to whether it accepts the program (`accepted`, `rejected` with
//! its `message` and `refused`, or `crashed`), under an `end` projection the end as the answer
//! states it. A program with no accepted value is `pending`, which is no answer, never a failure.
//!
//! A view naming a `metric` projection measures one metric the implementation's answer states
//! (`metrics`, [`Protocol::V3`]; [`crate::metric`]) and reads no side of the definition
//! ([`metric_rows`]): a deterministic metric is judged against the baseline a user accepted for
//! the program (a snapshot, `{metric, value}`) in the projection's direction, `improved`,
//! `regressed` or `stayed` with the change, or `pending` without a baseline; a regression beyond
//! the projection's `max_regression` is a finding (status 1), and no other metric verdict decides
//! a status. A metric declared `host_dependent` is reported only (`measured`): no baseline, no
//! gate, no lock row, and its value is never read from or written to the answer cache. The front
//! end never sees a metric view: it compares no cell.
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
//! is that the same binary, given the same request, gives the same answer. An implementation
//! one of whose views measures a host-dependent metric is never answered from the cache and
//! never written to it, on every program: the value is the host's, so it must be this run's,
//! and no cached answer holds it. The verdict is
//! computed again from the answer on every run, against the definition's ends and the views as
//! they are then, so an edit of the definition, the corpus or a view is never answered from the
//! cache. Without `identity` nothing says which build answered, and the implementation always
//! runs.

use crate::admit::{InputFiles, admit_spec, case_root};
use crate::cli::{EXIT_NO, EXIT_UNANSWERED, EXIT_UNASKED, EXIT_YES, exit_join};
use crate::clock::Kept;
use crate::lock::{Lock, LockKind, Settle, compare_row_id};
use crate::manifest::{
    FlowManifest, Given, ImplementationSection, MetricSection, ObserveSection, Program,
    ProjectionSection, Protocol, RejectedStage, ViewSection,
};
use crate::results::{
    BaselineRunner, ProgramRow, ResultClass, cache_directory, current_record,
    record_final_configuration, result_key, result_store, runner_refusal, update_results,
};
use crate::snapshot::{self, Judgement, SNAPSHOT_DIFFERENCE_FORMAT, SnapshotKind};
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
/// 5 since every view entry has `distance` ([`Distance`] for an end view's `equal` or
/// `different`, the first difference's index or the agreeing elements for a trace view's
/// verdict, else null) and `summary` has `views`, each (implementation, view)'s `compared` and
/// `agreeing` programs, which `--output text` prints and a lock's `[[compare.view]]` rows hold.
/// 6 since acceptance is compared (projections PJ-02): a view may be an acceptance view
/// (`kind = "accepts"`), an implementation of `kink-implementation/3` may answer `rejected`
/// (its `message` and `refused` in the row's `answer`, an entry's `refused` where both sides'
/// rejections were compared and agree), `could-not-apply` is a disagreement (status 1, its
/// reason in no lock row), the verdict `definition-refused` is gone (an end view of a program
/// the definition refuses at every end is judged by acceptance), and a crash on a program
/// whose acceptance the definition states is `different` on its acceptance views, its row
/// keeping `failure` (with `decided`).
/// 7 since a flow declares named projections (projections PJ-10): a document of a flow that
/// declares `[[projection]]` names them (`projections`, [`FlowManifest::projections_value`]: each
/// projection's keys as written and, where it has `views` or `observer`, the identity of its
/// `observation` as the front end resolved it), and a view written `{ projection, required }`
/// carries the projection's keys and `projection` in `implementations[].views[]`. A flow that
/// declares no projection gives version 6's document but for its version.
/// 8 since a projection's `domain` is applied (projections PJ-10): a view naming a projection
/// whose domain does not hold a program is `not-compared` for `outside-domain` there (status 0,
/// in no count of `summary`), and the implementation is asked only for the views whose domain
/// holds the program (none: it is not run, and its row has no request); a row's `required` says
/// whether a required view holds the program. A flow that writes no `domain` gives version 7's
/// document but for its version.
/// 9 since a projection's relation may be a snapshot (projections PJ-20): a view naming one
/// judges the implementation's value against the file a user accepted for the program
/// ([`crate::snapshot`]): its entry has `snapshot` (the file, relative to the flow's directory),
/// the verdict `pending` (no file: status 3), the reason `snapshot-unreadable`,
/// a `different` entry's `difference` of format `kink-snapshot/1`, and `summary` has
/// `snapshots` and counts `pending`; a crash has a verdict under an `accepts` snapshot view, its
/// value `crashed`. A flow without a snapshot projection gives version 8's
/// document but for its version.
/// 10 since a program's entry may state that it is rejected before it runs (projections PJ-32):
/// its `programs` entry has the class `rejected` (met) or `accepted` (unmet); the definition
/// rejects a met one, which its acceptance views and end views judge by acceptance (a `rejected`
/// answer's `refused` compared with nothing: it states no declared class), and a view left
/// without what it compares (the start of an implementation given
/// `start`, a trace, inputs with a document) is `not-compared` for the reason
/// `rejected-before-run` (status 0); every view of an unmet one is `not-compared` (`definition`).
/// A flow whose entries state no rejection gives version 9's document but for its version.
/// 11 since an implementation of `kink-implementation/3` may state metrics of its run and a view
/// may measure one under a `metric` projection (projections PJ-21): a row's `answer` has
/// `metrics` where the answer states them; a metric view's entry has `metric` (`{name,
/// direction, value, baseline, change, exceeded}`, or `{name, value, host_dependent}`), the
/// verdicts `improved`, `regressed`, `stayed`, `measured` (a host-dependent metric) and
/// `pending` (no baseline), the reason `metric-unstated`; `summary` has `metrics` and counts the
/// metric verdicts. A flow without a metric projection gives version 10's document but for its
/// version.
pub const COMPARE_VERSION: u64 = 11;
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
    /// The view compares a cell the corpus's ends leave out (cells no projection compares,
    /// unobservable cells), which the definition's side does not state: fix the declaration or the
    /// corpus (2).
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
    /// A view naming a projection whose `domain` (its case patterns) does not hold the program:
    /// the projection does not apply to it, so the view asks and decides nothing there (0).
    OutsideDomain {
        projection: String,
        domain: Vec<String>,
    },
    /// A snapshot view whose snapshot file cannot be read as a value of its kind: fix the file
    /// (2).
    SnapshotUnreadable(String),
    /// The definition rejects the program before it runs, as its entry states (class
    /// `rejected`), and the view or the request needs what such a program does not have: a
    /// start (`given = "start"`), a run whose channels a trace view compares, or inputs with a
    /// document in the definition's vocabulary (a program rejected at `input`). Neither the
    /// declaration nor the corpus is at fault and no run can answer, so it decides nothing (0).
    RejectedBeforeRun(String),
    /// A metric view whose answer states no value of its metric (`metrics`): fix the
    /// implementation or the projection's `metric` (2).
    MetricUnstated(String),
}

/// The reason of a view a program rejected before it runs leaves without what it compares
/// ([`NotCompared::RejectedBeforeRun`]).
const REJECTED_BEFORE_RUN_REASON: &str = "rejected-before-run";

/// The reason of a view outside its projection's domain ([`NotCompared::OutsideDomain`]).
pub(crate) const OUTSIDE_DOMAIN_REASON: &str = "outside-domain";

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
            Self::OutsideDomain { .. } => OUTSIDE_DOMAIN_REASON,
            Self::SnapshotUnreadable(_) => "snapshot-unreadable",
            Self::RejectedBeforeRun(_) => REJECTED_BEFORE_RUN_REASON,
            Self::MetricUnstated(_) => "metric-unstated",
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
            | Self::NoEnd { detail, .. }
            | Self::SnapshotUnreadable(detail)
            | Self::RejectedBeforeRun(detail)
            | Self::MetricUnstated(detail) => detail.clone(),
            Self::OutsideDomain { projection, domain } => format!(
                "the program is outside the domain of the projection `{projection}` ({}): the \
                 projection does not apply to it",
                domain
                    .iter()
                    .map(|pattern| format!("`{pattern}`"))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }
    }

    /// The status of a required view not compared for this reason: [`EXIT_UNANSWERED`] where
    /// another approach may answer (a view that did not end, several ends), [`EXIT_UNASKED`]
    /// where the declaration or the corpus must change. An end view of a program with no end
    /// ([`Self::NoEnd`]) is [`EXIT_YES`] where a required trace view carries the requirement, and
    /// a view outside its projection's domain ([`Self::OutsideDomain`]) or left without what it
    /// compares by a program rejected before it runs ([`Self::RejectedBeforeRun`]) is
    /// [`EXIT_YES`]: it decides nothing, as a view that is not required decides nothing.
    #[must_use]
    pub const fn status(&self) -> u8 {
        match self {
            Self::SeveralEnds(_)
            | Self::Undecided(_)
            | Self::ClockStopped(_)
            | Self::SeveralPaths(_)
            | Self::ObservedNothing(_)
            | Self::NoEnd { carried: false, .. } => EXIT_UNANSWERED,
            Self::Omitted(_)
            | Self::LeftOut(_)
            | Self::Unreadable(_)
            | Self::SnapshotUnreadable(_)
            | Self::MetricUnstated(_) => EXIT_UNASKED,
            Self::NoEnd { carried: true, .. }
            | Self::OutsideDomain { .. }
            | Self::RejectedBeforeRun(_) => EXIT_YES,
        }
    }
}

/// How far apart two ends are under a view (an end view entry's `distance`): the compared cells
/// at which they differ and the view's compared cells. `differing_cells` counts the first
/// difference's cell and every other cell the front end names as differing (krs: `cell` and
/// `also_differ`, an instance of a `List` or `Map` collection counted at each index or key that
/// differs, a `Set` collection once); `compared_cells` counts the view's compared leaf cells by
/// declared path. The two are not on one scale where a collection differs at several instances,
/// so `differing_cells` may exceed `compared_cells`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Distance {
    pub differing_cells: usize,
    pub compared_cells: usize,
}

impl Distance {
    /// The distance's member of its entry.
    #[must_use]
    pub fn value(&self) -> Value {
        json!({"differing_cells": self.differing_cells, "compared_cells": self.compared_cells})
    }
}

/// The front end's comparison of one view: equal, different with the first difference (the
/// front end's document), or not compared.
#[derive(Clone, Debug, PartialEq)]
pub enum Judged {
    /// Every end of the definition agrees with the answer on the view's cells; `omitted` lists
    /// the cells the comparison left out because the implementation omits them, and
    /// `compared_cells` counts the view's compared leaf cells ([`Distance`]).
    Equal {
        omitted: Vec<String>,
        compared_cells: usize,
    },
    /// They differ, first here, and this far apart.
    Different {
        difference: Value,
        omitted: Vec<String>,
        distance: Distance,
    },
    /// The view is not compared.
    NotCompared(NotCompared),
}

impl Judged {
    /// The distance this comparison found: none for a view not compared.
    #[must_use]
    pub const fn distance(&self) -> Option<Distance> {
        match self {
            Self::Equal { compared_cells, .. } => Some(Distance {
                differing_cells: 0,
                compared_cells: *compared_cells,
            }),
            Self::Different { distance, .. } => Some(*distance),
            Self::NotCompared(_) => None,
        }
    }
}

/// The `distance` of an end view entry whose cells were not counted: an answer that states no
/// cells (`horizon`), or a word difference whose comparison of cells did not conclude.
const UNCOUNTED: Value = Value::Null;

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

    /// Whether the definition declares a `finished` end, without which no end of it can be
    /// told accepted from one it has no rule for: an acceptance view over it is refused (stage
    /// `implementation`, reason `no-finished-end`). None by default.
    fn declares_finished_end(&self) -> bool {
        false
    }

    /// Check a `rejected` answer's `refused` (`{end, reason}`) against the definition before it
    /// is compared: `end` an item of a declared refused end, `reason` a document at that end's
    /// reason type. The value is its canonical document, `{end, reason}` (`reason` null where it
    /// is not stated), which a lock row holds where it was compared. `Err` makes the answer
    /// malformed, naming the part.
    ///
    /// # Errors
    ///
    /// Why `refused` names no refusal of the definition; by default, that the front end reads no
    /// declared end.
    fn read_refusal(&self, refused: &Value) -> Result<Value, String> {
        let _ = refused;
        Err("this front end reads no declared end, so it cannot read `refused`".to_owned())
    }

    /// Compare the definition's ends with a mutant's ends of one program under one `end`
    /// projection of the flow ([`EndsQuestion`]), for `run`'s judgement of a kill under it
    /// ([`crate::projected`]): equal when the two sets of ends are equal under the projection's
    /// cells and views (its views evaluated at both sides in the projection's one observer),
    /// different with the first difference otherwise, inconclusive where a view's evaluation is
    /// undecided or a side cannot be read. Never a difference that is not one: `run` counts a
    /// difference as a kill.
    ///
    /// # Errors
    ///
    /// Why the front end cannot compare ends under the projection; by default, that it compares
    /// none. `run` makes the program `unknown` under the projection, with the error as its reason.
    fn compare_ends(&self, question: &EndsQuestion<'_>) -> Result<EndsJudged, String> {
        let _ = question;
        Err("this front end compares no ends under a projection".to_owned())
    }

    /// Compare a `rejected` answer's `refused` with each of the definition's ends (every one of
    /// them rejected), on the parts of their declared class both state ([`RefusalJudged`]).
    ///
    /// # Errors
    ///
    /// A failure of the comparison itself, which fails the command.
    fn judge_refusal(&self, question: &RefusalQuestion<'_>) -> Result<RefusalJudged, String> {
        let _ = question;
        Err("this front end compares no refusal".to_owned())
    }
}

/// One question to the front end for `run` ([`Vocabulary::compare_ends`]): the definition's ends
/// and a mutant's ends of one program, compared under one `end` projection of the flow.
pub struct EndsQuestion<'a> {
    /// The projection, as the flow declares it (its `compare` in the front end's spelling).
    pub projection: &'a ProjectionSection,
    /// The definition's ends, final configurations of the K kink judges as its result slot
    /// compares them: each cell of `not_compared` replaced by `\top` of its sort, the counter
    /// erased.
    pub baseline: &'a BTreeSet<Pattern>,
    /// The mutant's ends, every one of them (the mutant's run is complete), projected as the
    /// definition's are; each is data under the definition.
    pub mutant: &'a BTreeSet<Pattern>,
    /// The cells the corpus's ends leave out, by K cell name.
    pub not_compared: &'a [String],
}

/// The front end's comparison of two sets of ends under a projection ([`EndsQuestion`]).
#[derive(Clone, Debug, PartialEq)]
pub enum EndsJudged {
    /// The sets of ends are equal under the projection.
    Equal,
    /// They differ: the first difference (the front end's document).
    Different(Value),
    /// The comparison does not conclude: why.
    Inconclusive(String),
}

/// One question to the front end: a `rejected` answer's `refused` against the definition's ends
/// on a program the definition rejects at every end ([`Vocabulary::judge_refusal`]).
pub struct RefusalQuestion<'a> {
    /// The answer's `refused`, as written; [`Vocabulary::read_refusal`] accepted it.
    pub refused: &'a Value,
    /// The definition's ends, as [`Question::ends`].
    pub ends: &'a BTreeSet<Pattern>,
    /// The cells the corpus's ends leave out, by K cell name.
    pub not_compared: &'a [String],
}

/// The front end's comparison of an answer's refusal with the definition's ends, on the parts of
/// their declared class both state (krs: an end's `class`, `end` and `reason`).
#[derive(Clone, Debug, PartialEq)]
pub enum RefusalJudged {
    /// It agrees with every end.
    Agree,
    /// It agrees with no end: the first difference (the front end's document).
    Different(Value),
    /// It agrees with some ends and not others: one answer against several ends is inclusion.
    SeveralEnds(String),
    /// A comparison could not conclude.
    Undecided(String),
}

/// The format of an acceptance difference ([`acceptance_difference`]).
pub const ACCEPTS_DIFFERENCE_FORMAT: &str = "kink-accepts/1";

/// Whether the definition accepts a program, from its baseline's ends: every end accepted (one
/// reached at the corpus's stop, or of a declared `finished` class), every end rejected (of a
/// declared `refused` class, or `none`: no declared end holds where no rule applies), or why
/// neither is known.
#[derive(Clone, Debug, PartialEq)]
pub enum Acceptance {
    Accepted,
    Rejected,
    NotCompared(NotCompared),
}

/// The definition's acceptance of a program whose baseline ends are summarized by `summaries`
/// (a program row's `ends`, with `halt` under `[stop]` and `declared` where the definition
/// declares ends).
pub(crate) fn ends_acceptance(summaries: &[Value]) -> Acceptance {
    match ends_acceptance_of(
        summaries,
        "the definition's run",
        "one answer against both is a question of inclusion, which compare does not decide",
    ) {
        Some(acceptance) => acceptance,
        None => Acceptance::NotCompared(NotCompared::Unreadable(
            "the baseline's record names no end".to_owned(),
        )),
    }
}

/// [`ends_acceptance`] of the run `side` names (its reasons say whose run it is, and `several`
/// why ends of both kinds decide nothing), `None` where `summaries` is empty: the same rule, for
/// the baseline's ends and for a mutant's (`crate::projected`, a kill under an `accepts`
/// projection).
pub(crate) fn ends_acceptance_of(
    summaries: &[Value],
    side: &str,
    several: &str,
) -> Option<Acceptance> {
    let mut accepted = 0;
    let mut rejected = 0;
    for summary in summaries {
        if summary["halt"] == "stop" {
            accepted += 1;
            continue;
        }
        match summary["declared"].as_str() {
            Some("finished") => accepted += 1,
            Some("refused" | "none") => rejected += 1,
            Some(class @ ("undecided" | "overlap")) => {
                return Some(Acceptance::NotCompared(NotCompared::Undecided(format!(
                    "the class of an end of {side} is `{class}`{}: whether it accepts the \
                     program is not known",
                    summary["declared_detail"]
                        .as_str()
                        .map(|detail| format!(" ({detail})"))
                        .unwrap_or_default()
                ))));
            }
            _ => {
                return Some(Acceptance::NotCompared(NotCompared::Undecided(format!(
                    "an end of {side} has no declared class: whether it accepts the program is \
                     not known"
                ))));
            }
        }
    }
    Some(match (accepted, rejected) {
        (0, 0) => return None,
        (_, 0) => Acceptance::Accepted,
        (0, _) => Acceptance::Rejected,
        _ => Acceptance::NotCompared(NotCompared::SeveralEnds(format!(
            "{side} accepts the program on some path and rejects it on another: {several}"
        ))),
    })
}

/// The definition's acceptance of the program whose definition side is `definition` and whose
/// baseline row is `row`.
fn definition_acceptance(definition: &Definition, row: &Value) -> Acceptance {
    match definition {
        Definition::Ends { .. } => ends_acceptance(
            row["ends"]
                .as_array()
                .map(Vec::as_slice)
                .unwrap_or_default(),
        ),
        Definition::Prefix { .. } => Acceptance::NotCompared(NotCompared::NoEnd {
            detail: "the definition's run of the program is cut by its bounds before it ends \
                     (`comparable-prefix`): whether it accepts the program is not known yet"
                .to_owned(),
            carried: false,
        }),
        Definition::None { class, .. } => Acceptance::NotCompared(NotCompared::Unreadable(
            format!("the definition's run of the program is `{class}`: it has no end"),
        )),
        // A rejection before the run is a rejection (README D2: the stage is not observed).
        Definition::Rejected { .. } => Acceptance::Rejected,
    }
}

/// An acceptance difference: `{format: "kink-accepts/1", definition, implementation}`, each side
/// `accepts`, `rejects`, or, for the implementation, what it answered instead (`horizon`: it did
/// not end; `crashed`: its run failed with kind `exit`).
fn acceptance_difference(definition: &str, implementation: &str) -> Value {
    json!({
        "format": ACCEPTS_DIFFERENCE_FORMAT,
        "definition": definition,
        "implementation": implementation,
    })
}

/// How an answer stands to acceptance: `accepts` (`stopped`, `final`), `rejects` (`rejected`),
/// `horizon` (it has not ended); `None` for `could-not-apply`, which has its own verdict.
const fn answer_acceptance(stated: &Stated) -> Option<&'static str> {
    match &stated.end {
        StatedEnd::Ended(_) => Some("accepts"),
        StatedEnd::Rejected { .. } => Some("rejects"),
        StatedEnd::Horizon => Some("horizon"),
        StatedEnd::CouldNotApply(_) => None,
    }
}

/// The verdict of a view judged by acceptance (an acceptance view, or an end view of a program
/// the definition refuses at every end), on an answer that is not `could-not-apply`: `equal`
/// where both sides accept, or both reject and agree on the refusal's parts both state
/// (`refusal`, the front end's comparison where the answer states `refused`, and `refused`,
/// its canonical document, which the row then holds); `different` otherwise, naming both
/// sides. It compares no cell, so its `distance` is null.
fn acceptance_row(
    view: &ViewSection,
    definition: &Acceptance,
    stated: &Stated,
    refusal: Option<&(Value, RefusalJudged)>,
) -> Value {
    let mut row = view_row(view);
    let definition = match definition {
        Acceptance::NotCompared(reason) => {
            not_compared_row(&mut row, reason);
            return row;
        }
        Acceptance::Accepted => "accepts",
        Acceptance::Rejected => "rejects",
    };
    let answer = answer_acceptance(stated).unwrap_or("could-not-apply");
    if definition != answer {
        row["verdict"] = json!("different");
        row["difference"] = acceptance_difference(definition, answer);
        return row;
    }
    match refusal {
        None => row["verdict"] = json!("equal"),
        Some((refused, RefusalJudged::Agree)) => {
            row["verdict"] = json!("equal");
            row["refused"] = refused.clone();
        }
        Some((_, RefusalJudged::Different(difference))) => {
            row["verdict"] = json!("different");
            row["difference"] = difference.clone();
        }
        Some((_, RefusalJudged::SeveralEnds(detail))) => {
            not_compared_row(&mut row, &NotCompared::SeveralEnds(detail.clone()));
        }
        Some((_, RefusalJudged::Undecided(detail))) => {
            not_compared_row(&mut row, &NotCompared::Undecided(detail.clone()));
        }
    }
    row
}

/// The row of an acceptance view on a program whose implementation run crashed (a failure of
/// kind `exit`: it exited with a failure status or a signal ended it): `different`, the implementation side `crashed`, where the definition
/// states its acceptance (README D1: a crash on a program the definition accepts or rejects is
/// a defect of the implementation on it, a function of the binary and the request); `None`
/// where it does not, so the view has no verdict, as on every other failure.
fn crashed_row(view: &ViewSection, definition: &Acceptance) -> Option<Value> {
    let definition = match definition {
        Acceptance::Accepted => "accepts",
        Acceptance::Rejected => "rejects",
        Acceptance::NotCompared(_) => return None,
    };
    let mut row = view_row(view);
    row["verdict"] = json!("different");
    row["difference"] = acceptance_difference(definition, "crashed");
    Some(row)
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
    /// The signal that ended it, when one did: the crash's value under a snapshot of an
    /// `accepts` projection ([`crate::snapshot::crashed`]); no member of the row's `failure`.
    pub signal: Option<i32>,
    /// The end of its stderr, when it wrote some.
    pub stderr: Option<String>,
}

impl Failure {
    pub(crate) fn new(kind: &'static str, detail: impl Into<String>) -> Self {
        Self {
            kind,
            detail: detail.into(),
            exit_code: None,
            signal: None,
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
    /// `rejected` ([`Protocol::V3`]): the implementation rejects the program. `message` is its
    /// own text, reported and never compared; `refused` the definition's declared refused end
    /// it names (`{end, reason}`, as written), compared with the definition's where both state
    /// a part ([`Vocabulary::judge_refusal`]).
    Rejected {
        message: Option<String>,
        refused: Option<Value>,
    },
}

/// An answer of either protocol, read ([`read_answer`], [`read_answer_2`]).
#[derive(Clone, Debug, PartialEq)]
pub struct Stated {
    pub end: StatedEnd,
    /// Its end's cells, where it states them.
    pub cells: Option<Value>,
    /// Its `observations` ([`Protocol::V2`]), where the request asked for them.
    pub observations: Option<Value>,
    /// Its `metrics` ([`Protocol::V3`]), where it states them: each a count of its run
    /// ([`crate::metric`]).
    pub metrics: Option<Map<String, Value>>,
}

impl From<Answer> for Stated {
    fn from(answer: Answer) -> Self {
        match answer {
            Answer::Ended { end, cells } => Self {
                end: StatedEnd::Ended(end),
                cells: Some(cells),
                observations: None,
                metrics: None,
            },
            Answer::CouldNotApply { reason } => Self {
                end: StatedEnd::CouldNotApply(reason),
                cells: None,
                observations: None,
                metrics: None,
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
            StatedEnd::Rejected { .. } => "rejected",
        }
    }

    /// The answer's member of its row: `{end, reason}` (its cells and its observations are
    /// compared, not shown), and its `metrics` where it states them (reported).
    fn value(&self) -> Value {
        let mut value = match &self.end {
            StatedEnd::CouldNotApply(reason) => json!({"end": self.word(), "reason": reason}),
            StatedEnd::Rejected { message, refused } => {
                json!({"end": self.word(), "reason": null, "message": message, "refused": refused})
            }
            _ => json!({"end": self.word(), "reason": null}),
        };
        if let Some(metrics) = &self.metrics {
            value["metrics"] = Value::Object(metrics.clone());
        }
        value
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
    read_answer_of(Protocol::V2, bytes, asked)
}

/// Read an answer document of [`Protocol::V3`]: one of [`Protocol::V2`] ([`read_answer_2`]), or
/// `end: "rejected"`, with an optional `message` (a string) and an optional `refused` (an
/// object of `end`, a nonempty string, and optionally `reason`), no `cells` and no `reason`, and
/// `observations` exactly as a `stopped` or `final` answer has them. `message` and `refused`
/// belong to a `rejected` answer only. Any answer but `could-not-apply` may also state `metrics`,
/// an object of metric names to counts of its run ([`crate::metric::read_metrics`]).
///
/// # Errors
///
/// Why the bytes are no answer.
pub fn read_answer_3(bytes: &[u8], asked: Asked) -> Result<Stated, String> {
    read_answer_of(Protocol::V3, bytes, asked)
}

/// Read an answer of `protocol`, [`Protocol::V2`] or [`Protocol::V3`] ([`read_answer_2`],
/// [`read_answer_3`]).
fn read_answer_of(protocol: Protocol, bytes: &[u8], asked: Asked) -> Result<Stated, String> {
    let rejections = protocol.has_rejections();
    let metrics = protocol.has_metrics();
    let protocol = protocol.as_str();
    let document: Value = serde_json::from_slice(bytes)
        .map_err(|error| format!("stdout is not one JSON document: {error}"))?;
    let Value::Object(mut object) = document else {
        return Err("the answer is not a JSON object".to_owned());
    };
    if let Some(key) = object.keys().find(|key| {
        !matches!(key.as_str(), "end" | "cells" | "reason" | "observations")
            && !(rejections && matches!(key.as_str(), "message" | "refused"))
            && !(metrics && key.as_str() == "metrics")
    }) {
        return Err(if rejections {
            format!(
                "the answer has the key `{key}`; an answer holds `end`, `cells`, `reason`, \
                 `observations`, `message`, `refused` and `metrics` only ({protocol})"
            )
        } else {
            format!(
                "the answer has the key `{key}`; an answer holds `end`, `cells`, `reason` and \
                 `observations` only ({protocol})"
            )
        });
    }
    let words = if rejections {
        "`stopped`, `final`, `horizon`, `rejected` or `could-not-apply`"
    } else {
        "`stopped`, `final`, `horizon` or `could-not-apply`"
    };
    let end = object
        .get("end")
        .and_then(Value::as_str)
        .ok_or_else(|| format!("the answer has no `end` string ({words})"))?;
    if end != "rejected" {
        for key in ["message", "refused"] {
            if object.contains_key(key) {
                return Err(format!(
                    "a `{end}` answer states no `{key}`: only a `rejected` answer does"
                ));
            }
        }
    }
    let end = match end {
        "stopped" => StatedEnd::Ended(EndWord::Stopped),
        "final" => StatedEnd::Ended(EndWord::Final),
        "horizon" => StatedEnd::Horizon,
        "rejected" if rejections => {
            let message = match object.remove("message") {
                None => None,
                Some(Value::String(message)) => Some(message),
                Some(_) => return Err("`message` is not a string".to_owned()),
            };
            let refused = match object.remove("refused") {
                None => None,
                Some(Value::Object(refused)) => {
                    if let Some(key) = refused
                        .keys()
                        .find(|key| !matches!(key.as_str(), "end" | "reason"))
                    {
                        return Err(format!(
                            "`refused` has the key `{key}`; it holds `end` (a declared refused \
                             end's item) and `reason` only"
                        ));
                    }
                    if !refused
                        .get("end")
                        .and_then(Value::as_str)
                        .is_some_and(|end| !end.trim().is_empty())
                    {
                        return Err("`refused` names its `end`, a declared refused end's item, \
                                    as a nonempty string"
                            .to_owned());
                    }
                    Some(Value::Object(refused))
                }
                Some(_) => return Err("`refused` is not a JSON object".to_owned()),
            };
            StatedEnd::Rejected { message, refused }
        }
        "could-not-apply" => {
            for key in ["cells", "observations", "metrics"] {
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
                metrics: None,
            });
        }
        other => {
            return Err(format!("`end` is `{other}`, not {words}"));
        }
    };
    let word = match &end {
        StatedEnd::Ended(end) => end.as_str(),
        StatedEnd::Rejected { .. } => "rejected",
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
        (Some(_), StatedEnd::Rejected { .. }) => {
            return Err(
                "a `rejected` answer states no `cells`: its rejection is what it observes"
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
    let metrics = object
        .remove("metrics")
        .map(crate::metric::read_metrics)
        .transpose()?;
    Ok(Stated {
        end,
        cells,
        observations,
        metrics,
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
            signal: signal(status),
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

/// The signal that ended a run, where the platform says.
fn signal(status: std::process::ExitStatus) -> Option<i32> {
    #[cfg(unix)]
    {
        std::os::unix::process::ExitStatusExt::signal(&status)
    }
    #[cfg(not(unix))]
    {
        let _ = status;
        None
    }
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
        /// Whether every end is of a declared `refused` class (its summary's `declared`,
        /// `crate::evidence`, "Declared ends"), so the end views judge the answer by acceptance.
        refused: bool,
    },
    /// The program's baseline was cut by its bounds before it ended (`comparable-prefix`): it
    /// has no end, and its channels' elements up to their horizons, which a trace view compares.
    Prefix { cause: Option<String> },
    /// The program's baseline has no end to compare: its class, its cause.
    None {
        class: String,
        cause: Option<String>,
    },
    /// The definition rejects the program before it runs, at the stage its entry states (class
    /// `rejected`; the `programs` entry's `cause` is the refusal): it has no start, no run and no
    /// end, and it rejects the program, which its acceptance views and its end views judge
    /// ([`acceptance_row`]).
    Rejected { stage: RejectedStage },
}

impl Definition {
    /// The stage at which the definition rejects the program before it runs, if it does.
    const fn rejected_before_run(&self) -> Option<RejectedStage> {
        match self {
            Self::Rejected { stage } => Some(*stage),
            _ => None,
        }
    }
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
    // Admission rejected the program at the stage its entry states (`rejected`): the definition
    // rejects it. One admission admitted (`accepted`, an unmet statement) runs nothing, so the
    // whole pipeline's acceptance of it is not known, and it is `None` as every class with no end.
    if class == ResultClass::Rejected.as_str()
        && let Some(stage) = program.rejected
    {
        return Definition::Rejected { stage };
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
    let refused = refused_everywhere(
        row.row["ends"]
            .as_array()
            .map(Vec::as_slice)
            .unwrap_or_default(),
    );
    Definition::Ends {
        ends,
        words,
        refused,
    }
}

/// Whether the definition refuses a program whose baseline ends are `summaries` (a program row's
/// `ends`) at every end, each of a declared `refused` class: its end views then compare the
/// answer by acceptance ([`acceptance_row`]), since the definition states no end to compare an
/// answer's cells with, only that it rejects the program. Where it also states another end, an
/// answer is compared with the ends as before, since a refusal on one path does not answer for
/// another.
fn refused_everywhere(summaries: &[Value]) -> bool {
    !summaries.is_empty()
        && summaries
            .iter()
            .all(|summary| summary["declared"] == "refused")
}

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
        // The words decide the verdict; the cells, where the answer states them, are compared
        // for the distance alone, so a comparison that does not conclude (or fails) leaves the
        // distance uncounted and decides nothing.
        let distance = stated.cells.as_ref().and_then(|cells| {
            vocabulary
                .compare(&Question {
                    implementation,
                    view,
                    cells,
                    ends,
                    not_compared,
                })
                .ok()?
                .distance()
        });
        row["distance"] = distance.map_or(UNCOUNTED, |distance| distance.value());
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
        let distance = judged.distance();
        match judged {
            Judged::Equal { omitted, .. } => {
                row["verdict"] = json!("equal");
                row["omitted"] = json!(omitted);
            }
            Judged::Different {
                difference,
                omitted,
                ..
            } => {
                row["verdict"] = json!("different");
                row["difference"] = difference;
                row["omitted"] = json!(omitted);
            }
            Judged::NotCompared(reason) => not_compared_row(&mut row, &reason),
        }
        if let Some(distance) = distance {
            row["distance"] = distance.value();
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
    acceptance: Option<&AcceptanceSide<'_>>,
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
        } else if view.accepts {
            match acceptance {
                Some(side) => acceptance_row(view, side.definition, stated, side.refusal),
                None => {
                    return Err(format!(
                        "the acceptance view `{}` was not judged",
                        view.name
                    ));
                }
            }
        } else if let Some(side) = acceptance.filter(|side| side.refused_everywhere) {
            // The definition rejects the program at every end, of a declared refused class: it
            // states no end whose cells an answer could match, so the end view asks whether the
            // answer rejects it too.
            acceptance_row(view, &Acceptance::Rejected, stated, side.refusal)
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

/// The kind of value the snapshot projection `view` names observes ([`crate::snapshot`]): `None`
/// for a view that names no projection or one whose relation is not a snapshot.
fn snapshot_kind(manifest: &FlowManifest, view: &ViewSection) -> Option<SnapshotKind> {
    let projection = manifest.projection(view.projection.as_deref()?)?;
    if projection.is_snapshot() {
        SnapshotKind::of(projection.kind)
    } else {
        None
    }
}

/// The metric `view` measures, where it names a `metric` projection ([`crate::metric`]).
fn metric_of(manifest: &FlowManifest, view: &ViewSection) -> Option<MetricSection> {
    manifest.projection(view.projection.as_deref()?)?.metric
}

/// `implementation` as the front end sees it: without its metric views, which kink-flow judges
/// alone and which compare no cell ([`metric_rows`]); `None` where it has none.
fn without_metric_views(
    manifest: &FlowManifest,
    implementation: &ImplementationSection,
) -> Option<ImplementationSection> {
    implementation
        .views
        .iter()
        .any(|view| metric_of(manifest, view).is_some())
        .then(|| ImplementationSection {
            views: implementation
                .views
                .iter()
                .filter(|view| metric_of(manifest, view).is_none())
                .cloned()
                .collect(),
            ..implementation.clone()
        })
}

/// Whether some view of `implementation` measures a host-dependent metric.
fn measures_host(manifest: &FlowManifest, implementation: &ImplementationSection) -> bool {
    implementation
        .views
        .iter()
        .any(|view| metric_of(manifest, view).is_some_and(|metric| metric.host_dependent))
}

/// The row of the metric view `view` (measuring `metric`) of `program`: on an answer, the value
/// its `metrics` states (`not-compared`, `metric-unstated`, where it states none), reported
/// (`measured`) for a host-dependent metric, else judged against the baseline a user accepted
/// ([`crate::metric::baseline`], a snapshot beside the flow): `improved`, `regressed`, `stayed`
/// or `pending` (no baseline), with `metric: {name, direction, value, baseline, change,
/// exceeded}` (`exceeded` where the projection has `max_regression`, which makes a regression
/// beyond it status 1), and the value pushed on `observed_values` (what `accept` writes);
/// `could-not-apply` (README D6). A crash states no value: no row.
fn metric_rows(
    manifest: &FlowManifest,
    view: &ViewSection,
    metric: &MetricSection,
    program: &Program,
    observation: &Observation<'_>,
    observed_values: &mut Vec<SnapshotObserved>,
) -> Option<Value> {
    let Observation::Answer(stated) = observation else {
        return None;
    };
    let projection = view.projection.as_deref().unwrap_or(&view.name);
    let relative = snapshot::relative(projection, &program.id);
    let mut row = view_row(view);
    if !metric.host_dependent {
        row["snapshot"] = json!(relative);
    }
    if let StatedEnd::CouldNotApply(reason) = &stated.end {
        row["verdict"] = json!("could-not-apply");
        row["detail"] = json!(reason);
        return Some(row);
    }
    let Some(value) = crate::metric::stated(stated.metrics.as_ref(), &metric.name) else {
        not_compared_row(
            &mut row,
            &NotCompared::MetricUnstated(format!(
                "the answer states no value of the metric `{}` (`metrics`)",
                metric.name
            )),
        );
        return Some(row);
    };
    row["status"] = json!(EXIT_YES);
    if metric.host_dependent {
        row["verdict"] = json!("measured");
        row["metric"] = json!({"name": metric.name, "value": value, "host_dependent": true});
        return Some(row);
    }
    row["metric"] = json!({
        "name": metric.name,
        "direction": metric.direction.as_str(),
        "value": value,
        "baseline": null,
        "change": null,
        "exceeded": null,
    });
    observed_values.push(SnapshotObserved {
        program: program.id.clone(),
        projection: projection.to_owned(),
        value: crate::metric::baseline(&metric.name, value),
    });
    let file = snapshot::path(&manifest.directory, projection, &program.id);
    let baseline = match snapshot::read(&file) {
        snapshot::Reference::Missing => {
            row["verdict"] = json!("pending");
            row["detail"] = json!(format!(
                "no baseline is accepted for the program: {relative} does not exist"
            ));
            row["status"] = json!(EXIT_UNANSWERED);
            return Some(row);
        }
        snapshot::Reference::Unreadable(why) => Err(why),
        snapshot::Reference::Value(accepted) => crate::metric::baseline_of(&accepted, &metric.name),
    };
    match baseline {
        Err(why) => not_compared_row(
            &mut row,
            &NotCompared::SnapshotUnreadable(format!("the baseline {relative}: {why}")),
        ),
        Ok(baseline) => {
            let judged = crate::metric::judge(metric, value, baseline);
            row["verdict"] = json!(judged.verdict);
            row["metric"]["baseline"] = json!(baseline);
            row["metric"]["change"] = json!(judged.change);
            row["metric"]["exceeded"] = json!(judged.exceeded);
            if judged.exceeded == Some(true) {
                row["status"] = json!(EXIT_NO);
            }
        }
    }
    Some(row)
}

/// The value a snapshot view observed of one (implementation, program): what `accept` writes
/// ([`crate::accept`]), the value [`snapshot_rows`] judged.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct SnapshotObserved {
    /// The program's id.
    pub program: String,
    /// The snapshot projection the view names.
    pub projection: String,
    pub value: snapshot::SnapshotValue,
}

/// What a snapshot view of one (implementation, program) judges: the implementation's answer,
/// or its run that crashed (a failure of kind `exit`).
enum Observation<'a> {
    Answer(&'a Stated),
    Crash(&'a Failure),
}

/// The rows of `implementation`'s snapshot views on `program`, in the declaration's order, `None`
/// for each other view. A snapshot view judges the value the implementation states
/// ([`snapshot::observed`]), or, under an `accepts` projection, the crash ([`snapshot::crashed`]),
/// against the file a user accepted for the program ([`snapshot::path`], beside the flow), and
/// reads no side of the definition: `equal`, `different` (`kink-snapshot/1`: both values and a
/// line diff), `pending` (no file: no answer, status 3), `not-compared` (`snapshot-unreadable`),
/// or `could-not-apply` (README D6). A crash gives an `end` snapshot view no row: it states no
/// end. Each row names its file (`snapshot`, relative to the flow's directory). Each value judged
/// is also pushed on `observed_values`. A metric view's row is [`metric_rows`]'s.
fn snapshot_rows(
    manifest: &FlowManifest,
    implementation: &ImplementationSection,
    program: &Program,
    observation: &Observation<'_>,
    observed_values: &mut Vec<SnapshotObserved>,
) -> Vec<Option<Value>> {
    implementation
        .views
        .iter()
        .map(|view| {
            if let Some(metric) = metric_of(manifest, view) {
                return metric_rows(
                    manifest,
                    view,
                    &metric,
                    program,
                    observation,
                    observed_values,
                );
            }
            let kind = snapshot_kind(manifest, view)?;
            let observed = match observation {
                Observation::Answer(stated) => snapshot::observed(kind, stated),
                Observation::Crash(failure) => match kind {
                    SnapshotKind::Acceptance => Some(snapshot::crashed(failure)),
                    SnapshotKind::End => return None,
                },
            };
            let projection = view.projection.as_deref().unwrap_or(&view.name);
            let relative = snapshot::relative(projection, &program.id);
            let mut row = view_row(view);
            row["snapshot"] = json!(relative);
            let Some(observed) = observed else {
                // `could-not-apply`, the one answer that states no value.
                if let Observation::Answer(Stated {
                    end: StatedEnd::CouldNotApply(reason),
                    ..
                }) = observation
                {
                    row["verdict"] = json!("could-not-apply");
                    row["detail"] = json!(reason);
                }
                return Some(row);
            };
            let file = snapshot::path(&manifest.directory, projection, &program.id);
            let judgement = snapshot::judge(&observed, &snapshot::read(&file));
            observed_values.push(SnapshotObserved {
                program: program.id.clone(),
                projection: projection.to_owned(),
                value: observed,
            });
            match judgement {
                Judgement::Equal => row["verdict"] = json!("equal"),
                Judgement::Different(difference) => {
                    row["verdict"] = json!("different");
                    row["difference"] = difference;
                }
                Judgement::Pending => {
                    row["verdict"] = json!("pending");
                    row["detail"] = json!(format!(
                        "no value is accepted for the program: {relative} does not exist"
                    ));
                    row["status"] = json!(EXIT_UNANSWERED);
                }
                Judgement::Unreadable(why) => not_compared_row(
                    &mut row,
                    &NotCompared::SnapshotUnreadable(format!("the snapshot {relative}: {why}")),
                ),
            }
            Some(row)
        })
        .collect()
}

/// `implementation` without its snapshot views (those `snapshots` has a row of), which the
/// definition's side judges; `None` where it has none.
fn without_snapshot_views(
    implementation: &ImplementationSection,
    snapshots: &[Option<Value>],
) -> Option<ImplementationSection> {
    snapshots
        .iter()
        .any(Option::is_some)
        .then(|| ImplementationSection {
            views: implementation
                .views
                .iter()
                .zip(snapshots)
                .filter(|(_, row)| row.is_none())
                .map(|(view, _)| view.clone())
                .collect(),
            ..implementation.clone()
        })
}

/// The rows of every view in the declaration's order: each snapshot view's of `snapshots`, and
/// each other view's of `judged`, in their order.
fn with_snapshot_rows(snapshots: Vec<Option<Value>>, judged: Vec<Value>) -> Vec<Value> {
    let mut judged = judged.into_iter();
    snapshots
        .into_iter()
        .filter_map(|row| row.or_else(|| judged.next()))
        .collect()
}

/// What the views judged by acceptance read of one (implementation, program) with an answer:
/// the definition's acceptance, whether it refuses the program at every end (so its end views
/// are judged by acceptance too), and, where the answer is `rejected` with a `refused` and the
/// definition rejects the program, its canonical document and the front end's comparison.
pub struct AcceptanceSide<'a> {
    pub definition: &'a Acceptance,
    pub refused_everywhere: bool,
    pub refusal: Option<&'a (Value, RefusalJudged)>,
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
            row["distance"] = json!({"first_difference": {
                "channel": difference.channel,
                "index": difference.index,
            }});
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
    // The elements that agree on each channel, the trace view's `distance` where nothing differs.
    let mut agreeing = Map::new();
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
        agreeing.insert(channel.clone(), json!(elements));
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
        row["distance"] = json!({"agreeing_elements": agreeing});
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
        row["distance"] = json!({"agreeing_elements": agreeing});
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
        "distance": null,
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
                // An unmet statement: admission admitted the program, which by its statement runs
                // nothing.
                Some(cause) if class == ResultClass::Accepted.as_str() => format!(
                    "the program's entry states that the definition rejects it before it runs, \
                     and admission admits it ({cause}): it runs nothing, so the definition states \
                     neither an end nor whether its pipeline accepts the program"
                ),
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
/// (`equal` [`EXIT_YES`]; `different` and `could-not-apply` [`EXIT_NO`], the implementation
/// stating that it does not apply a program being a disagreement with a reason; `not-compared`
/// its reason's status; a metric view's `improved`, `regressed`, `stayed` and `measured` its own
/// ([`EXIT_NO`] for a regression beyond the projection's `max_regression`, else [`EXIT_YES`]);
/// `agree-up-to` its own: [`EXIT_YES`] where the definition limits every
/// horizon, [`EXIT_UNANSWERED`] where the implementation's answer limits one), and of its
/// failure where some required view has no verdict (`failure.decided` false: a crash its
/// acceptance views judged decides only them). A view that is not required decides nothing.
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
                Some("equal") => EXIT_YES,
                Some("different" | "could-not-apply") => EXIT_NO,
                Some("pending") => EXIT_UNANSWERED,
                // A metric's verdict states its own status: 1 for a regression beyond its
                // projection's `max_regression`, else 0.
                Some(
                    "not-compared" | "agree-up-to" | "improved" | "regressed" | "stayed"
                    | "measured",
                ) => view["status"]
                    .as_u64()
                    .and_then(|status| u8::try_from(status).ok())
                    .unwrap_or(EXIT_UNASKED),
                _ => EXIT_UNASKED,
            },
        );
    }
    if row["failure"].is_object() && row["required"] == true && row["failure"]["decided"] != true {
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
            Err(detail) => return named(manifest, lock_refused(manifest, path, &detail)),
        },
    };
    let mut document = named(
        manifest,
        compared(manifest, options, vocabulary, &mut Vec::new()),
    );
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

/// [`command`] without its lock, with the value each snapshot view judged
/// ([`SnapshotObserved`]), in the order compare judged them: the run `accept` writes the values
/// of ([`crate::accept`]). The run is compare's own (requests, the answer cache, the result
/// cache), so the values are those a `compare` of the same flow, cache and build judges.
pub(crate) fn observed_snapshots(
    manifest: &FlowManifest,
    options: &CompareOptions,
    vocabulary: Option<&dyn Vocabulary>,
) -> (Value, Vec<SnapshotObserved>) {
    let mut observed = Vec::new();
    let document = named(
        manifest,
        compared(manifest, options, vocabulary, &mut observed),
    );
    (document, observed)
}

/// `document` naming the projections the flow declares (`projections`,
/// [`FlowManifest::projections_value`]), a refused document's too; absent without
/// `[[projection]]`. A view that names a projection names it in `implementations` (`projection`),
/// so a reader finds there the observation each such view measured under.
fn named(manifest: &FlowManifest, mut document: Value) -> Value {
    if let Some(projections) = manifest.projections_value() {
        document["projections"] = projections;
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
    observed: &mut Vec<SnapshotObserved>,
) -> Value {
    let mut document = compared_selected(manifest, options, vocabulary, observed);
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

/// The views of `implementation` whose domain holds `program` (`domains`: per view, the
/// projection it names where that projection has a `domain`; [`ProjectionSection::holds`]):
/// `None` where every view's holds it, so the implementation is asked and judged as declared;
/// otherwise the declaration with only those views, its trace views' channels and shapes (from
/// `shapes`, `None` where none of its trace views holds the program), and per declared view its
/// `outside-domain` row where its domain does not hold the program.
type Applying = (
    Option<ImplementationSection>,
    Option<Option<(Vec<String>, Vec<Value>)>>,
    Option<Vec<Option<Value>>>,
);

fn applying_views(
    implementation: &ImplementationSection,
    domains: &[Option<ProjectionSection>],
    shapes: &Option<(Vec<String>, Vec<Value>)>,
    program: &Program,
    manifest: &FlowManifest,
) -> Applying {
    let outside = implementation
        .views
        .iter()
        .zip(domains)
        .map(|(view, projection)| {
            projection
                .as_ref()
                .filter(|projection| !projection.holds(program))
                .map(|projection| {
                    let mut row = view_row(view);
                    not_compared_row(
                        &mut row,
                        &NotCompared::OutsideDomain {
                            projection: projection.name.clone(),
                            domain: projection.domain.clone().unwrap_or_default(),
                        },
                    );
                    row
                })
        })
        .collect::<Vec<_>>();
    if outside.iter().all(Option::is_none) {
        return (None, None, None);
    }
    let applying = ImplementationSection {
        views: implementation
            .views
            .iter()
            .zip(&outside)
            .filter(|(_, outside)| outside.is_none())
            .map(|(view, _)| view.clone())
            .collect(),
        ..implementation.clone()
    };
    let kept = traced_channels(&applying, manifest.observe.as_ref());
    let shapes = shapes
        .as_ref()
        .filter(|_| !kept.is_empty())
        .map(|(channels, shapes)| {
            channels
                .iter()
                .zip(shapes)
                .filter(|(channel, _)| kept.contains(channel))
                .map(|(channel, shape)| (channel.clone(), shape.clone()))
                .unzip()
        });
    (Some(applying), Some(shapes), Some(outside))
}

/// `row`, an (implementation, program) row judged under the views that apply to the program,
/// with every declared view of `implementation` in the declaration's order: its
/// `outside-domain` row where `outside` has one, else its judged row where it has one.
fn with_outside_rows(
    row: &mut Value,
    implementation: &ImplementationSection,
    outside: &[Option<Value>],
) {
    let judged = row["views"].take();
    let judged = judged.as_array().map_or(&[][..], Vec::as_slice);
    let views = implementation
        .views
        .iter()
        .zip(outside)
        .filter_map(|(view, outside)| {
            outside.clone().or_else(|| {
                judged
                    .iter()
                    .find(|judged| judged["view"] == view.name.as_str())
                    .cloned()
            })
        })
        .collect::<Vec<_>>();
    row["views"] = json!(views);
}

/// What stops the trace views of an answer from being compared.
enum Trouble {
    /// The answer's `observations` is malformed: the run failed.
    Malformed(String),
    /// The command fails: the refusal's reason and detail.
    Command(&'static str, String),
}

/// [`compared`]'s document before its protocols are named; each value a snapshot view judged is
/// pushed on `observed_values`.
fn compared_selected(
    manifest: &FlowManifest,
    options: &CompareOptions,
    vocabulary: Option<&dyn Vocabulary>,
    observed_values: &mut Vec<SnapshotObserved>,
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
    // Per selected implementation, per view: the projection it names where that projection has
    // a `domain`, which decides the programs the view applies to.
    let mut domains = Vec::new();
    for implementation in &selected {
        domains.push(
            implementation
                .views
                .iter()
                .map(|view| {
                    view.projection
                        .as_deref()
                        .and_then(|name| manifest.projection(name))
                        .filter(|projection| projection.domain.is_some())
                })
                .collect::<Vec<_>>(),
        );
        // What of the declaration depends on the flow, before what depends on the definition.
        if let Err(detail) = implementation.declaration(manifest.observe.as_ref()) {
            return refused(
                manifest,
                "declaration",
                format!("implementation `{}`: {detail}", implementation.name),
            );
        }
        // A metric is stated in `metrics`, which only a protocol with metrics has.
        if let Some((index, view)) = implementation
            .views
            .iter()
            .enumerate()
            .find(|(_, view)| metric_of(manifest, view).is_some())
            && !implementation.protocol().is_some_and(Protocol::has_metrics)
        {
            return refused(
                manifest,
                "declaration",
                format!(
                    "implementation `{}`: views[{index}]: the view `{}` measures a metric, which \
                     an answer of `{}` cannot state: declare `protocol = \"{}\"`",
                    implementation.name,
                    view.name,
                    implementation.protocol,
                    Protocol::V3.as_str()
                ),
            );
        }
        let front = without_metric_views(manifest, implementation);
        if let Err(detail) = vocabulary.check(front.as_ref().unwrap_or(implementation)) {
            return refused(
                manifest,
                "declaration",
                format!("implementation `{}`: {detail}", implementation.name),
            );
        }
        // A snapshot view of an `accepts` projection judges the implementation's diagnostic, not
        // the definition's acceptance.
        if let Some(view) = implementation
            .views
            .iter()
            .find(|view| view.accepts && snapshot_kind(manifest, view).is_none())
            && !vocabulary.declares_finished_end()
        {
            return refused(
                manifest,
                "no-finished-end",
                format!(
                    "implementation `{}`: the acceptance view `{}` compares whether the \
                     definition accepts each program, which it does only at a declared \
                     `finished` end, and the definition declares none: without one an end it \
                     completes is not told from one it has no rule for",
                    implementation.name, view.name
                ),
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
        // Whether the definition accepts the program, which its acceptance views (and, where it
        // refuses the program at every end, its end views) compare.
        let acceptance = definition_acceptance(&definition, &row.row);
        // A program rejected before it runs states no end either: its end views ask whether the
        // answer rejects it too.
        let rejected_before_run = definition.rejected_before_run();
        let refused_everywhere = rejected_before_run.is_some()
            || matches!(definition, Definition::Ends { refused: true, .. });
        // The request's parts every implementation shares: its inputs and the start, each
        // read once.
        let mut shared: Option<RequestParts> = None;
        // The definition's observation record and the values of its channels, each read once,
        // and only where an implementation with a trace view needs it.
        let mut observed: Option<Observed> = None;
        let mut values: Option<Result<Vec<ChannelValues>, ValuesRefusal>> = None;
        // The rows of this program's (implementation, program) pairs start here, one per
        // selected implementation; per pair, the rows of its views outside their domain.
        let first = rows.len();
        let mut outside = Vec::new();
        for (((implementation, declaration), shapes), domains) in
            selected.iter().zip(&declared).zip(&traced).zip(&domains)
        {
            let declared_implementation: &ImplementationSection = implementation;
            // The implementation is asked, and judged, under the views whose domain holds the
            // program: the declaration itself where every view's does.
            let (applying, applying_shapes, outside_rows) =
                applying_views(implementation, domains, shapes, program, manifest);
            let implementation = applying.as_ref().unwrap_or(*implementation);
            // What the front end sees of it: its views but the metric views, which compare no
            // cell.
            let front = without_metric_views(manifest, implementation);
            let front = front.as_ref().unwrap_or(implementation);
            let shapes = applying_shapes.as_ref().unwrap_or(shapes);
            outside.push(outside_rows);
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
            // No view applies to the program: nothing is asked.
            if implementation.views.is_empty() {
                rows.push(out);
                continue;
            }
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
                    out["views"] = if implementation.protocol().is_some_and(Protocol::has_traces) {
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
                Definition::Prefix { .. } | Definition::Rejected { .. } => None,
                Definition::Ends { ends, words, .. } => Some((ends, words)),
            };
            // The channels to ask for with their positions, or why the trace views are not
            // compared on this program; `None` for an implementation without a trace view.
            let trace = shapes.as_ref().map(|(channels, _)| {
                if let Some(stage) = rejected_before_run {
                    return Err(NotCompared::RejectedBeforeRun(format!(
                        "the definition rejects the program before it runs (at `{}`): it has no \
                         run, so no channel of it has an element to compare",
                        stage.as_str()
                    )));
                }
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
            let end_views = front.has_end_view();
            // Some view asks for an answer whatever its trace: an end view or an acceptance
            // view.
            let answered_views = implementation.views.iter().any(|view| !view.is_trace());
            // A program rejected before it runs has no end, and its end views are judged by
            // acceptance.
            if let Some(reason) = unasked
                && ((ends.is_none() && rejected_before_run.is_none()) || !answered_views)
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
                    rejected_before_run,
                    selected.iter().any(|i| i.given == Given::Start),
                )
            });
            let observe = asked
                .zip(shapes.as_ref())
                .map(|(asked, (_, shapes))| observe_value(shapes, asked));
            let request = match parts {
                Err(reason) => Err(reason.clone()),
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
            // build on the same request (module documentation); never for an implementation
            // measured under a host-dependent metric, whose value is each run's alone.
            let key = declaration["identity"]["sha256"]
                .as_str()
                .filter(|_| !measures_host(manifest, declared_implementation))
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
                    Some(Protocol::V3) => read_answer_3(&stdout, asks),
                    _ => read_answer(&stdout).map(Stated::from),
                }
                .map_err(|detail| Failure::new("malformed", detail))?;
                if fresh && let Some(key) = &key {
                    // A cache that cannot be written costs the next run a start, nothing else.
                    key.write(&answers, &stdout);
                }
                if let Some(cells) = &stated.cells {
                    vocabulary.read_answer(front, cells).map_err(|detail| {
                        Failure::new("malformed", format!("`cells`: {detail}"))
                    })?;
                }
                if let (Some(asked), Some(observations)) = (asked, &stated.observations) {
                    stated_channels(observations, asked).map_err(|detail| {
                        Failure::new("malformed", format!("`observations`: {detail}"))
                    })?;
                }
                // A rejection's `refused` names a refusal of the definition, read in its
                // vocabulary: its canonical document, which a lock row holds.
                let refused = match &stated.end {
                    StatedEnd::Rejected {
                        refused: Some(refused),
                        ..
                    } => Some(vocabulary.read_refusal(refused).map_err(|detail| {
                        Failure::new("malformed", format!("`refused`: {detail}"))
                    })?),
                    _ => None,
                };
                Ok((stated, refused))
            });
            match answer {
                Err(failure) => {
                    if failure.kind == "timeout" {
                        out["clock_stopped"] = json!("implementation");
                    }
                    out["failure"] = failure.value();
                    // A crash (a failure of kind `exit`: a failure status or a signal) on a
                    // program whose acceptance the definition states disagrees on it (README
                    // D1): the acceptance views judge it, the row keeps its failure.
                    if failure.kind == "exit" {
                        // A snapshot view of an `accepts` projection judges the crash as a
                        // value of its own ([`snapshot::crashed`]).
                        let snapshots = snapshot_rows(
                            manifest,
                            implementation,
                            program,
                            &Observation::Crash(&failure),
                            observed_values,
                        );
                        let crashed = implementation
                            .views
                            .iter()
                            .zip(snapshots)
                            .filter_map(|(view, snapshot)| {
                                snapshot.or_else(|| {
                                    if view.accepts && snapshot_kind(manifest, view).is_none() {
                                        crashed_row(view, &acceptance)
                                    } else {
                                        None
                                    }
                                })
                            })
                            .collect::<Vec<_>>();
                        if !crashed.is_empty() {
                            let decided = implementation.views.iter().all(|view| {
                                !view.required
                                    || crashed.iter().any(|row| row["view"] == view.name.as_str())
                            });
                            out["failure"]["decided"] = json!(decided);
                            out["views"] = json!(crashed);
                        }
                    }
                }
                Ok((stated, refused)) => {
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
                            // The refusal's comparison, where the answer names one and the
                            // definition rejects the program.
                            let refusal = match (&stated.end, refused, ends) {
                                (
                                    StatedEnd::Rejected {
                                        refused: Some(written),
                                        ..
                                    },
                                    Some(canonical),
                                    Some((ends, _)),
                                ) if acceptance == Acceptance::Rejected => vocabulary
                                    .judge_refusal(&RefusalQuestion {
                                        refused: written,
                                        ends,
                                        not_compared: &not_compared,
                                    })
                                    .map(|judged| Some((canonical, judged))),
                                // A program the definition rejects before it runs has no end,
                                // so its rejection states no part of a declared class: an
                                // answer's `refused` is compared with nothing (README D2).
                                _ => Ok(None),
                            };
                            // Snapshot views judge the answer alone; the other views are judged
                            // against the definition's side.
                            let snapshots = snapshot_rows(
                                manifest,
                                implementation,
                                program,
                                &Observation::Answer(&stated),
                                observed_values,
                            );
                            let judged = without_snapshot_views(implementation, &snapshots);
                            let rows = refusal.and_then(|refusal| {
                                answered_rows(
                                    vocabulary,
                                    judged.as_ref().unwrap_or(implementation),
                                    &stated,
                                    ends,
                                    &not_compared,
                                    side,
                                    Some(&AcceptanceSide {
                                        definition: &acceptance,
                                        refused_everywhere,
                                        refusal: refusal.as_ref(),
                                    }),
                                )
                                .map(|views| with_snapshot_rows(snapshots, views))
                            });
                            match rows {
                                Ok(views) => {
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
        debug_assert_eq!(rows.len(), first + selected.len());
        for ((row, implementation), outside) in rows[first..].iter_mut().zip(&selected).zip(outside)
        {
            if let Some(outside) = outside {
                with_outside_rows(row, implementation, &outside);
            }
        }
    }
    document["implementations"] = json!(declared);
    document["programs"] = json!(programs);
    if let Some(stop) = manifest.stop_value() {
        document["stop"] = stop;
    }
    document["result"] = json!({"not_compared": not_compared});
    let declarations = json!({
        "implementations": declared,
        "projections": manifest.projections_value(),
    });
    let snapshots = snapshot_views(&declarations);
    let metrics = metric_views(&declarations);
    document["summary"] = summary(&rows, second_protocol, &snapshots, &metrics);
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
/// none ([`request_parts`]); `Err` when its inputs have no document: why no view is compared.
type RequestParts = Result<(Value, Option<Result<Value, NotCompared>>), NotCompared>;

/// The request's typed inputs and, where some selected implementation is given it, the start
/// (or why it has none), for `program`; `Err` when its inputs have no document. `rejected` is
/// the stage at which the definition rejects the program before it runs, if it does: it then
/// has no start, and, rejected at `input`, its inputs no document where the front end writes
/// none, which no view needs to fail on.
fn request_parts(
    vocabulary: &dyn Vocabulary,
    inputs: &mut crate::admit::InputSession<'_>,
    cases: &crate::manifest::CaseRoot,
    program: &Program,
    row: &ProgramRow,
    rejected: Option<RejectedStage>,
    start: bool,
) -> RequestParts {
    let mut files = cases.case_files(program);
    let typed = vocabulary
        .inputs(program, &mut files)
        .map_err(|detail| no_inputs(rejected, &detail))?;
    if !start {
        return Ok((typed, None));
    }
    if let Some(stage) = rejected {
        return Ok((typed, Some(Err(no_start(stage)))));
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

/// Why no view of a program whose inputs the front end writes no document of (`detail`) is
/// compared: the definition rejects a program rejected at `input` (`rejected`) for the value the
/// request would carry, which no view needs to fail on (`rejected-before-run`); any other
/// program's inputs decoded at admission, so their having no document is the front end's fault
/// (`unreadable`).
fn no_inputs(rejected: Option<RejectedStage>, detail: &str) -> NotCompared {
    match rejected {
        Some(RejectedStage::Input) => NotCompared::RejectedBeforeRun(format!(
            "the definition rejects the program's input before it runs (at `input`), so the \
             request has no document of it: {detail}"
        )),
        _ => NotCompared::Unreadable(format!("the program's inputs have no document: {detail}")),
    }
}

/// Why an implementation given `start` is not asked about a program the definition rejects
/// before it runs (at `stage`): it has no start.
fn no_start(stage: RejectedStage) -> NotCompared {
    NotCompared::RejectedBeforeRun(format!(
        "the definition rejects the program before it runs (at `{}`): it has no start to give an \
         implementation given `start`",
        stage.as_str()
    ))
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
/// (never a `could-not-apply` verdict's, the implementation's words, nor a rejection's
/// `message`); `difference` is a `different` verdict's first difference as canonical JSON, a
/// text that is a function of the difference, but for a snapshot view's, which holds the
/// snapshot's content and the observed value and is never recorded (null); `identity_sha256` is null for an implementation
/// that declares no `identity`. An `agree-up-to` verdict's row also has `horizon`, its horizon as
/// canonical JSON, and an entry whose rejections were compared and agree has `refused`, the
/// answer's refusal as canonical JSON; no other row has either key. A metric view's row holds its
/// verdict alone (never its value, baseline or change), and a host-dependent metric's view has
/// no row. A row of a run that gave no
/// answer has no verdict, so it has none here, but for the acceptance views of a crash.
#[must_use]
pub fn verdict_rows(document: &Value) -> Vec<Value> {
    let rows = document["rows"].as_array().map_or(&[][..], Vec::as_slice);
    let metrics = metric_views(document);
    let mut verdicts = Vec::new();
    for implementation in document["implementations"].as_array().into_iter().flatten() {
        let name = implementation["name"].as_str().unwrap_or_default();
        let identity = &implementation["identity"]["sha256"];
        for row in rows.iter().filter(|row| row["implementation"] == name) {
            let program = row["program"].as_str().unwrap_or_default();
            for view in row["views"].as_array().into_iter().flatten() {
                // A host-dependent metric is the host's: reported, never recorded.
                if metrics.iter().any(|metric| {
                    metric.host_dependent
                        && metric.implementation == name
                        && view["view"] == metric.view.as_str()
                }) {
                    continue;
                }
                let verdict = view["verdict"].as_str().unwrap_or_default();
                // A `could-not-apply` reason is the implementation's own words, which may change
                // with no change of verdict, so it is reported and never recorded.
                let reason = match verdict {
                    "not-compared" => view["reason"].clone(),
                    _ => Value::Null,
                };
                // A snapshot's difference holds the accepted and the observed values, which are
                // inputs and answers, never in the record: its verdict alone is.
                let difference = if view["difference"].is_null()
                    || view["difference"]["format"] == SNAPSHOT_DIFFERENCE_FORMAT
                {
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
                if let Some(refused) = view.get("refused").filter(|refused| !refused.is_null()) {
                    verdict["refused"] = json!(canonical_json(refused));
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
/// that failed none. A view outside its projection's domain rests on no run, so its live row is
/// written in a pair that is kept too. Under `--locked` a section that differs in nothing else is
/// `undecided`.
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
    // The views of each implementation, in the declaration's order.
    let declared = |implementation: &str| {
        document["implementations"]
            .as_array()
            .into_iter()
            .flatten()
            .find(|declared| declared["name"] == implementation)
            .and_then(|declared| declared["views"].as_array())
            .map(|views| {
                views
                    .iter()
                    .filter_map(|view| view["name"].as_str())
                    .map(str::to_owned)
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default()
    };
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
            // A crash its acceptance views judged decides them (README D1); the pair is undecided
            // only where some other view has no verdict.
            None if row["failure"].is_object()
                && row["views"].as_array().is_some_and(|views| {
                    !views.is_empty() && views.len() >= declared(&pair.0).len()
                }) =>
            {
                continue;
            }
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
        if let Some(refused) = row.get("refused").filter(|refused| !refused.is_null()) {
            compared["refused"] = refused.clone();
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
                // A crash's acceptance rows are decided (README D1): they are the live ones,
                // every other view keeps its recorded row, in the declaration's order.
                let failed = document["rows"]
                    .as_array()
                    .into_iter()
                    .flatten()
                    .any(|row| {
                        row["implementation"] == pair.0.as_str()
                            && row["program"] == pair.1.as_str()
                            && row["failure"].is_object()
                            && row["clock_stopped"].is_null()
                    });
                let keep_row = |row: &Value, kept: &mut Vec<Value>| {
                    let now = own.clone().find(|live| live["id"] == row["id"]);
                    if let Some(now) = now.filter(|now| compared(now) != compared(row)) {
                        let mut entry =
                            LockKind::Compare.keyed(row["id"].as_str().unwrap_or_default());
                        entry.insert("recorded".into(), compared(row));
                        entry.insert("now".into(), compared(now));
                        kept.push(Value::Object(entry));
                    }
                    row.clone()
                };
                // A view outside its projection's domain rests on no run: its live row is
                // decided whatever run gave no answer.
                let outside = own
                    .clone()
                    .any(|live| live["reason"] == OUTSIDE_DOMAIN_REASON);
                if (failed && own.clone().next().is_some()) || outside {
                    for view in declared(&pair.0) {
                        let id = json!(compare_row_id(&pair.0, &pair.1, &view));
                        let live = own
                            .clone()
                            .find(|live| live["id"] == id)
                            .filter(|live| failed || live["reason"] == OUTSIDE_DOMAIN_REASON);
                        if let Some(live) = live {
                            verdicts.push(live.clone());
                        } else if let Some(row) = rows.iter().find(|row| row["id"] == id) {
                            verdicts.push(keep_row(row, &mut kept));
                        }
                    }
                } else {
                    for row in rows {
                        verdicts.push(keep_row(row, &mut kept));
                    }
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
/// only a trace view has that verdict, `pending` only in one with a snapshot or a metric view
/// (`snapshots`, `metrics`), since only those have that verdict, and `improved`, `regressed`,
/// `stayed` and `measured` only in one with a metric view.
fn counted(
    second_protocol: bool,
    snapshots: bool,
    metrics: bool,
) -> impl Iterator<Item = &'static str> {
    [
        "equal",
        "agree-up-to",
        "different",
        "improved",
        "regressed",
        "stayed",
        "measured",
        "could-not-apply",
        "pending",
        "not-compared",
    ]
    .into_iter()
    .filter(move |verdict| match *verdict {
        "agree-up-to" => second_protocol,
        "pending" => snapshots || metrics,
        "improved" | "regressed" | "stayed" | "measured" => metrics,
        _ => true,
    })
}

/// The snapshot views of a compare document's selected implementations
/// (`implementations[].views[]` naming, by `projection`, an entry of `projections` whose
/// `relation` is `snapshot` and whose kind is not `metric`: those are [`metric_views`]), each
/// `(implementation, view)`, in the declarations' order. A view naming a projection has the
/// projection's name, so `view` names the projection too.
#[must_use]
pub fn snapshot_views(document: &Value) -> Vec<(String, String)> {
    let snapshot = |name: &str| {
        document["projections"]
            .as_array()
            .into_iter()
            .flatten()
            .any(|projection| {
                projection["name"] == name
                    && projection["relation"] == "snapshot"
                    && projection["kind"] != "metric"
            })
    };
    let mut views = Vec::new();
    for implementation in document["implementations"].as_array().into_iter().flatten() {
        for view in implementation["views"].as_array().into_iter().flatten() {
            if view["projection"].as_str().is_some_and(snapshot)
                && let (Some(implementation), Some(view)) =
                    (implementation["name"].as_str(), view["name"].as_str())
            {
                views.push((implementation.to_owned(), view.to_owned()));
            }
        }
    }
    views
}

/// Per snapshot view of `views` ([`snapshot_views`]), in their order, the programs whose verdict
/// is `equal`, `different` and `pending` among `entries` (`(implementation, view, verdict)`):
/// `{projection, implementation, equal, different, pending}`. Every other verdict (a failed run,
/// `could-not-apply`, `not-compared`) is in none of the three.
#[must_use]
pub fn snapshot_counts<'a>(
    views: &[(String, String)],
    entries: impl IntoIterator<Item = (&'a str, &'a str, &'a str)>,
) -> Vec<Value> {
    let mut counts = vec![[0_u64; 3]; views.len()];
    for (implementation, view, verdict) in entries {
        let Some(index) = views
            .iter()
            .position(|(i, v)| i == implementation && v == view)
        else {
            continue;
        };
        if let Some(at) = ["equal", "different", "pending"]
            .iter()
            .position(|counted| *counted == verdict)
        {
            counts[index][at] += 1;
        }
    }
    views
        .iter()
        .zip(counts)
        .map(|((implementation, view), [equal, different, pending])| {
            json!({
                "projection": view,
                "implementation": implementation,
                "equal": equal,
                "different": different,
                "pending": pending,
            })
        })
        .collect()
}

/// One metric view of a compare document ([`metric_views`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MetricView {
    pub implementation: String,
    /// The view's name, the metric projection's.
    pub view: String,
    /// The metric it measures (`metric`).
    pub metric: String,
    /// `direction`, as written.
    pub direction: String,
    pub host_dependent: bool,
}

/// The metric views of a compare document's selected implementations
/// (`implementations[].views[]` naming, by `projection`, an entry of `projections` of kind
/// `metric`), in the declarations' order.
#[must_use]
pub fn metric_views(document: &Value) -> Vec<MetricView> {
    let mut views = Vec::new();
    for implementation in document["implementations"].as_array().into_iter().flatten() {
        for view in implementation["views"].as_array().into_iter().flatten() {
            let Some(projection) = document["projections"]
                .as_array()
                .into_iter()
                .flatten()
                .find(|projection| {
                    projection["kind"] == "metric"
                        && view["projection"].as_str().is_some()
                        && projection["name"] == view["projection"]
                })
            else {
                continue;
            };
            let text = |value: &Value| value.as_str().unwrap_or_default().to_owned();
            views.push(MetricView {
                implementation: text(&implementation["name"]),
                view: text(&view["name"]),
                metric: text(&projection["metric"]),
                direction: text(&projection["direction"]),
                host_dependent: projection["host_dependent"] == true,
            });
        }
    }
    views
}

/// Whether `(implementation, view)` is one of `metrics`.
fn is_metric(metrics: &[MetricView], implementation: &str, view: &str) -> bool {
    metrics
        .iter()
        .any(|metric| metric.implementation == implementation && metric.view == view)
}

/// Per metric view of `views` ([`metric_views`]), in their order, over `entries` (`(implementation,
/// view, verdict, value)`, `value` the measured count where the entry states it): `{projection,
/// implementation, metric, measured, total, improved, regressed, stayed, pending}`, `measured`
/// the entries whose verdict rests on a measured value (`improved`, `regressed`, `stayed`,
/// `pending`, `measured`; a lock row states no value, only its verdict) and `total` the sum of
/// the values stated (null where it exceeds 2^64 - 1, and 0 over lock rows, which state none).
#[must_use]
pub fn metric_counts<'a>(
    views: &[MetricView],
    entries: impl IntoIterator<Item = (&'a str, &'a str, &'a str, Option<u64>)>,
) -> Vec<Value> {
    // measured, improved, regressed, stayed, pending; and the total.
    let mut counts = vec![([0_u64; 5], 0_u128); views.len()];
    for (implementation, view, verdict, value) in entries {
        let Some(index) = views
            .iter()
            .position(|metric| metric.implementation == implementation && metric.view == view)
        else {
            continue;
        };
        let (counted, total) = &mut counts[index];
        if value.is_some()
            || matches!(
                verdict,
                "improved" | "regressed" | "stayed" | "pending" | "measured"
            )
        {
            counted[0] += 1;
        }
        if let Some(value) = value {
            *total += u128::from(value);
        }
        if let Some(at) = ["improved", "regressed", "stayed", "pending"]
            .iter()
            .position(|word| *word == verdict)
        {
            counted[at + 1] += 1;
        }
    }
    views
        .iter()
        .zip(counts)
        .map(
            |(metric, ([measured, improved, regressed, stayed, pending], total))| {
                json!({
                    "projection": metric.view,
                    "implementation": metric.implementation,
                    "metric": metric.metric,
                    "measured": measured,
                    "total": serde_json::Number::from_u128(total),
                    "improved": improved,
                    "regressed": regressed,
                    "stayed": stayed,
                    "pending": pending,
                })
            },
        )
        .collect()
}

/// The counts of the document's verdicts and failures: `{verdicts: {equal, different,
/// could-not-apply, not-compared}, required: {..the same, of required views}, failures}`, each
/// with `agree-up-to` under `second_protocol` and `pending` where some snapshot view is among
/// `snapshots` ([`counted`]), `views`, each (implementation, view)'s agreement ([`view_counts`]),
/// and, where some snapshot view is, `snapshots`, each one's counts ([`snapshot_counts`]); where
/// some metric view is, the metric verdicts ([`counted`]) and `metrics`, each one's counts
/// ([`metric_counts`]) with its `direction`, `host_dependent` and `exceeded` (its regressions
/// beyond `max_regression`). A metric view is in no `views` count: it agrees with no definition.
/// A view outside its projection's domain is counted in none: the projection does not apply to
/// the program.
fn summary(
    rows: &[Value],
    second_protocol: bool,
    snapshots: &[(String, String)],
    metrics: &[MetricView],
) -> Value {
    let mut verdicts = Map::new();
    let mut required = Map::new();
    for verdict in counted(second_protocol, !snapshots.is_empty(), !metrics.is_empty()) {
        let count = |only_required: bool| {
            rows.iter()
                .flat_map(|row| row["views"].as_array().into_iter().flatten())
                .filter(|view| {
                    view["verdict"] == verdict && view["reason"] != OUTSIDE_DOMAIN_REASON
                })
                .filter(|view| !only_required || view["required"] == true)
                .count()
        };
        verdicts.insert(verdict.into(), json!(count(false)));
        required.insert(verdict.into(), json!(count(true)));
    }
    let entries = rows
        .iter()
        .flat_map(|row| {
            row["views"]
                .as_array()
                .into_iter()
                .flatten()
                .map(move |view| ViewEntry {
                    implementation: row["implementation"].as_str().unwrap_or_default(),
                    view: view["view"].as_str().unwrap_or_default(),
                    required: view["required"] == true,
                    verdict: view["verdict"].as_str().unwrap_or_default(),
                    horizon: view["horizon"].clone(),
                })
        })
        .filter(|entry| !is_metric(metrics, entry.implementation, entry.view));
    let mut summary = json!({
        "verdicts": verdicts,
        "required": required,
        "failures": rows.iter().filter(|row| row["failure"].is_object()).count(),
        "views": view_counts(entries),
    });
    if !snapshots.is_empty() {
        summary["snapshots"] = json!(snapshot_counts(
            snapshots,
            rows.iter().flat_map(|row| {
                let implementation = row["implementation"].as_str().unwrap_or_default();
                row["views"]
                    .as_array()
                    .into_iter()
                    .flatten()
                    .map(move |view| {
                        (
                            implementation,
                            view["view"].as_str().unwrap_or_default(),
                            view["verdict"].as_str().unwrap_or_default(),
                        )
                    })
            })
        ));
    }
    if !metrics.is_empty() {
        let entries = || {
            rows.iter().flat_map(|row| {
                let implementation = row["implementation"].as_str().unwrap_or_default();
                row["views"]
                    .as_array()
                    .into_iter()
                    .flatten()
                    .map(move |view| (implementation, view))
            })
        };
        let mut counts = metric_counts(
            metrics,
            entries().map(|(implementation, view)| {
                (
                    implementation,
                    view["view"].as_str().unwrap_or_default(),
                    view["verdict"].as_str().unwrap_or_default(),
                    view["metric"]["value"].as_u64(),
                )
            }),
        );
        for (count, metric) in counts.iter_mut().zip(metrics) {
            count["direction"] = json!(metric.direction);
            count["host_dependent"] = json!(metric.host_dependent);
            count["exceeded"] = json!(
                entries()
                    .filter(|(implementation, view)| {
                        *implementation == metric.implementation
                            && view["view"] == metric.view.as_str()
                            && view["metric"]["exceeded"] == true
                    })
                    .count()
            );
        }
        summary["metrics"] = json!(counts);
    }
    summary
}

/// One verdict of one (implementation, view), as [`view_counts`] counts it: `horizon` is an
/// `agree-up-to` verdict's horizon object (or its canonical JSON text, as a lock row holds it).
pub struct ViewEntry<'a> {
    pub implementation: &'a str,
    pub view: &'a str,
    pub required: bool,
    pub verdict: &'a str,
    pub horizon: Value,
}

/// Whether a verdict is an agreement of the two sides over everything the definition states:
/// `equal`, or `agree-up-to` whose every horizon is the definition's (`limited_by:
/// "definition"`), whose status is 0 ([`judged_row`]).
fn agrees(verdict: &str, horizon: &Value) -> bool {
    match verdict {
        "equal" => true,
        "agree-up-to" => {
            let parsed;
            let horizon = match horizon {
                Value::String(text) => {
                    parsed = serde_json::from_str::<Value>(text).unwrap_or(Value::Null);
                    &parsed
                }
                other => other,
            };
            horizon.as_object().is_some_and(|channels| {
                !channels.is_empty()
                    && channels
                        .values()
                        .all(|channel| channel["limited_by"] == "definition")
            })
        }
        _ => false,
    }
}

/// The agreement of each (implementation, view) over the corpus's programs, in the order the
/// pairs first occur: `{implementation, view, required, compared, agreeing}`, `compared` the
/// programs whose verdict is not `not-compared` or `pending` and `agreeing` those of them that
/// agree ([`agrees`]). A run that gave no answer has no verdict and counts in neither, and
/// neither does a snapshot view with no accepted value (`pending`).
#[must_use]
pub fn view_counts<'a>(entries: impl IntoIterator<Item = ViewEntry<'a>>) -> Vec<Value> {
    let mut counts: Vec<(&str, &str, bool, u64, u64)> = Vec::new();
    for entry in entries {
        let index = match counts
            .iter()
            .position(|(i, v, ..)| *i == entry.implementation && *v == entry.view)
        {
            Some(index) => index,
            None => {
                counts.push((entry.implementation, entry.view, entry.required, 0, 0));
                counts.len() - 1
            }
        };
        if !matches!(entry.verdict, "not-compared" | "pending") {
            counts[index].3 += 1;
            if agrees(entry.verdict, &entry.horizon) {
                counts[index].4 += 1;
            }
        }
    }
    counts
        .into_iter()
        .map(|(implementation, view, required, compared, agreeing)| {
            json!({
                "implementation": implementation,
                "view": view,
                "required": required,
                "compared": compared,
                "agreeing": agreeing,
            })
        })
        .collect()
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
        // A failed run has no verdict but those its acceptance views judge (a crash).
        if let Some(failure) = row["failure"].as_object() {
            text.push_str(&format!(
                "{name}: failed ({}): {}\n",
                failure["kind"].as_str().unwrap_or("?"),
                failure["detail"].as_str().unwrap_or("")
            ));
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
                "different" if view["difference"]["format"] == ACCEPTS_DIFFERENCE_FORMAT => {
                    format!(
                        ": the definition {}, the implementation {}",
                        view["difference"]["definition"].as_str().unwrap_or("?"),
                        view["difference"]["implementation"].as_str().unwrap_or("?")
                    )
                }
                "different" if view["difference"]["format"] == SNAPSHOT_DIFFERENCE_FORMAT => {
                    let lines = view["difference"]["lines"]
                        .as_array()
                        .into_iter()
                        .flatten()
                        .map(|line| format!("\n    {}", line.as_str().unwrap_or_default()))
                        .collect::<String>();
                    format!(
                        " from the snapshot {}{lines}",
                        view["snapshot"].as_str().unwrap_or("?")
                    )
                }
                "different" => view["difference"]["at"]
                    .as_str()
                    .or_else(|| view["difference"]["path"].as_str())
                    .map(|at| format!(" at {at}"))
                    .unwrap_or_default(),
                "improved" | "regressed" | "stayed" | "measured" => metric_text(&view["metric"]),
                "pending" if view["metric"].is_object() => format!(
                    "{}: {}",
                    metric_text(&view["metric"]),
                    view["detail"].as_str().unwrap_or_default()
                ),
                "could-not-apply" | "not-compared" | "agree-up-to" | "pending" => view["detail"]
                    .as_str()
                    .map(|detail| format!(": {detail}"))
                    .unwrap_or_default(),
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
            counted(
                summary[member].get("agree-up-to").is_some(),
                summary[member].get("pending").is_some(),
                summary[member].get("measured").is_some(),
            )
            .map(|verdict| format!("{} {verdict}", summary[member][verdict]))
            .collect::<Vec<_>>()
            .join(", ")
        };
        for view in summary["views"].as_array().into_iter().flatten() {
            text.push_str(&format!(
                "{} {} ({}): {} of {} programs compared agree\n",
                view["implementation"].as_str().unwrap_or("?"),
                view["view"].as_str().unwrap_or("?"),
                if view["required"] == true {
                    "required"
                } else {
                    "reported"
                },
                view["agreeing"],
                view["compared"]
            ));
        }
        for snapshot in summary["snapshots"].as_array().into_iter().flatten() {
            text.push_str(&format!(
                "{} {} (snapshot): {} equal, {} different, {} pending\n",
                snapshot["implementation"].as_str().unwrap_or("?"),
                snapshot["projection"].as_str().unwrap_or("?"),
                snapshot["equal"],
                snapshot["different"],
                snapshot["pending"]
            ));
        }
        for metric in summary["metrics"].as_array().into_iter().flatten() {
            let name = format!(
                "{} {} (metric `{}`",
                metric["implementation"].as_str().unwrap_or("?"),
                metric["projection"].as_str().unwrap_or("?"),
                metric["metric"].as_str().unwrap_or("?"),
            );
            text.push_str(&if metric["host_dependent"] == true {
                format!(
                    "{name}, host-dependent): total {} over {} programs measured\n",
                    metric["total"], metric["measured"]
                )
            } else {
                format!(
                    "{name}, {} is better): total {} over {} programs measured; {} improved, {} \
                     regressed ({} beyond max_regression), {} stayed, {} pending\n",
                    metric["direction"].as_str().unwrap_or("?"),
                    metric["total"],
                    metric["measured"],
                    metric["improved"],
                    metric["regressed"],
                    metric["exceeded"],
                    metric["stayed"],
                    metric["pending"]
                )
            });
        }
        text.push_str(&format!(
            "verdicts: {}; required views: {}; failed runs: {}\n",
            counts("verdicts"),
            counts("required"),
            summary["failures"]
        ));
    }
    Ok(text)
}

/// A metric entry's `metric` member as a line says it: `: VALUE` and, against a baseline,
/// ` (baseline B, change C)`, with `beyond max_regression` where its gate is exceeded.
fn metric_text(metric: &Value) -> String {
    let mut text = format!(": {}", metric["value"]);
    if !metric["baseline"].is_null() {
        let change = metric["change"].as_i64().unwrap_or_default();
        text.push_str(&format!(
            " (baseline {}, change {}{change}{})",
            metric["baseline"],
            if change > 0 { "+" } else { "" },
            if metric["exceeded"] == true {
                ", beyond max_regression"
            } else {
                ""
            }
        ));
    }
    text
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

    #[test]
    fn the_definition_refuses_a_program_only_where_every_end_is_refused() {
        let refused =
            json!({"declared": "refused", "declared_by": "crate::trap", "reason_text": "7"});
        let finished = json!({"declared": "finished", "declared_by": "crate::halt"});
        let normal = json!({"class": "normal"});
        assert!(refused_everywhere(std::slice::from_ref(&refused)));
        assert!(refused_everywhere(&[refused.clone(), refused.clone()]));
        // A refusal on one path does not answer for another the definition also states.
        assert!(!refused_everywhere(&[refused.clone(), finished]));
        // A definition that declares no end has no `declared`.
        assert!(!refused_everywhere(&[normal]));
        assert!(!refused_everywhere(&[]));
    }

    /// The definition's acceptance of a program, from its ends: an end at the stop or of a
    /// declared `finished` class accepts, one of a `refused` class or of none (a gap) rejects;
    /// both kinds is inclusion, and an undecided class decides nothing.
    #[test]
    fn the_definition_accepts_by_its_declared_ends_and_its_stop() {
        let end = |declared: &str| json!({"declared": declared});
        let stop = json!({"halt": "stop"});
        assert_eq!(ends_acceptance(&[end("finished")]), Acceptance::Accepted);
        assert_eq!(
            ends_acceptance(std::slice::from_ref(&stop)),
            Acceptance::Accepted
        );
        assert_eq!(
            ends_acceptance(&[stop, end("finished")]),
            Acceptance::Accepted
        );
        assert_eq!(ends_acceptance(&[end("refused")]), Acceptance::Rejected);
        assert_eq!(
            ends_acceptance(&[end("none"), end("refused")]),
            Acceptance::Rejected
        );
        let reason = |acceptance: Acceptance| match acceptance {
            Acceptance::NotCompared(reason) => reason.reason(),
            other => panic!("{other:?}"),
        };
        assert_eq!(
            reason(ends_acceptance(&[end("finished"), end("refused")])),
            "several-ends"
        );
        assert_eq!(reason(ends_acceptance(&[end("undecided")])), "undecided");
        assert_eq!(reason(ends_acceptance(&[end("overlap")])), "undecided");
        assert_eq!(reason(ends_acceptance(&[json!({})])), "undecided");
    }

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
            // Projections D6: an implementation that does not apply a program disagrees on it.
            (
                row(
                    vec![view(true, "could-not-apply", Value::Null)],
                    Value::Null,
                    true,
                ),
                EXIT_NO,
            ),
            // Projections D1: a crash its acceptance views judge decides them; its failure counts
            // only where some required view has no verdict.
            (
                row(
                    vec![view(true, "different", Value::Null)],
                    json!({"kind": "exit", "decided": true}),
                    true,
                ),
                EXIT_NO,
            ),
            (
                row(
                    vec![view(true, "different", Value::Null)],
                    json!({"kind": "exit", "decided": false}),
                    true,
                ),
                EXIT_UNASKED,
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
                    compared_cells: 2,
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

    /// A third protocol answer may be `rejected`, with its own `message` and the definition's
    /// refusal it names (`refused`), and states no `cells`; `message` and `refused` belong to a
    /// `rejected` answer alone, and the second protocol has no such word.
    #[test]
    fn a_third_protocol_answer_may_reject_the_program() {
        let ended = Asked {
            observe: false,
            end_view: true,
        };
        let stated = read_answer_3(
            br#"{"end": "rejected", "message": "bad", "refused": {"end": "crate::trap", "reason": 1}}"#,
            ended,
        )
        .unwrap();
        assert_eq!(
            stated.end,
            StatedEnd::Rejected {
                message: Some("bad".to_owned()),
                refused: Some(json!({"end": "crate::trap", "reason": 1})),
            }
        );
        assert_eq!(stated.word(), "rejected");
        assert_eq!(
            stated.value(),
            json!({"end": "rejected", "reason": null, "message": "bad",
                   "refused": {"end": "crate::trap", "reason": 1}})
        );
        assert_eq!(
            read_answer_3(br#"{"end": "rejected"}"#, ended).unwrap().end,
            StatedEnd::Rejected {
                message: None,
                refused: None
            }
        );
        for (bytes, expected) in [
            (
                &br#"{"end": "rejected", "cells": {}}"#[..],
                "a `rejected` answer states no `cells`",
            ),
            (
                br#"{"end": "final", "cells": {}, "message": "x"}"#,
                "a `final` answer states no `message`",
            ),
            (
                br#"{"end": "rejected", "refused": {"reason": 1}}"#,
                "`refused` names its `end`",
            ),
            (
                br#"{"end": "rejected", "refused": {"end": "e", "why": 1}}"#,
                "`refused` has the key `why`",
            ),
            (
                br#"{"end": "rejected", "message": 3}"#,
                "`message` is not a string",
            ),
        ] {
            let error = read_answer_3(bytes, ended).unwrap_err();
            assert!(error.starts_with(expected), "{error}");
        }
        let error = read_answer_2(br#"{"end": "rejected"}"#, ended).unwrap_err();
        assert!(error.starts_with("`end` is `rejected`, not"), "{error}");
        let error =
            read_answer_2(br#"{"end": "final", "cells": {}, "message": "x"}"#, ended).unwrap_err();
        assert!(
            error.starts_with("the answer has the key `message`"),
            "{error}"
        );
    }

    /// A third protocol answer may state counts of its run (`metrics`, projections PJ-21), on any
    /// end but `could-not-apply`; its row's answer reports them; no other protocol has them.
    #[test]
    fn a_third_protocol_answer_may_state_metrics() {
        let asked = Asked {
            observe: false,
            end_view: false,
        };
        let stated =
            read_answer_3(br#"{"end": "final", "metrics": {"bytes": 12}}"#, asked).unwrap();
        assert_eq!(
            stated.metrics,
            Some(json!({"bytes": 12}).as_object().unwrap().clone())
        );
        assert_eq!(
            stated.value(),
            json!({"end": "final", "reason": null, "metrics": {"bytes": 12}})
        );
        let rejected =
            read_answer_3(br#"{"end": "rejected", "metrics": {"bytes": 0}}"#, asked).unwrap();
        assert_eq!(rejected.metrics.unwrap()["bytes"], 0);
        // No `metrics`: the row's answer is what it was.
        let plain = read_answer_3(br#"{"end": "final"}"#, asked).unwrap();
        assert_eq!(plain.metrics, None);
        assert_eq!(plain.value(), json!({"end": "final", "reason": null}));
        for (bytes, expected) in [
            (
                &br#"{"end": "could-not-apply", "reason": "no", "metrics": {}}"#[..],
                "a `could-not-apply` answer states no `metrics`",
            ),
            (
                br#"{"end": "final", "metrics": {"bytes": 1.5}}"#,
                "`metrics.bytes` is 1.5, not a metric's value",
            ),
            (
                br#"{"end": "final", "metrics": []}"#,
                "`metrics` is not a JSON object",
            ),
        ] {
            let error = read_answer_3(bytes, asked).unwrap_err();
            assert!(error.starts_with(expected), "{error}");
        }
        let error = read_answer_2(br#"{"end": "final", "metrics": {}}"#, asked).unwrap_err();
        assert!(
            error.starts_with("the answer has the key `metrics`"),
            "{error}"
        );
    }

    /// A view judged by acceptance: equal where both sides accept, or both reject and agree on
    /// the parts of the refusal both state; different otherwise, naming both sides; a crash
    /// differs where the definition states its acceptance, and has no verdict where it does not.
    #[test]
    fn a_view_judged_by_acceptance_compares_accept_and_reject() {
        let implementation = second("{ name = \"accepts\", kind = \"accepts\", required = true }");
        let view = &implementation.views[0];
        let ended = stated(StatedEnd::Ended(EndWord::Final), true, false);
        let rejected = |refused: Option<Value>| Stated {
            end: StatedEnd::Rejected {
                message: Some("why".to_owned()),
                refused,
            },
            cells: None,
            observations: None,
            metrics: None,
        };
        let verdict = |row: &Value| {
            (
                row["verdict"].as_str().unwrap().to_owned(),
                row["difference"].clone(),
            )
        };
        let accepts = |definition: &str, implementation: &str| {
            json!({"format": ACCEPTS_DIFFERENCE_FORMAT, "definition": definition,
                   "implementation": implementation})
        };
        let row = acceptance_row(view, &Acceptance::Accepted, &ended, None);
        assert_eq!(verdict(&row), ("equal".to_owned(), Value::Null));
        assert!(row["distance"].is_null());
        let row = acceptance_row(view, &Acceptance::Accepted, &rejected(None), None);
        assert_eq!(
            verdict(&row),
            ("different".to_owned(), accepts("accepts", "rejects"))
        );
        let row = acceptance_row(view, &Acceptance::Rejected, &ended, None);
        assert_eq!(
            verdict(&row),
            ("different".to_owned(), accepts("rejects", "accepts"))
        );
        let horizon = stated(StatedEnd::Horizon, false, true);
        let row = acceptance_row(view, &Acceptance::Accepted, &horizon, None);
        assert_eq!(
            verdict(&row),
            ("different".to_owned(), accepts("accepts", "horizon"))
        );
        let row = acceptance_row(view, &Acceptance::Rejected, &rejected(None), None);
        assert_eq!(verdict(&row), ("equal".to_owned(), Value::Null));
        // A refusal both state: recorded where it agrees.
        let named = json!({"end": "crate::trap", "reason": 1});
        let agree = (named.clone(), RefusalJudged::Agree);
        let row = acceptance_row(
            view,
            &Acceptance::Rejected,
            &rejected(Some(named.clone())),
            Some(&agree),
        );
        assert_eq!(row["verdict"], "equal");
        assert_eq!(row["refused"], named);
        let differ = (
            named.clone(),
            RefusalJudged::Different(json!({"format": "krs-difference/3", "at": "class"})),
        );
        let row = acceptance_row(
            view,
            &Acceptance::Rejected,
            &rejected(Some(named.clone())),
            Some(&differ),
        );
        assert_eq!(row["verdict"], "different");
        assert_eq!(row["difference"]["at"], "class");
        assert!(row.get("refused").is_none());
        let several = (named.clone(), RefusalJudged::SeveralEnds("some".to_owned()));
        let row = acceptance_row(
            view,
            &Acceptance::Rejected,
            &rejected(Some(named)),
            Some(&several),
        );
        assert_eq!(row["reason"], "several-ends");
        // The definition's acceptance is not known: not compared, for its reason.
        let row = acceptance_row(
            view,
            &Acceptance::NotCompared(NotCompared::Undecided("u".to_owned())),
            &ended,
            None,
        );
        assert_eq!(row["reason"], "undecided");
        // A crash.
        assert_eq!(
            crashed_row(view, &Acceptance::Rejected).map(|row| verdict(&row)),
            Some(("different".to_owned(), accepts("rejects", "crashed")))
        );
        assert!(
            crashed_row(
                view,
                &Acceptance::NotCompared(NotCompared::Undecided("u".to_owned()))
            )
            .is_none()
        );
        // Through answered_rows: an end view of a program the definition refuses at every end is
        // judged so too, and `could-not-apply` keeps its verdict on every view.
        let mixed = second(&format!(
            "{END}, {{ name = \"accepts\", kind = \"accepts\" }}"
        ));
        let mock = Mock::judging(Vec::new());
        let ends = BTreeSet::new();
        let words = BTreeSet::from(["final"]);
        let side = AcceptanceSide {
            definition: &Acceptance::Rejected,
            refused_everywhere: true,
            refusal: None,
        };
        let rows = answered_rows(
            &mock,
            &mixed,
            &rejected(None),
            Some((&ends, &words)),
            &[],
            None,
            Some(&side),
        )
        .unwrap();
        assert!(
            rows.iter().all(|row| row["verdict"] == "equal"),
            "{rows:#?}"
        );
        let rows = answered_rows(
            &mock,
            &mixed,
            &ended,
            Some((&ends, &words)),
            &[],
            None,
            Some(&side),
        )
        .unwrap();
        assert!(
            rows.iter()
                .all(|row| row["difference"] == accepts("rejects", "accepts")),
            "{rows:#?}"
        );
        let rows = answered_rows(
            &mock,
            &mixed,
            &stated(StatedEnd::CouldNotApply("no".to_owned()), false, false),
            Some((&ends, &words)),
            &[],
            None,
            Some(&side),
        )
        .unwrap();
        assert!(rows.iter().all(|row| row["verdict"] == "could-not-apply"));
        // Its reason is reported and never recorded.
        let document = json!({"implementations": [{"name": "fake"}],
                              "rows": [{"implementation": "fake", "program": "p",
                                        "request_sha256": "r", "views": rows}]});
        assert!(
            verdict_rows(&document)
                .iter()
                .all(|row| row["reason"].is_null())
        );
    }

    /// A program the definition rejects before it runs (projections PJ-32) is rejected on the
    /// definition's side: its acceptance views and end views are judged by acceptance, a
    /// `rejected` answer's `refused` is compared with nothing (the definition states no declared
    /// class), and a view left without what it compares (a trace, the start of an
    /// implementation given `start`, inputs rejected at `input` with no document) is
    /// `not-compared` for `rejected-before-run`, status 0. An unmet statement's views are
    /// `definition`, status 2, and say that the program runs nothing.
    #[test]
    fn a_program_rejected_before_it_runs_is_rejected_on_the_definition_side() {
        let definition = Definition::Rejected {
            stage: RejectedStage::Parse,
        };
        assert_eq!(definition.rejected_before_run(), Some(RejectedStage::Parse));
        assert_eq!(
            definition_acceptance(&definition, &json!({})),
            Acceptance::Rejected
        );
        let implementation = second(&format!(
            "{END}, {{ name = \"accepts\", kind = \"accepts\", required = true }}, {TICKS}"
        ));
        let no_trace = NotCompared::RejectedBeforeRun("no run".to_owned());
        let side = AcceptanceSide {
            definition: &Acceptance::Rejected,
            refused_everywhere: true,
            refusal: None,
        };
        let mock = Mock::judging(Vec::new());
        let verdicts = |stated: &Stated, side: &AcceptanceSide<'_>| {
            answered_rows(
                &mock,
                &implementation,
                stated,
                None,
                &[],
                Some(TraceSide::Not(&no_trace)),
                Some(side),
            )
            .unwrap()
            .iter()
            .map(|row| {
                (
                    row["verdict"].as_str().unwrap().to_owned(),
                    row["reason"].clone(),
                    row["status"].clone(),
                )
            })
            .collect::<Vec<_>>()
        };
        let not_compared = || {
            (
                "not-compared".to_owned(),
                json!("rejected-before-run"),
                json!(0),
            )
        };
        let rejected = |refused: Option<Value>| Stated {
            end: StatedEnd::Rejected {
                message: Some("syntax error".to_owned()),
                refused,
            },
            cells: None,
            observations: None,
            metrics: None,
        };
        let equal = || ("equal".to_owned(), Value::Null, Value::Null);
        let different = || ("different".to_owned(), Value::Null, Value::Null);
        assert_eq!(
            verdicts(&rejected(None), &side),
            [equal(), equal(), not_compared()]
        );
        assert_eq!(
            verdicts(
                &stated(StatedEnd::Ended(EndWord::Final), true, false),
                &side
            ),
            [different(), different(), not_compared()]
        );
        // An answer naming a declared refused end: the definition states no declared class, so
        // the refusal is compared with nothing, and the row records none.
        let named = json!({"end": "crate::trap", "reason": null});
        assert_eq!(
            verdicts(&rejected(Some(named)), &side),
            [equal(), equal(), not_compared()]
        );
        // A crash disagrees with the definition's rejection (README D1).
        assert_eq!(
            crashed_row(&implementation.views[1], &Acceptance::Rejected).unwrap()["difference"],
            acceptance_difference("rejects", "crashed")
        );
        // No start: an implementation given `start` is not asked, and its required views decide
        // nothing.
        let manifest = decoded(&format!("{PROGRAM}{ONE}")).unwrap();
        let start = Err(no_start(RejectedStage::Parse));
        let reason = request(
            &manifest,
            &manifest.programs[0],
            &manifest.implementations[0],
            &json!({}),
            Some(&start),
            None,
        )
        .unwrap_err();
        assert_eq!(
            (reason.reason(), reason.status()),
            ("rejected-before-run", EXIT_YES)
        );
        assert!(reason.detail().contains("no start"), "{}", reason.detail());
        let row = json!({"views": not_compared_rows(&manifest.implementations[0], &reason),
                         "failure": null, "required": true});
        assert_eq!(row_status(&row), EXIT_YES);
        // Inputs with no document: the definition's own rejection at `input`, else the front
        // end's fault as before.
        assert_eq!(
            no_inputs(Some(RejectedStage::Input), "bad value").reason(),
            "rejected-before-run"
        );
        for rejected in [Some(RejectedStage::Parse), None] {
            let reason = no_inputs(rejected, "bad value");
            assert_eq!(
                (reason.reason(), reason.status()),
                ("unreadable", EXIT_UNASKED)
            );
        }
        // An unmet statement: nothing is asked, and the corpus or the grammar must change.
        let rows = definition_rows(
            &manifest.implementations[0],
            ResultClass::Accepted.as_str(),
            Some("admission admits it"),
        );
        assert!(
            rows.iter().all(|row| row["reason"] == "definition"
                && row["status"] == EXIT_UNASKED
                && row["detail"].as_str().unwrap().contains("it runs nothing")),
            "{rows:#?}"
        );
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
                metrics: None,
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
                metrics: None,
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
                metrics: None,
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
            metrics: None,
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
            None,
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
            None,
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
            None,
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
            None,
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
            None,
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
            None,
        )
        .unwrap();
        assert!(
            rows.iter()
                .all(|row| row["verdict"] == "could-not-apply" && row["detail"] == "late")
        );
        // Projections D6: a disagreement with a reason.
        assert_eq!(status(&rows), EXIT_NO);

        // A trace view the front end did not compare fails the command.
        assert!(
            answered_rows(
                &mock,
                &mixed,
                &stated(StatedEnd::Horizon, false, true),
                None,
                &[],
                None,
                None
            )
            .is_err()
        );
    }

    /// Every entry says how far apart the two sides are (README "Verdicts", `distance`), and the
    /// summary, the text and the lock count each (implementation, view)'s agreement; neither
    /// changes a verdict or a status.
    #[test]
    fn an_entry_reports_its_distance_and_each_view_its_agreement() {
        let implementation = second(&format!("{END}, {TICKS}"));
        let ends = BTreeSet::new();
        let words = BTreeSet::from(["final"]);
        let end_row = |end: Judged, stated: &Stated| {
            let mock = Mock {
                end,
                ..Mock::judging(Vec::new())
            };
            end_view_row(
                &mock,
                &implementation,
                &implementation.views[0],
                stated,
                (&ends, &words),
                &[],
            )
            .unwrap()
        };
        let ended = stated(StatedEnd::Ended(EndWord::Final), true, false);
        let equal = Judged::Equal {
            omitted: Vec::new(),
            compared_cells: 4,
        };
        let different = Judged::Different {
            difference: json!({"format": "krs-difference/3", "cell": "acc"}),
            omitted: Vec::new(),
            distance: Distance {
                differing_cells: 3,
                compared_cells: 4,
            },
        };
        let row = end_row(equal.clone(), &ended);
        assert_eq!(row["verdict"], "equal");
        assert_eq!(
            row["distance"],
            json!({"differing_cells": 0, "compared_cells": 4})
        );
        let row = end_row(different.clone(), &ended);
        assert_eq!(row["verdict"], "different");
        assert_eq!(
            row["distance"],
            json!({"differing_cells": 3, "compared_cells": 4})
        );
        // The words differ: the verdict is the word difference, the distance the cells'.
        let stopped = stated(StatedEnd::Ended(EndWord::Stopped), true, false);
        let row = end_row(different, &stopped);
        assert_eq!(row["difference"]["format"], "kink-end/1");
        assert_eq!(
            row["distance"],
            json!({"differing_cells": 3, "compared_cells": 4})
        );
        let row = end_row(equal.clone(), &stopped);
        assert_eq!(row["difference"]["format"], "kink-end/1");
        assert_eq!(
            row["distance"],
            json!({"differing_cells": 0, "compared_cells": 4})
        );
        // No cells to count (a `horizon` answer), or a comparison of them that does not
        // conclude: the distance is uncounted, the verdict the same.
        let row = end_row(equal, &stated(StatedEnd::Horizon, false, true));
        assert_eq!(row["verdict"], "different");
        assert!(row["distance"].is_null());
        let undecided = Judged::NotCompared(NotCompared::Undecided("stopped".to_owned()));
        let row = end_row(undecided.clone(), &stopped);
        assert_eq!(row["verdict"], "different");
        assert!(row["distance"].is_null());
        let row = end_row(undecided, &ended);
        assert_eq!(row["verdict"], "not-compared");
        assert!(row["distance"].is_null());

        // A trace view: the agreeing elements per channel, or where it first differs.
        let (closed, _) = ticks_row(
            4,
            CLOSED,
            5,
            TraceJudged::Agree(vec![agreed("ticks", 4, TraceReach::Closed)]),
        )
        .unwrap();
        assert_eq!(closed["verdict"], "equal");
        assert_eq!(
            closed["distance"],
            json!({"agreeing_elements": {"ticks": 4}})
        );
        let (up_to, _) = ticks_row(
            6,
            open(Opening::Bound),
            6,
            TraceJudged::Agree(vec![agreed("ticks", 6, bounded(None))]),
        )
        .unwrap();
        assert_eq!(up_to["verdict"], "agree-up-to");
        assert_eq!(
            up_to["distance"],
            json!({"agreeing_elements": {"ticks": 6}})
        );
        let (short, _) = ticks_row(
            6,
            open(Opening::Bound),
            6,
            TraceJudged::Agree(vec![agreed("ticks", 2, bounded(Some("nothing")))]),
        )
        .unwrap();
        assert_eq!(short["status"], EXIT_UNANSWERED);
        let (differs, _) = ticks_row(6, CLOSED, 7, TraceJudged::Different(difference())).unwrap();
        assert_eq!(
            differs["distance"],
            json!({"first_difference": {"channel": "ticks", "index": 3}})
        );

        // Per (implementation, view): the programs compared, and those that agree: `equal`, and
        // `agree-up-to` only where every horizon is the definition's.
        let mut not = view_row(&implementation.views[1]);
        not_compared_row(
            &mut not,
            &NotCompared::SeveralPaths(SEVERAL_PATHS.to_owned()),
        );
        let end = |verdict: &str| json!({"view": "end", "required": true, "verdict": verdict});
        let rows = [
            (end("equal"), closed),
            (end("different"), up_to),
            (end("could-not-apply"), short),
            (end("not-compared"), not),
        ]
        .into_iter()
        .enumerate()
        .map(|(index, (end, trace))| {
            json!({"implementation": "fake", "program": format!("p{index}"), "required": true,
                   "request_sha256": "rr", "failure": null, "views": [end, trace]})
        })
        .chain([
            json!({"implementation": "fake", "program": "p4", "required": true,
                       "failure": {"kind": "exit", "detail": "exit 101"}, "views": []}),
        ])
        .collect::<Vec<_>>();
        let counts = json!([
            {"implementation": "fake", "view": "end", "required": true, "compared": 3, "agreeing": 1},
            {"implementation": "fake", "view": "ticks", "required": true, "compared": 3, "agreeing": 2},
        ]);
        let summary = summary(&rows, true, &[], &[]);
        assert_eq!(summary["views"], counts);
        let document = json!({"schema": COMPARE_SCHEMA, "rows": rows, "summary": summary,
                              "implementations": [{"name": "fake"}]});
        let text = text(&document).unwrap();
        assert!(
            text.contains("fake end (required): 1 of 3 programs compared agree\n")
                && text.contains("fake ticks (required): 2 of 3 programs compared agree\n"),
            "{text}"
        );
        // A lock row holds a horizon as text, and is counted as the summary counts it.
        let locked = verdict_rows(&document);
        assert!(locked.iter().any(|row| row["horizon"].is_string()));
        let from_lock = view_counts(locked.iter().map(|row| ViewEntry {
            implementation: row["implementation"].as_str().unwrap(),
            view: row["view"].as_str().unwrap(),
            required: row["required"] == true,
            verdict: row["verdict"].as_str().unwrap(),
            horizon: row["horizon"].clone(),
        }));
        assert_eq!(json!(from_lock), counts);
    }

    /// The rows, the summary and the text of an implementation of the first protocol are what
    /// they were before a second existed, but for each entry's `distance` and each view's
    /// agreement (version 5): no key and no word of a trace.
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
                distance: Distance {
                    differing_cells: 1,
                    compared_cells: 2,
                },
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
            None,
        )
        .unwrap();
        assert_eq!(
            serde_json::to_string(&rows).unwrap(),
            r#"[{"detail":null,"difference":{"format":"krs-difference/3","path":"acc"},"distance":{"compared_cells":2,"differing_cells":1},"omitted":["k"],"reason":null,"required":true,"status":null,"verdict":"different","view":"writes"},{"detail":null,"difference":{"format":"krs-difference/3","path":"acc"},"distance":{"compared_cells":2,"differing_cells":1},"omitted":["k"],"reason":null,"required":false,"status":null,"verdict":"different","view":"all"}]"#
        );
        assert_eq!(
            Stated::from(answer).value().to_string(),
            r#"{"end":"stopped","reason":null}"#
        );
        // A program its bounds cut is told of as before, and nothing is asked.
        assert_eq!(
            serde_json::to_string(&definition_rows(implementation, "comparable-prefix", None))
                .unwrap(),
            r#"[{"detail":"the definition's run of the program is `comparable-prefix`: it has no end to compare","difference":null,"distance":null,"omitted":[],"reason":"definition","required":true,"status":3,"verdict":"not-compared","view":"writes"},{"detail":"the definition's run of the program is `comparable-prefix`: it has no end to compare","difference":null,"distance":null,"omitted":[],"reason":"definition","required":false,"status":3,"verdict":"not-compared","view":"all"}]"#
        );
        let rows = vec![
            json!({"implementation": "cpu", "program": "p", "required": true,
                               "failure": null, "views": rows}),
        ];
        let summary = summary(&rows, false, &[], &[]);
        assert_eq!(
            summary.to_string(),
            r#"{"failures":0,"required":{"could-not-apply":0,"different":1,"equal":0,"not-compared":0},"verdicts":{"could-not-apply":0,"different":2,"equal":0,"not-compared":0},"views":[{"agreeing":0,"compared":1,"implementation":"cpu","required":true,"view":"writes"},{"agreeing":0,"compared":1,"implementation":"cpu","required":false,"view":"all"}]}"#
        );
        let document = json!({"schema": COMPARE_SCHEMA, "rows": rows, "summary": summary});
        assert_eq!(
            text(&document).unwrap(),
            "cpu p writes (required): different at acc\ncpu p all (reported): different at \
             acc\ncpu writes (required): 0 of 1 programs compared agree\ncpu all (reported): 0 \
             of 1 programs compared agree\nverdicts: 0 equal, 2 different, 0 could-not-apply, 0 not-compared; required \
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
        let summary = summary(&rows, true, &[], &[]);
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
                "fake ticks (required): 1 of 3 programs compared agree".to_owned(),
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
