//! `kink-flow prune FLOW.toml MUTATIONS [PATTERNS.toml]`: which cases of the corpus are
//! redundant, read from what the corpus discharges (README, "Redundant programs"). It writes no
//! lock and edits no file; it reads and fills the caches as `run`, `query` and `coverage` do.
//!
//! # The obligations
//!
//! A corpus discharges existential obligations, each of the shape "some case does X":
//!
//! - `mutations`: a mutation is killed, discharged by every case whose cell of the full kill
//!   matrix is a proved difference ([`crate::report::kill_cells`]);
//! - `patterns`: a pattern is hit, discharged by every case whose answer is a hit
//!   ([`crate::query::hit_cells`]); every pattern is an obligation of the corpus, with or without
//!   `programs` ([`crate::query`], "The obligation");
//! - each coverage family's items (`rules`, `requirements` with their unique-cause level,
//!   `syntax`, `rule_windows`, `syntax_paths`, `flips`), discharged by the cases the item's
//!   covering list names ([`crate::coverage::cover_cells`]);
//! - `arguments`: an argued item's invariant evidence that holds, discharged by every case whose
//!   run read a step of the item's rules ([`crate::coverage::argument_cells`]).
//!
//! Each obligation's row gives, per case, a decided discharge, a decided non-discharge, or an
//! unknown cell (an answer neither decided nor refuted: a timeout, an unknown, a record that left
//! a combination out). An unknown cell never discharges. An obligation with no case that can
//! discharge it in any corpus (an `equivalent` mutation, a refused flip, an out-of-scope rule) is
//! none.
//!
//! The report is computed, never read from a stored document: `prune` runs `coverage` (tier 2,
//! the flips where the front end derives them) in process, then the kill search and the pattern
//! walk of the corpus (lazily, "Lazy cells" below; with `--full` `run --full` and `query
//! --full`), each through its own command's code and caches ([`crate::coverage::coverage_front`],
//! [`crate::search::run_session`], [`crate::query::query_session`]), so it is a function of the
//! definition, the corpus and the counted budgets, as their verdicts are. The run stores no report
//! ([`crate::search::run_stored`]), so `report` and `fuzz --kill` keep reading the last `run`'s.
//! A family whose input is absent is skipped, and the document says so: no mutation list (a front
//! end's layout without one), or no patterns (none named and none declared).
//!
//! # The lists
//!
//! The `mutations` and `patterns` families read a list, and each `families` entry names it
//! (`list`: `{path, corpus_own}`, `path` null for the patterns the manifest declares or a
//! family with no list). The report holds for the lists it read: a case removable against a
//! list that is not the corpus's own may be the only killer of a mutation of the corpus's own
//! list. Only a front end knows its corpus's own lists (its layout), so `corpus_own` is what the
//! front end states ([`PruneOptions::corpus_lists`]), and null where none does: kink-flow's own
//! command line takes the mutation list as an operand and has no notion of a corpus's own list.
//!
//! # What is never prunable
//!
//! - A case a claim names: a pattern's `programs`. Removing it makes the pattern list refuse
//!   (`no program of the manifest has the id`). Nothing else of the manifest, the mutation lists
//!   or the pattern lists names a case: a mutation's `expect` states a verdict, not a case.
//! - A case whose decided cell refutes a universal claim: a killer of a mutation that expects to
//!   survive, a hitter of a pattern that expects `no`, the case whose run gave an argued item's
//!   invariant evidence its failing state, and a case whose own expectation is unmet. Removing
//!   it would hide the finding, not a redundancy.
//! - A case that is the only decided discharger of an obligation.
//! - A case whose cell on an obligation is unknown while no other case discharges that
//!   obligation: removing it could lose the only potential discharger.
//! - A case whose baseline run is undecided (class `timeout` or `unknown`: kink did not ask it of
//!   any mutant or pattern) while some obligation has no decided discharger: each of its cells
//!   is unknown, so the rule above applies to every obligation.
//!
//! So the report only ever under-states what is prunable: every unknown counts against removal.
//! The document counts the unknown cells (`unanswered`).
//!
//! # Redundant alone, and removable together
//!
//! A case is redundant alone when it is not kept by any rule above against the whole corpus:
//! every obligation it discharges has another decided discharger, and every obligation on which
//! its cell is unknown has a decided discharger. That is not the same as removable together: two
//! cases can each be the other's only alternative. So the report also gives one set removable
//! together, built greedily: walking the cases in reverse manifest order, a case is removed when
//! the same rules, read against the cases still kept, keep it nowhere. Each obligation then keeps
//! a decided discharger among the kept cases (or every unknown cell it had), whatever is removed.
//!
//! The order is reverse manifest order because every command that names one discharger of an
//! obligation names, by default, an early case: a mutation's killer is the first killing case of
//! the search order, whose groups are each in manifest order, and a pattern's witness the first
//! hitting case in manifest order, while no record names another ([`crate::search`],
//! [`crate::query`]). Removing the latest cases first keeps those, so the corpus record's rows
//! move least. The set is a function of the corpus and of this order; it is maximal under the
//! order (no kept case can be removed after it), not minimum: a smallest removable set is a
//! set cover problem.
//!
//! # Lazy cells
//!
//! The report reads three things of an obligation's row: whether a decided discharger other than
//! the case judged is among the cases still considered (the sole and unknown rules), the case's
//! own cell (discharger, unknown or neither), and, for a claim a decided cell refutes, every
//! refuting case. It never needs a row's every cell to answer them. Without `--full` the
//! `mutations` and `patterns` rows are asked lazily, and every decision is still the one the full
//! rows give:
//!
//! - The ordinary search of each family runs first: `run`'s first-kill search over the list and
//!   `query`'s walk of each pattern ([`crate::search`], [`crate::query`], "The obligation"),
//!   through their code and caches. A killed mutation's search gives one decided killer, its
//!   witness here, and every cell it asked before it; a hit pattern's walk one hitter and the
//!   pairs it asked. Every other row (survived, unknown, open, undecided, or no obligation) is
//!   one the search asked of every case it can be asked of, so it is complete, as under
//!   `--full`. Which killer or hitter it found depends on the recorded killer or witness of
//!   `--lock` and on the search order, never a decision: the decisions are functions of the
//!   cells alone.
//! - Let w be a known decided discharger of an obligation o, and S the cases considered (the
//!   whole corpus for redundant alone, the cases still kept during the walk). For a case c ≠ w
//!   with w in S, o keeps c by no rule: c is not o's only decided discharger in S, since w is
//!   one, and the unknown and baseline-undecided rules apply only to an obligation with no
//!   decided discharger in S other than c. So while some known discharger other than c is in S,
//!   no unasked cell of o can change the decision about c.
//! - When none is, the decision needs more of the row: its cells over S other than c that were
//!   not asked are asked one at a time (a mutation's in its search order, the programs that
//!   witness its edit first, a pattern's in manifest order) until one is a decided discharger or
//!   none is left, and then c's own cell if it was not asked. Each is asked through the code
//!   its full command asks it with ([`crate::search::KillCells`], [`crate::query::HitCells`]):
//!   a mutation's full row over an O holding that program alone, under the corpus's floor of
//!   polls, which tier 1 serves when a record is current; a pattern's one row. No record of the
//!   corpus record (`--lock`) is a cell: it only orders the searches. Every cell learned is
//!   kept for the later decisions. Then o's known cells over S other than c are its every cell
//!   there, so the rules read what the full row gives.
//! - A mutation that expects to survive and is killed, and a pattern that expects `no` and is
//!   hit, keep every refuting case: their rows are asked whole.
//! - A case that is not redundant alone is kept by the walk without asking anything: each rule
//!   only weakens as S shrinks (a discharger outside S counts for nothing), so a case some rule
//!   keeps against the whole corpus is kept against every S. The document gives no reason the
//!   walk found for it.
//! - Within a family a cell's value does not depend on which other cells were asked: under tier
//!   1 an outcome is a function of its key ([`crate::search`], module docs, the schedule
//!   paragraph) and a pattern answer of its own key ([`crate::query`]). Where the caches are off
//!   (a solver the clock bounds), every cell is a live run in either mode, and neither mode's
//!   report is a function of its inputs.
//!
//! In a lazy report the evidence holds the cells asked, not every cell: each obligation of a
//! `redundant` entry lists the other known dischargers (`others`) with whether its row is
//! complete (`complete`), the entry counts the obligations on which the case's own cell was not
//! asked (`unasked`), and each family and `unanswered` say whether every cell was asked
//! (`complete`). A distinguished flip's row is never complete: its kill search stops at its
//! first killer (limit `flips`). `accounting.cells` counts each family's cells: the matrix size,
//! those the ordinary search held, and those asked one at a time after it.
//!
//! # The corpus record
//!
//! With `--lock FILE` the record is read, never written: a removable case that is a recorded
//! killer (`[run]`, `[coverage]` flips), witness (`[query]`) or a program of a compare row
//! (`[compare]`) moves those rows when it is removed, so `--locked` fails until a command
//! without it re-records them; the document names them per case.
//!
//! # Limits
//!
//! `[[implementation]]` compare evidence and a case's own expectation are universal per case,
//! not existential, and are not read as obligations (an unmet expectation still keeps its case).
//! A fuzz template list may name a case (`program`); it is not read.

use crate::{
    cli::{EXIT_UNASKED, EXIT_YES, FrontEnd, Verb, completed},
    coverage::{ARGUED, CoverageOptions, FAMILIES},
    flips::DISTINGUISHED,
    lock::{Lock, LockKind},
    manifest::FlowManifest,
    mutation::{Expect, MutationList},
    pattern::{PatternExpect, PatternList},
    query::{HitCell, HitCells, QueryOptions},
    results::ResultClass,
    search::{KillCell, KillCells, RunMode, RunOptions},
};
use kink_campaign::ScheduleMode;
use kink_native::execution::SolverProfile;
use serde_json::{Value, json};
use std::path::{Path, PathBuf};

/// The `schema` of the prune document.
pub const PRUNE_SCHEMA: &str = "kink-flow-prune";
/// The version of the prune document. Version 2 asks the `mutations` and `patterns` rows lazily
/// unless `--full` (module docs, "Lazy cells"), with the same decisions, and names what the
/// evidence holds: the document's `mode` (`lazy` or `full`); each family's `list` (`{path,
/// corpus_own}`, the `mutations` and `patterns` families) and `complete`; each `redundant`
/// entry's obligations and unknown cells with `complete`, and its `unasked`; `unanswered`'s
/// `complete`; `accounting.cells`; and the limit `lazy` of a lazy report. Every field of
/// version 1 keeps its name and, under `--full`, its value.
pub const PRUNE_VERSION: u64 = 2;

/// The order the removable set is built in (`removable.order`, module docs).
pub const REVERSE_MANIFEST_ORDER: &str = "reverse-manifest";

/// The document's `mode` without `--full`: the rows asked lazily (module docs, "Lazy cells").
pub const LAZY: &str = "lazy";
/// The document's `mode` under `--full`: every cell of every row asked.
pub const FULL: &str = "full";

/// The obligation families, in the order the document lists them.
pub const PRUNE_FAMILIES: [&str; 9] = [
    "mutations",
    "patterns",
    "rules",
    "requirements",
    "syntax",
    "rule_windows",
    "syntax_paths",
    "flips",
    "arguments",
];

/// What the report does not read, each `{limit, detail}` in the document's `limits`.
const LIMITS: [(&str, &str); 5] = [
    (
        "implementation",
        "[[implementation]] compare evidence is universal per case, not an existential: it is \
         not read, and removing a case drops its [compare] rows (lock consequences)",
    ),
    (
        "case-expectation",
        "a case's own expectation is a claim about that case alone, not an existential: it is \
         not read as an obligation; an unmet one keeps its case",
    ),
    (
        "templates",
        "a fuzz template list, whose templates may name a case (`program`), is not read",
    ),
    (
        "flips",
        "a condition flip's kill search stops at its first killer, so its killer is its only \
         decided discharger",
    ),
    (
        "maximal",
        "the removable set is maximal under its order, not minimum: a smallest one is a set \
         cover problem",
    ),
];

/// The limit of a lazy report (`limits`, module docs "Lazy cells").
const LAZY_LIMIT: (&str, &str) = (
    "lazy",
    "a cell is asked only where a decision needs it: the evidence (`others`, `unknown`, \
     `unanswered`) holds the cells asked, and `complete` says where that is every cell; the \
     decisions are those of --full, which asks every cell",
);

/// Options of the `prune` command.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct PruneOptions {
    /// The cache directory; default `<directory of FLOW.toml>/.kink-flow`.
    pub cache: Option<PathBuf>,
    /// `--lock FILE`: the corpus record, read for the rows a removal moves and for the order
    /// the searches ask in, never written.
    pub lock: Option<PathBuf>,
    /// `--compile-workers N`, as `run`'s ([`RunOptions::compile_workers`]).
    pub compile_workers: Option<usize>,
    /// `--full`: ask every cell of every row (`run --full`, `query --full`), where `prune`
    /// without it asks a cell only where a decision needs it (module docs, "Lazy cells"). The
    /// decisions are the same either way.
    pub full: bool,
    /// Whether each list the command reads is the corpus's own, as a front end that keeps a
    /// corpus layout states it ([`crate::cli::FlowCommand::set_corpus_lists`]); `None` where
    /// the caller knows no layout, as kink-flow's own command line does.
    pub corpus_lists: Option<CorpusLists>,
}

/// Whether the lists a `prune` reads are its corpus's own ([`PruneOptions::corpus_lists`]).
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct CorpusLists {
    /// The mutation list is the corpus's own (also when the corpus has none and none is named).
    pub mutations: bool,
    /// The patterns are the corpus's own (also when it declares none and none are named).
    pub patterns: bool,
}

/// What one obligation's row states of each case ([`Reading::Obligation`]).
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Cells {
    /// The cases whose decided cell discharges the obligation.
    pub dischargers: Vec<String>,
    /// The cases whose cell is unknown: neither a decided discharge nor a decided non-discharge.
    pub unknown: Vec<String>,
    /// The row says the obligation is discharged and names no case that does: every case's cell
    /// is then read as unknown.
    pub unnamed: bool,
}

/// What a document's row states, read as a fact of the corpus.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Reading {
    /// No obligation: no case of any corpus can discharge it.
    None,
    /// An existential obligation of the corpus, with its cells.
    Obligation(Cells),
    /// A universal claim that the listed cases' decided cells refute: a finding each of them is
    /// evidence of.
    Refuted(Vec<String>),
}

/// Where a cell of an obligation not yet asked is asked: the list's mutation, or the selected
/// pattern, at this index.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Source {
    Mutation(usize),
    Pattern(usize),
}

/// One cell, as the report reads it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Cell {
    /// A decided discharge.
    Discharges,
    /// A decided non-discharge.
    Not,
    /// Neither.
    Unknown,
}

/// Why a cell could not be asked: the family and the detail of its refusal.
type Refusal = (&'static str, String);

/// The commands a lazy report asks its cells through.
trait Ask {
    /// The cell of `source` on the case at `case`, and whether a cache served it.
    fn ask(&mut self, source: Source, case: usize) -> Result<(Cell, bool), Refusal>;
    /// A progress line.
    fn announce(&self, line: &str);
    /// The run's `outcome_cache` and `baseline_runs` and the query's `pattern_cache` as they
    /// stand (null for a family that did not run).
    fn caches(&self) -> [Value; 3];
}

/// A report of complete rows asks nothing (`--full`): the documents' `outcome_cache`,
/// `baseline_runs` and `pattern_cache`.
struct Complete([Value; 3]);

impl Ask for Complete {
    fn ask(&mut self, _: Source, _: usize) -> Result<(Cell, bool), Refusal> {
        Err((
            "mutations",
            "a complete row has no cell left to ask".to_owned(),
        ))
    }

    fn announce(&self, _: &str) {}

    fn caches(&self) -> [Value; 3] {
        self.0.clone()
    }
}

/// The open search of each family a lazy report asks its cells through.
struct Askers<'c, 'k, 'h> {
    cases: &'c [String],
    kills: Option<&'k mut dyn KillCells>,
    hits: Option<&'h mut dyn HitCells>,
    progress: Option<&'c (dyn Fn(&str) + Sync)>,
}

impl Ask for Askers<'_, '_, '_> {
    fn ask(&mut self, source: Source, case: usize) -> Result<(Cell, bool), Refusal> {
        match source {
            Source::Mutation(index) => {
                let kills = self
                    .kills
                    .as_deref_mut()
                    .ok_or_else(|| ("mutations", "no search asks the mutations".to_owned()))?;
                let (cell, cached) = kills
                    .cell(index, &self.cases[case])
                    .map_err(|row| ("mutations", row_refusal(&row)))?;
                Ok((
                    match cell {
                        KillCell::Kill => Cell::Discharges,
                        KillCell::Agree => Cell::Not,
                        KillCell::Unknown => Cell::Unknown,
                    },
                    cached,
                ))
            }
            Source::Pattern(index) => {
                let hits = self
                    .hits
                    .as_deref_mut()
                    .ok_or_else(|| ("patterns", "no query asks the patterns".to_owned()))?;
                let (cell, cached) = hits
                    .cell(index, case)
                    .map_err(|row| ("patterns", row_refusal(&row)))?;
                Ok((
                    match cell {
                        HitCell::Hit => Cell::Discharges,
                        HitCell::No => Cell::Not,
                        HitCell::Unknown => Cell::Unknown,
                    },
                    cached,
                ))
            }
        }
    }

    fn announce(&self, line: &str) {
        if let Some(progress) = self.progress {
            progress(line);
        }
    }

    fn caches(&self) -> [Value; 3] {
        [
            self.kills
                .as_deref()
                .map_or(Value::Null, KillCells::outcome_cache),
            self.kills
                .as_deref()
                .map_or(Value::Null, KillCells::baseline_runs),
            self.hits
                .as_deref()
                .map_or(Value::Null, HitCells::pattern_cache),
        ]
    }
}

/// The refusal detail of a row a cell's ask could not decide.
fn row_refusal(row: &Value) -> String {
    let named = |key: &str| row[key].as_str().unwrap_or("?").to_owned();
    format!(
        "asking `{}` of `{}` met an error: {}: {}",
        row["id"]
            .as_str()
            .or_else(|| row["pattern"].as_str())
            .unwrap_or("?"),
        row["program"].as_str().unwrap_or("its program"),
        row["reason"]
            .as_str()
            .or_else(|| row["answer"].as_str())
            .unwrap_or("error"),
        row["detail"]
            .as_str()
            .or_else(|| row["cause"].as_str())
            .map_or_else(|| named("cache_error"), str::to_owned),
    )
}

/// One obligation, its cells by case index.
struct Obligation {
    family: &'static str,
    id: String,
    /// The known decided dischargers, in manifest order.
    dischargers: Vec<usize>,
    /// The known unknown cells, in manifest order.
    unknown: Vec<usize>,
    /// The cases whose cell was not asked, in the order they are asked; empty for a complete
    /// row.
    unasked: Vec<usize>,
    /// Where an unasked cell is asked.
    source: Option<Source>,
    /// The search that gave the row stopped at its first discharger (a distinguished flip):
    /// the cells after it were never asked, and are read as non-discharge (limit `flips`).
    stopped: bool,
}

impl Obligation {
    /// Every cell of the row is known.
    fn complete(&self) -> bool {
        self.unasked.is_empty() && !self.stopped
    }
}

/// Why a case is kept, against a set of kept cases.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Keep {
    /// A pattern's `programs` names it.
    Claimed(String),
    /// Its decided cell refutes a universal claim (family, id).
    Refutes(&'static str, String),
    /// It is the only kept decided discharger of the obligation at this index.
    Sole(usize),
    /// Its cell is unknown on the obligation at this index, which no kept case discharges.
    Unknown(usize),
    /// Its baseline is undecided (its class), and these obligations have no kept discharger.
    Undecided(String, Vec<usize>),
}

/// A family's facts as the commands gave them.
struct Family {
    name: &'static str,
    /// `None` when computed; else the reason token and its detail.
    skipped: Option<(&'static str, String)>,
}

/// What a family's cells cost (`accounting.cells`): the matrix's size, the cells the ordinary
/// search held, and the cells asked one at a time after it, of which a cache served
/// `from_cache`.
#[derive(Clone, Copy, Debug, Default)]
struct Asked {
    matrix: usize,
    searched: usize,
    asked: usize,
    from_cache: usize,
}

impl Asked {
    fn value(self) -> Value {
        json!({
            "matrix": self.matrix,
            "searched": self.searched,
            "asked": self.asked,
            "from_cache": self.from_cache,
        })
    }
}

/// What a lazy report does with the open first-kill search (`None` without a mutation list).
type WithRun<'f> = dyn FnMut(Option<(&Value, &mut dyn KillCells)>) -> (Value, u8) + 'f;
/// What a lazy report does with the open pattern walk (`None` without patterns).
type WithQuery<'f> = dyn FnMut(Option<(&Value, &mut dyn HitCells)>) -> (Value, u8) + 'f;

/// What the commands give `prune`, read before its families' searches run.
struct Inputs<'a> {
    manifest: &'a FlowManifest,
    options: &'a PruneOptions,
    front: &'a FrontEnd<'a>,
    locks: &'a [Lock],
    list: Option<&'a MutationList>,
    pattern_list: Option<&'a PatternList>,
    coverage: &'a Value,
    skipped: &'a [Family],
    /// Each family's `list` (`mutations`, `patterns`).
    lists: [Value; 2],
}

impl Inputs<'_> {
    fn announce(&self, line: &str) {
        if let Some(progress) = self.front.progress {
            progress(line);
        }
    }

    fn lock(&self, kind: LockKind) -> Option<&Lock> {
        self.locks.iter().find(|lock| lock.kind == kind)
    }

    fn run_options(&self, schedule: ScheduleMode) -> RunOptions {
        RunOptions {
            cache: self.options.cache.clone(),
            compile_workers: self.options.compile_workers,
            schedule,
            ..RunOptions::default()
        }
    }

    fn query_options(&self) -> QueryOptions {
        QueryOptions {
            cache: self.options.cache.clone(),
            full: self.options.full,
            no_explain: true,
            ..QueryOptions::default()
        }
    }

    /// The refusal of a family whose own command could not ask its question.
    fn family_refused(&self, family: &str, document: &Value, verb: Verb) -> (Value, u8) {
        let flag = if self.options.full { " --full" } else { "" };
        refused(
            family,
            Some(document),
            &format!("`{}{flag}` shows why", self.front.spelling.command(verb)),
        )
    }

    /// The prune document from the families' documents (each `None` where its family is
    /// skipped), asking further cells through `ask`; the `accounting`'s caches and baseline
    /// runs are as they stand once every cell is asked ([`Ask::caches`]).
    fn report(&self, run: Option<&Value>, query: Option<&Value>, ask: &mut dyn Ask) -> (Value, u8) {
        let claimed = self.pattern_list.map(claims).unwrap_or_default();
        let lazy = !self.options.full;
        let built = Facts::read(self, run, query, claimed, lazy, ask).and_then(|mut facts| {
            let document = facts.document(self.locks, &self.lists, ask)?;
            Ok((facts, document))
        });
        let (facts, mut document) = match built {
            Ok(built) => built,
            Err((family, detail)) => return refused(family, Some(self.coverage), &detail),
        };
        document["spec"] = self.coverage["spec"].clone();
        let [outcome_cache, baseline_runs, pattern_cache] = ask.caches();
        document["accounting"] = json!({
            "mutations": run.map(|_| json!({
                "outcome_cache": outcome_cache,
                "baseline_runs": baseline_runs,
            })),
            "patterns": query.map(|_| pattern_cache),
            "coverage": {"baseline_runs": self.coverage["baseline_runs"]},
            "cells": {
                "mutations": run.map(|_| facts.cells[0].value()),
                "patterns": query.map(|_| facts.cells[1].value()),
            },
        });
        (document, EXIT_YES)
    }

    /// `--full`: `run --full` and `query --full`, each in one pass, and the report of their
    /// complete rows.
    fn full(&self) -> (Value, u8) {
        let mut run = None;
        if let Some(list) = self.list {
            self.announce("prune: run --full of the mutation list");
            let (document, ok) = crate::search::run_stored(
                self.manifest,
                list,
                &self.run_options(ScheduleMode::Full),
                RunMode::Search,
                self.front,
                false,
            );
            if completed(crate::cli::run_status(&document), ok) == EXIT_UNASKED {
                return self.family_refused("mutations", &document, Verb::Run);
            }
            run = Some(document);
        }
        let mut query = None;
        if let Some(list) = self.pattern_list {
            self.announce("prune: query --full of the patterns");
            let (document, ok) = crate::query::query_spelled(
                self.manifest,
                list,
                &self.query_options(),
                &self.front.spelling.verb(Verb::Query),
            );
            if completed(crate::cli::query_status(&document), ok) == EXIT_UNASKED {
                return self.family_refused("patterns", &document, Verb::Query);
            }
            query = Some(document);
        }
        let mut complete = Complete([
            run.as_ref()
                .map_or(Value::Null, |run| run["outcome_cache"].clone()),
            run.as_ref()
                .map_or(Value::Null, |run| run["baseline_runs"].clone()),
            query
                .as_ref()
                .map_or(Value::Null, |query| query["pattern_cache"].clone()),
        ]);
        self.report(run.as_ref(), query.as_ref(), &mut complete)
    }

    /// Without `--full`: the first-kill search of the mutation list and the walk of the
    /// patterns, each kept open while the report asks its further cells (module docs, "Lazy
    /// cells").
    fn lazy(&self) -> (Value, u8) {
        self.with_run(&mut |mut run| {
            self.with_query(&mut |query| {
                let run: Option<(&Value, &mut dyn KillCells)> = match &mut run {
                    Some((document, kills)) => Some((*document, &mut **kills)),
                    None => None,
                };
                self.lazy_report(run, query)
            })
        })
    }

    /// The lazy report of the open searches.
    fn lazy_report(
        &self,
        run: Option<(&Value, &mut dyn KillCells)>,
        query: Option<(&Value, &mut dyn HitCells)>,
    ) -> (Value, u8) {
        let cases = self
            .manifest
            .programs
            .iter()
            .map(|program| program.id.clone())
            .collect::<Vec<_>>();
        let (run, kills) = run.unzip();
        let (query, hits) = query.unzip();
        let mut askers = Askers {
            cases: &cases,
            kills,
            hits,
            progress: self.front.progress,
        };
        self.report(run, query, &mut askers)
    }

    /// `f` of the open first-kill search of the mutation list (`None` without a list), or the
    /// refusal of a search that could not ask its question.
    fn with_run(&self, f: &mut WithRun<'_>) -> (Value, u8) {
        let Some(list) = self.list else {
            return f(None);
        };
        self.announce("prune: run of the mutation list (the first-kill search)");
        let recorded = self.lock(LockKind::Run).map(Lock::killers);
        let mut out = None;
        let (document, _) = crate::search::run_session(
            self.manifest,
            list,
            &self.run_options(ScheduleMode::FirstKill),
            RunMode::Search,
            self.front,
            false,
            Some(recorded.unwrap_or_default()),
            Some(&mut |document, ok, kills| {
                out = Some(
                    if completed(crate::cli::run_status(document), ok) == EXIT_UNASKED {
                        self.family_refused("mutations", document, Verb::Run)
                    } else {
                        f(Some((document, kills)))
                    },
                );
            }),
        );
        out.unwrap_or_else(|| self.family_refused("mutations", &document, Verb::Run))
    }

    /// `f` of the open walk of the patterns (`None` without patterns), or the refusal of a
    /// query that could not ask its question.
    fn with_query(&self, f: &mut WithQuery<'_>) -> (Value, u8) {
        let Some(list) = self.pattern_list else {
            return f(None);
        };
        self.announce("prune: query of the patterns (each walk to its first hit)");
        let recorded = self
            .lock(LockKind::Query)
            .map(Lock::witnesses)
            .unwrap_or_default();
        let mut out = None;
        let (document, _) = crate::query::query_session(
            self.manifest,
            list,
            &self.query_options(),
            &recorded,
            &mut |document, ok, hits| {
                out = Some(
                    if completed(crate::cli::query_status(document), ok) == EXIT_UNASKED {
                        self.family_refused("patterns", document, Verb::Query)
                    } else {
                        f(Some((document, hits)))
                    },
                );
            },
        );
        out.unwrap_or_else(|| self.family_refused("patterns", &document, Verb::Query))
    }
}

/// `kink-flow prune`: the prune document and the exit status, [`EXIT_YES`] when the report is
/// computed (unknowns make it conservative, never unanswered: every set it states holds), and
/// [`EXIT_UNASKED`] when a lock does not decode, a list does not decode, or a family's own command
/// could not ask its question (its exit status would be 2: a refused specification, program,
/// mutation or pattern, a corpus or infrastructure error, also one a cell asked lazily met),
/// whose document the refusal names. No status is 1: the report refutes nothing.
#[must_use]
pub fn command(
    manifest: &FlowManifest,
    mutations: Option<&Path>,
    patterns: Option<&Path>,
    options: &PruneOptions,
    front: &FrontEnd<'_>,
) -> (Value, u8) {
    let mut locks = Vec::new();
    if let Some(path) = &options.lock {
        for kind in [
            LockKind::Run,
            LockKind::Coverage,
            LockKind::Compare,
            LockKind::Query,
        ] {
            match Lock::read_kind(path, kind) {
                Ok(lock) => locks.push(lock),
                Err(detail) => return refused("lock", None, &detail),
            }
        }
    }
    // Every input is decoded before anything runs: a list that does not decode refuses the
    // command at once.
    let mut skipped = Vec::new();
    let list = match mutations.map(MutationList::read).transpose() {
        Ok(list) => list,
        Err(error) => return refused("mutations", None, &error.to_string()),
    };
    if list.is_none() {
        skipped.push(Family {
            name: "mutations",
            skipped: Some(("no-mutation-list", "no mutation list was given".to_owned())),
        });
    }
    let pattern_list = if patterns.is_none() && manifest.patterns.is_empty() {
        skipped.push(Family {
            name: "patterns",
            skipped: Some((
                "no-patterns",
                "no pattern list was given and the manifest declares none".to_owned(),
            )),
        });
        None
    } else {
        match crate::pattern::declared_patterns(manifest, patterns, front.krs_patterns) {
            Ok(list) => Some(list),
            Err(error) => return refused("patterns", None, &error.to_string()),
        }
    };
    let own = |pick: fn(&CorpusLists) -> bool| options.corpus_lists.as_ref().map(pick);
    let lists = [
        json!({
            "path": mutations.map(|path| path.display().to_string()),
            "corpus_own": own(|lists| lists.mutations),
        }),
        json!({
            "path": patterns.map(|path| path.display().to_string()),
            "corpus_own": own(|lists| lists.patterns),
        }),
    ];
    if let Some(progress) = front.progress {
        progress("prune: coverage of the corpus");
    }
    let coverage_options = CoverageOptions {
        cache: options.cache.clone(),
        ..CoverageOptions::default()
    };
    let coverage_lock = locks.iter().find(|lock| lock.kind == LockKind::Coverage);
    let (coverage, ok) =
        crate::coverage::coverage_front(manifest, &coverage_options, front, coverage_lock);
    let mut coverage = front.annotated(coverage);
    crate::coverage::derive(&mut coverage, front.spelling);
    if completed(crate::cli::coverage_status(&coverage), ok) == EXIT_UNASKED {
        return refused(
            "coverage",
            Some(&coverage),
            &format!("`{}` shows why", front.spelling.command(Verb::Coverage)),
        );
    }
    let inputs = Inputs {
        manifest,
        options,
        front,
        locks: &locks,
        list: list.as_ref(),
        pattern_list: pattern_list.as_ref(),
        coverage: &coverage,
        skipped: &skipped,
        lists,
    };
    if options.full {
        inputs.full()
    } else {
        inputs.lazy()
    }
}

/// Each claim of `list`: the pattern's id and the case its `programs` names.
fn claims(list: &PatternList) -> Vec<(String, String)> {
    list.patterns
        .iter()
        .flat_map(|entry| {
            entry
                .programs
                .iter()
                .flatten()
                .map(|program| (entry.id.clone(), program.clone()))
        })
        .collect()
}

/// The header every prune document has.
fn header() -> Value {
    crate::with_z3_build(json!({
        "schema": PRUNE_SCHEMA,
        "version": PRUNE_VERSION,
        "k_rust_revision": crate::k_rust_revision(),
        "profile": SolverProfile::BUILD.name(),
    }))
}

/// The document of a prune that could not ask its question: `refused`, `{family, detail}`, and
/// the family's document's `spec` where it has one; exit [`EXIT_UNASKED`].
fn refused(family: &str, document: Option<&Value>, detail: &str) -> (Value, u8) {
    let mut value = header();
    value["spec"] = document.map_or(Value::Null, |document| document["spec"].clone());
    value["refused"] = json!({"family": family, "detail": detail});
    (value, EXIT_UNASKED)
}

/// The prune document of a manifest that does not decode, under the command's schema.
#[must_use]
pub fn manifest_refused(error: &crate::ManifestError) -> Value {
    let mut document = crate::cli::manifest_refused(error);
    document["schema"] = json!(PRUNE_SCHEMA);
    document["version"] = json!(PRUNE_VERSION);
    document
}

/// The corpus's facts, by case index.
struct Facts {
    /// The cases, in manifest order.
    cases: Vec<String>,
    /// Each case's baseline class.
    classes: Vec<String>,
    obligations: Vec<Obligation>,
    /// Each case's claims and refutations.
    keeps: Vec<Vec<Keep>>,
    /// Each family, computed or skipped.
    families: Vec<Family>,
    /// Whether the rows were read lazily (the document's `mode`).
    lazy: bool,
    /// What the `mutations` and the `patterns` cells cost.
    cells: [Asked; 2],
}

/// Insert `at` into the sorted `into`, once.
fn insert(into: &mut Vec<usize>, at: usize) {
    if let Err(place) = into.binary_search(&at) {
        into.insert(place, at);
    }
}

impl Facts {
    #[allow(clippy::too_many_lines)]
    fn read(
        inputs: &Inputs<'_>,
        run: Option<&Value>,
        query: Option<&Value>,
        claims: Vec<(String, String)>,
        lazy: bool,
        ask: &mut dyn Ask,
    ) -> Result<Self, Refusal> {
        let (manifest, coverage) = (inputs.manifest, inputs.coverage);
        let cases = manifest
            .programs
            .iter()
            .map(|program| program.id.clone())
            .collect::<Vec<_>>();
        let index = |id: &str| cases.iter().position(|case| case == id);
        let indices = |ids: &[String]| {
            let mut found = ids.iter().filter_map(|id| index(id)).collect::<Vec<_>>();
            found.sort_unstable();
            found.dedup();
            found
        };
        let rows = coverage["programs"]
            .as_array()
            .map_or(&[][..], Vec::as_slice);
        let classes = cases
            .iter()
            .map(|case| {
                rows.iter()
                    .find(|row| row["id"] == case.as_str())
                    .and_then(|row| row["class"].as_str())
                    .unwrap_or("unknown")
                    .to_owned()
            })
            .collect::<Vec<_>>();
        // The cases a mutant runs on: the comparable ones (`run`'s O). Every other case has no
        // cell of the kill matrix, which reads it as no discharge.
        let comparable = classes
            .iter()
            .map(|class| ResultClass::can_kill(&json!(class)))
            .collect::<Vec<_>>();
        let mut keeps = vec![Vec::new(); cases.len()];
        for (pattern, case) in claims {
            if let Some(at) = index(&case) {
                keeps[at].push(Keep::Claimed(pattern));
            }
        }
        // A case's own expectation that its run does not meet.
        for row in rows {
            if row["expectation"]["verdict"] == "unmet"
                && let Some(at) = row["id"].as_str().and_then(index)
            {
                keeps[at].push(Keep::Refutes("expectations", cases[at].clone()));
            }
        }
        let mut facts = Self {
            classes,
            obligations: Vec::new(),
            keeps,
            families: Vec::new(),
            lazy,
            cells: [Asked::default(); 2],
            cases: cases.clone(),
        };
        let add =
            |facts: &mut Self, family: &'static str, id: &Value, reading: Reading| match reading {
                Reading::None => {}
                Reading::Refuted(by) => {
                    for at in indices(&by) {
                        facts.keeps[at].push(Keep::Refutes(family, text(id)));
                    }
                }
                Reading::Obligation(cells) => {
                    let (dischargers, unknown) = if cells.unnamed {
                        (Vec::new(), (0..cases.len()).collect())
                    } else {
                        let dischargers = indices(&cells.dischargers);
                        let mut unknown = indices(&cells.unknown);
                        unknown.retain(|at| !dischargers.contains(at));
                        (dischargers, unknown)
                    };
                    facts.obligations.push(Obligation {
                        family,
                        id: text(id),
                        dischargers,
                        unknown,
                        unasked: Vec::new(),
                        source: None,
                        stopped: false,
                    });
                }
            };
        if let Some(run) = run {
            let comparable_count = comparable.iter().filter(|c| **c).count();
            facts.cells[0].matrix =
                inputs.list.map_or(0, |list| list.mutations.len()) * comparable_count;
            for row in run["mutations"].as_array().into_iter().flatten() {
                let held = row["executed"]
                    .as_array()
                    .into_iter()
                    .flatten()
                    .filter_map(|entry| entry["program"].as_str().and_then(index))
                    .chain(row["killer"].as_str().and_then(index))
                    .filter(|at| comparable[*at])
                    .collect::<std::collections::BTreeSet<_>>();
                facts.cells[0].searched += held.len();
                let mutation = inputs.list.and_then(|list| {
                    list.mutations
                        .iter()
                        .position(|mutation| row["id"] == mutation.id.as_str())
                });
                let (true, Some(mutation)) = (lazy && row["status"] == "killed", mutation) else {
                    add(
                        &mut facts,
                        "mutations",
                        &row["id"],
                        crate::report::kill_cells(row),
                    );
                    continue;
                };
                // A killed row of the first-kill search: its killer and the cells it asked
                // before it; a cached kill it read past the killer is asked again.
                let killer = row["killer"].as_str().and_then(index);
                let mut obligation = Obligation {
                    family: "mutations",
                    id: text(&row["id"]),
                    dischargers: killer.into_iter().collect(),
                    unknown: Vec::new(),
                    unasked: Vec::new(),
                    source: Some(Source::Mutation(mutation)),
                    stopped: false,
                };
                let mut known = killer.into_iter().collect::<Vec<_>>();
                for entry in row["executed"].as_array().into_iter().flatten() {
                    let Some(at) = entry["program"].as_str().and_then(index) else {
                        continue;
                    };
                    match entry["outcome"].as_str() {
                        Some("distinguish") => {}
                        Some("agree") => insert(&mut known, at),
                        _ => {
                            insert(&mut known, at);
                            if Some(at) != killer {
                                insert(&mut obligation.unknown, at);
                            }
                        }
                    }
                }
                // The search order: the programs that witness the edit first, each group in
                // manifest order.
                let witnesses = indices(
                    &row["witnesses"]
                        .as_array()
                        .into_iter()
                        .flatten()
                        .filter_map(Value::as_str)
                        .map(str::to_owned)
                        .collect::<Vec<_>>(),
                );
                obligation.unasked = (0..cases.len())
                    .filter(|at| comparable[*at] && !known.contains(at))
                    .collect();
                obligation.unasked.sort_by_key(|at| !witnesses.contains(at));
                facts.obligations.push(obligation);
                if row["expect"] == Expect::Survive.as_str() {
                    // Every killer refutes the claim: the row is asked whole.
                    let at = facts.obligations.len() - 1;
                    facts.learn_all(at, ask)?;
                    let obligation = facts.obligations.pop().expect("just pushed");
                    for case in obligation.dischargers {
                        facts.keeps[case].push(Keep::Refutes("mutations", obligation.id.clone()));
                    }
                }
            }
        }
        if let Some(query) = query {
            facts.cells[1].matrix =
                inputs.pattern_list.map_or(0, |list| list.patterns.len()) * cases.len();
            let rows = query["rows"].as_array().map_or(&[][..], Vec::as_slice);
            facts.cells[1].searched = rows.len();
            for obligation in query["obligations"].as_array().into_iter().flatten() {
                let pattern = inputs.pattern_list.and_then(|list| {
                    list.patterns
                        .iter()
                        .position(|entry| obligation["id"] == entry.id.as_str())
                });
                let (true, Some(pattern)) = (lazy && obligation["status"] == "hit", pattern) else {
                    add(
                        &mut facts,
                        "patterns",
                        &obligation["id"],
                        crate::query::hit_cells(obligation),
                    );
                    continue;
                };
                // A hit pattern's walk: the pairs it asked (its claims, then the walk to its
                // first hit).
                let mut lazy = Obligation {
                    family: "patterns",
                    id: text(&obligation["id"]),
                    dischargers: Vec::new(),
                    unknown: Vec::new(),
                    unasked: Vec::new(),
                    source: Some(Source::Pattern(pattern)),
                    stopped: false,
                };
                let mut known = Vec::new();
                for row in rows.iter().filter(|row| row["pattern"] == obligation["id"]) {
                    let Some(at) = row["program"].as_str().and_then(index) else {
                        continue;
                    };
                    insert(&mut known, at);
                    match row["answer"].as_str() {
                        Some("hit") => insert(&mut lazy.dischargers, at),
                        Some("no") => {}
                        _ => insert(&mut lazy.unknown, at),
                    }
                }
                lazy.unasked = (0..cases.len()).filter(|at| !known.contains(at)).collect();
                facts.obligations.push(lazy);
                if obligation["expect"] == PatternExpect::No.as_str() {
                    let at = facts.obligations.len() - 1;
                    facts.learn_all(at, ask)?;
                    let obligation = facts.obligations.pop().expect("just pushed");
                    for case in obligation.dischargers {
                        facts.keeps[case].push(Keep::Refutes("patterns", obligation.id.clone()));
                    }
                }
            }
        }
        // The coverage families, each by its own name, which is also its prune family's.
        for family in PRUNE_FAMILIES
            .into_iter()
            .filter(|family| FAMILIES.contains(family))
        {
            let value = &coverage["families"][family];
            let binders = value["binders"].as_array().map_or(&[][..], Vec::as_slice);
            for item in value["items"].as_array().into_iter().flatten() {
                let before = facts.obligations.len();
                add(
                    &mut facts,
                    family,
                    &item["id"],
                    crate::coverage::cover_cells(family, item, binders),
                );
                if family == "flips"
                    && facts.obligations.len() > before
                    && flip_status(item) == DISTINGUISHED
                {
                    facts.obligations[before].stopped = true;
                }
            }
        }
        for family in FAMILIES {
            for item in coverage["families"][family]["items"]
                .as_array()
                .into_iter()
                .flatten()
            {
                add(
                    &mut facts,
                    "arguments",
                    &item["id"],
                    crate::coverage::argument_cells(item),
                );
            }
        }
        facts.families = PRUNE_FAMILIES
            .iter()
            .map(|name| Family {
                name,
                skipped: inputs
                    .skipped
                    .iter()
                    .find(|family| family.name == *name)
                    .and_then(|family| family.skipped.clone())
                    .or_else(|| coverage_skipped(coverage, name)),
            })
            .collect();
        Ok(facts)
    }

    /// Ask the cell of the obligation at `index` on the case at `case`, where it was not asked.
    fn learn(&mut self, index: usize, case: usize, ask: &mut dyn Ask) -> Result<(), Refusal> {
        let obligation = &mut self.obligations[index];
        let Some(place) = obligation.unasked.iter().position(|at| *at == case) else {
            return Ok(());
        };
        obligation.unasked.remove(place);
        let source = obligation
            .source
            .expect("a row with an unasked cell has a source");
        let (cell, cached) = ask.ask(source, case)?;
        let counted = match source {
            Source::Mutation(_) => &mut self.cells[0],
            Source::Pattern(_) => &mut self.cells[1],
        };
        counted.asked += 1;
        counted.from_cache += usize::from(cached);
        match cell {
            Cell::Discharges => insert(&mut obligation.dischargers, case),
            Cell::Unknown => insert(&mut obligation.unknown, case),
            Cell::Not => {}
        }
        ask.announce(&format!(
            "prune: {} `{}` on `{}`: {}{}",
            obligation.family,
            obligation.id,
            self.cases[case],
            match cell {
                Cell::Discharges => "discharges",
                Cell::Not => "does not discharge",
                Cell::Unknown => "unknown",
            },
            if cached { " (cached)" } else { "" }
        ));
        Ok(())
    }

    /// Ask every cell of the obligation at `index` not asked yet.
    fn learn_all(&mut self, index: usize, ask: &mut dyn Ask) -> Result<(), Refusal> {
        while let Some(&case) = self.obligations[index].unasked.first() {
            self.learn(index, case, ask)?;
        }
        Ok(())
    }

    /// Make the row of the obligation at `index` decide the case at `at` against the kept cases
    /// `kept` (module docs, "Lazy cells"): when no known decided discharger other than `at` is
    /// kept, ask its unasked cells over the kept cases other than `at`, in its order, until one
    /// discharges or none is left, then `at`'s own.
    fn settle(
        &mut self,
        index: usize,
        at: usize,
        kept: &[bool],
        ask: &mut dyn Ask,
    ) -> Result<(), Refusal> {
        let others = |obligation: &Obligation| {
            obligation
                .dischargers
                .iter()
                .any(|other| *other != at && kept[*other])
        };
        let obligation = &self.obligations[index];
        if obligation.unasked.is_empty() || others(obligation) {
            return Ok(());
        }
        let order = obligation
            .unasked
            .iter()
            .copied()
            .filter(|case| *case != at && kept[*case])
            .collect::<Vec<_>>();
        for case in order {
            self.learn(index, case, ask)?;
            if others(&self.obligations[index]) {
                return Ok(());
            }
        }
        self.learn(index, at, ask)
    }

    /// Whether the case at `at` has an undecided baseline: kink asked it of no mutant and no
    /// pattern, and covered nothing by it.
    fn undecided(&self, at: usize) -> bool {
        matches!(self.classes[at].as_str(), "timeout" | "unknown")
    }

    /// Why the case at `at` is kept against the kept cases `kept` (`at` itself among them); empty
    /// when it is not (module docs, "What is never prunable"), asking the cells the rules need.
    fn keeps(&mut self, at: usize, kept: &[bool], ask: &mut dyn Ask) -> Result<Vec<Keep>, Refusal> {
        let mut keeps = self.keeps[at].clone();
        let mut open = Vec::new();
        for index in 0..self.obligations.len() {
            self.settle(index, at, kept, ask)?;
            let obligation = &self.obligations[index];
            let others = obligation
                .dischargers
                .iter()
                .any(|other| *other != at && kept[*other]);
            if others {
                continue;
            }
            if obligation.dischargers.contains(&at) {
                keeps.push(Keep::Sole(index));
            } else if obligation.unknown.contains(&at) {
                keeps.push(Keep::Unknown(index));
            } else if self.undecided(at) {
                open.push(index);
            }
        }
        if !open.is_empty() {
            keeps.push(Keep::Undecided(self.classes[at].clone(), open));
        }
        Ok(keeps)
    }

    fn reference(&self, index: usize) -> Value {
        let obligation = &self.obligations[index];
        json!({"family": obligation.family, "id": obligation.id})
    }

    fn keep_value(&self, keep: &Keep) -> Value {
        match keep {
            Keep::Claimed(pattern) => json!({"reason": "claimed", "family": "patterns",
                                             "id": pattern}),
            Keep::Refutes(family, id) => json!({"reason": "refutes", "family": family, "id": id}),
            Keep::Sole(index) => {
                let mut value = self.reference(*index);
                value["reason"] = json!("sole-discharger");
                value
            }
            Keep::Unknown(index) => {
                let mut value = self.reference(*index);
                value["reason"] = json!("unknown");
                value
            }
            Keep::Undecided(class, open) => json!({
                "reason": "baseline-undecided",
                "class": class,
                "obligations": open.iter().map(|index| self.reference(*index)).collect::<Vec<_>>(),
            }),
        }
    }

    fn ids(&self, indices: impl IntoIterator<Item = usize>) -> Vec<String> {
        indices
            .into_iter()
            .map(|at| self.cases[at].clone())
            .collect()
    }

    /// The document of these facts, with the rows each case's removal moves in `locks` and
    /// each list-reading family's `list`, asking the cells its decisions need.
    #[allow(clippy::too_many_lines)]
    fn document(
        &mut self,
        locks: &[Lock],
        lists: &[Value; 2],
        ask: &mut dyn Ask,
    ) -> Result<Value, Refusal> {
        let all = vec![true; self.cases.len()];
        let alone = (0..self.cases.len())
            .map(|at| self.keeps(at, &all, ask))
            .collect::<Result<Vec<_>, _>>()?;
        // The greedy set (module docs): each case, latest first, against the cases still kept;
        // what kept a case is recorded when it was examined. A case some rule keeps against the
        // whole corpus is kept against every subset of it (module docs, "Lazy cells").
        let mut kept = all.clone();
        let mut kept_for = vec![Vec::new(); self.cases.len()];
        for at in (0..self.cases.len()).rev() {
            if !alone[at].is_empty() {
                continue;
            }
            let keeps = self.keeps(at, &kept, ask)?;
            if keeps.is_empty() {
                kept[at] = false;
            } else {
                kept_for[at] = keeps;
            }
        }
        let lock_rows = |at: usize| lock_rows(locks, &self.cases[at]);
        let redundant = (0..self.cases.len())
            .filter(|at| alone[*at].is_empty())
            .map(|at| {
                let discharged = self
                    .obligations
                    .iter()
                    .filter(|obligation| obligation.dischargers.contains(&at))
                    .map(|obligation| {
                        json!({
                            "family": obligation.family,
                            "id": obligation.id,
                            "others": self.ids(
                                obligation.dischargers.iter().copied().filter(|other| *other != at)
                            ),
                            "complete": obligation.complete(),
                        })
                    })
                    .collect::<Vec<_>>();
                let unknown = self
                    .obligations
                    .iter()
                    .filter(|obligation| obligation.unknown.contains(&at))
                    .map(|obligation| {
                        json!({
                            "family": obligation.family,
                            "id": obligation.id,
                            "dischargers": self.ids(obligation.dischargers.iter().copied()),
                            "complete": obligation.complete(),
                        })
                    })
                    .collect::<Vec<_>>();
                json!({
                    "case": self.cases[at],
                    "class": self.classes[at],
                    "obligations": discharged,
                    "unknown": unknown,
                    "unasked": self
                        .obligations
                        .iter()
                        .filter(|obligation| obligation.unasked.contains(&at))
                        .count(),
                    "removable": !kept[at],
                    "kept_for": kept_for[at]
                        .iter()
                        .map(|keep| self.keep_value(keep))
                        .collect::<Vec<_>>(),
                    "lock": lock_rows(at),
                })
            })
            .collect::<Vec<_>>();
        let kept_cases = (0..self.cases.len())
            .filter(|at| !alone[*at].is_empty())
            .map(|at| {
                let reasons = alone[at]
                    .iter()
                    .map(|keep| self.keep_value(keep))
                    .collect::<Vec<_>>();
                json!({"case": self.cases[at], "class": self.classes[at], "reasons": reasons})
            })
            .collect::<Vec<_>>();
        let removable = (0..self.cases.len())
            .filter(|at| !kept[*at])
            .collect::<Vec<_>>();
        let families = self
            .families
            .iter()
            .map(|family| {
                let of = self
                    .obligations
                    .iter()
                    .filter(|obligation| obligation.family == family.name)
                    .collect::<Vec<_>>();
                let mut value = match &family.skipped {
                    Some((reason, detail)) => json!({
                        "family": family.name,
                        "run": false,
                        "reason": reason,
                        "detail": detail,
                    }),
                    None => json!({
                        "family": family.name,
                        "run": true,
                        "obligations": of.len(),
                        "discharged": of.iter().filter(|o| !o.dischargers.is_empty()).count(),
                        "unanswered": of.iter().map(|o| o.unknown.len()).sum::<usize>(),
                        "complete": of.iter().all(|o| o.complete()),
                    }),
                };
                match family.name {
                    "mutations" => value["list"] = lists[0].clone(),
                    "patterns" => value["list"] = lists[1].clone(),
                    _ => {}
                }
                value
            })
            .collect::<Vec<_>>();
        let undecided = (0..self.cases.len())
            .filter(|at| self.undecided(*at))
            .map(|at| json!({"case": self.cases[at], "class": self.classes[at]}))
            .collect::<Vec<_>>();
        let mut document = header();
        document["mode"] = json!(if self.lazy { LAZY } else { FULL });
        document["cases"] = json!(self.cases.len());
        document["families"] = json!(families);
        document["redundant"] = json!(redundant);
        document["removable"] = json!({
            "order": REVERSE_MANIFEST_ORDER,
            "cases": self.ids(removable.iter().copied()),
            "lock": removable
                .iter()
                .filter_map(|at| {
                    let rows = lock_rows(*at);
                    (!rows.is_null()).then(|| json!({"case": self.cases[*at], "rows": rows}))
                })
                .collect::<Vec<_>>(),
        });
        document["kept"] = json!(kept_cases);
        document["unanswered"] = json!({
            "cells": self.obligations.iter().map(|o| o.unknown.len()).sum::<usize>(),
            "complete": self.obligations.iter().all(Obligation::complete),
            "undecided_cases": undecided,
        });
        document["lock"] = locks.first().map_or(Value::Null, |lock| {
            json!({
                "path": lock.path.display().to_string(),
                "read": lock.text.is_some(),
                "sections": locks
                    .iter()
                    .filter(|lock| lock.records())
                    .map(|lock| lock.kind.document())
                    .collect::<Vec<_>>(),
            })
        });
        document["limits"] = json!(
            LIMITS
                .iter()
                .chain(self.lazy.then_some(&LAZY_LIMIT))
                .map(|(limit, detail)| json!({"limit": limit, "detail": detail}))
                .collect::<Vec<_>>()
        );
        Ok(document)
    }
}

/// A flip item's status as its reading takes it: an argued flip's `unargued_status`.
fn flip_status(item: &Value) -> &str {
    if item["status"] == ARGUED {
        item["unargued_status"].as_str().unwrap_or_default()
    } else {
        item["status"].as_str().unwrap_or_default()
    }
}

/// Why the coverage document computed no family `name` (a coverage family, or `arguments`,
/// which every computed document reads); `None` for a family it computed or that is not one of
/// its own.
fn coverage_skipped(coverage: &Value, name: &str) -> Option<(&'static str, String)> {
    if !FAMILIES.contains(&name) {
        return None;
    }
    let family = &coverage["families"][name];
    let detail = family["reason"].as_str().map(str::to_owned);
    if family.is_null() {
        Some((
            "not-computed",
            "the coverage document computes no such family at its depth".to_owned(),
        ))
    } else if family["run"] == false || !family["items"].is_array() {
        Some((
            "not-computed",
            detail.unwrap_or_else(|| "the coverage family did not run".to_owned()),
        ))
    } else {
        None
    }
}

/// The rows of the corpus record that name `case`, by section: `run` and `coverage` rows whose
/// killer it is, `query` rows whose witness it is, `compare` rows of its program (`{implementation,
/// view}`); null when none does.
fn lock_rows(locks: &[Lock], case: &str) -> Value {
    let mut rows = serde_json::Map::new();
    for lock in locks {
        let named = lock
            .rows
            .iter()
            .filter_map(|row| match lock.kind {
                LockKind::Run | LockKind::Coverage => {
                    (row.killer.as_deref() == Some(case)).then(|| json!(row.id))
                }
                LockKind::Query => (row.witness.as_deref() == Some(case)).then(|| json!(row.id)),
                LockKind::Compare => {
                    let parts: Vec<String> = serde_json::from_str(&row.id).ok()?;
                    (parts.get(1).map(String::as_str) == Some(case))
                        .then(|| json!({"implementation": parts[0], "view": parts.get(2)}))
                }
            })
            .collect::<Vec<_>>();
        if !named.is_empty() {
            rows.insert(lock.kind.document().to_owned(), json!(named));
        }
    }
    if rows.is_empty() {
        Value::Null
    } else {
        Value::Object(rows)
    }
}

/// A row's id as text.
fn text(id: &Value) -> String {
    id.as_str().map_or_else(|| id.to_string(), str::to_owned)
}

/// The `--output text` rendering of a prune document: what is removable together; a note for
/// each list that is not the corpus's own; for a lazy report, the cells its families held and
/// asked; what each removal moves in the corpus record; each case redundant alone with the
/// other dischargers of what it discharges (of the cases asked, where its row is not complete);
/// each kept case with its reasons; the families and the unanswered cells.
///
/// # Errors
///
/// When the document is no prune document.
pub fn text_rendering(document: &Value) -> Result<String, String> {
    if document["schema"] != PRUNE_SCHEMA {
        return Err("the document has no text rendering".to_owned());
    }
    let mut text = String::new();
    if !document["refused"].is_null() {
        text.push_str(&format!(
            "prune refused: {}: {}\n",
            document["refused"]["family"].as_str().unwrap_or("?"),
            document["refused"]["detail"].as_str().unwrap_or("")
        ));
        return Ok(text);
    }
    if document["spec"]["outcome"] == "refused" {
        text.push_str(&format!(
            "prune refused: the specification is refused at stage {}: {}\n",
            document["spec"]["stage"].as_str().unwrap_or("?"),
            document["spec"]["detail"].as_str().unwrap_or("")
        ));
        return Ok(text);
    }
    let list = |value: &Value| {
        let ids = strings(value);
        if ids.is_empty() {
            "none".to_owned()
        } else {
            ids.join(", ")
        }
    };
    let removable = &document["removable"];
    text.push_str(&format!(
        "{} cases: {} redundant alone, {} removable together (in {} order): {}\n",
        document["cases"],
        document["redundant"].as_array().map_or(0, Vec::len),
        removable["cases"].as_array().map_or(0, Vec::len),
        removable["order"].as_str().unwrap_or("?"),
        list(&removable["cases"]),
    ));
    for family in document["families"].as_array().into_iter().flatten() {
        if family["list"]["corpus_own"] == false {
            text.push_str(&format!(
                "note: the {} family read {}, not the corpus's own list: the report holds for \
                 that list, not for the corpus\n",
                family["family"].as_str().unwrap_or("?"),
                family["list"]["path"].as_str().map_or_else(
                    || "the patterns the manifest declares".to_owned(),
                    |path| { format!("`{path}`") }
                ),
            ));
        }
    }
    if document["mode"] == LAZY {
        let cells = &document["accounting"]["cells"];
        let parts = ["mutations", "patterns"]
            .into_iter()
            .filter(|family| cells[family].is_object())
            .map(|family| {
                format!(
                    "{family} {} held by the search and {} asked after it, of {}",
                    cells[family]["searched"], cells[family]["asked"], cells[family]["matrix"]
                )
            })
            .collect::<Vec<_>>();
        if !parts.is_empty() {
            text.push_str(&format!(
                "cells (lazy, as each decision needs them; --full asks every one): {}\n",
                parts.join("; ")
            ));
        }
    }
    for entry in removable["lock"].as_array().into_iter().flatten() {
        for (section, rows) in entry["rows"].as_object().into_iter().flatten() {
            let rows = rows
                .as_array()
                .into_iter()
                .flatten()
                .map(|row| {
                    row.as_str().map_or_else(
                        || {
                            format!(
                                "{} {}",
                                row["implementation"].as_str().unwrap_or("?"),
                                row["view"].as_str().unwrap_or("?")
                            )
                        },
                        str::to_owned,
                    )
                })
                .collect::<Vec<_>>();
            text.push_str(&format!(
                "  removing {} moves the record's [{section}] rows {}: --locked fails until they \
                 are recorded again\n",
                entry["case"].as_str().unwrap_or("?"),
                rows.join(", "),
            ));
        }
    }
    let reference = |value: &Value| {
        format!(
            "{} {}",
            value["family"].as_str().unwrap_or("?"),
            value["id"].as_str().unwrap_or("?")
        )
    };
    text.push_str("redundant alone:\n");
    for entry in document["redundant"].as_array().into_iter().flatten() {
        let mut parts = entry["obligations"]
            .as_array()
            .into_iter()
            .flatten()
            .map(|o| {
                format!(
                    "{} (also {}{})",
                    reference(o),
                    list(&o["others"]),
                    if o["complete"] == false {
                        ", of the cases asked"
                    } else {
                        ""
                    }
                )
            })
            .collect::<Vec<_>>();
        if parts.is_empty() {
            parts.push("discharges nothing".to_owned());
        }
        let kept = entry["kept_for"]
            .as_array()
            .into_iter()
            .flatten()
            .map(|keep| reason_text(keep, &reference))
            .collect::<Vec<_>>();
        text.push_str(&format!(
            "  {}{}: {}\n",
            entry["case"].as_str().unwrap_or("?"),
            if entry["removable"] == true {
                String::new()
            } else {
                format!(" (kept in the removable set: {})", kept.join("; "))
            },
            parts.join("; ")
        ));
    }
    text.push_str("kept:\n");
    for entry in document["kept"].as_array().into_iter().flatten() {
        let reasons = entry["reasons"]
            .as_array()
            .into_iter()
            .flatten()
            .map(|keep| reason_text(keep, &reference))
            .collect::<Vec<_>>();
        text.push_str(&format!(
            "  {}: {}\n",
            entry["case"].as_str().unwrap_or("?"),
            reasons.join("; ")
        ));
    }
    text.push_str("families:\n");
    for family in document["families"].as_array().into_iter().flatten() {
        if family["run"] == true {
            text.push_str(&format!(
                "  {}: {} obligations, {} discharged, {} unanswered cells{}\n",
                family["family"].as_str().unwrap_or("?"),
                family["obligations"],
                family["discharged"],
                family["unanswered"],
                if family["complete"] == false {
                    " (not every cell asked)"
                } else {
                    ""
                },
            ));
        } else {
            text.push_str(&format!(
                "  {}: skipped ({})\n",
                family["family"].as_str().unwrap_or("?"),
                family["detail"].as_str().unwrap_or("?"),
            ));
        }
    }
    let unanswered = &document["unanswered"];
    text.push_str(&format!(
        "unanswered cells: {}; cases with an undecided baseline: {}{}\n",
        unanswered["cells"],
        list(&json!(
            unanswered["undecided_cases"]
                .as_array()
                .into_iter()
                .flatten()
                .map(|case| case["case"].clone())
                .collect::<Vec<_>>()
        )),
        if unanswered["complete"] == false {
            "; not every cell was asked"
        } else {
            ""
        },
    ));
    Ok(text)
}

/// A kept case's reason as the text rendering states it.
fn reason_text(keep: &Value, reference: &dyn Fn(&Value) -> String) -> String {
    match keep["reason"].as_str() {
        Some("claimed") => format!(
            "claimed by the pattern {}",
            keep["id"].as_str().unwrap_or("?")
        ),
        Some("refutes") => format!("its cell refutes {}", reference(keep)),
        Some("sole-discharger") => format!("the only discharger of {}", reference(keep)),
        Some("unknown") => format!(
            "its cell is unknown on {}, which no other case discharges",
            reference(keep)
        ),
        Some("baseline-undecided") => format!(
            "its baseline is {} and {} obligations have no discharger",
            keep["class"].as_str().unwrap_or("?"),
            keep["obligations"].as_array().map_or(0, Vec::len)
        ),
        _ => "?".to_owned(),
    }
}

fn strings(value: &Value) -> Vec<String> {
    value
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(Value::as_str)
        .map(str::to_owned)
        .collect()
}
