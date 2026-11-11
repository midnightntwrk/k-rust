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
//! the flips where the front end derives them), `run --full` and `query --full` in process, each
//! through its own command's code and caches ([`crate::coverage::coverage_front`],
//! [`crate::search::run_front`], [`crate::query::query_spelled`]), so it is a function of the
//! definition, the corpus and the counted budgets, as their verdicts are. The run stores no report
//! ([`crate::search::run_stored`]), so `report` and `fuzz --kill` keep reading the last `run`'s.
//! A family whose input is absent is skipped, and the document says so: no mutation list (a front
//! end's layout without one), or no patterns (none named and none declared).
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
    coverage::{CoverageOptions, FAMILIES},
    lock::{Lock, LockKind},
    manifest::FlowManifest,
    mutation::MutationList,
    pattern::PatternList,
    query::QueryOptions,
    search::{RunMode, RunOptions},
};
use kink_campaign::ScheduleMode;
use kink_native::execution::SolverProfile;
use serde_json::{Value, json};
use std::path::{Path, PathBuf};

/// The `schema` of the prune document.
pub const PRUNE_SCHEMA: &str = "kink-flow-prune";
/// The version of the prune document: 1, the first.
pub const PRUNE_VERSION: u64 = 1;

/// The order the removable set is built in (`removable.order`, module docs).
pub const REVERSE_MANIFEST_ORDER: &str = "reverse-manifest";

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

/// Options of the `prune` command.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct PruneOptions {
    /// The cache directory; default `<directory of FLOW.toml>/.kink-flow`.
    pub cache: Option<PathBuf>,
    /// `--lock FILE`: the corpus record, read for the rows a removal moves, never written.
    pub lock: Option<PathBuf>,
    /// `--compile-workers N`, as `run`'s ([`RunOptions::compile_workers`]).
    pub compile_workers: Option<usize>,
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

/// One obligation, its cells by case index.
struct Obligation {
    family: &'static str,
    id: String,
    dischargers: Vec<usize>,
    unknown: Vec<usize>,
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

/// `kink-flow prune`: the prune document and the exit status, [`EXIT_YES`] when the report is
/// computed (unknowns make it conservative, never unanswered: every set it states holds), and
/// [`EXIT_UNASKED`] when a lock does not decode, a list does not decode, or a family's own command
/// could not ask its question (its exit status would be 2: a refused specification, program,
/// mutation or pattern, a corpus or infrastructure error), whose document the refusal names.
/// No status is 1: the report refutes nothing.
#[must_use]
pub fn command(
    manifest: &FlowManifest,
    mutations: Option<&Path>,
    patterns: Option<&Path>,
    options: &PruneOptions,
    front: &FrontEnd<'_>,
) -> (Value, u8) {
    let announce = |line: &str| {
        if let Some(progress) = front.progress {
            progress(line);
        }
    };
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
    let coverage_lock = locks.iter().find(|lock| lock.kind == LockKind::Coverage);
    announce("prune: coverage of the corpus");
    let coverage_options = CoverageOptions {
        cache: options.cache.clone(),
        ..CoverageOptions::default()
    };
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
    let mut run = None;
    if let Some(list) = &list {
        announce("prune: run --full of the mutation list");
        let run_options = RunOptions {
            cache: options.cache.clone(),
            compile_workers: options.compile_workers,
            schedule: ScheduleMode::Full,
            ..RunOptions::default()
        };
        let (document, ok) =
            crate::search::run_stored(manifest, list, &run_options, RunMode::Search, front, false);
        if completed(crate::cli::run_status(&document), ok) == EXIT_UNASKED {
            return refused(
                "mutations",
                Some(&document),
                &format!("`{} --full` shows why", front.spelling.command(Verb::Run)),
            );
        }
        run = Some(document);
    }
    let mut query = None;
    let mut claimed = Vec::new();
    if let Some(list) = &pattern_list {
        announce("prune: query --full of the patterns");
        let query_options = QueryOptions {
            cache: options.cache.clone(),
            full: true,
            no_explain: true,
            ..QueryOptions::default()
        };
        let (document, ok) = crate::query::query_spelled(
            manifest,
            list,
            &query_options,
            &front.spelling.verb(Verb::Query),
        );
        if completed(crate::cli::query_status(&document), ok) == EXIT_UNASKED {
            return refused(
                "patterns",
                Some(&document),
                &format!("`{} --full` shows why", front.spelling.command(Verb::Query)),
            );
        }
        query = Some(document);
        claimed = claims(list);
    }
    let facts = Facts::read(
        manifest,
        &coverage,
        run.as_ref(),
        query.as_ref(),
        claimed,
        &skipped,
    );
    let mut document = facts.document(&locks);
    document["spec"] = coverage["spec"].clone();
    document["accounting"] = json!({
        "mutations": run.as_ref().map(|run| json!({
            "outcome_cache": run["outcome_cache"],
            "baseline_runs": run["baseline_runs"],
        })),
        "patterns": query.as_ref().map(|query| query["pattern_cache"].clone()),
        "coverage": {"baseline_runs": coverage["baseline_runs"]},
    });
    (document, EXIT_YES)
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
}

impl Facts {
    fn read(
        manifest: &FlowManifest,
        coverage: &Value,
        run: Option<&Value>,
        query: Option<&Value>,
        claims: Vec<(String, String)>,
        skipped: &[Family],
    ) -> Self {
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
        let mut obligations = Vec::new();
        let mut add = |family: &'static str, id: &Value, reading: Reading| match reading {
            Reading::None => {}
            Reading::Refuted(by) => {
                for at in indices(&by) {
                    keeps[at].push(Keep::Refutes(family, text(id)));
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
                obligations.push(Obligation {
                    family,
                    id: text(id),
                    dischargers,
                    unknown,
                });
            }
        };
        if let Some(run) = run {
            for row in run["mutations"].as_array().into_iter().flatten() {
                add("mutations", &row["id"], crate::report::kill_cells(row));
            }
        }
        if let Some(query) = query {
            for obligation in query["obligations"].as_array().into_iter().flatten() {
                add(
                    "patterns",
                    &obligation["id"],
                    crate::query::hit_cells(obligation),
                );
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
                add(
                    family,
                    &item["id"],
                    crate::coverage::cover_cells(family, item, binders),
                );
            }
        }
        for family in FAMILIES {
            for item in coverage["families"][family]["items"]
                .as_array()
                .into_iter()
                .flatten()
            {
                add(
                    "arguments",
                    &item["id"],
                    crate::coverage::argument_cells(item),
                );
            }
        }
        let families = PRUNE_FAMILIES
            .iter()
            .map(|name| Family {
                name,
                skipped: skipped
                    .iter()
                    .find(|family| family.name == *name)
                    .and_then(|family| family.skipped.clone())
                    .or_else(|| coverage_skipped(coverage, name)),
            })
            .collect();
        Self {
            cases,
            classes,
            obligations,
            keeps,
            families,
        }
    }

    /// Whether the case at `at` has an undecided baseline: kink asked it of no mutant and no
    /// pattern, and covered nothing by it.
    fn undecided(&self, at: usize) -> bool {
        matches!(self.classes[at].as_str(), "timeout" | "unknown")
    }

    /// Why the case at `at` is kept against the kept cases `kept` (`at` itself among them); empty
    /// when it is not (module docs, "What is never prunable").
    fn keeps(&self, at: usize, kept: &[bool]) -> Vec<Keep> {
        let mut keeps = self.keeps[at].clone();
        let mut open = Vec::new();
        for (index, obligation) in self.obligations.iter().enumerate() {
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
        keeps
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

    /// The document of these facts, with the rows each case's removal moves in `locks`.
    fn document(&self, locks: &[Lock]) -> Value {
        let all = vec![true; self.cases.len()];
        let alone = (0..self.cases.len())
            .map(|at| self.keeps(at, &all))
            .collect::<Vec<_>>();
        // The greedy set (module docs): each case, latest first, against the cases still kept;
        // what kept a case is recorded when it was examined.
        let mut kept = all.clone();
        let mut kept_for = vec![Vec::new(); self.cases.len()];
        for at in (0..self.cases.len()).rev() {
            let keeps = self.keeps(at, &kept);
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
                        })
                    })
                    .collect::<Vec<_>>();
                json!({
                    "case": self.cases[at],
                    "class": self.classes[at],
                    "obligations": discharged,
                    "unknown": unknown,
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
                match &family.skipped {
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
                    }),
                }
            })
            .collect::<Vec<_>>();
        let undecided = (0..self.cases.len())
            .filter(|at| self.undecided(*at))
            .map(|at| json!({"case": self.cases[at], "class": self.classes[at]}))
            .collect::<Vec<_>>();
        let mut document = header();
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
                .map(|(limit, detail)| json!({"limit": limit, "detail": detail}))
                .collect::<Vec<_>>()
        );
        document
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

/// The `--output text` rendering of a prune document: what is removable together and what each
/// removal moves in the corpus record, each case redundant alone with the other dischargers of
/// what it discharges, each kept case with its reasons, the families and the unanswered cells.
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
            .map(|o| format!("{} (also {})", reference(o), list(&o["others"])))
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
                "  {}: {} obligations, {} discharged, {} unanswered cells\n",
                family["family"].as_str().unwrap_or("?"),
                family["obligations"],
                family["discharged"],
                family["unanswered"],
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
        "unanswered cells: {}; cases with an undecided baseline: {}\n",
        unanswered["cells"],
        list(&json!(
            unanswered["undecided_cases"]
                .as_array()
                .into_iter()
                .flatten()
                .map(|case| case["case"].clone())
                .collect::<Vec<_>>()
        )),
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
