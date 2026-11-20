//! `kink-flow admit FLOW.toml FILE... [--found-by TEXT] [--reason TEXT] [--cache DIR]`: what the
//! flow says of each candidate case found elsewhere (an implementation-side fuzzer, a person), and
//! what it would add to the corpus. It writes nothing (PJ-22).
//!
//! # Candidates
//!
//! Each FILE is a case document, of one case or of named cases, read by the flow's own case
//! reader inside its case root ([`FlowManifest::document_cases`]): a case document and the files
//! its inputs name are relative to the root and stay inside it, so a FILE outside the root is
//! refused (it need not match a `cases` pattern). Each case of the document is one candidate,
//! whose id is the id a `cases` pattern matching the document would give it. A FILE the reader
//! refuses is not a case of the flow: its row is `refused` at stage `case-document`, and the
//! command exits 2. A document given twice is read once.
//!
//! # Outcomes
//!
//! Each candidate is admitted by the flow's own admission and its baseline run, as `coverage`
//! admits and runs a program ([`crate::coverage::coverage_front`]), and its row says:
//!
//! - `refused`: today's admission refuses it (`inputs`/`parse`, `inputs`/`input-value`, ...),
//!   with that stage, reason and detail. This is an answer about the candidate, and decides no
//!   exit status;
//! - `accepted` or `rejected`: by compare's acceptance rule ([`crate::compare`], PJ-02) over its
//!   baseline's ends. An end reached at the corpus's stop, or of a declared `finished` class, is
//!   accepted; one of a declared `refused` class, or `none`, is rejected, where the definition
//!   declares a `finished` end ([`outcome`]). A rejected candidate's `stage` is `end`, except a
//!   candidate that states it is rejected before it runs (a K case document, whose texts are
//!   parsed): it is `rejected` at the stage it states where admission rejects it there, and
//!   `accepted`, its statement unmet, where admission admits it;
//! - `unknown`: anything else, with the reason (an end with no declared class, which every end of
//!   kink-flow's own K front end is without `[stop]`; ends of both kinds; a baseline that is not
//!   `comparable`).
//!
//! # Newly discharged obligations
//!
//! An obligation is one of the corpus's existential obligations, as `prune` reads them
//! ([`crate::prune`]), among those a baseline run decides: the tier-1 coverage families, the
//! argued items' evidence (`arguments`) and the declared patterns (`patterns`). Kills of a
//! mutation list and condition flips need mutant runs, so they are not computed, and the document
//! says so. A candidate newly discharges an obligation when its decided cell discharges it and no
//! case of the corpus does. The corpus is the flow's programs without the cases of the
//! candidates' own documents, and each candidate is judged against the corpus alone, so the
//! answer does not depend on the other candidates or their order. A pair obligation (a
//! unique-cause requirement) is newly discharged when a pair over the corpus and the candidate
//! discharges it and no pair over the corpus does. Corpus cases whose cell is unknown, a case of
//! an undecided baseline among them, are named beside the entry (`corpus_unknown`), since they
//! may discharge it too.
//!
//! # Writing nothing
//!
//! Every manifest the command runs is an overlay held in memory, and every run uses a scratch
//! cache directory, removed on every path. The scratch is seeded with a symbolic link to each file
//! of the flow's cache ([`Scratch::mirror`]), so stored records are read and not recomputed. A
//! record a run writes is published by rename in the scratch, which replaces the link and never
//! its target. Nothing under the flow's directory, the corpus root or `--cache` changes, so no
//! later command's document does either.

use crate::{
    RejectedStage,
    cli::{EXIT_NO, EXIT_UNANSWERED, EXIT_UNASKED, EXIT_YES, FrontEnd, exit_join},
    compare::{Acceptance, row_acceptance},
    coverage::{CoverageOptions, Tier},
    manifest::{FlowManifest, Program, Provenance},
    pattern::{PatternExpect, PatternList},
    prune::{Cells, PairCells, Reading},
    query::QueryOptions,
    results::{ResultClass, cache_directory},
};
use serde_json::{Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
};
use toml::Table;

/// The document's `schema`.
pub const ADMIT_SCHEMA: &str = "kink-flow-admit";
/// The document's `version`. v2 (PJ-36): a candidate may state that it is rejected before it
/// runs (a K case document), so `rejected` may have the stage `parse` or `input` (with the
/// refusal's `reason` and `detail`, and no `ends`) and `accepted` may be an unmet statement (its
/// `expectation` unmet, exit 1); both rows carry `provenance` and `fragment`.
pub const ADMIT_VERSION: u64 = 2;

/// The coverage families a baseline run decides, in the document's order (`flips`, tier 2, is
/// not among them).
const TIER_ONE: [&str; 5] = [
    "rules",
    "requirements",
    "syntax",
    "rule_windows",
    "syntax_paths",
];

/// Why the kills of a mutation list are not computed.
const MUTATIONS_NOT_COMPUTED: &str = "a kill needs a mutant run, and admit runs each candidate's \
     baseline only and names no mutation list: run the flow's `run` once the case is added";
/// Why the condition flips are not computed.
const FLIPS_NOT_COMPUTED: &str = "a flip is discharged by a mutant run, and admit runs each \
     candidate's baseline only: run the flow's `coverage` (tier 2) once the case is added";

/// Options of the `admit` command.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct AdmitOptions {
    /// The candidates: case documents, in the order the command line gives them.
    pub candidates: Vec<PathBuf>,
    /// `--found-by` and `--reason`: the members each printed fragment's `provenance` takes in
    /// place of the candidate's own.
    pub provenance: Provenance,
    /// The cache directory whose records are read (never written); default
    /// `<directory of FLOW.toml>/.kink-flow`.
    pub cache: Option<PathBuf>,
}

/// A scratch cache directory, removed when dropped.
struct Scratch(PathBuf);

impl Scratch {
    fn new() -> std::io::Result<Self> {
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_or(0, |d| d.as_nanos());
        let path =
            std::env::temp_dir().join(format!("kink-flow-admit-{}-{nanos}", std::process::id()));
        fs::create_dir_all(&path)?;
        Ok(Self(path))
    }

    /// Seed the scratch with a symbolic link to each regular file under `cache` (the flow's
    /// cache), at the same relative path, in directories of the scratch's own. A store publishes
    /// a record by renaming a file of its directory over the path, which replaces the link, so no
    /// write reaches `cache`. A cache that does not exist seeds nothing.
    fn mirror(&self, cache: &Path) -> std::io::Result<()> {
        let mut pending = vec![PathBuf::new()];
        while let Some(relative) = pending.pop() {
            let Ok(entries) = fs::read_dir(cache.join(&relative)) else {
                continue;
            };
            fs::create_dir_all(self.0.join(&relative))?;
            for entry in entries {
                let entry = entry?;
                let kind = entry.file_type()?;
                let path = relative.join(entry.file_name());
                if kind.is_dir() {
                    pending.push(path);
                } else if kind.is_file() {
                    link(&fs::canonicalize(entry.path())?, &self.0.join(path))?;
                }
            }
        }
        Ok(())
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[cfg(unix)]
fn link(target: &Path, at: &Path) -> std::io::Result<()> {
    std::os::unix::fs::symlink(target, at)
}

#[cfg(not(unix))]
fn link(target: &Path, at: &Path) -> std::io::Result<()> {
    fs::copy(target, at).map(|_| ())
}

/// One candidate case read from a FILE.
struct Candidate {
    /// The FILE as the command line gives it.
    file: String,
    program: Program,
    /// The case as a document of one case states it.
    table: Table,
}

/// A row of a FILE that is not a case of the flow.
fn unread_row(file: &str, detail: String) -> Value {
    json!({
        "file": file,
        "id": null,
        "outcome": "refused",
        "stage": "case-document",
        "reason": "case-document",
        "detail": detail,
    })
}

/// The `refused` document of a command that could not ask its question at `stage`.
fn refused(stage: &str, detail: &str, spec: Option<&Value>, candidates: Vec<Value>) -> Value {
    json!({
        "schema": ADMIT_SCHEMA,
        "version": ADMIT_VERSION,
        "k_rust_revision": crate::k_rust_revision(),
        "spec": spec.cloned().unwrap_or(Value::Null),
        "refusal": {"stage": stage, "detail": detail},
        "candidates": candidates,
    })
}

/// `kink-flow admit`: the admit document and the exit status (module docs).
#[must_use]
pub fn command(
    manifest: &FlowManifest,
    options: &AdmitOptions,
    front: &FrontEnd<'_>,
) -> (Value, u8) {
    let mut status = EXIT_YES;
    let mut unread = BTreeMap::new();
    let mut candidates = Vec::new();
    let mut documents = BTreeSet::new();
    for (index, path) in options.candidates.iter().enumerate() {
        let file = path.display().to_string();
        match manifest.document_cases(path) {
            Err(error) => {
                status = EXIT_UNASKED;
                unread.insert(index, unread_row(&file, error.to_string()));
            }
            Ok(cases) => {
                let document = cases
                    .first()
                    .and_then(|(program, _)| program.case.clone())
                    .unwrap_or_default();
                if !documents.insert(document) {
                    continue;
                }
                for (program, table) in cases {
                    candidates.push((
                        index,
                        Candidate {
                            file: file.clone(),
                            program,
                            table,
                        },
                    ));
                }
            }
        }
    }
    let corpus: Vec<Program> = manifest
        .programs
        .iter()
        .filter(|program| {
            program
                .case
                .as_ref()
                .is_none_or(|case| !documents.contains(case))
        })
        .cloned()
        .collect();
    // A candidate whose id a listed program of the corpus gives cannot be told from it.
    let corpus_ids: BTreeSet<&str> = corpus.iter().map(|p| p.id.as_str()).collect();
    candidates.retain(|(index, candidate)| {
        if corpus_ids.contains(candidate.program.id.as_str()) {
            status = EXIT_UNASKED;
            unread.insert(
                *index,
                unread_row(
                    &candidate.file,
                    format!(
                        "a program of the corpus has the id `{}`, which the candidate would have",
                        candidate.program.id
                    ),
                ),
            );
            false
        } else {
            true
        }
    });
    let ordered = |rows: Vec<(usize, Value)>, unread: &BTreeMap<usize, Value>| {
        let mut all: Vec<(usize, Value)> = unread
            .iter()
            .map(|(index, row)| (*index, row.clone()))
            .chain(rows)
            .collect();
        all.sort_by_key(|(index, _)| *index);
        all.into_iter().map(|(_, row)| row).collect::<Vec<_>>()
    };
    if candidates.is_empty() {
        let document = refused(
            "case-document",
            "no FILE is a case document of the flow",
            None,
            ordered(Vec::new(), &unread),
        );
        return (document, EXIT_UNASKED);
    }
    let scratch = match Scratch::new().and_then(|scratch| {
        scratch
            .mirror(&cache_directory(manifest, options.cache.as_deref()))
            .map(|()| scratch)
    }) {
        Ok(scratch) => scratch,
        Err(error) => {
            let detail = format!("no scratch cache for the candidates' runs: {error}");
            return (
                refused("cache", &detail, None, ordered(Vec::new(), &unread)),
                EXIT_UNASKED,
            );
        }
    };
    let cache = Some(scratch.0.clone());

    // One tier-1 coverage of the corpus followed by every candidate.
    let mut overlay = manifest.clone();
    overlay.programs = corpus.clone();
    overlay
        .programs
        .extend(candidates.iter().map(|(_, c)| c.program.clone()));
    let (coverage, _) = crate::coverage::coverage_front(
        &overlay,
        &CoverageOptions {
            cache: cache.clone(),
            tier: Tier::One,
            ..CoverageOptions::default()
        },
        front,
        None,
    );
    let mut coverage = front.annotated(coverage);
    crate::coverage::derive(&mut coverage, front.spelling);
    if coverage["spec"]["outcome"] == "refused" {
        let detail = coverage["spec"]["detail"]
            .as_str()
            .unwrap_or_default()
            .to_owned();
        return (
            refused(
                "specification",
                &detail,
                Some(&coverage["spec"]),
                ordered(Vec::new(), &unread),
            ),
            EXIT_UNASKED,
        );
    }
    let corpus_set: BTreeSet<String> = corpus.iter().map(|p| p.id.clone()).collect();
    let rows: BTreeMap<String, Value> = coverage["programs"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|row| row["id"].as_str().map(|id| (id.to_owned(), row.clone())))
        .collect();
    let admitted: Vec<&Candidate> = candidates
        .iter()
        .map(|(_, candidate)| candidate)
        .filter(|candidate| {
            rows.get(&candidate.program.id).is_some_and(|row| {
                row["class"] != ResultClass::Refused.as_str()
                    && !ResultClass::states_rejection(&row["class"])
            })
        })
        .collect();
    let mut newly = coverage_newly(&coverage, &corpus_set);
    let mut families = coverage_families(&coverage);
    match pattern_newly(
        manifest,
        front,
        &corpus,
        &admitted,
        cache.as_deref(),
        &corpus_set,
    ) {
        Ok((entries, family)) => {
            for (id, list) in entries {
                newly.entry(id).or_default().extend(list);
            }
            families.insert("patterns".into(), family);
        }
        Err((stage, detail)) => {
            return (
                refused(
                    stage,
                    &detail,
                    Some(&coverage["spec"]),
                    ordered(Vec::new(), &unread),
                ),
                EXIT_UNASKED,
            );
        }
    }
    // A corpus case whose baseline is undecided holds no record, so each of its cells is
    // unknown (`prune`, "What is never prunable"): it may discharge what a candidate does.
    let undecided: Vec<String> = corpus
        .iter()
        .filter(|program| {
            rows.get(&program.id).is_some_and(|row| {
                row["class"] == ResultClass::Timeout.as_str()
                    || row["class"] == ResultClass::Unknown.as_str()
            })
        })
        .map(|program| program.id.clone())
        .collect();
    // Whether the definition declares a `finished` end: the front end says so (`compare`'s
    // vocabulary), or a run shows one.
    let declares_finished = front
        .implementations
        .is_some_and(crate::compare::Vocabulary::declares_finished_end)
        || rows.values().any(|row| {
            row["ends"]
                .as_array()
                .into_iter()
                .flatten()
                .any(|end| end["declared"] == "finished")
        });
    let mut out = Vec::new();
    for (index, candidate) in &candidates {
        let row = rows
            .get(&candidate.program.id)
            .cloned()
            .unwrap_or(Value::Null);
        let (mut value, row_status) = candidate_row(candidate, &row, options, declares_finished);
        if value["outcome"] != "refused" {
            let mut entries = newly.remove(&candidate.program.id).unwrap_or_default();
            for entry in &mut entries {
                with_undecided(entry, &undecided);
            }
            value["newly_discharged"] = Value::Array(entries);
        }
        status = exit_join(status, row_status);
        out.push((*index, value));
    }
    let cached = coverage["programs"]
        .as_array()
        .into_iter()
        .flatten()
        .filter(|row| {
            row["id"].as_str().is_some_and(|id| corpus_set.contains(id)) && row["cached"] == true
        })
        .count();
    let document = json!({
        "schema": ADMIT_SCHEMA,
        "version": ADMIT_VERSION,
        "k_rust_revision": crate::k_rust_revision(),
        "spec": coverage["spec"],
        "result_cache": coverage["result_cache"],
        "corpus": {"programs": corpus.len(), "cached": cached},
        "families": families,
        "candidates": ordered(out, &unread),
    });
    (document, status)
}

/// `entry`'s `corpus_unknown` with the corpus cases of an undecided baseline, `undecided`.
fn with_undecided(entry: &mut Value, undecided: &[String]) {
    if undecided.is_empty() {
        return;
    }
    let mut unknown: Vec<String> = entry["corpus_unknown"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|id| id.as_str().map(str::to_owned))
        .collect();
    for id in undecided {
        if !unknown.contains(id) {
            unknown.push(id.clone());
        }
    }
    entry["corpus_unknown"] = json!(unknown);
}

/// What the flow says of a candidate whose baseline row is `row` and that today's admission
/// admitted: `(outcome, stage, reason, detail)`. A rejection read from a declared class (`none`,
/// a gap, or `refused`) is one only where the definition declares a `finished` end
/// (`declares_finished`): without one, an end it completes is not told from one it has no rule
/// for, as `compare` refuses an acceptance view over it (`no-finished-end`). An end reached at
/// the corpus's stop is accepted by the stop, whatever the definition declares.
fn outcome(
    row: &Value,
    declares_finished: bool,
) -> (
    &'static str,
    Option<&'static str>,
    Option<String>,
    Option<String>,
) {
    let class = row["class"].as_str().unwrap_or("error");
    if class != ResultClass::Comparable.as_str() {
        let reason = if class == ResultClass::ComparablePrefix.as_str() {
            "no-end"
        } else {
            class
        };
        return (
            "unknown",
            None,
            Some(reason.to_owned()),
            row["cause"].as_str().map(str::to_owned),
        );
    }
    match row_acceptance(row) {
        Acceptance::Accepted => ("accepted", None, None, None),
        Acceptance::Rejected if !declares_finished => (
            "unknown",
            None,
            Some("no-finished-end".to_owned()),
            Some(
                "every end is rejected by its declared class, and the definition declares no \
                 `finished` end: without one an end it completes is not told from one it has no \
                 rule for"
                    .to_owned(),
            ),
        ),
        Acceptance::Rejected => ("rejected", Some("end"), None, None),
        Acceptance::NotCompared(why) => (
            "unknown",
            None,
            Some(why.reason().to_owned()),
            Some(why.detail()),
        ),
    }
}

/// The row of `candidate`, whose baseline row in the overlay's coverage is `row`, and its status
/// (`declares_finished` as [`outcome`]).
fn candidate_row(
    candidate: &Candidate,
    row: &Value,
    options: &AdmitOptions,
    declares_finished: bool,
) -> (Value, u8) {
    let class = row["class"].as_str().unwrap_or("error");
    let mut value = json!({
        "file": candidate.file,
        "id": candidate.program.id,
        "class": class,
        "cause": row["cause"],
    });
    if class == ResultClass::Refused.as_str() {
        // `results::program_row` writes a refusal's cause as `STAGE/REASON: DETAIL`.
        let cause = row["cause"].as_str().unwrap_or_default();
        let (head, detail) = cause.split_once(": ").unwrap_or(("", cause));
        let (stage, reason) = head.split_once('/').unwrap_or((head, ""));
        value["outcome"] = json!("refused");
        value["stage"] = json!(stage);
        value["reason"] = json!(reason);
        value["detail"] = json!(detail);
        return (value, EXIT_YES);
    }
    // A case that states its rejection before its run (a case document at the K level, whose
    // texts are parsed; krs's case reader refuses `rejected`, PJ-32) has the class `rejected` or
    // `accepted`, and its outcome is admission's: rejected at the stage it states (`parse` or
    // `input`, as `end` is the stage of a rejection read from the ends), with the refusal's reason
    // and detail from its cause (`STAGE/REASON: DETAIL`, as a refusal's), or accepted, an unmet
    // statement, with its expectation.
    let status = if class == ResultClass::Rejected.as_str() {
        let cause = row["cause"].as_str().unwrap_or_default();
        let (head, detail) = cause.split_once(": ").unwrap_or(("", cause));
        let reason = head.split_once('/').map_or("", |(_, reason)| reason);
        value["outcome"] = json!("rejected");
        value["stage"] = json!(candidate.program.rejected.map(RejectedStage::as_str));
        value["reason"] = json!(reason);
        value["detail"] = json!(detail);
        value["expectation"] = row["expectation"].clone();
        EXIT_YES
    } else if class == ResultClass::Accepted.as_str() {
        value["outcome"] = json!("accepted");
        value["expectation"] = row["expectation"].clone();
        EXIT_NO
    } else {
        ends_row(&mut value, row, class, declares_finished)
    };
    let (fragment, provenance) = fragment(&candidate.table, &options.provenance);
    if let Some(provenance) = provenance {
        value["provenance"] = provenance.value();
    }
    value["fragment"] = json!(fragment);
    (value, status)
}

/// The members of `value`, the row of a candidate whose baseline row is `row` (of class `class`,
/// neither refused nor stated rejected), read from its ends ([`outcome`]), with its expectation;
/// returns its exit status.
fn ends_row(value: &mut Value, row: &Value, class: &str, declares_finished: bool) -> u8 {
    let mut status = EXIT_YES;
    let (outcome, stage, reason, detail) = outcome(row, declares_finished);
    if outcome == "unknown" {
        status = if class == ResultClass::Error.as_str() {
            EXIT_UNASKED
        } else {
            EXIT_UNANSWERED
        };
    }
    value["outcome"] = json!(outcome);
    value["stage"] = json!(stage);
    value["reason"] = json!(reason);
    value["detail"] = json!(detail);
    if !row["ends"].is_null() {
        value["ends"] = row["ends"].clone();
    }
    if let Some(expectation) = row.get("expectation") {
        status = exit_join(
            status,
            match expectation["verdict"].as_str() {
                Some("unmet") => EXIT_NO,
                Some("inconclusive") => EXIT_UNANSWERED,
                _ => EXIT_YES,
            },
        );
        value["expectation"] = expectation.clone();
    }
    status
}

/// The printed fragment of a candidate whose case, as a document of one case, is `table`: that
/// document with `provenance` the candidate's own, each member `flags` states replaced by the
/// flag's; none where neither states one, since a case document refuses an empty one. Returns
/// the TOML text and the provenance it carries.
#[must_use]
pub fn fragment(table: &Table, flags: &Provenance) -> (String, Option<Provenance>) {
    let own = table.get("provenance").and_then(toml::Value::as_table);
    let member = |key: &str, flag: &Option<String>| {
        flag.clone().or_else(|| {
            own.and_then(|own| own.get(key))
                .and_then(toml::Value::as_str)
                .map(str::to_owned)
        })
    };
    let provenance = Provenance {
        found_by: member("found_by", &flags.found_by),
        reason: member("reason", &flags.reason),
    };
    let provenance = (provenance != Provenance::default()).then_some(provenance);
    let mut table = table.clone();
    table.remove("provenance");
    let mut document = Table::new();
    if let Some(provenance) = &provenance {
        document.insert("provenance".into(), toml::Value::Table(provenance.table()));
    }
    document.extend(table);
    let text = toml::to_string(&document).expect("a case document's values encode");
    (text, provenance)
}

/// What the overlay's coverage document says of each family a baseline run decides, and of
/// those it does not compute (`mutations`, `flips`).
fn coverage_families(coverage: &Value) -> serde_json::Map<String, Value> {
    let mut families = serde_json::Map::new();
    families.insert(
        "mutations".into(),
        json!({"computed": false, "reason": MUTATIONS_NOT_COMPUTED}),
    );
    for family in TIER_ONE {
        let value = &coverage["families"][family];
        families.insert(
            family.into(),
            if value.is_null() || !value["items"].is_array() {
                json!({
                    "computed": false,
                    "reason": value["reason"].as_str().unwrap_or(
                        "coverage derives no item of the family under the flow's settings \
                         (rule windows and syntax paths need [coverage] depth above 1)"
                    ),
                })
            } else {
                json!({"computed": true, "reason": null})
            },
        );
    }
    families.insert(
        "flips".into(),
        json!({"computed": false, "reason": FLIPS_NOT_COMPUTED}),
    );
    families.insert(
        "arguments".into(),
        json!({"computed": true, "reason": null}),
    );
    families
}

/// The newly discharged obligations of each candidate, by its id.
type Newly = BTreeMap<String, Vec<Value>>;

/// One newly discharged obligation, as a candidate's row lists it.
fn entry(family: &str, item: &Value, corpus_unknown: &[String]) -> Value {
    let mut entry = json!({"family": family, "item": item});
    if !corpus_unknown.is_empty() {
        entry["corpus_unknown"] = json!(corpus_unknown);
    }
    entry
}

/// The obligations of the overlay's coverage document that each program not in `corpus` newly
/// discharges, by program id (module docs).
fn coverage_newly(coverage: &Value, corpus: &BTreeSet<String>) -> Newly {
    let mut newly: BTreeMap<String, Vec<Value>> = BTreeMap::new();
    let rules = coverage["families"]["rules"]["items"]
        .as_array()
        .map_or(&[][..], Vec::as_slice);
    for family in TIER_ONE {
        let value = &coverage["families"][family];
        let binders = value["binders"].as_array().map_or(&[][..], Vec::as_slice);
        for item in value["items"].as_array().into_iter().flatten() {
            let reading = crate::coverage::cover_cells(family, item, binders, rules);
            for (id, unknown) in newly_by(&reading, corpus) {
                newly
                    .entry(id)
                    .or_default()
                    .push(entry(family, &item["id"], &unknown));
            }
        }
    }
    for family in crate::coverage::FAMILIES {
        for item in coverage["families"][family]["items"]
            .as_array()
            .into_iter()
            .flatten()
        {
            let reading = crate::coverage::argument_cells(item);
            for (id, unknown) in newly_by(&reading, corpus) {
                newly
                    .entry(id)
                    .or_default()
                    .push(entry("arguments", &item["id"], &unknown));
            }
        }
    }
    newly
}

/// The programs not in `corpus` that newly discharge the obligation `reading` states, each with
/// the corpus cases whose cell on it is unknown. A program newly discharges a single-case
/// obligation when it is a decided discharger and no corpus case is; a pair obligation when a
/// pair over the corpus and it discharges it and no pair over the corpus does. An obligation that
/// names no discharger (`unnamed`) is attributed to none.
fn newly_by(reading: &Reading, corpus: &BTreeSet<String>) -> Vec<(String, Vec<String>)> {
    let in_corpus = |ids: &[String]| {
        ids.iter()
            .filter(|id| corpus.contains(*id))
            .cloned()
            .collect::<Vec<_>>()
    };
    match reading {
        Reading::Obligation(Cells {
            dischargers,
            unknown,
            unnamed,
        }) => {
            if *unnamed || dischargers.iter().any(|id| corpus.contains(id)) {
                return Vec::new();
            }
            let unknown = in_corpus(unknown);
            dischargers
                .iter()
                .map(|id| (id.clone(), unknown.clone()))
                .collect()
        }
        Reading::Pairs(PairCells { pairs, unknown, .. }) => {
            let over = |side: &[String], with: Option<&str>| {
                side.iter()
                    .any(|id| corpus.contains(id) || with == Some(id.as_str()))
            };
            if pairs
                .iter()
                .any(|[held, refuted]| over(held, None) && over(refuted, None))
            {
                return Vec::new();
            }
            let unknown = in_corpus(unknown);
            let mut programs = BTreeSet::new();
            for [held, refuted] in pairs {
                for id in held
                    .iter()
                    .chain(refuted)
                    .filter(|id| !corpus.contains(*id))
                {
                    if over(held, Some(id)) && over(refuted, Some(id)) {
                        programs.insert(id.clone());
                    }
                }
            }
            programs
                .into_iter()
                .map(|id| (id, unknown.clone()))
                .collect()
        }
        Reading::None | Reading::Refuted(_) => Vec::new(),
    }
}

/// The patterns family: the declared patterns each admitted candidate newly discharges, by
/// candidate id, and the family's entry. A lazy query of the corpus alone gives each pattern's
/// corpus dischargers; a `--full` query of the admitted candidates alone, of the patterns the
/// corpus does not discharge, gives each candidate's hits. Claims (`programs`) name corpus
/// programs and state nothing of a candidate, and `expect = "no"` states no obligation, so the
/// queries ask each pattern without them. The error is the stage and the detail of a refusal.
fn pattern_newly(
    manifest: &FlowManifest,
    front: &FrontEnd<'_>,
    corpus: &[Program],
    admitted: &[&Candidate],
    cache: Option<&Path>,
    corpus_set: &BTreeSet<String>,
) -> Result<(Newly, Value), (&'static str, String)> {
    let mut newly: BTreeMap<String, Vec<Value>> = BTreeMap::new();
    if manifest.patterns.is_empty() {
        return Ok((
            newly,
            json!({"computed": false, "reason": "the manifest declares no patterns"}),
        ));
    }
    let list = crate::pattern::declared_patterns(manifest, None, front.krs_patterns)
        .map_err(|error| ("patterns", error.to_string()))?;
    let obligations: Vec<_> = list
        .patterns
        .iter()
        .filter(|entry| entry.expect != Some(PatternExpect::No))
        .map(|entry| crate::pattern::PatternEntry {
            programs: None,
            expect: None,
            ..entry.clone()
        })
        .collect();
    if admitted.is_empty() || obligations.is_empty() {
        return Ok((newly, json!({"computed": true, "reason": null})));
    }
    let verb = front.spelling.verb(crate::Verb::Query);
    let ask = |programs: Vec<Program>, patterns: Vec<crate::pattern::PatternEntry>, full: bool| {
        let mut overlay = manifest.clone();
        overlay.programs = programs;
        let (document, _) = crate::query::query_spelled(
            &overlay,
            &PatternList { patterns },
            &QueryOptions {
                cache: cache.map(Path::to_path_buf),
                full,
                no_explain: true,
                ..QueryOptions::default()
            },
            &verb,
        );
        if document["spec"]["outcome"] == "refused" {
            return Err((
                "patterns",
                format!(
                    "the query of the patterns is refused: {}",
                    document["spec"]["detail"].as_str().unwrap_or_default()
                ),
            ));
        }
        Ok(document)
    };
    let mut corpus_unknown: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut open = Vec::new();
    if corpus.is_empty() {
        open.clone_from(&obligations);
    } else {
        let document = ask(corpus.to_vec(), obligations.clone(), false)?;
        for obligation in document["obligations"].as_array().into_iter().flatten() {
            let Reading::Obligation(cells) = crate::query::hit_cells(obligation) else {
                continue;
            };
            if cells.unnamed || cells.dischargers.iter().any(|id| corpus_set.contains(id)) {
                continue;
            }
            if let Some(entry) = obligations
                .iter()
                .find(|entry| obligation["id"] == entry.id.as_str())
            {
                open.push(entry.clone());
                corpus_unknown.insert(entry.id.clone(), cells.unknown);
            }
        }
    }
    if open.is_empty() {
        return Ok((newly, json!({"computed": true, "reason": null})));
    }
    let programs = admitted.iter().map(|c| c.program.clone()).collect();
    let document = ask(programs, open, true)?;
    for obligation in document["obligations"].as_array().into_iter().flatten() {
        let Reading::Obligation(cells) = crate::query::hit_cells(obligation) else {
            continue;
        };
        let id = obligation["id"].as_str().unwrap_or_default();
        let unknown = corpus_unknown.get(id).cloned().unwrap_or_default();
        for program in cells.dischargers {
            newly
                .entry(program)
                .or_default()
                .push(entry("patterns", &obligation["id"], &unknown));
        }
    }
    Ok((newly, json!({"computed": true, "reason": null})))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ids(ids: &[&str]) -> Vec<String> {
        ids.iter().map(|id| (*id).to_owned()).collect()
    }

    /// A candidate newly discharges a single-case obligation only where no corpus case is a
    /// decided discharger; a corpus case's unknown cell is named beside it; an unnamed discharge
    /// is attributed to no one.
    #[test]
    fn a_single_obligation_is_newly_discharged_only_without_a_corpus_discharger() {
        let corpus: BTreeSet<String> = ids(&["a", "b"]).into_iter().collect();
        let reading = |dischargers: &[&str], unknown: &[&str], unnamed| {
            Reading::Obligation(Cells {
                dischargers: ids(dischargers),
                unknown: ids(unknown),
                unnamed,
            })
        };
        assert_eq!(
            newly_by(&reading(&["c1", "c2"], &["b", "c3"], false), &corpus),
            [
                ("c1".to_owned(), ids(&["b"])),
                ("c2".to_owned(), ids(&["b"]))
            ]
        );
        assert!(newly_by(&reading(&["a", "c1"], &[], false), &corpus).is_empty());
        assert!(newly_by(&reading(&[], &[], true), &corpus).is_empty());
        assert!(newly_by(&Reading::Refuted(ids(&["c1"])), &corpus).is_empty());
    }

    /// A pair obligation is newly discharged by a candidate that completes a pair with the
    /// corpus, or holds both sides itself, and by none where the corpus already holds a pair.
    #[test]
    fn a_pair_obligation_is_newly_discharged_by_a_candidate_that_completes_a_pair() {
        let corpus: BTreeSet<String> = ids(&["a", "b"]).into_iter().collect();
        let pairs = |pairs: &[(&[&str], &[&str])]| {
            Reading::Pairs(PairCells {
                pairs: pairs
                    .iter()
                    .map(|(held, refuted)| [ids(held), ids(refuted)])
                    .collect(),
                sides: Vec::new(),
                unknown: Vec::new(),
            })
        };
        // `a` holds one side, `c1` the other; `c2` both; `c3` pairs with nothing of the corpus.
        assert_eq!(
            newly_by(
                &pairs(&[(&["a"], &["c1"]), (&["c2"], &["c2", "c3"])]),
                &corpus
            ),
            [("c1".to_owned(), Vec::new()), ("c2".to_owned(), Vec::new())]
        );
        assert!(newly_by(&pairs(&[(&["a"], &["b"]), (&["c1"], &["c1"])]), &corpus).is_empty());
    }

    /// A rejection read from a declared class needs a declared `finished` end; an end at the
    /// stop is accepted whatever the definition declares; a baseline that is not comparable is
    /// unknown with its class.
    #[test]
    fn a_declared_rejection_needs_a_declared_finished_end() {
        let row = |ends: Value| json!({"class": "comparable", "ends": ends});
        let gap = row(json!([{"declared": "none"}]));
        assert_eq!(outcome(&gap, true), ("rejected", Some("end"), None, None));
        let (word, _, reason, _) = outcome(&gap, false);
        assert_eq!(
            (word, reason.as_deref()),
            ("unknown", Some("no-finished-end"))
        );
        let stopped = row(json!([{"halt": "stop"}]));
        assert_eq!(outcome(&stopped, false).0, "accepted");
        let (word, _, reason, _) = outcome(&json!({"class": "timeout", "cause": "t"}), true);
        assert_eq!((word, reason.as_deref()), ("unknown", Some("timeout")));
    }

    /// FX2 (after FX1): a baseline whose run accepts at every listed end and takes an undefined
    /// step on another path is not known to accept the candidate (the undefined step may reject):
    /// `unknown`, reason `undecided`, never `accepted`; one that rejects at every listed end
    /// rejects it whatever the undefined step is.
    #[test]
    fn an_undefined_step_beside_accepted_ends_is_no_acceptance() {
        let undefined =
            |ends: Value| json!({"class": "comparable", "ends": ends, "undefined_steps": true});
        for ends in [json!([{"halt": "stop"}]), json!([{"declared": "finished"}])] {
            let (word, _, reason, detail) = outcome(&undefined(ends), true);
            assert_eq!((word, reason.as_deref()), ("unknown", Some("undecided")));
            assert!(detail.unwrap_or_default().contains("undefined step"));
        }
        assert_eq!(
            outcome(&undefined(json!([{"declared": "none"}])), true),
            ("rejected", Some("end"), None, None)
        );
    }

    /// A row of a program whose entry states that it must be rejected before it runs (PJ-32,
    /// which no case document states) is read as admission decided it: `rejected` at the stage
    /// its entry states, exit 0, or `accepted` with its unmet expectation, exit 1.
    #[test]
    fn a_row_rejected_before_it_runs_is_read_as_admission_decided_it() {
        let candidate = Candidate {
            file: "c.toml".into(),
            program: crate::Program {
                id: "c".into(),
                source: None,
                start_sort: None,
                variables: Vec::new(),
                inputs: Table::new(),
                case: None,
                case_file: None,
                expect: None,
                expect_for: crate::manifest::ExpectFor::default(),
                provenance: None,
                rejected: Some(crate::RejectedStage::Parse),
                stop_count: None,
            },
            table: Table::new(),
        };
        let options = AdmitOptions {
            candidates: Vec::new(),
            provenance: Provenance::default(),
            cache: None,
        };
        let met = json!({"verdict": "met", "detail": "d", "difference": null});
        let (value, status) = candidate_row(
            &candidate,
            &json!({"class": "rejected", "cause": "inputs/parse: no parse", "expectation": met}),
            &options,
            true,
        );
        assert_eq!(status, EXIT_YES);
        assert_eq!(
            (
                &value["outcome"],
                &value["stage"],
                &value["reason"],
                &value["detail"]
            ),
            (
                &json!("rejected"),
                &json!("parse"),
                &json!("parse"),
                &json!("no parse")
            )
        );
        assert_eq!(value["expectation"], met);
        let unmet = json!({"verdict": "unmet", "detail": "d", "difference": null});
        let (value, status) = candidate_row(
            &candidate,
            &json!({"class": "accepted", "cause": "d", "expectation": unmet}),
            &options,
            true,
        );
        assert_eq!(status, EXIT_NO);
        assert_eq!(value["outcome"], "accepted");
        assert_eq!(value["expectation"], unmet);
    }

    /// The fragment is a document of one case whose `provenance` takes each member a flag
    /// states in place of the candidate's own, keeps the other, and is absent where neither
    /// states one; the rest of the case is kept as written, and the text reads back as TOML.
    #[test]
    fn the_fragment_carries_the_flags_provenance_over_the_candidates_own() {
        let table: Table = toml::from_str(
            "provenance = { found_by = \"old\", reason = \"kept\" }\n[inputs]\nn = 1\n",
        )
        .unwrap();
        let flags = Provenance {
            found_by: Some("cargo-fuzz decode".into()),
            reason: None,
        };
        let (text, provenance) = fragment(&table, &flags);
        assert_eq!(
            provenance,
            Some(Provenance {
                found_by: Some("cargo-fuzz decode".into()),
                reason: Some("kept".into()),
            })
        );
        let read: Table = toml::from_str(&text).unwrap();
        assert_eq!(read["inputs"]["n"].as_integer(), Some(1));
        assert_eq!(
            read["provenance"]["found_by"].as_str(),
            Some("cargo-fuzz decode")
        );
        assert_eq!(read["provenance"]["reason"].as_str(), Some("kept"));

        let bare: Table = toml::from_str("[inputs]\nn = 2\n").unwrap();
        let (text, provenance) = fragment(&bare, &Provenance::default());
        assert_eq!(provenance, None);
        let read: Table = toml::from_str(&text).unwrap();
        assert!(!read.contains_key("provenance"));
        let (_, provenance) = fragment(
            &bare,
            &Provenance {
                found_by: None,
                reason: Some("why".into()),
            },
        );
        assert_eq!(provenance.unwrap().found_by, None);
    }
}
