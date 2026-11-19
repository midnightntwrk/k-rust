//! `kink-flow accept FLOW.toml --projection NAME [--only CASE]... [--cache DIR] [--output
//! json|text]`: write the value each case's implementation states under a snapshot projection as
//! the case's snapshot, the value a user accepts (projections PJ-20). It is the only command that
//! writes a snapshot ([`crate::snapshot`]).
//!
//! # What is written
//!
//! The projection's producer is the one implementation whose views name it (decoding refuses a
//! second). `accept` runs `compare` of that implementation on the selected cases (every case of
//! the flow, or those `--only` names) and takes the value each snapshot view of the projection
//! judged ([`crate::compare::observed_snapshots`]): the run is compare's own, its requests, its
//! answer cache and its result cache, so the value written is the value a `compare` of the same
//! flow, cache and build judges, and a `compare` after `accept` finds it `equal`. Each value is
//! rendered as [`SnapshotValue::render`] renders it, into `snapshots/<projection>/<case id>.json`
//! beside the flow ([`snapshot::path`]); a file that already holds the value (as a JSON value: a
//! re-ordered or re-spaced file holds it) is left as it is, so `accept` changes exactly the files
//! a `compare` judges `pending`, `different` or `snapshot-unreadable`. Each file is written to a
//! temporary file beside it and renamed over it.
//!
//! Under a `metric` projection the value is the metric's baseline, `{metric, value}`
//! ([`crate::metric::baseline`]), the count the case's answer states; a case whose answer states
//! none is `not-accepted` (`metric-unstated`). A host-dependent metric has no baseline: `accept`
//! refuses its projection (`host-dependent`).
//!
//! # Cases without a value
//!
//! A case whose run gives no value is `not-accepted`, with the verdict, reason and detail
//! compare gives its snapshot view, and its file is left as it is (absent, or the value accepted
//! before): an answer `could-not-apply` states nothing of the program (README D6), so it is no
//! value to accept and no reason to drop the one accepted; a failure other than a crash under an
//! `accepts` projection (`spawn`, `malformed`, `timeout`; a crash under an `end` projection,
//! which states no end) states none either; and a case compare does not ask (its baseline has no
//! end, its inputs cannot be read) has no observed value. A case outside the projection's
//! `domain` has no snapshot: it is listed only where `--only` names it.
//!
//! # Stale files
//!
//! A file under `snapshots/<projection>/` that is the snapshot of no case of the flow in the
//! projection's domain (the case was removed, renamed or left the domain) is listed as `stale`
//! and never removed: no command reads it, so it decides no verdict, and whether its case is gone
//! or will return is the user's decision, as is deleting the value they accepted.
//!
//! # What else is written
//!
//! Nothing under the flow but the projection's snapshots, and the cache compare's run writes
//! (result records, answers of an implementation that declares `identity`, definition traces):
//! each entry is a function of its key, the entry `compare` writes for the same run, so no later
//! verdict changes; a later `compare` reads the answer `accept` accepted. No lock is read or
//! written.
//!
//! # Exit status
//!
//! 2 for a refused command (an unknown projection, one whose relation is not a snapshot or that
//! no view names, a host-dependent metric's, a `--only` case the flow does not hold, a refused manifest, specification or
//! comparison, a front end with no vocabulary), a snapshot that cannot be written, or a result
//! record that cannot (compare's `cache_error`); else 3 where a selected case is `not-accepted`;
//! else 0.

use crate::cli::{EXIT_UNANSWERED, EXIT_UNASKED, EXIT_YES, exit_join};
use crate::compare::{CompareOptions, SnapshotObserved, Vocabulary};
use crate::manifest::{FlowManifest, ImplementationSection, ProjectionSection};
use crate::snapshot::{self, Reference, SnapshotValue};
use serde_json::{Value, json};
use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};

/// The schema of the accept document.
pub const ACCEPT_SCHEMA: &str = "kink-flow-accept";

/// The accept document's version: its keys and their meanings.
pub const ACCEPT_VERSION: u64 = 1;

/// `kink-flow accept`'s options.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct AcceptOptions {
    /// `--projection NAME`: the snapshot projection whose values are accepted.
    pub projection: String,
    /// `--only CASE`: accept only these cases; empty: every case of the flow.
    pub only: Vec<String>,
    /// `--cache DIR`: compare's cache (default: `.kink-flow` beside FLOW.toml).
    pub cache: Option<PathBuf>,
}

/// The document of a command refused before anything was written, at `stage`.
fn refused(options: &AcceptOptions, stage: &str, reason: &str, detail: &str) -> Value {
    json!({
        "schema": ACCEPT_SCHEMA,
        "version": ACCEPT_VERSION,
        "k_rust_revision": crate::k_rust_revision(),
        "projection": options.projection,
        "implementation": null,
        "spec": null,
        "refusal": {"stage": stage, "reason": reason, "detail": detail},
        "cases": [],
        "changed": [],
        "stale": [],
        "summary": null,
    })
}

/// The names of `names`, as a refusal lists them.
fn listed<'a>(names: impl Iterator<Item = &'a str>) -> String {
    let names = names.map(|name| format!("`{name}`")).collect::<Vec<_>>();
    if names.is_empty() {
        "none".to_owned()
    } else {
        names.join(", ")
    }
}

/// The projection `options` names and its producer, the one implementation whose views name it;
/// the refused document where the projection is unknown or no snapshot, no view names it, or a
/// `--only` case is no case of the flow.
fn selection<'m>(
    manifest: &'m FlowManifest,
    options: &AcceptOptions,
) -> Result<(ProjectionSection, &'m ImplementationSection), Value> {
    let name = options.projection.as_str();
    let refuse = |reason: &str, detail: String| refused(options, "accept", reason, &detail);
    let Some(projection) = manifest.projection(name) else {
        return Err(refuse(
            "unknown-projection",
            format!(
                "--projection {name}: the manifest declares no projection of this name (it \
                 declares {})",
                listed(manifest.projections.iter().map(|p| p.name.as_str()))
            ),
        ));
    };
    if projection.is_host_dependent() {
        return Err(refuse(
            "host-dependent",
            format!(
                "--projection {name}: the projection measures a host-dependent metric, which is \
                 reported only: its value is a fact of the host, so no baseline of it is kept"
            ),
        ));
    }
    if !projection.is_snapshot() {
        return Err(refuse(
            "not-a-snapshot",
            format!(
                "--projection {name}: the projection's sides are compared with the definition's; \
                 only a projection with relation = \"snapshot\" has snapshots to accept"
            ),
        ));
    }
    let Some(producer) = manifest.implementations.iter().find(|implementation| {
        implementation
            .views
            .iter()
            .any(|view| view.projection.as_deref() == Some(name))
    }) else {
        return Err(refuse(
            "no-producer",
            format!(
                "--projection {name}: no [[implementation]] has a view naming the projection, so \
                 nothing states a value for it"
            ),
        ));
    };
    if let Some(case) = options
        .only
        .iter()
        .find(|case| !manifest.programs.iter().any(|program| &program.id == *case))
    {
        return Err(refuse(
            "unknown-case",
            format!("--only {case}: the flow has no case of this id"),
        ));
    }
    Ok((projection, producer))
}

/// `kink-flow accept`: the accept document and the exit status (module documentation).
#[must_use]
pub fn command(
    manifest: &FlowManifest,
    options: &AcceptOptions,
    vocabulary: Option<&dyn Vocabulary>,
) -> (Value, u8) {
    let (projection, producer) = match selection(manifest, options) {
        Ok(selected) => selected,
        Err(refused) => return (refused, EXIT_UNASKED),
    };
    let mut selected = manifest.clone();
    if !options.only.is_empty() {
        selected
            .programs
            .retain(|program| options.only.contains(&program.id));
    }
    let compare = CompareOptions {
        only: vec![producer.name.clone()],
        cache: options.cache.clone(),
        lock: None,
        locked: false,
    };
    let (compared, observed) = crate::compare::observed_snapshots(&selected, &compare, vocabulary);
    let mut document = json!({
        "schema": ACCEPT_SCHEMA,
        "version": ACCEPT_VERSION,
        "k_rust_revision": crate::k_rust_revision(),
        "projection": projection.name,
        "implementation": producer.name,
        "spec": compared["spec"],
        "refusal": null,
        "cases": [],
        "changed": [],
        "stale": [],
        "summary": null,
    });
    if compared["refusal"].is_object() {
        document["refusal"] = compared["refusal"].clone();
        return (document, EXIT_UNASKED);
    }
    if compared["spec"]["outcome"] != "admitted" {
        return (document, EXIT_UNASKED);
    }
    let mut status = EXIT_YES;
    if compared["cache_error"] == true {
        document["cache_error"] = json!(true);
        status = EXIT_UNASKED;
    }
    let views = producer
        .views
        .iter()
        .filter(|view| view.projection.as_deref() == Some(projection.name.as_str()))
        .map(|view| view.name.as_str())
        .collect::<Vec<_>>();
    let mut cases = Vec::new();
    for program in &selected.programs {
        let row = compared["rows"]
            .as_array()
            .into_iter()
            .flatten()
            .find(|row| row["program"] == program.id.as_str());
        let entry = row.and_then(|row| {
            row["views"]
                .as_array()
                .into_iter()
                .flatten()
                .find(|entry| views.iter().any(|view| entry["view"] == *view))
        });
        let outside =
            entry.is_some_and(|entry| entry["reason"] == crate::compare::OUTSIDE_DOMAIN_REASON);
        if outside && !options.only.contains(&program.id) {
            continue;
        }
        let value = observed
            .iter()
            .find(|observed| {
                observed.program == program.id && observed.projection == projection.name
            })
            .map(|SnapshotObserved { value, .. }| value);
        let case = case_row(manifest, &projection.name, &program.id, value, entry, row);
        status = exit_join(
            status,
            match case["outcome"].as_str() {
                Some("not-accepted") => EXIT_UNANSWERED,
                Some("unwritten") => EXIT_UNASKED,
                _ => EXIT_YES,
            },
        );
        cases.push(case);
    }
    let stale = stale(manifest, &projection);
    document["summary"] = summary(&cases, stale.len());
    document["changed"] = cases
        .iter()
        .filter(|case| matches!(case["outcome"].as_str(), Some("created" | "replaced")))
        .map(|case| case["snapshot"].clone())
        .collect();
    document["cases"] = json!(cases);
    document["stale"] = json!(stale);
    (document, status)
}

/// The count of each outcome of `cases`, and of the `stale` files.
fn summary(cases: &[Value], stale: usize) -> Value {
    let count = |outcome: &str| {
        cases
            .iter()
            .filter(|case| case["outcome"] == outcome)
            .count()
    };
    json!({
        "created": count("created"),
        "replaced": count("replaced"),
        "unchanged": count("unchanged"),
        "not_accepted": count("not-accepted"),
        "unwritten": count("unwritten"),
        "stale": stale,
    })
}

/// The row of `case` under the projection `name`: its snapshot (relative to the flow's
/// directory), the verdict compare gave its view (`entry`; the implementation's failure where
/// the view has no row), and its outcome: `created`, `replaced` or `unchanged` where the run
/// states `value`, `unwritten` where its file cannot be written, `not-accepted` where there is no
/// value.
fn case_row(
    manifest: &FlowManifest,
    name: &str,
    case: &str,
    value: Option<&SnapshotValue>,
    entry: Option<&Value>,
    row: Option<&Value>,
) -> Value {
    let relative = snapshot::relative(name, case);
    let mut out = json!({
        "case": case,
        "snapshot": relative,
        "outcome": null,
        "verdict": entry.map_or(Value::Null, |entry| entry["verdict"].clone()),
        "reason": entry.map_or(Value::Null, |entry| entry["reason"].clone()),
        "detail": null,
    });
    let Some(value) = value else {
        out["outcome"] = json!("not-accepted");
        out["detail"] = match (entry, row) {
            (Some(entry), _) => entry["detail"].clone(),
            (None, Some(row)) if row["failure"].is_object() => {
                out["reason"] = row["failure"]["kind"].clone();
                row["failure"]["detail"].clone()
            }
            _ => json!("the implementation was not asked for the case"),
        };
        return out;
    };
    let path = snapshot::path(&manifest.directory, name, case);
    let outcome = match snapshot::read(&path) {
        Reference::Value(accepted) if &accepted == value => "unchanged",
        Reference::Missing => "created",
        Reference::Value(_) | Reference::Unreadable(_) => "replaced",
    };
    if outcome != "unchanged"
        && let Err(error) = write(&path, &value.render())
    {
        out["outcome"] = json!("unwritten");
        out["detail"] = json!(format!("{relative} cannot be written: {error}"));
        return out;
    }
    out["outcome"] = json!(outcome);
    out
}

/// Write `text` at `path`: to a temporary file beside it, renamed over it, so a reader sees the
/// old file or the new one; the parent directories are created.
fn write(path: &Path, text: &str) -> std::io::Result<()> {
    let parent = path.parent().unwrap_or_else(|| Path::new("."));
    fs::create_dir_all(parent)?;
    let mut temporary = path.as_os_str().to_owned();
    temporary.push(format!(".accept-{}", std::process::id()));
    let temporary = PathBuf::from(temporary);
    fs::write(&temporary, text)?;
    fs::rename(&temporary, path).inspect_err(|_| {
        let _ = fs::remove_file(&temporary);
    })
}

/// The files under `projection`'s directory (relative to the flow's, `/` separating components,
/// sorted) that are the snapshot of no case of `manifest` in the projection's domain.
fn stale(manifest: &FlowManifest, projection: &ProjectionSection) -> Vec<String> {
    let name = projection.name.as_str();
    let expected = manifest
        .programs
        .iter()
        .filter(|program| projection.holds(program))
        .map(|program| snapshot::relative(name, &program.id))
        .collect::<BTreeSet<_>>();
    let mut found = BTreeSet::new();
    let mut pending = vec![snapshot::directory(name)];
    while let Some(relative) = pending.pop() {
        let directory = relative
            .split('/')
            .fold(manifest.directory.clone(), |path, part| path.join(part));
        let Ok(entries) = fs::read_dir(&directory) else {
            continue;
        };
        for entry in entries.flatten() {
            let Some(file) = entry.file_name().to_str().map(str::to_owned) else {
                continue;
            };
            let path = format!("{relative}/{file}");
            match entry.file_type() {
                Ok(kind) if kind.is_dir() => pending.push(path),
                Ok(_) if !expected.contains(&path) => {
                    found.insert(path);
                }
                _ => {}
            }
        }
    }
    found.into_iter().collect()
}

/// The `--output text` rendering of an accept document: one line per file written (`created`,
/// `replaced`), per case not accepted and per stale file, then the counts.
///
/// # Errors
///
/// The document is not an accept document.
pub fn text(document: &Value) -> Result<String, String> {
    if document["schema"] != ACCEPT_SCHEMA {
        return Err("the document is not an accept document".to_owned());
    }
    let mut text = String::new();
    let projection = document["projection"].as_str().unwrap_or_default();
    if let Some(refusal) = document["refusal"].as_object() {
        let field = |key: &str| refusal.get(key).and_then(Value::as_str).unwrap_or_default();
        let _ = writeln!(
            text,
            "accept {projection}: refused ({}/{}): {}",
            field("stage"),
            field("reason"),
            field("detail")
        );
        return Ok(text);
    }
    if document["spec"]["outcome"] != "admitted" {
        let _ = writeln!(
            text,
            "accept {projection}: the specification is refused: {}",
            document["spec"]["detail"].as_str().unwrap_or_default()
        );
        return Ok(text);
    }
    for case in document["cases"].as_array().into_iter().flatten() {
        let field = |key: &str| case[key].as_str().unwrap_or_default();
        match field("outcome") {
            outcome @ ("created" | "replaced") => {
                let _ = writeln!(text, "{outcome} {}", field("snapshot"));
            }
            "not-accepted" => {
                let why = [field("verdict"), field("reason")]
                    .into_iter()
                    .filter(|part| !part.is_empty())
                    .collect::<Vec<_>>()
                    .join(" ");
                let _ = writeln!(
                    text,
                    "not accepted {} ({why}): {}",
                    field("case"),
                    field("detail")
                );
            }
            "unwritten" => {
                let _ = writeln!(text, "unwritten {}", field("detail"));
            }
            _ => {}
        }
    }
    for path in document["stale"].as_array().into_iter().flatten() {
        let _ = writeln!(
            text,
            "stale {} (the snapshot of no case of the projection's domain; not removed)",
            path.as_str().unwrap_or_default()
        );
    }
    let summary = &document["summary"];
    let count = |key: &str| summary[key].as_u64().unwrap_or_default();
    let _ = writeln!(
        text,
        "accept {projection} ({}): {} created, {} replaced, {} unchanged, {} not accepted, {} \
         stale",
        document["implementation"].as_str().unwrap_or_default(),
        count("created"),
        count("replaced"),
        count("unchanged"),
        count("not_accepted"),
        count("stale"),
    );
    Ok(text)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A snapshot is written through a temporary file beside it, its directories created, and
    /// the temporary file does not remain.
    #[test]
    fn a_snapshot_is_written_by_rename_into_new_directories() {
        let dir = std::env::temp_dir().join(format!("kink-flow-accept-{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        let path = dir.join("snapshots/p/a%20b/c.json");
        write(&path, "{}\n").unwrap();
        write(&path, "{\n  \"answer\": \"accepted\"\n}\n").unwrap();
        assert_eq!(
            fs::read_to_string(&path).unwrap(),
            "{\n  \"answer\": \"accepted\"\n}\n"
        );
        let names = fs::read_dir(path.parent().unwrap())
            .unwrap()
            .map(|entry| entry.unwrap().file_name().into_string().unwrap())
            .collect::<Vec<_>>();
        assert_eq!(names, ["c.json"]);
        fs::remove_dir_all(&dir).unwrap();
    }

    /// The text lists each file changed, each case not accepted and each stale file, then the
    /// counts; a refused document is one line naming its stage and reason.
    #[test]
    fn the_text_lists_the_changed_files_and_the_counts() {
        let document = json!({
            "schema": ACCEPT_SCHEMA,
            "projection": "msg",
            "implementation": "diag",
            "spec": {"outcome": "admitted"},
            "refusal": null,
            "cases": [
                {"case": "a", "snapshot": "snapshots/msg/a.json", "outcome": "created"},
                {"case": "b", "snapshot": "snapshots/msg/b.json", "outcome": "unchanged"},
                {"case": "c", "snapshot": "snapshots/msg/c.json", "outcome": "replaced"},
                {"case": "d", "snapshot": "snapshots/msg/d.json", "outcome": "not-accepted",
                 "verdict": null, "reason": "timeout", "detail": "the clock cancelled it"},
            ],
            "stale": ["snapshots/msg/gone.json"],
            "summary": {"created": 1, "replaced": 1, "unchanged": 1, "not_accepted": 1,
                        "unwritten": 0, "stale": 1},
        });
        assert_eq!(
            text(&document).unwrap(),
            "created snapshots/msg/a.json\n\
             replaced snapshots/msg/c.json\n\
             not accepted d (timeout): the clock cancelled it\n\
             stale snapshots/msg/gone.json (the snapshot of no case of the projection's domain; \
             not removed)\n\
             accept msg (diag): 1 created, 1 replaced, 1 unchanged, 1 not accepted, 1 stale\n"
        );
        let options = AcceptOptions {
            projection: "nope".to_owned(),
            ..AcceptOptions::default()
        };
        let refused = refused(
            &options,
            "accept",
            "unknown-projection",
            "no such projection",
        );
        assert_eq!(
            text(&refused).unwrap(),
            "accept nope: refused (accept/unknown-projection): no such projection\n"
        );
        assert!(text(&json!({"schema": "kink-flow-compare"})).is_err());
    }
}
