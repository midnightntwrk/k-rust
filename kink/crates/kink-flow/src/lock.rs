//! The killer record, `verdicts.lock` (`run --lock FILE`): one recorded killer per killed
//! mutation, kept while it still kills.
//!
//! The record is an input. A run reads one fact from it: for each mutation id, the program id it
//! names as killer, which the search tries first ([`crate::search`], tier 2). Every status still
//! comes from runs or from tier-1 records; no status, cell or key is read from the record, so a
//! hand-edited or stale record can change which program is tried first, and so the cost and the
//! reported killer, but never a status.
//!
//! The record is also an output: after a run that judged every mutation of its list it is
//! rewritten ([`Lock::settle`]), so it states the verdicts of the current inputs. Its text is the
//! run's verdicts rendering without `killed_by` ([`crate::verdicts::lock_text`]), so a first-kill
//! run and a full run write the same bytes, and each killed mutation's `killer` is a function of
//! the record before the run and of the inputs (the corpus, the definition, the mutation list, the
//! budget, the solver profile and kink's build), never of the cache, the host's clock (while no
//! `budget.time_ms` bound fires) or the order work was done in.
//!
//! Reading tolerates any version: `schema` must be `kink-flow-verdicts` and `document` must be
//! `run`; each `[[mutation]]` must have a string `id` and may have a string `killer`, and its
//! `status` and `reason`, when they are strings, are read only to report what changed. A version-5
//! lock has no `killer` lines, so it records no killer. A file that is not TOML, has another
//! schema or document, or repeats an id does not decode, and the run is refused ([`Lock::read`]).

use crate::verdicts::{VERDICTS_SCHEMA, lock_text};
use kink_corpus::Store;
use serde_json::{Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
};

/// The record's file name in a corpus directory, the path the krs front end gives
/// `run --lock` (kink-flow itself has no default path).
pub const LOCK_FILE: &str = "verdicts.lock";

/// What a lock decodes to: each row's recorded facts, in the file's order.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Lock {
    /// The path the run reads and writes.
    pub path: PathBuf,
    /// The file's text; `None` when the file is absent.
    pub text: Option<String>,
    /// The rows, in the file's order.
    pub rows: Vec<LockRow>,
}

/// One `[[mutation]]` of a lock.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct LockRow {
    pub id: String,
    /// The recorded killer, the one fact a run reads.
    pub killer: Option<String>,
    /// The recorded status and reason, read only to report what changed.
    pub status: Option<String>,
    pub reason: Option<String>,
}

/// How a run ended, for [`Lock::settle`].
#[derive(Clone, Copy, Debug)]
pub struct Settle<'a> {
    /// `--locked`: compare, write nothing.
    pub locked: bool,
    /// `--verify`: write nothing.
    pub verify: bool,
    /// The ids `--only` selected (empty: every mutation).
    pub only: &'a [String],
    /// A corpus error stopped the run, so some mutation of the list has no row.
    pub stopped: bool,
}

/// The next step of a lock that does not decode.
const REFUSED_NEXT: &str = "resolve the file, or delete it to start from the search's killers";

impl Lock {
    /// Read the lock at `path`: an absent file is an empty lock; a file that does not decode is
    /// the refusal's detail (module documentation).
    pub fn read(path: &Path) -> Result<Self, String> {
        let refused = |what: String| format!("{}: {what}; {REFUSED_NEXT}", path.display());
        let text = match fs::read_to_string(path) {
            Ok(text) => text,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
                return Ok(Self {
                    path: path.to_path_buf(),
                    ..Self::default()
                });
            }
            Err(e) => return Err(refused(format!("cannot be read: {e}"))),
        };
        let table: toml::Table = text
            .parse()
            .map_err(|e: toml::de::Error| refused(format!("is not TOML: {}", e.message())))?;
        if table.get("schema").and_then(toml::Value::as_str) != Some(VERDICTS_SCHEMA) {
            return Err(refused(format!("its schema is not {VERDICTS_SCHEMA:?}")));
        }
        if table.get("document").and_then(toml::Value::as_str) != Some("run") {
            return Err(refused(
                "its document is not \"run\": a lock is the verdicts of a run".to_owned(),
            ));
        }
        let mutations = match table.get("mutation") {
            None => &[][..],
            Some(toml::Value::Array(rows)) => rows.as_slice(),
            Some(_) => return Err(refused("its mutation is not an array of tables".to_owned())),
        };
        let mut rows = Vec::with_capacity(mutations.len());
        let mut seen = BTreeSet::new();
        for (index, row) in mutations.iter().enumerate() {
            let Some(row) = row.as_table() else {
                return Err(refused(format!("mutation {} is not a table", index + 1)));
            };
            let Some(id) = row.get("id").and_then(toml::Value::as_str) else {
                return Err(refused(format!("mutation {} has no string id", index + 1)));
            };
            if !seen.insert(id.to_owned()) {
                return Err(refused(format!("the mutation {id:?} is listed twice")));
            }
            let killer = match row.get("killer") {
                None => None,
                Some(toml::Value::String(killer)) => Some(killer.clone()),
                Some(_) => return Err(refused(format!("the killer of {id:?} is not a string"))),
            };
            let string = |key: &str| {
                row.get(key)
                    .and_then(toml::Value::as_str)
                    .map(str::to_owned)
            };
            rows.push(LockRow {
                id: id.to_owned(),
                killer,
                status: string("status"),
                reason: string("reason"),
            });
        }
        Ok(Self {
            path: path.to_path_buf(),
            text: Some(text),
            rows,
        })
    }

    /// Each mutation id with its recorded killer.
    #[must_use]
    pub fn killers(&self) -> BTreeMap<String, String> {
        self.rows
            .iter()
            .filter_map(|row| Some((row.id.clone(), row.killer.clone()?)))
            .collect()
    }

    /// The run document's `lock` of a run that has not finished, which every report written
    /// before the last one carries: nothing written yet.
    #[must_use]
    pub fn pending(&self) -> Value {
        self.not_written("stopped")
    }

    /// The run document's `lock` when nothing was compared or written, for `reason`.
    #[must_use]
    pub fn not_written(&self, reason: &str) -> Value {
        json!({
            "path": self.path.display().to_string(),
            "status": "not-written",
            "reason": reason,
            "header": false,
            "changes": [],
        })
    }

    /// Settle the lock after a run whose document is `document`: compare the rendering the run
    /// would write with the file, and write it after a run that judged every mutation of its list
    /// in search mode without `--locked`. The value is the document's `lock`: `{path, status,
    /// reason, header, changes}` (README, "The killer record"), with `detail` when a write failed;
    /// the flag is false when it did.
    #[must_use]
    pub fn settle(&self, store: &Store, document: &Value, run: Settle<'_>) -> (Value, bool) {
        let path = self.path.display().to_string();
        let value = |status: &str, reason: Option<&str>, header: bool, changes: Vec<Value>| {
            json!({
                "path": path,
                "status": status,
                "reason": reason,
                "header": header,
                "changes": changes,
            })
        };
        let refused = document["spec"]["outcome"] == "refused";
        if refused || run.stopped {
            let reason = if refused { "refused" } else { "stopped" };
            return (value("not-written", Some(reason), false, Vec::new()), true);
        }
        let Ok(text) = lock_text(document) else {
            return (
                value("not-written", Some("refused"), false, Vec::new()),
                true,
            );
        };
        let header = self
            .text
            .as_deref()
            .is_none_or(|old| head(old) != head(&text));
        let changes = self.changes(document, run.only);
        if run.locked {
            let differs = if run.only.is_empty() {
                self.text.as_deref() != Some(text.as_str())
            } else {
                header || !changes.is_empty()
            };
            let status = if differs { "stale" } else { "unchanged" };
            return (value(status, Some("locked"), header, changes), true);
        }
        if run.verify {
            return (value("not-written", Some("verify"), header, changes), true);
        }
        if !run.only.is_empty() {
            return (value("not-written", Some("only"), header, changes), true);
        }
        if self.text.as_deref() == Some(text.as_str()) {
            return (value("unchanged", None, header, changes), true);
        }
        let status = if self.text.is_some() {
            "written"
        } else {
            "created"
        };
        match store.write_text(&self.path, &text) {
            Ok(()) => (value(status, None, header, changes), true),
            Err(e) => {
                let mut failed = value("not-written", Some("write-failed"), header, changes);
                failed["detail"] = json!(format!("cannot write {path}: {e}"));
                (failed, false)
            }
        }
    }

    /// Each mutation whose `(status, killer, reason)` differs between the lock and `document`'s
    /// rows: `{mutation, recorded, now}`, either side null for a row only the other has, in the
    /// document's order, then the lock's rows the document has no row for. Under `--only`
    /// (`only` not empty) only the selected rows are compared.
    fn changes(&self, document: &Value, only: &[String]) -> Vec<Value> {
        let selected = |id: &str| only.is_empty() || only.iter().any(|o| o == id);
        let recorded = self
            .rows
            .iter()
            .map(|row| {
                (
                    row.id.as_str(),
                    json!({"status": row.status, "killer": row.killer, "reason": row.reason}),
                )
            })
            .collect::<BTreeMap<_, _>>();
        let mut seen = BTreeSet::new();
        let mut changes = Vec::new();
        for row in document["mutations"].as_array().into_iter().flatten() {
            let id = row["id"].as_str().unwrap_or_default();
            if !selected(id) {
                continue;
            }
            seen.insert(id.to_owned());
            let now = json!({
                "status": row["status"],
                "killer": row["killer"],
                "reason": crate::verdicts::rendered_reason(row),
            });
            let before = recorded.get(id).cloned();
            if before.as_ref() != Some(&now) {
                changes.push(json!({"mutation": id, "recorded": before, "now": now}));
            }
        }
        for row in &self.rows {
            if selected(&row.id) && only.is_empty() && !seen.contains(&row.id) {
                changes.push(json!({
                    "mutation": row.id,
                    "recorded": recorded[row.id.as_str()],
                    "now": null,
                }));
            }
        }
        changes
    }
}

/// The lines of a rendering before its first `[[mutation]]`: the header and the `[spec]` section.
fn head(text: &str) -> &str {
    text.find("\n[[mutation]]").map_or(text, |end| &text[..end])
}

/// The run document's `lock` of a lock that does not decode: `{path, outcome: "refused",
/// detail}`.
#[must_use]
pub fn refused_value(path: &Path, detail: &str) -> Value {
    json!({"path": path.display().to_string(), "outcome": "refused", "detail": detail})
}

/// One line per change of a run document whose lock is `stale` (`--locked` found that the run
/// would change it), as `kink-flow` prints them on stderr: `verdicts.lock: plus/a: killer t4 ->
/// t2 (t4: not-in-corpus)`, `verdicts.lock: plus/c: killed -> survived`; empty otherwise.
#[must_use]
pub fn stale_lines(document: &Value) -> Vec<String> {
    let lock = &document["lock"];
    if lock["status"] != "stale" {
        return Vec::new();
    }
    let path = lock["path"].as_str().unwrap_or(LOCK_FILE);
    let mut lines = Vec::new();
    if lock["header"] == true {
        lines.push(format!(
            "{path}: the header differs (the file is absent, or another version or profile)"
        ));
    }
    let rows = document["mutations"].as_array();
    for change in lock["changes"].as_array().into_iter().flatten() {
        let id = change["mutation"].as_str().unwrap_or("?");
        let (recorded, now) = (&change["recorded"], &change["now"]);
        let text = |value: &Value| value.as_str().unwrap_or("none").to_owned();
        let line = match (recorded.is_null(), now.is_null()) {
            (true, _) => format!("added, {}", text(&now["status"])),
            (_, true) => format!("removed, was {}", text(&recorded["status"])),
            _ if recorded["status"] != now["status"] || recorded["reason"] != now["reason"] => {
                let with = |side: &Value| match side["reason"].as_str() {
                    Some(reason) => format!("{} ({reason})", text(&side["status"])),
                    None => text(&side["status"]),
                };
                format!("{} -> {}", with(recorded), with(now))
            }
            _ => {
                let why = rows
                    .into_iter()
                    .flatten()
                    .find(|row| row["id"] == id)
                    .and_then(|row| row["killer_change"].as_str());
                let because = match (recorded["killer"].as_str(), why) {
                    (Some(killer), Some(why)) => format!(" ({killer}: {why})"),
                    _ => String::new(),
                };
                format!(
                    "killer {} -> {}{because}",
                    text(&recorded["killer"]),
                    text(&now["killer"])
                )
            }
        };
        lines.push(format!("{path}: {id}: {line}"));
    }
    lines
}
