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
    /// The file's header: each key outside its `[[mutation]]` rows (a section's as
    /// `section.key`) with its value, read only to name what changed ([`header_values`]).
    pub header: BTreeMap<String, Value>,
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
    /// `--locked`: compare, and leave the lock unwritten.
    pub locked: bool,
    /// `--verify`: leave the lock unwritten.
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
            header: header_values(&table),
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
        not_written(&self.path, reason)
    }

    /// Settle the lock after a run whose document is `document`: compare the rendering the run
    /// would write with the file, and write it after a run that judged every mutation of its list
    /// in search mode without `--locked`. The value is the document's `lock`: `{path, status,
    /// reason, header, header_changes, changes, difference}` (README, "The killer record"), with
    /// `detail` when a write failed; the flag is false when it did.
    ///
    /// Under `--locked` a lock that differs from the rendering only in its header is `stale`,
    /// like one whose rows differ. In particular a lock recorded on another Z3 build (its
    /// `z3_version` or `z3_library_sha256`) is a finding even when every row agrees. Under the Z3
    /// profile a verdict is a function of the inputs and of the solver build, so the build is part
    /// of the instrument the lock was measured with, as the profile is. `--locked` asks whether
    /// this run, on this instrument, writes the committed lock. A run on another build cannot
    /// confirm that, because rows that agree on today's corpus do not make two builds
    /// interchangeable for the next edit. Passing it would leave the repository's lock naming a
    /// build no check ran on, so a later moved row would be blamed on the corpus while the header
    /// misnamed the solver. When every row agrees the fix is a header-only rewrite (a run
    /// without `--locked`), which review sees as exactly that.
    #[must_use]
    pub fn settle(&self, store: &Store, document: &Value, run: Settle<'_>) -> (Value, bool) {
        let path = self.path.display().to_string();
        let refused = document["spec"]["outcome"] == "refused";
        if refused || run.stopped {
            let reason = if refused { "refused" } else { "stopped" };
            return (self.not_written(reason), true);
        }
        let Ok(text) = lock_text(document) else {
            return (self.not_written("refused"), true);
        };
        let header = self
            .text
            .as_deref()
            .is_none_or(|old| head(old) != head(&text));
        let header_changes = self.header_changes(&text);
        let changes = self.changes(document, run.only);
        // Under `--only` the rows it did not select may differ from the file's: only the selected
        // rows and the header are compared, so no first difference of the whole file is named.
        let difference = if run.only.is_empty() {
            self.difference(&text)
        } else {
            Value::Null
        };
        let value = |status: &str, reason: Option<&str>, header: bool, changes: Vec<Value>| {
            json!({
                "path": path,
                "status": status,
                "reason": reason,
                "header": header,
                "header_changes": header_changes,
                "changes": changes,
                "difference": difference,
            })
        };
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

    /// Where the file first differs from `text`, the rendering the run would write:
    /// `{kind, line, recorded, now}`, `line` counted from 1 in the file; null when the file is
    /// absent or equal. `kind` is `order` when the two hold the same rows in another order: then
    /// `line` is the file's line of the `id` of its first row out of the rendering's order,
    /// `recorded` that line and `now` the `id` line of the row the rendering puts there, whatever
    /// else (a comment, spacing) differs before it. Otherwise `kind` is `text` (a comment,
    /// spacing, or a key the rendering does not write, beside what the header and the row changes
    /// say), and `line` is the first line in which the two differ, `recorded` and `now` that line
    /// of each (null past its end).
    fn difference(&self, text: &str) -> Value {
        let Some(old) = self.text.as_deref() else {
            return Value::Null;
        };
        if old == text {
            return Value::Null;
        }
        let ids = |rows: &mut dyn Iterator<Item = String>| {
            let mut ids = rows.collect::<Vec<_>>();
            let order = ids.clone();
            ids.sort();
            (order, ids)
        };
        let (old_order, old_set) = ids(&mut self.rows.iter().map(|row| row.id.clone()));
        let rendered = Lock::read_text(text);
        let (new_order, new_set) = ids(&mut rendered.into_iter());
        if old_order != new_order && old_set == new_set {
            let (old_ids, new_ids) = (id_lines(old), id_lines(text));
            let first = old_order.iter().zip(&new_order).position(|(a, b)| a != b);
            if let Some(((line, recorded), (_, now))) =
                first.and_then(|at| old_ids.get(at).zip(new_ids.get(at)))
            {
                return json!({"kind": "order", "line": line, "recorded": recorded, "now": now});
            }
        }
        let (mut recorded, mut now) = (old.split('\n'), text.split('\n'));
        let mut line = 1_u64;
        let (recorded, now) = loop {
            match (recorded.next(), now.next()) {
                (Some(a), Some(b)) if a == b => line += 1,
                (a, b) => break (a, b),
            }
        };
        json!({"kind": "text", "line": line, "recorded": recorded, "now": now})
    }

    /// Each key of the header whose value differs between the file and `text`, the rendering the
    /// run would write: `{key, recorded, now}`, either side null where that side has no such key,
    /// in the order of the rendering's lines, then the keys only the file has, in key order. Empty
    /// when the file is absent (there is no recorded header to compare) or the headers' values are
    /// equal (they may still differ in a comment or spacing, which `header` and `difference`
    /// show).
    fn header_changes(&self, text: &str) -> Vec<Value> {
        if self.text.is_none() {
            return Vec::new();
        }
        let now = text
            .parse::<toml::Table>()
            .map(|table| header_values(&table))
            .unwrap_or_default();
        let mut keys = header_key_order(text);
        keys.retain(|key| now.contains_key(key));
        keys.extend(
            self.header
                .keys()
                .filter(|key| !now.contains_key(*key))
                .cloned(),
        );
        keys.into_iter()
            .filter_map(|key| {
                let (recorded, now) = (self.header.get(&key), now.get(&key));
                (recorded != now).then(|| json!({"key": key, "recorded": recorded, "now": now}))
            })
            .collect()
    }

    /// The mutation ids of the rendering `text`, in its order; none for a text that does not
    /// decode, which a rendering always does.
    fn read_text(text: &str) -> Vec<String> {
        let Ok(table) = text.parse::<toml::Table>() else {
            return Vec::new();
        };
        table
            .get("mutation")
            .and_then(toml::Value::as_array)
            .into_iter()
            .flatten()
            .filter_map(|row| row.get("id")?.as_str().map(str::to_owned))
            .collect()
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

/// The run document's `lock` of a lock at `path` when nothing was compared or written, for
/// `reason`: also the lock of a run whose manifest or mutation list was refused before the lock
/// was read.
#[must_use]
pub fn not_written(path: &Path, reason: &str) -> Value {
    json!({
        "path": path.display().to_string(),
        "status": "not-written",
        "reason": reason,
        "header": false,
        "header_changes": [],
        "changes": [],
        "difference": null,
    })
}

/// The header of a decoded lock or rendering: each key outside its `[[mutation]]` rows, a
/// section's keys as `section.key`, with its value as JSON (a string, an integer or a boolean
/// as itself, any other value as its TOML text).
fn header_values(table: &toml::Table) -> BTreeMap<String, Value> {
    let json = |value: &toml::Value| match value {
        toml::Value::String(text) => json!(text),
        toml::Value::Integer(number) => json!(number),
        toml::Value::Boolean(flag) => json!(flag),
        other => json!(other.to_string()),
    };
    let mut header = BTreeMap::new();
    for (key, value) in table {
        match value {
            toml::Value::Table(section) => {
                for (inner, value) in section {
                    header.insert(format!("{key}.{inner}"), json(value));
                }
            }
            _ if key == "mutation" => {}
            value => {
                header.insert(key.clone(), json(value));
            }
        }
    }
    header
}

/// The header keys of a rendering's text, in the order of its lines, as [`header_values`]
/// names them: a key before any table, or `section.key` in a `[section]`; none in a
/// `[[mutation]]` row.
fn header_key_order(text: &str) -> Vec<String> {
    let mut keys = Vec::new();
    let mut section: Option<&str> = Some("");
    for line in text.split('\n') {
        let trimmed = line.trim();
        if trimmed.starts_with("[[") {
            section = None;
        } else if let Some(name) = trimmed.strip_prefix('[').and_then(|r| r.strip_suffix(']')) {
            section = Some(name.trim());
        } else if let (Some(section), Some((key, _))) = (section, trimmed.split_once('=')) {
            let key = key.trim();
            keys.push(if section.is_empty() {
                key.to_owned()
            } else {
                format!("{section}.{key}")
            });
        }
    }
    keys
}

/// The `id` line of each `[[mutation]]` row of a lock's text, in order, with its line number
/// counted from 1: the first line of the row's table that sets `id`.
fn id_lines(text: &str) -> Vec<(u64, &str)> {
    let mut lines = Vec::new();
    let mut in_row = false;
    for (number, line) in (1_u64..).zip(text.split('\n')) {
        let trimmed = line.trim();
        if trimmed.starts_with('[') {
            in_row = trimmed == "[[mutation]]";
        } else if in_row
            && trimmed
                .strip_prefix("id")
                .is_some_and(|rest| rest.trim_start().starts_with('='))
        {
            lines.push((number, line));
            in_row = false;
        }
    }
    lines
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
/// would change it), as `kink-flow` prints them on stderr: one per header key whose value differs
/// (`lock.header_changes`: `` verdicts.lock: the header's z3_library_sha256 differs: recorded
/// "7ca2…", now "1f0e…" (another Z3 build) ``), or one saying that the header differs when no
/// value does (the file is absent, or a comment or spacing differs); then one per row,
/// `verdicts.lock: plus/a: killer t4 -> t2 (t4: not-in-corpus)`, `verdicts.lock: plus/c:
/// killed -> survived`; when neither the header nor any row's verdict differs, one line naming
/// the first difference (`lock.difference`: the rows' order, or a line of text); empty
/// otherwise.
#[must_use]
pub fn stale_lines(document: &Value) -> Vec<String> {
    let lock = &document["lock"];
    if lock["status"] != "stale" {
        return Vec::new();
    }
    let path = lock["path"].as_str().unwrap_or(LOCK_FILE);
    let mut lines = Vec::new();
    if lock["header"] == true {
        let header_changes = lock["header_changes"]
            .as_array()
            .map_or(&[][..], Vec::as_slice);
        if header_changes.is_empty() {
            lines.push(format!(
                "{path}: the header differs (the file is absent, or a comment or spacing before \
                 its first mutation differs)"
            ));
        }
        for change in header_changes {
            let key = change["key"].as_str().unwrap_or("?");
            let side = |value: &Value| {
                if value.is_null() {
                    "absent".to_owned()
                } else {
                    value.to_string()
                }
            };
            let why = match key {
                "version" => " (another version of the rendering)",
                "profile" => " (another solver profile)",
                "z3_version" | "z3_library_sha256" => " (another Z3 build)",
                _ => "",
            };
            lines.push(format!(
                "{path}: the header's {key} differs: recorded {}, now {}{why}",
                side(&change["recorded"]),
                side(&change["now"])
            ));
        }
    }
    let rows = document["mutations"].as_array();
    let changes = lock["changes"].as_array().map_or(&[][..], Vec::as_slice);
    // A file that differs neither in its header nor in a row's verdict differs in its row order or
    // its text: the first difference says which.
    let difference = &lock["difference"];
    if lock["header"] != true && changes.is_empty() && difference.is_object() {
        let side = |value: &Value| {
            value.as_str().map_or_else(
                || "the end of the file".to_owned(),
                |line| format!("`{line}`"),
            )
        };
        let at = format!(
            "line {}: recorded {}, now {}",
            difference["line"],
            side(&difference["recorded"]),
            side(&difference["now"])
        );
        lines.push(if difference["kind"] == "order" {
            format!(
                "{path}: its rows are in another order than the mutation list's (first at {at}); \
                 a run writes them in the list's order"
            )
        } else {
            format!(
                "{path}: it differs from the rendering the run would write at {at} (a comment, \
                 spacing, or a key the rendering does not write); a run rewrites it"
            )
        });
    }
    for change in changes {
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

#[cfg(test)]
mod tests {
    use super::*;

    const AB: &str = "schema = \"kink-flow-verdicts\"\nversion = 6\ndocument = \"run\"\n\n\
                      [[mutation]]\nid = \"a\"\nstatus = \"survived\"\n\n\
                      [[mutation]]\nid = \"b\"\nstatus = \"survived\"\n";

    fn lock(text: &str) -> Lock {
        let path = PathBuf::from("verdicts.lock");
        let rows = Lock::read_text(text)
            .into_iter()
            .map(|id| LockRow {
                id,
                ..LockRow::default()
            })
            .collect();
        Lock {
            path,
            text: Some(text.to_owned()),
            rows,
            header: header_values(&text.parse().unwrap()),
        }
    }

    /// A lock whose rows are the rendering's in another order differs from it with kind `order`,
    /// at its first reordered row's `id` line, a comment before it included; one that differs
    /// only in its text with kind `text`, at the first line that differs; an equal or absent one
    /// has no difference.
    #[test]
    fn the_first_difference_names_a_reordering_or_a_line() {
        let ba = AB
            .replace("id = \"a\"", "id = \"x\"")
            .replace("id = \"b\"", "id = \"a\"")
            .replace("id = \"x\"", "id = \"b\"");
        assert_eq!(
            lock(&ba).difference(AB),
            json!({"kind": "order", "line": 6, "recorded": "id = \"b\"", "now": "id = \"a\""})
        );
        let commented = format!("# kept by hand\n{AB}");
        assert_eq!(
            lock(&commented).difference(AB),
            json!({
                "kind": "text",
                "line": 1,
                "recorded": "# kept by hand",
                "now": "schema = \"kink-flow-verdicts\"",
            })
        );
        // A hand comment before reordered rows: the order is what a run changes, and the line
        // named is the first reordered row's, not the comment's.
        let commented_ba = format!("# kept by hand\n{ba}");
        assert_eq!(
            lock(&commented_ba).difference(AB),
            json!({"kind": "order", "line": 7, "recorded": "id = \"b\"", "now": "id = \"a\""})
        );
        assert_eq!(lock(AB).difference(AB), Value::Null);
        assert_eq!(Lock::default().difference(AB), Value::Null);
    }

    /// `stale_lines` names the first difference only when neither the header nor a row's verdict
    /// explains the stale lock.
    #[test]
    fn a_stale_lock_with_no_change_names_its_first_difference() {
        let document = |header: bool, changes: Value| {
            json!({
                "mutations": [],
                "lock": {
                    "path": "verdicts.lock",
                    "status": "stale",
                    "header": header,
                    "changes": changes,
                    "difference": {"kind": "order", "line": 6, "recorded": "id = \"b\"", "now": "id = \"a\""},
                },
            })
        };
        assert_eq!(
            stale_lines(&document(false, json!([]))),
            [
                "verdicts.lock: its rows are in another order than the mutation list's (first at \
                 line 6: recorded `id = \"b\"`, now `id = \"a\"`); a run writes them in the list's \
                 order"
            ]
        );
        let changed = json!([{"mutation": "a", "recorded": null, "now": {"status": "survived"}}]);
        assert_eq!(
            stale_lines(&document(false, changed)),
            ["verdicts.lock: a: added, survived"]
        );
        assert_eq!(
            stale_lines(&document(true, json!([]))),
            [
                "verdicts.lock: the header differs (the file is absent, or a comment or spacing \
                 before its first mutation differs)"
            ]
        );
    }

    /// A lock recorded on another Z3 build differs from the rendering in the header's values
    /// only: `header_changes` names each key whose value differs, in the rendering's line order,
    /// and `stale_lines` names each with why it matters; a key only one side has is null on the
    /// other.
    #[test]
    fn a_lock_of_another_z3_build_names_the_build_lines() {
        let header = |build: &str| {
            format!(
                "schema = \"kink-flow-verdicts\"\nversion = 10\ndocument = \"run\"\nprofile = \
                 \"z3\"\nz3_version = \"5.3.3.0\"\n{build}\n[spec]\noutcome = \"admitted\"\n\n\
                 [[mutation]]\nid = \"a\"\nstatus = \"survived\"\n"
            )
        };
        let now = header("z3_library_sha256 = \"bbbb\"\n");
        let recorded = lock(&header("z3_library_sha256 = \"aaaa\"\n"));
        let changes = recorded.header_changes(&now);
        assert_eq!(
            changes,
            [json!({"key": "z3_library_sha256", "recorded": "aaaa", "now": "bbbb"})]
        );
        // A build that could not name its library has no digest line.
        assert_eq!(
            lock(&header("")).header_changes(&now),
            [json!({"key": "z3_library_sha256", "recorded": null, "now": "bbbb"})]
        );
        // The portable rendering of the same verdicts: another profile and no build lines.
        let portable = "schema = \"kink-flow-verdicts\"\nversion = 10\ndocument = \"run\"\nprofile = \
                        \"no-z3\"\n\n[spec]\noutcome = \"admitted\"\n\n[[mutation]]\nid = \"a\"\n\
                        status = \"survived\"\n";
        assert_eq!(
            recorded.header_changes(portable),
            [
                json!({"key": "profile", "recorded": "z3", "now": "no-z3"}),
                json!({"key": "z3_library_sha256", "recorded": "aaaa", "now": null}),
                json!({"key": "z3_version", "recorded": "5.3.3.0", "now": null}),
            ]
        );
        assert_eq!(
            recorded.header_changes(&recorded.text.clone().unwrap()),
            [] as [Value; 0]
        );
        assert_eq!(Lock::default().header_changes(&now), [] as [Value; 0]);
        let document = json!({
            "mutations": [],
            "lock": {
                "path": "verdicts.lock",
                "status": "stale",
                "header": true,
                "header_changes": changes,
                "changes": [],
                "difference": {"kind": "text", "line": 6, "recorded": "z3_library_sha256 = \"aaaa\"", "now": "z3_library_sha256 = \"bbbb\""},
            },
        });
        assert_eq!(
            stale_lines(&document),
            [
                "verdicts.lock: the header's z3_library_sha256 differs: recorded \"aaaa\", now \
                 \"bbbb\" (another Z3 build)"
            ]
        );
    }
}
