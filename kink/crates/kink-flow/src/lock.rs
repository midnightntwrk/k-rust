//! The killer record, `verdicts.lock` (`run --lock FILE`): one recorded killer per killed
//! mutation, kept while it still kills; and the coverage lock, `coverage.lock` (`coverage --lock
//! FILE`), one recorded killer per distinguished flip by the same rule ([`LockKind`]).
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
//!
//! # The coverage lock
//!
//! A coverage lock is the same record over a `coverage` document ([`LockKind::Coverage`]): its
//! text is the coverage verdicts rendering, `document` is `coverage`, and its rows are the flips
//! (`[[flip]]`), each with its `id`, `status`, a refused flip's `reason` and a distinguished flip's
//! `killer`. A flip's killer is a mutation's killer under another name: the flip's mutant is run
//! by the kill search `run` makes ([`crate::search`]), keyed by the flip's id, so the recorded
//! killer is tried first and kept while it still kills, else the first killing program in the
//! search's order. The rendering also lists each family's open and argued obligations (`[rules]
//! open`, `[rules] argued`, ...), and each argued item's standing (`[arguments]`, one
//! `"<id>" = "<standing>"` line per item), which are read only to report what changed, as a row's
//! status is: a standing that moves changes the text, so `--locked` finds the lock stale, and the
//! lock's state names the item (`argument_changes`).
//! Its header is what comes before the first family: the schema, version, profile and build lines,
//! the specification and the settings. `[arguments]` is no part of it: its keys are item ids, a
//! verdict per line, as a family's arrays are.

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

/// The coverage lock's file name in a corpus directory, the path the krs front end gives
/// `coverage --lock` (kink-flow itself has no default path).
pub const COVERAGE_LOCK_FILE: &str = "coverage.lock";

/// Which document a lock records: a run's verdicts (`verdicts.lock`), one row per mutation, or a
/// coverage command's (`coverage.lock`), one row per flip (module documentation).
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum LockKind {
    /// `run --lock`: `document = "run"`, `[[mutation]]` rows.
    #[default]
    Run,
    /// `coverage --lock`: `document = "coverage"`, `[[flip]]` rows.
    Coverage,
}

impl LockKind {
    /// The `document` a lock of this kind names.
    #[must_use]
    pub const fn document(self) -> &'static str {
        match self {
            Self::Run => "run",
            Self::Coverage => "coverage",
        }
    }

    /// The name of a row's table (`[[mutation]]`, `[[flip]]`).
    #[must_use]
    pub const fn row(self) -> &'static str {
        match self {
            Self::Run => "mutation",
            Self::Coverage => "flip",
        }
    }

    /// The file name a corpus directory keeps a lock of this kind under.
    #[must_use]
    pub const fn file(self) -> &'static str {
        match self {
            Self::Run => LOCK_FILE,
            Self::Coverage => COVERAGE_LOCK_FILE,
        }
    }

    /// The kind of the lock `document`'s rendering is: a coverage document's is a coverage lock,
    /// every other a run's.
    fn of(document: &Value) -> Self {
        if document["schema"] == crate::coverage::COVERAGE_SCHEMA {
            Self::Coverage
        } else {
            Self::Run
        }
    }

    /// The rows of `document` a lock of this kind records: a run's mutations, a coverage
    /// document's flips.
    fn rows(self, document: &Value) -> &[Value] {
        let rows = match self {
            Self::Run => &document["mutations"],
            Self::Coverage => &document["families"]["flips"]["items"],
        };
        rows.as_array().map_or(&[][..], Vec::as_slice)
    }

    /// What the rendering writes of a row of `document` that a lock compares: `{status, killer,
    /// reason}` (a horizon is rendered, and compared only as the rendering's text).
    fn now(self, row: &Value) -> Value {
        match self {
            Self::Run => json!({
                "status": row["status"],
                "killer": row["killer"],
                "reason": crate::verdicts::rendered_reason(row),
            }),
            Self::Coverage => {
                let rendered = crate::verdicts::rendered_flip(row);
                json!({
                    "status": rendered["status"],
                    "killer": rendered["killer"],
                    "reason": rendered["reason"],
                })
            }
        }
    }
}

/// What a lock decodes to: each row's recorded facts, in the file's order.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Lock {
    /// What the lock records.
    pub kind: LockKind,
    /// The path the run reads and writes.
    pub path: PathBuf,
    /// The file's text; `None` when the file is absent.
    pub text: Option<String>,
    /// The rows, in the file's order.
    pub rows: Vec<LockRow>,
    /// The file's header: each key outside its rows (a section's as `section.key`, a coverage
    /// lock's family sections left out) with its value, read only to name what changed
    /// ([`header_values`]).
    pub header: BTreeMap<String, Value>,
    /// A coverage lock's open obligations by family (`[rules] open`, ...), read only to report
    /// what changed; empty for a run's.
    pub open: BTreeMap<String, Vec<String>>,
    /// A coverage lock's argued obligations by family (`[rules] argued`, ...), read only to
    /// report what changed; empty for a run's and for a lock written before arguments were
    /// rendered.
    pub argued: BTreeMap<String, Vec<String>>,
    /// A coverage lock's standing of each argued item (`[arguments]`), by id, read only to report
    /// what changed; empty for a run's and for a lock written before standings were rendered. A
    /// value that is not a string is left out, as an `open` that is not an array of strings is.
    pub arguments: BTreeMap<String, String>,
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

/// The section of a coverage lock that gives each argued item's standing.
const ARGUMENTS: &str = "arguments";

/// The next step of a lock that does not decode.
const REFUSED_NEXT: &str = "resolve the file, or delete it to start from the search's killers";

impl Lock {
    /// Read the run lock (`verdicts.lock`) at `path` ([`Lock::read_kind`]).
    pub fn read(path: &Path) -> Result<Self, String> {
        Self::read_kind(path, LockKind::Run)
    }

    /// Read the lock of `kind` at `path`: an absent file is an empty lock; a file that does not
    /// decode is the refusal's detail (module documentation).
    pub fn read_kind(path: &Path, kind: LockKind) -> Result<Self, String> {
        let refused = |what: String| format!("{}: {what}; {REFUSED_NEXT}", path.display());
        let text = match fs::read_to_string(path) {
            Ok(text) => text,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
                return Ok(Self {
                    kind,
                    path: path.to_path_buf(),
                    ..Self::default()
                });
            }
            Err(e) => return Err(refused(format!("cannot be read: {e}"))),
        };
        Self::decode(path, text, kind)
    }

    /// The lock of `kind` at `path` whose file's text is `text`; a text that does not decode is
    /// the refusal's detail ([`Lock::read_kind`]).
    fn decode(path: &Path, text: String, kind: LockKind) -> Result<Self, String> {
        let refused = |what: String| format!("{}: {what}; {REFUSED_NEXT}", path.display());
        let table: toml::Table = text
            .parse()
            .map_err(|e: toml::de::Error| refused(format!("is not TOML: {}", e.message())))?;
        if table.get("schema").and_then(toml::Value::as_str) != Some(VERDICTS_SCHEMA) {
            return Err(refused(format!("its schema is not {VERDICTS_SCHEMA:?}")));
        }
        let document = kind.document();
        if table.get("document").and_then(toml::Value::as_str) != Some(document) {
            return Err(refused(match kind {
                LockKind::Run => {
                    "its document is not \"run\": a lock is the verdicts of a run".to_owned()
                }
                LockKind::Coverage => "its document is not \"coverage\": a coverage lock is the \
                                       verdicts of a coverage command"
                    .to_owned(),
            }));
        }
        let noun = kind.row();
        let listed = match table.get(noun) {
            None => &[][..],
            Some(toml::Value::Array(rows)) => rows.as_slice(),
            Some(_) => return Err(refused(format!("its {noun} is not an array of tables"))),
        };
        let mut rows = Vec::with_capacity(listed.len());
        let mut seen = BTreeSet::new();
        for (index, row) in listed.iter().enumerate() {
            let Some(row) = row.as_table() else {
                return Err(refused(format!("{noun} {} is not a table", index + 1)));
            };
            let Some(id) = row.get("id").and_then(toml::Value::as_str) else {
                return Err(refused(format!("{noun} {} has no string id", index + 1)));
            };
            if !seen.insert(id.to_owned()) {
                return Err(refused(format!("the {noun} {id:?} is listed twice")));
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
        // A coverage lock's open and argued obligations: each family section's `open` and
        // `argued`, when it is an array of strings; read only to report what changed.
        let listed = |key: &str| match kind {
            LockKind::Run => BTreeMap::new(),
            LockKind::Coverage => table
                .iter()
                .filter(|(family, _)| crate::coverage::FAMILIES.contains(&family.as_str()))
                .filter_map(|(family, section)| {
                    let ids = section.get(key)?.as_array()?;
                    let ids = ids
                        .iter()
                        .map(|id| id.as_str().map(str::to_owned))
                        .collect::<Option<Vec<_>>>()?;
                    Some((family.clone(), ids))
                })
                .collect(),
        };
        let arguments = match kind {
            LockKind::Run => BTreeMap::new(),
            LockKind::Coverage => table
                .get(ARGUMENTS)
                .and_then(toml::Value::as_table)
                .into_iter()
                .flatten()
                .filter_map(|(id, standing)| Some((id.clone(), standing.as_str()?.to_owned())))
                .collect(),
        };
        Ok(Self {
            kind,
            path: path.to_path_buf(),
            text: Some(text),
            rows,
            header: header_values(&table, kind),
            open: listed("open"),
            argued: listed("argued"),
            arguments,
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
    /// `detail` when a write failed; the flag is false when it did. An entry a run the clock
    /// stopped could change keeps its recorded value ([`crate::clock`]: `clock_stopped`, `kept`),
    /// and under `--locked` a lock that differs in nothing else is `undecided`.
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
        // An entry a run the clock stopped decided keeps its recorded value: the lock compared
        // and written is the rendering of the document with those values ([`crate::clock`]).
        let clock = crate::clock::keep(self, document);
        let document = &clock.document;
        let text = match lock_text(document) {
            Ok(text) if LockKind::of(document) == self.kind => text,
            _ => return (self.not_written("refused"), true),
        };
        let kind = self.kind;
        let header = self
            .text
            .as_deref()
            .is_none_or(|old| head(kind, old) != head(kind, &text));
        let header_changes = self.header_changes(&text);
        let changes = self.changes(document, run.only);
        // Under `--only` the rows it did not select may differ from the file's: only the selected
        // rows and the header are compared, so no first difference of the whole file is named.
        let difference = if run.only.is_empty() {
            self.difference(&text)
        } else {
            Value::Null
        };
        let open = (kind == LockKind::Coverage).then(|| self.open_changes(document));
        let arguments = (kind == LockKind::Coverage).then(|| self.argument_changes(document));
        let value = |status: &str, reason: Option<&str>, header: bool, changes: Vec<Value>| {
            let mut value = json!({
                "path": path,
                "status": status,
                "reason": reason,
                "header": header,
                "header_changes": header_changes,
                "changes": changes,
                "difference": difference,
                "clock_stopped": clock.stopped,
                "kept": clock.kept,
            });
            if let Some(open) = &open {
                value["open_changes"] = json!(open);
            }
            if let Some(arguments) = &arguments {
                value["argument_changes"] = json!(arguments);
            }
            value
        };
        if run.locked {
            let differs = if run.only.is_empty() {
                self.text.as_deref() != Some(text.as_str())
            } else {
                header || !changes.is_empty()
            };
            // Not a difference, and not confirmed either: some entry rests on a run the clock
            // stopped, so this host cannot decide it.
            let status = if differs {
                "stale"
            } else if clock.stopped.is_empty() {
                "unchanged"
            } else {
                "undecided"
            };
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
        let rendered = Lock::read_text(text, self.kind);
        let (new_order, new_set) = ids(&mut rendered.into_iter());
        if old_order != new_order && old_set == new_set {
            let row = self.kind.row();
            let (old_ids, new_ids) = (id_lines(old, row), id_lines(text, row));
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
            .map(|table| header_values(&table, self.kind))
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

    /// The row ids (mutations, flips) of the rendering `text` of a lock of `kind`, in its order;
    /// none for a text that does not decode, which a rendering always does.
    fn read_text(text: &str, kind: LockKind) -> Vec<String> {
        let Ok(table) = text.parse::<toml::Table>() else {
            return Vec::new();
        };
        table
            .get(kind.row())
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
        for row in self.kind.rows(document) {
            let id = row["id"].as_str().unwrap_or_default();
            if !selected(id) {
                continue;
            }
            seen.insert(id.to_owned());
            let now = self.kind.now(row);
            let before = recorded.get(id).cloned();
            if before.as_ref() != Some(&now) {
                changes.push(json!({self.kind.row(): id, "recorded": before, "now": now}));
            }
        }
        for row in &self.rows {
            if selected(&row.id) && only.is_empty() && !seen.contains(&row.id) {
                changes.push(json!({
                    self.kind.row(): row.id,
                    "recorded": recorded[row.id.as_str()],
                    "now": null,
                }));
            }
        }
        changes
    }

    /// Each obligation of a coverage lock whose state differs between the lock and `document`:
    /// `{family, obligation, recorded, now}`, each side `"open"` or `"argued"` where that side
    /// lists it so and null where it lists it neither way (it is covered, or no longer an
    /// obligation), in family order, then the document's order, then the lock's order.
    fn open_changes(&self, document: &Value) -> Vec<Value> {
        // Each family's ids by state, on one side.
        let states = |open: Vec<(String, Vec<String>)>, argued: Vec<(String, Vec<String>)>| {
            let mut states = BTreeMap::<String, Vec<(String, &'static str)>>::new();
            for (family, ids) in open {
                let entry = states.entry(family).or_default();
                entry.extend(ids.into_iter().map(|id| (id, "open")));
            }
            for (family, ids) in argued {
                let entry = states.entry(family).or_default();
                entry.extend(ids.into_iter().map(|id| (id, "argued")));
            }
            states
        };
        let owned = |ids: Vec<(&'static str, Vec<String>)>| {
            ids.into_iter()
                .map(|(family, ids)| (family.to_owned(), ids))
                .collect::<Vec<_>>()
        };
        let now = states(
            owned(crate::coverage::open_ids(document)),
            owned(crate::coverage::argued_ids(document)),
        );
        let recorded = states(
            self.open.clone().into_iter().collect(),
            self.argued.clone().into_iter().collect(),
        );
        let mut changes = Vec::new();
        for family in crate::coverage::FAMILIES {
            let (recorded, current) = (recorded.get(family), now.get(family));
            let state = |ids: Option<&Vec<(String, &'static str)>>, id: &str| {
                ids.and_then(|ids| ids.iter().find(|(listed, _)| listed == id))
                    .map(|(_, state)| *state)
            };
            for (id, state_now) in current.into_iter().flatten() {
                let before = state(recorded, id);
                if before != Some(*state_now) {
                    changes.push(json!({"family": family, "obligation": id,
                                        "recorded": before, "now": state_now}));
                }
            }
            for (id, state_before) in recorded.into_iter().flatten() {
                if state(current, id).is_none() {
                    changes.push(json!({"family": family, "obligation": id,
                                        "recorded": state_before, "now": null}));
                }
            }
        }
        changes
    }

    /// Each argued item of a coverage lock whose standing differs between the lock's
    /// `[arguments]` and `document`: `{obligation, recorded, now}`, either side null where that side
    /// has no line for it, in the document's order, then the lock's ids the document does not argue,
    /// in id order.
    fn argument_changes(&self, document: &Value) -> Vec<Value> {
        let now = crate::coverage::argument_standings(document);
        let mut changes = Vec::new();
        for (id, standing) in &now {
            let recorded = self.arguments.get(id);
            if recorded != Some(standing) {
                changes.push(json!({"obligation": id, "recorded": recorded, "now": standing}));
            }
        }
        for (id, recorded) in &self.arguments {
            if !now.iter().any(|(argued, _)| argued == id) {
                changes.push(json!({"obligation": id, "recorded": recorded, "now": null}));
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
        "clock_stopped": [],
        "kept": [],
    })
}

/// The header of a decoded lock or rendering of `kind`: each key outside its rows (`[[mutation]]`,
/// `[[flip]]`) and, for a coverage lock, outside its family sections (`[rules]`, ...; [`head`])
/// and its `[arguments]`,
/// a section's keys as `section.key`, with its value as JSON (a string, an integer or a boolean
/// as itself, any other value as its TOML text).
fn header_values(table: &toml::Table, kind: LockKind) -> BTreeMap<String, Value> {
    let json = |value: &toml::Value| match value {
        toml::Value::String(text) => json!(text),
        toml::Value::Integer(number) => json!(number),
        toml::Value::Boolean(flag) => json!(flag),
        other => json!(other.to_string()),
    };
    let mut header = BTreeMap::new();
    for (key, value) in table {
        match value {
            _ if key == kind.row() => {}
            toml::Value::Table(_)
                if kind == LockKind::Coverage
                    && (crate::coverage::FAMILIES.contains(&key.as_str()) || key == ARGUMENTS) => {}
            toml::Value::Table(section) => {
                for (inner, value) in section {
                    header.insert(format!("{key}.{inner}"), json(value));
                }
            }
            value => {
                header.insert(key.clone(), json(value));
            }
        }
    }
    header
}

/// The header keys of a rendering's text, in the order of its lines, as [`header_values`]
/// names them: a key before any table, or `section.key` in a `[section]`; none in a
/// `[[mutation]]` row, and none from the continuation lines of a multi-line array (a value, a
/// string or an inline table, or its closing `]`), which belong to the key that opened it, nor
/// from a line whose key is quoted (an `[arguments]` line, whose key is an item id): the
/// rendering quotes no header key, so such a line is no header line, and [`header_values`]
/// leaves its section out.
fn header_key_order(text: &str) -> Vec<String> {
    let mut keys = Vec::new();
    let mut section: Option<&str> = Some("");
    for line in text.split('\n') {
        let trimmed = line.trim();
        if trimmed.starts_with(['"', '{', ']']) {
            continue;
        }
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

/// The `id` line of each `[[<row>]]` row of a lock's text (`[[mutation]]`, `[[flip]]`), in order,
/// with its line number counted from 1: the first line of the row's table that sets `id`.
fn id_lines<'t>(text: &'t str, row: &str) -> Vec<(u64, &'t str)> {
    let table = format!("[[{row}]]");
    let mut lines = Vec::new();
    let mut in_row = false;
    for (number, line) in (1_u64..).zip(text.split('\n')) {
        let trimmed = line.trim();
        if trimmed.starts_with('[') {
            in_row = trimmed == table;
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

/// The header of a rendering of a lock of `kind`: a run's lines before its first `[[mutation]]`
/// (the header and the `[spec]` section), a coverage document's before its first family section
/// or `[[flip]]` (the header, the `[spec]` and the `[settings]`).
fn head(kind: LockKind, text: &str) -> &str {
    let end = match kind {
        LockKind::Run => text.find("\n[[mutation]]"),
        LockKind::Coverage => text.match_indices("\n[").map(|(at, _)| at).find(|&at| {
            let line = text[at + 1..].lines().next().unwrap_or_default();
            line == "[[flip]]"
                || line == "[arguments]"
                || crate::coverage::FAMILIES.iter().any(|family| {
                    line.strip_prefix('[').and_then(|l| l.strip_suffix(']')) == Some(family)
                })
        }),
    };
    end.map_or(text, |end| &text[..end])
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
/// killed -> survived`, and for a coverage lock one per obligation whose openness differs
/// (`lock.open_changes`: `coverage.lock: rules: rule:x is open`, `coverage.lock: requirements:
/// requirement:x:held is no longer open`, `coverage.lock: rules: rule:x is argued (was open)`)
/// and one per argued item whose standing differs where no such line names it
/// (`lock.argument_changes`: `coverage.lock: arguments: rule:x: text -> unchecked`) before them;
/// when neither the header nor any obligation nor any standing nor any row's verdict differs,
/// one line naming the first difference
/// (`lock.difference`: the rows' order, or a line of text); empty otherwise.
#[must_use]
pub fn stale_lines(document: &Value) -> Vec<String> {
    let lock = &document["lock"];
    if lock["status"] != "stale" {
        return Vec::new();
    }
    let kind = LockKind::of(document);
    let path = lock["path"].as_str().unwrap_or(kind.file());
    let mut lines = Vec::new();
    if lock["header"] == true {
        let header_changes = lock["header_changes"]
            .as_array()
            .map_or(&[][..], Vec::as_slice);
        if header_changes.is_empty() {
            let first = match kind {
                LockKind::Run => "its first mutation",
                LockKind::Coverage => "its first family",
            };
            lines.push(format!(
                "{path}: the header differs (the file is absent, or a comment or spacing before \
                 {first} differs)"
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
    let rows = kind.rows(document);
    let changes = lock["changes"].as_array().map_or(&[][..], Vec::as_slice);
    let open = lock["open_changes"]
        .as_array()
        .map_or(&[][..], Vec::as_slice);
    // A standing whose item an obligation's or a row's change already names moved with the item's
    // argued state (an argument added or removed): that line says so.
    let named = open
        .iter()
        .map(|change| &change["obligation"])
        .chain(changes.iter().map(|change| &change[kind.row()]))
        .filter_map(Value::as_str)
        .collect::<BTreeSet<_>>();
    let arguments = lock["argument_changes"]
        .as_array()
        .into_iter()
        .flatten()
        .filter(|change| {
            change["obligation"]
                .as_str()
                .is_some_and(|id| !named.contains(id))
        })
        .collect::<Vec<_>>();
    // A file that differs neither in its header nor in an obligation nor in a standing nor in a
    // row's verdict differs in its row order or its text: the first difference says which.
    let difference = &lock["difference"];
    if lock["header"] != true
        && changes.is_empty()
        && open.is_empty()
        && arguments.is_empty()
        && difference.is_object()
    {
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
        let (order, written) = match kind {
            LockKind::Run => ("the mutation list's", "the list's order"),
            LockKind::Coverage => ("the flips family's", "the family's order"),
        };
        lines.push(if difference["kind"] == "order" {
            format!(
                "{path}: its rows are in another order than {order} (first at {at}); a run \
                 writes them in {written}"
            )
        } else {
            format!(
                "{path}: it differs from the rendering the run would write at {at} (a comment, \
                 spacing, or a key the rendering does not write); a run rewrites it"
            )
        });
    }
    for change in open {
        let (family, id) = (
            change["family"].as_str().unwrap_or("?"),
            change["obligation"].as_str().unwrap_or("?"),
        );
        let what = match (change["recorded"].as_str(), change["now"].as_str()) {
            (Some(before), None) => format!("is no longer {before}"),
            (None, Some(now)) => format!("is {now}"),
            (Some(before), Some(now)) => format!("is {now} (was {before})"),
            (None, None) => "is unchanged".to_owned(),
        };
        lines.push(format!("{path}: {family}: {id} {what}"));
    }
    for change in arguments {
        let side = |value: &Value| value.as_str().unwrap_or("none").to_owned();
        lines.push(format!(
            "{path}: arguments: {}: {} -> {}",
            change["obligation"].as_str().unwrap_or("?"),
            side(&change["recorded"]),
            side(&change["now"])
        ));
    }
    for change in changes {
        let id = change[kind.row()].as_str().unwrap_or("?");
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
                    .iter()
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
        lock_of(text, LockKind::Run)
    }

    fn lock_of(text: &str, kind: LockKind) -> Lock {
        let path = PathBuf::from(kind.file());
        let rows = Lock::read_text(text, kind)
            .into_iter()
            .map(|id| LockRow {
                id,
                ..LockRow::default()
            })
            .collect();
        Lock {
            kind,
            path,
            text: Some(text.to_owned()),
            rows,
            header: header_values(&text.parse().unwrap(), kind),
            open: BTreeMap::new(),
            argued: BTreeMap::new(),
            arguments: BTreeMap::new(),
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

    /// A coverage lock whose arrays have one value per line, as the rendering writes them
    /// ([`crate::verdicts`]), reads as the same lock with each array on one line: the same head,
    /// header values and header key order (a value holding `=` names no key), the same rows and
    /// row `id` lines (at their own line numbers), and a reordering of its rows is named as one,
    /// at the first reordered row's `id` line.
    #[test]
    fn a_multi_line_lock_reads_as_its_one_line_form() {
        let one_line = |items: &[&str]| format!("[{}]", items.join(", "));
        let multi_line = |items: &[&str]| {
            crate::verdicts::list(
                &items
                    .iter()
                    .map(|&item| item.to_owned())
                    .collect::<Vec<_>>(),
            )
        };
        let render = |array: &dyn Fn(&[&str]) -> String, first: &str, second: &str| {
            format!(
                "schema = \"kink-flow-verdicts\"\nversion = 23\ndocument = \"coverage\"\n\n\
                 [settings]\ntiers = [1, 2]\ndepth = 1\nmcdc = {}\n\n[rules]\nopen = {}\n\
                 argued = {}\n\n[syntax]\nopen = {}\nargued = {}\n\n[flips]\nrun = true\n\n\
                 [[flip]]\nid = \"{first}\"\nstatus = \"undistinguished\"\nhorizon = {}\n\n\
                 [[flip]]\nid = \"{second}\"\nstatus = \"argued\"\n",
                array(&["\"GUARDS.wake\""]),
                array(&["\"rule:GUARDS.wake\"", "\"rule:GUARDS.high\""]),
                array(&[]),
                array(&["\"syntax:crate::decode_ld:r=2\""]),
                array(&[]),
                array(&[
                    "{ program = \"run\", channel = \"clock\", elements = 16, opening = \"bound\" }"
                ]),
            )
        };
        let (one, multi) = (render(&one_line, "a", "b"), render(&multi_line, "a", "b"));
        assert!(
            multi.contains("\n[rules]\nopen = [\n  \"rule:GUARDS.wake\",\n"),
            "{multi}"
        );
        assert!(multi.contains("\nargued = [\n]\n"), "{multi}");
        let kind = LockKind::Coverage;
        let table = |text: &str| text.parse::<toml::Table>().unwrap();
        assert_eq!(table(&multi), table(&one));
        assert_eq!(table(head(kind, &multi)), table(head(kind, &one)));
        assert!(head(kind, &multi).ends_with("mcdc = [\n  \"GUARDS.wake\",\n]\n"));
        assert_eq!(
            header_values(&table(&multi), kind),
            header_values(&table(&one), kind)
        );
        assert_eq!(header_key_order(&multi), header_key_order(&one));
        let lines = |text: &str| {
            id_lines(text, kind.row())
                .into_iter()
                .map(|(_, line)| line.to_owned())
                .collect::<Vec<_>>()
        };
        assert_eq!(lines(&multi), lines(&one));
        for (number, line) in id_lines(&multi, kind.row()) {
            assert_eq!(
                multi.split('\n').nth(usize::try_from(number).unwrap() - 1),
                Some(line)
            );
        }
        assert_eq!(Lock::read_text(&multi, kind), Lock::read_text(&one, kind));
        assert_eq!(lock_of(&multi, kind).difference(&multi), Value::Null);
        for (array, now) in [
            (&one_line as &dyn Fn(&[&str]) -> String, &one),
            (&multi_line, &multi),
        ] {
            let reordered = render(array, "b", "a");
            let (line, _) = id_lines(&reordered, kind.row())[0];
            assert_eq!(
                lock_of(&reordered, kind).difference(now),
                json!({"kind": "order", "line": line, "recorded": "id = \"b\"", "now": "id = \"a\""})
            );
        }
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

    /// A coverage lock reads `[arguments]` as each argued item's standing, outside its header:
    /// the lines, whose keys are quoted item ids, give no header key and are no part of the head.
    /// A standing that moves makes a `--locked` run stale, with no header change: the lock's
    /// state names the item (`argument_changes`) and the line (`difference`), and `stale_lines`
    /// names the move. An argument added with its item names the item once, by the obligation's
    /// change.
    #[test]
    fn a_moved_standing_makes_the_lock_stale_and_names_its_line() {
        let document = |argued: &[(&str, &str)], open: &[&str]| {
            let mut items = argued
                .iter()
                .map(|(id, standing)| {
                    json!({"id": id, "status": "argued", "argument_check": {"standing": standing}})
                })
                .collect::<Vec<_>>();
            items.extend(open.iter().map(
                |id| json!({"id": id, "status": "matched", "obligation": true, "covered": false}),
            ));
            json!({
                "schema": crate::coverage::COVERAGE_SCHEMA,
                "spec": {"outcome": "admitted"},
                "settings": {"tiers": [1], "depth": 1, "mcdc": []},
                "families": {
                    "rules": {"items": items},
                    "requirements": {"items": []},
                    "syntax": {"items": []},
                    "flips": {"run": false},
                },
            })
        };
        let text = |document: &Value| lock_text(document).unwrap();
        let recorded = document(&[("rule:a", "text"), ("rule:b", "text")], &[]);
        let recorded_text = text(&recorded);
        assert!(
            recorded_text.contains(
                "\n[arguments]\n\"rule:a\" = \"text\"\n\"rule:b\" = \"text\"\n\n[flips]\n"
            ),
            "{recorded_text}"
        );
        let kind = LockKind::Coverage;
        let lock =
            Lock::decode(Path::new(COVERAGE_LOCK_FILE), recorded_text.clone(), kind).unwrap();
        assert_eq!(
            lock.arguments,
            BTreeMap::from([
                ("rule:a".to_owned(), "text".to_owned()),
                ("rule:b".to_owned(), "text".to_owned()),
            ])
        );
        assert!(
            lock.header.keys().all(|key| !key.starts_with("arguments")),
            "{:?}",
            lock.header
        );
        assert!(
            header_key_order(&recorded_text)
                .iter()
                .all(|key| !key.starts_with("arguments")),
            "{recorded_text}"
        );
        assert!(!head(kind, &recorded_text).contains("[arguments]"));

        let store = Store::new("/nonexistent");
        let locked = Settle {
            locked: true,
            verify: false,
            only: &[],
            stopped: false,
        };
        let (same, _) = lock.settle(&store, &recorded, locked);
        assert_eq!(same["status"], "unchanged", "{same:#}");
        assert_eq!(same["argument_changes"], json!([]));

        let moved = document(&[("rule:a", "text"), ("rule:b", "unchecked")], &[]);
        let (stale, _) = lock.settle(&store, &moved, locked);
        assert_eq!(
            (&stale["status"], &stale["header"], &stale["header_changes"]),
            (&json!("stale"), &json!(false), &json!([])),
            "{stale:#}"
        );
        assert_eq!(
            stale["argument_changes"],
            json!([{"obligation": "rule:b", "recorded": "text", "now": "unchecked"}])
        );
        let line = recorded_text
            .split('\n')
            .position(|line| line == "\"rule:b\" = \"text\"")
            .unwrap()
            + 1;
        assert_eq!(
            stale["difference"],
            json!({"kind": "text", "line": line, "recorded": "\"rule:b\" = \"text\"",
                   "now": "\"rule:b\" = \"unchecked\""})
        );
        let mut with_lock = moved.clone();
        with_lock["lock"] = stale;
        assert_eq!(
            stale_lines(&with_lock),
            ["coverage.lock: arguments: rule:b: text -> unchecked"]
        );

        // An argument removed: its item's obligation names it, and its standing's line is not
        // named again.
        let reopened = document(&[("rule:a", "text")], &["rule:b"]);
        let (stale, _) = lock.settle(&store, &reopened, locked);
        assert_eq!(
            stale["argument_changes"],
            json!([{"obligation": "rule:b", "recorded": "text", "now": null}])
        );
        let mut with_lock = reopened.clone();
        with_lock["lock"] = stale;
        assert_eq!(
            stale_lines(&with_lock),
            ["coverage.lock: rules: rule:b is open (was argued)"]
        );

        // A line removed by hand, the item still argued: the standing's change names it.
        let edited = recorded_text.replace("\"rule:b\" = \"text\"\n", "");
        let lock = Lock::decode(Path::new(COVERAGE_LOCK_FILE), edited, kind).unwrap();
        let (stale, _) = lock.settle(&store, &recorded, locked);
        let mut with_lock = recorded.clone();
        with_lock["lock"] = stale;
        assert_eq!(
            stale_lines(&with_lock),
            ["coverage.lock: arguments: rule:b: none -> text"]
        );
    }

    /// A coverage lock recorded at verdicts version 20 has no `[arguments]`: a run that argues
    /// items finds it stale, the header's `version` and each argued item's standing named, and
    /// the obligations unchanged.
    #[test]
    fn a_version_20_lock_without_arguments_is_stale_and_names_each_standing() {
        let document = json!({
            "schema": crate::coverage::COVERAGE_SCHEMA,
            "spec": {"outcome": "admitted"},
            "settings": {"tiers": [1], "depth": 1, "mcdc": []},
            "families": {
                "rules": {"items": [
                    {"id": "rule:a", "status": "argued", "argument_check": {"standing": "text"}},
                    {"id": "rule:b", "status": "argued",
                     "argument_check": {"standing": "unchecked", "invariant": "i"}},
                ]},
                "requirements": {"items": []},
                "syntax": {"items": []},
                "flips": {"run": false},
            },
        });
        let now = lock_text(&document).unwrap();
        let section = "\n[arguments]\n\"rule:a\" = \"text\"\n\"rule:b\" = \"unchecked\"\n";
        assert!(now.contains(section), "{now}");
        let recorded = now.replace(section, "").replace(
            &format!("\nversion = {}\n", crate::verdicts::VERDICTS_VERSION),
            "\nversion = 20\n",
        );
        assert!(recorded.contains("\nversion = 20\n") && !recorded.contains("[arguments]"));
        let kind = LockKind::Coverage;
        let lock = Lock::decode(Path::new(COVERAGE_LOCK_FILE), recorded, kind).unwrap();
        assert!(lock.arguments.is_empty());
        let locked = Settle {
            locked: true,
            verify: false,
            only: &[],
            stopped: false,
        };
        let (stale, _) = lock.settle(&Store::new("/nonexistent"), &document, locked);
        assert_eq!(stale["status"], "stale", "{stale:#}");
        assert_eq!(stale["open_changes"], json!([]));
        assert_eq!(
            stale["argument_changes"],
            json!([
                {"obligation": "rule:a", "recorded": null, "now": "text"},
                {"obligation": "rule:b", "recorded": null, "now": "unchecked"},
            ])
        );
        let mut with_lock = document.clone();
        with_lock["lock"] = stale;
        assert_eq!(
            stale_lines(&with_lock),
            [
                format!(
                    "coverage.lock: the header's version differs: recorded 20, now {} (another \
                     version of the rendering)",
                    crate::verdicts::VERDICTS_VERSION
                ),
                "coverage.lock: arguments: rule:a: none -> text".to_owned(),
                "coverage.lock: arguments: rule:b: none -> unchecked".to_owned(),
            ]
        );
    }
}
