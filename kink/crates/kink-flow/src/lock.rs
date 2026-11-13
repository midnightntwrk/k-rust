//! The corpus record, `kink.lock` (`run --lock FILE`, `coverage --lock FILE`, `compare --lock
//! FILE`, `query --lock FILE`): one file, one section per command. `[run]` holds the killer
//! record, one recorded killer per killed mutation, kept while it still kills; `[coverage]` holds
//! the coverage lock, one recorded killer per distinguished flip by the same rule, with each
//! family's open and argued obligations; `[compare]` holds one verdict per (implementation,
//! program, view) of the corpus's other implementations ([`crate::compare`]); `[query]` holds one
//! obligation per pattern of the pattern list, its status and, for a hit, its one recorded
//! witness, kept while it still hits ([`crate::query`], [`LockKind`]).
//!
//! Each command owns its section. It reads only its own, compares only its own under `--locked`,
//! and rewrites only its own, keeping the other sections' text byte for byte, so that
//! `coverage --locked` is unaffected by a stale `[run]`, and the reverse. A file with no section
//! for a command records nothing for it: a first `coverage` after only `run`s is no error.
//!
//! The header, before the first section, holds only what is the same for every section by
//! construction: the comment that says what the file is, `schema`, and, for a flow that names its
//! definition (a KRS flow, [`crate::manifest::KrsSpec::name`]), `definition = "PACKAGE:FACET"`.
//! Every section of a record is a function of one definition (a mutation is a patch of its K, an
//! obligation is one of its rules, a verdict compares its ends), so the record says which: a
//! record that does not name its subject can be overwritten by another's. A command whose flow
//! is for another definition than the one the file names is refused before anything runs, with
//! or without `--locked` ([`Lock::for_definition`]). A K flow's record names none, its `[spec]`
//! being the specification itself. Every value a verdict
//! depends on, the rendering's `version`, the solver `profile`, the Z3 build and the
//! specification's admission, is in each section: each command writes its section at its own
//! time, on the build it runs on, and keeps the other as it is, so a value said once would be
//! wrong for the section the last command did not write, and a `run` on another Z3 build would
//! make `coverage --locked` stale for a change `coverage` did not make.
//!
//! A section is the lines from its `[run]`, `[coverage]`, `[compare]` or `[query]` line to the next such line
//! (or the end of the file), trailing blank lines aside: it is the command's verdicts rendering
//! after the record's header ([`crate::verdicts::lock_section`]), so a file only one command has
//! written is that command's `--output verdicts` (for `run`, without `killed_by`).
//!
//! A command writes its section by a read-modify-write under an exclusive lock of the file's
//! directory: it reads the file again, keeps the other sections' text, writes the whole file to a
//! temporary name in the directory and renames it over the file ([`Store::write_text`]), then
//! releases the lock. Two commands that write at once each find the other's section in the file
//! they rewrite, so neither loses it; a reader never sees a part-written file.
//!
//! The record is an input. A run reads one fact from it: for each mutation id, the program id it
//! names as killer, which the search tries first ([`crate::search`], tier 2). Every status still
//! comes from runs or from tier-1 records; no status, cell or key is read from the record, so a
//! hand-edited or stale record can change which program is tried first, and so the cost and the
//! reported killer, but never a status. A query reads the same kind of fact from its section: for
//! each pattern id, the program id it names as witness, which the query asks first
//! ([`crate::query`]); a status is never read, and the witness is asked again on every query.
//!
//! The record is also an output: after a run that judged every mutation of its list its section
//! is rewritten ([`Lock::settle`]), so it states the verdicts of the current inputs. Its text is
//! the run's verdicts rendering without `killed_by`, so a first-kill run and a full run write the
//! same bytes, and each killed mutation's `killer` is a function of the record before the run and
//! of the inputs (the corpus, the definition, the mutation list, the budget, the solver profile
//! and kink's build), never of the cache, the host's clock (while no `budget.time_ms` bound
//! fires) or the order work was done in.
//!
//! Reading tolerates any version: `schema` must be `kink-flow-verdicts`, the command's section,
//! where there is one, must be a table and begin with its own `[run]`, `[coverage]`, `[compare]` or
//! `[query]` line, and each row (`[[run.mutation]]`, `[[coverage.flip]]`) must have a string `id`
//! and may have a string `killer`, each `[[query.pattern]]` a string `id` and may have a string
//! `witness`, and each `[[compare.verdict]]` a string `implementation`, `program` and `view`; its `status` (`verdict`), `reason` and `difference`, when they are strings, are read
//! only to report what changed. A file that is not TOML, has another schema, or repeats an id does
//! not decode, and the command is refused ([`Lock::read`]).
//!
//! A lock written before version 24 is one command's rendering at the top of its file
//! (`document = "run"` or `"coverage"`, the rows `[[mutation]]` or `[[flip]]`, a coverage lock's
//! standings under `[arguments]` and its argued ids bare). It is still read, as the section of the
//! command it names: a command without `--locked` keeps its killers and rewrites the file in the
//! current layout, which then holds that command's section alone, as the old file held nothing
//! else. A file of the other command's is refused, since rewriting it would lose that command's
//! record. A front end that kept the two commands' locks in their own files names the old file
//! beside the record ([`Lock::adopt_legacy`]): while the record has no section for the command,
//! its killers are read from the old file, and the next write moves them into the record.
//!
//! Under `--locked` a lock whose section is of another version is refused, naming the command
//! that rewrites it ([`Lock::refuse_other_version`]): another version writes other bytes for the
//! same verdicts, so the check could only fail, and a command without `--locked` reads its killers
//! and rewrites it. So is an old file a front end names, while it is there.

use crate::verdicts::{ASSUMED_TOTALS, VERDICTS_SCHEMA, lock_section_with, record_header};
use kink_corpus::Store;
use serde_json::{Map, Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
};

/// The record's file name in a corpus directory, the path the krs front end gives `run --lock`
/// and `coverage --lock` (kink-flow itself has no default path): kink's record of the corpus,
/// named for the tool, as `Cargo.lock` is for Cargo, since it holds every command's section.
pub const LOCK_FILE: &str = "kink.lock";

/// The file a corpus directory kept `run`'s killer record in before version 24, which the krs
/// front end names beside [`LOCK_FILE`] ([`Lock::adopt_legacy`]).
pub const LEGACY_RUN_LOCK_FILE: &str = "verdicts.lock";

/// The file a corpus directory kept the coverage lock in before version 24.
pub const LEGACY_COVERAGE_LOCK_FILE: &str = "coverage.lock";

/// Which command's section of the record a lock is: a run's verdicts (`[run]`), one row per
/// mutation, a coverage command's (`[coverage]`), one row per flip, a compare command's
/// (`[compare]`), one row per (implementation, program, view), or a query command's (`[query]`),
/// one row per pattern (module documentation).
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum LockKind {
    /// `run --lock`: `[run]`, `[[run.mutation]]` rows.
    #[default]
    Run,
    /// `coverage --lock`: `[coverage]`, `[[coverage.flip]]` rows.
    Coverage,
    /// `compare --lock`: `[compare]`, `[[compare.verdict]]` rows, each keyed by its
    /// `implementation`, `program` and `view` rather than an `id` ([`row_id`]).
    Compare,
    /// `query --lock`: `[query]`, `[[query.pattern]]` rows, each a pattern's obligation, with its
    /// recorded `witness` where it is a hit.
    Query,
}

/// The sections of a record, in the order a record writes them.
const SECTIONS: [LockKind; 4] = [
    LockKind::Run,
    LockKind::Coverage,
    LockKind::Compare,
    LockKind::Query,
];

impl LockKind {
    /// The command, and the name of its section (`run`, `coverage`); a lock before version 24
    /// named it as its `document`.
    #[must_use]
    pub const fn document(self) -> &'static str {
        match self {
            Self::Run => "run",
            Self::Coverage => "coverage",
            Self::Compare => "compare",
            Self::Query => "query",
        }
    }

    /// The name of a row's table inside the section (`mutation`, `flip`, `verdict`, `pattern`).
    #[must_use]
    pub const fn row(self) -> &'static str {
        match self {
            Self::Run => "mutation",
            Self::Coverage => "flip",
            Self::Compare => "verdict",
            Self::Query => "pattern",
        }
    }

    /// The old file a corpus directory kept this command's lock in before version 24; none for
    /// `compare` and `query`, whose sections are newer than the record.
    #[must_use]
    pub const fn legacy_file(self) -> Option<&'static str> {
        match self {
            Self::Run => Some(LEGACY_RUN_LOCK_FILE),
            Self::Coverage => Some(LEGACY_COVERAGE_LOCK_FILE),
            Self::Compare | Self::Query => None,
        }
    }

    /// The section's first line (`[run]`, `[coverage]`, `[compare]`, `[query]`).
    fn heading(self) -> &'static str {
        match self {
            Self::Run => "[run]",
            Self::Coverage => "[coverage]",
            Self::Compare => "[compare]",
            Self::Query => "[query]",
        }
    }

    /// The key whose line opens a row's table in the rendering: `id`, and for a compare row
    /// `implementation`, the first of its three keys.
    const fn key_line(self) -> &'static str {
        match self {
            Self::Run | Self::Coverage | Self::Query => "id",
            Self::Compare => "implementation",
        }
    }

    /// The kind of the lock `document`'s rendering is: a coverage document's is a coverage lock,
    /// a compare document's a compare lock, a query document's a query lock, every other a run's.
    pub(crate) fn of(document: &Value) -> Self {
        if document["schema"] == crate::coverage::COVERAGE_SCHEMA {
            Self::Coverage
        } else if document["schema"] == crate::compare::COMPARE_SCHEMA {
            Self::Compare
        } else if document["schema"] == crate::query::QUERY_SCHEMA {
            Self::Query
        } else {
            Self::Run
        }
    }

    /// The rows of `document` a lock of this kind records: a run's mutations, a coverage
    /// document's flips, a compare document's verdict rows as the lock holds them
    /// (`verdicts`, which [`crate::compare::keep`] sets on the document a lock settles), a query
    /// document's obligations.
    fn rows(self, document: &Value) -> &[Value] {
        let rows = match self {
            Self::Run => &document["mutations"],
            Self::Coverage => &document["families"]["flips"]["items"],
            Self::Compare => &document["verdicts"],
            Self::Query => &document["obligations"],
        };
        rows.as_array().map_or(&[][..], Vec::as_slice)
    }

    /// What the rendering writes of a row of `document` that a lock compares: `{status, killer,
    /// reason}` (a horizon is rendered, and compared only as the rendering's text); for a
    /// compare row `{verdict, reason, difference}`, with `horizon` where the row has one (its
    /// digests are compared as the rendering's text); for a query row `{status, witness}`.
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
            Self::Compare => {
                let mut now = json!({
                    "verdict": row["verdict"],
                    "reason": row["reason"],
                    "difference": row["difference"],
                });
                if let Some(horizon) = row["horizon"].as_str() {
                    now["horizon"] = json!(horizon);
                }
                now
            }
            Self::Query => json!({"status": row["status"], "witness": row["witness"]}),
        }
    }

    /// The members that name the row `id` in a change or a kept entry: `{mutation: id}`,
    /// `{flip: id}`, `{pattern: id}`, and for a compare row `{implementation, program, view}`.
    pub(crate) fn keyed(self, id: &str) -> Map<String, Value> {
        let mut keyed = Map::new();
        match self {
            Self::Run | Self::Coverage | Self::Query => {
                keyed.insert(self.row().into(), json!(id));
            }
            Self::Compare => {
                let parts: Vec<String> = serde_json::from_str(id).unwrap_or_default();
                for (key, part) in ["implementation", "program", "view"].iter().zip(parts) {
                    keyed.insert((*key).into(), json!(part));
                }
            }
        }
        keyed
    }

    /// How a line names the row a change or kept entry names ([`LockKind::keyed`]): its id, and
    /// for a compare row `IMPLEMENTATION PROGRAM VIEW`, as `compare --output text` does.
    pub(crate) fn named(self, entry: &Value) -> String {
        match self {
            Self::Run | Self::Coverage | Self::Query => {
                entry[self.row()].as_str().unwrap_or("?").to_owned()
            }
            Self::Compare => ["implementation", "program", "view"]
                .iter()
                .map(|key| entry[*key].as_str().unwrap_or("?"))
                .collect::<Vec<_>>()
                .join(" "),
        }
    }
}

/// The id of a compare row, its `(implementation, program, view)` as one JSON array: a function
/// of the three that no two rows share, whatever their names hold.
#[must_use]
pub fn compare_row_id(implementation: &str, program: &str, view: &str) -> String {
    json!([implementation, program, view]).to_string()
}

/// The id of a row of a `kind` section as TOML: its `id`, and for a compare row its three keys
/// ([`compare_row_id`]); `None` where one is not a string.
fn row_id(kind: LockKind, row: &toml::Table) -> Option<String> {
    let string = |key: &str| row.get(key).and_then(toml::Value::as_str);
    match kind {
        LockKind::Run | LockKind::Coverage | LockKind::Query => string("id").map(str::to_owned),
        LockKind::Compare => Some(compare_row_id(
            string("implementation")?,
            string("program")?,
            string("view")?,
        )),
    }
}

/// What a lock decodes to: the command's section's recorded facts, each row in the file's order.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Lock {
    /// The command whose section this is.
    pub kind: LockKind,
    /// The path the command reads and writes.
    pub path: PathBuf,
    /// The file's text; `None` when the file is absent.
    pub text: Option<String>,
    /// The command's section's text, from its `[run]` or `[coverage]` line, ending with one
    /// newline; `None` when the file has none (it is absent, only the other command wrote it, or
    /// it is a lock before version 24).
    pub section: Option<String>,
    /// The line of the file, counted from 1, that `section` starts at.
    pub section_line: u64,
    /// The rows, in the file's order.
    pub rows: Vec<LockRow>,
    /// The section's header: each key outside its rows (a sub-table's as `table.key`, a coverage
    /// section's families left out) with its value, read only to name what changed
    /// ([`header_values`]).
    pub header: BTreeMap<String, Value>,
    /// A coverage section's open obligations by family (`[coverage.rules] open`, ...), read only
    /// to report what changed; empty for a run's.
    pub open: BTreeMap<String, Vec<String>>,
    /// A coverage section's argued obligations by family (each entry's `id`, or the bare id a
    /// lock before version 24 writes), read only to report what changed; empty for a run's and for
    /// a lock written before arguments were rendered.
    pub argued: BTreeMap<String, Vec<String>>,
    /// A coverage section's standing of each argued item (an `argued` entry's `standing`, an
    /// argued flip's; `[arguments]` before version 24), by id, read only to report what changed;
    /// empty for a run's and for a lock written before standings were rendered. A value that is
    /// not a string is left out, as an `open` that is not an array of ids is.
    pub arguments: BTreeMap<String, String>,
    /// The old file a front end kept this command's lock in, where it is still there
    /// ([`Lock::adopt_legacy`]).
    pub legacy: Option<Legacy>,
    /// The definition the command's flow is for, which a write states in the record's header
    /// ([`Lock::for_definition`]); `None` for a K flow.
    pub definition: Option<String>,
    /// The definition the file's header names; `None` when the file is absent or names none (a K
    /// flow's record, or one written before version 28).
    pub recorded_definition: Option<String>,
    /// The definition's assumed totalities, each its symbol and its reason
    /// ([`Lock::with_assumed_totals`]), which a write states in the command's section.
    pub assumed_totals: Vec<(String, String)>,
}

/// An old file a front end kept a command's lock in before version 24, still beside the record.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Legacy {
    /// Its path.
    pub path: PathBuf,
    /// Whether the record had no section for the command, so the recorded facts were read from
    /// it, and the next write moves them into the record.
    pub migrated: bool,
}

/// One row of a lock's section (`[[run.mutation]]`, `[[coverage.flip]]`, `[[compare.verdict]]`,
/// `[[query.pattern]]`).
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct LockRow {
    /// The row's `id`; a compare row's [`compare_row_id`].
    pub id: String,
    /// The recorded killer of a run or coverage row, the one fact a run reads; none in a compare
    /// or a query row.
    pub killer: Option<String>,
    /// The recorded witness of a query row, the one fact a query reads; none in every other row.
    pub witness: Option<String>,
    /// The recorded status (a compare row's `verdict`) and reason, read only to report what
    /// changed.
    pub status: Option<String>,
    pub reason: Option<String>,
    /// A compare row's first difference, as the section writes it; read only to report what
    /// changed.
    pub difference: Option<String>,
    /// A compare row's horizon (an `agree-up-to` verdict's), as the section writes it; read only
    /// to report what changed. None in every other row.
    pub horizon: Option<String>,
}

impl LockRow {
    /// What a lock compares of the recorded row ([`LockKind::now`]'s shape for `kind`).
    fn recorded(&self, kind: LockKind) -> Value {
        match kind {
            LockKind::Run | LockKind::Coverage => {
                json!({"status": self.status, "killer": self.killer, "reason": self.reason})
            }
            LockKind::Query => json!({"status": self.status, "witness": self.witness}),
            LockKind::Compare => {
                let mut recorded = json!({"verdict": self.status, "reason": self.reason,
                       "difference": self.difference});
                if let Some(horizon) = &self.horizon {
                    recorded["horizon"] = json!(horizon);
                }
                recorded
            }
        }
    }
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

/// The table of a coverage lock written before version 24 that gave each argued item's
/// standing, one `"<id>" = "<standing>"` line per item; read only to report what changed, and
/// left out of the header.
const LEGACY_ARGUMENTS: &str = "arguments";

/// The next step of a lock that does not decode.
const REFUSED_NEXT: &str = "resolve the file, or delete it to start from the search's killers";

/// How [`Lock::write_section`] left the file.
enum Outcome {
    /// The file already held the text it would write.
    Unchanged,
    /// The file had no section for the command (or was absent), and now has one.
    Created,
    /// The command's section was replaced.
    Replaced,
}

impl Lock {
    /// Read the run's section of the record at `path` ([`Lock::read_kind`]).
    pub fn read(path: &Path) -> Result<Self, String> {
        Self::read_kind(path, LockKind::Run)
    }

    /// Read `kind`'s section of the record at `path`: an absent file, or one with no such
    /// section, is an empty lock; a file that does not decode is the refusal's detail (module
    /// documentation).
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

    /// The lock as the record of a flow for `definition` (`PACKAGE:FACET`; `None` for a K flow),
    /// which a write then states in the record's header. A file that names another definition is
    /// refused, whatever the command: its sections are that definition's verdicts, so this
    /// command's rows would replace them (or, read as this flow's, give killers and statuses of
    /// another specification). A file that names none is read: it is a K flow's record, or one
    /// written before version 28, which a command without `--locked` rewrites with the name
    /// ([`Lock::refuse_other_version`] refuses it under `--locked`).
    pub fn for_definition(mut self, definition: Option<&str>) -> Result<Self, String> {
        if let Some(recorded) = &self.recorded_definition
            && Some(recorded.as_str()) != definition
        {
            let flow = definition.map_or_else(
                || "this flow names no definition (a K flow)".to_owned(),
                |definition| format!("this flow is for `{definition}`"),
            );
            return Err(format!(
                "{}: it is the record of the definition `{recorded}`, and {flow}: every section \
                 holds that definition's verdicts, which this command would replace with \
                 another's; give --lock this flow's own file",
                self.path.display()
            ));
        }
        self.definition = definition.map(str::to_owned);
        Ok(self)
    }

    /// The lock as the record of a definition whose functions `assumed` (each a symbol and its
    /// reason) are total on its author's word, which a write states in the command's section
    /// (`[<command>.assumed_totals]`, [`crate::verdicts::lock_section_with`]). Every verdict of
    /// the section may rest on each: a backend takes a total function's application to have a
    /// value. So a change of the list changes the section, as a change of the definition's
    /// verdicts does, and `--locked` finds the section stale; a definition with none writes no
    /// such table, so its section is the one it was. The list is in the record only: no document
    /// prints it, and a difference in it is named by its line alone.
    #[must_use]
    pub fn with_assumed_totals(mut self, assumed: &[(String, String)]) -> Self {
        self.assumed_totals = assumed.to_vec();
        self
    }

    /// Read `kind`'s section of the record at `path` for a command whose flow is for
    /// `definition` ([`Lock::for_definition`]): [`Lock::read_kind`], the old
    /// file `legacy` a front end kept the command's lock in ([`Lock::adopt_legacy`]), and under
    /// `--locked` ([`Lock::refuse_other_version`], [`Lock::refuse_legacy`]) the refusals that name
    /// `command`, the front end's spelling of the verb, as the command that rewrites the file.
    pub fn read_for(
        path: &Path,
        kind: LockKind,
        legacy: Option<&Path>,
        locked: bool,
        command: &str,
        definition: Option<&str>,
    ) -> Result<Self, String> {
        let mut lock = Self::read_kind(path, kind)?.for_definition(definition)?;
        if let Some(legacy) = legacy {
            lock.adopt_legacy(legacy)?;
        }
        if locked {
            lock.refuse_legacy(command)?;
            lock.refuse_other_version(command)?;
        }
        Ok(lock)
    }

    /// The lock `text` of the file at `path` decodes to, for `kind`'s section; a text that does
    /// not decode is the refusal's detail ([`Lock::read_kind`]).
    fn decode(path: &Path, text: String, kind: LockKind) -> Result<Self, String> {
        let refused = |what: String| format!("{}: {what}; {REFUSED_NEXT}", path.display());
        let table: toml::Table = text
            .parse()
            .map_err(|e: toml::de::Error| refused(format!("is not TOML: {}", e.message())))?;
        if table.get("schema").and_then(toml::Value::as_str) != Some(VERDICTS_SCHEMA) {
            return Err(refused(format!("its schema is not {VERDICTS_SCHEMA:?}")));
        }
        let recorded_definition = match table.get("definition") {
            None => None,
            Some(toml::Value::String(definition)) => Some(definition.clone()),
            Some(_) => return Err(refused("its definition is not a string".to_owned())),
        };
        let name = kind.document();
        // A lock before version 24 is one command's rendering at the top of its file.
        let empty = toml::Table::new();
        let (source, section, section_line) = match table.get("document") {
            Some(document) if document.as_str() == Some(name) => (&table, None, 0),
            Some(document) => {
                return Err(refused(format!(
                    "it is a lock written before version 24 whose document is {document}, not \
                     {name:?}: the file holds another command's record, which a {name} would \
                     overwrite; give --lock this command's own file"
                )));
            }
            None => {
                let source = match table.get(name) {
                    None => &empty,
                    Some(toml::Value::Table(section)) => section,
                    Some(_) => return Err(refused(format!("its {name} is not a table"))),
                };
                let found = sections(&text)
                    .into_iter()
                    .find(|(found, _, _)| *found == kind);
                match found {
                    Some((_, line, slice)) => (source, Some(trimmed(slice)), line),
                    None if table.contains_key(name) => {
                        return Err(refused(format!(
                            "its {name} section does not begin with a line `{}`",
                            kind.heading()
                        )));
                    }
                    None => (source, None, 0),
                }
            }
        };
        let noun = kind.row();
        let listed_rows = match source.get(noun) {
            None => &[][..],
            Some(toml::Value::Array(rows)) => rows.as_slice(),
            Some(_) => return Err(refused(format!("its {noun} is not an array of tables"))),
        };
        let mut rows = Vec::with_capacity(listed_rows.len());
        let mut seen = BTreeSet::new();
        for (index, row) in listed_rows.iter().enumerate() {
            let Some(row) = row.as_table() else {
                return Err(refused(format!("{noun} {} is not a table", index + 1)));
            };
            let Some(id) = row_id(kind, row) else {
                return Err(refused(match kind {
                    LockKind::Compare => format!(
                        "{noun} {} has no string implementation, program and view",
                        index + 1
                    ),
                    _ => format!("{noun} {} has no string id", index + 1),
                }));
            };
            let id = id.as_str();
            if !seen.insert(id.to_owned()) {
                let shown = match kind {
                    LockKind::Compare => id.to_owned(),
                    _ => format!("{id:?}"),
                };
                return Err(refused(format!("the {noun} {shown} is listed twice")));
            }
            // A query row's recorded fact is its witness, a run's and a flip's its killer; a row
            // holds only its own section's.
            let fact = |key: &str, applies: bool| match row.get(key) {
                Some(toml::Value::String(value)) if applies => Ok(Some(value.clone())),
                Some(_) if applies => Err(refused(format!("the {key} of {id:?} is not a string"))),
                _ => Ok(None),
            };
            let killer = fact("killer", matches!(kind, LockKind::Run | LockKind::Coverage))?;
            let witness = fact("witness", kind == LockKind::Query)?;
            let string = |key: &str| {
                row.get(key)
                    .and_then(toml::Value::as_str)
                    .map(str::to_owned)
            };
            rows.push(LockRow {
                id: id.to_owned(),
                killer,
                witness,
                status: string(if kind == LockKind::Compare {
                    "verdict"
                } else {
                    "status"
                }),
                reason: string("reason"),
                difference: string("difference"),
                horizon: string("horizon").filter(|_| kind == LockKind::Compare),
            });
        }
        // A coverage section's open and argued obligations: each family table's `open` and
        // `argued`, when it is an array of ids; read only to report what changed. An `argued`
        // entry is `{ id, standing }`; a lock written before version 24 lists bare ids.
        let entry_id = |entry: &toml::Value| {
            entry
                .as_str()
                .or_else(|| entry.get("id")?.as_str())
                .map(str::to_owned)
        };
        let families = || {
            source
                .iter()
                .filter(|(family, _)| crate::coverage::FAMILIES.contains(&family.as_str()))
        };
        let listed = |key: &str| match kind {
            LockKind::Run | LockKind::Compare | LockKind::Query => BTreeMap::new(),
            LockKind::Coverage => families()
                .filter_map(|(family, section)| {
                    let ids = section.get(key)?.as_array()?;
                    let ids = ids.iter().map(entry_id).collect::<Option<Vec<_>>>()?;
                    Some((family.clone(), ids))
                })
                .collect(),
        };
        // Each argued item's standing: an `argued` entry's, an argued flip's on its row, and, in a
        // lock written before version 24, its `[arguments]` line. A standing that is not a string
        // is left out, as an `open` that is not an array of ids is.
        let arguments = match kind {
            LockKind::Run | LockKind::Compare | LockKind::Query => BTreeMap::new(),
            LockKind::Coverage => {
                let standing = |entry: &toml::Value| {
                    Some((
                        entry_id(entry)?,
                        entry.get("standing")?.as_str()?.to_owned(),
                    ))
                };
                let entries = families()
                    .filter_map(|(_, section)| section.get("argued")?.as_array())
                    .flatten()
                    .chain(listed_rows);
                let legacy = source
                    .get(LEGACY_ARGUMENTS)
                    .and_then(toml::Value::as_table)
                    .into_iter()
                    .flatten()
                    .filter_map(|(id, standing)| Some((id.clone(), standing.as_str()?.to_owned())));
                legacy.chain(entries.filter_map(standing)).collect()
            }
        };
        Ok(Self {
            kind,
            path: path.to_path_buf(),
            text: Some(text),
            section,
            section_line,
            rows,
            header: header_values(source, kind),
            open: listed("open"),
            argued: listed("argued"),
            arguments,
            legacy: None,
            definition: None,
            recorded_definition,
            assumed_totals: Vec::new(),
        })
    }

    /// The table of the command's recorded facts, as TOML: its section's table, the whole file of
    /// a lock before version 24, or, where the record has no section of the command, the old file
    /// [`Lock::adopt_legacy`] read; `None` where nothing is recorded or a file no longer reads.
    /// [`crate::clock`] reads a kept row's `horizon` and the `undecided` ids from it, which
    /// [`Lock`] does not decode.
    #[must_use]
    pub fn recorded_table(&self) -> Option<toml::Table> {
        let text = match &self.legacy {
            Some(legacy) if legacy.migrated => fs::read_to_string(&legacy.path).ok()?,
            _ => self.text.clone()?,
        };
        let table = text.parse::<toml::Table>().ok()?;
        if table.contains_key("document") {
            return Some(table);
        }
        match table.get(self.kind.document()) {
            Some(toml::Value::Table(section)) => Some(section.clone()),
            _ => None,
        }
    }

    /// Whether the file records anything for the command: a section, or a lock before version 24
    /// of the command (an old file's, read by [`Lock::adopt_legacy`], included).
    #[must_use]
    pub fn records(&self) -> bool {
        self.section.is_some() || !self.header.is_empty() || !self.rows.is_empty()
    }

    /// Note the old file `legacy` a front end kept the command's lock in before version 24, where
    /// it is still there: while the record has no section for the command, its recorded facts
    /// (killers, statuses, obligations, the header) are read from it, so a migration loses no
    /// killer, and the next write moves them into the record ([`Legacy::migrated`]). An old file
    /// that does not decode refuses the command, as the record would. Nothing is deleted: the
    /// document's `lock.legacy` says to delete it ([`lock_notes`]).
    pub fn adopt_legacy(&mut self, legacy: &Path) -> Result<(), String> {
        if !legacy.exists() {
            return Ok(());
        }
        let migrated = !self.records();
        if migrated {
            let old = Self::read_kind(legacy, self.kind)?;
            self.rows = old.rows;
            self.header = old.header;
            self.open = old.open;
            self.argued = old.argued;
            self.arguments = old.arguments;
        }
        self.legacy = Some(Legacy {
            path: legacy.to_path_buf(),
            migrated,
        });
        Ok(())
    }

    /// Refuse, under `--locked`, an old file a front end kept the command's lock in, while it is
    /// there: the committed record is not the file `--locked` would compare, so the check cannot
    /// say the corpus's lock is current. While the record has no section for the command, the
    /// detail names `command` without `--locked` as the command that moves the old file's killers
    /// into it; once it has one, it says to delete the old file.
    pub fn refuse_legacy(&self, command: &str) -> Result<(), String> {
        let Some(legacy) = &self.legacy else {
            return Ok(());
        };
        let (old, record) = (legacy.path.display(), self.path.display());
        let section = self.kind.heading();
        Err(if legacy.migrated {
            format!(
                "{old}: it is a lock written before version 24, which {record} replaces with \
                 one {section} section per command, so --locked cannot find the corpus's lock \
                 current; run `{command}` without --locked once to move its killers into \
                 {record}, then delete {old}"
            )
        } else {
            format!(
                "{old}: it is a lock written before version 24, whose verdicts {record}'s \
                 {section} section now keeps; delete {old}"
            )
        })
    }

    /// Refuse a lock `--locked` cannot find current whatever the command decides: a section (or
    /// a lock before version 24) whose `version` is not the rendering's
    /// ([`crate::verdicts::VERDICTS_VERSION`]), or that names none. The rendering of another
    /// version writes other bytes for the same verdicts, so the comparison would only say so
    /// after a whole run; the refusal says it before admission, and names the command that
    /// rewrites the section, `command` (the front end's spelling of the verb) without
    /// `--locked`. A command without `--locked` reads such a lock for its killers and rewrites
    /// it. A file with no section for the command is no refusal: it is stale.
    pub fn refuse_other_version(&self, command: &str) -> Result<(), String> {
        if !self.records() {
            return Ok(());
        }
        let current = crate::verdicts::VERDICTS_VERSION;
        let recorded = match self.header.get("version") {
            Some(version) if version.as_u64() == Some(current) => return Ok(()),
            Some(version) => format!("is recorded at version {version} of the verdicts rendering"),
            None => "names no version of the verdicts rendering".to_owned(),
        };
        let what = if self.section.is_some() {
            format!("its {} section", self.kind.heading())
        } else {
            "it".to_owned()
        };
        Err(format!(
            "{}: {what} {recorded}, and this build writes version {current}, so --locked cannot \
             find it current; run `{command}` without --locked once to rewrite it, and review \
             its diff",
            self.path.display()
        ))
    }

    /// Each mutation (or flip) id with its recorded killer; empty for a compare or query section,
    /// whose rows record none ([`Lock::witnesses`]).
    #[must_use]
    pub fn killers(&self) -> BTreeMap<String, String> {
        self.rows
            .iter()
            .filter_map(|row| Some((row.id.clone(), row.killer.clone()?)))
            .collect()
    }

    /// Each pattern id of a query section with its recorded witness; empty for every other
    /// section, whose rows record none.
    #[must_use]
    pub fn witnesses(&self) -> BTreeMap<String, String> {
        self.rows
            .iter()
            .filter_map(|row| Some((row.id.clone(), row.witness.clone()?)))
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
        let mut value = not_written(&self.path, reason);
        self.with_legacy(&mut value, false);
        value
    }

    /// `value` with `legacy`, `{path, status}`, where the command was given an old file that is
    /// still there: `migrated` where its killers were read and `moved` says the write moved them
    /// into the record, `superseded` where the record already has the command's section.
    fn with_legacy(&self, value: &mut Value, moved: bool) {
        if let Some(legacy) = &self.legacy {
            value["legacy"] = json!({
                "path": legacy.path.display().to_string(),
                "status": if legacy.migrated { "migrated" } else { "superseded" },
                "moved": legacy.migrated && moved,
            });
        }
    }

    /// Settle the command's section after a run whose document is `document`: compare the
    /// section the run would write with the file's, and write it after a run that judged every
    /// mutation of its list in search mode without `--locked`. The value is the document's
    /// `lock`: `{path, status, reason, header, header_changes, changes, difference, clock_stopped,
    /// kept}` (README, "The corpus record"), with `detail` when a write failed, and `legacy` where
    /// the command was given an old file; the flag is false when a write failed. An entry of the
    /// command's section that a run the clock stopped could change keeps its recorded value
    /// ([`crate::clock`]: `clock_stopped`, `kept`), so the section written holds it, and under
    /// `--locked` a section that differs in nothing else is `undecided`; the other command's
    /// section is untouched by it, as by every write.
    ///
    /// Under `--locked` a section that differs from the rendering only in its header is `stale`,
    /// like one whose rows differ. In particular a section recorded on another Z3 build (its
    /// `z3_version` or `z3_library_sha256`) is a finding even when every row agrees. Under the Z3
    /// profile a verdict is a function of the inputs and of the solver build, so the build is part
    /// of the instrument the section was measured with, as the profile is. `--locked` asks whether
    /// this run, on this instrument, writes the committed section. A run on another build cannot
    /// confirm that, because rows that agree on today's corpus do not make two builds
    /// interchangeable for the next edit. Passing it would leave the repository's lock naming a
    /// build no check ran on, so a later moved row would be blamed on the corpus while the header
    /// misnamed the solver. When every row agrees the fix is a header-only rewrite (a run
    /// without `--locked`), which review sees as exactly that. The other command's section is
    /// neither compared nor written.
    #[must_use]
    pub fn settle(&self, store: &Store, document: &Value, run: Settle<'_>) -> (Value, bool) {
        let path = self.path.display().to_string();
        let refused = document["spec"]["outcome"] == "refused";
        if refused || run.stopped {
            let reason = if refused { "refused" } else { "stopped" };
            return (self.not_written(reason), true);
        }
        // An entry of the command's section that a run the clock stopped decided keeps its
        // recorded value: the section compared and written is the rendering of the document with
        // those values ([`crate::clock`]).
        let clock = crate::clock::keep(self, document);
        let document = &clock.document;
        let section = match lock_section_with(document, &self.assumed_totals) {
            Ok(section) if LockKind::of(document) == self.kind => section,
            _ => return (self.not_written("refused"), true),
        };
        let kind = self.kind;
        // The record's header is the file's: a file whose header is not the one a write gives
        // differs in its header, as one with no section for the command does.
        let file_header = self.text.as_deref().is_some_and(|text| {
            split(text).0.trim_end_matches('\n')
                == record_header(self.definition.as_deref()).trim_end()
        });
        let header = !file_header
            || self
                .section
                .as_deref()
                .is_none_or(|old| head(kind, old) != head(kind, &section));
        let header_changes = self.header_changes(&section);
        let changes = self.changes(document, run.only);
        // Under `--only` the rows it did not select may differ from the file's: only the selected
        // rows and the header are compared, so no first difference of the whole section is
        // named.
        let difference = if run.only.is_empty() {
            self.difference(&section)
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
            if kind == LockKind::Compare {
                value["failed"] = json!(clock.failed);
            }
            value
        };
        if run.locked {
            let differs = if run.only.is_empty() {
                !file_header || self.section.as_deref() != Some(section.as_str())
            } else {
                header || !changes.is_empty()
            };
            // Not a difference, and not confirmed either: some entry rests on a run the clock
            // stopped (or, for `compare`, on a run of an implementation that gave no answer), so
            // this host cannot decide it.
            let status = if differs {
                "stale"
            } else if clock.stopped.is_empty() && clock.failed.is_empty() {
                "unchanged"
            } else {
                "undecided"
            };
            let mut locked = value(status, Some("locked"), header, changes);
            self.with_legacy(&mut locked, false);
            return (locked, true);
        }
        let not_written = |reason: &str, changes: Vec<Value>| {
            let mut skipped = value("not-written", Some(reason), header, changes);
            self.with_legacy(&mut skipped, false);
            (skipped, true)
        };
        if run.verify {
            return not_written("verify", changes);
        }
        if !run.only.is_empty() {
            return not_written("only", changes);
        }
        match self.write_section(store, &section) {
            Ok(written) => {
                let status = match written {
                    Outcome::Unchanged => "unchanged",
                    Outcome::Created => "created",
                    Outcome::Replaced => "written",
                };
                let mut done = value(status, None, header, changes);
                self.with_legacy(&mut done, true);
                (done, true)
            }
            Err(e) => {
                let mut failed = value("not-written", Some("write-failed"), header, changes);
                failed["detail"] = json!(format!("cannot write {path}: {e}"));
                self.with_legacy(&mut failed, false);
                (failed, false)
            }
        }
    }

    /// Write `section` as the command's section of the record: under an exclusive lock of the
    /// file's directory, read the file again, keep the other command's section as its text is
    /// (trailing blank lines aside), and publish the record's header and the sections by rename
    /// ([`Store::write_text`]); nothing when the file already holds that text. A file that no
    /// longer decodes as a record the command may write is not overwritten.
    fn write_section(&self, store: &Store, section: &str) -> Result<Outcome, String> {
        let directory = match self.path.parent() {
            Some(parent) if !parent.as_os_str().is_empty() => parent.to_path_buf(),
            _ => PathBuf::from("."),
        };
        fs::create_dir_all(&directory).map_err(|e| e.to_string())?;
        let guard = fs::File::open(&directory).map_err(|e| e.to_string())?;
        guard
            .lock()
            .map_err(|e| format!("cannot lock {}: {e}", directory.display()))?;
        let fresh = match fs::read_to_string(&self.path) {
            Ok(text) => Some(text),
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => None,
            Err(e) => return Err(e.to_string()),
        };
        // Another command may have written the file since it was read: what it holds now is
        // what this write keeps, and it must still be a record this command may write.
        let current = match &fresh {
            Some(text) => Some(
                Self::decode(&self.path, text.clone(), self.kind)?
                    .for_definition(self.definition.as_deref())?,
            ),
            None => None,
        };
        let kept = fresh.as_deref().map_or_else(Vec::new, |text| {
            sections(text)
                .into_iter()
                .filter(|(found, _, _)| *found != self.kind)
                .map(|(found, _, slice)| (found, trimmed(slice)))
                .collect()
        });
        let mut text = record_header(self.definition.as_deref());
        for kind in SECTIONS {
            let part = if kind == self.kind {
                Some(section.to_owned())
            } else {
                kept.iter()
                    .find(|(found, _)| *found == kind)
                    .map(|(_, slice)| slice.clone())
            };
            if let Some(part) = part {
                text.push('\n');
                text.push_str(&part);
            }
        }
        if fresh.as_deref() == Some(text.as_str()) {
            return Ok(Outcome::Unchanged);
        }
        // The record must read back with the section written and the other kept.
        Self::decode(&self.path, text.clone(), self.kind)?;
        store
            .write_text(&self.path, &text)
            .map_err(|e| e.to_string())?;
        drop(guard);
        Ok(
            if current
                .as_ref()
                .is_some_and(|current| current.section.is_some())
            {
                Outcome::Replaced
            } else {
                Outcome::Created
            },
        )
    }

    /// Where the command's section first differs from `section`, the section the run would
    /// write: `{kind, line, recorded, now}`, `line` counted from 1 in the file; null when the file
    /// has no section for the command, or an equal one. `kind` is `order` when the two hold the
    /// same rows in another order: then `line` is the file's line of the `id` of its first row out
    /// of the rendering's order, `recorded` that line and `now` the `id` line of the row the
    /// rendering puts there, whatever else (a comment, spacing) differs before it. Otherwise
    /// `kind` is `text` (a comment, spacing, or a key the rendering does not write, beside what
    /// the header and the row changes say), and `line` is the first line in which the two differ,
    /// `recorded` and `now` that line of each (null past its end).
    fn difference(&self, section: &str) -> Value {
        let Some(old) = self.section.as_deref() else {
            return Value::Null;
        };
        if old == section {
            return Value::Null;
        }
        let offset = self.section_line.saturating_sub(1);
        let ids = |rows: &mut dyn Iterator<Item = String>| {
            let mut ids = rows.collect::<Vec<_>>();
            let order = ids.clone();
            ids.sort();
            (order, ids)
        };
        let (old_order, old_set) = ids(&mut self.rows.iter().map(|row| row.id.clone()));
        let rendered = Lock::read_text(section, self.kind);
        let (new_order, new_set) = ids(&mut rendered.into_iter());
        if old_order != new_order && old_set == new_set {
            let (old_ids, new_ids) = (id_lines(old, self.kind), id_lines(section, self.kind));
            let first = old_order.iter().zip(&new_order).position(|(a, b)| a != b);
            if let Some(((line, recorded), (_, now))) =
                first.and_then(|at| old_ids.get(at).zip(new_ids.get(at)))
            {
                return json!({"kind": "order", "line": line + offset, "recorded": recorded,
                              "now": now});
            }
        }
        let (mut recorded, mut now) = (old.split('\n'), section.split('\n'));
        let mut line = 1_u64;
        let (recorded, now) = loop {
            match (recorded.next(), now.next()) {
                (Some(a), Some(b)) if a == b => line += 1,
                (a, b) => break (a, b),
            }
        };
        // A line of the assumed totalities is named by its place alone: no output prints them
        // ([`Lock::with_assumed_totals`]).
        let at = usize::try_from(line - 1).unwrap_or(usize::MAX);
        if in_assumed_totals(old, at) || in_assumed_totals(section, at) {
            return json!({"kind": ASSUMED_TOTALS, "line": line + offset});
        }
        json!({"kind": "text", "line": line + offset, "recorded": recorded, "now": now})
    }

    /// Each key of the section's header whose value differs between the file and `section`, the
    /// section the run would write: `{key, recorded, now}`, either side null where that side has
    /// no such key, in the order of the section's lines, then the keys only the file has, in key
    /// order. Empty when the file records nothing for the command (there is no recorded header to
    /// compare) or the headers' values are equal (they may still differ in a comment or spacing,
    /// which `header` and `difference` show).
    fn header_changes(&self, section: &str) -> Vec<Value> {
        if !self.records() {
            return Vec::new();
        }
        let name = self.kind.document();
        let now = section
            .parse::<toml::Table>()
            .ok()
            .and_then(|table| table.get(name).and_then(toml::Value::as_table).cloned())
            .map(|table| header_values(&table, self.kind))
            .unwrap_or_default();
        let mut keys = header_key_order(section, name);
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

    /// The row ids (mutations, flips) of the section `text` of a lock of `kind` (or of a record
    /// holding it), in its order; none for a text that does not decode, which a rendering always
    /// does.
    fn read_text(text: &str, kind: LockKind) -> Vec<String> {
        let Ok(table) = text.parse::<toml::Table>() else {
            return Vec::new();
        };
        table
            .get(kind.document())
            .and_then(|section| section.get(kind.row()))
            .and_then(toml::Value::as_array)
            .into_iter()
            .flatten()
            .filter_map(|row| row_id(kind, row.as_table()?))
            .collect()
    }

    /// Each mutation whose `(status, killer, reason)` differs between the lock and `document`'s
    /// rows: `{mutation, recorded, now}`, either side null for a row only the other has, in the
    /// document's order, then the lock's rows the document has no row for. Under `--only`
    /// (`only` not empty) only the selected rows are compared.
    fn changes(&self, document: &Value, only: &[String]) -> Vec<Value> {
        let selected = |id: &str| selected(self.kind, only, id);
        let recorded = self
            .rows
            .iter()
            .map(|row| (row.id.as_str(), row.recorded(self.kind)))
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
                let mut change = self.kind.keyed(id);
                change.insert("recorded".into(), json!(before));
                change.insert("now".into(), now);
                changes.push(Value::Object(change));
            }
        }
        for row in &self.rows {
            if selected(&row.id) && only.is_empty() && !seen.contains(&row.id) {
                let mut change = self.kind.keyed(&row.id);
                change.insert("recorded".into(), recorded[row.id.as_str()].clone());
                change.insert("now".into(), Value::Null);
                changes.push(Value::Object(change));
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

/// Whether `--only` (`only`, empty: every row) selects the row `id` of a `kind` section: by its
/// id, and for a compare row by its implementation, since `compare --only` names
/// implementations.
fn selected(kind: LockKind, only: &[String], id: &str) -> bool {
    only.is_empty()
        || match kind {
            LockKind::Run | LockKind::Coverage | LockKind::Query => only.iter().any(|o| o == id),
            LockKind::Compare => {
                let keyed = kind.keyed(id);
                only.iter().any(|o| keyed["implementation"] == o.as_str())
            }
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

/// The header of a decoded section of `kind` (or of a lock before version 24, its whole file):
/// each key outside its rows (`mutation`, `flip`), the `schema` and `document` of a lock before
/// version 24, and, for a coverage section, its family tables (`rules`, ...; [`head`]) and an old
/// lock's `[arguments]`, a sub-table's keys as `table.key`, with its value as JSON (a string, an
/// integer or a boolean as itself, any other value as its TOML text).
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
            // The assumed totalities are named by no change: no output prints them.
            _ if key == kind.row()
                || key == "schema"
                || key == "document"
                || key == ASSUMED_TOTALS => {}
            toml::Value::Table(_)
                if kind == LockKind::Coverage
                    && (crate::coverage::FAMILIES.contains(&key.as_str())
                        || key == LEGACY_ARGUMENTS) => {}
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

/// The header keys of the section `text` of the command `name`, in the order of its lines, as
/// [`header_values`] names them: a key of `[<name>]`, or `table.key` in a `[<name>.table]`; none
/// in a row (`[[<name>.mutation]]`), none from a comment, and none from the continuation lines of
/// a multi-line array (a value, a string or an inline table, or its closing `]`), which belong to
/// the key that opened it, nor from a line whose key is quoted (an `[arguments]` line of a lock
/// written before version 24, whose key is an item id): the rendering quotes no header key, so
/// such a line is no header line, and [`header_values`] leaves its table out.
fn header_key_order(text: &str, name: &str) -> Vec<String> {
    let mut keys = Vec::new();
    let mut table: Option<String> = None;
    for line in text.split('\n') {
        let trimmed = line.trim();
        if trimmed.starts_with(['"', '{', ']', '#']) {
            continue;
        }
        if trimmed.starts_with("[[") {
            table = None;
        } else if let Some(heading) = trimmed.strip_prefix('[').and_then(|r| r.strip_suffix(']')) {
            let heading = heading.trim();
            table = if heading == name {
                Some(String::new())
            } else {
                heading
                    .strip_prefix(name)
                    .and_then(|rest| rest.strip_prefix('.'))
                    .map(str::to_owned)
            };
        } else if let (Some(table), Some((key, _))) = (&table, trimmed.split_once('=')) {
            let key = key.trim();
            keys.push(if table.is_empty() {
                key.to_owned()
            } else {
                format!("{table}.{key}")
            });
        }
    }
    keys
}

/// The `id` line of each row of `kind`'s section `text` (`[[run.mutation]]`, `[[coverage.flip]]`;
/// a `[[compare.verdict]]`'s `implementation` line), in order, with its line number counted from
/// 1 in `text`: the first line of the row's table that sets that key.
fn id_lines(text: &str, kind: LockKind) -> Vec<(u64, &str)> {
    let table = format!("[[{}.{}]]", kind.document(), kind.row());
    let key = kind.key_line();
    let mut lines = Vec::new();
    let mut in_row = false;
    for (number, line) in (1_u64..).zip(text.split('\n')) {
        let trimmed = line.trim();
        if trimmed.starts_with('[') {
            in_row = trimmed == table;
        } else if in_row
            && trimmed
                .strip_prefix(key)
                .is_some_and(|rest| rest.trim_start().starts_with('='))
        {
            lines.push((number, line));
            in_row = false;
        }
    }
    lines
}

/// Whether line `at` (from 0) of the section `text` is inside its `assumed_totals` table
/// ([`Lock::with_assumed_totals`]), its heading included.
fn in_assumed_totals(text: &str, at: usize) -> bool {
    let mut inside = false;
    for (index, line) in text.split('\n').enumerate() {
        let trimmed = line.trim();
        if trimmed.starts_with('[') {
            inside = trimmed
                .trim_start_matches('[')
                .trim_end_matches(']')
                .rsplit('.')
                .next()
                == Some(ASSUMED_TOTALS)
                && !trimmed.starts_with("[[");
        }
        if index == at {
            return inside;
        }
    }
    false
}

/// The header of a section of `kind`: a run section's lines before its first `[[run.mutation]]`
/// (the version, profile and build lines and `[run.spec]`, with the comments before the rows), a
/// coverage section's before its first family table or `[[coverage.flip]]` (the version, profile,
/// build and `krs_annotation` lines, `[coverage.spec]` and `[coverage.settings]`), a compare
/// section's before its first `[[compare.verdict]]` (the version, profile, build and `protocol`
/// lines and `[compare.spec]`), a query section's before its first `[[query.pattern]]` (the
/// version, profile and build lines and `[query.spec]`).
fn head(kind: LockKind, text: &str) -> &str {
    let end = match kind {
        LockKind::Run => text.find("\n[[run.mutation]]"),
        LockKind::Query => text.find("\n[[query.pattern]]"),
        LockKind::Compare => text.find("\n[[compare.verdict]]"),
        LockKind::Coverage => text.match_indices("\n[").map(|(at, _)| at).find(|&at| {
            let line = text[at + 1..].lines().next().unwrap_or_default();
            line == "[[coverage.flip]]"
                || crate::coverage::FAMILIES.iter().any(|family| {
                    line.strip_prefix("[coverage.")
                        .and_then(|l| l.strip_suffix(']'))
                        == Some(family)
                })
        }),
    };
    end.map_or(text, |end| &text[..end])
}

/// A record's text split at its sections: the header, the text before the first section, and
/// each section ([`sections`]).
fn split(text: &str) -> (&str, Vec<(LockKind, u64, &str)>) {
    let sections = sections(text);
    let end = sections
        .first()
        .map_or(text.len(), |(_, _, slice)| offset_of(text, slice));
    (&text[..end], sections)
}

/// The byte offset of `slice`, a part of `text`, in `text`.
fn offset_of(text: &str, slice: &str) -> usize {
    slice.as_ptr() as usize - text.as_ptr() as usize
}

/// Each section of a record's text, in the file's order: the command, the line it starts at
/// (counted from 1), and its text, from its `[run]` or `[coverage]` line to the next such line or
/// the end of the file. A lock before version 24 has none.
fn sections(text: &str) -> Vec<(LockKind, u64, &str)> {
    let mut starts = Vec::new();
    let mut at = 0;
    for (number, line) in (1_u64..).zip(text.split('\n')) {
        if let Some(kind) = SECTIONS.into_iter().find(|kind| line == kind.heading()) {
            starts.push((kind, number, at));
        }
        at += line.len() + 1;
    }
    starts
        .iter()
        .enumerate()
        .map(|(index, &(kind, number, start))| {
            let end = starts
                .get(index + 1)
                .map_or(text.len(), |&(_, _, next)| next);
            (kind, number, &text[start..end.min(text.len())])
        })
        .collect()
}

/// A section's text without its trailing blank lines, ending with one newline: the bytes a
/// record keeps of it, the blank line before the next section being the record's.
fn trimmed(slice: &str) -> String {
    format!("{}\n", slice.trim_end_matches('\n'))
}
/// The run document's `lock` of a lock that does not decode: `{path, outcome: "refused",
/// detail}`.
#[must_use]
pub fn refused_value(path: &Path, detail: &str) -> Value {
    json!({"path": path.display().to_string(), "outcome": "refused", "detail": detail})
}

/// One line per change of a run document whose lock is `stale` (`--locked` found that the run
/// would change it), as `kink-flow` prints them on stderr: one per header key whose value differs
/// (`lock.header_changes`: `` kink.lock: [run] z3_library_sha256 differs: recorded
/// "7ca2…", now "1f0e…" (another Z3 build) ``), or one saying that the header differs when no
/// value does (the file is absent, or a comment or spacing differs); then one per row,
/// `kink.lock: plus/a: killer t4 -> t2 (t4: not-in-corpus)`, `kink.lock: plus/c:
/// killed -> survived`, and for a coverage lock one per obligation whose openness differs
/// (`lock.open_changes`: `kink.lock: rules: rule:x is open`, `kink.lock: requirements:
/// requirement:x:held is no longer open`, `kink.lock: rules: rule:x is argued (was open)`)
/// and one per argued item whose standing differs where no such line names it
/// (`lock.argument_changes`: `kink.lock: rule:x: standing text -> unchecked`) before them;
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
    let path = lock["path"].as_str().unwrap_or(LOCK_FILE);
    let section = kind.heading();
    let mut lines = Vec::new();
    if lock["header"] == true {
        let header_changes = lock["header_changes"]
            .as_array()
            .map_or(&[][..], Vec::as_slice);
        if header_changes.is_empty() {
            let first = match kind {
                LockKind::Run => "its first mutation",
                LockKind::Coverage => "its first family",
                LockKind::Compare => "its first verdict",
                LockKind::Query => "its first pattern",
            };
            lines.push(format!(
                "{path}: the {section} section's header differs (the file has no {section} \
                 section, or the record's header, or a comment or spacing before {first}, \
                 differs)"
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
            // `version` differs on no stale lock: under `--locked` a lock of another version is
            // refused before the command runs ([`Lock::refuse_other_version`]).
            let why = match key {
                "profile" => " (another solver profile)",
                "z3_version" | "z3_library_sha256" => " (another Z3 build)",
                _ => "",
            };
            lines.push(format!(
                "{path}: {section} {key} differs: recorded {}, now {}{why}",
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
        .filter(|_| kind != LockKind::Compare)
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
            LockKind::Compare => (
                "the declarations'",
                "implementation, program and view order",
            ),
            LockKind::Query => ("the pattern list's", "the list's order"),
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
            "{path}: {}: standing {} -> {}",
            change["obligation"].as_str().unwrap_or("?"),
            side(&change["recorded"]),
            side(&change["now"])
        ));
    }
    for change in changes {
        let id = kind.named(change);
        let (recorded, now) = (&change["recorded"], &change["now"]);
        let text = |value: &Value| value.as_str().unwrap_or("none").to_owned();
        if kind == LockKind::Compare {
            lines.push(format!("{path}: {id}: {}", compare_change(recorded, now)));
            continue;
        }
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
                // A query row's fact is its witness, which moves for its `witness_change`.
                let (fact, change) = if kind == LockKind::Query {
                    ("witness", "witness_change")
                } else {
                    ("killer", "killer_change")
                };
                let why = rows
                    .iter()
                    .find(|row| row["id"] == id)
                    .and_then(|row| row[change].as_str());
                let because = match (recorded[fact].as_str(), why) {
                    (Some(killer), Some(why)) => format!(" ({killer}: {why})"),
                    _ => String::new(),
                };
                format!(
                    "{fact} {} -> {}{because}",
                    text(&recorded[fact]),
                    text(&now[fact])
                )
            }
        };
        lines.push(format!("{path}: {id}: {line}"));
    }
    lines
}

/// What a line says of a compare row whose `{verdict, reason, difference, horizon}` moved from
/// `recorded` to `now` (either null for a row only the other side has): `added, equal`, `removed,
/// was different`, `equal -> different`, `not-compared (omitted) -> equal`, or, where only the
/// first difference or only the horizon moved, both of its forms.
fn compare_change(recorded: &Value, now: &Value) -> String {
    let verdict = |side: &Value| {
        let word = side["verdict"].as_str().unwrap_or("none");
        match side["reason"].as_str() {
            Some(reason) => format!("{word} ({reason})"),
            None => word.to_owned(),
        }
    };
    match (recorded.is_null(), now.is_null()) {
        (true, _) => format!("added, {}", verdict(now)),
        (_, true) => format!("removed, was {}", verdict(recorded)),
        _ if recorded["verdict"] != now["verdict"] || recorded["reason"] != now["reason"] => {
            format!("{} -> {}", verdict(recorded), verdict(now))
        }
        _ => {
            let side = |value: &Value| value.as_str().unwrap_or("none").to_owned();
            let (what, key) = if recorded["difference"] == now["difference"] {
                ("horizon", "horizon")
            } else {
                ("first difference", "difference")
            };
            format!(
                "{}: its {what} moved: recorded {}, now {}",
                verdict(now),
                side(&recorded[key]),
                side(&now[key])
            )
        }
    }
}

/// One line per note on the lock of `document` that is no finding, as `kink-flow` prints them on
/// stderr whatever the lock's status: where the command was given an old file a front end kept
/// its lock in before version 24 (`lock.legacy`), that its killers were moved into the record
/// (`kink/verdicts.lock: its killers are now in kink/kink.lock's [run] section; delete
/// kink/verdicts.lock`), that they were read but not moved, or that the record already keeps
/// them. kink-flow deletes no file.
#[must_use]
pub fn lock_notes(document: &Value) -> Vec<String> {
    let lock = &document["lock"];
    let legacy = &lock["legacy"];
    let Some(old) = legacy["path"].as_str() else {
        return Vec::new();
    };
    let path = lock["path"].as_str().unwrap_or(LOCK_FILE);
    let section = LockKind::of(document).heading();
    vec![match (legacy["status"].as_str(), legacy["moved"] == true) {
        (Some("migrated"), true) => {
            format!("{old}: its killers are now in {path}'s {section} section; delete {old}")
        }
        (Some("migrated"), false) => format!(
            "{old}: its killers were read, and the run that rewrites {path} moves them into its \
             {section} section; then delete {old}"
        ),
        _ => format!("{old}: {path}'s {section} section keeps its verdicts now; delete {old}"),
    }]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::verdicts::{lock_section, lock_text};

    /// A run document judging `rows` (`(id, status, killer)`), admitted, under `profile`.
    fn run_document(rows: &[(&str, &str, Option<&str>)]) -> Value {
        json!({
            "schema": crate::report::RUN_SCHEMA,
            "profile": "no-z3",
            "spec": {"outcome": "admitted"},
            "mutations": rows
                .iter()
                .map(|(id, status, killer)| json!({"id": id, "status": status, "killer": killer}))
                .collect::<Vec<_>>(),
        })
    }

    /// A coverage document arguing `argued` (`(id, standing)`) and leaving `open` open, of a
    /// front end that derives no flips.
    fn coverage_document(argued: &[(&str, &str)], open: &[&str]) -> Value {
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
            "profile": "no-z3",
            "spec": {"outcome": "admitted"},
            "settings": {"tiers": [1], "depth": 1, "mcdc": []},
            "families": {
                "rules": {"items": items},
                "requirements": {"items": []},
                "syntax": {"items": []},
                "flips": {"run": false},
            },
        })
    }

    /// A fresh directory of this test process.
    fn scratch(name: &str) -> PathBuf {
        let dir = std::env::temp_dir()
            .join(format!("kink-flow-lock-unit-{}", std::process::id()))
            .join(name);
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        dir
    }

    const LOCKED: Settle<'static> = Settle {
        locked: true,
        verify: false,
        only: &[],
        stopped: false,
    };

    const WRITE: Settle<'static> = Settle {
        locked: false,
        verify: false,
        only: &[],
        stopped: false,
    };

    /// `kind`'s section of `text`, as a file at `kink.lock` decodes it.
    fn decoded(text: &str, kind: LockKind) -> Lock {
        Lock::decode(Path::new(LOCK_FILE), text.to_owned(), kind).unwrap()
    }

    /// A view of a compare row: its name, whether it is required, its verdict, and its other
    /// members (`difference`, `reason`, `detail`).
    fn view(name: &str, required: bool, verdict: &str, extra: Value) -> Value {
        let mut view = json!({"view": name, "required": required, "verdict": verdict,
                              "difference": null, "reason": null, "detail": null});
        for (key, value) in extra.as_object().into_iter().flatten() {
            view[key] = value.clone();
        }
        view
    }

    /// The row of the implementation `cpu` on `program`: its views, its failure and which run
    /// the clock stopped.
    fn compare_row(program: &str, views: Vec<Value>, failure: Value, clock: Value) -> Value {
        json!({"implementation": "cpu", "program": program,
               "request_sha256": format!("r-{program}"), "failure": failure,
               "clock_stopped": clock, "views": views})
    }

    /// The two views of `cpu` on `program` it answered `equal` (`whole`, required) and
    /// `different` at `parity` (reported), the difference at `cell`.
    fn answered(program: &str, cell: &str) -> Value {
        compare_row(
            program,
            vec![
                view("whole", true, "equal", json!({})),
                view(
                    "parity",
                    false,
                    "different",
                    json!({"difference": {"format": "krs-difference/3", "path": cell,
                                          "definition": 1, "implementation": 3}}),
                ),
            ],
            Value::Null,
            Value::Null,
        )
    }

    /// A compare document of `cpu` (identity digest `aa`) on the programs `p1` and `p2`.
    fn compare_document(rows: Vec<Value>) -> Value {
        json!({
            "schema": crate::compare::COMPARE_SCHEMA,
            "profile": "no-z3",
            "protocol": crate::compare::PROTOCOL,
            "spec": {"outcome": "admitted"},
            "refusal": null,
            "implementations": [{"name": "cpu", "identity": {"file": "bin/cpu", "sha256": "aa"}}],
            "programs": [{"id": "p1", "class": "comparable"}, {"id": "p2", "class": "comparable"}],
            "rows": rows,
        })
    }

    /// The compare section of `cpu` answering both programs, as the record writes it.
    fn compare_section_text() -> String {
        let legend = crate::verdicts::COMPARE_LEGEND
            .iter()
            .map(|line| format!("# {line}\n"))
            .collect::<String>();
        let preamble = crate::verdicts::COMPARE_PREAMBLE
            .iter()
            .map(|line| format!("# {line}\n"))
            .collect::<String>();
        let rows = ["p1", "p2"]
            .iter()
            .map(|program| {
                format!(
                    "[[compare.verdict]]\nimplementation = \"cpu\"\nprogram = \"{program}\"\n\
                     view = \"whole\"\nrequired = true\nverdict = \"equal\"\n\
                     request_sha256 = \"r-{program}\"\nidentity_sha256 = \"aa\"\n\n\
                     [[compare.verdict]]\nimplementation = \"cpu\"\nprogram = \"{program}\"\n\
                     view = \"parity\"\nrequired = false\nverdict = \"different\"\n\
                     difference = '{{\"definition\":1,\"format\":\"krs-difference/3\",\
                     \"implementation\":3,\"path\":\"acc\"}}'\n\
                     request_sha256 = \"r-{program}\"\nidentity_sha256 = \"aa\"\n"
                )
            })
            .collect::<Vec<_>>()
            .join("\n");
        format!(
            "[compare]\n{preamble}version = 29\nprofile = \"no-z3\"\n\
             protocols = [\"kink-implementation/1\"]\n\n[compare.spec]\noutcome = \
             \"admitted\"\n\n{legend}{rows}"
        )
    }

    /// A compare section is one `[[compare.verdict]]` per (implementation, program, view) in
    /// the declarations' order, keyed by its three names, with `required`, the verdict, a
    /// different view's first difference as canonical JSON, and the request's and the
    /// identity's digests; its header names the protocol. It renders the same bytes every time,
    /// decodes to its rows, and a write then `--locked` finds it unchanged.
    #[test]
    fn a_compare_section_renders_decodes_and_round_trips() {
        let document = compare_document(vec![answered("p1", "acc"), answered("p2", "acc")]);
        let section = lock_section(&document).unwrap();
        assert_eq!(section, compare_section_text());
        assert_eq!(lock_section(&document).unwrap(), section);
        let text = lock_text(&document).unwrap();
        let lock = decoded(&text, LockKind::Compare);
        assert_eq!(lock.section.as_deref(), Some(section.as_str()));
        assert_eq!(
            lock.rows
                .iter()
                .map(|row| row.id.clone())
                .collect::<Vec<_>>(),
            [
                compare_row_id("cpu", "p1", "whole"),
                compare_row_id("cpu", "p1", "parity"),
                compare_row_id("cpu", "p2", "whole"),
                compare_row_id("cpu", "p2", "parity"),
            ]
        );
        assert_eq!(lock.rows[1].status.as_deref(), Some("different"));
        assert_eq!(
            lock.rows[1].difference.as_deref(),
            Some(
                "{\"definition\":1,\"format\":\"krs-difference/3\",\"implementation\":3,\
                 \"path\":\"acc\"}"
            )
        );
        assert_eq!(lock.header["protocols"], "[\"kink-implementation/1\"]");
        assert_eq!(lock.header["version"], 29);
        // A row with no implementation, program or view does not decode.
        let broken = text.replacen("view = \"whole\"\n", "", 1);
        assert!(
            Lock::decode(Path::new(LOCK_FILE), broken, LockKind::Compare)
                .unwrap_err()
                .contains("verdict 1 has no string implementation, program and view")
        );

        let dir = scratch("compare-round-trip");
        let path = dir.join(LOCK_FILE);
        let store = Store::new(&dir);
        let read = || Lock::read_kind(&path, LockKind::Compare).unwrap();
        let (value, ok) = read().settle(&store, &document, WRITE);
        assert!(ok);
        assert_eq!(value["status"], "created", "{value:#}");
        assert_eq!(fs::read_to_string(&path).unwrap(), text);
        let (value, _) = read().settle(&store, &document, LOCKED);
        assert_eq!(value["status"], "unchanged", "{value:#}");
        assert_eq!(value["failed"], json!([]), "{value:#}");
        let (value, _) = read().settle(&store, &document, WRITE);
        assert_eq!(value["status"], "unchanged", "{value:#}");
        assert_eq!(fs::read_to_string(&path).unwrap(), text);
        // `--only` compares the selected implementations' rows, and writes nothing.
        let only = ["cpu".to_owned()];
        let (value, _) = read().settle(
            &store,
            &document,
            Settle {
                only: &only,
                ..WRITE
            },
        );
        assert_eq!(
            (&value["status"], &value["reason"]),
            (&json!("not-written"), &json!("only"))
        );
    }

    /// A definition with no assumed totality writes the section it wrote before; one with some
    /// states them in a table of the section's header, which the verdicts rendering never holds;
    /// a change of them makes the section stale under `--locked`, and the change is named by its
    /// line alone, in no header change, and with neither symbol nor reason.
    #[test]
    fn the_assumed_totalities_are_in_the_section_and_a_change_of_them_is_stale() {
        let document = run_document(&[("m1", "killed", Some("p1")), ("m2", "survived", None)]);
        assert_eq!(
            crate::verdicts::lock_section_with(&document, &[]).unwrap(),
            lock_section(&document).unwrap()
        );
        let first = [("Lblsame".to_owned(), "the first reason".to_owned())];
        let section = crate::verdicts::lock_section_with(&document, &first).unwrap();
        assert!(
            section.contains("\n[run.assumed_totals]\n")
                && section.contains("\n\"Lblsame\" = \"the first reason\"\n"),
            "{section}"
        );
        assert!(!lock_text(&document).unwrap().contains("assumed_totals"));
        // The table is in the section's header, before its rows.
        assert!(section.find("assumed_totals") < section.find("[[run.mutation]]"));

        let dir = scratch("assumed-totals");
        let path = dir.join(LOCK_FILE);
        let store = Store::new(&dir);
        let read = |assumed: &[(String, String)]| {
            Lock::read_kind(&path, LockKind::Run)
                .unwrap()
                .with_assumed_totals(assumed)
        };
        let (value, ok) = read(&first).settle(&store, &document, WRITE);
        assert!(ok);
        assert_eq!(value["status"], "created", "{value:#}");
        let written = fs::read_to_string(&path).unwrap();
        assert!(written.contains("the first reason"), "{written}");
        let (value, _) = read(&first).settle(&store, &document, LOCKED);
        assert_eq!(value["status"], "unchanged", "{value:#}");

        let other = [("Lblsame".to_owned(), "another reason".to_owned())];
        for assumed in [&other[..], &[][..]] {
            let (value, _) = read(assumed).settle(&store, &document, LOCKED);
            assert_eq!(value["status"], "stale", "{value:#}");
            assert_eq!(value["header"], true, "{value:#}");
            assert_eq!(value["header_changes"], json!([]), "{value:#}");
            assert_eq!(value["difference"]["kind"], ASSUMED_TOTALS, "{value:#}");
            let shown = value.to_string();
            for hidden in ["Lblsame", "the first reason", "another reason"] {
                assert!(!shown.contains(hidden), "{value:#}");
            }
        }
        assert_eq!(fs::read_to_string(&path).unwrap(), written);
        // A run without --locked rewrites the section with the list it has.
        let (value, _) = read(&other).settle(&store, &document, WRITE);
        assert_eq!(value["status"], "written", "{value:#}");
        assert!(
            fs::read_to_string(&path)
                .unwrap()
                .contains("another reason")
        );
    }

    /// Under `--locked` a verdict that moved, or the first difference of a reported view, is a
    /// lock difference, named by its implementation, program and view.
    #[test]
    fn a_moved_verdict_or_first_difference_makes_the_compare_section_stale() {
        let recorded = compare_document(vec![answered("p1", "acc"), answered("p2", "acc")]);
        let lock = decoded(&lock_text(&recorded).unwrap(), LockKind::Compare);
        let store = Store::new("/nonexistent");
        let stale = |document: &Value| {
            let (value, _) = lock.settle(&store, document, LOCKED);
            assert_eq!(value["status"], "stale", "{value:#}");
            let mut with_lock = document.clone();
            with_lock["lock"] = value;
            assert_eq!(crate::cli::lock_status(&with_lock), crate::cli::EXIT_NO);
            stale_lines(&with_lock)
        };
        let moved = compare_document(vec![answered("p1", "n"), answered("p2", "acc")]);
        assert_eq!(
            stale(&moved),
            [
                "kink.lock: cpu p1 parity: different: its first difference moved: recorded \
              {\"definition\":1,\"format\":\"krs-difference/3\",\"implementation\":3,\
              \"path\":\"acc\"}, now {\"definition\":1,\"format\":\"krs-difference/3\",\
              \"implementation\":3,\"path\":\"n\"}"
            ]
        );
        let mut differs = answered("p2", "acc");
        differs["views"][0] = view(
            "whole",
            true,
            "different",
            json!({"difference": {"at": "end"}}),
        );
        let changed = compare_document(vec![answered("p1", "acc"), differs]);
        let (value, _) = lock.settle(&store, &changed, LOCKED);
        assert_eq!(
            value["changes"][0],
            json!({"implementation": "cpu", "program": "p2", "view": "whole",
                   "recorded": {"verdict": "equal", "reason": null, "difference": null},
                   "now": {"verdict": "different", "reason": null,
                           "difference": "{\"at\":\"end\"}"}})
        );
        assert_eq!(
            stale(&changed),
            ["kink.lock: cpu p2 whole: equal -> different"]
        );
        // A program the corpus no longer has: its rows are removed.
        let fewer = compare_document(vec![answered("p1", "acc")]);
        let mut fewer = fewer;
        fewer["programs"] = json!([{"id": "p1", "class": "comparable"}]);
        assert_eq!(
            stale(&fewer),
            [
                "kink.lock: cpu p2 whole: removed, was equal",
                "kink.lock: cpu p2 parity: removed, was different"
            ]
        );
    }

    /// The compare section of `cpu` answering both programs as a build of version 28 wrote it
    /// (taken from that build's rendering): before a section named its protocols, and before a
    /// verdict could hold a horizon.
    const COMPARE_SECTION_28: &str = r#"[compare]
# The verdicts of kink's `compare` command (`krs kink compare`, `kink-flow compare`): a run
# without --locked rewrites this section, and `compare --locked` checks that it is current.
version = 28
profile = "no-z3"
protocol = "kink-implementation/1"

[compare.spec]
outcome = "admitted"

# Each [[compare.verdict]] is one view of one implementation on one program, and its verdict:
# equal (its end agrees with the definition's under the view), different (`difference`, the
# first difference), could-not-apply (it declined the program; `reason`, its own words) or
# not-compared (`reason` says why). `request_sha256` names the request it was given, and
# `identity_sha256` its build (its `identity` file); a run that gave no answer keeps its rows.
[[compare.verdict]]
implementation = "cpu"
program = "p1"
view = "whole"
required = true
verdict = "equal"
request_sha256 = "r-p1"
identity_sha256 = "aa"

[[compare.verdict]]
implementation = "cpu"
program = "p1"
view = "parity"
required = false
verdict = "different"
difference = '{"definition":1,"format":"krs-difference/3","implementation":3,"path":"acc"}'
request_sha256 = "r-p1"
identity_sha256 = "aa"

[[compare.verdict]]
implementation = "cpu"
program = "p2"
view = "whole"
required = true
verdict = "equal"
request_sha256 = "r-p2"
identity_sha256 = "aa"

[[compare.verdict]]
implementation = "cpu"
program = "p2"
view = "parity"
required = false
verdict = "different"
difference = '{"definition":1,"format":"krs-difference/3","implementation":3,"path":"acc"}'
request_sha256 = "r-p2"
identity_sha256 = "aa"
"#;

    /// A section of implementations of the first protocol differs from the one version 28
    /// wrote in its header only: the `version` line, the line that names the protocol, now
    /// `protocols`, and the comments, which say what a verdict is. Every row is the bytes it was.
    #[test]
    fn a_first_protocol_compare_section_differs_from_version_28_in_its_header_only() {
        let document = compare_document(vec![answered("p1", "acc"), answered("p2", "acc")]);
        let section = lock_section(&document).unwrap();
        let parts = |text: &str| {
            let (header, rows) = text
                .split_once("\n[[compare.verdict]]\n")
                .expect("the section has rows");
            let stated = header
                .lines()
                .filter(|line| !line.starts_with('#'))
                .map(str::to_owned)
                .collect::<Vec<_>>();
            (stated, rows.to_owned())
        };
        let (before, rows_before) = parts(COMPARE_SECTION_28);
        let (now, rows_now) = parts(&section);
        assert_eq!(rows_now, rows_before);
        let moved = before
            .iter()
            .zip(&now)
            .filter(|(before, now)| before != now)
            .collect::<Vec<_>>();
        assert_eq!(before.len(), now.len());
        assert_eq!(
            moved,
            [
                (&"version = 28".to_owned(), &"version = 29".to_owned()),
                (
                    &"protocol = \"kink-implementation/1\"".to_owned(),
                    &"protocols = [\"kink-implementation/1\"]".to_owned()
                ),
            ]
        );
        // The comments say that a verdict is a test, and of what.
        for said in [
            "# Each verdict is a test of one build of an implementation on this corpus's programs",
            "it relates\n# no two definitions.",
            "point k is the implementation's claim",
        ] {
            assert!(section.contains(said), "{said}\n{section}");
        }
        // A record version 28 wrote is of another version: `--locked` refuses it, naming the
        // command that rewrites it.
        let old = format!("{}\n{COMPARE_SECTION_28}", record_header(None));
        let lock = decoded(&old, LockKind::Compare);
        assert!(lock.rows.iter().all(|row| row.horizon.is_none()));
        assert!(
            lock.refuse_other_version("kink-flow compare FLOW.toml --lock kink.lock")
                .unwrap_err()
                .starts_with("kink.lock: its [compare] section is recorded at version 28"),
        );
    }

    /// The row of `cpu` on `program` whose one view, the trace view `ticks`, agrees with the
    /// definition through `elements` elements, the definition's horizon.
    fn traced(program: &str, elements: u64) -> Value {
        compare_row(
            program,
            vec![view(
                "ticks",
                true,
                "agree-up-to",
                json!({"correspondence": "implementation-claim",
                       "horizon": {"ticks": {"elements": elements, "limited_by": "definition",
                                             "definition": "bound", "implementation": null}}}),
            )],
            Value::Null,
            Value::Null,
        )
    }

    /// A compare document of `cpu`, an implementation of the second protocol.
    fn traced_document(rows: Vec<Value>) -> Value {
        let mut document = compare_document(rows);
        let members = document.as_object_mut().unwrap();
        members.remove("protocol");
        members.insert("protocols".into(), json!(["kink-implementation/2"]));
        members.insert("evidence".into(), json!("testing"));
        document
    }

    /// A trace view's row holds its horizon, as canonical JSON in a literal string, and the
    /// header names the section's protocols. The section decodes to it and `--locked` finds it
    /// unchanged; a horizon that moved, the verdict being the same, makes the section stale.
    #[test]
    fn a_moved_horizon_makes_the_compare_section_stale() {
        let recorded = traced_document(vec![traced("p1", 6), answered("p2", "acc")]);
        let text = lock_text(&recorded).unwrap();
        let horizon = |elements: u64| {
            format!(
                "{{\"ticks\":{{\"definition\":\"bound\",\"elements\":{elements},\
                 \"implementation\":null,\"limited_by\":\"definition\"}}}}"
            )
        };
        assert!(
            text.contains(&format!(
                "[[compare.verdict]]\nimplementation = \"cpu\"\nprogram = \"p1\"\nview = \
                 \"ticks\"\nrequired = true\nverdict = \"agree-up-to\"\nhorizon = \
                 '{}'\nrequest_sha256 = \"r-p1\"\nidentity_sha256 = \"aa\"\n",
                horizon(6)
            )),
            "{text}"
        );
        assert!(
            text.contains("\nprotocols = [\"kink-implementation/2\"]\n"),
            "{text}"
        );
        let lock = decoded(&text, LockKind::Compare);
        assert_eq!(lock.rows[0].status.as_deref(), Some("agree-up-to"));
        assert_eq!(lock.rows[0].horizon, Some(horizon(6)));
        assert!(lock.rows[1..].iter().all(|row| row.horizon.is_none()));
        let store = Store::new("/nonexistent");
        let (value, _) = lock.settle(&store, &recorded, LOCKED);
        assert_eq!(value["status"], "unchanged", "{value:#}");

        let moved = traced_document(vec![traced("p1", 5), answered("p2", "acc")]);
        let (value, _) = lock.settle(&store, &moved, LOCKED);
        assert_eq!(value["status"], "stale", "{value:#}");
        assert_eq!(
            value["changes"],
            json!([{"implementation": "cpu", "program": "p1", "view": "ticks",
                    "recorded": {"verdict": "agree-up-to", "reason": null, "difference": null,
                                 "horizon": horizon(6)},
                    "now": {"verdict": "agree-up-to", "reason": null, "difference": null,
                            "horizon": horizon(5)}}])
        );
        let mut with_lock = moved.clone();
        with_lock["lock"] = value;
        assert_eq!(crate::cli::lock_status(&with_lock), crate::cli::EXIT_NO);
        assert_eq!(
            stale_lines(&with_lock),
            [format!(
                "kink.lock: cpu p1 ticks: agree-up-to: its horizon moved: recorded {}, now {}",
                horizon(6),
                horizon(5)
            )]
        );
        // A verdict that moved from a horizon to both sides' closure is a moved verdict.
        let mut closed = traced("p1", 6);
        closed["views"][0] = view(
            "ticks",
            true,
            "equal",
            json!({"correspondence": "implementation-claim", "horizon": null}),
        );
        let closed = traced_document(vec![closed, answered("p2", "acc")]);
        let (value, _) = lock.settle(&store, &closed, LOCKED);
        let mut with_lock = closed.clone();
        with_lock["lock"] = value;
        assert_eq!(
            stale_lines(&with_lock),
            ["kink.lock: cpu p1 ticks: agree-up-to -> equal"]
        );
        // A run of the implementation that gave no answer keeps the recorded row, its horizon
        // included: the section is undecided, not stale.
        let failed = traced_document(vec![
            compare_row(
                "p1",
                vec![],
                json!({"kind": "exit", "detail": "status 3"}),
                Value::Null,
            ),
            answered("p2", "acc"),
        ]);
        let (value, _) = lock.settle(&store, &failed, LOCKED);
        assert_eq!(value["status"], "undecided", "{value:#}");
        assert_eq!(value["changes"], json!([]), "{value:#}");
    }

    /// A row of a run that gave no answer (the implementation failed, the clock cancelled it, or
    /// the clock stopped the definition's baseline) keeps its recorded verdicts: under `--locked`
    /// the section is `undecided` (exit 3), not stale, and a write leaves the file as it was.
    #[test]
    fn a_run_with_no_answer_keeps_its_compare_rows() {
        let dir = scratch("compare-no-answer");
        let path = dir.join(LOCK_FILE);
        let store = Store::new(&dir);
        let recorded = compare_document(vec![answered("p1", "acc"), answered("p2", "acc")]);
        let read = || Lock::read_kind(&path, LockKind::Compare).unwrap();
        let _ = read().settle(&store, &recorded, WRITE);
        let text = fs::read_to_string(&path).unwrap();
        let timeout = json!({"kind": "timeout", "detail": "cancelled"});
        let exit = json!({"kind": "exit", "detail": "status 3"});
        let cancelled = compare_document(vec![
            compare_row("p1", vec![], timeout, json!("implementation")),
            answered("p2", "acc"),
        ]);
        let crashed = compare_document(vec![
            answered("p1", "acc"),
            compare_row("p2", vec![], exit, Value::Null),
        ]);
        let mut baseline = compare_document(vec![
            compare_row(
                "p1",
                vec![
                    view(
                        "whole",
                        true,
                        "not-compared",
                        json!({"reason": "definition"}),
                    ),
                    view(
                        "parity",
                        false,
                        "not-compared",
                        json!({"reason": "definition"}),
                    ),
                ],
                Value::Null,
                json!("baseline"),
            ),
            answered("p2", "acc"),
        ]);
        baseline["programs"][0]["class"] = json!("timeout");
        for (document, stopped, failed, kept) in [
            (
                &cancelled,
                json!([{"implementation": "cpu", "program": "p1", "run": "implementation"}]),
                json!([]),
                0,
            ),
            (
                &crashed,
                json!([]),
                json!([{"implementation": "cpu", "program": "p2", "failure": "exit"}]),
                0,
            ),
            (
                &baseline,
                json!([{"program": "p1", "run": "baseline"}]),
                json!([]),
                2,
            ),
        ] {
            let (value, _) = read().settle(&store, document, LOCKED);
            assert_eq!(value["status"], "undecided", "{value:#}");
            assert_eq!(value["clock_stopped"], stopped, "{value:#}");
            assert_eq!(value["failed"], failed, "{value:#}");
            assert_eq!(
                value["kept"].as_array().map(Vec::len),
                Some(kept),
                "{value:#}"
            );
            let mut with_lock = document.clone();
            with_lock["lock"] = value;
            assert_eq!(
                crate::cli::lock_status(&with_lock),
                crate::cli::EXIT_UNANSWERED
            );
            assert!(!crate::clock::clock_lines(&with_lock).is_empty());
            let (value, _) = read().settle(&store, document, WRITE);
            assert_eq!(value["status"], "unchanged", "{value:#}");
            assert_eq!(fs::read_to_string(&path).unwrap(), text);
        }
        let mut with_lock = baseline.clone();
        with_lock["lock"] = read().settle(&store, &baseline, LOCKED).0;
        with_lock["lock"]["path"] = json!(LOCK_FILE);
        assert_eq!(
            crate::clock::clock_lines(&with_lock),
            [
                "kink.lock: the clock (budget.time_ms) stopped the baseline run of p1: its \
                 compare rows are not decided on this host",
                "kink.lock: cpu p1 whole: kept equal unverified: this host gives not-compared \
                 (definition)",
                "kink.lock: cpu p1 parity: kept different unverified: this host gives \
                 not-compared (definition)",
            ]
        );
        // A row the lock does not record is written from the run, but a run with no answer
        // writes none.
        fs::remove_file(&path).unwrap();
        let _ = read().settle(&store, &cancelled, WRITE);
        let only_p2 = decoded(&fs::read_to_string(&path).unwrap(), LockKind::Compare);
        assert_eq!(
            only_p2
                .rows
                .iter()
                .map(|row| row.id.clone())
                .collect::<Vec<_>>(),
            [
                compare_row_id("cpu", "p2", "whole"),
                compare_row_id("cpu", "p2", "parity")
            ]
        );
    }

    /// `compare` writes its section after the other two, keeping their text byte for byte, a
    /// hand comment included; and a write of another section keeps the compare section's.
    #[test]
    fn the_compare_section_keeps_the_other_sections_byte_for_byte() {
        let dir = scratch("compare-own-section");
        let path = dir.join(LOCK_FILE);
        let store = Store::new(&dir);
        let run = run_document(&[("m", "killed", Some("t1"))]);
        let coverage = coverage_document(&[("rule:a", "text")], &["rule:b"]);
        let _ = Lock::read_kind(&path, LockKind::Run)
            .unwrap()
            .settle(&store, &run, WRITE);
        let _ = Lock::read_kind(&path, LockKind::Coverage)
            .unwrap()
            .settle(&store, &coverage, WRITE);
        let both = fs::read_to_string(&path)
            .unwrap()
            .replace("[run.spec]\n", "[run.spec]\n# kept by hand\n");
        fs::write(&path, &both).unwrap();
        let compare = compare_document(vec![answered("p1", "acc"), answered("p2", "acc")]);
        let (value, _) = Lock::read_kind(&path, LockKind::Compare)
            .unwrap()
            .settle(&store, &compare, WRITE);
        assert_eq!(value["status"], "created", "{value:#}");
        let all = fs::read_to_string(&path).unwrap();
        assert_eq!(all, format!("{both}\n{}", compare_section_text()));
        // `run` and `coverage` find their sections as they were, and `run` rewrites its own
        // keeping the compare section.
        let (value, _) = Lock::read_kind(&path, LockKind::Coverage)
            .unwrap()
            .settle(&store, &coverage, LOCKED);
        assert_eq!(value["status"], "unchanged", "{value:#}");
        let moved = run_document(&[("m", "survived", None)]);
        let _ = Lock::read_kind(&path, LockKind::Run)
            .unwrap()
            .settle(&store, &moved, WRITE);
        let rewritten = fs::read_to_string(&path).unwrap();
        assert!(
            rewritten.ends_with(&format!("\n{}", compare_section_text())),
            "{rewritten}"
        );
        let (value, _) = Lock::read_kind(&path, LockKind::Compare)
            .unwrap()
            .settle(&store, &compare, LOCKED);
        assert_eq!(value["status"], "unchanged", "{value:#}");
    }

    /// A record is its header and one section per command that wrote it: a command's rendering
    /// is the record holding its section alone, which starts at its `[run]` or `[coverage]`
    /// line; the record's header holds the comment and `schema` only, and every value a verdict
    /// depends on (version, profile) is in the section.
    #[test]
    fn a_record_is_its_header_and_one_section_per_command() {
        let run = lock_text(&run_document(&[("a", "killed", Some("t1"))])).unwrap();
        let header = record_header(None);
        assert!(run.starts_with(&format!("{header}\n[run]\n# ")), "{run}");
        assert!(!header.contains("version"), "{header}");
        assert!(
            run.contains(
                "\nversion = 29\nprofile = \"no-z3\"\n\n[run.spec]\noutcome = \"admitted\"\n"
            ),
            "{run}"
        );
        assert!(
            run.ends_with("[[run.mutation]]\nid = \"a\"\nstatus = \"killed\"\nkiller = \"t1\"\n"),
            "{run}"
        );
        let (head_text, found) = split(&run);
        assert_eq!(head_text, format!("{header}\n"));
        assert_eq!(found.len(), 1);
        assert_eq!((found[0].0, found[0].1), (LockKind::Run, 7));
        let lock = decoded(&run, LockKind::Run);
        assert_eq!(lock.section.as_deref(), Some(&run[header.len() + 1..]));
        assert_eq!(
            lock.killers(),
            BTreeMap::from([("a".to_owned(), "t1".to_owned())])
        );
        assert_eq!(lock.header["version"], 29);
        // The other command finds no section of its own: it records nothing, and is no error.
        let coverage = decoded(&run, LockKind::Coverage);
        assert_eq!(
            (coverage.section.as_deref(), coverage.rows.len()),
            (None, 0)
        );
        assert!(!coverage.records());
    }

    /// The record of a flow that names its definition states it in its header, and a command
    /// whose flow is for another definition (or for none) is refused before it compares or writes,
    /// the file left as it was. A record that names none (a K flow's, or one written before
    /// version 28) is read; `--locked` finds its header stale, and a write adds the name.
    #[test]
    fn a_record_names_its_definition_and_refuses_another() {
        let dir = scratch("definition");
        let path = dir.join(LOCK_FILE);
        let store = Store::new(&dir);
        let run = run_document(&[("m", "killed", Some("t1"))]);
        let read = |definition: Option<&str>| {
            Lock::read_for(&path, LockKind::Run, None, false, "run", definition)
        };
        let (value, _) = read(Some("plus:main")).unwrap().settle(&store, &run, WRITE);
        assert_eq!(value["status"], "created", "{value:#}");
        let written = fs::read_to_string(&path).unwrap();
        let header = record_header(Some("plus:main"));
        assert!(
            header.ends_with("schema = \"kink-flow-verdicts\"\ndefinition = \"plus:main\"\n"),
            "{header}"
        );
        assert_eq!(
            written,
            format!("{header}\n{}", lock_section(&run).unwrap())
        );
        let (value, _) = read(Some("plus:main"))
            .unwrap()
            .settle(&store, &run, LOCKED);
        assert_eq!(value["status"], "unchanged", "{value:#}");

        // Another definition's flow, and a flow that names none, are refused; nothing is written.
        for other in [Some("refined:main"), Some("plus:other"), None] {
            let detail = read(other).unwrap_err();
            assert!(
                detail.contains("it is the record of the definition `plus:main`")
                    && detail.contains(other.unwrap_or("names no definition")),
                "{detail}"
            );
        }
        assert_eq!(fs::read_to_string(&path).unwrap(), written);
        // So is a write whose file came to name another definition after it was read.
        let lock = read(Some("plus:main")).unwrap();
        let theirs = written.replace("plus:main", "refined:main");
        fs::write(&path, &theirs).unwrap();
        let moved = run_document(&[("m", "survived", None)]);
        let (value, ok) = lock.settle(&store, &moved, WRITE);
        assert!(!ok);
        assert_eq!(value["reason"], "write-failed", "{value:#}");
        assert_eq!(fs::read_to_string(&path).unwrap(), theirs);

        // A record that names no definition: stale in its header under `--locked`, rewritten
        // with the name otherwise, its rows kept.
        let unnamed = lock_text(&run).unwrap();
        assert!(!unnamed.contains("definition ="), "{unnamed}");
        fs::write(&path, &unnamed).unwrap();
        let (value, _) = read(Some("plus:main"))
            .unwrap()
            .settle(&store, &run, LOCKED);
        assert_eq!(value["status"], "stale", "{value:#}");
        assert_eq!(value["header"], true, "{value:#}");
        assert_eq!(value["changes"], json!([]), "{value:#}");
        let (value, _) = read(Some("plus:main")).unwrap().settle(&store, &run, WRITE);
        assert_eq!(value["status"], "written", "{value:#}");
        assert_eq!(fs::read_to_string(&path).unwrap(), written);
        // A definition that is not a string does not decode.
        fs::write(
            &path,
            unnamed.replace("\n\n[run]", "\ndefinition = 1\n\n[run]"),
        )
        .unwrap();
        assert!(
            read(None)
                .unwrap_err()
                .contains("its definition is not a string")
        );
    }

    /// Each command rewrites only its own section and keeps the other's text byte for byte
    /// (trailing blank lines aside), in the record's order `[run]`, `[coverage]`; `--locked`
    /// compares only the command's own section, so a stale `[run]` leaves `coverage --locked`
    /// unchanged, and the reverse.
    #[test]
    fn each_command_keeps_and_checks_only_its_own_section() {
        let dir = scratch("own-section");
        let path = dir.join(LOCK_FILE);
        let store = Store::new(&dir);
        let coverage = coverage_document(&[("rule:a", "text")], &["rule:b"]);
        let read = |kind| Lock::read_kind(&path, kind).unwrap();
        let (value, ok) = read(LockKind::Coverage).settle(&store, &coverage, WRITE);
        assert!(ok);
        assert_eq!(value["status"], "created", "{value:#}");
        let only_coverage = fs::read_to_string(&path).unwrap();
        assert_eq!(only_coverage, lock_text(&coverage).unwrap());

        let run = run_document(&[("m", "killed", Some("t1"))]);
        let (value, _) = read(LockKind::Run).settle(&store, &run, WRITE);
        assert_eq!(value["status"], "created", "{value:#}");
        let both = fs::read_to_string(&path).unwrap();
        let run_section = lock_section(&run).unwrap();
        let coverage_section = lock_section(&coverage).unwrap();
        assert_eq!(
            both,
            format!("{}\n{run_section}\n{coverage_section}", record_header(None))
        );

        // A stale `[run]`: `coverage --locked` is unchanged, `run --locked` is stale.
        let moved = run_document(&[("m", "survived", None)]);
        let (value, _) = read(LockKind::Coverage).settle(&store, &coverage, LOCKED);
        assert_eq!(value["status"], "unchanged", "{value:#}");
        let (value, _) = read(LockKind::Run).settle(&store, &moved, LOCKED);
        assert_eq!(value["status"], "stale", "{value:#}");
        assert_eq!(value["header"], false, "{value:#}");
        assert_eq!(
            value["difference"]["line"],
            u64::try_from(
                both.lines()
                    .position(|l| l == "status = \"killed\"")
                    .unwrap()
                    + 1
            )
            .unwrap()
        );

        // `run` rewrites its section; the coverage section's bytes are as they were, a hand
        // comment in it included, and its trailing blank lines are the record's.
        let commented =
            both.replace("[coverage.rules]\n", "[coverage.rules]\n# kept by hand\n") + "\n\n";
        fs::write(&path, &commented).unwrap();
        let (value, _) = read(LockKind::Run).settle(&store, &moved, WRITE);
        assert_eq!(value["status"], "written", "{value:#}");
        let rewritten = fs::read_to_string(&path).unwrap();
        let kept = trimmed(sections(&commented)[1].2);
        assert!(kept.contains("# kept by hand\n"));
        assert_eq!(
            rewritten,
            format!(
                "{}\n{}\n{kept}",
                record_header(None),
                lock_section(&moved).unwrap()
            )
        );
        // `coverage --locked` now finds its own hand comment, and nothing of `[run]`.
        let (value, _) = read(LockKind::Coverage).settle(&store, &coverage, LOCKED);
        assert_eq!(value["status"], "stale", "{value:#}");
        assert_eq!(value["changes"], json!([]), "{value:#}");
        let (value, _) = read(LockKind::Run).settle(&store, &moved, LOCKED);
        assert_eq!(value["status"], "unchanged", "{value:#}");
        // Writing what the file holds writes nothing.
        let (value, _) = read(LockKind::Run).settle(&store, &moved, WRITE);
        assert_eq!(value["status"], "unchanged", "{value:#}");
        assert_eq!(fs::read_to_string(&path).unwrap(), rewritten);
    }

    /// Two commands writing their sections at once never lose one: each write reads the file
    /// again under the directory's lock and keeps the other section the file then holds.
    #[test]
    fn concurrent_writes_of_the_two_sections_lose_neither() {
        let dir = scratch("concurrent");
        let path = dir.join(LOCK_FILE);
        let store = Store::new(&dir);
        let runs = (0..24)
            .map(|n| run_document(&[("m", "killed", Some(&*format!("t{n}")))]))
            .collect::<Vec<_>>();
        let coverages = (0..24)
            .map(|n| coverage_document(&[], &[&*format!("rule:{n}")]))
            .collect::<Vec<_>>();
        std::thread::scope(|scope| {
            for (kind, documents) in [(LockKind::Run, &runs), (LockKind::Coverage, &coverages)] {
                let (path, store) = (&path, &store);
                scope.spawn(move || {
                    for document in documents {
                        let lock = Lock::read_kind(path, kind).unwrap();
                        let (value, ok) = lock.settle(store, document, WRITE);
                        assert!(ok, "{value:#}");
                    }
                });
            }
        });
        let last = fs::read_to_string(&path).unwrap();
        assert_eq!(
            last,
            format!(
                "{}\n{}\n{}",
                record_header(None),
                lock_section(runs.last().unwrap()).unwrap(),
                lock_section(coverages.last().unwrap()).unwrap()
            )
        );
    }

    /// A section whose rows are the rendering's in another order differs from it with kind
    /// `order`, at its first reordered row's `id` line in the file, a comment before it
    /// included; one that differs only in its text with kind `text`, at the first line that
    /// differs; an equal or absent section has no difference.
    #[test]
    fn the_first_difference_names_a_reordering_or_a_line() {
        let ab = run_document(&[("a", "survived", None), ("b", "survived", None)]);
        let rendered = lock_section(&ab).unwrap();
        let text = lock_text(&ab).unwrap();
        let ba = text
            .replace("id = \"a\"", "id = \"x\"")
            .replace("id = \"b\"", "id = \"a\"")
            .replace("id = \"x\"", "id = \"b\"");
        let line = |text: &str, wanted: &str| {
            u64::try_from(text.split('\n').position(|l| l == wanted).unwrap() + 1).unwrap()
        };
        assert_eq!(
            decoded(&ba, LockKind::Run).difference(&rendered),
            json!({"kind": "order", "line": line(&ba, "id = \"b\""), "recorded": "id = \"b\"",
                   "now": "id = \"a\""})
        );
        let commented = text.replace("[run.spec]\n", "[run.spec]\n# kept by hand\n");
        assert_eq!(
            decoded(&commented, LockKind::Run).difference(&rendered),
            json!({"kind": "text", "line": line(&commented, "# kept by hand"),
                   "recorded": "# kept by hand", "now": "outcome = \"admitted\""})
        );
        // A hand comment before reordered rows: the order is what a run changes.
        let commented_ba = ba.replace("[run.spec]\n", "[run.spec]\n# kept by hand\n");
        assert_eq!(
            decoded(&commented_ba, LockKind::Run).difference(&rendered)["kind"],
            "order"
        );
        assert_eq!(
            decoded(&text, LockKind::Run).difference(&rendered),
            Value::Null
        );
        assert_eq!(Lock::default().difference(&rendered), Value::Null);
    }

    /// The header keys of a section are named relative to it, in its line order, and no comment,
    /// row, continuation line or family names one.
    #[test]
    fn a_sections_header_keys_are_its_own() {
        let coverage =
            lock_section(&coverage_document(&[("rule:a", "text")], &["rule:b"])).unwrap();
        assert_eq!(
            header_key_order(&coverage, "coverage"),
            [
                "version",
                "profile",
                "spec.outcome",
                "settings.depth",
                "settings.mcdc",
                "rules.open",
                "rules.argued",
                "requirements.open",
                "requirements.argued",
                "syntax.open",
                "syntax.argued",
                "flips.run",
            ]
        );
        let lock = decoded(
            &format!("{}\n{coverage}", record_header(None)),
            LockKind::Coverage,
        );
        assert_eq!(
            lock.header.keys().collect::<Vec<_>>(),
            [
                "profile",
                "settings.depth",
                "settings.mcdc",
                "spec.outcome",
                "version"
            ]
        );
        assert_eq!(lock.argued["rules"], ["rule:a"]);
        assert_eq!(lock.open["rules"], ["rule:b"]);
        assert_eq!(lock.arguments["rule:a"], "text");
        assert!(!head(LockKind::Coverage, &coverage).contains("rule:"));
    }

    /// `stale_lines` names the first difference only when neither the header nor a row's verdict
    /// explains the stale lock.
    #[test]
    fn a_stale_lock_with_no_change_names_its_first_difference() {
        let document = |header: bool, changes: Value| {
            json!({
                "mutations": [],
                "lock": {
                    "path": "kink.lock",
                    "status": "stale",
                    "header": header,
                    "changes": changes,
                    "difference": {"kind": "order", "line": 9, "recorded": "id = \"b\"", "now": "id = \"a\""},
                },
            })
        };
        assert_eq!(
            stale_lines(&document(false, json!([]))),
            [
                "kink.lock: its rows are in another order than the mutation list's (first at \
                 line 9: recorded `id = \"b\"`, now `id = \"a\"`); a run writes them in the list's \
                 order"
            ]
        );
        let changed = json!([{"mutation": "a", "recorded": null, "now": {"status": "survived"}}]);
        assert_eq!(
            stale_lines(&document(false, changed)),
            ["kink.lock: a: added, survived"]
        );
        assert_eq!(
            stale_lines(&document(true, json!([]))),
            [
                "kink.lock: the [run] section's header differs (the file has no [run] section, \
                 or the record's header, or a comment or spacing before its first mutation, \
                 differs)"
            ]
        );
    }

    /// A section recorded on another Z3 build differs from the rendering in its header's values
    /// only: `header_changes` names each key whose value differs, in the section's line order,
    /// and `stale_lines` names each with why it matters; a key only one side has is null on the
    /// other.
    #[test]
    fn a_lock_of_another_z3_build_names_the_build_lines() {
        let document = |build: Value| {
            let mut document = run_document(&[("a", "survived", None)]);
            document["profile"] = json!("z3");
            document["z3"] = build;
            document
        };
        let now = document(json!({"version": "5.3.3.0", "library_sha256": "bbbb"}));
        let section = lock_section(&now).unwrap();
        let recorded = |build: Value| decoded(&lock_text(&document(build)).unwrap(), LockKind::Run);
        let other = recorded(json!({"version": "5.3.3.0", "library_sha256": "aaaa"}));
        let changes = other.header_changes(&section);
        assert_eq!(
            changes,
            [json!({"key": "z3_library_sha256", "recorded": "aaaa", "now": "bbbb"})]
        );
        // A build that could not name its library has no digest line.
        assert_eq!(
            recorded(json!({"version": "5.3.3.0"})).header_changes(&section),
            [json!({"key": "z3_library_sha256", "recorded": null, "now": "bbbb"})]
        );
        let mut portable = run_document(&[("a", "survived", None)]);
        portable["profile"] = json!("no-z3");
        assert_eq!(
            other.header_changes(&lock_section(&portable).unwrap()),
            [
                json!({"key": "profile", "recorded": "z3", "now": "no-z3"}),
                json!({"key": "z3_library_sha256", "recorded": "aaaa", "now": null}),
                json!({"key": "z3_version", "recorded": "5.3.3.0", "now": null}),
            ]
        );
        assert_eq!(
            other.header_changes(other.section.as_deref().unwrap()),
            [] as [Value; 0]
        );
        assert_eq!(Lock::default().header_changes(&section), [] as [Value; 0]);
        let mut stale = now.clone();
        stale["lock"] = json!({
            "path": "kink.lock",
            "status": "stale",
            "header": true,
            "header_changes": changes,
            "changes": [],
            "difference": {"kind": "text", "line": 9, "recorded": "z3_library_sha256 = \"aaaa\"", "now": "z3_library_sha256 = \"bbbb\""},
        });
        assert_eq!(
            stale_lines(&stale),
            [
                "kink.lock: [run] z3_library_sha256 differs: recorded \"aaaa\", now \"bbbb\" \
                 (another Z3 build)"
            ]
        );
    }

    /// A coverage section gives each argued item once, in its family's `argued` with its
    /// standing: a standing that moves makes a `--locked` run stale, with no header change, the
    /// lock's state naming the item (`argument_changes`) and the line (`difference`), and
    /// `stale_lines` the move. An argument removed is named once, by its obligation's change.
    #[test]
    fn a_moved_standing_makes_the_lock_stale_and_names_its_line() {
        let recorded = coverage_document(&[("rule:a", "text"), ("rule:b", "text")], &[]);
        let recorded_text = lock_text(&recorded).unwrap();
        let entry =
            |id: &str, standing: &str| format!("  {{ id = \"{id}\", standing = \"{standing}\" }},");
        assert!(
            recorded_text.contains(&format!(
                "\n[coverage.rules]\nopen = [\n]\nargued = [\n{}\n{}\n]\n",
                entry("rule:a", "text"),
                entry("rule:b", "text")
            )),
            "{recorded_text}"
        );
        assert!(!recorded_text.contains("arguments"), "{recorded_text}");
        let lock = decoded(&recorded_text, LockKind::Coverage);
        let store = Store::new("/nonexistent");
        let (same, _) = lock.settle(&store, &recorded, LOCKED);
        assert_eq!(same["status"], "unchanged", "{same:#}");
        assert_eq!(same["argument_changes"], json!([]));

        let moved = coverage_document(&[("rule:a", "text"), ("rule:b", "unchecked")], &[]);
        let (stale, _) = lock.settle(&store, &moved, LOCKED);
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
            .position(|line| line == entry("rule:b", "text"))
            .unwrap()
            + 1;
        assert_eq!(
            stale["difference"],
            json!({"kind": "text", "line": line, "recorded": entry("rule:b", "text"),
                   "now": entry("rule:b", "unchecked")})
        );
        let mut with_lock = moved.clone();
        with_lock["lock"] = stale;
        assert_eq!(
            stale_lines(&with_lock),
            ["kink.lock: rule:b: standing text -> unchecked"]
        );

        let reopened = coverage_document(&[("rule:a", "text")], &["rule:b"]);
        let (stale, _) = lock.settle(&store, &reopened, LOCKED);
        let mut with_lock = reopened.clone();
        with_lock["lock"] = stale;
        assert_eq!(
            stale_lines(&with_lock),
            ["kink.lock: rules: rule:b is open (was argued)"]
        );

        // A standing removed by hand, the item still argued: the standing's change names it.
        let edited = recorded_text.replace(&entry("rule:b", "text"), "  { id = \"rule:b\" },");
        let lock = decoded(&edited, LockKind::Coverage);
        let (stale, _) = lock.settle(&store, &recorded, LOCKED);
        let mut with_lock = recorded.clone();
        with_lock["lock"] = stale;
        assert_eq!(
            stale_lines(&with_lock),
            ["kink.lock: rule:b: standing none -> text"]
        );
    }

    /// A coverage lock written before version 24 (one command's rendering at the top of its
    /// file: `document`, bare `argued` ids, the standings under `[arguments]`, `[[flip]]`) still
    /// decodes as the coverage section: its rows, argued ids and standings are read, and
    /// `[arguments]` is no part of its header. Under `--locked` it is refused, naming the command
    /// that rewrites it, as a lock that names no version is; a current section and an absent file
    /// are not. Read for `run`, the file is another command's record, which a run would
    /// overwrite: refused.
    #[test]
    fn a_lock_of_another_version_is_read_and_refused_under_locked() {
        let old = "schema = \"kink-flow-verdicts\"\nversion = 23\ndocument = \"coverage\"\n\n\
                   [spec]\noutcome = \"admitted\"\n\n[settings]\ntiers = [1, 2]\ndepth = 1\n\
                   mcdc = [\n]\n\n[rules]\nopen = [\n]\nargued = [\n  \"rule:a\",\n]\n\n\
                   [arguments]\n\"rule:a\" = \"text\"\n\"flip--a+b--X\" = \"unchecked\"\n\n\
                   [flips]\nrun = true\n\n[[flip]]\nid = \"flip--a+b--X\"\nstatus = \"argued\"\n\n\
                   [[flip]]\nid = \"flip--a+b--Y\"\nstatus = \"distinguished\"\nkiller = \"t1\"\n";
        let kind = LockKind::Coverage;
        let lock = decoded(old, kind);
        assert_eq!(lock.section, None);
        assert_eq!(
            lock.argued,
            BTreeMap::from([("rules".to_owned(), vec!["rule:a".to_owned()])])
        );
        assert_eq!(
            lock.arguments,
            BTreeMap::from([
                ("flip--a+b--X".to_owned(), "unchecked".to_owned()),
                ("rule:a".to_owned(), "text".to_owned()),
            ])
        );
        assert_eq!(
            lock.killers(),
            BTreeMap::from([("flip--a+b--Y".to_owned(), "t1".to_owned())])
        );
        assert!(
            lock.header
                .keys()
                .all(|key| !key.starts_with("arguments") && key != "schema" && key != "document"),
            "{:?}",
            lock.header
        );
        let command = "krs kink coverage --package p --definition main";
        assert_eq!(
            lock.refuse_other_version(command).unwrap_err(),
            "kink.lock: it is recorded at version 23 of the verdicts rendering, and this build \
             writes version 29, so --locked cannot find it current; run `krs kink coverage \
             --package p --definition main` without --locked once to rewrite it, and review its \
             diff"
        );
        let unversioned = decoded(&old.replace("version = 23\n", ""), kind);
        assert!(
            unversioned
                .refuse_other_version(command)
                .unwrap_err()
                .contains("it names no version of the verdicts rendering"),
        );
        let current = lock_text(&coverage_document(&[], &[])).unwrap();
        assert_eq!(
            decoded(&current, kind).refuse_other_version(command),
            Ok(())
        );
        let other_version = current.replace("\nversion = 29\n", "\nversion = 30\n");
        assert!(
            decoded(&other_version, kind)
                .refuse_other_version(command)
                .unwrap_err()
                .starts_with("kink.lock: its [coverage] section is recorded at version 30"),
        );
        assert_eq!(Lock::default().refuse_other_version(command), Ok(()));
        let refused = Lock::decode(Path::new(LOCK_FILE), old.to_owned(), LockKind::Run);
        assert!(
            refused
                .unwrap_err()
                .contains("whose document is \"coverage\", not \"run\""),
        );
    }

    /// An old file a front end kept the command's lock in: while the record has no section of
    /// the command, its killers are read (`migrated`), and the write moves them into the record,
    /// with a note to delete the old file, which is left as it is; once the record has the
    /// section, the old file is `superseded`. Under `--locked` it refuses the command while it is
    /// there, naming the command that moves it, or saying to delete it.
    #[test]
    fn an_old_lock_file_is_migrated_and_refused_under_locked() {
        let dir = scratch("legacy");
        let path = dir.join(LOCK_FILE);
        let old = dir.join(LEGACY_RUN_LOCK_FILE);
        let old_text = "schema = \"kink-flow-verdicts\"\nversion = 23\ndocument = \"run\"\n\n\
                        [[mutation]]\nid = \"m\"\nstatus = \"killed\"\nkiller = \"t9\"\n";
        fs::write(&old, old_text).unwrap();
        let command = "krs kink run --package p --definition main";
        let read = |locked| Lock::read_for(&path, LockKind::Run, Some(&old), locked, command, None);
        assert_eq!(
            read(true).unwrap_err(),
            format!(
                "{}: it is a lock written before version 24, which {} replaces with one [run] \
                 section per command, so --locked cannot find the corpus's lock current; run \
                 `{command}` without --locked once to move its killers into {}, then delete {}",
                old.display(),
                path.display(),
                path.display(),
                old.display()
            )
        );
        let lock = read(false).unwrap();
        assert_eq!(lock.killers()["m"], "t9");
        assert_eq!(
            lock.legacy,
            Some(Legacy {
                path: old.clone(),
                migrated: true
            })
        );
        let document = run_document(&[("m", "killed", Some("t9"))]);
        let (value, _) = lock.settle(&Store::new(&dir), &document, WRITE);
        assert_eq!(value["status"], "created", "{value:#}");
        assert_eq!(value["changes"], json!([]), "{value:#}");
        assert_eq!(
            value["legacy"],
            json!({"path": old.display().to_string(), "status": "migrated", "moved": true})
        );
        let mut with_lock = document.clone();
        with_lock["lock"] = value;
        assert_eq!(
            lock_notes(&with_lock),
            [format!(
                "{}: its killers are now in {}'s [run] section; delete {}",
                old.display(),
                path.display(),
                old.display()
            )]
        );
        assert_eq!(fs::read_to_string(&old).unwrap(), old_text);
        assert_eq!(
            fs::read_to_string(&path).unwrap(),
            lock_text(&document).unwrap()
        );

        // The record has the section now: the old file is superseded, and refused under
        // `--locked` until it is deleted.
        let lock = read(false).unwrap();
        assert_eq!(
            lock.legacy.as_ref().map(|legacy| legacy.migrated),
            Some(false)
        );
        assert!(read(true).unwrap_err().ends_with(&format!(
            "[run] section now keeps; delete {}",
            old.display()
        )),);
        fs::remove_file(&old).unwrap();
        assert!(read(true).unwrap().legacy.is_none());
    }
}
